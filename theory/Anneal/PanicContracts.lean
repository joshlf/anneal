-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.
import Trusted
import Anneal.Refinement
import Anneal.Effect
import Anneal.ITree
import Anneal.EffectWP
import Anneal.ITreeWP
import Anneal.Pass
import Anneal.Rustc.V2026_06_01.Lower
import Anneal.Rustc.V2026_06_01.SymbolicEval

namespace Anneal.PanicContracts

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Refinement
open Anneal.Effect
open Anneal.ITree
open Anneal.Pass
open Anneal.EffectWP
open Anneal.ITreeWP
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-!
First-class panic contracts and call-boundary preservation for interaction
trees and captured MIR.

A safe Rust function may panic on some inputs (an out-of-range index, checked
arithmetic overflow, an explicit `assert!`) while remaining free of undefined
behavior on every input. The certificates in `Trusted.VerificationResult`
constrain normal returns only: a partial-correctness claim admits any panic or
abort, and a total-correctness claim forbids all of them. The contracts below
state when a panic may happen, when it must happen, and that every execution
(including the panicking and the diverging ones) is fault-free.

1. `AbortPolicy` and the outcome classifiers `PolicyOutcomeOk`,
   `PanicOutcomeOk`, `PanicAbortOutcomeOk`, and `ExactPolicyOutcome`.
2. Tree-level contracts over `Inp → ITree E (Outcome Val)`: `PanicsOnlyIf`,
   `PanicsIf`, `AbortsIf`, `FailsIf`, `ExactPanicContract`,
   `TotalExactPanicContract`, `NeverPanics`, and the policy-parameterized family
   `PanicsWithPolicyOnlyIf`, `PanicsOrAbortsOnlyIf`, `ExactPanicAbortContract`,
   `ExactPolicyPanicContract`, `TotalExactPolicyPanicContract`.
3. Captured-MIR tree families (`mirTrees`, `mirStatefulTrees`,
   `mirHandledTrees`) and bridges to `VerificationResult`,
   `StatefulVerificationResult`, `TotalVerificationResult`, and
   `ModularVerificationResult`.
4. Adequacy of `DWLP` / `DWP` and of the bounded evaluators of
   `Anneal.Rustc.V2026_06_01.Lower` for these contracts.
5. Panic call contracts (`PanicMirCallContract`), caller–callee composition
   through `linkCalleeHandler` (`panicsOnlyIf_call_compose`) and through the
   frame-restoring `linkCalleeWithCalleesHandler`, the memory a linked callee
   presents on unwind, and finite counterexample traces of a linked system
   (`ReachesLinkedFault`).
6. The runtime call-boundary guard `CalleeTableExcludes`, under which
   `evalTerminator` emits a `MirCallE` request instead of entering a callee
   body. The guard is established for initial states, used at each call
   terminator, and carried across the resumption of an external call whose
   contract has `withTraitsPreserved`. That the statements executed between two
   calls leave `callees` and `traitImpls` unchanged is not proved here.
7. The syntactic call-boundary guards `CallBoundaryPreserved`,
   `CalleesCallBoundaryPreserved`, and the counted `CallSitesPreserved`.
8. Transfer of the contracts across `CompilerPass`, `VerifierPass`, and
   `ExactPass`.
-/

universe u w w'

/-! ## 1. `AbortPolicy` and Outcome Classification -/

/--
How a contract treats a defined abort (`Outcome.abort`). There is no boolean
"aborts allowed" flag: an unconditional waiver has to be requested by name
(`waiveAbortUnchecked`), and a `-C panic=abort` contract states its abort
condition (`abortOnlyIf cond`).

Reference (The Rust Reference, "Panic"):
<https://doc.rust-lang.org/1.98.0/reference/panic.html>

> "There are two panic strategies defined by Rust: `unwind` and `abort`."
-/
inductive AbortPolicy (Ctx : Type w) : Type w where
  /-- No execution may abort. -/
  | forbidAbort : AbortPolicy Ctx
  /-- An execution from context `ctx` may abort only if `cond ctx`. -/
  | abortOnlyIf (cond : Ctx → Prop) : AbortPolicy Ctx
  /-- Every abort is accepted without any condition. -/
  | waiveAbortUnchecked : AbortPolicy Ctx

namespace AbortPolicy

variable {Ctx : Type w} {Ctx' : Type w'}

/-- Whether `policy` accepts an abort of an execution from context `ctx`. -/
def allowsAbort : AbortPolicy Ctx → Ctx → Prop
  | .forbidAbort, _ => False
  | .abortOnlyIf cond, ctx => cond ctx
  | .waiveAbortUnchecked, _ => True

theorem allowsAbort_forbidAbort (ctx : Ctx) :
    ¬ (forbidAbort : AbortPolicy Ctx).allowsAbort ctx :=
  fun h => h

@[simp]
theorem allowsAbort_abortOnlyIf (cond : Ctx → Prop) (ctx : Ctx) :
    (abortOnlyIf cond).allowsAbort ctx ↔ cond ctx :=
  Iff.rfl

theorem allowsAbort_waiveAbortUnchecked (ctx : Ctx) :
    (waiveAbortUnchecked : AbortPolicy Ctx).allowsAbort ctx :=
  trivial

/-- `p ≤ q` when every abort accepted by `p` is accepted by `q`. -/
instance : LE (AbortPolicy Ctx) where
  le p q := ∀ ctx, p.allowsAbort ctx → q.allowsAbort ctx

theorem le_iff (p q : AbortPolicy Ctx) :
    p ≤ q ↔ ∀ ctx, p.allowsAbort ctx → q.allowsAbort ctx :=
  Iff.rfl

/-- Equal policies are comparable; reflexivity is the case `h := rfl`. -/
theorem le_of_eq {p q : AbortPolicy Ctx} (h : p = q) : p ≤ q :=
  fun _ hp => h ▸ hp

theorem le_trans {p q r : AbortPolicy Ctx} (hpq : p ≤ q) (hqr : q ≤ r) : p ≤ r :=
  fun ctx h => hqr ctx (hpq ctx h)

/-- `forbidAbort` is the least policy. -/
theorem forbidAbort_le (p : AbortPolicy Ctx) : forbidAbort ≤ p :=
  fun _ h => False.elim h

/-- `waiveAbortUnchecked` is the greatest policy. -/
theorem le_waiveAbortUnchecked (p : AbortPolicy Ctx) : p ≤ waiveAbortUnchecked :=
  fun _ _ => trivial

theorem abortOnlyIf_le_abortOnlyIf_iff (c₁ c₂ : Ctx → Prop) :
    abortOnlyIf c₁ ≤ abortOnlyIf c₂ ↔ ∀ ctx, c₁ ctx → c₂ ctx :=
  Iff.rfl

/-- `abortOnlyIf cond` is as strict as `forbidAbort` exactly when `cond` never holds. -/
theorem abortOnlyIf_le_forbidAbort_iff (cond : Ctx → Prop) :
    abortOnlyIf cond ≤ forbidAbort ↔ ∀ ctx, ¬ cond ctx :=
  Iff.rfl

/-- The unconditional waiver is strictly weaker than `forbidAbort` on any inhabited context. -/
theorem not_waiveAbortUnchecked_le_forbidAbort (ctx : Ctx) :
    ¬ ((waiveAbortUnchecked : AbortPolicy Ctx) ≤ forbidAbort) :=
  fun h => h ctx trivial

/-- The unconditional waiver is weaker than `abortOnlyIf cond` unless `cond` always holds. -/
theorem waiveAbortUnchecked_le_abortOnlyIf_iff (cond : Ctx → Prop) :
    waiveAbortUnchecked ≤ abortOnlyIf cond ↔ ∀ ctx, cond ctx :=
  ⟨fun h ctx => h ctx trivial, fun h ctx _ => h ctx⟩

/-- Reindex a policy along `f : Ctx' → Ctx`. -/
def comap (f : Ctx' → Ctx) : AbortPolicy Ctx → AbortPolicy Ctx'
  | .forbidAbort => .forbidAbort
  | .abortOnlyIf cond => .abortOnlyIf (fun ctx => cond (f ctx))
  | .waiveAbortUnchecked => .waiveAbortUnchecked

@[simp]
theorem allowsAbort_comap (f : Ctx' → Ctx) (p : AbortPolicy Ctx) (ctx : Ctx') :
    (p.comap f).allowsAbort ctx ↔ p.allowsAbort (f ctx) := by
  cases p <;> exact Iff.rfl

end AbortPolicy

section OutcomeClassifiers

variable {Ctx : Type w} {Val : Type u}

/--
Outcome classifier of a policy-parameterized panic contract: a normal return
satisfies `post`, a panic implies `panicCond`, and an abort is accepted only as
far as `policy` allows it from `ctx`.
-/
def PolicyOutcomeOk (policy : AbortPolicy Ctx) (ctx : Ctx)
    (post : Val → Prop) (panicCond : Prop) : Outcome Val → Prop
  | .normal v => post v
  | .panic => panicCond
  | .abort => policy.allowsAbort ctx

/-- Outcome classifier of an unwinding panic contract: aborts are forbidden. -/
def PanicOutcomeOk (post : Val → Prop) (panicCond : Prop) : Outcome Val → Prop
  | .normal v => post v
  | .panic => panicCond
  | .abort => False

/-- Outcome classifier of a panic contract with an explicit abort condition. -/
def PanicAbortOutcomeOk (post : Val → Prop) (panicCond abortCond : Prop) :
    Outcome Val → Prop
  | .normal v => post v
  | .panic => panicCond
  | .abort => abortCond

/--
Exact outcome classifier: the kind of outcome is determined by `panicCond` and
by whether `policy` accepts an abort from `ctx`. A panic requires `panicCond`
and excludes the abort condition, an abort requires the abort condition and
excludes `panicCond`, and a normal return excludes both and satisfies `post`.
-/
def ExactPolicyOutcome (policy : AbortPolicy Ctx) (ctx : Ctx)
    (post : Val → Prop) (panicCond : Prop) : Outcome Val → Prop
  | .normal v => ¬ panicCond ∧ ¬ policy.allowsAbort ctx ∧ post v
  | .panic => panicCond ∧ ¬ policy.allowsAbort ctx
  | .abort => policy.allowsAbort ctx ∧ ¬ panicCond

/--
Exact outcome classifier of an unwinding panic contract: a panic requires
`panicCond`, a normal return excludes it and satisfies `post`, and aborts are
forbidden.
-/
def ExactPanicOutcome (post : Val → Prop) (panicCond : Prop) : Outcome Val → Prop
  | .normal v => ¬ panicCond ∧ post v
  | .panic => panicCond
  | .abort => False

theorem exactPolicyOutcome_forbidAbort_iff (ctx : Ctx) (post : Val → Prop)
    (panicCond : Prop) (out : Outcome Val) :
    ExactPolicyOutcome .forbidAbort ctx post panicCond out ↔
      ExactPanicOutcome post panicCond out := by
  cases out with
  | normal v => exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, fun ha => ha, h.2⟩⟩
  | panic => exact ⟨fun h => h.1, fun h => ⟨h, fun ha => ha⟩⟩
  | abort => exact ⟨fun h => h.1, fun h => False.elim h⟩

/-- An exactly classified outcome satisfies the unwinding only-if classifier. -/
theorem ExactPanicOutcome.toPanicOutcomeOk {post : Val → Prop} {panicCond : Prop}
    {out : Outcome Val} (h : ExactPanicOutcome post panicCond out) :
    PanicOutcomeOk post panicCond out := by
  cases out with
  | normal v => exact h.2
  | panic => exact h
  | abort => exact h

theorem policyOutcomeOk_forbidAbort_iff (ctx : Ctx) (post : Val → Prop)
    (panicCond : Prop) (out : Outcome Val) :
    PolicyOutcomeOk .forbidAbort ctx post panicCond out ↔
      PanicOutcomeOk post panicCond out := by
  cases out <;> exact Iff.rfl

theorem policyOutcomeOk_abortOnlyIf_iff (cond : Ctx → Prop) (ctx : Ctx)
    (post : Val → Prop) (panicCond : Prop) (out : Outcome Val) :
    PolicyOutcomeOk (.abortOnlyIf cond) ctx post panicCond out ↔
      PanicAbortOutcomeOk post panicCond (cond ctx) out := by
  cases out <;> exact Iff.rfl

/-- Under the unconditional waiver only normal returns and panics are constrained. -/
theorem policyOutcomeOk_waiveAbortUnchecked_iff (ctx : Ctx) (post : Val → Prop)
    (panicCond : Prop) (out : Outcome Val) :
    PolicyOutcomeOk .waiveAbortUnchecked ctx post panicCond out ↔
      (∀ v, out = .normal v → post v) ∧ (out = .panic → panicCond) := by
  cases out with
  | normal v =>
    exact ⟨fun h => ⟨fun v' hv => by cases hv; exact h, fun hv => nomatch hv⟩,
      fun h => h.1 v rfl⟩
  | panic =>
    exact ⟨fun h => ⟨fun _ hv => (nomatch hv), fun _ => h⟩, fun h => h.2 rfl⟩
  | abort =>
    exact ⟨fun _ => ⟨fun _ hv => (nomatch hv), fun hv => (nomatch hv)⟩, fun _ => trivial⟩

/-- `PolicyOutcomeOk` as a three-way case split on the outcome. -/
theorem policyOutcomeOk_iff (policy : AbortPolicy Ctx) (ctx : Ctx)
    (post : Val → Prop) (panicCond : Prop) (out : Outcome Val) :
    PolicyOutcomeOk policy ctx post panicCond out ↔
      (∃ v, out = .normal v ∧ post v) ∨ (out = .panic ∧ panicCond) ∨
        (out = .abort ∧ policy.allowsAbort ctx) := by
  cases out with
  | normal v =>
    refine ⟨fun h => Or.inl ⟨v, rfl, h⟩, ?_⟩
    rintro (⟨v', hv, hp⟩ | ⟨hv, _⟩ | ⟨hv, _⟩)
    · cases hv; exact hp
    · nomatch hv
    · nomatch hv
  | panic =>
    refine ⟨fun h => Or.inr (Or.inl ⟨rfl, h⟩), ?_⟩
    rintro (⟨_, hv, _⟩ | ⟨_, hp⟩ | ⟨hv, _⟩)
    · nomatch hv
    · exact hp
    · nomatch hv
  | abort =>
    refine ⟨fun h => Or.inr (Or.inr ⟨rfl, h⟩), ?_⟩
    rintro (⟨_, hv, _⟩ | ⟨hv, _⟩ | ⟨_, hp⟩)
    · nomatch hv
    · nomatch hv
    · exact hp

/-- `PanicOutcomeOk` as a two-way case split on the outcome. -/
theorem panicOutcomeOk_iff (post : Val → Prop) (panicCond : Prop) (out : Outcome Val) :
    PanicOutcomeOk post panicCond out ↔
      (∃ v, out = .normal v ∧ post v) ∨ (out = .panic ∧ panicCond) := by
  cases out with
  | normal v =>
    refine ⟨fun h => Or.inl ⟨v, rfl, h⟩, ?_⟩
    rintro (⟨v', hv, hp⟩ | ⟨hv, _⟩)
    · cases hv; exact hp
    · nomatch hv
  | panic =>
    refine ⟨fun h => Or.inr ⟨rfl, h⟩, ?_⟩
    rintro (⟨_, hv, _⟩ | ⟨_, hp⟩)
    · nomatch hv
    · exact hp
  | abort =>
    refine ⟨fun h => False.elim h, ?_⟩
    rintro (⟨_, hv, _⟩ | ⟨hv, _⟩)
    · nomatch hv
    · nomatch hv

/-- With an unsatisfiable panic condition only normal returns remain. -/
theorem panicOutcomeOk_false_iff (post : Val → Prop) (out : Outcome Val) :
    PanicOutcomeOk post False out ↔ ∃ v, out = .normal v ∧ post v := by
  rw [panicOutcomeOk_iff]
  exact ⟨fun h => h.elim id (fun h' => False.elim h'.2), Or.inl⟩

/-- `PolicyOutcomeOk` is monotone in `post`, `panicCond`, and the policy. -/
theorem PolicyOutcomeOk.mono {p q : AbortPolicy Ctx} {ctx : Ctx}
    {post post' : Val → Prop} {panicCond panicCond' : Prop} {out : Outcome Val}
    (hPolicy : p ≤ q) (hPost : ∀ v, post v → post' v)
    (hPanic : panicCond → panicCond')
    (h : PolicyOutcomeOk p ctx post panicCond out) :
    PolicyOutcomeOk q ctx post' panicCond' out := by
  cases out with
  | normal v => exact hPost v h
  | panic => exact hPanic h
  | abort => exact hPolicy ctx h

/-- `PanicOutcomeOk` is monotone in `post` and `panicCond`. -/
theorem PanicOutcomeOk.mono {post post' : Val → Prop} {panicCond panicCond' : Prop}
    {out : Outcome Val} (hPost : ∀ v, post v → post' v)
    (hPanic : panicCond → panicCond')
    (h : PanicOutcomeOk post panicCond out) :
    PanicOutcomeOk post' panicCond' out := by
  cases out with
  | normal v => exact hPost v h
  | panic => exact hPanic h
  | abort => exact h

/-- `PanicAbortOutcomeOk` is monotone in `post`, `panicCond`, and `abortCond`. -/
theorem PanicAbortOutcomeOk.mono {post post' : Val → Prop}
    {panicCond panicCond' abortCond abortCond' : Prop}
    {out : Outcome Val} (hPost : ∀ v, post v → post' v)
    (hPanic : panicCond → panicCond') (hAbort : abortCond → abortCond')
    (h : PanicAbortOutcomeOk post panicCond abortCond out) :
    PanicAbortOutcomeOk post' panicCond' abortCond' out := by
  cases out with
  | normal v => exact hPost v h
  | panic => exact hPanic h
  | abort => exact hAbort h

/-- An unwinding panic contract outcome is accepted under every abort policy. -/
theorem PanicOutcomeOk.toPolicy {post : Val → Prop} {panicCond : Prop}
    {out : Outcome Val} (policy : AbortPolicy Ctx) (ctx : Ctx)
    (h : PanicOutcomeOk post panicCond out) :
    PolicyOutcomeOk policy ctx post panicCond out :=
  PolicyOutcomeOk.mono (AbortPolicy.forbidAbort_le policy) (fun _ hv => hv) id
    ((policyOutcomeOk_forbidAbort_iff ctx post panicCond out).2 h)

/-- An exactly classified outcome satisfies the corresponding only-if classifier. -/
theorem ExactPolicyOutcome.toPolicyOutcomeOk {policy : AbortPolicy Ctx} {ctx : Ctx}
    {post : Val → Prop} {panicCond : Prop} {out : Outcome Val}
    (h : ExactPolicyOutcome policy ctx post panicCond out) :
    PolicyOutcomeOk policy ctx post panicCond out := by
  cases out with
  | normal v => exact h.2.2
  | panic => exact h.1
  | abort => exact h.1

/-- An exact classifier with `forbidAbort` never accepts an abort. -/
theorem not_exactPolicyOutcome_forbidAbort_abort (ctx : Ctx) (post : Val → Prop)
    (panicCond : Prop) :
    ¬ ExactPolicyOutcome .forbidAbort ctx post panicCond (.abort : Outcome Val) :=
  fun h => h.1

/-- An exact classifier with the unconditional waiver accepts neither a normal return nor a panic. -/
theorem exactPolicyOutcome_waiveAbortUnchecked_iff (ctx : Ctx) (post : Val → Prop)
    (panicCond : Prop) (out : Outcome Val) :
    ExactPolicyOutcome .waiveAbortUnchecked ctx post panicCond out ↔
      out = .abort ∧ ¬ panicCond := by
  cases out with
  | normal v => exact ⟨fun h => False.elim (h.2.1 trivial), fun h => nomatch h.1⟩
  | panic => exact ⟨fun h => False.elim (h.2 trivial), fun h => nomatch h.1⟩
  | abort => exact ⟨fun h => ⟨rfl, h.2⟩, fun h => ⟨trivial, h.2⟩⟩

/-- `ExactPolicyOutcome` as a three-way exclusive case split on the outcome. -/
theorem exactPolicyOutcome_iff (policy : AbortPolicy Ctx) (ctx : Ctx)
    (post : Val → Prop) (panicCond : Prop) (out : Outcome Val) :
    ExactPolicyOutcome policy ctx post panicCond out ↔
      (∃ v, out = .normal v ∧ ¬ panicCond ∧ ¬ policy.allowsAbort ctx ∧ post v) ∨
        (out = .panic ∧ panicCond ∧ ¬ policy.allowsAbort ctx) ∨
        (out = .abort ∧ policy.allowsAbort ctx ∧ ¬ panicCond) := by
  cases out with
  | normal v =>
    refine ⟨fun h => Or.inl ⟨v, rfl, h⟩, ?_⟩
    rintro (⟨v', hv, hp⟩ | ⟨hv, _⟩ | ⟨hv, _⟩)
    · cases hv; exact hp
    · nomatch hv
    · nomatch hv
  | panic =>
    refine ⟨fun h => Or.inr (Or.inl ⟨rfl, h⟩), ?_⟩
    rintro (⟨_, hv, _⟩ | ⟨_, hp⟩ | ⟨hv, _⟩)
    · nomatch hv
    · exact hp
    · nomatch hv
  | abort =>
    refine ⟨fun h => Or.inr (Or.inr ⟨rfl, h⟩), ?_⟩
    rintro (⟨_, hv, _⟩ | ⟨hv, _⟩ | ⟨_, hp⟩)
    · nomatch hv
    · nomatch hv
    · exact hp

/-- `ExactPanicOutcome` as a two-way exclusive case split on the outcome. -/
theorem exactPanicOutcome_iff (post : Val → Prop) (panicCond : Prop) (out : Outcome Val) :
    ExactPanicOutcome post panicCond out ↔
      (∃ v, out = .normal v ∧ ¬ panicCond ∧ post v) ∨ (out = .panic ∧ panicCond) := by
  cases out with
  | normal v =>
    refine ⟨fun h => Or.inl ⟨v, rfl, h⟩, ?_⟩
    rintro (⟨v', hv, hp⟩ | ⟨hv, _⟩)
    · cases hv; exact hp
    · nomatch hv
  | panic =>
    refine ⟨fun h => Or.inr ⟨rfl, h⟩, ?_⟩
    rintro (⟨_, hv, _⟩ | ⟨_, hp⟩)
    · nomatch hv
    · exact hp
  | abort =>
    refine ⟨fun h => False.elim h, ?_⟩
    rintro (⟨_, hv, _⟩ | ⟨hv, _⟩)
    · nomatch hv
    · nomatch hv

end OutcomeClassifiers

/-! ## 2. Tree-Level Panic Contracts -/

section TreeContracts

variable {E : Effect.{u}} [FaultEffect E] {R Val : Type u} {Inp : Type w}

/--
Fault freedom stated on requests: no residual reachable from `t` is a `.vis`
node whose request is a fault. For MIR effects the fault requests are exactly
`.fail .ub`, `.fail .unsupported`, and `.fail .outOfFuel`.
-/
def NoFault (t : ITree E R) : Prop :=
  ∀ tr u i k, Reaches t tr u → u.observe = .vis i k → ¬ FaultEffect.isFault i

/-- `TreeSafe` is fault freedom on every reachable request. -/
theorem treeSafe_iff_noFault (t : ITree E R) : TreeSafe t ↔ NoFault t := by
  constructor
  · intro hs tr u i k hr hobs hf
    exact hs tr u hr ⟨u, i, k, .refl u, hobs, hf⟩
  · rintro hn tr u hr ⟨u', i, k, htau, hobs, hf⟩
    exact hn (tr ++ []) u' i k (reaches_trans hr (Reaches.of_tauStar htau (.refl u')))
      hobs hf

/--
Policy-parameterized only-if panic contract. For every input `x` satisfying
`pre`, the tree `tree x` is fault-free on every reachable branch (the returning,
the panicking, and the diverging ones), every normal return satisfies `post x`,
every panic implies `panicCond x`, and every abort is accepted by `policy`.
-/
def PanicsWithPolicyOnlyIf (tree : Inp → ITree E (Outcome Val)) (pre : Inp → Prop)
    (post : Inp → Val → Prop) (panicCond : Inp → Prop) (policy : AbortPolicy Inp) :
    Prop :=
  ∀ x, pre x →
    TreeSafe (tree x) ∧
      ∀ tr out, ReachesRet (tree x) tr out →
        PolicyOutcomeOk policy x (post x) (panicCond x) out

/--
Only-if panic contract (`panics_only_if`). For every input `x` satisfying
`pre`, the tree `tree x` is fault-free on every reachable branch, no execution
aborts, every normal return satisfies `post x`, and every panic implies
`panicCond x`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Rust code is incorrect if it exhibits any of the behaviors in the following
> list. This includes code within unsafe blocks and unsafe functions."
-/
def PanicsOnlyIf (tree : Inp → ITree E (Outcome Val)) (pre : Inp → Prop)
    (post : Inp → Val → Prop) (panicCond : Inp → Prop) : Prop :=
  ∀ x, pre x →
    TreeSafe (tree x) ∧
      ∀ tr out, ReachesRet (tree x) tr out →
        PanicOutcomeOk (post x) (panicCond x) out

/--
Only-if panic contract with an explicit abort condition (`-C panic=abort`,
`UnwindAction.terminate`): as `PanicsOnlyIf`, except that an execution may abort
when `abortCond x`.
-/
def PanicsOrAbortsOnlyIf (tree : Inp → ITree E (Outcome Val)) (pre : Inp → Prop)
    (post : Inp → Val → Prop) (panicCond abortCond : Inp → Prop) : Prop :=
  ∀ x, pre x →
    TreeSafe (tree x) ∧
      ∀ tr out, ReachesRet (tree x) tr out →
        PanicAbortOutcomeOk (post x) (panicCond x) (abortCond x) out

/--
Panic trigger (`panics_if`): every input satisfying `pre` and `panicCond` has an
execution that reaches `.panic`. The witness is a completed trace, so a tree
that merely never diverges silently (a reactive loop of visible requests) does
not satisfy it.
-/
def PanicsIf (tree : Inp → ITree E (Outcome Val)) (pre panicCond : Inp → Prop) :
    Prop :=
  ∀ x, pre x → panicCond x → ∃ tr, ReachesRet (tree x) tr .panic

/-- Abort trigger: every input satisfying `pre` and `abortCond` has an execution that reaches `.abort`. -/
def AbortsIf (tree : Inp → ITree E (Outcome Val)) (pre abortCond : Inp → Prop) :
    Prop :=
  ∀ x, pre x → abortCond x → ∃ tr, ReachesRet (tree x) tr .abort

/--
Failure trigger independent of the panic strategy: every input satisfying `pre`
and `failCond` has an execution that reaches `.panic` or `.abort`.
-/
def FailsIf (tree : Inp → ITree E (Outcome Val)) (pre failCond : Inp → Prop) :
    Prop :=
  ∀ x, pre x → failCond x →
    ∃ tr, ReachesRet (tree x) tr .panic ∨ ReachesRet (tree x) tr .abort

/-- Return trigger: every input satisfying `pre` and `retCond` has an execution that returns normally. -/
def ReturnsIf (tree : Inp → ITree E (Outcome Val)) (pre retCond : Inp → Prop) :
    Prop :=
  ∀ x, pre x → retCond x → ∃ tr v, ReachesRet (tree x) tr (.normal v)

/-- `PanicsOnlyIf` with an unsatisfiable panic condition. -/
def NeverPanics (tree : Inp → ITree E (Outcome Val)) (pre : Inp → Prop)
    (post : Inp → Val → Prop) : Prop :=
  PanicsOnlyIf tree pre post (fun _ => False)

/-- Exact panic contract: `PanicsOnlyIf` together with `PanicsIf`. -/
def ExactPanicContract (tree : Inp → ITree E (Outcome Val)) (pre : Inp → Prop)
    (post : Inp → Val → Prop) (panicCond : Inp → Prop) : Prop :=
  PanicsOnlyIf tree pre post panicCond ∧ PanicsIf tree pre panicCond

/-- Exact panic-or-abort contract: `PanicsOrAbortsOnlyIf` with both triggers. -/
def ExactPanicAbortContract (tree : Inp → ITree E (Outcome Val)) (pre : Inp → Prop)
    (post : Inp → Val → Prop) (panicCond abortCond : Inp → Prop) : Prop :=
  PanicsOrAbortsOnlyIf tree pre post panicCond abortCond ∧
    PanicsIf tree pre panicCond ∧ AbortsIf tree pre abortCond

/--
Exact policy contract: `PanicsWithPolicyOnlyIf` together with the panic trigger
and the abort trigger of `policy`. With `waiveAbortUnchecked` the abort trigger
is unconditional, so every input satisfying `pre` must be able to abort.
-/
def ExactPolicyPanicContract (tree : Inp → ITree E (Outcome Val)) (pre : Inp → Prop)
    (post : Inp → Val → Prop) (panicCond : Inp → Prop) (policy : AbortPolicy Inp) :
    Prop :=
  PanicsWithPolicyOnlyIf tree pre post panicCond policy ∧
    PanicsIf tree pre panicCond ∧ AbortsIf tree pre policy.allowsAbort

/--
Termination on `pre`: every reachable residual stabilizes after finitely many
silent steps and no reachable residual diverges silently.
-/
def TerminatesOn (tree : Inp → ITree E (Outcome Val)) (pre : Inp → Prop) : Prop :=
  ∀ x, pre x → Productive (tree x) ∧ ¬ MayDiverge (tree x)

/--
Total exact panic contract: an `ExactPanicContract` whose executions terminate,
return normally on every input outside `panicCond`, and never return normally on
an input inside `panicCond`.
-/
structure TotalExactPanicContract (tree : Inp → ITree E (Outcome Val))
    (pre : Inp → Prop) (post : Inp → Val → Prop) (panicCond : Inp → Prop) :
    Prop where
  /-- The only-if contract and the panic trigger. -/
  exact : ExactPanicContract tree pre post panicCond
  /-- Executions on `pre` terminate. -/
  terminates : TerminatesOn tree pre
  /-- Inputs outside `panicCond` return normally. -/
  returnsIf : ReturnsIf tree pre (fun x => ¬ panicCond x)
  /-- Inputs inside `panicCond` never return normally. -/
  noReturnIfPanics :
    ∀ x, pre x → panicCond x → ∀ tr v, ¬ ReachesRet (tree x) tr (.normal v)

/--
Total exact policy contract: an `ExactPolicyPanicContract` whose executions
terminate, return normally on every input outside both the panic and the abort
condition, and whose every outcome is classified by `ExactPolicyOutcome`.
-/
structure TotalExactPolicyPanicContract (tree : Inp → ITree E (Outcome Val))
    (pre : Inp → Prop) (post : Inp → Val → Prop) (panicCond : Inp → Prop)
    (policy : AbortPolicy Inp) : Prop where
  /-- The only-if contract, the panic trigger, and the abort trigger. -/
  exact : ExactPolicyPanicContract tree pre post panicCond policy
  /-- Executions on `pre` terminate. -/
  terminates : TerminatesOn tree pre
  /-- Inputs outside both conditions return normally. -/
  returnsIf : ReturnsIf tree pre (fun x => ¬ panicCond x ∧ ¬ policy.allowsAbort x)
  /-- Every outcome has the kind its conditions determine. -/
  exclusive :
    ∀ x, pre x → ∀ tr out, ReachesRet (tree x) tr out →
      ExactPolicyOutcome policy x (post x) (panicCond x) out

variable {tree : Inp → ITree E (Outcome Val)} {pre : Inp → Prop}
  {post : Inp → Val → Prop} {panicCond abortCond : Inp → Prop}
  {policy : AbortPolicy Inp}

/-! ### Specialization of the policy family -/

/-- `PanicsWithPolicyOnlyIf` with `forbidAbort` is `PanicsOnlyIf`. -/
theorem panicsWithPolicyOnlyIf_forbidAbort_iff :
    PanicsWithPolicyOnlyIf tree pre post panicCond .forbidAbort ↔
      PanicsOnlyIf tree pre post panicCond := by
  constructor
  · intro h x hx
    exact ⟨(h x hx).1, fun tr out hr =>
      (policyOutcomeOk_forbidAbort_iff x (post x) (panicCond x) out).1 ((h x hx).2 tr out hr)⟩
  · intro h x hx
    exact ⟨(h x hx).1, fun tr out hr =>
      (policyOutcomeOk_forbidAbort_iff x (post x) (panicCond x) out).2 ((h x hx).2 tr out hr)⟩

/-- `PanicsWithPolicyOnlyIf` with `abortOnlyIf abortCond` is `PanicsOrAbortsOnlyIf`. -/
theorem panicsWithPolicyOnlyIf_abortOnlyIf_iff :
    PanicsWithPolicyOnlyIf tree pre post panicCond (.abortOnlyIf abortCond) ↔
      PanicsOrAbortsOnlyIf tree pre post panicCond abortCond := by
  constructor
  · intro h x hx
    exact ⟨(h x hx).1, fun tr out hr =>
      (policyOutcomeOk_abortOnlyIf_iff abortCond x (post x) (panicCond x) out).1
        ((h x hx).2 tr out hr)⟩
  · intro h x hx
    exact ⟨(h x hx).1, fun tr out hr =>
      (policyOutcomeOk_abortOnlyIf_iff abortCond x (post x) (panicCond x) out).2
        ((h x hx).2 tr out hr)⟩

/-- The abort trigger of `forbidAbort` holds of every tree family. -/
theorem abortsIf_forbidAbort (tree : Inp → ITree E (Outcome Val)) (pre : Inp → Prop) :
    AbortsIf tree pre (AbortPolicy.forbidAbort : AbortPolicy Inp).allowsAbort :=
  fun _ _ h => False.elim h

/-- `ExactPolicyPanicContract` with `forbidAbort` is `ExactPanicContract`. -/
theorem exactPolicyPanicContract_forbidAbort_iff :
    ExactPolicyPanicContract tree pre post panicCond .forbidAbort ↔
      ExactPanicContract tree pre post panicCond :=
  ⟨fun h => ⟨panicsWithPolicyOnlyIf_forbidAbort_iff.1 h.1, h.2.1⟩,
   fun h => ⟨panicsWithPolicyOnlyIf_forbidAbort_iff.2 h.1, h.2, abortsIf_forbidAbort tree pre⟩⟩

/-- `ExactPolicyPanicContract` with `abortOnlyIf abortCond` is `ExactPanicAbortContract`. -/
theorem exactPolicyPanicContract_abortOnlyIf_iff :
    ExactPolicyPanicContract tree pre post panicCond (.abortOnlyIf abortCond) ↔
      ExactPanicAbortContract tree pre post panicCond abortCond :=
  ⟨fun h => ⟨panicsWithPolicyOnlyIf_abortOnlyIf_iff.1 h.1, h.2.1, h.2.2⟩,
   fun h => ⟨panicsWithPolicyOnlyIf_abortOnlyIf_iff.2 h.1, h.2.1, h.2.2⟩⟩

/-! ### Monotonicity -/

/--
`PanicsWithPolicyOnlyIf` is antitone in `pre` and monotone in `post`,
`panicCond`, and the policy.
-/
theorem PanicsWithPolicyOnlyIf.mono {pre' : Inp → Prop} {post' : Inp → Val → Prop}
    {panicCond' : Inp → Prop} {policy' : AbortPolicy Inp}
    (hPre : ∀ x, pre' x → pre x)
    (hPost : ∀ x v, pre' x → post x v → post' x v)
    (hPanic : ∀ x, pre' x → panicCond x → panicCond' x)
    (hPolicy : policy ≤ policy')
    (h : PanicsWithPolicyOnlyIf tree pre post panicCond policy) :
    PanicsWithPolicyOnlyIf tree pre' post' panicCond' policy' :=
  fun x hx =>
    ⟨(h x (hPre x hx)).1, fun tr out hr =>
      PolicyOutcomeOk.mono hPolicy (fun v => hPost x v hx) (hPanic x hx)
        ((h x (hPre x hx)).2 tr out hr)⟩

/-- `PanicsOnlyIf` is antitone in `pre` and monotone in `post` and `panicCond`. -/
theorem PanicsOnlyIf.mono {pre' : Inp → Prop} {post' : Inp → Val → Prop}
    {panicCond' : Inp → Prop}
    (hPre : ∀ x, pre' x → pre x)
    (hPost : ∀ x v, pre' x → post x v → post' x v)
    (hPanic : ∀ x, pre' x → panicCond x → panicCond' x)
    (h : PanicsOnlyIf tree pre post panicCond) :
    PanicsOnlyIf tree pre' post' panicCond' :=
  fun x hx =>
    ⟨(h x (hPre x hx)).1, fun tr out hr =>
      PanicOutcomeOk.mono (fun v => hPost x v hx) (hPanic x hx)
        ((h x (hPre x hx)).2 tr out hr)⟩

/-- An unwinding only-if contract holds under every abort policy. -/
theorem PanicsOnlyIf.toPolicy (policy : AbortPolicy Inp)
    (h : PanicsOnlyIf tree pre post panicCond) :
    PanicsWithPolicyOnlyIf tree pre post panicCond policy :=
  PanicsWithPolicyOnlyIf.mono (fun _ hx => hx) (fun _ _ _ hv => hv) (fun _ _ hp => hp)
    (AbortPolicy.forbidAbort_le policy) (panicsWithPolicyOnlyIf_forbidAbort_iff.2 h)

/-- `PanicsIf` is antitone in both `pre` and `panicCond`. -/
theorem PanicsIf.mono {pre' panicCond' : Inp → Prop}
    (hPre : ∀ x, pre' x → pre x)
    (hPanic : ∀ x, pre' x → panicCond' x → panicCond x)
    (h : PanicsIf tree pre panicCond) :
    PanicsIf tree pre' panicCond' :=
  fun x hx hp => h x (hPre x hx) (hPanic x hx hp)

/-- `AbortsIf` is antitone in both `pre` and `abortCond`. -/
theorem AbortsIf.mono {pre' abortCond' : Inp → Prop}
    (hPre : ∀ x, pre' x → pre x)
    (hAbort : ∀ x, pre' x → abortCond' x → abortCond x)
    (h : AbortsIf tree pre abortCond) :
    AbortsIf tree pre' abortCond' :=
  fun x hx hp => h x (hPre x hx) (hAbort x hx hp)

/-! ### Consequences of the only-if contracts -/

theorem PanicsWithPolicyOnlyIf.treeSafe {x : Inp}
    (h : PanicsWithPolicyOnlyIf tree pre post panicCond policy) (hx : pre x) :
    TreeSafe (tree x) :=
  (h x hx).1

/-- No reachable request of a contracted tree is a fault. -/
theorem PanicsWithPolicyOnlyIf.noFault {x : Inp}
    (h : PanicsWithPolicyOnlyIf tree pre post panicCond policy) (hx : pre x) :
    NoFault (tree x) :=
  (treeSafe_iff_noFault (tree x)).1 (h x hx).1

theorem PanicsWithPolicyOnlyIf.post_of_returns {x : Inp} {tr : List (Event E)} {v : Val}
    (h : PanicsWithPolicyOnlyIf tree pre post panicCond policy) (hx : pre x)
    (hr : ReachesRet (tree x) tr (.normal v)) : post x v :=
  (h x hx).2 tr _ hr

theorem PanicsWithPolicyOnlyIf.panicCond_of_panics {x : Inp} {tr : List (Event E)}
    (h : PanicsWithPolicyOnlyIf tree pre post panicCond policy) (hx : pre x)
    (hr : ReachesRet (tree x) tr .panic) : panicCond x :=
  (h x hx).2 tr _ hr

theorem PanicsWithPolicyOnlyIf.allowsAbort_of_aborts {x : Inp} {tr : List (Event E)}
    (h : PanicsWithPolicyOnlyIf tree pre post panicCond policy) (hx : pre x)
    (hr : ReachesRet (tree x) tr .abort) : policy.allowsAbort x :=
  (h x hx).2 tr _ hr

theorem PanicsOnlyIf.treeSafe {x : Inp}
    (h : PanicsOnlyIf tree pre post panicCond) (hx : pre x) : TreeSafe (tree x) :=
  (h x hx).1

/-- No reachable request of a contracted tree is a fault. -/
theorem PanicsOnlyIf.noFault {x : Inp}
    (h : PanicsOnlyIf tree pre post panicCond) (hx : pre x) : NoFault (tree x) :=
  (treeSafe_iff_noFault (tree x)).1 (h x hx).1

theorem PanicsOnlyIf.post_of_returns {x : Inp} {tr : List (Event E)} {v : Val}
    (h : PanicsOnlyIf tree pre post panicCond) (hx : pre x)
    (hr : ReachesRet (tree x) tr (.normal v)) : post x v :=
  (h x hx).2 tr _ hr

theorem PanicsOnlyIf.panicCond_of_panics {x : Inp} {tr : List (Event E)}
    (h : PanicsOnlyIf tree pre post panicCond) (hx : pre x)
    (hr : ReachesRet (tree x) tr .panic) : panicCond x :=
  (h x hx).2 tr _ hr

/-- An unwinding only-if contract makes `.abort` unreachable. -/
theorem PanicsOnlyIf.not_reaches_abort {x : Inp} {tr : List (Event E)}
    (h : PanicsOnlyIf tree pre post panicCond) (hx : pre x) :
    ¬ ReachesRet (tree x) tr .abort :=
  fun hr => (h x hx).2 tr _ hr

/-! ### `NeverPanics` -/

/-- `NeverPanics` says that every completed execution returns normally and satisfies `post`. -/
theorem neverPanics_iff :
    NeverPanics tree pre post ↔
      ∀ x, pre x →
        TreeSafe (tree x) ∧
          ∀ tr out, ReachesRet (tree x) tr out → ∃ v, out = .normal v ∧ post x v := by
  constructor
  · intro h x hx
    exact ⟨(h x hx).1, fun tr out hr =>
      (panicOutcomeOk_false_iff (post x) out).1 ((h x hx).2 tr out hr)⟩
  · intro h x hx
    exact ⟨(h x hx).1, fun tr out hr =>
      (panicOutcomeOk_false_iff (post x) out).2 ((h x hx).2 tr out hr)⟩

/-- `NeverPanics` implies `PanicsOnlyIf` for every panic condition. -/
theorem NeverPanics.toPanicsOnlyIf (panicCond : Inp → Prop)
    (h : NeverPanics tree pre post) : PanicsOnlyIf tree pre post panicCond :=
  PanicsOnlyIf.mono (fun _ hx => hx) (fun _ _ _ hv => hv) (fun _ _ hp => False.elim hp) h

theorem NeverPanics.not_reaches_panic {x : Inp} {tr : List (Event E)}
    (h : NeverPanics tree pre post) (hx : pre x) :
    ¬ ReachesRet (tree x) tr .panic :=
  fun hr => (h x hx).2 tr _ hr

/-- When `panicCond` is unsatisfiable on `pre`, `PanicsOnlyIf` is `NeverPanics`. -/
theorem panicsOnlyIf_iff_neverPanics_of_not_panicCond
    (hNo : ∀ x, pre x → ¬ panicCond x) :
    PanicsOnlyIf tree pre post panicCond ↔ NeverPanics tree pre post :=
  ⟨PanicsOnlyIf.mono (fun _ hx => hx) (fun _ _ _ hv => hv) (fun x hx hp => hNo x hx hp),
   NeverPanics.toPanicsOnlyIf panicCond⟩

/-! ### Triggers -/

theorem PanicsIf.toFailsIf (h : PanicsIf tree pre panicCond) : FailsIf tree pre panicCond :=
  fun x hx hp => (h x hx hp).elim fun tr hr => ⟨tr, Or.inl hr⟩

theorem AbortsIf.toFailsIf (h : AbortsIf tree pre abortCond) : FailsIf tree pre abortCond :=
  fun x hx hp => (h x hx hp).elim fun tr hr => ⟨tr, Or.inr hr⟩

/-- A panic trigger and an abort trigger give a failure trigger for the union of the conditions. -/
theorem FailsIf.of_panicsIf_abortsIf (hp : PanicsIf tree pre panicCond)
    (ha : AbortsIf tree pre abortCond) :
    FailsIf tree pre (fun x => panicCond x ∨ abortCond x) :=
  fun x hx hc => hc.elim (hp.toFailsIf x hx) (ha.toFailsIf x hx)

/-- Under an unwinding only-if contract every failure is a panic. -/
theorem FailsIf.toPanicsIf {failCond : Inp → Prop}
    (hOnly : PanicsOnlyIf tree pre post panicCond) (h : FailsIf tree pre failCond) :
    PanicsIf tree pre failCond :=
  fun x hx hf => (h x hx hf).elim fun tr hr =>
    hr.elim (fun hp => ⟨tr, hp⟩) (fun ha => False.elim (hOnly.not_reaches_abort hx ha))

/-- A tree with no completed execution refutes every panic trigger that fires on it. -/
theorem not_panicsIf_of_no_reachesRet {x : Inp} (hx : pre x) (hp : panicCond x)
    (hNo : ∀ tr out, ¬ ReachesRet (tree x) tr out) :
    ¬ PanicsIf tree pre panicCond :=
  fun h => (h x hx hp).elim fun tr hr => hNo tr _ hr

/-- A panic trigger that fires on some input contradicts `NeverPanics`. -/
theorem not_panicsIf_of_neverPanics {x : Inp} (hx : pre x) (hp : panicCond x)
    (hNever : NeverPanics tree pre post) :
    ¬ PanicsIf tree pre panicCond :=
  fun h => (h x hx hp).elim fun _ hr => hNever.not_reaches_panic hx hr

/-! ### Reactive self-loops -/

section ReactiveLoop

variable {S : Type u} {step : S → ITreeF E R S} {st : S} {i : E.I}

omit [FaultEffect E] in
private theorem observe_cofix_selfLoop (hStep : step st = .vis i (fun _ => st)) :
    (ITree.cofix step st).observe = .vis i (fun _ => ITree.cofix step st) := by
  rw [ITree.observe_cofix, hStep]
  rfl

/--
A coalgebra state whose step is a visible request that returns to the same state
unfolds to a reactive loop: every residual reachable from it is the loop itself.
-/
theorem reaches_cofix_selfLoop (hStep : step st = .vis i (fun _ => st))
    {tr : List (Event E)} {u : ITree E R} (h : Reaches (ITree.cofix step st) tr u) :
    u = ITree.cofix step st := by
  generalize hT : ITree.cofix step st = t at h
  induction h with
  | refl => rfl
  | tau hTau _ _ =>
    rw [← hT, observe_cofix_selfLoop hStep] at hTau
    nomatch hTau
  | vis hVis _ o _ ih =>
    rw [← hT, observe_cofix_selfLoop hStep] at hVis
    injection hVis with hi hk
    subst hi
    have hk' := eq_of_heq hk
    subst hk'
    exact (ih rfl).trans hT

/-- A reactive self-loop is productive: it never takes a silent step. -/
theorem productive_cofix_selfLoop (hStep : step st = .vis i (fun _ => st)) :
    Productive (ITree.cofix step st) := by
  intro tr u hr
  rw [reaches_cofix_selfLoop hStep hr]
  refine ⟨_, .refl _, fun w hw => ?_⟩
  rw [observe_cofix_selfLoop hStep] at hw
  nomatch hw

/-- A reactive self-loop never diverges silently. -/
theorem not_mayDiverge_cofix_selfLoop (hStep : step st = .vis i (fun _ => st)) :
    ¬ MayDiverge (ITree.cofix step st) :=
  productive_not_mayDiverge (productive_cofix_selfLoop hStep)

/-- A reactive self-loop has no completed execution. -/
theorem not_reachesRet_cofix_selfLoop (hStep : step st = .vis i (fun _ => st))
    (tr : List (Event E)) (r : R) : ¬ ReachesRet (ITree.cofix step st) tr r := by
  rintro ⟨u, hr, hu⟩
  rw [reaches_cofix_selfLoop hStep hr, observe_cofix_selfLoop hStep] at hu
  nomatch hu

end ReactiveLoop

/--
Productivity and absence of silent divergence do not imply a panic trigger: a
tree family that is a reactive self-loop on some input satisfying `pre` and
`panicCond` is productive and never diverges there, yet refutes `PanicsIf`. This
is why the triggers ask for a completed trace.
-/
theorem not_panicsIf_of_selfLoop {S : Type u} {step : S → ITreeF E (Outcome Val) S}
    {st : S} {i : E.I} {x : Inp}
    (hTree : tree x = ITree.cofix step st) (hStep : step st = .vis i (fun _ => st))
    (hx : pre x) (hp : panicCond x) :
    Productive (tree x) ∧ ¬ MayDiverge (tree x) ∧ ¬ PanicsIf tree pre panicCond :=
  ⟨hTree ▸ productive_cofix_selfLoop hStep, hTree ▸ not_mayDiverge_cofix_selfLoop hStep,
    not_panicsIf_of_no_reachesRet hx hp fun tr out hr =>
      not_reachesRet_cofix_selfLoop hStep tr out (hTree ▸ hr)⟩

/-! ### Exact contracts -/

/-- Under an exact contract, `panicCond` holds exactly on the inputs that can panic. -/
theorem ExactPanicContract.panics_iff {x : Inp}
    (h : ExactPanicContract tree pre post panicCond) (hx : pre x) :
    panicCond x ↔ ∃ tr, ReachesRet (tree x) tr .panic :=
  ⟨h.2 x hx, fun ⟨_, hr⟩ => h.1.panicCond_of_panics hx hr⟩

/-- An exact contract with an unsatisfiable panic condition is `NeverPanics`. -/
theorem exactPanicContract_false_iff :
    ExactPanicContract tree pre post (fun _ => False) ↔ NeverPanics tree pre post :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ _ hp => False.elim hp⟩⟩

theorem ExactPanicAbortContract.panics_iff {x : Inp}
    (h : ExactPanicAbortContract tree pre post panicCond abortCond) (hx : pre x) :
    panicCond x ↔ ∃ tr, ReachesRet (tree x) tr .panic :=
  ⟨h.2.1 x hx, fun ⟨tr, hr⟩ => (h.1 x hx).2 tr _ hr⟩

theorem ExactPanicAbortContract.aborts_iff {x : Inp}
    (h : ExactPanicAbortContract tree pre post panicCond abortCond) (hx : pre x) :
    abortCond x ↔ ∃ tr, ReachesRet (tree x) tr .abort :=
  ⟨h.2.2 x hx, fun ⟨tr, hr⟩ => (h.1 x hx).2 tr _ hr⟩

theorem ExactPolicyPanicContract.panics_iff {x : Inp}
    (h : ExactPolicyPanicContract tree pre post panicCond policy) (hx : pre x) :
    panicCond x ↔ ∃ tr, ReachesRet (tree x) tr .panic :=
  ⟨h.2.1 x hx, fun ⟨_, hr⟩ => h.1.panicCond_of_panics hx hr⟩

theorem ExactPolicyPanicContract.aborts_iff {x : Inp}
    (h : ExactPolicyPanicContract tree pre post panicCond policy) (hx : pre x) :
    policy.allowsAbort x ↔ ∃ tr, ReachesRet (tree x) tr .abort :=
  ⟨h.2.2 x hx, fun ⟨_, hr⟩ => h.1.allowsAbort_of_aborts hx hr⟩

/-! ### Outcome determinism and mutual exclusion of the conditions -/

/-- All completed executions of `t` return the same value. -/
def DeterministicRet (t : ITree E R) : Prop :=
  ∀ tr₁ tr₂ r₁ r₂, ReachesRet t tr₁ r₁ → ReachesRet t tr₂ r₂ → r₁ = r₂

/--
On a tree with deterministic outcomes, an exact panic-or-abort contract makes
`panicCond` and `abortCond` mutually exclusive on `pre`.
-/
theorem ExactPanicAbortContract.conds_disjoint_of_deterministic {x : Inp}
    (h : ExactPanicAbortContract tree pre post panicCond abortCond) (hx : pre x)
    (hDet : DeterministicRet (tree x)) :
    ¬ (panicCond x ∧ abortCond x) := by
  rintro ⟨hp, ha⟩
  obtain ⟨tr₁, hr₁⟩ := h.2.1 x hx hp
  obtain ⟨tr₂, hr₂⟩ := h.2.2 x hx ha
  exact nomatch hDet tr₁ tr₂ _ _ hr₁ hr₂

/--
On a tree with deterministic outcomes, an exact policy contract makes
`panicCond` and the abort condition of the policy mutually exclusive on `pre`.
-/
theorem ExactPolicyPanicContract.conds_disjoint_of_deterministic {x : Inp}
    (h : ExactPolicyPanicContract tree pre post panicCond policy) (hx : pre x)
    (hDet : DeterministicRet (tree x)) :
    ¬ (panicCond x ∧ policy.allowsAbort x) := by
  rintro ⟨hp, ha⟩
  obtain ⟨tr₁, hr₁⟩ := h.2.1 x hx hp
  obtain ⟨tr₂, hr₂⟩ := h.2.2 x hx ha
  exact nomatch hDet tr₁ tr₂ _ _ hr₁ hr₂

/--
The unconditional waiver is incompatible with normal returns in an exact
contract: on a tree with deterministic outcomes, an exact policy contract with
`waiveAbortUnchecked` has no normally returning execution on `pre`.
-/
theorem ExactPolicyPanicContract.not_returns_of_waiveAbortUnchecked {x : Inp}
    {tr : List (Event E)} {v : Val}
    (h : ExactPolicyPanicContract tree pre post panicCond .waiveAbortUnchecked)
    (hx : pre x) (hDet : DeterministicRet (tree x)) :
    ¬ ReachesRet (tree x) tr (.normal v) := by
  intro hr
  obtain ⟨tr₂, hr₂⟩ := h.2.2 x hx trivial
  exact nomatch hDet tr tr₂ _ _ hr hr₂

/--
On a tree with deterministic outcomes, an exact policy contract with
`waiveAbortUnchecked` forces `panicCond` to be unsatisfiable on `pre`.
-/
theorem ExactPolicyPanicContract.not_panicCond_of_waiveAbortUnchecked {x : Inp}
    (h : ExactPolicyPanicContract tree pre post panicCond .waiveAbortUnchecked)
    (hx : pre x) (hDet : DeterministicRet (tree x)) :
    ¬ panicCond x :=
  fun hp => h.conds_disjoint_of_deterministic hx hDet ⟨hp, trivial⟩

/-- On a tree with deterministic outcomes, an input inside `panicCond` never returns normally. -/
theorem ExactPanicContract.not_returns_of_panicCond {x : Inp} {tr : List (Event E)}
    {v : Val} (h : ExactPanicContract tree pre post panicCond) (hx : pre x)
    (hp : panicCond x) (hDet : DeterministicRet (tree x)) :
    ¬ ReachesRet (tree x) tr (.normal v) := by
  intro hr
  obtain ⟨tr₂, hr₂⟩ := h.2 x hx hp
  exact nomatch hDet tr tr₂ _ _ hr hr₂

/--
An exact contract on trees with deterministic outcomes is total once its
executions terminate and inputs outside `panicCond` return.
-/
theorem TotalExactPanicContract.of_deterministic
    (h : ExactPanicContract tree pre post panicCond)
    (hTerm : TerminatesOn tree pre)
    (hRet : ReturnsIf tree pre (fun x => ¬ panicCond x))
    (hDet : ∀ x, pre x → DeterministicRet (tree x)) :
    TotalExactPanicContract tree pre post panicCond :=
  ⟨h, hTerm, hRet, fun x hx hp _ _ => h.not_returns_of_panicCond hx hp (hDet x hx)⟩

/-! ### Total exact contracts -/

/-- Under a total exact contract, `panicCond` holds exactly on the inputs that can panic. -/
theorem TotalExactPanicContract.panics_iff {x : Inp}
    (h : TotalExactPanicContract tree pre post panicCond) (hx : pre x) :
    panicCond x ↔ ∃ tr, ReachesRet (tree x) tr .panic :=
  h.exact.panics_iff hx

/--
Under a total exact contract, `panicCond` fails exactly on the inputs that can
return normally, and every such return satisfies `post`.
-/
theorem TotalExactPanicContract.returns_iff {x : Inp}
    (h : TotalExactPanicContract tree pre post panicCond) (hx : pre x) :
    ¬ panicCond x ↔ ∃ tr v, ReachesRet (tree x) tr (.normal v) ∧ post x v := by
  constructor
  · intro hnp
    obtain ⟨tr, v, hr⟩ := h.returnsIf x hx hnp
    exact ⟨tr, v, hr, h.exact.1.post_of_returns hx hr⟩
  · rintro ⟨tr, v, hr, _⟩ hp
    exact h.noReturnIfPanics x hx hp tr v hr

/-- Under a total exact contract every completed execution has the kind `panicCond` determines. -/
theorem TotalExactPanicContract.outcome_eq {x : Inp} {tr : List (Event E)}
    {out : Outcome Val}
    (h : TotalExactPanicContract tree pre post panicCond) (hx : pre x)
    (hr : ReachesRet (tree x) tr out) :
    (panicCond x ∧ out = .panic) ∨ (¬ panicCond x ∧ ∃ v, out = .normal v ∧ post x v) := by
  cases out with
  | normal v =>
    exact Or.inr ⟨fun hp => h.noReturnIfPanics x hx hp tr v hr, v, rfl,
      h.exact.1.post_of_returns hx hr⟩
  | panic => exact Or.inl ⟨h.exact.1.panicCond_of_panics hx hr, rfl⟩
  | abort => exact False.elim (h.exact.1.not_reaches_abort hx hr)

/-- The total exact policy contract with `forbidAbort` is the total exact panic contract. -/
theorem totalExactPolicyPanicContract_forbidAbort_iff :
    TotalExactPolicyPanicContract tree pre post panicCond .forbidAbort ↔
      TotalExactPanicContract tree pre post panicCond := by
  constructor
  · intro h
    refine ⟨exactPolicyPanicContract_forbidAbort_iff.1 h.exact, h.terminates,
      fun x hx hnp => h.returnsIf x hx ⟨hnp, fun ha => ha⟩, fun x hx hp tr v hr => ?_⟩
    exact (h.exclusive x hx tr _ hr).1 hp
  · intro h
    refine ⟨exactPolicyPanicContract_forbidAbort_iff.2 h.exact, h.terminates,
      fun x hx hc => h.returnsIf x hx hc.1, fun x hx tr out hr => ?_⟩
    cases out with
    | normal v =>
      exact ⟨fun hp => h.noReturnIfPanics x hx hp tr v hr, fun ha => ha,
        h.exact.1.post_of_returns hx hr⟩
    | panic => exact ⟨h.exact.1.panicCond_of_panics hx hr, fun ha => ha⟩
    | abort => exact False.elim (h.exact.1.not_reaches_abort hx hr)

theorem TotalExactPolicyPanicContract.panics_iff {x : Inp}
    (h : TotalExactPolicyPanicContract tree pre post panicCond policy) (hx : pre x) :
    panicCond x ↔ ∃ tr, ReachesRet (tree x) tr .panic :=
  h.exact.panics_iff hx

theorem TotalExactPolicyPanicContract.aborts_iff {x : Inp}
    (h : TotalExactPolicyPanicContract tree pre post panicCond policy) (hx : pre x) :
    policy.allowsAbort x ↔ ∃ tr, ReachesRet (tree x) tr .abort :=
  h.exact.aborts_iff hx

/--
Under a total exact policy contract, the inputs outside both conditions are
exactly the inputs that can return normally, and every such return satisfies
`post`.
-/
theorem TotalExactPolicyPanicContract.returns_iff {x : Inp}
    (h : TotalExactPolicyPanicContract tree pre post panicCond policy) (hx : pre x) :
    (¬ panicCond x ∧ ¬ policy.allowsAbort x) ↔
      ∃ tr v, ReachesRet (tree x) tr (.normal v) ∧ post x v := by
  constructor
  · intro hc
    obtain ⟨tr, v, hr⟩ := h.returnsIf x hx hc
    exact ⟨tr, v, hr, h.exact.1.post_of_returns hx hr⟩
  · rintro ⟨tr, v, hr, _⟩
    exact ⟨(h.exclusive x hx tr _ hr).1, (h.exclusive x hx tr _ hr).2.1⟩

/--
A total exact policy contract makes `panicCond` and the abort condition of the
policy mutually exclusive on `pre`, without any determinism assumption.
-/
theorem TotalExactPolicyPanicContract.conds_disjoint {x : Inp}
    (h : TotalExactPolicyPanicContract tree pre post panicCond policy) (hx : pre x) :
    ¬ (panicCond x ∧ policy.allowsAbort x) := by
  rintro ⟨hp, ha⟩
  obtain ⟨tr, hr⟩ := h.exact.2.1 x hx hp
  exact (h.exclusive x hx tr _ hr).2 ha

/--
The unconditional waiver is incompatible with normal returns: a total exact
policy contract with `waiveAbortUnchecked` has no normally returning execution
on `pre`.
-/
theorem TotalExactPolicyPanicContract.not_returns_of_waiveAbortUnchecked {x : Inp}
    {tr : List (Event E)} {v : Val}
    (h : TotalExactPolicyPanicContract tree pre post panicCond .waiveAbortUnchecked)
    (hx : pre x) :
    ¬ ReachesRet (tree x) tr (.normal v) :=
  fun hr => (h.exclusive x hx tr _ hr).2.1 trivial

/-- A total exact policy contract with `waiveAbortUnchecked` aborts on every input in `pre`. -/
theorem TotalExactPolicyPanicContract.outcome_eq_abort_of_waiveAbortUnchecked {x : Inp}
    {tr : List (Event E)} {out : Outcome Val}
    (h : TotalExactPolicyPanicContract tree pre post panicCond .waiveAbortUnchecked)
    (hx : pre x) (hr : ReachesRet (tree x) tr out) :
    out = .abort :=
  ((exactPolicyOutcome_waiveAbortUnchecked_iff x (post x) (panicCond x) out).1
    (h.exclusive x hx tr out hr)).1

/--
Under a total exact panic contract, every input satisfying `pre` has at least
one completed execution, and its outcome matches `ExactPanicOutcome`.
-/
theorem TotalExactPanicContract.reaches_outcome {x : Inp}
    (h : TotalExactPanicContract tree pre post panicCond) (hx : pre x) :
    ∃ tr out, ReachesRet (tree x) tr out ∧ ExactPanicOutcome (post x) (panicCond x) out := by
  by_cases hp : panicCond x
  · obtain ⟨tr, hr⟩ := h.exact.2 x hx hp
    exact ⟨tr, .panic, hr, hp⟩
  · obtain ⟨tr, v, hr⟩ := h.returnsIf x hx hp
    exact ⟨tr, .normal v, hr, hp, h.exact.1.post_of_returns hx hr⟩

/--
Under a total exact policy contract, every completed execution has the outcome
kind determined by `panicCond` and `policy` (three-way exclusive trichotomy).
-/
theorem TotalExactPolicyPanicContract.outcome_eq {x : Inp} {tr : List (Event E)}
    {out : Outcome Val}
    (h : TotalExactPolicyPanicContract tree pre post panicCond policy) (hx : pre x)
    (hr : ReachesRet (tree x) tr out) :
    (panicCond x ∧ ¬ policy.allowsAbort x ∧ out = .panic) ∨
      (policy.allowsAbort x ∧ ¬ panicCond x ∧ out = .abort) ∨
      (¬ panicCond x ∧ ¬ policy.allowsAbort x ∧ ∃ v, out = .normal v ∧ post x v) := by
  have hEx := h.exclusive x hx tr out hr
  cases out with
  | normal v => exact Or.inr (Or.inr ⟨hEx.1, hEx.2.1, v, rfl, hEx.2.2⟩)
  | panic => exact Or.inl ⟨hEx.1, hEx.2, rfl⟩
  | abort => exact Or.inr (Or.inl ⟨hEx.1, hEx.2, rfl⟩)

/--
Under a total exact policy contract, every input satisfying `pre` has at least
one completed execution, and its outcome matches `ExactPolicyOutcome`.
-/
theorem TotalExactPolicyPanicContract.reaches_outcome {x : Inp}
    (h : TotalExactPolicyPanicContract tree pre post panicCond policy) (hx : pre x) :
    ∃ tr out, ReachesRet (tree x) tr out ∧
      ExactPolicyOutcome policy x (post x) (panicCond x) out := by
  by_cases hp : panicCond x
  · obtain ⟨tr, hr⟩ := h.exact.2.1 x hx hp
    exact ⟨tr, .panic, hr, h.exclusive x hx tr _ hr⟩
  · by_cases ha : policy.allowsAbort x
    · obtain ⟨tr, hr⟩ := h.exact.2.2 x hx ha
      exact ⟨tr, .abort, hr, h.exclusive x hx tr _ hr⟩
    · obtain ⟨tr, v, hr⟩ := h.returnsIf x hx ⟨hp, ha⟩
      exact ⟨tr, .normal v, hr, h.exclusive x hx tr _ hr⟩

/--
An exact policy contract on trees with deterministic outcomes is total once its
executions terminate and inputs outside both conditions return normally.
-/
theorem TotalExactPolicyPanicContract.of_deterministic
    (h : ExactPolicyPanicContract tree pre post panicCond policy)
    (hTerm : TerminatesOn tree pre)
    (hRet : ReturnsIf tree pre (fun x => ¬ panicCond x ∧ ¬ policy.allowsAbort x))
    (hDet : ∀ x, pre x → DeterministicRet (tree x)) :
    TotalExactPolicyPanicContract tree pre post panicCond policy := by
  refine ⟨h, hTerm, hRet, fun x hx tr out hr => ?_⟩
  cases out with
  | normal v =>
    refine ⟨?_, ?_, h.1.post_of_returns hx hr⟩
    · intro hp
      obtain ⟨tr', hr'⟩ := h.2.1 x hx hp
      exact nomatch hDet x hx tr tr' _ _ hr hr'
    · intro ha
      obtain ⟨tr', hr'⟩ := h.2.2 x hx ha
      exact nomatch hDet x hx tr tr' _ _ hr hr'
  | panic =>
    refine ⟨h.1.panicCond_of_panics hx hr, fun ha => ?_⟩
    exact h.conds_disjoint_of_deterministic hx (hDet x hx) ⟨h.1.panicCond_of_panics hx hr, ha⟩
  | abort =>
    refine ⟨h.1.allowsAbort_of_aborts hx hr, fun hp => ?_⟩
    exact h.conds_disjoint_of_deterministic hx (hDet x hx) ⟨hp, h.1.allowsAbort_of_aborts hx hr⟩

end TreeContracts

/-! ### Effects with deterministic answers -/

section Determinism

variable {E : Effect.{u}} [FaultEffect E] {R : Type u}

/--
Every non-fault request of `E` has at most one answer, so a tree over `E` has
no environment nondeterminism.
-/
class DeterministicAnswers (E : Effect.{u}) [FaultEffect E] : Prop where
  /-- Any two answers to a non-fault request coincide. -/
  answer_unique : ∀ (i : E.I), ¬ FaultEffect.isFault i → ∀ o₁ o₂ : E.O i, o₁ = o₂

private theorem reaches_ret_unique [DeterministicAnswers E]
    {t u₁ u₂ : ITree E R} {tr₁ tr₂ : List (Event E)} {r₁ r₂ : R}
    (h₁ : Reaches t tr₁ u₁) (hr₁ : u₁.observe = .ret r₁)
    (h₂ : Reaches t tr₂ u₂) (hr₂ : u₂.observe = .ret r₂) : r₁ = r₂ := by
  induction h₁ generalizing tr₂ u₂ with
  | refl t =>
    cases h₂ with
    | refl => rw [hr₁] at hr₂; injection hr₂
    | tau ht _ => rw [hr₁] at ht; nomatch ht
    | vis hv _ _ _ => rw [hr₁] at hv; nomatch hv
  | tau ht _ ih =>
    cases h₂ with
    | refl => rw [ht] at hr₂; nomatch hr₂
    | tau ht₂ hrest =>
      rw [ht] at ht₂; injection ht₂ with heq; subst heq
      exact ih hr₁ hrest hr₂
    | vis hv _ _ _ => rw [ht] at hv; nomatch hv
  | vis hv hnf o _ ih =>
    cases h₂ with
    | refl => rw [hv] at hr₂; nomatch hr₂
    | tau ht₂ _ => rw [hv] at ht₂; nomatch ht₂
    | vis hv₂ _ o₂ hrest =>
      rw [hv] at hv₂
      injection hv₂ with hi hk
      subst hi
      have hk' := eq_of_heq hk
      subst hk'
      have ho : o = o₂ := DeterministicAnswers.answer_unique _ hnf o o₂
      subst ho
      exact ih hr₁ hrest hr₂

/-- Over an effect with deterministic answers every tree has deterministic outcomes. -/
theorem deterministicRet_of_deterministicAnswers [DeterministicAnswers E]
    (t : ITree E R) : DeterministicRet t :=
  fun _ _ _ _ ⟨_, h₁, hr₁⟩ ⟨_, h₂, hr₂⟩ => reaches_ret_unique h₁ hr₁ h₂ hr₂

end Determinism

private theorem reaches_ret_unique_of_dwlp_mirNoCallWP {R : Type}
    {t u₁ u₂ : ITree MirEffect R} {tr₁ tr₂ : List (Event MirEffect)} {r₁ r₂ : R}
    (hD : DWLP mirNoCallWP t (fun _ _ => True) PUnit.unit)
    (h₁ : Reaches t tr₁ u₁) (hr₁ : u₁.observe = .ret r₁)
    (h₂ : Reaches t tr₂ u₂) (hr₂ : u₂.observe = .ret r₂) : r₁ = r₂ := by
  induction h₁ generalizing tr₂ u₂ with
  | refl t =>
    cases h₂ with
    | refl => rw [hr₁] at hr₂; injection hr₂
    | tau ht _ => rw [hr₁] at ht; nomatch ht
    | vis hv _ _ _ => rw [hr₁] at hv; nomatch hv
  | tau ht _ ih =>
    rw [DWLP.unfold_eq, ht] at hD
    cases h₂ with
    | refl => rw [ht] at hr₂; nomatch hr₂
    | tau ht₂ hrest =>
      rw [ht] at ht₂; injection ht₂ with heq; subst heq
      exact ih hD hr₁ hrest hr₂
    | vis hv _ _ _ => rw [ht] at hv; nomatch hv
  | @vis x _ i k _ hv hnf o _ ih =>
    rw [DWLP.unfold_eq, hv] at hD
    cases h₂ with
    | refl => rw [hv] at hr₂; nomatch hr₂
    | tau ht₂ _ => rw [hv] at ht₂; nomatch ht₂
    | vis hv₂ _ o₂ hrest =>
      rw [hv] at hv₂
      injection hv₂ with hi hk
      subst hi
      have hk' := eq_of_heq hk
      subst hk'
      cases i with
      | inl _ => exact False.elim hD
      | inr i' =>
        cases i' with
        | inr _ => exact False.elim hD
        | inl obs =>
          cases obs with
          | emit _ =>
            cases o
            cases o₂
            exact ih hD hr₁ hrest hr₂

/--
A call-free `MirEffect` tree (one satisfying `DWLP mirNoCallWP`) has
deterministic outcomes: every reachable visible step is a `MirObsE` observation
whose answer is `PUnit.unit`.
-/
theorem deterministicRet_of_dwlp_mirNoCallWP {R : Type} {t : ITree MirEffect R}
    {Q : R → PUnit → Prop} (hD : DWLP mirNoCallWP t Q PUnit.unit) :
    DeterministicRet t :=
  fun _ _ _ _ ⟨_, h₁, hr₁⟩ ⟨_, h₂, hr₂⟩ =>
    reaches_ret_unique_of_dwlp_mirNoCallWP (DWLP.mono (fun _ _ _ => trivial) hD)
      h₁ hr₁ h₂ hr₂

/-- `MirClosedEffect` has deterministic answers: faults have none and observations answer `()`. -/
instance : DeterministicAnswers MirClosedEffect where
  answer_unique
    | .inl _, hnf, _, _ => False.elim (hnf trivial)
    | .inr (.emit _), _, .unit, .unit => rfl

/-- Every non-fault request of `MirEffect` has an answer. -/
theorem mirEffect_nonFault_nonempty :
    ∀ i : MirEffect.I, ¬ FaultEffect.isFault i → Nonempty (MirEffect.O i)
  | .inl _, hnf => False.elim (hnf trivial)
  | .inr (.inl (.emit _)), _ => ⟨PUnit.unit⟩
  | .inr (.inr (.call _)), _ => ⟨MirCallAns.aborted⟩

/-- Every non-fault request of `MirClosedEffect` has an answer. -/
theorem mirClosedEffect_nonFault_nonempty :
    ∀ i : MirClosedEffect.I, ¬ FaultEffect.isFault i → Nonempty (MirClosedEffect.O i)
  | .inl _, hnf => False.elim (hnf trivial)
  | .inr (.emit _), _ => ⟨PUnit.unit⟩

/--
`NoFault` on a `MirEffect` tree: no reachable residual is a `.fail` request of
any `FailureKind` (`.ub`, `.unsupported`, or `.outOfFuel`).
-/
theorem mir_noFault_iff {R : Type} (t : ITree MirEffect R) :
    NoFault t ↔
      ∀ tr u (fk : FailureKind) k, Reaches t tr u →
        u.observe ≠ .vis (.inl (.fail fk)) k := by
  constructor
  · intro h tr u fk k hr hobs
    exact h tr u _ k hr hobs trivial
  · intro h tr u i k hr hobs hf
    match i, k, hobs, hf with
    | .inl (.fail fk), k, hobs, _ => exact h tr u fk k hr hobs
    | .inr (.inl _), _, _, hf => exact hf
    | .inr (.inr _), _, _, hf => exact hf

/--
`NoFault` on a `MirClosedEffect` tree: no reachable residual is a `.fail`
request of any `FailureKind`.
-/
theorem mirClosed_noFault_iff {R : Type} (t : ITree MirClosedEffect R) :
    NoFault t ↔
      ∀ tr u (fk : FailureKind) k, Reaches t tr u →
        u.observe ≠ .vis (.inl (.fail fk)) k := by
  constructor
  · intro h tr u fk k hr hobs
    exact h tr u _ k hr hobs trivial
  · intro h tr u i k hr hobs hf
    match i, k, hobs, hf with
    | .inl (.fail fk), k, hobs, _ => exact h tr u fk k hr hobs
    | .inr _, _, _, hf => exact hf

/-! ## 3. Captured-MIR Panic Contracts -/

/-- Input of a memory-aware MIR contract: argument values and initial memory. -/
abbrev MirInput : Type := List Value × Memory

/-- Tree family of `body` unfolded from the initial machine states `init x`. -/
def mirTreesFrom {Inp : Type w} (body : CapturedMir) (init : Inp → MachineState) :
    Inp → ITree MirEffect MirOutcome :=
  fun x => mirTree body (init x)

/--
`Claim`-style tree family of `body`: the tree of `body` on `args` from its
initial memory, with linked callee table `callees`.
-/
def mirTrees (body : CapturedMir) (callees : List CapturedMir := .nil) :
    List Value → ITree MirEffect MirOutcome :=
  mirTreesFrom body (fun args => initMachineStateWithCallees body args callees)

/--
`StatefulClaim`-style tree family of `body`: the tree of `body` from
`(args, mem)`, with default callee table `callees`.
-/
def mirStatefulTrees (body : CapturedMir) (callees : List CapturedMir := .nil) :
    MirInput → ITree MirEffect MirOutcome :=
  mirTreesFrom body
    (fun x => initMachineStateWithMemoryAndCallees body x.1 x.2 callees)

theorem mirTrees_apply (body : CapturedMir) (callees : List CapturedMir)
    (args : List Value) :
    mirTrees body callees args = mirCallTreeWithCallees body args callees :=
  rfl

theorem mirStatefulTrees_apply (body : CapturedMir) (callees : List CapturedMir)
    (x : MirInput) :
    mirStatefulTrees body callees x = mirStatefulTreeWithCallees body x.1 x.2 callees :=
  rfl

/--
`ModularClaim`-style tree family of `body`: the tree of `body` from
`(args, mem)` with every external call answered by the handler `h`.
-/
def mirHandledTrees (body : CapturedMir) (h : ExternalCallHandler)
    (callees : List CapturedMir := .nil) :
    MirInput → ITree MirClosedEffect MirOutcome :=
  fun x => mirHandledTreeWithCallees body x.1 x.2 callees h

theorem mirHandledTrees_apply (body : CapturedMir) (h : ExternalCallHandler)
    (callees : List CapturedMir) (x : MirInput) :
    mirHandledTrees body h callees x =
      ITree.interp (handleMirExternalCalls h) (mirStatefulTrees body callees x) :=
  rfl

/--
Rely–guarantee only-if policy contract: for every handler `h` satisfying
`envAssumed`, the handled trees of `body` satisfy `PanicsWithPolicyOnlyIf`.
-/
def MirModularPanicsWithPolicyOnlyIf (body : CapturedMir)
    (envAssumed : ExternalCallHandler → Prop)
    (pre : MirInput → Prop) (post : MirInput → MirReturn → Prop)
    (panicCond : MirInput → Prop) (policy : AbortPolicy MirInput)
    (callees : List CapturedMir := .nil) : Prop :=
  ∀ h, envAssumed h →
    PanicsWithPolicyOnlyIf (mirHandledTrees body h callees) pre post panicCond policy

/--
Rely–guarantee only-if contract: for every handler `h` satisfying `envAssumed`,
the handled trees of `body` satisfy `PanicsOnlyIf`.
-/
def MirModularPanicsOnlyIf (body : CapturedMir)
    (envAssumed : ExternalCallHandler → Prop)
    (pre : MirInput → Prop) (post : MirInput → MirReturn → Prop)
    (panicCond : MirInput → Prop) (callees : List CapturedMir := .nil) : Prop :=
  ∀ h, envAssumed h → PanicsOnlyIf (mirHandledTrees body h callees) pre post panicCond

/--
Rely–guarantee panic trigger: for every handler `h` satisfying `envAssumed`, the
handled trees of `body` satisfy `PanicsIf`.
-/
def MirModularPanicsIf (body : CapturedMir)
    (envAssumed : ExternalCallHandler → Prop)
    (pre panicCond : MirInput → Prop) (callees : List CapturedMir := .nil) : Prop :=
  ∀ h, envAssumed h → PanicsIf (mirHandledTrees body h callees) pre panicCond

/-- Rely–guarantee `NeverPanics`. -/
def MirModularNeverPanics (body : CapturedMir)
    (envAssumed : ExternalCallHandler → Prop)
    (pre : MirInput → Prop) (post : MirInput → MirReturn → Prop)
    (callees : List CapturedMir := .nil) : Prop :=
  ∀ h, envAssumed h → NeverPanics (mirHandledTrees body h callees) pre post

/-- Rely–guarantee exact contract: `MirModularPanicsOnlyIf` together with `MirModularPanicsIf`. -/
def MirModularExactPanicContract (body : CapturedMir)
    (envAssumed : ExternalCallHandler → Prop)
    (pre : MirInput → Prop) (post : MirInput → MirReturn → Prop)
    (panicCond : MirInput → Prop) (callees : List CapturedMir := .nil) : Prop :=
  ∀ h, envAssumed h →
    ExactPanicContract (mirHandledTrees body h callees) pre post panicCond

/-- Rely–guarantee only-if contract with an explicit abort condition. -/
def MirModularPanicsOrAbortsOnlyIf (body : CapturedMir)
    (envAssumed : ExternalCallHandler → Prop)
    (pre : MirInput → Prop) (post : MirInput → MirReturn → Prop)
    (panicCond abortCond : MirInput → Prop) (callees : List CapturedMir := .nil) : Prop :=
  ∀ h, envAssumed h →
    PanicsOrAbortsOnlyIf (mirHandledTrees body h callees) pre post panicCond abortCond

/-- Rely–guarantee abort trigger. -/
def MirModularAbortsIf (body : CapturedMir)
    (envAssumed : ExternalCallHandler → Prop)
    (pre abortCond : MirInput → Prop) (callees : List CapturedMir := .nil) : Prop :=
  ∀ h, envAssumed h → AbortsIf (mirHandledTrees body h callees) pre abortCond

/-- Rely–guarantee exact policy contract. -/
def MirModularExactPolicyPanicContract (body : CapturedMir)
    (envAssumed : ExternalCallHandler → Prop)
    (pre : MirInput → Prop) (post : MirInput → MirReturn → Prop)
    (panicCond : MirInput → Prop) (policy : AbortPolicy MirInput)
    (callees : List CapturedMir := .nil) : Prop :=
  ∀ h, envAssumed h →
    ExactPolicyPanicContract (mirHandledTrees body h callees) pre post panicCond policy

/-- Rely–guarantee exact panic-or-abort contract. -/
def MirModularExactPanicAbortContract (body : CapturedMir)
    (envAssumed : ExternalCallHandler → Prop)
    (pre : MirInput → Prop) (post : MirInput → MirReturn → Prop)
    (panicCond abortCond : MirInput → Prop) (callees : List CapturedMir := .nil) : Prop :=
  ∀ h, envAssumed h →
    ExactPanicAbortContract (mirHandledTrees body h callees) pre post panicCond abortCond

theorem mirModularPanicsWithPolicyOnlyIf_forbidAbort_iff {body : CapturedMir}
    {envAssumed : ExternalCallHandler → Prop} {pre : MirInput → Prop}
    {post : MirInput → MirReturn → Prop} {panicCond : MirInput → Prop}
    {callees : List CapturedMir} :
    MirModularPanicsWithPolicyOnlyIf body envAssumed pre post panicCond .forbidAbort
        callees ↔
      MirModularPanicsOnlyIf body envAssumed pre post panicCond callees :=
  ⟨fun h hdl hEnv => panicsWithPolicyOnlyIf_forbidAbort_iff.1 (h hdl hEnv),
   fun h hdl hEnv => panicsWithPolicyOnlyIf_forbidAbort_iff.2 (h hdl hEnv)⟩

theorem mirModularExactPanicContract_iff {body : CapturedMir}
    {envAssumed : ExternalCallHandler → Prop} {pre : MirInput → Prop}
    {post : MirInput → MirReturn → Prop} {panicCond : MirInput → Prop}
    {callees : List CapturedMir} :
    MirModularExactPanicContract body envAssumed pre post panicCond callees ↔
      MirModularPanicsOnlyIf body envAssumed pre post panicCond callees ∧
        MirModularPanicsIf body envAssumed pre panicCond callees :=
  ⟨fun h => ⟨fun hdl hEnv => (h hdl hEnv).1, fun hdl hEnv => (h hdl hEnv).2⟩,
   fun h hdl hEnv => ⟨h.1 hdl hEnv, h.2 hdl hEnv⟩⟩

theorem mirModularExactPolicyPanicContract_forbidAbort_iff {body : CapturedMir}
    {envAssumed : ExternalCallHandler → Prop} {pre : MirInput → Prop}
    {post : MirInput → MirReturn → Prop} {panicCond : MirInput → Prop}
    {callees : List CapturedMir} :
    MirModularExactPolicyPanicContract body envAssumed pre post panicCond .forbidAbort
        callees ↔
      MirModularExactPanicContract body envAssumed pre post panicCond callees :=
  ⟨fun h hdl hEnv => exactPolicyPanicContract_forbidAbort_iff.1 (h hdl hEnv),
   fun h hdl hEnv => exactPolicyPanicContract_forbidAbort_iff.2 (h hdl hEnv)⟩

theorem mirModularExactPolicyPanicContract_abortOnlyIf_iff {body : CapturedMir}
    {envAssumed : ExternalCallHandler → Prop} {pre : MirInput → Prop}
    {post : MirInput → MirReturn → Prop} {panicCond abortCond : MirInput → Prop}
    {callees : List CapturedMir} :
    MirModularExactPolicyPanicContract body envAssumed pre post panicCond
        (.abortOnlyIf abortCond) callees ↔
      MirModularExactPanicAbortContract body envAssumed pre post panicCond abortCond
        callees :=
  ⟨fun h hdl hEnv => exactPolicyPanicContract_abortOnlyIf_iff.1 (h hdl hEnv),
   fun h hdl hEnv => exactPolicyPanicContract_abortOnlyIf_iff.2 (h hdl hEnv)⟩

/-! ### Bridges to `Trusted.VerificationResult` -/

/--
A stateless only-if contract with any panic condition and any abort policy
yields the partial-correctness certificate of the claim with the same `pre` and
`post`.
-/
theorem PanicsWithPolicyOnlyIf.toVerificationResult (c : Claim)
    {panicCond : List Value → Prop} {policy : AbortPolicy (List Value)}
    (h : PanicsWithPolicyOnlyIf (mirTrees c.body c.callees) c.pre
      (fun args r => c.post args r.1) panicCond policy) :
    VerificationResult c := by
  refine ⟨fun args h_pre => ⟨(h args h_pre).1, ?_⟩⟩
  intro outPair h_ret _ retVal mem' h_out
  have hOk := (h args h_pre).2 outPair.1 outPair.2 h_ret
  rw [h_out] at hOk
  exact hOk

theorem PanicsOnlyIf.toVerificationResult (c : Claim)
    {panicCond : List Value → Prop}
    (h : PanicsOnlyIf (mirTrees c.body c.callees) c.pre
      (fun args r => c.post args r.1) panicCond) :
    VerificationResult c :=
  (h.toPolicy .forbidAbort).toVerificationResult c

/--
Round trip for stateless claims: `NeverPanics` is the partial-correctness
certificate together with the absence of panicking and aborting executions.
-/
theorem neverPanics_iff_verificationResult (c : Claim) :
    NeverPanics (mirTrees c.body c.callees) c.pre (fun args r => c.post args r.1) ↔
      VerificationResult c ∧
        ∀ args, c.pre args → ∀ tr out,
          ReachesRet (mirTrees c.body c.callees args) tr out → ∃ r, out = .normal r := by
  constructor
  · intro h
    refine ⟨PanicsOnlyIf.toVerificationResult c h, fun args h_pre tr out h_ret => ?_⟩
    obtain ⟨r, hr, _⟩ := (neverPanics_iff.1 h args h_pre).2 tr out h_ret
    exact ⟨r, hr⟩
  · rintro ⟨hVer, hNormal⟩
    refine neverPanics_iff.2 fun args h_pre => ?_
    obtain ⟨h_safe, h_val⟩ := hVer.proof args h_pre
    refine ⟨h_safe, fun tr out h_ret => ?_⟩
    obtain ⟨r, hr⟩ := hNormal args h_pre tr out h_ret
    exact ⟨r, hr, h_val (tr, out) h_ret h_pre r.1 r.2 hr⟩

/--
A memory-aware only-if contract with any panic condition and any abort policy
yields the stateful partial-correctness certificate.
-/
theorem PanicsWithPolicyOnlyIf.toStatefulVerificationResult (c : StatefulClaim)
    {panicCond : MirInput → Prop} {policy : AbortPolicy MirInput}
    (h : PanicsWithPolicyOnlyIf (mirStatefulTrees c.body c.callees)
      (fun x => c.pre x.1 x.2) (fun x r => c.post x.1 x.2 r.1 r.2) panicCond policy) :
    StatefulVerificationResult c := by
  refine ⟨fun args mem h_pre => ⟨(h (args, mem) h_pre).1, ?_⟩⟩
  intro outPair h_ret _ retVal mem' h_out
  have hOk := (h (args, mem) h_pre).2 outPair.1 outPair.2 h_ret
  rw [h_out] at hOk
  exact hOk

theorem PanicsOnlyIf.toStatefulVerificationResult (c : StatefulClaim)
    {panicCond : MirInput → Prop}
    (h : PanicsOnlyIf (mirStatefulTrees c.body c.callees)
      (fun x => c.pre x.1 x.2) (fun x r => c.post x.1 x.2 r.1 r.2) panicCond) :
    StatefulVerificationResult c :=
  (h.toPolicy .forbidAbort).toStatefulVerificationResult c

/--
Round trip for stateful claims: `NeverPanics` is the stateful
partial-correctness certificate together with the absence of panicking and
aborting executions.
-/
theorem neverPanics_iff_statefulVerificationResult (c : StatefulClaim) :
    NeverPanics (mirStatefulTrees c.body c.callees)
        (fun x => c.pre x.1 x.2) (fun x r => c.post x.1 x.2 r.1 r.2) ↔
      StatefulVerificationResult c ∧
        ∀ x : MirInput, c.pre x.1 x.2 → ∀ tr out,
          ReachesRet (mirStatefulTrees c.body c.callees x) tr out →
            ∃ r, out = .normal r := by
  constructor
  · intro h
    refine ⟨PanicsOnlyIf.toStatefulVerificationResult c h, fun x h_pre tr out h_ret => ?_⟩
    obtain ⟨r, hr, _⟩ := (neverPanics_iff.1 h x h_pre).2 tr out h_ret
    exact ⟨r, hr⟩
  · rintro ⟨hVer, hNormal⟩
    refine neverPanics_iff.2 fun x h_pre => ?_
    obtain ⟨h_safe, h_val⟩ := hVer.proof x.1 x.2 h_pre
    refine ⟨h_safe, fun tr out h_ret => ?_⟩
    obtain ⟨r, hr⟩ := hNormal x h_pre tr out h_ret
    exact ⟨r, hr, h_val (tr, out) h_ret h_pre r.1 r.2 hr⟩

/--
Round trip for total-correctness claims: the certificate is exactly
`NeverPanics` together with termination.
-/
theorem totalVerificationResult_iff_neverPanics (c : TotalClaim) :
    TotalVerificationResult c ↔
      NeverPanics (mirStatefulTrees c.body c.callees)
          (fun x => c.pre x.1 x.2) (fun x r => c.post x.1 x.2 r.1 r.2) ∧
        TerminatesOn (mirStatefulTrees c.body c.callees) (fun x => c.pre x.1 x.2) := by
  constructor
  · intro hVer
    refine ⟨neverPanics_iff.2 fun x h_pre => ?_, fun x h_pre => ?_⟩
    · obtain ⟨h_safe, _, _, h_ret⟩ := hVer.proof x.1 x.2 h_pre
      refine ⟨h_safe, fun tr out hr => ?_⟩
      obtain ⟨retVal, mem', h_out, h_post⟩ := h_ret tr out hr
      exact ⟨(retVal, mem'), h_out, h_post⟩
    · obtain ⟨_, h_prod, h_div, _⟩ := hVer.proof x.1 x.2 h_pre
      exact ⟨h_prod, h_div⟩
  · rintro ⟨hNever, hTerm⟩
    refine ⟨fun args mem h_pre => ?_⟩
    obtain ⟨h_safe, h_ret⟩ := neverPanics_iff.1 hNever (args, mem) h_pre
    obtain ⟨h_prod, h_div⟩ := hTerm (args, mem) h_pre
    refine ⟨h_safe, h_prod, h_div, fun tr out hr => ?_⟩
    obtain ⟨r, h_out, h_post⟩ := h_ret tr out hr
    exact ⟨r.1, r.2, h_out, h_post⟩

/-- A total exact contract with an unsatisfiable panic condition yields the total-correctness certificate. -/
theorem TotalExactPanicContract.toTotalVerificationResult (c : TotalClaim)
    (h : TotalExactPanicContract (mirStatefulTrees c.body c.callees)
      (fun x => c.pre x.1 x.2) (fun x r => c.post x.1 x.2 r.1 r.2) (fun _ => False)) :
    TotalVerificationResult c :=
  (totalVerificationResult_iff_neverPanics c).2 ⟨h.exact.1, h.terminates⟩

/--
A rely–guarantee only-if contract with any panic condition and any abort policy
yields the modular partial-correctness certificate.
-/
theorem MirModularPanicsWithPolicyOnlyIf.toModularVerificationResult (c : ModularClaim)
    {panicCond : MirInput → Prop} {policy : AbortPolicy MirInput}
    (h : MirModularPanicsWithPolicyOnlyIf c.body c.envAssumed
      (fun x => c.pre x.1 x.2) (fun x r => c.post x.1 x.2 r.1 r.2) panicCond policy
      c.callees) :
    ModularVerificationResult c := by
  refine ⟨fun hdl hEnv args mem h_pre => ⟨(h hdl hEnv (args, mem) h_pre).1, ?_⟩⟩
  intro outPair h_ret _ retVal mem' h_out
  have hOk := (h hdl hEnv (args, mem) h_pre).2 outPair.1 outPair.2 h_ret
  rw [h_out] at hOk
  exact hOk

/--
Round trip for modular claims: rely–guarantee `NeverPanics` is the modular
partial-correctness certificate together with the absence of panicking and
aborting executions under every assumed handler.
-/
theorem mirModularNeverPanics_iff_modularVerificationResult (c : ModularClaim) :
    MirModularNeverPanics c.body c.envAssumed
        (fun x => c.pre x.1 x.2) (fun x r => c.post x.1 x.2 r.1 r.2) c.callees ↔
      ModularVerificationResult c ∧
        ∀ hdl, c.envAssumed hdl → ∀ x : MirInput, c.pre x.1 x.2 → ∀ tr out,
          ReachesRet (mirHandledTrees c.body hdl c.callees x) tr out →
            ∃ r, out = .normal r := by
  constructor
  · intro h
    refine ⟨MirModularPanicsWithPolicyOnlyIf.toModularVerificationResult c
      (panicCond := fun _ => False) (policy := .forbidAbort)
      (fun hdl hEnv => (h hdl hEnv).toPolicy .forbidAbort), ?_⟩
    intro hdl hEnv x h_pre tr out h_ret
    obtain ⟨r, hr, _⟩ := (neverPanics_iff.1 (h hdl hEnv) x h_pre).2 tr out h_ret
    exact ⟨r, hr⟩
  · rintro ⟨hVer, hNormal⟩ hdl hEnv
    refine neverPanics_iff.2 fun x h_pre => ?_
    obtain ⟨h_safe, h_val⟩ := hVer.proof hdl hEnv x.1 x.2 h_pre
    refine ⟨h_safe, fun tr out h_ret => ?_⟩
    obtain ⟨r, hr⟩ := hNormal hdl hEnv x h_pre tr out h_ret
    exact ⟨r, hr, h_val (tr, out) h_ret h_pre r.1 r.2 hr⟩

/--
Exact round trip to `TraceVerificationResult`: a memory-aware
`PanicsWithPolicyOnlyIf` contract is directly equivalent to a trusted
`TraceVerificationResult` whose trace-oblivious postcondition is
`PolicyOutcomeOk`.
-/
theorem panicsWithPolicyOnlyIf_iff_traceVerificationResult (body : CapturedMir)
    (callees : List CapturedMir) (pre : MirInput → Prop)
    (post : MirInput → MirReturn → Prop) (panicCond : MirInput → Prop)
    (policy : AbortPolicy MirInput) :
    PanicsWithPolicyOnlyIf (mirStatefulTrees body callees) pre post panicCond policy ↔
      TraceVerificationResult
        { body := body
          pre := fun args mem => pre (args, mem)
          post := fun args mem _ out =>
            PolicyOutcomeOk policy (args, mem) (post (args, mem)) (panicCond (args, mem)) out
          callees := callees } := by
  constructor
  · intro h
    exact ⟨fun args mem hPre =>
      ⟨(h (args, mem) hPre).1, fun outPair hRet => (h (args, mem) hPre).2 outPair.1 outPair.2 hRet⟩⟩
  · intro hVer x hPre
    obtain ⟨hSafe, hPost⟩ := hVer.proof x.1 x.2 hPre
    exact ⟨hSafe, fun tr out hRet => hPost (tr, out) hRet⟩

/-! ## 4. Predicate-Transformer Adequacy -/

section Adequacy

variable {E : Effect.{u}} [FaultEffect E] {R Val : Type u} {Inp : Type w}
  {tree : Inp → ITree E (Outcome Val)} {pre : Inp → Prop}
  {post : Inp → Val → Prop} {panicCond : Inp → Prop} {policy : AbortPolicy Inp}

/-- `DWLP` under a sound stateless transformer establishes `PanicsWithPolicyOnlyIf`. -/
theorem panicsWithPolicyOnlyIf_of_dwlp {ewp : EffectWP E} [PureSoundWP ewp]
    (h : ∀ x, pre x →
      DWLP ewp (tree x)
        (fun out _ => PolicyOutcomeOk policy x (post x) (panicCond x) out) PUnit.unit) :
    PanicsWithPolicyOnlyIf tree pre post panicCond policy :=
  fun x hx => dwlp_pure_adequacy (h x hx)

/-- `DWLP` under a sound stateless transformer establishes `PanicsOnlyIf`. -/
theorem panicsOnlyIf_of_dwlp {ewp : EffectWP E} [PureSoundWP ewp]
    (h : ∀ x, pre x →
      DWLP ewp (tree x)
        (fun out _ => PanicOutcomeOk (post x) (panicCond x) out) PUnit.unit) :
    PanicsOnlyIf tree pre post panicCond :=
  fun x hx => dwlp_pure_adequacy (h x hx)

/-- `DWLP` under a sound stateless transformer establishes `NeverPanics`. -/
theorem neverPanics_of_dwlp {ewp : EffectWP E} [PureSoundWP ewp]
    (h : ∀ x, pre x →
      DWLP ewp (tree x)
        (fun out _ => ∃ v, out = .normal v ∧ post x v) PUnit.unit) :
    NeverPanics tree pre post :=
  neverPanics_iff.2 fun x hx => dwlp_pure_adequacy (h x hx)

/--
A total-correctness proof exhibits a completed execution: if every non-fault
request has an answer, `DWP` yields a trace reaching a return value that
satisfies the postcondition.
-/
theorem exists_reachesRet_of_dwp {ewp : EffectWP E} [PureSoundWP ewp]
    (hAns : ∀ i : E.I, ¬ FaultEffect.isFault i → Nonempty (E.O i))
    {t : ITree E R} {Q : R → Prop}
    (h : DWP ewp t (fun r _ => Q r) PUnit.unit) :
    ∃ tr r, ReachesRet t tr r ∧ Q r := by
  refine DWP.induct (fun x _ => ∃ tr r, ReachesRet x tr r ∧ Q r) ?_ h
  intro x _ hx
  cases h_obs : x.observe with
  | ret r =>
    simp only [h_obs] at hx
    exact ⟨[], r, ⟨x, .refl x, h_obs⟩, hx⟩
  | tau x' =>
    simp only [h_obs] at hx
    obtain ⟨tr, r, ⟨u, hr, hu⟩, hq⟩ := hx
    exact ⟨tr, r, ⟨u, .tau h_obs hr, hu⟩, hq⟩
  | vis i k =>
    simp only [h_obs] at hx
    obtain ⟨hnf, hAll⟩ := PureSoundWP.sound hx
    obtain ⟨o⟩ := hAns i hnf
    obtain ⟨tr, r, ⟨u, hr, hu⟩, hq⟩ := hAll o
    exact ⟨⟨i, o⟩ :: tr, r, ⟨u, .vis h_obs hnf o hr, hu⟩, hq⟩

/-- `DWP` under a sound stateless transformer establishes termination. -/
theorem terminatesOn_of_dwp {ewp : EffectWP E} [PureSoundWP ewp]
    {Q : Inp → Outcome Val → Prop}
    (h : ∀ x, pre x → DWP ewp (tree x) (fun out _ => Q x out) PUnit.unit) :
    TerminatesOn tree pre :=
  fun x hx =>
    have hAdeq := dwp_pure_adequacy (h x hx)
    ⟨hAdeq.2.1, hAdeq.2.2.1⟩

/--
One total-correctness obligation with the exact classifier establishes the
total exact policy contract: the only-if contract, both triggers, termination,
the return trigger, and exclusivity of the outcome kinds.
-/
theorem totalExactPolicyPanicContract_of_dwp {ewp : EffectWP E} [PureSoundWP ewp]
    (hAns : ∀ i : E.I, ¬ FaultEffect.isFault i → Nonempty (E.O i))
    (h : ∀ x, pre x →
      DWP ewp (tree x)
        (fun out _ => ExactPolicyOutcome policy x (post x) (panicCond x) out) PUnit.unit) :
    TotalExactPolicyPanicContract tree pre post panicCond policy := by
  have hAll : ∀ x, pre x → ∀ tr out, ReachesRet (tree x) tr out →
      ExactPolicyOutcome policy x (post x) (panicCond x) out :=
    fun x hx => (dwp_pure_adequacy (h x hx)).2.2.2
  have hSome : ∀ x, pre x → ∃ tr out, ReachesRet (tree x) tr out ∧
      ExactPolicyOutcome policy x (post x) (panicCond x) out :=
    fun x hx => exists_reachesRet_of_dwp hAns (h x hx)
  refine ⟨⟨fun x hx => ⟨(dwp_pure_adequacy (h x hx)).1, fun tr out hr =>
      (hAll x hx tr out hr).toPolicyOutcomeOk⟩, ?_, ?_⟩, terminatesOn_of_dwp h, ?_, hAll⟩
  · intro x hx hp
    obtain ⟨tr, out, hr, hc⟩ := hSome x hx
    cases out with
    | normal v => exact False.elim (hc.1 hp)
    | panic => exact ⟨tr, hr⟩
    | abort => exact False.elim (hc.2 hp)
  · intro x hx ha
    obtain ⟨tr, out, hr, hc⟩ := hSome x hx
    cases out with
    | normal v => exact False.elim (hc.2.1 ha)
    | panic => exact False.elim (hc.2 ha)
    | abort => exact ⟨tr, hr⟩
  · intro x hx hc
    obtain ⟨tr, out, hr, hOut⟩ := hSome x hx
    cases out with
    | normal v => exact ⟨tr, v, hr⟩
    | panic => exact False.elim (hc.1 hOut.1)
    | abort => exact False.elim (hc.2 hOut.1)

/--
One total-correctness obligation with the exact classifier establishes the
total exact panic contract.
-/
theorem totalExactPanicContract_of_dwp {ewp : EffectWP E} [PureSoundWP ewp]
    (hAns : ∀ i : E.I, ¬ FaultEffect.isFault i → Nonempty (E.O i))
    (h : ∀ x, pre x →
      DWP ewp (tree x)
        (fun out _ => ExactPanicOutcome (post x) (panicCond x) out) PUnit.unit) :
    TotalExactPanicContract tree pre post panicCond :=
  totalExactPolicyPanicContract_forbidAbort_iff.1
    (totalExactPolicyPanicContract_of_dwp hAns fun x hx =>
      DWP.mono (fun out _ hOut =>
        (exactPolicyOutcome_forbidAbort_iff x (post x) (panicCond x) out).2 hOut) (h x hx))

end Adequacy

/-! ### Bounded evaluators of `Anneal.Rustc.V2026_06_01.Lower` -/

section MirAdequacy

variable {Inp : Type w} {body : CapturedMir} {init : Inp → MachineState}
  {pre : Inp → Prop} {post : Inp → MirReturn → Prop} {panicCond : Inp → Prop}
  {policy : AbortPolicy Inp}

/-- `wpMirBounded` establishes `PanicsWithPolicyOnlyIf` on `mirTreesFrom body init`. -/
theorem panicsWithPolicyOnlyIf_of_wpMirBounded (fuel : Nat)
    (h : ∀ x, pre x →
      wpMirBounded fuel body (init x)
        (PolicyOutcomeOk policy x (post x) (panicCond x))) :
    PanicsWithPolicyOnlyIf (mirTreesFrom body init) pre post panicCond policy :=
  panicsWithPolicyOnlyIf_of_dwlp (ewp := mirDefaultWP)
    fun x hx => dwlp_cofix_of_wpCoalBounded (h x hx)

/-- `wpMirBounded` establishes `PanicsOnlyIf` on `mirTreesFrom body init`. -/
theorem panicsOnlyIf_of_wpMirBounded (fuel : Nat)
    (h : ∀ x, pre x →
      wpMirBounded fuel body (init x) (PanicOutcomeOk (post x) (panicCond x))) :
    PanicsOnlyIf (mirTreesFrom body init) pre post panicCond :=
  panicsOnlyIf_of_dwlp (ewp := mirDefaultWP)
    fun x hx => dwlp_cofix_of_wpCoalBounded (h x hx)

/-- `wpMirBounded` establishes `NeverPanics` on `mirTreesFrom body init`. -/
theorem neverPanics_of_wpMirBounded (fuel : Nat)
    (h : ∀ x, pre x →
      wpMirBounded fuel body (init x) (fun out => ∃ r, out = .normal r ∧ post x r)) :
    NeverPanics (mirTreesFrom body init) pre post :=
  neverPanics_of_dwlp (ewp := mirDefaultWP)
    fun x hx => dwlp_cofix_of_wpCoalBounded (h x hx)

/--
`wpMirBounded` with the exact classifier establishes the total exact policy
contract on `mirTreesFrom body init`.
-/
theorem totalExactPolicyPanicContract_of_wpMirBounded (fuel : Nat)
    (h : ∀ x, pre x →
      wpMirBounded fuel body (init x)
        (ExactPolicyOutcome policy x (post x) (panicCond x))) :
    TotalExactPolicyPanicContract (mirTreesFrom body init) pre post panicCond policy :=
  totalExactPolicyPanicContract_of_dwp (ewp := mirDefaultWP) mirEffect_nonFault_nonempty
    fun x hx => dwp_cofix_of_wpCoalBounded fuel (h x hx)

/--
`wpMirBounded` with the exact classifier establishes the total exact panic
contract on `mirTreesFrom body init`.
-/
theorem totalExactPanicContract_of_wpMirBounded (fuel : Nat)
    (h : ∀ x, pre x →
      wpMirBounded fuel body (init x) (ExactPanicOutcome (post x) (panicCond x))) :
    TotalExactPanicContract (mirTreesFrom body init) pre post panicCond :=
  totalExactPanicContract_of_dwp (ewp := mirDefaultWP) mirEffect_nonFault_nonempty
    fun x hx => dwp_cofix_of_wpCoalBounded fuel (h x hx)

/-- `wpMirNoCallBounded` establishes `PanicsWithPolicyOnlyIf` on `mirTreesFrom body init`. -/
theorem panicsWithPolicyOnlyIf_of_wpMirNoCallBounded (fuel : Nat)
    (h : ∀ x, pre x →
      wpMirNoCallBounded fuel body (init x)
        (PolicyOutcomeOk policy x (post x) (panicCond x))) :
    PanicsWithPolicyOnlyIf (mirTreesFrom body init) pre post panicCond policy :=
  panicsWithPolicyOnlyIf_of_dwlp (ewp := mirNoCallWP)
    fun x hx => dwlp_cofix_of_wpCoalBounded (h x hx)

/-- `wpMirNoCallBounded` establishes `PanicsOnlyIf` on `mirTreesFrom body init`. -/
theorem panicsOnlyIf_of_wpMirNoCallBounded (fuel : Nat)
    (h : ∀ x, pre x →
      wpMirNoCallBounded fuel body (init x) (PanicOutcomeOk (post x) (panicCond x))) :
    PanicsOnlyIf (mirTreesFrom body init) pre post panicCond :=
  panicsOnlyIf_of_dwlp (ewp := mirNoCallWP)
    fun x hx => dwlp_cofix_of_wpCoalBounded (h x hx)

/-- `wpMirNoCallBounded` establishes `NeverPanics` on `mirTreesFrom body init`. -/
theorem neverPanics_of_wpMirNoCallBounded (fuel : Nat)
    (h : ∀ x, pre x →
      wpMirNoCallBounded fuel body (init x) (fun out => ∃ r, out = .normal r ∧ post x r)) :
    NeverPanics (mirTreesFrom body init) pre post :=
  neverPanics_of_dwlp (ewp := mirNoCallWP)
    fun x hx => dwlp_cofix_of_wpCoalBounded (h x hx)

/--
`wpMirNoCallBounded` with the exact classifier establishes the total exact
policy contract on `mirTreesFrom body init`.
-/
theorem totalExactPolicyPanicContract_of_wpMirNoCallBounded (fuel : Nat)
    (h : ∀ x, pre x →
      wpMirNoCallBounded fuel body (init x)
        (ExactPolicyOutcome policy x (post x) (panicCond x))) :
    TotalExactPolicyPanicContract (mirTreesFrom body init) pre post panicCond policy :=
  totalExactPolicyPanicContract_of_dwp (ewp := mirNoCallWP) mirEffect_nonFault_nonempty
    fun x hx => dwp_cofix_of_wpCoalBounded fuel (h x hx)

/--
`wpMirNoCallBounded` with the exact classifier establishes the total exact
panic contract on `mirTreesFrom body init`.
-/
theorem totalExactPanicContract_of_wpMirNoCallBounded (fuel : Nat)
    (h : ∀ x, pre x →
      wpMirNoCallBounded fuel body (init x) (ExactPanicOutcome (post x) (panicCond x))) :
    TotalExactPanicContract (mirTreesFrom body init) pre post panicCond :=
  totalExactPanicContract_of_dwp (ewp := mirNoCallWP) mirEffect_nonFault_nonempty
    fun x hx => dwp_cofix_of_wpCoalBounded fuel (h x hx)

/-! Single-pass symbolic evaluators of `Anneal.Rustc.V2026_06_01.SymbolicEval`. -/

/-- `wpMirNoCallSym` establishes `PanicsWithPolicyOnlyIf` on `mirTreesFrom body init`. -/
theorem panicsWithPolicyOnlyIf_of_wpMirNoCallSym (fuel : Nat)
    (h : ∀ x, pre x →
      wpMirNoCallSym fuel body (init x) (PolicyOutcomeOk policy x (post x) (panicCond x))) :
    PanicsWithPolicyOnlyIf (mirTreesFrom body init) pre post panicCond policy :=
  panicsWithPolicyOnlyIf_of_wpMirNoCallBounded fuel fun x hx =>
    (wpMirNoCallSym_eq_wpMirNoCallBounded fuel body (init x) _) ▸ h x hx

/-- `wpMirNoCallSym` establishes `PanicsOnlyIf` on `mirTreesFrom body init`. -/
theorem panicsOnlyIf_of_wpMirNoCallSym (fuel : Nat)
    (h : ∀ x, pre x →
      wpMirNoCallSym fuel body (init x) (PanicOutcomeOk (post x) (panicCond x))) :
    PanicsOnlyIf (mirTreesFrom body init) pre post panicCond :=
  panicsOnlyIf_of_wpMirNoCallBounded fuel fun x hx =>
    (wpMirNoCallSym_eq_wpMirNoCallBounded fuel body (init x) _) ▸ h x hx

/-- `wpMirNoCallSym` establishes `NeverPanics` on `mirTreesFrom body init`. -/
theorem neverPanics_of_wpMirNoCallSym (fuel : Nat)
    (h : ∀ x, pre x →
      wpMirNoCallSym fuel body (init x) (fun out => ∃ r, out = .normal r ∧ post x r)) :
    NeverPanics (mirTreesFrom body init) pre post :=
  neverPanics_of_wpMirNoCallBounded fuel fun x hx =>
    (wpMirNoCallSym_eq_wpMirNoCallBounded fuel body (init x) _) ▸ h x hx

/--
`wpMirNoCallSym` with the exact classifier establishes the total exact policy
contract on `mirTreesFrom body init`.
-/
theorem totalExactPolicyPanicContract_of_wpMirNoCallSym (fuel : Nat)
    (h : ∀ x, pre x →
      wpMirNoCallSym fuel body (init x) (ExactPolicyOutcome policy x (post x) (panicCond x))) :
    TotalExactPolicyPanicContract (mirTreesFrom body init) pre post panicCond policy :=
  totalExactPolicyPanicContract_of_wpMirNoCallBounded fuel fun x hx =>
    (wpMirNoCallSym_eq_wpMirNoCallBounded fuel body (init x) _) ▸ h x hx

/--
`wpMirNoCallSym` with the exact classifier establishes the total exact panic
contract on `mirTreesFrom body init`.
-/
theorem totalExactPanicContract_of_wpMirNoCallSym (fuel : Nat)
    (h : ∀ x, pre x →
      wpMirNoCallSym fuel body (init x) (ExactPanicOutcome (post x) (panicCond x))) :
    TotalExactPanicContract (mirTreesFrom body init) pre post panicCond :=
  totalExactPanicContract_of_wpMirNoCallBounded fuel fun x hx =>
    (wpMirNoCallSym_eq_wpMirNoCallBounded fuel body (init x) _) ▸ h x hx

/-- `wpMirSym` establishes `PanicsWithPolicyOnlyIf` on `mirTreesFrom body init`. -/
theorem panicsWithPolicyOnlyIf_of_wpMirSym (fuel : Nat)
    (h : ∀ x, pre x →
      wpMirSym fuel body (init x) (PolicyOutcomeOk policy x (post x) (panicCond x))) :
    PanicsWithPolicyOnlyIf (mirTreesFrom body init) pre post panicCond policy :=
  panicsWithPolicyOnlyIf_of_wpMirBounded fuel fun x hx =>
    (wpMirSym_eq_wpMirBounded fuel body (init x) _) ▸ h x hx

/-- `wpMirSym` establishes `PanicsOnlyIf` on `mirTreesFrom body init`. -/
theorem panicsOnlyIf_of_wpMirSym (fuel : Nat)
    (h : ∀ x, pre x →
      wpMirSym fuel body (init x) (PanicOutcomeOk (post x) (panicCond x))) :
    PanicsOnlyIf (mirTreesFrom body init) pre post panicCond :=
  panicsOnlyIf_of_wpMirBounded fuel fun x hx =>
    (wpMirSym_eq_wpMirBounded fuel body (init x) _) ▸ h x hx

/-- `wpMirSym` establishes `NeverPanics` on `mirTreesFrom body init`. -/
theorem neverPanics_of_wpMirSym (fuel : Nat)
    (h : ∀ x, pre x →
      wpMirSym fuel body (init x) (fun out => ∃ r, out = .normal r ∧ post x r)) :
    NeverPanics (mirTreesFrom body init) pre post :=
  neverPanics_of_wpMirBounded fuel fun x hx =>
    (wpMirSym_eq_wpMirBounded fuel body (init x) _) ▸ h x hx

/--
`wpMirSym` with the exact classifier establishes the total exact policy contract
on `mirTreesFrom body init`.
-/
theorem totalExactPolicyPanicContract_of_wpMirSym (fuel : Nat)
    (h : ∀ x, pre x →
      wpMirSym fuel body (init x) (ExactPolicyOutcome policy x (post x) (panicCond x))) :
    TotalExactPolicyPanicContract (mirTreesFrom body init) pre post panicCond policy :=
  totalExactPolicyPanicContract_of_wpMirBounded fuel fun x hx =>
    (wpMirSym_eq_wpMirBounded fuel body (init x) _) ▸ h x hx

/--
`wpMirSym` with the exact classifier establishes the total exact panic contract
on `mirTreesFrom body init`.
-/
theorem totalExactPanicContract_of_wpMirSym (fuel : Nat)
    (h : ∀ x, pre x →
      wpMirSym fuel body (init x) (ExactPanicOutcome (post x) (panicCond x))) :
    TotalExactPanicContract (mirTreesFrom body init) pre post panicCond :=
  totalExactPanicContract_of_wpMirBounded fuel fun x hx =>
    (wpMirSym_eq_wpMirBounded fuel body (init x) _) ▸ h x hx

end MirAdequacy

/-! ### Closed and handled trees -/

section ClosedAdequacy

variable {Inp : Type w} {tree : Inp → ITree MirClosedEffect MirOutcome}
  {pre : Inp → Prop} {post : Inp → MirReturn → Prop} {panicCond : Inp → Prop}
  {policy : AbortPolicy Inp}

/--
On closed MIR trees `PanicsWithPolicyOnlyIf` is exactly `DWLP mirClosedWP` with
the policy classifier.
-/
theorem panicsWithPolicyOnlyIf_iff_dwlp_mirClosedWP :
    PanicsWithPolicyOnlyIf tree pre post panicCond policy ↔
      ∀ x, pre x →
        DWLP mirClosedWP (tree x)
          (fun out _ => PolicyOutcomeOk policy x (post x) (panicCond x) out) PUnit.unit :=
  ⟨fun h x hx => dwlp_mirClosedWP_of_treeSafe_reachesRet (h x hx).1 (h x hx).2,
   panicsWithPolicyOnlyIf_of_dwlp⟩

/-- On closed MIR trees `PanicsOnlyIf` is exactly `DWLP mirClosedWP` with the panic classifier. -/
theorem panicsOnlyIf_iff_dwlp_mirClosedWP :
    PanicsOnlyIf tree pre post panicCond ↔
      ∀ x, pre x →
        DWLP mirClosedWP (tree x)
          (fun out _ => PanicOutcomeOk (post x) (panicCond x) out) PUnit.unit :=
  ⟨fun h x hx => dwlp_mirClosedWP_of_treeSafe_reachesRet (h x hx).1 (h x hx).2,
   panicsOnlyIf_of_dwlp⟩

/-- Closed MIR trees have deterministic outcomes. -/
theorem mirClosed_deterministicRet {R : Type} (t : ITree MirClosedEffect R) :
    DeterministicRet t :=
  deterministicRet_of_deterministicAnswers t

private theorem dwp_mirClosedWP_of_reaches {R : Type} {t u : ITree MirClosedEffect R}
    {tr : List (Event MirClosedEffect)} {r : R} {Q : R → Prop}
    (h_reach : Reaches t tr u) (hu : u.observe = .ret r) (hQ : Q r) :
    DWP mirClosedWP t (fun r' _ => Q r') PUnit.unit := by
  induction h_reach with
  | refl =>
    rw [DWP.unfold_eq, hu]
    exact hQ
  | tau hTau _ ih =>
    rw [DWP.unfold_eq, hTau]
    exact ih hu
  | @vis x _ i k _ hVis hnf o _ ih =>
    rw [DWP.unfold_eq, hVis]
    cases i with
    | inl _ => exact False.elim (hnf trivial)
    | inr obs =>
      cases obs with
      | emit _ =>
        cases o
        exact ih hu

/--
Because every non-fault request of `MirClosedEffect` has singleton answer type
`PUnit`, reaching a return satisfying `Q` already establishes total correctness
`DWP mirClosedWP`.
-/
theorem dwp_mirClosedWP_of_reachesRet {R : Type} {t : ITree MirClosedEffect R}
    {tr : List (Event MirClosedEffect)} {r : R} {Q : R → Prop}
    (hr : ReachesRet t tr r) (hQ : Q r) :
    DWP mirClosedWP t (fun r' _ => Q r') PUnit.unit :=
  let ⟨_, h_reach, hu⟩ := hr
  dwp_mirClosedWP_of_reaches h_reach hu hQ

/--
On `MirClosedEffect`, `DWP mirClosedWP` is equivalent to the existence of a
completed execution satisfying the postcondition.
-/
theorem dwp_mirClosedWP_iff_exists_reachesRet {R : Type} (t : ITree MirClosedEffect R)
    (Q : R → Prop) :
    DWP mirClosedWP t (fun r _ => Q r) PUnit.unit ↔ ∃ tr r, ReachesRet t tr r ∧ Q r :=
  ⟨exists_reachesRet_of_dwp mirClosedEffect_nonFault_nonempty,
   fun ⟨_, _, hr, hQ⟩ => dwp_mirClosedWP_of_reachesRet hr hQ⟩

/--
On closed MIR trees an exact panic-or-abort contract makes the panic and the
abort condition mutually exclusive on `pre`.
-/
theorem mirClosed_exactPanicAbortContract_conds_disjoint {abortCond : Inp → Prop}
    {x : Inp} (h : ExactPanicAbortContract tree pre post panicCond abortCond)
    (hx : pre x) : ¬ (panicCond x ∧ abortCond x) :=
  h.conds_disjoint_of_deterministic hx (mirClosed_deterministicRet (tree x))

/--
On closed MIR trees an exact policy contract makes the panic condition and the
abort condition of the policy mutually exclusive on `pre`.
-/
theorem mirClosed_exactPolicyPanicContract_conds_disjoint {x : Inp}
    (h : ExactPolicyPanicContract tree pre post panicCond policy) (hx : pre x) :
    ¬ (panicCond x ∧ policy.allowsAbort x) :=
  h.conds_disjoint_of_deterministic hx (mirClosed_deterministicRet (tree x))

/--
On closed MIR trees an exact policy contract with `waiveAbortUnchecked` has no
normally returning execution on `pre`.
-/
theorem mirClosed_not_returns_of_exactPolicy_waiveAbortUnchecked {x : Inp}
    {tr : List (Event MirClosedEffect)} {r : MirReturn}
    (h : ExactPolicyPanicContract tree pre post panicCond .waiveAbortUnchecked)
    (hx : pre x) : ¬ ReachesRet (tree x) tr (.normal r) :=
  h.not_returns_of_waiveAbortUnchecked hx (mirClosed_deterministicRet (tree x))

end ClosedAdequacy

/-- Handler link for partial correctness: a handler satisfying `C` discharges `mirModularWP C`. -/
private theorem handleMirExternalCalls_links_dwlp
    (C : CallContract MirCallReq (fun _ => MirCallAns))
    (hdl : ExternalCallHandler) (hEnv : envSatisfiesContract C hdl) :
    ∀ (i : MirEffect.I) (Q : MirEffect.O i → PUnit → Prop) (u : PUnit),
      (mirModularWP C).wp i Q u →
      DWLP mirClosedWP (handleMirExternalCalls hdl i) Q u
  | .inl (.fail _), _, .unit, h_wp => False.elim h_wp
  | .inr (.inl (.emit _)), _, .unit, h_wp => DWLP.vis (DWLP.ret h_wp)
  | .inr (.inr (.call req)), Q, .unit, h_wp => hEnv req Q h_wp.1 h_wp.2

/--
A handler implements `C` totally when, on every request satisfying `C.pre`, it
is fault-free, terminates, and answers within `C.post`.
-/
def _root_.Trusted.VerificationResult.MirCallContract.holdsTotallyOn
    (C : MirCallContract) (hdl : ExternalCallHandler) : Prop :=
  ∀ req : MirCallReq, C.pre req →
    DWP mirClosedWP (hdl req) (fun ans _ => C.post req ans) PUnit.unit

/-- A total implementation of `C` is an implementation of `C`. -/
theorem holdsOn_of_holdsTotallyOn {C : MirCallContract} {hdl : ExternalCallHandler}
    (h : C.holdsTotallyOn hdl) : C.holdsOn hdl :=
  fun req hPre => dwlp_pure_adequacy (h req hPre).toDWLP

/-- A total implementation of `C` has a completed execution on every request satisfying `C.pre`. -/
theorem exists_reachesRet_of_holdsTotallyOn {C : MirCallContract}
    {hdl : ExternalCallHandler} (h : C.holdsTotallyOn hdl) {req : MirCallReq}
    (hPre : C.pre req) :
    ∃ tr ans, ReachesRet (hdl req) tr ans ∧ C.post req ans :=
  exists_reachesRet_of_dwp mirClosedEffect_nonFault_nonempty (h req hPre)

/-- Handler link for total correctness: a total implementation of `C` discharges `mirModularWP C`. -/
private theorem handleMirExternalCalls_links_dwp
    (C : MirCallContract) (hdl : ExternalCallHandler) (hTot : C.holdsTotallyOn hdl) :
    ∀ (i : MirEffect.I) (Q : MirEffect.O i → PUnit → Prop) (u : PUnit),
      (mirModularWP C.toCallContract).wp i Q u →
      DWP mirClosedWP (handleMirExternalCalls hdl i) Q u
  | .inl (.fail _), _, .unit, h_wp => False.elim h_wp
  | .inr (.inl (.emit _)), _, .unit, h_wp => DWP.vis (DWP.ret h_wp)
  | .inr (.inr (.call req)), _, .unit, h_wp =>
    DWP.mono (fun ans _ hPost => h_wp.2 ans hPost) (hTot req h_wp.1)

/-- Total-correctness soundness of the symbolic modular evaluator `wpMirModularSym`. -/
theorem dwp_of_wpMirModularSym {C : MirCallContract} {fuel : Nat} {body : CapturedMir}
    {s : MachineState} {Q : MirOutcome → Prop}
    (h : wpMirModularSym C fuel body s Q) :
    DWP (mirModularWP C.toCallContract) (mirTree body s) (fun out _ => Q out) PUnit.unit :=
  dwp_cofix_of_wpCoalBounded fuel
    ((wpMirExecModularSym_eq_wpCoalBounded C fuel body (.running s) Q) ▸ h)

/-- Total-correctness soundness of the symbolic call-free evaluator `wpMirNoCallSym`. -/
theorem dwp_of_wpMirNoCallSym {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {Q : MirOutcome → Prop} (h : wpMirNoCallSym fuel body s Q) :
    DWP mirNoCallWP (mirTree body s) (fun out _ => Q out) PUnit.unit := by
  rw [wpMirNoCallSym_eq_wpMirNoCallBounded] at h
  exact dwp_cofix_of_wpCoalBounded fuel h

section ModularAdequacy

variable {body : CapturedMir} {callees : List CapturedMir}
  {pre : MirInput → Prop} {post : MirInput → MirReturn → Prop}
  {panicCond : MirInput → Prop} {policy : AbortPolicy MirInput}

/--
`DWLP (mirModularWP C)` on the open tree of `body` establishes the
rely–guarantee policy contract against every handler implementing `C`.
-/
theorem mirModularPanicsWithPolicyOnlyIf_of_dwlp (C : MirCallContract)
    (h : ∀ x, pre x →
      DWLP (mirModularWP C.toCallContract) (mirStatefulTrees body callees x)
        (fun out _ => PolicyOutcomeOk policy x (post x) (panicCond x) out) PUnit.unit) :
    MirModularPanicsWithPolicyOnlyIf body C.holdsOn pre post panicCond policy callees :=
  fun hdl hOn =>
    panicsWithPolicyOnlyIf_of_dwlp (ewp := mirClosedWP) fun x hx =>
      dwlp_interp (handleMirExternalCalls hdl)
        (handleMirExternalCalls_links_dwlp C.toCallContract hdl
          (envSatisfiesContract_of_holdsOn C hdl hOn))
        (h x hx)

/--
`DWLP (mirModularWP C)` on the open tree of `body` establishes the
rely–guarantee only-if contract against every handler implementing `C`.
-/
theorem mirModularPanicsOnlyIf_of_dwlp (C : MirCallContract)
    (h : ∀ x, pre x →
      DWLP (mirModularWP C.toCallContract) (mirStatefulTrees body callees x)
        (fun out _ => PanicOutcomeOk (post x) (panicCond x) out) PUnit.unit) :
    MirModularPanicsOnlyIf body C.holdsOn pre post panicCond callees :=
  fun hdl hOn =>
    panicsOnlyIf_of_dwlp (ewp := mirClosedWP) fun x hx =>
      dwlp_interp (handleMirExternalCalls hdl)
        (handleMirExternalCalls_links_dwlp C.toCallContract hdl
          (envSatisfiesContract_of_holdsOn C hdl hOn))
        (h x hx)

/--
`wpMirModularBounded` establishes the rely–guarantee policy contract against
every handler implementing `C`.
-/
theorem mirModularPanicsWithPolicyOnlyIf_of_wpMirModularBounded (C : MirCallContract)
    (fuel : Nat)
    (h : ∀ x : MirInput, pre x →
      wpMirModularBounded fuel C.toCallContract body
        (initMachineStateWithMemoryAndCallees body x.1 x.2 callees)
        (PolicyOutcomeOk policy x (post x) (panicCond x))) :
    MirModularPanicsWithPolicyOnlyIf body C.holdsOn pre post panicCond policy callees :=
  mirModularPanicsWithPolicyOnlyIf_of_dwlp C
    fun x hx => dwlp_cofix_of_wpCoalBounded (h x hx)

/--
`wpMirModularBounded` establishes the rely–guarantee only-if contract against
every handler implementing `C`.
-/
theorem mirModularPanicsOnlyIf_of_wpMirModularBounded (C : MirCallContract)
    (fuel : Nat)
    (h : ∀ x : MirInput, pre x →
      wpMirModularBounded fuel C.toCallContract body
        (initMachineStateWithMemoryAndCallees body x.1 x.2 callees)
        (PanicOutcomeOk (post x) (panicCond x))) :
    MirModularPanicsOnlyIf body C.holdsOn pre post panicCond callees :=
  mirModularPanicsOnlyIf_of_dwlp C
    fun x hx => dwlp_cofix_of_wpCoalBounded (h x hx)

/--
Exact composition: `DWP (mirModularWP C)` with the exact classifier on the open
tree of `body`, linked with a total implementation of `C`, establishes the total
exact policy contract of the handled trees.
-/
theorem mirHandled_totalExactPolicyPanicContract_of_dwp (C : MirCallContract)
    {hdl : ExternalCallHandler} (hTot : C.holdsTotallyOn hdl)
    (h : ∀ x, pre x →
      DWP (mirModularWP C.toCallContract) (mirStatefulTrees body callees x)
        (fun out _ => ExactPolicyOutcome policy x (post x) (panicCond x) out)
        PUnit.unit) :
    TotalExactPolicyPanicContract (mirHandledTrees body hdl callees) pre post panicCond
      policy :=
  totalExactPolicyPanicContract_of_dwp (ewp := mirClosedWP)
    mirClosedEffect_nonFault_nonempty fun x hx =>
      dwp_interp (handleMirExternalCalls hdl)
        (handleMirExternalCalls_links_dwp C hdl hTot) (h x hx)

/--
Exact composition from the bounded modular evaluator: `wpMirModularBounded` with
the exact classifier, linked with a total implementation of `C`, establishes the
total exact policy contract of the handled trees.
-/
theorem mirHandled_totalExactPolicyPanicContract_of_wpMirModularBounded
    (C : MirCallContract) {hdl : ExternalCallHandler} (hTot : C.holdsTotallyOn hdl)
    (fuel : Nat)
    (h : ∀ x : MirInput, pre x →
      wpMirModularBounded fuel C.toCallContract body
        (initMachineStateWithMemoryAndCallees body x.1 x.2 callees)
        (ExactPolicyOutcome policy x (post x) (panicCond x))) :
    TotalExactPolicyPanicContract (mirHandledTrees body hdl callees) pre post panicCond
      policy :=
  mirHandled_totalExactPolicyPanicContract_of_dwp C hTot
    fun x hx => dwp_cofix_of_wpCoalBounded fuel (h x hx)

/--
`wpMirModularSym` establishes the rely–guarantee policy contract against every
handler implementing `C`.
-/
theorem mirModularPanicsWithPolicyOnlyIf_of_wpMirModularSym (C : MirCallContract)
    (fuel : Nat)
    (h : ∀ x : MirInput, pre x →
      wpMirModularSym C fuel body
        (initMachineStateWithMemoryAndCallees body x.1 x.2 callees)
        (PolicyOutcomeOk policy x (post x) (panicCond x))) :
    MirModularPanicsWithPolicyOnlyIf body C.holdsOn pre post panicCond policy callees :=
  mirModularPanicsWithPolicyOnlyIf_of_wpMirModularBounded C fuel fun x hx => by
    rw [wpMirModularBounded, ← wpMirExecModularSym_eq_wpCoalBounded]
    exact h x hx

/--
`wpMirModularSym` establishes the rely–guarantee only-if contract against every
handler implementing `C`.
-/
theorem mirModularPanicsOnlyIf_of_wpMirModularSym (C : MirCallContract)
    (fuel : Nat)
    (h : ∀ x : MirInput, pre x →
      wpMirModularSym C fuel body
        (initMachineStateWithMemoryAndCallees body x.1 x.2 callees)
        (PanicOutcomeOk (post x) (panicCond x))) :
    MirModularPanicsOnlyIf body C.holdsOn pre post panicCond callees :=
  mirModularPanicsOnlyIf_of_wpMirModularBounded C fuel fun x hx => by
    rw [wpMirModularBounded, ← wpMirExecModularSym_eq_wpCoalBounded]
    exact h x hx

/--
Exact composition from the symbolic modular evaluator: `wpMirModularSym` with
the exact classifier, linked with a total implementation of `C`, establishes the
total exact policy contract of the handled trees.
-/
theorem mirHandled_totalExactPolicyPanicContract_of_wpMirModularSym
    (C : MirCallContract) {hdl : ExternalCallHandler} (hTot : C.holdsTotallyOn hdl)
    (fuel : Nat)
    (h : ∀ x : MirInput, pre x →
      wpMirModularSym C fuel body
        (initMachineStateWithMemoryAndCallees body x.1 x.2 callees)
        (ExactPolicyOutcome policy x (post x) (panicCond x))) :
    TotalExactPolicyPanicContract (mirHandledTrees body hdl callees) pre post panicCond
      policy :=
  mirHandled_totalExactPolicyPanicContract_of_wpMirModularBounded C hTot fuel
    fun x hx => by
      rw [wpMirModularBounded, ← wpMirExecModularSym_eq_wpCoalBounded]
      exact h x hx

/-- `DWLP (mirModularWP C)` establishes rely–guarantee `NeverPanics`. -/
theorem mirModularNeverPanics_of_dwlp (C : MirCallContract)
    (h : ∀ x, pre x →
      DWLP (mirModularWP C.toCallContract) (mirStatefulTrees body callees x)
        (fun out _ => ∃ r, out = .normal r ∧ post x r) PUnit.unit) :
    MirModularNeverPanics body C.holdsOn pre post callees :=
  fun hdl hOn =>
    neverPanics_of_dwlp (ewp := mirClosedWP) fun x hx =>
      dwlp_interp (handleMirExternalCalls hdl)
        (handleMirExternalCalls_links_dwlp C.toCallContract hdl
          (envSatisfiesContract_of_holdsOn C hdl hOn))
        (h x hx)

/-- `wpMirModularBounded` establishes rely–guarantee `NeverPanics`. -/
theorem mirModularNeverPanics_of_wpMirModularBounded (C : MirCallContract) (fuel : Nat)
    (h : ∀ x : MirInput, pre x →
      wpMirModularBounded fuel C.toCallContract body
        (initMachineStateWithMemoryAndCallees body x.1 x.2 callees)
        (fun out => ∃ r, out = .normal r ∧ post x r)) :
    MirModularNeverPanics body C.holdsOn pre post callees :=
  mirModularNeverPanics_of_dwlp C
    fun x hx => dwlp_cofix_of_wpCoalBounded (h x hx)

/-- `wpMirModularSym` establishes rely–guarantee `NeverPanics`. -/
theorem mirModularNeverPanics_of_wpMirModularSym (C : MirCallContract) (fuel : Nat)
    (h : ∀ x : MirInput, pre x →
      wpMirModularSym C fuel body
        (initMachineStateWithMemoryAndCallees body x.1 x.2 callees)
        (fun out => ∃ r, out = .normal r ∧ post x r)) :
    MirModularNeverPanics body C.holdsOn pre post callees :=
  mirModularNeverPanics_of_wpMirModularBounded C fuel fun x hx => by
    rw [wpMirModularBounded, ← wpMirExecModularSym_eq_wpCoalBounded]
    exact h x hx

/-- Exact unwinding composition from `DWP (mirModularWP C)`. -/
theorem mirHandled_totalExactPanicContract_of_dwp (C : MirCallContract)
    {hdl : ExternalCallHandler} (hTot : C.holdsTotallyOn hdl)
    (h : ∀ x, pre x →
      DWP (mirModularWP C.toCallContract) (mirStatefulTrees body callees x)
        (fun out _ => ExactPanicOutcome (post x) (panicCond x) out) PUnit.unit) :
    TotalExactPanicContract (mirHandledTrees body hdl callees) pre post panicCond :=
  totalExactPolicyPanicContract_forbidAbort_iff.1
    (mirHandled_totalExactPolicyPanicContract_of_dwp C hTot fun x hx =>
      DWP.mono (fun out _ hOut =>
        (exactPolicyOutcome_forbidAbort_iff x (post x) (panicCond x) out).2 hOut) (h x hx))

/-- Exact unwinding composition from `wpMirModularBounded`. -/
theorem mirHandled_totalExactPanicContract_of_wpMirModularBounded (C : MirCallContract)
    {hdl : ExternalCallHandler} (hTot : C.holdsTotallyOn hdl) (fuel : Nat)
    (h : ∀ x : MirInput, pre x →
      wpMirModularBounded fuel C.toCallContract body
        (initMachineStateWithMemoryAndCallees body x.1 x.2 callees)
        (ExactPanicOutcome (post x) (panicCond x))) :
    TotalExactPanicContract (mirHandledTrees body hdl callees) pre post panicCond :=
  mirHandled_totalExactPanicContract_of_dwp C hTot
    fun x hx => dwp_cofix_of_wpCoalBounded fuel (h x hx)

/-- Exact unwinding composition from `wpMirModularSym`. -/
theorem mirHandled_totalExactPanicContract_of_wpMirModularSym (C : MirCallContract)
    {hdl : ExternalCallHandler} (hTot : C.holdsTotallyOn hdl) (fuel : Nat)
    (h : ∀ x : MirInput, pre x →
      wpMirModularSym C fuel body
        (initMachineStateWithMemoryAndCallees body x.1 x.2 callees)
        (ExactPanicOutcome (post x) (panicCond x))) :
    TotalExactPanicContract (mirHandledTrees body hdl callees) pre post panicCond :=
  mirHandled_totalExactPanicContract_of_wpMirModularBounded C hTot fuel fun x hx => by
    rw [wpMirModularBounded, ← wpMirExecModularSym_eq_wpCoalBounded]
    exact h x hx

end ModularAdequacy

/-! ## 5. Panic Call Contracts and Caller–Callee Composition -/

/--
Panic contract of an external callee, stated on call requests. `pre` is the
caller's obligation at the call site, `post` constrains a normal return,
`panicCond` over-approximates the requests on which the callee may unwind, and
`panicMemInv` constrains the memory the callee presents when it unwinds.

Reference (The Rust Reference, "Call expressions"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/call-expr.html>

> "If the function eventually returns, then the expression completes."
-/
structure PanicMirCallContract : Type where
  /-- Obligation of the caller at the call site. -/
  pre : MirCallReq → Prop := fun _ => True
  /-- Guarantee on a normal return with value `retVal` and memory `memAfter`. -/
  post : MirCallReq → Value → Memory → Prop := fun _ _ _ => True
  /-- The callee unwinds only on requests satisfying `panicCond`. -/
  panicCond : MirCallReq → Prop := fun _ => False
  /-- Invariant of the memory presented to the caller on unwind. -/
  panicMemInv : MirCallReq → Memory → Prop := fun _ _ => True

namespace PanicMirCallContract

/--
Lower a panic call contract to a `MirCallContract` under an abort policy: a
return satisfies `post`, an unwind implies `panicCond` and `panicMemInv`, and an
abort is accepted only as far as `policy` allows.
-/
def toPolicyMirCallContract (P : PanicMirCallContract)
    (policy : AbortPolicy MirCallReq) : MirCallContract where
  pre := P.pre
  post req ans :=
    match ans with
    | .returned retVal memAfter => P.post req retVal memAfter
    | .panicked memAfter => P.panicCond req ∧ P.panicMemInv req memAfter
    | .aborted => policy.allowsAbort req

/-- Lower a panic call contract to a `MirCallContract` that forbids aborts. -/
def toMirCallContract (P : PanicMirCallContract) : MirCallContract :=
  P.toPolicyMirCallContract .forbidAbort

/--
Lower a panic call contract to the exact `MirCallContract` under an abort
policy: the kind of answer is determined by `panicCond` and by the abort
condition of `policy`, which exclude each other.
-/
def toExactPolicyMirCallContract (P : PanicMirCallContract)
    (policy : AbortPolicy MirCallReq) : MirCallContract where
  pre := P.pre
  post req ans :=
    match ans with
    | .returned retVal memAfter =>
      ¬ P.panicCond req ∧ ¬ policy.allowsAbort req ∧ P.post req retVal memAfter
    | .panicked memAfter =>
      (P.panicCond req ∧ ¬ policy.allowsAbort req) ∧ P.panicMemInv req memAfter
    | .aborted => policy.allowsAbort req ∧ ¬ P.panicCond req

/--
Strengthen a panic call contract with `callFramePreserved`: on return and on
unwind the callee hands back the caller's `callees`, `callStack`,
`activeCallee`, `activeProtectors`, and existing `fnPtrs`.
-/
def withFramePreserved (P : PanicMirCallContract) : PanicMirCallContract where
  pre := P.pre
  post req retVal memAfter :=
    P.post req retVal memAfter ∧ callFramePreserved req.memory memAfter
  panicCond := P.panicCond
  panicMemInv req memAfter :=
    P.panicMemInv req memAfter ∧ callFramePreserved req.memory memAfter

/--
Strengthen a panic call contract with `callFramePreserved` and with
preservation of `traitImpls`. `callFramePreserved` alone leaves `traitImpls`
unconstrained, so a first call could register a `TraitImplEntry` that makes
`lookupCallee` resolve the target of a later call to a body in `callees`.
-/
def withTraitsPreserved (P : PanicMirCallContract) : PanicMirCallContract where
  pre := P.pre
  post req retVal memAfter :=
    P.post req retVal memAfter ∧ callFrameAndTraitsPreserved req.memory memAfter
  panicCond := P.panicCond
  panicMemInv req memAfter :=
    P.panicMemInv req memAfter ∧ callFrameAndTraitsPreserved req.memory memAfter

variable (P : PanicMirCallContract) (policy : AbortPolicy MirCallReq)

@[simp]
theorem toPolicyMirCallContract_pre (req : MirCallReq) :
    (P.toPolicyMirCallContract policy).pre req ↔ P.pre req :=
  Iff.rfl

@[simp]
theorem toPolicyMirCallContract_post_returned (req : MirCallReq) (retVal : Value)
    (memAfter : Memory) :
    (P.toPolicyMirCallContract policy).post req (.returned retVal memAfter) ↔
      P.post req retVal memAfter :=
  Iff.rfl

@[simp]
theorem toPolicyMirCallContract_post_panicked (req : MirCallReq) (memAfter : Memory) :
    (P.toPolicyMirCallContract policy).post req (.panicked memAfter) ↔
      P.panicCond req ∧ P.panicMemInv req memAfter :=
  Iff.rfl

@[simp]
theorem toPolicyMirCallContract_post_aborted (req : MirCallReq) :
    (P.toPolicyMirCallContract policy).post req .aborted ↔ policy.allowsAbort req :=
  Iff.rfl

/-- The contract that forbids aborts never accepts `MirCallAns.aborted`. -/
theorem not_toMirCallContract_post_aborted (req : MirCallReq) :
    ¬ P.toMirCallContract.post req .aborted :=
  fun h => h

/-- The exact contract refines the only-if contract with the same policy. -/
theorem toPolicy_post_of_toExactPolicy_post {req : MirCallReq} {ans : MirCallAns}
    (h : (P.toExactPolicyMirCallContract policy).post req ans) :
    (P.toPolicyMirCallContract policy).post req ans := by
  cases ans with
  | returned retVal memAfter => exact h.2.2
  | panicked memAfter => exact ⟨h.1.1, h.2⟩
  | aborted => exact h.1

/-- The only-if contract is monotone in the abort policy. -/
theorem toPolicy_post_mono {policy policy' : AbortPolicy MirCallReq}
    (hLe : policy ≤ policy') {req : MirCallReq} {ans : MirCallAns}
    (h : (P.toPolicyMirCallContract policy).post req ans) :
    (P.toPolicyMirCallContract policy').post req ans := by
  cases ans with
  | returned retVal memAfter => exact h
  | panicked memAfter => exact h
  | aborted => exact hLe req h

/-- Strengthening with trait preservation refines the original contract. -/
theorem toPolicy_post_of_withTraitsPreserved {req : MirCallReq} {ans : MirCallAns}
    (h : (P.withTraitsPreserved.toPolicyMirCallContract policy).post req ans) :
    (P.toPolicyMirCallContract policy).post req ans := by
  cases ans with
  | returned retVal memAfter => exact h.1
  | panicked memAfter => exact ⟨h.1, h.2.1⟩
  | aborted => exact h

/-- Strengthening with frame preservation refines the original contract. -/
theorem toPolicy_post_of_withFramePreserved {req : MirCallReq} {ans : MirCallAns}
    (h : (P.withFramePreserved.toPolicyMirCallContract policy).post req ans) :
    (P.toPolicyMirCallContract policy).post req ans := by
  cases ans with
  | returned retVal memAfter => exact h.1
  | panicked memAfter => exact ⟨h.1, h.2.1⟩
  | aborted => exact h

/-- Trait preservation implies frame preservation. -/
theorem withFramePreserved_post_of_withTraitsPreserved {req : MirCallReq}
    {ans : MirCallAns}
    (h : (P.withTraitsPreserved.toPolicyMirCallContract policy).post req ans) :
    (P.withFramePreserved.toPolicyMirCallContract policy).post req ans := by
  cases ans with
  | returned retVal memAfter => exact ⟨h.1, h.2.1⟩
  | panicked memAfter => exact ⟨h.1, h.2.1, h.2.2.1⟩
  | aborted => exact h

/-- A return accepted by a trait-preserving contract preserves the call frame and `traitImpls`. -/
theorem callFrameAndTraitsPreserved_of_returned {req : MirCallReq} {retVal : Value}
    {memAfter : Memory}
    (h : (P.withTraitsPreserved.toPolicyMirCallContract policy).post req
      (.returned retVal memAfter)) :
    callFrameAndTraitsPreserved req.memory memAfter :=
  h.2

/-- An unwind accepted by a trait-preserving contract preserves the call frame and `traitImpls`. -/
theorem callFrameAndTraitsPreserved_of_panicked {req : MirCallReq} {memAfter : Memory}
    (h : (P.withTraitsPreserved.toPolicyMirCallContract policy).post req
      (.panicked memAfter)) :
    callFrameAndTraitsPreserved req.memory memAfter :=
  h.2.2

/-- Trait preservation on an exact policy contract refines the un-strengthened exact contract. -/
theorem toExactPolicy_post_of_withTraitsPreserved {req : MirCallReq} {ans : MirCallAns}
    (h : (P.withTraitsPreserved.toExactPolicyMirCallContract policy).post req ans) :
    (P.toExactPolicyMirCallContract policy).post req ans := by
  cases ans with
  | returned retVal memAfter => exact ⟨h.1, h.2.1, h.2.2.1⟩
  | panicked memAfter => exact ⟨h.1, h.2.1⟩
  | aborted => exact h

/-- A return accepted by a trait-preserving exact policy contract preserves frame and `traitImpls`. -/
theorem callFrameAndTraitsPreserved_of_toExactPolicy_returned {req : MirCallReq}
    {retVal : Value} {memAfter : Memory}
    (h : (P.withTraitsPreserved.toExactPolicyMirCallContract policy).post req
      (.returned retVal memAfter)) :
    callFrameAndTraitsPreserved req.memory memAfter :=
  h.2.2.2

/-- An unwind accepted by a trait-preserving exact policy contract preserves frame and `traitImpls`. -/
theorem callFrameAndTraitsPreserved_of_toExactPolicy_panicked {req : MirCallReq}
    {memAfter : Memory}
    (h : (P.withTraitsPreserved.toExactPolicyMirCallContract policy).post req
      (.panicked memAfter)) :
    callFrameAndTraitsPreserved req.memory memAfter :=
  h.2.2

/-- A return accepted by a frame-preserving contract preserves the call frame. -/
theorem callFramePreserved_of_returned {req : MirCallReq} {retVal : Value}
    {memAfter : Memory}
    (h : (P.withFramePreserved.toPolicyMirCallContract policy).post req
      (.returned retVal memAfter)) :
    callFramePreserved req.memory memAfter :=
  h.2

/-- An unwind accepted by a frame-preserving contract preserves the call frame. -/
theorem callFramePreserved_of_panicked {req : MirCallReq} {memAfter : Memory}
    (h : (P.withFramePreserved.toPolicyMirCallContract policy).post req
      (.panicked memAfter)) :
    callFramePreserved req.memory memAfter :=
  h.2.2

variable {P} {policy}

theorem holdsOn_toPolicy_of_holdsOn_toExactPolicy {hdl : ExternalCallHandler}
    (h : (P.toExactPolicyMirCallContract policy).holdsOn hdl) :
    (P.toPolicyMirCallContract policy).holdsOn hdl :=
  fun req hPre =>
    ⟨(h req hPre).1, fun tr ans hr =>
      P.toPolicy_post_of_toExactPolicy_post policy ((h req hPre).2 tr ans hr)⟩

theorem holdsOn_toPolicy_mono {policy' : AbortPolicy MirCallReq}
    {hdl : ExternalCallHandler} (hLe : policy ≤ policy')
    (h : (P.toPolicyMirCallContract policy).holdsOn hdl) :
    (P.toPolicyMirCallContract policy').holdsOn hdl :=
  fun req hPre =>
    ⟨(h req hPre).1, fun tr ans hr => P.toPolicy_post_mono hLe ((h req hPre).2 tr ans hr)⟩

theorem holdsOn_of_holdsOn_withTraitsPreserved {hdl : ExternalCallHandler}
    (h : (P.withTraitsPreserved.toPolicyMirCallContract policy).holdsOn hdl) :
    (P.toPolicyMirCallContract policy).holdsOn hdl :=
  fun req hPre =>
    ⟨(h req hPre).1, fun tr ans hr =>
      P.toPolicy_post_of_withTraitsPreserved policy ((h req hPre).2 tr ans hr)⟩

/--
Under the exact contract, the panic condition and the abort condition of the
policy exclude each other on every request whose handler tree completes.
-/
theorem not_panicCond_and_allowsAbort_of_holdsOn_toExactPolicy
    {hdl : ExternalCallHandler} {req : MirCallReq} {tr : List (Event MirClosedEffect)}
    {ans : MirCallAns}
    (h : (P.toExactPolicyMirCallContract policy).holdsOn hdl) (hPre : P.pre req)
    (hr : ReachesRet (hdl req) tr ans) :
    ¬ (P.panicCond req ∧ policy.allowsAbort req) := by
  rintro ⟨hp, ha⟩
  have hPost := (h req hPre).2 tr ans hr
  cases ans with
  | returned retVal memAfter => exact hPost.1 hp
  | panicked memAfter => exact hPost.1.2 ha
  | aborted => exact hPost.2 hp

/--
The unconditional waiver is inconsistent with a normally returning handler under
the exact contract.
-/
theorem not_holdsOn_toExactPolicy_waiveAbortUnchecked_of_returns
    {hdl : ExternalCallHandler} {req : MirCallReq} {tr : List (Event MirClosedEffect)}
    {retVal : Value} {memAfter : Memory} (hPre : P.pre req)
    (hr : ReachesRet (hdl req) tr (.returned retVal memAfter)) :
    ¬ (P.toExactPolicyMirCallContract .waiveAbortUnchecked).holdsOn hdl :=
  fun h => ((h req hPre).2 tr _ hr).2.1 trivial

/--
The unconditional waiver is inconsistent with an unwinding handler under the
exact contract.
-/
theorem not_holdsOn_toExactPolicy_waiveAbortUnchecked_of_panics
    {hdl : ExternalCallHandler} {req : MirCallReq} {tr : List (Event MirClosedEffect)}
    {memAfter : Memory} (hPre : P.pre req)
    (hr : ReachesRet (hdl req) tr (.panicked memAfter)) :
    ¬ (P.toExactPolicyMirCallContract .waiveAbortUnchecked).holdsOn hdl :=
  fun h => ((h req hPre).2 tr _ hr).1.2 trivial

/--
Call rule of the modular transformer for a panic call contract: the caller
establishes `pre` and continues from each kind of answer under the matching
assumption.
-/
theorem mirModularWP_call_iff (P : PanicMirCallContract)
    (policy : AbortPolicy MirCallReq) (req : MirCallReq)
    (Q : MirCallAns → PUnit → Prop) :
    (mirModularWP (P.toPolicyMirCallContract policy).toCallContract).wp
        (.inr (.inr (.call req))) Q PUnit.unit ↔
      P.pre req ∧
        (∀ retVal memAfter, P.post req retVal memAfter →
          Q (.returned retVal memAfter) PUnit.unit) ∧
        (∀ memAfter, P.panicCond req → P.panicMemInv req memAfter →
          Q (.panicked memAfter) PUnit.unit) ∧
        (policy.allowsAbort req → Q .aborted PUnit.unit) := by
  constructor
  · rintro ⟨hPre, hAll⟩
    exact ⟨hPre, fun retVal memAfter hp => hAll (.returned retVal memAfter) hp,
      fun memAfter hc hi => hAll (.panicked memAfter) ⟨hc, hi⟩,
      fun ha => hAll .aborted ha⟩
  · rintro ⟨hPre, hRet, hPanic, hAbort⟩
    refine ⟨hPre, fun resp hp => ?_⟩
    cases resp with
    | returned retVal memAfter => exact hRet retVal memAfter hp
    | panicked memAfter => exact hPanic memAfter hp.1 hp.2
    | aborted => exact hAbort hp

end PanicMirCallContract

/-! ### The answer a linked callee presents -/

@[simp]
theorem outcomeToCallAns_normal (memFallback : Memory) (retVal : Value) (mem' : Memory) :
    outcomeToCallAns memFallback (.normal (retVal, mem')) = .returned retVal mem' :=
  rfl

/-- A panicking callee outcome is presented with the fallback memory. -/
@[simp]
theorem outcomeToCallAns_panic (memFallback : Memory) :
    outcomeToCallAns memFallback .panic = .panicked memFallback :=
  rfl

@[simp]
theorem outcomeToCallAns_abort (memFallback : Memory) :
    outcomeToCallAns memFallback .abort = .aborted :=
  rfl

/--
The policy call contract of the answer a linked callee presents for outcome
`out`, as the policy classifier of `out`. The unwind invariant is evaluated at
the request memory, because `outcomeToCallAns` presents `req.memory` on panic.
-/
theorem PanicMirCallContract.toPolicy_post_outcomeToCallAns_iff
    (P : PanicMirCallContract) (policy : AbortPolicy MirCallReq) (req : MirCallReq)
    (out : MirOutcome) :
    (P.toPolicyMirCallContract policy).post req (outcomeToCallAns req.memory out) ↔
      PolicyOutcomeOk policy req (fun r => P.post req r.1 r.2)
        (P.panicCond req ∧ P.panicMemInv req req.memory) out := by
  cases out with
  | normal r => exact Iff.rfl
  | panic => exact Iff.rfl
  | abort => exact Iff.rfl

/-- Exact policy call contract of `outcomeToCallAns req.memory out` as `ExactPolicyOutcome`. -/
theorem PanicMirCallContract.toExactPolicy_post_outcomeToCallAns_iff
    (P : PanicMirCallContract) (policy : AbortPolicy MirCallReq) (req : MirCallReq)
    (out : MirOutcome)
    (hPanicInv : P.panicCond req → P.panicMemInv req req.memory) :
    (P.toExactPolicyMirCallContract policy).post req (outcomeToCallAns req.memory out) ↔
      ExactPolicyOutcome policy req (fun r => P.post req r.1 r.2) (P.panicCond req) out := by
  cases out with
  | normal r => exact Iff.rfl
  | panic =>
    exact ⟨fun h => h.1, fun h => ⟨h, hPanicInv h.1⟩⟩
  | abort => exact Iff.rfl

/-- `outcomeToRestoredCallAns` on a normal return restores the caller's frame and trait table. -/
@[simp]
theorem outcomeToRestoredCallAns_normal (callerMem : Memory) (retVal : Value) (mem' : Memory) :
    outcomeToRestoredCallAns callerMem (.normal (retVal, mem')) =
      .returned retVal (restoreCallerMemoryFrame callerMem mem') :=
  rfl

/-- `outcomeToRestoredCallAns` also presents `callerMem` on panic. -/
@[simp]
theorem outcomeToRestoredCallAns_panic (callerMem : Memory) :
    outcomeToRestoredCallAns callerMem .panic = .panicked callerMem :=
  rfl

@[simp]
theorem outcomeToRestoredCallAns_abort (callerMem : Memory) :
    outcomeToRestoredCallAns callerMem .abort = .aborted :=
  rfl

/--
The lowered call contract of the frame-restored answer
`outcomeToRestoredCallAns req.memory out`, as an outcome classifier on the
isolated callee: a return is judged on the memory with the caller's frame
restored, and a panic presents `req.memory`.
-/
theorem PanicMirCallContract.toPolicy_post_outcomeToRestoredCallAns_iff
    (P : PanicMirCallContract) (policy : AbortPolicy MirCallReq) (req : MirCallReq)
    (out : MirOutcome) :
    (P.toPolicyMirCallContract policy).post req
        (outcomeToRestoredCallAns req.memory out) ↔
      PolicyOutcomeOk policy req
        (fun r => P.post req r.1 (restoreCallerMemoryFrame req.memory r.2))
        (P.panicCond req ∧ P.panicMemInv req req.memory) out := by
  cases out with
  | normal r => exact Iff.rfl
  | panic => exact Iff.rfl
  | abort => exact Iff.rfl

section AnyAnswer

variable {E : Effect.{u}} {R A B : Type u}

/--
Transformer that accepts every request and quantifies over all of its answers.
Its `DWLP` constrains the returned values of a tree without requiring fault
freedom.
-/
def anyAnswerWP (E : Effect.{u}) : EffectWP E where
  wp _ Q s := ∀ o, Q o s
  mono h_imp h_wp := fun o => h_imp o _ (h_wp o)

/-- A postcondition that holds of every value holds under `anyAnswerWP`. -/
theorem dwlp_anyAnswerWP_of_forall (t : ITree E R) {Q : R → PUnit → Prop}
    (hQ : ∀ r s, Q r s) (s : PUnit) : DWLP (anyAnswerWP E) t Q s := by
  refine DWLP.coinduct (fun _ _ => True) ?_ trivial
  intro x s₀ _
  cases x.observe with
  | ret r => exact hQ r s₀
  | tau _ => trivial
  | vis _ _ => exact fun _ => trivial

private theorem dwlp_anyAnswerWP_reaches [FaultEffect E] {t u : ITree E R}
    {tr : List (Event E)} {Q : R → PUnit → Prop}
    (h_reach : Reaches t tr u) (h : DWLP (anyAnswerWP E) t Q PUnit.unit) :
    DWLP (anyAnswerWP E) u Q PUnit.unit := by
  induction h_reach with
  | refl => exact h
  | tau ht _ ih => rw [DWLP.unfold_eq, ht] at h; exact ih h
  | vis hv _ o _ ih => rw [DWLP.unfold_eq, hv] at h; exact ih (h o)

/-- `DWLP (anyAnswerWP E)` holds of every returned value, on faulting trees too. -/
theorem reachesRet_of_dwlp_anyAnswerWP [FaultEffect E] {t : ITree E R}
    {Q : R → Prop} {tr : List (Event E)} {r : R}
    (h : DWLP (anyAnswerWP E) t (fun r _ => Q r) PUnit.unit)
    (hr : ReachesRet t tr r) : Q r := by
  obtain ⟨u, h_reach, h_ret⟩ := hr
  have hu := dwlp_anyAnswerWP_reaches h_reach h
  rw [DWLP.unfold_eq, h_ret] at hu
  exact hu

/-- Every value returned by `t >>= fun a => pure (f a)` is in the image of `f`. -/
theorem exists_eq_of_reachesRet_bind_pure [FaultEffect E] {t : ITree E A} {f : A → B}
    {tr : List (Event E)} {b : B}
    (hr : ReachesRet (t >>= fun a => (pure (f a) : ITree E B)) tr b) :
    ∃ a, b = f a :=
  have hD : DWLP (anyAnswerWP E) (t >>= fun a => (pure (f a) : ITree E B))
      (fun b _ => ∃ a, b = f a) PUnit.unit :=
    DWLP.bind (dwlp_anyAnswerWP_of_forall t (fun a _ => DWLP.ret ⟨a, rfl⟩) PUnit.unit)
  reachesRet_of_dwlp_anyAnswerWP (Q := fun b => ∃ a, b = f a) hD hr

end AnyAnswer

/-- Every answer of a closed callee tree is `outcomeToCallAns` of some callee outcome. -/
theorem closeMirTreeAsCallAns_reachesRet_eq {memFallback : Memory}
    {t : ITree MirEffect MirOutcome} {tr : List (Event MirClosedEffect)}
    {ans : MirCallAns}
    (hr : ReachesRet (closeMirTreeAsCallAns memFallback t) tr ans) :
    ∃ out, ans = outcomeToCallAns memFallback out :=
  exists_eq_of_reachesRet_bind_pure hr

/--
A closed callee tree unwinds with the fallback memory: `MirOutcome.panic`
carries no `Memory`, so whatever the callee wrote before panicking is absent
from the answer.
-/
theorem closeMirTreeAsCallAns_panicked_memory_eq {memFallback : Memory}
    {t : ITree MirEffect MirOutcome} {tr : List (Event MirClosedEffect)}
    {memAfter : Memory}
    (hr : ReachesRet (closeMirTreeAsCallAns memFallback t) tr (.panicked memAfter)) :
    memAfter = memFallback := by
  obtain ⟨out, hOut⟩ := closeMirTreeAsCallAns_reachesRet_eq hr
  cases out with
  | normal r => nomatch hOut
  | panic => injection hOut
  | abort => nomatch hOut

/-- `linkCalleeHandler` runs the callee on requests that target it. -/
theorem linkCalleeHandler_of_defPath_eq (calleeBody : CapturedMir)
    (fallback : ExternalCallHandler) {req : MirCallReq}
    (hEq : req.defPath = calleeBody.defPath) :
    linkCalleeHandler calleeBody fallback req =
      closeMirTreeAsCallAns req.memory
        (mirStatefulTree calleeBody req.args req.memory) := by
  unfold linkCalleeHandler
  split
  · rfl
  · next hNe => exact False.elim (hNe hEq)

/-- `linkCalleeHandler` defers to the fallback handler on every other request. -/
theorem linkCalleeHandler_of_defPath_ne (calleeBody : CapturedMir)
    (fallback : ExternalCallHandler) {req : MirCallReq}
    (hNe : req.defPath ≠ calleeBody.defPath) :
    linkCalleeHandler calleeBody fallback req = fallback req := by
  unfold linkCalleeHandler
  split
  · next hEq => exact False.elim (hNe hEq)
  · rfl

/--
Pre-panic memory rollback boundary of modular linking. When a linked callee
unwinds, `linkCalleeHandler` presents the caller with exactly `req.memory`, the
memory at the call site. A caller's `UnwindAction.cleanup` block therefore runs
on the pre-call memory, whereas the same callee inlined through `Memory.callees`
unwinds into the cleanup block with every write it performed before panicking
(for example through a `&mut` argument).
-/
theorem linkCalleeHandler_panicked_memory_eq_request_memory (calleeBody : CapturedMir)
    (fallback : ExternalCallHandler) {req : MirCallReq}
    {tr : List (Event MirClosedEffect)} {memAfter : Memory}
    (hEq : req.defPath = calleeBody.defPath)
    (hr : ReachesRet (linkCalleeHandler calleeBody fallback req) tr (.panicked memAfter)) :
    memAfter = req.memory := by
  rw [linkCalleeHandler_of_defPath_eq calleeBody fallback hEq] at hr
  exact closeMirTreeAsCallAns_panicked_memory_eq hr

/--
A linked callee satisfies the unwind invariant `memAfter = req.memory` whatever
it wrote before panicking, so this invariant says nothing about the callee's
writes.
-/
theorem holdsOn_linkCalleeHandler_panicMemInv_request_memory
    (P : PanicMirCallContract) (policy : AbortPolicy MirCallReq)
    (calleeBody : CapturedMir) (fallback : ExternalCallHandler)
    (hTarget : ∀ req, P.pre req → req.defPath = calleeBody.defPath)
    (h : (P.toPolicyMirCallContract policy).holdsOn
      (linkCalleeHandler calleeBody fallback)) :
    ({ P with panicMemInv := fun req memAfter => memAfter = req.memory }
        |>.toPolicyMirCallContract policy).holdsOn
      (linkCalleeHandler calleeBody fallback) := by
  intro req hPre
  refine ⟨(h req hPre).1, fun tr ans hr => ?_⟩
  have hPost := (h req hPre).2 tr ans hr
  cases ans with
  | returned retVal memAfter => exact hPost
  | panicked memAfter =>
    exact ⟨hPost.1, linkCalleeHandler_panicked_memory_eq_request_memory calleeBody
      fallback (hTarget req hPre) hr⟩
  | aborted => exact hPost

/--
Every answer of `closeMirTreeRestoringFrame` is `outcomeToRestoredCallAns` of
some callee outcome.
-/
theorem closeMirTreeRestoringFrame_reachesRet_eq {callerMem : Memory}
    {t : ITree MirEffect MirOutcome} {tr : List (Event MirClosedEffect)}
    {ans : MirCallAns}
    (hr : ReachesRet (closeMirTreeRestoringFrame callerMem t) tr ans) :
    ∃ out, ans = outcomeToRestoredCallAns callerMem out :=
  exists_eq_of_reachesRet_bind_pure hr

/--
Frame-restoring callee linking (`closeMirTreeRestoringFrame`) exhibits the same
pre-panic memory rollback boundary: `.panic` carries no `Memory`, so the answer
always presents `callerMem`.
-/
theorem closeMirTreeRestoringFrame_panicked_memory_eq {callerMem : Memory}
    {t : ITree MirEffect MirOutcome} {tr : List (Event MirClosedEffect)}
    {memAfter : Memory}
    (hr : ReachesRet (closeMirTreeRestoringFrame callerMem t) tr (.panicked memAfter)) :
    memAfter = callerMem := by
  obtain ⟨out, hOut⟩ := closeMirTreeRestoringFrame_reachesRet_eq hr
  cases out with
  | normal r => nomatch hOut
  | panic => injection hOut
  | abort => nomatch hOut

theorem linkCalleeWithCalleesHandler_of_defPath_eq (calleeBody : CapturedMir)
    (calleeCallees : List CapturedMir) (fallback : ExternalCallHandler) {req : MirCallReq}
    (hEq : req.defPath = calleeBody.defPath) :
    linkCalleeWithCalleesHandler calleeBody calleeCallees fallback req =
      closeMirTreeRestoringFrame req.memory
        (mirExternalCalleeTree calleeBody req.args req.memory calleeCallees) := by
  unfold linkCalleeWithCalleesHandler
  split
  · rfl
  · next hNe => exact False.elim (hNe hEq)

theorem linkCalleeWithCalleesHandler_of_defPath_ne (calleeBody : CapturedMir)
    (calleeCallees : List CapturedMir) (fallback : ExternalCallHandler) {req : MirCallReq}
    (hNe : req.defPath ≠ calleeBody.defPath) :
    linkCalleeWithCalleesHandler calleeBody calleeCallees fallback req = fallback req := by
  unfold linkCalleeWithCalleesHandler
  split
  · next hEq => exact False.elim (hNe hEq)
  · rfl

/--
Pre-panic memory rollback boundary for `linkCalleeWithCalleesHandler`: on
unwind, the caller receives `req.memory` regardless of pre-panic mutations.
-/
theorem linkCalleeWithCalleesHandler_panicked_memory_eq_request_memory
    (calleeBody : CapturedMir) (calleeCallees : List CapturedMir)
    (fallback : ExternalCallHandler) {req : MirCallReq}
    {tr : List (Event MirClosedEffect)} {memAfter : Memory}
    (hEq : req.defPath = calleeBody.defPath)
    (hr : ReachesRet (linkCalleeWithCalleesHandler calleeBody calleeCallees fallback req)
      tr (.panicked memAfter)) :
    memAfter = req.memory := by
  rw [linkCalleeWithCalleesHandler_of_defPath_eq calleeBody calleeCallees fallback hEq] at hr
  exact closeMirTreeRestoringFrame_panicked_memory_eq hr

/-! ### Verified callees as handlers -/

private theorem failUnlinkedCalls_links_dwlp :
    ∀ (i : MirEffect.I) (Q : MirEffect.O i → PUnit → Prop) (u : PUnit),
      mirNoCallWP.wp i Q u →
      DWLP mirClosedWP (failUnlinkedCalls i) Q u
  | .inl (.fail _), _, .unit, h_wp => False.elim h_wp
  | .inr (.inl (.emit _)), _, .unit, h_wp => DWLP.vis (DWLP.ret h_wp)
  | .inr (.inr (.call _)), _, .unit, h_wp => False.elim h_wp

private theorem failUnlinkedCalls_links_dwp :
    ∀ (i : MirEffect.I) (Q : MirEffect.O i → PUnit → Prop) (u : PUnit),
      mirNoCallWP.wp i Q u →
      DWP mirClosedWP (failUnlinkedCalls i) Q u
  | .inl (.fail _), _, .unit, h_wp => False.elim h_wp
  | .inr (.inl (.emit _)), _, .unit, h_wp => DWP.vis (DWP.ret h_wp)
  | .inr (.inr (.call _)), _, .unit, h_wp => False.elim h_wp

/--
Closed trees of a callee on call requests: the tree of `calleeBody` from
`(req.args, req.memory)` with every nested unlinked call failing closed. This is
the tree `linkCalleeHandler` runs before converting the outcome to an answer.
-/
def mirClosedCalleeTrees (calleeBody : CapturedMir) :
    MirCallReq → ITree MirClosedEffect MirOutcome :=
  fun req =>
    ITree.interp failUnlinkedCalls (mirStatefulTree calleeBody req.args req.memory)

section ClosedCallee

variable {calleeBody : CapturedMir} {pre : MirCallReq → Prop}
  {post : MirCallReq → MirReturn → Prop} {panicCond : MirCallReq → Prop}
  {policy : AbortPolicy MirCallReq}

/-- `DWLP mirNoCallWP` on the open callee tree establishes the policy contract of the closed callee trees. -/
theorem mirClosedCalleeTrees_panicsWithPolicyOnlyIf_of_dwlp
    (h : ∀ req, pre req →
      DWLP mirNoCallWP (mirStatefulTree calleeBody req.args req.memory)
        (fun out _ => PolicyOutcomeOk policy req (post req) (panicCond req) out)
        PUnit.unit) :
    PanicsWithPolicyOnlyIf (mirClosedCalleeTrees calleeBody) pre post panicCond policy :=
  panicsWithPolicyOnlyIf_of_dwlp (ewp := mirClosedWP) fun req hPre =>
    dwlp_interp failUnlinkedCalls failUnlinkedCalls_links_dwlp (h req hPre)

/-- `wpMirNoCallBounded` establishes the policy contract of the closed callee trees. -/
theorem mirClosedCalleeTrees_panicsWithPolicyOnlyIf_of_wpMirNoCallBounded (fuel : Nat)
    (h : ∀ req, pre req →
      wpMirNoCallBounded fuel calleeBody
        (initMachineStateWithMemory calleeBody req.args req.memory)
        (PolicyOutcomeOk policy req (post req) (panicCond req))) :
    PanicsWithPolicyOnlyIf (mirClosedCalleeTrees calleeBody) pre post panicCond policy :=
  mirClosedCalleeTrees_panicsWithPolicyOnlyIf_of_dwlp
    fun req hPre => dwlp_cofix_of_wpCoalBounded (h req hPre)

/-- `wpMirNoCallBounded` establishes the only-if contract of the closed callee trees. -/
theorem mirClosedCalleeTrees_panicsOnlyIf_of_wpMirNoCallBounded (fuel : Nat)
    (h : ∀ req, pre req →
      wpMirNoCallBounded fuel calleeBody
        (initMachineStateWithMemory calleeBody req.args req.memory)
        (PanicOutcomeOk (post req) (panicCond req))) :
    PanicsOnlyIf (mirClosedCalleeTrees calleeBody) pre post panicCond :=
  panicsOnlyIf_of_dwlp (ewp := mirClosedWP) fun req hPre =>
    dwlp_interp failUnlinkedCalls failUnlinkedCalls_links_dwlp
      (dwlp_cofix_of_wpCoalBounded (h req hPre))

/-- `wpMirNoCallSym` establishes the policy contract of the closed callee trees. -/
theorem mirClosedCalleeTrees_panicsWithPolicyOnlyIf_of_wpMirNoCallSym (fuel : Nat)
    (h : ∀ req, pre req →
      wpMirNoCallSym fuel calleeBody
        (initMachineStateWithMemory calleeBody req.args req.memory)
        (PolicyOutcomeOk policy req (post req) (panicCond req))) :
    PanicsWithPolicyOnlyIf (mirClosedCalleeTrees calleeBody) pre post panicCond policy :=
  mirClosedCalleeTrees_panicsWithPolicyOnlyIf_of_wpMirNoCallBounded fuel fun req hPre =>
    (wpMirNoCallSym_eq_wpMirNoCallBounded fuel calleeBody _ _) ▸ h req hPre

/-- `wpMirNoCallSym` establishes the only-if contract of the closed callee trees. -/
theorem mirClosedCalleeTrees_panicsOnlyIf_of_wpMirNoCallSym (fuel : Nat)
    (h : ∀ req, pre req →
      wpMirNoCallSym fuel calleeBody
        (initMachineStateWithMemory calleeBody req.args req.memory)
        (PanicOutcomeOk (post req) (panicCond req))) :
    PanicsOnlyIf (mirClosedCalleeTrees calleeBody) pre post panicCond :=
  mirClosedCalleeTrees_panicsOnlyIf_of_wpMirNoCallBounded fuel fun req hPre =>
    (wpMirNoCallSym_eq_wpMirNoCallBounded fuel calleeBody _ _) ▸ h req hPre

end ClosedCallee

/--
A callee whose closed trees satisfy the policy contract of `P` induces a
`linkCalleeHandler` that implements the lowered call contract. The callee's
unwind obligation is `panicMemInv` at the request memory, the memory
`outcomeToCallAns` presents on panic. Requests that do not target `calleeBody`
are the fallback handler's obligation.
-/
theorem holdsOn_linkCalleeHandler_of_panicsWithPolicyOnlyIf
    (P : PanicMirCallContract) (policy : AbortPolicy MirCallReq)
    (calleeBody : CapturedMir) (fallback : ExternalCallHandler)
    (hCallee : PanicsWithPolicyOnlyIf (mirClosedCalleeTrees calleeBody)
      (fun req => P.pre req ∧ req.defPath = calleeBody.defPath)
      (fun req r => P.post req r.1 r.2)
      (fun req => P.panicCond req ∧ P.panicMemInv req req.memory) policy)
    (hFallback : ∀ req, P.pre req → req.defPath ≠ calleeBody.defPath →
      TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans →
          (P.toPolicyMirCallContract policy).post req ans) :
    (P.toPolicyMirCallContract policy).holdsOn
      (linkCalleeHandler calleeBody fallback) := by
  intro req hPre
  by_cases hEq : req.defPath = calleeBody.defPath
  · rw [linkCalleeHandler_of_defPath_eq calleeBody fallback hEq]
    have hC := hCallee req ⟨hPre, hEq⟩
    have hD : DWLP mirClosedWP
        (closeMirTreeAsCallAns req.memory
          (mirStatefulTree calleeBody req.args req.memory))
        (fun ans _ => (P.toPolicyMirCallContract policy).post req ans) PUnit.unit := by
      unfold closeMirTreeAsCallAns
      apply DWLP.bind
      exact dwlp_mirClosedWP_of_treeSafe_reachesRet hC.1 fun tr out hr =>
        DWLP.ret ((P.toPolicy_post_outcomeToCallAns_iff policy req out).2 (hC.2 tr out hr))
    exact dwlp_pure_adequacy hD
  · rw [linkCalleeHandler_of_defPath_ne calleeBody fallback hEq]
    exact hFallback req hPre hEq

/--
Variant of `holdsOn_linkCalleeHandler_of_panicsWithPolicyOnlyIf` for a contract
whose `pre` already pins the callee, so no fallback obligation remains.
-/
theorem holdsOn_linkCalleeHandler_of_pre_targets
    (P : PanicMirCallContract) (policy : AbortPolicy MirCallReq)
    (calleeBody : CapturedMir) (fallback : ExternalCallHandler)
    (hTarget : ∀ req, P.pre req → req.defPath = calleeBody.defPath)
    (hCallee : PanicsWithPolicyOnlyIf (mirClosedCalleeTrees calleeBody) P.pre
      (fun req r => P.post req r.1 r.2)
      (fun req => P.panicCond req ∧ P.panicMemInv req req.memory) policy) :
    (P.toPolicyMirCallContract policy).holdsOn
      (linkCalleeHandler calleeBody fallback) :=
  holdsOn_linkCalleeHandler_of_panicsWithPolicyOnlyIf P policy calleeBody fallback
    (hCallee.mono (fun _ h => h.1) (fun _ _ _ hv => hv) (fun _ _ hp => hp)
      (AbortPolicy.le_of_eq rfl))
    (fun req hPre hNe => False.elim (hNe (hTarget req hPre)))

/--
A callee that satisfies `C` totally on its own requests, linked over a fallback
handler that satisfies `C` totally on the others, implements `C` totally.
-/
theorem holdsTotallyOn_linkCalleeHandler (C : MirCallContract)
    (calleeBody : CapturedMir) (fallback : ExternalCallHandler)
    (hCallee : ∀ req, C.pre req → req.defPath = calleeBody.defPath →
      DWP mirNoCallWP (mirStatefulTree calleeBody req.args req.memory)
        (fun out _ => C.post req (outcomeToCallAns req.memory out)) PUnit.unit)
    (hFallback : ∀ req, C.pre req → req.defPath ≠ calleeBody.defPath →
      DWP mirClosedWP (fallback req) (fun ans _ => C.post req ans) PUnit.unit) :
    C.holdsTotallyOn (linkCalleeHandler calleeBody fallback) := by
  intro req hPre
  by_cases hEq : req.defPath = calleeBody.defPath
  · rw [linkCalleeHandler_of_defPath_eq calleeBody fallback hEq]
    unfold closeMirTreeAsCallAns
    apply DWP.bind
    exact DWP.mono (fun _ _ hq => DWP.ret hq)
      (dwp_interp failUnlinkedCalls failUnlinkedCalls_links_dwp (hCallee req hPre hEq))
  · rw [linkCalleeHandler_of_defPath_ne calleeBody fallback hEq]
    exact hFallback req hPre hEq

/-- `holdsTotallyOn_linkCalleeHandler` from the bounded call-free evaluator. -/
theorem holdsTotallyOn_linkCalleeHandler_of_wpMirNoCallBounded (C : MirCallContract)
    (calleeBody : CapturedMir) (fallback : ExternalCallHandler) (fuel : Nat)
    (hTarget : ∀ req, C.pre req → req.defPath = calleeBody.defPath)
    (hCallee : ∀ req, C.pre req →
      wpMirNoCallBounded fuel calleeBody
        (initMachineStateWithMemory calleeBody req.args req.memory)
        (fun out => C.post req (outcomeToCallAns req.memory out))) :
    C.holdsTotallyOn (linkCalleeHandler calleeBody fallback) :=
  holdsTotallyOn_linkCalleeHandler C calleeBody fallback
    (fun req hPre _ => dwp_cofix_of_wpCoalBounded fuel (hCallee req hPre))
    (fun req hPre hNe => False.elim (hNe (hTarget req hPre)))

/-- `holdsTotallyOn_linkCalleeHandler` from the symbolic call-free evaluator. -/
theorem holdsTotallyOn_linkCalleeHandler_of_wpMirNoCallSym (C : MirCallContract)
    (calleeBody : CapturedMir) (fallback : ExternalCallHandler) (fuel : Nat)
    (hTarget : ∀ req, C.pre req → req.defPath = calleeBody.defPath)
    (hCallee : ∀ req, C.pre req →
      wpMirNoCallSym fuel calleeBody
        (initMachineStateWithMemory calleeBody req.args req.memory)
        (fun out => C.post req (outcomeToCallAns req.memory out))) :
    C.holdsTotallyOn (linkCalleeHandler calleeBody fallback) :=
  holdsTotallyOn_linkCalleeHandler_of_wpMirNoCallBounded C calleeBody fallback fuel hTarget
    fun req hPre => (wpMirNoCallSym_eq_wpMirNoCallBounded fuel calleeBody _ _) ▸ hCallee req hPre

/--
Contract-level total linking: a callee whose closed trees satisfy
`TotalExactPolicyPanicContract` (with `panicMemInv` holding on `req.memory`)
induces a `linkCalleeHandler` that satisfies `toExactPolicyMirCallContract`
totally, without dropping down to raw `DWP mirNoCallWP`.
-/
theorem holdsTotallyOn_linkCalleeHandler_of_totalExactPolicy
    (P : PanicMirCallContract) (policy : AbortPolicy MirCallReq)
    (calleeBody : CapturedMir) (fallback : ExternalCallHandler)
    (hPanicInv : ∀ req, P.pre req → req.defPath = calleeBody.defPath →
      P.panicCond req → P.panicMemInv req req.memory)
    (hCallee : TotalExactPolicyPanicContract (mirClosedCalleeTrees calleeBody)
      (fun req => P.pre req ∧ req.defPath = calleeBody.defPath)
      (fun req r => P.post req r.1 r.2) P.panicCond policy)
    (hFallback : ∀ req, P.pre req → req.defPath ≠ calleeBody.defPath →
      DWP mirClosedWP (fallback req)
        (fun ans _ => (P.toExactPolicyMirCallContract policy).post req ans) PUnit.unit) :
    (P.toExactPolicyMirCallContract policy).holdsTotallyOn
      (linkCalleeHandler calleeBody fallback) := by
  intro req hPre
  by_cases hEq : req.defPath = calleeBody.defPath
  · rw [linkCalleeHandler_of_defPath_eq calleeBody fallback hEq]
    obtain ⟨tr, out, hr, hEx⟩ := hCallee.reaches_outcome ⟨hPre, hEq⟩
    unfold closeMirTreeAsCallAns
    apply DWP.bind
    exact dwp_mirClosedWP_of_reachesRet
      (Q := fun out' =>
        DWP mirClosedWP (pure (outcomeToCallAns req.memory out'))
          (fun ans _ => (P.toExactPolicyMirCallContract policy).post req ans) PUnit.unit)
      hr
      (DWP.ret ((P.toExactPolicy_post_outcomeToCallAns_iff policy req out
        (hPanicInv req hPre hEq)).2 hEx))
  · rw [linkCalleeHandler_of_defPath_ne calleeBody fallback hEq]
    exact hFallback req hPre hEq

/--
Closed trees of an isolated external callee (`mirExternalCalleeTree`), matching
the tree `linkCalleeWithCalleesHandler` runs before restoring the caller's frame.
-/
def mirExternalClosedCalleeTrees (calleeBody : CapturedMir)
    (calleeCallees : List CapturedMir := .nil) :
    MirCallReq → ITree MirClosedEffect MirOutcome :=
  fun req =>
    ITree.interp failUnlinkedCalls
      (mirExternalCalleeTree calleeBody req.args req.memory calleeCallees)

section ExternalClosedCallee

variable {calleeBody : CapturedMir} {calleeCallees : List CapturedMir}
  {pre : MirCallReq → Prop} {post : MirCallReq → MirReturn → Prop}
  {panicCond : MirCallReq → Prop} {policy : AbortPolicy MirCallReq}

/--
`DWLP mirNoCallWP` on the isolated callee tree establishes the policy contract
of the isolated closed callee trees.
-/
theorem mirExternalClosedCalleeTrees_panicsWithPolicyOnlyIf_of_dwlp
    (h : ∀ req, pre req →
      DWLP mirNoCallWP (mirExternalCalleeTree calleeBody req.args req.memory calleeCallees)
        (fun out _ => PolicyOutcomeOk policy req (post req) (panicCond req) out)
        PUnit.unit) :
    PanicsWithPolicyOnlyIf (mirExternalClosedCalleeTrees calleeBody calleeCallees)
      pre post panicCond policy :=
  panicsWithPolicyOnlyIf_of_dwlp (ewp := mirClosedWP) fun req hPre =>
    dwlp_interp failUnlinkedCalls failUnlinkedCalls_links_dwlp (h req hPre)

/-- `wpMirNoCallBounded` establishes the policy contract of the isolated closed callee trees. -/
theorem mirExternalClosedCalleeTrees_panicsWithPolicyOnlyIf_of_wpMirNoCallBounded
    (fuel : Nat)
    (h : ∀ req, pre req →
      wpMirNoCallBounded fuel calleeBody
        (enterExternalCalleeState calleeBody req.args req.memory calleeCallees)
        (PolicyOutcomeOk policy req (post req) (panicCond req))) :
    PanicsWithPolicyOnlyIf (mirExternalClosedCalleeTrees calleeBody calleeCallees)
      pre post panicCond policy :=
  mirExternalClosedCalleeTrees_panicsWithPolicyOnlyIf_of_dwlp
    fun req hPre => dwlp_cofix_of_wpCoalBounded (h req hPre)

/-- `wpMirNoCallSym` establishes the policy contract of the isolated closed callee trees. -/
theorem mirExternalClosedCalleeTrees_panicsWithPolicyOnlyIf_of_wpMirNoCallSym
    (fuel : Nat)
    (h : ∀ req, pre req →
      wpMirNoCallSym fuel calleeBody
        (enterExternalCalleeState calleeBody req.args req.memory calleeCallees)
        (PolicyOutcomeOk policy req (post req) (panicCond req))) :
    PanicsWithPolicyOnlyIf (mirExternalClosedCalleeTrees calleeBody calleeCallees)
      pre post panicCond policy :=
  mirExternalClosedCalleeTrees_panicsWithPolicyOnlyIf_of_wpMirNoCallBounded fuel
    fun req hPre => (wpMirNoCallSym_eq_wpMirNoCallBounded fuel calleeBody _ _) ▸ h req hPre

/-- `wpMirNoCallBounded` establishes the only-if contract of the isolated closed callee trees. -/
theorem mirExternalClosedCalleeTrees_panicsOnlyIf_of_wpMirNoCallBounded (fuel : Nat)
    (h : ∀ req, pre req →
      wpMirNoCallBounded fuel calleeBody
        (enterExternalCalleeState calleeBody req.args req.memory calleeCallees)
        (PanicOutcomeOk (post req) (panicCond req))) :
    PanicsOnlyIf (mirExternalClosedCalleeTrees calleeBody calleeCallees)
      pre post panicCond :=
  panicsOnlyIf_of_dwlp (ewp := mirClosedWP) fun req hPre =>
    dwlp_interp failUnlinkedCalls failUnlinkedCalls_links_dwlp
      (dwlp_cofix_of_wpCoalBounded (h req hPre))

/-- `wpMirNoCallSym` establishes the only-if contract of the isolated closed callee trees. -/
theorem mirExternalClosedCalleeTrees_panicsOnlyIf_of_wpMirNoCallSym (fuel : Nat)
    (h : ∀ req, pre req →
      wpMirNoCallSym fuel calleeBody
        (enterExternalCalleeState calleeBody req.args req.memory calleeCallees)
        (PanicOutcomeOk (post req) (panicCond req))) :
    PanicsOnlyIf (mirExternalClosedCalleeTrees calleeBody calleeCallees)
      pre post panicCond :=
  mirExternalClosedCalleeTrees_panicsOnlyIf_of_wpMirNoCallBounded fuel fun req hPre =>
    (wpMirNoCallSym_eq_wpMirNoCallBounded fuel calleeBody _ _) ▸ h req hPre

end ExternalClosedCallee

/--
A callee whose isolated closed trees satisfy the frame-restored policy contract
of `P` induces a `linkCalleeWithCalleesHandler` implementing the lowered call
contract.
-/
theorem holdsOn_linkCalleeWithCalleesHandler_of_panicsWithPolicyOnlyIf
    (P : PanicMirCallContract) (policy : AbortPolicy MirCallReq)
    (calleeBody : CapturedMir) (calleeCallees : List CapturedMir)
    (fallback : ExternalCallHandler)
    (hCallee : PanicsWithPolicyOnlyIf (mirExternalClosedCalleeTrees calleeBody calleeCallees)
      (fun req => P.pre req ∧ req.defPath = calleeBody.defPath)
      (fun req r => P.post req r.1 (restoreCallerMemoryFrame req.memory r.2))
      (fun req => P.panicCond req ∧ P.panicMemInv req req.memory) policy)
    (hFallback : ∀ req, P.pre req → req.defPath ≠ calleeBody.defPath →
      TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans →
          (P.toPolicyMirCallContract policy).post req ans) :
    (P.toPolicyMirCallContract policy).holdsOn
      (linkCalleeWithCalleesHandler calleeBody calleeCallees fallback) := by
  intro req hPre
  by_cases hEq : req.defPath = calleeBody.defPath
  · rw [linkCalleeWithCalleesHandler_of_defPath_eq calleeBody calleeCallees fallback hEq]
    have hC := hCallee req ⟨hPre, hEq⟩
    have hD : DWLP mirClosedWP
        (closeMirTreeRestoringFrame req.memory
          (mirExternalCalleeTree calleeBody req.args req.memory calleeCallees))
        (fun ans _ => (P.toPolicyMirCallContract policy).post req ans) PUnit.unit := by
      unfold closeMirTreeRestoringFrame
      apply DWLP.bind
      exact dwlp_mirClosedWP_of_treeSafe_reachesRet hC.1 fun tr out hr => by
        have hOk := hC.2 tr out hr
        cases out with
        | normal r => exact DWLP.ret hOk
        | panic => exact DWLP.ret hOk
        | abort => exact DWLP.ret hOk
    exact dwlp_pure_adequacy hD
  · rw [linkCalleeWithCalleesHandler_of_defPath_ne calleeBody calleeCallees fallback hEq]
    exact hFallback req hPre hEq

/--
Total handler linking for `linkCalleeWithCalleesHandler`: handles arbitrary
caller `callStack` / `activeCallee` / `activeProtectors` and restores the
caller's call frame and `traitImpls` upon return.
-/
theorem holdsTotallyOn_linkCalleeWithCalleesHandler (C : MirCallContract)
    (calleeBody : CapturedMir) (calleeCallees : List CapturedMir)
    (fallback : ExternalCallHandler)
    (hCallee : ∀ req, C.pre req → req.defPath = calleeBody.defPath →
      DWP mirNoCallWP
        (mirExternalCalleeTree calleeBody req.args req.memory calleeCallees)
        (fun out _ => C.post req (outcomeToRestoredCallAns req.memory out)) PUnit.unit)
    (hFallback : ∀ req, C.pre req → req.defPath ≠ calleeBody.defPath →
      DWP mirClosedWP (fallback req) (fun ans _ => C.post req ans) PUnit.unit) :
    C.holdsTotallyOn (linkCalleeWithCalleesHandler calleeBody calleeCallees fallback) := by
  intro req hPre
  by_cases hEq : req.defPath = calleeBody.defPath
  · rw [linkCalleeWithCalleesHandler_of_defPath_eq calleeBody calleeCallees fallback hEq]
    unfold closeMirTreeRestoringFrame
    apply DWP.bind
    exact DWP.mono (fun _ _ hq => DWP.ret hq)
      (dwp_interp failUnlinkedCalls failUnlinkedCalls_links_dwp (hCallee req hPre hEq))
  · rw [linkCalleeWithCalleesHandler_of_defPath_ne calleeBody calleeCallees fallback hEq]
    exact hFallback req hPre hEq

/-- `holdsTotallyOn_linkCalleeWithCalleesHandler` from `wpMirNoCallSym`. -/
theorem holdsTotallyOn_linkCalleeWithCalleesHandler_of_wpMirNoCallSym (C : MirCallContract)
    (calleeBody : CapturedMir) (calleeCallees : List CapturedMir)
    (fallback : ExternalCallHandler) (fuel : Nat)
    (hTarget : ∀ req, C.pre req → req.defPath = calleeBody.defPath)
    (hCallee : ∀ req, C.pre req →
      wpMirNoCallSym fuel calleeBody
        (enterExternalCalleeState calleeBody req.args req.memory calleeCallees)
        (fun out => C.post req (outcomeToRestoredCallAns req.memory out))) :
    C.holdsTotallyOn (linkCalleeWithCalleesHandler calleeBody calleeCallees fallback) :=
  holdsTotallyOn_linkCalleeWithCalleesHandler C calleeBody calleeCallees fallback
    (fun req hPre _ => dwp_of_wpMirNoCallSym (hCallee req hPre))
    (fun req hPre hNe => False.elim (hNe (hTarget req hPre)))

/-! ### Horizontal composition -/

section Compose

variable {callerBody calleeBody : CapturedMir} {callees : List CapturedMir}
  {fallback : ExternalCallHandler}
  {pre : MirInput → Prop} {post : MirInput → MirReturn → Prop}
  {panicCond : MirInput → Prop} {policy : AbortPolicy MirInput}

/--
Horizontal composition of policy contracts. A caller verified against every
handler implementing the lowered contract of `P`, linked through
`linkCalleeHandler` with a callee whose closed trees satisfy the policy contract
of `P`, satisfies its own policy contract: the linked system is fault-free on
every branch, and its panics and aborts are the ones the caller's contract
admits.
-/
theorem panicsWithPolicyOnlyIf_call_compose (P : PanicMirCallContract)
    (calleePolicy : AbortPolicy MirCallReq)
    (hCaller : MirModularPanicsWithPolicyOnlyIf callerBody
      (P.toPolicyMirCallContract calleePolicy).holdsOn pre post panicCond policy callees)
    (hCallee : PanicsWithPolicyOnlyIf (mirClosedCalleeTrees calleeBody)
      (fun req => P.pre req ∧ req.defPath = calleeBody.defPath)
      (fun req r => P.post req r.1 r.2)
      (fun req => P.panicCond req ∧ P.panicMemInv req req.memory) calleePolicy)
    (hFallback : ∀ req, P.pre req → req.defPath ≠ calleeBody.defPath →
      TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans →
          (P.toPolicyMirCallContract calleePolicy).post req ans) :
    PanicsWithPolicyOnlyIf
      (mirHandledTrees callerBody (linkCalleeHandler calleeBody fallback) callees)
      pre post panicCond policy :=
  hCaller _
    (holdsOn_linkCalleeHandler_of_panicsWithPolicyOnlyIf P calleePolicy calleeBody
      fallback hCallee hFallback)

/--
Horizontal composition of unwinding panic contracts. A caller satisfying
`MirModularPanicsOnlyIf` against the lowered contract of `P`, linked with a
callee satisfying `PanicsOnlyIf` on its closed trees, satisfies `PanicsOnlyIf`:
the linked system is fault-free on every branch, never aborts, and panics only
under the caller's `panicCond`.
-/
theorem panicsOnlyIf_call_compose (P : PanicMirCallContract)
    (hCaller : MirModularPanicsOnlyIf callerBody P.toMirCallContract.holdsOn
      pre post panicCond callees)
    (hCallee : PanicsOnlyIf (mirClosedCalleeTrees calleeBody)
      (fun req => P.pre req ∧ req.defPath = calleeBody.defPath)
      (fun req r => P.post req r.1 r.2)
      (fun req => P.panicCond req ∧ P.panicMemInv req req.memory))
    (hFallback : ∀ req, P.pre req → req.defPath ≠ calleeBody.defPath →
      TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans →
          P.toMirCallContract.post req ans) :
    PanicsOnlyIf
      (mirHandledTrees callerBody (linkCalleeHandler calleeBody fallback) callees)
      pre post panicCond :=
  hCaller _
    (holdsOn_linkCalleeHandler_of_panicsWithPolicyOnlyIf P .forbidAbort calleeBody
      fallback (panicsWithPolicyOnlyIf_forbidAbort_iff.2 hCallee) hFallback)

/--
Horizontal composition for a caller verified with the modular transformer:
`DWLP (mirModularWP …)` on the caller's open tree and a verified callee give the
policy contract of the linked system.
-/
theorem panicsWithPolicyOnlyIf_call_compose_of_dwlp (P : PanicMirCallContract)
    (calleePolicy : AbortPolicy MirCallReq)
    (hCaller : ∀ x, pre x →
      DWLP (mirModularWP (P.toPolicyMirCallContract calleePolicy).toCallContract)
        (mirStatefulTrees callerBody callees x)
        (fun out _ => PolicyOutcomeOk policy x (post x) (panicCond x) out) PUnit.unit)
    (hCallee : PanicsWithPolicyOnlyIf (mirClosedCalleeTrees calleeBody)
      (fun req => P.pre req ∧ req.defPath = calleeBody.defPath)
      (fun req r => P.post req r.1 r.2)
      (fun req => P.panicCond req ∧ P.panicMemInv req req.memory) calleePolicy)
    (hFallback : ∀ req, P.pre req → req.defPath ≠ calleeBody.defPath →
      TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans →
          (P.toPolicyMirCallContract calleePolicy).post req ans) :
    PanicsWithPolicyOnlyIf
      (mirHandledTrees callerBody (linkCalleeHandler calleeBody fallback) callees)
      pre post panicCond policy :=
  panicsWithPolicyOnlyIf_call_compose P calleePolicy
    (mirModularPanicsWithPolicyOnlyIf_of_dwlp _ hCaller) hCallee hFallback

/--
Exact horizontal composition. A caller verified with `DWP (mirModularWP C)`
against the exact classifier, linked with a callee that implements `C` totally,
satisfies the total exact policy contract: besides fault freedom, the linked
system panics exactly under `panicCond`, aborts exactly under the abort
condition of the policy, and returns otherwise.
-/
theorem totalExactPolicyPanicContract_call_compose (C : MirCallContract)
    (hCaller : ∀ x, pre x →
      DWP (mirModularWP C.toCallContract) (mirStatefulTrees callerBody callees x)
        (fun out _ => ExactPolicyOutcome policy x (post x) (panicCond x) out)
        PUnit.unit)
    (hCallee : ∀ req, C.pre req → req.defPath = calleeBody.defPath →
      DWP mirNoCallWP (mirStatefulTree calleeBody req.args req.memory)
        (fun out _ => C.post req (outcomeToCallAns req.memory out)) PUnit.unit)
    (hFallback : ∀ req, C.pre req → req.defPath ≠ calleeBody.defPath →
      DWP mirClosedWP (fallback req) (fun ans _ => C.post req ans) PUnit.unit) :
    TotalExactPolicyPanicContract
      (mirHandledTrees callerBody (linkCalleeHandler calleeBody fallback) callees)
      pre post panicCond policy :=
  mirHandled_totalExactPolicyPanicContract_of_dwp C
    (holdsTotallyOn_linkCalleeHandler C calleeBody fallback hCallee hFallback) hCaller

/--
Contract-level exact horizontal composition: links a modularly verified caller
directly against a callee's `TotalExactPolicyPanicContract` on its closed trees.
-/
theorem totalExactPolicyPanicContract_call_compose_of_callee_contract
    (P : PanicMirCallContract) (calleePolicy : AbortPolicy MirCallReq)
    (hCaller : ∀ x, pre x →
      DWP (mirModularWP (P.toExactPolicyMirCallContract calleePolicy).toCallContract)
        (mirStatefulTrees callerBody callees x)
        (fun out _ => ExactPolicyOutcome policy x (post x) (panicCond x) out)
        PUnit.unit)
    (hPanicInv : ∀ req, P.pre req → req.defPath = calleeBody.defPath →
      P.panicCond req → P.panicMemInv req req.memory)
    (hCallee : TotalExactPolicyPanicContract (mirClosedCalleeTrees calleeBody)
      (fun req => P.pre req ∧ req.defPath = calleeBody.defPath)
      (fun req r => P.post req r.1 r.2) P.panicCond calleePolicy)
    (hFallback : ∀ req, P.pre req → req.defPath ≠ calleeBody.defPath →
      DWP mirClosedWP (fallback req)
        (fun ans _ => (P.toExactPolicyMirCallContract calleePolicy).post req ans)
        PUnit.unit) :
    TotalExactPolicyPanicContract
      (mirHandledTrees callerBody (linkCalleeHandler calleeBody fallback) callees)
      pre post panicCond policy :=
  mirHandled_totalExactPolicyPanicContract_of_dwp
    (P.toExactPolicyMirCallContract calleePolicy)
    (holdsTotallyOn_linkCalleeHandler_of_totalExactPolicy P calleePolicy calleeBody
      fallback hPanicInv hCallee hFallback)
    hCaller

/-- Exact unwinding horizontal composition specializing `policy = .forbidAbort`. -/
theorem totalExactPanicContract_call_compose (C : MirCallContract)
    (hCaller : ∀ x, pre x →
      DWP (mirModularWP C.toCallContract) (mirStatefulTrees callerBody callees x)
        (fun out _ => ExactPanicOutcome (post x) (panicCond x) out) PUnit.unit)
    (hCallee : ∀ req, C.pre req → req.defPath = calleeBody.defPath →
      DWP mirNoCallWP (mirStatefulTree calleeBody req.args req.memory)
        (fun out _ => C.post req (outcomeToCallAns req.memory out)) PUnit.unit)
    (hFallback : ∀ req, C.pre req → req.defPath ≠ calleeBody.defPath →
      DWP mirClosedWP (fallback req) (fun ans _ => C.post req ans) PUnit.unit) :
    TotalExactPanicContract
      (mirHandledTrees callerBody (linkCalleeHandler calleeBody fallback) callees)
      pre post panicCond :=
  totalExactPolicyPanicContract_forbidAbort_iff.1
    (totalExactPolicyPanicContract_call_compose C
      (fun x hx => DWP.mono
        (fun out _ hOut => (exactPolicyOutcome_forbidAbort_iff x (post x) (panicCond x) out).2 hOut)
        (hCaller x hx))
      hCallee hFallback)

/-- Horizontal policy composition via frame-restoring `linkCalleeWithCalleesHandler`. -/
theorem panicsWithPolicyOnlyIf_call_compose_withCallees (P : PanicMirCallContract)
    (calleePolicy : AbortPolicy MirCallReq) (calleeCallees : List CapturedMir)
    (hCaller : MirModularPanicsWithPolicyOnlyIf callerBody
      (P.toPolicyMirCallContract calleePolicy).holdsOn pre post panicCond policy callees)
    (hCallee : PanicsWithPolicyOnlyIf (mirExternalClosedCalleeTrees calleeBody calleeCallees)
      (fun req => P.pre req ∧ req.defPath = calleeBody.defPath)
      (fun req r => P.post req r.1 (restoreCallerMemoryFrame req.memory r.2))
      (fun req => P.panicCond req ∧ P.panicMemInv req req.memory) calleePolicy)
    (hFallback : ∀ req, P.pre req → req.defPath ≠ calleeBody.defPath →
      TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans →
          (P.toPolicyMirCallContract calleePolicy).post req ans) :
    PanicsWithPolicyOnlyIf
      (mirHandledTrees callerBody
        (linkCalleeWithCalleesHandler calleeBody calleeCallees fallback) callees)
      pre post panicCond policy :=
  hCaller _
    (holdsOn_linkCalleeWithCalleesHandler_of_panicsWithPolicyOnlyIf P calleePolicy calleeBody
      calleeCallees fallback hCallee hFallback)

/-- Horizontal unwinding composition via frame-restoring `linkCalleeWithCalleesHandler`. -/
theorem panicsOnlyIf_call_compose_withCallees (P : PanicMirCallContract)
    (calleeCallees : List CapturedMir)
    (hCaller : MirModularPanicsOnlyIf callerBody P.toMirCallContract.holdsOn
      pre post panicCond callees)
    (hCallee : PanicsOnlyIf (mirExternalClosedCalleeTrees calleeBody calleeCallees)
      (fun req => P.pre req ∧ req.defPath = calleeBody.defPath)
      (fun req r => P.post req r.1 (restoreCallerMemoryFrame req.memory r.2))
      (fun req => P.panicCond req ∧ P.panicMemInv req req.memory))
    (hFallback : ∀ req, P.pre req → req.defPath ≠ calleeBody.defPath →
      TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans →
          P.toMirCallContract.post req ans) :
    PanicsOnlyIf
      (mirHandledTrees callerBody
        (linkCalleeWithCalleesHandler calleeBody calleeCallees fallback) callees)
      pre post panicCond :=
  hCaller _
    (holdsOn_linkCalleeWithCalleesHandler_of_panicsWithPolicyOnlyIf P .forbidAbort calleeBody
      calleeCallees fallback (panicsWithPolicyOnlyIf_forbidAbort_iff.2 hCallee) hFallback)

end Compose

/-! ### Refuting linked contracts -/

section BindReach

variable {E : Effect.{u}} [FaultEffect E] {A B : Type u}

/-- Reachability is preserved by sequencing a continuation after the tree. -/
theorem reaches_bind {t u : ITree E A} {tr : List (Event E)} (f : A → ITree E B)
    (h : Reaches t tr u) : Reaches (t >>= f) tr (u >>= f) := by
  induction h with
  | refl x => exact .refl _
  | @tau x x' _ _ hTau _ ih =>
    have hx : x = ITree.tau x' :=
      ITree.eq_of_observe_eq (hTau.trans (ITree.observe_tau _).symm)
    rw [hx, tau_bind]
    exact .tau (ITree.observe_tau _) ih
  | @vis x _ i k _ hVis hnf o _ ih =>
    have hx : x = ITree.vis i k :=
      ITree.eq_of_observe_eq (hVis.trans (ITree.observe_vis _ _).symm)
    rw [hx, vis_bind]
    exact .vis (ITree.observe_vis _ _) hnf o ih

/-- A completed execution of `t` with result `a` continues as `f a` in `t >>= f`. -/
theorem reaches_bind_of_reachesRet {t : ITree E A} {tr : List (Event E)} {a : A}
    (f : A → ITree E B) (h : ReachesRet t tr a) : Reaches (t >>= f) tr (f a) := by
  obtain ⟨u, hr, hu⟩ := h
  have hx : u = ITree.ret a :=
    ITree.eq_of_observe_eq (hu.trans (ITree.observe_ret a).symm)
  have hb := reaches_bind f hr
  rwa [hx, ret_bind] at hb

/-- A fault reached silently by `t` is reached silently by `t >>= f`. -/
theorem faultNow_bind {t : ITree E A} (f : A → ITree E B) (h : FaultNow t) :
    FaultNow (t >>= f) := by
  obtain ⟨u, i, k, hTau, hObs, hF⟩ := h
  have hu : u = ITree.vis i k :=
    ITree.eq_of_observe_eq (hObs.trans (ITree.observe_vis _ _).symm)
  refine ⟨u >>= f, i, fun o => k o >>= f, TauStar.bind f hTau, ?_, hF⟩
  rw [hu, vis_bind, ITree.observe_vis]

/-- Sequencing a continuation cannot repair a fault of the first tree. -/
theorem not_treeSafe_bind {t : ITree E A} (f : A → ITree E B) (h : ¬ TreeSafe t) :
    ¬ TreeSafe (t >>= f) := fun hs =>
  h fun tr u hr hF => hs tr (u >>= f) (reaches_bind f hr) (faultNow_bind f hF)

/-- A tree whose first step is silent is safe only if its residual is. -/
theorem treeSafe_of_treeSafe_tau {t : ITree E A} (h : TreeSafe (ITree.tau t)) :
    TreeSafe t :=
  treeSafe_residual h (Reaches.tau (ITree.observe_tau t) (.refl t))

end BindReach

section InterpCofix

variable {S : Type} {E₁ E₂ : Effect.{0}} {R : Type}

private theorem interp_cofix_tau (H : (i : E₁.I) → ITree E₂ (E₁.O i))
    {step : S → ITreeF E₁ R S} {st st' : S} (h : step st = .tau st') :
    ITree.interp H (ITree.cofix step st) =
      ITree.tau (ITree.interp H (ITree.cofix step st')) := by
  have hEq : ITree.cofix step st = ITree.tau (ITree.cofix step st') := by
    apply ITree.eq_of_observe_eq
    rw [ITree.observe_cofix, h, ITree.observe_tau]
    rfl
  rw [hEq, interp_tau]

private theorem interp_cofix_vis (H : (i : E₁.I) → ITree E₂ (E₁.O i))
    {step : S → ITreeF E₁ R S} {st : S} {i : E₁.I} {k : E₁.O i → S}
    (h : step st = .vis i k) :
    ITree.interp H (ITree.cofix step st) =
      (H i >>= fun o => ITree.tau (ITree.interp H (ITree.cofix step (k o)))) := by
  have hEq : ITree.cofix step st = ITree.vis i (fun o => ITree.cofix step (k o)) := by
    apply ITree.eq_of_observe_eq
    rw [ITree.observe_cofix, h, ITree.observe_vis]
    rfl
  rw [hEq, interp_vis]

end InterpCofix

private theorem reachesRet_emit_mirClosed (obs : MirObs) :
    ∃ tr, ReachesRet (ITree.emit (E := MirClosedEffect) obs) tr PUnit.unit := by
  unfold ITree.emit ITree.triggerSub
  exact ⟨_, _, .vis (ITree.observe_vis _ _) (fun hF => hF) PUnit.unit (.refl _),
    ITree.observe_ret _⟩

/--
Residual of `body` from the execution state `st` with every external call
answered by the handler `h`.
-/
def mirHandledFrom (body : CapturedMir) (h : ExternalCallHandler) (st : MirExecState) :
    ITree MirClosedEffect MirOutcome :=
  ITree.interp (handleMirExternalCalls h) (ITree.cofix (stepMirState body) st)

/-- `mirHandledTrees` is the handled residual from the initial state. -/
theorem mirHandledTrees_eq_mirHandledFrom (body : CapturedMir) (h : ExternalCallHandler)
    (callees : List CapturedMir) (x : MirInput) :
    mirHandledTrees body h callees x =
      mirHandledFrom body h
        (.running (initMachineStateWithMemoryAndCallees body x.1 x.2 callees)) :=
  rfl

/--
The linked execution of `body` from `st` under the handler `h` reaches a fault.
Each constructor follows one step of `stepMirState`: a fault, a silent step, an
observation, an external call answered by a completed execution of `h`, or an
external call on which `h` itself is not fault-free.

A derivation is a finite counterexample trace. It refutes every panic contract
of the linked system on a precondition that contains the input, whatever the
postcondition, the panic condition, and the abort policy.
-/
inductive ReachesLinkedFault (body : CapturedMir) (h : ExternalCallHandler) :
    MirExecState → Prop where
  /-- The next step is a fault request. -/
  | fail {st : MirExecState} {f : FailReq FailureKind} {k : PEmpty → MirExecState} :
      stepMirState body st = .vis (.inl f) k → ReachesLinkedFault body h st
  /-- The next step is silent and the residual reaches a fault. -/
  | tau {st st' : MirExecState} :
      stepMirState body st = .tau st' → ReachesLinkedFault body h st' →
      ReachesLinkedFault body h st
  /-- The next step is an observation and the residual reaches a fault. -/
  | obs {st : MirExecState} {ev : ObsReq MirObs} {k : PUnit → MirExecState} :
      stepMirState body st = .vis (.inr (.inl ev)) k →
      ReachesLinkedFault body h (k PUnit.unit) → ReachesLinkedFault body h st
  /-- The next step is a call, `h` answers `ans`, and the resumed residual reaches a fault. -/
  | call {st : MirExecState} {req : MirCallReq} {k : MirCallAns → MirExecState}
      {tr : List (Event MirClosedEffect)} {ans : MirCallAns} :
      stepMirState body st = MirStepNode.extCall req k →
      ReachesRet (h req) tr ans → ReachesLinkedFault body h (k ans) →
      ReachesLinkedFault body h st
  /-- The next step is a call on which `h` is not fault-free. -/
  | handler {st : MirExecState} {req : MirCallReq} {k : MirCallAns → MirExecState} :
      stepMirState body st = MirStepNode.extCall req k → ¬ TreeSafe (h req) →
      ReachesLinkedFault body h st

/-- A linked fault makes the handled residual unsafe. -/
theorem ReachesLinkedFault.not_treeSafe {body : CapturedMir} {h : ExternalCallHandler}
    {st : MirExecState} (hF : ReachesLinkedFault body h st) :
    ¬ TreeSafe (mirHandledFrom body h st) := by
  induction hF with
  | @fail st f k hStep =>
    intro hs
    unfold mirHandledFrom at hs
    cases f with
    | fail fk =>
      rw [interp_cofix_vis (E₁ := MirEffect) (handleMirExternalCalls h)
        (i := Sum.inl (FailReq.fail fk)) (k := k) hStep] at hs
      exact hs [] _ (.refl _) (faultNow_bind _ (faultNow_fail fk))
  | @tau st st' hStep _ ih =>
    intro hs
    unfold mirHandledFrom at hs
    rw [interp_cofix_tau (handleMirExternalCalls h) hStep] at hs
    exact ih (treeSafe_of_treeSafe_tau hs)
  | @obs st ev k hStep _ ih =>
    intro hs
    unfold mirHandledFrom at hs
    rw [interp_cofix_vis (E₁ := MirEffect) (handleMirExternalCalls h)
      (i := Sum.inr (Sum.inl ev)) (k := k) hStep] at hs
    cases ev with
    | emit obsEv =>
      obtain ⟨tr, hEmit⟩ := reachesRet_emit_mirClosed obsEv
      exact ih (treeSafe_of_treeSafe_tau
        (treeSafe_residual hs (reaches_bind_of_reachesRet _ hEmit)))
  | @call st req k tr ans hStep hAns _ ih =>
    intro hs
    unfold mirHandledFrom at hs
    rw [interp_cofix_vis (E₁ := MirEffect) (handleMirExternalCalls h)
      (i := Sum.inr (Sum.inr (CallReq.call req))) (k := k) hStep] at hs
    exact ih (treeSafe_of_treeSafe_tau
      (treeSafe_residual hs (reaches_bind_of_reachesRet _ hAns)))
  | @handler st req k hStep hBad =>
    intro hs
    unfold mirHandledFrom at hs
    rw [interp_cofix_vis (E₁ := MirEffect) (handleMirExternalCalls h)
      (i := Sum.inr (Sum.inr (CallReq.call req))) (k := k) hStep] at hs
    exact not_treeSafe_bind _ hBad hs

/--
A fault found by the call-free bounded detector `reachesFaultExecBounded` is a
linked fault under every handler: the detector follows silent steps and
observations only, so no handler answer is involved.
-/
theorem ReachesLinkedFault.of_reachesFaultExecBounded {body : CapturedMir}
    (h : ExternalCallHandler) (fuel : Nat) {st : MirExecState}
    (hFault : reachesFaultExecBounded fuel body st = true) :
    ReachesLinkedFault body h st := by
  induction fuel generalizing st with
  | zero => nomatch hFault
  | succ fuel' ih =>
    unfold reachesFaultExecBounded at hFault
    rw [stepMirStatePeriodic_eq] at hFault
    cases hStep : stepMirState body st with
    | ret _ =>
      simp only [hStep] at hFault
      nomatch hFault
    | tau st' =>
      simp only [hStep] at hFault
      exact .tau hStep (ih hFault)
    | vis i k =>
      rcases i with f | (e | c)
      · exact .fail hStep
      · simp only [hStep] at hFault
        exact .obs hStep (ih hFault)
      · simp only [hStep] at hFault
        nomatch hFault

section LinkedRefutation

variable {body : CapturedMir} {h : ExternalCallHandler} {callees : List CapturedMir}
  {pre : MirInput → Prop} {post : MirInput → MirReturn → Prop}
  {panicCond : MirInput → Prop} {policy : AbortPolicy MirInput} {x : MirInput}

/--
A linked fault from the initial state of an input in `pre` refutes every policy
contract of the linked system, for every `post`, `panicCond`, and `policy`.
-/
theorem not_panicsWithPolicyOnlyIf_of_reachesLinkedFault (hx : pre x)
    (hF : ReachesLinkedFault body h
      (.running (initMachineStateWithMemoryAndCallees body x.1 x.2 callees))) :
    ¬ PanicsWithPolicyOnlyIf (mirHandledTrees body h callees) pre post panicCond policy :=
  fun hC => hF.not_treeSafe (hC x hx).1

/-- A linked fault from the initial state of an input in `pre` refutes `PanicsOnlyIf`. -/
theorem not_panicsOnlyIf_of_reachesLinkedFault (hx : pre x)
    (hF : ReachesLinkedFault body h
      (.running (initMachineStateWithMemoryAndCallees body x.1 x.2 callees))) :
    ¬ PanicsOnlyIf (mirHandledTrees body h callees) pre post panicCond :=
  fun hC => hF.not_treeSafe (hC x hx).1

/--
A rely–guarantee policy contract is refuted by one handler that satisfies the
rely and under which the linked execution of an input in `pre` reaches a fault.
-/
theorem not_mirModularPanicsWithPolicyOnlyIf_of_reachesLinkedFault
    {envAssumed : ExternalCallHandler → Prop} (hEnv : envAssumed h) (hx : pre x)
    (hF : ReachesLinkedFault body h
      (.running (initMachineStateWithMemoryAndCallees body x.1 x.2 callees))) :
    ¬ MirModularPanicsWithPolicyOnlyIf body envAssumed pre post panicCond policy callees :=
  fun hC => not_panicsWithPolicyOnlyIf_of_reachesLinkedFault hx hF (hC h hEnv)

/--
A rely–guarantee only-if contract is refuted by one handler that satisfies the
rely and under which the linked execution of an input in `pre` reaches a fault.
-/
theorem not_mirModularPanicsOnlyIf_of_reachesLinkedFault
    {envAssumed : ExternalCallHandler → Prop} (hEnv : envAssumed h) (hx : pre x)
    (hF : ReachesLinkedFault body h
      (.running (initMachineStateWithMemoryAndCallees body x.1 x.2 callees))) :
    ¬ MirModularPanicsOnlyIf body envAssumed pre post panicCond callees :=
  fun hC => not_panicsOnlyIf_of_reachesLinkedFault hx hF (hC h hEnv)

end LinkedRefutation

/-- A handler that answers `answer req` immediately completes with that answer. -/
theorem reachesRet_pure_handler (answer : MirCallAns) :
    ReachesRet (pure answer : ITree MirClosedEffect MirCallAns) [] answer :=
  ⟨_, .refl _, ITree.observe_ret answer⟩

/--
A handler that answers every request immediately implements every call contract
its answers satisfy.
-/
theorem holdsOn_pure_handler (C : MirCallContract) (answer : MirCallReq → MirCallAns)
    (h : ∀ req, C.pre req → C.post req (answer req)) :
    C.holdsOn (fun req => pure (answer req)) :=
  fun req hPre => dwlp_pure_adequacy (ewp := mirClosedWP) (DWLP.ret (h req hPre))

/-! ### Unwind actions at an external call site -/

section UnwindActions

variable (s : MachineState) (localsAfterArgs : List LocalSlot) (destination : Place)
  (targetBb : BasicBlockIdx) (memAfter : Memory)

/-- An unwinding answer dispatches the call's `UnwindAction`. -/
theorem resumeExternalCall_panicked (unwind : UnwindAction) :
    resumeExternalCall s localsAfterArgs destination targetBb unwind
        (.panicked memAfter) =
      applyUnwindAction s localsAfterArgs memAfter unwind :=
  rfl

/-- An aborting answer halts the caller with `.abort`, whatever the `UnwindAction`. -/
theorem resumeExternalCall_aborted (unwind : UnwindAction) :
    resumeExternalCall s localsAfterArgs destination targetBb unwind .aborted =
      .halted .abort :=
  rfl

/--
`UnwindAction.continue_` in the root frame: a callee panic becomes a panic of
the caller, so the caller's panic condition has to cover the callee's.
-/
theorem resumeExternalCall_panicked_continue (hRoot : memAfter.callStack = .nil) :
    resumeExternalCall s localsAfterArgs destination targetBb .continue_
        (.panicked memAfter) =
      .halted .panic := by
  rw [resumeExternalCall_panicked]
  unfold applyUnwindAction
  rw [hRoot]
  rfl

/--
`UnwindAction.cleanup`: a callee panic resumes the caller at the cleanup block
with the memory the callee presented.
-/
theorem resumeExternalCall_panicked_cleanup (cleanupBb : BasicBlockIdx) :
    resumeExternalCall s localsAfterArgs destination targetBb (.cleanup cleanupBb)
        (.panicked memAfter) =
      .running
        { frame :=
            { s.frame with
              blockIdx := cleanupBb
              stmtIdx := 0
              locals := localsAfterArgs }
          memory := memAfter } :=
  rfl

/--
`UnwindAction.terminate`: a callee panic becomes an abort of the caller, so the
caller's abort policy has to admit it.
-/
theorem resumeExternalCall_panicked_terminate :
    resumeExternalCall s localsAfterArgs destination targetBb .terminate
        (.panicked memAfter) =
      .halted .abort :=
  rfl

/-- `UnwindAction.unreachable`: a callee panic is undefined behavior of the caller. -/
theorem resumeExternalCall_panicked_unreachable :
    resumeExternalCall s localsAfterArgs destination targetBb .unreachable
        (.panicked memAfter) =
      .faulted .ub :=
  rfl

/-- A diverging call dispatches an unwinding answer in the same way. -/
theorem resumeExternalDivergingCall_panicked (unwind : UnwindAction) :
    resumeExternalDivergingCall s localsAfterArgs unwind (.panicked memAfter) =
      applyUnwindAction s localsAfterArgs memAfter unwind :=
  rfl

/-- A normal return from a diverging call is undefined behavior. -/
theorem resumeExternalDivergingCall_returned (unwind : UnwindAction) (retVal : Value) :
    resumeExternalDivergingCall s localsAfterArgs unwind (.returned retVal memAfter) =
      .faulted .ub :=
  rfl

/-- An aborting answer to a diverging call halts with `.abort`. -/
theorem resumeExternalDivergingCall_aborted (unwind : UnwindAction) :
    resumeExternalDivergingCall s localsAfterArgs unwind .aborted = .halted .abort :=
  rfl

/-- At the root frame, a normal return from a tail call halts with that return value and memory. -/
theorem resumeExternalTailCall_returned_root (retVal : Value)
    (hRoot : memAfter.callStack = .nil) :
    resumeExternalTailCall (.returned retVal memAfter) =
      .halted (.normal (retVal, memAfter)) := by
  simp only [resumeExternalTailCall, hRoot]

/-- At the root frame, an unwinding tail call halts with `.panic`. -/
theorem resumeExternalTailCall_panicked_root (hRoot : memAfter.callStack = .nil) :
    resumeExternalTailCall (.panicked memAfter) = .halted .panic := by
  simp only [resumeExternalTailCall, hRoot, unwindFromCallStack]

/-- An aborting tail call halts with `.abort`. -/
theorem resumeExternalTailCall_aborted :
    resumeExternalTailCall .aborted = .halted .abort :=
  rfl

/-! ### Preservation of `callees` and `traitImpls` across call resumption -/

private theorem commitForeignFrameLocals_preserves_tables
    {mem mem' : Memory} {target : ForeignFrameTarget} {locals' : List LocalSlot}
    (h : commitForeignFrameLocals mem target locals' = .some mem') :
    mem'.callees = mem.callees ∧ mem'.traitImpls = mem.traitImpls := by
  unfold commitForeignFrameLocals at h
  split at h
  · injection h with hEq; subst hEq; exact ⟨rfl, rfl⟩
  · split at h
    · split at h
      · injection h with hEq; subst hEq; exact ⟨rfl, rfl⟩
      · contradiction
    · contradiction

private theorem foreignFrameDerefWrite_preserves_tables
    {locals₁ locals₂ : List LocalSlot} {mem₁ mem₂ : Memory} {dst : Place}
    {restProj : List ProjectionElem} {val : Value} {localDecls : List LocalDecl}
    {layouts : LayoutTable}
    (h : foreignFrameDerefWrite locals₁ mem₁ dst restProj val localDecls layouts =
      .ok locals₂ mem₂) :
    mem₂.callees = mem₁.callees ∧ mem₂.traitImpls = mem₁.traitImpls := by
  unfold foreignFrameDerefWrite at h
  repeat' (first | contradiction | split at h)
  all_goals
    rename_i hCommit
    injection h with _ hMem
    subst hMem
    have hTab := commitForeignFrameLocals_preserves_tables hCommit
    exact hTab

private theorem writeReturnDestination_preserves_tables
    {callerLocals updatedLocals : List LocalSlot} {mem mem' : Memory} {dst : Place}
    {retVal : Value} {localDecls : List LocalDecl} {layouts : LayoutTable}
    (h : writeReturnDestination callerLocals mem dst retVal localDecls layouts =
      .ok updatedLocals mem') :
    mem'.callees = mem.callees ∧ mem'.traitImpls = mem.traitImpls := by
  unfold writeReturnDestination at h
  cases hProj : dst.projection with
  | nil =>
    simp only [hProj] at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · injection h with _ hMem; subst hMem; exact ⟨rfl, rfl⟩
        · contradiction
    · contradiction
  | cons p rest =>
    cases p with
    | deref =>
      simp only [hProj] at h
      split at h
      · split at h
        · contradiction
        · injection h with _ hMem; subst hMem; exact ⟨rfl, rfl⟩
      · exact foreignFrameDerefWrite_preserves_tables h
      · contradiction
    | _ =>
      simp only [hProj] at h
      split at h
      · contradiction
      · split at h
        · contradiction
        · split at h
          · split at h
            · injection h with _ hMem; subst hMem; exact ⟨rfl, rfl⟩
            · contradiction
          · contradiction
          · contradiction

/-- Unwinding up the call stack never modifies `callees` or `traitImpls`. -/
theorem unwindFromCallStack_preserves_tables :
    ∀ (stack : List SavedCallerFrame) (mem : Memory) (nextState : MachineState),
      unwindFromCallStack stack mem = .running nextState →
      nextState.memory.callees = mem.callees ∧ nextState.memory.traitImpls = mem.traitImpls
  | .nil, _, _, h => nomatch h
  | caller :: restStack, mem, nextState, h => by
    simp only [unwindFromCallStack] at h
    cases hUnw : caller.returnUnwind with
    | unreachable => simp only [hUnw] at h; nomatch h
    | terminate => simp only [hUnw] at h; nomatch h
    | continue_ =>
      simp only [hUnw] at h
      have hRec := unwindFromCallStack_preserves_tables restStack _ nextState h
      exact hRec
    | cleanup cleanupBb =>
      simp only [hUnw] at h
      injection h with hEq
      subst hEq
      exact ⟨rfl, rfl⟩

/-- Dispatching an `UnwindAction` never modifies `callees` or `traitImpls`. -/
theorem applyUnwindAction_preserves_tables (unwind : UnwindAction)
    {nextState : MachineState}
    (h : applyUnwindAction s localsAfterArgs memAfter unwind = .running nextState) :
    nextState.memory.callees = memAfter.callees ∧
      nextState.memory.traitImpls = memAfter.traitImpls := by
  cases unwind with
  | unreachable => nomatch h
  | terminate => nomatch h
  | continue_ => exact unwindFromCallStack_preserves_tables memAfter.callStack memAfter nextState h
  | cleanup cleanupBb =>
    injection h with hEq
    subst hEq
    exact ⟨rfl, rfl⟩

/--
Resuming after a returning external call (`resumeExternalCall`) preserves the
answer memory's `callees` and `traitImpls` into the resumed caller state.
-/
theorem resumeExternalCall_returned_preserves_tables (unwind : UnwindAction)
    {retVal : Value} {nextState : MachineState}
    (h : resumeExternalCall s localsAfterArgs destination targetBb unwind
        (.returned retVal memAfter) = .running nextState) :
    nextState.memory.callees = memAfter.callees ∧
      nextState.memory.traitImpls = memAfter.traitImpls := by
  simp only [resumeExternalCall] at h
  cases hProj : destination.projection with
  | nil =>
    simp only [hProj] at h
    split at h
    · injection h with hEq; subst hEq; exact ⟨rfl, rfl⟩
    · contradiction
    · contradiction
  | cons p rest =>
    cases p with
    | deref =>
      simp only [hProj] at h
      split at h
      · split at h
        · contradiction
        · injection h with hEq; subst hEq; exact ⟨rfl, rfl⟩
      · cases hFor : foreignFrameDerefWrite localsAfterArgs memAfter destination rest retVal with
        | ok updatedLocals mem' =>
          simp only [hFor] at h
          injection h with hEq
          subst hEq
          exact foreignFrameDerefWrite_preserves_tables hFor
        | ub => simp only [hFor] at h; nomatch h
        | unsupported => simp only [hFor] at h; nomatch h
      · contradiction
    | _ =>
      simp only [hProj] at h
      split at h
      · injection h with hEq; subst hEq; exact ⟨rfl, rfl⟩
      · contradiction
      · contradiction

/--
Resuming after an unwinding external call preserves the answer memory's
`callees` and `traitImpls` into the resumed cleanup state.
-/
theorem resumeExternalCall_panicked_preserves_tables (unwind : UnwindAction)
    {nextState : MachineState}
    (h : resumeExternalCall s localsAfterArgs destination targetBb unwind
        (.panicked memAfter) = .running nextState) :
    nextState.memory.callees = memAfter.callees ∧
      nextState.memory.traitImpls = memAfter.traitImpls :=
  applyUnwindAction_preserves_tables s localsAfterArgs memAfter unwind h

/--
Resuming after a diverging external call preserves the answer memory's
`callees` and `traitImpls` into the resumed cleanup state.
-/
theorem resumeExternalDivergingCall_panicked_preserves_tables (unwind : UnwindAction)
    {nextState : MachineState}
    (h : resumeExternalDivergingCall s localsAfterArgs unwind (.panicked memAfter) =
      .running nextState) :
    nextState.memory.callees = memAfter.callees ∧
      nextState.memory.traitImpls = memAfter.traitImpls :=
  applyUnwindAction_preserves_tables s localsAfterArgs memAfter unwind h

/--
Resuming after a tail call preserves the answer memory's `callees` and
`traitImpls` whenever execution continues in a suspended caller frame.
-/
theorem resumeExternalTailCall_returned_preserves_tables {retVal : Value}
    {nextState : MachineState}
    (h : resumeExternalTailCall (.returned retVal memAfter) = .running nextState) :
    nextState.memory.callees = memAfter.callees ∧
      nextState.memory.traitImpls = memAfter.traitImpls := by
  simp only [resumeExternalTailCall] at h
  cases hStack : memAfter.callStack with
  | nil => simp only [hStack] at h; nomatch h
  | cons caller restStack =>
    simp only [hStack] at h
    cases hDiv : caller.isDiverging with
    | true => simp only [hDiv] at h; nomatch h
    | false =>
      simp only [hDiv] at h
      cases hWr : writeReturnDestination caller.frame.locals
          { memAfter with
            callStack := restStack
            activeCallee := .some caller.callerBody
            activeProtectors := restoreCallerProtectors caller }
          caller.destination retVal caller.callerBody.localDecls
          caller.callerBody.layouts with
      | ok updatedLocals mem' =>
        simp only [hWr] at h
        injection h with hEq
        subst hEq
        have hTab := writeReturnDestination_preserves_tables hWr
        exact hTab
      | ub => simp only [hWr] at h; nomatch h
      | unsupported => simp only [hWr] at h; nomatch h

theorem resumeExternalTailCall_panicked_preserves_tables {nextState : MachineState}
    (h : resumeExternalTailCall (.panicked memAfter) = .running nextState) :
    nextState.memory.callees = memAfter.callees ∧
      nextState.memory.traitImpls = memAfter.traitImpls :=
  unwindFromCallStack_preserves_tables memAfter.callStack memAfter nextState h

end UnwindActions

/-! ## 6. Runtime Call-Boundary Guard (`CalleeTableExcludes`) -/

/--
Runtime call-boundary guard for `targetDefPath`: `lookupCallee` finds no body
for `targetDefPath` in `mem.callees` under `mem.traitImpls`, for every caller
`LayoutTable` and every list of type arguments. The guard reads only the callee
table and the trait-implementation table of `mem`, so it does not depend on the
active frame, the call stack, or the borrow state.

While the guard holds, a call to `targetDefPath` cannot step into a body: it
leaves the machine as a `MirCallE` request, where a call contract applies.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1192-L1203>

> "Block ends with the call of a function."
-/
def CalleeTableExcludes (mem : Memory) (targetDefPath : DefPath) : Prop :=
  ∀ (callerLayouts : LayoutTable) (typeArgs : List RigidTy),
    lookupCallee mem.callees callerLayouts targetDefPath typeArgs mem.traitImpls = .none

/-- Runtime call-boundary guard for every contracted callee in `targets`. -/
def RuntimeCallBoundaryGuarded (mem : Memory) (targets : List DefPath) : Prop :=
  ∀ targetDefPath, targetDefPath ∈ targets → CalleeTableExcludes mem targetDefPath

theorem RuntimeCallBoundaryGuarded.excludes {mem : Memory} {targets : List DefPath}
    {targetDefPath : DefPath} (h : RuntimeCallBoundaryGuarded mem targets)
    (hMem : targetDefPath ∈ targets) : CalleeTableExcludes mem targetDefPath :=
  h targetDefPath hMem

/-- The guard depends only on `callees` and `traitImpls`. -/
theorem CalleeTableExcludes.of_tables_eq {mem mem' : Memory} {targetDefPath : DefPath}
    (hCallees : mem'.callees = mem.callees) (hTraits : mem'.traitImpls = mem.traitImpls)
    (h : CalleeTableExcludes mem targetDefPath) :
    CalleeTableExcludes mem' targetDefPath := by
  intro callerLayouts typeArgs
  rw [hCallees, hTraits]
  exact h callerLayouts typeArgs

/-- The guard is preserved in both directions by a memory change that keeps both tables. -/
theorem calleeTableExcludes_iff_of_tables_eq {mem mem' : Memory} {targetDefPath : DefPath}
    (hCallees : mem'.callees = mem.callees) (hTraits : mem'.traitImpls = mem.traitImpls) :
    CalleeTableExcludes mem' targetDefPath ↔ CalleeTableExcludes mem targetDefPath :=
  ⟨CalleeTableExcludes.of_tables_eq hCallees.symm hTraits.symm,
   CalleeTableExcludes.of_tables_eq hCallees hTraits⟩

/-- `RuntimeCallBoundaryGuarded` depends only on `callees` and `traitImpls`. -/
theorem RuntimeCallBoundaryGuarded.of_tables_eq {mem mem' : Memory}
    {targets : List DefPath}
    (hCallees : mem'.callees = mem.callees) (hTraits : mem'.traitImpls = mem.traitImpls)
    (h : RuntimeCallBoundaryGuarded mem targets) :
    RuntimeCallBoundaryGuarded mem' targets :=
  fun p hp => (h p hp).of_tables_eq hCallees hTraits

/--
The guard survives an external call whose answer preserves the call frame and
`traitImpls`.
-/
theorem CalleeTableExcludes.of_callFrameAndTraitsPreserved {before after : Memory}
    {targetDefPath : DefPath}
    (hPres : callFrameAndTraitsPreserved before after)
    (h : CalleeTableExcludes before targetDefPath) :
    CalleeTableExcludes after targetDefPath :=
  h.of_tables_eq hPres.1.1 hPres.2

/--
Sequential external calls: the guard holds in the memory returned by a call
whose contract was strengthened with `withTraitsPreserved`.
-/
theorem CalleeTableExcludes.of_withTraitsPreserved_returned
    (P : PanicMirCallContract) (policy : AbortPolicy MirCallReq)
    {req : MirCallReq} {retVal : Value} {memAfter : Memory} {targetDefPath : DefPath}
    (hPost : (P.withTraitsPreserved.toPolicyMirCallContract policy).post req
      (.returned retVal memAfter))
    (h : CalleeTableExcludes req.memory targetDefPath) :
    CalleeTableExcludes memAfter targetDefPath :=
  h.of_callFrameAndTraitsPreserved
    (P.callFrameAndTraitsPreserved_of_returned policy hPost)

/--
Sequential external calls: the guard holds in the memory presented by an
unwinding call whose contract was strengthened with `withTraitsPreserved`.
-/
theorem CalleeTableExcludes.of_withTraitsPreserved_panicked
    (P : PanicMirCallContract) (policy : AbortPolicy MirCallReq)
    {req : MirCallReq} {memAfter : Memory} {targetDefPath : DefPath}
    (hPost : (P.withTraitsPreserved.toPolicyMirCallContract policy).post req
      (.panicked memAfter))
    (h : CalleeTableExcludes req.memory targetDefPath) :
    CalleeTableExcludes memAfter targetDefPath :=
  h.of_callFrameAndTraitsPreserved
    (P.callFrameAndTraitsPreserved_of_panicked policy hPost)

/--
End-to-end call-resumption guard preservation: after an external call whose
contract carries `withTraitsPreserved`, `resumeExternalCall` preserves
`CalleeTableExcludes` into the resumed caller state (across both normal
destination writeback and unwind cleanup dispatch).
-/
theorem CalleeTableExcludes.of_resumeExternalCall_withTraitsPreserved
    (P : PanicMirCallContract) (policy : AbortPolicy MirCallReq)
    {s nextState : MachineState} {localsAfterArgs : List LocalSlot}
    {destination : Place} {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    {req : MirCallReq} {ans : MirCallAns} {targetDefPath : DefPath}
    (hPost : (P.withTraitsPreserved.toPolicyMirCallContract policy).post req ans)
    (hRes : resumeExternalCall s localsAfterArgs destination targetBb unwind ans =
      .running nextState)
    (h : CalleeTableExcludes req.memory targetDefPath) :
    CalleeTableExcludes nextState.memory targetDefPath := by
  cases ans with
  | returned retVal memAfter =>
    obtain ⟨hC, hT⟩ :=
      resumeExternalCall_returned_preserves_tables s localsAfterArgs destination targetBb
        memAfter unwind hRes
    exact (h.of_withTraitsPreserved_returned P policy hPost).of_tables_eq hC hT
  | panicked memAfter =>
    obtain ⟨hC, hT⟩ :=
      resumeExternalCall_panicked_preserves_tables s localsAfterArgs destination targetBb
        memAfter unwind hRes
    exact (h.of_withTraitsPreserved_panicked P policy hPost).of_tables_eq hC hT
  | aborted => nomatch hRes

/-- End-to-end guard preservation across `resumeExternalDivergingCall`. -/
theorem CalleeTableExcludes.of_resumeExternalDivergingCall_withTraitsPreserved
    (P : PanicMirCallContract) (policy : AbortPolicy MirCallReq)
    {s nextState : MachineState} {localsAfterArgs : List LocalSlot}
    {unwind : UnwindAction} {req : MirCallReq} {ans : MirCallAns}
    {targetDefPath : DefPath}
    (hPost : (P.withTraitsPreserved.toPolicyMirCallContract policy).post req ans)
    (hRes : resumeExternalDivergingCall s localsAfterArgs unwind ans = .running nextState)
    (h : CalleeTableExcludes req.memory targetDefPath) :
    CalleeTableExcludes nextState.memory targetDefPath := by
  cases ans with
  | returned _ _ => nomatch hRes
  | panicked memAfter =>
    obtain ⟨hC, hT⟩ :=
      resumeExternalDivergingCall_panicked_preserves_tables s localsAfterArgs memAfter
        unwind hRes
    exact (h.of_withTraitsPreserved_panicked P policy hPost).of_tables_eq hC hT
  | aborted => nomatch hRes

/-- End-to-end guard preservation across `resumeExternalTailCall`. -/
theorem CalleeTableExcludes.of_resumeExternalTailCall_withTraitsPreserved
    (P : PanicMirCallContract) (policy : AbortPolicy MirCallReq)
    {nextState : MachineState} {req : MirCallReq} {ans : MirCallAns}
    {targetDefPath : DefPath}
    (hPost : (P.withTraitsPreserved.toPolicyMirCallContract policy).post req ans)
    (hRes : resumeExternalTailCall ans = .running nextState)
    (h : CalleeTableExcludes req.memory targetDefPath) :
    CalleeTableExcludes nextState.memory targetDefPath := by
  cases ans with
  | returned retVal memAfter =>
    obtain ⟨hC, hT⟩ := resumeExternalTailCall_returned_preserves_tables memAfter hRes
    exact (h.of_withTraitsPreserved_returned P policy hPost).of_tables_eq hC hT
  | panicked memAfter =>
    obtain ⟨hC, hT⟩ := resumeExternalTailCall_panicked_preserves_tables memAfter hRes
    exact (h.of_withTraitsPreserved_panicked P policy hPost).of_tables_eq hC hT
  | aborted => nomatch hRes

/-- Disabling the borrows of a torn-down frame does not affect the guard. -/
theorem CalleeTableExcludes.with_borrows {mem : Memory} {targetDefPath : DefPath}
    (borrows : List BorrowEntry) (h : CalleeTableExcludes mem targetDefPath) :
    CalleeTableExcludes { mem with borrows := borrows } targetDefPath :=
  h.of_tables_eq rfl rfl

private theorem collectMatchingTraitImpls_of_no_trait (callees : List CapturedMir)
    (defPath : DefPath) (typeArgs : List RigidTy) :
    ∀ (traitImpls : List TraitImplEntry)
      (acc : List (TraitImplEntry × Option (List RigidTy))),
      hasTraitImplForDefPath traitImpls defPath = false →
      collectMatchingTraitImpls callees traitImpls defPath typeArgs acc = acc
  | .nil, _, _ => rfl
  | entry :: rest, acc, h => by
    unfold hasTraitImplForDefPath at h
    unfold collectMatchingTraitImpls
    cases hEq : stringEq entry.traitRef.defPath defPath with
    | true => rw [hEq] at h; nomatch h
    | false =>
      rw [hEq] at h
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact collectMatchingTraitImpls_of_no_trait callees defPath typeArgs rest acc h

/--
Table-level sufficient condition for the guard: no body in `mem.callees` has
path `targetDefPath`, and no `TraitImplEntry` (in `mem.traitImpls` or attached to
a body in `mem.callees`) implements a trait method with path `targetDefPath`.
Both conditions are boolean checks on the tables.
-/
theorem calleeTableExcludes_of_no_callee_no_traitImpl {mem : Memory}
    {targetDefPath : DefPath}
    (hCallee : findCallee? mem.callees targetDefPath = .none)
    (hTrait : hasTraitImplForDefPath
      (mem.traitImpls ++ flatMapTraitImpls mem.callees) targetDefPath = false) :
    CalleeTableExcludes mem targetDefPath := by
  intro callerLayouts typeArgs
  have hResolve :
      resolveCalleeBodyAndArgs? mem.callees targetDefPath typeArgs mem.traitImpls =
        .none := by
    unfold resolveCalleeBodyAndArgs?
    split
    · rw [hCallee]
    · rw [hCallee]
    · simp only [collectMatchingTraitImpls_of_no_trait mem.callees targetDefPath _ _ _ hTrait,
        hCallee]
  unfold lookupCallee
  rw [hResolve]

/--
An empty callee table excludes every target, regardless of `mem.traitImpls`:
`resolveCalleeBodyAndArgs?` always looks up the resolved path in `callees`, so
`findCallee? .nil _ = .none` rejects every lookup unconditionally.
-/
theorem calleeTableExcludes_of_callees_nil {mem : Memory} {targetDefPath : DefPath}
    (hNil : mem.callees = .nil) :
    CalleeTableExcludes mem targetDefPath := by
  intro callerLayouts typeArgs
  have hResolve :
      resolveCalleeBodyAndArgs? .nil targetDefPath typeArgs mem.traitImpls = .none := by
    unfold resolveCalleeBodyAndArgs?
    cases typeArgs with
    | nil => rfl
    | cons firstArg restArgs =>
      cases firstArg with
      | param _ _ => rfl
      | _ =>
        simp only [findCallee?]
        split
        · rfl
        · split <;> rfl
  unfold lookupCallee
  rw [hNil, hResolve]

/-- Layout table of the active body, as `evalTerminator` reads it. -/
@[reducible]
def activeBodyLayouts : Option CapturedMir → LayoutTable
  | .some b => b.layouts
  | .none => emptyLayoutTable

/-- Step node of an execution state that a terminator computes inline. -/
def execStateStepNode : MirExecState → MirStepNode
  | .running nextState => MirStepNode.step nextState
  | .halted out => MirStepNode.retOutcome out
  | .faulted fk => MirStepNode.fail fk

section EvalTerminatorGuard

variable {s : MachineState} {term : Terminator} {currentBody : Option CapturedMir}
  {func : Operand} {argOps : List Operand} {destination : Place}
  {targetBb : BasicBlockIdx} {unwind : UnwindAction}
  {target : ResolvedCallTarget} {localsAfterFunc locals' : List LocalSlot}
  {argVals : List Value}

/--
Under the guard, a `TerminatorKind.call` with a return target emits an unlinked
`MirCallE` request carrying the call-site memory instead of pushing a callee
frame. The statement is in terms of the resolved target, so it covers every way
`resolveCallTarget` resolves `func`: a direct or polymorphic function item, a
trait method, a zero-sized function-item local, and a reified function pointer.

Two kinds of target are modeled inline by `evalTerminator` after `lookupCallee`
misses and are excluded: `core::intrinsics::exact_div`, and a direct call to an
intrinsic recognized by `classifyRustIntrinsic?`.
-/
theorem evalTerminator_call_extCall_of_calleeTableExcludes
    (hKind : term.kind = .call func argOps destination (.some targetBb) unwind)
    (hResolve :
      resolveCallTarget s func (Trusted.Sequence.length argOps)
        (bodyLocalDeclsOf currentBody) (activeBodyLayouts currentBody) =
        .ok target localsAfterFunc)
    (hArgs :
      evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
        (activeBodyLayouts currentBody) s.memory.callerLocals
        (callStack := s.memory.callStack) = .ok argVals locals')
    (hExcl : CalleeTableExcludes s.memory target.defPath)
    (hNotExactDiv : isDirectExactDivTarget target = false)
    (hNotIntrinsic :
      target.isIndirect = true ∨ classifyRustIntrinsic? target.defPath = .none) :
    evalTerminator s term currentBody =
      MirStepNode.extCall
        { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals,
          memory := s.memory }
        (resumeExternalCall s locals' destination targetBb unwind) := by
  have hLookup := hExcl (activeBodyLayouts currentBody) target.typeArgs
  cases currentBody <;>
  · unfold evalTerminator
    rw [hKind]
    simp only [bodyLocalDeclsOf, activeBodyLayouts] at hResolve hArgs hLookup ⊢
    simp only [hResolve, hArgs, hLookup, hNotExactDiv]
    rcases hNotIntrinsic with hInd | hCls
    · rw [hInd]
    · cases target.isIndirect with
      | true => rfl
      | false => simp only [evalDirectRustIntrinsic?, hCls]

/--
Under the guard, a diverging `TerminatorKind.call` (`target = .none`) emits an
unlinked `MirCallE` request resumed by `resumeExternalDivergingCall`.

Direct calls to `unreachable_unchecked` and to the panic entry points
(`isAbortingPanicDefPath`, `isUnwindingPanicDefPath`) are modeled inline by
`evalTerminator` after `lookupCallee` misses and are excluded.
-/
theorem evalTerminator_divergingCall_extCall_of_calleeTableExcludes
    (hKind : term.kind = .call func argOps destination .none unwind)
    (hResolve :
      resolveCallTarget s func (Trusted.Sequence.length argOps)
        (bodyLocalDeclsOf currentBody) (activeBodyLayouts currentBody) =
        .ok target localsAfterFunc)
    (hArgs :
      evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
        (activeBodyLayouts currentBody) s.memory.callerLocals
        (callStack := s.memory.callStack) = .ok argVals locals')
    (hExcl : CalleeTableExcludes s.memory target.defPath)
    (hNotInline :
      target.isIndirect = true ∨
        (isUnreachableCallTarget target.defPath = false ∧
          isAbortingPanicDefPath target.defPath = false ∧
          isUnwindingPanicDefPath target.defPath = false)) :
    evalTerminator s term currentBody =
      MirStepNode.extCall
        { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals,
          memory := s.memory }
        (resumeExternalDivergingCall s locals' unwind) := by
  have hLookup := hExcl (activeBodyLayouts currentBody) target.typeArgs
  cases currentBody <;>
  · unfold evalTerminator
    rw [hKind]
    simp only [bodyLocalDeclsOf, activeBodyLayouts] at hResolve hArgs hLookup ⊢
    simp only [hResolve, hArgs, hLookup]
    rcases hNotInline with hInd | ⟨hUnreach, hAbort, hUnwind⟩
    · rw [hInd]
    · cases target.isIndirect with
      | true => rfl
      | false => rw [hUnreach, hAbort, hUnwind]

/--
The guard does not turn `unreachable_unchecked` into a request: a direct
diverging call to an unreachable target faults with `.ub`.
-/
theorem evalTerminator_divergingCall_unreachable_of_calleeTableExcludes
    (hKind : term.kind = .call func argOps destination .none unwind)
    (hResolve :
      resolveCallTarget s func (Trusted.Sequence.length argOps)
        (bodyLocalDeclsOf currentBody) (activeBodyLayouts currentBody) =
        .ok target localsAfterFunc)
    (hArgs :
      evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
        (activeBodyLayouts currentBody) s.memory.callerLocals
        (callStack := s.memory.callStack) = .ok argVals locals')
    (hExcl : CalleeTableExcludes s.memory target.defPath)
    (hDirect : target.isIndirect = false)
    (hUnreach : isUnreachableCallTarget target.defPath = true) :
    evalTerminator s term currentBody = MirStepNode.fail .ub := by
  have hLookup := hExcl (activeBodyLayouts currentBody) target.typeArgs
  cases currentBody <;>
  · unfold evalTerminator
    rw [hKind]
    simp only [bodyLocalDeclsOf, activeBodyLayouts] at hResolve hArgs hLookup ⊢
    simp only [hResolve, hArgs, hLookup]
    rw [hDirect, hUnreach]

/--
The guard does not turn an aborting panic entry point into a request: a direct
diverging call to `panic_nounwind` and its relatives halts with `.abort`.
-/
theorem evalTerminator_divergingCall_abortingPanic_of_calleeTableExcludes
    (hKind : term.kind = .call func argOps destination .none unwind)
    (hResolve :
      resolveCallTarget s func (Trusted.Sequence.length argOps)
        (bodyLocalDeclsOf currentBody) (activeBodyLayouts currentBody) =
        .ok target localsAfterFunc)
    (hArgs :
      evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
        (activeBodyLayouts currentBody) s.memory.callerLocals
        (callStack := s.memory.callStack) = .ok argVals locals')
    (hExcl : CalleeTableExcludes s.memory target.defPath)
    (hDirect : target.isIndirect = false)
    (hReach : isUnreachableCallTarget target.defPath = false)
    (hAbort : isAbortingPanicDefPath target.defPath = true) :
    evalTerminator s term currentBody = MirStepNode.retOutcome .abort := by
  have hLookup := hExcl (activeBodyLayouts currentBody) target.typeArgs
  cases currentBody <;>
  · unfold evalTerminator
    rw [hKind]
    simp only [bodyLocalDeclsOf, activeBodyLayouts] at hResolve hArgs hLookup ⊢
    simp only [hResolve, hArgs, hLookup]
    rw [hDirect, hReach, hAbort]

/--
The guard does not turn an unwinding panic entry point into a request: a direct
diverging call to `core::panicking::panic` and its relatives applies the call's
`UnwindAction` to the call-site memory.
-/
theorem evalTerminator_divergingCall_unwindingPanic_of_calleeTableExcludes
    (hKind : term.kind = .call func argOps destination .none unwind)
    (hResolve :
      resolveCallTarget s func (Trusted.Sequence.length argOps)
        (bodyLocalDeclsOf currentBody) (activeBodyLayouts currentBody) =
        .ok target localsAfterFunc)
    (hArgs :
      evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
        (activeBodyLayouts currentBody) s.memory.callerLocals
        (callStack := s.memory.callStack) = .ok argVals locals')
    (hExcl : CalleeTableExcludes s.memory target.defPath)
    (hDirect : target.isIndirect = false)
    (hReach : isUnreachableCallTarget target.defPath = false)
    (hAbort : isAbortingPanicDefPath target.defPath = false)
    (hUnwind : isUnwindingPanicDefPath target.defPath = true) :
    evalTerminator s term currentBody =
      execStateStepNode (applyUnwindAction s locals' s.memory unwind) := by
  have hLookup := hExcl (activeBodyLayouts currentBody) target.typeArgs
  cases currentBody <;>
  · unfold evalTerminator
    rw [hKind]
    simp only [bodyLocalDeclsOf, activeBodyLayouts] at hResolve hArgs hLookup ⊢
    simp only [hResolve, hArgs, hLookup]
    rw [hDirect, hReach, hAbort, hUnwind]
    cases applyUnwindAction s locals' s.memory unwind <;> rfl

/--
Under the guard, a `TerminatorKind.tailCall` whose frame teardown has no
protector conflict emits an unlinked `MirCallE` request. The caller frame is
torn down first: the request carries the memory with the frame's borrows
disabled (`disableFrameBorrows`). No intrinsic or panic entry point is modeled
inline on a tail call.
-/
theorem evalTerminator_tailCall_extCall_of_calleeTableExcludes
    (hKind : term.kind = .tailCall func argOps)
    (hResolve :
      resolveCallTarget s func (Trusted.Sequence.length argOps)
        (bodyLocalDeclsOf currentBody) (activeBodyLayouts currentBody) =
        .ok target localsAfterFunc)
    (hArgs :
      evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
        (activeBodyLayouts currentBody) s.memory.callerLocals
        (callStack := s.memory.callStack) = .ok argVals locals')
    (hNoConflict :
      hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
        (Trusted.Sequence.length s.memory.callStack)
        (Trusted.Sequence.length s.frame.locals) = false)
    (hExcl : CalleeTableExcludes s.memory target.defPath) :
    evalTerminator s term currentBody =
      MirStepNode.extCall
        { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals,
          memory :=
            { s.memory with
              borrows :=
                disableFrameBorrows s.memory.borrows
                  (Trusted.Sequence.length s.memory.callStack)
                  (Trusted.Sequence.length s.frame.locals) } }
        resumeExternalTailCall := by
  have hLookup := hExcl (activeBodyLayouts currentBody) target.typeArgs
  cases currentBody <;>
  · unfold evalTerminator
    rw [hKind]
    simp only []
    unfold evalTailCallTerminator
    simp only [bodyLocalDeclsOf, activeBodyLayouts] at hResolve hArgs hLookup ⊢
    simp only [hResolve, hArgs, hNoConflict, hLookup]

/--
A `TerminatorKind.tailCall` whose frame teardown conflicts with an active
protector is undefined behavior, before any callee lookup and before any
`MirCallE` request.
-/
theorem evalTerminator_tailCall_ub_of_protectorConflict
    (hKind : term.kind = .tailCall func argOps)
    (hResolve :
      resolveCallTarget s func (Trusted.Sequence.length argOps)
        (bodyLocalDeclsOf currentBody) (activeBodyLayouts currentBody) =
        .ok target localsAfterFunc)
    (hArgs :
      evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
        (activeBodyLayouts currentBody) s.memory.callerLocals
        (callStack := s.memory.callStack) = .ok argVals locals')
    (hConflict :
      hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
        (Trusted.Sequence.length s.memory.callStack)
        (Trusted.Sequence.length s.frame.locals) = true) :
    evalTerminator s term currentBody = MirStepNode.fail .ub := by
  cases currentBody <;>
  · unfold evalTerminator
    rw [hKind]
    simp only []
    unfold evalTailCallTerminator
    simp only [bodyLocalDeclsOf, activeBodyLayouts] at hResolve hArgs ⊢
    simp only [hResolve, hArgs, hConflict]

end EvalTerminatorGuard

/-! ### How `resolveCallTarget` resolves each kind of call operand -/

/--
Direct, polymorphic, and trait-method calls: a constant operand of function-item
type `fnDef defPath typeArgs` resolves to the direct target
`(defPath, typeArgs)` without touching the frame.
-/
theorem resolveCallTarget_const_fnDef (s : MachineState) (c : ConstOperand)
    (defPath : DefPath) (typeArgs : List RigidTy) (argCount : Nat)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (hTy : c.ty.kind = .fnDef defPath typeArgs) :
    resolveCallTarget s (.constant c) argCount bodyLocalDecls bodyLayouts =
      .ok { defPath := defPath, typeArgs := typeArgs, fnSig := .none, isIndirect := false }
        s.frame.locals := by
  simp only [resolveCallTarget, extractCalleeDefPath?, extractCalleeTypeArgs, hTy]

/--
Zero-sized function-item locals: a `copy` or `move` operand that evaluates to
`()` and whose declared type is `fnDef defPath typeArgs` resolves to the direct
target `(defPath, typeArgs)`.
-/
theorem resolveCallTarget_fnItem_local (s : MachineState) (func : Operand)
    (defPath : DefPath) (typeArgs : List RigidTy) (argCount : Nat)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (localsAfterFunc : List LocalSlot)
    (hNotConst : extractCalleeDefPath? func = .none)
    (hEval :
      evalOperand s.frame.locals func s.memory.borrows s.memory.globals bodyLayouts
        s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok .unit localsAfterFunc)
    (hTy :
      extractFnItemTarget? (operandTy bodyLocalDecls bodyLayouts func) =
        .some (defPath, typeArgs)) :
    resolveCallTarget s func argCount bodyLocalDecls bodyLayouts =
      .ok { defPath := defPath, typeArgs := typeArgs, fnSig := .none, isIndirect := false }
        localsAfterFunc := by
  simp only [resolveCallTarget, hNotConst, hEval, hTy]

/--
Zero-sized function-item locals represented as an empty aggregate
`.aggregate 0 .nil`: resolves identically to the `.unit` case.
-/
theorem resolveCallTarget_fnItem_local_aggregate (s : MachineState) (func : Operand)
    (defPath : DefPath) (typeArgs : List RigidTy) (argCount : Nat)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (localsAfterFunc : List LocalSlot)
    (hNotConst : extractCalleeDefPath? func = .none)
    (hEval :
      evalOperand s.frame.locals func s.memory.borrows s.memory.globals bodyLayouts
        s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok (.aggregate 0 .nil) localsAfterFunc)
    (hTy :
      extractFnItemTarget? (operandTy bodyLocalDecls bodyLayouts func) =
        .some (defPath, typeArgs)) :
    resolveCallTarget s func argCount bodyLocalDecls bodyLayouts =
      .ok { defPath := defPath, typeArgs := typeArgs, fnSig := .none, isIndirect := false }
        localsAfterFunc := by
  simp only [resolveCallTarget, hNotConst, hEval, hTy]

/--
Indirect calls: an operand that evaluates to a function pointer registered in
`mem.fnPtrs` with a compatible signature resolves to the indirect target recorded
in its `FnPtrEntry`.
-/
theorem resolveCallTarget_fnPtr (s : MachineState) (func : Operand)
    (argCount : Nat) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (ptrVal : ProvenancePtr) (fnEntry : FnPtrEntry) (localsAfterFunc : List LocalSlot)
    (hNotConst : extractCalleeDefPath? func = .none)
    (hEval :
      evalOperand s.frame.locals func s.memory.borrows s.memory.globals bodyLayouts
        s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok (.ptr ptrVal 8) localsAfterFunc)
    (hOffset : ptrVal.offsetBytes = 0)
    (hNoBorrow : lookupBorrow s.memory.borrows ptrVal.tag = .none)
    (hEntry : lookupFnPtr s.memory.fnPtrs ptrVal.allocId = .some fnEntry)
    (hCompat :
      fnEntryCompatibleWithCallSite fnEntry argCount
        (operandTy bodyLocalDecls bodyLayouts func) = true) :
    resolveCallTarget s func argCount bodyLocalDecls bodyLayouts =
      .ok
        { defPath := fnEntry.defPath, typeArgs := fnEntry.typeArgs,
          fnSig := fnEntry.fnSig, isIndirect := true }
        localsAfterFunc := by
  simp only [resolveCallTarget, hNotConst, hEval, hOffset, hNoBorrow, hEntry, hCompat]
  rfl

/-- An indirect target is never the inline-modeled `exact_div` intrinsic. -/
theorem isDirectExactDivTarget_indirect (defPath : DefPath) (typeArgs : List RigidTy)
    (fnSig : Option RigidTy) :
    isDirectExactDivTarget
      { defPath := defPath, typeArgs := typeArgs, fnSig := fnSig, isIndirect := true } =
      false :=
  rfl

/-! ## 7. Syntactic Call-Boundary Guard (`CallBoundaryPreserved`) -/

private theorem listByteEq_eq_true_iff :
    ∀ (xs ys : List UInt8), listByteEq xs ys = true ↔ xs = ys
  | [], [] => ⟨fun _ => rfl, fun _ => rfl⟩
  | [], _ :: _ => ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | _ :: _, [] => ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | b₁ :: bs₁, b₂ :: bs₂ => by
    have ih := listByteEq_eq_true_iff bs₁ bs₂
    simp only [listByteEq]
    cases hb : Nat.beq b₁.toBitVec.toNat b₂.toBitVec.toNat with
    | false =>
      refine ⟨fun h => (nomatch h), fun h => ?_⟩
      injection h with hb₁ _
      subst hb₁
      rw [Nat.beq_refl] at hb
      nomatch hb
    | true =>
      have hByte : b₁ = b₂ :=
        UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hb))
      subst hByte
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [ih.mp h]
      · injection h with _ h'
        exact ih.mpr h'

/-- The byte-wise `stringEq` of the trusted semantics decides equality of paths. -/
theorem stringEq_eq_true_iff (a b : String) : stringEq a b = true ↔ a = b := by
  constructor
  · intro h
    unfold stringEq at h
    exact String.toByteArray_inj.mp
      (ByteArray.ext (Array.toList_inj.mp ((listByteEq_eq_true_iff _ _).mp h)))
  · rintro rfl
    unfold stringEq
    exact (listByteEq_eq_true_iff _ _).mpr rfl

/--
Checker: `func` is a constant function-item operand that names `targetDefPath`,
as `extractCalleeDefPath?` reads it.
-/
def operandNamesDefPath (targetDefPath : DefPath) (func : Operand) : Bool :=
  match extractCalleeDefPath? func with
  | .some defPath => stringEq defPath targetDefPath
  | .none => false

/--
Checker: `term` is a `call` or `tailCall` whose function operand is a constant
function item naming `targetDefPath`.
-/
def terminatorCallsDefPath (targetDefPath : DefPath) (term : Terminator) : Bool :=
  match term.kind with
  | .call func _ _ _ _ => operandNamesDefPath targetDefPath func
  | .tailCall func _ => operandNamesDefPath targetDefPath func
  | _ => false

/-- Checker: some basic block of `body` ends in a direct call to `targetDefPath`. -/
def bodyCallsDefPath (targetDefPath : DefPath) (body : CapturedMir) : Bool :=
  body.basicBlocks.any (fun bb => terminatorCallsDefPath targetDefPath bb.terminator)

/--
`term` is a `call` or `tailCall` whose function operand is a constant function
item naming `targetDefPath`.

Reference (The Rust Reference, "Function item types"):
<https://doc.rust-lang.org/1.98.0/reference/types/function-item.html>

> "When referred to, a function item, or the constructor of a tuple-like struct
> or enum variant, yields a zero-sized value of its function item type. That
> type uniquely identifies the function"
-/
def TerminatorCallsDefPath (targetDefPath : DefPath) (term : Terminator) : Prop :=
  ∃ func, extractCalleeDefPath? func = .some targetDefPath ∧
    ((∃ args destination target unwind,
        term.kind = .call func args destination target unwind) ∨
      ∃ args, term.kind = .tailCall func args)

/-- Some basic block of `body` ends in a direct call to `targetDefPath`. -/
def BodyCallsDefPath (targetDefPath : DefPath) (body : CapturedMir) : Prop :=
  ∃ bb, bb ∈ body.basicBlocks ∧ TerminatorCallsDefPath targetDefPath bb.terminator

theorem operandNamesDefPath_iff (targetDefPath : DefPath) (func : Operand) :
    operandNamesDefPath targetDefPath func = true ↔
      extractCalleeDefPath? func = .some targetDefPath := by
  unfold operandNamesDefPath
  cases h : extractCalleeDefPath? func with
  | none => exact ⟨fun hf => (nomatch hf), fun hf => (nomatch hf)⟩
  | some defPath =>
    exact ⟨fun hEq => congrArg _ ((stringEq_eq_true_iff _ _).1 hEq),
      fun hEq => (stringEq_eq_true_iff _ _).2 (Option.some.inj hEq)⟩

/-- The terminator checker decides `TerminatorCallsDefPath`. -/
theorem terminatorCallsDefPath_iff (targetDefPath : DefPath) (term : Terminator) :
    terminatorCallsDefPath targetDefPath term = true ↔
      TerminatorCallsDefPath targetDefPath term := by
  unfold terminatorCallsDefPath TerminatorCallsDefPath
  constructor
  · intro h
    split at h
    · next func args destination target unwind hKind =>
      exact ⟨func, (operandNamesDefPath_iff _ _).1 h,
        Or.inl ⟨args, destination, target, unwind, hKind⟩⟩
    · next func args hKind =>
      exact ⟨func, (operandNamesDefPath_iff _ _).1 h, Or.inr ⟨args, hKind⟩⟩
    · nomatch h
  · rintro ⟨func, hFunc, ⟨args, destination, target, unwind, hKind⟩ | ⟨args, hKind⟩⟩
    · rw [hKind]
      exact (operandNamesDefPath_iff _ _).2 hFunc
    · rw [hKind]
      exact (operandNamesDefPath_iff _ _).2 hFunc

/-- The body checker decides `BodyCallsDefPath`. -/
theorem bodyCallsDefPath_iff (targetDefPath : DefPath) (body : CapturedMir) :
    bodyCallsDefPath targetDefPath body = true ↔ BodyCallsDefPath targetDefPath body := by
  unfold bodyCallsDefPath BodyCallsDefPath
  rw [List.any_eq_true]
  exact ⟨fun ⟨bb, hMem, h⟩ => ⟨bb, hMem, (terminatorCallsDefPath_iff _ _).1 h⟩,
    fun ⟨bb, hMem, h⟩ => ⟨bb, hMem, (terminatorCallsDefPath_iff _ _).2 h⟩⟩

/--
Capture-level call-boundary guard of `callerBody` for the contracted callee
`targetDefPath`, with linked callee table `callees`:

* the call site survives in the captured MIR (`BodyCallsDefPath`), so a
  pre-capture inlining pass did not erase it, and
* the callee table cannot resolve the call (no body with that path, and no
  trait implementation for it on the caller or on a linked body).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1192-L1203>

> "Block ends with the call of a function."
-/
structure CallBoundaryPreserved (callerBody : CapturedMir) (callees : List CapturedMir)
    (targetDefPath : DefPath) : Prop where
  /-- The captured caller still contains a direct call to the target. -/
  callSite : BodyCallsDefPath targetDefPath callerBody
  /-- No linked body has the target's path. -/
  notLinked : findCallee? callees targetDefPath = .none
  /-- No trait implementation of the caller or of a linked body dispatches the target. -/
  noTraitImpl :
    hasTraitImplForDefPath (callerBody.traitImpls ++ flatMapTraitImpls callees)
      targetDefPath = false

/-- Checker for `CallBoundaryPreserved`. -/
def callBoundaryPreserved (callerBody : CapturedMir) (callees : List CapturedMir)
    (targetDefPath : DefPath) : Bool :=
  bodyCallsDefPath targetDefPath callerBody &&
    ((findCallee? callees targetDefPath).isNone &&
      !hasTraitImplForDefPath (callerBody.traitImpls ++ flatMapTraitImpls callees)
        targetDefPath)

/-- The checker decides `CallBoundaryPreserved`. -/
theorem callBoundaryPreserved_iff (callerBody : CapturedMir) (callees : List CapturedMir)
    (targetDefPath : DefPath) :
    callBoundaryPreserved callerBody callees targetDefPath = true ↔
      CallBoundaryPreserved callerBody callees targetDefPath := by
  unfold callBoundaryPreserved
  simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none]
  exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨(bodyCallsDefPath_iff _ _).1 h₁, h₂, h₃⟩,
    fun h => ⟨(bodyCallsDefPath_iff _ _).2 h.callSite, h.notLinked, h.noTraitImpl⟩⟩

/--
Capture-level call-boundary guard for transitive helpers linked into `callees`:
1. every path in `expectedCallers` is actually present in `callees` (avoiding
   vacuity when a helper is missing from `callees`),
2. every linked body in `callees` whose path is in `expectedCallers` still
   contains a direct syntactic call to `targetDefPath`,
3. no linked body in `callees` has path `targetDefPath`, and
4. no trait implementation on `callerBody` or any linked body dispatches
   `targetDefPath`.
-/
structure CalleesCallBoundaryPreserved (callerBody : CapturedMir)
    (callees : List CapturedMir) (expectedCallers : List DefPath)
    (targetDefPath : DefPath) : Prop where
  /-- Every expected transitive helper is present in `callees`. -/
  expectedPresent :
    ∀ callerPath, callerPath ∈ expectedCallers →
      ∃ body, body ∈ callees ∧ body.defPath = callerPath
  /-- Every linked body matching an expected helper retains a direct call site. -/
  callerSites :
    ∀ body, body ∈ callees → body.defPath ∈ expectedCallers →
      BodyCallsDefPath targetDefPath body
  /-- No linked body has the target's path. -/
  notLinked : findCallee? callees targetDefPath = .none
  /-- No trait implementation on `callerBody` or `callees` dispatches the target. -/
  noTraitImpl :
    hasTraitImplForDefPath (callerBody.traitImpls ++ flatMapTraitImpls callees)
      targetDefPath = false

/-- Checker for `CalleesCallBoundaryPreserved`. -/
def calleesCallBoundaryPreserved (callerBody : CapturedMir)
    (callees : List CapturedMir) (expectedCallers : List DefPath)
    (targetDefPath : DefPath) : Bool :=
  expectedCallers.all (fun callerPath =>
      callees.any (fun body => stringEq body.defPath callerPath)) &&
    (callees.all (fun body =>
        !expectedCallers.any (fun caller => stringEq body.defPath caller) ||
          bodyCallsDefPath targetDefPath body) &&
      ((findCallee? callees targetDefPath).isNone &&
        !hasTraitImplForDefPath (callerBody.traitImpls ++ flatMapTraitImpls callees)
          targetDefPath))

/-- The checker decides `CalleesCallBoundaryPreserved`. -/
theorem calleesCallBoundaryPreserved_iff (callerBody : CapturedMir)
    (callees : List CapturedMir) (expectedCallers : List DefPath)
    (targetDefPath : DefPath) :
    calleesCallBoundaryPreserved callerBody callees expectedCallers targetDefPath = true ↔
      CalleesCallBoundaryPreserved callerBody callees expectedCallers targetDefPath := by
  unfold calleesCallBoundaryPreserved
  simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none,
    List.all_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨hPres, hSites, hNotLinked, hNoTrait⟩
    refine ⟨?_, ?_, hNotLinked, hNoTrait⟩
    · intro callerPath hMem
      obtain ⟨body, hBodyMem, hEq⟩ := hPres callerPath hMem
      exact ⟨body, hBodyMem, (stringEq_eq_true_iff _ _).1 hEq⟩
    · intro body hMem hCaller
      have hBody := hSites body hMem
      rw [Bool.or_eq_true] at hBody
      rcases hBody with hNot | hCalls
      · have hAny : expectedCallers.any (fun caller => stringEq body.defPath caller) = true :=
          List.any_eq_true.2 ⟨body.defPath, hCaller, (stringEq_eq_true_iff _ _).2 rfl⟩
        rw [hAny] at hNot
        nomatch hNot
      · exact (bodyCallsDefPath_iff _ _).1 hCalls
  · intro h
    refine ⟨?_, ?_, h.notLinked, h.noTraitImpl⟩
    · intro callerPath hMem
      obtain ⟨body, hBodyMem, hEq⟩ := h.expectedPresent callerPath hMem
      exact ⟨body, hBodyMem, (stringEq_eq_true_iff _ _).2 hEq⟩
    · intro body hMem
      rw [Bool.or_eq_true]
      cases hAny : expectedCallers.any (fun caller => stringEq body.defPath caller) with
      | false => exact Or.inl rfl
      | true =>
        obtain ⟨caller, hCallerMem, hEq⟩ := List.any_eq_true.1 hAny
        have hPath : body.defPath = caller := (stringEq_eq_true_iff _ _).1 hEq
        exact Or.inr ((bodyCallsDefPath_iff _ _).2 (h.callerSites body hMem (hPath ▸ hCallerMem)))

/-- Non-vacuity: omitting an expected helper from `callees` refutes `CalleesCallBoundaryPreserved`. -/
theorem not_calleesCallBoundaryPreserved_of_missing_caller {callerBody : CapturedMir}
    {callees : List CapturedMir} {expectedCallers : List DefPath}
    {targetDefPath callerPath : DefPath}
    (hMem : callerPath ∈ expectedCallers)
    (hMissing : ∀ body, body ∈ callees → body.defPath ≠ callerPath) :
    ¬ CalleesCallBoundaryPreserved callerBody callees expectedCallers targetDefPath := by
  intro h
  obtain ⟨body, hBodyMem, hEq⟩ := h.expectedPresent callerPath hMem
  exact hMissing body hBodyMem hEq

/-- Soundness: linking `targetDefPath` into `callees` refutes `CalleesCallBoundaryPreserved`. -/
theorem not_calleesCallBoundaryPreserved_of_linked_target {callerBody : CapturedMir}
    {callees : List CapturedMir} {expectedCallers : List DefPath}
    {targetDefPath : DefPath} {targetBody : CapturedMir}
    (hLinked : findCallee? callees targetDefPath = .some targetBody) :
    ¬ CalleesCallBoundaryPreserved callerBody callees expectedCallers targetDefPath := by
  intro h
  rw [h.notLinked] at hLinked
  nomatch hLinked

/-! ### Soundness of the syntactic layer -/

/--
A syntactic call site resolves at run time to the direct target it names: the
operand of a terminator accepted by `TerminatorCallsDefPath` is resolved by
`resolveCallTarget` to `targetDefPath` without evaluating anything.
-/
theorem resolveCallTarget_of_extractCalleeDefPath (s : MachineState) (func : Operand)
    (targetDefPath : DefPath) (argCount : Nat) (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (hFunc : extractCalleeDefPath? func = .some targetDefPath) :
    resolveCallTarget s func argCount bodyLocalDecls bodyLayouts =
      .ok
        { defPath := targetDefPath, typeArgs := extractCalleeTypeArgs func,
          fnSig := .none, isIndirect := false }
        s.frame.locals := by
  simp only [resolveCallTarget, hFunc]

/--
The two layers together: at a syntactic call site of `targetDefPath`, under the
runtime guard, `evalTerminator` emits the `MirCallE` request for
`targetDefPath`. The target must not be an intrinsic that `evalTerminator`
models inline.
-/
theorem evalTerminator_extCall_of_call_site {s : MachineState} {term : Terminator}
    {currentBody : Option CapturedMir} {func : Operand} {argOps : List Operand}
    {destination : Place} {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    {targetDefPath : DefPath} {locals' : List LocalSlot} {argVals : List Value}
    (hKind : term.kind = .call func argOps destination (.some targetBb) unwind)
    (hFunc : extractCalleeDefPath? func = .some targetDefPath)
    (hArgs :
      evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals
        (activeBodyLayouts currentBody) s.memory.callerLocals
        (callStack := s.memory.callStack) = .ok argVals locals')
    (hExcl : CalleeTableExcludes s.memory targetDefPath)
    (hNotExactDiv : stringEq targetDefPath "core::intrinsics::exact_div" = false)
    (hNotIntrinsic : classifyRustIntrinsic? targetDefPath = .none) :
    evalTerminator s term currentBody =
      MirStepNode.extCall
        { defPath := targetDefPath, typeArgs := extractCalleeTypeArgs func,
          args := argVals, memory := s.memory }
        (resumeExternalCall s locals' destination targetBb unwind) :=
  evalTerminator_call_extCall_of_calleeTableExcludes
    (target :=
      { defPath := targetDefPath, typeArgs := extractCalleeTypeArgs func,
        fnSig := .none, isIndirect := false })
    hKind (resolveCallTarget_of_extractCalleeDefPath s func targetDefPath _ _ _ hFunc)
    hArgs hExcl hNotExactDiv (Or.inr hNotIntrinsic)

/-- Two-layer bridge for a syntactic diverging call site (`target = .none`). -/
theorem evalTerminator_divergingCall_extCall_of_call_site {s : MachineState}
    {term : Terminator} {currentBody : Option CapturedMir} {func : Operand}
    {argOps : List Operand} {destination : Place} {unwind : UnwindAction}
    {targetDefPath : DefPath} {locals' : List LocalSlot} {argVals : List Value}
    (hKind : term.kind = .call func argOps destination .none unwind)
    (hFunc : extractCalleeDefPath? func = .some targetDefPath)
    (hArgs :
      evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals
        (activeBodyLayouts currentBody) s.memory.callerLocals
        (callStack := s.memory.callStack) = .ok argVals locals')
    (hExcl : CalleeTableExcludes s.memory targetDefPath)
    (hNotUnreach : isUnreachableCallTarget targetDefPath = false)
    (hNotAbort : isAbortingPanicDefPath targetDefPath = false)
    (hNotUnwind : isUnwindingPanicDefPath targetDefPath = false) :
    evalTerminator s term currentBody =
      MirStepNode.extCall
        { defPath := targetDefPath, typeArgs := extractCalleeTypeArgs func,
          args := argVals, memory := s.memory }
        (resumeExternalDivergingCall s locals' unwind) :=
  evalTerminator_divergingCall_extCall_of_calleeTableExcludes
    (target :=
      { defPath := targetDefPath, typeArgs := extractCalleeTypeArgs func,
        fnSig := .none, isIndirect := false })
    hKind (resolveCallTarget_of_extractCalleeDefPath s func targetDefPath _ _ _ hFunc)
    hArgs hExcl (Or.inr ⟨hNotUnreach, hNotAbort, hNotUnwind⟩)

/-- Two-layer bridge for a syntactic tail-call site (`TerminatorKind.tailCall`). -/
theorem evalTerminator_tailCall_extCall_of_call_site {s : MachineState}
    {term : Terminator} {currentBody : Option CapturedMir} {func : Operand}
    {argOps : List Operand} {targetDefPath : DefPath} {locals' : List LocalSlot}
    {argVals : List Value}
    (hKind : term.kind = .tailCall func argOps)
    (hFunc : extractCalleeDefPath? func = .some targetDefPath)
    (hArgs :
      evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals
        (activeBodyLayouts currentBody) s.memory.callerLocals
        (callStack := s.memory.callStack) = .ok argVals locals')
    (hNoConflict :
      hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
        (Trusted.Sequence.length s.memory.callStack)
        (Trusted.Sequence.length s.frame.locals) = false)
    (hExcl : CalleeTableExcludes s.memory targetDefPath) :
    evalTerminator s term currentBody =
      MirStepNode.extCall
        { defPath := targetDefPath, typeArgs := extractCalleeTypeArgs func,
          args := argVals,
          memory :=
            { s.memory with
              borrows :=
                disableFrameBorrows s.memory.borrows
                  (Trusted.Sequence.length s.memory.callStack)
                  (Trusted.Sequence.length s.frame.locals) } }
        resumeExternalTailCall :=
  evalTerminator_tailCall_extCall_of_calleeTableExcludes
    (target :=
      { defPath := targetDefPath, typeArgs := extractCalleeTypeArgs func,
        fnSig := .none, isIndirect := false })
    hKind (resolveCallTarget_of_extractCalleeDefPath s func targetDefPath _ _ _ hFunc)
    hArgs hNoConflict hExcl

/--
The capture-level guard establishes the runtime guard in the initial memory of
`callerBody` linked with `callees`.
-/
theorem CallBoundaryPreserved.calleeTableExcludes_init {callerBody : CapturedMir}
    {callees : List CapturedMir} {targetDefPath : DefPath}
    (h : CallBoundaryPreserved callerBody callees targetDefPath) (args : List Value) :
    CalleeTableExcludes (initMachineStateWithCallees callerBody args callees).memory
      targetDefPath := by
  cases callees with
  | nil =>
    exact calleeTableExcludes_of_callees_nil rfl
  | cons c cs =>
    exact calleeTableExcludes_of_no_callee_no_traitImpl h.notLinked h.noTraitImpl

/--
When `callees` is nonempty, `initMachineStateWithMemoryAndCallees` replaces
`mem.callees` and `mem.traitImpls`, so `CallBoundaryPreserved` establishes the
runtime guard for any initial memory `mem`. When `callees = []`,
`initMachineStateWithMemoryAndCallees` keeps `mem` untouched and the caller
must establish `CalleeTableExcludes mem targetDefPath` directly.
-/
theorem CallBoundaryPreserved.calleeTableExcludes_initStateful_of_ne_nil
    {callerBody : CapturedMir} {callees : List CapturedMir} {targetDefPath : DefPath}
    (h : CallBoundaryPreserved callerBody callees targetDefPath)
    (hNe : callees ≠ .nil) (args : List Value) (mem : Memory) :
    CalleeTableExcludes
      (initMachineStateWithMemoryAndCallees callerBody args mem callees).memory
      targetDefPath := by
  cases callees with
  | nil => exact False.elim (hNe rfl)
  | cons c cs =>
    exact calleeTableExcludes_of_no_callee_no_traitImpl h.notLinked h.noTraitImpl

/--
The transitive helper boundary guard establishes the runtime guard in the
initial memory of `callerBody` linked with `callees`.
-/
theorem CalleesCallBoundaryPreserved.calleeTableExcludes_init {callerBody : CapturedMir}
    {callees : List CapturedMir} {expectedCallers : List DefPath}
    {targetDefPath : DefPath}
    (h : CalleesCallBoundaryPreserved callerBody callees expectedCallers targetDefPath)
    (args : List Value) :
    CalleeTableExcludes (initMachineStateWithCallees callerBody args callees).memory
      targetDefPath := by
  cases callees with
  | nil =>
    exact calleeTableExcludes_of_callees_nil rfl
  | cons c cs =>
    exact calleeTableExcludes_of_no_callee_no_traitImpl h.notLinked h.noTraitImpl

theorem CalleesCallBoundaryPreserved.calleeTableExcludes_initStateful_of_ne_nil
    {callerBody : CapturedMir} {callees : List CapturedMir}
    {expectedCallers : List DefPath} {targetDefPath : DefPath}
    (h : CalleesCallBoundaryPreserved callerBody callees expectedCallers targetDefPath)
    (hNe : callees ≠ .nil) (args : List Value) (mem : Memory) :
    CalleeTableExcludes
      (initMachineStateWithMemoryAndCallees callerBody args mem callees).memory
      targetDefPath := by
  cases callees with
  | nil => exact False.elim (hNe rfl)
  | cons c cs =>
    exact calleeTableExcludes_of_no_callee_no_traitImpl h.notLinked h.noTraitImpl

/-! ### Scope limits of the syntactic layer -/

/--
The checker sees only constant function-item operands. A call through a `copy`
operand (a function pointer, or a zero-sized function-item local) is never
reported, whatever it resolves to at run time.
-/
theorem not_terminatorCallsDefPath_of_copy (targetDefPath : DefPath) (place : Place)
    (args : List Operand) (destination : Place) (target : Option BasicBlockIdx)
    (unwind : UnwindAction) (span : String) :
    terminatorCallsDefPath targetDefPath
      { kind := .call (.copy place) args destination target unwind, span := span } =
      false :=
  rfl

/-- A call through a `move` operand is never reported either. -/
theorem not_terminatorCallsDefPath_of_move (targetDefPath : DefPath) (place : Place)
    (args : List Operand) (destination : Place) (target : Option BasicBlockIdx)
    (unwind : UnwindAction) (span : String) :
    terminatorCallsDefPath targetDefPath
      { kind := .call (.move place) args destination target unwind, span := span } =
      false :=
  rfl

/-- A tail call through a `copy` or `move` operand is never reported. -/
theorem not_terminatorCallsDefPath_of_indirect_tailCall (targetDefPath : DefPath)
    (place : Place) (args : List Operand) (span : String) :
    terminatorCallsDefPath targetDefPath
        { kind := .tailCall (.copy place) args, span := span } = false ∧
      terminatorCallsDefPath targetDefPath
        { kind := .tailCall (.move place) args, span := span } = false :=
  ⟨rfl, rfl⟩

/--
The checker is purely syntactic: a block that calls `targetDefPath` satisfies it
wherever the block sits, so an unreachable decoy block appended to a body from
which the real call was inlined away is accepted.
-/
theorem bodyCallsDefPath_append_block (targetDefPath : DefPath) (body : CapturedMir)
    (decoy : BasicBlockData)
    (hDecoy : terminatorCallsDefPath targetDefPath decoy.terminator = true) :
    bodyCallsDefPath targetDefPath
      { body with basicBlocks := body.basicBlocks ++ [decoy] } = true := by
  unfold bodyCallsDefPath
  rw [List.any_eq_true]
  exact ⟨decoy, List.mem_append_right _ (List.mem_singleton.2 rfl), hDecoy⟩

/-- A body without basic blocks calls nothing. -/
theorem not_bodyCallsDefPath_of_no_blocks (targetDefPath : DefPath) (body : CapturedMir)
    (hNil : body.basicBlocks = .nil) : bodyCallsDefPath targetDefPath body = false := by
  unfold bodyCallsDefPath
  rw [hNil]
  rfl

/-! ### Call-site counts -/

/-- Number of basic blocks of `body` that end in a direct call to `targetDefPath`. -/
def bodyCallSiteCount (targetDefPath : DefPath) (body : CapturedMir) : Nat :=
  body.basicBlocks.countP (fun bb => terminatorCallsDefPath targetDefPath bb.terminator)

/-- A body calls the target exactly when it has at least one direct call site. -/
theorem bodyCallsDefPath_iff_bodyCallSiteCount_pos (targetDefPath : DefPath)
    (body : CapturedMir) :
    bodyCallsDefPath targetDefPath body = true ↔
      0 < bodyCallSiteCount targetDefPath body := by
  unfold bodyCallsDefPath bodyCallSiteCount
  rw [List.any_eq_true, List.countP_pos_iff]

/--
Capture-level call-boundary guard with a call-site count.
`CallBoundaryPreserved` asks for one surviving direct call, so a caller with
several calls to the target still satisfies it after all but one of them were
inlined before capture. This guard pins the number of direct call sites to
`expectedSites`, the number recorded for the caller before optimization.

The count is syntactic, as `BodyCallsDefPath` is: it does not distinguish a
reachable call from an unreachable decoy block.
-/
structure CallSitesPreserved (callerBody : CapturedMir) (callees : List CapturedMir)
    (targetDefPath : DefPath) (expectedSites : Nat) : Prop where
  /-- The captured caller has exactly `expectedSites` direct calls to the target. -/
  siteCount : bodyCallSiteCount targetDefPath callerBody = expectedSites
  /-- No linked body has the target's path. -/
  notLinked : findCallee? callees targetDefPath = .none
  /-- No trait implementation of the caller or of a linked body dispatches the target. -/
  noTraitImpl :
    hasTraitImplForDefPath (callerBody.traitImpls ++ flatMapTraitImpls callees)
      targetDefPath = false

/-- Checker for `CallSitesPreserved`. -/
def callSitesPreserved (callerBody : CapturedMir) (callees : List CapturedMir)
    (targetDefPath : DefPath) (expectedSites : Nat) : Bool :=
  Nat.beq (bodyCallSiteCount targetDefPath callerBody) expectedSites &&
    ((findCallee? callees targetDefPath).isNone &&
      !hasTraitImplForDefPath (callerBody.traitImpls ++ flatMapTraitImpls callees)
        targetDefPath)

/-- The checker decides `CallSitesPreserved`. -/
theorem callSitesPreserved_iff (callerBody : CapturedMir) (callees : List CapturedMir)
    (targetDefPath : DefPath) (expectedSites : Nat) :
    callSitesPreserved callerBody callees targetDefPath expectedSites = true ↔
      CallSitesPreserved callerBody callees targetDefPath expectedSites := by
  unfold callSitesPreserved
  simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none]
  exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨Nat.eq_of_beq_eq_true h₁, h₂, h₃⟩,
    fun h => ⟨h.siteCount ▸ Nat.beq_refl _, h.notLinked, h.noTraitImpl⟩⟩

/-- With at least one expected site, the counted guard implies `CallBoundaryPreserved`. -/
theorem CallSitesPreserved.toCallBoundaryPreserved {callerBody : CapturedMir}
    {callees : List CapturedMir} {targetDefPath : DefPath} {expectedSites : Nat}
    (h : CallSitesPreserved callerBody callees targetDefPath expectedSites)
    (hPos : 0 < expectedSites) :
    CallBoundaryPreserved callerBody callees targetDefPath :=
  ⟨(bodyCallsDefPath_iff _ _).1
      ((bodyCallsDefPath_iff_bodyCallSiteCount_pos _ _).2 (h.siteCount ▸ hPos)),
    h.notLinked, h.noTraitImpl⟩

/-- The counted guard rejects a caller whose number of direct call sites changed. -/
theorem not_callSitesPreserved_of_count_ne {callerBody : CapturedMir}
    {callees : List CapturedMir} {targetDefPath : DefPath} {expectedSites : Nat}
    (hNe : bodyCallSiteCount targetDefPath callerBody ≠ expectedSites) :
    ¬ CallSitesPreserved callerBody callees targetDefPath expectedSites :=
  fun h => hNe h.siteCount

/--
Scope limit of `CallBoundaryPreserved`: it holds for every positive number of
surviving call sites, so it cannot tell a caller with all `n + 1` sites from one
in which `n` of them were inlined.
-/
theorem callBoundaryPreserved_iff_exists_callSitesPreserved (callerBody : CapturedMir)
    (callees : List CapturedMir) (targetDefPath : DefPath) :
    CallBoundaryPreserved callerBody callees targetDefPath ↔
      ∃ n, 0 < n ∧ CallSitesPreserved callerBody callees targetDefPath n :=
  ⟨fun h =>
      ⟨bodyCallSiteCount targetDefPath callerBody,
        (bodyCallsDefPath_iff_bodyCallSiteCount_pos _ _).1
          ((bodyCallsDefPath_iff _ _).2 h.callSite),
        rfl, h.notLinked, h.noTraitImpl⟩,
    fun ⟨_, hPos, h⟩ => h.toCallBoundaryPreserved hPos⟩

/-! ## 8. Transfer Across `Anneal.Pass` Refinements -/

section PassVariance

universe v₁ v₂

variable {Obs Val : Type u} {Inp : Type w}

/--
Behavior domain of a contracted program over `Anneal.Pass` behavior sets: for
each input, the UB-closed set of projected execution prefixes. It is ordered
pointwise by inclusion.
-/
abbrev PanicBehavior (Obs Val : Type u) (Inp : Type w) : Type (max u w) :=
  Inp → BehaviorSet (ObsPrefix Obs (Outcome Val))

/-- Behavior of a tree family under the observation projection `proj`. -/
def panicBehavior {E : Effect.{u}} [FaultEffect E] (proj : EffectObs E Obs)
    (tree : Inp → ITree E (Outcome Val)) : PanicBehavior Obs Val Inp :=
  fun x => UBClosedObsPrefixes proj (tree x)

/-- Behavior semantics of a family of programs with tree semantics `sem`. -/
def panicSemantics {Prog : Type v₁} {E : Effect.{u}} [FaultEffect E]
    (proj : EffectObs E Obs) (sem : Prog → Inp → ITree E (Outcome Val)) :
    Semantics Prog (PanicBehavior Obs Val Inp) :=
  fun p => panicBehavior proj (sem p)

/--
Classifier of an execution prefix under a policy contract: a running prefix is
accepted, a completed one is classified by `PolicyOutcomeOk`, and a faulting one
is rejected.
-/
def PolicyPrefixOk (policy : AbortPolicy Inp) (x : Inp) (post : Val → Prop)
    (panicCond : Prop) : TreePrefixOutcome (Outcome Val) → Prop
  | .running => True
  | .ret out => PolicyOutcomeOk policy x post panicCond out
  | .fault => False

/--
`PanicsWithPolicyOnlyIf` as a downward-closed specification on behaviors. It
depends on outcomes only, not on the observation trace.
-/
def PanicPolicySpec (pre : Inp → Prop) (post : Inp → Val → Prop)
    (panicCond : Inp → Prop) (policy : AbortPolicy Inp) :
    Spec (PanicBehavior Obs Val Inp) where
  holds B :=
    ∀ x, pre x → ∀ p, B x p → PolicyPrefixOk policy x (post x) (panicCond x) p.outcome
  downward_closed _ _ h_ref h_high x hx p hp := h_high x hx p (h_ref x p hp)

/-- `PanicsOnlyIf` as a downward-closed specification on behaviors. -/
def PanicSpec (pre : Inp → Prop) (post : Inp → Val → Prop) (panicCond : Inp → Prop) :
    Spec (PanicBehavior Obs Val Inp) :=
  PanicPolicySpec pre post panicCond .forbidAbort

section Trees

variable {E : Effect.{u}} [FaultEffect E] {tree : Inp → ITree E (Outcome Val)}
  {pre : Inp → Prop} {post : Inp → Val → Prop} {panicCond : Inp → Prop}
  {policy : AbortPolicy Inp}

/-- The specification holds of the behavior of a tree family exactly when the contract does. -/
theorem panicPolicySpec_holds_iff (proj : EffectObs E Obs) :
    (PanicPolicySpec pre post panicCond policy).holds (panicBehavior proj tree) ↔
      PanicsWithPolicyOnlyIf tree pre post panicCond policy := by
  constructor
  · intro h x hx
    refine ⟨fun tr u hru hfu => ?_, fun tr out hr => ?_⟩
    · exact h x hx ⟨tr.filterMap proj.obsOf, .fault⟩ (Or.inl ⟨tr, u, hru, hfu, rfl⟩)
    · exact h x hx ⟨tr.filterMap proj.obsOf, .ret out⟩ (Or.inl ⟨tr, hr, rfl⟩)
  · intro h x hx p hp
    obtain ⟨hs, hRet⟩ := h x hx
    have hp' : HasObsPrefix proj (tree x) p := by
      have hEq := ubClosedObsPrefixes_eq_of_treeSafe proj hs
      exact hEq ▸ hp
    cases ho : p.outcome with
    | running => trivial
    | ret out =>
      simp only [HasObsPrefix, ho] at hp'
      obtain ⟨tr, hr, _⟩ := hp'
      exact hRet tr out hr
    | fault =>
      simp only [HasObsPrefix, ho] at hp'
      obtain ⟨tr, u, hru, hfu, _⟩ := hp'
      exact hs tr u hru hfu

/-- The specification holds of the behavior of a tree family exactly when `PanicsOnlyIf` does. -/
theorem panicSpec_holds_iff (proj : EffectObs E Obs) :
    (PanicSpec pre post panicCond).holds (panicBehavior proj tree) ↔
      PanicsOnlyIf tree pre post panicCond :=
  (panicPolicySpec_holds_iff proj).trans panicsWithPolicyOnlyIf_forbidAbort_iff

/--
Generic trigger: every input satisfying `pre` and `cond` has a completed
execution whose outcome is in `kind`. `PanicsIf`, `AbortsIf`, `FailsIf`, and
`ReturnsIf` are instances.
-/
def ReachesOutcomeIf (tree : Inp → ITree E (Outcome Val)) (pre cond : Inp → Prop)
    (kind : Outcome Val → Prop) : Prop :=
  ∀ x, pre x → cond x → ∃ tr out, ReachesRet (tree x) tr out ∧ kind out

theorem panicsIf_iff_reachesOutcomeIf {cond : Inp → Prop} :
    PanicsIf tree pre cond ↔ ReachesOutcomeIf tree pre cond (fun out => out = .panic) :=
  ⟨fun h x hx hc => (h x hx hc).elim fun tr hr => ⟨tr, _, hr, rfl⟩,
   fun h x hx hc => by
     obtain ⟨tr, out, hr, hOut⟩ := h x hx hc
     exact ⟨tr, hOut ▸ hr⟩⟩

theorem abortsIf_iff_reachesOutcomeIf {cond : Inp → Prop} :
    AbortsIf tree pre cond ↔ ReachesOutcomeIf tree pre cond (fun out => out = .abort) :=
  ⟨fun h x hx hc => (h x hx hc).elim fun tr hr => ⟨tr, _, hr, rfl⟩,
   fun h x hx hc => by
     obtain ⟨tr, out, hr, hOut⟩ := h x hx hc
     exact ⟨tr, hOut ▸ hr⟩⟩

theorem failsIf_iff_reachesOutcomeIf {cond : Inp → Prop} :
    FailsIf tree pre cond ↔
      ReachesOutcomeIf tree pre cond (fun out => out = .panic ∨ out = .abort) :=
  ⟨fun h x hx hc => (h x hx hc).elim fun tr hr =>
     hr.elim (fun hp => ⟨tr, _, hp, Or.inl rfl⟩) (fun ha => ⟨tr, _, ha, Or.inr rfl⟩),
   fun h x hx hc => by
     obtain ⟨tr, out, hr, hOut⟩ := h x hx hc
     rcases hOut with hOut | hOut
     · exact ⟨tr, Or.inl (hOut ▸ hr)⟩
     · exact ⟨tr, Or.inr (hOut ▸ hr)⟩⟩

theorem returnsIf_iff_reachesOutcomeIf {cond : Inp → Prop} :
    ReturnsIf tree pre cond ↔
      ReachesOutcomeIf tree pre cond (fun out => ∃ v, out = .normal v) :=
  ⟨fun h x hx hc => by
     obtain ⟨tr, v, hr⟩ := h x hx hc
     exact ⟨tr, _, hr, v, rfl⟩,
   fun h x hx hc => by
     obtain ⟨tr, out, hr, v, hOut⟩ := h x hx hc
     exact ⟨tr, v, hOut ▸ hr⟩⟩

end Trees

section Transfer

variable {Prog₁ : Type v₁} {Prog₂ : Type v₂}
  {E₁ E₂ : Effect.{u}} [FaultEffect E₁] [FaultEffect E₂]
  {proj₁ : EffectObs E₁ Obs} {proj₂ : EffectObs E₂ Obs}
  {sem₁ : Prog₁ → Inp → ITree E₁ (Outcome Val)}
  {sem₂ : Prog₂ → Inp → ITree E₂ (Outcome Val)}
  {p₁ : Prog₁} {p₂ : Prog₂}
  {pre : Inp → Prop} {post : Inp → Val → Prop} {panicCond : Inp → Prop}
  {policy : AbortPolicy Inp}

/--
Completed executions pull back along behavior inclusion into a fault-free tree:
if every behavior of `t₂` is a behavior of `t₁` and `t₁` is fault-free, every
outcome `t₂` reaches is reached by `t₁`.
-/
theorem exists_reachesRet_of_ubClosedObsPrefixes_le {R : Type u}
    {t₁ : ITree E₁ R} {t₂ : ITree E₂ R}
    (hLe : UBClosedObsPrefixes proj₂ t₂ ≤ UBClosedObsPrefixes proj₁ t₁)
    (hSafe : TreeSafe t₁) {tr : List (Event E₂)} {r : R} (hr : ReachesRet t₂ tr r) :
    ∃ tr', ReachesRet t₁ tr' r := by
  have h₂ : UBClosedObsPrefixes proj₂ t₂ ⟨tr.filterMap proj₂.obsOf, .ret r⟩ :=
    Or.inl ⟨tr, hr, rfl⟩
  have h₁ : HasObsPrefix proj₁ t₁ ⟨tr.filterMap proj₂.obsOf, .ret r⟩ := by
    have hEq := ubClosedObsPrefixes_eq_of_treeSafe proj₁ hSafe
    exact hEq ▸ hLe _ h₂
  obtain ⟨tr', hr', _⟩ := h₁
  exact ⟨tr', hr'⟩

/--
A trigger transfers against behavior inclusion: if the behaviors of `tree₂` are
included in those of the fault-free `tree₁` on `pre`, a trigger of `tree₂` is a
trigger of `tree₁`.
-/
theorem ReachesOutcomeIf.of_behavior_le
    {tree₁ : Inp → ITree E₁ (Outcome Val)} {tree₂ : Inp → ITree E₂ (Outcome Val)}
    {cond : Inp → Prop} {kind : Outcome Val → Prop}
    (hLe : panicBehavior proj₂ tree₂ ≤ panicBehavior proj₁ tree₁)
    (hSafe : ∀ x, pre x → TreeSafe (tree₁ x))
    (h : ReachesOutcomeIf tree₂ pre cond kind) :
    ReachesOutcomeIf tree₁ pre cond kind := by
  intro x hx hc
  obtain ⟨tr, out, hr, hKind⟩ := h x hx hc
  obtain ⟨tr', hr'⟩ := exists_reachesRet_of_ubClosedObsPrefixes_le (hLe x) (hSafe x hx) hr
  exact ⟨tr', out, hr', hKind⟩

/-! ### Only-if contracts: forward across `CompilerPass`, backward across `VerifierPass` -/

/-- A compiler pass preserves `PanicsWithPolicyOnlyIf` from source to target. -/
theorem PanicsWithPolicyOnlyIf.compilerPass_forward
    {G₁ : Spec (PanicBehavior Obs Val Inp)}
    (hPass : CompilerPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) G₁ id
      p₁ p₂)
    (hGuard : G₁.holds (panicSemantics proj₁ sem₁ p₁))
    (h : PanicsWithPolicyOnlyIf (sem₁ p₁) pre post panicCond policy) :
    PanicsWithPolicyOnlyIf (sem₂ p₂) pre post panicCond policy :=
  (panicPolicySpec_holds_iff proj₂).1
    (GuardedRefines.transfer hPass hGuard (PanicPolicySpec pre post panicCond policy)
      ((panicPolicySpec_holds_iff proj₁).2 h))

/-- A compiler pass preserves `PanicsOnlyIf` from source to target. -/
theorem PanicsOnlyIf.compilerPass_forward
    {G₁ : Spec (PanicBehavior Obs Val Inp)}
    (hPass : CompilerPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) G₁ id
      p₁ p₂)
    (hGuard : G₁.holds (panicSemantics proj₁ sem₁ p₁))
    (h : PanicsOnlyIf (sem₁ p₁) pre post panicCond) :
    PanicsOnlyIf (sem₂ p₂) pre post panicCond :=
  panicsWithPolicyOnlyIf_forbidAbort_iff.1
    (PanicsWithPolicyOnlyIf.compilerPass_forward hPass hGuard
      (panicsWithPolicyOnlyIf_forbidAbort_iff.2 h))

/-- A verifier pass reflects `PanicsWithPolicyOnlyIf` from the verified model to the program. -/
theorem PanicsWithPolicyOnlyIf.verifierPass_backward
    {G₂ : Spec (PanicBehavior Obs Val Inp)}
    (hPass : VerifierPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) G₂ id
      p₁ p₂)
    (hGuard : G₂.holds (panicSemantics proj₂ sem₂ p₂))
    (h : PanicsWithPolicyOnlyIf (sem₂ p₂) pre post panicCond policy) :
    PanicsWithPolicyOnlyIf (sem₁ p₁) pre post panicCond policy :=
  (panicPolicySpec_holds_iff proj₁).1
    (GuardedRefines.transfer hPass hGuard (PanicPolicySpec pre post panicCond policy)
      ((panicPolicySpec_holds_iff proj₂).2 h))

/-- A verifier pass reflects `PanicsOnlyIf` from the verified model to the program. -/
theorem PanicsOnlyIf.verifierPass_backward
    {G₂ : Spec (PanicBehavior Obs Val Inp)}
    (hPass : VerifierPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) G₂ id
      p₁ p₂)
    (hGuard : G₂.holds (panicSemantics proj₂ sem₂ p₂))
    (h : PanicsOnlyIf (sem₂ p₂) pre post panicCond) :
    PanicsOnlyIf (sem₁ p₁) pre post panicCond :=
  panicsWithPolicyOnlyIf_forbidAbort_iff.1
    (PanicsWithPolicyOnlyIf.verifierPass_backward hPass hGuard
      (panicsWithPolicyOnlyIf_forbidAbort_iff.2 h))

/-- An exact pass preserves `PanicsWithPolicyOnlyIf` in both directions. -/
theorem panicsWithPolicyOnlyIf_exactPass_iff
    (hPass : ExactPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) id id
      p₁ p₂) :
    PanicsWithPolicyOnlyIf (sem₁ p₁) pre post panicCond policy ↔
      PanicsWithPolicyOnlyIf (sem₂ p₂) pre post panicCond policy :=
  ⟨PanicsWithPolicyOnlyIf.compilerPass_forward (hPass.toCompilerPass Spec.top) trivial,
   PanicsWithPolicyOnlyIf.verifierPass_backward (hPass.toVerifierPass Spec.top) trivial⟩

/-- An exact pass preserves `PanicsOnlyIf` in both directions. -/
theorem panicsOnlyIf_exactPass_iff
    (hPass : ExactPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) id id
      p₁ p₂) :
    PanicsOnlyIf (sem₁ p₁) pre post panicCond ↔ PanicsOnlyIf (sem₂ p₂) pre post panicCond :=
  ⟨PanicsOnlyIf.compilerPass_forward (hPass.toCompilerPass Spec.top) trivial,
   PanicsOnlyIf.verifierPass_backward (hPass.toVerifierPass Spec.top) trivial⟩

/-- A compiler pass preserves `PanicsOrAbortsOnlyIf` from source to target. -/
theorem PanicsOrAbortsOnlyIf.compilerPass_forward
    {G₁ : Spec (PanicBehavior Obs Val Inp)} {abortCond : Inp → Prop}
    (hPass : CompilerPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) G₁ id
      p₁ p₂)
    (hGuard : G₁.holds (panicSemantics proj₁ sem₁ p₁))
    (h : PanicsOrAbortsOnlyIf (sem₁ p₁) pre post panicCond abortCond) :
    PanicsOrAbortsOnlyIf (sem₂ p₂) pre post panicCond abortCond :=
  panicsWithPolicyOnlyIf_abortOnlyIf_iff.1
    (PanicsWithPolicyOnlyIf.compilerPass_forward hPass hGuard
      (panicsWithPolicyOnlyIf_abortOnlyIf_iff.2 h))

/-- A verifier pass reflects `PanicsOrAbortsOnlyIf` from the verified model to the program. -/
theorem PanicsOrAbortsOnlyIf.verifierPass_backward
    {G₂ : Spec (PanicBehavior Obs Val Inp)} {abortCond : Inp → Prop}
    (hPass : VerifierPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) G₂ id
      p₁ p₂)
    (hGuard : G₂.holds (panicSemantics proj₂ sem₂ p₂))
    (h : PanicsOrAbortsOnlyIf (sem₂ p₂) pre post panicCond abortCond) :
    PanicsOrAbortsOnlyIf (sem₁ p₁) pre post panicCond abortCond :=
  panicsWithPolicyOnlyIf_abortOnlyIf_iff.1
    (PanicsWithPolicyOnlyIf.verifierPass_backward hPass hGuard
      (panicsWithPolicyOnlyIf_abortOnlyIf_iff.2 h))

/-- An exact pass preserves `PanicsOrAbortsOnlyIf` in both directions. -/
theorem panicsOrAbortsOnlyIf_exactPass_iff {abortCond : Inp → Prop}
    (hPass : ExactPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) id id
      p₁ p₂) :
    PanicsOrAbortsOnlyIf (sem₁ p₁) pre post panicCond abortCond ↔
      PanicsOrAbortsOnlyIf (sem₂ p₂) pre post panicCond abortCond :=
  ⟨PanicsOrAbortsOnlyIf.compilerPass_forward (hPass.toCompilerPass Spec.top) trivial,
   PanicsOrAbortsOnlyIf.verifierPass_backward (hPass.toVerifierPass Spec.top) trivial⟩

/-- A compiler pass preserves `NeverPanics` from source to target. -/
theorem NeverPanics.compilerPass_forward
    {G₁ : Spec (PanicBehavior Obs Val Inp)}
    (hPass : CompilerPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) G₁ id
      p₁ p₂)
    (hGuard : G₁.holds (panicSemantics proj₁ sem₁ p₁))
    (h : NeverPanics (sem₁ p₁) pre post) :
    NeverPanics (sem₂ p₂) pre post :=
  PanicsOnlyIf.compilerPass_forward hPass hGuard h

/-- A verifier pass reflects `NeverPanics` from the verified model to the program. -/
theorem NeverPanics.verifierPass_backward
    {G₂ : Spec (PanicBehavior Obs Val Inp)}
    (hPass : VerifierPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) G₂ id
      p₁ p₂)
    (hGuard : G₂.holds (panicSemantics proj₂ sem₂ p₂))
    (h : NeverPanics (sem₂ p₂) pre post) :
    NeverPanics (sem₁ p₁) pre post :=
  PanicsOnlyIf.verifierPass_backward hPass hGuard h

/-- An exact pass preserves `NeverPanics` in both directions. -/
theorem neverPanics_exactPass_iff
    (hPass : ExactPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) id id
      p₁ p₂) :
    NeverPanics (sem₁ p₁) pre post ↔ NeverPanics (sem₂ p₂) pre post :=
  panicsOnlyIf_exactPass_iff hPass

/-! ### Triggers: backward across `CompilerPass`, forward across `VerifierPass` -/

/--
A compiler pass reflects triggers from target to source: an outcome the target
can reach is an outcome of the fault-free source. The converse fails, because a
compiler pass may remove executions.
-/
theorem ReachesOutcomeIf.compilerPass_backward
    {G₁ : Spec (PanicBehavior Obs Val Inp)} {cond : Inp → Prop}
    {kind : Outcome Val → Prop}
    (hPass : CompilerPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) G₁ id
      p₁ p₂)
    (hGuard : G₁.holds (panicSemantics proj₁ sem₁ p₁))
    (hSafe : ∀ x, pre x → TreeSafe (sem₁ p₁ x))
    (h : ReachesOutcomeIf (sem₂ p₂) pre cond kind) :
    ReachesOutcomeIf (sem₁ p₁) pre cond kind :=
  ReachesOutcomeIf.of_behavior_le (hPass hGuard) hSafe h

/--
A verifier pass preserves triggers from the program to the verified model: an
outcome the program can reach is an outcome of the fault-free model.
-/
theorem ReachesOutcomeIf.verifierPass_forward
    {G₂ : Spec (PanicBehavior Obs Val Inp)} {cond : Inp → Prop}
    {kind : Outcome Val → Prop}
    (hPass : VerifierPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) G₂ id
      p₁ p₂)
    (hGuard : G₂.holds (panicSemantics proj₂ sem₂ p₂))
    (hSafe : ∀ x, pre x → TreeSafe (sem₂ p₂ x))
    (h : ReachesOutcomeIf (sem₁ p₁) pre cond kind) :
    ReachesOutcomeIf (sem₂ p₂) pre cond kind :=
  ReachesOutcomeIf.of_behavior_le (hPass hGuard) hSafe h

/-- `PanicsIf` transfers backward across a compiler pass with a fault-free source. -/
theorem PanicsIf.compilerPass_backward
    {G₁ : Spec (PanicBehavior Obs Val Inp)}
    (hPass : CompilerPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) G₁ id
      p₁ p₂)
    (hGuard : G₁.holds (panicSemantics proj₁ sem₁ p₁))
    (hSafe : ∀ x, pre x → TreeSafe (sem₁ p₁ x))
    (h : PanicsIf (sem₂ p₂) pre panicCond) :
    PanicsIf (sem₁ p₁) pre panicCond :=
  panicsIf_iff_reachesOutcomeIf.2
    (ReachesOutcomeIf.compilerPass_backward hPass hGuard hSafe
      (panicsIf_iff_reachesOutcomeIf.1 h))

/-- `AbortsIf` transfers backward across a compiler pass with a fault-free source. -/
theorem AbortsIf.compilerPass_backward
    {G₁ : Spec (PanicBehavior Obs Val Inp)} {abortCond : Inp → Prop}
    (hPass : CompilerPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) G₁ id
      p₁ p₂)
    (hGuard : G₁.holds (panicSemantics proj₁ sem₁ p₁))
    (hSafe : ∀ x, pre x → TreeSafe (sem₁ p₁ x))
    (h : AbortsIf (sem₂ p₂) pre abortCond) :
    AbortsIf (sem₁ p₁) pre abortCond :=
  abortsIf_iff_reachesOutcomeIf.2
    (ReachesOutcomeIf.compilerPass_backward hPass hGuard hSafe
      (abortsIf_iff_reachesOutcomeIf.1 h))

/-- `FailsIf` transfers backward across a compiler pass with a fault-free source. -/
theorem FailsIf.compilerPass_backward
    {G₁ : Spec (PanicBehavior Obs Val Inp)} {failCond : Inp → Prop}
    (hPass : CompilerPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) G₁ id
      p₁ p₂)
    (hGuard : G₁.holds (panicSemantics proj₁ sem₁ p₁))
    (hSafe : ∀ x, pre x → TreeSafe (sem₁ p₁ x))
    (h : FailsIf (sem₂ p₂) pre failCond) :
    FailsIf (sem₁ p₁) pre failCond :=
  failsIf_iff_reachesOutcomeIf.2
    (ReachesOutcomeIf.compilerPass_backward hPass hGuard hSafe
      (failsIf_iff_reachesOutcomeIf.1 h))

/-- `PanicsIf` transfers forward across a verifier pass with a fault-free model. -/
theorem PanicsIf.verifierPass_forward
    {G₂ : Spec (PanicBehavior Obs Val Inp)}
    (hPass : VerifierPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) G₂ id
      p₁ p₂)
    (hGuard : G₂.holds (panicSemantics proj₂ sem₂ p₂))
    (hSafe : ∀ x, pre x → TreeSafe (sem₂ p₂ x))
    (h : PanicsIf (sem₁ p₁) pre panicCond) :
    PanicsIf (sem₂ p₂) pre panicCond :=
  panicsIf_iff_reachesOutcomeIf.2
    (ReachesOutcomeIf.verifierPass_forward hPass hGuard hSafe
      (panicsIf_iff_reachesOutcomeIf.1 h))

/-- `AbortsIf` transfers forward across a verifier pass with a fault-free model. -/
theorem AbortsIf.verifierPass_forward
    {G₂ : Spec (PanicBehavior Obs Val Inp)} {abortCond : Inp → Prop}
    (hPass : VerifierPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) G₂ id
      p₁ p₂)
    (hGuard : G₂.holds (panicSemantics proj₂ sem₂ p₂))
    (hSafe : ∀ x, pre x → TreeSafe (sem₂ p₂ x))
    (h : AbortsIf (sem₁ p₁) pre abortCond) :
    AbortsIf (sem₂ p₂) pre abortCond :=
  abortsIf_iff_reachesOutcomeIf.2
    (ReachesOutcomeIf.verifierPass_forward hPass hGuard hSafe
      (abortsIf_iff_reachesOutcomeIf.1 h))

/-- `FailsIf` transfers forward across a verifier pass with a fault-free model. -/
theorem FailsIf.verifierPass_forward
    {G₂ : Spec (PanicBehavior Obs Val Inp)} {failCond : Inp → Prop}
    (hPass : VerifierPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) G₂ id
      p₁ p₂)
    (hGuard : G₂.holds (panicSemantics proj₂ sem₂ p₂))
    (hSafe : ∀ x, pre x → TreeSafe (sem₂ p₂ x))
    (h : FailsIf (sem₁ p₁) pre failCond) :
    FailsIf (sem₂ p₂) pre failCond :=
  failsIf_iff_reachesOutcomeIf.2
    (ReachesOutcomeIf.verifierPass_forward hPass hGuard hSafe
      (failsIf_iff_reachesOutcomeIf.1 h))

/-- An exact pass preserves triggers in both directions between fault-free programs. -/
theorem reachesOutcomeIf_exactPass_iff {cond : Inp → Prop} {kind : Outcome Val → Prop}
    (hPass : ExactPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) id id
      p₁ p₂)
    (hSafe₁ : ∀ x, pre x → TreeSafe (sem₁ p₁ x))
    (hSafe₂ : ∀ x, pre x → TreeSafe (sem₂ p₂ x)) :
    ReachesOutcomeIf (sem₁ p₁) pre cond kind ↔ ReachesOutcomeIf (sem₂ p₂) pre cond kind :=
  ⟨ReachesOutcomeIf.verifierPass_forward (hPass.toVerifierPass Spec.top) trivial hSafe₂,
   ReachesOutcomeIf.compilerPass_backward (hPass.toCompilerPass Spec.top) trivial hSafe₁⟩

/-- An exact pass preserves `PanicsIf` in both directions between fault-free programs. -/
theorem panicsIf_exactPass_iff
    (hPass : ExactPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) id id
      p₁ p₂)
    (hSafe₁ : ∀ x, pre x → TreeSafe (sem₁ p₁ x))
    (hSafe₂ : ∀ x, pre x → TreeSafe (sem₂ p₂ x)) :
    PanicsIf (sem₁ p₁) pre panicCond ↔ PanicsIf (sem₂ p₂) pre panicCond :=
  panicsIf_iff_reachesOutcomeIf.trans
    ((reachesOutcomeIf_exactPass_iff hPass hSafe₁ hSafe₂).trans
      panicsIf_iff_reachesOutcomeIf.symm)

/-- An exact pass preserves `AbortsIf` in both directions between fault-free programs. -/
theorem abortsIf_exactPass_iff {abortCond : Inp → Prop}
    (hPass : ExactPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) id id
      p₁ p₂)
    (hSafe₁ : ∀ x, pre x → TreeSafe (sem₁ p₁ x))
    (hSafe₂ : ∀ x, pre x → TreeSafe (sem₂ p₂ x)) :
    AbortsIf (sem₁ p₁) pre abortCond ↔ AbortsIf (sem₂ p₂) pre abortCond :=
  abortsIf_iff_reachesOutcomeIf.trans
    ((reachesOutcomeIf_exactPass_iff hPass hSafe₁ hSafe₂).trans
      abortsIf_iff_reachesOutcomeIf.symm)

/-- An exact pass preserves `FailsIf` in both directions between fault-free programs. -/
theorem failsIf_exactPass_iff {failCond : Inp → Prop}
    (hPass : ExactPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) id id
      p₁ p₂)
    (hSafe₁ : ∀ x, pre x → TreeSafe (sem₁ p₁ x))
    (hSafe₂ : ∀ x, pre x → TreeSafe (sem₂ p₂ x)) :
    FailsIf (sem₁ p₁) pre failCond ↔ FailsIf (sem₂ p₂) pre failCond :=
  failsIf_iff_reachesOutcomeIf.trans
    ((reachesOutcomeIf_exactPass_iff hPass hSafe₁ hSafe₂).trans
      failsIf_iff_reachesOutcomeIf.symm)

/-! ### Exact contracts across `ExactPass` -/

/-- An exact pass preserves `ExactPanicContract` in both directions. -/
theorem exactPanicContract_exactPass_iff
    (hPass : ExactPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) id id
      p₁ p₂) :
    ExactPanicContract (sem₁ p₁) pre post panicCond ↔
      ExactPanicContract (sem₂ p₂) pre post panicCond := by
  constructor
  · rintro ⟨hOnly, hIf⟩
    have hOnly₂ := (panicsOnlyIf_exactPass_iff hPass).1 hOnly
    exact ⟨hOnly₂, PanicsIf.verifierPass_forward (hPass.toVerifierPass Spec.top) trivial
      (fun x hx => (hOnly₂ x hx).1) hIf⟩
  · rintro ⟨hOnly, hIf⟩
    have hOnly₁ := (panicsOnlyIf_exactPass_iff hPass).2 hOnly
    exact ⟨hOnly₁, PanicsIf.compilerPass_backward (hPass.toCompilerPass Spec.top) trivial
      (fun x hx => (hOnly₁ x hx).1) hIf⟩

/-- An exact pass preserves `ExactPolicyPanicContract` in both directions. -/
theorem exactPolicyPanicContract_exactPass_iff
    (hPass : ExactPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) id id
      p₁ p₂) :
    ExactPolicyPanicContract (sem₁ p₁) pre post panicCond policy ↔
      ExactPolicyPanicContract (sem₂ p₂) pre post panicCond policy := by
  constructor
  · rintro ⟨hOnly, hIf, hAb⟩
    have hOnly₂ := (panicsWithPolicyOnlyIf_exactPass_iff hPass).1 hOnly
    have hSafe₂ : ∀ x, pre x → TreeSafe (sem₂ p₂ x) := fun x hx => (hOnly₂ x hx).1
    exact ⟨hOnly₂,
      PanicsIf.verifierPass_forward (hPass.toVerifierPass Spec.top) trivial hSafe₂ hIf,
      AbortsIf.verifierPass_forward (hPass.toVerifierPass Spec.top) trivial hSafe₂ hAb⟩
  · rintro ⟨hOnly, hIf, hAb⟩
    have hOnly₁ := (panicsWithPolicyOnlyIf_exactPass_iff hPass).2 hOnly
    have hSafe₁ : ∀ x, pre x → TreeSafe (sem₁ p₁ x) := fun x hx => (hOnly₁ x hx).1
    exact ⟨hOnly₁,
      PanicsIf.compilerPass_backward (hPass.toCompilerPass Spec.top) trivial hSafe₁ hIf,
      AbortsIf.compilerPass_backward (hPass.toCompilerPass Spec.top) trivial hSafe₁ hAb⟩

/-- An exact pass preserves `ExactPanicAbortContract` in both directions. -/
theorem exactPanicAbortContract_exactPass_iff {abortCond : Inp → Prop}
    (hPass : ExactPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) id id
      p₁ p₂) :
    ExactPanicAbortContract (sem₁ p₁) pre post panicCond abortCond ↔
      ExactPanicAbortContract (sem₂ p₂) pre post panicCond abortCond :=
  exactPolicyPanicContract_abortOnlyIf_iff.symm.trans
    ((exactPolicyPanicContract_exactPass_iff (policy := .abortOnlyIf abortCond) hPass).trans
      exactPolicyPanicContract_abortOnlyIf_iff)

/--
An exact pass carries a total exact panic contract forward once the target
terminates on `pre`. Termination is a separate hypothesis: sets of finite
prefixes do not distinguish a tree that diverges silently from one that keeps
making progress.
-/
theorem TotalExactPanicContract.exactPass_forward
    (hPass : ExactPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) id id
      p₁ p₂)
    (hTerm : TerminatesOn (sem₂ p₂) pre)
    (h : TotalExactPanicContract (sem₁ p₁) pre post panicCond) :
    TotalExactPanicContract (sem₂ p₂) pre post panicCond := by
  have hExact₂ := (exactPanicContract_exactPass_iff hPass).1 h.exact
  have hSafe₁ : ∀ x, pre x → TreeSafe (sem₁ p₁ x) := fun x hx => (h.exact.1 x hx).1
  have hSafe₂ : ∀ x, pre x → TreeSafe (sem₂ p₂ x) := fun x hx => (hExact₂.1 x hx).1
  refine ⟨hExact₂, hTerm, ?_, ?_⟩
  · exact returnsIf_iff_reachesOutcomeIf.2
      (ReachesOutcomeIf.verifierPass_forward (hPass.toVerifierPass Spec.top) trivial hSafe₂
        (returnsIf_iff_reachesOutcomeIf.1 h.returnsIf))
  · intro x hx hp tr v hr
    obtain ⟨tr', hr'⟩ :=
      exists_reachesRet_of_ubClosedObsPrefixes_le (hPass.down_refines trivial x)
        (hSafe₁ x hx) hr
    exact h.noReturnIfPanics x hx hp tr' v hr'

/-- An exact pass carries a total exact panic contract backward once the source terminates on `pre`. -/
theorem TotalExactPanicContract.exactPass_backward
    (hPass : ExactPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) id id
      p₁ p₂)
    (hTerm : TerminatesOn (sem₁ p₁) pre)
    (h : TotalExactPanicContract (sem₂ p₂) pre post panicCond) :
    TotalExactPanicContract (sem₁ p₁) pre post panicCond := by
  have hExact₁ := (exactPanicContract_exactPass_iff hPass).2 h.exact
  have hSafe₁ : ∀ x, pre x → TreeSafe (sem₁ p₁ x) := fun x hx => (hExact₁.1 x hx).1
  have hSafe₂ : ∀ x, pre x → TreeSafe (sem₂ p₂ x) := fun x hx => (h.exact.1 x hx).1
  refine ⟨hExact₁, hTerm, ?_, ?_⟩
  · exact returnsIf_iff_reachesOutcomeIf.2
      (ReachesOutcomeIf.compilerPass_backward (hPass.toCompilerPass Spec.top) trivial hSafe₁
        (returnsIf_iff_reachesOutcomeIf.1 h.returnsIf))
  · intro x hx hp tr v hr
    obtain ⟨tr', hr'⟩ :=
      exists_reachesRet_of_ubClosedObsPrefixes_le (hPass.up_refines trivial x)
        (hSafe₂ x hx) hr
    exact h.noReturnIfPanics x hx hp tr' v hr'

/--
An exact pass carries a total exact policy contract forward once the target
terminates on `pre`.
-/
theorem TotalExactPolicyPanicContract.exactPass_forward
    (hPass : ExactPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) id id
      p₁ p₂)
    (hTerm : TerminatesOn (sem₂ p₂) pre)
    (h : TotalExactPolicyPanicContract (sem₁ p₁) pre post panicCond policy) :
    TotalExactPolicyPanicContract (sem₂ p₂) pre post panicCond policy := by
  have hExact₂ := (exactPolicyPanicContract_exactPass_iff hPass).1 h.exact
  have hSafe₁ : ∀ x, pre x → TreeSafe (sem₁ p₁ x) := fun x hx => (h.exact.1 x hx).1
  have hSafe₂ : ∀ x, pre x → TreeSafe (sem₂ p₂ x) := fun x hx => (hExact₂.1 x hx).1
  refine ⟨hExact₂, hTerm, ?_, ?_⟩
  · exact returnsIf_iff_reachesOutcomeIf.2
      (ReachesOutcomeIf.verifierPass_forward (hPass.toVerifierPass Spec.top) trivial hSafe₂
        (returnsIf_iff_reachesOutcomeIf.1 h.returnsIf))
  · intro x hx tr out hr
    obtain ⟨tr', hr'⟩ :=
      exists_reachesRet_of_ubClosedObsPrefixes_le (hPass.down_refines trivial x)
        (hSafe₁ x hx) hr
    exact h.exclusive x hx tr' out hr'

/--
An exact pass carries a total exact policy contract backward once the source
terminates on `pre`.
-/
theorem TotalExactPolicyPanicContract.exactPass_backward
    (hPass : ExactPass (panicSemantics proj₁ sem₁) (panicSemantics proj₂ sem₂) id id
      p₁ p₂)
    (hTerm : TerminatesOn (sem₁ p₁) pre)
    (h : TotalExactPolicyPanicContract (sem₂ p₂) pre post panicCond policy) :
    TotalExactPolicyPanicContract (sem₁ p₁) pre post panicCond policy := by
  have hExact₁ := (exactPolicyPanicContract_exactPass_iff hPass).2 h.exact
  have hSafe₁ : ∀ x, pre x → TreeSafe (sem₁ p₁ x) := fun x hx => (hExact₁.1 x hx).1
  have hSafe₂ : ∀ x, pre x → TreeSafe (sem₂ p₂ x) := fun x hx => (h.exact.1 x hx).1
  refine ⟨hExact₁, hTerm, ?_, ?_⟩
  · exact returnsIf_iff_reachesOutcomeIf.2
      (ReachesOutcomeIf.compilerPass_backward (hPass.toCompilerPass Spec.top) trivial hSafe₁
        (returnsIf_iff_reachesOutcomeIf.1 h.returnsIf))
  · intro x hx tr out hr
    obtain ⟨tr', hr'⟩ :=
      exists_reachesRet_of_ubClosedObsPrefixes_le (hPass.up_refines trivial x)
        (hSafe₂ x hx) hr
    exact h.exclusive x hx tr' out hr'

end Transfer

/-! ### Triggers are neither downward-closed nor upward-closed -/

section NonClosure

variable {E : Effect.{u}} [FaultEffect E]

private theorem reaches_spin_inv {R : Type u} {t u : ITree E R} {tr : List (Event E)}
    (h : Reaches t tr u) (ht : t = ITree.spin) : tr = [] ∧ u = ITree.spin := by
  induction h with
  | refl => exact ⟨rfl, ht⟩
  | tau hTau _ ih =>
    rw [ht, observe_spin] at hTau
    injection hTau with hEq
    exact ih hEq.symm
  | vis hVis _ _ _ _ =>
    rw [ht, observe_spin] at hVis
    nomatch hVis

/-- The silently diverging tree has no completed execution. -/
theorem not_reachesRet_spin {R : Type u} (tr : List (Event E)) (r : R) :
    ¬ ReachesRet (ITree.spin : ITree E R) tr r := by
  rintro ⟨u, hr, hu⟩
  obtain ⟨_, hEq⟩ := reaches_spin_inv hr rfl
  rw [hEq, observe_spin] at hu
  nomatch hu

/--
Triggers are not downward-closed. The silently diverging tree refines the tree
that panics immediately (its only prefix is the empty running one), yet it never
panics: a refinement may drop the panicking execution.
-/
theorem panic_trigger_not_downward_closed (proj : EffectObs E Obs) :
    UBClosedObsPrefixes proj (ITree.spin : ITree E (Outcome Val)) ≤
        UBClosedObsPrefixes proj (ITree.ret (.panic : Outcome Val)) ∧
      (∃ tr, ReachesRet (ITree.ret (E := E) (.panic : Outcome Val)) tr .panic) ∧
      ¬ ∃ tr, ReachesRet (ITree.spin : ITree E (Outcome Val)) tr .panic := by
  refine ⟨?_, ⟨[], _, .refl _, ITree.observe_ret _⟩, fun ⟨tr, hr⟩ => not_reachesRet_spin tr _ hr⟩
  intro p hp
  have hSafe : TreeSafe (ITree.spin : ITree E (Outcome Val)) := by
    rintro tr u hr ⟨u', i, k, hTau, hObs, _⟩
    obtain ⟨_, hEq⟩ := reaches_spin_inv (reaches_trans hr (Reaches.of_tauStar hTau (.refl u'))) rfl
    rw [hEq, observe_spin] at hObs
    nomatch hObs
  have hp' : HasObsPrefix proj (ITree.spin : ITree E (Outcome Val)) p := by
    have hEq := ubClosedObsPrefixes_eq_of_treeSafe proj hSafe
    exact hEq ▸ hp
  refine Or.inl ?_
  cases ho : p.outcome with
  | running =>
    simp only [HasObsPrefix, ho] at hp' ⊢
    obtain ⟨tr, u, hr, hTrace⟩ := hp'
    obtain ⟨hNil, _⟩ := reaches_spin_inv hr rfl
    subst hNil
    exact ⟨[], _, .refl _, hTrace⟩
  | ret r =>
    simp only [HasObsPrefix, ho] at hp'
    obtain ⟨tr, hr, _⟩ := hp'
    exact False.elim (not_reachesRet_spin tr r hr)
  | fault =>
    simp only [HasObsPrefix, ho] at hp'
    obtain ⟨tr, u, hr, hf, _⟩ := hp'
    exact False.elim (hSafe tr u hr hf)

/--
Triggers are not upward-closed along UB-closed refinement. A tree that panics
immediately refines a tree that faults immediately (a fault admits every
behavior), yet the faulting tree never panics: reaching `.panic` in the
behaviors of an unsafe program says nothing about its executions.
-/
theorem panic_trigger_not_upward_closed (proj : EffectObs E Obs) (i : E.I)
    (k : E.O i → ITree E (Outcome Val)) (hFault : FaultEffect.isFault i) :
    UBClosedObsPrefixes proj (ITree.ret (.panic : Outcome Val)) ≤
        UBClosedObsPrefixes proj (ITree.vis i k) ∧
      (∃ tr, ReachesRet (ITree.ret (E := E) (.panic : Outcome Val)) tr .panic) ∧
      ¬ ∃ tr, ReachesRet (ITree.vis i k) tr .panic := by
  refine ⟨fun p _ => Or.inr ⟨[], List.nil_prefix, ?_⟩,
    ⟨[], _, .refl _, ITree.observe_ret _⟩, ?_⟩
  · exact ⟨[], ITree.vis i k, .refl _, ⟨_, i, k, .refl _, ITree.observe_vis i k, hFault⟩, rfl⟩
  · rintro ⟨tr, u, hr, hu⟩
    cases hr with
    | refl => rw [ITree.observe_vis] at hu; nomatch hu
    | tau hTau _ => rw [ITree.observe_vis] at hTau; nomatch hTau
    | vis hVis hnf _ _ =>
      rw [ITree.observe_vis] at hVis
      injection hVis with hi _
      subst hi
      exact hnf hFault

end NonClosure

end PassVariance

/-! ### Captured-MIR instance -/

/--
Trace-erased behavior semantics of captured MIR bodies on `(args, mem)` inputs
with default callee table `callees`.
-/
def mirPanicSemantics (callees : List CapturedMir := .nil) :
    Semantics CapturedMir (PanicBehavior PUnit MirReturn MirInput) :=
  panicSemantics (EffectObs.erase MirEffect PUnit) (fun body => mirStatefulTrees body callees)

/--
Trace-erased behavior semantics of handled (closed-effect) captured MIR bodies
linked against handler `hdl`.
-/
def mirHandledPanicSemantics (hdl : ExternalCallHandler)
    (callees : List CapturedMir := .nil) :
    Semantics CapturedMir (PanicBehavior PUnit MirReturn MirInput) :=
  panicSemantics (EffectObs.erase MirClosedEffect PUnit)
    (fun body => mirHandledTrees body hdl callees)

/-- A compiler pass between captured MIR bodies preserves `PanicsWithPolicyOnlyIf` forward. -/
theorem mir_panicsWithPolicyOnlyIf_compilerPass_forward {callees₁ callees₂ : List CapturedMir}
    {G₁ : Spec (PanicBehavior PUnit MirReturn MirInput)} {src tgt : CapturedMir}
    {pre : MirInput → Prop} {post : MirInput → MirReturn → Prop}
    {panicCond : MirInput → Prop} {policy : AbortPolicy MirInput}
    (hPass : CompilerPass (mirPanicSemantics callees₁) (mirPanicSemantics callees₂) G₁ id
      src tgt)
    (hGuard : G₁.holds (mirPanicSemantics callees₁ src))
    (h : PanicsWithPolicyOnlyIf (mirStatefulTrees src callees₁) pre post panicCond policy) :
    PanicsWithPolicyOnlyIf (mirStatefulTrees tgt callees₂) pre post panicCond policy :=
  PanicsWithPolicyOnlyIf.compilerPass_forward
    (sem₁ := fun body => mirStatefulTrees body callees₁)
    (sem₂ := fun body => mirStatefulTrees body callees₂) hPass hGuard h

/--
A compiler pass between captured MIR bodies (for example a MIR optimization
validated per program) preserves `PanicsOnlyIf` from the source body to the
target body.
-/
theorem mir_panicsOnlyIf_compilerPass_forward {callees₁ callees₂ : List CapturedMir}
    {G₁ : Spec (PanicBehavior PUnit MirReturn MirInput)} {src tgt : CapturedMir}
    {pre : MirInput → Prop} {post : MirInput → MirReturn → Prop}
    {panicCond : MirInput → Prop}
    (hPass : CompilerPass (mirPanicSemantics callees₁) (mirPanicSemantics callees₂) G₁ id
      src tgt)
    (hGuard : G₁.holds (mirPanicSemantics callees₁ src))
    (h : PanicsOnlyIf (mirStatefulTrees src callees₁) pre post panicCond) :
    PanicsOnlyIf (mirStatefulTrees tgt callees₂) pre post panicCond :=
  PanicsOnlyIf.compilerPass_forward (sem₁ := fun body => mirStatefulTrees body callees₁)
    (sem₂ := fun body => mirStatefulTrees body callees₂) hPass hGuard h

/-- A verifier pass between captured MIR bodies reflects `PanicsOnlyIf` backward. -/
theorem mir_panicsOnlyIf_verifierPass_backward {callees₁ callees₂ : List CapturedMir}
    {G₂ : Spec (PanicBehavior PUnit MirReturn MirInput)} {src tgt : CapturedMir}
    {pre : MirInput → Prop} {post : MirInput → MirReturn → Prop}
    {panicCond : MirInput → Prop}
    (hPass : VerifierPass (mirPanicSemantics callees₁) (mirPanicSemantics callees₂) G₂ id
      src tgt)
    (hGuard : G₂.holds (mirPanicSemantics callees₂ tgt))
    (h : PanicsOnlyIf (mirStatefulTrees tgt callees₂) pre post panicCond) :
    PanicsOnlyIf (mirStatefulTrees src callees₁) pre post panicCond :=
  PanicsOnlyIf.verifierPass_backward (sem₁ := fun body => mirStatefulTrees body callees₁)
    (sem₂ := fun body => mirStatefulTrees body callees₂) hPass hGuard h

/--
A compiler pass between captured MIR bodies reflects `PanicsIf` from the target
body to a fault-free source body.
-/
theorem mir_panicsIf_compilerPass_backward {callees₁ callees₂ : List CapturedMir}
    {G₁ : Spec (PanicBehavior PUnit MirReturn MirInput)} {src tgt : CapturedMir}
    {pre panicCond : MirInput → Prop}
    (hPass : CompilerPass (mirPanicSemantics callees₁) (mirPanicSemantics callees₂) G₁ id
      src tgt)
    (hGuard : G₁.holds (mirPanicSemantics callees₁ src))
    (hSafe : ∀ x, pre x → TreeSafe (mirStatefulTrees src callees₁ x))
    (h : PanicsIf (mirStatefulTrees tgt callees₂) pre panicCond) :
    PanicsIf (mirStatefulTrees src callees₁) pre panicCond :=
  PanicsIf.compilerPass_backward (sem₁ := fun body => mirStatefulTrees body callees₁)
    (sem₂ := fun body => mirStatefulTrees body callees₂) hPass hGuard hSafe h

/-- A verifier pass between captured MIR bodies preserves `PanicsIf` forward. -/
theorem mir_panicsIf_verifierPass_forward {callees₁ callees₂ : List CapturedMir}
    {G₂ : Spec (PanicBehavior PUnit MirReturn MirInput)} {src tgt : CapturedMir}
    {pre panicCond : MirInput → Prop}
    (hPass : VerifierPass (mirPanicSemantics callees₁) (mirPanicSemantics callees₂) G₂ id
      src tgt)
    (hGuard : G₂.holds (mirPanicSemantics callees₂ tgt))
    (hSafe : ∀ x, pre x → TreeSafe (mirStatefulTrees tgt callees₂ x))
    (h : PanicsIf (mirStatefulTrees src callees₁) pre panicCond) :
    PanicsIf (mirStatefulTrees tgt callees₂) pre panicCond :=
  PanicsIf.verifierPass_forward (sem₁ := fun body => mirStatefulTrees body callees₁)
    (sem₂ := fun body => mirStatefulTrees body callees₂) hPass hGuard hSafe h

/--
An exact pass between captured MIR bodies preserves `ExactPanicContract` in both
directions.
-/
theorem mir_exactPanicContract_exactPass_iff {callees₁ callees₂ : List CapturedMir}
    {src tgt : CapturedMir}
    {pre : MirInput → Prop} {post : MirInput → MirReturn → Prop}
    {panicCond : MirInput → Prop}
    (hPass : ExactPass (mirPanicSemantics callees₁) (mirPanicSemantics callees₂) id id
      src tgt) :
    ExactPanicContract (mirStatefulTrees src callees₁) pre post panicCond ↔
      ExactPanicContract (mirStatefulTrees tgt callees₂) pre post panicCond :=
  exactPanicContract_exactPass_iff (sem₁ := fun body => mirStatefulTrees body callees₁)
    (sem₂ := fun body => mirStatefulTrees body callees₂) hPass

/-- An exact pass between captured MIR bodies transfers `TotalExactPanicContract` forward given target termination. -/
theorem mir_totalExactPanicContract_exactPass_forward {callees₁ callees₂ : List CapturedMir}
    {src tgt : CapturedMir}
    {pre : MirInput → Prop} {post : MirInput → MirReturn → Prop}
    {panicCond : MirInput → Prop}
    (hPass : ExactPass (mirPanicSemantics callees₁) (mirPanicSemantics callees₂) id id
      src tgt)
    (hTerm : TerminatesOn (mirStatefulTrees tgt callees₂) pre)
    (h : TotalExactPanicContract (mirStatefulTrees src callees₁) pre post panicCond) :
    TotalExactPanicContract (mirStatefulTrees tgt callees₂) pre post panicCond :=
  TotalExactPanicContract.exactPass_forward
    (sem₁ := fun body => mirStatefulTrees body callees₁)
    (sem₂ := fun body => mirStatefulTrees body callees₂) hPass hTerm h

/-- An exact pass between captured MIR bodies transfers `TotalExactPanicContract` backward given source termination. -/
theorem mir_totalExactPanicContract_exactPass_backward {callees₁ callees₂ : List CapturedMir}
    {src tgt : CapturedMir}
    {pre : MirInput → Prop} {post : MirInput → MirReturn → Prop}
    {panicCond : MirInput → Prop}
    (hPass : ExactPass (mirPanicSemantics callees₁) (mirPanicSemantics callees₂) id id
      src tgt)
    (hTerm : TerminatesOn (mirStatefulTrees src callees₁) pre)
    (h : TotalExactPanicContract (mirStatefulTrees tgt callees₂) pre post panicCond) :
    TotalExactPanicContract (mirStatefulTrees src callees₁) pre post panicCond :=
  TotalExactPanicContract.exactPass_backward
    (sem₁ := fun body => mirStatefulTrees body callees₁)
    (sem₂ := fun body => mirStatefulTrees body callees₂) hPass hTerm h

end Anneal.PanicContracts
