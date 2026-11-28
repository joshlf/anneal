-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.Data.Int.Basic
import Init.Data.List.Basic
import Init.Data.Option.Basic
import Anneal.InitLemmas
import Anneal.Framework.StepWp
import Anneal.Hybrid
import Anneal.LinearArith
import Anneal.LinearArithIndexed
import Anneal.FarkasMirCert
import Anneal.CanonicalDiode
import Anneal.Backend
import Anneal.Mir.OverflowTrapRefinement

/-!
# Unified Certificate-Gate Bridges (`Anneal.HybridCertBridgesV2026`)

Unifies Anneal's four certificate-checked subsystems under `Anneal.Hybrid`
(`CertifiedGate`, `certGateCut_sound`, `withFallback`, `firstAccepted`, and
`foldStreamPrefix`) with zero `Classical.choice` and zero `._unsafe_rec`:

1. **Pillar 1 (`Anneal.LinearArithIndexed`):** wraps `checkNatCutGoalIdx` and
   `checkIntCutGoalIdx` as `natCutIdxGate` / `intCutIdxGate` with one-`rfl`
   `BoolCertCut` discharges, dual-backend (`indexed` + `list`) gates and
   `firstAccepted` / `withFallback` portfolios, oversized / forged witness
   rejections, and sabotage-resistant total `Bool` verdicts (`verdictGate` /
   `gateVerdict`) where uncertified `false` claims never short-circuit valid
   later certificates.
2. **Pillar 2 (`Anneal.FarkasMirCert`):** defines computable
   `farkasMirCertSize` (exact `CutStep` count across `.single`, `.pair`,
   `.triple`, `.edge`) and empty-edge-bomb-hardened `farkasMirCertWeight` /
   `farkasMirBoundedEdgeGate`, wraps `checkFarkasMirGoal` as `farkasMirGate`
   with `BoolCertCut` discharge, `firstAccepted` portfolios (made total by
   `gateVerdict`), and indexed-to-MIR arithmetic bridges from `natCutIdxGate`
   directly to `evalScalarBinOp` overflow/underflow freedom.
3. **Pillar 3 (`Anneal.CanonicalDiode`):** wraps any lawful `CanonicalDiode`
   with a sound equality check as `canonicalDiodeChunkGate` plugged into
   `Anneal.Hybrid.foldStreamPrefix`, proving strict canonical image on all
   emitted chunks, immediate halt on rejected / tampered / non-canonical
   chunks at any stream position, exact agreement with
   `CanonicalDiode.filterAll` on faithful accepted streams, and, for ANY
   producer, emitted chunks equal to `filterAll` of the consumed input prefix.
4. **Pillar 4 (`Anneal.Backend.CtxFact` <-> `OverflowTrapRefinement`):**
   maps `ExecOutcome Nat Unit` faithfully into `Option (MirOutcomeClass Value)`
   and `Option (MirExactOutcomeClass Value)` under `PanicStrategy.abort`
   without collapsing `.diverged` into `.ret`, `.trap`, or `.ub` (the bridge
   is injective and refinement-reflecting on `u64`-ranged outcomes); proves
   that `SemRefinesUnder` (both relational and full asymmetric) and
   `blockOptGate` preserve `MirOutcomeRefines` and `MirExactOutcomeRefines`;
   transports ANY accepted `blockOptGate` certificate, at every `u64`-ranged
   environment, to real `stepMirState` runs and Layer 1A `ITree.toPartial`
   refinement/equivalence (including genuinely asymmetric `.ub ⊑ .ret`
   transport on `dropAddNuw` and two-gate `farkasMirGate` / `natCutIdxGate` +
   `blockOptGate` capstones); and proves concrete negative
   counterexamples for undischarged guard elision (including that no
   certificate is ever accepted while the fact is unproven) and
   abort-vs-unwind strategy separation.
-/

namespace Anneal.HybridCertBridgesV2026

open Anneal.InitLemmas
open Anneal.Hybrid
open Anneal.LinearArith
open Anneal.AiPcc
open Anneal.FarkasMirCert
open Anneal.CanonicalDiode
open Anneal.Backend
open Anneal.Mir.OverflowTrapRefinement
open Trusted.Refinement
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

private theorem nat_ble_false_of_lt_local {a b : Nat} (h : a < b) :
    Nat.ble b a = false := by
  cases hb : Nat.ble b a with
  | false => rfl
  | true => exact False.elim (Nat.not_le_of_gt h (Nat.le_of_ble_eq_true hb))

private theorem nat_lt_of_ble_false_local {a b : Nat}
    (h : Nat.ble b a = false) : a < b :=
  Nat.lt_of_not_le (fun hLe => by
    rw [Nat.ble_eq_true_of_le hLe] at h
    nomatch h)

private theorem u64Mod_eq_modPow2 : u64Mod = modPow2 (uintWidth .u64) :=
  rfl

private theorem word64_eq_mod_u64 (n : Nat) :
    word64 n = n % modPow2 (uintWidth .u64) :=
  rfl

private theorem word64_idem (n : Nat) : word64 (word64 n) = word64 n :=
  Nat.mod_eq_of_lt (Nat.mod_lt n u64Mod_pos)

/-! ## Pillar 1: `Anneal.LinearArithIndexed` Gates & Portfolios -/

/-- `Anneal.LinearArithIndexed` tree-indexed natural-number cut certificates
as an `Anneal.Hybrid.CertifiedGate` (matching `Anneal.Hybrid.natCutGate`). -/
noncomputable def natCutIdxGate (maxSteps : Nat) :
    CertifiedGate NatCutGoal Unit (List CutStep) (fun _ => True)
      (fun goal _ => goal.denote) where
  maxWitness := fun _ => maxSteps
  wSize := List.length
  check := fun goal _ steps => checkNatCutGoalIdx goal steps
  sound := fun goal _ steps _ _ h => checkNatCutGoalIdx_sound goal steps h

/-- `Anneal.LinearArithIndexed` tree-indexed integer cut certificates as an
`Anneal.Hybrid.CertifiedGate` (matching `Anneal.Hybrid.intCutGate`). -/
noncomputable def intCutIdxGate (maxSteps : Nat) :
    CertifiedGate IntCutGoal Unit (List CutStep) (fun _ => True)
      (fun goal _ => goal.denote) where
  maxWitness := fun _ => maxSteps
  wSize := List.length
  check := fun goal _ steps => checkIntCutGoalIdx goal steps
  sound := fun goal _ steps _ _ h => checkIntCutGoalIdx_sound goal steps h

/-- One-`rfl` `BoolCertCut` discharge through `natCutIdxGate`. -/
theorem natCutIdxGate_cut_sound (maxSteps : Nat) (goal : NatCutGoal)
    (steps : List CutStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (natCutIdxGate maxSteps)) (goal, (), steps)) :
    goal.denote :=
  certGateCut_sound (natCutIdxGate maxSteps) True.intro hCut

/-- One-`rfl` `BoolCertCut` discharge through `intCutIdxGate`. -/
theorem intCutIdxGate_cut_sound (maxSteps : Nat) (goal : IntCutGoal)
    (steps : List CutStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (intCutIdxGate maxSteps)) (goal, (), steps)) :
    goal.denote :=
  certGateCut_sound (intCutIdxGate maxSteps) True.intro hCut

/-- Size-bound rejection for `natCutIdxGate` without consulting the checker. -/
theorem natCutIdxGate_rejects_oversized {E : Type} (maxSteps : Nat)
    (goal : NatCutGoal) (steps : List CutStep)
    (hOver : maxSteps < steps.length) :
    evalGate (E := E) (natCutIdxGate maxSteps) goal (.candidate () steps) =
      .error (.witnessOversized steps.length maxSteps) :=
  evalGate_rejects_oversized (natCutIdxGate maxSteps) goal () steps hOver

/-- Size-bound rejection for `intCutIdxGate` without consulting the checker. -/
theorem intCutIdxGate_rejects_oversized {E : Type} (maxSteps : Nat)
    (goal : IntCutGoal) (steps : List CutStep)
    (hOver : maxSteps < steps.length) :
    evalGate (E := E) (intCutIdxGate maxSteps) goal (.candidate () steps) =
      .error (.witnessOversized steps.length maxSteps) :=
  evalGate_rejects_oversized (intCutIdxGate maxSteps) goal () steps hOver

/-- Forged-certificate rejection for `natCutIdxGate`. -/
theorem natCutIdxGate_rejects_forged {E : Type} (maxSteps : Nat)
    (goal : NatCutGoal) (steps : List CutStep)
    (hFit : steps.length ≤ maxSteps)
    (hBad : checkNatCutGoalIdx goal steps = false) :
    evalGate (E := E) (natCutIdxGate maxSteps) goal (.candidate () steps) =
      .error .rejectedByChecker := by
  dsimp only [evalGate, natCutIdxGate]
  rw [Nat.ble_eq_true_of_le hFit, hBad]

/-- Forged-certificate rejection for `intCutIdxGate`. -/
theorem intCutIdxGate_rejects_forged {E : Type} (maxSteps : Nat)
    (goal : IntCutGoal) (steps : List CutStep)
    (hFit : steps.length ≤ maxSteps)
    (hBad : checkIntCutGoalIdx goal steps = false) :
    evalGate (E := E) (intCutIdxGate maxSteps) goal (.candidate () steps) =
      .error .rejectedByChecker := by
  dsimp only [evalGate, intCutIdxGate]
  rw [Nat.ble_eq_true_of_le hFit, hBad]

/-- Selector tagging whether a cut witness is replayed by the tree-indexed
checker (`LinearArithIndexed`) or the list-backed checker (`LinearArith`). -/
inductive CutCheckerKind where
  | indexed
  | list

/-- Dual-backend gate dispatching `.indexed` witnesses to `checkNatCutGoalIdx`
and `.list` witnesses to `checkNatCutGoal` under one `CertifiedGate`. -/
noncomputable def natCutDualGate (maxSteps : Nat) :
    CertifiedGate NatCutGoal Unit (CutCheckerKind × List CutStep)
      (fun _ => True) (fun goal _ => goal.denote) where
  maxWitness := fun _ => maxSteps
  wSize := fun w => w.2.length
  check := fun goal _ w =>
    match w.1 with
    | .indexed => checkNatCutGoalIdx goal w.2
    | .list => checkNatCutGoal goal w.2
  sound := by
    intro goal _ w _ _ hChk
    cases w with
    | mk k steps =>
      cases k with
      | indexed => exact checkNatCutGoalIdx_sound goal steps hChk
      | list => exact checkNatCutGoal_sound goal steps hChk

/-- Dual-backend gate dispatching `.indexed` witnesses to `checkIntCutGoalIdx`
and `.list` witnesses to `checkIntCutGoal` under one `CertifiedGate`. -/
noncomputable def intCutDualGate (maxSteps : Nat) :
    CertifiedGate IntCutGoal Unit (CutCheckerKind × List CutStep)
      (fun _ => True) (fun goal _ => goal.denote) where
  maxWitness := fun _ => maxSteps
  wSize := fun w => w.2.length
  check := fun goal _ w =>
    match w.1 with
    | .indexed => checkIntCutGoalIdx goal w.2
    | .list => checkIntCutGoal goal w.2
  sound := by
    intro goal _ w _ _ hChk
    cases w with
    | mk k steps =>
      cases k with
      | indexed => exact checkIntCutGoalIdx_sound goal steps hChk
      | list => exact checkIntCutGoal_sound goal steps hChk

/-- Lift an `Except` gate outcome one level so `withFallback` can chain a
secondary portfolio gate when the primary gate rejects. -/
def liftGateResult {E Y : Type} :
    Except (HybridErr E) Y → Except (HybridErr E) (Except (HybridErr E) Y)
  | .ok y => .ok (.ok y)
  | .error e => .error e

/-- Portfolio combining `natCutIdxGate` (primary `firstAccepted` pass) with
`natCutGate` (fallback `firstAccepted` pass via `withFallback`). -/
noncomputable def natCutPortfolio {E : Type} (maxSteps : Nat)
    (goal : NatCutGoal)
    (rsIdx rsList : List (RawOutcome E Unit (List CutStep))) :
    Except (HybridErr E) Unit :=
  withFallback goal
    (liftGateResult (firstAccepted (natCutIdxGate maxSteps) goal rsIdx))
    (fun g => firstAccepted (natCutGate maxSteps) g rsList)

theorem natCutPortfolio_sound {E : Type} (maxSteps : Nat) (goal : NatCutGoal)
    (rsIdx rsList : List (RawOutcome E Unit (List CutStep)))
    (hOk : natCutPortfolio maxSteps goal rsIdx rsList = .ok ()) :
    goal.denote := by
  have hSpec :
      (fun g (res : Except (HybridErr E) Unit) => res = .ok () → g.denote)
        goal (natCutPortfolio maxSteps goal rsIdx rsList) := by
    refine withFallback_sound_of
      (Spec := fun g (res : Except (HybridErr E) Unit) =>
        res = .ok () → g.denote)
      goal
      (liftGateResult (firstAccepted (natCutIdxGate maxSteps) goal rsIdx))
      (fun g => firstAccepted (natCutGate maxSteps) g rsList) ?_ ?_
    · intro res hLift hResOk
      cases hPrim : firstAccepted (natCutIdxGate maxSteps) goal rsIdx with
      | error e =>
        rw [hPrim] at hLift
        nomatch hLift
      | ok u =>
        rw [hPrim] at hLift
        injection hLift with hEq
        rw [← hEq] at hResOk
        injection hResOk with hU
        rw [hU] at hPrim
        exact firstAccepted_sound (natCutIdxGate maxSteps) goal rsIdx ()
          True.intro hPrim
    · intro hFbOk
      exact firstAccepted_sound (natCutGate maxSteps) goal rsList ()
        True.intro hFbOk
  exact hSpec hOk

/-- `natCutPortfolio` succeeds iff either the indexed portfolio or the
list-backed fallback portfolio accepts some candidate. -/
theorem natCutPortfolio_ok_iff_exists {E : Type} (maxSteps : Nat)
    (goal : NatCutGoal)
    (rsIdx rsList : List (RawOutcome E Unit (List CutStep))) :
    natCutPortfolio maxSteps goal rsIdx rsList = .ok () ↔
      (∃ r, r ∈ rsIdx ∧ evalGate (natCutIdxGate maxSteps) goal r = .ok ()) ∨
      (∃ r, r ∈ rsList ∧ evalGate (natCutGate maxSteps) goal r = .ok ()) := by
  dsimp only [natCutPortfolio]
  cases hPrim : firstAccepted (natCutIdxGate maxSteps) goal rsIdx with
  | ok u =>
    cases u
    dsimp only [liftGateResult, withFallback]
    constructor
    · intro _
      have ⟨r, hMem, y, hEv⟩ :=
        (firstAccepted_ok_iff_exists (natCutIdxGate maxSteps) goal rsIdx).1
          ⟨(), hPrim⟩
      cases y
      exact Or.inl ⟨r, hMem, hEv⟩
    · intro _; rfl
  | error e =>
    dsimp only [liftGateResult, withFallback]
    constructor
    · intro hFb
      have ⟨r, hMem, y, hEv⟩ :=
        (firstAccepted_ok_iff_exists (natCutGate maxSteps) goal rsList).1
          ⟨(), hFb⟩
      cases y
      exact Or.inr ⟨r, hMem, hEv⟩
    · intro hEx
      cases hEx with
      | inl hI =>
        have ⟨r, hMem, hEv⟩ := hI
        have ⟨u, hOk⟩ :=
          (firstAccepted_ok_iff_exists (natCutIdxGate maxSteps) goal rsIdx).2
            ⟨r, hMem, (), hEv⟩
        rw [hPrim] at hOk
        nomatch hOk
      | inr hL =>
        have ⟨r, hMem, hEv⟩ := hL
        have ⟨u, hOk⟩ :=
          (firstAccepted_ok_iff_exists (natCutGate maxSteps) goal rsList).2
            ⟨r, hMem, (), hEv⟩
        cases u
        exact hOk

/-- Portfolio combining `intCutIdxGate` (primary `firstAccepted` pass) with
`intCutGate` (fallback `firstAccepted` pass via `withFallback`). -/
noncomputable def intCutPortfolio {E : Type} (maxSteps : Nat)
    (goal : IntCutGoal)
    (rsIdx rsList : List (RawOutcome E Unit (List CutStep))) :
    Except (HybridErr E) Unit :=
  withFallback goal
    (liftGateResult (firstAccepted (intCutIdxGate maxSteps) goal rsIdx))
    (fun g => firstAccepted (intCutGate maxSteps) g rsList)

theorem intCutPortfolio_sound {E : Type} (maxSteps : Nat) (goal : IntCutGoal)
    (rsIdx rsList : List (RawOutcome E Unit (List CutStep)))
    (hOk : intCutPortfolio maxSteps goal rsIdx rsList = .ok ()) :
    goal.denote := by
  have hSpec :
      (fun g (res : Except (HybridErr E) Unit) => res = .ok () → g.denote)
        goal (intCutPortfolio maxSteps goal rsIdx rsList) := by
    refine withFallback_sound_of
      (Spec := fun g (res : Except (HybridErr E) Unit) =>
        res = .ok () → g.denote)
      goal
      (liftGateResult (firstAccepted (intCutIdxGate maxSteps) goal rsIdx))
      (fun g => firstAccepted (intCutGate maxSteps) g rsList) ?_ ?_
    · intro res hLift hResOk
      cases hPrim : firstAccepted (intCutIdxGate maxSteps) goal rsIdx with
      | error e =>
        rw [hPrim] at hLift
        nomatch hLift
      | ok u =>
        rw [hPrim] at hLift
        injection hLift with hEq
        rw [← hEq] at hResOk
        injection hResOk with hU
        rw [hU] at hPrim
        exact firstAccepted_sound (intCutIdxGate maxSteps) goal rsIdx ()
          True.intro hPrim
    · intro hFbOk
      exact firstAccepted_sound (intCutGate maxSteps) goal rsList ()
        True.intro hFbOk
  exact hSpec hOk

/-- `intCutPortfolio` succeeds iff either the indexed portfolio or the
list-backed fallback portfolio accepts some candidate. -/
theorem intCutPortfolio_ok_iff_exists {E : Type} (maxSteps : Nat)
    (goal : IntCutGoal)
    (rsIdx rsList : List (RawOutcome E Unit (List CutStep))) :
    intCutPortfolio maxSteps goal rsIdx rsList = .ok () ↔
      (∃ r, r ∈ rsIdx ∧ evalGate (intCutIdxGate maxSteps) goal r = .ok ()) ∨
      (∃ r, r ∈ rsList ∧ evalGate (intCutGate maxSteps) goal r = .ok ()) := by
  dsimp only [intCutPortfolio]
  cases hPrim : firstAccepted (intCutIdxGate maxSteps) goal rsIdx with
  | ok u =>
    cases u
    dsimp only [liftGateResult, withFallback]
    constructor
    · intro _
      have ⟨r, hMem, y, hEv⟩ :=
        (firstAccepted_ok_iff_exists (intCutIdxGate maxSteps) goal rsIdx).1
          ⟨(), hPrim⟩
      cases y
      exact Or.inl ⟨r, hMem, hEv⟩
    · intro _; rfl
  | error e =>
    dsimp only [liftGateResult, withFallback]
    constructor
    · intro hFb
      have ⟨r, hMem, y, hEv⟩ :=
        (firstAccepted_ok_iff_exists (intCutGate maxSteps) goal rsList).1
          ⟨(), hFb⟩
      cases y
      exact Or.inr ⟨r, hMem, hEv⟩
    · intro hEx
      cases hEx with
      | inl hI =>
        have ⟨r, hMem, hEv⟩ := hI
        have ⟨u, hOk⟩ :=
          (firstAccepted_ok_iff_exists (intCutIdxGate maxSteps) goal rsIdx).2
            ⟨r, hMem, (), hEv⟩
        rw [hPrim] at hOk
        nomatch hOk
      | inr hL =>
        have ⟨r, hMem, hEv⟩ := hL
        have ⟨u, hOk⟩ :=
          (firstAccepted_ok_iff_exists (intCutGate maxSteps) goal rsList).2
            ⟨r, hMem, (), hEv⟩
        cases u
        exact hOk

/-- One-`rfl` `BoolCertCut` discharge through `natCutDualGate`, whichever
checker the witness tag selects. -/
theorem natCutDualGate_cut_sound (maxSteps : Nat) (goal : NatCutGoal)
    (w : CutCheckerKind × List CutStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (natCutDualGate maxSteps)) (goal, (), w)) :
    goal.denote :=
  certGateCut_sound (natCutDualGate maxSteps) True.intro hCut

/-- One-`rfl` `BoolCertCut` discharge through `intCutDualGate`, whichever
checker the witness tag selects. -/
theorem intCutDualGate_cut_sound (maxSteps : Nat) (goal : IntCutGoal)
    (w : CutCheckerKind × List CutStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (intCutDualGate maxSteps)) (goal, (), w)) :
    goal.denote :=
  certGateCut_sound (intCutDualGate maxSteps) True.intro hCut

/-- The witness tag of `natCutDualGate` selects the checker and nothing else:
`.indexed` witnesses are judged exactly as by `natCutIdxGate` and `.list`
witnesses exactly as by `Anneal.Hybrid.natCutGate`. -/
theorem natCutDualGate_agrees {E : Type} (maxSteps : Nat) (goal : NatCutGoal)
    (steps : List CutStep) :
    evalGate (E := E) (natCutDualGate maxSteps) goal
        (.candidate () (.indexed, steps)) =
      evalGate (natCutIdxGate maxSteps) goal (.candidate () steps) ∧
    evalGate (E := E) (natCutDualGate maxSteps) goal
        (.candidate () (.list, steps)) =
      evalGate (natCutGate maxSteps) goal (.candidate () steps) :=
  ⟨rfl, rfl⟩

/-- The witness tag of `intCutDualGate` selects the checker and nothing else.
-/
theorem intCutDualGate_agrees {E : Type} (maxSteps : Nat) (goal : IntCutGoal)
    (steps : List CutStep) :
    evalGate (E := E) (intCutDualGate maxSteps) goal
        (.candidate () (.indexed, steps)) =
      evalGate (intCutIdxGate maxSteps) goal (.candidate () steps) ∧
    evalGate (E := E) (intCutDualGate maxSteps) goal
        (.candidate () (.list, steps)) =
      evalGate (intCutGate maxSteps) goal (.candidate () steps) :=
  ⟨rfl, rfl⟩

/-! ### Total verdicts (`withFallback` over a `Bool` verdict)

A gate whose output is `Unit` has no total `withFallback` form worth stating:
any fallback inhabiting its specification already proves the goal. Lifting
the output to a `Bool` verdict gives a fallback that is sound because it
claims nothing (`false`), so `withFallback` is total and its soundness is not
vacuous. -/

/-- Lift a `Unit`-output gate establishing `P x` to a `Bool`-verdict gate.
Only a `true` verdict carrying a witness the underlying checker accepts is
accepted; an uncertified `false` proposal is rejected so an untrusted producer
cannot short-circuit a `firstAccepted` portfolio and hide a valid later
producer. The conservative fallback `false` in `gateVerdict` is the sole source
of `false`. -/
def verdictGate {X W : Type} {P : X → Prop}
    (g : CertifiedGate X Unit W (fun _ => True) (fun x _ => P x)) :
    CertifiedGate X Bool W (fun _ => True) (fun x b => b = true → P x) where
  maxWitness := g.maxWitness
  wSize := g.wSize
  check := fun x b w =>
    match b with
    | true => g.check x () w
    | false => false
  sound := by
    intro x b w _ hCap hChk hTrue
    cases b with
    | false => nomatch hTrue
    | true => exact g.sound x () w True.intro hCap hChk

/-- A `true` verdict is accepted exactly when the underlying gate's complete
acceptance test passes: `verdictGate` adds no new way to claim `true`. -/
theorem verdictGate_true_ok_iff {X W E : Type} {P : X → Prop}
    (g : CertifiedGate X Unit W (fun _ => True) (fun x _ => P x)) (x : X)
    (w : W) :
    evalGate (E := E) (verdictGate g) x (.candidate true w) = .ok true ↔
      gateCheckBounded g (x, (), w) = true := by
  refine Iff.trans (evalGate_candidate_ok_iff (verdictGate g) x true w true) ?_
  dsimp only [verdictGate, gateCheckBounded]
  constructor
  · intro h
    rw [Nat.ble_eq_true_of_le h.2.1, h.2.2]
    rfl
  · intro h
    exact ⟨rfl, Nat.le_of_ble_eq_true (bool_and_left h), bool_and_right h⟩

/-- An uncertified `false` candidate is never accepted by `verdictGate`, so a
producer claiming `false` cannot sabotage a later valid producer in
`firstAccepted`. -/
theorem verdictGate_false_never_ok {X W E : Type} {P : X → Prop}
    (g : CertifiedGate X Unit W (fun _ => True) (fun x _ => P x)) (x : X)
    (w : W) (b : Bool) :
    evalGate (E := E) (verdictGate g) x (.candidate false w) ≠ .ok b := by
  intro hOk
  have hChk :=
    ((evalGate_candidate_ok_iff (verdictGate g) x false w b).1 hOk).2.2
  dsimp only [verdictGate] at hChk
  nomatch hChk

/-- Total verdict over a producer portfolio: `true` if any producer supplies a
gate-accepted `true` candidate, or the conservative fallback `false` when every
producer is rejected (`withFallback`). -/
def gateVerdict {X W E : Type} {P : X → Prop}
    (g : CertifiedGate X Unit W (fun _ => True) (fun x _ => P x)) (x : X)
    (rs : List (RawOutcome E Bool W)) : Bool :=
  withFallback x (firstAccepted (verdictGate g) x rs) (fun _ => false)

/-- `gateVerdict` never answers `true` without a gate-accepted witness
(`withFallback_firstAccepted_sound`). -/
theorem gateVerdict_sound {X W E : Type} {P : X → Prop}
    (g : CertifiedGate X Unit W (fun _ => True) (fun x _ => P x)) (x : X)
    (rs : List (RawOutcome E Bool W)) (hTrue : gateVerdict g x rs = true) :
    P x :=
  withFallback_firstAccepted_sound (verdictGate g) x rs (fun _ => false)
    True.intro (fun _ _ h => nomatch h) hTrue

/-- The output `firstAccepted` returns is the very output the gate accepted
for some producer in the list (`firstAccepted_ok_iff_exists` only relates the
existence of the two). -/
theorem firstAcceptedOpt_ok_mem {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X) :
    ∀ (rs : List (RawOutcome E Y W)) (y : Y),
      firstAcceptedOpt g x rs = some (.ok y) →
      ∃ r, r ∈ rs ∧ evalGate g x r = .ok y
  | [], _, h => by cases h
  | r :: rs, y, h => by
    rw [firstAcceptedOpt_cons] at h
    injection h with h
    revert h
    dsimp only [firstAcceptedStep]
    cases hEv : evalGate g x r with
    | ok y' =>
      intro h
      have h' : (Except.ok y' : Except (HybridErr E) Y) = .ok y := h
      injection h' with h'
      rw [← h']
      exact ⟨r, List.Mem.head _, hEv⟩
    | error _ =>
      cases hRest : firstAcceptedOpt g x rs with
      | none => intro h; cases h
      | some res =>
        intro h
        have h' : res = .ok y := h
        rw [h'] at hRest
        have ⟨r', hMem, hEv'⟩ := firstAcceptedOpt_ok_mem g x rs y hRest
        exact ⟨r', List.Mem.tail _ hMem, hEv'⟩

theorem firstAccepted_ok_mem {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X)
    (rs : List (RawOutcome E Y W)) (y : Y)
    (hOk : firstAccepted g x rs = .ok y) :
    ∃ r, r ∈ rs ∧ evalGate g x r = .ok y :=
  firstAcceptedOpt_ok_mem g x rs y ((firstAccepted_ok_iff_opt g x rs y).1 hOk)

/-- Every verdict `verdictGate` accepts, from any raw producer outcome, is
`true`. -/
theorem verdictGate_ok_eq_true {X W E : Type} {P : X → Prop}
    (g : CertifiedGate X Unit W (fun _ => True) (fun x _ => P x)) (x : X)
    (r : RawOutcome E Bool W) (b : Bool)
    (hOk : evalGate (verdictGate g) x r = .ok b) : b = true := by
  cases r with
  | trapped => cases hOk
  | prodErr _ => cases hOk
  | candidate bc wc =>
    cases bc with
    | false => exact False.elim (verdictGate_false_never_ok g x wc b hOk)
    | true =>
      exact ((evalGate_candidate_ok_iff (verdictGate g) x true wc b).1 hOk).1

/-- Exact characterization of `gateVerdict`: returns `true` iff SOME producer
in `rs` supplies a `.candidate true w` accepted by `gateCheckBounded g`,
regardless of any preceding `.candidate false _` or failing producers. -/
theorem gateVerdict_eq_true_iff_exists {X W E : Type} {P : X → Prop}
    (g : CertifiedGate X Unit W (fun _ => True) (fun x _ => P x)) (x : X)
    (rs : List (RawOutcome E Bool W)) :
    gateVerdict g x rs = true ↔
      ∃ r, r ∈ rs ∧ ∃ w,
        r = .candidate true w ∧ gateCheckBounded g (x, (), w) = true := by
  dsimp only [gateVerdict]
  constructor
  · intro hTrue
    cases hFirst : firstAccepted (verdictGate g) x rs with
    | error e =>
      rw [hFirst] at hTrue
      nomatch hTrue
    | ok b =>
      rw [hFirst] at hTrue
      have hB : b = true := hTrue
      rw [hB] at hFirst
      have ⟨r, hMem, hEv⟩ :=
        firstAccepted_ok_mem (verdictGate g) x rs true hFirst
      cases r with
      | trapped => cases hEv
      | prodErr _ => cases hEv
      | candidate bc wc =>
        cases bc with
        | false =>
          exact False.elim (verdictGate_false_never_ok g x wc true hEv)
        | true =>
          exact ⟨.candidate true wc, hMem, wc, rfl,
            (verdictGate_true_ok_iff g x wc).1 hEv⟩
  · intro ⟨r, hMem, w, hEq, hChk⟩
    have hEv : evalGate (verdictGate g) x r = .ok true := by
      rw [hEq]
      exact (verdictGate_true_ok_iff g x w).2 hChk
    have ⟨b, hOk⟩ :=
      (firstAccepted_ok_iff_exists (verdictGate g) x rs).2 ⟨r, hMem, true, hEv⟩
    have ⟨r', _, hEv'⟩ := firstAccepted_ok_mem (verdictGate g) x rs b hOk
    rw [hOk, verdictGate_ok_eq_true g x r' b hEv']
    rfl

/-- When the gate rejects every producer, `gateVerdict` is the fallback
`false`: forged or oversized `true` claims do not leak through. -/
theorem gateVerdict_eq_false_of_all_rejected {X W E : Type} {P : X → Prop}
    (g : CertifiedGate X Unit W (fun _ => True) (fun x _ => P x)) (x : X)
    (rs : List (RawOutcome E Bool W))
    (hAll : ∀ r, r ∈ rs → ∀ b, evalGate (verdictGate g) x r ≠ .ok b) :
    gateVerdict g x rs = false := by
  dsimp only [gateVerdict]
  cases hFirst : firstAccepted (verdictGate g) x rs with
  | error _ => rfl
  | ok b =>
    have ⟨r, hMem, b', hEv⟩ :=
      (firstAccepted_ok_iff_exists (verdictGate g) x rs).1 ⟨b, hFirst⟩
    exact False.elim (hAll r hMem b' hEv)

/-- Total `Bool` verdict over interleaved indexed and list-backed `NatCutGoal`
producers (`natCutDualGate`). -/
theorem natCutDualGate_verdict_sound {E : Type} (maxSteps : Nat)
    (goal : NatCutGoal)
    (rs : List (RawOutcome E Bool (CutCheckerKind × List CutStep)))
    (hTrue : gateVerdict (natCutDualGate maxSteps) goal rs = true) :
    goal.denote :=
  gateVerdict_sound (natCutDualGate maxSteps) goal rs hTrue

/-- Total `Bool` verdict over interleaved indexed and list-backed `IntCutGoal`
producers (`intCutDualGate`). -/
theorem intCutDualGate_verdict_sound {E : Type} (maxSteps : Nat)
    (goal : IntCutGoal)
    (rs : List (RawOutcome E Bool (CutCheckerKind × List CutStep)))
    (hTrue : gateVerdict (intCutDualGate maxSteps) goal rs = true) :
    goal.denote :=
  gateVerdict_sound (intCutDualGate maxSteps) goal rs hTrue

/-! ## Pillar 2: `Anneal.FarkasMirCert` Unified Gate & Indexed-to-MIR Bridge -/

/-- Computable total `CutStep` count across all four `FarkasMirCert` variants
(`List.foldr`, `0` `._unsafe_rec`). -/
def farkasMirCertSize : FarkasMirCert → Nat
  | .single steps => steps.length
  | .pair s1 s2 => s1.length + s2.length
  | .triple s1 s2 s3 => s1.length + s2.length + s3.length
  | .edge certs => List.foldr (fun cs acc => cs.length + acc) 0 certs

theorem farkasMirCertSize_single (steps : List CutStep) :
    farkasMirCertSize (.single steps) = steps.length :=
  rfl

theorem farkasMirCertSize_pair (s1 s2 : List CutStep) :
    farkasMirCertSize (.pair s1 s2) = s1.length + s2.length :=
  rfl

theorem farkasMirCertSize_triple (s1 s2 s3 : List CutStep) :
    farkasMirCertSize (.triple s1 s2 s3) = s1.length + s2.length + s3.length :=
  rfl

theorem farkasMirCertSize_edge_nil :
    farkasMirCertSize (.edge []) = 0 :=
  rfl

theorem farkasMirCertSize_edge_cons (cs : List CutStep)
    (rest : List (List CutStep)) :
    farkasMirCertSize (.edge (cs :: rest)) =
      cs.length + farkasMirCertSize (.edge rest) :=
  rfl

/-- Structural weight of a `FarkasMirCert` charging `1 + cs.length` per `.edge`
entry so an empty-list `.edge [[], [], ...]` bomb cannot slip past the size
bound with zero cost (`List.foldr`, `0` `._unsafe_rec`). -/
def farkasMirCertWeight : FarkasMirCert → Nat
  | .single steps => steps.length
  | .pair s1 s2 => s1.length + s2.length
  | .triple s1 s2 s3 => s1.length + s2.length + s3.length
  | .edge certs => List.foldr (fun cs acc => 1 + cs.length + acc) 0 certs

private theorem edge_size_le_weight :
    ∀ certs : List (List CutStep),
      List.foldr (fun cs acc => cs.length + acc) 0 certs ≤
        List.foldr (fun cs acc => 1 + cs.length + acc) 0 certs
  | [] => Nat.le_refl 0
  | cs :: rest =>
    Nat.add_le_add (Nat.le_add_left cs.length 1) (edge_size_le_weight rest)

theorem farkasMirCertSize_le_weight :
    ∀ c : FarkasMirCert, farkasMirCertSize c ≤ farkasMirCertWeight c
  | .single _ => Nat.le_refl _
  | .pair _ _ => Nat.le_refl _
  | .triple _ _ _ => Nat.le_refl _
  | .edge certs => edge_size_le_weight certs

/-- Edge-bomb-hardened `FarkasMirCert` gate using `farkasMirCertWeight` so
empty-list `.edge` payloads are rejected in `O(n)` before calling
`checkFarkasMirGoal`. -/
noncomputable def farkasMirBoundedEdgeGate (maxWeight : Nat) :
    CertifiedGate FarkasMirGoal Unit FarkasMirCert (fun _ => True)
      (fun goal _ => goal.denote) where
  maxWitness := fun _ => maxWeight
  wSize := farkasMirCertWeight
  check := fun goal _ cert => checkFarkasMirGoal goal cert
  sound := fun goal _ cert _ _ h => checkFarkasMirGoal_sound goal cert h

theorem farkasMirBoundedEdgeGate_cut_sound (maxWeight : Nat)
    (goal : FarkasMirGoal) (cert : FarkasMirCert)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (farkasMirBoundedEdgeGate maxWeight))
      (goal, (), cert)) :
    goal.denote :=
  certGateCut_sound (farkasMirBoundedEdgeGate maxWeight) True.intro hCut

/-- Empty-edge bomb witness: `.edge [[], [], [], [], []]` has
`farkasMirCertSize = 0` (exact `CutStep` count), whereas
`farkasMirBoundedEdgeGate 2` rejects it as `.witnessOversized 5 2`. -/
theorem neg_farkasMir_empty_edge_bomb_bounded (goal : FarkasMirGoal) :
    farkasMirCertSize (.edge [[], [], [], [], []]) = 0 ∧
    farkasMirCertWeight (.edge [[], [], [], [], []]) = 5 ∧
    evalGate (E := Unit) (farkasMirBoundedEdgeGate 2) goal
      (.candidate () (.edge [[], [], [], [], []])) =
      .error (.witnessOversized 5 2) :=
  ⟨rfl, rfl,
   evalGate_rejects_oversized (farkasMirBoundedEdgeGate 2) goal ()
     (.edge [[], [], [], [], []]) (Nat.le_of_ble_eq_true rfl)⟩

/-- Unified `Anneal.FarkasMirCert` checker wrapped as an
`Anneal.Hybrid.CertifiedGate` bounded by `maxSteps` total `CutStep`s. -/
noncomputable def farkasMirGate (maxSteps : Nat) :
    CertifiedGate FarkasMirGoal Unit FarkasMirCert (fun _ => True)
      (fun goal _ => goal.denote) where
  maxWitness := fun _ => maxSteps
  wSize := farkasMirCertSize
  check := fun goal _ cert => checkFarkasMirGoal goal cert
  sound := fun goal _ cert _ _ h => checkFarkasMirGoal_sound goal cert h

/-- One-`rfl` `BoolCertCut` discharge for any `FarkasMirGoal` via
`certGateCut_sound`. -/
theorem farkasMirGate_cut_sound (maxSteps : Nat) (goal : FarkasMirGoal)
    (cert : FarkasMirCert)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (farkasMirGate maxSteps)) (goal, (), cert)) :
    goal.denote :=
  certGateCut_sound (farkasMirGate maxSteps) True.intro hCut

/-- Size-bound rejection for `farkasMirGate` without invoking
`checkFarkasMirGoal`. -/
theorem farkasMirGate_rejects_oversized {E : Type} (maxSteps : Nat)
    (goal : FarkasMirGoal) (cert : FarkasMirCert)
    (hOver : maxSteps < farkasMirCertSize cert) :
    evalGate (E := E) (farkasMirGate maxSteps) goal (.candidate () cert) =
      .error (.witnessOversized (farkasMirCertSize cert) maxSteps) :=
  evalGate_rejects_oversized (farkasMirGate maxSteps) goal () cert hOver

/-- Forged or payload-mismatched certificate rejection for `farkasMirGate`. -/
theorem farkasMirGate_rejects_forged {E : Type} (maxSteps : Nat)
    (goal : FarkasMirGoal) (cert : FarkasMirCert)
    (hFit : farkasMirCertSize cert ≤ maxSteps)
    (hBad : checkFarkasMirGoal goal cert = false) :
    evalGate (E := E) (farkasMirGate maxSteps) goal (.candidate () cert) =
      .error .rejectedByChecker := by
  dsimp only [evalGate, farkasMirGate]
  rw [Nat.ble_eq_true_of_le hFit, hBad]

/-- The weight of an `.edge` certificate bounds its number of entries, so a
weight cap also caps how many (possibly empty) step lists reach the checker.
-/
theorem farkasMirCertWeight_edge_length_le :
    ∀ certs : List (List CutStep),
      certs.length ≤ farkasMirCertWeight (.edge certs)
  | [] => Nat.le_refl 0
  | cs :: rest => by
    have ih := farkasMirCertWeight_edge_length_le rest
    have h1 : rest.length + 1 ≤ 1 + farkasMirCertWeight (.edge rest) := by
      rw [Nat.add_comm 1]
      exact Nat.succ_le_succ ih
    exact Nat.le_trans h1
      (Nat.add_le_add_right (Nat.le_add_right 1 cs.length) _)

/-- General empty-edge bomb: for EVERY `n`, an `.edge` of `n` empty step
lists has exact size `0`, so no `farkasMirGate` cap keeps it from the checker,
while its weight is `n`. -/
theorem farkasMirCert_empty_edge_size_and_weight :
    ∀ n : Nat,
      farkasMirCertSize (.edge (List.replicate n [])) = 0 ∧
      farkasMirCertWeight (.edge (List.replicate n [])) = n
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
    have ih := farkasMirCert_empty_edge_size_and_weight n
    refine ⟨?_, ?_⟩
    · show 0 + farkasMirCertSize (.edge (List.replicate n [])) = 0
      rw [ih.1]
    · show 1 + 0 + farkasMirCertWeight (.edge (List.replicate n [])) = n + 1
      rw [ih.2, Nat.add_zero, Nat.add_comm]

/-- `farkasMirBoundedEdgeGate` rejects ANY `.edge` certificate with more
entries than the cap, whatever the entries are, before `checkFarkasMirGoal`
runs. -/
theorem farkasMirBoundedEdgeGate_rejects_long_edge {E : Type}
    (maxWeight : Nat) (goal : FarkasMirGoal) (certs : List (List CutStep))
    (hLong : maxWeight < certs.length) :
    evalGate (E := E) (farkasMirBoundedEdgeGate maxWeight) goal
      (.candidate () (.edge certs)) =
      .error
        (.witnessOversized (farkasMirCertWeight (.edge certs)) maxWeight) :=
  evalGate_rejects_oversized (farkasMirBoundedEdgeGate maxWeight) goal ()
    (.edge certs)
    (Nat.lt_of_lt_of_le hLong (farkasMirCertWeight_edge_length_le certs))

/-- `farkasMirBoundedEdgeGate` is the stricter gate: whatever it accepts,
`farkasMirGate` accepts under the same cap, so hardening the bound never
admits a certificate the exact-size gate would refuse. -/
theorem farkasMirBoundedEdgeGate_accept_imp_farkasMirGate (maxSteps : Nat)
    (goal : FarkasMirGoal) (cert : FarkasMirCert)
    (hOk : gateCheckBounded (farkasMirBoundedEdgeGate maxSteps)
      (goal, (), cert) = true) :
    gateCheckBounded (farkasMirGate maxSteps) (goal, (), cert) = true := by
  dsimp only [gateCheckBounded, farkasMirBoundedEdgeGate, farkasMirGate]
    at hOk ⊢
  have hW := Nat.le_of_ble_eq_true (bool_and_left hOk)
  rw [Nat.ble_eq_true_of_le
    (Nat.le_trans (farkasMirCertSize_le_weight cert) hW), bool_and_right hOk]
  rfl

/-- Strictness lifted to `evalGate`: any producer outcome accepted by
`farkasMirBoundedEdgeGate` is accepted by `farkasMirGate` under the same cap.
-/
theorem farkasMirBoundedEdgeGate_eval_ok_imp_farkasMirGate {E : Type}
    (maxSteps : Nat) (goal : FarkasMirGoal)
    (r : RawOutcome E Unit FarkasMirCert)
    (hOk : evalGate (farkasMirBoundedEdgeGate maxSteps) goal r = .ok ()) :
    evalGate (farkasMirGate maxSteps) goal r = .ok () := by
  cases r with
  | trapped => cases hOk
  | prodErr _ => cases hOk
  | candidate y cert =>
    cases y
    have h := (evalGate_candidate_ok_iff (farkasMirBoundedEdgeGate maxSteps)
      goal () cert ()).1 hOk
    have hChk : gateCheckBounded (farkasMirBoundedEdgeGate maxSteps)
        (goal, (), cert) = true := by
      dsimp only [gateCheckBounded]
      rw [Nat.ble_eq_true_of_le h.2.1, h.2.2]
      rfl
    have hMir := farkasMirBoundedEdgeGate_accept_imp_farkasMirGate maxSteps
      goal cert hChk
    exact (evalGate_candidate_ok_iff (farkasMirGate maxSteps) goal () cert ()).2
      ⟨rfl, Nat.le_of_ble_eq_true (bool_and_left hMir), bool_and_right hMir⟩

/-- Strictness lifted to `gateVerdict`: whenever the bounded-edge portfolio
returns `true`, the exact-size `farkasMirGate` portfolio also returns `true`.
-/
theorem farkasMirBoundedEdgeGate_verdict_imp_farkasMirGate {E : Type}
    (maxSteps : Nat) (goal : FarkasMirGoal)
    (rs : List (RawOutcome E Bool FarkasMirCert))
    (hTrue : gateVerdict (farkasMirBoundedEdgeGate maxSteps) goal rs = true) :
    gateVerdict (farkasMirGate maxSteps) goal rs = true := by
  have ⟨r, hMem, w, hEq, hChk⟩ :=
    (gateVerdict_eq_true_iff_exists (farkasMirBoundedEdgeGate maxSteps) goal
      rs).1 hTrue
  exact (gateVerdict_eq_true_iff_exists (farkasMirGate maxSteps) goal rs).2
    ⟨r, hMem, w, hEq,
      farkasMirBoundedEdgeGate_accept_imp_farkasMirGate maxSteps goal w hChk⟩

/-- `firstAccepted` portfolio selection over candidate `FarkasMirCert`
producers. -/
noncomputable def farkasMirPortfolio {E : Type} (maxSteps : Nat)
    (goal : FarkasMirGoal)
    (rs : List (RawOutcome E Unit FarkasMirCert)) :
    Except (HybridErr E) Unit :=
  firstAccepted (farkasMirGate maxSteps) goal rs

theorem farkasMirPortfolio_sound {E : Type} (maxSteps : Nat)
    (goal : FarkasMirGoal) (rs : List (RawOutcome E Unit FarkasMirCert))
    (hOk : farkasMirPortfolio maxSteps goal rs = .ok ()) :
    goal.denote :=
  firstAccepted_sound (farkasMirGate maxSteps) goal rs () True.intro hOk

theorem farkasMirPortfolio_ok_iff_exists {E : Type} (maxSteps : Nat)
    (goal : FarkasMirGoal) (rs : List (RawOutcome E Unit FarkasMirCert)) :
    (∃ u, farkasMirPortfolio maxSteps goal rs = .ok u) ↔
      (∃ r, r ∈ rs ∧ ∃ u, evalGate (farkasMirGate maxSteps) goal r = .ok u) :=
  firstAccepted_ok_iff_exists (farkasMirGate maxSteps) goal rs

/-- Indexed strict-inequality soundness: `lhs + 1 ≤ rhs` proved via
`checkNatCutGoalIdx` implies `lhs < rhs`. -/
theorem checkNatCutGoalIdx_lt_sound (hyps : List NatCutIneq)
    (lhs rhs : NatLinExpr) (steps : List CutStep)
    (hChk : checkNatCutGoalIdx ⟨hyps, ⟨.add lhs (.cst 1), rhs⟩⟩ steps = true)
    (env : List Nat) :
    HypsImp (NatCutIneq.holds env) hyps (lhs.eval env < rhs.eval env) :=
  hypsImp_concl_mono
    (fun hLe => nat_lt_of_add_one_le hLe)
    (checkNatCutGoalIdx_sound ⟨hyps, ⟨.add lhs (.cst 1), rhs⟩⟩ steps hChk env)

/-- Indexed-to-MIR addition overflow-freedom bridge: `checkNatCutGoalIdx`
discharges the exact `evalScalarBinOp` `.addUnchecked` and `.addWithOverflow`
obligations of `FarkasMirGoal.uintAddNoOverflow`. -/
theorem natCutIdx_discharges_uint_add_no_overflow
    (u : UintTy) (hyps : List NatCutIneq) (lhsExpr rhsExpr : NatLinExpr)
    (steps : List CutStep)
    (hChk : checkNatCutGoalIdx
      ⟨hyps, ⟨.add (.add lhsExpr rhsExpr) (.cst 1),
        .cst (modPow2 (uintWidth u))⟩⟩ steps = true)
    (env : List Nat) (locals : List LocalSlot) (mem : Memory) :
    HypsImp (NatCutIneq.holds env) hyps
      (lhsExpr.eval env + rhsExpr.eval env < modPow2 (uintWidth u) ∧
       lhsExpr.eval env + rhsExpr.eval env < scalarModulus (uintBytes u) ∧
       evalScalarBinOp .addUnchecked
         ⟨lhsExpr.eval env, uintBytes u⟩ ⟨rhsExpr.eval env, uintBytes u⟩
         locals mem false =
         .ok (.scalar ⟨lhsExpr.eval env + rhsExpr.eval env, uintBytes u⟩)
           locals mem ∧
       evalScalarBinOp .addWithOverflow
         ⟨lhsExpr.eval env, uintBytes u⟩ ⟨rhsExpr.eval env, uintBytes u⟩
         locals mem false =
         .ok (.aggregate 0
           [.scalar ⟨lhsExpr.eval env + rhsExpr.eval env, uintBytes u⟩,
            .scalar ⟨0, 1⟩]) locals mem) :=
  hypsImp_concl_mono (fun hLt => by
    dsimp only [NatLinExpr.eval] at hLt
    have hMod :
        lhsExpr.eval env + rhsExpr.eval env < scalarModulus (uintBytes u) := by
      rw [scalarModulus_uintBytes]
      exact hLt
    have hUnchk :=
      evalScalarBinOp_uint_addUnchecked (u := u) locals mem hLt
    rw [wrapVal_of_lt hLt] at hUnchk
    have hWithOv := evalScalarBinOp_uint_addWithOverflow (u := u)
      (a := lhsExpr.eval env) (b := rhsExpr.eval env) locals mem
    rw [wrapVal_of_lt hLt, nat_ble_false_of_lt_local hLt] at hWithOv
    exact ⟨hLt, hMod, hUnchk, hWithOv⟩)
    (checkNatCutGoalIdx_lt_sound hyps (.add lhsExpr rhsExpr)
      (.cst (modPow2 (uintWidth u))) steps hChk env)

/-- One-`rfl` `natCutIdxGate` `BoolCertCut` discharges the full
`FarkasMirGoal.uintAddNoOverflow` denotation directly. -/
theorem natCutIdxGate_discharges_uint_add_no_overflow
    (maxSteps : Nat) (u : UintTy) (hyps : List NatCutIneq)
    (lhsExpr rhsExpr : NatLinExpr) (steps : List CutStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (natCutIdxGate maxSteps))
      (⟨hyps, ⟨.add (.add lhsExpr rhsExpr) (.cst 1),
        .cst (modPow2 (uintWidth u))⟩⟩, (), steps)) :
    (FarkasMirGoal.uintAddNoOverflow u hyps lhsExpr rhsExpr).denote := by
  have hUnseal := Anneal.Framework.StepWp.BoolCertCut.unseal hCut
  have hChk :
      checkNatCutGoalIdx
        ⟨hyps, ⟨.add (.add lhsExpr rhsExpr) (.cst 1),
          .cst (modPow2 (uintWidth u))⟩⟩ steps = true :=
    bool_and_right hUnseal
  intro env locals mem
  exact natCutIdx_discharges_uint_add_no_overflow u hyps lhsExpr rhsExpr steps
    hChk env locals mem

/-- Indexed-to-MIR subtraction underflow-freedom bridge: `checkNatCutGoalIdx`
discharges the exact `evalScalarBinOp` `.subUnchecked` and `.subWithOverflow`
obligations of `FarkasMirGoal.uintSubNoUnderflow`. -/
theorem natCutIdx_discharges_uint_sub_no_underflow
    (u : UintTy) (hyps : List NatCutIneq) (lhsExpr rhsExpr : NatLinExpr)
    (steps : List CutStep)
    (hChk : checkNatCutGoalIdx ⟨hyps, ⟨rhsExpr, lhsExpr⟩⟩ steps = true)
    (env : List Nat) (locals : List LocalSlot) (mem : Memory)
    (hLhsLt : lhsExpr.eval env < modPow2 (uintWidth u)) :
    HypsImp (NatCutIneq.holds env) hyps
      (rhsExpr.eval env ≤ lhsExpr.eval env ∧
       lhsExpr.eval env - rhsExpr.eval env < modPow2 (uintWidth u) ∧
       evalScalarBinOp .subUnchecked
         ⟨lhsExpr.eval env, uintBytes u⟩ ⟨rhsExpr.eval env, uintBytes u⟩
         locals mem false =
         .ok (.scalar ⟨lhsExpr.eval env - rhsExpr.eval env, uintBytes u⟩)
           locals mem ∧
       evalScalarBinOp .subWithOverflow
         ⟨lhsExpr.eval env, uintBytes u⟩ ⟨rhsExpr.eval env, uintBytes u⟩
         locals mem false =
         .ok (.aggregate 0
           [.scalar ⟨lhsExpr.eval env - rhsExpr.eval env, uintBytes u⟩,
            .scalar ⟨0, 1⟩]) locals mem) :=
  hypsImp_concl_mono (fun hLe => by
    have hDiffLt :
        lhsExpr.eval env - rhsExpr.eval env < modPow2 (uintWidth u) :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) hLhsLt
    have hRhsLt : rhsExpr.eval env < modPow2 (uintWidth u) :=
      Nat.lt_of_le_of_lt hLe hLhsLt
    have hUnchk :=
      evalScalarBinOp_uint_subUnchecked (u := u) locals mem hLhsLt hLe
    rw [← wrapVal_sub_of_le hLe hLhsLt, wrapVal_of_lt hDiffLt] at hUnchk
    have hWithOv :=
      evalScalarBinOp_uint_subWithOverflow (u := u) locals mem hLhsLt hRhsLt
    rw [← wrapVal_sub_of_le hLe hLhsLt, wrapVal_of_lt hDiffLt,
      Nat.ble_eq_true_of_le hLe] at hWithOv
    exact ⟨hLe, hDiffLt, hUnchk, hWithOv⟩)
    (checkNatCutGoalIdx_sound ⟨hyps, ⟨rhsExpr, lhsExpr⟩⟩ steps hChk env)

/-- One-`rfl` `natCutIdxGate` `BoolCertCut` discharges
`FarkasMirGoal.uintSubNoUnderflow`. -/
theorem natCutIdxGate_discharges_uint_sub_no_underflow
    (maxSteps : Nat) (u : UintTy) (hyps : List NatCutIneq)
    (lhsExpr rhsExpr : NatLinExpr) (steps : List CutStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (natCutIdxGate maxSteps))
      (⟨hyps, ⟨rhsExpr, lhsExpr⟩⟩, (), steps)) :
    (FarkasMirGoal.uintSubNoUnderflow u hyps lhsExpr rhsExpr).denote := by
  have hUnseal := Anneal.Framework.StepWp.BoolCertCut.unseal hCut
  have hChk : checkNatCutGoalIdx ⟨hyps, ⟨rhsExpr, lhsExpr⟩⟩ steps = true :=
    bool_and_right hUnseal
  intro env locals mem hLhsLt
  exact natCutIdx_discharges_uint_sub_no_underflow u hyps lhsExpr rhsExpr steps
    hChk env locals mem hLhsLt

/-- Two `natCutIdxGate` `BoolCertCut`s discharge the fully certified
`FarkasMirGoal.uintSubNoUnderflowCertified` denotation directly. -/
theorem natCutIdxGate_discharges_uint_sub_no_underflow_certified
    (maxSteps : Nat) (u : UintTy) (hyps : List NatCutIneq)
    (lhsExpr rhsExpr : NatLinExpr) (stepsLe stepsRange : List CutStep)
    (hCutLe : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (natCutIdxGate maxSteps))
      (⟨hyps, ⟨rhsExpr, lhsExpr⟩⟩, (), stepsLe))
    (hCutRange : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (natCutIdxGate maxSteps))
      (⟨hyps, ⟨.add lhsExpr (.cst 1), .cst (modPow2 (uintWidth u))⟩⟩,
        (), stepsRange)) :
    (FarkasMirGoal.uintSubNoUnderflowCertified u hyps lhsExpr
      rhsExpr).denote := by
  have hUnsealLe := Anneal.Framework.StepWp.BoolCertCut.unseal hCutLe
  have hChkLe : checkNatCutGoalIdx ⟨hyps, ⟨rhsExpr, lhsExpr⟩⟩ stepsLe = true :=
    bool_and_right hUnsealLe
  have hUnsealRange := Anneal.Framework.StepWp.BoolCertCut.unseal hCutRange
  have hChkRange :
      checkNatCutGoalIdx
        ⟨hyps, ⟨.add lhsExpr (.cst 1), .cst (modPow2 (uintWidth u))⟩⟩
        stepsRange = true :=
    bool_and_right hUnsealRange
  intro env locals mem
  exact hypsImp_of_all_imp hyps (fun hAll =>
    have hLt : lhsExpr.eval env < modPow2 (uintWidth u) :=
      hypsImp_apply_all hyps
        (checkNatCutGoalIdx_lt_sound hyps lhsExpr (.cst (modPow2 (uintWidth u)))
          stepsRange hChkRange env) hAll
    ⟨hLt, hypsImp_apply_all hyps
      (natCutIdx_discharges_uint_sub_no_underflow u hyps lhsExpr rhsExpr stepsLe
        hChkLe env locals mem hLt) hAll⟩)

/-! ## Pillar 3: `Anneal.CanonicalDiode` Streaming Gate & `foldStreamPrefix` -/

/-- Strict canonical-image predicate for a `CanonicalDiode`: wire value `c` is
the exact canonical encoding of an AST `a` that decodes back to `a`. -/
def IsCanonicalImage {A B : Type} (d : CanonicalDiode A B) (c : B) : Prop :=
  ∃ a : A, d.canon.enc a = c ∧ d.canon.dec c = some a

/-- Structural `List Bool` equality via `List.foldr` (`0` `._unsafe_rec`). -/
def boolListBeq (xs ys : List Bool) : Bool :=
  List.foldr
    (fun b ih zs =>
      match zs with
      | [] => false
      | c :: zs' => FarkasMirCert.boolBeq b c && ih zs')
    (fun zs =>
      match zs with
      | [] => true
      | _ :: _ => false)
    xs ys

theorem boolListBeq_eq :
    ∀ (xs ys : List Bool), boolListBeq xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | b :: xs', c :: ys', h => by
    change (FarkasMirCert.boolBeq b c && boolListBeq xs' ys') = true at h
    have hb : b = c := bool_eq_of_beq (bool_and_left h)
    have htl := boolListBeq_eq xs' ys' (bool_and_right h)
    rw [hb, htl]

theorem boolListBeq_refl : ∀ xs : List Bool, boolListBeq xs xs = true
  | [] => rfl
  | b :: xs' => by
    change (FarkasMirCert.boolBeq b b && boolListBeq xs' xs') = true
    have hb : FarkasMirCert.boolBeq b b = true := by cases b <;> rfl
    rw [hb]
    exact boolListBeq_refl xs'

/-- Wrap any lawful `CanonicalDiode` with a sound equality predicate `beqB` as
an `Anneal.Hybrid.CertifiedGate` ready for `Anneal.Hybrid.foldStreamPrefix`. -/
def canonicalDiodeChunkGate {A B : Type} (d : CanonicalDiode A B)
    (hLawful : Lawful d.canon) (beqB : B → B → Bool)
    (hBeq : ∀ x y, beqB x y = true → x = y) :
    CertifiedGate (Unit × B) (Unit × B) Unit
      (fun _ => True) (fun _ sc => True ∧ IsCanonicalImage d sc.2) where
  maxWitness := fun _ => 0
  wSize := fun _ => 0
  check := fun su sc _ =>
    match d.filter su.2 with
    | none => false
    | some canonOut => beqB sc.2 canonOut
  sound := by
    intro su sc _ _ _ hChk
    cases hFilt : d.filter su.2 with
    | none =>
      rw [hFilt] at hChk
      nomatch hChk
    | some canonOut =>
      rw [hFilt] at hChk
      have hEq : sc.2 = canonOut := hBeq sc.2 canonOut hChk
      rw [hEq]
      have ⟨a, _, hDec, hEnc⟩ := CanonicalDiode.filter_sound hLawful.1 hFilt
      exact ⟨True.intro, ⟨a, hEnc, hDec⟩⟩

/-- One-`rfl` `BoolCertCut` discharge through `canonicalDiodeChunkGate`. -/
theorem canonicalDiodeChunkGate_cut_sound {A B : Type} (d : CanonicalDiode A B)
    (hLawful : Lawful d.canon) (beqB : B → B → Bool)
    (hBeq : ∀ x y, beqB x y = true → x = y) (u c : B)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (canonicalDiodeChunkGate d hLawful beqB hBeq))
      (((), u), ((), c), ())) :
    IsCanonicalImage d c :=
  (certGateCut_sound (canonicalDiodeChunkGate d hLawful beqB hBeq)
    True.intro hCut).2

/-- Acceptance of candidate `((), c)` on raw input `u` implies
`d.filter u = some c` and full upstream-to-canonical round-trip soundness. -/
theorem canonicalDiodeChunkGate_accept_sound {A B E : Type}
    (d : CanonicalDiode A B) (hLawful : Lawful d.canon) (beqB : B → B → Bool)
    (hBeq : ∀ x y, beqB x y = true → x = y) (u c : B)
    (hOk : evalGate (E := E) (canonicalDiodeChunkGate d hLawful beqB hBeq)
      ((), u) (.candidate ((), c) ()) = .ok ((), c)) :
    d.filter u = some c ∧
      ∃ a : A, d.parse u = some a ∧ d.canon.enc a = c ∧
        d.canon.dec c = some a := by
  have hChk :
      (canonicalDiodeChunkGate d hLawful beqB hBeq).check ((), u) ((), c) () =
        true :=
    ((evalGate_candidate_ok_iff _ _ _ _ _).1 hOk).2.2
  dsimp only [canonicalDiodeChunkGate] at hChk
  cases hFilt : d.filter u with
  | none =>
    rw [hFilt] at hChk
    nomatch hChk
  | some canonOut =>
    rw [hFilt] at hChk
    have hEq : c = canonOut := hBeq c canonOut hChk
    rw [hEq]
    have ⟨a, hP, hDec, hEnc⟩ := CanonicalDiode.filter_sound hLawful.1 hFilt
    exact ⟨rfl, ⟨a, hP, hEnc, hDec⟩⟩

/-- Pillar 3 (i): every chunk emitted by `foldStreamPrefix` through
`canonicalDiodeChunkGate` lies in the strict canonical image of `d.canon`. -/
theorem canonicalDiode_stream_all_emitted_canonical {A B E : Type}
    (d : CanonicalDiode A B) (hLawful : Lawful d.canon) (beqB : B → B → Bool)
    (hBeq : ∀ x y, beqB x y = true → x = y)
    (pChunk : Unit → B → RawOutcome E (Unit × B) Unit) (us : List B) :
    ∀ c, c ∈ (foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := IsCanonicalImage d)
      (canonicalDiodeChunkGate d hLawful beqB hBeq) pChunk () us).1 →
      IsCanonicalImage d c :=
  foldStreamPrefix_all_emitted_valid
    (AccInv := fun _ => True) (ValidChunk := IsCanonicalImage d)
    (canonicalDiodeChunkGate d hLawful beqB hBeq) pChunk us () True.intro

/-- Pillar 3 (ii-a): whenever `d.filter u = none`, `canonicalDiodeChunkGate`
rejects any proposed candidate `((), c)` and `foldStreamPrefix` halts
immediately with `([], some .rejectedByChecker)`, never emitting `c`. -/
theorem canonicalDiode_stream_halts_on_filter_none {A B E : Type}
    (d : CanonicalDiode A B) (hLawful : Lawful d.canon) (beqB : B → B → Bool)
    (hBeq : ∀ x y, beqB x y = true → x = y)
    (pChunk : Unit → B → RawOutcome E (Unit × B) Unit)
    (u c : B) (us : List B)
    (hNone : d.filter u = none)
    (hCand : pChunk () u = .candidate ((), c) ()) :
    foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := IsCanonicalImage d)
      (canonicalDiodeChunkGate d hLawful beqB hBeq) pChunk () (u :: us) =
      ([], some .rejectedByChecker) := by
  have hRej :
      evalGate (canonicalDiodeChunkGate d hLawful beqB hBeq) ((), u)
        (pChunk () u) = .error .rejectedByChecker := by
    rw [hCand]
    dsimp only [evalGate, canonicalDiodeChunkGate]
    rw [hNone]
  exact foldStreamPrefix_halts
    (AccInv := fun _ => True) (ValidChunk := IsCanonicalImage d)
    (canonicalDiodeChunkGate d hLawful beqB hBeq) pChunk () u us
    .rejectedByChecker hRej

/-- Pillar 3 (ii-b): whenever a producer proposes a tampered or mismatched
chunk (`d.filter u ≠ some c`), `canonicalDiodeChunkGate` rejects it and
`foldStreamPrefix` halts immediately without emitting `c`. -/
theorem canonicalDiode_stream_halts_on_tampered {A B E : Type}
    (d : CanonicalDiode A B) (hLawful : Lawful d.canon) (beqB : B → B → Bool)
    (hBeq : ∀ x y, beqB x y = true → x = y)
    (pChunk : Unit → B → RawOutcome E (Unit × B) Unit)
    (u c : B) (us : List B)
    (hMismatch : d.filter u ≠ some c)
    (hCand : pChunk () u = .candidate ((), c) ()) :
    foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := IsCanonicalImage d)
      (canonicalDiodeChunkGate d hLawful beqB hBeq) pChunk () (u :: us) =
      ([], some .rejectedByChecker) := by
  have hRej :
      evalGate (canonicalDiodeChunkGate d hLawful beqB hBeq) ((), u)
        (pChunk () u) = .error .rejectedByChecker := by
    rw [hCand]
    dsimp only [evalGate, canonicalDiodeChunkGate]
    cases hFilt : d.filter u with
    | none => rfl
    | some canonOut =>
      dsimp only
      cases hEqB : beqB c canonOut with
      | false => rfl
      | true =>
        have hEq : c = canonOut := hBeq c canonOut hEqB
        rw [hEq] at hMismatch
        exact False.elim (hMismatch hFilt)
  exact foldStreamPrefix_halts
    (AccInv := fun _ => True) (ValidChunk := IsCanonicalImage d)
    (canonicalDiodeChunkGate d hLawful beqB hBeq) pChunk () u us
    .rejectedByChecker hRej

/-- Pillar 3 (ii-c): any non-canonical chunk (`¬ IsCanonicalImage d c`) fails
`d.filter u ≠ some c` for every input `u`, so `foldStreamPrefix` halts
immediately and never emits it. -/
theorem canonicalDiode_stream_halts_on_nonCanonical {A B E : Type}
    (d : CanonicalDiode A B) (hLawful : Lawful d.canon) (beqB : B → B → Bool)
    (hBeq : ∀ x y, beqB x y = true → x = y)
    (pChunk : Unit → B → RawOutcome E (Unit × B) Unit)
    (u c : B) (us : List B)
    (hNotCanon : ¬ IsCanonicalImage d c)
    (hCand : pChunk () u = .candidate ((), c) ()) :
    foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := IsCanonicalImage d)
      (canonicalDiodeChunkGate d hLawful beqB hBeq) pChunk () (u :: us) =
      ([], some .rejectedByChecker) := by
  refine canonicalDiode_stream_halts_on_tampered d hLawful beqB hBeq pChunk
    u c us ?_ hCand
  intro hFilt
  have ⟨a, _, hDec, hEnc⟩ := CanonicalDiode.filter_sound hLawful.1 hFilt
  exact hNotCanon ⟨a, hEnc, hDec⟩

/-- Faithful streaming producer backed directly by `d.filter`: emits
`.candidate ((), out) ()` when accepted and `.prodErr eReject` when rejected. -/
def faithfulDiodeProducer {A B E : Type} (d : CanonicalDiode A B)
    (eReject : E) :
    Unit → B → RawOutcome E (Unit × B) Unit :=
  fun _ u =>
    match d.filter u with
    | none => .prodErr eReject
    | some out => .candidate ((), out) ()

/-- Pillar 3 (iii): for a faithful producer, whenever
`d.filterAll us = some outs`, `foldStreamPrefix` emits the exact canonical
list `outs` with `err = none`. -/
theorem canonicalDiode_stream_faithful_eq_filterAll {A B E : Type}
    (d : CanonicalDiode A B) (hLawful : Lawful d.canon) (beqB : B → B → Bool)
    (hBeq : ∀ x y, beqB x y = true → x = y)
    (hBeqRefl : ∀ x, beqB x x = true) (eReject : E) :
    ∀ (us outs : List B),
      d.filterAll us = some outs →
      foldStreamPrefix (AccInv := fun _ => True)
        (ValidChunk := IsCanonicalImage d)
        (canonicalDiodeChunkGate d hLawful beqB hBeq)
        (faithfulDiodeProducer d eReject) () us = (outs, none)
  | [], outs, hAll => by
    dsimp only [CanonicalDiode.filterAll, List.foldr] at hAll
    injection hAll with hEq
    rw [← hEq]
    rfl
  | u :: us, outs, hAll => by
    rw [CanonicalDiode.filterAll_cons] at hAll
    cases hFilt : d.filter u with
    | none =>
      rw [hFilt] at hAll
      nomatch hAll
    | some out =>
      rw [hFilt, Option.bind_some] at hAll
      cases hRest : d.filterAll us with
      | none =>
        rw [hRest] at hAll
        nomatch hAll
      | some outs' =>
        rw [hRest, Option.map_some] at hAll
        injection hAll with hOuts
        rw [foldStreamPrefix_cons]
        have hEv :
            evalGate (canonicalDiodeChunkGate d hLawful beqB hBeq) ((), u)
              (faithfulDiodeProducer d eReject () u) = .ok ((), out) := by
          dsimp only [faithfulDiodeProducer]
          rw [hFilt]
          dsimp only [evalGate, canonicalDiodeChunkGate]
          rw [hFilt]
          dsimp only
          rw [hBeqRefl out]
        rw [hEv]
        dsimp only
        have ih := canonicalDiode_stream_faithful_eq_filterAll d hLawful beqB
          hBeq hBeqRefl eReject us outs' hRest
        rw [ih, ← hOuts]

/-- When `d.filterAll us = none`, the faithful producer halts at the first
rejected chunk with `some (.producerFailed eReject)`, and every chunk emitted
before the halt is strictly canonical. -/
theorem canonicalDiode_stream_faithful_reject_halts {A B E : Type}
    (d : CanonicalDiode A B) (hLawful : Lawful d.canon) (beqB : B → B → Bool)
    (hBeq : ∀ x y, beqB x y = true → x = y)
    (hBeqRefl : ∀ x, beqB x x = true) (eReject : E) :
    ∀ (us : List B),
      d.filterAll us = none →
      let res :=
        foldStreamPrefix (AccInv := fun _ => True)
          (ValidChunk := IsCanonicalImage d)
          (canonicalDiodeChunkGate d hLawful beqB hBeq)
          (faithfulDiodeProducer d eReject) () us
      res.2 = some (.producerFailed eReject) ∧
        ∀ c, c ∈ res.1 → IsCanonicalImage d c
  | [], hNone => by
    dsimp only [CanonicalDiode.filterAll, List.foldr] at hNone
    nomatch hNone
  | u :: us, hNone => by
    have hAllValid :=
      canonicalDiode_stream_all_emitted_canonical d hLawful beqB hBeq
        (faithfulDiodeProducer d eReject) (u :: us)
    refine ⟨?_, hAllValid⟩
    rw [CanonicalDiode.filterAll_cons] at hNone
    cases hFilt : d.filter u with
    | none =>
      have hRej :
          evalGate (canonicalDiodeChunkGate d hLawful beqB hBeq) ((), u)
            (faithfulDiodeProducer d eReject () u) =
            .error (.producerFailed eReject) := by
        dsimp only [faithfulDiodeProducer]
        rw [hFilt]
        rfl
      rw [foldStreamPrefix_halts
        (AccInv := fun _ => True) (ValidChunk := IsCanonicalImage d)
        (canonicalDiodeChunkGate d hLawful beqB hBeq)
        (faithfulDiodeProducer d eReject) () u us
        (.producerFailed eReject) hRej]
    | some out =>
      rw [hFilt, Option.bind_some] at hNone
      cases hRest : d.filterAll us with
      | some outs' =>
        rw [hRest, Option.map_some] at hNone
        nomatch hNone
      | none =>
        rw [foldStreamPrefix_cons]
        have hEv :
            evalGate (canonicalDiodeChunkGate d hLawful beqB hBeq) ((), u)
              (faithfulDiodeProducer d eReject () u) = .ok ((), out) := by
          dsimp only [faithfulDiodeProducer]
          rw [hFilt]
          dsimp only [evalGate, canonicalDiodeChunkGate]
          rw [hFilt]
          dsimp only
          rw [hBeqRefl out]
        rw [hEv]
        dsimp only
        exact (canonicalDiode_stream_faithful_reject_halts d hLawful beqB hBeq
          hBeqRefl eReject us hRest).1

/-- Any accepted gate result, from any raw producer outcome, is the filter
image of its input chunk: `evalGate` never accepts a substituted chunk. -/
theorem canonicalDiodeChunkGate_ok_filter {A B E : Type}
    (d : CanonicalDiode A B) (hLawful : Lawful d.canon) (beqB : B → B → Bool)
    (hBeq : ∀ x y, beqB x y = true → x = y) (u : B)
    (raw : RawOutcome E (Unit × B) Unit) (sc : Unit × B)
    (hOk : evalGate (canonicalDiodeChunkGate d hLawful beqB hBeq) ((), u) raw =
      .ok sc) :
    d.filter u = some sc.2 := by
  cases raw with
  | trapped => cases hOk
  | prodErr _ => cases hOk
  | candidate y w =>
    have h := (evalGate_candidate_ok_iff _ _ _ _ _).1 hOk
    rw [h.1]
    have hChk := h.2.2
    dsimp only [canonicalDiodeChunkGate] at hChk
    cases hFilt : d.filter u with
    | none =>
      rw [hFilt] at hChk
      nomatch hChk
    | some canonOut =>
      rw [hFilt] at hChk
      rw [hBeq y.2 canonOut hChk]

/-- A candidate chunk that is not the filter image of its input is rejected
by the checker, whatever it is. -/
theorem canonicalDiodeChunkGate_rejects_mismatch {A B E : Type}
    (d : CanonicalDiode A B) (hLawful : Lawful d.canon) (beqB : B → B → Bool)
    (hBeq : ∀ x y, beqB x y = true → x = y) (u c : B)
    (hMismatch : d.filter u ≠ some c) :
    evalGate (E := E) (canonicalDiodeChunkGate d hLawful beqB hBeq) ((), u)
      (.candidate ((), c) ()) = .error .rejectedByChecker := by
  dsimp only [evalGate, canonicalDiodeChunkGate]
  cases hFilt : d.filter u with
  | none => rfl
  | some canonOut =>
    dsimp only
    cases hEqB : beqB c canonOut with
    | false => rfl
    | true =>
      have hEq : c = canonOut := hBeq c canonOut hEqB
      rw [hEq] at hMismatch
      exact False.elim (hMismatch hFilt)

/-- Mid-stream halt at any position: once the prefix `pre` has been emitted
as `outs` with no error, a chunk the gate rejects ends the stream with exactly
`outs` emitted, whatever follows it. -/
theorem canonicalDiode_stream_halts_midstream {A B E : Type}
    (d : CanonicalDiode A B) (hLawful : Lawful d.canon) (beqB : B → B → Bool)
    (hBeq : ∀ x y, beqB x y = true → x = y)
    (pChunk : Unit → B → RawOutcome E (Unit × B) Unit)
    (u : B) (us : List B) (err : HybridErr E)
    (hRej : evalGate (canonicalDiodeChunkGate d hLawful beqB hBeq) ((), u)
      (pChunk () u) = .error err) :
    ∀ (pre outs : List B),
      foldStreamPrefix (AccInv := fun _ => True)
        (ValidChunk := IsCanonicalImage d)
        (canonicalDiodeChunkGate d hLawful beqB hBeq) pChunk () pre =
        (outs, none) →
      foldStreamPrefix (AccInv := fun _ => True)
        (ValidChunk := IsCanonicalImage d)
        (canonicalDiodeChunkGate d hLawful beqB hBeq) pChunk ()
        (pre ++ u :: us) = (outs, some err)
  | [], outs, hPre => by
    injection hPre with hOuts _
    rw [← hOuts]
    exact foldStreamPrefix_halts
      (AccInv := fun _ => True) (ValidChunk := IsCanonicalImage d)
      (canonicalDiodeChunkGate d hLawful beqB hBeq) pChunk () u us err hRej
  | p :: pre, outs, hPre => by
    rw [List.cons_append, foldStreamPrefix_cons]
    rw [foldStreamPrefix_cons] at hPre
    cases hEv : evalGate (canonicalDiodeChunkGate d hLawful beqB hBeq)
        ((), p) (pChunk () p) with
    | error e =>
      rw [hEv] at hPre
      injection hPre with _ hErr
      nomatch hErr
    | ok sc =>
      rw [hEv] at hPre
      cases sc with
      | mk s c =>
        cases s
        have hOuts := congrArg Prod.fst hPre
        have hNone := congrArg Prod.snd hPre
        dsimp only at hOuts hNone ⊢
        have ih := canonicalDiode_stream_halts_midstream d hLawful beqB hBeq
          pChunk u us err hRej pre _ (congrArg (Prod.mk _) hNone)
        rw [ih]
        exact congrArg (fun o => (o, some err)) hOuts

/-- Pillar 3 (ii) at any stream position: a tampered, substituted, or
non-canonical candidate `c` for chunk `u` after an accepted prefix ends the
stream with exactly the prefix emitted. The candidate `c` is never appended.
-/
theorem canonicalDiode_stream_halts_on_tampered_midstream {A B E : Type}
    (d : CanonicalDiode A B) (hLawful : Lawful d.canon) (beqB : B → B → Bool)
    (hBeq : ∀ x y, beqB x y = true → x = y)
    (pChunk : Unit → B → RawOutcome E (Unit × B) Unit)
    (pre outs : List B) (u c : B) (us : List B)
    (hPre : foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := IsCanonicalImage d)
      (canonicalDiodeChunkGate d hLawful beqB hBeq) pChunk () pre =
      (outs, none))
    (hMismatch : d.filter u ≠ some c)
    (hCand : pChunk () u = .candidate ((), c) ()) :
    foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := IsCanonicalImage d)
      (canonicalDiodeChunkGate d hLawful beqB hBeq) pChunk ()
      (pre ++ u :: us) = (outs, some .rejectedByChecker) := by
  refine canonicalDiode_stream_halts_midstream d hLawful beqB hBeq pChunk u us
    .rejectedByChecker ?_ pre outs hPre
  rw [hCand]
  exact canonicalDiodeChunkGate_rejects_mismatch d hLawful beqB hBeq u c
    hMismatch

/-- Exact characterization of the stream for ANY producer, faithful or
adversarial: the input splits as `consumed ++ rest`, the emitted chunks are
exactly `d.filterAll consumed`, a stream without error consumed everything,
and a stream with error `e` stopped at the first chunk of `rest`, the one the
gate rejected with `e`. No producer can reorder, replay, or substitute
chunks, even canonical ones. -/
theorem canonicalDiode_stream_prefix_eq_filterAll {A B E : Type}
    (d : CanonicalDiode A B) (hLawful : Lawful d.canon) (beqB : B → B → Bool)
    (hBeq : ∀ x y, beqB x y = true → x = y)
    (pChunk : Unit → B → RawOutcome E (Unit × B) Unit) :
    ∀ us : List B, ∃ consumed rest : List B,
      us = consumed ++ rest ∧
      d.filterAll consumed =
        some (foldStreamPrefix (AccInv := fun _ => True)
          (ValidChunk := IsCanonicalImage d)
          (canonicalDiodeChunkGate d hLawful beqB hBeq) pChunk () us).1 ∧
      ((foldStreamPrefix (AccInv := fun _ => True)
          (ValidChunk := IsCanonicalImage d)
          (canonicalDiodeChunkGate d hLawful beqB hBeq) pChunk () us).2 =
          none → rest = []) ∧
      (∀ e, (foldStreamPrefix (AccInv := fun _ => True)
          (ValidChunk := IsCanonicalImage d)
          (canonicalDiodeChunkGate d hLawful beqB hBeq) pChunk () us).2 =
          some e →
        ∃ u rest', rest = u :: rest' ∧
          evalGate (canonicalDiodeChunkGate d hLawful beqB hBeq) ((), u)
            (pChunk () u) = .error e)
  | [] => by
    refine ⟨[], [], rfl, rfl, fun _ => rfl, fun e h => ?_⟩
    have h' : (none : Option (HybridErr E)) = some e := h
    nomatch h'
  | u :: us => by
    have ih := canonicalDiode_stream_prefix_eq_filterAll d hLawful beqB hBeq
      pChunk us
    rw [foldStreamPrefix_cons]
    cases hEv : evalGate (canonicalDiodeChunkGate d hLawful beqB hBeq)
        ((), u) (pChunk () u) with
    | error err =>
      dsimp only
      refine ⟨[], u :: us, rfl, rfl, (fun h => nomatch h), fun e h => ?_⟩
      injection h with h
      rw [← h]
      exact ⟨u, us, rfl, hEv⟩
    | ok sc =>
      have hFilt := canonicalDiodeChunkGate_ok_filter d hLawful beqB hBeq u
        (pChunk () u) sc hEv
      cases sc with
      | mk s c =>
        cases s
        dsimp only at hFilt ⊢
        have ⟨consumed, rest, hSplit, hAll, hNone, hSome⟩ := ih
        refine ⟨u :: consumed, rest, ?_, ?_, hNone, hSome⟩
        · rw [hSplit]
          rfl
        · rw [CanonicalDiode.filterAll_cons, hFilt, Option.bind_some, hAll,
            Option.map_some]

/-! ## Pillar 4: `Anneal.Backend.CtxFact` <-> `OverflowTrapRefinement` -/

/-! ### 4.1 Faithful Outcome Mapping (`.diverged` Kept Explicitly Distinct) -/

/-- Canonical 64-bit unsigned scalar value corresponding to a `Nat` word. -/
def execOutcomeToMirValue (v : Nat) : Value :=
  .scalar ⟨v % modPow2 (uintWidth .u64), uintBytes .u64⟩

/-- Faithful partial bridge from `Anneal.Backend.ExecOutcome Nat Unit` to
`MirOutcomeClass Value`:
- `.returned v ()` maps to `some (.ret (.scalar ⟨v % 2^64, 8⟩))`;
- `.aborted ()` maps to `some .trap`;
- `.faultUB` maps to `some .ub`;
- `.diverged` maps to `none`, keeping divergence explicitly distinct from
  `.ret`, `.trap`, `.ub`, and `.unsupported`. -/
def execOutcomeToMirClass? :
    ExecOutcome Nat Unit → Option (MirOutcomeClass Value)
  | .returned v () => some (.ret (execOutcomeToMirValue v))
  | .aborted () => some .trap
  | .faultUB => some .ub
  | .diverged => none

/-- Strategy-exact bridge under `PanicStrategy.abort` (`-C panic=abort`):
`.aborted ()` maps strictly to `some (.trap .abort)` (never `.trap .panic`),
and `.diverged` stays `none`. -/
def execOutcomeToMirExactClass? :
    ExecOutcome Nat Unit → Option (MirExactOutcomeClass Value)
  | .returned v () => some (.ret (execOutcomeToMirValue v))
  | .aborted () => some (.trap .abort)
  | .faultUB => some .ub
  | .diverged => none

/-- Divergence-preserving lift of `MirOutcomeRefines` over `Option`:
- `some .ub` (spec UB) refines any outcome (including `none` / `.diverged`);
- `none` (`.diverged`) refines ONLY `none` (never `.ret`, `.trap`, or `.ub`);
- `some s` with `s ≠ .ub` refines `some i` iff `MirOutcomeRefines s i` and
  never refines `none`. -/
def MirOptOutcomeRefines (spec impl : Option (MirOutcomeClass Value)) : Prop :=
  match spec, impl with
  | some s, some i => MirOutcomeRefines s i
  | some .ub, none => True
  | none, none => True
  | _, _ => False

/-- Divergence-preserving lift of `MirExactOutcomeRefines` over `Option`. -/
def MirOptExactOutcomeRefines
    (spec impl : Option (MirExactOutcomeClass Value)) : Prop :=
  match spec, impl with
  | some s, some i => MirExactOutcomeRefines s i
  | some .ub, none => True
  | none, none => True
  | _, _ => False

theorem execOutcomeToMirExactClass?_forget (out : ExecOutcome Nat Unit) :
    (execOutcomeToMirExactClass? out).map MirExactOutcomeClass.forgetTrapKind =
      execOutcomeToMirClass? out := by
  cases out with
  | returned v m => cases m; rfl
  | aborted m => cases m; rfl
  | faultUB => rfl
  | diverged => rfl

/-- `.diverged` never collapses into `.ret`, `.trap`, `.ub`, or `.unsupported`,
and never refines (nor is refined by) `.ret` or `.trap`. -/
theorem execOutcomeToMirClass?_diverged_distinct (v : Nat) :
    execOutcomeToMirClass? .diverged = none ∧
    execOutcomeToMirClass? .diverged ≠ execOutcomeToMirClass? (.returned v ()) ∧
    execOutcomeToMirClass? .diverged ≠ execOutcomeToMirClass? (.aborted ()) ∧
    execOutcomeToMirClass? .diverged ≠ execOutcomeToMirClass? .faultUB ∧
    execOutcomeToMirClass? .diverged ≠ some .unsupported ∧
    MirOptOutcomeRefines (execOutcomeToMirClass? .diverged)
      (execOutcomeToMirClass? .diverged) ∧
    ¬ MirOptOutcomeRefines (execOutcomeToMirClass? .diverged)
        (execOutcomeToMirClass? (.returned v ())) ∧
    ¬ MirOptOutcomeRefines (execOutcomeToMirClass? .diverged)
        (execOutcomeToMirClass? (.aborted ())) ∧
    ¬ MirOptOutcomeRefines (execOutcomeToMirClass? .diverged)
        (execOutcomeToMirClass? .faultUB) ∧
    ¬ MirOptOutcomeRefines (execOutcomeToMirClass? (.returned v ()))
        (execOutcomeToMirClass? .diverged) ∧
    ¬ MirOptOutcomeRefines (execOutcomeToMirClass? (.aborted ()))
        (execOutcomeToMirClass? .diverged) :=
  ⟨rfl, (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h),
   (fun h => nomatch h), True.intro, (fun h => h), (fun h => h), (fun h => h),
   (fun h => h), (fun h => h)⟩

theorem execOutcomeToMirExactClass?_diverged_distinct (v : Nat) :
    execOutcomeToMirExactClass? .diverged = none ∧
    execOutcomeToMirExactClass? .diverged ≠
      execOutcomeToMirExactClass? (.returned v ()) ∧
    execOutcomeToMirExactClass? .diverged ≠
      execOutcomeToMirExactClass? (.aborted ()) ∧
    execOutcomeToMirExactClass? .diverged ≠
      execOutcomeToMirExactClass? .faultUB ∧
    execOutcomeToMirExactClass? .diverged ≠ some .unsupported ∧
    MirOptExactOutcomeRefines (execOutcomeToMirExactClass? .diverged)
      (execOutcomeToMirExactClass? .diverged) ∧
    ¬ MirOptExactOutcomeRefines (execOutcomeToMirExactClass? .diverged)
        (execOutcomeToMirExactClass? (.returned v ())) ∧
    ¬ MirOptExactOutcomeRefines (execOutcomeToMirExactClass? .diverged)
        (execOutcomeToMirExactClass? (.aborted ())) ∧
    ¬ MirOptExactOutcomeRefines (execOutcomeToMirExactClass? .diverged)
        (execOutcomeToMirExactClass? .faultUB) :=
  ⟨rfl, (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h),
   (fun h => nomatch h), True.intro, (fun h => h), (fun h => h), (fun h => h)⟩

theorem execOutcomeToMirClass?_inj_on_u64 {v₁ v₂ : Nat}
    (h₁ : v₁ < modPow2 (uintWidth .u64))
    (h₂ : v₂ < modPow2 (uintWidth .u64))
    (hEq : execOutcomeToMirClass? (.returned v₁ ()) =
      execOutcomeToMirClass? (.returned v₂ ())) :
    v₁ = v₂ := by
  dsimp only [execOutcomeToMirClass?, execOutcomeToMirValue] at hEq
  injection hEq with hRet
  injection hRet with hVal
  injection hVal with hSc
  injection hSc with hBits _
  rw [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at hBits
  exact hBits

/-! ### 4.2 `SemRefinesUnder` & `blockOptGate` MIR Refinement Preservation -/

/-- General preservation: for any `SemRefinesUnder EntryPre semSrc semTgt`, if
`semSrc` is deterministic at `q` with `EntryPre q`, then `MirOptOutcomeRefines`
and `MirOptExactOutcomeRefines` hold for every `(outSrc, outTgt)` pair (covering
UB, trap, return, and divergence without collapsing `.diverged`). -/
theorem semRefinesUnder_preserves_mirOptRefines {Q : Type}
    {EntryPre : Q → Prop}
    {semSrc semTgt : Q → ExecOutcome Nat Unit → Prop}
    (hRef : SemRefinesUnder EntryPre semSrc semTgt)
    {q : Q} (hPre : EntryPre q)
    (hDet : ∀ o₁ o₂, semSrc q o₁ → semSrc q o₂ → o₁ = o₂)
    {outSrc outTgt : ExecOutcome Nat Unit}
    (hSrc : semSrc q outSrc) (hTgt : semTgt q outTgt) :
    MirOptOutcomeRefines (execOutcomeToMirClass? outSrc)
      (execOutcomeToMirClass? outTgt) ∧
    MirOptExactOutcomeRefines (execOutcomeToMirExactClass? outSrc)
      (execOutcomeToMirExactClass? outTgt) := by
  cases outSrc with
  | faultUB =>
    cases outTgt with
    | returned v m => cases m; exact ⟨True.intro, True.intro⟩
    | aborted m => cases m; exact ⟨True.intro, True.intro⟩
    | faultUB => exact ⟨True.intro, True.intro⟩
    | diverged => exact ⟨True.intro, True.intro⟩
  | returned v m =>
    cases m
    have hNoUb : ¬ semSrc q .faultUB := fun hUb => by
      have hEq := hDet (.returned v ()) .faultUB hSrc hUb
      nomatch hEq
    have hSrcTgt : semSrc q outTgt := (hRef q hPre hNoUb).2 outTgt hTgt
    have hEq : outTgt = .returned v () :=
      hDet outTgt (.returned v ()) hSrcTgt hSrc
    rw [hEq]
    exact ⟨rfl, rfl⟩
  | aborted m =>
    cases m
    have hNoUb : ¬ semSrc q .faultUB := fun hUb => by
      have hEq := hDet (.aborted ()) .faultUB hSrc hUb
      nomatch hEq
    have hSrcTgt : semSrc q outTgt := (hRef q hPre hNoUb).2 outTgt hTgt
    have hEq : outTgt = .aborted () := hDet outTgt (.aborted ()) hSrcTgt hSrc
    rw [hEq]
    exact ⟨True.intro, rfl⟩
  | diverged =>
    have hNoUb : ¬ semSrc q .faultUB := fun hUb => by
      have hEq := hDet .diverged .faultUB hSrc hUb
      nomatch hEq
    have hSrcTgt : semSrc q outTgt := (hRef q hPre hNoUb).2 outTgt hTgt
    have hEq : outTgt = .diverged := hDet outTgt .diverged hSrcTgt hSrc
    rw [hEq]
    exact ⟨True.intro, True.intro⟩

/-- Unwrapped MIR outcome preservation: when `semSrc` is deterministic and
terminates without UB at `q` (`EntryPre q`), `SemRefinesUnder` yields exact
`MirOutcomeRefines`, `MirExactOutcomeRefines`, `MirOutcomeEquiv`,
`MirExactOutcomeEquiv`, and `Partial` order preservation under
`PanicStrategy.abort`. -/
theorem semRefinesUnder_preserves_mirOutcomeRefines {Q : Type}
    {EntryPre : Q → Prop}
    {semSrc semTgt : Q → ExecOutcome Nat Unit → Prop}
    (hRef : SemRefinesUnder EntryPre semSrc semTgt)
    {q : Q} (hPre : EntryPre q)
    (hDet : ∀ o₁ o₂, semSrc q o₁ → semSrc q o₂ → o₁ = o₂)
    {outSrc outTgt : ExecOutcome Nat Unit}
    {cSrc : MirOutcomeClass Value} {eSrc : MirExactOutcomeClass Value}
    (hSrc : semSrc q outSrc) (hTgt : semTgt q outTgt)
    (hNoUb : ¬ semSrc q .faultUB)
    (hCls : execOutcomeToMirClass? outSrc = some cSrc)
    (hEx : execOutcomeToMirExactClass? outSrc = some eSrc) :
    ∃ cTgt eTgt,
      execOutcomeToMirClass? outTgt = some cTgt ∧
      execOutcomeToMirExactClass? outTgt = some eTgt ∧
      MirOutcomeRefines cSrc cTgt ∧
      MirExactOutcomeRefines eSrc eTgt ∧
      MirOutcomeEquiv cSrc cTgt ∧
      MirExactOutcomeEquiv eSrc eTgt ∧
      cTgt.toPartial ≤ cSrc.toPartial ∧
      eTgt.toPartial ≤ eSrc.toPartial := by
  have hSrcTgt : semSrc q outTgt := (hRef q hPre hNoUb).2 outTgt hTgt
  have hEq : outTgt = outSrc := hDet outTgt outSrc hSrcTgt hSrc
  rw [hEq]
  refine ⟨cSrc, eSrc, hCls, hEx, mirOutcomeRefines_refl cSrc,
    mirExactOutcomeRefines_refl eSrc, mirOutcomeEquiv_refl cSrc,
    mirExactOutcomeEquiv_refl eSrc,
    (mirOutcomeRefines_iff_partial_le cSrc cSrc).1
      (mirOutcomeRefines_refl cSrc),
    (mirExactOutcomeRefines_iff_partial_le eSrc eSrc).1
      (mirExactOutcomeRefines_refl eSrc)⟩

theorem mirOptOutcomeRefines_refl (x : Option (MirOutcomeClass Value)) :
    MirOptOutcomeRefines x x := by
  cases x with
  | none => exact True.intro
  | some c =>
    cases c with
    | ret _ => exact rfl
    | trap => exact True.intro
    | ub => exact True.intro
    | unsupported => exact True.intro

theorem mirOptExactOutcomeRefines_refl
    (x : Option (MirExactOutcomeClass Value)) :
    MirOptExactOutcomeRefines x x := by
  cases x with
  | none => exact True.intro
  | some c =>
    cases c with
    | ret _ => exact rfl
    | trap _ => exact rfl
    | ub => exact True.intro
    | unsupported => exact True.intro

/-! Faithfulness of the outcome bridge. Returned values are reduced modulo
`2^64`, so the bridge is exact on `u64`-ranged outcomes and only there. -/

/-- Backend outcomes whose returned value is `u64`-ranged. -/
def ExecOutcomeInU64 : ExecOutcome Nat Unit → Prop
  | .returned v () => v < modPow2 (uintWidth .u64)
  | .aborted () => True
  | .faultUB => True
  | .diverged => True

private theorem execOutcomeToMirValue_inj_on_u64 {v₁ v₂ : Nat}
    (h₁ : v₁ < modPow2 (uintWidth .u64)) (h₂ : v₂ < modPow2 (uintWidth .u64))
    (hEq : execOutcomeToMirValue v₁ = execOutcomeToMirValue v₂) :
    v₁ = v₂ := by
  dsimp only [execOutcomeToMirValue] at hEq
  injection hEq with hSc
  injection hSc with hBits _
  rw [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at hBits
  exact hBits

/-- The strategy-exact outcome bridge is injective on `u64`-ranged outcomes:
no two distinct Backend outcomes (returns, abort, UB, divergence) are
identified. -/
theorem execOutcomeToMirExactClass?_injective_on_u64
    {o₁ o₂ : ExecOutcome Nat Unit}
    (h₁ : ExecOutcomeInU64 o₁) (h₂ : ExecOutcomeInU64 o₂)
    (hEq : execOutcomeToMirExactClass? o₁ = execOutcomeToMirExactClass? o₂) :
    o₁ = o₂ := by
  cases o₁ with
  | returned v₁ m₁ =>
    cases m₁
    cases o₂ with
    | returned v₂ m₂ =>
      cases m₂
      have hV : execOutcomeToMirValue v₁ = execOutcomeToMirValue v₂ := by
        injection hEq with hRet
        injection hRet
      rw [execOutcomeToMirValue_inj_on_u64 h₁ h₂ hV]
    | aborted m₂ => cases m₂; nomatch hEq
    | faultUB => nomatch hEq
    | diverged => nomatch hEq
  | aborted m₁ =>
    cases m₁
    cases o₂ with
    | returned v₂ m₂ => cases m₂; nomatch hEq
    | aborted m₂ => cases m₂; rfl
    | faultUB => nomatch hEq
    | diverged => nomatch hEq
  | faultUB =>
    cases o₂ with
    | returned v₂ m₂ => cases m₂; nomatch hEq
    | aborted m₂ => cases m₂; nomatch hEq
    | faultUB => rfl
    | diverged => nomatch hEq
  | diverged =>
    cases o₂ with
    | returned v₂ m₂ => cases m₂; nomatch hEq
    | aborted m₂ => cases m₂; nomatch hEq
    | faultUB => nomatch hEq
    | diverged => rfl

/-- Refinement reflection: on `u64`-ranged outcomes, the divergence-preserving
strategy-exact refinement between bridged outcomes holds exactly when the
spec outcome is UB or the two Backend outcomes are equal. The bridge neither
adds nor loses a refinement. -/
theorem mirOptExactOutcomeRefines_exec_iff_on_u64
    {o₁ o₂ : ExecOutcome Nat Unit}
    (h₁ : ExecOutcomeInU64 o₁) (h₂ : ExecOutcomeInU64 o₂) :
    MirOptExactOutcomeRefines (execOutcomeToMirExactClass? o₁)
        (execOutcomeToMirExactClass? o₂) ↔
      (o₁ = .faultUB ∨ o₁ = o₂) := by
  constructor
  · intro hRef
    cases o₁ with
    | faultUB => exact Or.inl rfl
    | returned v₁ m₁ =>
      cases m₁
      cases o₂ with
      | returned v₂ m₂ =>
        cases m₂
        have hV : execOutcomeToMirValue v₁ = execOutcomeToMirValue v₂ := hRef
        exact Or.inr (by rw [execOutcomeToMirValue_inj_on_u64 h₁ h₂ hV])
      | aborted m₂ => cases m₂; exact False.elim hRef
      | faultUB => exact False.elim hRef
      | diverged => exact False.elim hRef
    | aborted m₁ =>
      cases m₁
      cases o₂ with
      | returned v₂ m₂ => cases m₂; exact False.elim hRef
      | aborted m₂ => cases m₂; exact Or.inr rfl
      | faultUB => exact False.elim hRef
      | diverged => exact False.elim hRef
    | diverged =>
      cases o₂ with
      | returned v₂ m₂ => cases m₂; exact False.elim hRef
      | aborted m₂ => cases m₂; exact False.elim hRef
      | faultUB => exact False.elim hRef
      | diverged => exact Or.inr rfl
  · intro h
    cases h with
    | inl hUb =>
      rw [hUb]
      cases o₂ with
      | returned v₂ m₂ => cases m₂; exact True.intro
      | aborted m₂ => cases m₂; exact True.intro
      | faultUB => exact True.intro
      | diverged => exact True.intro
    | inr hEq =>
      rw [hEq]
      exact mirOptExactOutcomeRefines_refl _

/-- Without the range restriction the bridge is NOT injective: returned
values are reduced modulo `2^64`, so `0` and `2^64` are identified. -/
theorem neg_execOutcomeToMirExactClass?_not_injective_unranged :
    execOutcomeToMirExactClass? (.returned 0 ()) =
      execOutcomeToMirExactClass? (.returned u64Mod ()) ∧
    (ExecOutcome.returned 0 () : ExecOutcome Nat Unit) ≠
      .returned u64Mod () ∧
    ¬ ExecOutcomeInU64 (.returned u64Mod ()) :=
  ⟨rfl,
   (fun h => by
     injection h with hV _
     exact absurd hV (Nat.ne_of_lt u64Mod_pos)),
   (fun h => Nat.lt_irrefl _ h)⟩

/-- The strategy-erased (`PanicStrategy.abort`) outcome bridge is also
injective on `u64`-ranged outcomes, because `ExecOutcome` has only `.aborted`
(never `.panic`). -/
theorem execOutcomeToMirClass?_injective_on_u64
    {o₁ o₂ : ExecOutcome Nat Unit}
    (h₁ : ExecOutcomeInU64 o₁) (h₂ : ExecOutcomeInU64 o₂)
    (hEq : execOutcomeToMirClass? o₁ = execOutcomeToMirClass? o₂) :
    o₁ = o₂ := by
  cases o₁ with
  | returned v₁ m₁ =>
    cases m₁
    cases o₂ with
    | returned v₂ m₂ =>
      cases m₂
      have hV : execOutcomeToMirValue v₁ = execOutcomeToMirValue v₂ := by
        injection hEq with hRet
        injection hRet
      rw [execOutcomeToMirValue_inj_on_u64 h₁ h₂ hV]
    | aborted m₂ => cases m₂; nomatch hEq
    | faultUB => nomatch hEq
    | diverged => nomatch hEq
  | aborted m₁ =>
    cases m₁
    cases o₂ with
    | returned v₂ m₂ => cases m₂; nomatch hEq
    | aborted m₂ => cases m₂; rfl
    | faultUB => nomatch hEq
    | diverged => nomatch hEq
  | faultUB =>
    cases o₂ with
    | returned v₂ m₂ => cases m₂; nomatch hEq
    | aborted m₂ => cases m₂; nomatch hEq
    | faultUB => rfl
    | diverged => nomatch hEq
  | diverged =>
    cases o₂ with
    | returned v₂ m₂ => cases m₂; nomatch hEq
    | aborted m₂ => cases m₂; nomatch hEq
    | faultUB => nomatch hEq
    | diverged => rfl

/-- Refinement reflection for the strategy-erased bridge on `u64`-ranged
outcomes: `MirOptOutcomeRefines` holds iff the spec is UB or equal to impl. -/
theorem mirOptOutcomeRefines_exec_iff_on_u64
    {o₁ o₂ : ExecOutcome Nat Unit}
    (h₁ : ExecOutcomeInU64 o₁) (h₂ : ExecOutcomeInU64 o₂) :
    MirOptOutcomeRefines (execOutcomeToMirClass? o₁)
        (execOutcomeToMirClass? o₂) ↔
      (o₁ = .faultUB ∨ o₁ = o₂) := by
  constructor
  · intro hRef
    cases o₁ with
    | faultUB => exact Or.inl rfl
    | returned v₁ m₁ =>
      cases m₁
      cases o₂ with
      | returned v₂ m₂ =>
        cases m₂
        have hV : execOutcomeToMirValue v₁ = execOutcomeToMirValue v₂ := hRef
        exact Or.inr (by rw [execOutcomeToMirValue_inj_on_u64 h₁ h₂ hV])
      | aborted m₂ => cases m₂; exact False.elim hRef
      | faultUB => exact False.elim hRef
      | diverged => exact False.elim hRef
    | aborted m₁ =>
      cases m₁
      cases o₂ with
      | returned v₂ m₂ => cases m₂; exact False.elim hRef
      | aborted m₂ => cases m₂; exact Or.inr rfl
      | faultUB => exact False.elim hRef
      | diverged => exact False.elim hRef
    | diverged =>
      cases o₂ with
      | returned v₂ m₂ => cases m₂; exact False.elim hRef
      | aborted m₂ => cases m₂; exact False.elim hRef
      | faultUB => exact False.elim hRef
      | diverged => exact Or.inr rfl
  · intro h
    cases h with
    | inl hUb =>
      rw [hUb]
      cases o₂ with
      | returned v₂ m₂ => cases m₂; exact True.intro
      | aborted m₂ => cases m₂; exact True.intro
      | faultUB => exact True.intro
      | diverged => exact True.intro
    | inr hEq =>
      rw [hEq]
      exact mirOptOutcomeRefines_refl _

/-- Relational preservation with NO determinism assumption on `semSrc`: under
`SemRefinesUnder`, on an input satisfying `EntryPre` where `semSrc` cannot
fault with UB, no target outcome maps to `.ub`, and every target outcome is
matched by a source outcome that it refines in both the strategy-erased and
the strategy-exact order (`.diverged` only by `.diverged`). -/
theorem semRefinesUnder_preserves_mirOptRefines_relational {Q : Type}
    {EntryPre : Q → Prop}
    {semSrc semTgt : Q → ExecOutcome Nat Unit → Prop}
    (hRef : SemRefinesUnder EntryPre semSrc semTgt)
    {q : Q} (hPre : EntryPre q) (hNoUb : ¬ semSrc q .faultUB)
    {outTgt : ExecOutcome Nat Unit} (hTgt : semTgt q outTgt) :
    execOutcomeToMirClass? outTgt ≠ some .ub ∧
    execOutcomeToMirExactClass? outTgt ≠ some .ub ∧
    ∃ outSrc, semSrc q outSrc ∧
      MirOptOutcomeRefines (execOutcomeToMirClass? outSrc)
        (execOutcomeToMirClass? outTgt) ∧
      MirOptExactOutcomeRefines (execOutcomeToMirExactClass? outSrc)
        (execOutcomeToMirExactClass? outTgt) := by
  have hBoth := hRef q hPre hNoUb
  have hExists :
      ∃ outSrc, semSrc q outSrc ∧
        MirOptOutcomeRefines (execOutcomeToMirClass? outSrc)
          (execOutcomeToMirClass? outTgt) ∧
        MirOptExactOutcomeRefines (execOutcomeToMirExactClass? outSrc)
          (execOutcomeToMirExactClass? outTgt) :=
    ⟨outTgt, hBoth.2 outTgt hTgt, mirOptOutcomeRefines_refl _,
      mirOptExactOutcomeRefines_refl _⟩
  cases outTgt with
  | returned v m =>
    cases m
    exact ⟨(fun h => nomatch h), (fun h => nomatch h), hExists⟩
  | aborted m =>
    cases m
    exact ⟨(fun h => nomatch h), (fun h => nomatch h), hExists⟩
  | faultUB => exact False.elim (hBoth.1 hTgt)
  | diverged =>
    exact ⟨(fun h => nomatch h), (fun h => nomatch h), hExists⟩

/-- Asymmetric relational preservation without determinism, covering BOTH the
source-UB case (`semSrc q .faultUB`, where `outSrc = .faultUB` refines any
target outcome) and the UB-free case (`¬ semSrc q .faultUB`). -/
theorem semRefinesUnder_preserves_mirOptRefines_asymmetric {Q : Type}
    {EntryPre : Q → Prop}
    {semSrc semTgt : Q → ExecOutcome Nat Unit → Prop}
    (hRef : SemRefinesUnder EntryPre semSrc semTgt)
    {q : Q} (hPre : EntryPre q)
    (hUbDec : semSrc q .faultUB ∨ ¬ semSrc q .faultUB)
    {outTgt : ExecOutcome Nat Unit} (hTgt : semTgt q outTgt) :
    ∃ outSrc, semSrc q outSrc ∧
      MirOptOutcomeRefines (execOutcomeToMirClass? outSrc)
        (execOutcomeToMirClass? outTgt) ∧
      MirOptExactOutcomeRefines (execOutcomeToMirExactClass? outSrc)
        (execOutcomeToMirExactClass? outTgt) := by
  cases hUbDec with
  | inl hUb =>
    refine ⟨.faultUB, hUb, ?_, ?_⟩
    · cases outTgt with
      | returned _ m => cases m; exact True.intro
      | aborted m => cases m; exact True.intro
      | faultUB => exact True.intro
      | diverged => exact True.intro
    · cases outTgt with
      | returned _ m => cases m; exact True.intro
      | aborted m => cases m; exact True.intro
      | faultUB => exact True.intro
      | diverged => exact True.intro
  | inr hNoUb =>
    exact (semRefinesUnder_preserves_mirOptRefines_relational hRef hPre hNoUb
      hTgt).2.2

/-- Deterministic operational form of `evalBlockWithGuards`. -/
def evalBlockWithGuardsDet (guards : List GuardCond) (arena : List DagNode)
    (retId : Nat) (env : Nat → Nat) : ExecOutcome Nat Unit :=
  match evalGuards (evalArena env arena) guards with
  | none => .faultUB
  | some false => .aborted ()
  | some true =>
    match evalArenaNode env arena retId with
    | .poison => .faultUB
    | .val v => .returned v ()

theorem evalBlockWithGuards_iff_det (guards : List GuardCond)
    (arena : List DagNode) (retId : Nat) (env : Nat → Nat)
    (out : ExecOutcome Nat Unit) :
    evalBlockWithGuards guards arena retId env out ↔
      out = evalBlockWithGuardsDet guards arena retId env := by
  dsimp only [evalBlockWithGuards, evalBlockWithGuardsDet]
  cases evalGuards (evalArena env arena) guards with
  | none => exact Iff.rfl
  | some b =>
    cases b with
    | false => exact Iff.rfl
    | true =>
      cases evalArenaNode env arena retId with
      | poison => exact Iff.rfl
      | val _ => exact Iff.rfl

theorem evalBlockWithGuards_det (guards : List GuardCond)
    (arena : List DagNode) (retId : Nat) (env : Nat → Nat)
    {o₁ o₂ : ExecOutcome Nat Unit}
    (h₁ : evalBlockWithGuards guards arena retId env o₁)
    (h₂ : evalBlockWithGuards guards arena retId env o₂) : o₁ = o₂ := by
  rw [evalBlockWithGuards_iff_det] at h₁ h₂
  rw [h₁, h₂]

theorem evalBlockWithGuardsDet_ne_diverged (guards : List GuardCond)
    (arena : List DagNode) (retId : Nat) (env : Nat → Nat) :
    evalBlockWithGuardsDet guards arena retId env ≠ .diverged := by
  dsimp only [evalBlockWithGuardsDet]
  cases evalGuards (evalArena env arena) guards with
  | none => intro h; nomatch h
  | some b =>
    cases b with
    | false => intro h; nomatch h
    | true =>
      cases evalArenaNode env arena retId with
      | poison => intro h; nomatch h
      | val _ => intro h; nomatch h

/-- Direct `MirOutcomeClass Value` semantics of a guarded expression block. -/
def evalBlockMirClass (guards : List GuardCond) (arena : List DagNode)
    (retId : Nat) (env : Nat → Nat) : MirOutcomeClass Value :=
  match evalGuards (evalArena env arena) guards with
  | none => .ub
  | some false => .trap
  | some true =>
    match evalArenaNode env arena retId with
    | .poison => .ub
    | .val v => .ret (execOutcomeToMirValue v)

/-- Direct strategy-exact `MirExactOutcomeClass Value` (`PanicStrategy.abort`)
semantics of a guarded expression block. -/
def evalBlockMirExactClass (guards : List GuardCond) (arena : List DagNode)
    (retId : Nat) (env : Nat → Nat) : MirExactOutcomeClass Value :=
  match evalGuards (evalArena env arena) guards with
  | none => .ub
  | some false => .trap .abort
  | some true =>
    match evalArenaNode env arena retId with
    | .poison => .ub
    | .val v => .ret (execOutcomeToMirValue v)

theorem execOutcomeToMirClass?_evalBlockDet (guards : List GuardCond)
    (arena : List DagNode) (retId : Nat) (env : Nat → Nat) :
    execOutcomeToMirClass? (evalBlockWithGuardsDet guards arena retId env) =
      some (evalBlockMirClass guards arena retId env) := by
  dsimp only [evalBlockWithGuardsDet, evalBlockMirClass]
  cases evalGuards (evalArena env arena) guards with
  | none => rfl
  | some b =>
    cases b with
    | false => rfl
    | true =>
      cases evalArenaNode env arena retId with
      | poison => rfl
      | val _ => rfl

theorem execOutcomeToMirExactClass?_evalBlockDet (guards : List GuardCond)
    (arena : List DagNode) (retId : Nat) (env : Nat → Nat) :
    execOutcomeToMirExactClass?
        (evalBlockWithGuardsDet guards arena retId env) =
      some (evalBlockMirExactClass guards arena retId env) := by
  dsimp only [evalBlockWithGuardsDet, evalBlockMirExactClass]
  cases evalGuards (evalArena env arena) guards with
  | none => rfl
  | some b =>
    cases b with
    | false => rfl
    | true =>
      cases evalArenaNode env arena retId with
      | poison => rfl
      | val _ => rfl

/-- Any `blockOptGate` `BoolCertCut` preserves asymmetric `MirOutcomeRefines`
and `MirExactOutcomeRefines` (and `Partial` order) for all inputs satisfying
`SourceEntryPre src`. -/
theorem blockOptGate_cut_preserves_mirRefines (maxStepsPerNode : Nat)
    (src : SourceBlockUnit) (out : CompiledBlockUnit) (steps : List DagStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (blockOptGate maxStepsPerNode)) (src, out, steps))
    (env : Nat → Nat) (hEntry : SourceEntryPre src env) :
    MirOutcomeRefines
      (evalBlockMirClass src.guards src.arena src.srcRetId env)
      (evalBlockMirClass out.guardsOut out.arenaOut out.retId env) ∧
    MirExactOutcomeRefines
      (evalBlockMirExactClass src.guards src.arena src.srcRetId env)
      (evalBlockMirExactClass out.guardsOut out.arenaOut out.retId env) ∧
    (evalBlockMirClass out.guardsOut out.arenaOut out.retId env).toPartial ≤
      (evalBlockMirClass src.guards src.arena src.srcRetId env).toPartial ∧
    (evalBlockMirExactClass out.guardsOut out.arenaOut out.retId
        env).toPartial ≤
      (evalBlockMirExactClass src.guards src.arena src.srcRetId
        env).toPartial := by
  have hRef :
      SemRefinesUnder (SourceEntryPre src)
        (evalSourceBlockUnit src) (evalCompiledBlockUnit out) :=
    certGateCut_sound (blockOptGate maxStepsPerNode) True.intro hCut
  have hSrc :
      evalSourceBlockUnit src env
        (evalBlockWithGuardsDet src.guards src.arena src.srcRetId env) :=
    (evalBlockWithGuards_iff_det _ _ _ _ _).2 rfl
  have hTgt :
      evalCompiledBlockUnit out env
        (evalBlockWithGuardsDet out.guardsOut out.arenaOut out.retId env) :=
    (evalBlockWithGuards_iff_det _ _ _ _ _).2 rfl
  have hOpt :=
    semRefinesUnder_preserves_mirOptRefines hRef hEntry
      (fun _ _ h₁ h₂ => evalBlockWithGuards_det _ _ _ _ h₁ h₂) hSrc hTgt
  rw [execOutcomeToMirClass?_evalBlockDet,
      execOutcomeToMirClass?_evalBlockDet,
      execOutcomeToMirExactClass?_evalBlockDet,
      execOutcomeToMirExactClass?_evalBlockDet] at hOpt
  exact ⟨hOpt.1, hOpt.2,
    (mirOutcomeRefines_iff_partial_le _ _).1 hOpt.1,
    (mirExactOutcomeRefines_iff_partial_le _ _).1 hOpt.2⟩

/-- Forgetting the trap kind of the strategy-exact block class gives the
strategy-erased block class. -/
theorem evalBlockMirExactClass_forget (guards : List GuardCond)
    (arena : List DagNode) (retId : Nat) (env : Nat → Nat) :
    (evalBlockMirExactClass guards arena retId env).forgetTrapKind =
      evalBlockMirClass guards arena retId env := by
  dsimp only [evalBlockMirExactClass, evalBlockMirClass]
  cases evalGuards (evalArena env arena) guards with
  | none => rfl
  | some b =>
    cases b with
    | false => rfl
    | true =>
      cases evalArenaNode env arena retId with
      | poison => rfl
      | val _ => rfl

/-- A guarded expression block never unwinds: its strategy-exact class is
never `.trap .panic`. -/
theorem evalBlockMirExactClass_ne_trap_panic (guards : List GuardCond)
    (arena : List DagNode) (retId : Nat) (env : Nat → Nat) :
    evalBlockMirExactClass guards arena retId env ≠ .trap .panic := by
  dsimp only [evalBlockMirExactClass]
  cases evalGuards (evalArena env arena) guards with
  | none => intro h; nomatch h
  | some b =>
    cases b with
    | false => intro h; nomatch h
    | true =>
      cases evalArenaNode env arena retId with
      | poison => intro h; nomatch h
      | val _ => intro h; nomatch h

/-- A guarded expression block always settles: its strategy-exact class is
never `.unsupported`. -/
theorem evalBlockMirExactClass_ne_unsupported (guards : List GuardCond)
    (arena : List DagNode) (retId : Nat) (env : Nat → Nat) :
    evalBlockMirExactClass guards arena retId env ≠ .unsupported := by
  dsimp only [evalBlockMirExactClass]
  cases evalGuards (evalArena env arena) guards with
  | none => intro h; nomatch h
  | some b =>
    cases b with
    | false => intro h; nomatch h
    | true =>
      cases evalArenaNode env arena retId with
      | poison => intro h; nomatch h
      | val _ => intro h; nomatch h

/-- A defined spec outcome (neither `.ub` nor `.unsupported`) that is refined
is matched exactly, so the refinement is an equivalence. -/
theorem mirExactOutcomeEquiv_of_refines_of_defined
    {x y : MirExactOutcomeClass Value}
    (h : MirExactOutcomeRefines x y) (hUb : x ≠ .ub)
    (hUns : x ≠ .unsupported) : MirExactOutcomeEquiv x y := by
  cases x with
  | ub => exact False.elim (hUb rfl)
  | unsupported => exact False.elim (hUns rfl)
  | trap k =>
    cases y with
    | trap k' => exact ⟨h, h.symm⟩
    | ret _ => exact False.elim h
    | ub => exact False.elim h
    | unsupported => exact False.elim h
  | ret v =>
    cases y with
    | ret v' => exact ⟨h, h.symm⟩
    | trap _ => exact False.elim h
    | ub => exact False.elim h
    | unsupported => exact False.elim h

/-- A MIR state whose strategy-exact class is not `.trap .panic` is
classified under `PanicStrategy.abort` by forgetting the trap kind. -/
theorem classifyMirExecState_abort_eq_forget {st : MirExecState}
    (hNoPanic : classifyMirExecStateExact st ≠ .trap .panic) :
    classifyMirExecState .abort st =
      (classifyMirExecStateExact st).forgetTrapKind :=
  classifyMirExecState_matches_exact_abort st
    (fun h => hNoPanic (by rw [h]; rfl))

/-- A strategy-exact pointwise correspondence between a guarded block and a
MIR state also gives the `PanicStrategy.abort` correspondence. -/
theorem evalBlockMirClass_corresponds_of_exact {guards : List GuardCond}
    {arena : List DagNode} {retId : Nat} {env : Nat → Nat}
    {st : MirExecState}
    (hExact : evalBlockMirExactClass guards arena retId env =
      classifyMirExecStateExact st) :
    evalBlockMirClass guards arena retId env =
      classifyMirExecState .abort st := by
  have hNoPanic : classifyMirExecStateExact st ≠ .trap .panic := by
    rw [← hExact]
    exact evalBlockMirExactClass_ne_trap_panic guards arena retId env
  rw [classifyMirExecState_abort_eq_forget hNoPanic, ← hExact,
    evalBlockMirExactClass_forget]

/-- Certificate transport: ANY `blockOptGate` `BoolCertCut`, together with
pointwise correspondences identifying the source and compiled blocks with MIR
execution states `stSrc` and `stTgt`, yields asymmetric
`MirExactOutcomeRefines` and `MirOutcomeRefines` (`PanicStrategy.abort`)
between those states. The MIR refinement is derived from the
gate-established `SemRefinesUnder`; it is not re-proved from arithmetic side
conditions. -/
theorem blockOptGate_cut_transports_to_mirExecState (maxStepsPerNode : Nat)
    (src : SourceBlockUnit) (out : CompiledBlockUnit) (steps : List DagStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (blockOptGate maxStepsPerNode)) (src, out, steps))
    (env : Nat → Nat) (hEntry : SourceEntryPre src env)
    {stSrc stTgt : MirExecState}
    (hSrcCorr : evalBlockMirExactClass src.guards src.arena src.srcRetId env =
      classifyMirExecStateExact stSrc)
    (hTgtCorr :
      evalBlockMirExactClass out.guardsOut out.arenaOut out.retId env =
        classifyMirExecStateExact stTgt) :
    MirExactOutcomeRefines (classifyMirExecStateExact stSrc)
      (classifyMirExecStateExact stTgt) ∧
    MirOutcomeRefines (classifyMirExecState .abort stSrc)
      (classifyMirExecState .abort stTgt) := by
  have hBlock := blockOptGate_cut_preserves_mirRefines maxStepsPerNode src out
    steps hCut env hEntry
  have hExact := hBlock.2.1
  have hErased := hBlock.1
  rw [hSrcCorr, hTgtCorr] at hExact
  rw [evalBlockMirClass_corresponds_of_exact hSrcCorr,
    evalBlockMirClass_corresponds_of_exact hTgtCorr] at hErased
  exact ⟨hExact, hErased⟩

/-- Certificate transport to an EQUIVALENCE: when the source run is defined
(not UB), the gate-derived refinement alone forces the compiled run to match
it exactly, in both the strategy-exact and the `PanicStrategy.abort` order.
No converse refinement theorem is needed. -/
theorem blockOptGate_cut_transports_to_mirExecState_equiv
    (maxStepsPerNode : Nat)
    (src : SourceBlockUnit) (out : CompiledBlockUnit) (steps : List DagStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (blockOptGate maxStepsPerNode)) (src, out, steps))
    (env : Nat → Nat) (hEntry : SourceEntryPre src env)
    {stSrc stTgt : MirExecState}
    (hSrcCorr : evalBlockMirExactClass src.guards src.arena src.srcRetId env =
      classifyMirExecStateExact stSrc)
    (hTgtCorr :
      evalBlockMirExactClass out.guardsOut out.arenaOut out.retId env =
        classifyMirExecStateExact stTgt)
    (hSrcDefined : classifyMirExecStateExact stSrc ≠ .ub) :
    MirExactOutcomeEquiv (classifyMirExecStateExact stSrc)
      (classifyMirExecStateExact stTgt) ∧
    MirOutcomeEquiv (classifyMirExecState .abort stSrc)
      (classifyMirExecState .abort stTgt) := by
  have hFwd := blockOptGate_cut_transports_to_mirExecState maxStepsPerNode src
    out steps hCut env hEntry hSrcCorr hTgtCorr
  have hSrcSettled : classifyMirExecStateExact stSrc ≠ .unsupported := by
    rw [← hSrcCorr]
    exact evalBlockMirExactClass_ne_unsupported _ _ _ _
  have hEquiv :=
    mirExactOutcomeEquiv_of_refines_of_defined hFwd.1 hSrcDefined hSrcSettled
  have hSrcNoPanic : classifyMirExecStateExact stSrc ≠ .trap .panic := by
    rw [← hSrcCorr]
    exact evalBlockMirExactClass_ne_trap_panic _ _ _ _
  have hTgtNoPanic : classifyMirExecStateExact stTgt ≠ .trap .panic := by
    rw [← hTgtCorr]
    exact evalBlockMirExactClass_ne_trap_panic _ _ _ _
  refine ⟨hEquiv, hFwd.2, ?_⟩
  rw [classifyMirExecState_abort_eq_forget hSrcNoPanic,
    classifyMirExecState_abort_eq_forget hTgtNoPanic]
  exact mirExactOutcomeRefines_forget hEquiv.2

/-- Any `MirExecState` whose exact classification is not `.unsupported` is a
`SettledExec` (halted or `.faulted .ub`). -/
theorem settledExec_of_classifyExact_ne_unsupported {st : MirExecState}
    (h : classifyMirExecStateExact st ≠ .unsupported) : SettledExec st := by
  cases st with
  | halted _ => exact True.intro
  | running _ => exact False.elim (h rfl)
  | faulted fk =>
    cases fk with
    | ub => exact True.intro
    | unsupported => exact False.elim (h rfl)
    | outOfFuel => exact False.elim (h rfl)

/-- Lift `MirExactOutcomeRefines` from value-only `classifyMirExecStateExact`
to full `(Value × Memory)` `classifyMirOutcomeExact` whenever normal halts
agree on final memory. -/
theorem mirExactOutcomeRefines_to_full_outcome {stSrc stTgt : MirExecState}
    (hRef : MirExactOutcomeRefines (classifyMirExecStateExact stSrc)
      (classifyMirExecStateExact stTgt))
    (hMem : ∀ v₁ m₁ v₂ m₂,
      stSrc = .halted (.normal (v₁, m₁)) →
      stTgt = .halted (.normal (v₂, m₂)) → m₁ = m₂) :
    MirExactOutcomeRefines (classifyMirOutcomeExact stSrc)
      (classifyMirOutcomeExact stTgt) := by
  cases stSrc with
  | running _ => exact True.intro
  | faulted fkS =>
    cases fkS with
    | ub => exact True.intro
    | unsupported => exact True.intro
    | outOfFuel => exact True.intro
  | halted oS =>
    cases oS with
    | abort =>
      cases stTgt with
      | running _ => exact False.elim hRef
      | faulted fkT => cases fkT <;> exact False.elim hRef
      | halted oT =>
        cases oT with
        | abort => rfl
        | panic => exact False.elim (nomatch hRef)
        | normal _ => exact False.elim hRef
    | panic =>
      cases stTgt with
      | running _ => exact False.elim hRef
      | faulted fkT => cases fkT <;> exact False.elim hRef
      | halted oT =>
        cases oT with
        | panic => rfl
        | abort => exact False.elim (nomatch hRef)
        | normal _ => exact False.elim hRef
    | normal vmS =>
      cases vmS with
      | mk v₁ m₁ =>
        cases stTgt with
        | running _ => exact False.elim hRef
        | faulted fkT => cases fkT <;> exact False.elim hRef
        | halted oT =>
          cases oT with
          | abort => exact False.elim hRef
          | panic => exact False.elim hRef
          | normal vmT =>
            cases vmT with
            | mk v₂ m₂ =>
              have hm : m₁ = m₂ := hMem v₁ m₁ v₂ m₂ rfl rfl
              cases hRef
              cases hm
              rfl

/-- Layer 1A `ITree.toPartial` certificate transport: ANY accepted
`blockOptGate` `BoolCertCut` plus pointwise correspondences and final-memory
agreement transports directly to the Layer 1A refinement of
`mirCallTree bSrc args` by `mirCallTree bTgt args`, via
`mirExactOutcomeRefines_iff_mirCallTree_toPartial_le`. -/
theorem blockOptGate_cut_transports_to_mirCallTree_toPartial
    (maxStepsPerNode : Nat)
    (src : SourceBlockUnit) (out : CompiledBlockUnit) (steps : List DagStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (blockOptGate maxStepsPerNode)) (src, out, steps))
    (env : Nat → Nat) (hEntry : SourceEntryPre src env)
    {bSrc bTgt : CapturedMir} {fSrc fTgt : Nat} {args : List Value}
    (hSrcCorr : evalBlockMirExactClass src.guards src.arena src.srcRetId env =
      classifyMirExecStateExact (runMirCall bSrc fSrc args))
    (hTgtCorr :
      evalBlockMirExactClass out.guardsOut out.arenaOut out.retId env =
        classifyMirExecStateExact (runMirCall bTgt fTgt args))
    (hMem : ∀ v₁ m₁ v₂ m₂,
      runMirCall bSrc fSrc args = .halted (.normal (v₁, m₁)) →
      runMirCall bTgt fTgt args = .halted (.normal (v₂, m₂)) → m₁ = m₂) :
    (mirCallTree bTgt args).toPartial ≤ (mirCallTree bSrc args).toPartial := by
  have hRef := (blockOptGate_cut_transports_to_mirExecState maxStepsPerNode src
    out steps hCut env hEntry hSrcCorr hTgtCorr).1
  have hSrcSet : SettledExec (runMirCall bSrc fSrc args) :=
    settledExec_of_classifyExact_ne_unsupported (by
      rw [← hSrcCorr]
      exact evalBlockMirExactClass_ne_unsupported _ _ _ _)
  have hTgtSet : SettledExec (runMirCall bTgt fTgt args) :=
    settledExec_of_classifyExact_ne_unsupported (by
      rw [← hTgtCorr]
      exact evalBlockMirExactClass_ne_unsupported _ _ _ _)
  exact (mirExactOutcomeRefines_iff_mirCallTree_toPartial_le hSrcSet hTgtSet).1
    (mirExactOutcomeRefines_to_full_outcome hRef hMem)

/-- Bidirectional Layer 1A `ITree.toPartial` certificate transport when the
source run is defined (non-UB). -/
theorem blockOptGate_cut_transports_to_mirCallTree_toPartial_equiv
    (maxStepsPerNode : Nat)
    (src : SourceBlockUnit) (out : CompiledBlockUnit) (steps : List DagStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (blockOptGate maxStepsPerNode)) (src, out, steps))
    (env : Nat → Nat) (hEntry : SourceEntryPre src env)
    {bSrc bTgt : CapturedMir} {fSrc fTgt : Nat} {args : List Value}
    (hSrcCorr : evalBlockMirExactClass src.guards src.arena src.srcRetId env =
      classifyMirExecStateExact (runMirCall bSrc fSrc args))
    (hTgtCorr :
      evalBlockMirExactClass out.guardsOut out.arenaOut out.retId env =
        classifyMirExecStateExact (runMirCall bTgt fTgt args))
    (hSrcDefined : classifyMirExecStateExact (runMirCall bSrc fSrc args) ≠ .ub)
    (hMem : ∀ v₁ m₁ v₂ m₂,
      runMirCall bSrc fSrc args = .halted (.normal (v₁, m₁)) →
      runMirCall bTgt fTgt args = .halted (.normal (v₂, m₂)) → m₁ = m₂) :
    (mirCallTree bTgt args).toPartial ≤ (mirCallTree bSrc args).toPartial ∧
    (mirCallTree bSrc args).toPartial ≤ (mirCallTree bTgt args).toPartial := by
  have hEq := (blockOptGate_cut_transports_to_mirExecState_equiv maxStepsPerNode
    src out steps hCut env hEntry hSrcCorr hTgtCorr hSrcDefined).1
  have hSrcSet : SettledExec (runMirCall bSrc fSrc args) :=
    settledExec_of_classifyExact_ne_unsupported (by
      rw [← hSrcCorr]
      exact evalBlockMirExactClass_ne_unsupported _ _ _ _)
  have hTgtSet : SettledExec (runMirCall bTgt fTgt args) :=
    settledExec_of_classifyExact_ne_unsupported (by
      rw [← hTgtCorr]
      exact evalBlockMirExactClass_ne_unsupported _ _ _ _)
  exact
    ⟨(mirExactOutcomeRefines_iff_mirCallTree_toPartial_le hSrcSet hTgtSet).1
       (mirExactOutcomeRefines_to_full_outcome hEq.1 hMem),
     (mirExactOutcomeRefines_iff_mirCallTree_toPartial_le hTgtSet hSrcSet).1
       (mirExactOutcomeRefines_to_full_outcome hEq.2
         (fun v₁ m₁ v₂ m₂ hT hS => (hMem v₂ m₂ v₁ m₁ hS hT).symm))⟩

/-! ### 4.3 Concrete `u64` Guard Elision <-> MIR `stepMirState` Bridges -/

/-- Two-variable environment mapping variable `0 ↦ a`, `1 ↦ b`, others `↦ 0`. -/
def env2 (a b : Nat) : Nat → Nat
  | 0 => a
  | 1 => b
  | _ => 0

/-- Canonical 4-node arena for `u64` checked/unchecked/wrapping addition. -/
def u64CheckedAddArena : List DagNode :=
  [ { op := .var 0, args := [] },       -- 0: a
    { op := .var 1, args := [] },       -- 1: b
    { op := .addWrap, args := [0, 1] }, -- 2: a +_w b
    { op := .addNuw, args := [0, 1] } ] -- 3: a +_nuw b

/-- Checked `u64` addition block guarded by `GuardCond.addNoOverflow 0 1`. -/
def u64CheckedAddSrc : SourceBlockUnit :=
  { guards := [.addNoOverflow 0 1]
    arena := u64CheckedAddArena
    srcRetId := 2
    candidates := [{ tier := .proven, fact := .addNoOverflow 0 1 }] }

/-- Guard-elided unchecked `u64` addition block (`addNuw`, faults UB on
overflow). -/
def u64UncheckedAddOpt : CompiledBlockUnit :=
  { guardsOut := []
    arenaOut := u64CheckedAddArena
    retId := 3 }

/-- Guard-elided wrapping `u64` addition block (`addWrap`, wraps mod `2^64`). -/
def u64WrappingAddOpt : CompiledBlockUnit :=
  { guardsOut := []
    arenaOut := u64CheckedAddArena
    retId := 2 }

def u64CheckedAddToUncheckedSteps : List DagStep :=
  [.biRule (.promoteAddNuw 0) [0, 1] 2 3]

def u64CheckedAddToWrappingSteps : List DagStep :=
  [ .biRule (.promoteAddNuw 0) [0, 1] 2 3,
    .dirRule .dropAddNuw [0, 1] 3 2,
    .trans 0 1 ]

/-- Canonical 4-node arena for `u64` checked/unchecked/wrapping subtraction. -/
def u64CheckedSubArena : List DagNode :=
  [ { op := .var 0, args := [] },       -- 0: a
    { op := .var 1, args := [] },       -- 1: b
    { op := .subWrap, args := [0, 1] }, -- 2: a -_w b
    { op := .subNuw, args := [0, 1] } ] -- 3: a -_nuw b

/-- Checked `u64` subtraction block guarded by `GuardCond.subNoUnderflow 0 1`.
-/
def u64CheckedSubSrc : SourceBlockUnit :=
  { guards := [.subNoUnderflow 0 1]
    arena := u64CheckedSubArena
    srcRetId := 2
    candidates := [{ tier := .proven, fact := .subNoUnderflow 0 1 }] }

/-- Guard-elided unchecked `u64` subtraction block (`subNuw`, faults UB on
underflow). -/
def u64UncheckedSubOpt : CompiledBlockUnit :=
  { guardsOut := []
    arenaOut := u64CheckedSubArena
    retId := 3 }

/-- Guard-elided wrapping `u64` subtraction block (`subWrap`, wraps mod
`2^64`). -/
def u64WrappingSubOpt : CompiledBlockUnit :=
  { guardsOut := []
    arenaOut := u64CheckedSubArena
    retId := 2 }

def u64CheckedSubToUncheckedSteps : List DagStep :=
  [.biRule (.promoteSubNuw 0) [0, 1] 2 3]

def u64CheckedSubToWrappingSteps : List DagStep :=
  [ .biRule (.promoteSubNuw 0) [0, 1] 2 3,
    .dirRule .dropSubNuw [0, 1] 3 2,
    .trans 0 1 ]

/-- Certified `blockOptGate` elision of `GuardCond.addNoOverflow 0 1` to
`addNuw` via `BoolCertCut.seal _ _ rfl`. -/
theorem u64CheckedAdd_blockOptGate_to_unchecked :
    SemRefinesUnder (SourceEntryPre u64CheckedAddSrc)
      (evalSourceBlockUnit u64CheckedAddSrc)
      (evalCompiledBlockUnit u64UncheckedAddOpt) :=
  certGateCut_sound (blockOptGate 2)
    (x := u64CheckedAddSrc) (y := u64UncheckedAddOpt)
    (w := u64CheckedAddToUncheckedSteps) True.intro
    (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)

/-- Certified `blockOptGate` elision of `GuardCond.addNoOverflow 0 1` to
`addWrap` via `BoolCertCut.seal _ _ rfl`. -/
theorem u64CheckedAdd_blockOptGate_to_wrapping :
    SemRefinesUnder (SourceEntryPre u64CheckedAddSrc)
      (evalSourceBlockUnit u64CheckedAddSrc)
      (evalCompiledBlockUnit u64WrappingAddOpt) :=
  certGateCut_sound (blockOptGate 2)
    (x := u64CheckedAddSrc) (y := u64WrappingAddOpt)
    (w := u64CheckedAddToWrappingSteps) True.intro
    (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)

/-- Certified `blockOptGate` elision of `GuardCond.subNoUnderflow 0 1` to
`subNuw` via `BoolCertCut.seal _ _ rfl`. -/
theorem u64CheckedSub_blockOptGate_to_unchecked :
    SemRefinesUnder (SourceEntryPre u64CheckedSubSrc)
      (evalSourceBlockUnit u64CheckedSubSrc)
      (evalCompiledBlockUnit u64UncheckedSubOpt) :=
  certGateCut_sound (blockOptGate 2)
    (x := u64CheckedSubSrc) (y := u64UncheckedSubOpt)
    (w := u64CheckedSubToUncheckedSteps) True.intro
    (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)

/-- Certified `blockOptGate` elision of `GuardCond.subNoUnderflow 0 1` to
`subWrap` via `BoolCertCut.seal _ _ rfl`. -/
theorem u64CheckedSub_blockOptGate_to_wrapping :
    SemRefinesUnder (SourceEntryPre u64CheckedSubSrc)
      (evalSourceBlockUnit u64CheckedSubSrc)
      (evalCompiledBlockUnit u64WrappingSubOpt) :=
  certGateCut_sound (blockOptGate 2)
    (x := u64CheckedSubSrc) (y := u64WrappingSubOpt)
    (w := u64CheckedSubToWrappingSteps) True.intro
    (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)

private theorem u64AddArena_node0 (a b : Nat) (ha : a < u64Mod) :
    listNthOpt (evalArena (env2 a b) u64CheckedAddArena) 0 = some (.val a) := by
  have h := (evalArenaNode_eq (env2 a b) u64CheckedAddArena rfl rfl (nid := 0)
    (d := { op := .var 0, args := [] })).1
  change listNthOpt (evalArena (env2 a b) u64CheckedAddArena) 0 =
    some (.val (word64 a)) at h
  rw [word64_of_lt ha] at h
  exact h

private theorem u64AddArena_node1 (a b : Nat) (hb : b < u64Mod) :
    listNthOpt (evalArena (env2 a b) u64CheckedAddArena) 1 = some (.val b) := by
  have h := (evalArenaNode_eq (env2 a b) u64CheckedAddArena rfl rfl (nid := 1)
    (d := { op := .var 1, args := [] })).1
  change listNthOpt (evalArena (env2 a b) u64CheckedAddArena) 1 =
    some (.val (word64 b)) at h
  rw [word64_of_lt hb] at h
  exact h

private theorem u64AddArena_node2 (a b : Nat) (ha : a < u64Mod)
    (hb : b < u64Mod) :
    evalArenaNode (env2 a b) u64CheckedAddArena 2 = .val (word64 (a + b)) := by
  have h := (evalArenaNode_eq (env2 a b) u64CheckedAddArena rfl rfl (nid := 2)
    (d := { op := .addWrap, args := [0, 1] })).2
  dsimp only [List.map, evalArenaNode] at h
  rw [u64AddArena_node0 a b ha, u64AddArena_node1 a b hb] at h
  dsimp only [Option.getD, evalSsaOp, evalBinaryPoison] at h
  rw [word64_of_lt ha, word64_of_lt hb] at h
  exact h

private theorem u64AddArena_node3 (a b : Nat) (ha : a < u64Mod)
    (hb : b < u64Mod) :
    evalArenaNode (env2 a b) u64CheckedAddArena 3 =
      match Nat.blt (a + b) u64Mod with
      | true => .val (a + b)
      | false => .poison := by
  have h := (evalArenaNode_eq (env2 a b) u64CheckedAddArena rfl rfl (nid := 3)
    (d := { op := .addNuw, args := [0, 1] })).2
  dsimp only [List.map, evalArenaNode] at h
  rw [u64AddArena_node0 a b ha, u64AddArena_node1 a b hb] at h
  dsimp only [Option.getD, evalSsaOp, evalBinaryPoison] at h
  rw [word64_of_lt ha, word64_of_lt hb] at h
  exact h

private theorem u64SubArena_node0 (a b : Nat) (ha : a < u64Mod) :
    listNthOpt (evalArena (env2 a b) u64CheckedSubArena) 0 = some (.val a) := by
  have h := (evalArenaNode_eq (env2 a b) u64CheckedSubArena rfl rfl (nid := 0)
    (d := { op := .var 0, args := [] })).1
  change listNthOpt (evalArena (env2 a b) u64CheckedSubArena) 0 =
    some (.val (word64 a)) at h
  rw [word64_of_lt ha] at h
  exact h

private theorem u64SubArena_node1 (a b : Nat) (hb : b < u64Mod) :
    listNthOpt (evalArena (env2 a b) u64CheckedSubArena) 1 = some (.val b) := by
  have h := (evalArenaNode_eq (env2 a b) u64CheckedSubArena rfl rfl (nid := 1)
    (d := { op := .var 1, args := [] })).1
  change listNthOpt (evalArena (env2 a b) u64CheckedSubArena) 1 =
    some (.val (word64 b)) at h
  rw [word64_of_lt hb] at h
  exact h

private theorem u64SubArena_node2 (a b : Nat) (ha : a < u64Mod)
    (hb : b < u64Mod) :
    evalArenaNode (env2 a b) u64CheckedSubArena 2 =
      .val (word64 (u64Mod + a - b)) := by
  have h := (evalArenaNode_eq (env2 a b) u64CheckedSubArena rfl rfl (nid := 2)
    (d := { op := .subWrap, args := [0, 1] })).2
  dsimp only [List.map, evalArenaNode] at h
  rw [u64SubArena_node0 a b ha, u64SubArena_node1 a b hb] at h
  dsimp only [Option.getD, evalSsaOp, evalBinaryPoison] at h
  rw [word64_of_lt ha, word64_of_lt hb] at h
  exact h

private theorem u64SubArena_node3 (a b : Nat) (ha : a < u64Mod)
    (hb : b < u64Mod) :
    evalArenaNode (env2 a b) u64CheckedSubArena 3 =
      match Nat.ble b a with
      | true => .val (a - b)
      | false => .poison := by
  have h := (evalArenaNode_eq (env2 a b) u64CheckedSubArena rfl rfl (nid := 3)
    (d := { op := .subNuw, args := [0, 1] })).2
  dsimp only [List.map, evalArenaNode] at h
  rw [u64SubArena_node0 a b ha, u64SubArena_node1 a b hb] at h
  dsimp only [Option.getD, evalSsaOp, evalBinaryPoison] at h
  rw [word64_of_lt ha, word64_of_lt hb] at h
  exact h

/-- `SourceEntryPre u64CheckedAddSrc (env2 a b)` holds iff `a + b < 2^64` for
all `u64`-ranged `a, b`. -/
theorem sourceEntryPre_u64CheckedAdd_iff (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64)) :
    SourceEntryPre u64CheckedAddSrc (env2 a b) ↔
      a + b < modPow2 (uintWidth .u64) := by
  have ha' : a < u64Mod := ha
  have hb' : b < u64Mod := hb
  constructor
  · intro hPre
    have hF := hPre 0 (.addNoOverflow 0 1) rfl
    exact hF a b (u64AddArena_node0 a b ha') (u64AddArena_node1 a b hb')
  · intro hLt idx f hNth
    cases idx with
    | succ _ => nomatch hNth
    | zero =>
      dsimp only [u64CheckedAddSrc, extractProvenFacts, List.foldr,
        listNthOpt] at hNth
      injection hNth with hf
      rw [← hf]
      intro x y hx hy
      dsimp only [u64CheckedAddSrc] at hx hy
      rw [u64AddArena_node0 a b ha'] at hx
      rw [u64AddArena_node1 a b hb'] at hy
      injection hx with hpx
      injection hpx with hxEq
      injection hy with hpy
      injection hpy with hyEq
      rw [← hxEq, ← hyEq]
      exact hLt

/-- `SourceEntryPre u64CheckedSubSrc (env2 a b)` holds iff `b ≤ a` for all
`u64`-ranged `a, b`. -/
theorem sourceEntryPre_u64CheckedSub_iff (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64)) :
    SourceEntryPre u64CheckedSubSrc (env2 a b) ↔ b ≤ a := by
  have ha' : a < u64Mod := ha
  have hb' : b < u64Mod := hb
  constructor
  · intro hPre
    have hF := hPre 0 (.subNoUnderflow 0 1) rfl
    exact hF a b (u64SubArena_node0 a b ha') (u64SubArena_node1 a b hb')
  · intro hLe idx f hNth
    cases idx with
    | succ _ => nomatch hNth
    | zero =>
      dsimp only [u64CheckedSubSrc, extractProvenFacts, List.foldr,
        listNthOpt] at hNth
      injection hNth with hf
      rw [← hf]
      intro x y hx hy
      dsimp only [u64CheckedSubSrc] at hx hy
      rw [u64SubArena_node0 a b ha'] at hx
      rw [u64SubArena_node1 a b hb'] at hy
      injection hx with hpx
      injection hpx with hxEq
      injection hy with hpy
      injection hpy with hyEq
      rw [← hxEq, ← hyEq]
      exact hLe

/-- Exact pointwise correspondence between guarded `u64CheckedAddSrc` and
`stepMirState` `mkCheckedArithBody .u64 .add .terminate` for ALL `u64`-ranged
inputs `a, b < 2^64`. -/
theorem u64CheckedAddSrc_corresponds_stepMirState (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64)) :
    evalBlockMirExactClass u64CheckedAddSrc.guards u64CheckedAddSrc.arena
      u64CheckedAddSrc.srcRetId (env2 a b) =
      classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 a b)) := by
  have ha' : a < u64Mod := ha
  have hb' : b < u64Mod := hb
  dsimp only [evalBlockMirExactClass, u64CheckedAddSrc, evalGuards, List.foldr,
    evalGuard]
  rw [u64AddArena_node0 a b ha', u64AddArena_node1 a b hb']
  dsimp only
  cases hBlt : Nat.blt (a + b) u64Mod with
  | true =>
    have hLt : a + b < modPow2 (uintWidth .u64) := (nat_blt_iff _ _).1 hBlt
    dsimp only
    rw [u64AddArena_node2 a b ha' hb']
    have hMir := runMirCall_checked_add_ok .u64 .abort a b hLt
    dsimp only [PanicStrategy.toUnwindAction] at hMir
    rw [hMir]
    dsimp only [classifyMirExecStateExact, execOutcomeToMirValue]
    rw [word64_of_lt hLt, Nat.mod_eq_of_lt hLt]
  | false =>
    have hOv : modPow2 (uintWidth .u64) ≤ a + b := by
      cases hLe : Nat.ble u64Mod (a + b) with
      | true => exact Nat.le_of_ble_eq_true hLe
      | false =>
        have hLt := nat_lt_of_ble_false_local hLe
        rw [(nat_blt_iff _ _).2 hLt] at hBlt
        nomatch hBlt
    dsimp only
    have hMir := runMirCall_checked_add_trap .u64 .abort a b hOv
    dsimp only [PanicStrategy.toUnwindAction, PanicStrategy.toTrapOutcome]
      at hMir
    rw [hMir]
    rfl

/-- Exact pointwise correspondence between `u64UncheckedAddOpt` (`addNuw`) and
`stepMirState` `mkUncheckedArithBody .u64 .add` for ALL `u64`-ranged inputs. -/
theorem u64UncheckedAddOpt_corresponds_stepMirState (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64)) :
    evalBlockMirExactClass u64UncheckedAddOpt.guardsOut
      u64UncheckedAddOpt.arenaOut u64UncheckedAddOpt.retId (env2 a b) =
      classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .add) 2
          (uintArgs2 .u64 a b)) := by
  have ha' : a < u64Mod := ha
  have hb' : b < u64Mod := hb
  dsimp only [evalBlockMirExactClass, u64UncheckedAddOpt, evalGuards,
    List.foldr]
  rw [u64AddArena_node3 a b ha' hb']
  cases hBlt : Nat.blt (a + b) u64Mod with
  | true =>
    have hLt : a + b < modPow2 (uintWidth .u64) := (nat_blt_iff _ _).1 hBlt
    dsimp only
    rw [runMirCall_unchecked_add_ok .u64 a b hLt]
    dsimp only [classifyMirExecStateExact, execOutcomeToMirValue]
    rw [Nat.mod_eq_of_lt hLt]
  | false =>
    have hOv : modPow2 (uintWidth .u64) ≤ a + b := by
      cases hLe : Nat.ble u64Mod (a + b) with
      | true => exact Nat.le_of_ble_eq_true hLe
      | false =>
        have hLt := nat_lt_of_ble_false_local hLe
        rw [(nat_blt_iff _ _).2 hLt] at hBlt
        nomatch hBlt
    dsimp only
    rw [runMirCall_unchecked_add_ub .u64 a b hOv]
    rfl

/-- Exact pointwise correspondence between `u64WrappingAddOpt` (`addWrap`) and
`stepMirState` `mkWrappingArithBody .u64 .add` for ALL `u64`-ranged inputs. -/
theorem u64WrappingAddOpt_corresponds_stepMirState (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64)) :
    evalBlockMirExactClass u64WrappingAddOpt.guardsOut
      u64WrappingAddOpt.arenaOut u64WrappingAddOpt.retId (env2 a b) =
      classifyMirExecStateExact
        (runMirCall (mkWrappingArithBody .u64 .add) 2
          (uintArgs2 .u64 a b)) := by
  have ha' : a < u64Mod := ha
  have hb' : b < u64Mod := hb
  dsimp only [evalBlockMirExactClass, u64WrappingAddOpt, evalGuards, List.foldr]
  rw [u64AddArena_node2 a b ha' hb', runMirCall_wrapping_add .u64 a b]
  dsimp only [classifyMirExecStateExact, execOutcomeToMirValue]
  have hPos : 0 < modPow2 (uintWidth .u64) := u64Mod_pos
  rw [word64_eq_mod_u64, Nat.mod_eq_of_lt (Nat.mod_lt _ hPos)]
  rfl

/-- Exact pointwise correspondence between guarded `u64CheckedSubSrc` and
`stepMirState` `mkCheckedArithBody .u64 .sub .terminate` for ALL `u64`-ranged
inputs `a, b < 2^64`. -/
theorem u64CheckedSubSrc_corresponds_stepMirState (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64)) :
    evalBlockMirExactClass u64CheckedSubSrc.guards u64CheckedSubSrc.arena
      u64CheckedSubSrc.srcRetId (env2 a b) =
      classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 a b)) := by
  have ha' : a < u64Mod := ha
  have hb' : b < u64Mod := hb
  dsimp only [evalBlockMirExactClass, u64CheckedSubSrc, evalGuards, List.foldr,
    evalGuard]
  rw [u64SubArena_node0 a b ha', u64SubArena_node1 a b hb']
  dsimp only
  cases hBle : Nat.ble b a with
  | true =>
    have hLe : b ≤ a := Nat.le_of_ble_eq_true hBle
    have hDiffLt : a - b < modPow2 (uintWidth .u64) :=
      Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
    dsimp only
    rw [u64SubArena_node2 a b ha' hb']
    have hMir := runMirCall_checked_sub_ok .u64 .abort a b ha hb hLe
    dsimp only [PanicStrategy.toUnwindAction] at hMir
    rw [hMir]
    dsimp only [classifyMirExecStateExact, execOutcomeToMirValue]
    have hWrapSub : word64 (u64Mod + a - b) = a - b := by
      have hW := wrapVal_sub_of_le (w := uintWidth .u64) hLe ha
      rw [wrapVal_of_lt hDiffLt] at hW
      exact hW.symm
    rw [hWrapSub, Nat.mod_eq_of_lt hDiffLt]
  | false =>
    have hUnd : a < b := nat_lt_of_ble_false_local hBle
    dsimp only
    have hMir := runMirCall_checked_sub_trap .u64 .abort a b ha hb hUnd
    dsimp only [PanicStrategy.toUnwindAction, PanicStrategy.toTrapOutcome]
      at hMir
    rw [hMir]
    rfl

/-- Exact pointwise correspondence between `u64UncheckedSubOpt` (`subNuw`) and
`stepMirState` `mkUncheckedArithBody .u64 .sub` for ALL `u64`-ranged inputs. -/
theorem u64UncheckedSubOpt_corresponds_stepMirState (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64)) :
    evalBlockMirExactClass u64UncheckedSubOpt.guardsOut
      u64UncheckedSubOpt.arenaOut u64UncheckedSubOpt.retId (env2 a b) =
      classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .sub) 2
          (uintArgs2 .u64 a b)) := by
  have ha' : a < u64Mod := ha
  have hb' : b < u64Mod := hb
  dsimp only [evalBlockMirExactClass, u64UncheckedSubOpt, evalGuards,
    List.foldr]
  rw [u64SubArena_node3 a b ha' hb']
  cases hBle : Nat.ble b a with
  | true =>
    have hLe : b ≤ a := Nat.le_of_ble_eq_true hBle
    have hDiffLt : a - b < modPow2 (uintWidth .u64) :=
      Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
    dsimp only
    rw [runMirCall_unchecked_sub_ok .u64 a b ha hLe]
    dsimp only [classifyMirExecStateExact, execOutcomeToMirValue]
    rw [Nat.mod_eq_of_lt hDiffLt]
  | false =>
    have hUnd : a < b := nat_lt_of_ble_false_local hBle
    dsimp only
    rw [runMirCall_unchecked_sub_ub .u64 a b hUnd]
    rfl

/-- Exact pointwise correspondence between `u64WrappingSubOpt` (`subWrap`) and
`stepMirState` `mkWrappingArithBody .u64 .sub` for ALL `u64`-ranged inputs. -/
theorem u64WrappingSubOpt_corresponds_stepMirState (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64)) :
    evalBlockMirExactClass u64WrappingSubOpt.guardsOut
      u64WrappingSubOpt.arenaOut u64WrappingSubOpt.retId (env2 a b) =
      classifyMirExecStateExact
        (runMirCall (mkWrappingArithBody .u64 .sub) 2
          (uintArgs2 .u64 a b)) := by
  have ha' : a < u64Mod := ha
  have hb' : b < u64Mod := hb
  dsimp only [evalBlockMirExactClass, u64WrappingSubOpt, evalGuards, List.foldr]
  rw [u64SubArena_node2 a b ha' hb', runMirCall_wrapping_sub .u64 a b ha hb]
  dsimp only [classifyMirExecStateExact, execOutcomeToMirValue]
  have hPos : 0 < modPow2 (uintWidth .u64) := u64Mod_pos
  rw [word64_eq_mod_u64, Nat.mod_eq_of_lt (Nat.mod_lt _ hPos)]
  rfl

private theorem canonMem_checked_add (a b : Nat) {v : Value} {m : Memory}
    (h : runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
      (uintArgs2 .u64 a b) = .halted (.normal (v, m))) :
    m = canonInitMemory := by
  cases hB : Nat.ble (modPow2 (uintWidth .u64)) (a + b) with
  | false =>
    have hOk := runMirCall_checked_add_ok .u64 .abort a b
      (nat_lt_of_ble_false_local hB)
    dsimp only [PanicStrategy.toUnwindAction] at hOk
    rw [hOk] at h
    injection h with hN
    injection hN with hP
    exact (congrArg Prod.snd hP).symm
  | true =>
    have hTr := runMirCall_checked_add_trap .u64 .abort a b
      (Nat.le_of_ble_eq_true hB)
    dsimp only [PanicStrategy.toUnwindAction,
      PanicStrategy.toTrapOutcome] at hTr
    rw [hTr] at h
    nomatch h

private theorem canonMem_unchecked_add (a b : Nat) {v : Value} {m : Memory}
    (h : runMirCall (mkUncheckedArithBody .u64 .add) 2
      (uintArgs2 .u64 a b) = .halted (.normal (v, m))) :
    m = canonInitMemory := by
  cases hB : Nat.ble (modPow2 (uintWidth .u64)) (a + b) with
  | false =>
    rw [runMirCall_unchecked_add_ok .u64 a b
      (nat_lt_of_ble_false_local hB)] at h
    injection h with hN
    injection hN with hP
    exact (congrArg Prod.snd hP).symm
  | true =>
    rw [runMirCall_unchecked_add_ub .u64 a b (Nat.le_of_ble_eq_true hB)] at h
    nomatch h

private theorem canonMem_wrapping_add (a b : Nat) {v : Value} {m : Memory}
    (h : runMirCall (mkWrappingArithBody .u64 .add) 2
      (uintArgs2 .u64 a b) = .halted (.normal (v, m))) :
    m = canonInitMemory := by
  rw [runMirCall_wrapping_add .u64 a b] at h
  injection h with hN
  injection hN with hP
  exact (congrArg Prod.snd hP).symm

private theorem canonMem_checked_sub (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64))
    {v : Value} {m : Memory}
    (h : runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
      (uintArgs2 .u64 a b) = .halted (.normal (v, m))) :
    m = canonInitMemory := by
  cases hB : Nat.ble b a with
  | true =>
    have hOk := runMirCall_checked_sub_ok .u64 .abort a b ha hb
      (Nat.le_of_ble_eq_true hB)
    dsimp only [PanicStrategy.toUnwindAction] at hOk
    rw [hOk] at h
    injection h with hN
    injection hN with hP
    exact (congrArg Prod.snd hP).symm
  | false =>
    have hTr := runMirCall_checked_sub_trap .u64 .abort a b ha hb
      (nat_lt_of_ble_false_local hB)
    dsimp only [PanicStrategy.toUnwindAction,
      PanicStrategy.toTrapOutcome] at hTr
    rw [hTr] at h
    nomatch h

private theorem canonMem_unchecked_sub (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) {v : Value} {m : Memory}
    (h : runMirCall (mkUncheckedArithBody .u64 .sub) 2
      (uintArgs2 .u64 a b) = .halted (.normal (v, m))) :
    m = canonInitMemory := by
  cases hB : Nat.ble b a with
  | true =>
    rw [runMirCall_unchecked_sub_ok .u64 a b ha
      (Nat.le_of_ble_eq_true hB)] at h
    injection h with hN
    injection hN with hP
    exact (congrArg Prod.snd hP).symm
  | false =>
    rw [runMirCall_unchecked_sub_ub .u64 a b
      (nat_lt_of_ble_false_local hB)] at h
    nomatch h

private theorem canonMem_wrapping_sub (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64))
    {v : Value} {m : Memory}
    (h : runMirCall (mkWrappingArithBody .u64 .sub) 2
      (uintArgs2 .u64 a b) = .halted (.normal (v, m))) :
    m = canonInitMemory := by
  rw [runMirCall_wrapping_sub .u64 a b ha hb] at h
  injection h with hN
  injection hN with hP
  exact (congrArg Prod.snd hP).symm

/-- End-to-end `CtxFact` -> Backend `blockOptGate` + `stepMirState` bridge for
`u64` checked addition: derives `MirOutcomeEquiv`, `MirExactOutcomeEquiv`, and
bidirectional `ITree.toPartial` equivalence by transporting the certified
`blockOptGate` `BoolCertCut` across the pointwise block correspondences. -/
theorem u64_add_ctxFact_to_stepMirState_bridge (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64))
    (hEntry : SourceEntryPre u64CheckedAddSrc (env2 a b)) :
    SemRefinesUnder (SourceEntryPre u64CheckedAddSrc)
      (evalSourceBlockUnit u64CheckedAddSrc)
      (evalCompiledBlockUnit u64UncheckedAddOpt) ∧
    MirOutcomeEquiv
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 a b)))
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u64 .add) 2
          (uintArgs2 .u64 a b))) ∧
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 a b)))
      (classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .add) 2
          (uintArgs2 .u64 a b))) ∧
    (mirCallTree (mkUncheckedArithBody .u64 .add)
        (uintArgs2 .u64 a b)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u64 .add .terminate)
        (uintArgs2 .u64 a b)).toPartial ∧
    (mirCallTree (mkCheckedArithBody .u64 .add .terminate)
      (uintArgs2 .u64 a b)).toPartial ≤
      (mirCallTree (mkUncheckedArithBody .u64 .add)
        (uintArgs2 .u64 a b)).toPartial := by
  have hCut :
      Anneal.Framework.StepWp.BoolCertCut
        (gateCheckBounded (blockOptGate 2))
        (u64CheckedAddSrc, u64UncheckedAddOpt, u64CheckedAddToUncheckedSteps) :=
    Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl
  have hLt : a + b < modPow2 (uintWidth .u64) :=
    (sourceEntryPre_u64CheckedAdd_iff a b ha hb).1 hEntry
  have hSrcDef :
      classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 a b)) ≠ .ub := by
    have hOk := runMirCall_checked_add_ok .u64 .abort a b hLt
    dsimp only [PanicStrategy.toUnwindAction] at hOk
    rw [hOk]
    intro h
    nomatch h
  have hEq :=
    blockOptGate_cut_transports_to_mirExecState_equiv 2
      u64CheckedAddSrc u64UncheckedAddOpt u64CheckedAddToUncheckedSteps hCut
      (env2 a b) hEntry
      (u64CheckedAddSrc_corresponds_stepMirState a b ha hb)
      (u64UncheckedAddOpt_corresponds_stepMirState a b ha hb) hSrcDef
  have hTree :=
    blockOptGate_cut_transports_to_mirCallTree_toPartial_equiv 2
      u64CheckedAddSrc u64UncheckedAddOpt u64CheckedAddToUncheckedSteps hCut
      (env2 a b) hEntry
      (u64CheckedAddSrc_corresponds_stepMirState a b ha hb)
      (u64UncheckedAddOpt_corresponds_stepMirState a b ha hb) hSrcDef
      (fun _ _ _ _ hS hT =>
        (canonMem_checked_add a b hS).trans
          (canonMem_unchecked_add a b hT).symm)
  exact ⟨certGateCut_sound (blockOptGate 2) True.intro hCut,
    hEq.2, hEq.1, hTree.1, hTree.2⟩

/-- End-to-end `CtxFact` -> Backend `blockOptGate` + `stepMirState` bridge for
`u64` checked subtraction: derives `MirOutcomeEquiv`, `MirExactOutcomeEquiv`,
and bidirectional `ITree.toPartial` equivalence via certificate transport. -/
theorem u64_sub_ctxFact_to_stepMirState_bridge (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64))
    (hEntry : SourceEntryPre u64CheckedSubSrc (env2 a b)) :
    SemRefinesUnder (SourceEntryPre u64CheckedSubSrc)
      (evalSourceBlockUnit u64CheckedSubSrc)
      (evalCompiledBlockUnit u64UncheckedSubOpt) ∧
    MirOutcomeEquiv
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 a b)))
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u64 .sub) 2
          (uintArgs2 .u64 a b))) ∧
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 a b)))
      (classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .sub) 2
          (uintArgs2 .u64 a b))) ∧
    (mirCallTree (mkUncheckedArithBody .u64 .sub)
        (uintArgs2 .u64 a b)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u64 .sub .terminate)
        (uintArgs2 .u64 a b)).toPartial ∧
    (mirCallTree (mkCheckedArithBody .u64 .sub .terminate)
      (uintArgs2 .u64 a b)).toPartial ≤
      (mirCallTree (mkUncheckedArithBody .u64 .sub)
        (uintArgs2 .u64 a b)).toPartial := by
  have hCut :
      Anneal.Framework.StepWp.BoolCertCut
        (gateCheckBounded (blockOptGate 2))
        (u64CheckedSubSrc, u64UncheckedSubOpt, u64CheckedSubToUncheckedSteps) :=
    Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl
  have hLe : b ≤ a := (sourceEntryPre_u64CheckedSub_iff a b ha hb).1 hEntry
  have hSrcDef :
      classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 a b)) ≠ .ub := by
    have hOk := runMirCall_checked_sub_ok .u64 .abort a b ha hb hLe
    dsimp only [PanicStrategy.toUnwindAction] at hOk
    rw [hOk]
    intro h
    nomatch h
  have hEq :=
    blockOptGate_cut_transports_to_mirExecState_equiv 2
      u64CheckedSubSrc u64UncheckedSubOpt u64CheckedSubToUncheckedSteps hCut
      (env2 a b) hEntry
      (u64CheckedSubSrc_corresponds_stepMirState a b ha hb)
      (u64UncheckedSubOpt_corresponds_stepMirState a b ha hb) hSrcDef
  have hTree :=
    blockOptGate_cut_transports_to_mirCallTree_toPartial_equiv 2
      u64CheckedSubSrc u64UncheckedSubOpt u64CheckedSubToUncheckedSteps hCut
      (env2 a b) hEntry
      (u64CheckedSubSrc_corresponds_stepMirState a b ha hb)
      (u64UncheckedSubOpt_corresponds_stepMirState a b ha hb) hSrcDef
      (fun _ _ _ _ hS hT =>
        (canonMem_checked_sub a b ha hb hS).trans
          (canonMem_unchecked_sub a b ha hT).symm)
  exact ⟨certGateCut_sound (blockOptGate 2) True.intro hCut,
    hEq.2, hEq.1, hTree.1, hTree.2⟩

/-- Unified `farkasMirGate` `BoolCertCut` -> `CtxFact` + `blockOptGate` +
`stepMirState` capstone bridge for `u64` addition. -/
theorem u64_add_farkasMirGate_to_stepMirState_bridge (maxSteps : Nat)
    (hyps : List NatCutIneq) (lhsExpr rhsExpr : NatLinExpr)
    (cert : FarkasMirCert)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (farkasMirGate maxSteps))
      (.uintAddNoOverflow .u64 hyps lhsExpr rhsExpr, (), cert))
    (env : List Nat) :
    HypsImp (NatCutIneq.holds env) hyps
      (SourceEntryPre u64CheckedAddSrc
          (env2 (lhsExpr.eval env) (rhsExpr.eval env)) ∧
       SemRefinesUnder (SourceEntryPre u64CheckedAddSrc)
          (evalSourceBlockUnit u64CheckedAddSrc)
          (evalCompiledBlockUnit u64UncheckedAddOpt) ∧
       MirOutcomeEquiv
          (classifyMirExecState .abort
            (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))))
          (classifyMirExecState .abort
            (runMirCall (mkUncheckedArithBody .u64 .add) 2
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env)))) ∧
       MirExactOutcomeEquiv
          (classifyMirExecStateExact
            (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))))
          (classifyMirExecStateExact
            (runMirCall (mkUncheckedArithBody .u64 .add) 2
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env)))) ∧
       (mirCallTree (mkUncheckedArithBody .u64 .add)
         (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))).toPartial ≤
         (mirCallTree (mkCheckedArithBody .u64 .add .terminate)
           (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))).toPartial) :=
  hypsImp_concl_mono (fun hFarkas => by
    have hSumLt :
        lhsExpr.eval env + rhsExpr.eval env < modPow2 (uintWidth .u64) :=
      hFarkas.1
    have hLhsLt : lhsExpr.eval env < modPow2 (uintWidth .u64) :=
      Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hSumLt
    have hRhsLt : rhsExpr.eval env < modPow2 (uintWidth .u64) :=
      Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hSumLt
    have hEntry :
        SourceEntryPre u64CheckedAddSrc
          (env2 (lhsExpr.eval env) (rhsExpr.eval env)) :=
      (sourceEntryPre_u64CheckedAdd_iff _ _ hLhsLt hRhsLt).2 hSumLt
    have hBr := u64_add_ctxFact_to_stepMirState_bridge _ _ hLhsLt hRhsLt hEntry
    exact ⟨hEntry, hBr.1, hBr.2.1, hBr.2.2.1, hBr.2.2.2.1⟩)
    (farkasMirGate_cut_sound maxSteps
      (.uintAddNoOverflow .u64 hyps lhsExpr rhsExpr) cert hCut
      env [] canonInitMemory)

/-- Unified `farkasMirGate` `BoolCertCut` -> `CtxFact` + `blockOptGate` +
`stepMirState` capstone bridge for certified `u64` subtraction. -/
theorem u64_sub_farkasMirGate_to_stepMirState_bridge (maxSteps : Nat)
    (hyps : List NatCutIneq) (lhsExpr rhsExpr : NatLinExpr)
    (cert : FarkasMirCert)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (farkasMirGate maxSteps))
      (.uintSubNoUnderflowCertified .u64 hyps lhsExpr rhsExpr, (), cert))
    (env : List Nat) :
    HypsImp (NatCutIneq.holds env) hyps
      (SourceEntryPre u64CheckedSubSrc
          (env2 (lhsExpr.eval env) (rhsExpr.eval env)) ∧
       SemRefinesUnder (SourceEntryPre u64CheckedSubSrc)
          (evalSourceBlockUnit u64CheckedSubSrc)
          (evalCompiledBlockUnit u64UncheckedSubOpt) ∧
       MirOutcomeEquiv
          (classifyMirExecState .abort
            (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))))
          (classifyMirExecState .abort
            (runMirCall (mkUncheckedArithBody .u64 .sub) 2
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env)))) ∧
       MirExactOutcomeEquiv
          (classifyMirExecStateExact
            (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))))
          (classifyMirExecStateExact
            (runMirCall (mkUncheckedArithBody .u64 .sub) 2
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env)))) ∧
       (mirCallTree (mkUncheckedArithBody .u64 .sub)
         (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))).toPartial ≤
         (mirCallTree (mkCheckedArithBody .u64 .sub .terminate)
           (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))).toPartial) :=
  hypsImp_concl_mono (fun hFarkas => by
    have hLhsLt : lhsExpr.eval env < modPow2 (uintWidth .u64) := hFarkas.1
    have hLe : rhsExpr.eval env ≤ lhsExpr.eval env := hFarkas.2.1
    have hRhsLt : rhsExpr.eval env < modPow2 (uintWidth .u64) :=
      Nat.lt_of_le_of_lt hLe hLhsLt
    have hEntry :
        SourceEntryPre u64CheckedSubSrc
          (env2 (lhsExpr.eval env) (rhsExpr.eval env)) :=
      (sourceEntryPre_u64CheckedSub_iff _ _ hLhsLt hRhsLt).2 hLe
    have hBr := u64_sub_ctxFact_to_stepMirState_bridge _ _ hLhsLt hRhsLt hEntry
    exact ⟨hEntry, hBr.1, hBr.2.1, hBr.2.2.1, hBr.2.2.2.1⟩)
    (farkasMirGate_cut_sound maxSteps
      (.uintSubNoUnderflowCertified .u64 hyps lhsExpr rhsExpr) cert hCut
      env [] canonInitMemory)

/-- Unified `natCutIdxGate` `BoolCertCut` -> `CtxFact` + `blockOptGate` +
`stepMirState` capstone bridge for `u64` addition. -/
theorem u64_add_natCutIdxGate_to_stepMirState_bridge (maxSteps : Nat)
    (hyps : List NatCutIneq) (lhsExpr rhsExpr : NatLinExpr)
    (steps : List CutStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (natCutIdxGate maxSteps))
      (⟨hyps, ⟨.add (.add lhsExpr rhsExpr) (.cst 1),
        .cst (modPow2 (uintWidth .u64))⟩⟩, (), steps))
    (env : List Nat) :
    HypsImp (NatCutIneq.holds env) hyps
      (SourceEntryPre u64CheckedAddSrc
          (env2 (lhsExpr.eval env) (rhsExpr.eval env)) ∧
       SemRefinesUnder (SourceEntryPre u64CheckedAddSrc)
          (evalSourceBlockUnit u64CheckedAddSrc)
          (evalCompiledBlockUnit u64UncheckedAddOpt) ∧
       MirOutcomeEquiv
          (classifyMirExecState .abort
            (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))))
          (classifyMirExecState .abort
            (runMirCall (mkUncheckedArithBody .u64 .add) 2
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env)))) ∧
       MirExactOutcomeEquiv
          (classifyMirExecStateExact
            (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))))
          (classifyMirExecStateExact
            (runMirCall (mkUncheckedArithBody .u64 .add) 2
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env)))) ∧
       (mirCallTree (mkUncheckedArithBody .u64 .add)
         (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))).toPartial ≤
         (mirCallTree (mkCheckedArithBody .u64 .add .terminate)
           (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))).toPartial) :=
  hypsImp_concl_mono (fun hFarkas => by
    have hSumLt :
        lhsExpr.eval env + rhsExpr.eval env < modPow2 (uintWidth .u64) :=
      hFarkas.1
    have hLhsLt : lhsExpr.eval env < modPow2 (uintWidth .u64) :=
      Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hSumLt
    have hRhsLt : rhsExpr.eval env < modPow2 (uintWidth .u64) :=
      Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hSumLt
    have hEntry :
        SourceEntryPre u64CheckedAddSrc
          (env2 (lhsExpr.eval env) (rhsExpr.eval env)) :=
      (sourceEntryPre_u64CheckedAdd_iff _ _ hLhsLt hRhsLt).2 hSumLt
    have hBr := u64_add_ctxFact_to_stepMirState_bridge _ _ hLhsLt hRhsLt hEntry
    exact ⟨hEntry, hBr.1, hBr.2.1, hBr.2.2.1, hBr.2.2.2.1⟩)
    (natCutIdxGate_discharges_uint_add_no_overflow maxSteps .u64 hyps lhsExpr
      rhsExpr steps hCut env [] canonInitMemory)

/-- Unified `natCutIdxGate` `BoolCertCut` -> `CtxFact` + `blockOptGate` +
`stepMirState` capstone bridge for certified `u64` subtraction. -/
theorem u64_sub_natCutIdxGate_to_stepMirState_bridge (maxSteps : Nat)
    (hyps : List NatCutIneq) (lhsExpr rhsExpr : NatLinExpr)
    (stepsLe stepsRange : List CutStep)
    (hCutLe : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (natCutIdxGate maxSteps))
      (⟨hyps, ⟨rhsExpr, lhsExpr⟩⟩, (), stepsLe))
    (hCutRange : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (natCutIdxGate maxSteps))
      (⟨hyps, ⟨.add lhsExpr (.cst 1), .cst (modPow2 (uintWidth .u64))⟩⟩,
        (), stepsRange))
    (env : List Nat) :
    HypsImp (NatCutIneq.holds env) hyps
      (SourceEntryPre u64CheckedSubSrc
          (env2 (lhsExpr.eval env) (rhsExpr.eval env)) ∧
       SemRefinesUnder (SourceEntryPre u64CheckedSubSrc)
          (evalSourceBlockUnit u64CheckedSubSrc)
          (evalCompiledBlockUnit u64UncheckedSubOpt) ∧
       MirOutcomeEquiv
          (classifyMirExecState .abort
            (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))))
          (classifyMirExecState .abort
            (runMirCall (mkUncheckedArithBody .u64 .sub) 2
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env)))) ∧
       MirExactOutcomeEquiv
          (classifyMirExecStateExact
            (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))))
          (classifyMirExecStateExact
            (runMirCall (mkUncheckedArithBody .u64 .sub) 2
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env)))) ∧
       (mirCallTree (mkUncheckedArithBody .u64 .sub)
         (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))).toPartial ≤
         (mirCallTree (mkCheckedArithBody .u64 .sub .terminate)
           (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))).toPartial) :=
  hypsImp_concl_mono (fun hFarkas => by
    have hLhsLt : lhsExpr.eval env < modPow2 (uintWidth .u64) := hFarkas.1
    have hLe : rhsExpr.eval env ≤ lhsExpr.eval env := hFarkas.2.1
    have hRhsLt : rhsExpr.eval env < modPow2 (uintWidth .u64) :=
      Nat.lt_of_le_of_lt hLe hLhsLt
    have hEntry :
        SourceEntryPre u64CheckedSubSrc
          (env2 (lhsExpr.eval env) (rhsExpr.eval env)) :=
      (sourceEntryPre_u64CheckedSub_iff _ _ hLhsLt hRhsLt).2 hLe
    have hBr := u64_sub_ctxFact_to_stepMirState_bridge _ _ hLhsLt hRhsLt hEntry
    exact ⟨hEntry, hBr.1, hBr.2.1, hBr.2.2.1, hBr.2.2.2.1⟩)
    (natCutIdxGate_discharges_uint_sub_no_underflow_certified maxSteps .u64
      hyps lhsExpr rhsExpr stepsLe stepsRange hCutLe hCutRange
      env [] canonInitMemory)

/-! ### 4.3b Certificate Transport: ANY Accepted `blockOptGate` Witness

The bridges above pair the canonical `blockOptGate` certificate with a MIR
equivalence proved from the arithmetic side condition. The theorems below
make the Backend certificate load-bearing: the refinement between real
`stepMirState` runs is derived from an arbitrary accepted `blockOptGate`
`BoolCertCut` through the pointwise block correspondences. -/

/-- `u64` checked addition: ANY certificate `blockOptGate` accepts for eliding
`GuardCond.addNoOverflow 0 1` to `addNuw` transports to an equivalence of the
real `stepMirState` runs. Both directions come from the gate-derived
refinement, because the checked run is defined under the discharged fact. -/
theorem u64_add_blockOptGate_cut_to_stepMirState (maxStepsPerNode : Nat)
    (steps : List DagStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (blockOptGate maxStepsPerNode))
      (u64CheckedAddSrc, u64UncheckedAddOpt, steps))
    (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64))
    (hEntry : SourceEntryPre u64CheckedAddSrc (env2 a b)) :
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 a b)))
      (classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .add) 2
          (uintArgs2 .u64 a b))) ∧
    MirOutcomeEquiv
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 a b)))
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u64 .add) 2
          (uintArgs2 .u64 a b))) := by
  have hLt : a + b < modPow2 (uintWidth .u64) :=
    (sourceEntryPre_u64CheckedAdd_iff a b ha hb).1 hEntry
  have hOk := runMirCall_checked_add_ok .u64 .abort a b hLt
  dsimp only [PanicStrategy.toUnwindAction] at hOk
  refine blockOptGate_cut_transports_to_mirExecState_equiv maxStepsPerNode
    u64CheckedAddSrc u64UncheckedAddOpt steps hCut (env2 a b) hEntry
    (u64CheckedAddSrc_corresponds_stepMirState a b ha hb)
    (u64UncheckedAddOpt_corresponds_stepMirState a b ha hb) ?_
  rw [hOk]
  intro h
  nomatch h

/-- `u64` checked addition to the WRAPPING target: ANY accepted `blockOptGate`
certificate transports to a full `stepMirState` equivalence, so under the
discharged `CtxFact` the checked run matches `mkWrappingArithBody` in both
directions (no abort is turned into a silent wrap). -/
theorem u64_add_blockOptGate_cut_to_stepMirState_wrapping
    (maxStepsPerNode : Nat) (steps : List DagStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (blockOptGate maxStepsPerNode))
      (u64CheckedAddSrc, u64WrappingAddOpt, steps))
    (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64))
    (hEntry : SourceEntryPre u64CheckedAddSrc (env2 a b)) :
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 a b)))
      (classifyMirExecStateExact
        (runMirCall (mkWrappingArithBody .u64 .add) 2
          (uintArgs2 .u64 a b))) ∧
    MirOutcomeEquiv
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 a b)))
      (classifyMirExecState .abort
        (runMirCall (mkWrappingArithBody .u64 .add) 2
          (uintArgs2 .u64 a b))) := by
  have hLt : a + b < modPow2 (uintWidth .u64) :=
    (sourceEntryPre_u64CheckedAdd_iff a b ha hb).1 hEntry
  have hOk := runMirCall_checked_add_ok .u64 .abort a b hLt
  dsimp only [PanicStrategy.toUnwindAction] at hOk
  refine blockOptGate_cut_transports_to_mirExecState_equiv maxStepsPerNode
    u64CheckedAddSrc u64WrappingAddOpt steps hCut (env2 a b) hEntry
    (u64CheckedAddSrc_corresponds_stepMirState a b ha hb)
    (u64WrappingAddOpt_corresponds_stepMirState a b ha hb) ?_
  rw [hOk]
  intro h
  nomatch h

/-- `u64` checked subtraction: ANY certificate `blockOptGate` accepts for
eliding `GuardCond.subNoUnderflow 0 1` to `subNuw` transports to an
equivalence of the real `stepMirState` runs. Both directions come from the
gate-derived refinement. -/
theorem u64_sub_blockOptGate_cut_to_stepMirState (maxStepsPerNode : Nat)
    (steps : List DagStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (blockOptGate maxStepsPerNode))
      (u64CheckedSubSrc, u64UncheckedSubOpt, steps))
    (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64))
    (hEntry : SourceEntryPre u64CheckedSubSrc (env2 a b)) :
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 a b)))
      (classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .sub) 2
          (uintArgs2 .u64 a b))) ∧
    MirOutcomeEquiv
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 a b)))
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u64 .sub) 2
          (uintArgs2 .u64 a b))) := by
  have hLe : b ≤ a := (sourceEntryPre_u64CheckedSub_iff a b ha hb).1 hEntry
  have hOk := runMirCall_checked_sub_ok .u64 .abort a b ha hb hLe
  dsimp only [PanicStrategy.toUnwindAction] at hOk
  refine blockOptGate_cut_transports_to_mirExecState_equiv maxStepsPerNode
    u64CheckedSubSrc u64UncheckedSubOpt steps hCut (env2 a b) hEntry
    (u64CheckedSubSrc_corresponds_stepMirState a b ha hb)
    (u64UncheckedSubOpt_corresponds_stepMirState a b ha hb) ?_
  rw [hOk]
  intro h
  nomatch h

/-- `u64` checked subtraction to the WRAPPING target: ANY accepted
`blockOptGate` certificate transports to a full `stepMirState` equivalence. -/
theorem u64_sub_blockOptGate_cut_to_stepMirState_wrapping
    (maxStepsPerNode : Nat) (steps : List DagStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (blockOptGate maxStepsPerNode))
      (u64CheckedSubSrc, u64WrappingSubOpt, steps))
    (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64))
    (hEntry : SourceEntryPre u64CheckedSubSrc (env2 a b)) :
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 a b)))
      (classifyMirExecStateExact
        (runMirCall (mkWrappingArithBody .u64 .sub) 2
          (uintArgs2 .u64 a b))) ∧
    MirOutcomeEquiv
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 a b)))
      (classifyMirExecState .abort
        (runMirCall (mkWrappingArithBody .u64 .sub) 2
          (uintArgs2 .u64 a b))) := by
  have hLe : b ≤ a := (sourceEntryPre_u64CheckedSub_iff a b ha hb).1 hEntry
  have hOk := runMirCall_checked_sub_ok .u64 .abort a b ha hb hLe
  dsimp only [PanicStrategy.toUnwindAction] at hOk
  refine blockOptGate_cut_transports_to_mirExecState_equiv maxStepsPerNode
    u64CheckedSubSrc u64WrappingSubOpt steps hCut (env2 a b) hEntry
    (u64CheckedSubSrc_corresponds_stepMirState a b ha hb)
    (u64WrappingSubOpt_corresponds_stepMirState a b ha hb) ?_
  rw [hOk]
  intro h
  nomatch h

/-- Fully chained capstone for `u64` addition through `natCutIdxGate` AND ANY
accepted `blockOptGate` `BoolCertCut`. -/
theorem u64_add_natCutIdx_and_blockOpt_cuts_to_stepMirState
    (maxSteps maxStepsPerNode : Nat)
    (hyps : List NatCutIneq) (lhsExpr rhsExpr : NatLinExpr)
    (cutSteps : List CutStep) (dagSteps : List DagStep)
    (hIdx : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (natCutIdxGate maxSteps))
      (⟨hyps, ⟨.add (.add lhsExpr rhsExpr) (.cst 1),
        .cst (modPow2 (uintWidth .u64))⟩⟩, (), cutSteps))
    (hBlock : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (blockOptGate maxStepsPerNode))
      (u64CheckedAddSrc, u64UncheckedAddOpt, dagSteps))
    (env : List Nat) :
    HypsImp (NatCutIneq.holds env) hyps
      (MirExactOutcomeEquiv
          (classifyMirExecStateExact
            (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))))
          (classifyMirExecStateExact
            (runMirCall (mkUncheckedArithBody .u64 .add) 2
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env)))) ∧
       MirOutcomeEquiv
          (classifyMirExecState .abort
            (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))))
          (classifyMirExecState .abort
            (runMirCall (mkUncheckedArithBody .u64 .add) 2
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))))) :=
  hypsImp_concl_mono (fun hDen => by
    have hSumLt :
        lhsExpr.eval env + rhsExpr.eval env < modPow2 (uintWidth .u64) :=
      hDen.1
    have hLhsLt : lhsExpr.eval env < modPow2 (uintWidth .u64) :=
      Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hSumLt
    have hRhsLt : rhsExpr.eval env < modPow2 (uintWidth .u64) :=
      Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hSumLt
    exact u64_add_blockOptGate_cut_to_stepMirState maxStepsPerNode dagSteps
      hBlock _ _ hLhsLt hRhsLt
      ((sourceEntryPre_u64CheckedAdd_iff _ _ hLhsLt hRhsLt).2 hSumLt))
    (natCutIdxGate_discharges_uint_add_no_overflow maxSteps .u64 hyps lhsExpr
      rhsExpr cutSteps hIdx env [] canonInitMemory)

/-- Fully chained capstone for certified `u64` subtraction through
`natCutIdxGate` AND ANY accepted `blockOptGate` `BoolCertCut`. -/
theorem u64_sub_natCutIdx_and_blockOpt_cuts_to_stepMirState
    (maxSteps maxStepsPerNode : Nat)
    (hyps : List NatCutIneq) (lhsExpr rhsExpr : NatLinExpr)
    (stepsLe stepsRange : List CutStep) (dagSteps : List DagStep)
    (hIdxLe : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (natCutIdxGate maxSteps))
      (⟨hyps, ⟨rhsExpr, lhsExpr⟩⟩, (), stepsLe))
    (hIdxRange : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (natCutIdxGate maxSteps))
      (⟨hyps, ⟨.add lhsExpr (.cst 1), .cst (modPow2 (uintWidth .u64))⟩⟩,
        (), stepsRange))
    (hBlock : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (blockOptGate maxStepsPerNode))
      (u64CheckedSubSrc, u64UncheckedSubOpt, dagSteps))
    (env : List Nat) :
    HypsImp (NatCutIneq.holds env) hyps
      (MirExactOutcomeEquiv
          (classifyMirExecStateExact
            (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))))
          (classifyMirExecStateExact
            (runMirCall (mkUncheckedArithBody .u64 .sub) 2
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env)))) ∧
       MirOutcomeEquiv
          (classifyMirExecState .abort
            (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))))
          (classifyMirExecState .abort
            (runMirCall (mkUncheckedArithBody .u64 .sub) 2
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))))) :=
  hypsImp_concl_mono (fun hDen => by
    have hLhsLt : lhsExpr.eval env < modPow2 (uintWidth .u64) := hDen.1
    have hLe : rhsExpr.eval env ≤ lhsExpr.eval env := hDen.2.1
    have hRhsLt : rhsExpr.eval env < modPow2 (uintWidth .u64) :=
      Nat.lt_of_le_of_lt hLe hLhsLt
    exact u64_sub_blockOptGate_cut_to_stepMirState maxStepsPerNode dagSteps
      hBlock _ _ hLhsLt hRhsLt
      ((sourceEntryPre_u64CheckedSub_iff _ _ hLhsLt hRhsLt).2 hLe))
    (natCutIdxGate_discharges_uint_sub_no_underflow_certified maxSteps .u64
      hyps lhsExpr rhsExpr stepsLe stepsRange hIdxLe hIdxRange
      env [] canonInitMemory)

/-- Unchecked (`addNuw`) source block with no guards and no contextual facts,
used to exercise genuinely asymmetric `.ub ⊑ .ret` certificate transport via
`.dirRule .dropAddNuw`. -/
def u64UncheckedAddSrc : SourceBlockUnit :=
  { guards := []
    arena := u64CheckedAddArena
    srcRetId := 3
    candidates := [] }

/-- Genuinely asymmetric `.ub ⊑ .ret` certificate transport through
`blockOptGate`: dropping `nuw` (`.dirRule .dropAddNuw`) refines
`mkUncheckedArithBody .u64 .add` to `mkWrappingArithBody .u64 .add` for ALL
`u64`-ranged `a, b` (in `MirExactOutcomeRefines`, `MirOutcomeRefines`, and
Layer 1A `ITree.toPartial`), and at `(u64Max, 1)` the source faults `.ub` while
the target returns `0` so the converse strictly fails. -/
theorem u64_addNuw_to_addWrap_asymmetric_ub_transport (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64)) :
    MirExactOutcomeRefines
      (classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .add) 2 (uintArgs2 .u64 a b)))
      (classifyMirExecStateExact
        (runMirCall (mkWrappingArithBody .u64 .add) 2 (uintArgs2 .u64 a b))) ∧
    MirOutcomeRefines
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u64 .add) 2 (uintArgs2 .u64 a b)))
      (classifyMirExecState .abort
        (runMirCall (mkWrappingArithBody .u64 .add) 2 (uintArgs2 .u64 a b))) ∧
    (mirCallTree (mkWrappingArithBody .u64 .add)
        (uintArgs2 .u64 a b)).toPartial ≤
      (mirCallTree (mkUncheckedArithBody .u64 .add)
        (uintArgs2 .u64 a b)).toPartial ∧
    ¬ MirExactOutcomeRefines
        (classifyMirExecStateExact
          (runMirCall (mkWrappingArithBody .u64 .add) 2
            (uintArgs2 .u64 u64Max 1)))
        (classifyMirExecStateExact
          (runMirCall (mkUncheckedArithBody .u64 .add) 2
            (uintArgs2 .u64 u64Max 1))) := by
  have hCut :
      Anneal.Framework.StepWp.BoolCertCut
        (gateCheckBounded (blockOptGate 2))
        (u64UncheckedAddSrc, u64WrappingAddOpt,
          [.dirRule .dropAddNuw [0, 1] 3 2]) :=
    Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl
  have hEntry : SourceEntryPre u64UncheckedAddSrc (env2 a b) :=
    fun _ _ h => nomatch h
  have hTr :=
    blockOptGate_cut_transports_to_mirExecState 2
      u64UncheckedAddSrc u64WrappingAddOpt [.dirRule .dropAddNuw [0, 1] 3 2]
      hCut (env2 a b) hEntry
      (u64UncheckedAddOpt_corresponds_stepMirState a b ha hb)
      (u64WrappingAddOpt_corresponds_stepMirState a b ha hb)
  have hPartial :=
    blockOptGate_cut_transports_to_mirCallTree_toPartial 2
      u64UncheckedAddSrc u64WrappingAddOpt [.dirRule .dropAddNuw [0, 1] 3 2]
      hCut (env2 a b) hEntry
      (u64UncheckedAddOpt_corresponds_stepMirState a b ha hb)
      (u64WrappingAddOpt_corresponds_stepMirState a b ha hb)
      (fun _ _ _ _ hS hT =>
        (canonMem_unchecked_add a b hS).trans
          (canonMem_wrapping_add a b hT).symm)
  have hOv : modPow2 (uintWidth .u64) ≤ u64Max + 1 := Nat.le_of_ble_eq_true rfl
  have hMirU := runMirCall_unchecked_add_ub .u64 u64Max 1 hOv
  have hMirW := runMirCall_wrapping_add .u64 u64Max 1
  refine ⟨hTr.1, hTr.2, hPartial, ?_⟩
  rw [hMirW, hMirU]
  intro h
  exact False.elim h

/-- Unchecked (`subNuw`) source block with no guards and no contextual facts,
used to exercise genuinely asymmetric `.ub ⊑ .ret` certificate transport via
`.dirRule .dropSubNuw`. -/
def u64UncheckedSubSrc : SourceBlockUnit :=
  { guards := []
    arena := u64CheckedSubArena
    srcRetId := 3
    candidates := [] }

/-- Genuinely asymmetric `.ub ⊑ .ret` certificate transport for subtraction
through `blockOptGate`: dropping `nuw` (`.dirRule .dropSubNuw`) refines
`mkUncheckedArithBody .u64 .sub` to `mkWrappingArithBody .u64 .sub` for ALL
`u64`-ranged `a, b` (in `MirExactOutcomeRefines`, `MirOutcomeRefines`, and
Layer 1A `ITree.toPartial`), and at `(0, 1)` the source faults `.ub` while the
target returns `u64Max` so the converse strictly fails. -/
theorem u64_subNuw_to_subWrap_asymmetric_ub_transport (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64)) :
    MirExactOutcomeRefines
      (classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .sub) 2 (uintArgs2 .u64 a b)))
      (classifyMirExecStateExact
        (runMirCall (mkWrappingArithBody .u64 .sub) 2 (uintArgs2 .u64 a b))) ∧
    MirOutcomeRefines
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u64 .sub) 2 (uintArgs2 .u64 a b)))
      (classifyMirExecState .abort
        (runMirCall (mkWrappingArithBody .u64 .sub) 2 (uintArgs2 .u64 a b))) ∧
    (mirCallTree (mkWrappingArithBody .u64 .sub)
        (uintArgs2 .u64 a b)).toPartial ≤
      (mirCallTree (mkUncheckedArithBody .u64 .sub)
        (uintArgs2 .u64 a b)).toPartial ∧
    ¬ MirExactOutcomeRefines
        (classifyMirExecStateExact
          (runMirCall (mkWrappingArithBody .u64 .sub) 2
            (uintArgs2 .u64 0 1)))
        (classifyMirExecStateExact
          (runMirCall (mkUncheckedArithBody .u64 .sub) 2
            (uintArgs2 .u64 0 1))) := by
  have hCut :
      Anneal.Framework.StepWp.BoolCertCut
        (gateCheckBounded (blockOptGate 2))
        (u64UncheckedSubSrc, u64WrappingSubOpt,
          [.dirRule .dropSubNuw [0, 1] 3 2]) :=
    Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl
  have hEntry : SourceEntryPre u64UncheckedSubSrc (env2 a b) :=
    fun _ _ h => nomatch h
  have hTr :=
    blockOptGate_cut_transports_to_mirExecState 2
      u64UncheckedSubSrc u64WrappingSubOpt [.dirRule .dropSubNuw [0, 1] 3 2]
      hCut (env2 a b) hEntry
      (u64UncheckedSubOpt_corresponds_stepMirState a b ha hb)
      (u64WrappingSubOpt_corresponds_stepMirState a b ha hb)
  have hPartial :=
    blockOptGate_cut_transports_to_mirCallTree_toPartial 2
      u64UncheckedSubSrc u64WrappingSubOpt [.dirRule .dropSubNuw [0, 1] 3 2]
      hCut (env2 a b) hEntry
      (u64UncheckedSubOpt_corresponds_stepMirState a b ha hb)
      (u64WrappingSubOpt_corresponds_stepMirState a b ha hb)
      (fun _ _ _ _ hS hT =>
        (canonMem_unchecked_sub a b ha hS).trans
          (canonMem_wrapping_sub a b ha hb hT).symm)
  have h0Lt : 0 < modPow2 (uintWidth .u64) := u64Mod_pos
  have h1Lt : 1 < modPow2 (uintWidth .u64) := Nat.le_of_ble_eq_true rfl
  have hMirU := runMirCall_unchecked_sub_ub .u64 0 1 (Nat.le_of_ble_eq_true rfl)
  have hMirW := runMirCall_wrapping_sub .u64 0 1 h0Lt h1Lt
  refine ⟨hTr.1, hTr.2, hPartial, ?_⟩
  rw [hMirW, hMirU]
  intro h
  exact False.elim h

/-- Fully chained capstone for `u64` addition through BOTH gates: a
`farkasMirGate` `BoolCertCut` discharges the `CtxFact` entry precondition, and
ANY `blockOptGate` `BoolCertCut` then transports the guard elision to the real
`stepMirState` runs. -/
theorem u64_add_farkas_and_blockOpt_cuts_to_stepMirState
    (maxSteps maxStepsPerNode : Nat)
    (hyps : List NatCutIneq) (lhsExpr rhsExpr : NatLinExpr)
    (cert : FarkasMirCert) (steps : List DagStep)
    (hFarkas : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (farkasMirGate maxSteps))
      (.uintAddNoOverflow .u64 hyps lhsExpr rhsExpr, (), cert))
    (hBlock : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (blockOptGate maxStepsPerNode))
      (u64CheckedAddSrc, u64UncheckedAddOpt, steps))
    (env : List Nat) :
    HypsImp (NatCutIneq.holds env) hyps
      (MirExactOutcomeEquiv
          (classifyMirExecStateExact
            (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))))
          (classifyMirExecStateExact
            (runMirCall (mkUncheckedArithBody .u64 .add) 2
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env)))) ∧
       MirOutcomeEquiv
          (classifyMirExecState .abort
            (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))))
          (classifyMirExecState .abort
            (runMirCall (mkUncheckedArithBody .u64 .add) 2
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))))) :=
  hypsImp_concl_mono (fun hDen => by
    have hSumLt :
        lhsExpr.eval env + rhsExpr.eval env < modPow2 (uintWidth .u64) :=
      hDen.1
    have hLhsLt : lhsExpr.eval env < modPow2 (uintWidth .u64) :=
      Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hSumLt
    have hRhsLt : rhsExpr.eval env < modPow2 (uintWidth .u64) :=
      Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hSumLt
    exact u64_add_blockOptGate_cut_to_stepMirState maxStepsPerNode steps
      hBlock _ _ hLhsLt hRhsLt
      ((sourceEntryPre_u64CheckedAdd_iff _ _ hLhsLt hRhsLt).2 hSumLt))
    (farkasMirGate_cut_sound maxSteps
      (.uintAddNoOverflow .u64 hyps lhsExpr rhsExpr) cert hFarkas
      env [] canonInitMemory)

/-- Fully chained capstone for certified `u64` subtraction through BOTH
gates: a `farkasMirGate` `BoolCertCut` discharges the `CtxFact` entry
precondition, and ANY `blockOptGate` `BoolCertCut` then transports the guard
elision to the real `stepMirState` runs. -/
theorem u64_sub_farkas_and_blockOpt_cuts_to_stepMirState
    (maxSteps maxStepsPerNode : Nat)
    (hyps : List NatCutIneq) (lhsExpr rhsExpr : NatLinExpr)
    (cert : FarkasMirCert) (steps : List DagStep)
    (hFarkas : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (farkasMirGate maxSteps))
      (.uintSubNoUnderflowCertified .u64 hyps lhsExpr rhsExpr, (), cert))
    (hBlock : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (blockOptGate maxStepsPerNode))
      (u64CheckedSubSrc, u64UncheckedSubOpt, steps))
    (env : List Nat) :
    HypsImp (NatCutIneq.holds env) hyps
      (MirExactOutcomeEquiv
          (classifyMirExecStateExact
            (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))))
          (classifyMirExecStateExact
            (runMirCall (mkUncheckedArithBody .u64 .sub) 2
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env)))) ∧
       MirOutcomeEquiv
          (classifyMirExecState .abort
            (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))))
          (classifyMirExecState .abort
            (runMirCall (mkUncheckedArithBody .u64 .sub) 2
              (uintArgs2 .u64 (lhsExpr.eval env) (rhsExpr.eval env))))) :=
  hypsImp_concl_mono (fun hDen => by
    have hLhsLt : lhsExpr.eval env < modPow2 (uintWidth .u64) := hDen.1
    have hLe : rhsExpr.eval env ≤ lhsExpr.eval env := hDen.2.1
    have hRhsLt : rhsExpr.eval env < modPow2 (uintWidth .u64) :=
      Nat.lt_of_le_of_lt hLe hLhsLt
    exact u64_sub_blockOptGate_cut_to_stepMirState maxStepsPerNode steps
      hBlock _ _ hLhsLt hRhsLt
      ((sourceEntryPre_u64CheckedSub_iff _ _ hLhsLt hRhsLt).2 hLe))
    (farkasMirGate_cut_sound maxSteps
      (.uintSubNoUnderflowCertified .u64 hyps lhsExpr rhsExpr) cert hFarkas
      env [] canonInitMemory)

/-! ### 4.3c Every Backend Environment

`SemRefinesUnder` quantifies over every environment `env : Nat → Nat`, while
the correspondences above are stated at `env2 a b`. Both block arenas read
only variables `0` and `1`, so every environment evaluates them exactly as
`env2 (env 0) (env 1)` does, and certificate transport holds at every
`u64`-ranged environment, for ANY accepted certificate. -/

/-- `u64CheckedAddArena` reads only variables `0` and `1`. -/
theorem u64CheckedAddArena_evalArena_env (env : Nat → Nat) :
    evalArena env u64CheckedAddArena =
      evalArena (env2 (env 0) (env 1)) u64CheckedAddArena :=
  rfl

/-- `u64CheckedSubArena` reads only variables `0` and `1`. -/
theorem u64CheckedSubArena_evalArena_env (env : Nat → Nat) :
    evalArena env u64CheckedSubArena =
      evalArena (env2 (env 0) (env 1)) u64CheckedSubArena :=
  rfl

/-- The `CtxFact` entry precondition of `u64CheckedAddSrc` at any environment
is the one at `env2 (env 0) (env 1)`. -/
theorem sourceEntryPre_u64CheckedAdd_env_iff (env : Nat → Nat) :
    SourceEntryPre u64CheckedAddSrc env ↔
      SourceEntryPre u64CheckedAddSrc (env2 (env 0) (env 1)) :=
  Iff.rfl

/-- The `CtxFact` entry precondition of `u64CheckedSubSrc` at any environment
is the one at `env2 (env 0) (env 1)`. -/
theorem sourceEntryPre_u64CheckedSub_env_iff (env : Nat → Nat) :
    SourceEntryPre u64CheckedSubSrc env ↔
      SourceEntryPre u64CheckedSubSrc (env2 (env 0) (env 1)) :=
  Iff.rfl

/-- `u64` checked addition at EVERY `u64`-ranged environment and for ANY
accepted `blockOptGate` certificate: the `CtxFact` discharged at `env` makes
the real `stepMirState` runs on `(env 0, env 1)` equivalent in the
strategy-exact order, under `PanicStrategy.abort`, and as Layer 1A
`ITree.toPartial`. -/
theorem u64_add_blockOptGate_cut_to_stepMirState_env (maxStepsPerNode : Nat)
    (steps : List DagStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (blockOptGate maxStepsPerNode))
      (u64CheckedAddSrc, u64UncheckedAddOpt, steps))
    (env : Nat → Nat)
    (h0 : env 0 < modPow2 (uintWidth .u64))
    (h1 : env 1 < modPow2 (uintWidth .u64))
    (hEntry : SourceEntryPre u64CheckedAddSrc env) :
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 (env 0) (env 1))))
      (classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .add) 2
          (uintArgs2 .u64 (env 0) (env 1)))) ∧
    MirOutcomeEquiv
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 (env 0) (env 1))))
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u64 .add) 2
          (uintArgs2 .u64 (env 0) (env 1)))) ∧
    (mirCallTree (mkUncheckedArithBody .u64 .add)
        (uintArgs2 .u64 (env 0) (env 1))).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u64 .add .terminate)
        (uintArgs2 .u64 (env 0) (env 1))).toPartial ∧
    (mirCallTree (mkCheckedArithBody .u64 .add .terminate)
        (uintArgs2 .u64 (env 0) (env 1))).toPartial ≤
      (mirCallTree (mkUncheckedArithBody .u64 .add)
        (uintArgs2 .u64 (env 0) (env 1))).toPartial := by
  have hEntry2 := (sourceEntryPre_u64CheckedAdd_env_iff env).1 hEntry
  have hLt : env 0 + env 1 < modPow2 (uintWidth .u64) :=
    (sourceEntryPre_u64CheckedAdd_iff _ _ h0 h1).1 hEntry2
  have hOk := runMirCall_checked_add_ok .u64 .abort (env 0) (env 1) hLt
  dsimp only [PanicStrategy.toUnwindAction] at hOk
  have hDef :
      classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 (env 0) (env 1))) ≠ .ub := by
    rw [hOk]
    intro h
    nomatch h
  have hEq := u64_add_blockOptGate_cut_to_stepMirState maxStepsPerNode steps
    hCut (env 0) (env 1) h0 h1 hEntry2
  have hTree :=
    blockOptGate_cut_transports_to_mirCallTree_toPartial_equiv
      maxStepsPerNode u64CheckedAddSrc u64UncheckedAddOpt steps hCut
      (env2 (env 0) (env 1)) hEntry2
      (u64CheckedAddSrc_corresponds_stepMirState _ _ h0 h1)
      (u64UncheckedAddOpt_corresponds_stepMirState _ _ h0 h1) hDef
      (fun _ _ _ _ hS hT =>
        (canonMem_checked_add _ _ hS).trans
          (canonMem_unchecked_add _ _ hT).symm)
  exact ⟨hEq.1, hEq.2, hTree.1, hTree.2⟩

/-- `u64` checked subtraction at EVERY `u64`-ranged environment and for ANY
accepted `blockOptGate` certificate. -/
theorem u64_sub_blockOptGate_cut_to_stepMirState_env (maxStepsPerNode : Nat)
    (steps : List DagStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (blockOptGate maxStepsPerNode))
      (u64CheckedSubSrc, u64UncheckedSubOpt, steps))
    (env : Nat → Nat)
    (h0 : env 0 < modPow2 (uintWidth .u64))
    (h1 : env 1 < modPow2 (uintWidth .u64))
    (hEntry : SourceEntryPre u64CheckedSubSrc env) :
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 (env 0) (env 1))))
      (classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .sub) 2
          (uintArgs2 .u64 (env 0) (env 1)))) ∧
    MirOutcomeEquiv
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 (env 0) (env 1))))
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u64 .sub) 2
          (uintArgs2 .u64 (env 0) (env 1)))) ∧
    (mirCallTree (mkUncheckedArithBody .u64 .sub)
        (uintArgs2 .u64 (env 0) (env 1))).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u64 .sub .terminate)
        (uintArgs2 .u64 (env 0) (env 1))).toPartial ∧
    (mirCallTree (mkCheckedArithBody .u64 .sub .terminate)
        (uintArgs2 .u64 (env 0) (env 1))).toPartial ≤
      (mirCallTree (mkUncheckedArithBody .u64 .sub)
        (uintArgs2 .u64 (env 0) (env 1))).toPartial := by
  have hEntry2 := (sourceEntryPre_u64CheckedSub_env_iff env).1 hEntry
  have hLe : env 1 ≤ env 0 :=
    (sourceEntryPre_u64CheckedSub_iff _ _ h0 h1).1 hEntry2
  have hOk := runMirCall_checked_sub_ok .u64 .abort (env 0) (env 1) h0 h1 hLe
  dsimp only [PanicStrategy.toUnwindAction] at hOk
  have hDef :
      classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 (env 0) (env 1))) ≠ .ub := by
    rw [hOk]
    intro h
    nomatch h
  have hEq := u64_sub_blockOptGate_cut_to_stepMirState maxStepsPerNode steps
    hCut (env 0) (env 1) h0 h1 hEntry2
  have hTree :=
    blockOptGate_cut_transports_to_mirCallTree_toPartial_equiv
      maxStepsPerNode u64CheckedSubSrc u64UncheckedSubOpt steps hCut
      (env2 (env 0) (env 1)) hEntry2
      (u64CheckedSubSrc_corresponds_stepMirState _ _ h0 h1)
      (u64UncheckedSubOpt_corresponds_stepMirState _ _ h0 h1) hDef
      (fun _ _ _ _ hS hT =>
        (canonMem_checked_sub _ _ h0 h1 hS).trans
          (canonMem_unchecked_sub _ _ h0 hT).symm)
  exact ⟨hEq.1, hEq.2, hTree.1, hTree.2⟩

/-- `u64CheckedAddArena` reduces inputs via `word64`, so EVERY unrestricted
`env : Nat → Nat` evaluates identically to
`env2 (word64 (env 0)) (word64 (env 1))`. -/
theorem u64CheckedAddArena_evalArena_any_env (env : Nat → Nat) :
    evalArena env u64CheckedAddArena =
      evalArena (env2 (word64 (env 0)) (word64 (env 1)))
        u64CheckedAddArena := by
  let env' : Nat → Nat := env2 (word64 (env 0)) (word64 (env 1))
  have h0 : word64 (env' 0) = word64 (env 0) := word64_idem (env 0)
  have h1 : word64 (env' 1) = word64 (env 1) := word64_idem (env 1)
  change
    [ .val (word64 (env 0)),
      .val (word64 (env 1)),
      evalSsaOp (fun _ => 0) .addWrap
        [.val (word64 (env 0)), .val (word64 (env 1))],
      evalSsaOp (fun _ => 0) .addNuw
        [.val (word64 (env 0)), .val (word64 (env 1))] ] =
    [ .val (word64 (env' 0)),
      .val (word64 (env' 1)),
      evalSsaOp (fun _ => 0) .addWrap
        [.val (word64 (env' 0)), .val (word64 (env' 1))],
      evalSsaOp (fun _ => 0) .addNuw
        [.val (word64 (env' 0)), .val (word64 (env' 1))] ]
  rw [h0, h1]

/-- `u64CheckedSubArena` reduces inputs via `word64`, so EVERY unrestricted
`env : Nat → Nat` evaluates identically to
`env2 (word64 (env 0)) (word64 (env 1))`. -/
theorem u64CheckedSubArena_evalArena_any_env (env : Nat → Nat) :
    evalArena env u64CheckedSubArena =
      evalArena (env2 (word64 (env 0)) (word64 (env 1)))
        u64CheckedSubArena := by
  let env' : Nat → Nat := env2 (word64 (env 0)) (word64 (env 1))
  have h0 : word64 (env' 0) = word64 (env 0) := word64_idem (env 0)
  have h1 : word64 (env' 1) = word64 (env 1) := word64_idem (env 1)
  change
    [ .val (word64 (env 0)),
      .val (word64 (env 1)),
      evalSsaOp (fun _ => 0) .subWrap
        [.val (word64 (env 0)), .val (word64 (env 1))],
      evalSsaOp (fun _ => 0) .subNuw
        [.val (word64 (env 0)), .val (word64 (env 1))] ] =
    [ .val (word64 (env' 0)),
      .val (word64 (env' 1)),
      evalSsaOp (fun _ => 0) .subWrap
        [.val (word64 (env' 0)), .val (word64 (env' 1))],
      evalSsaOp (fun _ => 0) .subNuw
        [.val (word64 (env' 0)), .val (word64 (env' 1))] ]
  rw [h0, h1]

theorem sourceEntryPre_u64CheckedAdd_any_env_iff (env : Nat → Nat) :
    SourceEntryPre u64CheckedAddSrc env ↔
      SourceEntryPre u64CheckedAddSrc
        (env2 (word64 (env 0)) (word64 (env 1))) := by
  dsimp only [SourceEntryPre, EntryFactsHold, u64CheckedAddSrc]
  rw [u64CheckedAddArena_evalArena_any_env env]

theorem sourceEntryPre_u64CheckedSub_any_env_iff (env : Nat → Nat) :
    SourceEntryPre u64CheckedSubSrc env ↔
      SourceEntryPre u64CheckedSubSrc
        (env2 (word64 (env 0)) (word64 (env 1))) := by
  dsimp only [SourceEntryPre, EntryFactsHold, u64CheckedSubSrc]
  rw [u64CheckedSubArena_evalArena_any_env env]

/-- Unrestricted every-environment transport for `u64` checked-to-unchecked
addition (NO `env 0, env 1 < 2^64` range hypotheses): ANY accepted
`blockOptGate` certificate transports to `stepMirState` and bidirectional
`ITree.toPartial` equivalence on `word64 (env 0), word64 (env 1)`. -/
theorem u64_add_blockOptGate_cut_to_stepMirState_any_env
    (maxStepsPerNode : Nat) (steps : List DagStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (blockOptGate maxStepsPerNode))
      (u64CheckedAddSrc, u64UncheckedAddOpt, steps))
    (env : Nat → Nat) (hEntry : SourceEntryPre u64CheckedAddSrc env) :
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))))
      (classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .add) 2
          (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1))))) ∧
    MirOutcomeEquiv
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))))
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u64 .add) 2
          (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1))))) ∧
    (mirCallTree (mkUncheckedArithBody .u64 .add)
        (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u64 .add .terminate)
        (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))).toPartial ∧
    (mirCallTree (mkCheckedArithBody .u64 .add .terminate)
        (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))).toPartial ≤
      (mirCallTree (mkUncheckedArithBody .u64 .add)
        (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))).toPartial :=
  u64_add_blockOptGate_cut_to_stepMirState_env maxStepsPerNode steps hCut
    (env2 (word64 (env 0)) (word64 (env 1)))
    (Nat.mod_lt (env 0) u64Mod_pos) (Nat.mod_lt (env 1) u64Mod_pos)
    ((sourceEntryPre_u64CheckedAdd_any_env_iff env).1 hEntry)

/-- Unrestricted every-environment transport for `u64` checked-to-wrapping
addition (NO range hypotheses): full `stepMirState` and bidirectional
`ITree.toPartial` equivalence for ANY accepted `blockOptGate` certificate. -/
theorem u64_add_blockOptGate_cut_to_stepMirState_wrapping_any_env
    (maxStepsPerNode : Nat) (steps : List DagStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (blockOptGate maxStepsPerNode))
      (u64CheckedAddSrc, u64WrappingAddOpt, steps))
    (env : Nat → Nat) (hEntry : SourceEntryPre u64CheckedAddSrc env) :
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))))
      (classifyMirExecStateExact
        (runMirCall (mkWrappingArithBody .u64 .add) 2
          (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1))))) ∧
    MirOutcomeEquiv
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))))
      (classifyMirExecState .abort
        (runMirCall (mkWrappingArithBody .u64 .add) 2
          (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1))))) ∧
    (mirCallTree (mkWrappingArithBody .u64 .add)
        (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u64 .add .terminate)
        (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))).toPartial ∧
    (mirCallTree (mkCheckedArithBody .u64 .add .terminate)
        (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))).toPartial ≤
      (mirCallTree (mkWrappingArithBody .u64 .add)
        (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))).toPartial := by
  have h0 : word64 (env 0) < modPow2 (uintWidth .u64) :=
    Nat.mod_lt (env 0) u64Mod_pos
  have h1 : word64 (env 1) < modPow2 (uintWidth .u64) :=
    Nat.mod_lt (env 1) u64Mod_pos
  have hEntry2 := (sourceEntryPre_u64CheckedAdd_any_env_iff env).1 hEntry
  have hLt : word64 (env 0) + word64 (env 1) < modPow2 (uintWidth .u64) :=
    (sourceEntryPre_u64CheckedAdd_iff _ _ h0 h1).1 hEntry2
  have hOk := runMirCall_checked_add_ok .u64 .abort (word64 (env 0))
    (word64 (env 1)) hLt
  dsimp only [PanicStrategy.toUnwindAction] at hOk
  have hDef :
      classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))) ≠ .ub := by
    rw [hOk]
    intro h
    nomatch h
  have hEq := u64_add_blockOptGate_cut_to_stepMirState_wrapping maxStepsPerNode
    steps hCut (word64 (env 0)) (word64 (env 1)) h0 h1 hEntry2
  have hTree :=
    blockOptGate_cut_transports_to_mirCallTree_toPartial_equiv
      maxStepsPerNode u64CheckedAddSrc u64WrappingAddOpt steps hCut
      (env2 (word64 (env 0)) (word64 (env 1))) hEntry2
      (u64CheckedAddSrc_corresponds_stepMirState _ _ h0 h1)
      (u64WrappingAddOpt_corresponds_stepMirState _ _ h0 h1) hDef
      (fun _ _ _ _ hS hT =>
        (canonMem_checked_add _ _ hS).trans
          (canonMem_wrapping_add _ _ hT).symm)
  exact ⟨hEq.1, hEq.2, hTree.1, hTree.2⟩

/-- Unrestricted every-environment transport for `u64` checked-to-unchecked
subtraction (NO range hypotheses). -/
theorem u64_sub_blockOptGate_cut_to_stepMirState_any_env
    (maxStepsPerNode : Nat) (steps : List DagStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (blockOptGate maxStepsPerNode))
      (u64CheckedSubSrc, u64UncheckedSubOpt, steps))
    (env : Nat → Nat) (hEntry : SourceEntryPre u64CheckedSubSrc env) :
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))))
      (classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .sub) 2
          (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1))))) ∧
    MirOutcomeEquiv
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))))
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u64 .sub) 2
          (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1))))) ∧
    (mirCallTree (mkUncheckedArithBody .u64 .sub)
        (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u64 .sub .terminate)
        (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))).toPartial ∧
    (mirCallTree (mkCheckedArithBody .u64 .sub .terminate)
        (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))).toPartial ≤
      (mirCallTree (mkUncheckedArithBody .u64 .sub)
        (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))).toPartial :=
  u64_sub_blockOptGate_cut_to_stepMirState_env maxStepsPerNode steps hCut
    (env2 (word64 (env 0)) (word64 (env 1)))
    (Nat.mod_lt (env 0) u64Mod_pos) (Nat.mod_lt (env 1) u64Mod_pos)
    ((sourceEntryPre_u64CheckedSub_any_env_iff env).1 hEntry)

/-- Unrestricted every-environment transport for `u64` checked-to-wrapping
subtraction (NO range hypotheses): full `stepMirState` and bidirectional
`ITree.toPartial` equivalence for ANY accepted `blockOptGate` certificate. -/
theorem u64_sub_blockOptGate_cut_to_stepMirState_wrapping_any_env
    (maxStepsPerNode : Nat) (steps : List DagStep)
    (hCut : Anneal.Framework.StepWp.BoolCertCut
      (gateCheckBounded (blockOptGate maxStepsPerNode))
      (u64CheckedSubSrc, u64WrappingSubOpt, steps))
    (env : Nat → Nat) (hEntry : SourceEntryPre u64CheckedSubSrc env) :
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))))
      (classifyMirExecStateExact
        (runMirCall (mkWrappingArithBody .u64 .sub) 2
          (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1))))) ∧
    MirOutcomeEquiv
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))))
      (classifyMirExecState .abort
        (runMirCall (mkWrappingArithBody .u64 .sub) 2
          (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1))))) ∧
    (mirCallTree (mkWrappingArithBody .u64 .sub)
        (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u64 .sub .terminate)
        (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))).toPartial ∧
    (mirCallTree (mkCheckedArithBody .u64 .sub .terminate)
        (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))).toPartial ≤
      (mirCallTree (mkWrappingArithBody .u64 .sub)
        (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))).toPartial := by
  have h0 : word64 (env 0) < modPow2 (uintWidth .u64) :=
    Nat.mod_lt (env 0) u64Mod_pos
  have h1 : word64 (env 1) < modPow2 (uintWidth .u64) :=
    Nat.mod_lt (env 1) u64Mod_pos
  have hEntry2 := (sourceEntryPre_u64CheckedSub_any_env_iff env).1 hEntry
  have hLe : word64 (env 1) ≤ word64 (env 0) :=
    (sourceEntryPre_u64CheckedSub_iff _ _ h0 h1).1 hEntry2
  have hOk := runMirCall_checked_sub_ok .u64 .abort (word64 (env 0))
    (word64 (env 1)) h0 h1 hLe
  dsimp only [PanicStrategy.toUnwindAction] at hOk
  have hDef :
      classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 (word64 (env 0)) (word64 (env 1)))) ≠ .ub := by
    rw [hOk]
    intro h
    nomatch h
  have hEq := u64_sub_blockOptGate_cut_to_stepMirState_wrapping maxStepsPerNode
    steps hCut (word64 (env 0)) (word64 (env 1)) h0 h1 hEntry2
  have hTree :=
    blockOptGate_cut_transports_to_mirCallTree_toPartial_equiv
      maxStepsPerNode u64CheckedSubSrc u64WrappingSubOpt steps hCut
      (env2 (word64 (env 0)) (word64 (env 1))) hEntry2
      (u64CheckedSubSrc_corresponds_stepMirState _ _ h0 h1)
      (u64WrappingSubOpt_corresponds_stepMirState _ _ h0 h1) hDef
      (fun _ _ _ _ hS hT =>
        (canonMem_checked_sub _ _ h0 h1 hS).trans
          (canonMem_wrapping_sub _ _ h0 h1 hT).symm)
  exact ⟨hEq.1, hEq.2, hTree.1, hTree.2⟩

/-! ### 4.4 Negative Counterexamples (Undischarged Elision & Strategy Split) -/

/-- Negative counterexample (a-1): eliding an undischarged
`GuardCond.addNoOverflow 0 1` on `u64` at `(u64Max, 1)` breaks BOTH
`SemRefines` and `MirOutcomeRefines` / `MirExactOutcomeRefines` /
`ITree.toPartial` for wrapping AND unchecked targets. -/
theorem neg_u64_add_undischarged_guard_elision_unsound :
    evalSourceBlockUnit u64CheckedAddSrc (env2 u64Max 1) (.aborted ()) ∧
    evalCompiledBlockUnit u64WrappingAddOpt (env2 u64Max 1) (.returned 0 ()) ∧
    evalCompiledBlockUnit u64UncheckedAddOpt (env2 u64Max 1) .faultUB ∧
    ¬ SemRefines (evalSourceBlockUnit u64CheckedAddSrc)
        (evalCompiledBlockUnit u64WrappingAddOpt) ∧
    ¬ SemRefines (evalSourceBlockUnit u64CheckedAddSrc)
        (evalCompiledBlockUnit u64UncheckedAddOpt) ∧
    ¬ MirOutcomeRefines
        (evalBlockMirClass u64CheckedAddSrc.guards u64CheckedAddSrc.arena
          u64CheckedAddSrc.srcRetId (env2 u64Max 1))
        (evalBlockMirClass u64WrappingAddOpt.guardsOut
          u64WrappingAddOpt.arenaOut u64WrappingAddOpt.retId (env2 u64Max 1)) ∧
    ¬ MirExactOutcomeRefines
        (evalBlockMirExactClass u64CheckedAddSrc.guards u64CheckedAddSrc.arena
          u64CheckedAddSrc.srcRetId (env2 u64Max 1))
        (evalBlockMirExactClass u64WrappingAddOpt.guardsOut
          u64WrappingAddOpt.arenaOut u64WrappingAddOpt.retId (env2 u64Max 1)) ∧
    ¬ MirOutcomeRefines
        (classifyMirExecState .abort
          (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
            (uintArgs2 .u64 u64Max 1)))
        (classifyMirExecState .abort
          (runMirCall (mkWrappingArithBody .u64 .add) 2
            (uintArgs2 .u64 u64Max 1))) ∧
    ¬ MirExactOutcomeRefines
        (classifyMirExecStateExact
          (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
            (uintArgs2 .u64 u64Max 1)))
        (classifyMirExecStateExact
          (runMirCall (mkUncheckedArithBody .u64 .add) 2
            (uintArgs2 .u64 u64Max 1))) ∧
    ¬ ((mirCallTree (mkUncheckedArithBody .u64 .add)
          (uintArgs2 .u64 u64Max 1)).toPartial ≤
        (mirCallTree (mkCheckedArithBody .u64 .add .terminate)
          (uintArgs2 .u64 u64Max 1)).toPartial) := by
  have hOv : modPow2 (uintWidth .u64) ≤ u64Max + 1 := Nat.le_of_ble_eq_true rfl
  have hMirC := runMirCall_checked_add_trap .u64 .abort u64Max 1 hOv
  have hMirU := runMirCall_unchecked_add_ub .u64 u64Max 1 hOv
  have hMirW := runMirCall_wrapping_add .u64 u64Max 1
  dsimp only [PanicStrategy.toUnwindAction, PanicStrategy.toTrapOutcome]
    at hMirC
  have ⟨uC, hTauC, hObsC⟩ := runMirSteps_halted_to_tauStar _ 6 _ _ hMirC
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hRef
    have hNoUb :
        ¬ evalSourceBlockUnit u64CheckedAddSrc (env2 u64Max 1) .faultUB :=
      fun h => by nomatch h
    have hSub := (hRef (env2 u64Max 1) True.intro hNoUb).2 (.returned 0 ()) rfl
    nomatch hSub
  · intro hRef
    have hNoUb :
        ¬ evalSourceBlockUnit u64CheckedAddSrc (env2 u64Max 1) .faultUB :=
      fun h => by nomatch h
    exact (hRef (env2 u64Max 1) True.intro hNoUb).1 rfl
  · intro h; nomatch h
  · intro h; nomatch h
  · rw [hMirC, hMirW]
    exact trap_not_refines_ret _
  · rw [hMirC, hMirU]
    intro h; exact False.elim h
  · exact not_toPartial_le_of_faultNow_ret (runMirCall_ub_faultNow hMirU)
      hTauC hObsC

/-- Negative counterexample (a-2): eliding an undischarged
`GuardCond.subNoUnderflow 0 1` on `u64` at `(0, 1)` breaks BOTH `SemRefines`
and `MirOutcomeRefines` / `MirExactOutcomeRefines` / `ITree.toPartial` for
wrapping AND unchecked targets. -/
theorem neg_u64_sub_undischarged_guard_elision_unsound :
    evalSourceBlockUnit u64CheckedSubSrc (env2 0 1) (.aborted ()) ∧
    evalCompiledBlockUnit u64WrappingSubOpt (env2 0 1) (.returned u64Max ()) ∧
    evalCompiledBlockUnit u64UncheckedSubOpt (env2 0 1) .faultUB ∧
    ¬ SemRefines (evalSourceBlockUnit u64CheckedSubSrc)
        (evalCompiledBlockUnit u64WrappingSubOpt) ∧
    ¬ SemRefines (evalSourceBlockUnit u64CheckedSubSrc)
        (evalCompiledBlockUnit u64UncheckedSubOpt) ∧
    ¬ MirOutcomeRefines
        (evalBlockMirClass u64CheckedSubSrc.guards u64CheckedSubSrc.arena
          u64CheckedSubSrc.srcRetId (env2 0 1))
        (evalBlockMirClass u64WrappingSubOpt.guardsOut
          u64WrappingSubOpt.arenaOut u64WrappingSubOpt.retId (env2 0 1)) ∧
    ¬ MirExactOutcomeRefines
        (evalBlockMirExactClass u64CheckedSubSrc.guards u64CheckedSubSrc.arena
          u64CheckedSubSrc.srcRetId (env2 0 1))
        (evalBlockMirExactClass u64WrappingSubOpt.guardsOut
          u64WrappingSubOpt.arenaOut u64WrappingSubOpt.retId (env2 0 1)) ∧
    ¬ MirOutcomeRefines
        (classifyMirExecState .abort
          (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
            (uintArgs2 .u64 0 1)))
        (classifyMirExecState .abort
          (runMirCall (mkWrappingArithBody .u64 .sub) 2
            (uintArgs2 .u64 0 1))) ∧
    ¬ MirExactOutcomeRefines
        (classifyMirExecStateExact
          (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
            (uintArgs2 .u64 0 1)))
        (classifyMirExecStateExact
          (runMirCall (mkUncheckedArithBody .u64 .sub) 2
            (uintArgs2 .u64 0 1))) ∧
    ¬ ((mirCallTree (mkUncheckedArithBody .u64 .sub)
          (uintArgs2 .u64 0 1)).toPartial ≤
        (mirCallTree (mkCheckedArithBody .u64 .sub .terminate)
          (uintArgs2 .u64 0 1)).toPartial) := by
  have ha : 0 < modPow2 (uintWidth .u64) := Nat.le_of_ble_eq_true rfl
  have hb : 1 < modPow2 (uintWidth .u64) := Nat.le_of_ble_eq_true rfl
  have hUnd : 0 < 1 := Nat.le_of_ble_eq_true rfl
  have hMirC := runMirCall_checked_sub_trap .u64 .abort 0 1 ha hb hUnd
  have hMirU := runMirCall_unchecked_sub_ub .u64 0 1 hUnd
  have hMirW := runMirCall_wrapping_sub .u64 0 1 ha hb
  dsimp only [PanicStrategy.toUnwindAction, PanicStrategy.toTrapOutcome]
    at hMirC
  have ⟨uC, hTauC, hObsC⟩ := runMirSteps_halted_to_tauStar _ 6 _ _ hMirC
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hRef
    have hNoUb : ¬ evalSourceBlockUnit u64CheckedSubSrc (env2 0 1) .faultUB :=
      fun h => by nomatch h
    have hSub := (hRef (env2 0 1) True.intro hNoUb).2 (.returned u64Max ()) rfl
    nomatch hSub
  · intro hRef
    have hNoUb : ¬ evalSourceBlockUnit u64CheckedSubSrc (env2 0 1) .faultUB :=
      fun h => by nomatch h
    exact (hRef (env2 0 1) True.intro hNoUb).1 rfl
  · intro h; nomatch h
  · intro h; nomatch h
  · rw [hMirC, hMirW]
    exact trap_not_refines_ret _
  · rw [hMirC, hMirU]
    intro h; exact False.elim h
  · exact not_toPartial_le_of_faultNow_ret (runMirCall_ub_faultNow hMirU)
      hTauC hObsC

/-- Negative counterexample (b): strategy separation — backend `.aborted ()`
maps to `.trap .abort` (`-C panic=abort`), refines `.trap .abort` (and
`mkCheckedArithBody .u64 .add .terminate` on overflow), and does NOT refine
`.trap .panic` (`-C panic=unwind`, `mkCheckedArithBody .u64 .add .continue_`),
nor vice versa. -/
theorem neg_aborted_strategy_separation :
    execOutcomeToMirExactClass? (.aborted ()) = some (.trap .abort) ∧
    MirExactOutcomeRefines (.trap .abort : MirExactOutcomeClass Value)
      (.trap .abort) ∧
    ¬ MirExactOutcomeRefines (.trap .abort : MirExactOutcomeClass Value)
        (.trap .panic) ∧
    ¬ MirExactOutcomeRefines (.trap .panic : MirExactOutcomeClass Value)
        (.trap .abort) ∧
    MirExactOutcomeRefines
      (evalBlockMirExactClass u64CheckedAddSrc.guards u64CheckedAddSrc.arena
        u64CheckedAddSrc.srcRetId (env2 u64Max 1))
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 u64Max 1))) ∧
    ¬ MirExactOutcomeRefines
        (evalBlockMirExactClass u64CheckedAddSrc.guards u64CheckedAddSrc.arena
          u64CheckedAddSrc.srcRetId (env2 u64Max 1))
        (classifyMirExecStateExact
          (runMirCall (mkCheckedArithBody .u64 .add .continue_) 6
            (uintArgs2 .u64 u64Max 1))) ∧
    ¬ MirExactOutcomeRefines
        (classifyMirExecStateExact
          (runMirCall (mkCheckedArithBody .u64 .add .continue_) 6
            (uintArgs2 .u64 u64Max 1)))
        (evalBlockMirExactClass u64CheckedAddSrc.guards u64CheckedAddSrc.arena
          u64CheckedAddSrc.srcRetId (env2 u64Max 1)) := by
  have hOv : modPow2 (uintWidth .u64) ≤ u64Max + 1 := Nat.le_of_ble_eq_true rfl
  have hAbort := runMirCall_checked_add_trap .u64 .abort u64Max 1 hOv
  have hUnwind := runMirCall_checked_add_trap .u64 .unwind u64Max 1 hOv
  dsimp only [PanicStrategy.toUnwindAction, PanicStrategy.toTrapOutcome]
    at hAbort hUnwind
  refine ⟨rfl, rfl, (fun h => nomatch h), (fun h => nomatch h), ?_, ?_, ?_⟩
  · rw [hAbort]
    rfl
  · rw [hUnwind]
    intro h
    nomatch h
  · rw [hUnwind]
    intro h
    nomatch h

/-! ### 4.5 Undischarged Facts: No Certificate Is Ever Accepted -/

/-- `u64CheckedAddSrc` with its `addNoOverflow` candidate at trust tier
`tier`. Only `.proven` is admitted by `extractProvenFacts`. -/
def u64CheckedAddSrcAt (tier : TrustTier) : SourceBlockUnit :=
  { guards := [.addNoOverflow 0 1]
    arena := u64CheckedAddArena
    srcRetId := 2
    candidates := [{ tier := tier, fact := .addNoOverflow 0 1 }] }

/-- `u64CheckedSubSrc` with its `subNoUnderflow` candidate at trust tier
`tier`. -/
def u64CheckedSubSrcAt (tier : TrustTier) : SourceBlockUnit :=
  { guards := [.subNoUnderflow 0 1]
    arena := u64CheckedSubArena
    srcRetId := 2
    candidates := [{ tier := tier, fact := .subNoUnderflow 0 1 }] }

theorem u64CheckedAddSrcAt_proven :
    u64CheckedAddSrcAt .proven = u64CheckedAddSrc :=
  rfl

theorem u64CheckedSubSrcAt_proven :
    u64CheckedSubSrcAt .proven = u64CheckedSubSrc :=
  rfl

/-- Without a `.proven` fact nothing has been discharged, so the entry
precondition holds on every input, including the overflowing ones. -/
theorem sourceEntryPre_u64CheckedAddSrcAt_unproven (tier : TrustTier)
    (hTier : tier ≠ .proven) (env : Nat → Nat) :
    SourceEntryPre (u64CheckedAddSrcAt tier) env := by
  cases tier with
  | proven => exact False.elim (hTier rfl)
  | fuzz => intro idx f hNth; nomatch hNth
  | sorryStub => intro idx f hNth; nomatch hNth

theorem sourceEntryPre_u64CheckedSubSrcAt_unproven (tier : TrustTier)
    (hTier : tier ≠ .proven) (env : Nat → Nat) :
    SourceEntryPre (u64CheckedSubSrcAt tier) env := by
  cases tier with
  | proven => exact False.elim (hTier rfl)
  | fuzz => intro idx f hNth; nomatch hNth
  | sorryStub => intro idx f hNth; nomatch hNth

/-- Negative counterexample (a-3): with the `addNoOverflow` fact undischarged
(`.fuzz` or `.sorryStub` tier), NO certificate of ANY size is accepted by
`blockOptGate` for eliding the guard, to either the wrapping or the unchecked
target. The proof uses only gate soundness and the overflow witness
`(u64Max, 1)`, so it holds for every sound checker, not just this one. -/
theorem neg_u64_add_unproven_elision_never_certified (tier : TrustTier)
    (hTier : tier ≠ .proven) (maxStepsPerNode : Nat) (steps : List DagStep) :
    gateCheckBounded (blockOptGate maxStepsPerNode)
      (u64CheckedAddSrcAt tier, u64WrappingAddOpt, steps) = false ∧
    gateCheckBounded (blockOptGate maxStepsPerNode)
      (u64CheckedAddSrcAt tier, u64UncheckedAddOpt, steps) = false := by
  have hEntry :=
    sourceEntryPre_u64CheckedAddSrcAt_unproven tier hTier (env2 u64Max 1)
  have hNoUb :
      ¬ evalSourceBlockUnit (u64CheckedAddSrcAt tier) (env2 u64Max 1)
        .faultUB :=
    fun h => by nomatch h
  constructor
  · cases hChk : gateCheckBounded (blockOptGate maxStepsPerNode)
        (u64CheckedAddSrcAt tier, u64WrappingAddOpt, steps) with
    | false => rfl
    | true =>
      have hRef := certGateCut_sound (blockOptGate maxStepsPerNode)
        True.intro (Anneal.Framework.StepWp.BoolCertCut.seal _ _ hChk)
      have hSub :=
        (hRef (env2 u64Max 1) hEntry hNoUb).2 (.returned 0 ()) rfl
      nomatch hSub
  · cases hChk : gateCheckBounded (blockOptGate maxStepsPerNode)
        (u64CheckedAddSrcAt tier, u64UncheckedAddOpt, steps) with
    | false => rfl
    | true =>
      have hRef := certGateCut_sound (blockOptGate maxStepsPerNode)
        True.intro (Anneal.Framework.StepWp.BoolCertCut.seal _ _ hChk)
      exact False.elim ((hRef (env2 u64Max 1) hEntry hNoUb).1 rfl)

/-- Negative counterexample (a-3'): with the `subNoUnderflow` fact
undischarged, NO certificate of ANY size is accepted by `blockOptGate` for
eliding the guard (underflow witness `(0, 1)`). -/
theorem neg_u64_sub_unproven_elision_never_certified (tier : TrustTier)
    (hTier : tier ≠ .proven) (maxStepsPerNode : Nat) (steps : List DagStep) :
    gateCheckBounded (blockOptGate maxStepsPerNode)
      (u64CheckedSubSrcAt tier, u64WrappingSubOpt, steps) = false ∧
    gateCheckBounded (blockOptGate maxStepsPerNode)
      (u64CheckedSubSrcAt tier, u64UncheckedSubOpt, steps) = false := by
  have hEntry :=
    sourceEntryPre_u64CheckedSubSrcAt_unproven tier hTier (env2 0 1)
  have hNoUb :
      ¬ evalSourceBlockUnit (u64CheckedSubSrcAt tier) (env2 0 1) .faultUB :=
    fun h => by nomatch h
  constructor
  · cases hChk : gateCheckBounded (blockOptGate maxStepsPerNode)
        (u64CheckedSubSrcAt tier, u64WrappingSubOpt, steps) with
    | false => rfl
    | true =>
      have hRef := certGateCut_sound (blockOptGate maxStepsPerNode)
        True.intro (Anneal.Framework.StepWp.BoolCertCut.seal _ _ hChk)
      have hSub :=
        (hRef (env2 0 1) hEntry hNoUb).2 (.returned u64Max ()) rfl
      nomatch hSub
  · cases hChk : gateCheckBounded (blockOptGate maxStepsPerNode)
        (u64CheckedSubSrcAt tier, u64UncheckedSubOpt, steps) with
    | false => rfl
    | true =>
      have hRef := certGateCut_sound (blockOptGate maxStepsPerNode)
        True.intro (Anneal.Framework.StepWp.BoolCertCut.seal _ _ hChk)
      exact False.elim ((hRef (env2 0 1) hEntry hNoUb).1 rfl)

/-- Negative counterexample (a-4): the full `stepMirState` picture at the
`u64` overflow witness `(u64Max, 1)`. Checked addition aborts
(`.trap .abort`), wrapping returns `0`, unchecked is UB, and the checked run
is refined by neither in either order. Together with
`neg_u64_add_undischarged_guard_elision_unsound` this covers both targets
under both `MirOutcomeRefines` and `MirExactOutcomeRefines`. -/
theorem neg_u64_add_overflow_stepMirState_matrix :
    classifyMirExecStateExact
      (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
        (uintArgs2 .u64 u64Max 1)) = .trap .abort ∧
    classifyMirExecStateExact
      (runMirCall (mkWrappingArithBody .u64 .add) 2
        (uintArgs2 .u64 u64Max 1)) = .ret (execOutcomeToMirValue 0) ∧
    classifyMirExecStateExact
      (runMirCall (mkUncheckedArithBody .u64 .add) 2
        (uintArgs2 .u64 u64Max 1)) = .ub ∧
    ¬ MirExactOutcomeRefines
        (classifyMirExecStateExact
          (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
            (uintArgs2 .u64 u64Max 1)))
        (classifyMirExecStateExact
          (runMirCall (mkWrappingArithBody .u64 .add) 2
            (uintArgs2 .u64 u64Max 1))) ∧
    ¬ MirOutcomeRefines
        (classifyMirExecState .abort
          (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
            (uintArgs2 .u64 u64Max 1)))
        (classifyMirExecState .abort
          (runMirCall (mkUncheckedArithBody .u64 .add) 2
            (uintArgs2 .u64 u64Max 1))) := by
  have hOv : modPow2 (uintWidth .u64) ≤ u64Max + 1 := Nat.le_of_ble_eq_true rfl
  have hMirC := runMirCall_checked_add_trap .u64 .abort u64Max 1 hOv
  have hMirU := runMirCall_unchecked_add_ub .u64 u64Max 1 hOv
  have hMirW := runMirCall_wrapping_add .u64 u64Max 1
  dsimp only [PanicStrategy.toUnwindAction, PanicStrategy.toTrapOutcome]
    at hMirC
  rw [hMirC, hMirW, hMirU]
  exact ⟨rfl, rfl, rfl, fun h => h, fun h => h⟩

/-- Negative counterexample (a-4'): the full `stepMirState` picture at the
`u64` underflow witness `(0, 1)`. Checked subtraction aborts, wrapping
returns `u64Max`, unchecked is UB. -/
theorem neg_u64_sub_underflow_stepMirState_matrix :
    classifyMirExecStateExact
      (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
        (uintArgs2 .u64 0 1)) = .trap .abort ∧
    classifyMirExecStateExact
      (runMirCall (mkWrappingArithBody .u64 .sub) 2
        (uintArgs2 .u64 0 1)) = .ret (execOutcomeToMirValue u64Max) ∧
    classifyMirExecStateExact
      (runMirCall (mkUncheckedArithBody .u64 .sub) 2
        (uintArgs2 .u64 0 1)) = .ub ∧
    ¬ MirExactOutcomeRefines
        (classifyMirExecStateExact
          (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
            (uintArgs2 .u64 0 1)))
        (classifyMirExecStateExact
          (runMirCall (mkWrappingArithBody .u64 .sub) 2
            (uintArgs2 .u64 0 1))) ∧
    ¬ MirOutcomeRefines
        (classifyMirExecState .abort
          (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
            (uintArgs2 .u64 0 1)))
        (classifyMirExecState .abort
          (runMirCall (mkUncheckedArithBody .u64 .sub) 2
            (uintArgs2 .u64 0 1))) := by
  have ha : 0 < modPow2 (uintWidth .u64) := Nat.le_of_ble_eq_true rfl
  have hb : 1 < modPow2 (uintWidth .u64) := Nat.le_of_ble_eq_true rfl
  have hUnd : 0 < 1 := Nat.le_of_ble_eq_true rfl
  have hMirC := runMirCall_checked_sub_trap .u64 .abort 0 1 ha hb hUnd
  have hMirU := runMirCall_unchecked_sub_ub .u64 0 1 hUnd
  have hMirW := runMirCall_wrapping_sub .u64 0 1 ha hb
  dsimp only [PanicStrategy.toUnwindAction, PanicStrategy.toTrapOutcome]
    at hMirC
  rw [hMirC, hMirW, hMirU]
  exact ⟨rfl, rfl, rfl, fun h => h, fun h => h⟩

end Anneal.HybridCertBridgesV2026
