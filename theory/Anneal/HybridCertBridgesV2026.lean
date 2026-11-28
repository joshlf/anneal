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
   `firstAccepted` / `withFallback` portfolios, and oversized / forged witness
   rejections.
2. **Pillar 2 (`Anneal.FarkasMirCert`):** defines computable
   `farkasMirCertSize` (total `CutStep` count across `.single`, `.pair`,
   `.triple`, `.edge`), wraps `checkFarkasMirGoal` as `farkasMirGate` with
   `BoolCertCut` discharge, `firstAccepted` / `withFallback` portfolios, and
   an indexed-to-MIR arithmetic bridge from `natCutIdxGate` directly to
   `evalScalarBinOp` overflow/underflow freedom.
3. **Pillar 3 (`Anneal.CanonicalDiode`):** wraps any lawful `CanonicalDiode`
   with a sound equality check as `canonicalDiodeChunkGate` plugged into
   `Anneal.Hybrid.foldStreamPrefix`, proving strict canonical image on all
   emitted chunks, immediate halt on rejected / tampered / non-canonical
   chunks, and exact agreement with `CanonicalDiode.filterAll` on faithful
   accepted streams.
4. **Pillar 4 (`Anneal.Backend.CtxFact` <-> `OverflowTrapRefinement`):**
   maps `ExecOutcome Nat Unit` faithfully into `Option (MirOutcomeClass Value)`
   and `Option (MirExactOutcomeClass Value)` under `PanicStrategy.abort`
   without collapsing `.diverged` into `.ret`, `.trap`, or `.ub`; proves that
   `SemRefinesUnder` and `blockOptGate` preserve asymmetric `MirOutcomeRefines`
   and `MirExactOutcomeRefines`; establishes end-to-end `u64` guarded add/sub
   elision <-> real `stepMirState` (`mkCheckedArithBody` <->
   `mkUncheckedArithBody` + `ITree.toPartial`) bridges from `CtxFact`,
   `farkasMirGate`, and `natCutIdxGate`; and proves concrete negative
   counterexamples for undischarged guard elision and abort-vs-unwind strategy
   separation.
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
    (goal : NatCutGoal) (steps : List CutStep) (hOver : maxSteps < steps.length) :
    evalGate (E := E) (natCutIdxGate maxSteps) goal (.candidate () steps) =
      .error (.witnessOversized steps.length maxSteps) :=
  evalGate_rejects_oversized (natCutIdxGate maxSteps) goal () steps hOver

/-- Size-bound rejection for `intCutIdxGate` without consulting the checker. -/
theorem intCutIdxGate_rejects_oversized {E : Type} (maxSteps : Nat)
    (goal : IntCutGoal) (steps : List CutStep) (hOver : maxSteps < steps.length) :
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
      (Spec := fun g (res : Except (HybridErr E) Unit) => res = .ok () → g.denote)
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
      (Spec := fun g (res : Except (HybridErr E) Unit) => res = .ok () → g.denote)
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

/-- Total `withFallback` adapter pairing `natCutIdxGate` with any verified
fallback `fb : NatCutGoal → Unit` on a satisfiable precondition `Pre`. -/
theorem natCutIdx_withFallback_sound {E : Type} (maxSteps : Nat)
    {Pre : NatCutGoal → Prop} (goal : NatCutGoal)
    (rs : List (RawOutcome E Unit (List CutStep)))
    (fb : NatCutGoal → Unit) (hPre : Pre goal)
    (hFb : ∀ g, Pre g → g.denote) :
    goal.denote := by
  have hRes :=
    withFallback_firstAccepted_sound
      (g :=
        { maxWitness := (natCutIdxGate maxSteps).maxWitness
          wSize := (natCutIdxGate maxSteps).wSize
          check := (natCutIdxGate maxSteps).check
          sound := fun g u w _ hCap hChk =>
            (natCutIdxGate maxSteps).sound g u w True.intro hCap hChk })
      (Pre := Pre) (Spec := fun g _ => g.denote)
      goal rs fb hPre (fun g hp => hFb g hp)
  exact hRes

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
    (FarkasMirGoal.uintSubNoUnderflowCertified u hyps lhsExpr rhsExpr).denote := by
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

theorem boolListBeq_eq : ∀ (xs ys : List Bool), boolListBeq xs ys = true → xs = ys
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

/-- Acceptance of candidate `((), c)` on raw input `u` implies `d.filter u =
some c` and full upstream-to-canonical round-trip soundness. -/
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
def faithfulDiodeProducer {A B E : Type} (d : CanonicalDiode A B) (eReject : E) :
    Unit → B → RawOutcome E (Unit × B) Unit :=
  fun _ u =>
    match d.filter u with
    | none => .prodErr eReject
    | some out => .candidate ((), out) ()

/-- Pillar 3 (iii): for a faithful producer, whenever `d.filterAll us = some
outs`, `foldStreamPrefix` emits the exact canonical list `outs` with
`err = none`. -/
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
    have hEq : outTgt = .returned v () := hDet outTgt (.returned v ()) hSrcTgt hSrc
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
    (mirOutcomeRefines_iff_partial_le cSrc cSrc).1 (mirOutcomeRefines_refl cSrc),
    (mirExactOutcomeRefines_iff_partial_le eSrc eSrc).1
      (mirExactOutcomeRefines_refl eSrc)⟩

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
    execOutcomeToMirExactClass? (evalBlockWithGuardsDet guards arena retId env) =
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
    (evalBlockMirExactClass out.guardsOut out.arenaOut out.retId env).toPartial ≤
      (evalBlockMirExactClass src.guards src.arena src.srcRetId env).toPartial := by
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
    dsimp only [PanicStrategy.toUnwindAction, PanicStrategy.toTrapOutcome] at hMir
    rw [hMir]
    rfl

/-- Exact pointwise correspondence between `u64UncheckedAddOpt` (`addNuw`) and
`stepMirState` `mkUncheckedArithBody .u64 .add` for ALL `u64`-ranged inputs. -/
theorem u64UncheckedAddOpt_corresponds_stepMirState (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64)) :
    evalBlockMirExactClass u64UncheckedAddOpt.guardsOut
      u64UncheckedAddOpt.arenaOut u64UncheckedAddOpt.retId (env2 a b) =
      classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .add) 2 (uintArgs2 .u64 a b)) := by
  have ha' : a < u64Mod := ha
  have hb' : b < u64Mod := hb
  dsimp only [evalBlockMirExactClass, u64UncheckedAddOpt, evalGuards, List.foldr]
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
        (runMirCall (mkWrappingArithBody .u64 .add) 2 (uintArgs2 .u64 a b)) := by
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
    dsimp only [PanicStrategy.toUnwindAction, PanicStrategy.toTrapOutcome] at hMir
    rw [hMir]
    rfl

/-- Exact pointwise correspondence between `u64UncheckedSubOpt` (`subNuw`) and
`stepMirState` `mkUncheckedArithBody .u64 .sub` for ALL `u64`-ranged inputs. -/
theorem u64UncheckedSubOpt_corresponds_stepMirState (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64)) :
    evalBlockMirExactClass u64UncheckedSubOpt.guardsOut
      u64UncheckedSubOpt.arenaOut u64UncheckedSubOpt.retId (env2 a b) =
      classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .sub) 2 (uintArgs2 .u64 a b)) := by
  have ha' : a < u64Mod := ha
  have hb' : b < u64Mod := hb
  dsimp only [evalBlockMirExactClass, u64UncheckedSubOpt, evalGuards, List.foldr]
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
        (runMirCall (mkWrappingArithBody .u64 .sub) 2 (uintArgs2 .u64 a b)) := by
  have ha' : a < u64Mod := ha
  have hb' : b < u64Mod := hb
  dsimp only [evalBlockMirExactClass, u64WrappingSubOpt, evalGuards, List.foldr]
  rw [u64SubArena_node2 a b ha' hb', runMirCall_wrapping_sub .u64 a b ha hb]
  dsimp only [classifyMirExecStateExact, execOutcomeToMirValue]
  have hPos : 0 < modPow2 (uintWidth .u64) := u64Mod_pos
  rw [word64_eq_mod_u64, Nat.mod_eq_of_lt (Nat.mod_lt _ hPos)]
  rfl

/-- End-to-end `CtxFact` -> Backend `blockOptGate` + `stepMirState` bridge for
`u64` checked addition: whenever `SourceEntryPre u64CheckedAddSrc (env2 a b)`
holds on `u64`-ranged `a, b`, BOTH backend guard elision AND real MIR
`stepMirState` `MirOutcomeEquiv`, `MirExactOutcomeEquiv`, and `ITree.toPartial`
equivalence hold between checked and unchecked `u64` addition. -/
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
    (mirCallTree (mkUncheckedArithBody .u64 .add) (uintArgs2 .u64 a b)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u64 .add .terminate)
        (uintArgs2 .u64 a b)).toPartial ∧
    (mirCallTree (mkCheckedArithBody .u64 .add .terminate)
      (uintArgs2 .u64 a b)).toPartial ≤
      (mirCallTree (mkUncheckedArithBody .u64 .add)
        (uintArgs2 .u64 a b)).toPartial := by
  have hLt : a + b < modPow2 (uintWidth .u64) :=
    (sourceEntryPre_u64CheckedAdd_iff a b ha hb).1 hEntry
  have hC := runMirCall_checked_add_ok .u64 .abort a b hLt
  have hU := runMirCall_unchecked_add_ok .u64 a b hLt
  dsimp only [PanicStrategy.toUnwindAction] at hC
  have hTree := mirCallTree_toPartial_equiv_of_same_halted hU hC
  refine ⟨u64CheckedAdd_blockOptGate_to_unchecked, ?_, ?_, hTree.1, hTree.2⟩
  · rw [hC, hU]
    exact mirOutcomeEquiv_refl _
  · rw [hC, hU]
    exact mirExactOutcomeEquiv_refl _

/-- End-to-end `CtxFact` -> Backend `blockOptGate` + `stepMirState` bridge for
`u64` checked subtraction. -/
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
    (mirCallTree (mkUncheckedArithBody .u64 .sub) (uintArgs2 .u64 a b)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u64 .sub .terminate)
        (uintArgs2 .u64 a b)).toPartial ∧
    (mirCallTree (mkCheckedArithBody .u64 .sub .terminate)
      (uintArgs2 .u64 a b)).toPartial ≤
      (mirCallTree (mkUncheckedArithBody .u64 .sub)
        (uintArgs2 .u64 a b)).toPartial := by
  have hLe : b ≤ a := (sourceEntryPre_u64CheckedSub_iff a b ha hb).1 hEntry
  have hC := runMirCall_checked_sub_ok .u64 .abort a b ha hb hLe
  have hU := runMirCall_unchecked_sub_ok .u64 a b ha hLe
  dsimp only [PanicStrategy.toUnwindAction] at hC
  have hTree := mirCallTree_toPartial_equiv_of_same_halted hU hC
  refine ⟨u64CheckedSub_blockOptGate_to_unchecked, ?_, ?_, hTree.1, hTree.2⟩
  · rw [hC, hU]
    exact mirOutcomeEquiv_refl _
  · rw [hC, hU]
    exact mirExactOutcomeEquiv_refl _

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
  dsimp only [PanicStrategy.toUnwindAction, PanicStrategy.toTrapOutcome] at hMirC
  have ⟨uC, hTauC, hObsC⟩ := runMirSteps_halted_to_tauStar _ 6 _ _ hMirC
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hRef
    have hNoUb : ¬ evalSourceBlockUnit u64CheckedAddSrc (env2 u64Max 1) .faultUB :=
      fun h => by nomatch h
    have hSub := (hRef (env2 u64Max 1) True.intro hNoUb).2 (.returned 0 ()) rfl
    nomatch hSub
  · intro hRef
    have hNoUb : ¬ evalSourceBlockUnit u64CheckedAddSrc (env2 u64Max 1) .faultUB :=
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
  dsimp only [PanicStrategy.toUnwindAction, PanicStrategy.toTrapOutcome] at hMirC
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
  dsimp only [PanicStrategy.toUnwindAction, PanicStrategy.toTrapOutcome] at hAbort hUnwind
  refine ⟨rfl, rfl, (fun h => nomatch h), (fun h => nomatch h), ?_, ?_, ?_⟩
  · rw [hAbort]
    rfl
  · rw [hUnwind]
    intro h
    nomatch h
  · rw [hUnwind]
    intro h
    nomatch h

end Anneal.HybridCertBridgesV2026
