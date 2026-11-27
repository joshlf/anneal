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
import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Int.Basic
import Init.Data.List.Basic
import Trusted.Rustc.V2026_06_01.MirSemantics.Machine
import Anneal.LinearArith
import Anneal.AiPcc.BitArith
import Anneal.AiPcc.Tnum
import Anneal.AiPcc.WrappedInterval
import Anneal.AiPcc.ReducedProduct
import Anneal.AiPcc.MirBridge
import Anneal.UnsafeObligations

/-!
# Reflective Farkas & Chvatal-Gomory MIR Certificate Bridge (`Anneal.FarkasMirCert`)

Strictly Pass-1-safe, zero-TCB Lean 4 library lifting `Anneal.LinearArith`
(`NatCutGoal`, `IntCutGoal`, `CutStep`, `checkNatCutGoal_sound`,
`checkIntCutGoal_sound`) into:

1. **MIR Scalar & Overflow-Freedom Discharge**: bridges unsigned linear
   certificates directly to `Trusted.Rustc.V2026_06_01.MirSemantics.evalScalarBinOp`
   for `.addUnchecked`, `.addWithOverflow`, `.subUnchecked`, `.subWithOverflow`,
   `.mulUnchecked`, and `.mulWithOverflow` (with overflow flag `⟨0, 1⟩`), plus
   width-bound hypothesis extractors from `UintScalarInRange` and
   `MirAbsSlot.denote`.
2. **`Anneal.UnsafeObligations` Discharge**: bridges linear and Chvatal-Gomory
   certificates to `ValidSliceRange` (and `evalPtrOffset`), `ValidSliceSplit`,
   `AlignedPtr`, `NonOverlappingPtrs`, and `ValidArrayToSliceCast`.
3. **`Anneal.AiPcc` Bridges**: extracts sound linear bounds from
   `WrappedInterval.denote`, `AbsVal.denote`, and `MirAbsSlot.denote`, and
   refines `WrappedInterval` / `MirAbsSlot` bounds via certified linear
   inequalities.
4. **Reflective Entailment-Graph Specification Adequacy** (`arXiv:2611.31430`
   *CrossCheck* and `arXiv:2611.31571` *Entailment Graphs*): verifies
   multi-obligation entailment edges (fail-closed on certificate list length),
   graph/path transitivity, concrete non-vacuity satisfiability witnesses, and
   optional strictness counter-witnesses or bidirectional equivalence in a
   single `rfl`.
5. **Unified `FarkasMirGoal` / `FarkasMirCert` Schema**: packages all four
   obligation families behind a single reflective checker `checkFarkasMirGoal`
   and soundness theorem `checkFarkasMirGoal_sound`.
-/

namespace Anneal.FarkasMirCert

open Anneal.LinearArith
open Anneal.AiPcc
open Anneal.UnsafeObligations
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Core Constructive Helpers, `NatLinSpec` / `IntLinSpec`, & Relational Bridges -/

private theorem bool_and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | true => rfl
  | false => nomatch h

private theorem bool_and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | true => exact h
  | false => nomatch h

private theorem nat_ble_false_of_lt {a b : Nat} (h : a < b) :
    Nat.ble b a = false := by
  cases hb : Nat.ble b a with
  | false => rfl
  | true => exact False.elim (Nat.not_le_of_gt h (Nat.le_of_ble_eq_true hb))

private theorem nat_not_le_of_ble_false {a b : Nat} (h : Nat.ble a b = false) :
    ¬ (a ≤ b) := by
  intro hLe
  rw [Nat.ble_eq_true_of_le hLe] at h
  nomatch h

/-- Strict inequality on `Nat` from `a + 1 ≤ b`. -/
theorem nat_lt_of_add_one_le {a b : Nat} (h : a + 1 ≤ b) : a < b := h

/-- `a + 1 ≤ b` from strict inequality `a < b`. -/
theorem nat_add_one_le_of_lt {a b : Nat} (h : a < b) : a + 1 ≤ b := h

/-- Equality on `Nat` from two-sided `≤` bounds. -/
theorem nat_eq_of_le_antisymm {a b : Nat} (h1 : a ≤ b) (h2 : b ≤ a) : a = b :=
  Nat.le_antisymm h1 h2

/-- Conjunction of two `HypsImp` derivations over the same hypothesis list. -/
theorem hypsImp_and {α : Type} {f : α → Prop} {p q : Prop} :
    ∀ {xs : List α}, HypsImp f xs p → HypsImp f xs q → HypsImp f xs (p ∧ q)
  | [], hp, hq => ⟨hp, hq⟩
  | _ :: _, hp, hq => fun h => hypsImp_and (hp h) (hq h)

/-- Applies a curried `HypsImp` derivation to a universal list-membership proof. -/
theorem hypsImp_apply_all {α : Type} {f : α → Prop} {p : Prop} :
    ∀ (xs : List α), HypsImp f xs p → (∀ x, x ∈ xs → f x) → p
  | [], h, _ => h
  | x :: rest, h, hAll =>
    hypsImp_apply_all rest (h (hAll x (List.Mem.head rest)))
      (fun y hy => hAll y (List.Mem.tail x hy))

/-- Lifts a list-membership implication into a curried `HypsImp` chain. -/
theorem hypsImp_of_all_imp {α : Type} {f : α → Prop} {p : Prop} :
    ∀ (xs : List α), ((∀ x, x ∈ xs → f x) → p) → HypsImp f xs p
  | [], h => h (fun _ hm => nomatch hm)
  | x :: rest, h =>
    fun hx =>
      hypsImp_of_all_imp rest (fun hRest =>
        h (fun y hy => by
          cases hy with
          | head _ => exact hx
          | tail _ hTail => exact hRest y hTail))

/-- Discharges strict `Nat` inequality `lhs < rhs` from a `NatCutGoal` whose
conclusion encodes `lhs + 1 ≤ rhs`. -/
theorem checkNatCutGoal_lt_sound
    (hyps : List NatCutIneq) (lhs rhs : NatLinExpr) (steps : List CutStep)
    (hChk : checkNatCutGoal ⟨hyps, ⟨.add lhs (.cst 1), rhs⟩⟩ steps = true)
    (env : List Nat) :
    HypsImp (NatCutIneq.holds env) hyps (lhs.eval env < rhs.eval env) :=
  hypsImp_concl_mono nat_lt_of_add_one_le
    (checkNatCutGoal_sound ⟨hyps, ⟨.add lhs (.cst 1), rhs⟩⟩ steps hChk env)

/-- Discharges `Nat` equality `lhs = rhs` from a pair of `NatCutGoal`
certificates proving `lhs ≤ rhs` and `rhs ≤ lhs` under shared `hyps`. -/
theorem checkNatCutGoal_eq_sound
    (hyps : List NatCutIneq) (lhs rhs : NatLinExpr)
    (stepsLe stepsGe : List CutStep)
    (hLe : checkNatCutGoal ⟨hyps, ⟨lhs, rhs⟩⟩ stepsLe = true)
    (hGe : checkNatCutGoal ⟨hyps, ⟨rhs, lhs⟩⟩ stepsGe = true)
    (env : List Nat) :
    HypsImp (NatCutIneq.holds env) hyps (lhs.eval env = rhs.eval env) :=
  hypsImp_concl_mono (fun h => Nat.le_antisymm h.1 h.2)
    (hypsImp_and
      (checkNatCutGoal_sound ⟨hyps, ⟨lhs, rhs⟩⟩ stepsLe hLe env)
      (checkNatCutGoal_sound ⟨hyps, ⟨rhs, lhs⟩⟩ stepsGe hGe env))

/-- Discharges strict `Int` inequality `lhs < rhs` (`lhs + 1 ≤ rhs`) from an
`IntCutGoal` certificate. -/
theorem checkIntCutGoal_lt_sound
    (hyps : List IntCutIneq) (lhs rhs : IntLinExpr) (steps : List CutStep)
    (hChk : checkIntCutGoal ⟨hyps, ⟨.add lhs (.cst SInt.one), rhs⟩⟩ steps = true)
    (env : List Int) :
    HypsImp (IntCutIneq.holds env) hyps (lhs.eval env < rhs.eval env) :=
  checkIntCutGoal_sound ⟨hyps, ⟨.add lhs (.cst SInt.one), rhs⟩⟩ steps hChk env

/-- Discharges `Int` equality `lhs = rhs` from two-sided `IntCutGoal`
certificates under shared `hyps`. -/
theorem checkIntCutGoal_eq_sound
    (hyps : List IntCutIneq) (lhs rhs : IntLinExpr)
    (stepsLe stepsGe : List CutStep)
    (hLe : checkIntCutGoal ⟨hyps, ⟨lhs, rhs⟩⟩ stepsLe = true)
    (hGe : checkIntCutGoal ⟨hyps, ⟨rhs, lhs⟩⟩ stepsGe = true)
    (env : List Int) :
    HypsImp (IntCutIneq.holds env) hyps (lhs.eval env = rhs.eval env) :=
  hypsImp_concl_mono (fun h => by
    have ha := intBalance_self (lhs.eval env)
    have hb := intBalance_self (rhs.eval env)
    have h1 := (intBalance_le ha hb).1 h.1
    have h2 := (intBalance_le hb ha).1 h.2
    have hEqNat : intPos (lhs.eval env) + intNeg (rhs.eval env) =
        intPos (rhs.eval env) + intNeg (lhs.eval env) :=
      Nat.le_antisymm h1 h2
    exact intBalance_eq_of_eq ha (intBalance_of_add_eq hb hEqNat.symm))
    (hypsImp_and
      (checkIntCutGoal_sound ⟨hyps, ⟨lhs, rhs⟩⟩ stepsLe hLe env)
      (checkIntCutGoal_sound ⟨hyps, ⟨rhs, lhs⟩⟩ stepsGe hGe env))

/-- Conjunctive natural-number linear specification (`List NatCutIneq`). -/
abbrev NatLinSpec := List NatCutIneq

/-- Conjunctive integer linear specification (`List IntCutIneq`). -/
abbrev IntLinSpec := List IntCutIneq

/-- Semantic satisfaction of every inequality in `spec : NatLinSpec`. -/
def NatLinSpec.holds (env : List Nat) (spec : NatLinSpec) : Prop :=
  ∀ iq : NatCutIneq, iq ∈ spec → iq.holds env

/-- Semantic satisfaction of every inequality in `spec : IntLinSpec`. -/
def IntLinSpec.holds (env : List Int) (spec : IntLinSpec) : Prop :=
  ∀ iq : IntCutIneq, iq ∈ spec → iq.holds env

theorem natLinSpec_holds_nil (env : List Nat) : NatLinSpec.holds env [] :=
  fun _ hm => nomatch hm

theorem natLinSpec_holds_cons {env : List Nat} {iq : NatCutIneq} {rest : NatLinSpec}
    (hHead : iq.holds env) (hTail : NatLinSpec.holds env rest) :
    NatLinSpec.holds env (iq :: rest) := by
  intro q hq
  cases hq with
  | head _ => exact hHead
  | tail _ hT => exact hTail q hT

theorem intLinSpec_holds_nil (env : List Int) : IntLinSpec.holds env [] :=
  fun _ hm => nomatch hm

theorem intLinSpec_holds_cons {env : List Int} {iq : IntCutIneq} {rest : IntLinSpec}
    (hHead : iq.holds env) (hTail : IntLinSpec.holds env rest) :
    IntLinSpec.holds env (iq :: rest) := by
  intro q hq
  cases hq with
  | head _ => exact hHead
  | tail _ hT => exact hTail q hT

/-! ## 2. MIR Scalar Width Bounds & Overflow-Freedom Bridges -/

/-- Canonical unsigned MIR scalar range predicate: `sc` has byte width
`uintBytes u` and bit pattern strictly below `2 ^ (uintWidth u)`. -/
def UintScalarInRange (u : UintTy) (sc : ScalarInt) : Prop :=
  sc.sizeBytes = uintBytes u ∧ sc.bits < modPow2 (uintWidth u)

/-- Extracts `sc.bits < modPow2 (uintWidth u)` from `UintScalarInRange`. -/
theorem uintScalarInRange_lt {u : UintTy} {sc : ScalarInt}
    (h : UintScalarInRange u sc) : sc.bits < modPow2 (uintWidth u) :=
  h.2

/-- Extracts `sc.bits + 1 ≤ modPow2 (uintWidth u)` ready for `NatCutGoal`. -/
theorem uintScalarInRange_succ_le {u : UintTy} {sc : ScalarInt}
    (h : UintScalarInRange u sc) : sc.bits + 1 ≤ modPow2 (uintWidth u) :=
  h.2

/-- Extracts `sc.bits ≤ modPow2 (uintWidth u) - 1` from `UintScalarInRange`. -/
theorem uintScalarInRange_le_max {u : UintTy} {sc : ScalarInt}
    (h : UintScalarInRange u sc) : sc.bits ≤ modPow2 (uintWidth u) - 1 :=
  Nat.le_sub_one_of_lt h.2

/-- Extracts `sc.bits < scalarModulus (uintBytes u)` from `UintScalarInRange`. -/
theorem uintScalarInRange_lt_scalarModulus {u : UintTy} {sc : ScalarInt}
    (h : UintScalarInRange u sc) : sc.bits < scalarModulus (uintBytes u) := by
  rw [scalarModulus_uintBytes]
  exact h.2

/-- Extracts `UintScalarInRange` from an initialized `MirAbsSlot.uint` slot. -/
theorem uintScalarInRange_of_mirAbsSlot_uint {ty : Ty} {locals : List LocalSlot}
    {u : UintTy} {a : AbsVal} {sc : ScalarInt}
    (h : (MirAbsSlot.uint u a).denote ty locals (.init (.scalar sc))) :
    UintScalarInRange u sc :=
  ⟨h.2.1, (absVal_some_elim h.2.2).1⟩

/-- Extracts `UintScalarInRange` from an initialized `MirAbsSlot.uintCopy` slot. -/
theorem uintScalarInRange_of_mirAbsSlot_uintCopy {ty : Ty} {locals : List LocalSlot}
    {u : UintTy} {a : AbsVal} {src : Nat} {sc : ScalarInt}
    (h : (MirAbsSlot.uintCopy u a src).denote ty locals (.init (.scalar sc))) :
    UintScalarInRange u sc :=
  ⟨h.2.1, (absVal_some_elim h.2.2.1).1⟩

/-- Extracts `UintScalarInRange` from an initialized `MirAbsSlot.uintBoolPair` slot. -/
theorem uintScalarInRange_of_mirAbsSlot_uintBoolPair {ty : Ty} {locals : List LocalSlot}
    {u : UintTy} {a : AbsVal} {ov : BoolAbs} {sc : ScalarInt} {vb : Value}
    (h : (MirAbsSlot.uintBoolPair u a ov).denote ty locals
      (.init (.aggregate 0 [.scalar sc, vb]))) :
    UintScalarInRange u sc :=
  ⟨h.2.1, (absVal_some_elim h.2.2.1).1⟩

/-- Turns `UintScalarInRange u sc` (with `envLookupNat env v = sc.bits`) into
a `NatCutIneq` hypothesis `var v + 1 ≤ modPow2 (uintWidth u)`. -/
theorem natCutIneq_uint_bound_of_inRange {u : UintTy} {sc : ScalarInt}
    {env : List Nat} {v : Nat}
    (hRange : UintScalarInRange u sc) (hEnv : envLookupNat env v = sc.bits) :
    (⟨.add (.var v) (.cst 1), .cst (modPow2 (uintWidth u))⟩ : NatCutIneq).holds env := by
  dsimp [NatCutIneq.holds, NatLinExpr.eval]
  rw [hEnv]
  exact hRange.2

/-- Discharges `x < modPow2 (uintWidth u)` (and `UintScalarInRange u ⟨x, uintBytes u⟩`)
from a `NatCutGoal` certificate for `x + 1 ≤ modPow2 (uintWidth u)`. -/
theorem farkas_discharges_uint_in_range
    (u : UintTy) (hyps : List NatCutIneq) (xExpr : NatLinExpr)
    (steps : List CutStep)
    (hChk : checkNatCutGoal
      ⟨hyps, ⟨.add xExpr (.cst 1), .cst (modPow2 (uintWidth u))⟩⟩ steps = true)
    (env : List Nat) :
    HypsImp (NatCutIneq.holds env) hyps
      (xExpr.eval env < modPow2 (uintWidth u) ∧
       xExpr.eval env < scalarModulus (uintBytes u) ∧
       UintScalarInRange u ⟨xExpr.eval env, uintBytes u⟩) :=
  hypsImp_concl_mono (fun hLt => by
    have hMod : xExpr.eval env < scalarModulus (uintBytes u) := by
      rw [scalarModulus_uintBytes]
      exact hLt
    exact ⟨hLt, hMod, ⟨rfl, hLt⟩⟩)
    (checkNatCutGoal_lt_sound hyps xExpr (.cst (modPow2 (uintWidth u))) steps hChk env)

/-- Discharges unsigned addition overflow-freedom for any `u : UintTy` from a
`NatCutGoal` certificate proving `lhs + rhs + 1 ≤ modPow2 (uintWidth u)`:
proves the strict bound (`< modPow2 (uintWidth u)` and `< scalarModulus (uintBytes u)`),
exact `.addUnchecked` evaluation, and exact `.addWithOverflow` evaluation with
overflow bit `⟨0, 1⟩`. -/
theorem farkas_discharges_uint_add_no_overflow
    (u : UintTy) (hyps : List NatCutIneq) (lhsExpr rhsExpr : NatLinExpr)
    (steps : List CutStep)
    (hChk : checkNatCutGoal
      ⟨hyps, ⟨.add (.add lhsExpr rhsExpr) (.cst 1), .cst (modPow2 (uintWidth u))⟩⟩
      steps = true)
    (env : List Nat) (locals : List LocalSlot) (mem : Memory) :
    HypsImp (NatCutIneq.holds env) hyps
      (lhsExpr.eval env + rhsExpr.eval env < modPow2 (uintWidth u) ∧
       lhsExpr.eval env + rhsExpr.eval env < scalarModulus (uintBytes u) ∧
       evalScalarBinOp .addUnchecked
         ⟨lhsExpr.eval env, uintBytes u⟩ ⟨rhsExpr.eval env, uintBytes u⟩
         locals mem false =
         .ok (.scalar ⟨lhsExpr.eval env + rhsExpr.eval env, uintBytes u⟩) locals mem ∧
       evalScalarBinOp .addWithOverflow
         ⟨lhsExpr.eval env, uintBytes u⟩ ⟨rhsExpr.eval env, uintBytes u⟩
         locals mem false =
         .ok (.aggregate 0
           [.scalar ⟨lhsExpr.eval env + rhsExpr.eval env, uintBytes u⟩,
            .scalar ⟨0, 1⟩]) locals mem) :=
  hypsImp_concl_mono (fun hLt => by
    dsimp only [NatLinExpr.eval] at hLt
    have hMod : lhsExpr.eval env + rhsExpr.eval env < scalarModulus (uintBytes u) := by
      rw [scalarModulus_uintBytes]
      exact hLt
    have hUnchk := evalScalarBinOp_uint_addUnchecked (u := u) locals mem hLt
    rw [wrapVal_of_lt hLt] at hUnchk
    have hWithOv := evalScalarBinOp_uint_addWithOverflow (u := u)
      (a := lhsExpr.eval env) (b := rhsExpr.eval env) locals mem
    rw [wrapVal_of_lt hLt, nat_ble_false_of_lt hLt] at hWithOv
    exact ⟨hLt, hMod, hUnchk, hWithOv⟩)
    (checkNatCutGoal_lt_sound hyps (.add lhsExpr rhsExpr)
      (.cst (modPow2 (uintWidth u))) steps hChk env)

/-- Specialized `u64` unsigned addition overflow-freedom bridge. -/
theorem farkas_discharges_u64_add_no_overflow
    (hyps : List NatCutIneq) (lhsExpr rhsExpr : NatLinExpr)
    (steps : List CutStep)
    (hChk : checkNatCutGoal
      ⟨hyps, ⟨.add (.add lhsExpr rhsExpr) (.cst 1), .cst (modPow2 (uintWidth .u64))⟩⟩
      steps = true)
    (env : List Nat) (locals : List LocalSlot) (mem : Memory) :
    HypsImp (NatCutIneq.holds env) hyps
      (lhsExpr.eval env + rhsExpr.eval env < modPow2 (uintWidth .u64) ∧
       lhsExpr.eval env + rhsExpr.eval env < scalarModulus (uintBytes .u64) ∧
       evalScalarBinOp .addUnchecked
         ⟨lhsExpr.eval env, uintBytes .u64⟩ ⟨rhsExpr.eval env, uintBytes .u64⟩
         locals mem false =
         .ok (.scalar ⟨lhsExpr.eval env + rhsExpr.eval env, uintBytes .u64⟩) locals mem ∧
       evalScalarBinOp .addWithOverflow
         ⟨lhsExpr.eval env, uintBytes .u64⟩ ⟨rhsExpr.eval env, uintBytes .u64⟩
         locals mem false =
         .ok (.aggregate 0
           [.scalar ⟨lhsExpr.eval env + rhsExpr.eval env, uintBytes .u64⟩,
            .scalar ⟨0, 1⟩]) locals mem) :=
  farkas_discharges_uint_add_no_overflow .u64 hyps lhsExpr rhsExpr steps hChk env locals mem

/-- Discharges unsigned subtraction underflow-freedom for any `u : UintTy`
from a `NatCutGoal` certificate proving `rhs ≤ lhs` together with an in-range
bound `lhs < modPow2 (uintWidth u)`: proves `rhs ≤ lhs`,
`lhs - rhs < modPow2 (uintWidth u)`, exact `.subUnchecked` evaluation, and
exact `.subWithOverflow` evaluation with overflow bit `⟨0, 1⟩`. -/
theorem farkas_discharges_uint_sub_no_underflow
    (u : UintTy) (hyps : List NatCutIneq) (lhsExpr rhsExpr : NatLinExpr)
    (steps : List CutStep)
    (hChk : checkNatCutGoal ⟨hyps, ⟨rhsExpr, lhsExpr⟩⟩ steps = true)
    (env : List Nat) (locals : List LocalSlot) (mem : Memory)
    (hLhsLt : lhsExpr.eval env < modPow2 (uintWidth u)) :
    HypsImp (NatCutIneq.holds env) hyps
      (rhsExpr.eval env ≤ lhsExpr.eval env ∧
       lhsExpr.eval env - rhsExpr.eval env < modPow2 (uintWidth u) ∧
       evalScalarBinOp .subUnchecked
         ⟨lhsExpr.eval env, uintBytes u⟩ ⟨rhsExpr.eval env, uintBytes u⟩
         locals mem false =
         .ok (.scalar ⟨lhsExpr.eval env - rhsExpr.eval env, uintBytes u⟩) locals mem ∧
       evalScalarBinOp .subWithOverflow
         ⟨lhsExpr.eval env, uintBytes u⟩ ⟨rhsExpr.eval env, uintBytes u⟩
         locals mem false =
         .ok (.aggregate 0
           [.scalar ⟨lhsExpr.eval env - rhsExpr.eval env, uintBytes u⟩,
            .scalar ⟨0, 1⟩]) locals mem) :=
  hypsImp_concl_mono (fun hLe => by
    have hDiffLt : lhsExpr.eval env - rhsExpr.eval env < modPow2 (uintWidth u) :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) hLhsLt
    have hRhsLt : rhsExpr.eval env < modPow2 (uintWidth u) :=
      Nat.lt_of_le_of_lt hLe hLhsLt
    have hUnchk := evalScalarBinOp_uint_subUnchecked (u := u) locals mem hLhsLt hLe
    rw [← wrapVal_sub_of_le hLe hLhsLt, wrapVal_of_lt hDiffLt] at hUnchk
    have hWithOv := evalScalarBinOp_uint_subWithOverflow (u := u) locals mem hLhsLt hRhsLt
    rw [← wrapVal_sub_of_le hLe hLhsLt, wrapVal_of_lt hDiffLt,
        Nat.ble_eq_true_of_le hLe] at hWithOv
    exact ⟨hLe, hDiffLt, hUnchk, hWithOv⟩)
    (checkNatCutGoal_sound ⟨hyps, ⟨rhsExpr, lhsExpr⟩⟩ steps hChk env)

/-- Fully certificate-derived variant of `farkas_discharges_uint_sub_no_underflow`:
the in-range operand bound `lhs < modPow2 (uintWidth u)` is no longer an
external hypothesis but is itself discharged by a second `NatCutGoal`
certificate proving `lhs + 1 ≤ modPow2 (uintWidth u)` from the same `hyps`. -/
theorem farkas_discharges_uint_sub_no_underflow_certified
    (u : UintTy) (hyps : List NatCutIneq) (lhsExpr rhsExpr : NatLinExpr)
    (stepsLe stepsRange : List CutStep)
    (hChkLe : checkNatCutGoal ⟨hyps, ⟨rhsExpr, lhsExpr⟩⟩ stepsLe = true)
    (hChkRange : checkNatCutGoal
      ⟨hyps, ⟨.add lhsExpr (.cst 1), .cst (modPow2 (uintWidth u))⟩⟩ stepsRange = true)
    (env : List Nat) (locals : List LocalSlot) (mem : Memory) :
    HypsImp (NatCutIneq.holds env) hyps
      (lhsExpr.eval env < modPow2 (uintWidth u) ∧
       rhsExpr.eval env ≤ lhsExpr.eval env ∧
       lhsExpr.eval env - rhsExpr.eval env < modPow2 (uintWidth u) ∧
       evalScalarBinOp .subUnchecked
         ⟨lhsExpr.eval env, uintBytes u⟩ ⟨rhsExpr.eval env, uintBytes u⟩
         locals mem false =
         .ok (.scalar ⟨lhsExpr.eval env - rhsExpr.eval env, uintBytes u⟩) locals mem ∧
       evalScalarBinOp .subWithOverflow
         ⟨lhsExpr.eval env, uintBytes u⟩ ⟨rhsExpr.eval env, uintBytes u⟩
         locals mem false =
         .ok (.aggregate 0
           [.scalar ⟨lhsExpr.eval env - rhsExpr.eval env, uintBytes u⟩,
            .scalar ⟨0, 1⟩]) locals mem) :=
  hypsImp_of_all_imp hyps (fun hAll =>
    have hLt : lhsExpr.eval env < modPow2 (uintWidth u) :=
      hypsImp_apply_all hyps
        (checkNatCutGoal_lt_sound hyps lhsExpr (.cst (modPow2 (uintWidth u)))
          stepsRange hChkRange env) hAll
    ⟨hLt, hypsImp_apply_all hyps
      (farkas_discharges_uint_sub_no_underflow u hyps lhsExpr rhsExpr stepsLe hChkLe
        env locals mem hLt) hAll⟩)

/-- Discharges constant-scaled unsigned multiplication overflow-freedom
`k * x < modPow2 (uintWidth u)` for any `u : UintTy` from `k < 2^width` and a
`NatCutGoal` certificate proving `k * x + 1 ≤ modPow2 (uintWidth u)`: proves
`UintScalarInRange u ⟨k, uintBytes u⟩`, the strict product bound, exact
`.mulUnchecked` evaluation, and exact `.mulWithOverflow` evaluation with
overflow bit `⟨0, 1⟩`. -/
theorem farkas_discharges_uint_mul_const_no_overflow
    (u : UintTy) (hyps : List NatCutIneq) (k : Nat) (xExpr : NatLinExpr)
    (steps : List CutStep)
    (hKRange : Nat.blt k (modPow2 (uintWidth u)) = true)
    (hChk : checkNatCutGoal
      ⟨hyps, ⟨.add (.mulC k xExpr) (.cst 1), .cst (modPow2 (uintWidth u))⟩⟩
      steps = true)
    (env : List Nat) (locals : List LocalSlot) (mem : Memory) :
    HypsImp (NatCutIneq.holds env) hyps
      (UintScalarInRange u ⟨k, uintBytes u⟩ ∧
       k * xExpr.eval env < modPow2 (uintWidth u) ∧
       k * xExpr.eval env < scalarModulus (uintBytes u) ∧
       evalScalarBinOp .mulUnchecked
         ⟨k, uintBytes u⟩ ⟨xExpr.eval env, uintBytes u⟩
         locals mem false =
         .ok (.scalar ⟨k * xExpr.eval env, uintBytes u⟩) locals mem ∧
       evalScalarBinOp .mulWithOverflow
         ⟨k, uintBytes u⟩ ⟨xExpr.eval env, uintBytes u⟩
         locals mem false =
         .ok (.aggregate 0
           [.scalar ⟨k * xExpr.eval env, uintBytes u⟩,
            .scalar ⟨0, 1⟩]) locals mem) :=
  hypsImp_concl_mono (fun hLt => by
    dsimp only [NatLinExpr.eval] at hLt
    have hKInRange : UintScalarInRange u ⟨k, uintBytes u⟩ :=
      ⟨rfl, lt_of_blt_true hKRange⟩
    have hMod : k * xExpr.eval env < scalarModulus (uintBytes u) := by
      rw [scalarModulus_uintBytes]
      exact hLt
    have hUnchk := evalScalarBinOp_uint_mulUnchecked (u := u) locals mem hLt
    rw [wrapVal_of_lt hLt] at hUnchk
    have hWithOv := evalScalarBinOp_uint_mulWithOverflow (u := u)
      (a := k) (b := xExpr.eval env) locals mem
    rw [wrapVal_of_lt hLt, nat_ble_false_of_lt hLt] at hWithOv
    exact ⟨hKInRange, hLt, hMod, hUnchk, hWithOv⟩)
    (checkNatCutGoal_lt_sound hyps (.mulC k xExpr)
      (.cst (modPow2 (uintWidth u))) steps hChk env)

/-- From `0 < k` and `k * x < modPow2 (uintWidth u)`, derives
`UintScalarInRange u ⟨x, uintBytes u⟩` (so the variable operand of a positive
constant-scaled multiplication is automatically in-range). -/
theorem uintScalarInRange_rhs_of_mul_const_pos {u : UintTy} {k x : Nat}
    (hkPos : 0 < k) (hProd : k * x < modPow2 (uintWidth u)) :
    UintScalarInRange u ⟨x, uintBytes u⟩ := by
  have hxLe : x ≤ k * x := by
    have h1 : 1 * x ≤ k * x := Nat.mul_le_mul_right x hkPos
    rw [Nat.one_mul] at h1
    exact h1
  exact ⟨rfl, Nat.lt_of_le_of_lt hxLe hProd⟩

/-- Right-constant variant of `farkas_discharges_uint_mul_const_no_overflow`:
discharges `x * k < modPow2 (uintWidth u)` and exact `.mulUnchecked` /
`.mulWithOverflow` evaluation for `⟨x, uintBytes u⟩ * ⟨k, uintBytes u⟩` from
the same `k * x + 1 ≤ modPow2 (uintWidth u)` certificate. -/
theorem farkas_discharges_uint_mul_const_right_no_overflow
    (u : UintTy) (hyps : List NatCutIneq) (xExpr : NatLinExpr) (k : Nat)
    (steps : List CutStep)
    (hKRange : Nat.blt k (modPow2 (uintWidth u)) = true)
    (hChk : checkNatCutGoal
      ⟨hyps, ⟨.add (.mulC k xExpr) (.cst 1), .cst (modPow2 (uintWidth u))⟩⟩
      steps = true)
    (env : List Nat) (locals : List LocalSlot) (mem : Memory) :
    HypsImp (NatCutIneq.holds env) hyps
      (UintScalarInRange u ⟨k, uintBytes u⟩ ∧
       xExpr.eval env * k < modPow2 (uintWidth u) ∧
       xExpr.eval env * k < scalarModulus (uintBytes u) ∧
       evalScalarBinOp .mulUnchecked
         ⟨xExpr.eval env, uintBytes u⟩ ⟨k, uintBytes u⟩
         locals mem false =
         .ok (.scalar ⟨xExpr.eval env * k, uintBytes u⟩) locals mem ∧
       evalScalarBinOp .mulWithOverflow
         ⟨xExpr.eval env, uintBytes u⟩ ⟨k, uintBytes u⟩
         locals mem false =
         .ok (.aggregate 0
           [.scalar ⟨xExpr.eval env * k, uintBytes u⟩,
            .scalar ⟨0, 1⟩]) locals mem) :=
  hypsImp_concl_mono (fun hLt => by
    dsimp only [NatLinExpr.eval] at hLt
    have hKInRange : UintScalarInRange u ⟨k, uintBytes u⟩ :=
      ⟨rfl, lt_of_blt_true hKRange⟩
    have hLtR : xExpr.eval env * k < modPow2 (uintWidth u) := by
      rw [Nat.mul_comm]
      exact hLt
    have hMod : xExpr.eval env * k < scalarModulus (uintBytes u) := by
      rw [scalarModulus_uintBytes]
      exact hLtR
    have hUnchk := evalScalarBinOp_uint_mulUnchecked (u := u) locals mem hLtR
    rw [wrapVal_of_lt hLtR] at hUnchk
    have hWithOv := evalScalarBinOp_uint_mulWithOverflow (u := u)
      (a := xExpr.eval env) (b := k) locals mem
    rw [wrapVal_of_lt hLtR, nat_ble_false_of_lt hLtR] at hWithOv
    exact ⟨hKInRange, hLtR, hMod, hUnchk, hWithOv⟩)
    (checkNatCutGoal_lt_sound hyps (.mulC k xExpr)
      (.cst (modPow2 (uintWidth u))) steps hChk env)

/-! ## 3. `Anneal.UnsafeObligations` Bridges -/

/-- Discharges `ValidSliceRange rp len totalLen` and the operational
`evalPtrOffset` corollary from a `NatCutGoal` certificate proving
`off + len ≤ total`. -/
theorem farkas_discharges_slice_bounds
    (hyps : List NatCutIneq) (offExpr lenExpr totalExpr : NatLinExpr)
    (steps : List CutStep)
    (hChk : checkNatCutGoal ⟨hyps, ⟨.add offExpr lenExpr, totalExpr⟩⟩ steps = true)
    (env : List Nat) (rp : RawPtrVal)
    (hOff : rp.offset = offExpr.eval env) :
    HypsImp (NatCutIneq.holds env) hyps
      (ValidSliceRange rp (lenExpr.eval env) (totalExpr.eval env) ∧
       evalPtrOffset rp (lenExpr.eval env) (totalExpr.eval env) =
         some { rp with offset := rp.offset + lenExpr.eval env }) :=
  hypsImp_concl_mono (fun hBound => by
    have hRange : ValidSliceRange rp (lenExpr.eval env) (totalExpr.eval env) := by
      unfold ValidSliceRange
      rw [hOff]
      exact hBound
    exact ⟨hRange, evalPtrOffset_of_validSliceRange rp _ _ hRange⟩)
    (checkNatCutGoal_sound ⟨hyps, ⟨.add offExpr lenExpr, totalExpr⟩⟩ steps hChk env)

/-- Discharges `ValidSliceSplit rp elemSize total mid right` (and the
`evalPtrOffset` split-pointer corollary) from two-sided `NatCutGoal`
certificates proving `mid + right = total`. -/
theorem farkas_discharges_slice_split
    (hyps : List NatCutIneq) (midExpr rightExpr totalExpr : NatLinExpr)
    (stepsLe stepsGe : List CutStep)
    (hChkLe : checkNatCutGoal ⟨hyps, ⟨.add midExpr rightExpr, totalExpr⟩⟩ stepsLe = true)
    (hChkGe : checkNatCutGoal ⟨hyps, ⟨totalExpr, .add midExpr rightExpr⟩⟩ stepsGe = true)
    (env : List Nat) (rp : RawPtrVal) (elemSize : Nat) :
    HypsImp (NatCutIneq.holds env) hyps
      (ValidSliceSplit rp elemSize (totalExpr.eval env)
         (midExpr.eval env) (rightExpr.eval env) ∧
       evalPtrOffset rp (midExpr.eval env * elemSize)
         (rp.offset + totalExpr.eval env * elemSize) =
         some (sliceSplitRightPtr rp elemSize (midExpr.eval env))) :=
  hypsImp_concl_mono (fun hPart => by
    dsimp only [NatLinExpr.eval] at hPart
    have hFull : ValidSliceRange rp (totalExpr.eval env * elemSize)
        (rp.offset + totalExpr.eval env * elemSize) :=
      Nat.le_refl _
    have hLeft : ValidSliceRange rp (midExpr.eval env * elemSize)
        (rp.offset + totalExpr.eval env * elemSize) := by
      unfold ValidSliceRange
      rw [← hPart]
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_right elemSize (Nat.le_add_right _ _)) rp.offset
    have hRight : ValidSliceRange (sliceSplitRightPtr rp elemSize (midExpr.eval env))
        (rightExpr.eval env * elemSize) (rp.offset + totalExpr.eval env * elemSize) := by
      unfold ValidSliceRange sliceSplitRightPtr
      dsimp only
      rw [Nat.add_assoc, ← Nat.add_mul, hPart]
      exact Nat.le_refl _
    have hSplit : ValidSliceSplit rp elemSize (totalExpr.eval env)
        (midExpr.eval env) (rightExpr.eval env) :=
      ⟨hFull, hPart, hLeft, hRight⟩
    exact ⟨hSplit, evalPtrOffset_of_validSliceSplit hSplit⟩)
    (checkNatCutGoal_eq_sound hyps (.add midExpr rightExpr) totalExpr
      stepsLe stepsGe hChkLe hChkGe env)

/-- Discharges `AlignedPtr rp alignBytes` from `alignBytes ≥ 1` and two-sided
`NatCutGoal` certificates proving `alignBytes * quot = off` (including traces
that apply Chvatal-Gomory `CutStep.divCut` on scaled stride equations). -/
theorem farkas_discharges_aligned_stride
    (hyps : List NatCutIneq) (alignBytes : Nat)
    (offExpr quotExpr : NatLinExpr)
    (stepsLe stepsGe : List CutStep)
    (hAlignPos : Nat.ble 1 alignBytes = true)
    (hChkLe : checkNatCutGoal ⟨hyps, ⟨.mulC alignBytes quotExpr, offExpr⟩⟩ stepsLe = true)
    (hChkGe : checkNatCutGoal ⟨hyps, ⟨offExpr, .mulC alignBytes quotExpr⟩⟩ stepsGe = true)
    (env : List Nat) (rp : RawPtrVal)
    (hOff : rp.offset = offExpr.eval env) :
    HypsImp (NatCutIneq.holds env) hyps (AlignedPtr rp alignBytes) :=
  hypsImp_concl_mono (fun hEq => by
    refine ⟨Nat.le_of_ble_eq_true hAlignPos, ?_⟩
    rw [hOff, ← hEq]
    exact Nat.mul_mod_right alignBytes (quotExpr.eval env))
    (checkNatCutGoal_eq_sound hyps (.mulC alignBytes quotExpr) offExpr
      stepsLe stepsGe hChkLe hChkGe env)

/-- Preserves `AlignedPtr` when advancing an already-aligned base pointer by a
Farkas-certified stride multiple `delta = alignBytes * qs`. -/
theorem farkas_discharges_aligned_base_plus_stride
    (hyps : List NatCutIneq) (alignBytes : Nat)
    (deltaExpr qsExpr : NatLinExpr)
    (stepsLe stepsGe : List CutStep)
    (hChkLe : checkNatCutGoal ⟨hyps, ⟨.mulC alignBytes qsExpr, deltaExpr⟩⟩ stepsLe = true)
    (hChkGe : checkNatCutGoal ⟨hyps, ⟨deltaExpr, .mulC alignBytes qsExpr⟩⟩ stepsGe = true)
    (env : List Nat) (rp : RawPtrVal)
    (hBaseAlign : AlignedPtr rp alignBytes) :
    HypsImp (NatCutIneq.holds env) hyps
      (AlignedPtr { rp with offset := rp.offset + deltaExpr.eval env } alignBytes) :=
  hypsImp_concl_mono (fun hDeltaEq => by
    refine ⟨hBaseAlign.1, ?_⟩
    dsimp only
    rw [← hDeltaEq]
    change Nat.mod (rp.offset + alignBytes * qsExpr.eval env) alignBytes = 0
    rw [nat_add_mul_mod_self_left]
    exact hBaseAlign.2)
    (checkNatCutGoal_eq_sound hyps (.mulC alignBytes qsExpr) deltaExpr
      stepsLe stepsGe hChkLe hChkGe env)

/-- Separation orientation for `NonOverlappingPtrs` certificates. -/
inductive NonOverlapDir where
  /-- Source range precedes destination range: `src.offset + count ≤ dst.offset`. -/
  | srcBeforeDst
  /-- Destination range precedes source range: `dst.offset + count ≤ src.offset`. -/
  | dstBeforeSrc

/-- Target inequality selected by `dir : NonOverlapDir`. -/
def nonOverlapTargetIneq (srcOffExpr dstOffExpr countExpr : NatLinExpr) :
    NonOverlapDir → NatCutIneq
  | .srcBeforeDst => ⟨.add srcOffExpr countExpr, dstOffExpr⟩
  | .dstBeforeSrc => ⟨.add dstOffExpr countExpr, srcOffExpr⟩

/-- Discharges `NonOverlappingPtrs src dst count` via a `NatCutGoal` certificate
proving either `src.offset + count ≤ dst.offset` (`.srcBeforeDst`) or
`dst.offset + count ≤ src.offset` (`.dstBeforeSrc`). -/
theorem farkas_discharges_non_overlapping_ptrs
    (hyps : List NatCutIneq)
    (srcOffExpr dstOffExpr countExpr : NatLinExpr)
    (dir : NonOverlapDir) (steps : List CutStep)
    (hChk : checkNatCutGoal
      ⟨hyps, nonOverlapTargetIneq srcOffExpr dstOffExpr countExpr dir⟩ steps = true)
    (env : List Nat) (src dst : RawPtrVal)
    (hSrcOff : src.offset = srcOffExpr.eval env)
    (hDstOff : dst.offset = dstOffExpr.eval env) :
    HypsImp (NatCutIneq.holds env) hyps
      (NonOverlappingPtrs src dst (countExpr.eval env)) := by
  cases dir with
  | srcBeforeDst =>
    exact hypsImp_concl_mono (fun hLe => by
      refine Or.inr (Or.inr (Or.inl ?_))
      rw [hSrcOff, hDstOff]
      exact hLe)
      (checkNatCutGoal_sound ⟨hyps, ⟨.add srcOffExpr countExpr, dstOffExpr⟩⟩ steps hChk env)
  | dstBeforeSrc =>
    exact hypsImp_concl_mono (fun hLe => by
      refine Or.inr (Or.inr (Or.inr ?_))
      rw [hSrcOff, hDstOff]
      exact hLe)
      (checkNatCutGoal_sound ⟨hyps, ⟨.add dstOffExpr countExpr, srcOffExpr⟩⟩ steps hChk env)

/-- Convenience wrapper for `farkas_discharges_non_overlapping_ptrs` when
`src.offset + count ≤ dst.offset`. -/
theorem farkas_discharges_non_overlapping_ptrs_left
    (hyps : List NatCutIneq) (srcOffExpr dstOffExpr countExpr : NatLinExpr)
    (steps : List CutStep)
    (hChk : checkNatCutGoal ⟨hyps, ⟨.add srcOffExpr countExpr, dstOffExpr⟩⟩ steps = true)
    (env : List Nat) (src dst : RawPtrVal)
    (hSrcOff : src.offset = srcOffExpr.eval env)
    (hDstOff : dst.offset = dstOffExpr.eval env) :
    HypsImp (NatCutIneq.holds env) hyps
      (NonOverlappingPtrs src dst (countExpr.eval env)) :=
  farkas_discharges_non_overlapping_ptrs hyps srcOffExpr dstOffExpr countExpr
    .srcBeforeDst steps hChk env src dst hSrcOff hDstOff

/-- Convenience wrapper for `farkas_discharges_non_overlapping_ptrs` when
`dst.offset + count ≤ src.offset`. -/
theorem farkas_discharges_non_overlapping_ptrs_right
    (hyps : List NatCutIneq) (srcOffExpr dstOffExpr countExpr : NatLinExpr)
    (steps : List CutStep)
    (hChk : checkNatCutGoal ⟨hyps, ⟨.add dstOffExpr countExpr, srcOffExpr⟩⟩ steps = true)
    (env : List Nat) (src dst : RawPtrVal)
    (hSrcOff : src.offset = srcOffExpr.eval env)
    (hDstOff : dst.offset = dstOffExpr.eval env) :
    HypsImp (NatCutIneq.holds env) hyps
      (NonOverlappingPtrs src dst (countExpr.eval env)) :=
  farkas_discharges_non_overlapping_ptrs hyps srcOffExpr dstOffExpr countExpr
    .dstBeforeSrc steps hChk env src dst hSrcOff hDstOff

/-- Discharges `ValidArrayToSliceCast rp elemSize elemAlign arrayLen allocLen`
(and the end-pointer `evalPtrOffset` corollary) by composing alignment
certificates (`elemAlign * quot = off`) with a slice-range certificate
(`off + elemSize * arrayLen ≤ allocLen`). -/
theorem farkas_discharges_array_to_slice_cast
    (hyps : List NatCutIneq) (elemSize elemAlign : Nat)
    (offExpr quotExpr arrayLenExpr allocLenExpr : NatLinExpr)
    (stepsAlignLe stepsAlignGe stepsRange : List CutStep)
    (hAlignPos : Nat.ble 1 elemAlign = true)
    (hChkAlignLe :
      checkNatCutGoal ⟨hyps, ⟨.mulC elemAlign quotExpr, offExpr⟩⟩ stepsAlignLe = true)
    (hChkAlignGe :
      checkNatCutGoal ⟨hyps, ⟨offExpr, .mulC elemAlign quotExpr⟩⟩ stepsAlignGe = true)
    (hChkRange :
      checkNatCutGoal
        ⟨hyps, ⟨.add offExpr (.mulC elemSize arrayLenExpr), allocLenExpr⟩⟩
        stepsRange = true)
    (env : List Nat) (rp : RawPtrVal)
    (hOff : rp.offset = offExpr.eval env) :
    HypsImp (NatCutIneq.holds env) hyps
      (ValidArrayToSliceCast rp elemSize elemAlign
         (arrayLenExpr.eval env) (allocLenExpr.eval env) ∧
       evalPtrOffset rp (arrayLenExpr.eval env * elemSize) (allocLenExpr.eval env) =
         some { rp with offset := rp.offset + arrayLenExpr.eval env * elemSize }) :=
  hypsImp_concl_mono (fun hPair => by
    have hRange : ValidSliceRange rp (arrayLenExpr.eval env * elemSize)
        (allocLenExpr.eval env) := by
      unfold ValidSliceRange
      rw [hOff, Nat.mul_comm]
      exact hPair.2
    have hCast : ValidArrayToSliceCast rp elemSize elemAlign
        (arrayLenExpr.eval env) (allocLenExpr.eval env) :=
      ⟨hPair.1, hRange⟩
    exact ⟨hCast, evalPtrOffset_end_of_validArrayToSliceCast hCast⟩)
    (hypsImp_and
      (farkas_discharges_aligned_stride hyps elemAlign offExpr quotExpr
        stepsAlignLe stepsAlignGe hAlignPos hChkAlignLe hChkAlignGe env rp hOff)
      (checkNatCutGoal_sound
        ⟨hyps, ⟨.add offExpr (.mulC elemSize arrayLenExpr), allocLenExpr⟩⟩
        stepsRange hChkRange env))

/-- Discharges `UnalignRawPtrSafe rp innerSize allocLen` constructively from a
`NatCutGoal` slice-range certificate. -/
theorem farkas_discharges_unalign_raw_ptr_safe
    (hyps : List NatCutIneq) (offExpr innerExpr allocExpr : NatLinExpr)
    (steps : List CutStep)
    (hChk : checkNatCutGoal ⟨hyps, ⟨.add offExpr innerExpr, allocExpr⟩⟩ steps = true)
    (env : List Nat) (rp : RawPtrVal)
    (hOff : rp.offset = offExpr.eval env) :
    HypsImp (NatCutIneq.holds env) hyps
      (UnalignRawPtrSafe rp (innerExpr.eval env) (allocExpr.eval env)) :=
  hypsImp_concl_mono (fun h =>
    ⟨⟨Nat.zero_lt_succ 0, Nat.mod_one rp.offset⟩, h.1⟩)
    (farkas_discharges_slice_bounds hyps offExpr innerExpr allocExpr steps hChk env rp hOff)

/-! ## 4. `Anneal.AiPcc` Bridges (`WrappedInterval`, `AbsVal`, & `MirAbsSlot`) -/

/-- Extracts `lo ≤ x`, `x ≤ hi`, and `x + 1 ≤ M` from a non-wrapping
`WrappedInterval.denote M (.iv lo hi) x` (when `Nat.ble lo hi = true`). -/
theorem wrappedInterval_denote_bounds {M lo hi x : Nat}
    (hNonWrap : Nat.ble lo hi = true)
    (h : WrappedInterval.denote M (.iv lo hi) x) :
    lo ≤ x ∧ x ≤ hi ∧ x + 1 ≤ M := by
  dsimp only [WrappedInterval.denote] at h
  rw [hNonWrap] at h
  exact ⟨h.2.2.2.1, h.2.2.2.2, h.2.2.1⟩

/-- Extracts `x + 1 ≤ modPow2 (uintWidth u)` plus optional non-wrapping
interval lower/upper bounds from `AbsVal.denote (uintWidth u) a (some x)`. -/
theorem absVal_denote_bounds {u : UintTy} {a : AbsVal} {x : Nat}
    (h : AbsVal.denote (uintWidth u) a (some x)) :
    x + 1 ≤ modPow2 (uintWidth u) ∧
    (∀ lo, a.lbound? = some lo → lo ≤ x) ∧
    (∀ hi, a.ubound? = some hi → x ≤ hi) :=
  ⟨(absVal_some_elim h).1,
   fun _ hLo => absVal_lbound?_sound hLo h,
   fun _ hHi => absVal_ubound?_sound hHi h⟩

/-- Extracts `lo ≤ x`, `x ≤ hi`, and `x + 1 ≤ modPow2 (uintWidth u)` directly
from an `AbsVal` whose `wi` component is a non-wrapping `.iv lo hi`. -/
theorem absVal_denote_iv_bounds {u : UintTy} {initDom : InitDom} {t : Tnum}
    {lo hi : Nat} {sc : StridedCong} {x : Nat}
    (hNonWrap : Nat.ble lo hi = true)
    (h : AbsVal.denote (uintWidth u) ⟨initDom, t, .iv lo hi, sc⟩ (some x)) :
    lo ≤ x ∧ x ≤ hi ∧ x + 1 ≤ modPow2 (uintWidth u) :=
  wrappedInterval_denote_bounds hNonWrap (absVal_some_elim h).2.2.1

/-- Extracts `lo ≤ sc.bits`, `sc.bits ≤ hi`, and
`sc.bits + 1 ≤ modPow2 (uintWidth u)` from a `MirAbsSlot.uint` denotation
carrying a non-wrapping interval `.iv lo hi`. -/
theorem mirAbsSlot_uint_iv_bounds {ty : Ty} {locals : List LocalSlot}
    {u : UintTy} {initDom : InitDom} {t : Tnum} {lo hi : Nat} {sg : StridedCong}
    {sc : ScalarInt} (hNonWrap : Nat.ble lo hi = true)
    (h : (MirAbsSlot.uint u ⟨initDom, t, .iv lo hi, sg⟩).denote ty locals
      (.init (.scalar sc))) :
    lo ≤ sc.bits ∧ sc.bits ≤ hi ∧ sc.bits + 1 ≤ modPow2 (uintWidth u) :=
  absVal_denote_iv_bounds hNonWrap h.2.2

/-- Extracts `lo ≤ sc.bits`, `sc.bits ≤ hi`, and
`sc.bits + 1 ≤ modPow2 (uintWidth u)` from a `MirAbsSlot.uintCopy` denotation
carrying a non-wrapping interval `.iv lo hi`. -/
theorem mirAbsSlot_uintCopy_iv_bounds {ty : Ty} {locals : List LocalSlot}
    {u : UintTy} {initDom : InitDom} {t : Tnum} {lo hi : Nat} {sg : StridedCong}
    {src : Nat} {sc : ScalarInt} (hNonWrap : Nat.ble lo hi = true)
    (h : (MirAbsSlot.uintCopy u ⟨initDom, t, .iv lo hi, sg⟩ src).denote ty locals
      (.init (.scalar sc))) :
    lo ≤ sc.bits ∧ sc.bits ≤ hi ∧ sc.bits + 1 ≤ modPow2 (uintWidth u) :=
  absVal_denote_iv_bounds hNonWrap h.2.2.1

/-- Packages extracted `WrappedInterval` bounds as `NatCutIneq.holds`
hypotheses ready for `NatCutGoal`. -/
theorem natCutIneqs_of_wrappedInterval {M lo hi x : Nat} {env : List Nat} {v : Nat}
    (hNonWrap : Nat.ble lo hi = true)
    (h : WrappedInterval.denote M (.iv lo hi) x)
    (hEnv : envLookupNat env v = x) :
    (⟨.cst lo, .var v⟩ : NatCutIneq).holds env ∧
    (⟨.var v, .cst hi⟩ : NatCutIneq).holds env ∧
    (⟨.add (.var v) (.cst 1), .cst M⟩ : NatCutIneq).holds env := by
  have hB := wrappedInterval_denote_bounds hNonWrap h
  dsimp [NatCutIneq.holds, NatLinExpr.eval]
  rw [hEnv]
  exact hB

/-- Discharges `WrappedInterval.denote M (.iv lo₂ hi₂) (xExpr.eval env)` from
`lo₂ ≤ hi₂ < M` and two `NatCutGoal` certificates deriving `lo₂ ≤ x` and
`x ≤ hi₂`. -/
theorem farkas_discharges_aipcc_interval_refinement
    (hyps : List NatCutIneq) (M lo₂ hi₂ : Nat) (xExpr : NatLinExpr)
    (stepsLo stepsHi : List CutStep)
    (hLoLeHi : Nat.ble lo₂ hi₂ = true)
    (hHiLtM : Nat.blt hi₂ M = true)
    (hChkLo : checkNatCutGoal ⟨hyps, ⟨.cst lo₂, xExpr⟩⟩ stepsLo = true)
    (hChkHi : checkNatCutGoal ⟨hyps, ⟨xExpr, .cst hi₂⟩⟩ stepsHi = true)
    (env : List Nat) :
    HypsImp (NatCutIneq.holds env) hyps
      (WrappedInterval.denote M (.iv lo₂ hi₂) (xExpr.eval env)) :=
  hypsImp_concl_mono (fun hPair => by
    have hLe : lo₂ ≤ hi₂ := Nat.le_of_ble_eq_true hLoLeHi
    have hHiLt : hi₂ < M := lt_of_blt_true hHiLtM
    have hLoLt : lo₂ < M := Nat.lt_of_le_of_lt hLe hHiLt
    exact wrapped_denote_iv_of_le hLoLt hHiLt hLe hPair.1 hPair.2)
    (hypsImp_and
      (checkNatCutGoal_sound ⟨hyps, ⟨.cst lo₂, xExpr⟩⟩ stepsLo hChkLo env)
      (checkNatCutGoal_sound ⟨hyps, ⟨xExpr, .cst hi₂⟩⟩ stepsHi hChkHi env))

/-- Refines the interval component of an initialized `AbsVal` via
`WrappedInterval.meet` and `reduceAbsVal` given a newly proven
`WrappedInterval.denote` bound. -/
theorem absVal_refine_wi_sound {u : UintTy} {a : AbsVal} {wi' : WrappedInterval}
    {x : Nat}
    (ha : AbsVal.denote (uintWidth u) a (some x))
    (hWi : WrappedInterval.denote (modPow2 (uintWidth u)) wi' x) :
    AbsVal.denote (uintWidth u)
      (reduceAbsVal (uintWidth u)
        ⟨.init, a.tnum, WrappedInterval.meet (modPow2 (uintWidth u)) a.wi wi', a.sc⟩)
      (some x) := by
  have hE := absVal_some_elim ha
  apply reduceAbsVal_sound (uintWidth_valid u)
  exact ⟨⟨x, rfl, hE.1⟩, hE.2.1,
         wrappedInterval_meet_sound (modPow2_pos (uintWidth u)) hE.2.2.1 hWi,
         hE.2.2.2⟩

/-- Lifts `farkas_discharges_aipcc_interval_refinement` to a `MirAbsSlot.uint`
slot: proves both the direct `.iv lo₂ hi₂` slot denotation and the
reduced-product `reduceAbsVal` / `WrappedInterval.meet` slot denotation. -/
theorem farkas_refines_mirAbsSlot_uint
    (u : UintTy) (hyps : List NatCutIneq) (lo₂ hi₂ : Nat) (xExpr : NatLinExpr)
    (stepsLo stepsHi : List CutStep)
    (hLoLeHi : Nat.ble lo₂ hi₂ = true)
    (hHiLtM : Nat.blt hi₂ (modPow2 (uintWidth u)) = true)
    (hChkLo : checkNatCutGoal ⟨hyps, ⟨.cst lo₂, xExpr⟩⟩ stepsLo = true)
    (hChkHi : checkNatCutGoal ⟨hyps, ⟨xExpr, .cst hi₂⟩⟩ stepsHi = true)
    (env : List Nat) (ty : Ty) (locals : List LocalSlot) (a : AbsVal)
    (sc : ScalarInt)
    (hSlot : (MirAbsSlot.uint u a).denote ty locals (.init (.scalar sc)))
    (hBits : sc.bits = xExpr.eval env) :
    HypsImp (NatCutIneq.holds env) hyps
      ((MirAbsSlot.uint u ⟨.init, a.tnum, .iv lo₂ hi₂, a.sc⟩).denote ty locals
         (.init (.scalar sc)) ∧
       (MirAbsSlot.uint u
         (reduceAbsVal (uintWidth u)
           ⟨.init, a.tnum,
            WrappedInterval.meet (modPow2 (uintWidth u)) a.wi (.iv lo₂ hi₂),
            a.sc⟩)).denote ty locals (.init (.scalar sc))) :=
  hypsImp_concl_mono (fun hWiEval => by
    have hWi : WrappedInterval.denote (modPow2 (uintWidth u)) (.iv lo₂ hi₂) sc.bits := by
      rw [hBits]
      exact hWiEval
    have hE := absVal_some_elim hSlot.2.2
    have hDirect :
        (MirAbsSlot.uint u ⟨.init, a.tnum, .iv lo₂ hi₂, a.sc⟩).denote ty locals
          (.init (.scalar sc)) :=
      ⟨hSlot.1, hSlot.2.1, ⟨⟨sc.bits, rfl, hE.1⟩, hE.2.1, hWi, hE.2.2.2⟩⟩
    have hReduced :
        (MirAbsSlot.uint u
          (reduceAbsVal (uintWidth u)
            ⟨.init, a.tnum,
             WrappedInterval.meet (modPow2 (uintWidth u)) a.wi (.iv lo₂ hi₂),
             a.sc⟩)).denote ty locals (.init (.scalar sc)) :=
      ⟨hSlot.1, hSlot.2.1, absVal_refine_wi_sound hSlot.2.2 hWi⟩
    exact ⟨hDirect, hReduced⟩)
    (farkas_discharges_aipcc_interval_refinement hyps (modPow2 (uintWidth u))
      lo₂ hi₂ xExpr stepsLo stepsHi hLoLeHi hHiLtM hChkLo hChkHi env)

/-- Lifts `farkas_discharges_aipcc_interval_refinement` to a `MirAbsSlot.uintCopy`
slot while preserving the copy-alias fact `localUintNat? locals src u = some sc.bits`. -/
theorem farkas_refines_mirAbsSlot_uintCopy
    (u : UintTy) (hyps : List NatCutIneq) (lo₂ hi₂ : Nat) (xExpr : NatLinExpr)
    (stepsLo stepsHi : List CutStep)
    (hLoLeHi : Nat.ble lo₂ hi₂ = true)
    (hHiLtM : Nat.blt hi₂ (modPow2 (uintWidth u)) = true)
    (hChkLo : checkNatCutGoal ⟨hyps, ⟨.cst lo₂, xExpr⟩⟩ stepsLo = true)
    (hChkHi : checkNatCutGoal ⟨hyps, ⟨xExpr, .cst hi₂⟩⟩ stepsHi = true)
    (env : List Nat) (ty : Ty) (locals : List LocalSlot) (a : AbsVal)
    (src : Nat) (sc : ScalarInt)
    (hSlot : (MirAbsSlot.uintCopy u a src).denote ty locals (.init (.scalar sc)))
    (hBits : sc.bits = xExpr.eval env) :
    HypsImp (NatCutIneq.holds env) hyps
      ((MirAbsSlot.uintCopy u ⟨.init, a.tnum, .iv lo₂ hi₂, a.sc⟩ src).denote ty locals
         (.init (.scalar sc)) ∧
       (MirAbsSlot.uintCopy u
         (reduceAbsVal (uintWidth u)
           ⟨.init, a.tnum,
            WrappedInterval.meet (modPow2 (uintWidth u)) a.wi (.iv lo₂ hi₂),
            a.sc⟩) src).denote ty locals (.init (.scalar sc))) :=
  hypsImp_concl_mono (fun hWiEval => by
    have hWi : WrappedInterval.denote (modPow2 (uintWidth u)) (.iv lo₂ hi₂) sc.bits := by
      rw [hBits]
      exact hWiEval
    have hE := absVal_some_elim hSlot.2.2.1
    have hDirect :
        (MirAbsSlot.uintCopy u ⟨.init, a.tnum, .iv lo₂ hi₂, a.sc⟩ src).denote ty locals
          (.init (.scalar sc)) :=
      ⟨hSlot.1, hSlot.2.1, ⟨⟨sc.bits, rfl, hE.1⟩, hE.2.1, hWi, hE.2.2.2⟩, hSlot.2.2.2⟩
    have hReduced :
        (MirAbsSlot.uintCopy u
          (reduceAbsVal (uintWidth u)
            ⟨.init, a.tnum,
             WrappedInterval.meet (modPow2 (uintWidth u)) a.wi (.iv lo₂ hi₂),
             a.sc⟩) src).denote ty locals (.init (.scalar sc)) :=
      ⟨hSlot.1, hSlot.2.1, absVal_refine_wi_sound hSlot.2.2.1 hWi, hSlot.2.2.2⟩
    exact ⟨hDirect, hReduced⟩)
    (farkas_discharges_aipcc_interval_refinement hyps (modPow2 (uintWidth u))
      lo₂ hi₂ xExpr stepsLo stepsHi hLoLeHi hHiLtM hChkLo hChkHi env)

/-! ## 5. Reflective Entailment-Graph Specification Adequacy (`arXiv:2611.31571`) -/

/-! ### 5.1 Syntactic Equality Checkers for Path & Graph Chaining -/

def boolBeq : Bool → Bool → Bool
  | false, false => true
  | true, true => true
  | _, _ => false

theorem bool_eq_of_beq {a b : Bool} (h : boolBeq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | nomatch h

def sintBeq (a b : SInt) : Bool :=
  boolBeq a.neg b.neg && Nat.beq a.mag b.mag

theorem sint_eq_of_beq {a b : SInt} (h : sintBeq a b = true) : a = b := by
  cases a with
  | mk na ma =>
    cases b with
    | mk nb mb =>
      dsimp only [sintBeq] at h
      have hN := bool_eq_of_beq (bool_and_left h)
      have hM := Nat.eq_of_beq_eq_true (bool_and_right h)
      rw [hN, hM]

def natLinExprBeq : NatLinExpr → NatLinExpr → Bool
  | .cst n1, .cst n2 => Nat.beq n1 n2
  | .var i1, .var i2 => Nat.beq i1 i2
  | .add a1 b1, .add a2 b2 => natLinExprBeq a1 a2 && natLinExprBeq b1 b2
  | .mulC k1 a1, .mulC k2 a2 => Nat.beq k1 k2 && natLinExprBeq a1 a2
  | _, _ => false

theorem natLinExpr_eq_of_beq :
    ∀ {e1 e2 : NatLinExpr}, natLinExprBeq e1 e2 = true → e1 = e2
  | .cst _, .cst _, h => by rw [Nat.eq_of_beq_eq_true h]
  | .var _, .var _, h => by rw [Nat.eq_of_beq_eq_true h]
  | .add a1 b1, .add a2 b2, h => by
    dsimp only [natLinExprBeq] at h
    rw [natLinExpr_eq_of_beq (e1 := a1) (e2 := a2) (bool_and_left h),
        natLinExpr_eq_of_beq (e1 := b1) (e2 := b2) (bool_and_right h)]
  | .mulC _ a1, .mulC _ a2, h => by
    dsimp only [natLinExprBeq] at h
    rw [Nat.eq_of_beq_eq_true (bool_and_left h),
        natLinExpr_eq_of_beq (e1 := a1) (e2 := a2) (bool_and_right h)]
  | .cst _, .var _, h | .cst _, .add _ _, h | .cst _, .mulC _ _, h
  | .var _, .cst _, h | .var _, .add _ _, h | .var _, .mulC _ _, h
  | .add _ _, .cst _, h | .add _ _, .var _, h | .add _ _, .mulC _ _, h
  | .mulC _ _, .cst _, h | .mulC _ _, .var _, h | .mulC _ _, .add _ _, h =>
    nomatch h

def natCutIneqBeq (a b : NatCutIneq) : Bool :=
  natLinExprBeq a.lhs b.lhs && natLinExprBeq a.rhs b.rhs

theorem natCutIneq_eq_of_beq {a b : NatCutIneq} (h : natCutIneqBeq a b = true) :
    a = b := by
  cases a with
  | mk l1 r1 =>
    cases b with
    | mk l2 r2 =>
      dsimp only [natCutIneqBeq] at h
      rw [natLinExpr_eq_of_beq (bool_and_left h),
          natLinExpr_eq_of_beq (bool_and_right h)]

def natLinSpecBeq : NatLinSpec → NatLinSpec → Bool
  | [], [] => true
  | x :: xs, y :: ys => natCutIneqBeq x y && natLinSpecBeq xs ys
  | _, _ => false

theorem natLinSpec_eq_of_beq :
    ∀ {s1 s2 : NatLinSpec}, natLinSpecBeq s1 s2 = true → s1 = s2
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    dsimp only [natLinSpecBeq] at h
    rw [natCutIneq_eq_of_beq (a := x) (b := y) (bool_and_left h),
        natLinSpec_eq_of_beq (s1 := xs) (s2 := ys) (bool_and_right h)]
  | [], _ :: _, h | _ :: _, [], h => nomatch h

def intLinExprBeq : IntLinExpr → IntLinExpr → Bool
  | .cst c1, .cst c2 => sintBeq c1 c2
  | .var i1, .var i2 => Nat.beq i1 i2
  | .add a1 b1, .add a2 b2 => intLinExprBeq a1 a2 && intLinExprBeq b1 b2
  | .sub a1 b1, .sub a2 b2 => intLinExprBeq a1 a2 && intLinExprBeq b1 b2
  | .neg a1, .neg a2 => intLinExprBeq a1 a2
  | .mulC k1 a1, .mulC k2 a2 => sintBeq k1 k2 && intLinExprBeq a1 a2
  | _, _ => false

theorem intLinExpr_eq_of_beq :
    ∀ {e1 e2 : IntLinExpr}, intLinExprBeq e1 e2 = true → e1 = e2
  | .cst _, .cst _, h => by rw [sint_eq_of_beq h]
  | .var _, .var _, h => by rw [Nat.eq_of_beq_eq_true h]
  | .add a1 b1, .add a2 b2, h => by
    dsimp only [intLinExprBeq] at h
    rw [intLinExpr_eq_of_beq (e1 := a1) (e2 := a2) (bool_and_left h),
        intLinExpr_eq_of_beq (e1 := b1) (e2 := b2) (bool_and_right h)]
  | .sub a1 b1, .sub a2 b2, h => by
    dsimp only [intLinExprBeq] at h
    rw [intLinExpr_eq_of_beq (e1 := a1) (e2 := a2) (bool_and_left h),
        intLinExpr_eq_of_beq (e1 := b1) (e2 := b2) (bool_and_right h)]
  | .neg a1, .neg a2, h => by
    rw [intLinExpr_eq_of_beq (e1 := a1) (e2 := a2) h]
  | .mulC _ a1, .mulC _ a2, h => by
    dsimp only [intLinExprBeq] at h
    rw [sint_eq_of_beq (bool_and_left h),
        intLinExpr_eq_of_beq (e1 := a1) (e2 := a2) (bool_and_right h)]
  | .cst _, .var _, h | .cst _, .add _ _, h | .cst _, .sub _ _, h
  | .cst _, .neg _, h | .cst _, .mulC _ _, h
  | .var _, .cst _, h | .var _, .add _ _, h | .var _, .sub _ _, h
  | .var _, .neg _, h | .var _, .mulC _ _, h
  | .add _ _, .cst _, h | .add _ _, .var _, h | .add _ _, .sub _ _, h
  | .add _ _, .neg _, h | .add _ _, .mulC _ _, h
  | .sub _ _, .cst _, h | .sub _ _, .var _, h | .sub _ _, .add _ _, h
  | .sub _ _, .neg _, h | .sub _ _, .mulC _ _, h
  | .neg _, .cst _, h | .neg _, .var _, h | .neg _, .add _ _, h
  | .neg _, .sub _ _, h | .neg _, .mulC _ _, h
  | .mulC _ _, .cst _, h | .mulC _ _, .var _, h | .mulC _ _, .add _ _, h
  | .mulC _ _, .sub _ _, h | .mulC _ _, .neg _, h =>
    nomatch h

def intCutIneqBeq (a b : IntCutIneq) : Bool :=
  intLinExprBeq a.lhs b.lhs && intLinExprBeq a.rhs b.rhs

theorem intCutIneq_eq_of_beq {a b : IntCutIneq} (h : intCutIneqBeq a b = true) :
    a = b := by
  cases a with
  | mk l1 r1 =>
    cases b with
    | mk l2 r2 =>
      dsimp only [intCutIneqBeq] at h
      rw [intLinExpr_eq_of_beq (bool_and_left h),
          intLinExpr_eq_of_beq (bool_and_right h)]

def intLinSpecBeq : IntLinSpec → IntLinSpec → Bool
  | [], [] => true
  | x :: xs, y :: ys => intCutIneqBeq x y && intLinSpecBeq xs ys
  | _, _ => false

theorem intLinSpec_eq_of_beq :
    ∀ {s1 s2 : IntLinSpec}, intLinSpecBeq s1 s2 = true → s1 = s2
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    dsimp only [intLinSpecBeq] at h
    rw [intCutIneq_eq_of_beq (a := x) (b := y) (bool_and_left h),
        intLinSpec_eq_of_beq (s1 := xs) (s2 := ys) (bool_and_right h)]
  | [], _ :: _, h | _ :: _, [], h => nomatch h

/-! ### 5.2 Reflective Entailment Edge, Graph, & Path Checkers -/

/-- Directed certified entailment edge `src ⟹ dst` in an Entailment Graph. -/
structure EntailmentEdge (Spec : Type) where
  src   : Spec
  dst   : Spec
  certs : List (List CutStep)

/-- Indexed Entailment Graph over specification nodes and certified edges. -/
structure EntailmentGraph (Spec : Type) where
  nodes : List Spec
  edges : List (Nat × Nat × List (List CutStep))

abbrev NatEntailmentEdge := EntailmentEdge NatLinSpec
abbrev IntEntailmentEdge := EntailmentEdge IntLinSpec
abbrev NatEntailmentGraph := EntailmentGraph NatLinSpec
abbrev IntEntailmentGraph := EntailmentGraph IntLinSpec

/-- Polymorphic transitivity of semantic entailment. -/
theorem entailment_trans {Env Spec : Type} {holds : Env → Spec → Prop}
    {a b c : Spec}
    (hab : ∀ env, holds env a → holds env b)
    (hbc : ∀ env, holds env b → holds env c) :
    ∀ env, holds env a → holds env c :=
  fun env ha => hbc env (hab env ha)

/-- Fail-closed reflective checker for `src ⟹ dst` over `NatLinSpec`: checks
every inequality in `dst` against its corresponding certificate in `certs` and
rejects any length mismatch (`certs.length ≠ dst.length`). -/
noncomputable def checkNatEntailmentEdge (src : NatLinSpec) :
    NatLinSpec → List (List CutStep) → Bool
  | [], [] => true
  | iq :: rest, c :: crest =>
    checkNatCutGoal ⟨src, iq⟩ c && checkNatEntailmentEdge src rest crest
  | _, _ => false

/-- Soundness of `checkNatEntailmentEdge`: `src ⟹ dst` holds universally. -/
theorem checkNatEntailmentEdge_sound {src : NatLinSpec} :
    ∀ {dst : NatLinSpec} {certs : List (List CutStep)},
      checkNatEntailmentEdge src dst certs = true →
      ∀ env : List Nat, src.holds env → dst.holds env
  | [], [], _, env, _ => natLinSpec_holds_nil env
  | iq :: rest, c :: crest, hChk, env, hSrc => by
    dsimp only [checkNatEntailmentEdge] at hChk
    have hHead : iq.holds env :=
      hypsImp_apply_all src
        (checkNatCutGoal_sound ⟨src, iq⟩ c (bool_and_left hChk) env) hSrc
    have hTail : NatLinSpec.holds env rest :=
      checkNatEntailmentEdge_sound (bool_and_right hChk) env hSrc
    exact natLinSpec_holds_cons hHead hTail
  | [], _ :: _, hChk, _, _ => nomatch hChk
  | _ :: _, [], hChk, _, _ => nomatch hChk

/-- Fail-closed reflective checker for `src ⟹ dst` over `IntLinSpec`. -/
noncomputable def checkIntEntailmentEdge (src : IntLinSpec) :
    IntLinSpec → List (List CutStep) → Bool
  | [], [] => true
  | iq :: rest, c :: crest =>
    checkIntCutGoal ⟨src, iq⟩ c && checkIntEntailmentEdge src rest crest
  | _, _ => false

/-- Soundness of `checkIntEntailmentEdge`: `src ⟹ dst` holds universally. -/
theorem checkIntEntailmentEdge_sound {src : IntLinSpec} :
    ∀ {dst : IntLinSpec} {certs : List (List CutStep)},
      checkIntEntailmentEdge src dst certs = true →
      ∀ env : List Int, src.holds env → dst.holds env
  | [], [], _, env, _ => intLinSpec_holds_nil env
  | iq :: rest, c :: crest, hChk, env, hSrc => by
    dsimp only [checkIntEntailmentEdge] at hChk
    have hHead : iq.holds env :=
      hypsImp_apply_all src
        (checkIntCutGoal_sound ⟨src, iq⟩ c (bool_and_left hChk) env) hSrc
    have hTail : IntLinSpec.holds env rest :=
      checkIntEntailmentEdge_sound (bool_and_right hChk) env hSrc
    exact intLinSpec_holds_cons hHead hTail
  | [], _ :: _, hChk, _, _ => nomatch hChk
  | _ :: _, [], hChk, _, _ => nomatch hChk

/-- Reflective multi-edge path checker for `NatLinSpec` entailment chains. -/
noncomputable def checkNatEntailmentPath (cur goal : NatLinSpec) :
    List NatEntailmentEdge → Bool
  | [] => natLinSpecBeq cur goal
  | e :: rest =>
    natLinSpecBeq cur e.src &&
    checkNatEntailmentEdge e.src e.dst e.certs &&
    checkNatEntailmentPath e.dst goal rest

/-- Soundness of `checkNatEntailmentPath` via `entailment_trans`. -/
theorem checkNatEntailmentPath_sound :
    ∀ (path : List NatEntailmentEdge) (start goal : NatLinSpec),
      checkNatEntailmentPath start goal path = true →
      ∀ env : List Nat, start.holds env → goal.holds env
  | [], start, goal, hChk => by
    have hEq := natLinSpec_eq_of_beq hChk
    rw [hEq]
    exact fun _ h => h
  | e :: rest, start, goal, hChk => by
    dsimp only [checkNatEntailmentPath] at hChk
    have hLeft := bool_and_left hChk
    have hSrcEq := natLinSpec_eq_of_beq (bool_and_left hLeft)
    have hEdge := checkNatEntailmentEdge_sound (bool_and_right hLeft)
    have hRest := checkNatEntailmentPath_sound rest e.dst goal (bool_and_right hChk)
    rw [hSrcEq]
    exact entailment_trans hEdge hRest

/-- Reflective multi-edge path checker for `IntLinSpec` entailment chains. -/
noncomputable def checkIntEntailmentPath (cur goal : IntLinSpec) :
    List IntEntailmentEdge → Bool
  | [] => intLinSpecBeq cur goal
  | e :: rest =>
    intLinSpecBeq cur e.src &&
    checkIntEntailmentEdge e.src e.dst e.certs &&
    checkIntEntailmentPath e.dst goal rest

/-- Soundness of `checkIntEntailmentPath` via `entailment_trans`. -/
theorem checkIntEntailmentPath_sound :
    ∀ (path : List IntEntailmentEdge) (start goal : IntLinSpec),
      checkIntEntailmentPath start goal path = true →
      ∀ env : List Int, start.holds env → goal.holds env
  | [], start, goal, hChk => by
    have hEq := intLinSpec_eq_of_beq hChk
    rw [hEq]
    exact fun _ h => h
  | e :: rest, start, goal, hChk => by
    dsimp only [checkIntEntailmentPath] at hChk
    have hLeft := bool_and_left hChk
    have hSrcEq := intLinSpec_eq_of_beq (bool_and_left hLeft)
    have hEdge := checkIntEntailmentEdge_sound (bool_and_right hLeft)
    have hRest := checkIntEntailmentPath_sound rest e.dst goal (bool_and_right hChk)
    rw [hSrcEq]
    exact entailment_trans hEdge hRest

/-- Computable total list lookup helper. -/
def listLookup? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, i + 1 => listLookup? xs i

private theorem listLookup?_eq_listGet? {α : Type} :
    ∀ (xs : List α) (i : Nat), listLookup? xs i = listGet? xs i
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => listLookup?_eq_listGet? xs i

/-- Checks every edge `(u, v, certs)` in `g : NatEntailmentGraph`. -/
noncomputable def checkNatEntailmentGraphEdges (nodes : List NatLinSpec) :
    List (Nat × Nat × List (List CutStep)) → Bool
  | [] => true
  | (u, v, certs) :: rest =>
    match listLookup? nodes u, listLookup? nodes v with
    | some src, some dst =>
      checkNatEntailmentEdge src dst certs && checkNatEntailmentGraphEdges nodes rest
    | _, _ => false

/-- Whole-graph reflective checker for `NatEntailmentGraph`. -/
noncomputable def checkNatEntailmentGraph (g : NatEntailmentGraph) : Bool :=
  checkNatEntailmentGraphEdges g.nodes g.edges

/-- Soundness of `checkNatEntailmentGraph`: every edge `(u, v, _)` in `g.edges`
resolves to valid nodes `src`, `dst` satisfying `src ⟹ dst`. -/
theorem checkNatEntailmentGraph_sound {g : NatEntailmentGraph}
    (hChk : checkNatEntailmentGraph g = true) :
    ∀ u v certs, (u, v, certs) ∈ g.edges →
      ∃ src dst,
        listLookup? g.nodes u = some src ∧
        listLookup? g.nodes v = some dst ∧
        (∀ env : List Nat, src.holds env → dst.holds env) := by
  have hAux :
      ∀ (edges : List (Nat × Nat × List (List CutStep))),
        checkNatEntailmentGraphEdges g.nodes edges = true →
        ∀ u v certs, (u, v, certs) ∈ edges →
          ∃ src dst,
            listLookup? g.nodes u = some src ∧
            listLookup? g.nodes v = some dst ∧
            (∀ env : List Nat, src.holds env → dst.holds env) := by
    intro edges
    induction edges with
    | nil => intro _ _ _ _ hm; nomatch hm
    | cons hd rest ih =>
      intro hE u v certs hm
      cases hd with
      | mk hu hvr =>
        cases hvr with
        | mk hv hcerts =>
          dsimp only [checkNatEntailmentGraphEdges] at hE
          cases hLu : listLookup? g.nodes hu with
          | none => rw [hLu] at hE; nomatch hE
          | some src =>
            cases hLv : listLookup? g.nodes hv with
            | none => rw [hLu, hLv] at hE; nomatch hE
            | some dst =>
              rw [hLu, hLv] at hE
              cases hm with
              | head _ =>
                exact ⟨src, dst, hLu, hLv,
                  checkNatEntailmentEdge_sound (bool_and_left hE)⟩
              | tail _ hT =>
                exact ih (bool_and_right hE) u v certs hT
  exact hAux g.edges hChk

/-- Checks every edge `(u, v, certs)` in `g : IntEntailmentGraph`. -/
noncomputable def checkIntEntailmentGraphEdges (nodes : List IntLinSpec) :
    List (Nat × Nat × List (List CutStep)) → Bool
  | [] => true
  | (u, v, certs) :: rest =>
    match listLookup? nodes u, listLookup? nodes v with
    | some src, some dst =>
      checkIntEntailmentEdge src dst certs && checkIntEntailmentGraphEdges nodes rest
    | _, _ => false

/-- Whole-graph reflective checker for `IntEntailmentGraph`. -/
noncomputable def checkIntEntailmentGraph (g : IntEntailmentGraph) : Bool :=
  checkIntEntailmentGraphEdges g.nodes g.edges

/-- Soundness of `checkIntEntailmentGraph`. -/
theorem checkIntEntailmentGraph_sound {g : IntEntailmentGraph}
    (hChk : checkIntEntailmentGraph g = true) :
    ∀ u v certs, (u, v, certs) ∈ g.edges →
      ∃ src dst,
        listLookup? g.nodes u = some src ∧
        listLookup? g.nodes v = some dst ∧
        (∀ env : List Int, src.holds env → dst.holds env) := by
  have hAux :
      ∀ (edges : List (Nat × Nat × List (List CutStep))),
        checkIntEntailmentGraphEdges g.nodes edges = true →
        ∀ u v certs, (u, v, certs) ∈ edges →
          ∃ src dst,
            listLookup? g.nodes u = some src ∧
            listLookup? g.nodes v = some dst ∧
            (∀ env : List Int, src.holds env → dst.holds env) := by
    intro edges
    induction edges with
    | nil => intro _ _ _ _ hm; nomatch hm
    | cons hd rest ih =>
      intro hE u v certs hm
      cases hd with
      | mk hu hvr =>
        cases hvr with
        | mk hv hcerts =>
          dsimp only [checkIntEntailmentGraphEdges] at hE
          cases hLu : listLookup? g.nodes hu with
          | none => rw [hLu] at hE; nomatch hE
          | some src =>
            cases hLv : listLookup? g.nodes hv with
            | none => rw [hLu, hLv] at hE; nomatch hE
            | some dst =>
              rw [hLu, hLv] at hE
              cases hm with
              | head _ =>
                exact ⟨src, dst, hLu, hLv,
                  checkIntEntailmentEdge_sound (bool_and_left hE)⟩
              | tail _ hT =>
                exact ih (bool_and_right hE) u v certs hT
  exact hAux g.edges hChk

/-- Checks whether directed edge `(u, v)` appears in `edges`. -/
def hasEdgeInList (u v : Nat) : List (Nat × Nat × List (List CutStep)) → Bool
  | [] => false
  | (a, b, _) :: rest => (Nat.beq a u && Nat.beq b v) || hasEdgeInList u v rest

theorem hasEdgeInList_sound {u v : Nat} :
    ∀ {edges : List (Nat × Nat × List (List CutStep))},
      hasEdgeInList u v edges = true → ∃ certs, (u, v, certs) ∈ edges
  | [], h => nomatch h
  | (a, b, cs) :: rest, h => by
    dsimp only [hasEdgeInList] at h
    cases hHead : (Nat.beq a u && Nat.beq b v) with
    | true =>
      have ha := Nat.eq_of_beq_eq_true (bool_and_left hHead)
      have hb := Nat.eq_of_beq_eq_true (bool_and_right hHead)
      rw [ha, hb]
      exact ⟨cs, List.Mem.head rest⟩
    | false =>
      rw [hHead] at h
      dsimp only [Bool.or] at h
      cases hasEdgeInList_sound h with
      | intro certs hMem => exact ⟨certs, List.Mem.tail _ hMem⟩

/-- Checks a multi-hop node-index path `cur → hops → goal` inside an
`EntailmentGraph` (reusing already-checked graph edges via transitivity). -/
def checkGraphIndexPath {Spec : Type} (g : EntailmentGraph Spec)
    (cur goal : Nat) : List Nat → Bool
  | [] =>
    match listLookup? g.nodes cur with
    | some _ => Nat.beq cur goal
    | none => false
  | nxt :: rest =>
    hasEdgeInList cur nxt g.edges && checkGraphIndexPath g nxt goal rest

/-- Multi-hop reachability soundness over a verified `NatEntailmentGraph`:
derives `nodes[start] ⟹ nodes[goal]` via `entailment_trans` without
re-verifying `CutStep` certificates. -/
theorem checkNatGraphIndexPath_sound {g : NatEntailmentGraph}
    (hGraph : checkNatEntailmentGraph g = true) :
    ∀ (hops : List Nat) (start goal : Nat),
      checkGraphIndexPath g start goal hops = true →
      ∃ src dst,
        listLookup? g.nodes start = some src ∧
        listLookup? g.nodes goal = some dst ∧
        (∀ env : List Nat, src.holds env → dst.holds env)
  | [], start, goal, hPath => by
    dsimp only [checkGraphIndexPath] at hPath
    cases hLu : listLookup? g.nodes start with
    | none => rw [hLu] at hPath; nomatch hPath
    | some src =>
      rw [hLu] at hPath
      have hEq := Nat.eq_of_beq_eq_true hPath
      rw [← hEq]
      exact ⟨src, src, rfl, hLu, fun _ h => h⟩
  | nxt :: rest, start, goal, hPath => by
    dsimp only [checkGraphIndexPath] at hPath
    cases hasEdgeInList_sound (bool_and_left hPath) with
    | intro certs hEdgeMem =>
      cases checkNatEntailmentGraph_sound hGraph start nxt certs hEdgeMem with
      | intro src h1 =>
        cases h1 with
        | intro mid h2 =>
          cases checkNatGraphIndexPath_sound hGraph rest nxt goal (bool_and_right hPath) with
          | intro mid2 h3 =>
            cases h3 with
            | intro dst h4 =>
              have hMidEq : mid = mid2 := by
                rw [h2.2.1] at h4
                injection h4.1 with heq
              rw [← hMidEq] at h4
              exact ⟨src, dst, h2.1, h4.2.1, entailment_trans h2.2.2 h4.2.2⟩

/-- Multi-hop reachability soundness over a verified `IntEntailmentGraph`. -/
theorem checkIntGraphIndexPath_sound {g : IntEntailmentGraph}
    (hGraph : checkIntEntailmentGraph g = true) :
    ∀ (hops : List Nat) (start goal : Nat),
      checkGraphIndexPath g start goal hops = true →
      ∃ src dst,
        listLookup? g.nodes start = some src ∧
        listLookup? g.nodes goal = some dst ∧
        (∀ env : List Int, src.holds env → dst.holds env)
  | [], start, goal, hPath => by
    dsimp only [checkGraphIndexPath] at hPath
    cases hLu : listLookup? g.nodes start with
    | none => rw [hLu] at hPath; nomatch hPath
    | some src =>
      rw [hLu] at hPath
      have hEq := Nat.eq_of_beq_eq_true hPath
      rw [← hEq]
      exact ⟨src, src, rfl, hLu, fun _ h => h⟩
  | nxt :: rest, start, goal, hPath => by
    dsimp only [checkGraphIndexPath] at hPath
    cases hasEdgeInList_sound (bool_and_left hPath) with
    | intro certs hEdgeMem =>
      cases checkIntEntailmentGraph_sound hGraph start nxt certs hEdgeMem with
      | intro src h1 =>
        cases h1 with
        | intro mid h2 =>
          cases checkIntGraphIndexPath_sound hGraph rest nxt goal (bool_and_right hPath) with
          | intro mid2 h3 =>
            cases h3 with
            | intro dst h4 =>
              have hMidEq : mid = mid2 := by
                rw [h2.2.1] at h4
                injection h4.1 with heq
              rw [← hMidEq] at h4
              exact ⟨src, dst, h2.1, h4.2.1, entailment_trans h2.2.2 h4.2.2⟩

/-! ### 5.3 Reflective Concrete Witness Evaluators & Refuters (`Nat` and `Int`) -/

/-- Computable environment lookup on `List Nat` matching `envLookupNat`. -/
def natEnvGet (env : List Nat) (idx : Nat) : Nat :=
  match listLookup? env idx with
  | some v => v
  | none => 0

theorem natEnvGet_eq_envLookupNat (env : List Nat) (idx : Nat) :
    natEnvGet env idx = envLookupNat env idx := by
  dsimp only [natEnvGet, envLookupNat]
  rw [listLookup?_eq_listGet?]
  rfl

/-- Computable concrete evaluator for `NatLinExpr`. -/
def evalNatLinExpr (env : List Nat) : NatLinExpr → Nat
  | .cst n => n
  | .var idx => natEnvGet env idx
  | .add a b => evalNatLinExpr env a + evalNatLinExpr env b
  | .mulC k a => k * evalNatLinExpr env a

theorem evalNatLinExpr_eq (env : List Nat) :
    ∀ e : NatLinExpr, evalNatLinExpr env e = e.eval env
  | .cst _ => rfl
  | .var idx => natEnvGet_eq_envLookupNat env idx
  | .add a b => by
    dsimp only [evalNatLinExpr, NatLinExpr.eval]
    rw [evalNatLinExpr_eq env a, evalNatLinExpr_eq env b]
  | .mulC _ a => by
    dsimp only [evalNatLinExpr, NatLinExpr.eval]
    rw [evalNatLinExpr_eq env a]

/-- Reflective concrete checker for one `NatCutIneq` under `env`. -/
def checkNatIneqWitness (env : List Nat) (iq : NatCutIneq) : Bool :=
  Nat.ble (evalNatLinExpr env iq.lhs) (evalNatLinExpr env iq.rhs)

theorem checkNatIneqWitness_sound {env : List Nat} {iq : NatCutIneq}
    (h : checkNatIneqWitness env iq = true) : iq.holds env := by
  dsimp only [NatCutIneq.holds]
  rw [← evalNatLinExpr_eq env iq.lhs, ← evalNatLinExpr_eq env iq.rhs]
  exact Nat.le_of_ble_eq_true h

theorem checkNatIneqWitness_false_sound {env : List Nat} {iq : NatCutIneq}
    (h : checkNatIneqWitness env iq = false) : ¬ iq.holds env := by
  intro hHolds
  dsimp only [NatCutIneq.holds] at hHolds
  rw [← evalNatLinExpr_eq env iq.lhs, ← evalNatLinExpr_eq env iq.rhs] at hHolds
  exact nat_not_le_of_ble_false h hHolds

/-- Reflective concrete satisfiability checker for `NatLinSpec`. -/
def checkNatSpecWitness (env : List Nat) : NatLinSpec → Bool
  | [] => true
  | iq :: rest => checkNatIneqWitness env iq && checkNatSpecWitness env rest

/-- Soundness of `checkNatSpecWitness`: `= true` proves `spec.holds env`. -/
theorem checkNatSpecWitness_sound (env : List Nat) :
    ∀ {spec : NatLinSpec},
      checkNatSpecWitness env spec = true → spec.holds env
  | [], _ => natLinSpec_holds_nil env
  | iq :: rest, hChk => by
    dsimp only [checkNatSpecWitness] at hChk
    exact natLinSpec_holds_cons
      (checkNatIneqWitness_sound (bool_and_left hChk))
      (checkNatSpecWitness_sound env (bool_and_right hChk))

/-- Reflective concrete refutation checker for `NatLinSpec`: returns `true` iff
at least one inequality in `spec` is strictly violated by `env`. -/
def checkNatSpecFalsifies (env : List Nat) : NatLinSpec → Bool
  | [] => false
  | iq :: rest => !(checkNatIneqWitness env iq) || checkNatSpecFalsifies env rest

/-- Soundness of `checkNatSpecFalsifies`: `= true` proves `¬ spec.holds env`. -/
theorem checkNatSpecFalsifies_sound (env : List Nat) :
    ∀ {spec : NatLinSpec},
      checkNatSpecFalsifies env spec = true → ¬ spec.holds env
  | [], hChk => nomatch hChk
  | iq :: rest, hChk => by
    dsimp only [checkNatSpecFalsifies] at hChk
    cases hHead : checkNatIneqWitness env iq with
    | false =>
      intro hHolds
      exact checkNatIneqWitness_false_sound hHead (hHolds iq (List.Mem.head rest))
    | true =>
      rw [hHead] at hChk
      dsimp only [Bool.not, Bool.or] at hChk
      intro hHolds
      exact checkNatSpecFalsifies_sound env hChk
        (fun q hq => hHolds q (List.Mem.tail iq hq))

/-- Computable environment lookup on `List Int` matching `envLookupInt`. -/
def intEnvGet (env : List Int) (idx : Nat) : Int :=
  match listLookup? env idx with
  | some v => v
  | none => 0

theorem intEnvGet_eq_envLookupInt (env : List Int) (idx : Nat) :
    intEnvGet env idx = envLookupInt env idx := by
  dsimp only [intEnvGet, envLookupInt]
  rw [listLookup?_eq_listGet?]
  rfl

/-- Converts a concrete `Int` to sign-magnitude `SInt`. -/
def intToSInt : Int → SInt
  | .ofNat n => ⟨false, n⟩
  | .negSucc m => ⟨true, m + 1⟩

theorem intToSInt_toInt : ∀ x : Int, (intToSInt x).toInt = x
  | .ofNat _ => rfl
  | .negSucc _ => rfl

private theorem sint_negate_toInt (s : SInt) :
    (SInt.negate s).toInt = Int.neg s.toInt :=
  intBalance_eq_of_eq (sint_negate_balance s) (intBalance_neg (sint_intBalance s))

/-- Computable sign-magnitude `≤` comparison on `SInt` using only `Nat.ble`. -/
def sintLe (a b : SInt) : Bool :=
  Nat.ble (a.posPart + b.negPart) (b.posPart + a.negPart)

theorem sintLe_sound {a b : SInt} (h : sintLe a b = true) :
    a.toInt ≤ b.toInt :=
  (intBalance_le (sint_intBalance a) (sint_intBalance b)).2
    (Nat.le_of_ble_eq_true h)

theorem sintLe_false_sound {a b : SInt} (h : sintLe a b = false) :
    ¬ (a.toInt ≤ b.toInt) := by
  intro hLe
  have hNat := (intBalance_le (sint_intBalance a) (sint_intBalance b)).1 hLe
  exact nat_not_le_of_ble_false h hNat

/-- Computable concrete `SInt` evaluator for `IntLinExpr`. -/
def evalIntLinExprSInt (env : List Int) : IntLinExpr → SInt
  | .cst c => c
  | .var idx => intToSInt (intEnvGet env idx)
  | .add a b => SInt.add (evalIntLinExprSInt env a) (evalIntLinExprSInt env b)
  | .sub a b => SInt.sub (evalIntLinExprSInt env a) (evalIntLinExprSInt env b)
  | .neg a => SInt.negate (evalIntLinExprSInt env a)
  | .mulC k a => SInt.mul k (evalIntLinExprSInt env a)

theorem evalIntLinExprSInt_toInt (env : List Int) :
    ∀ e : IntLinExpr, (evalIntLinExprSInt env e).toInt = e.eval env
  | .cst _ => rfl
  | .var idx => by
    dsimp only [evalIntLinExprSInt, IntLinExpr.eval]
    rw [intToSInt_toInt, intEnvGet_eq_envLookupInt]
  | .add a b => by
    dsimp only [evalIntLinExprSInt, IntLinExpr.eval]
    rw [sint_add_toInt, evalIntLinExprSInt_toInt env a, evalIntLinExprSInt_toInt env b]
  | .sub a b => by
    dsimp only [evalIntLinExprSInt, IntLinExpr.eval, SInt.sub]
    rw [sint_add_toInt, sint_negate_toInt,
        evalIntLinExprSInt_toInt env a, evalIntLinExprSInt_toInt env b]
    rfl
  | .neg a => by
    dsimp only [evalIntLinExprSInt, IntLinExpr.eval]
    rw [sint_negate_toInt, evalIntLinExprSInt_toInt env a]
  | .mulC _ a => by
    dsimp only [evalIntLinExprSInt, IntLinExpr.eval]
    rw [sint_mul_toInt, evalIntLinExprSInt_toInt env a]

/-- Computable `Int` evaluator for `IntLinExpr` (via `SInt`). -/
def evalIntLinExpr (env : List Int) (e : IntLinExpr) : Int :=
  (evalIntLinExprSInt env e).toInt

theorem evalIntLinExpr_eq (env : List Int) (e : IntLinExpr) :
    evalIntLinExpr env e = e.eval env :=
  evalIntLinExprSInt_toInt env e

/-- Reflective concrete checker for one `IntCutIneq` under `env`. -/
def checkIntIneqWitness (env : List Int) (iq : IntCutIneq) : Bool :=
  sintLe (evalIntLinExprSInt env iq.lhs) (evalIntLinExprSInt env iq.rhs)

theorem checkIntIneqWitness_sound {env : List Int} {iq : IntCutIneq}
    (h : checkIntIneqWitness env iq = true) : iq.holds env := by
  dsimp only [IntCutIneq.holds]
  rw [← evalIntLinExprSInt_toInt env iq.lhs, ← evalIntLinExprSInt_toInt env iq.rhs]
  exact sintLe_sound h

theorem checkIntIneqWitness_false_sound {env : List Int} {iq : IntCutIneq}
    (h : checkIntIneqWitness env iq = false) : ¬ iq.holds env := by
  intro hHolds
  dsimp only [IntCutIneq.holds] at hHolds
  rw [← evalIntLinExprSInt_toInt env iq.lhs, ← evalIntLinExprSInt_toInt env iq.rhs] at hHolds
  exact sintLe_false_sound h hHolds

/-- Reflective concrete satisfiability checker for `IntLinSpec`. -/
def checkIntSpecWitness (env : List Int) : IntLinSpec → Bool
  | [] => true
  | iq :: rest => checkIntIneqWitness env iq && checkIntSpecWitness env rest

/-- Soundness of `checkIntSpecWitness`: `= true` proves `spec.holds env`. -/
theorem checkIntSpecWitness_sound (env : List Int) :
    ∀ {spec : IntLinSpec},
      checkIntSpecWitness env spec = true → spec.holds env
  | [], _ => intLinSpec_holds_nil env
  | iq :: rest, hChk => by
    dsimp only [checkIntSpecWitness] at hChk
    exact intLinSpec_holds_cons
      (checkIntIneqWitness_sound (bool_and_left hChk))
      (checkIntSpecWitness_sound env (bool_and_right hChk))

/-- Reflective concrete refutation checker for `IntLinSpec`. -/
def checkIntSpecFalsifies (env : List Int) : IntLinSpec → Bool
  | [] => false
  | iq :: rest => !(checkIntIneqWitness env iq) || checkIntSpecFalsifies env rest

/-- Soundness of `checkIntSpecFalsifies`: `= true` proves `¬ spec.holds env`. -/
theorem checkIntSpecFalsifies_sound (env : List Int) :
    ∀ {spec : IntLinSpec},
      checkIntSpecFalsifies env spec = true → ¬ spec.holds env
  | [], hChk => nomatch hChk
  | iq :: rest, hChk => by
    dsimp only [checkIntSpecFalsifies] at hChk
    cases hHead : checkIntIneqWitness env iq with
    | false =>
      intro hHolds
      exact checkIntIneqWitness_false_sound hHead (hHolds iq (List.Mem.head rest))
    | true =>
      rw [hHead] at hChk
      dsimp only [Bool.not, Bool.or] at hChk
      intro hHolds
      exact checkIntSpecFalsifies_sound env hChk
        (fun q hq => hHolds q (List.Mem.tail iq hq))

/-! ### 5.4 Reflective Entailment Adequacy Certificates (`farkas_entailment_adequacy_cert`) -/

/-- Adequacy refinement mode for `NatLinSpec` entailment checks. -/
inductive NatAdequacyMode where
  /-- Certify sufficiency (`pre ⟹ obligation`) and non-vacuity (`∃ env, pre.holds env`) only. -/
  | sufficientOnly
  /-- Additionally certify strict strengthening via a concrete witness
  satisfying `obligation` and falsifying `pre`. -/
  | strict (strictWitness : List Nat)
  /-- Additionally certify bidirectional equivalence (`obligation ⟹ pre`) via
  reverse `CutStep` certificates. -/
  | equiv (revCerts : List (List CutStep))

/-- Mode-specific semantic obligation for `NatAdequacyMode`. -/
def NatAdequacyMode.denote (pre obligation : NatLinSpec) : NatAdequacyMode → Prop
  | .sufficientOnly => True
  | .strict _ =>
    (∃ env : List Nat, obligation.holds env ∧ ¬ pre.holds env) ∧
    ¬ (∀ env : List Nat, obligation.holds env → pre.holds env)
  | .equiv _ =>
    ∀ env : List Nat, pre.holds env ↔ obligation.holds env

/-- Full semantic specification adequacy proposition for `NatLinSpec`:
1. Sufficiency (`∀ env, pre.holds env → obligation.holds env`),
2. Non-vacuity (`∃ env, pre.holds env`), and
3. Mode-specific strictness or bidirectional equivalence. -/
def NatEntailmentAdequacyProp (pre obligation : NatLinSpec)
    (mode : NatAdequacyMode) : Prop :=
  (∀ env : List Nat, pre.holds env → obligation.holds env) ∧
  (∃ env : List Nat, pre.holds env) ∧
  mode.denote pre obligation

/-- Single-`rfl` reflective adequacy checker for `NatLinSpec`. -/
noncomputable def checkNatEntailmentAdequacy
    (pre obligation : NatLinSpec)
    (fwdCerts : List (List CutStep))
    (satWitness : List Nat)
    (mode : NatAdequacyMode) : Bool :=
  checkNatEntailmentEdge pre obligation fwdCerts &&
  checkNatSpecWitness satWitness pre &&
  match mode with
  | .sufficientOnly => true
  | .strict strictWitness =>
    checkNatSpecWitness strictWitness obligation &&
    checkNatSpecFalsifies strictWitness pre
  | .equiv revCerts =>
    checkNatEntailmentEdge obligation pre revCerts

/-- Master reflective Entailment-Graph adequacy theorem for `NatLinSpec`:
a single `rfl` certifies sufficiency, non-vacuity, and (when requested) strict
strengthening or bidirectional equivalence. -/
theorem farkas_entailment_adequacy_cert
    (pre obligation : NatLinSpec)
    (fwdCerts : List (List CutStep))
    (satWitness : List Nat)
    (mode : NatAdequacyMode)
    (hChk : checkNatEntailmentAdequacy pre obligation fwdCerts satWitness mode = true) :
    NatEntailmentAdequacyProp pre obligation mode := by
  dsimp only [checkNatEntailmentAdequacy] at hChk
  have hLeft := bool_and_left hChk
  have hFwd := checkNatEntailmentEdge_sound (bool_and_left hLeft)
  have hSat := checkNatSpecWitness_sound satWitness (bool_and_right hLeft)
  have hModeChk := bool_and_right hChk
  refine ⟨hFwd, ⟨satWitness, hSat⟩, ?_⟩
  cases mode with
  | sufficientOnly => exact True.intro
  | strict strictWitness =>
    dsimp only at hModeChk
    have hObl := checkNatSpecWitness_sound strictWitness (bool_and_left hModeChk)
    have hNotPre := checkNatSpecFalsifies_sound strictWitness (bool_and_right hModeChk)
    refine ⟨⟨strictWitness, hObl, hNotPre⟩, fun hRev => hNotPre (hRev strictWitness hObl)⟩
  | equiv revCerts =>
    dsimp only at hModeChk
    have hRev := checkNatEntailmentEdge_sound hModeChk
    exact fun env => ⟨hFwd env, hRev env⟩

/-- Adequacy refinement mode for `IntLinSpec` entailment checks. -/
inductive IntAdequacyMode where
  /-- Certify sufficiency and non-vacuity only. -/
  | sufficientOnly
  /-- Additionally certify strict strengthening via a concrete witness
  satisfying `obligation` and falsifying `pre`. -/
  | strict (strictWitness : List Int)
  /-- Additionally certify bidirectional equivalence (`obligation ⟹ pre`). -/
  | equiv (revCerts : List (List CutStep))

/-- Mode-specific semantic obligation for `IntAdequacyMode`. -/
def IntAdequacyMode.denote (pre obligation : IntLinSpec) : IntAdequacyMode → Prop
  | .sufficientOnly => True
  | .strict _ =>
    (∃ env : List Int, obligation.holds env ∧ ¬ pre.holds env) ∧
    ¬ (∀ env : List Int, obligation.holds env → pre.holds env)
  | .equiv _ =>
    ∀ env : List Int, pre.holds env ↔ obligation.holds env

/-- Full semantic specification adequacy proposition for `IntLinSpec`. -/
def IntEntailmentAdequacyProp (pre obligation : IntLinSpec)
    (mode : IntAdequacyMode) : Prop :=
  (∀ env : List Int, pre.holds env → obligation.holds env) ∧
  (∃ env : List Int, pre.holds env) ∧
  mode.denote pre obligation

/-- Single-`rfl` reflective adequacy checker for `IntLinSpec`. -/
noncomputable def checkIntEntailmentAdequacy
    (pre obligation : IntLinSpec)
    (fwdCerts : List (List CutStep))
    (satWitness : List Int)
    (mode : IntAdequacyMode) : Bool :=
  checkIntEntailmentEdge pre obligation fwdCerts &&
  checkIntSpecWitness satWitness pre &&
  match mode with
  | .sufficientOnly => true
  | .strict strictWitness =>
    checkIntSpecWitness strictWitness obligation &&
    checkIntSpecFalsifies strictWitness pre
  | .equiv revCerts =>
    checkIntEntailmentEdge obligation pre revCerts

/-- Master reflective Entailment-Graph adequacy theorem for `IntLinSpec`. -/
theorem farkas_int_entailment_adequacy_cert
    (pre obligation : IntLinSpec)
    (fwdCerts : List (List CutStep))
    (satWitness : List Int)
    (mode : IntAdequacyMode)
    (hChk : checkIntEntailmentAdequacy pre obligation fwdCerts satWitness mode = true) :
    IntEntailmentAdequacyProp pre obligation mode := by
  dsimp only [checkIntEntailmentAdequacy] at hChk
  have hLeft := bool_and_left hChk
  have hFwd := checkIntEntailmentEdge_sound (bool_and_left hLeft)
  have hSat := checkIntSpecWitness_sound satWitness (bool_and_right hLeft)
  have hModeChk := bool_and_right hChk
  refine ⟨hFwd, ⟨satWitness, hSat⟩, ?_⟩
  cases mode with
  | sufficientOnly => exact True.intro
  | strict strictWitness =>
    dsimp only at hModeChk
    have hObl := checkIntSpecWitness_sound strictWitness (bool_and_left hModeChk)
    have hNotPre := checkIntSpecFalsifies_sound strictWitness (bool_and_right hModeChk)
    refine ⟨⟨strictWitness, hObl, hNotPre⟩, fun hRev => hNotPre (hRev strictWitness hObl)⟩
  | equiv revCerts =>
    dsimp only at hModeChk
    have hRev := checkIntEntailmentEdge_sound hModeChk
    exact fun env => ⟨hFwd env, hRev env⟩

/-! ## 6. Unified `FarkasMirGoal` / `FarkasMirCert` Schema -/

/-- Unified reflective goal schema covering unsigned MIR arithmetic overflow /
underflow freedom, `Anneal.UnsafeObligations` pointer/slice/alignment safety,
`Anneal.AiPcc` wrapped-interval refinement, and reflective Entailment-Graph
specification adequacy. -/
inductive FarkasMirGoal where
  | uintAddNoOverflow
      (u : UintTy) (hyps : List NatCutIneq) (lhs rhs : NatLinExpr)
  | uintSubNoUnderflow
      (u : UintTy) (hyps : List NatCutIneq) (lhs rhs : NatLinExpr)
  /-- Like `uintSubNoUnderflow`, but the operand range `lhs < 2^width` is also
  certified (paired with `.pair stepsLe stepsRange`). -/
  | uintSubNoUnderflowCertified
      (u : UintTy) (hyps : List NatCutIneq) (lhs rhs : NatLinExpr)
  | uintMulConstNoOverflow
      (u : UintTy) (hyps : List NatCutIneq) (k : Nat) (x : NatLinExpr)
  | sliceBounds
      (hyps : List NatCutIneq) (off len total : NatLinExpr)
  | sliceSplit
      (hyps : List NatCutIneq) (mid right total : NatLinExpr)
  | alignedStride
      (hyps : List NatCutIneq) (alignBytes : Nat) (off quot : NatLinExpr)
  | nonOverlappingPtrs
      (hyps : List NatCutIneq) (srcOff dstOff count : NatLinExpr)
      (dir : NonOverlapDir)
  | arrayToSliceCast
      (hyps : List NatCutIneq) (elemSize elemAlign : Nat)
      (off quot arrayLen allocLen : NatLinExpr)
  | aipccIntervalRefine
      (hyps : List NatCutIneq) (M lo hi : Nat) (x : NatLinExpr)
  | natEntailmentAdequacy
      (pre obligation : NatLinSpec) (satWitness : List Nat)
      (mode : NatAdequacyMode)
  | intEntailmentAdequacy
      (pre obligation : IntLinSpec) (satWitness : List Int)
      (mode : IntAdequacyMode)

/-- Unified certificate payload paired with `FarkasMirGoal`. -/
inductive FarkasMirCert where
  | single (steps : List CutStep)
  | pair   (steps1 steps2 : List CutStep)
  | triple (steps1 steps2 steps3 : List CutStep)
  | edge   (certs : List (List CutStep))

/-- Semantic proposition denoted by a `FarkasMirGoal`. -/
def FarkasMirGoal.denote : FarkasMirGoal → Prop
  | .uintAddNoOverflow u hyps lhs rhs =>
    ∀ (env : List Nat) (locals : List LocalSlot) (mem : Memory),
      HypsImp (NatCutIneq.holds env) hyps
        (lhs.eval env + rhs.eval env < modPow2 (uintWidth u) ∧
         lhs.eval env + rhs.eval env < scalarModulus (uintBytes u) ∧
         evalScalarBinOp .addUnchecked
           ⟨lhs.eval env, uintBytes u⟩ ⟨rhs.eval env, uintBytes u⟩
           locals mem false =
           .ok (.scalar ⟨lhs.eval env + rhs.eval env, uintBytes u⟩) locals mem ∧
         evalScalarBinOp .addWithOverflow
           ⟨lhs.eval env, uintBytes u⟩ ⟨rhs.eval env, uintBytes u⟩
           locals mem false =
           .ok (.aggregate 0
             [.scalar ⟨lhs.eval env + rhs.eval env, uintBytes u⟩,
              .scalar ⟨0, 1⟩]) locals mem)
  | .uintSubNoUnderflow u hyps lhs rhs =>
    ∀ (env : List Nat) (locals : List LocalSlot) (mem : Memory),
      lhs.eval env < modPow2 (uintWidth u) →
      HypsImp (NatCutIneq.holds env) hyps
        (rhs.eval env ≤ lhs.eval env ∧
         lhs.eval env - rhs.eval env < modPow2 (uintWidth u) ∧
         evalScalarBinOp .subUnchecked
           ⟨lhs.eval env, uintBytes u⟩ ⟨rhs.eval env, uintBytes u⟩
           locals mem false =
           .ok (.scalar ⟨lhs.eval env - rhs.eval env, uintBytes u⟩) locals mem ∧
         evalScalarBinOp .subWithOverflow
           ⟨lhs.eval env, uintBytes u⟩ ⟨rhs.eval env, uintBytes u⟩
           locals mem false =
           .ok (.aggregate 0
             [.scalar ⟨lhs.eval env - rhs.eval env, uintBytes u⟩,
              .scalar ⟨0, 1⟩]) locals mem)
  | .uintSubNoUnderflowCertified u hyps lhs rhs =>
    ∀ (env : List Nat) (locals : List LocalSlot) (mem : Memory),
      HypsImp (NatCutIneq.holds env) hyps
        (lhs.eval env < modPow2 (uintWidth u) ∧
         rhs.eval env ≤ lhs.eval env ∧
         lhs.eval env - rhs.eval env < modPow2 (uintWidth u) ∧
         evalScalarBinOp .subUnchecked
           ⟨lhs.eval env, uintBytes u⟩ ⟨rhs.eval env, uintBytes u⟩
           locals mem false =
           .ok (.scalar ⟨lhs.eval env - rhs.eval env, uintBytes u⟩) locals mem ∧
         evalScalarBinOp .subWithOverflow
           ⟨lhs.eval env, uintBytes u⟩ ⟨rhs.eval env, uintBytes u⟩
           locals mem false =
           .ok (.aggregate 0
             [.scalar ⟨lhs.eval env - rhs.eval env, uintBytes u⟩,
              .scalar ⟨0, 1⟩]) locals mem)
  | .uintMulConstNoOverflow u hyps k x =>
    ∀ (env : List Nat) (locals : List LocalSlot) (mem : Memory),
      HypsImp (NatCutIneq.holds env) hyps
        (UintScalarInRange u ⟨k, uintBytes u⟩ ∧
         k * x.eval env < modPow2 (uintWidth u) ∧
         k * x.eval env < scalarModulus (uintBytes u) ∧
         evalScalarBinOp .mulUnchecked
           ⟨k, uintBytes u⟩ ⟨x.eval env, uintBytes u⟩
           locals mem false =
           .ok (.scalar ⟨k * x.eval env, uintBytes u⟩) locals mem ∧
         evalScalarBinOp .mulWithOverflow
           ⟨k, uintBytes u⟩ ⟨x.eval env, uintBytes u⟩
           locals mem false =
           .ok (.aggregate 0
             [.scalar ⟨k * x.eval env, uintBytes u⟩,
              .scalar ⟨0, 1⟩]) locals mem)
  | .sliceBounds hyps off len total =>
    ∀ (env : List Nat) (rp : RawPtrVal),
      rp.offset = off.eval env →
      HypsImp (NatCutIneq.holds env) hyps
        (ValidSliceRange rp (len.eval env) (total.eval env) ∧
         evalPtrOffset rp (len.eval env) (total.eval env) =
           some { rp with offset := rp.offset + len.eval env })
  | .sliceSplit hyps mid right total =>
    ∀ (env : List Nat) (rp : RawPtrVal) (elemSize : Nat),
      HypsImp (NatCutIneq.holds env) hyps
        (ValidSliceSplit rp elemSize (total.eval env) (mid.eval env) (right.eval env) ∧
         evalPtrOffset rp (mid.eval env * elemSize)
           (rp.offset + total.eval env * elemSize) =
           some (sliceSplitRightPtr rp elemSize (mid.eval env)))
  | .alignedStride hyps alignBytes off _ =>
    ∀ (env : List Nat) (rp : RawPtrVal),
      rp.offset = off.eval env →
      HypsImp (NatCutIneq.holds env) hyps (AlignedPtr rp alignBytes)
  | .nonOverlappingPtrs hyps srcOff dstOff count _ =>
    ∀ (env : List Nat) (src dst : RawPtrVal),
      src.offset = srcOff.eval env →
      dst.offset = dstOff.eval env →
      HypsImp (NatCutIneq.holds env) hyps
        (NonOverlappingPtrs src dst (count.eval env))
  | .arrayToSliceCast hyps elemSize elemAlign off _ arrayLen allocLen =>
    ∀ (env : List Nat) (rp : RawPtrVal),
      rp.offset = off.eval env →
      HypsImp (NatCutIneq.holds env) hyps
        (ValidArrayToSliceCast rp elemSize elemAlign
           (arrayLen.eval env) (allocLen.eval env) ∧
         evalPtrOffset rp (arrayLen.eval env * elemSize) (allocLen.eval env) =
           some { rp with offset := rp.offset + arrayLen.eval env * elemSize })
  | .aipccIntervalRefine hyps M lo hi x =>
    ∀ env : List Nat,
      HypsImp (NatCutIneq.holds env) hyps
        (WrappedInterval.denote M (.iv lo hi) (x.eval env))
  | .natEntailmentAdequacy pre obligation _ mode =>
    NatEntailmentAdequacyProp pre obligation mode
  | .intEntailmentAdequacy pre obligation _ mode =>
    IntEntailmentAdequacyProp pre obligation mode

/-- Unified fail-closed reflective checker for `FarkasMirGoal`. -/
noncomputable def checkFarkasMirGoal : FarkasMirGoal → FarkasMirCert → Bool
  | .uintAddNoOverflow u hyps lhs rhs, .single steps =>
    checkNatCutGoal
      ⟨hyps, ⟨.add (.add lhs rhs) (.cst 1), .cst (modPow2 (uintWidth u))⟩⟩ steps
  | .uintSubNoUnderflow _ hyps lhs rhs, .single steps =>
    checkNatCutGoal ⟨hyps, ⟨rhs, lhs⟩⟩ steps
  | .uintSubNoUnderflowCertified u hyps lhs rhs, .pair stepsLe stepsRange =>
    checkNatCutGoal ⟨hyps, ⟨rhs, lhs⟩⟩ stepsLe &&
    checkNatCutGoal ⟨hyps, ⟨.add lhs (.cst 1), .cst (modPow2 (uintWidth u))⟩⟩ stepsRange
  | .uintMulConstNoOverflow u hyps k x, .single steps =>
    Nat.blt k (modPow2 (uintWidth u)) &&
    checkNatCutGoal
      ⟨hyps, ⟨.add (.mulC k x) (.cst 1), .cst (modPow2 (uintWidth u))⟩⟩ steps
  | .sliceBounds hyps off len total, .single steps =>
    checkNatCutGoal ⟨hyps, ⟨.add off len, total⟩⟩ steps
  | .sliceSplit hyps mid right total, .pair stepsLe stepsGe =>
    checkNatCutGoal ⟨hyps, ⟨.add mid right, total⟩⟩ stepsLe &&
    checkNatCutGoal ⟨hyps, ⟨total, .add mid right⟩⟩ stepsGe
  | .alignedStride hyps alignBytes off quot, .pair stepsLe stepsGe =>
    Nat.ble 1 alignBytes &&
    checkNatCutGoal ⟨hyps, ⟨.mulC alignBytes quot, off⟩⟩ stepsLe &&
    checkNatCutGoal ⟨hyps, ⟨off, .mulC alignBytes quot⟩⟩ stepsGe
  | .nonOverlappingPtrs hyps srcOff dstOff count dir, .single steps =>
    checkNatCutGoal ⟨hyps, nonOverlapTargetIneq srcOff dstOff count dir⟩ steps
  | .arrayToSliceCast hyps elemSize elemAlign off quot arrayLen allocLen,
    .triple stepsAlignLe stepsAlignGe stepsRange =>
    Nat.ble 1 elemAlign &&
    checkNatCutGoal ⟨hyps, ⟨.mulC elemAlign quot, off⟩⟩ stepsAlignLe &&
    checkNatCutGoal ⟨hyps, ⟨off, .mulC elemAlign quot⟩⟩ stepsAlignGe &&
    checkNatCutGoal ⟨hyps, ⟨.add off (.mulC elemSize arrayLen), allocLen⟩⟩ stepsRange
  | .aipccIntervalRefine hyps M lo hi x, .pair stepsLo stepsHi =>
    Nat.ble lo hi &&
    Nat.blt hi M &&
    checkNatCutGoal ⟨hyps, ⟨.cst lo, x⟩⟩ stepsLo &&
    checkNatCutGoal ⟨hyps, ⟨x, .cst hi⟩⟩ stepsHi
  | .natEntailmentAdequacy pre obligation satWitness mode, .edge fwdCerts =>
    checkNatEntailmentAdequacy pre obligation fwdCerts satWitness mode
  | .intEntailmentAdequacy pre obligation satWitness mode, .edge fwdCerts =>
    checkIntEntailmentAdequacy pre obligation fwdCerts satWitness mode
  | _, _ => false

/-- Master soundness theorem for the unified `FarkasMirGoal` checker. -/
theorem checkFarkasMirGoal_sound (goal : FarkasMirGoal) (cert : FarkasMirCert)
    (hChk : checkFarkasMirGoal goal cert = true) : goal.denote := by
  cases goal with
  | uintAddNoOverflow u hyps lhs rhs =>
    cases cert with
    | single steps =>
      intro env locals mem
      exact farkas_discharges_uint_add_no_overflow u hyps lhs rhs steps hChk env locals mem
    | pair _ _ | triple _ _ _ | edge _ => nomatch hChk
  | uintSubNoUnderflow u hyps lhs rhs =>
    cases cert with
    | single steps =>
      intro env locals mem hLt
      exact farkas_discharges_uint_sub_no_underflow u hyps lhs rhs steps hChk env locals mem hLt
    | pair _ _ | triple _ _ _ | edge _ => nomatch hChk
  | uintSubNoUnderflowCertified u hyps lhs rhs =>
    cases cert with
    | pair stepsLe stepsRange =>
      dsimp only [checkFarkasMirGoal] at hChk
      intro env locals mem
      exact farkas_discharges_uint_sub_no_underflow_certified u hyps lhs rhs
        stepsLe stepsRange (bool_and_left hChk) (bool_and_right hChk) env locals mem
    | single _ | triple _ _ _ | edge _ => nomatch hChk
  | uintMulConstNoOverflow u hyps k x =>
    cases cert with
    | single steps =>
      dsimp only [checkFarkasMirGoal] at hChk
      intro env locals mem
      exact farkas_discharges_uint_mul_const_no_overflow u hyps k x steps
        (bool_and_left hChk) (bool_and_right hChk) env locals mem
    | pair _ _ | triple _ _ _ | edge _ => nomatch hChk
  | sliceBounds hyps off len total =>
    cases cert with
    | single steps =>
      intro env rp hOff
      exact farkas_discharges_slice_bounds hyps off len total steps hChk env rp hOff
    | pair _ _ | triple _ _ _ | edge _ => nomatch hChk
  | sliceSplit hyps mid right total =>
    cases cert with
    | pair stepsLe stepsGe =>
      dsimp only [checkFarkasMirGoal] at hChk
      intro env rp elemSize
      exact farkas_discharges_slice_split hyps mid right total stepsLe stepsGe
        (bool_and_left hChk) (bool_and_right hChk) env rp elemSize
    | single _ | triple _ _ _ | edge _ => nomatch hChk
  | alignedStride hyps alignBytes off quot =>
    cases cert with
    | pair stepsLe stepsGe =>
      dsimp only [checkFarkasMirGoal] at hChk
      have hLeft := bool_and_left hChk
      intro env rp hOff
      exact farkas_discharges_aligned_stride hyps alignBytes off quot stepsLe stepsGe
        (bool_and_left hLeft) (bool_and_right hLeft) (bool_and_right hChk) env rp hOff
    | single _ | triple _ _ _ | edge _ => nomatch hChk
  | nonOverlappingPtrs hyps srcOff dstOff count dir =>
    cases cert with
    | single steps =>
      intro env src dst hSrc hDst
      exact farkas_discharges_non_overlapping_ptrs hyps srcOff dstOff count dir steps
        hChk env src dst hSrc hDst
    | pair _ _ | triple _ _ _ | edge _ => nomatch hChk
  | arrayToSliceCast hyps elemSize elemAlign off quot arrayLen allocLen =>
    cases cert with
    | triple s1 s2 s3 =>
      dsimp only [checkFarkasMirGoal] at hChk
      have h123 := bool_and_left hChk
      have h12 := bool_and_left h123
      intro env rp hOff
      exact farkas_discharges_array_to_slice_cast hyps elemSize elemAlign off quot
        arrayLen allocLen s1 s2 s3 (bool_and_left h12) (bool_and_right h12)
        (bool_and_right h123) (bool_and_right hChk) env rp hOff
    | single _ | pair _ _ | edge _ => nomatch hChk
  | aipccIntervalRefine hyps M lo hi x =>
    cases cert with
    | pair stepsLo stepsHi =>
      dsimp only [checkFarkasMirGoal] at hChk
      have h123 := bool_and_left hChk
      have h12 := bool_and_left h123
      intro env
      exact farkas_discharges_aipcc_interval_refinement hyps M lo hi x stepsLo stepsHi
        (bool_and_left h12) (bool_and_right h12) (bool_and_right h123)
        (bool_and_right hChk) env
    | single _ | triple _ _ _ | edge _ => nomatch hChk
  | natEntailmentAdequacy pre obligation satWitness mode =>
    cases cert with
    | edge fwdCerts =>
      exact farkas_entailment_adequacy_cert pre obligation fwdCerts satWitness mode hChk
    | single _ | pair _ _ | triple _ _ _ => nomatch hChk
  | intEntailmentAdequacy pre obligation satWitness mode =>
    cases cert with
    | edge fwdCerts =>
      exact farkas_int_entailment_adequacy_cert pre obligation fwdCerts satWitness mode hChk
    | single _ | pair _ _ | triple _ _ _ => nomatch hChk

/-! ## 7. Built-In Positive & Negative (`= false`) `rfl` Canaries -/

/-- Canary: `u64` addition overflow-freedom (`a ≤ 1000`, `b ≤ 2000` implies
`a + b < 2^64` and exact `.addUnchecked` / `.addWithOverflow` with overflow `0`). -/
theorem canary_u64_add_no_overflow (a b : Nat) (locals : List LocalSlot) (mem : Memory)
    (ha : a ≤ 1000) (hb : b ≤ 2000) :
    a + b < modPow2 (uintWidth .u64) ∧
    a + b < scalarModulus (uintBytes .u64) ∧
    evalScalarBinOp .addUnchecked ⟨a, uintBytes .u64⟩ ⟨b, uintBytes .u64⟩
      locals mem false =
      .ok (.scalar ⟨a + b, uintBytes .u64⟩) locals mem ∧
    evalScalarBinOp .addWithOverflow ⟨a, uintBytes .u64⟩ ⟨b, uintBytes .u64⟩
      locals mem false =
      .ok (.aggregate 0 [.scalar ⟨a + b, uintBytes .u64⟩, .scalar ⟨0, 1⟩]) locals mem :=
  farkas_discharges_u64_add_no_overflow
    [⟨.var 0, .cst 1000⟩, ⟨.var 1, .cst 2000⟩] (.var 0) (.var 1)
    [.hyp 0, .hyp 1, .comb 0 1 1 1, .hyp 4, .comb 2 1 3 1]
    rfl [a, b] locals mem ha hb

/-- Canary: `u128` boundary addition overflow-freedom at `2^128 = magCap128`
(`a ≤ 2^128 - 10`, `b ≤ 9` implies `a + b < 2^128`). -/
theorem canary_u128_add_boundary_no_overflow (a b : Nat)
    (locals : List LocalSlot) (mem : Memory)
    (ha : a ≤ modPow2 128 - 10) (hb : b ≤ 9) :
    a + b < modPow2 (uintWidth .u128) ∧
    a + b < scalarModulus (uintBytes .u128) ∧
    evalScalarBinOp .addUnchecked ⟨a, uintBytes .u128⟩ ⟨b, uintBytes .u128⟩
      locals mem false =
      .ok (.scalar ⟨a + b, uintBytes .u128⟩) locals mem ∧
    evalScalarBinOp .addWithOverflow ⟨a, uintBytes .u128⟩ ⟨b, uintBytes .u128⟩
      locals mem false =
      .ok (.aggregate 0 [.scalar ⟨a + b, uintBytes .u128⟩, .scalar ⟨0, 1⟩]) locals mem :=
  farkas_discharges_uint_add_no_overflow .u128
    [⟨.var 0, .cst (modPow2 128 - 10)⟩, ⟨.var 1, .cst 9⟩] (.var 0) (.var 1)
    [.hyp 0, .hyp 1, .comb 0 1 1 1, .hyp 4, .comb 2 1 3 1]
    rfl [a, b] locals mem ha hb

/-- Canary: `u32` subtraction underflow-freedom (`b + 4 ≤ a` implies `b ≤ a`,
`a - b < 2^32`, and zero-overflow `.subUnchecked` / `.subWithOverflow`). -/
theorem canary_u32_sub_no_underflow (a b : Nat) (locals : List LocalSlot) (mem : Memory)
    (hRange : a < modPow2 (uintWidth .u32)) (hGap : b + 4 ≤ a) :
    b ≤ a ∧
    a - b < modPow2 (uintWidth .u32) ∧
    evalScalarBinOp .subUnchecked ⟨a, uintBytes .u32⟩ ⟨b, uintBytes .u32⟩
      locals mem false =
      .ok (.scalar ⟨a - b, uintBytes .u32⟩) locals mem ∧
    evalScalarBinOp .subWithOverflow ⟨a, uintBytes .u32⟩ ⟨b, uintBytes .u32⟩
      locals mem false =
      .ok (.aggregate 0 [.scalar ⟨a - b, uintBytes .u32⟩, .scalar ⟨0, 1⟩]) locals mem :=
  farkas_discharges_uint_sub_no_underflow .u32
    [⟨.add (.var 1) (.cst 4), .var 0⟩] (.var 0) (.var 1)
    [.hyp 0, .hyp 3, .comb 0 1 1 1]
    rfl [a, b] locals mem hRange hGap

/-- Canary: constant-scaled `u64` multiplication overflow-freedom (`x ≤ 1024`
implies `UintScalarInRange .u64 ⟨8, 8⟩` and `8 * x < 2^64`). -/
theorem canary_u64_mul_const_no_overflow (x : Nat) (locals : List LocalSlot) (mem : Memory)
    (hx : x ≤ 1024) :
    UintScalarInRange .u64 ⟨8, uintBytes .u64⟩ ∧
    8 * x < modPow2 (uintWidth .u64) ∧
    8 * x < scalarModulus (uintBytes .u64) ∧
    evalScalarBinOp .mulUnchecked ⟨8, uintBytes .u64⟩ ⟨x, uintBytes .u64⟩
      locals mem false =
      .ok (.scalar ⟨8 * x, uintBytes .u64⟩) locals mem ∧
    evalScalarBinOp .mulWithOverflow ⟨8, uintBytes .u64⟩ ⟨x, uintBytes .u64⟩
      locals mem false =
      .ok (.aggregate 0 [.scalar ⟨8 * x, uintBytes .u64⟩, .scalar ⟨0, 1⟩]) locals mem :=
  farkas_discharges_uint_mul_const_no_overflow .u64
    [⟨.var 0, .cst 1024⟩] 8 (.var 0)
    [.hyp 0, .hyp 2, .comb 0 8 1 1]
    rfl rfl [x] locals mem hx

/-- Canary: `ValidSliceRange` and `evalPtrOffset` from Farkas bounds. -/
theorem canary_slice_bounds (rp : RawPtrVal) (len total : Nat)
    (h1 : rp.offset ≤ 16) (h2 : len ≤ 32) (h3 : 48 ≤ total) :
    ValidSliceRange rp len total ∧
    evalPtrOffset rp len total = some { rp with offset := rp.offset + len } :=
  farkas_discharges_slice_bounds
    [⟨.var 0, .cst 16⟩, ⟨.var 1, .cst 32⟩, ⟨.cst 48, .var 2⟩]
    (.var 0) (.var 1) (.var 2)
    [.hyp 0, .hyp 1, .comb 0 1 1 1, .hyp 2, .comb 2 1 3 1, .hyp 6, .comb 4 1 5 1]
    rfl [rp.offset, len, total] rp rfl h1 h2 h3

/-- Canary: `ValidSliceSplit` from Farkas partition equality certificates. -/
theorem canary_slice_split (rp : RawPtrVal) (elemSize mid right total : Nat)
    (h1 : mid + right ≤ total) (h2 : total ≤ mid + right) :
    ValidSliceSplit rp elemSize total mid right ∧
    evalPtrOffset rp (mid * elemSize) (rp.offset + total * elemSize) =
      some (sliceSplitRightPtr rp elemSize mid) :=
  farkas_discharges_slice_split
    [⟨.add (.var 0) (.var 1), .var 2⟩, ⟨.var 2, .add (.var 0) (.var 1)⟩]
    (.var 0) (.var 1) (.var 2)
    [.hyp 0, .hyp 5, .comb 0 1 1 1]
    [.hyp 1, .hyp 5, .comb 0 1 1 1]
    rfl rfl [mid, right, total] rp elemSize h1 h2

/-- Canary: `AlignedPtr rp 8` proved via a genuinely cut-required Chvatal-Gomory
`CutStep.divCut 2` from `2 * z ≤ 1`, `8 * q ≤ rp.offset + 2 * z`, and
`rp.offset ≤ 8 * q + 2 * z` (rationally satisfiable at `z = 1/2` with
`rp.offset = 8 * q ± 1`, so cut-free Farkas combinations cannot discharge
either direction). -/
theorem canary_aligned_stride_divcut (rp : RawPtrVal) (q z : Nat)
    (hz : 2 * z ≤ 1) (h1 : 8 * q ≤ rp.offset + 2 * z)
    (h2 : rp.offset ≤ 8 * q + 2 * z) :
    AlignedPtr rp 8 :=
  farkas_discharges_aligned_stride
    [⟨.mulC 2 (.var 2), .cst 1⟩,
     ⟨.mulC 8 (.var 1), .add (.var 0) (.mulC 2 (.var 2))⟩,
     ⟨.var 0, .add (.mulC 8 (.var 1)) (.mulC 2 (.var 2))⟩]
    8 (.var 0) (.var 1)
    [.hyp 0, .divCut 2 0, .hyp 1, .comb 2 1 1 2, .hyp 6, .comb 3 1 4 1]
    [.hyp 0, .divCut 2 0, .hyp 2, .comb 2 1 1 2, .hyp 6, .comb 3 1 4 1]
    rfl rfl rfl [rp.offset, q, z] rp rfl hz h1 h2

/-- Canary: `NonOverlappingPtrs` when `src.offset + count ≤ dst.offset`. -/
theorem canary_non_overlapping_ptrs (src dst : RawPtrVal) (count : Nat)
    (h1 : src.offset + count ≤ 64) (h2 : 64 ≤ dst.offset) :
    NonOverlappingPtrs src dst count :=
  farkas_discharges_non_overlapping_ptrs
    [⟨.add (.var 0) (.var 2), .cst 64⟩, ⟨.cst 64, .var 1⟩]
    (.var 0) (.var 1) (.var 2) .srcBeforeDst
    [.hyp 0, .hyp 1, .comb 0 1 1 1, .hyp 5, .comb 2 1 3 1]
    rfl [src.offset, dst.offset, count] src dst rfl rfl h1 h2

/-- Canary: `ValidArrayToSliceCast` composing alignment and slice range. -/
theorem canary_array_to_slice_cast (rp : RawPtrVal) (q arrayLen allocLen : Nat)
    (hAlign1 : 8 * q ≤ rp.offset) (hAlign2 : rp.offset ≤ 8 * q)
    (hOff : rp.offset ≤ 64) (hLen : arrayLen ≤ 10) (hAlloc : 144 ≤ allocLen) :
    ValidArrayToSliceCast rp 8 8 arrayLen allocLen ∧
    evalPtrOffset rp (arrayLen * 8) allocLen =
      some { rp with offset := rp.offset + arrayLen * 8 } :=
  farkas_discharges_array_to_slice_cast
    [⟨.mulC 8 (.var 1), .var 0⟩, ⟨.var 0, .mulC 8 (.var 1)⟩,
     ⟨.var 0, .cst 64⟩, ⟨.var 2, .cst 10⟩, ⟨.cst 144, .var 3⟩]
    8 8 (.var 0) (.var 1) (.var 2) (.var 3)
    [.hyp 0, .hyp 9, .comb 0 1 1 1]
    [.hyp 1, .hyp 9, .comb 0 1 1 1]
    [.hyp 2, .hyp 3, .comb 0 1 1 8, .hyp 4, .comb 2 1 3 1, .hyp 9, .comb 4 1 5 1]
    rfl rfl rfl rfl [rp.offset, q, arrayLen, allocLen] rp rfl
    hAlign1 hAlign2 hOff hLen hAlloc

/-- Canary: `Anneal.AiPcc` `WrappedInterval` and `MirAbsSlot.uint` refinement. -/
theorem canary_aipcc_interval_and_slot_refinement
    (ty : Ty) (locals : List LocalSlot) (t : Tnum) (sg : StridedCong)
    (sc : ScalarInt)
    (hSlot : (MirAbsSlot.uint .u32 ⟨.init, t, .iv 0 1000, sg⟩).denote ty locals
      (.init (.scalar sc)))
    (hGuardLo : 10 ≤ sc.bits) (hGuardHi : sc.bits ≤ 50) :
    WrappedInterval.denote (modPow2 (uintWidth .u32)) (.iv 10 50) sc.bits ∧
    (MirAbsSlot.uint .u32 ⟨.init, t, .iv 10 50, sg⟩).denote ty locals
      (.init (.scalar sc)) := by
  have hRef :=
    farkas_refines_mirAbsSlot_uint .u32
      [⟨.cst 10, .var 0⟩, ⟨.var 0, .cst 50⟩] 10 50 (.var 0)
      [.hyp 0, .hyp 3, .comb 0 1 1 1]
      [.hyp 1, .hyp 3, .comb 0 1 1 1]
      rfl rfl rfl rfl [sc.bits] ty locals ⟨.init, t, .iv 0 1000, sg⟩ sc hSlot rfl
      hGuardLo hGuardHi
  exact ⟨(absVal_some_elim hRef.1.2.2).2.2.1, hRef.1⟩

/-- Canary: `NatLinSpec` strict entailment adequacy (`x ≤ 5 ∧ y ≤ 5` strictly
entails `x + y ≤ 12`, witnessed non-vacuous at `[0, 0]` and strict at `[6, 6]`). -/
theorem canary_nat_entailment_strict :
    NatEntailmentAdequacyProp
      [⟨.var 0, .cst 5⟩, ⟨.var 1, .cst 5⟩]
      [⟨.add (.var 0) (.var 1), .cst 12⟩]
      (.strict [6, 6]) :=
  farkas_entailment_adequacy_cert
    [⟨.var 0, .cst 5⟩, ⟨.var 1, .cst 5⟩]
    [⟨.add (.var 0) (.var 1), .cst 12⟩]
    [[.hyp 0, .hyp 1, .comb 0 1 1 1, .hyp 4, .comb 2 1 3 1]]
    [0, 0]
    (.strict [6, 6])
    rfl

/-- Canary: `NatLinSpec` bidirectional equivalence (`x + 1 ≤ y` ↔ `x + 2 ≤ y + 1`). -/
theorem canary_nat_entailment_equiv :
    NatEntailmentAdequacyProp
      [⟨.add (.var 0) (.cst 1), .var 1⟩]
      [⟨.add (.var 0) (.cst 2), .add (.var 1) (.cst 1)⟩]
      (.equiv [[.hyp 0, .hyp 3, .comb 0 1 1 1]]) :=
  farkas_entailment_adequacy_cert
    [⟨.add (.var 0) (.cst 1), .var 1⟩]
    [⟨.add (.var 0) (.cst 2), .add (.var 1) (.cst 1)⟩]
    [[.hyp 0, .hyp 3, .comb 0 1 1 1]]
    [0, 1]
    (.equiv [[.hyp 0, .hyp 3, .comb 0 1 1 1]])
    rfl

/-- Canary: `IntLinSpec` strict entailment adequacy with negative witnesses
(`-3 ≤ x ∧ x ≤ 2` strictly entails `-5 ≤ x`, sat at `[Int.negOfNat 1]`, strict
counter-witness at `[Int.negOfNat 4]`). -/
theorem canary_int_entailment_strict :
    IntEntailmentAdequacyProp
      [⟨.cst ⟨true, 3⟩, .var 0⟩, ⟨.var 0, .cst ⟨false, 2⟩⟩]
      [⟨.cst ⟨true, 5⟩, .var 0⟩]
      (.strict [Int.negOfNat 4]) :=
  farkas_int_entailment_adequacy_cert
    [⟨.cst ⟨true, 3⟩, .var 0⟩, ⟨.var 0, .cst ⟨false, 2⟩⟩]
    [⟨.cst ⟨true, 5⟩, .var 0⟩]
    [[.hyp 0, .hyp 2, .comb 0 1 1 1]]
    [Int.negOfNat 1]
    (.strict [Int.negOfNat 4])
    rfl

/-- Canary: two-edge `NatEntailmentPath` transitivity (`x ≤ 3 ⟹ x ≤ 5 ⟹ x ≤ 10`). -/
theorem canary_nat_entailment_path_trans :
    ∀ env : List Nat,
      NatLinSpec.holds env [⟨.var 0, .cst 3⟩] →
      NatLinSpec.holds env [⟨.var 0, .cst 10⟩] :=
  checkNatEntailmentPath_sound
    [ { src := [⟨.var 0, .cst 3⟩], dst := [⟨.var 0, .cst 5⟩],
        certs := [[.hyp 0, .hyp 2, .comb 0 1 1 1]] }
    , { src := [⟨.var 0, .cst 5⟩], dst := [⟨.var 0, .cst 10⟩],
        certs := [[.hyp 0, .hyp 2, .comb 0 1 1 1]] } ]
    [⟨.var 0, .cst 3⟩] [⟨.var 0, .cst 10⟩]
    rfl

/-- Canary: whole-graph reflective check on a two-edge `NatEntailmentGraph`. -/
theorem canary_nat_entailment_graph_ok :
    checkNatEntailmentGraph
      { nodes := [[⟨.var 0, .cst 3⟩], [⟨.var 0, .cst 5⟩], [⟨.var 0, .cst 10⟩]]
        edges :=
          [ (0, 1, [[.hyp 0, .hyp 2, .comb 0 1 1 1]])
          , (1, 2, [[.hyp 0, .hyp 2, .comb 0 1 1 1]]) ] } = true :=
  rfl

/-- Canary: unified `checkFarkasMirGoal` discharges a `sliceBounds` goal. -/
theorem canary_unified_farkas_mir_goal :
    (FarkasMirGoal.sliceBounds
      [⟨.var 0, .cst 8⟩, ⟨.var 1, .cst 8⟩, ⟨.cst 16, .var 2⟩]
      (.var 0) (.var 1) (.var 2)).denote :=
  checkFarkasMirGoal_sound _
    (.single [.hyp 0, .hyp 1, .comb 0 1 1 1, .hyp 2, .comb 2 1 3 1, .hyp 6, .comb 4 1 5 1])
    rfl

/-- Canary: fully certified `u32` subtraction (both `b ≤ a` AND the operand range
`a < 2^32` are discharged by certificates; no external range hypothesis). -/
theorem canary_u32_sub_no_underflow_certified (a b : Nat)
    (locals : List LocalSlot) (mem : Memory)
    (hGap : b + 4 ≤ a) (hA : a ≤ 1000) :
    a < modPow2 (uintWidth .u32) ∧ b ≤ a ∧ a - b < modPow2 (uintWidth .u32) ∧
    evalScalarBinOp .subUnchecked ⟨a, uintBytes .u32⟩ ⟨b, uintBytes .u32⟩
      locals mem false =
      .ok (.scalar ⟨a - b, uintBytes .u32⟩) locals mem ∧
    evalScalarBinOp .subWithOverflow ⟨a, uintBytes .u32⟩ ⟨b, uintBytes .u32⟩
      locals mem false =
      .ok (.aggregate 0 [.scalar ⟨a - b, uintBytes .u32⟩, .scalar ⟨0, 1⟩]) locals mem :=
  checkFarkasMirGoal_sound
    (.uintSubNoUnderflowCertified .u32
      [⟨.add (.var 1) (.cst 4), .var 0⟩, ⟨.var 0, .cst 1000⟩] (.var 0) (.var 1))
    (.pair [.hyp 0, .hyp 4, .comb 0 1 1 1] [.hyp 1, .hyp 4, .comb 0 1 1 1])
    rfl [a, b] locals mem hGap hA

/-- Canary: the `magCap128` guard is the *sole* reason the detoured trace is
rejected. The same semantically valid `u128` refutation is accepted directly
(all derived rows `≤ 2^128`) and rejected when routed through the
intermediate row `2 * x ≤ 2^129 - 2` (`> magCap128`), although that detour is
arithmetically sound (`2 * hyp + 2 * negGoal` still yields `0 ≤ -2`); an
unrelated over-cap hypothesis also poisons an otherwise valid trace
(`rowsWithinCap` checks every hypothesis). -/
theorem canary_u128_mag_cap_isolated :
    checkFarkasMirGoal
      (.uintAddNoOverflow .u128 [⟨.add (.var 0) (.cst 1), .cst (modPow2 128)⟩]
        (.var 0) (.cst 0))
      (.single [.hyp 0, .hyp 2, .comb 0 1 1 1]) = true ∧
    checkFarkasMirGoal
      (.uintAddNoOverflow .u128 [⟨.add (.var 0) (.cst 1), .cst (modPow2 128)⟩]
        (.var 0) (.cst 0))
      (.single [.hyp 0, .hyp 2, .comb 0 1 0 1, .comb 2 1 1 2]) = false ∧
    checkFarkasMirGoal
      (.uintAddNoOverflow .u128
        [⟨.add (.var 0) (.cst 1), .cst (modPow2 128)⟩, ⟨.var 1, .cst 5⟩]
        (.var 0) (.cst 0))
      (.single [.hyp 0, .hyp 4, .comb 0 1 1 1]) = true ∧
    checkFarkasMirGoal
      (.uintAddNoOverflow .u128
        [⟨.add (.var 0) (.cst 1), .cst (modPow2 128)⟩, ⟨.var 1, .cst (magCap128 + 1)⟩]
        (.var 0) (.cst 0))
      (.single [.hyp 0, .hyp 4, .comb 0 1 1 1]) = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Canary: the unified schema rejects a constant multiplier `k` that is not a
valid `uN` scalar operand (`k ≥ 2^width`), even when `k * x < 2^width` holds
(here `x ≤ 0`), while accepting the in-range neighbour `k = 2^width - 1`. -/
theorem canary_mul_const_operand_range :
    checkFarkasMirGoal
      (.uintMulConstNoOverflow .u8 [⟨.var 0, .cst 0⟩] 255 (.var 0))
      (.single [.hyp 0, .hyp 2, .comb 0 255 1 1]) = true ∧
    checkFarkasMirGoal
      (.uintMulConstNoOverflow .u8 [⟨.var 0, .cst 0⟩] 256 (.var 0))
      (.single [.hyp 0, .hyp 2, .comb 0 256 1 1]) = false :=
  ⟨rfl, rfl⟩

/-! ### Per-Checker Positive / Negative Coverage

Every reflective checker below gets at least one direct `= true` and one direct
`= false` `rfl` canary (previously `checkIntEntailmentGraph`,
`checkIntEntailmentPath`, `check{Nat,Int}SpecWitness`, `sintLe`,
`hasEdgeInList`, and the syntactic `*Beq` checkers were only exercised
indirectly or not at all). -/

/-- Canary: `IntLinSpec` two-edge path (`-3 ≤ x ⟹ -5 ≤ x ⟹ -10 ≤ x`) is accepted,
a disconnected path and a reversed (non-entailing) edge are rejected. -/
theorem canary_int_entailment_path_and_graph :
    checkIntEntailmentPath [⟨.cst ⟨true, 3⟩, .var 0⟩] [⟨.cst ⟨true, 10⟩, .var 0⟩]
      [ { src := [⟨.cst ⟨true, 3⟩, .var 0⟩], dst := [⟨.cst ⟨true, 5⟩, .var 0⟩],
          certs := [[.hyp 0, .hyp 1, .comb 0 1 1 1]] }
      , { src := [⟨.cst ⟨true, 5⟩, .var 0⟩], dst := [⟨.cst ⟨true, 10⟩, .var 0⟩],
          certs := [[.hyp 0, .hyp 1, .comb 0 1 1 1]] } ] = true ∧
    checkIntEntailmentPath [⟨.cst ⟨true, 3⟩, .var 0⟩] [⟨.cst ⟨true, 10⟩, .var 0⟩]
      [ { src := [⟨.cst ⟨true, 3⟩, .var 0⟩], dst := [⟨.cst ⟨true, 5⟩, .var 0⟩],
          certs := [[.hyp 0, .hyp 1, .comb 0 1 1 1]] }
      , { src := [⟨.cst ⟨true, 4⟩, .var 0⟩], dst := [⟨.cst ⟨true, 10⟩, .var 0⟩],
          certs := [[.hyp 0, .hyp 1, .comb 0 1 1 1]] } ] = false ∧
    checkIntEntailmentGraph
      { nodes := [[⟨.cst ⟨true, 3⟩, .var 0⟩], [⟨.cst ⟨true, 5⟩, .var 0⟩],
                  [⟨.cst ⟨true, 10⟩, .var 0⟩]]
        edges := [ (0, 1, [[.hyp 0, .hyp 1, .comb 0 1 1 1]])
                 , (1, 2, [[.hyp 0, .hyp 1, .comb 0 1 1 1]]) ] } = true ∧
    checkIntEntailmentGraph
      { nodes := [[⟨.cst ⟨true, 3⟩, .var 0⟩], [⟨.cst ⟨true, 5⟩, .var 0⟩],
                  [⟨.cst ⟨true, 10⟩, .var 0⟩]]
        edges := [ (0, 1, [[.hyp 0, .hyp 1, .comb 0 1 1 1]])
                 , (2, 0, [[.hyp 0, .hyp 1, .comb 0 1 1 1]]) ] } = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Canary: direct concrete witness checkers, `sintLe` (including the
sign-magnitude negative zero `⟨true, 0⟩`), and `hasEdgeInList`. -/
theorem canary_witness_sintLe_hasEdge :
    checkNatSpecWitness [5, 7] [⟨.var 0, .cst 5⟩, ⟨.add (.var 0) (.cst 2), .var 1⟩] = true ∧
    checkNatSpecWitness [6, 7] [⟨.var 0, .cst 5⟩, ⟨.add (.var 0) (.cst 2), .var 1⟩] = false ∧
    checkNatSpecWitness [5, 6] [⟨.var 0, .cst 5⟩, ⟨.add (.var 0) (.cst 2), .var 1⟩] = false ∧
    checkIntSpecWitness [Int.negOfNat 3] [⟨.cst ⟨true, 3⟩, .var 0⟩] = true ∧
    checkIntSpecWitness [Int.negOfNat 4] [⟨.cst ⟨true, 3⟩, .var 0⟩] = false ∧
    checkIntSpecWitness [Int.ofNat 1] [⟨.sub (.var 0) (.neg (.var 0)), .cst ⟨false, 2⟩⟩] = true ∧
    checkIntSpecWitness [Int.ofNat 2] [⟨.sub (.var 0) (.neg (.var 0)), .cst ⟨false, 3⟩⟩] = false ∧
    sintLe ⟨true, 0⟩ ⟨false, 0⟩ = true ∧
    sintLe ⟨false, 0⟩ ⟨true, 0⟩ = true ∧
    sintLe ⟨false, 1⟩ ⟨true, 0⟩ = false ∧
    sintLe ⟨true, 5⟩ ⟨true, 3⟩ = true ∧
    sintLe ⟨true, 3⟩ ⟨true, 5⟩ = false ∧
    hasEdgeInList 1 2 [(0, 1, []), (1, 2, [])] = true ∧
    hasEdgeInList 2 1 [(0, 1, []), (1, 2, [])] = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Canary: the syntactic path-chaining equality checkers accept identical
specs and reject constant, variable, length, and constructor mismatches. The
sign-magnitude zeros `⟨true, 0⟩` / `⟨false, 0⟩` are deliberately treated as
distinct (conservative: may reject a valid chain, never accepts an invalid
one). -/
theorem canary_syntactic_beq :
    natLinSpecBeq [⟨.add (.var 0) (.mulC 2 (.var 1)), .cst 5⟩]
      [⟨.add (.var 0) (.mulC 2 (.var 1)), .cst 5⟩] = true ∧
    natLinSpecBeq [⟨.var 0, .cst 5⟩] [⟨.var 0, .cst 6⟩] = false ∧
    natLinSpecBeq [⟨.var 0, .cst 5⟩] [⟨.var 1, .cst 5⟩] = false ∧
    natLinSpecBeq [⟨.var 0, .cst 5⟩] [⟨.var 0, .cst 5⟩, ⟨.var 0, .cst 5⟩] = false ∧
    natLinSpecBeq [⟨.mulC 1 (.var 0), .cst 5⟩] [⟨.var 0, .cst 5⟩] = false ∧
    intLinSpecBeq [⟨.sub (.var 0) (.neg (.var 1)), .cst ⟨true, 2⟩⟩]
      [⟨.sub (.var 0) (.neg (.var 1)), .cst ⟨true, 2⟩⟩] = true ∧
    intLinSpecBeq [⟨.var 0, .cst ⟨true, 2⟩⟩] [⟨.var 0, .cst ⟨false, 2⟩⟩] = false ∧
    intLinSpecBeq [⟨.var 0, .cst ⟨true, 0⟩⟩] [⟨.var 0, .cst ⟨false, 0⟩⟩] = false ∧
    intLinSpecBeq [⟨.sub (.var 0) (.var 1), .cst SInt.zero⟩]
      [⟨.add (.var 0) (.neg (.var 1)), .cst SInt.zero⟩] = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Fail-Closed Negative `rfl` Controls (`= false`) -/

/-- Negative canary: truncated or overlong `certs` lists are rejected fail-closed
by `checkNatEntailmentEdge` and `checkIntEntailmentEdge`. -/
theorem neg_canary_entailment_edge_length_mismatch :
    checkNatEntailmentEdge
      [⟨.var 0, .cst 5⟩]
      [⟨.var 0, .cst 5⟩, ⟨.var 0, .cst 10⟩]
      [[.hyp 0, .hyp 2, .comb 0 1 1 1]] = false ∧
    checkNatEntailmentEdge
      [⟨.var 0, .cst 5⟩]
      [⟨.var 0, .cst 5⟩]
      [[.hyp 0, .hyp 2, .comb 0 1 1 1], [.hyp 0, .hyp 2, .comb 0 1 1 1]] = false ∧
    checkIntEntailmentEdge
      [⟨.var 0, .cst ⟨false, 5⟩⟩]
      [⟨.var 0, .cst ⟨false, 5⟩⟩, ⟨.var 0, .cst ⟨false, 10⟩⟩]
      [[.hyp 0, .hyp 1, .comb 0 1 1 1]] = false :=
  ⟨rfl, rfl, rfl⟩

/-- Negative canary: vacuous/unsatisfiable `pre` (`1 ≤ 0`) fails
`checkNatEntailmentAdequacy` and `checkIntEntailmentAdequacy` even when forward
entailment holds. -/
theorem neg_canary_vacuous_pre_rejected :
    checkNatEntailmentAdequacy
      [⟨.cst 1, .cst 0⟩]
      [⟨.var 0, .cst 0⟩]
      [[.hyp 0]]
      [0]
      .sufficientOnly = false ∧
    checkIntEntailmentAdequacy
      [⟨.cst SInt.one, .cst SInt.zero⟩]
      [⟨.var 0, .cst SInt.zero⟩]
      [[.hyp 0]]
      [Int.ofNat 0]
      .sufficientOnly = false :=
  ⟨rfl, rfl⟩

/-- Negative canary: invalid `satWitness` (falsifies `pre`), invalid
`strictWitness` (satisfies `pre` or falsifies `obligation`), and false `.equiv`
claims all return `false`. -/
theorem neg_canary_invalid_witnesses_and_equiv_rejected :
    -- satWitness [6] violates pre (x ≤ 5)
    checkNatEntailmentAdequacy
      [⟨.var 0, .cst 5⟩] [⟨.var 0, .cst 10⟩]
      [[.hyp 0, .hyp 2, .comb 0 1 1 1]] [6] .sufficientOnly = false ∧
    -- strictWitness [4] satisfies pre (does not show strictness)
    checkNatEntailmentAdequacy
      [⟨.var 0, .cst 5⟩] [⟨.var 0, .cst 10⟩]
      [[.hyp 0, .hyp 2, .comb 0 1 1 1]] [0] (.strict [4]) = false ∧
    -- strictWitness [11] falsifies obligation (x ≤ 10)
    checkNatEntailmentAdequacy
      [⟨.var 0, .cst 5⟩] [⟨.var 0, .cst 10⟩]
      [[.hyp 0, .hyp 2, .comb 0 1 1 1]] [0] (.strict [11]) = false ∧
    -- false equiv (x ≤ 10 does not imply x ≤ 5)
    checkNatEntailmentAdequacy
      [⟨.var 0, .cst 5⟩] [⟨.var 0, .cst 10⟩]
      [[.hyp 0, .hyp 2, .comb 0 1 1 1]] [0]
      (.equiv [[.hyp 0, .hyp 2, .comb 0 1 1 1]]) = false ∧
    -- Int strictWitness [0] satisfies pre (-3 ≤ x ≤ 2), rejected
    checkIntEntailmentAdequacy
      [⟨.cst ⟨true, 3⟩, .var 0⟩, ⟨.var 0, .cst ⟨false, 2⟩⟩]
      [⟨.cst ⟨true, 5⟩, .var 0⟩]
      [[.hyp 0, .hyp 2, .comb 0 1 1 1]] [Int.ofNat 0]
      (.strict [Int.ofNat 0]) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Canary: multi-hop node-index reachability (`0 → 1 → 2`) over a verified
`NatEntailmentGraph` via `checkNatGraphIndexPath_sound`. -/
theorem canary_nat_graph_index_path_ok :
    let g : NatEntailmentGraph :=
      { nodes := [[⟨.var 0, .cst 3⟩], [⟨.var 0, .cst 5⟩], [⟨.var 0, .cst 10⟩]]
        edges :=
          [ (0, 1, [[.hyp 0, .hyp 2, .comb 0 1 1 1]])
          , (1, 2, [[.hyp 0, .hyp 2, .comb 0 1 1 1]]) ] }
    ∃ src dst,
      listLookup? g.nodes 0 = some src ∧
      listLookup? g.nodes 2 = some dst ∧
      (∀ env : List Nat, src.holds env → dst.holds env) :=
  checkNatGraphIndexPath_sound (g :=
    { nodes := [[⟨.var 0, .cst 3⟩], [⟨.var 0, .cst 5⟩], [⟨.var 0, .cst 10⟩]]
      edges :=
        [ (0, 1, [[.hyp 0, .hyp 2, .comb 0 1 1 1]])
        , (1, 2, [[.hyp 0, .hyp 2, .comb 0 1 1 1]]) ] })
    rfl [1, 2] 0 2 rfl

/-- Negative canary: disconnected path, out-of-bounds graph node, missing graph
hop, empty/satisfied falsifier queries, zero alignment, malformed interval,
mismatched cert shape, and unprovable certified subtraction range all fail
closed (`= false`). -/
theorem neg_canary_structural_fail_closed :
    -- Disconnected path: edge 0 ends at x ≤ 5, edge 1 starts at x ≤ 6
    checkNatEntailmentPath [⟨.var 0, .cst 3⟩] [⟨.var 0, .cst 10⟩]
      [ { src := [⟨.var 0, .cst 3⟩], dst := [⟨.var 0, .cst 5⟩],
          certs := [[.hyp 0, .hyp 2, .comb 0 1 1 1]] }
      , { src := [⟨.var 0, .cst 6⟩], dst := [⟨.var 0, .cst 10⟩],
          certs := [[.hyp 0, .hyp 2, .comb 0 1 1 1]] } ] = false ∧
    -- Out-of-bounds node index in graph
    checkNatEntailmentGraph
      { nodes := [[⟨.var 0, .cst 3⟩]]
        edges := [(0, 2, [[.hyp 0, .hyp 2, .comb 0 1 1 1]])] } = false ∧
    -- Missing direct hop (0 -> 2) and out-of-bounds node in graph index path
    checkGraphIndexPath
      ({ nodes := [[⟨.var 0, .cst 3⟩], [⟨.var 0, .cst 5⟩], [⟨.var 0, .cst 10⟩]]
         edges := [(0, 1, []), (1, 2, [])] } : NatEntailmentGraph) 0 2 [2] = false ∧
    checkGraphIndexPath
      ({ nodes := [[⟨.var 0, .cst 3⟩]]
         edges := [] } : NatEntailmentGraph) 5 5 [] = false ∧
    -- Empty and satisfied specs cannot be falsified
    checkNatSpecFalsifies [0] [] = false ∧
    checkNatSpecFalsifies [3] [⟨.var 0, .cst 5⟩] = false ∧
    checkIntSpecFalsifies [Int.ofNat 0] [] = false ∧
    checkIntSpecFalsifies [Int.negOfNat 1] [⟨.cst ⟨true, 3⟩, .var 0⟩] = false ∧
    -- alignBytes = 0 rejected
    checkFarkasMirGoal
      (.alignedStride [⟨.cst 0, .var 0⟩, ⟨.var 0, .cst 0⟩] 0 (.var 0) (.var 1))
      (.pair [.hyp 0, .hyp 3, .comb 0 1 1 1] [.hyp 1, .hyp 3, .comb 0 1 1 1]) = false ∧
    -- WrappedInterval lo > hi rejected
    checkFarkasMirGoal
      (.aipccIntervalRefine [⟨.cst 10, .var 0⟩, ⟨.var 0, .cst 5⟩] 256 10 5 (.var 0))
      (.pair [.hyp 0, .hyp 3, .comb 0 1 1 1] [.hyp 1, .hyp 3, .comb 0 1 1 1]) = false ∧
    -- WrappedInterval hi >= M rejected
    checkFarkasMirGoal
      (.aipccIntervalRefine [⟨.cst 0, .var 0⟩, ⟨.var 0, .cst 256⟩] 256 0 256 (.var 0))
      (.pair [.hyp 0, .hyp 3, .comb 0 1 1 1] [.hyp 1, .hyp 3, .comb 0 1 1 1]) = false ∧
    -- Mismatched goal/cert constructor rejected
    checkFarkasMirGoal
      (.sliceBounds [⟨.var 0, .cst 1⟩] (.var 0) (.cst 0) (.cst 1))
      (.edge []) = false ∧
    -- Certified subtraction with an unprovable operand range (`a ≤ 2^32`
    -- admits `a = 2^32`) rejected even though `b ≤ a` is certified
    checkFarkasMirGoal
      (.uintSubNoUnderflowCertified .u32
        [⟨.add (.var 1) (.cst 4), .var 0⟩, ⟨.var 0, .cst (modPow2 32)⟩] (.var 0) (.var 1))
      (.pair [.hyp 0, .hyp 4, .comb 0 1 1 1] [.hyp 1, .hyp 4, .comb 0 1 1 1]) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Canary: `farkas_discharges_aligned_base_plus_stride` and
`farkas_discharges_unalign_raw_ptr_safe` (both `UnsafeObligations` bridges). -/
theorem canary_aligned_base_plus_stride_and_unalign
    (delta q off inner alloc : Nat) (rp : RawPtrVal)
    (hBaseAligned : AlignedPtr rp 8)
    (hLo : 8 * q ≤ delta) (hHi : delta ≤ 8 * q)
    (hOff : rp.offset = off) (hBound : off + inner ≤ alloc) :
    AlignedPtr { rp with offset := rp.offset + delta } 8 ∧
    UnalignRawPtrSafe rp inner alloc :=
  ⟨farkas_discharges_aligned_base_plus_stride
     [⟨.mulC 8 (.var 1), .var 0⟩, ⟨.var 0, .mulC 8 (.var 1)⟩] 8
     (.var 0) (.var 1)
     [.hyp 0, .hyp 4, .comb 0 1 1 1] [.hyp 1, .hyp 4, .comb 0 1 1 1]
     rfl rfl [delta, q] rp hBaseAligned hLo hHi,
   farkas_discharges_unalign_raw_ptr_safe
     [⟨.add (.var 0) (.var 1), .var 2⟩] (.var 0) (.var 1) (.var 2)
     [.hyp 0, .hyp 4, .comb 0 1 1 1] rfl [off, inner, alloc] rp hOff hBound⟩

/-- Canary: right-constant multiplication `x * 8 < 2^64` plus automatic
in-range derivation `UintScalarInRange .u64 ⟨x, uintBytes .u64⟩`. -/
theorem canary_uint_mul_const_right_and_rhs_inRange
    (x : Nat) (locals : List LocalSlot) (mem : Memory) (hx : x ≤ 1024) :
    UintScalarInRange .u64 ⟨8, uintBytes .u64⟩ ∧
    UintScalarInRange .u64 ⟨x, uintBytes .u64⟩ ∧
    evalScalarBinOp .mulUnchecked ⟨x, uintBytes .u64⟩ ⟨8, uintBytes .u64⟩ locals mem false =
      .ok (.scalar ⟨x * 8, uintBytes .u64⟩) locals mem ∧
    evalScalarBinOp .mulWithOverflow ⟨x, uintBytes .u64⟩ ⟨8, uintBytes .u64⟩ locals mem false =
      .ok (.aggregate 0 [.scalar ⟨x * 8, uintBytes .u64⟩, .scalar ⟨0, 1⟩]) locals mem := by
  have h := farkas_discharges_uint_mul_const_right_no_overflow .u64
    [⟨.var 0, .cst 1024⟩] (.var 0) 8
    [.hyp 0, .hyp 2, .comb 0 8 1 1] rfl rfl [x] locals mem hx
  have hProdComm : 8 * x < modPow2 (uintWidth .u64) := by
    rw [Nat.mul_comm]
    exact h.2.1
  have hXInRange : UintScalarInRange .u64 ⟨x, uintBytes .u64⟩ :=
    uintScalarInRange_rhs_of_mul_const_pos (Nat.zero_lt_succ 7) hProdComm
  exact ⟨h.1, hXInRange, h.2.2.2.1, h.2.2.2.2⟩

/-- Canary: `checkIntCutGoal_lt_sound`, `checkIntCutGoal_eq_sound`, and
`checkIntGraphIndexPath_sound` (multi-hop `0 → 1 → 2` over `IntEntailmentGraph`). -/
theorem canary_int_cut_lt_eq_and_graph_index_path (x : Int)
    (hLo : Int.negOfNat 3 ≤ x) (hHi : x ≤ Int.negOfNat 3) :
    x < Int.ofNat 0 ∧ x = Int.negOfNat 3 ∧
    (let g : IntEntailmentGraph :=
      { nodes := [[⟨.cst ⟨true, 3⟩, .var 0⟩], [⟨.cst ⟨true, 5⟩, .var 0⟩],
                  [⟨.cst ⟨true, 10⟩, .var 0⟩]]
        edges :=
          [ (0, 1, [[.hyp 0, .hyp 1, .comb 0 1 1 1]])
          , (1, 2, [[.hyp 0, .hyp 1, .comb 0 1 1 1]]) ] }
     ∃ src dst,
       listLookup? g.nodes 0 = some src ∧
       listLookup? g.nodes 2 = some dst ∧
       (∀ env : List Int, src.holds env → dst.holds env)) :=
  ⟨checkIntCutGoal_lt_sound
     [⟨.var 0, .cst ⟨true, 3⟩⟩] (.var 0) (.cst SInt.zero)
     [.hyp 0, .hyp 1, .comb 0 1 1 1] rfl [x] hHi,
   checkIntCutGoal_eq_sound
     [⟨.cst ⟨true, 3⟩, .var 0⟩, ⟨.var 0, .cst ⟨true, 3⟩⟩]
     (.var 0) (.cst ⟨true, 3⟩)
     [.hyp 1, .hyp 2, .comb 0 1 1 1] [.hyp 0, .hyp 2, .comb 0 1 1 1]
     rfl rfl [x] hLo hHi,
   checkIntGraphIndexPath_sound (g :=
     { nodes := [[⟨.cst ⟨true, 3⟩, .var 0⟩], [⟨.cst ⟨true, 5⟩, .var 0⟩],
                 [⟨.cst ⟨true, 10⟩, .var 0⟩]]
       edges :=
         [ (0, 1, [[.hyp 0, .hyp 1, .comb 0 1 1 1]])
         , (1, 2, [[.hyp 0, .hyp 1, .comb 0 1 1 1]]) ] })
     rfl [1, 2] 0 2 rfl⟩

/-- End-to-end MIR-to-AiPcc-to-Farkas composition canary: extracts interval
bounds from `MirAbsSlot.uint` and `MirAbsSlot.uintCopy`, refines the copy slot
via `farkas_refines_mirAbsSlot_uintCopy`, and discharges `u64` `.addUnchecked`
/ `.addWithOverflow` overflow-freedom for `sa.bits + sb.bits`. -/
theorem canary_e2e_mirAbsSlot_to_uint_add_no_overflow
    (tyA tyB : Ty) (locals : List LocalSlot) (mem : Memory) (src : Nat)
    (sa sb : ScalarInt)
    (hA : (MirAbsSlot.uint .u64 ⟨.init, Tnum.top 64, .iv 0 1000, .top⟩).denote
      tyA locals (.init (.scalar sa)))
    (hB : (MirAbsSlot.uintCopy .u64 ⟨.init, Tnum.top 64, .iv 10 2000, .top⟩ src).denote
      tyB locals (.init (.scalar sb)))
    (hTight : sb.bits ≤ 500) :
    (MirAbsSlot.uintCopy .u64 ⟨.init, Tnum.top 64, .iv 10 500, .top⟩ src).denote
      tyB locals (.init (.scalar sb)) ∧
    evalScalarBinOp .addUnchecked
      ⟨sa.bits, uintBytes .u64⟩ ⟨sb.bits, uintBytes .u64⟩ locals mem false =
      .ok (.scalar ⟨sa.bits + sb.bits, uintBytes .u64⟩) locals mem := by
  have hAb := mirAbsSlot_uint_iv_bounds rfl hA
  have hBb := mirAbsSlot_uintCopy_iv_bounds rfl hB
  have hRef := farkas_refines_mirAbsSlot_uintCopy .u64
    [⟨.cst 10, .var 0⟩, ⟨.var 0, .cst 500⟩] 10 500 (.var 0)
    [.hyp 0, .hyp 3, .comb 0 1 1 1] [.hyp 1, .hyp 3, .comb 0 1 1 1]
    rfl rfl rfl rfl [sb.bits] tyB locals ⟨.init, Tnum.top 64, .iv 10 2000, .top⟩ src sb hB rfl
    hBb.1 hTight
  have hAdd := farkas_discharges_u64_add_no_overflow
    [⟨.var 0, .cst 1000⟩, ⟨.var 1, .cst 500⟩] (.var 0) (.var 1)
    [.hyp 0, .hyp 1, .comb 0 1 1 1, .hyp 4, .comb 2 1 3 1]
    rfl [sa.bits, sb.bits] locals mem hAb.2.1 hTight
  exact ⟨hRef.1, hAdd.2.2.1⟩

end Anneal.FarkasMirCert
