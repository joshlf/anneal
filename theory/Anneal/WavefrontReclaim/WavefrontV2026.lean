-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted.Sequence
import Trusted.Rustc.V2026_06_01.Layout
import Trusted.Rustc.V2026_06_01.MirAst.Types
import Trusted.Rustc.V2026_06_01.MirAst.Body
import Trusted.Rustc.V2026_06_01.MirSemantics.State
import Trusted.Rustc.V2026_06_01.MirSemantics.Bytes
import Trusted.Rustc.V2026_06_01.MirSemantics.Places
import Trusted.Rustc.V2026_06_01.MirSemantics.Machine
import Anneal.CnfOrd.Ord
import Anneal.Firewall
import Anneal.WavefrontReclaim.SpatialPcm
import Anneal.MirLoops

/-!
# `< ω^ω` Ordinal-Bounded Wavefront Drain, Loan Reclamation, & `V2026_06_01` Bridge (`WavefrontV2026`)

Converges `google/zerocopy#4184` (`Anneal.WavefrontReclaim.Wavefront` & `Canaries`) onto
`unstable`'s `Anneal.WavefrontReclaim.SpatialPcm`, `Anneal.CnfOrd.Ord`, `Anneal.Firewall`,
and unmodified `Trusted.Rustc.V2026_06_01.MirSemantics` (`Memory`, `MachineState`, `stepMirFn`,
`encodeLittleEndianBytes`, `encodeValueToBytes`, `decodeValueFromBytes`) plus
`Anneal.PureMirExec.runCfgSteps`:

1. **Section 1 — Constructive `< ω^ω` Ordinal & Rank-Tower Worklist Preliminaries:**
   - Computable `SpawnPolicy`, `spawnAdmissible`, `PolicyAdmissible`,
     `isStrictlyDescendingTower`, `towerLookupNext`, and `towerLookupNext_admissible` (`[]`).
2. **Section 2 — `Firewall`-Shielded `V2026_06_01` `Memory` Sub-Lens & Loan Synchronization:**
   - `V2026SubLens`, `v2026LensDisjoint`, `v2026SubLensGet`, `v2026SubLensPut` directly over
     unmodified `Memory.globals` (`lookupGlobalAlloc` + `globalAllocSliceToAbstractBytes`).
   - Exact byte-encoding bridges `wfEncodeU32LeAbsBytes_eq_encodeLittleEndianBytes` and
     `wfEncodeU32LeAbsBytes_eq_encodeValueToBytes` / `decodeValueFromBytes`.
   - `WfLoanEntryV2026`, `Firewall`-shielded `LoansSyncedWithMemV2026` (blocking WHNF traversal
     into large `Memory` terms), and `QueueMatchesLoansV2026`.
3. **Section 3 — Fail-Closed Hybrid Command Semantics (`evalHybridCmdV2026`) & `VSepWpOrdRelV2026`:**
   - Pure-lifted fastpath (`vsepWpOrdRelV2026_pure_fastpath`), spatial cell update
     (`vsepWpOrdRelV2026_updateSpatialCell`), exclusive loan checkout
     (`vsepWpOrdRelV2026_checkoutLoan`), amortized `< ω^ω` debt burst submission
     (`vsepWpOrdRelV2026_submitTaskBurst_amortized_growth`), strict `< ω^ω` wavefront step
     (`vsepWpOrdRelV2026_wavefrontStep_strict_descent`), and general framing (`vsepWpOrdRelV2026_frame`).
4. **Section 4 — Arbitrary-Depth `< ω^ω` Drain Termination & Universal `.activeMut` Reclamation:**
   - `multiRank_wavefront_terminates_arbitrary_depth`, `universal_post_drain_activeMut_reclaim`,
     `vsepWpOrdRelV2026_wavefrontDrain`, and `vsepWpOrdRelV2026_fiveStage_chained_lifecycle`.
5. **Section 5 — `Firewall` / `IndexedCut`-Shielded `stepMirFn` & `runCfgSteps` Operational Bridge:**
   - Links real `V2026_06_01` `CapturedMir` loop/reclaim execution steps (`stepMirFn` and
     `runCfgSteps`) to strict `< ω^ω` ordinal descent, universal post-drain `.activeMut`
     reclamation, spatial `VProp` frame preservation, and `Firewall`-shielded `Memory` framing.
6. **Section 6 — Concrete Positive Multi-Rank / 5-Stage / `CapturedMir` Witnesses & Fail-Closed Negatives.**

Pass-1 hygiene: non-`module`, zero direct `Std.Do`/`MiniRustSpec`/`Miri`/`LeanMiriSpec`/`Lean`
imports, zero `Std.Do` constants in closure, zero `omega`/`bv_decide`/`by_cases`/`grind`/
`native_decide`/`._unsafe_rec`/`sorry`; axioms strictly `⊆ {propext}`.
-/

namespace Anneal.WavefrontReclaim.WavefrontV2026

set_option autoImplicit false

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.CnfOrd
open Anneal.Firewall
open Anneal.WavefrontReclaim
open Anneal.PureMirExec

/-! ## 1. Internal Arithmetic, Rank-Tower `SpawnPolicy`, and `CnfOrd` Helpers -/

private theorem boolFalseNeTrue (h : false = true) : False :=
  Bool.noConfusion h

private theorem boolTrueNeFalse (h : true = false) : False :=
  Bool.noConfusion h

private theorem bandIntro {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := by
  rw [ha, hb]; rfl

private theorem bandLeft {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact False.elim (boolFalseNeTrue h)
  | true => rfl

private theorem bandRight {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => exact False.elim (boolFalseNeTrue h)
  | true => exact h

private theorem borFalseElim {a b : Bool} (h : (a || b) = false) :
    a = false ∧ b = false := by
  cases a with
  | false => exact ⟨rfl, h⟩
  | true => exact False.elim (boolTrueNeFalse h)

private theorem trueOfBnotTrue {b : Bool} (h : (!b) = true) : b = false := by
  cases b with
  | false => rfl
  | true => exact False.elim (boolFalseNeTrue h)

private theorem natBeq_refl (a : Nat) : Nat.beq a a = true := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natBeq_symm (a b : Nat) : Nat.beq a b = Nat.beq b a := by
  revert b
  induction a with
  | zero => intro b; cases b <;> rfl
  | succ _ ih => intro b; cases b with | zero => rfl | succ b' => exact ih b'

private theorem natEq_of_beq (a b : Nat) (h : Nat.beq a b = true) : a = b := by
  revert b
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => rfl
    | succ _ => exact False.elim (boolFalseNeTrue h)
  | succ _ ih =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ b' => exact congrArg Nat.succ (ih b' h)

private theorem natBle_refl (a : Nat) : Nat.ble a a = true := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natBle_zero_left (a : Nat) : Nat.ble 0 a = true := by
  cases a <;> rfl

private theorem natBle_succ_right (a b : Nat) (h : Nat.ble a b = true) :
    Nat.ble a (b + 1) = true := by
  revert b h
  induction a with
  | zero => intro _ _; rfl
  | succ _ ih =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ b' => exact ih b' h

private theorem natBle_trans (a b c : Nat)
    (h1 : Nat.ble a b = true) (h2 : Nat.ble b c = true) :
    Nat.ble a c = true := by
  revert b c
  induction a with
  | zero => intro _ c _ _; exact natBle_zero_left c
  | succ _ ih =>
    intro b c h1 h2
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h1)
    | succ b' =>
      cases c with
      | zero => exact False.elim (boolFalseNeTrue h2)
      | succ c' => exact ih b' c' h1 h2

private theorem natAdd_zero_left (a : Nat) : 0 + a = a := by
  induction a with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

private theorem natAdd_succ_left (a b : Nat) : (a + 1) + b = (a + b) + 1 := by
  induction b with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

private theorem natAdd_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => exact natAdd_zero_left b
  | succ a' ih =>
    exact Eq.trans (natAdd_succ_left a' b) (congrArg Nat.succ ih)

private theorem natAdd_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

private theorem natBle_add_mono_right (a b c : Nat) (h : Nat.ble a b = true) :
    Nat.ble (a + c) (b + c) = true := by
  induction c with
  | zero => exact h
  | succ _ ih => exact ih

private theorem natBle_add_mono_left (c a b : Nat) (h : Nat.ble a b = true) :
    Nat.ble (c + a) (c + b) = true := by
  rw [natAdd_comm c a, natAdd_comm c b]
  exact natBle_add_mono_right a b c h

private theorem natLtSuccSelf (a : Nat) : natLt a (a + 1) = true :=
  natBle_refl (a + 1)

private theorem natLtTrans (a b c : Nat)
    (h1 : natLt a b = true) (h2 : natLt b c = true) :
    natLt a c = true :=
  natBle_trans (a + 1) b c h1
    (natBle_trans b (b + 1) c (natBle_succ_right b b (natBle_refl b)) h2)

private theorem natLtOfLtOfBle (a b c : Nat)
    (h1 : natLt a b = true) (h2 : Nat.ble b c = true) :
    natLt a c = true :=
  natBle_trans (a + 1) b c h1 h2

private theorem natLt_add_left_of_lt (a b c : Nat) (h : natLt a b = true) :
    natLt (a + c) (b + c) = true := by
  dsimp only [natLt] at h
  dsimp only [natLt]
  rw [← natAdd_succ_left a c]
  exact natBle_add_mono_right (a + 1) b c h

private theorem natBeqFalseOfLt {a b : Nat} (h : natLt a b = true) :
    Nat.beq a b = false := by
  revert b h
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ _ => rfl
  | succ _ ih =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ _ => exact ih h

private theorem natBleOfLtFalse (a b : Nat) (h : natLt a b = false) :
    Nat.ble b a = true := by
  revert b h
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => rfl
    | succ _ => exact False.elim (boolTrueNeFalse h)
  | succ _ ih =>
    intro b h
    cases b with
    | zero => rfl
    | succ b' => exact ih b' h

private theorem natBleAntisymm (a b : Nat)
    (h1 : Nat.ble a b = true) (h2 : Nat.ble b a = true) : a = b := by
  revert b
  induction a with
  | zero =>
    intro b _ h2
    cases b with
    | zero => rfl
    | succ _ => exact False.elim (boolFalseNeTrue h2)
  | succ _ ih =>
    intro b h1 h2
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h1)
    | succ b' => exact congrArg Nat.succ (ih b' h1 h2)

private theorem natCmpLtToLt {a b : Nat} (h : natCmp a b = .lt) :
    natLt a b = true := by
  dsimp only [natCmp] at h
  cases hLt : natLt a b with
  | true => rfl
  | false =>
    rw [hLt] at h
    cases hGt : natLt b a with
    | true => rw [hGt] at h; cases h
    | false => rw [hGt] at h; cases h

private theorem natCmpEqEq {a b : Nat} (h : natCmp a b = .eq) : a = b := by
  dsimp only [natCmp] at h
  cases hLt : natLt a b with
  | true => rw [hLt] at h; cases h
  | false =>
    rw [hLt] at h
    cases hGt : natLt b a with
    | true => rw [hGt] at h; cases h
    | false =>
      exact natBleAntisymm a b (natBleOfLtFalse b a hGt) (natBleOfLtFalse a b hLt)

/-- Tail-preserving `List.foldr` helper (`0` `noncomputable`). -/
def listFoldAux {α β : Type} (nil : β) (cons : α → List α → β → β)
    (xs : List α) : List α × β :=
  List.foldr (fun x acc => (x :: acc.1, cons x acc.1 acc.2)) ([], nil) xs

private theorem listFoldAux_fst {α β : Type} (nil : β)
    (cons : α → List α → β → β) (xs : List α) :
    (listFoldAux nil cons xs).1 = xs := by
  induction xs with
  | nil => rfl
  | cons x _ ih => exact congrArg (List.cons x) ih

/-- Tail-aware right fold over `xs` (`0` `noncomputable`). -/
def listFold {α β : Type} (nil : β) (cons : α → List α → β → β)
    (xs : List α) : β :=
  (listFoldAux nil cons xs).2

private theorem listFold_cons {α β : Type} (nil : β)
    (cons : α → List α → β → β) (x : α) (tl : List α) :
    listFold nil cons (x :: tl) = cons x tl (listFold nil cons tl) := by
  dsimp only [listFold]
  change (cons x (listFoldAux nil cons tl).1 (listFoldAux nil cons tl).2) = _
  rw [listFoldAux_fst]

/-- Rank-indexed spawn policy returning `(fanout, childRank, childYields)`. -/
abbrev SpawnPolicy : Type := Nat → Nat × Nat × Nat

/-- Spawn admissibility check: any non-zero fanout (`k = _ + 1`) must strictly
drop rank (`childRank < parentRank`). -/
def spawnAdmissible (parentRank fanout childRank : Nat) : Bool :=
  match fanout with
  | 0 => true
  | _ + 1 => natLt childRank parentRank

/-- Global admissibility of a `SpawnPolicy` across all parent ranks. -/
def PolicyAdmissible (pol : SpawnPolicy) : Prop :=
  ∀ r : Nat, spawnAdmissible r (pol r).1 (pol r).2.1 = true

/-- Computable check that a finite rank list `ranks` is strictly descending. -/
def isStrictlyDescendingTower (ranks : List Nat) : Bool :=
  listFold true
    (fun r tl ih =>
      (match tl with
       | [] => true
       | nextR :: _ => natLt nextR r) && ih)
    ranks

/-- Builds a `SpawnPolicy` descending along `ranks` with `(fanout, childYields)`
at each non-terminal tier and `(0, 0, 0)` at the bottom / unlisted ranks. -/
def towerLookupNext (ranks : List Nat) (fanout childYields : Nat) (r : Nat) :
    Nat × Nat × Nat :=
  listFold (0, 0, 0)
    (fun x tl ih =>
      match Nat.beq x r with
      | true =>
        match tl with
        | [] => (0, 0, 0)
        | nextR :: _ => (fanout, nextR, childYields)
      | false => ih)
    ranks

/-- Every strictly descending rank tower induces an admissible `SpawnPolicy`
(`[]` zero axioms). -/
theorem towerLookupNext_admissible (ranks : List Nat) (fanout childYields : Nat)
    (hDesc : isStrictlyDescendingTower ranks = true) :
    PolicyAdmissible (towerLookupNext ranks fanout childYields) := by
  intro r
  induction ranks with
  | nil => rfl
  | cons x tl ih =>
    dsimp only [isStrictlyDescendingTower] at hDesc
    rw [listFold_cons] at hDesc
    have hStep := bandLeft hDesc
    have hTlDesc := bandRight hDesc
    dsimp only [towerLookupNext]
    rw [listFold_cons]
    cases hEq : Nat.beq x r with
    | false => exact ih hTlDesc
    | true =>
      have hSame := natEq_of_beq x r hEq
      cases tl with
      | nil => rfl
      | cons nextR rest =>
        dsimp only at hStep ⊢
        cases fanout with
        | zero => rfl
        | succ _ =>
          dsimp only [spawnAdmissible]
          rw [← hSame]
          exact hStep

private theorem cnfBle_of_lt (xs ys : CnfOrd) (h : cnfLt xs ys = true) :
    cnfBle xs ys = true := by
  dsimp only [cnfLt] at h
  dsimp only [cnfBle]
  cases hc : cnfCmp xs ys with
  | lt => rfl
  | eq => rfl
  | gt => rw [hc] at h; exact False.elim (boolFalseNeTrue h)

private theorem cnfLt_exists_coeff_drop (xs ys : CnfOrd)
    (hX : isCanonicalCnf xs = true) (hY : isCanonicalCnf ys = true)
    (hLt : cnfLt xs ys = true) :
    ∃ q0 : Nat,
      natLt (cnfCoeffAt q0 xs) (cnfCoeffAt q0 ys) = true ∧
      (∀ (q : Nat), natLt q0 q = true → cnfCoeffAt q xs = cnfCoeffAt q ys) := by
  revert ys hY hLt
  induction xs with
  | nil =>
    intro ys hY hLt
    cases ys with
    | nil => exact False.elim (boolFalseNeTrue hLt)
    | cons b ytl =>
      rw [isCanonicalCnf_cons] at hY
      have hbPos := bandLeft (bandLeft hY)
      have hbBel := bandRight (bandLeft hY)
      refine ⟨b.1, ?_, ?_⟩
      · rw [cnfCoeffAt_cons_head b ytl hbBel]
        exact hbPos
      · intro q hGt
        have hLe : Nat.ble b.1 q = true :=
          natBle_trans b.1 (b.1 + 1) q (natBle_succ_right _ _ (natBle_refl _)) hGt
        rw [cnfCoeffAt_zero_of_allBelow q (b :: ytl) (bandIntro hGt
          (cnfAllBelow_mono b.1 q ytl hLe hbBel))]
        rfl
  | cons a xtl ih =>
    intro ys hY hLt
    rw [isCanonicalCnf_cons] at hX
    have haBel := bandRight (bandLeft hX)
    have hXtl := bandRight hX
    cases ys with
    | nil => exact False.elim (boolFalseNeTrue hLt)
    | cons b ytl =>
      rw [isCanonicalCnf_cons] at hY
      have hbPos := bandLeft (bandLeft hY)
      have hbBel := bandRight (bandLeft hY)
      have hYtl := bandRight hY
      dsimp only [cnfLt, cnfCmp, List.foldr, termCmp] at hLt
      cases hCmp1 : natCmp a.1 b.1 with
      | gt => rw [hCmp1] at hLt; exact False.elim (boolFalseNeTrue hLt)
      | lt =>
        have hab := natCmpLtToLt hCmp1
        have hLeAb : Nat.ble a.1 b.1 = true :=
          natBle_trans a.1 (a.1 + 1) b.1 (natBle_succ_right _ _ (natBle_refl _)) hab
        refine ⟨b.1, ?_, ?_⟩
        · rw [cnfCoeffAt_zero_of_allBelow b.1 (a :: xtl) (bandIntro hab
            (cnfAllBelow_mono a.1 b.1 xtl hLeAb haBel)),
            cnfCoeffAt_cons_head b ytl hbBel]
          exact hbPos
        · intro q hGt
          have hLeBq : Nat.ble b.1 q = true :=
            natBle_trans b.1 (b.1 + 1) q (natBle_succ_right _ _ (natBle_refl _)) hGt
          have hAq : natLt a.1 q = true := natLtTrans a.1 b.1 q hab hGt
          have hLeAq : Nat.ble a.1 q = true :=
            natBle_trans a.1 b.1 q hLeAb hLeBq
          rw [cnfCoeffAt_zero_of_allBelow q (a :: xtl) (bandIntro hAq
            (cnfAllBelow_mono a.1 q xtl hLeAq haBel)),
            cnfCoeffAt_zero_of_allBelow q (b :: ytl) (bandIntro hGt
              (cnfAllBelow_mono b.1 q ytl hLeBq hbBel))]
      | eq =>
        rw [hCmp1] at hLt
        dsimp only at hLt
        have hab1 := natCmpEqEq hCmp1
        cases hCmp2 : natCmp a.2 b.2 with
        | gt => rw [hCmp2] at hLt; exact False.elim (boolFalseNeTrue hLt)
        | lt =>
          refine ⟨a.1, ?_, ?_⟩
          · rw [cnfCoeffAt_cons_head a xtl haBel, hab1,
              cnfCoeffAt_cons_head b ytl hbBel]
            exact natCmpLtToLt hCmp2
          · intro q hGt
            have hLeAq : Nat.ble a.1 q = true :=
              natBle_trans a.1 (a.1 + 1) q (natBle_succ_right _ _ (natBle_refl _)) hGt
            have hBq : natLt b.1 q = true := by rw [← hab1]; exact hGt
            have hLeBq : Nat.ble b.1 q = true := by rw [← hab1]; exact hLeAq
            rw [cnfCoeffAt_zero_of_allBelow q (a :: xtl) (bandIntro hGt
              (cnfAllBelow_mono a.1 q xtl hLeAq haBel)),
              cnfCoeffAt_zero_of_allBelow q (b :: ytl) (bandIntro hBq
                (cnfAllBelow_mono b.1 q ytl hLeBq hbBel))]
        | eq =>
          rw [hCmp2] at hLt
          dsimp only at hLt
          have hab2 := natCmpEqEq hCmp2
          cases ih hXtl ytl hYtl (by dsimp only [cnfLt]; exact hLt) with
          | intro q0 hSub =>
            have hQ0LtA : natLt q0 a.1 = true := by
              cases hGe : natLt q0 a.1 with
              | true => rfl
              | false =>
                have hLeAq0 := natBleOfLtFalse q0 a.1 hGe
                have hLeBq0 : Nat.ble b.1 q0 = true := by
                  rw [← hab1]; exact hLeAq0
                have hZx := cnfCoeffAt_zero_of_allBelow q0 xtl
                  (cnfAllBelow_mono a.1 q0 xtl hLeAq0 haBel)
                have hZy := cnfCoeffAt_zero_of_allBelow q0 ytl
                  (cnfAllBelow_mono b.1 q0 ytl hLeBq0 hbBel)
                have hD := hSub.1
                rw [hZx, hZy] at hD
                exact False.elim (boolFalseNeTrue hD)
            have hNeA : Nat.beq a.1 q0 = false := by
              rw [natBeq_symm]
              exact natBeqFalseOfLt hQ0LtA
            refine ⟨q0, ?_, ?_⟩
            · change natLt
                (match Nat.beq a.1 q0 with
                 | true => a.2 + cnfCoeffAt q0 xtl
                 | false => cnfCoeffAt q0 xtl)
                (match Nat.beq b.1 q0 with
                 | true => b.2 + cnfCoeffAt q0 ytl
                 | false => cnfCoeffAt q0 ytl) = true
              rw [← hab1, hNeA]
              exact hSub.1
            · intro q hGt
              change
                (match Nat.beq a.1 q with
                 | true => a.2 + cnfCoeffAt q xtl
                 | false => cnfCoeffAt q xtl) =
                (match Nat.beq b.1 q with
                 | true => b.2 + cnfCoeffAt q ytl
                 | false => cnfCoeffAt q ytl)
              rw [← hab1, hab2, hSub.2 q hGt]

private theorem cnfLt_cnfNatAdd_left (a b c : CnfOrd)
    (hA : isCanonicalCnf a = true) (hB : isCanonicalCnf b = true)
    (hLt : cnfLt a b = true) :
    cnfLt (cnfNatAdd a c) (cnfNatAdd b c) = true := by
  cases cnfLt_exists_coeff_drop a b hA hB hLt with
  | intro q0 hQ0 =>
    apply cnfLt_of_coeff_drop _ _
      (isCanonicalCnf_cnfNatAdd a c) (isCanonicalCnf_cnfNatAdd b c) q0
    · rw [cnfCoeffAt_cnfNatAdd, cnfCoeffAt_cnfNatAdd]
      exact natLt_add_left_of_lt _ _ _ hQ0.1
    · intro q hGt
      rw [cnfCoeffAt_cnfNatAdd, cnfCoeffAt_cnfNatAdd, hQ0.2 q hGt]

private theorem cnfBle_cnfNatAdd_left (a b c : CnfOrd)
    (hA : isCanonicalCnf a = true) (hB : isCanonicalCnf b = true)
    (hLe : cnfBle a b = true) :
    cnfBle (cnfNatAdd a c) (cnfNatAdd b c) = true := by
  dsimp only [cnfBle] at hLe
  cases hc : cnfCmp a b with
  | gt => rw [hc] at hLe; exact False.elim (boolFalseNeTrue hLe)
  | eq =>
    rw [cnfCmp_eq_imp_eq a b hc]
    exact cnfBle_refl (cnfNatAdd b c)
  | lt =>
    exact cnfBle_of_lt _ _
      (cnfLt_cnfNatAdd_left a b c hA hB (by dsimp only [cnfLt]; rw [hc]))

private theorem cnfBle_cnfNatAdd_right (u a b : CnfOrd)
    (hA : isCanonicalCnf a = true) (hB : isCanonicalCnf b = true)
    (hLe : cnfBle a b = true) :
    cnfBle (cnfNatAdd u a) (cnfNatAdd u b) = true := by
  rw [cnfNatAdd_comm u a, cnfNatAdd_comm u b]
  exact cnfBle_cnfNatAdd_left a b u hA hB hLe

/-! ## 2. `Firewall`-Shielded `V2026_06_01` `Memory` Sub-Lens, Byte Codecs, & Loan Sync -/

/-- Modulus `2^32` (`4294967296`) for wrapping `u32` loan accumulation. -/
def u32Modulus : Nat := 4294967296

/-- Reduces `v` modulo `u32Modulus` (`2^32`). -/
def wrapU32 (v : Nat) : Nat := Nat.mod v u32Modulus

/-- `wrapU32 v < u32Modulus`. -/
theorem wrapU32_lt (v : Nat) : wrapU32 v < u32Modulus :=
  Nat.mod_lt v (Nat.le_of_ble_eq_true rfl)

/-- Idempotence of `wrapU32` (`[propext]`). -/
theorem wrapU32_idem (v : Nat) : wrapU32 (wrapU32 v) = wrapU32 v :=
  Nat.mod_eq_of_lt (wrapU32_lt v)

/-- Left modular-addition absorption `wrapU32 (wrapU32 a + b) = wrapU32 (a + b)`
(`[propext]`). -/
theorem wrapU32_add_left (a b : Nat) :
    wrapU32 (wrapU32 a + b) = wrapU32 (a + b) := by
  dsimp only [wrapU32]
  have hDivMod : u32Modulus * Nat.div a u32Modulus + Nat.mod a u32Modulus = a :=
    Nat.div_add_mod a u32Modulus
  have h1 :
      Nat.mod (u32Modulus * Nat.div a u32Modulus + (Nat.mod a u32Modulus + b))
        u32Modulus =
      Nat.mod (Nat.mod a u32Modulus + b) u32Modulus :=
    Nat.mul_add_mod_self_left u32Modulus (Nat.div a u32Modulus)
      (Nat.mod a u32Modulus + b)
  rw [← natAdd_assoc (u32Modulus * Nat.div a u32Modulus) (Nat.mod a u32Modulus) b,
    hDivMod] at h1
  exact h1.symm

/-- Canonical `V2026_06_01` `u32` MIR type (`RigidTy.uint .u32`). -/
def wfU32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }

/-- Computable raw `Option UInt8` little-endian byte encoder (`@Nat.rec`, `0` `._unsafe_rec`). -/
def wfEncodeRawLeBytesAux (bits n : Nat) : List (Option UInt8) :=
  (@Nat.rec (fun _ => Nat → List (Option UInt8))
    (fun _ => [])
    (fun _ rec b => some (UInt8.ofNat b) :: rec (Nat.div b 256))
    n) bits

/-- 4-byte little-endian raw `CapturedAllocation` slice for `wrapU32 v` (`0` `._unsafe_rec`). -/
def wfEncodeU32LeRawBytes (v : Nat) : List (Option UInt8) :=
  wfEncodeRawLeBytesAux (wrapU32 v) 4

/-- `wfEncodeU32LeRawBytes v` always has length `4` (`[]` zero axioms). -/
theorem wfEncodeU32LeRawBytes_length (v : Nat) :
    (wfEncodeU32LeRawBytes v).length = 4 := rfl

/-- 4-byte little-endian `AbstractByte` slice for `wrapU32 v` via unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.encodeLittleEndianBytes`. -/
def wfEncodeU32LeAbsBytes (v : Nat) : List AbstractByte :=
  encodeLittleEndianBytes (wrapU32 v) 4 none

/-- `wfEncodeU32LeAbsBytes v` always has length `4` (`[]` zero axioms). -/
theorem wfEncodeU32LeAbsBytes_length (v : Nat) :
    (wfEncodeU32LeAbsBytes v).length = 4 := rfl

/-- Exact bridge from `wfEncodeU32LeAbsBytes` to
`Trusted.Rustc.V2026_06_01.MirSemantics.encodeLittleEndianBytes` (`[]` zero axioms). -/
theorem wfEncodeU32LeAbsBytes_eq_encodeLittleEndianBytes (v : Nat) :
    wfEncodeU32LeAbsBytes v = encodeLittleEndianBytes (wrapU32 v) 4 none := rfl

/-- Exact bridge from `wfEncodeU32LeAbsBytes` to unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.encodeValueToBytes` (`[]` zero axioms). -/
theorem wfEncodeU32LeAbsBytes_eq_encodeValueToBytes
    (fuel : Nat) (layouts : LayoutTable) (v : Nat) :
    encodeValueToBytes (fuel + 1) layouts wfU32Ty (.scalar ⟨wrapU32 v, 4⟩) =
      some (wfEncodeU32LeAbsBytes v) := rfl

private theorem uint8_ofNat_toNat_mod256 (n : Nat) :
    (UInt8.ofNat n).toBitVec.toNat = n % 256 := rfl

private theorem pow256_pos : ∀ k : Nat, 0 < 256 ^ k
  | 0 => Nat.zero_lt_succ 0
  | k + 1 => by
    rw [Nat.pow_succ]
    exact Nat.mul_pos (pow256_pos k) (Nat.zero_lt_succ 255)

private theorem natModMul256 (b c : Nat) (hc : 0 < c) :
    b % 256 + 256 * ((b / 256) % c) = b % (256 * c) := by
  let q1 := b / 256
  let r1 := b % 256
  let q2 := q1 / c
  let r2 := q1 % c
  have h1 : 256 * q1 + r1 = b := Nat.div_add_mod b 256
  have h2 : c * q2 + r2 = q1 := Nat.div_add_mod q1 c
  have hDecomp : (256 * c) * q2 + (r1 + 256 * r2) = b := by
    rw [← h1, ← h2, Nat.left_distrib 256 (c * q2) r2, ← Nat.mul_assoc 256 c q2,
      Nat.add_assoc ((256 * c) * q2) (256 * r2) r1, Nat.add_comm (256 * r2) r1]
  have hModEq : b % (256 * c) = (r1 + 256 * r2) % (256 * c) := by
    rw [← hDecomp]
    exact Nat.mul_add_mod_self_left (256 * c) q2 (r1 + 256 * r2)
  have hr1 : r1 < 256 := Nat.mod_lt b (Nat.zero_lt_succ 255)
  have hr2 : r2 + 1 ≤ c := Nat.succ_le_of_lt (Nat.mod_lt q1 hc)
  have hBound : r1 + 256 * r2 < 256 * c := by
    have hLt1 : r1 + 256 * r2 < 256 + 256 * r2 := Nat.add_lt_add_right hr1 (256 * r2)
    have hEq2 : 256 + 256 * r2 = 256 * (r2 + 1) := by
      rw [Nat.left_distrib 256 r2 1, Nat.mul_one, Nat.add_comm]
    rw [hEq2] at hLt1
    exact Nat.lt_of_lt_of_le hLt1 (Nat.mul_le_mul_left 256 hr2)
  rw [hModEq, Nat.mod_eq_of_lt hBound]

private theorem decodeLittleEndianBytes_encodeLittleEndianBytes_none :
    ∀ (numBytes bits : Nat),
      decodeLittleEndianBytes (encodeLittleEndianBytes bits numBytes none) =
        some (bits % (256 ^ numBytes), none)
  | 0, bits => by
    unfold encodeLittleEndianBytes decodeLittleEndianBytes
    have h1 : 256 ^ 0 = 1 := rfl
    rw [h1, Nat.mod_one]
  | rem + 1, bits => by
    unfold encodeLittleEndianBytes decodeLittleEndianBytes
    have hDiv : Nat.div bits 256 = bits / 256 := rfl
    rw [hDiv, decodeLittleEndianBytes_encodeLittleEndianBytes_none rem (bits / 256)]
    dsimp only [mergeByteProvenance]
    change some ((UInt8.ofNat bits).toBitVec.toNat + 256 * ((bits / 256) % (256 ^ rem)), none) =
      some (bits % (256 ^ (rem + 1)), none)
    rw [uint8_ofNat_toNat_mod256]
    have hPow : 256 ^ (rem + 1) = 256 * 256 ^ rem := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hPow, natModMul256 bits (256 ^ rem) (pow256_pos rem)]

/-- Exact round-trip bridge through unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.decodeValueFromBytes` (`[propext]`):
decoding `wfEncodeU32LeAbsBytes v` at `wfU32Ty` recovers `.scalar ⟨wrapU32 v, 4⟩`. -/
theorem decodeValueFromBytes_wfEncodeU32LeAbsBytes
    (fuel : Nat) (layouts : LayoutTable) (v : Nat) :
    decodeValueFromBytes (fuel + 1) layouts wfU32Ty (wfEncodeU32LeAbsBytes v) =
      some (.scalar ⟨wrapU32 v, 4⟩) := by
  unfold decodeValueFromBytes wfU32Ty intCastTargetBytes
  dsimp only
  have hLen : length (wfEncodeU32LeAbsBytes v) = 4 := rfl
  rw [hLen]
  dsimp only [Nat.beq, decodeScalarBytes]
  rw [hLen]
  dsimp only [Nat.beq]
  unfold wfEncodeU32LeAbsBytes
  rw [decodeLittleEndianBytes_encodeLittleEndianBytes_none 4 (wrapU32 v)]
  have hPow4 : 256 ^ 4 = u32Modulus := rfl
  rw [hPow4]
  have hIdem : wrapU32 v % u32Modulus = wrapU32 v := wrapU32_idem v
  rw [hIdem]

/-- Sub-slice byte lens `(allocId, offset, size, alignBytes)` directly into an
unmodified `Trusted.Rustc.V2026_06_01.MirSemantics.Memory` global allocation. -/
structure V2026SubLens where
  allocId : AllocId
  offset : Nat
  size : Nat
  alignBytes : Nat
  deriving DecidableEq

/-- Computable $O(1)$ byte-interval disjointness on `V2026SubLens`. -/
def v2026LensDisjoint (L1 L2 : V2026SubLens) : Bool :=
  (!Nat.beq L1.allocId L2.allocId) ||
    Nat.ble (L1.offset + L1.size) L2.offset ||
    Nat.ble (L2.offset + L2.size) L1.offset

/-- Symmetry of `v2026LensDisjoint` (`[]` zero axioms). -/
theorem v2026LensDisjoint_symm (L1 L2 : V2026SubLens) :
    v2026LensDisjoint L1 L2 = v2026LensDisjoint L2 L1 := by
  dsimp only [v2026LensDisjoint]
  rw [natBeq_symm L1.allocId L2.allocId]
  cases (!Nat.beq L2.allocId L1.allocId) with
  | true => rfl
  | false =>
    cases Nat.ble (L1.offset + L1.size) L2.offset <;>
      cases Nat.ble (L2.offset + L2.size) L1.offset <;> rfl

private theorem natLe_of_ble_wf : ∀ {a b : Nat}, Nat.ble a b = true → a ≤ b
  | 0, b, _ => Nat.zero_le b
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => Nat.succ_le_succ (natLe_of_ble_wf h)

private theorem natBle_of_le_wf : ∀ {a b : Nat}, a ≤ b → Nat.ble a b = true
  | 0, _, _ => rfl
  | Nat.succ _, 0, h => nomatch h
  | Nat.succ a, Nat.succ b, h =>
    @natBle_of_le_wf a b (Nat.le_of_succ_le_succ h)

private theorem natSub_add_cancel_wf :
    ∀ {k n : Nat}, k ≤ n → k + (n - k) = n
  | 0, n, _ => by rw [Nat.zero_add, Nat.sub_zero]
  | _ + 1, 0, h => nomatch h
  | k + 1, n + 1, h => by
    rw [Nat.succ_sub_succ, Nat.succ_add]
    exact congrArg Nat.succ (natSub_add_cancel_wf (Nat.le_of_succ_le_succ h))

private theorem listLength_take_of_le_wf {α : Type} :
    ∀ (k : Nat) (bs : List α), k ≤ bs.length → (bs.take k).length = k
  | 0, _, _ => rfl
  | _ + 1, [], h => nomatch h
  | k + 1, _ :: bs, h =>
    congrArg Nat.succ (listLength_take_of_le_wf k bs (Nat.le_of_succ_le_succ h))

private theorem listLength_drop_wf {α : Type} :
    ∀ (k : Nat) (bs : List α), (bs.drop k).length = bs.length - k
  | 0, _ => rfl
  | k + 1, [] => by
    change 0 = 0 - (k + 1)
    rw [Nat.zero_sub]
  | k + 1, _ :: bs => by
    change (bs.drop k).length = (bs.length + 1) - (k + 1)
    rw [Nat.succ_sub_succ, listLength_drop_wf k bs]

private theorem listGet_append_left_wf {α : Type} :
    ∀ (xs ys : List α) (i : Nat), i < xs.length →
      Trusted.Sequence.get? (xs ++ ys) i = Trusted.Sequence.get? xs i
  | [], _, _, hLt => nomatch hLt
  | _ :: _, _, 0, _ => rfl
  | _ :: xs, ys, i + 1, hLt =>
    listGet_append_left_wf xs ys i (Nat.lt_of_succ_lt_succ hLt)

private theorem listGet_append_right_wf {α : Type} :
    ∀ (xs ys : List α) (i : Nat), xs.length ≤ i →
      Trusted.Sequence.get? (xs ++ ys) i = Trusted.Sequence.get? ys (i - xs.length)
  | [], ys, i, _ => by
    change Trusted.Sequence.get? ys i = Trusted.Sequence.get? ys (i - 0)
    rw [Nat.sub_zero]
  | _ :: _, _, 0, hLe => nomatch hLe
  | _ :: xs, ys, i + 1, hLe => by
    change Trusted.Sequence.get? (xs ++ ys) i =
      Trusted.Sequence.get? ys ((i + 1) - (xs.length + 1))
    rw [Nat.succ_sub_succ]
    exact listGet_append_right_wf xs ys i (Nat.le_of_succ_le_succ hLe)

private theorem listGet_take_lt_wf {α : Type} :
    ∀ (n : Nat) (xs : List α) (i : Nat), i < n →
      Trusted.Sequence.get? (xs.take n) i = Trusted.Sequence.get? xs i
  | 0, _, _, hLt => nomatch hLt
  | _ + 1, [], _, _ => rfl
  | _ + 1, _ :: _, 0, _ => rfl
  | n + 1, _ :: xs, i + 1, hLt =>
    listGet_take_lt_wf n xs i (Nat.lt_of_succ_lt_succ hLt)

private theorem listDrop_nil_wf {α : Type} :
    ∀ k : Nat, ([] : List α).drop k = []
  | 0 => rfl
  | _ + 1 => rfl

private theorem listGet_drop_wf {α : Type} :
    ∀ (n : Nat) (xs : List α) (i : Nat),
      Trusted.Sequence.get? (xs.drop n) i = Trusted.Sequence.get? xs (n + i)
  | 0, _, _ => by rw [Nat.zero_add]; rfl
  | n + 1, [], _ => by rw [listDrop_nil_wf, Nat.succ_add]; rfl
  | n + 1, _ :: xs, i => by
    rw [Nat.succ_add]
    exact listGet_drop_wf n xs i

private theorem listGet_splice_lt_wf {α : Type} (xs mid : List α)
    {wStart i : Nat} (hWLe : wStart ≤ xs.length) (hLt : i < wStart) :
    Trusted.Sequence.get?
      ((xs.take wStart ++ mid) ++ xs.drop (wStart + mid.length)) i =
      Trusted.Sequence.get? xs i := by
  have hTakeLen : (xs.take wStart).length = wStart :=
    listLength_take_of_le_wf wStart xs hWLe
  have hPreLen : (xs.take wStart ++ mid).length = wStart + mid.length := by
    rw [List.length_append, hTakeLen]
  have hLtPre : i < (xs.take wStart ++ mid).length := by
    rw [hPreLen]
    exact Nat.lt_of_lt_of_le hLt (Nat.le_add_right wStart mid.length)
  rw [listGet_append_left_wf (xs.take wStart ++ mid) _ i hLtPre,
    listGet_append_left_wf (xs.take wStart) mid i (by rw [hTakeLen]; exact hLt),
    listGet_take_lt_wf wStart xs i hLt]

private theorem listGet_splice_ge_wf {α : Type} (xs mid : List α)
    {wStart i : Nat} (hWLe : wStart ≤ xs.length) (hGe : wStart + mid.length ≤ i) :
    Trusted.Sequence.get?
      ((xs.take wStart ++ mid) ++ xs.drop (wStart + mid.length)) i =
      Trusted.Sequence.get? xs i := by
  have hPreLen : (xs.take wStart ++ mid).length = wStart + mid.length := by
    rw [List.length_append, listLength_take_of_le_wf wStart xs hWLe]
  rw [listGet_append_right_wf (xs.take wStart ++ mid) _ i (by rw [hPreLen]; exact hGe),
    hPreLen, listGet_drop_wf (wStart + mid.length) xs (i - (wStart + mid.length)),
    natSub_add_cancel_wf hGe]

private theorem listGet_splice_mid_wf {α : Type} (xs mid : List α)
    {wStart k : Nat} (hWLe : wStart ≤ xs.length) (hKLt : k < mid.length) :
    Trusted.Sequence.get?
      ((xs.take wStart ++ mid) ++ xs.drop (wStart + mid.length)) (wStart + k) =
      Trusted.Sequence.get? mid k := by
  have hTakeLen : (xs.take wStart).length = wStart :=
    listLength_take_of_le_wf wStart xs hWLe
  have hPreLen : (xs.take wStart ++ mid).length = wStart + mid.length := by
    rw [List.length_append, hTakeLen]
  have hLtPre : wStart + k < (xs.take wStart ++ mid).length := by
    rw [hPreLen]
    exact Nat.add_lt_add_left hKLt wStart
  have hGeTake : (xs.take wStart).length ≤ wStart + k := by
    rw [hTakeLen]
    exact Nat.le_add_right wStart k
  rw [listGet_append_left_wf (xs.take wStart ++ mid) _ (wStart + k) hLtPre,
    listGet_append_right_wf (xs.take wStart) mid (wStart + k) hGeTake,
    hTakeLen, Nat.add_sub_cancel_left]

/-- Mutable scalar sub-lens guard on a `CapturedAllocation`: mutable, relocation-free,
properly aligned (`1 ≤ alignBytes ≤ a.align.bytes`, `offset % alignBytes == 0`), and
in-bounds (`offset + size ≤ a.bytes.length`). -/
def v2026AllocLensOk (L : V2026SubLens) (a : CapturedAllocation) : Bool :=
  (match a.mutability with | .mut => true | .not => false) &&
  a.relocations.isEmpty &&
  Nat.ble 1 L.alignBytes &&
  Nat.ble L.alignBytes a.align.bytes &&
  Nat.beq (L.offset % L.alignBytes) 0 &&
  Nat.ble (L.offset + L.size) a.bytes.length

/-- Fail-closed `V2026_06_01` sub-lens read via unmodified `lookupGlobalAlloc` and
`globalAllocSliceToAbstractBytes`. -/
def v2026SubLensGet (L : V2026SubLens) (m : Memory) : Option (List AbstractByte) :=
  match lookupGlobalAlloc m.globals L.allocId with
  | none => none
  | some a =>
    match v2026AllocLensOk L a with
    | false => none
    | true => globalAllocSliceToAbstractBytes a L.offset L.size

/-- Replaces matching global `CapturedAllocation` entries for `a'.allocId` (`0` `._unsafe_rec`). -/
def replaceGlobalAllocWf (a' : CapturedAllocation)
    (gs : List CapturedAllocation) : List CapturedAllocation :=
  gs.map (fun a =>
    match Nat.beq a.allocId a'.allocId with
    | true => a'
    | false => a)

/-- Fail-closed `V2026_06_01` sub-lens write splicing `rawPatch` into `m.globals`. -/
def v2026SubLensPut (L : V2026SubLens) (m : Memory)
    (rawPatch : List (Option UInt8)) : Option Memory :=
  match lookupGlobalAlloc m.globals L.allocId with
  | none => none
  | some a =>
    match v2026AllocLensOk L a && Nat.beq rawPatch.length L.size with
    | false => none
    | true =>
      let bytes' :=
        (a.bytes.take L.offset ++ rawPatch) ++ a.bytes.drop (L.offset + rawPatch.length)
      some { m with globals := replaceGlobalAllocWf { a with bytes := bytes' } m.globals }

private theorem lookupGlobalAlloc_id_eq_wf :
    ∀ (globals : List CapturedAllocation) (aid : AllocId) (a : CapturedAllocation),
      lookupGlobalAlloc globals aid = some a → a.allocId = aid
  | [], _, _, h => nomatch h
  | hd :: tl, aid, a, h => by
    unfold lookupGlobalAlloc at h
    cases hb : Nat.beq hd.allocId aid with
    | true =>
      rw [hb] at h
      injection h with hEq
      rw [← hEq]
      exact natEq_of_beq hd.allocId aid hb
    | false =>
      rw [hb] at h
      exact lookupGlobalAlloc_id_eq_wf tl aid a h

private theorem lookupGlobalAlloc_replace_eq_wf (a' : CapturedAllocation) :
    ∀ {globals : List CapturedAllocation} {a : CapturedAllocation},
      lookupGlobalAlloc globals a'.allocId = some a →
      lookupGlobalAlloc (replaceGlobalAllocWf a' globals) a'.allocId = some a'
  | [], _, h => nomatch h
  | hd :: tl, a, h => by
    unfold lookupGlobalAlloc at h
    dsimp only [replaceGlobalAllocWf, List.map]
    cases hb : Nat.beq hd.allocId a'.allocId with
    | true =>
      dsimp only
      unfold lookupGlobalAlloc
      rw [natBeq_refl a'.allocId]
    | false =>
      rw [hb] at h
      dsimp only
      unfold lookupGlobalAlloc
      rw [hb]
      exact lookupGlobalAlloc_replace_eq_wf a' h

private theorem lookupGlobalAlloc_replace_ne_wf (a' : CapturedAllocation) (otherId : AllocId)
    (hNe : Nat.beq a'.allocId otherId = false) :
    ∀ (globals : List CapturedAllocation),
      lookupGlobalAlloc (replaceGlobalAllocWf a' globals) otherId =
        lookupGlobalAlloc globals otherId
  | [] => rfl
  | hd :: tl => by
    dsimp only [replaceGlobalAllocWf, List.map]
    cases hb : Nat.beq hd.allocId a'.allocId with
    | true =>
      have hEq : hd.allocId = a'.allocId := natEq_of_beq hd.allocId a'.allocId hb
      have hNeHd : Nat.beq hd.allocId otherId = false := by
        rw [hEq]; exact hNe
      dsimp only
      unfold lookupGlobalAlloc
      rw [hNe, hNeHd]
      exact lookupGlobalAlloc_replace_ne_wf a' otherId hNe tl
    | false =>
      dsimp only
      unfold lookupGlobalAlloc
      cases Nat.beq hd.allocId otherId with
      | true => rfl
      | false => exact lookupGlobalAlloc_replace_ne_wf a' otherId hNe tl

private theorem globalAllocBytesAux_congr_get_wf
    (bytes₁ bytes₂ : List (Option UInt8)) (relocs : List (Nat × ProvenancePtr)) :
    ∀ (start len : Nat),
      (∀ i : Nat, start ≤ i → i < start + len →
        Trusted.Sequence.get? bytes₁ i = Trusted.Sequence.get? bytes₂ i) →
      globalAllocBytesAux bytes₁ relocs start len =
        globalAllocBytesAux bytes₂ relocs start len
  | _, 0, _ => rfl
  | start, len + 1, hEq => by
    unfold globalAllocBytesAux
    have h0 : Trusted.Sequence.get? bytes₁ start = Trusted.Sequence.get? bytes₂ start :=
      hEq start (Nat.le_refl start) (Nat.lt_of_lt_of_le (Nat.lt_succ_self start)
        (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le len)) start))
    rw [h0]
    cases Trusted.Sequence.get? bytes₂ start with
    | none => rfl
    | some _ =>
      have hRest := globalAllocBytesAux_congr_get_wf bytes₁ bytes₂ relocs (start + 1) len
        (fun i hGe hLt => by
          have hSt : start + 1 + len = start + (len + 1) := by
            rw [Nat.add_assoc, Nat.add_comm 1 len]
          rw [hSt] at hLt
          exact hEq i (Nat.le_trans (Nat.le_succ start) hGe) hLt)
      rw [hRest]

private theorem globalAllocBytesAux_rawLe_at
    (bytes' : List (Option UInt8)) :
    ∀ (n off bits : Nat),
      (∀ i : Nat, i < n →
        Trusted.Sequence.get? bytes' (off + i) =
          Trusted.Sequence.get? (wfEncodeRawLeBytesAux bits n) i) →
      globalAllocBytesAux bytes' [] off n =
        some (encodeLittleEndianBytes bits n none)
  | 0, _, _, _ => rfl
  | rem + 1, off, bits, hAt => by
    unfold globalAllocBytesAux encodeLittleEndianBytes
    have h0 := hAt 0 (Nat.zero_lt_succ rem)
    rw [Nat.add_zero] at h0
    dsimp only [wfEncodeRawLeBytesAux] at h0
    change Trusted.Sequence.get? bytes' off = some (some (UInt8.ofNat bits)) at h0
    rw [h0]
    dsimp only [lookupRelocAllocId]
    have hSub := globalAllocBytesAux_rawLe_at bytes' rem (off + 1) (Nat.div bits 256)
      (fun i hi => by
        have h1 : (off + 1) + i = off + (i + 1) := by
          rw [Nat.add_assoc, Nat.add_comm 1 i]
        rw [h1]
        exact hAt (i + 1) (Nat.succ_lt_succ hi))
    rw [hSub]

/-- If `v2026SubLensGet L m` succeeds, any same-size `v2026SubLensPut` succeeds (`[]`). -/
theorem v2026SubLens_put_succeeds_of_get (L : V2026SubLens) (m : Memory)
    (oldBs : List AbstractByte) (rawPatch : List (Option UInt8))
    (hGet : v2026SubLensGet L m = some oldBs)
    (hLen : rawPatch.length = L.size) :
    ∃ mOut : Memory, v2026SubLensPut L m rawPatch = some mOut := by
  unfold v2026SubLensGet at hGet
  unfold v2026SubLensPut
  cases hFind : lookupGlobalAlloc m.globals L.allocId with
  | none => rw [hFind] at hGet; nomatch hGet
  | some a =>
    rw [hFind] at hGet
    dsimp only at hGet ⊢
    cases hOk : v2026AllocLensOk L a with
    | false => rw [hOk] at hGet; nomatch hGet
    | true =>
      have hLenBeq : Nat.beq rawPatch.length L.size = true := by
        rw [hLen]; exact natBeq_refl L.size
      rw [hLenBeq]
      exact ⟨_, rfl⟩

/-- Put-Get law for 4-byte `u32` little-endian writes (`[propext]`): writing
`wfEncodeU32LeRawBytes v` via `v2026SubLensPut` reads back `some (wfEncodeU32LeAbsBytes v)`
via `v2026SubLensGet`. -/
theorem v2026SubLens_put_get_u32 (L : V2026SubLens) (m mOut : Memory) (v : Nat)
    (hPut : v2026SubLensPut L m (wfEncodeU32LeRawBytes v) = some mOut) :
    v2026SubLensGet L mOut = some (wfEncodeU32LeAbsBytes v) := by
  unfold v2026SubLensPut at hPut
  cases hFind : lookupGlobalAlloc m.globals L.allocId with
  | none => rw [hFind] at hPut; nomatch hPut
  | some a =>
    rw [hFind] at hPut
    dsimp only at hPut
    cases hChk : (v2026AllocLensOk L a && Nat.beq (wfEncodeU32LeRawBytes v).length L.size) with
    | false => rw [hChk] at hPut; nomatch hPut
    | true =>
      rw [hChk] at hPut
      dsimp only at hPut
      injection hPut with hMeq
      have hOk : v2026AllocLensOk L a = true := bandLeft hChk
      have hSize4 : 4 = L.size := natEq_of_beq _ _ (bandRight hChk)
      have hBnd : L.offset + L.size ≤ a.bytes.length :=
        natLe_of_ble_wf (bandRight hOk)
      have hOffLe : L.offset ≤ a.bytes.length :=
        Nat.le_trans (Nat.le_add_right L.offset L.size) hBnd
      have hRelEmpBool : a.relocations.isEmpty = true :=
        bandRight (bandLeft (bandLeft (bandLeft (bandLeft hOk))))
      have hRelNil : a.relocations = [] := by
        cases hr : a.relocations with
        | nil => rfl
        | cons _ _ => rw [hr] at hRelEmpBool; nomatch hRelEmpBool
      let rawP := wfEncodeU32LeRawBytes v
      let bytes' := (a.bytes.take L.offset ++ rawP) ++ a.bytes.drop (L.offset + rawP.length)
      let a' : CapturedAllocation := { a with bytes := bytes' }
      have hAId : a.allocId = L.allocId :=
        lookupGlobalAlloc_id_eq_wf m.globals L.allocId a hFind
      have hLenEq : bytes'.length = a.bytes.length := by
        dsimp only [bytes', rawP]
        have hP4 : (wfEncodeU32LeRawBytes v).length = L.size := hSize4
        rw [List.length_append, List.length_append,
          listLength_take_of_le_wf L.offset a.bytes hOffLe,
          listLength_drop_wf, hP4, Nat.add_sub_of_le hBnd]
      have hOk' : v2026AllocLensOk L a' = true := by
        dsimp only [v2026AllocLensOk, a']
        rw [hLenEq]
        exact hOk
      unfold v2026SubLensGet
      rw [← hMeq]
      dsimp only
      have hFind' : lookupGlobalAlloc (replaceGlobalAllocWf a' m.globals) L.allocId = some a' := by
        rw [← hAId]
        exact lookupGlobalAlloc_replace_eq_wf a'
          (by dsimp only [a']; rw [hAId]; exact hFind)
      rw [hFind']
      dsimp only
      rw [hOk']
      dsimp only [a']
      unfold globalAllocSliceToAbstractBytes
      have hBle : Nat.ble L.offset (Trusted.Sequence.length bytes') = true := by
        change Nat.ble L.offset bytes'.length = true
        rw [hLenEq]
        exact natBle_of_le_wf hOffLe
      rw [hBle, hRelNil, ← hSize4]
      exact globalAllocBytesAux_rawLe_at bytes' 4 L.offset (wrapU32 v)
        (fun i hi => listGet_splice_mid_wf a.bytes rawP hOffLe hi)

/-- Disjoint sub-lens frame law (`[propext]`): writing to `L1` leaves `v2026SubLensGet L2`
invariant whenever `v2026LensDisjoint L1 L2 = true` (both cross-allocation and
same-allocation disjoint sub-slices). -/
theorem v2026SubLens_get_put_disjoint (L1 L2 : V2026SubLens) (m mOut : Memory)
    (rawPatch : List (Option UInt8))
    (hDisj : v2026LensDisjoint L1 L2 = true)
    (hPut : v2026SubLensPut L1 m rawPatch = some mOut) :
    v2026SubLensGet L2 mOut = v2026SubLensGet L2 m := by
  unfold v2026SubLensPut at hPut
  cases hFind1 : lookupGlobalAlloc m.globals L1.allocId with
  | none => rw [hFind1] at hPut; nomatch hPut
  | some a1 =>
    rw [hFind1] at hPut
    dsimp only at hPut
    cases hChk1 : (v2026AllocLensOk L1 a1 && Nat.beq rawPatch.length L1.size) with
    | false => rw [hChk1] at hPut; nomatch hPut
    | true =>
      rw [hChk1] at hPut
      dsimp only at hPut
      injection hPut with hMeq
      have hOk1 : v2026AllocLensOk L1 a1 = true := bandLeft hChk1
      have hPatchSz : rawPatch.length = L1.size := natEq_of_beq _ _ (bandRight hChk1)
      have hBnd1 : L1.offset + L1.size ≤ a1.bytes.length :=
        natLe_of_ble_wf (bandRight hOk1)
      have hOff1Le : L1.offset ≤ a1.bytes.length :=
        Nat.le_trans (Nat.le_add_right L1.offset L1.size) hBnd1
      have hA1Id : a1.allocId = L1.allocId :=
        lookupGlobalAlloc_id_eq_wf m.globals L1.allocId a1 hFind1
      let bytes' :=
        (a1.bytes.take L1.offset ++ rawPatch) ++ a1.bytes.drop (L1.offset + rawPatch.length)
      let a1' : CapturedAllocation := { a1 with bytes := bytes' }
      unfold v2026SubLensGet
      rw [← hMeq]
      dsimp only
      cases hIdEq : Nat.beq L1.allocId L2.allocId with
      | false =>
        have hNeA1' : Nat.beq a1'.allocId L2.allocId = false := by
          dsimp only [a1']
          rw [hA1Id]
          exact hIdEq
        rw [lookupGlobalAlloc_replace_ne_wf a1' L2.allocId hNeA1' m.globals]
      | true =>
        have hSameId : L1.allocId = L2.allocId := natEq_of_beq _ _ hIdEq
        dsimp only [v2026LensDisjoint] at hDisj
        rw [hIdEq] at hDisj
        dsimp only [Bool.not, Bool.or] at hDisj
        have hLenEq : bytes'.length = a1.bytes.length := by
          dsimp only [bytes']
          rw [List.length_append, List.length_append,
            listLength_take_of_le_wf L1.offset a1.bytes hOff1Le,
            listLength_drop_wf, hPatchSz, Nat.add_sub_of_le hBnd1]
        have hFind2Orig : lookupGlobalAlloc m.globals L2.allocId = some a1 := by
          rw [← hSameId]; exact hFind1
        have hFind2New : lookupGlobalAlloc (replaceGlobalAllocWf a1' m.globals) L2.allocId =
            some a1' := by
          rw [← hSameId, ← hA1Id]
          exact lookupGlobalAlloc_replace_eq_wf a1' (by dsimp only [a1']; rw [hA1Id]; exact hFind1)
        rw [hFind2New, hFind2Orig]
        dsimp only
        have hOk2Eq : v2026AllocLensOk L2 a1' = v2026AllocLensOk L2 a1 := by
          dsimp only [v2026AllocLensOk, a1']
          rw [hLenEq]
        rw [hOk2Eq]
        cases hOk2 : v2026AllocLensOk L2 a1 with
        | false => rfl
        | true =>
          dsimp only [a1']
          have hBnd2 : L2.offset + L2.size ≤ a1.bytes.length :=
            natLe_of_ble_wf (bandRight hOk2)
          have hOff2Le : L2.offset ≤ a1.bytes.length :=
            Nat.le_trans (Nat.le_add_right L2.offset L2.size) hBnd2
          unfold globalAllocSliceToAbstractBytes
          have hBleNew : Nat.ble L2.offset (Trusted.Sequence.length bytes') = true := by
            change Nat.ble L2.offset bytes'.length = true
            rw [hLenEq]
            exact natBle_of_le_wf hOff2Le
          have hBleOld : Nat.ble L2.offset (Trusted.Sequence.length a1.bytes) = true :=
            natBle_of_le_wf hOff2Le
          rw [hBleNew, hBleOld]
          apply globalAllocBytesAux_congr_get_wf bytes' a1.bytes a1.relocations L2.offset L2.size
          intro i hGe2 hLt2
          cases hLeft : Nat.ble (L1.offset + L1.size) L2.offset with
          | true =>
            have hAfter : L1.offset + rawPatch.length ≤ i := by
              rw [hPatchSz]
              exact Nat.le_trans (natLe_of_ble_wf hLeft) hGe2
            exact listGet_splice_ge_wf a1.bytes rawPatch hOff1Le hAfter
          | false =>
            rw [hLeft] at hDisj
            dsimp only [Bool.or] at hDisj
            have hBefore : i < L1.offset :=
              Nat.lt_of_lt_of_le hLt2 (natLe_of_ble_wf hDisj)
            exact listGet_splice_lt_wf a1.bytes rawPatch hOff1Le hBefore

/-- Explicit `Anneal.Firewall` tag isolating `Memory` global-allocation loan
synchronization from outer wavefront/CFG proof obligations. -/
def wfMemSyncFirewallTag : Nat := 202601

/-- Explicit `Anneal.Firewall` tag isolating `MachineState.memory` disjoint
global-allocation framing across `stepMirFn` / `runCfgSteps`. -/
def wfMirMemFrameFirewallTag : Nat := 202602

/-- Lifecycle phase of a tracked sub-slice loan (`.activeMut`, `.frozen`,
`.spatialCheckedOut scopeId`, or `.ended`). -/
inductive WfLoanPhase where
  | activeMut
  | frozen
  | spatialCheckedOut (scopeId : Nat)
  | ended

/-- Returns `true` iff the loan phase is not `.ended`. -/
def loanPhaseIsLive (ph : WfLoanPhase) : Bool :=
  match ph with
  | .ended => false
  | .activeMut | .frozen | .spatialCheckedOut _ => true

/-- Returns `true` iff `ph = .spatialCheckedOut sc`. -/
def loanPhaseMatchesScope (ph : WfLoanPhase) (sc : Nat) : Bool :=
  match ph with
  | .spatialCheckedOut s => Nat.beq s sc
  | .activeMut | .frozen | .ended => false

/-- Tracked `&mut` 4-byte `u32` loan entry directly coupled to unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.Memory` via `V2026SubLens`. -/
structure WfLoanEntryV2026 where
  id : Pos4
  phase : WfLoanPhase
  lens : V2026SubLens
  val : Nat

/-- Looks up the first loan entry with identifier `lid` in `loans`. -/
def wfFindLoan (lid : Pos4) (loans : List WfLoanEntryV2026) :
    Option WfLoanEntryV2026 :=
  loans.foldr
    (fun e acc =>
      match Pos4.beq e.id lid with
      | true => some e
      | false => acc)
    none

/-- Pure-lifted access check on a loan table (reads allow `.activeMut` and
`.frozen`; writes require `.activeMut`). -/
def wfCanPureAccessLoan (loans : List WfLoanEntryV2026) (lid : Pos4)
    (isWrite : Bool) : Bool :=
  match wfFindLoan lid loans with
  | none => false
  | some e =>
    match e.phase with
    | .activeMut => true
    | .frozen => !isWrite
    | .spatialCheckedOut _ | .ended => false

/-- Updates the `phase` and `val` of loan `lid` in `loans`. -/
def wfSetLoanEntryAt (loans : List WfLoanEntryV2026) (lid : Pos4)
    (ph : WfLoanPhase) (newVal : Nat) : List WfLoanEntryV2026 :=
  loans.map (fun e =>
    match Pos4.beq e.id lid with
    | true => ⟨e.id, ph, e.lens, newVal⟩
    | false => e)

private theorem wfFindLoan_wfSetLoanEntryAt_same (loans : List WfLoanEntryV2026)
    (lid : Pos4) (ph : WfLoanPhase) (newVal : Nat) (e : WfLoanEntryV2026)
    (hFind : wfFindLoan lid loans = some e) :
    wfFindLoan lid (wfSetLoanEntryAt loans lid ph newVal) =
      some ⟨e.id, ph, e.lens, newVal⟩ := by
  induction loans with
  | nil => nomatch hFind
  | cons hd tl ih =>
    dsimp only [wfFindLoan, List.foldr] at hFind
    dsimp only [wfSetLoanEntryAt, List.map, wfFindLoan, List.foldr]
    cases hEq : Pos4.beq hd.id lid with
    | true =>
      rw [hEq] at hFind
      injection hFind with hSame
      rw [← hSame]
      dsimp only
      rw [hEq]
    | false =>
      rw [hEq] at hFind
      dsimp only
      rw [hEq]
      exact ih hFind

private theorem wfFindLoan_wfSetLoanEntryAt_ne (loans : List WfLoanEntryV2026)
    (lid lid2 : Pos4) (ph : WfLoanPhase) (newVal : Nat)
    (hNe : Pos4.beq lid lid2 = false) :
    wfFindLoan lid2 (wfSetLoanEntryAt loans lid ph newVal) =
      wfFindLoan lid2 loans := by
  induction loans with
  | nil => rfl
  | cons hd tl ih =>
    dsimp only [wfSetLoanEntryAt, List.map, wfFindLoan, List.foldr]
    cases hEq1 : Pos4.beq hd.id lid with
    | true =>
      dsimp only
      have hSame := pos4_eq_of_beq hd.id lid hEq1
      rw [hSame, hNe]
      exact ih
    | false =>
      dsimp only
      cases Pos4.beq hd.id lid2 with
      | true => rfl
      | false => exact ih

private theorem wfFindLoan_wfSetLoanEntryAt_preserves_none
    (loans : List WfLoanEntryV2026) (q lid : Pos4)
    (ph : WfLoanPhase) (newVal : Nat) (hNone : wfFindLoan q loans = none) :
    wfFindLoan q (wfSetLoanEntryAt loans lid ph newVal) = none := by
  induction loans with
  | nil => rfl
  | cons hd tl ih =>
    dsimp only [wfFindLoan, List.foldr] at hNone
    dsimp only [wfSetLoanEntryAt, List.map, wfFindLoan, List.foldr]
    cases hEqQ : Pos4.beq hd.id q with
    | true => rw [hEqQ] at hNone; nomatch hNone
    | false =>
      rw [hEqQ] at hNone
      cases Pos4.beq hd.id lid with
      | true => dsimp only; rw [hEqQ]; exact ih hNone
      | false => dsimp only; rw [hEqQ]; exact ih hNone

private theorem wfSetLoanEntryAt_of_wfFindLoan_none
    (loans : List WfLoanEntryV2026) (lid : Pos4)
    (ph : WfLoanPhase) (newVal : Nat) (hNone : wfFindLoan lid loans = none) :
    wfSetLoanEntryAt loans lid ph newVal = loans := by
  induction loans with
  | nil => rfl
  | cons hd tl ih =>
    dsimp only [wfFindLoan, List.foldr] at hNone
    dsimp only [wfSetLoanEntryAt, List.map]
    cases hEq : Pos4.beq hd.id lid with
    | true => rw [hEq] at hNone; nomatch hNone
    | false =>
      rw [hEq] at hNone
      exact congrArg (List.cons hd) (ih hNone)

/-- Asserts that `L` is byte-disjoint from every loan lens in `tl`. -/
def allDisjointFromLens (L : V2026SubLens) (tl : List WfLoanEntryV2026) : Prop :=
  tl.foldr (fun e' acc => v2026LensDisjoint L e'.lens = true ∧ acc) True

private theorem allDisjointFromLens_wfSetLoanEntryAt (L : V2026SubLens)
    (tl : List WfLoanEntryV2026) (lid : Pos4) (ph : WfLoanPhase) (newVal : Nat)
    (hDisj : allDisjointFromLens L tl) :
    allDisjointFromLens L (wfSetLoanEntryAt tl lid ph newVal) := by
  induction tl with
  | nil => exact True.intro
  | cons hd rest ih =>
    dsimp only [allDisjointFromLens, List.foldr] at hDisj
    dsimp only [wfSetLoanEntryAt, List.map, allDisjointFromLens, List.foldr]
    cases Pos4.beq hd.id lid with
    | true => exact ⟨hDisj.1, ih hDisj.2⟩
    | false => exact ⟨hDisj.1, ih hDisj.2⟩

private theorem allDisjointFromLens_wfFindLoan (L : V2026SubLens)
    (tl : List WfLoanEntryV2026) (lid : Pos4) (e : WfLoanEntryV2026)
    (hDisj : allDisjointFromLens L tl) (hFind : wfFindLoan lid tl = some e) :
    v2026LensDisjoint L e.lens = true := by
  induction tl with
  | nil => nomatch hFind
  | cons hd rest ih =>
    dsimp only [allDisjointFromLens, List.foldr] at hDisj
    dsimp only [wfFindLoan, List.foldr] at hFind
    cases hEq : Pos4.beq hd.id lid with
    | true =>
      rw [hEq] at hFind
      injection hFind with hSame
      rw [← hSame]
      exact hDisj.1
    | false =>
      rw [hEq] at hFind
      exact ih hDisj.2 hFind

/-- Unshielded loan-to-`V2026_06_01.MirSemantics.Memory` synchronization body:
unique `Pos4` IDs, pairwise-disjoint 4-byte `V2026SubLens` slices, `val < 2^32`,
and exact little-endian `encodeLittleEndianBytes` byte agreement in `m` for live loans. -/
def LoansSyncedWithMemRawV2026 (loans : List WfLoanEntryV2026) (m : Memory) : Prop :=
  listFold True
    (fun e tl acc =>
      wfFindLoan e.id tl = none ∧
      allDisjointFromLens e.lens tl ∧
      e.lens.size = 4 ∧
      e.val = wrapU32 e.val ∧
      (match loanPhaseIsLive e.phase with
       | false => True
       | true => v2026SubLensGet e.lens m = some (wfEncodeU32LeAbsBytes e.val)) ∧
      acc)
    loans

/-- `Anneal.Firewall`-shielded loan-to-`V2026_06_01` `Memory` synchronization
invariant (`Firewall wfMemSyncFirewallTag`): prevents Lean's kernel WHNF and
tactic `rw` / `dsimp` from unfolding large `Memory` terms during wavefront drain! -/
def LoansSyncedWithMemV2026 (loans : List WfLoanEntryV2026) (m : Memory) : Prop :=
  Firewall wfMemSyncFirewallTag (LoansSyncedWithMemRawV2026 loans m)

/-- Seals `LoansSyncedWithMemRawV2026` behind `Firewall wfMemSyncFirewallTag`. -/
theorem seal_loansSyncedWithMemV2026 {loans : List WfLoanEntryV2026} {m : Memory}
    (h : LoansSyncedWithMemRawV2026 loans m) : LoansSyncedWithMemV2026 loans m :=
  Firewall.wrap wfMemSyncFirewallTag h

/-- Unseals `LoansSyncedWithMemV2026` at explicit memory-access boundaries. -/
theorem unseal_loansSyncedWithMemV2026 {loans : List WfLoanEntryV2026} {m : Memory}
    (h : LoansSyncedWithMemV2026 loans m) : LoansSyncedWithMemRawV2026 loans m :=
  Firewall.unwrap h

private theorem loansSyncedWithMemRaw_cons (e : WfLoanEntryV2026)
    (tl : List WfLoanEntryV2026) (m : Memory) :
    LoansSyncedWithMemRawV2026 (e :: tl) m =
      (wfFindLoan e.id tl = none ∧
       allDisjointFromLens e.lens tl ∧
       e.lens.size = 4 ∧
       e.val = wrapU32 e.val ∧
       (match loanPhaseIsLive e.phase with
        | false => True
        | true => v2026SubLensGet e.lens m = some (wfEncodeU32LeAbsBytes e.val)) ∧
       LoansSyncedWithMemRawV2026 tl m) :=
  listFold_cons _ _ e tl

private theorem wfFindLoan_synced_live_props (loans : List WfLoanEntryV2026)
    (m : Memory) (lid : Pos4) (e : WfLoanEntryV2026)
    (hSyncFw : LoansSyncedWithMemV2026 loans m)
    (hFind : wfFindLoan lid loans = some e)
    (hLive : loanPhaseIsLive e.phase = true) :
    e.id = lid ∧
    e.lens.size = 4 ∧
    e.val = wrapU32 e.val ∧
    v2026SubLensGet e.lens m = some (wfEncodeU32LeAbsBytes e.val) := by
  have hSync := unseal_loansSyncedWithMemV2026 hSyncFw
  induction loans with
  | nil => nomatch hFind
  | cons hd tl ih =>
    rw [loansSyncedWithMemRaw_cons] at hSync
    dsimp only [wfFindLoan, List.foldr] at hFind
    cases hEq : Pos4.beq hd.id lid with
    | true =>
      rw [hEq] at hFind
      injection hFind with hSame
      rw [← hSame]
      have hMem := hSync.2.2.2.2.1
      rw [← hSame] at hLive
      rw [hLive] at hMem
      exact ⟨pos4_eq_of_beq hd.id lid hEq, hSync.2.2.1, hSync.2.2.2.1, hMem⟩
    | false =>
      rw [hEq] at hFind
      exact ih (seal_loansSyncedWithMemV2026 hSync.2.2.2.2.2) hFind hSync.2.2.2.2.2

private theorem loansSyncedWithMemRaw_put_disjoint (L : V2026SubLens)
    (loans : List WfLoanEntryV2026) (m mOut : Memory) (rawPatch : List (Option UInt8))
    (hDisj : allDisjointFromLens L loans)
    (hPut : v2026SubLensPut L m rawPatch = some mOut)
    (hSync : LoansSyncedWithMemRawV2026 loans m) :
    LoansSyncedWithMemRawV2026 loans mOut := by
  induction loans with
  | nil => exact True.intro
  | cons hd tl ih =>
    dsimp only [allDisjointFromLens, List.foldr] at hDisj
    rw [loansSyncedWithMemRaw_cons] at hSync
    rw [loansSyncedWithMemRaw_cons]
    refine ⟨hSync.1, hSync.2.1, hSync.2.2.1, hSync.2.2.2.1, ?_,
      ih hDisj.2 hSync.2.2.2.2.2⟩
    cases hLv : loanPhaseIsLive hd.phase with
    | false => exact True.intro
    | true =>
      have hM := hSync.2.2.2.2.1
      rw [hLv] at hM
      rw [v2026SubLens_get_put_disjoint L hd.lens m mOut rawPatch hDisj.1 hPut]
      exact hM

private theorem loansSyncedWithMemV2026_setPhase_sameVal
    (loans : List WfLoanEntryV2026) (m : Memory)
    (lid : Pos4) (e : WfLoanEntryV2026) (newPh : WfLoanPhase)
    (hSyncFw : LoansSyncedWithMemV2026 loans m)
    (hFind : wfFindLoan lid loans = some e)
    (hOldLive : loanPhaseIsLive e.phase = true)
    (hNewLive : loanPhaseIsLive newPh = true) :
    LoansSyncedWithMemV2026 (wfSetLoanEntryAt loans lid newPh e.val) m := by
  apply seal_loansSyncedWithMemV2026
  have hSync := unseal_loansSyncedWithMemV2026 hSyncFw
  induction loans with
  | nil => nomatch hFind
  | cons hd tl ih =>
    rw [loansSyncedWithMemRaw_cons] at hSync
    dsimp only [wfFindLoan, List.foldr] at hFind
    dsimp only [wfSetLoanEntryAt, List.map]
    cases hEq : Pos4.beq hd.id lid with
    | true =>
      rw [hEq] at hFind
      injection hFind with hSame
      have hIdEq := pos4_eq_of_beq hd.id lid hEq
      have hNoneLid : wfFindLoan lid tl = none := by rw [← hIdEq]; exact hSync.1
      have hTlEq : wfSetLoanEntryAt tl lid newPh e.val = tl :=
        wfSetLoanEntryAt_of_wfFindLoan_none tl lid newPh e.val hNoneLid
      change LoansSyncedWithMemRawV2026
        (⟨hd.id, newPh, hd.lens, e.val⟩ :: wfSetLoanEntryAt tl lid newPh e.val) m
      rw [hTlEq, loansSyncedWithMemRaw_cons]
      have hMem := hSync.2.2.2.2.1
      rw [hSame, hOldLive] at hMem
      rw [← hSame] at hMem
      refine ⟨hSync.1, hSync.2.1, hSync.2.2.1, ?_, ?_, hSync.2.2.2.2.2⟩
      · rw [← hSame]; exact hSync.2.2.2.1
      · dsimp only; rw [hNewLive, ← hSame]; exact hMem
    | false =>
      rw [hEq] at hFind
      change LoansSyncedWithMemRawV2026 (hd :: wfSetLoanEntryAt tl lid newPh e.val) m
      rw [loansSyncedWithMemRaw_cons]
      exact ⟨wfFindLoan_wfSetLoanEntryAt_preserves_none tl hd.id lid newPh e.val hSync.1,
        allDisjointFromLens_wfSetLoanEntryAt hd.lens tl lid newPh e.val hSync.2.1,
        hSync.2.2.1, hSync.2.2.2.1, hSync.2.2.2.2.1,
        ih (seal_loansSyncedWithMemV2026 hSync.2.2.2.2.2) hFind hSync.2.2.2.2.2⟩

private theorem loansSyncedWithMemV2026_set_and_put
    (loans : List WfLoanEntryV2026) (m mOut : Memory)
    (lid : Pos4) (e : WfLoanEntryV2026) (newPh : WfLoanPhase) (newVal : Nat)
    (hSyncFw : LoansSyncedWithMemV2026 loans m)
    (hFind : wfFindLoan lid loans = some e)
    (hNewLive : loanPhaseIsLive newPh = true)
    (hWrap : newVal = wrapU32 newVal)
    (hPut : v2026SubLensPut e.lens m (wfEncodeU32LeRawBytes newVal) = some mOut) :
    LoansSyncedWithMemV2026 (wfSetLoanEntryAt loans lid newPh newVal) mOut := by
  apply seal_loansSyncedWithMemV2026
  have hSync := unseal_loansSyncedWithMemV2026 hSyncFw
  induction loans with
  | nil => nomatch hFind
  | cons hd tl ih =>
    rw [loansSyncedWithMemRaw_cons] at hSync
    dsimp only [wfFindLoan, List.foldr] at hFind
    dsimp only [wfSetLoanEntryAt, List.map]
    cases hEq : Pos4.beq hd.id lid with
    | true =>
      rw [hEq] at hFind
      injection hFind with hSame
      have hIdEq := pos4_eq_of_beq hd.id lid hEq
      have hNoneLid : wfFindLoan lid tl = none := by rw [← hIdEq]; exact hSync.1
      have hTlEq : wfSetLoanEntryAt tl lid newPh newVal = tl :=
        wfSetLoanEntryAt_of_wfFindLoan_none tl lid newPh newVal hNoneLid
      change LoansSyncedWithMemRawV2026
        (⟨hd.id, newPh, hd.lens, newVal⟩ :: wfSetLoanEntryAt tl lid newPh newVal) mOut
      rw [hTlEq, loansSyncedWithMemRaw_cons]
      rw [← hSame] at hPut
      refine ⟨hSync.1, hSync.2.1, hSync.2.2.1, hWrap, ?_,
        loansSyncedWithMemRaw_put_disjoint hd.lens tl m mOut _ hSync.2.1 hPut
          hSync.2.2.2.2.2⟩
      dsimp only
      rw [hNewLive]
      exact v2026SubLens_put_get_u32 hd.lens m mOut newVal hPut
    | false =>
      rw [hEq] at hFind
      change LoansSyncedWithMemRawV2026 (hd :: wfSetLoanEntryAt tl lid newPh newVal) mOut
      rw [loansSyncedWithMemRaw_cons]
      have hDisjHdE : v2026LensDisjoint hd.lens e.lens = true :=
        allDisjointFromLens_wfFindLoan hd.lens tl lid e hSync.2.1 hFind
      have hDisjEHd : v2026LensDisjoint e.lens hd.lens = true := by
        rw [v2026LensDisjoint_symm]; exact hDisjHdE
      refine ⟨wfFindLoan_wfSetLoanEntryAt_preserves_none tl hd.id lid newPh newVal hSync.1,
        allDisjointFromLens_wfSetLoanEntryAt hd.lens tl lid newPh newVal hSync.2.1,
        hSync.2.2.1, hSync.2.2.2.1, ?_,
        ih (seal_loansSyncedWithMemV2026 hSync.2.2.2.2.2) hFind hSync.2.2.2.2.2⟩
      cases hLv : loanPhaseIsLive hd.phase with
      | false => exact True.intro
      | true =>
        have hM := hSync.2.2.2.2.1
        rw [hLv] at hM
        rw [v2026SubLens_get_put_disjoint e.lens hd.lens m mOut _ hDisjEHd hPut]
        exact hM

/-- Queued wavefront worker task carrying `taskId`, `rank`, remaining yields
`remYields`, target `loanId`, `scopeId`, and leaf `writeDelta`. -/
structure WorkerTask where
  taskId : Nat
  rank : Nat
  remYields : Nat
  loanId : Pos4
  scopeId : Nat
  writeDelta : Nat

/-- Concrete `V2026_06_01` wavefront machine state coupling unmodified `Memory`,
`loans`, spatial `cells`, `fifoQueue`, `stealDeque`, `nextTaskId`,
`completedCount`, and `stepCount`. -/
structure WavefrontWorldV2026 where
  mem : Memory
  loans : List WfLoanEntryV2026
  cells : ResTrie Nat
  fifoQueue : List WorkerTask
  stealDeque : List WorkerTask
  nextTaskId : Nat
  completedCount : Nat
  stepCount : Nat

/-- Returns `true` if any task in `qs` targets `lid`. -/
def anyTaskHasLoan (lid : Pos4) (qs : List WorkerTask) : Bool :=
  qs.foldr (fun t acc => Pos4.beq t.loanId lid || acc) false

/-- Returns `true` if any task in `qs` targets `(lid, sc)`. -/
def anyTaskHasLoanScope (lid : Pos4) (sc : Nat) (qs : List WorkerTask) : Bool :=
  qs.foldr (fun t acc => (Pos4.beq t.loanId lid && Nat.beq t.scopeId sc) || acc) false

private theorem anyTaskHasLoan_append (lid : Pos4) (xs ys : List WorkerTask) :
    anyTaskHasLoan lid (xs ++ ys) = (anyTaskHasLoan lid xs || anyTaskHasLoan lid ys) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    change (Pos4.beq hd.loanId lid || anyTaskHasLoan lid (tl ++ ys)) =
      ((Pos4.beq hd.loanId lid || anyTaskHasLoan lid tl) || anyTaskHasLoan lid ys)
    rw [ih]
    cases Pos4.beq hd.loanId lid <;> rfl

/-- Every queued task in `qs` targets a live loan in `loans` whose phase is
`.spatialCheckedOut t.scopeId`. -/
def queueMatchesLoansBool (qs : List WorkerTask) (loans : List WfLoanEntryV2026) : Bool :=
  qs.foldr
    (fun t acc =>
      (match wfFindLoan t.loanId loans with
       | none => false
       | some e => loanPhaseMatchesScope e.phase t.scopeId) && acc)
    true

/-- Checks that every queued task in `fifoQueue` and `stealDeque` references a
live `.spatialCheckedOut` loan with matching `scopeId`. -/
def checkQueueMatchesLoansBool (w : WavefrontWorldV2026) : Bool :=
  queueMatchesLoansBool w.fifoQueue w.loans &&
    queueMatchesLoansBool w.stealDeque w.loans

/-- Propositional queue-to-loan coupling `checkQueueMatchesLoansBool w = true`. -/
def QueueMatchesLoansV2026 (w : WavefrontWorldV2026) : Prop :=
  checkQueueMatchesLoansBool w = true

private theorem queueMatchesLoansBool_append (xs ys : List WorkerTask)
    (loans : List WfLoanEntryV2026) :
    queueMatchesLoansBool (xs ++ ys) loans =
      (queueMatchesLoansBool xs loans && queueMatchesLoansBool ys loans) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    change (_ && queueMatchesLoansBool (tl ++ ys) loans) =
      ((_ && queueMatchesLoansBool tl loans) && queueMatchesLoansBool ys loans)
    rw [ih]
    cases
      (match wfFindLoan hd.loanId loans with
       | none => false
       | some e => loanPhaseMatchesScope e.phase hd.scopeId) <;> rfl

private theorem not_anyTaskHasLoan_of_activeMut (lid : Pos4) (e : WfLoanEntryV2026)
    (qs : List WorkerTask) (loans : List WfLoanEntryV2026)
    (hFind : wfFindLoan lid loans = some e)
    (hPh : e.phase = .activeMut)
    (hQ : queueMatchesLoansBool qs loans = true) :
    anyTaskHasLoan lid qs = false := by
  induction qs with
  | nil => rfl
  | cons t tl ih =>
    dsimp only [queueMatchesLoansBool, List.foldr] at hQ
    dsimp only [anyTaskHasLoan, List.foldr]
    cases hEq : Pos4.beq t.loanId lid with
    | false => exact ih (bandRight hQ)
    | true =>
      have hSame := pos4_eq_of_beq t.loanId lid hEq
      have hHd := bandLeft hQ
      rw [hSame, hFind] at hHd
      dsimp only at hHd
      rw [hPh] at hHd
      exact False.elim (boolFalseNeTrue hHd)

private theorem queueMatchesLoansBool_wfSetLoanEntryAt_of_not_hasLoan
    (qs : List WorkerTask) (loans : List WfLoanEntryV2026)
    (lid : Pos4) (ph : WfLoanPhase) (newVal : Nat)
    (hNo : anyTaskHasLoan lid qs = false)
    (hQ : queueMatchesLoansBool qs loans = true) :
    queueMatchesLoansBool qs (wfSetLoanEntryAt loans lid ph newVal) = true := by
  induction qs with
  | nil => rfl
  | cons t tl ih =>
    dsimp only [anyTaskHasLoan, List.foldr] at hNo
    have hSp := borFalseElim hNo
    dsimp only [queueMatchesLoansBool, List.foldr] at hQ
    dsimp only [queueMatchesLoansBool, List.foldr]
    have hNeSymm : Pos4.beq lid t.loanId = false := by
      rw [pos4_beq_symm]; exact hSp.1
    rw [wfFindLoan_wfSetLoanEntryAt_ne loans lid t.loanId ph newVal hNeSymm]
    exact bandIntro (bandLeft hQ) (ih hSp.2 (bandRight hQ))

private theorem queueMatchesLoansBool_wfSetLoanEntryAt_samePhase
    (qs : List WorkerTask) (loans : List WfLoanEntryV2026)
    (lid : Pos4) (e : WfLoanEntryV2026) (newVal : Nat)
    (hFind : wfFindLoan lid loans = some e)
    (hQ : queueMatchesLoansBool qs loans = true) :
    queueMatchesLoansBool qs (wfSetLoanEntryAt loans lid e.phase newVal) = true := by
  induction qs with
  | nil => rfl
  | cons t tl ih =>
    dsimp only [queueMatchesLoansBool, List.foldr] at hQ
    dsimp only [queueMatchesLoansBool, List.foldr]
    cases hEq : Pos4.beq lid t.loanId with
    | true =>
      have hSame := pos4_eq_of_beq lid t.loanId hEq
      rw [← hSame, wfFindLoan_wfSetLoanEntryAt_same loans lid e.phase newVal e hFind]
      have hHd := bandLeft hQ
      rw [← hSame, hFind] at hHd
      exact bandIntro hHd (ih (bandRight hQ))
    | false =>
      rw [wfFindLoan_wfSetLoanEntryAt_ne loans lid t.loanId e.phase newVal hEq]
      exact bandIntro (bandLeft hQ) (ih (bandRight hQ))

private theorem anyTaskHasLoanScope_eq_anyTaskHasLoan_of_queueMatches
    (lid : Pos4) (sc : Nat) (e : WfLoanEntryV2026) (qs : List WorkerTask)
    (loans : List WfLoanEntryV2026)
    (hFind : wfFindLoan lid loans = some e)
    (hPh : e.phase = .spatialCheckedOut sc)
    (hQ : queueMatchesLoansBool qs loans = true) :
    anyTaskHasLoanScope lid sc qs = anyTaskHasLoan lid qs := by
  induction qs with
  | nil => rfl
  | cons t tl ih =>
    dsimp only [queueMatchesLoansBool, List.foldr] at hQ
    change ((Pos4.beq t.loanId lid && Nat.beq t.scopeId sc) ||
      anyTaskHasLoanScope lid sc tl) =
      (Pos4.beq t.loanId lid || anyTaskHasLoan lid tl)
    rw [ih (bandRight hQ)]
    cases hEq : Pos4.beq t.loanId lid with
    | false => rfl
    | true =>
      have hSame := pos4_eq_of_beq t.loanId lid hEq
      have hHd := bandLeft hQ
      rw [hSame, hFind] at hHd
      dsimp only at hHd
      rw [hPh] at hHd
      dsimp only [loanPhaseMatchesScope] at hHd
      have hScSymm : Nat.beq t.scopeId sc = true := by
        rw [natBeq_symm]; exact hHd
      rw [hScSymm]
      rfl

/-- Coefficient contributed by task `t` at CNF exponent `q` (`1` at `2*rank + 1`
plus `remYields` at `2*rank`). -/
def wfTaskWeightAt (q : Nat) (t : WorkerTask) : Nat :=
  (match Nat.beq (t.rank + t.rank + 1) q with | true => 1 | false => 0) +
  (match Nat.beq (t.rank + t.rank) q with | true => t.remYields | false => 0)

/-- Total coefficient summed across `qs` at exponent `q`. -/
def wfTasksWeightAt (q : Nat) (qs : List WorkerTask) : Nat :=
  qs.foldr (fun t acc => wfTaskWeightAt q t + acc) 0

/-- Adds task `t`'s ordinal weight `ω^(2*rank + 1) + ω^(2*rank) * remYields`
into canonical CNF accumulator `acc`. -/
def wfTaskMeasure (t : WorkerTask) (acc : CnfOrd) : CnfOrd :=
  cnfAddTerm (t.rank + t.rank + 1) 1 (cnfAddTerm (t.rank + t.rank) t.remYields acc)

/-- Single-task `< ω^ω` ordinal weight `ω^(2*rank + 1) + ω^(2*rank) * remYields`. -/
def burstTaskDelta (rank remYields : Nat) : CnfOrd :=
  cnfAddTerm (rank + rank + 1) 1 (cnfAddTerm (rank + rank) remYields [])

/-- Folds `wfTaskMeasure` across `qs` onto `init`. -/
def wfQueueMeasure (qs : List WorkerTask) (init : CnfOrd) : CnfOrd :=
  qs.foldr wfTaskMeasure init

/-- Total `< ω^ω` Cantor Normal Form ordinal measure of `w.fifoQueue` and
`w.stealDeque`. -/
def worldMeasureV2026 (w : WavefrontWorldV2026) : CnfOrd :=
  wfQueueMeasure w.fifoQueue (wfQueueMeasure w.stealDeque [])

private theorem wfTasksWeightAt_append (q : Nat) (xs ys : List WorkerTask) :
    wfTasksWeightAt q (xs ++ ys) = wfTasksWeightAt q xs + wfTasksWeightAt q ys := by
  induction xs with
  | nil => exact Eq.symm (natAdd_zero_left (wfTasksWeightAt q ys))
  | cons hd _ ih =>
    change wfTaskWeightAt q hd + wfTasksWeightAt q (_ ++ ys) =
      (wfTaskWeightAt q hd + wfTasksWeightAt q _) + wfTasksWeightAt q ys
    rw [ih, natAdd_assoc]

private theorem wfQueueMeasure_canonical_and_coeff (q : Nat) (qs : List WorkerTask)
    (init : CnfOrd) (hInit : isCanonicalCnf init = true) :
    isCanonicalCnf (wfQueueMeasure qs init) = true ∧
    cnfCoeffAt q (wfQueueMeasure qs init) =
      wfTasksWeightAt q qs + cnfCoeffAt q init := by
  induction qs with
  | nil => exact ⟨hInit, Eq.symm (natAdd_zero_left (cnfCoeffAt q init))⟩
  | cons t _ ih =>
    exact ⟨isCanonicalCnf_cnfAddTerm (t.rank + t.rank + 1) 1 _
      (isCanonicalCnf_cnfAddTerm (t.rank + t.rank) t.remYields _ ih.1),
      Eq.trans (cnfCoeffAt_cnfAddTerm q (t.rank + t.rank + 1) 1 _)
        (Eq.trans (congrArg (Nat.add _) (cnfCoeffAt_cnfAddTerm q (t.rank +
          t.rank) t.remYields _))
          (Eq.trans (Eq.symm (natAdd_assoc _ _ _))
            (Eq.trans (congrArg (Nat.add (wfTaskWeightAt q t)) ih.2)
              (Eq.symm (natAdd_assoc _ _ _)))))⟩

/-- Every `worldMeasureV2026 w` is in canonical Cantor Normal Form (`[]`). -/
theorem worldMeasureV2026_canonical (w : WavefrontWorldV2026) :
    isCanonicalCnf (worldMeasureV2026 w) = true :=
  (wfQueueMeasure_canonical_and_coeff 0 w.fifoQueue _
    (wfQueueMeasure_canonical_and_coeff 0 w.stealDeque [] rfl).1).1

private theorem cnfCoeffAt_worldMeasureV2026 (q : Nat) (w : WavefrontWorldV2026) :
    cnfCoeffAt q (worldMeasureV2026 w) =
      wfTasksWeightAt q w.fifoQueue + wfTasksWeightAt q w.stealDeque := by
  have hS := wfQueueMeasure_canonical_and_coeff q w.stealDeque [] rfl
  exact Eq.trans (wfQueueMeasure_canonical_and_coeff q w.fifoQueue _ hS.1).2
    (congrArg (Nat.add (wfTasksWeightAt q w.fifoQueue)) hS.2)

private theorem burstTaskDelta_canonical (rank remYields : Nat) :
    isCanonicalCnf (burstTaskDelta rank remYields) = true :=
  isCanonicalCnf_cnfAddTerm (rank + rank + 1) 1 _
    (isCanonicalCnf_cnfAddTerm (rank + rank) remYields [] rfl)

private theorem burstTaskDelta_pos (rank remYields : Nat) :
    cnfLt [] (burstTaskDelta rank remYields) = true := by
  apply cnfLt_of_coeff_drop [] (burstTaskDelta rank remYields) rfl
    (burstTaskDelta_canonical rank remYields) (rank + rank + 1)
  · dsimp only [burstTaskDelta]
    rw [cnfCoeffAt_cnfAddTerm, cnfCoeffAt_cnfAddTerm, natBeq_refl (rank + rank + 1)]
    have hNe : Nat.beq (rank + rank) (rank + rank + 1) = false :=
      natBeqFalseOfLt (natLtSuccSelf (rank + rank))
    rw [hNe]
    rfl
  · intro q hGt
    dsimp only [burstTaskDelta]
    rw [cnfCoeffAt_cnfAddTerm, cnfCoeffAt_cnfAddTerm, natBeqFalseOfLt hGt,
      natBeqFalseOfLt (natLtTrans (rank + rank) (rank + rank + 1) q
        (natLtSuccSelf _) hGt)]
    rfl

private theorem wfTaskMeasure_eq_cnfAddOrd_burstTaskDelta (t : WorkerTask)
    (acc : CnfOrd) (hAcc : isCanonicalCnf acc = true) :
    wfTaskMeasure t acc = cnfAddOrd (burstTaskDelta t.rank t.remYields) acc := by
  apply cnf_eq_of_coeff_eq _ _
    (isCanonicalCnf_cnfAddTerm _ _ _ (isCanonicalCnf_cnfAddTerm _ _ _ hAcc))
    (isCanonicalCnf_cnfNatAdd _ acc)
  intro q
  dsimp only [wfTaskMeasure, burstTaskDelta, cnfAddOrd]
  rw [cnfCoeffAt_cnfNatAdd, cnfCoeffAt_cnfAddTerm, cnfCoeffAt_cnfAddTerm,
    cnfCoeffAt_cnfAddTerm, cnfCoeffAt_cnfAddTerm]
  have hZ : cnfCoeffAt q [] = 0 := rfl
  rw [hZ]
  exact Eq.symm (natAdd_assoc _ _ _)

/-- Reads `.pool` ordinal capacity from `poolPath` (defaulting `none` to `some []`). -/
def extractPoolCap (r : ResTrie ResElem) : Option CnfOrd :=
  match ResTrie.getBits poolPath r with
  | none => some []
  | some (.pool p) => some (cnfNorm p)
  | some (.debt _) | some (.checkedOutLoan _ _) | some (.cell _) => none

/-- Reads `.debt` ordinal budget from `debtPath` (defaulting `none` to `some []`). -/
def extractDebtCap (r : ResTrie ResElem) : Option CnfOrd :=
  match ResTrie.getBits debtPath r with
  | none => some []
  | some (.debt d) => some (cnfNorm d)
  | some (.pool _) | some (.checkedOutLoan _ _) | some (.cell _) => none

/-- Boolean pool and debt `< ω^ω` capacity check for `WorldMatchesV2026`. -/
def checkWorldMatchesPoolBool (r : ResTrie ResElem) (w : WavefrontWorldV2026) : Bool :=
  match extractPoolCap r with
  | none => false
  | some poolCap =>
    match extractDebtCap r with
    | none => false
    | some debtCap =>
      cnfBle (worldMeasureV2026 w) poolCap &&
      cnfBle (cnfAddOrd debtCap (worldMeasureV2026 w)) poolCap

/-- Full `V2026_06_01` spatial and `Firewall`-shielded memory world invariant. -/
structure WorldMatchesV2026 (v : View) (r : ResTrie ResElem)
    (w : WavefrontWorldV2026) : Prop where
  viewOk : Nat.ble (viewGet v 0) w.stepCount = true
  loansMemOk : LoansSyncedWithMemV2026 w.loans w.mem
  queueLoansOk : QueueMatchesLoansV2026 w
  poolDebtOk : checkWorldMatchesPoolBool r w = true
  cellOk : ∀ (cid : Pos4),
    match ResTrie.getBits (cellPath cid) r with
    | none => True
    | some (.pool _) | some (.debt _) | some (.checkedOutLoan _ _) => False
    | some (.cell cf) =>
      match cf with
      | .capOnly =>
        match ResTrie.getBits (pos4ToList cid) w.cells with
        | none => False | some _ => True
      | .authOnly cv | .capAndAuth cv =>
        ResTrie.getBits (pos4ToList cid) w.cells = some cv
  checkedLoanOk : ∀ (lid : Pos4),
    match ResTrie.getBits (checkedLoanPath lid) r with
    | none => True
    | some (.pool _) | some (.debt _) | some (.cell _) => False
    | some (.checkedOutLoan sid lv) =>
      (!anyTaskHasLoan lid w.fifoQueue && !anyTaskHasLoan lid w.stealDeque) = true ∧
      ∃ e : WfLoanEntryV2026,
        wfFindLoan lid w.loans = some e ∧
        e.phase = .spatialCheckedOut sid ∧ e.val = lv

/-- Generates `count` sequential `WorkerTask`s starting at `baseId`. -/
def mkWorkers (baseId count rank yields : Nat) (lid : Pos4) (sc writeDelta : Nat) :
    List WorkerTask :=
  @Nat.rec (fun _ => Nat → List WorkerTask)
    (fun _ => [])
    (fun _ ih tid => WorkerTask.mk tid rank yields lid sc writeDelta :: ih (tid + 1))
    count baseId

private theorem mkWorkers_not_hasLoan (lid1 lid2 : Pos4)
    (baseId k rc cy sc wd : Nat) (hNe : Pos4.beq lid1 lid2 = false) :
    anyTaskHasLoan lid2 (mkWorkers baseId k rc cy lid1 sc wd) = false := by
  revert baseId
  induction k with
  | zero => intro _; rfl
  | succ m ih =>
    intro baseId
    change (Pos4.beq lid1 lid2 || anyTaskHasLoan lid2
      (mkWorkers (baseId + 1) m rc cy lid1 sc wd)) = false
    rw [hNe, ih (baseId + 1)]
    rfl

private theorem queueMatchesLoansBool_mkWorkers (baseId k rc cy : Nat)
    (lid : Pos4) (sc wd : Nat) (loans : List WfLoanEntryV2026)
    (hMatch :
      (match wfFindLoan lid loans with
       | none => false
       | some e => loanPhaseMatchesScope e.phase sc) = true) :
    queueMatchesLoansBool (mkWorkers baseId k rc cy lid sc wd) loans = true := by
  revert baseId
  induction k with
  | zero => intro _; rfl
  | succ m ih =>
    intro baseId
    change
      ((match wfFindLoan lid loans with
        | none => false
        | some e => loanPhaseMatchesScope e.phase sc) &&
        queueMatchesLoansBool (mkWorkers (baseId + 1) m rc cy lid sc wd) loans) = true
    rw [hMatch]
    exact ih (baseId + 1)

/-! ## 3. Fail-Closed Hybrid Command Semantics (`evalHybridCmdV2026`) & `VSepWpOrdRelV2026` -/

/-- Hybrid commands coupling pure-lifted writes, spatial cells, loan checkout,
amortized task-burst submission, and `< ω^ω`-bounded wavefront steps. -/
inductive HybridCmdV2026 where
  | pureLiftSafe (lid : Pos4) (delta : Nat)
  | updateSpatialCell (cid : Pos4) (newVal : Nat)
  | checkoutLoan (lid : Pos4) (scopeId : Nat)
  | submitTaskBurst (rank remYields : Nat) (lid : Pos4) (scopeId writeDelta : Nat)
  | poolWavefrontStep (pol : SpawnPolicy)

/-- Outcome of evaluating a `HybridCmdV2026` against a `WavefrontWorldV2026`. -/
inductive HybridOutV2026 where
  | returned (wOut : WavefrontWorldV2026)
  | faultInvalidSpawn
  | faultLoanViolation

/-- Fail-closed pure-lifted write on an `.activeMut` loan directly into
`V2026_06_01.MirSemantics.Memory`. -/
def execPureLiftSafeV2026 (lid : Pos4) (delta : Nat) (w : WavefrontWorldV2026) :
    HybridOutV2026 :=
  match wfCanPureAccessLoan w.loans lid true with
  | false => .faultLoanViolation
  | true =>
    match wfFindLoan lid w.loans with
    | none => .faultLoanViolation
    | some e =>
      let newVal := wrapU32 (e.val + delta)
      match v2026SubLensPut e.lens w.mem (wfEncodeU32LeRawBytes newVal) with
      | none => .faultLoanViolation
      | some memOut =>
        .returned {
          mem := memOut
          loans := wfSetLoanEntryAt w.loans lid .activeMut newVal
          cells := w.cells
          fifoQueue := w.fifoQueue
          stealDeque := w.stealDeque
          nextTaskId := w.nextTaskId
          completedCount := w.completedCount
          stepCount := w.stepCount
        }

/-- Fail-closed spatial cell update. -/
def execUpdateSpatialCellV2026 (cid : Pos4) (newVal : Nat) (w : WavefrontWorldV2026) :
    HybridOutV2026 :=
  match ResTrie.getBits (pos4ToList cid) w.cells with
  | none => .faultLoanViolation
  | some _ =>
    .returned {
      mem := w.mem
      loans := w.loans
      cells := ResTrie.modifyBits (pos4ToList cid) (fun _ => some newVal) w.cells
      fifoQueue := w.fifoQueue
      stealDeque := w.stealDeque
      nextTaskId := w.nextTaskId
      completedCount := w.completedCount
      stepCount := w.stepCount
    }

/-- Fail-closed checkout transitioning an `.activeMut` loan with no queued tasks
into `.spatialCheckedOut scopeId`. -/
def execCheckoutLoanV2026 (lid : Pos4) (scopeId : Nat) (w : WavefrontWorldV2026) :
    HybridOutV2026 :=
  match (!anyTaskHasLoan lid w.fifoQueue && !anyTaskHasLoan lid w.stealDeque) with
  | false => .faultLoanViolation
  | true =>
    match wfFindLoan lid w.loans with
    | none => .faultLoanViolation
    | some e =>
      match e.phase with
      | .activeMut =>
        .returned {
          mem := w.mem
          loans := wfSetLoanEntryAt w.loans lid (.spatialCheckedOut scopeId) e.val
          cells := w.cells
          fifoQueue := w.fifoQueue
          stealDeque := w.stealDeque
          nextTaskId := w.nextTaskId
          completedCount := w.completedCount
          stepCount := w.stepCount
        }
      | .frozen | .spatialCheckedOut _ | .ended => .faultLoanViolation

/-- Fail-closed task-burst submission targeting a checked-out loan. -/
def execSubmitTaskBurstV2026 (rank remYields : Nat) (lid : Pos4)
    (scopeId writeDelta : Nat) (w : WavefrontWorldV2026) : HybridOutV2026 :=
  match wfFindLoan lid w.loans with
  | none => .faultLoanViolation
  | some e =>
    match loanPhaseMatchesScope e.phase scopeId with
    | false => .faultLoanViolation
    | true =>
      let newTask :=
        WorkerTask.mk w.nextTaskId rank remYields lid scopeId writeDelta
      .returned {
        mem := w.mem
        loans := w.loans
        cells := w.cells
        fifoQueue := newTask :: w.fifoQueue
        stealDeque := w.stealDeque
        nextTaskId := w.nextTaskId + 1
        completedCount := w.completedCount
        stepCount := w.stepCount + 1
      }

/-- Fail-closed execution of one popped wavefront task over `V2026_06_01` `Memory`. -/
def execWavefrontPoppedV2026 (pol : SpawnPolicy) (hd : WorkerTask)
    (remFifo remSteal : List WorkerTask) (w : WavefrontWorldV2026) : HybridOutV2026 :=
  let polRes := pol hd.rank
  let k := polRes.1
  let childRank := polRes.2.1
  let childYields := polRes.2.2
  match spawnAdmissible hd.rank k childRank with
  | false => .faultInvalidSpawn
  | true =>
    let children :=
      mkWorkers w.nextTaskId k childRank childYields hd.loanId hd.scopeId hd.writeDelta
    let nextSteal := children ++ remSteal
    match hd.remYields with
    | y' + 1 =>
      let hdNext :=
        WorkerTask.mk hd.taskId hd.rank y' hd.loanId hd.scopeId hd.writeDelta
      .returned {
        mem := w.mem
        loans := w.loans
        cells := w.cells
        fifoQueue := remFifo ++ [hdNext]
        stealDeque := nextSteal
        nextTaskId := w.nextTaskId + k
        completedCount := w.completedCount
        stepCount := w.stepCount + 1
      }
    | 0 =>
      match k with
      | k' + 1 =>
        .returned {
          mem := w.mem
          loans := w.loans
          cells := w.cells
          fifoQueue := remFifo
          stealDeque := nextSteal
          nextTaskId := w.nextTaskId + (k' + 1)
          completedCount := w.completedCount + 1
          stepCount := w.stepCount + 1
        }
      | 0 =>
        match wfFindLoan hd.loanId w.loans with
        | none => .faultLoanViolation
        | some e =>
          match loanPhaseMatchesScope e.phase hd.scopeId with
          | false => .faultLoanViolation
          | true =>
            let newVal := wrapU32 (e.val + hd.writeDelta)
            match v2026SubLensPut e.lens w.mem (wfEncodeU32LeRawBytes newVal) with
            | none => .faultLoanViolation
            | some memOut =>
              let stillInFlight :=
                anyTaskHasLoanScope hd.loanId hd.scopeId remFifo ||
                anyTaskHasLoanScope hd.loanId hd.scopeId remSteal
              let nextPh := match stillInFlight with
                | true => WfLoanPhase.spatialCheckedOut hd.scopeId
                | false => WfLoanPhase.activeMut
              .returned {
                mem := memOut
                loans := wfSetLoanEntryAt w.loans hd.loanId nextPh newVal
                cells := w.cells
                fifoQueue := remFifo
                stealDeque := remSteal
                nextTaskId := w.nextTaskId
                completedCount := w.completedCount + 1
                stepCount := w.stepCount + 1
              }

/-- Top-level fail-closed evaluator for `HybridCmdV2026` over `WavefrontWorldV2026`. -/
def evalHybridCmdV2026 (cmd : HybridCmdV2026) (w : WavefrontWorldV2026) : HybridOutV2026 :=
  match cmd with
  | .pureLiftSafe lid delta => execPureLiftSafeV2026 lid delta w
  | .updateSpatialCell cid newVal => execUpdateSpatialCellV2026 cid newVal w
  | .checkoutLoan lid scopeId => execCheckoutLoanV2026 lid scopeId w
  | .submitTaskBurst rank remYields lid scopeId writeDelta =>
    execSubmitTaskBurstV2026 rank remYields lid scopeId writeDelta w
  | .poolWavefrontStep pol =>
    match w.fifoQueue with
    | hd :: ft => execWavefrontPoppedV2026 pol hd ft w.stealDeque w
    | [] =>
      match w.stealDeque with
      | [] => .faultInvalidSpawn
      | hd :: stTail => execWavefrontPoppedV2026 pol hd [] stTail w

/-- Three-mode `< ω^ω` ordinal step classification. -/
inductive OrdStepKind where
  | preserve
  | strictDescent
  | amortized (ordSpent : CnfOrd)

/-- Checks that any `.amortized ordSpent` payload is a canonical CNF ordinal. -/
def ordStepKindCanonical (k : OrdStepKind) : Bool :=
  match k with
  | .preserve | .strictDescent => true
  | .amortized ordSpent => isCanonicalCnf ordSpent

/-- Relates `worldMeasureV2026 wIn` and `worldMeasureV2026 wOut` by `OrdStepKind`. -/
def OrdRelStepV2026 (k : OrdStepKind) (wIn wOut : WavefrontWorldV2026) : Prop :=
  match k with
  | .preserve => worldMeasureV2026 wOut = worldMeasureV2026 wIn
  | .strictDescent => cnfLt (worldMeasureV2026 wOut) (worldMeasureV2026 wIn) = true
  | .amortized ordSpent =>
    cnfLt (worldMeasureV2026 wOut) (cnfAddOrd ordSpent (worldMeasureV2026 wIn)) = true

/-- Frame-preserving view-indexed relational weakest precondition over
`evalHybridCmdV2026` and `SpatialPcm` (`VProp`), conserving `extractPoolCap` and
establishing `OrdRelStepV2026` and `Firewall`-shielded `WorldMatchesV2026`. -/
structure VSepWpOrdRelV2026 (cmd : HybridCmdV2026) (ordKind : OrdStepKind)
    (worldGuard : WavefrontWorldV2026 → Prop)
    (Pre : VProp) (Post : WavefrontWorldV2026 → VProp) : Prop where
  canonKind : ordStepKindCanonical ordKind = true
  run : ∀ (v : View) (F : VProp) (rIn : ResTrie ResElem) (wIn : WavefrontWorldV2026),
    worldGuard wIn →
    (vsep Pre F).holds v rIn →
    WorldMatchesV2026 v rIn wIn →
    ∃ (wOut : WavefrontWorldV2026) (rOut : ResTrie ResElem) (vOut : View),
      evalHybridCmdV2026 cmd wIn = .returned wOut ∧
      ViewLe v vOut ∧
      extractPoolCap rOut = extractPoolCap rIn ∧
      (vsep (Post wOut) F).holds vOut rOut ∧
      WorldMatchesV2026 vOut rOut wOut ∧
      OrdRelStepV2026 ordKind wIn wOut

/-- Spatial frame rule for `VSepWpOrdRelV2026` (`[]` zero axioms). -/
theorem vsepWpOrdRelV2026_frame (cmd : HybridCmdV2026) (ordKind : OrdStepKind)
    (worldGuard : WavefrontWorldV2026 → Prop)
    (Pre Frame : VProp) (Post : WavefrontWorldV2026 → VProp)
    (hWp : VSepWpOrdRelV2026 cmd ordKind worldGuard Pre Post) :
    VSepWpOrdRelV2026 cmd ordKind worldGuard (vsep Pre Frame)
      (fun wOut => vsep (Post wOut) Frame) where
  canonKind := hWp.canonKind
  run v F rIn wIn hG hPre hMatch := by
    have hAssocIn : (vsep Pre (vsep Frame F)).holds v rIn :=
      (vsep_assoc_lr Pre Frame F).imp v rIn hPre
    cases hWp.run v (vsep Frame F) rIn wIn hG hAssocIn hMatch with
    | intro wOut hw =>
      cases hw with
      | intro rOut hr =>
        cases hr with
        | intro vOut hv =>
          exact ⟨wOut, rOut, vOut, hv.1, hv.2.1, hv.2.2.1,
            (vsep_assoc_rl (Post wOut) Frame F).imp vOut rOut hv.2.2.2.1,
            hv.2.2.2.2.1, hv.2.2.2.2.2⟩

/-- Witnesses that loan `lid` is in `.activeMut` phase at `subL` with value `vIn`. -/
def ActivePureLoanAtV2026 (lid : Pos4) (subL : V2026SubLens) (vIn : Nat)
    (w : WavefrontWorldV2026) : Prop :=
  ∃ e : WfLoanEntryV2026,
    wfFindLoan lid w.loans = some e ∧
    e.phase = .activeMut ∧
    e.lens = subL ∧
    e.val = vIn

private theorem pureLiftSafe_step_core
    (lid : Pos4) (subL : V2026SubLens) (vIn delta : Nat)
    (v : View) (rIn : ResTrie ResElem) (wIn : WavefrontWorldV2026)
    (hAct : ActivePureLoanAtV2026 lid subL vIn wIn)
    (hM : WorldMatchesV2026 v rIn wIn) :
    ∃ wOut : WavefrontWorldV2026,
      evalHybridCmdV2026 (.pureLiftSafe lid delta) wIn = .returned wOut ∧
      WorldMatchesV2026 v rIn wOut ∧
      OrdRelStepV2026 .preserve wIn wOut ∧
      wOut.fifoQueue = wIn.fifoQueue ∧
      wOut.stealDeque = wIn.stealDeque ∧
      v2026SubLensPut subL wIn.mem (wfEncodeU32LeRawBytes (wrapU32 (vIn + delta))) =
        some wOut.mem := by
  cases hAct with
  | intro e he =>
    have hFind := he.1
    have hPh := he.2.1
    have hLens := he.2.2.1
    have hVal := he.2.2.2
    have hLive : loanPhaseIsLive e.phase = true := by rw [hPh]; rfl
    have hSynced := wfFindLoan_synced_live_props wIn.loans wIn.mem lid e
      hM.loansMemOk hFind hLive
    have hCan : wfCanPureAccessLoan wIn.loans lid true = true := by
      dsimp only [wfCanPureAccessLoan]
      rw [hFind]; dsimp only; rw [hPh]
    let newVal := wrapU32 (vIn + delta)
    have hLenSl : (wfEncodeU32LeRawBytes newVal).length = e.lens.size := by
      rw [wfEncodeU32LeRawBytes_length, hSynced.2.1]
    cases v2026SubLens_put_succeeds_of_get e.lens wIn.mem (wfEncodeU32LeAbsBytes e.val)
        (wfEncodeU32LeRawBytes newVal) hSynced.2.2.2 hLenSl with
    | intro memOut hPut =>
      let wOut : WavefrontWorldV2026 := {
        mem := memOut
        loans := wfSetLoanEntryAt wIn.loans lid .activeMut newVal
        cells := wIn.cells
        fifoQueue := wIn.fifoQueue
        stealDeque := wIn.stealDeque
        nextTaskId := wIn.nextTaskId
        completedCount := wIn.completedCount
        stepCount := wIn.stepCount
      }
      have hEval : evalHybridCmdV2026 (.pureLiftSafe lid delta) wIn =
          .returned wOut := by
        dsimp only [evalHybridCmdV2026, execPureLiftSafeV2026]
        rw [hCan, hFind]
        dsimp only
        rw [hVal]
        change (match v2026SubLensPut e.lens wIn.mem (wfEncodeU32LeRawBytes newVal) with
          | none => HybridOutV2026.faultLoanViolation
          | some m' => _) = _
        rw [hPut]
      have hSyncOut : LoansSyncedWithMemV2026 wOut.loans wOut.mem :=
        loansSyncedWithMemV2026_set_and_put wIn.loans wIn.mem memOut lid e
          .activeMut newVal hM.loansMemOk hFind rfl
          (Eq.symm (wrapU32_idem (vIn + delta))) hPut
      have hQIn := hM.queueLoansOk
      have hNoF := not_anyTaskHasLoan_of_activeMut lid e wIn.fifoQueue
        wIn.loans hFind hPh (bandLeft hQIn)
      have hNoS := not_anyTaskHasLoan_of_activeMut lid e wIn.stealDeque
        wIn.loans hFind hPh (bandRight hQIn)
      have hQOut : QueueMatchesLoansV2026 wOut :=
        bandIntro
          (queueMatchesLoansBool_wfSetLoanEntryAt_of_not_hasLoan wIn.fifoQueue
            wIn.loans lid .activeMut newVal hNoF (bandLeft hQIn))
          (queueMatchesLoansBool_wfSetLoanEntryAt_of_not_hasLoan wIn.stealDeque
            wIn.loans lid .activeMut newVal hNoS (bandRight hQIn))
      have hMeasEq : worldMeasureV2026 wOut = worldMeasureV2026 wIn := rfl
      have hPoolOkOut : checkWorldMatchesPoolBool rIn wOut = true := by
        dsimp only [checkWorldMatchesPoolBool]
        rw [hMeasEq]
        exact hM.poolDebtOk
      have hMOut : WorldMatchesV2026 v rIn wOut :=
        WorldMatchesV2026.mk hM.viewOk hSyncOut hQOut hPoolOkOut hM.cellOk (fun lid2 => by
          have hCk := hM.checkedLoanOk lid2
          cases hG : ResTrie.getBits (checkedLoanPath lid2) rIn with
          | none => exact True.intro
          | some elem =>
            rw [hG] at hCk
            cases elem with
            | pool _ | debt _ | cell _ => exact hCk
            | checkedOutLoan sid lv =>
              cases hCk.2 with
              | intro e2 he2 =>
                cases hEqId : Pos4.beq lid lid2 with
                | true =>
                  have hSameId := pos4_eq_of_beq lid lid2 hEqId
                  rw [← hSameId] at he2
                  rw [hFind] at he2
                  injection he2.1 with hSameE
                  rw [← hSameE] at he2
                  have hBad : WfLoanPhase.activeMut = WfLoanPhase.spatialCheckedOut sid :=
                    Eq.trans hPh.symm he2.2.1
                  nomatch hBad
                | false =>
                  exact ⟨hCk.1, ⟨e2,
                    Eq.trans (wfFindLoan_wfSetLoanEntryAt_ne wIn.loans lid lid2
                      .activeMut newVal hEqId) he2.1,
                    he2.2⟩⟩)
      have hPutSub :
          v2026SubLensPut subL wIn.mem (wfEncodeU32LeRawBytes newVal) =
            some wOut.mem := by
        rw [← hLens]; exact hPut
      exact ⟨wOut, hEval, hMOut, hMeasEq, rfl, rfl, hPutSub⟩

/-- Universal frame-preserving weakest precondition for `.pureLiftSafe` over
unmodified `V2026_06_01.MirSemantics.Memory` (`[propext]`). -/
theorem vsepWpOrdRelV2026_pure_fastpath
    (lid : Pos4) (subL : V2026SubLens) (vIn delta : Nat) :
    VSepWpOrdRelV2026 (.pureLiftSafe lid delta) .preserve
      (ActivePureLoanAtV2026 lid subL vIn) vemp (fun _ => vemp) ∧
    (∀ (v : View) (F : VProp) (rIn : ResTrie ResElem) (wIn : WavefrontWorldV2026),
      ActivePureLoanAtV2026 lid subL vIn wIn →
      (vsep vemp F).holds v rIn →
      WorldMatchesV2026 v rIn wIn →
      ∃ wOut : WavefrontWorldV2026,
        evalHybridCmdV2026 (.pureLiftSafe lid delta) wIn = .returned wOut ∧
        WorldMatchesV2026 v rIn wOut ∧
        OrdRelStepV2026 .preserve wIn wOut ∧
        wOut.fifoQueue = wIn.fifoQueue ∧
        wOut.stealDeque = wIn.stealDeque ∧
        v2026SubLensGet subL wOut.mem =
          some (wfEncodeU32LeAbsBytes (wrapU32 (vIn + delta))) ∧
        (∀ otherL : V2026SubLens,
          v2026LensDisjoint subL otherL = true →
          v2026SubLensGet otherL wOut.mem = v2026SubLensGet otherL wIn.mem)) := by
  let wpInst :
      VSepWpOrdRelV2026 (.pureLiftSafe lid delta) .preserve
        (ActivePureLoanAtV2026 lid subL vIn) vemp (fun _ => vemp) :=
    VSepWpOrdRelV2026.mk rfl (fun v F rIn wIn hG hPre hM => by
      cases pureLiftSafe_step_core lid subL vIn delta v rIn wIn hG hM with
      | intro wOut hw =>
        exact ⟨wOut, rIn, v, hw.1, viewLe_refl v, rfl, hPre, hw.2.1, hw.2.2.1⟩)
  refine ⟨wpInst, ?_⟩
  intro v _ rIn wIn hAct _ hM
  cases pureLiftSafe_step_core lid subL vIn delta v rIn wIn hAct hM with
  | intro wOut hw =>
    exact ⟨wOut, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1,
      v2026SubLens_put_get_u32 subL wIn.mem wOut.mem (wrapU32 (vIn + delta)) hw.2.2.2.2.2,
      fun otherL hDisj =>
        v2026SubLens_get_put_disjoint subL otherL wIn.mem wOut.mem _ hDisj hw.2.2.2.2.2⟩

/-- Updates spatial cell `cid` from `oldVal` to `newVal` under
`cellCapProp cid ∗ cellAuthProp cid oldVal` (`[]` zero axioms). -/
theorem vsepWpOrdRelV2026_updateSpatialCell (cid : Pos4) (oldVal newVal : Nat) :
    VSepWpOrdRelV2026 (.updateSpatialCell cid newVal) .preserve (fun _ => True)
      (vsep (cellCapProp cid) (cellAuthProp cid oldVal))
      (fun _ => vsep (cellCapProp cid) (cellAuthProp cid newVal)) :=
  VSepWpOrdRelV2026.mk rfl (fun v F rIn wIn _ hPre hM => by
    cases hPre with
    | intro rPre hrP =>
      cases hrP with
      | intro rF hPF =>
        cases hPF.2.1 with
        | intro rCap hrC =>
          cases hrC with
          | intro rAuth hCA =>
            cases hCA.2.1.holds with
            | intro fC hfC =>
              cases hCA.2.2.holds with
              | intro fA hfA =>
                let tCap := singleRes (cellPath cid) (.cell .capOnly)
                let tAuthOld := singleRes (cellPath cid) (.cell (.authOnly oldVal))
                let tFullOld := singleRes (cellPath cid) (.cell (.capAndAuth oldVal))
                let tAuthNew := singleRes (cellPath cid) (.cell (.authOnly newVal))
                let tFullNew := singleRes (cellPath cid) (.cell (.capAndAuth newVal))
                cases resTrieMerge_assoc tCap fC rAuth rCap rPre hfC hCA.1 with
                | intro x1 hx1 =>
                  have hx1Comm : resTrieMerge rAuth fC = some x1 :=
                    Eq.trans (resTrieMerge_comm rAuth fC) hx1.1
                  cases resTrieMerge_assoc tAuthOld fA fC rAuth x1 hfA hx1Comm with
                  | intro fCA hfCA =>
                    cases resTrieMerge_assoc_rl tCap tAuthOld fCA x1 rPre hfCA.2 hx1.2 with
                    | intro rComb hrComb =>
                      rw [singleRes_cell_cap_auth_merge cid oldVal] at hrComb
                      injection hrComb.1 with hCombEq
                      rw [← hCombEq] at hrComb
                      cases resTrieMerge_assoc tFullOld fCA rF rPre rIn hrComb.2 hPF.1 with
                      | intro rRest hrRest =>
                        have hGIn :=
                          resTrie_getBits_resTrieMerge (cellPath cid) tFullOld
                            rRest rIn rfl hrRest.2
                        rw [singleRes_getBits_same] at hGIn
                        have hCellInOk := hM.cellOk cid
                        have hCellRIn : ResTrie.getBits (cellPath cid) rIn =
                            some (.cell (.capAndAuth oldVal)) := by
                          cases hGr : ResTrie.getBits (cellPath cid) rRest with
                          | none =>
                            rw [hGr] at hGIn
                            dsimp only [optOp] at hGIn
                            injection hGIn with hEqG
                            exact Eq.symm hEqG
                          | some er =>
                            rw [hGr] at hGIn
                            cases er with
                            | pool _ | debt _ | checkedOutLoan _ _ =>
                              dsimp only [optOp, resMerge] at hGIn; nomatch hGIn
                            | cell cf =>
                              cases cf with
                              | authOnly _ | capAndAuth _ =>
                                dsimp only [optOp, resMerge, cellFragMerge] at hGIn
                                nomatch hGIn
                              | capOnly =>
                                dsimp only [optOp, resMerge, cellFragMerge] at hGIn
                                injection hGIn with hEqG
                                exact Eq.symm hEqG
                        rw [hCellRIn] at hCellInOk
                        dsimp only at hCellInOk
                        let wOut : WavefrontWorldV2026 := {
                          mem := wIn.mem
                          loans := wIn.loans
                          cells := ResTrie.modifyBits (pos4ToList cid)
                            (fun _ => some newVal) wIn.cells
                          fifoQueue := wIn.fifoQueue
                          stealDeque := wIn.stealDeque
                          nextTaskId := wIn.nextTaskId
                          completedCount := wIn.completedCount
                          stepCount := wIn.stepCount
                        }
                        have hEval : evalHybridCmdV2026 (.updateSpatialCell cid newVal) wIn =
                            .returned wOut := by
                          dsimp only [evalHybridCmdV2026, execUpdateSpatialCellV2026]
                          rw [hCellInOk]
                        let rOut :=
                          ResTrie.modifyBits (cellPath cid)
                            (fun _ => some (.cell (.capAndAuth newVal))) rIn
                        have hMergeNew : resTrieMerge tFullNew rRest = some rOut :=
                          resTrieMergeFuel_singleRes_capAndAuth_swap resFuel
                            (cellPath cid) oldVal newVal rRest rIn rfl hrRest.2
                        cases resTrieMerge_assoc_rl tFullNew fCA rF rRest rOut
                            hrRest.1 hMergeNew with
                        | intro rPreNew hrPreNew =>
                          have hSplitNew := singleRes_cell_cap_auth_merge cid newVal
                          have hPostOut : (vsep (vsep (cellCapProp cid)
                              (cellAuthProp cid newVal)) F).holds v rOut :=
                            ⟨rPreNew, rF, hrPreNew.2,
                              ⟨tCap, rPreNew, ?_, resTrieSub_refl tCap, ?_⟩,
                              hPF.2.2⟩
                          · have hPoolOut : checkWorldMatchesPoolBool rOut wOut = true := by
                              dsimp only [checkWorldMatchesPoolBool,
                                extractPoolCap, extractDebtCap]
                              rw [resTrie_getBits_modifyBits_ne (cellPath cid) poolPath rfl rfl,
                                resTrie_getBits_modifyBits_ne (cellPath cid) debtPath rfl rfl]
                              exact hM.poolDebtOk
                            have hMOut : WorldMatchesV2026 v rOut wOut :=
                              WorldMatchesV2026.mk hM.viewOk hM.loansMemOk
                                hM.queueLoansOk hPoolOut
                                (fun cid2 => by
                                  cases hEqC : Pos4.beq cid cid2 with
                                  | true =>
                                    have hSameC := pos4_eq_of_beq cid cid2 hEqC
                                    rw [← hSameC]
                                    dsimp only [rOut, wOut]
                                    rw [resTrie_getBits_modifyBits_same,
                                      resTrie_getBits_modifyBits_same]
                                  | false =>
                                    have hNeCellPath :
                                        listBoolBeq (cellPath cid) (cellPath cid2) = false := by
                                      dsimp only [cellPath, listBoolBeq, Bool.and]
                                      exact hEqC
                                    dsimp only [rOut, wOut]
                                    rw [resTrie_getBits_modifyBits_ne (cellPath cid)
                                      (cellPath cid2) rfl hNeCellPath]
                                    have hPrev := hM.cellOk cid2
                                    cases hGc2 : ResTrie.getBits (cellPath cid2) rIn with
                                    | none => exact True.intro
                                    | some elem2 =>
                                      rw [hGc2] at hPrev
                                      cases elem2 with
                                      | pool _ | debt _ | checkedOutLoan _ _ => exact hPrev
                                      | cell _ =>
                                        dsimp only
                                        rw [resTrie_getBits_modifyBits_ne
                                          (pos4ToList cid) (pos4ToList cid2) rfl hEqC]
                                        exact hPrev)
                                (fun lid2 => by
                                  have hNeChk :
                                      listBoolBeq (cellPath cid) (checkedLoanPath lid2) = false := rfl
                                  dsimp only [rOut, wOut]
                                  rw [resTrie_getBits_modifyBits_ne (cellPath cid)
                                    (checkedLoanPath lid2) rfl hNeChk]
                                  exact hM.checkedLoanOk lid2)
                            have hPoolCapEq : extractPoolCap rOut = extractPoolCap rIn := by
                              dsimp only [extractPoolCap, rOut]
                              rw [resTrie_getBits_modifyBits_ne (cellPath cid) poolPath rfl rfl]
                            exact ⟨wOut, rOut, v, hEval, viewLe_refl v,
                              hPoolCapEq, hPostOut, hMOut, rfl⟩
                          · have hIdemCap : resTrieMerge tCap tFullNew = some tFullNew := by
                              cases cid with
                              | mk b0 r1 =>
                                cases r1 with
                                | mk b1 r2 =>
                                  cases r2 with
                                  | mk b2 b3 =>
                                    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> rfl
                            cases resTrieMerge_assoc tCap tFullNew fCA tFullNew
                                rPreNew hIdemCap hrPreNew.1 with
                            | intro z hz =>
                              rw [hrPreNew.1] at hz
                              injection hz.1 with hzEq
                              rw [← hzEq] at hz
                              exact hz.2
                          · cases resTrieMerge_assoc tAuthNew tCap fCA tFullNew rPreNew
                                (Eq.trans (resTrieMerge_comm tAuthNew tCap) hSplitNew)
                                hrPreNew.1 with
                            | intro fRest hfRest =>
                              exact ResTrieSub.mk ⟨fRest, hfRest.2⟩)

/-- Precondition for `.checkoutLoan`: `ActivePureLoanAtV2026 lid subL vIn w` with
zero queued tasks referencing `lid`. -/
def CheckoutLoanGuardV2026 (lid : Pos4) (subL : V2026SubLens) (vIn : Nat)
    (w : WavefrontWorldV2026) : Prop :=
  ActivePureLoanAtV2026 lid subL vIn w ∧
  (!anyTaskHasLoan lid w.fifoQueue && !anyTaskHasLoan lid w.stealDeque) = true

/-- Checks out `.activeMut` loan `lid` into `.spatialCheckedOut scopeId`,
minting `checkedOutLoanProp lid scopeId vIn` (`[]` zero axioms). -/
theorem vsepWpOrdRelV2026_checkoutLoan (lid : Pos4) (subL : V2026SubLens)
    (vIn scopeId : Nat) :
    VSepWpOrdRelV2026 (.checkoutLoan lid scopeId) .preserve
      (CheckoutLoanGuardV2026 lid subL vIn)
      vemp (fun _ => checkedOutLoanProp lid scopeId vIn) :=
  VSepWpOrdRelV2026.mk rfl (fun v F rIn wIn hG hPre hM => by
    have hF : F.holds v rIn := vsep_vemp_elim v F rIn hPre
    cases hG.1 with
    | intro e he =>
      have hFind := he.1
      have hPh := he.2.1
      have hVal := he.2.2.2
      have hRNone : ResTrie.getBits (checkedLoanPath lid) rIn = none := by
        have hCk := hM.checkedLoanOk lid
        cases hGr : ResTrie.getBits (checkedLoanPath lid) rIn with
        | none => rfl
        | some elem =>
          rw [hGr] at hCk
          cases elem with
          | pool _ | debt _ | cell _ => exact False.elim hCk
          | checkedOutLoan sid _ =>
            cases hCk.2 with
            | intro e2 he2 =>
              rw [hFind] at he2
              injection he2.1 with hSame
              rw [← hSame] at he2
              have hBad : WfLoanPhase.activeMut = WfLoanPhase.spatialCheckedOut sid :=
                Eq.trans hPh.symm he2.2.1
              nomatch hBad
      let tLoan := singleRes (checkedLoanPath lid) (.checkedOutLoan scopeId vIn)
      let rOut := ResTrie.modifyBits (checkedLoanPath lid)
        (fun _ => some (.checkedOutLoan scopeId vIn)) rIn
      have hMergeOut : resTrieMerge tLoan rIn = some rOut :=
        resTrieMergeFuel_singleRes_of_getBits_none resFuel (checkedLoanPath lid)
          (.checkedOutLoan scopeId vIn) rIn rfl hRNone
      let wOut : WavefrontWorldV2026 := {
        mem := wIn.mem
        loans := wfSetLoanEntryAt wIn.loans lid (.spatialCheckedOut scopeId) e.val
        cells := wIn.cells
        fifoQueue := wIn.fifoQueue
        stealDeque := wIn.stealDeque
        nextTaskId := wIn.nextTaskId
        completedCount := wIn.completedCount
        stepCount := wIn.stepCount
      }
      have hEval : evalHybridCmdV2026 (.checkoutLoan lid scopeId) wIn = .returned wOut := by
        dsimp only [evalHybridCmdV2026, execCheckoutLoanV2026]
        rw [hG.2, hFind]
        dsimp only
        rw [hPh]
      have hLiveOld : loanPhaseIsLive e.phase = true := by rw [hPh]; rfl
      have hSyncOut : LoansSyncedWithMemV2026 wOut.loans wOut.mem :=
        loansSyncedWithMemV2026_setPhase_sameVal wIn.loans wIn.mem lid e
          (.spatialCheckedOut scopeId) hM.loansMemOk hFind hLiveOld rfl
      have hQIn := hM.queueLoansOk
      have hQOut : QueueMatchesLoansV2026 wOut :=
        bandIntro
          (queueMatchesLoansBool_wfSetLoanEntryAt_of_not_hasLoan wIn.fifoQueue wIn.loans
            lid (.spatialCheckedOut scopeId) e.val (trueOfBnotTrue (bandLeft hG.2))
            (bandLeft hQIn))
          (queueMatchesLoansBool_wfSetLoanEntryAt_of_not_hasLoan wIn.stealDeque wIn.loans
            lid (.spatialCheckedOut scopeId) e.val (trueOfBnotTrue (bandRight hG.2))
            (bandRight hQIn))
      have hPoolOut : checkWorldMatchesPoolBool rOut wOut = true := by
        dsimp only [checkWorldMatchesPoolBool, extractPoolCap, extractDebtCap, rOut, wOut]
        rw [resTrie_getBits_modifyBits_ne (checkedLoanPath lid) poolPath rfl rfl,
          resTrie_getBits_modifyBits_ne (checkedLoanPath lid) debtPath rfl rfl]
        exact hM.poolDebtOk
      have hMOut : WorldMatchesV2026 v rOut wOut :=
        WorldMatchesV2026.mk hM.viewOk hSyncOut hQOut hPoolOut
          (fun cid => by
            dsimp only [rOut, wOut]
            rw [resTrie_getBits_modifyBits_ne (checkedLoanPath lid) (cellPath cid) rfl rfl]
            exact hM.cellOk cid)
          (fun lid2 => by
            cases hEqId : Pos4.beq lid lid2 with
            | true =>
              have hSameId := pos4_eq_of_beq lid lid2 hEqId
              rw [← hSameId]
              dsimp only [rOut, wOut]
              rw [resTrie_getBits_modifyBits_same]
              exact ⟨hG.2, ⟨⟨e.id, .spatialCheckedOut scopeId, e.lens, e.val⟩,
                wfFindLoan_wfSetLoanEntryAt_same wIn.loans lid
                  (.spatialCheckedOut scopeId) e.val e hFind,
                rfl, hVal⟩⟩
            | false =>
              have hNePath :
                  listBoolBeq (checkedLoanPath lid) (checkedLoanPath lid2) = false := by
                dsimp only [checkedLoanPath, listBoolBeq, Bool.and]
                exact hEqId
              dsimp only [rOut, wOut]
              rw [resTrie_getBits_modifyBits_ne (checkedLoanPath lid)
                (checkedLoanPath lid2) rfl hNePath]
              have hPrev := hM.checkedLoanOk lid2
              cases hGl2 : ResTrie.getBits (checkedLoanPath lid2) rIn with
              | none => exact True.intro
              | some elem2 =>
                rw [hGl2] at hPrev
                cases elem2 with
                | pool _ | debt _ | cell _ => exact hPrev
                | checkedOutLoan _ _ =>
                  cases hPrev.2 with
                  | intro e2 he2 =>
                    exact ⟨hPrev.1, ⟨e2,
                      Eq.trans (wfFindLoan_wfSetLoanEntryAt_ne wIn.loans lid lid2
                        (.spatialCheckedOut scopeId) e.val hEqId) he2.1,
                      he2.2⟩⟩)
      have hPoolCapEq : extractPoolCap rOut = extractPoolCap rIn := by
        dsimp only [extractPoolCap, rOut]
        rw [resTrie_getBits_modifyBits_ne (checkedLoanPath lid) poolPath rfl rfl]
      exact ⟨wOut, rOut, v, hEval, viewLe_refl v, hPoolCapEq,
        ⟨tLoan, rIn, hMergeOut, resTrieSub_refl tLoan, hF⟩, hMOut, rfl⟩)

/-! ### Amortized Ordinal-Debt Burst & Strict `< ω^ω` Wavefront Step Descent -/

private theorem cnfNatAdd_cnfNorm_right (xs ys : CnfOrd) :
    cnfNatAdd xs (cnfNorm ys) = cnfNatAdd xs ys :=
  cnf_eq_of_coeff_eq _ _ (isCanonicalCnf_cnfNatAdd xs (cnfNorm ys))
    (isCanonicalCnf_cnfNatAdd xs ys)
    (fun q => Eq.trans (cnfCoeffAt_cnfNatAdd q xs (cnfNorm ys))
      (Eq.trans (congrArg (Nat.add (cnfCoeffAt q xs)) (cnfCoeffAt_cnfNorm q ys))
        (Eq.symm (cnfCoeffAt_cnfNatAdd q xs ys))))

/-- Universal amortized `< ω^ω` ordinal-debt spending law for `.submitTaskBurst`
(`[]` zero axioms). -/
theorem vsepWpOrdRelV2026_submitTaskBurst_amortized_growth
    (rank remYields : Nat) (lid : Pos4) (scopeId writeDelta lv : Nat)
    (ordSpent : CnfOrd)
    (hCanSpent : isCanonicalCnf ordSpent = true)
    (hBudget : cnfLt (burstTaskDelta rank remYields) ordSpent = true) :
    VSepWpOrdRelV2026 (.submitTaskBurst rank remYields lid scopeId writeDelta)
      (.amortized ordSpent)
      (fun _ => True)
      (vsep (ordDebtProp ordSpent) (checkedOutLoanProp lid scopeId lv))
      (fun _ => vemp) ∧
    (∀ (wIn wOut : WavefrontWorldV2026),
      evalHybridCmdV2026 (.submitTaskBurst rank remYields lid scopeId writeDelta)
        wIn = .returned wOut →
      cnfLt (worldMeasureV2026 wIn) (worldMeasureV2026 wOut) = true ∧
      cnfLt (worldMeasureV2026 wOut)
        (cnfAddOrd ordSpent (worldMeasureV2026 wIn)) = true) := by
  have hGrowthOfEval : ∀ (wIn wOut : WavefrontWorldV2026),
      evalHybridCmdV2026 (.submitTaskBurst rank remYields lid scopeId writeDelta)
        wIn = .returned wOut →
      cnfLt (worldMeasureV2026 wIn) (worldMeasureV2026 wOut) = true ∧
      cnfLt (worldMeasureV2026 wOut) (cnfAddOrd ordSpent (worldMeasureV2026 wIn)) = true := by
    intro wIn wOut hEv
    dsimp only [evalHybridCmdV2026, execSubmitTaskBurstV2026] at hEv
    cases hFl : wfFindLoan lid wIn.loans with
    | none => rw [hFl] at hEv; nomatch hEv
    | some e =>
      rw [hFl] at hEv; dsimp only at hEv
      cases hSc : loanPhaseMatchesScope e.phase scopeId with
      | false => rw [hSc] at hEv; nomatch hEv
      | true =>
        rw [hSc] at hEv
        injection hEv with hwOut
        have hMeasOut : worldMeasureV2026 wOut =
            cnfAddOrd (burstTaskDelta rank remYields) (worldMeasureV2026 wIn) := by
          rw [← hwOut]
          exact wfTaskMeasure_eq_cnfAddOrd_burstTaskDelta
            (WorkerTask.mk wIn.nextTaskId rank remYields lid scopeId writeDelta)
            (worldMeasureV2026 wIn) (worldMeasureV2026_canonical wIn)
        rw [hMeasOut]
        have hNilAdd : cnfNatAdd [] (worldMeasureV2026 wIn) = worldMeasureV2026 wIn :=
          cnfNorm_eq_of_canonical (worldMeasureV2026 wIn) (worldMeasureV2026_canonical wIn)
        have hStrictGrow :
            cnfLt (worldMeasureV2026 wIn)
              (cnfAddOrd (burstTaskDelta rank remYields) (worldMeasureV2026 wIn)) = true := by
          have hStep := cnfLt_cnfNatAdd_left [] (burstTaskDelta rank remYields)
            (worldMeasureV2026 wIn) rfl (burstTaskDelta_canonical rank remYields)
            (burstTaskDelta_pos rank remYields)
          rw [hNilAdd] at hStep
          exact hStep
        have hAmort := cnfLt_cnfNatAdd_left (burstTaskDelta rank remYields)
          ordSpent (worldMeasureV2026 wIn)
          (burstTaskDelta_canonical rank remYields) hCanSpent hBudget
        exact ⟨hStrictGrow, hAmort⟩
  let wpBurst : VSepWpOrdRelV2026
      (.submitTaskBurst rank remYields lid scopeId writeDelta) (.amortized ordSpent)
      (fun _ => True)
      (vsep (ordDebtProp ordSpent) (checkedOutLoanProp lid scopeId lv))
      (fun _ => vemp) :=
    VSepWpOrdRelV2026.mk hCanSpent (fun v F rIn wIn _ hPre hM => by
      cases hPre with
      | intro r12 hr12 =>
        cases hr12 with
        | intro rF h12F =>
          cases h12F.2.1 with
          | intro rD hrD =>
            cases hrD with
            | intro rL hDL =>
              cases hDL.2.1.holds with
              | intro fD hfD =>
                cases hDL.2.2.holds with
                | intro fL hfL =>
                  let tDebt := singleRes debtPath (.debt ordSpent)
                  let tPool := singleRes poolPath (.pool ordSpent)
                  let tLoan := singleRes (checkedLoanPath lid) (.checkedOutLoan scopeId lv)
                  cases resTrieMerge_assoc tDebt tPool fD (ordDebtTree ordSpent) rD
                      (ordDebtTree_decomp ordSpent) hfD with
                  | intro pfD hpfD =>
                    cases resTrieMerge_assoc tDebt pfD rL rD r12 hpfD.2 hDL.1 with
                    | intro x1 hx1 =>
                      have hx1Comm : resTrieMerge rL pfD = some x1 :=
                        Eq.trans (resTrieMerge_comm rL pfD) hx1.1
                      cases resTrieMerge_assoc tLoan fL pfD rL x1 hfL hx1Comm with
                      | intro x2 hx2 =>
                        cases resTrieMerge_assoc tDebt x1 rF r12 rIn hx1.2 h12F.1 with
                        | intro rMid hrMid =>
                          cases resTrieMerge_assoc tLoan x2 rF x1 rMid hx2.2 hrMid.1 with
                          | intro rOut hrOut =>
                            have hGLMid :=
                              resTrie_getBits_resTrieMerge (checkedLoanPath lid)
                                tLoan rOut rMid rfl hrOut.2
                            rw [singleRes_getBits_same] at hGLMid
                            have hGLIn :=
                              resTrie_getBits_resTrieMerge (checkedLoanPath lid)
                                tDebt rMid rIn rfl hrMid.2
                            rw [singleRes_getBits_ne debtPath (checkedLoanPath lid)
                              _ rfl rfl] at hGLIn
                            dsimp only [optOp] at hGLIn
                            injection hGLIn with hMidEqIn
                            have hROutLoanNone :
                                ResTrie.getBits (checkedLoanPath lid) rOut = none := by
                              cases hGo : ResTrie.getBits (checkedLoanPath lid) rOut with
                              | none => rfl
                              | some _ =>
                                rw [hGo] at hGLMid
                                dsimp only [optOp, resMerge] at hGLMid
                                nomatch hGLMid
                            rw [hROutLoanNone] at hGLMid
                            dsimp only [optOp] at hGLMid
                            injection hGLMid with hMidSome
                            have hRInLoan :
                                ResTrie.getBits (checkedLoanPath lid) rIn =
                                  some (.checkedOutLoan scopeId lv) :=
                              Eq.trans (Eq.symm hMidEqIn) (Eq.symm hMidSome)
                            have hCkIn := hM.checkedLoanOk lid
                            rw [hRInLoan] at hCkIn
                            dsimp only at hCkIn
                            cases hCkIn.2 with
                            | intro e he =>
                              have hMatchSc : loanPhaseMatchesScope e.phase scopeId = true := by
                                rw [he.2.1]
                                dsimp only [loanPhaseMatchesScope]
                                exact natBeq_refl scopeId
                              let newTask :=
                                WorkerTask.mk wIn.nextTaskId rank remYields lid
                                  scopeId writeDelta
                              let wOut : WavefrontWorldV2026 := {
                                mem := wIn.mem
                                loans := wIn.loans
                                cells := wIn.cells
                                fifoQueue := newTask :: wIn.fifoQueue
                                stealDeque := wIn.stealDeque
                                nextTaskId := wIn.nextTaskId + 1
                                completedCount := wIn.completedCount
                                stepCount := wIn.stepCount + 1
                              }
                              have hEval :
                                  evalHybridCmdV2026
                                    (.submitTaskBurst rank remYields lid scopeId writeDelta) wIn =
                                  .returned wOut := by
                                dsimp only [evalHybridCmdV2026, execSubmitTaskBurstV2026]
                                rw [he.1]; dsimp only; rw [hMatchSc]
                              have hGrow := hGrowthOfEval wIn wOut hEval
                              let vOut := bumpView0 v wOut.stepCount
                              have hVLe : ViewLe v vOut :=
                                viewLe_bumpView0 v wOut.stepCount
                                  (natBle_succ_right (viewGet v 0) wIn.stepCount hM.viewOk)
                              have hSubFRout : ResTrieSub rF rOut :=
                                ResTrieSub.mk ⟨x2, Eq.trans (resTrieMerge_comm rF x2) hrOut.1⟩
                              have hPostHold : (vsep vemp F).holds vOut rOut :=
                                vsep_vemp_intro vOut F rOut
                                  (F.upClosed v vOut rF rOut hVLe hSubFRout h12F.2.2)
                              have hPresOther : ∀ (p : List Bool),
                                  p.length = 6 →
                                  listBoolBeq debtPath p = false →
                                  listBoolBeq (checkedLoanPath lid) p = false →
                                  ResTrie.getBits p rOut = ResTrie.getBits p rIn := by
                                intro p hLp hNeD hNeL
                                have h1 :=
                                  resTrie_getBits_resTrieMerge p tLoan rOut rMid
                                    (by rw [hLp]; rfl) hrOut.2
                                rw [singleRes_getBits_ne (checkedLoanPath lid) p _
                                  (Eq.symm hLp) hNeL] at h1
                                dsimp only [optOp] at h1
                                injection h1 with e1
                                have h2 :=
                                  resTrie_getBits_resTrieMerge p tDebt rMid rIn
                                    (by rw [hLp]; rfl) hrMid.2
                                rw [singleRes_getBits_ne debtPath p _ (Eq.symm hLp) hNeD] at h2
                                dsimp only [optOp] at h2
                                injection h2 with e2
                                exact Eq.trans e1 e2
                              have hPoolEq :
                                  ResTrie.getBits poolPath rOut = ResTrie.getBits poolPath rIn :=
                                hPresOther poolPath rfl rfl rfl
                              have hDebtRel :=
                                resTrie_getBits_resTrieMerge debtPath tDebt rMid rIn rfl hrMid.2
                              rw [singleRes_getBits_same] at hDebtRel
                              have hDebtMid :=
                                resTrie_getBits_resTrieMerge debtPath tLoan rOut rMid rfl hrOut.2
                              rw [singleRes_getBits_ne (checkedLoanPath lid) debtPath _ rfl rfl]
                                at hDebtMid
                              dsimp only [optOp] at hDebtMid
                              injection hDebtMid with hDebtOutEqMid
                              rw [← hDebtOutEqMid] at hDebtRel
                              have hPcEq : extractPoolCap rOut = extractPoolCap rIn := by
                                dsimp only [extractPoolCap]
                                rw [hPoolEq]
                              have hPoolDebtIn := hM.poolDebtOk
                              dsimp only [checkWorldMatchesPoolBool] at hPoolDebtIn
                              have hPoolDebtOut : checkWorldMatchesPoolBool rOut wOut = true := by
                                dsimp only [checkWorldMatchesPoolBool]
                                rw [hPcEq]
                                cases hPc : extractPoolCap rIn with
                                | none =>
                                  rw [hPc] at hPoolDebtIn
                                  exact False.elim (boolFalseNeTrue hPoolDebtIn)
                                | some poolCap =>
                                  rw [hPc] at hPoolDebtIn
                                  dsimp only at hPoolDebtIn
                                  dsimp only
                                  have hLeGrow :
                                      cnfBle (worldMeasureV2026 wOut)
                                        (cnfAddOrd ordSpent (worldMeasureV2026 wIn)) = true :=
                                    cnfBle_of_lt _ _ hGrow.2
                                  dsimp only [extractDebtCap]
                                  cases hGdOut : ResTrie.getBits debtPath rOut with
                                  | none =>
                                    rw [hGdOut] at hDebtRel
                                    dsimp only [optOp] at hDebtRel
                                    injection hDebtRel with hGdInEq
                                    dsimp only [extractDebtCap] at hPoolDebtIn
                                    rw [← hGdInEq] at hPoolDebtIn
                                    dsimp only at hPoolDebtIn
                                    rw [cnfNorm_eq_of_canonical ordSpent hCanSpent] at hPoolDebtIn
                                    have hBoundIn := bandRight hPoolDebtIn
                                    have hOutLePool :
                                        cnfBle (worldMeasureV2026 wOut) poolCap = true :=
                                      cnfBle_trans _ _ _ hLeGrow hBoundIn
                                    have hNilAddOut :
                                        cnfAddOrd [] (worldMeasureV2026 wOut) =
                                          worldMeasureV2026 wOut :=
                                      cnfNorm_eq_of_canonical _ (worldMeasureV2026_canonical wOut)
                                    dsimp only
                                    rw [hNilAddOut]
                                    exact bandIntro hOutLePool hOutLePool
                                  | some eOut =>
                                    rw [hGdOut] at hDebtRel
                                    cases eOut with
                                    | pool _ | checkedOutLoan _ _ | cell _ =>
                                      dsimp only [optOp, resMerge] at hDebtRel
                                      nomatch hDebtRel
                                    | debt dOut =>
                                      dsimp only [optOp, resMerge] at hDebtRel
                                      injection hDebtRel with hGdInEq
                                      dsimp only [extractDebtCap] at hPoolDebtIn
                                      rw [← hGdInEq] at hPoolDebtIn
                                      dsimp only at hPoolDebtIn
                                      rw [cnfNorm_eq_of_canonical _
                                        (isCanonicalCnf_cnfNatAdd ordSpent dOut)] at hPoolDebtIn
                                      have hBoundIn := bandRight hPoolDebtIn
                                      have hRewriteDebt :
                                          cnfAddOrd (cnfNatAdd ordSpent dOut)
                                              (worldMeasureV2026 wIn) =
                                            cnfAddOrd (cnfNorm dOut)
                                              (cnfAddOrd ordSpent (worldMeasureV2026 wIn)) := by
                                        dsimp only [cnfAddOrd]
                                        rw [← cnfNatAdd_cnfNorm_right ordSpent dOut,
                                          cnfNatAdd_comm ordSpent (cnfNorm dOut),
                                          cnfNatAdd_assoc (cnfNorm dOut) ordSpent
                                            (worldMeasureV2026 wIn)]
                                      rw [hRewriteDebt] at hBoundIn
                                      have hMonoDebt :
                                          cnfBle (cnfAddOrd (cnfNorm dOut) (worldMeasureV2026 wOut))
                                            (cnfAddOrd (cnfNorm dOut)
                                              (cnfAddOrd ordSpent (worldMeasureV2026 wIn))) =
                                            true :=
                                        cnfBle_cnfNatAdd_right (cnfNorm dOut)
                                          (worldMeasureV2026 wOut)
                                          (cnfAddOrd ordSpent (worldMeasureV2026 wIn))
                                          (worldMeasureV2026_canonical wOut)
                                          (isCanonicalCnf_cnfNatAdd ordSpent
                                            (worldMeasureV2026 wIn))
                                          hLeGrow
                                      have hSplitOut :
                                          cnfBle (cnfAddOrd (cnfNorm dOut) (worldMeasureV2026 wOut))
                                            poolCap = true :=
                                        cnfBle_trans _ _ _ hMonoDebt hBoundIn
                                      have hMeasLeSplit :
                                          cnfBle (worldMeasureV2026 wOut)
                                            (cnfAddOrd (cnfNorm dOut)
                                              (worldMeasureV2026 wOut)) = true :=
                                        cnfBle_cnfAddOrd_right (cnfNorm dOut)
                                          (worldMeasureV2026 wOut)
                                          (worldMeasureV2026_canonical wOut)
                                      have hOutLePool :
                                          cnfBle (worldMeasureV2026 wOut) poolCap = true :=
                                        cnfBle_trans _ _ _ hMeasLeSplit hSplitOut
                                      dsimp only
                                      exact bandIntro hOutLePool hSplitOut
                              have hViewOut : Nat.ble (viewGet vOut 0) wOut.stepCount = true := by
                                dsimp only [vOut]
                                rw [viewGet_bumpView0_zero]
                                exact natBle_refl wOut.stepCount
                              have hQIn := hM.queueLoansOk
                              have hQOut : QueueMatchesLoansV2026 wOut := by
                                refine bandIntro ?_ (bandRight hQIn)
                                dsimp only [wOut, newTask, queueMatchesLoansBool, List.foldr]
                                rw [he.1]
                                dsimp only
                                rw [hMatchSc]
                                exact bandLeft hQIn
                              have hMOut : WorldMatchesV2026 vOut rOut wOut :=
                                WorldMatchesV2026.mk hViewOut hM.loansMemOk hQOut hPoolDebtOut
                                  (fun cid => by
                                    rw [hPresOther (cellPath cid) rfl rfl rfl]
                                    exact hM.cellOk cid)
                                  (fun lid2 => by
                                    cases hEqL : Pos4.beq lid lid2 with
                                    | true =>
                                      rw [← pos4_eq_of_beq lid lid2 hEqL, hROutLoanNone]
                                      exact True.intro
                                    | false =>
                                      have hNeL :
                                          listBoolBeq (checkedLoanPath lid)
                                            (checkedLoanPath lid2) = false := by
                                        dsimp only [checkedLoanPath, listBoolBeq, Bool.and]
                                        exact hEqL
                                      rw [hPresOther (checkedLoanPath lid2) rfl rfl hNeL]
                                      have hPrev := hM.checkedLoanOk lid2
                                      cases hGl2 : ResTrie.getBits (checkedLoanPath lid2) rIn with
                                      | none => exact True.intro
                                      | some elem2 =>
                                        rw [hGl2] at hPrev
                                        cases elem2 with
                                        | pool _ | debt _ | cell _ => exact hPrev
                                        | checkedOutLoan _ _ =>
                                          have hNoNew :
                                              (!anyTaskHasLoan lid2 (newTask :: wIn.fifoQueue) &&
                                                !anyTaskHasLoan lid2 wIn.stealDeque) = true := by
                                            change (!(Pos4.beq lid lid2 ||
                                              anyTaskHasLoan lid2 wIn.fifoQueue) &&
                                              !anyTaskHasLoan lid2 wIn.stealDeque) = true
                                            rw [hEqL]
                                            exact hPrev.1
                                          exact ⟨hNoNew, hPrev.2⟩)
                              exact ⟨wOut, rOut, vOut, hEval, hVLe, hPcEq,
                                hPostHold, hMOut, hGrow.2⟩)
  exact ⟨wpBurst, hGrowthOfEval⟩

private theorem childRank_double_plus1_lt (rc rp : Nat)
    (hLt : natLt rc rp = true) :
    natLt (rc + rc + 1) (rp + rp) = true := by
  dsimp only [natLt] at hLt
  dsimp only [natLt]
  have hSum : (rc + rc + 1) + 1 = (rc + 1) + (rc + 1) := by
    rw [natAdd_assoc (rc + rc) 1 1, natAdd_assoc rc rc 2,
      natAdd_comm rc 2, ← natAdd_assoc rc 2 rc]
    have h2 : rc + 2 = (rc + 1) + 1 := rfl
    rw [h2, natAdd_assoc (rc + 1) 1 rc, natAdd_comm 1 rc]
  rw [hSum]
  exact natBle_trans ((rc + 1) + (rc + 1)) (rp + (rc + 1)) (rp + rp)
    (natBle_add_mono_right (rc + 1) rp (rc + 1) hLt)
    (natBle_add_mono_left rp (rc + 1) rp hLt)

private theorem wfTasksWeightAt_mkWorkers_zero_above (q baseId k rc cy : Nat)
    (lid : Pos4) (sc wd : Nat)
    (rp : Nat) (hAdm : spawnAdmissible rp k rc = true)
    (hGe : Nat.ble (rp + rp) q = true) :
    wfTasksWeightAt q (mkWorkers baseId k rc cy lid sc wd) = 0 := by
  cases k with
  | zero => rfl
  | succ k' =>
    dsimp only [spawnAdmissible] at hAdm
    have hOddLt : natLt (rc + rc + 1) q = true :=
      natLtOfLtOfBle (rc + rc + 1) (rp + rp) q (childRank_double_plus1_lt rc rp hAdm) hGe
    have hEvenLt : natLt (rc + rc) q = true :=
      natLtTrans (rc + rc) (rc + rc + 1) q (natLtSuccSelf (rc + rc)) hOddLt
    have hB1 : Nat.beq (rc + rc + 1) q = false := natBeqFalseOfLt hOddLt
    have hB0 : Nat.beq (rc + rc) q = false := natBeqFalseOfLt hEvenLt
    revert baseId
    induction k' with
    | zero =>
      intro baseId
      dsimp only [mkWorkers, wfTasksWeightAt, List.foldr, wfTaskWeightAt]
      rw [hB1, hB0]
      rfl
    | succ m ih =>
      intro baseId
      change wfTaskWeightAt q (WorkerTask.mk baseId rc cy lid sc wd) +
        wfTasksWeightAt q (mkWorkers (baseId + 1) (m + 1) rc cy lid sc wd) = 0
      dsimp only [wfTaskWeightAt]
      rw [hB1, hB0, ih (baseId + 1)]
      rfl

private theorem wfTaskWeightAt_self_even (t : WorkerTask) :
    wfTaskWeightAt (t.rank + t.rank) t = t.remYields := by
  dsimp only [wfTaskWeightAt]
  have hNe : Nat.beq (t.rank + t.rank + 1) (t.rank + t.rank) = false := by
    rw [natBeq_symm]
    exact natBeqFalseOfLt (natLtSuccSelf (t.rank + t.rank))
  rw [hNe, natBeq_refl (t.rank + t.rank), natAdd_zero_left]

private theorem wfTaskWeightAt_self_odd (t : WorkerTask) :
    wfTaskWeightAt (t.rank + t.rank + 1) t = 1 := by
  dsimp only [wfTaskWeightAt]
  have hNe : Nat.beq (t.rank + t.rank) (t.rank + t.rank + 1) = false :=
    natBeqFalseOfLt (natLtSuccSelf (t.rank + t.rank))
  rw [natBeq_refl (t.rank + t.rank + 1), hNe]
  rfl

private theorem wfTaskWeightAt_zero_above_odd (t : WorkerTask) (q : Nat)
    (hGt : natLt (t.rank + t.rank + 1) q = true) :
    wfTaskWeightAt q t = 0 := by
  dsimp only [wfTaskWeightAt]
  have hEvenGt : natLt (t.rank + t.rank) q = true :=
    natLtTrans (t.rank + t.rank) (t.rank + t.rank + 1) q (natLtSuccSelf (t.rank + t.rank)) hGt
  rw [natBeqFalseOfLt hGt, natBeqFalseOfLt hEvenGt]
  rfl

private theorem execWavefrontPopped_queues (pol : SpawnPolicy) (hd : WorkerTask)
    (remFifo remSteal : List WorkerTask) (w wOut : WavefrontWorldV2026)
    (hStep : execWavefrontPoppedV2026 pol hd remFifo remSteal w = .returned wOut) :
    spawnAdmissible hd.rank (pol hd.rank).1 (pol hd.rank).2.1 = true ∧
    ((∃ y' : Nat,
        hd.remYields = y' + 1 ∧
        wOut.fifoQueue = remFifo ++
          [WorkerTask.mk hd.taskId hd.rank y' hd.loanId hd.scopeId hd.writeDelta] ∧
        wOut.stealDeque =
          mkWorkers w.nextTaskId (pol hd.rank).1 (pol hd.rank).2.1 (pol hd.rank).2.2
            hd.loanId hd.scopeId hd.writeDelta ++ remSteal) ∨
     (hd.remYields = 0 ∧
      wOut.fifoQueue = remFifo ∧
      wOut.stealDeque =
        mkWorkers w.nextTaskId (pol hd.rank).1 (pol hd.rank).2.1 (pol hd.rank).2.2
          hd.loanId hd.scopeId hd.writeDelta ++ remSteal)) := by
  dsimp only [execWavefrontPoppedV2026] at hStep
  change (match spawnAdmissible hd.rank (pol hd.rank).1 (pol hd.rank).2.1 with
    | false => HybridOutV2026.faultInvalidSpawn
    | true => _) = _ at hStep
  cases hAdm : spawnAdmissible hd.rank (pol hd.rank).1 (pol hd.rank).2.1 with
  | false => rw [hAdm] at hStep; nomatch hStep
  | true =>
    rw [hAdm] at hStep
    dsimp only at hStep
    refine ⟨rfl, ?_⟩
    cases hy : hd.remYields with
    | succ y' =>
      rw [hy] at hStep
      injection hStep with hw
      rw [← hw]
      exact Or.inl ⟨y', rfl, rfl, rfl⟩
    | zero =>
      rw [hy] at hStep
      dsimp only at hStep
      cases hk : (pol hd.rank).1 with
      | succ _ =>
        rw [hk] at hStep
        injection hStep with hw
        rw [← hw]
        exact Or.inr ⟨rfl, rfl, rfl⟩
      | zero =>
        rw [hk] at hStep
        dsimp only at hStep
        cases hFl : wfFindLoan hd.loanId w.loans with
        | none => rw [hFl] at hStep; nomatch hStep
        | some e =>
          rw [hFl] at hStep
          dsimp only at hStep
          cases hSc : loanPhaseMatchesScope e.phase hd.scopeId with
          | false => rw [hSc] at hStep; nomatch hStep
          | true =>
            rw [hSc] at hStep
            dsimp only at hStep
            cases hPut : v2026SubLensPut e.lens w.mem
                (wfEncodeU32LeRawBytes (wrapU32 (e.val + hd.writeDelta))) with
            | none => rw [hPut] at hStep; nomatch hStep
            | some _ =>
              rw [hPut] at hStep
              injection hStep with hw
              rw [← hw]
              exact Or.inr ⟨rfl, rfl, rfl⟩

private theorem execWavefrontPopped_strict_cnf_descent (pol : SpawnPolicy) (hd : WorkerTask)
    (remFifo remSteal : List WorkerTask) (w wOut : WavefrontWorldV2026)
    (hQueueSum : ∀ (q : Nat),
      cnfCoeffAt q (worldMeasureV2026 w) =
        wfTaskWeightAt q hd + (wfTasksWeightAt q remFifo + wfTasksWeightAt q remSteal))
    (hStep : execWavefrontPoppedV2026 pol hd remFifo remSteal w = .returned wOut) :
    cnfLt (worldMeasureV2026 wOut) (worldMeasureV2026 w) = true := by
  have hQ := execWavefrontPopped_queues pol hd remFifo remSteal w wOut hStep
  have hAdm := hQ.1
  cases hQ.2 with
  | inl hYield =>
    cases hYield with
    | intro y' hy =>
      let q0 := hd.rank + hd.rank
      apply cnfLt_of_coeff_drop _ _ (worldMeasureV2026_canonical wOut)
        (worldMeasureV2026_canonical w) q0
      · rw [cnfCoeffAt_worldMeasureV2026, hQueueSum q0, hy.2.1, hy.2.2,
          wfTasksWeightAt_append, wfTasksWeightAt_append]
        have hCh0 := wfTasksWeightAt_mkWorkers_zero_above q0 w.nextTaskId
          (pol hd.rank).1 (pol hd.rank).2.1 (pol hd.rank).2.2 hd.loanId
          hd.scopeId hd.writeDelta hd.rank hAdm (natBle_refl q0)
        rw [hCh0, natAdd_zero_left]
        have hSingle : wfTasksWeightAt q0
            [WorkerTask.mk hd.taskId hd.rank y' hd.loanId hd.scopeId hd.writeDelta] = y' := by
          dsimp only [q0, wfTasksWeightAt, List.foldr]
          rw [wfTaskWeightAt_self_even
            (WorkerTask.mk hd.taskId hd.rank y' hd.loanId hd.scopeId hd.writeDelta)]
          rfl
        rw [hSingle]
        dsimp only [q0]
        rw [wfTaskWeightAt_self_even hd, hy.1,
          natAdd_comm (wfTasksWeightAt (hd.rank + hd.rank) remFifo) y',
          natAdd_assoc y' (wfTasksWeightAt (hd.rank + hd.rank) remFifo)
            (wfTasksWeightAt (hd.rank + hd.rank) remSteal)]
        exact natLt_add_left_of_lt y' (y' + 1) _ (natLtSuccSelf y')
      · intro q hGt
        rw [cnfCoeffAt_worldMeasureV2026, hQueueSum q, hy.2.1, hy.2.2,
          wfTasksWeightAt_append, wfTasksWeightAt_append]
        have hGe : Nat.ble (hd.rank + hd.rank) q = true :=
          natBle_trans (hd.rank + hd.rank) (hd.rank + hd.rank + 1) q
            (natBle_succ_right _ _ (natBle_refl _)) hGt
        have hCh0 := wfTasksWeightAt_mkWorkers_zero_above q w.nextTaskId
          (pol hd.rank).1 (pol hd.rank).2.1 (pol hd.rank).2.2 hd.loanId
          hd.scopeId hd.writeDelta hd.rank hAdm hGe
        rw [hCh0, natAdd_zero_left]
        have hSameHd : wfTasksWeightAt q
            [WorkerTask.mk hd.taskId hd.rank y' hd.loanId hd.scopeId hd.writeDelta] =
            wfTaskWeightAt q hd := by
          dsimp only [wfTasksWeightAt, List.foldr, wfTaskWeightAt]
          rw [natBeqFalseOfLt hGt]
          cases Nat.beq (hd.rank + hd.rank + 1) q <;> rfl
        rw [hSameHd, natAdd_comm (wfTasksWeightAt q remFifo) (wfTaskWeightAt q hd),
          natAdd_assoc (wfTaskWeightAt q hd) (wfTasksWeightAt q remFifo)
            (wfTasksWeightAt q remSteal)]
  | inr hDone =>
    let q0 := hd.rank + hd.rank + 1
    apply cnfLt_of_coeff_drop _ _ (worldMeasureV2026_canonical wOut)
      (worldMeasureV2026_canonical w) q0
    · rw [cnfCoeffAt_worldMeasureV2026, hQueueSum q0, hDone.2.1, hDone.2.2,
        wfTasksWeightAt_append]
      have hGe : Nat.ble (hd.rank + hd.rank) q0 = true :=
        natBle_succ_right (hd.rank + hd.rank) (hd.rank + hd.rank) (natBle_refl _)
      have hCh0 := wfTasksWeightAt_mkWorkers_zero_above q0 w.nextTaskId
        (pol hd.rank).1 (pol hd.rank).2.1 (pol hd.rank).2.2 hd.loanId
        hd.scopeId hd.writeDelta hd.rank hAdm hGe
      rw [hCh0, natAdd_zero_left]
      dsimp only [q0]
      rw [wfTaskWeightAt_self_odd hd]
      let R := wfTasksWeightAt (hd.rank + hd.rank + 1) remFifo +
        wfTasksWeightAt (hd.rank + hd.rank + 1) remSteal
      change natLt R (1 + R) = true
      rw [natAdd_comm 1 R]
      exact natLtSuccSelf R
    · intro q hGt
      rw [cnfCoeffAt_worldMeasureV2026, hQueueSum q, hDone.2.1, hDone.2.2,
        wfTasksWeightAt_append]
      have hGe : Nat.ble (hd.rank + hd.rank) q = true :=
        natBle_trans (hd.rank + hd.rank) q0 q
          (natBle_succ_right _ _ (natBle_refl _))
          (natBle_trans q0 (q0 + 1) q (natBle_succ_right _ _ (natBle_refl _)) hGt)
      have hCh0 := wfTasksWeightAt_mkWorkers_zero_above q w.nextTaskId
        (pol hd.rank).1 (pol hd.rank).2.1 (pol hd.rank).2.2 hd.loanId
        hd.scopeId hd.writeDelta hd.rank hAdm hGe
      rw [hCh0, natAdd_zero_left, wfTaskWeightAt_zero_above_odd hd q hGt, natAdd_zero_left]

/-- Under an admissible `SpawnPolicy`, popping one task strictly decreases
`worldMeasureV2026` under `cnfLt` (`[]` zero axioms). -/
theorem wavefrontStep_strict_cnf_descent (pol : SpawnPolicy)
    (w wOut : WavefrontWorldV2026)
    (hEval : evalHybridCmdV2026 (.poolWavefrontStep pol) w = .returned wOut) :
    cnfLt (worldMeasureV2026 wOut) (worldMeasureV2026 w) = true := by
  dsimp only [evalHybridCmdV2026] at hEval
  cases hF : w.fifoQueue with
  | cons hd ft =>
    rw [hF] at hEval
    apply execWavefrontPopped_strict_cnf_descent pol hd ft w.stealDeque w wOut _ hEval
    intro q
    rw [cnfCoeffAt_worldMeasureV2026, hF]
    dsimp only [wfTasksWeightAt, List.foldr]
    rw [natAdd_assoc]
  | nil =>
    rw [hF] at hEval
    cases hS : w.stealDeque with
    | nil => rw [hS] at hEval; nomatch hEval
    | cons hd stTail =>
      rw [hS] at hEval
      apply execWavefrontPopped_strict_cnf_descent pol hd [] stTail w wOut _ hEval
      intro q
      rw [cnfCoeffAt_worldMeasureV2026, hF, hS]
      dsimp only [wfTasksWeightAt, List.foldr]
      rw [natAdd_zero_left, natAdd_zero_left]

/-- Returns `true` iff either `fifoQueue` or `stealDeque` is non-empty. -/
def wfPoolIsNonEmpty (w : WavefrontWorldV2026) : Bool :=
  match w.fifoQueue with
  | _ :: _ => true
  | [] =>
    match w.stealDeque with
    | _ :: _ => true
    | [] => false

/-- Under `LoansSyncedWithMemV2026` and `QueueMatchesLoansV2026`, `execWavefrontPoppedV2026`
succeeds without loan faults and preserves both invariants (`[propext]`). -/
theorem execWavefrontPopped_returns_and_preserves (pol : SpawnPolicy)
    (hd : WorkerTask) (remFifo remSteal : List WorkerTask) (w : WavefrontWorldV2026)
    (hAdm : spawnAdmissible hd.rank (pol hd.rank).1 (pol hd.rank).2.1 = true)
    (hSync : LoansSyncedWithMemV2026 w.loans w.mem)
    (hHdLoan : (match wfFindLoan hd.loanId w.loans with
      | none => false
      | some e => loanPhaseMatchesScope e.phase hd.scopeId) = true)
    (hRemFifo : queueMatchesLoansBool remFifo w.loans = true)
    (hRemSteal : queueMatchesLoansBool remSteal w.loans = true) :
    ∃ wOut : WavefrontWorldV2026,
      execWavefrontPoppedV2026 pol hd remFifo remSteal w = .returned wOut ∧
      LoansSyncedWithMemV2026 wOut.loans wOut.mem ∧
      QueueMatchesLoansV2026 wOut ∧
      wOut.cells = w.cells ∧
      wOut.stepCount = w.stepCount + 1 ∧
      (∀ (lid2 : Pos4),
        Pos4.beq hd.loanId lid2 = false →
        (!anyTaskHasLoan lid2 remFifo && !anyTaskHasLoan lid2 remSteal) = true →
        wfFindLoan lid2 wOut.loans = wfFindLoan lid2 w.loans ∧
        (!anyTaskHasLoan lid2 wOut.fifoQueue &&
          !anyTaskHasLoan lid2 wOut.stealDeque) = true) := by
  dsimp only [execWavefrontPoppedV2026]
  rw [hAdm]
  dsimp only
  cases hy : hd.remYields with
  | succ y' =>
    have hQOut : QueueMatchesLoansV2026 {
        mem := w.mem, loans := w.loans, cells := w.cells,
        fifoQueue := remFifo ++ [WorkerTask.mk hd.taskId hd.rank y' hd.loanId
          hd.scopeId hd.writeDelta],
        stealDeque := mkWorkers w.nextTaskId (pol hd.rank).1 (pol hd.rank).2.1
          (pol hd.rank).2.2 hd.loanId hd.scopeId hd.writeDelta ++ remSteal,
        nextTaskId := w.nextTaskId + (pol hd.rank).1,
        completedCount := w.completedCount, stepCount := w.stepCount + 1 } := by
      refine bandIntro ?_ ?_
      · dsimp only
        rw [queueMatchesLoansBool_append]
        exact bandIntro hRemFifo (bandIntro hHdLoan rfl)
      · dsimp only
        rw [queueMatchesLoansBool_append]
        exact bandIntro (queueMatchesLoansBool_mkWorkers _ _ _ _ _ _ _ w.loans hHdLoan)
          hRemSteal
    refine ⟨_, rfl, hSync, hQOut, rfl, rfl, ?_⟩
    intro lid2 hNe hRemOk
    refine ⟨rfl, ?_⟩
    dsimp only
    rw [anyTaskHasLoan_append, anyTaskHasLoan_append,
      mkWorkers_not_hasLoan hd.loanId lid2 _ _ _ _ _ _ hNe]
    have hSingle : anyTaskHasLoan lid2
        [WorkerTask.mk hd.taskId hd.rank y' hd.loanId hd.scopeId hd.writeDelta] = false := by
      dsimp only [anyTaskHasLoan, List.foldr]
      rw [hNe]
      rfl
    rw [hSingle, trueOfBnotTrue (bandLeft hRemOk), trueOfBnotTrue (bandRight hRemOk)]
    rfl
  | zero =>
    dsimp only
    cases hk : (pol hd.rank).1 with
    | succ k' =>
      have hQOut : QueueMatchesLoansV2026 {
          mem := w.mem, loans := w.loans, cells := w.cells,
          fifoQueue := remFifo,
          stealDeque := mkWorkers w.nextTaskId (k' + 1) (pol hd.rank).2.1
            (pol hd.rank).2.2 hd.loanId hd.scopeId hd.writeDelta ++ remSteal,
          nextTaskId := w.nextTaskId + (k' + 1),
          completedCount := w.completedCount + 1, stepCount := w.stepCount + 1 } := by
        refine bandIntro hRemFifo ?_
        dsimp only
        rw [queueMatchesLoansBool_append]
        exact bandIntro (queueMatchesLoansBool_mkWorkers _ _ _ _ _ _ _ w.loans hHdLoan)
          hRemSteal
      refine ⟨_, rfl, hSync, hQOut, rfl, rfl, ?_⟩
      intro lid2 hNe hRemOk
      refine ⟨rfl, ?_⟩
      dsimp only
      rw [anyTaskHasLoan_append, mkWorkers_not_hasLoan hd.loanId lid2 _ _ _ _ _ _ hNe,
        trueOfBnotTrue (bandLeft hRemOk), trueOfBnotTrue (bandRight hRemOk)]
      rfl
    | zero =>
      dsimp only
      cases hFl : wfFindLoan hd.loanId w.loans with
      | none => rw [hFl] at hHdLoan; exact False.elim (boolFalseNeTrue hHdLoan)
      | some e =>
        rw [hFl] at hHdLoan
        dsimp only at hHdLoan
        dsimp only
        rw [hHdLoan]
        dsimp only
        have hPhEq : e.phase = .spatialCheckedOut hd.scopeId := by
          cases hp : e.phase with
          | spatialCheckedOut s =>
            rw [hp] at hHdLoan
            dsimp only [loanPhaseMatchesScope] at hHdLoan
            exact congrArg WfLoanPhase.spatialCheckedOut (natEq_of_beq s hd.scopeId hHdLoan)
          | activeMut | frozen | ended =>
            rw [hp] at hHdLoan; exact False.elim (boolFalseNeTrue hHdLoan)
        have hLiveE : loanPhaseIsLive e.phase = true := by rw [hPhEq]; rfl
        have hProps := wfFindLoan_synced_live_props w.loans w.mem hd.loanId e
          hSync hFl hLiveE
        let newVal := wrapU32 (e.val + hd.writeDelta)
        have hLenSl : (wfEncodeU32LeRawBytes newVal).length = e.lens.size := by
          rw [wfEncodeU32LeRawBytes_length, hProps.2.1]
        cases v2026SubLens_put_succeeds_of_get e.lens w.mem (wfEncodeU32LeAbsBytes e.val)
            (wfEncodeU32LeRawBytes newVal) hProps.2.2.2 hLenSl with
        | intro memOut hPut =>
          dsimp only [newVal] at hPut
          rw [hPut]
          dsimp only
          let stillInFlight :=
            anyTaskHasLoanScope hd.loanId hd.scopeId remFifo ||
            anyTaskHasLoanScope hd.loanId hd.scopeId remSteal
          let nextPh := match stillInFlight with
            | true => WfLoanPhase.spatialCheckedOut hd.scopeId
            | false => WfLoanPhase.activeMut
          have hNextLive : loanPhaseIsLive nextPh = true := by
            dsimp only [nextPh]
            cases stillInFlight <;> rfl
          have hSyncNext :
              LoansSyncedWithMemV2026 (wfSetLoanEntryAt w.loans hd.loanId nextPh newVal)
                memOut :=
            loansSyncedWithMemV2026_set_and_put w.loans w.mem memOut hd.loanId e
              nextPh newVal hSync hFl hNextLive
              (Eq.symm (wrapU32_idem (e.val + hd.writeDelta))) hPut
          have hQNext : QueueMatchesLoansV2026 {
              mem := memOut,
              loans := wfSetLoanEntryAt w.loans hd.loanId nextPh newVal,
              cells := w.cells, fifoQueue := remFifo, stealDeque := remSteal,
              nextTaskId := w.nextTaskId, completedCount := w.completedCount + 1,
              stepCount := w.stepCount + 1 } := by
            have hScF := anyTaskHasLoanScope_eq_anyTaskHasLoan_of_queueMatches
              hd.loanId hd.scopeId e remFifo w.loans hFl hPhEq hRemFifo
            have hScS := anyTaskHasLoanScope_eq_anyTaskHasLoan_of_queueMatches
              hd.loanId hd.scopeId e remSteal w.loans hFl hPhEq hRemSteal
            dsimp only [QueueMatchesLoansV2026, checkQueueMatchesLoansBool, nextPh,
              stillInFlight]
            cases hAny : (anyTaskHasLoanScope hd.loanId hd.scopeId remFifo ||
                anyTaskHasLoanScope hd.loanId hd.scopeId remSteal) with
            | true =>
              dsimp only
              rw [← hPhEq]
              exact bandIntro
                (queueMatchesLoansBool_wfSetLoanEntryAt_samePhase remFifo
                  w.loans hd.loanId e newVal hFl hRemFifo)
                (queueMatchesLoansBool_wfSetLoanEntryAt_samePhase remSteal
                  w.loans hd.loanId e newVal hFl hRemSteal)
            | false =>
              dsimp only
              rw [hScF, hScS] at hAny
              have hNoBoth := borFalseElim hAny
              exact bandIntro
                (queueMatchesLoansBool_wfSetLoanEntryAt_of_not_hasLoan remFifo
                  w.loans hd.loanId .activeMut newVal hNoBoth.1 hRemFifo)
                (queueMatchesLoansBool_wfSetLoanEntryAt_of_not_hasLoan remSteal
                  w.loans hd.loanId .activeMut newVal hNoBoth.2 hRemSteal)
          exact ⟨_, rfl, hSyncNext, hQNext, rfl, rfl, fun lid2 hNe hRemOk =>
            ⟨wfFindLoan_wfSetLoanEntryAt_ne w.loans hd.loanId lid2 nextPh newVal hNe,
              hRemOk⟩⟩

private theorem nonEmptyPool_wavefrontStep_returns (pol : SpawnPolicy)
    (hPol : PolicyAdmissible pol)
    (w : WavefrontWorldV2026) (hNonEmpty : wfPoolIsNonEmpty w = true)
    (hSync : LoansSyncedWithMemV2026 w.loans w.mem)
    (hQ : QueueMatchesLoansV2026 w) :
    ∃ wOut : WavefrontWorldV2026,
      evalHybridCmdV2026 (.poolWavefrontStep pol) w = .returned wOut ∧
      LoansSyncedWithMemV2026 wOut.loans wOut.mem ∧
      QueueMatchesLoansV2026 wOut ∧
      wOut.cells = w.cells ∧
      wOut.stepCount = w.stepCount + 1 ∧
      (∀ (lid2 : Pos4),
        (!anyTaskHasLoan lid2 w.fifoQueue && !anyTaskHasLoan lid2 w.stealDeque) = true →
        wfFindLoan lid2 wOut.loans = wfFindLoan lid2 w.loans ∧
        (!anyTaskHasLoan lid2 wOut.fifoQueue &&
          !anyTaskHasLoan lid2 wOut.stealDeque) = true) := by
  dsimp only [evalHybridCmdV2026]
  dsimp only [wfPoolIsNonEmpty] at hNonEmpty
  have hQF := bandLeft hQ
  have hQS := bandRight hQ
  cases hF : w.fifoQueue with
  | cons hd ft =>
    rw [hF] at hQF
    dsimp only [queueMatchesLoansBool, List.foldr] at hQF
    cases execWavefrontPopped_returns_and_preserves pol hd ft w.stealDeque w
        (hPol hd.rank) hSync (bandLeft hQF) (bandRight hQF) hQS with
    | intro wOut hw =>
      refine ⟨wOut, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, ?_⟩
      intro lid2 hNoIn
      have hNotF := trueOfBnotTrue (bandLeft hNoIn)
      change (Pos4.beq hd.loanId lid2 || anyTaskHasLoan lid2 ft) = false at hNotF
      have hSplitF := borFalseElim hNotF
      exact hw.2.2.2.2.2 lid2 hSplitF.1
        (bandIntro (by rw [hSplitF.2]; rfl) (bandRight hNoIn))
  | nil =>
    rw [hF] at hNonEmpty hQF
    cases hS : w.stealDeque with
    | nil => rw [hS] at hNonEmpty; exact False.elim (boolFalseNeTrue hNonEmpty)
    | cons hd stTail =>
      rw [hS] at hQS
      dsimp only [queueMatchesLoansBool, List.foldr] at hQS
      cases execWavefrontPopped_returns_and_preserves pol hd [] stTail w
          (hPol hd.rank) hSync (bandLeft hQS) rfl (bandRight hQS) with
      | intro wOut hw =>
        refine ⟨wOut, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, ?_⟩
        intro lid2 hNoIn
        have hNotS := trueOfBnotTrue (bandRight hNoIn)
        change (Pos4.beq hd.loanId lid2 || anyTaskHasLoan lid2 stTail) = false at hNotS
        have hSplitS := borFalseElim hNotS
        exact hw.2.2.2.2.2 lid2 hSplitS.1
          (bandIntro rfl (by rw [hSplitS.2]; rfl))

/-- `VSepWpOrdRelV2026` rule for `.poolWavefrontStep pol`: establishes `.strictDescent`
(`cnfLt (worldMeasureV2026 wOut) (worldMeasureV2026 wIn) = true`) while preserving
`Firewall`-shielded `WorldMatchesV2026` (`[propext]`). -/
theorem vsepWpOrdRelV2026_wavefrontStep_strict_descent
    (pol : SpawnPolicy) (hPol : PolicyAdmissible pol) :
    VSepWpOrdRelV2026 (.poolWavefrontStep pol) .strictDescent
      (fun w => wfPoolIsNonEmpty w = true)
      vemp (fun wOut => vMinStep wOut.stepCount) :=
  VSepWpOrdRelV2026.mk rfl (fun v F rIn wIn hNe hPre hM => by
    have hFIn : F.holds v rIn := vsep_vemp_elim v F rIn hPre
    cases nonEmptyPool_wavefrontStep_returns pol hPol wIn hNe hM.loansMemOk
        hM.queueLoansOk with
    | intro wOut hw =>
      have hLt := wavefrontStep_strict_cnf_descent pol wIn wOut hw.1
      have hLe := cnfBle_of_lt (worldMeasureV2026 wOut) (worldMeasureV2026 wIn) hLt
      let vOut := bumpView0 v wOut.stepCount
      have hVLe : ViewLe v vOut :=
        viewLe_bumpView0 v wOut.stepCount
          (by
            rw [hw.2.2.2.2.1]
            exact natBle_succ_right (viewGet v 0) wIn.stepCount hM.viewOk)
      have hFOut : F.holds vOut rIn :=
        F.upClosed v vOut rIn rIn hVLe (resTrieSub_refl rIn) hFIn
      have hMinStepHold : (vMinStep wOut.stepCount).holds vOut .empty := by
        dsimp only [vMinStep, vOut]
        rw [viewGet_bumpView0_zero]
        exact natBle_refl wOut.stepCount
      have hPostHold : (vsep (vMinStep wOut.stepCount) F).holds vOut rIn :=
        ⟨.empty, rIn, resTrieMerge_empty_left_fuel resFuel rIn, hMinStepHold, hFOut⟩
      have hPoolDebtOut : checkWorldMatchesPoolBool rIn wOut = true := by
        have hInOk := hM.poolDebtOk
        dsimp only [checkWorldMatchesPoolBool] at hInOk
        dsimp only [checkWorldMatchesPoolBool]
        cases hPc : extractPoolCap rIn with
        | none => rw [hPc] at hInOk; exact False.elim (boolFalseNeTrue hInOk)
        | some poolCap =>
          rw [hPc] at hInOk; dsimp only at hInOk; dsimp only
          cases hDc : extractDebtCap rIn with
          | none => rw [hDc] at hInOk; exact False.elim (boolFalseNeTrue hInOk)
          | some debtCap =>
            rw [hDc] at hInOk; dsimp only at hInOk; dsimp only
            have h1 : cnfBle (worldMeasureV2026 wOut) poolCap = true :=
              cnfBle_trans _ _ _ hLe (bandLeft hInOk)
            have hMonoD : cnfBle (cnfAddOrd debtCap (worldMeasureV2026 wOut))
                (cnfAddOrd debtCap (worldMeasureV2026 wIn)) = true :=
              cnfBle_cnfNatAdd_right debtCap (worldMeasureV2026 wOut)
                (worldMeasureV2026 wIn)
                (worldMeasureV2026_canonical wOut) (worldMeasureV2026_canonical wIn) hLe
            have h2 : cnfBle (cnfAddOrd debtCap (worldMeasureV2026 wOut)) poolCap = true :=
              cnfBle_trans _ _ _ hMonoD (bandRight hInOk)
            exact bandIntro h1 h2
      have hViewOut : Nat.ble (viewGet vOut 0) wOut.stepCount = true := by
        dsimp only [vOut]
        rw [viewGet_bumpView0_zero]
        exact natBle_refl wOut.stepCount
      have hMOut : WorldMatchesV2026 vOut rIn wOut :=
        WorldMatchesV2026.mk hViewOut hw.2.1 hw.2.2.1 hPoolDebtOut
          (fun cid => by rw [hw.2.2.2.1]; exact hM.cellOk cid)
          (fun lid2 => by
            have hPrev := hM.checkedLoanOk lid2
            cases hGl2 : ResTrie.getBits (checkedLoanPath lid2) rIn with
            | none => exact True.intro
            | some elem2 =>
              rw [hGl2] at hPrev
              cases elem2 with
              | pool _ | debt _ | cell _ => exact hPrev
              | checkedOutLoan _ _ =>
                have hPres := hw.2.2.2.2.2 lid2 hPrev.1
                cases hPrev.2 with
                | intro e2 he2 =>
                  exact ⟨hPres.2, ⟨e2, Eq.trans hPres.1 he2.1, he2.2⟩⟩)
      exact ⟨wOut, rIn, vOut, hw.1, hVLe, rfl, hPostHold, hMOut, hLt⟩)

/-! ## 4. Arbitrary-Depth `< ω^ω` Drain & Universal `.activeMut` Loan Reclamation -/

/-- Multi-step reflexive-transitive wavefront drain relation terminating at an
empty-queue quiescent `WavefrontWorldV2026`. -/
inductive WavefrontConvergesV2026 (pol : SpawnPolicy) :
    WavefrontWorldV2026 → WavefrontWorldV2026 → Prop where
  | quiescent (w : WavefrontWorldV2026) (hEmpty : wfPoolIsNonEmpty w = false) :
      WavefrontConvergesV2026 pol w w
  | step (w wNext wFinal : WavefrontWorldV2026)
      (hNonEmpty : wfPoolIsNonEmpty w = true)
      (hStep : evalHybridCmdV2026 (.poolWavefrontStep pol) w = .returned wNext)
      (hLt : cnfLt (worldMeasureV2026 wNext) (worldMeasureV2026 w) = true)
      (hRest : WavefrontConvergesV2026 pol wNext wFinal) :
      WavefrontConvergesV2026 pol w wFinal

/-- Computable fuel-bounded wavefront step runner returning `some wFinal` upon
reaching quiescence. -/
def runWavefrontStepsV2026 (fuel : Nat) (pol : SpawnPolicy)
    (w : WavefrontWorldV2026) : Option WavefrontWorldV2026 :=
  @Nat.rec (fun _ => WavefrontWorldV2026 → Option WavefrontWorldV2026)
    (fun _ => none)
    (fun _ ih cur =>
      match wfPoolIsNonEmpty cur with
      | false => some cur
      | true =>
        match evalHybridCmdV2026 (.poolWavefrontStep pol) cur with
        | .returned next => ih next
        | .faultInvalidSpawn | .faultLoanViolation => none)
    fuel w

/-- Extracts a concrete fuel bound at which `runWavefrontStepsV2026` reproduces
`WavefrontConvergesV2026` (`[]` zero axioms). -/
theorem wavefrontConvergesV2026_extract_fuel (pol : SpawnPolicy)
    (w wFinal : WavefrontWorldV2026)
    (hConv : WavefrontConvergesV2026 pol w wFinal) :
    wFinal.fifoQueue = [] ∧
    wFinal.stealDeque = [] ∧
    worldMeasureV2026 wFinal = [] ∧
    ∃ fuel : Nat, runWavefrontStepsV2026 fuel pol w = some wFinal := by
  induction hConv with
  | quiescent w0 hEmp =>
    dsimp only [wfPoolIsNonEmpty] at hEmp
    cases hF : w0.fifoQueue with
    | cons _ _ => rw [hF] at hEmp; exact False.elim (boolTrueNeFalse hEmp)
    | nil =>
      rw [hF] at hEmp
      cases hS : w0.stealDeque with
      | cons _ _ => rw [hS] at hEmp; exact False.elim (boolTrueNeFalse hEmp)
      | nil =>
        refine ⟨rfl, rfl, ?_, ⟨1, ?_⟩⟩
        · dsimp only [worldMeasureV2026]; rw [hF, hS]; rfl
        · change (match wfPoolIsNonEmpty w0 with | false => some w0 | true => _) = some w0
          dsimp only [wfPoolIsNonEmpty]; rw [hF, hS]
  | step w0 _ wf hNe hSt _ _ ih =>
    cases ih.2.2.2 with
    | intro f hf =>
      refine ⟨ih.1, ih.2.1, ih.2.2.1, ⟨f + 1, ?_⟩⟩
      change (match wfPoolIsNonEmpty w0 with
        | false => some w0
        | true =>
          match evalHybridCmdV2026 (.poolWavefrontStep pol) w0 with
          | .returned next => runWavefrontStepsV2026 f pol next
          | .faultInvalidSpawn | .faultLoanViolation => none) = some wf
      rw [hNe, hSt]
      exact hf

/-- Arbitrary-depth `< ω^ω` convergence for every admissible spawn policy and
every strictly descending rank tower (`[propext]`). -/
theorem multiRank_wavefront_terminates_arbitrary_depth :
    (∀ (pol : SpawnPolicy), PolicyAdmissible pol →
      ∀ (w0 : WavefrontWorldV2026),
        LoansSyncedWithMemV2026 w0.loans w0.mem →
        QueueMatchesLoansV2026 w0 →
        ∃ wFinal : WavefrontWorldV2026,
          WavefrontConvergesV2026 pol w0 wFinal ∧
          LoansSyncedWithMemV2026 wFinal.loans wFinal.mem ∧
          QueueMatchesLoansV2026 wFinal ∧
          wFinal.fifoQueue = [] ∧
          wFinal.stealDeque = [] ∧
          worldMeasureV2026 wFinal = [] ∧
          (∃ fuel : Nat, runWavefrontStepsV2026 fuel pol w0 = some wFinal)) ∧
    (∀ (ranks : List Nat) (fanout childYields : Nat) (w0 : WavefrontWorldV2026),
      isStrictlyDescendingTower ranks = true →
      LoansSyncedWithMemV2026 w0.loans w0.mem →
      QueueMatchesLoansV2026 w0 →
      ∃ wFinal : WavefrontWorldV2026,
        WavefrontConvergesV2026 (towerLookupNext ranks fanout childYields) w0 wFinal ∧
        LoansSyncedWithMemV2026 wFinal.loans wFinal.mem ∧
        QueueMatchesLoansV2026 wFinal ∧
        worldMeasureV2026 wFinal = []) := by
  have hUniv : ∀ (pol : SpawnPolicy), PolicyAdmissible pol →
      ∀ (ord : CnfOrd), isCanonicalCnf ord = true →
      ∀ (w0 : WavefrontWorldV2026), worldMeasureV2026 w0 = ord →
      LoansSyncedWithMemV2026 w0.loans w0.mem →
      QueueMatchesLoansV2026 w0 →
      ∃ wFinal : WavefrontWorldV2026,
        WavefrontConvergesV2026 pol w0 wFinal ∧
        LoansSyncedWithMemV2026 wFinal.loans wFinal.mem ∧
        QueueMatchesLoansV2026 wFinal := by
    intro pol hPol ord hCan
    induction cnfAcc_all ord hCan with
    | intro x _ ih =>
      intro w0 hMeas hSync0 hQ0
      cases hNe : wfPoolIsNonEmpty w0 with
      | false => exact ⟨w0, WavefrontConvergesV2026.quiescent w0 hNe, hSync0, hQ0⟩
      | true =>
        cases nonEmptyPool_wavefrontStep_returns pol hPol w0 hNe hSync0 hQ0 with
        | intro wNext hwNext =>
          have hStep := hwNext.1
          have hLt0 : cnfLt (worldMeasureV2026 wNext) (worldMeasureV2026 w0) = true :=
            wavefrontStep_strict_cnf_descent pol w0 wNext hStep
          have hLtX : cnfLt (worldMeasureV2026 wNext) x = true := by
            rw [← hMeas]; exact hLt0
          have hCanNext : isCanonicalCnf (worldMeasureV2026 wNext) = true :=
            worldMeasureV2026_canonical wNext
          cases ih (worldMeasureV2026 wNext) hCanNext hLtX hCanNext wNext rfl
              hwNext.2.1 hwNext.2.2.1 with
          | intro wFinal hRest =>
            exact ⟨wFinal,
              WavefrontConvergesV2026.step w0 wNext wFinal hNe hStep hLt0 hRest.1,
              hRest.2⟩
  refine ⟨?_, ?_⟩
  · intro pol hPol w0 hSync0 hQ0
    cases hUniv pol hPol (worldMeasureV2026 w0) (worldMeasureV2026_canonical w0)
        w0 rfl hSync0 hQ0 with
    | intro wFinal hRes =>
      have hEx := wavefrontConvergesV2026_extract_fuel pol w0 wFinal hRes.1
      exact ⟨wFinal, hRes.1, hRes.2.1, hRes.2.2, hEx.1, hEx.2.1, hEx.2.2.1, hEx.2.2.2⟩
  · intro ranks fanout childYields w0 hDesc hSync0 hQ0
    have hPol := towerLookupNext_admissible ranks fanout childYields hDesc
    cases hUniv (towerLookupNext ranks fanout childYields) hPol
        (worldMeasureV2026 w0) (worldMeasureV2026_canonical w0) w0 rfl hSync0 hQ0 with
    | intro wFinal hRes =>
      exact ⟨wFinal, hRes.1, hRes.2.1, hRes.2.2,
        (wavefrontConvergesV2026_extract_fuel _ w0 wFinal hRes.1).2.2.1⟩

/-! ### Leaf-Count Multiplier, `universal_post_drain_activeMut_reclaim`, & 5-Stage Lifecycle -/

private theorem natZeroMul (n : Nat) : 0 * n = 0 := by
  induction n with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natSuccMul (a b : Nat) : (a + 1) * b = a * b + b := by
  induction b with
  | zero => rfl
  | succ k ih =>
    change (a + 1) * k + (a + 1) = (a * k + a) + (k + 1)
    rw [ih, natAdd_assoc (a * k) k (a + 1), ← natAdd_assoc k a 1,
      natAdd_comm k a, natAdd_assoc a k 1, ← natAdd_assoc (a * k) a (k + 1)]

private theorem natOneMul (n : Nat) : 1 * n = n := by
  have h := natSuccMul 0 n
  rw [natZeroMul n, natAdd_zero_left n] at h
  exact h

private theorem natAddMul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  induction a with
  | zero => rw [natZeroMul, natAdd_zero_left, natAdd_zero_left]
  | succ a' ih =>
    have h1 : (a' + 1) + b = (a' + b) + 1 := by
      rw [natAdd_assoc a' 1 b, natAdd_comm 1 b, ← natAdd_assoc a' b 1]
    rw [h1, natSuccMul, ih, natSuccMul, natAdd_assoc (a' * c) (b * c) c,
      natAdd_comm (b * c) c, ← natAdd_assoc (a' * c) c (b * c)]

/-- Bounded `@Nat.rec` helper computing transitive zero-fanout leaf writebacks. -/
def rankLeafMultAt (pol : SpawnPolicy) (fuel : Nat) : Nat → Nat → Nat :=
  @Nat.rec (fun _ => Nat → Nat → Nat)
    (fun _ _ => 0)
    (fun _ ih r y =>
      let p := pol r
      let childOne := ih p.2.1 p.2.2
      let zeroYield := match p.1 with
        | 0 => 1
        | k' + 1 => (k' + 1) * childOne
      y * (p.1 * childOne) + zeroYield)
    fuel

private theorem rankLeafMultAt_succ (pol : SpawnPolicy) (n r y : Nat) :
    rankLeafMultAt pol (n + 1) r y =
      let p := pol r
      let childOne := rankLeafMultAt pol n p.2.1 p.2.2
      y * (p.1 * childOne) + (match p.1 with | 0 => 1 | k' + 1 => (k' + 1) * childOne) := rfl

private theorem rankLeafMultAt_fuel_irrel (pol : SpawnPolicy) (hPol : PolicyAdmissible pol)
    (f1 : Nat) :
    ∀ (f2 r y : Nat),
      natLt r f1 = true →
      natLt r f2 = true →
      rankLeafMultAt pol f1 r y = rankLeafMultAt pol f2 r y := by
  induction f1 with
  | zero =>
    intro _ _ _ h1 _
    exact False.elim (boolFalseNeTrue h1)
  | succ n1 ih =>
    intro f2 r y h1 h2
    cases f2 with
    | zero => exact False.elim (boolFalseNeTrue h2)
    | succ n2 =>
      rw [rankLeafMultAt_succ, rankLeafMultAt_succ]
      dsimp only
      have hAdm := hPol r
      dsimp only [spawnAdmissible] at hAdm
      cases hk : (pol r).1 with
      | zero =>
        rw [natZeroMul, natZeroMul]
      | succ _ =>
        rw [hk] at hAdm
        have hLe1 : Nat.ble r n1 = true := h1
        have hLe2 : Nat.ble r n2 = true := h2
        have hCh1 : natLt (pol r).2.1 n1 = true :=
          natLtOfLtOfBle _ r n1 hAdm hLe1
        have hCh2 : natLt (pol r).2.1 n2 = true :=
          natLtOfLtOfBle _ r n2 hAdm hLe2
        rw [ih n2 (pol r).2.1 (pol r).2.2 hCh1 hCh2]

/-- Total number of zero-fanout leaf writebacks transitively generated by one
task at `(rank, remYields)` under `pol`. -/
def taskLeafMult (pol : SpawnPolicy) (rank remYields : Nat) : Nat :=
  rankLeafMultAt pol (rank + 1) rank remYields

private theorem taskLeafMult_unfold (pol : SpawnPolicy) (hPol : PolicyAdmissible pol)
    (r y : Nat) :
    taskLeafMult pol r y =
      y * ((pol r).1 * taskLeafMult pol (pol r).2.1 (pol r).2.2) +
      (match (pol r).1 with
       | 0 => 1
       | k' + 1 => (k' + 1) * taskLeafMult pol (pol r).2.1 (pol r).2.2) := by
  dsimp only [taskLeafMult]
  rw [rankLeafMultAt_succ]
  dsimp only
  have hAdm := hPol r
  dsimp only [spawnAdmissible] at hAdm
  cases hk : (pol r).1 with
  | zero =>
    rw [natZeroMul, natZeroMul]
  | succ _ =>
    rw [hk] at hAdm
    have hEq := rankLeafMultAt_fuel_irrel pol hPol r ((pol r).2.1 + 1)
      (pol r).2.1 (pol r).2.2 hAdm (natLtSuccSelf _)
    rw [hEq]

/-- Total `u32` write delta contributed to loan `lid` by task `t`. -/
def taskLoanDelta (pol : SpawnPolicy) (lid : Pos4) (t : WorkerTask) : Nat :=
  match Pos4.beq t.loanId lid with
  | true => taskLeafMult pol t.rank t.remYields * t.writeDelta
  | false => 0

/-- Sums `taskLoanDelta pol lid` across `qs`. -/
def queueLoanDeltaSum (pol : SpawnPolicy) (lid : Pos4) (qs : List WorkerTask) : Nat :=
  qs.foldr (fun t acc => taskLoanDelta pol lid t + acc) 0

/-- Total pending `u32` write delta for loan `lid` across `w.fifoQueue` and `w.stealDeque`. -/
def worldLoanDeltaSum (pol : SpawnPolicy) (lid : Pos4) (w : WavefrontWorldV2026) : Nat :=
  queueLoanDeltaSum pol lid w.fifoQueue + queueLoanDeltaSum pol lid w.stealDeque

private theorem queueLoanDeltaSum_append (pol : SpawnPolicy) (lid : Pos4)
    (xs ys : List WorkerTask) :
    queueLoanDeltaSum pol lid (xs ++ ys) =
      queueLoanDeltaSum pol lid xs + queueLoanDeltaSum pol lid ys := by
  induction xs with
  | nil => exact Eq.symm (natAdd_zero_left _)
  | cons hd _ ih =>
    change taskLoanDelta pol lid hd + queueLoanDeltaSum pol lid (_ ++ ys) =
      (taskLoanDelta pol lid hd + queueLoanDeltaSum pol lid _) +
        queueLoanDeltaSum pol lid ys
    rw [ih, natAdd_assoc]

private theorem queueLoanDeltaSum_zero_of_not_hasLoan (pol : SpawnPolicy)
    (lid : Pos4) (qs : List WorkerTask) (hNo : anyTaskHasLoan lid qs = false) :
    queueLoanDeltaSum pol lid qs = 0 := by
  induction qs with
  | nil => rfl
  | cons t tl ih =>
    dsimp only [anyTaskHasLoan, List.foldr] at hNo
    have hSp := borFalseElim hNo
    change taskLoanDelta pol lid t + queueLoanDeltaSum pol lid tl = 0
    dsimp only [taskLoanDelta]
    rw [hSp.1, natAdd_zero_left]
    exact ih hSp.2

private theorem queueLoanDeltaSum_mkWorkers_same (pol : SpawnPolicy)
    (baseId k rc cy : Nat) (lid : Pos4) (sc wd : Nat) :
    queueLoanDeltaSum pol lid (mkWorkers baseId k rc cy lid sc wd) =
      (k * taskLeafMult pol rc cy) * wd := by
  revert baseId
  induction k with
  | zero =>
    intro _
    rw [natZeroMul, natZeroMul]
    rfl
  | succ m ih =>
    intro baseId
    change taskLoanDelta pol lid (WorkerTask.mk baseId rc cy lid sc wd) +
      queueLoanDeltaSum pol lid (mkWorkers (baseId + 1) m rc cy lid sc wd) =
      ((m + 1) * taskLeafMult pol rc cy) * wd
    dsimp only [taskLoanDelta]
    rw [pos4_beq_refl lid, ih (baseId + 1),
      natSuccMul m (taskLeafMult pol rc cy),
      natAddMul (m * taskLeafMult pol rc cy) (taskLeafMult pol rc cy) wd,
      natAdd_comm (taskLeafMult pol rc cy * wd) _]

private theorem mkWorkers_hasLoan_succ (baseId m rc cy : Nat) (lid : Pos4) (sc wd : Nat) :
    anyTaskHasLoan lid (mkWorkers baseId (m + 1) rc cy lid sc wd) = true := by
  change (Pos4.beq lid lid ||
    anyTaskHasLoan lid (mkWorkers (baseId + 1) m rc cy lid sc wd)) = true
  rw [pos4_beq_refl lid]
  rfl

/-- Two-phase tracking invariant for loan `lid` across `WavefrontConvergesV2026`. -/
def LoanTrackInv (pol : SpawnPolicy) (lid id0 : Pos4) (lens0 : V2026SubLens)
    (targetVal : Nat) (w : WavefrontWorldV2026) : Prop :=
  ∃ e : WfLoanEntryV2026,
    wfFindLoan lid w.loans = some e ∧
    e.id = id0 ∧
    e.lens = lens0 ∧
    wrapU32 (e.val + worldLoanDeltaSum pol lid w) = targetVal ∧
    match anyTaskHasLoan lid w.fifoQueue || anyTaskHasLoan lid w.stealDeque with
    | true => True
    | false => e.phase = .activeMut ∧ e.val = targetVal

private theorem execWavefrontPopped_preserves_loanTrackInv (pol : SpawnPolicy)
    (hPol : PolicyAdmissible pol)
    (lid id0 : Pos4) (lens0 : V2026SubLens) (targetVal : Nat)
    (hd : WorkerTask) (remFifo remSteal : List WorkerTask)
    (w wOut : WavefrontWorldV2026)
    (hRemFifo : queueMatchesLoansBool remFifo w.loans = true)
    (hRemSteal : queueMatchesLoansBool remSteal w.loans = true)
    (hAnyDecomp : (anyTaskHasLoan lid w.fifoQueue || anyTaskHasLoan lid w.stealDeque) =
      (Pos4.beq hd.loanId lid ||
        (anyTaskHasLoan lid remFifo || anyTaskHasLoan lid remSteal)))
    (hSumDecomp : worldLoanDeltaSum pol lid w =
      taskLoanDelta pol lid hd +
        (queueLoanDeltaSum pol lid remFifo + queueLoanDeltaSum pol lid remSteal))
    (hInv : LoanTrackInv pol lid id0 lens0 targetVal w)
    (hStep : execWavefrontPoppedV2026 pol hd remFifo remSteal w = .returned wOut) :
    LoanTrackInv pol lid id0 lens0 targetVal wOut := by
  cases hInv with
  | intro e he =>
    have hFindL := he.1
    have hId0 := he.2.1
    have hLens0 := he.2.2.1
    have hWrapTarget := he.2.2.2.1
    have hTailInv := he.2.2.2.2
    dsimp only [execWavefrontPoppedV2026] at hStep
    have hAdm : spawnAdmissible hd.rank (pol hd.rank).1 (pol hd.rank).2.1 = true :=
      hPol hd.rank
    rw [hAdm] at hStep
    dsimp only at hStep
    cases hEqHd : Pos4.beq hd.loanId lid with
    | false =>
      have hHdZero : taskLoanDelta pol lid hd = 0 := by
        dsimp only [taskLoanDelta]; rw [hEqHd]
      have hSumRem : worldLoanDeltaSum pol lid w =
          queueLoanDeltaSum pol lid remFifo + queueLoanDeltaSum pol lid remSteal := by
        rw [hSumDecomp, hHdZero, natAdd_zero_left]
      have hAnyRem :
          (anyTaskHasLoan lid w.fifoQueue || anyTaskHasLoan lid w.stealDeque) =
            (anyTaskHasLoan lid remFifo || anyTaskHasLoan lid remSteal) := by
        rw [hAnyDecomp, hEqHd]; rfl
      rw [hAnyRem] at hTailInv
      cases hy : hd.remYields with
      | succ y' =>
        rw [hy] at hStep
        injection hStep with hw
        rw [← hw]
        refine ⟨e, hFindL, hId0, hLens0, ?_, ?_⟩
        · dsimp only [worldLoanDeltaSum]
          rw [queueLoanDeltaSum_append, queueLoanDeltaSum_append,
            queueLoanDeltaSum_zero_of_not_hasLoan pol lid _
              (mkWorkers_not_hasLoan hd.loanId lid _ _ _ _ _ _ hEqHd),
            natAdd_zero_left]
          have hS0 : queueLoanDeltaSum pol lid
              [WorkerTask.mk hd.taskId hd.rank y' hd.loanId hd.scopeId hd.writeDelta] = 0 := by
            dsimp only [queueLoanDeltaSum, List.foldr, taskLoanDelta]
            rw [hEqHd]
          rw [hS0]
          change wrapU32 (e.val + (queueLoanDeltaSum pol lid remFifo +
            queueLoanDeltaSum pol lid remSteal)) = targetVal
          rw [← hSumRem]
          exact hWrapTarget
        · dsimp only
          rw [anyTaskHasLoan_append, anyTaskHasLoan_append,
            mkWorkers_not_hasLoan hd.loanId lid _ _ _ _ _ _ hEqHd]
          have hA0 : anyTaskHasLoan lid
              [WorkerTask.mk hd.taskId hd.rank y' hd.loanId hd.scopeId hd.writeDelta] = false := by
            dsimp only [anyTaskHasLoan, List.foldr]; rw [hEqHd]; rfl
          rw [hA0]
          have hOrF : (anyTaskHasLoan lid remFifo || false) = anyTaskHasLoan lid remFifo := by
            cases anyTaskHasLoan lid remFifo <;> rfl
          have hOrS : (false || anyTaskHasLoan lid remSteal) = anyTaskHasLoan lid remSteal := rfl
          rw [hOrF, hOrS]
          exact hTailInv
      | zero =>
        rw [hy] at hStep
        dsimp only at hStep
        cases hk : (pol hd.rank).1 with
        | succ _ =>
          rw [hk] at hStep
          injection hStep with hw
          rw [← hw]
          refine ⟨e, hFindL, hId0, hLens0, ?_, ?_⟩
          · dsimp only [worldLoanDeltaSum]
            rw [queueLoanDeltaSum_append,
              queueLoanDeltaSum_zero_of_not_hasLoan pol lid _
                (mkWorkers_not_hasLoan hd.loanId lid _ _ _ _ _ _ hEqHd),
              natAdd_zero_left, ← hSumRem]
            exact hWrapTarget
          · dsimp only
            rw [anyTaskHasLoan_append,
              mkWorkers_not_hasLoan hd.loanId lid _ _ _ _ _ _ hEqHd]
            exact hTailInv
        | zero =>
          rw [hk] at hStep
          dsimp only at hStep
          cases hFlHd : wfFindLoan hd.loanId w.loans with
          | none => rw [hFlHd] at hStep; nomatch hStep
          | some eHd =>
            rw [hFlHd] at hStep; dsimp only at hStep
            cases hScHd : loanPhaseMatchesScope eHd.phase hd.scopeId with
            | false => rw [hScHd] at hStep; nomatch hStep
            | true =>
              rw [hScHd] at hStep; dsimp only at hStep
              cases hPut : v2026SubLensPut eHd.lens w.mem
                  (wfEncodeU32LeRawBytes (wrapU32 (eHd.val + hd.writeDelta))) with
              | none => rw [hPut] at hStep; nomatch hStep
              | some _ =>
                rw [hPut] at hStep
                injection hStep with hw
                rw [← hw]
                refine ⟨e, ?_, hId0, hLens0, ?_, hTailInv⟩
                · dsimp only
                  rw [wfFindLoan_wfSetLoanEntryAt_ne w.loans hd.loanId lid _ _ hEqHd]
                  exact hFindL
                · dsimp only [worldLoanDeltaSum]
                  rw [← hSumRem]
                  exact hWrapTarget
    | true =>
      have hSameId := pos4_eq_of_beq hd.loanId lid hEqHd
      cases hy : hd.remYields with
      | succ y' =>
        rw [hy] at hStep
        injection hStep with hw
        rw [← hw]
        refine ⟨e, hFindL, hId0, hLens0, ?_, ?_⟩
        · dsimp only [worldLoanDeltaSum]
          rw [queueLoanDeltaSum_append, queueLoanDeltaSum_append, hSameId,
            queueLoanDeltaSum_mkWorkers_same]
          have hSingle : queueLoanDeltaSum pol lid
              [WorkerTask.mk hd.taskId hd.rank y' lid hd.scopeId hd.writeDelta] =
              taskLeafMult pol hd.rank y' * hd.writeDelta := by
            dsimp only [queueLoanDeltaSum, List.foldr, taskLoanDelta]
            rw [pos4_beq_refl lid]
            rfl
          rw [hSingle]
          have hHdVal : taskLoanDelta pol lid hd =
              taskLeafMult pol hd.rank (y' + 1) * hd.writeDelta := by
            dsimp only [taskLoanDelta]; rw [hEqHd, hy]
          have hUnf1 := taskLeafMult_unfold pol hPol hd.rank (y' + 1)
          have hUnf0 := taskLeafMult_unfold pol hPol hd.rank y'
          let C := (pol hd.rank).1 * taskLeafMult pol (pol hd.rank).2.1 (pol hd.rank).2.2
          let Z :=
            match (pol hd.rank).1 with
            | 0 => 1
            | k' + 1 =>
              (k' + 1) * taskLeafMult pol (pol hd.rank).2.1 (pol hd.rank).2.2
          have hMultSplit : taskLeafMult pol hd.rank (y' + 1) * hd.writeDelta =
              C * hd.writeDelta + taskLeafMult pol hd.rank y' * hd.writeDelta := by
            rw [hUnf1, hUnf0, natSuccMul y' C, natAdd_comm (y' * C) C,
              natAdd_assoc C (y' * C) Z, natAddMul C (y' * C + Z) hd.writeDelta]
          let F := queueLoanDeltaSum pol lid remFifo
          let S := queueLoanDeltaSum pol lid remSteal
          let Y := taskLeafMult pol hd.rank y' * hd.writeDelta
          let W := C * hd.writeDelta
          have hRearr : (F + Y) + (W + S) = (W + Y) + (F + S) := by
            rw [natAdd_comm F Y, natAdd_assoc Y F (W + S), ← natAdd_assoc F W S,
              natAdd_comm F W, natAdd_assoc W F S, ← natAdd_assoc Y W (F + S),
              natAdd_comm Y W]
          change wrapU32 (e.val + ((F + Y) + (W + S))) = targetVal
          rw [hRearr, ← hMultSplit, ← hHdVal, ← hSumDecomp]
          exact hWrapTarget
        · dsimp only
          rw [anyTaskHasLoan_append, hSameId]
          have hA1 : anyTaskHasLoan lid
              [WorkerTask.mk hd.taskId hd.rank y' lid hd.scopeId hd.writeDelta] = true := by
            dsimp only [anyTaskHasLoan, List.foldr]; rw [pos4_beq_refl lid]; rfl
          rw [hA1]
          have hT1 : (anyTaskHasLoan lid remFifo || true) = true := by
            cases anyTaskHasLoan lid remFifo <;> rfl
          rw [hT1]
          exact True.intro
      | zero =>
        rw [hy] at hStep
        dsimp only at hStep
        cases hk : (pol hd.rank).1 with
        | succ k' =>
          rw [hk] at hStep
          injection hStep with hw
          rw [← hw]
          refine ⟨e, hFindL, hId0, hLens0, ?_, ?_⟩
          · dsimp only [worldLoanDeltaSum]
            rw [queueLoanDeltaSum_append, hSameId, queueLoanDeltaSum_mkWorkers_same]
            have hHdVal : taskLoanDelta pol lid hd =
                ((k' + 1) * taskLeafMult pol (pol hd.rank).2.1 (pol hd.rank).2.2) *
                  hd.writeDelta := by
              dsimp only [taskLoanDelta]
              rw [hEqHd, hy, taskLeafMult_unfold pol hPol hd.rank 0, hk,
                natZeroMul, natAdd_zero_left]
            let F := queueLoanDeltaSum pol lid remFifo
            let S := queueLoanDeltaSum pol lid remSteal
            let W := ((k' + 1) * taskLeafMult pol (pol hd.rank).2.1 (pol hd.rank).2.2) *
              hd.writeDelta
            have hRearr : F + (W + S) = W + (F + S) := by
              rw [← natAdd_assoc F W S, natAdd_comm F W, natAdd_assoc W F S]
            change wrapU32 (e.val + (F + (W + S))) = targetVal
            rw [hRearr]
            dsimp only [W, F, S]
            rw [← hHdVal, ← hSumDecomp]
            exact hWrapTarget
          · dsimp only
            rw [anyTaskHasLoan_append, hSameId, mkWorkers_hasLoan_succ]
            dsimp only [Bool.or]
            cases anyTaskHasLoan lid remFifo <;> exact True.intro
        | zero =>
          rw [hk] at hStep
          dsimp only at hStep
          rw [hSameId, hFindL] at hStep
          dsimp only at hStep
          cases hSc : loanPhaseMatchesScope e.phase hd.scopeId with
          | false => rw [hSc] at hStep; nomatch hStep
          | true =>
            rw [hSc] at hStep
            dsimp only at hStep
            have hPhEq : e.phase = .spatialCheckedOut hd.scopeId := by
              cases hp : e.phase with
              | spatialCheckedOut s =>
                rw [hp] at hSc
                dsimp only [loanPhaseMatchesScope] at hSc
                exact congrArg WfLoanPhase.spatialCheckedOut (natEq_of_beq s hd.scopeId hSc)
              | activeMut | frozen | ended =>
                rw [hp] at hSc; exact False.elim (boolFalseNeTrue hSc)
            cases hPut : v2026SubLensPut e.lens w.mem
                (wfEncodeU32LeRawBytes (wrapU32 (e.val + hd.writeDelta))) with
            | none => rw [hPut] at hStep; nomatch hStep
            | some _ =>
              rw [hPut] at hStep
              injection hStep with hw
              rw [← hw]
              have hScF := anyTaskHasLoanScope_eq_anyTaskHasLoan_of_queueMatches
                lid hd.scopeId e remFifo w.loans hFindL hPhEq hRemFifo
              have hScS := anyTaskHasLoanScope_eq_anyTaskHasLoan_of_queueMatches
                lid hd.scopeId e remSteal w.loans hFindL hPhEq hRemSteal
              have hHdOne : taskLoanDelta pol lid hd = hd.writeDelta := by
                dsimp only [taskLoanDelta]
                rw [hEqHd, hy, taskLeafMult_unfold pol hPol hd.rank 0, hk,
                  natZeroMul, natAdd_zero_left, natOneMul]
              let remSum := queueLoanDeltaSum pol lid remFifo +
                queueLoanDeltaSum pol lid remSteal
              have hWrapStep :
                  wrapU32 (wrapU32 (e.val + hd.writeDelta) + remSum) = targetVal := by
                rw [wrapU32_add_left, natAdd_assoc e.val hd.writeDelta remSum,
                  ← hHdOne, ← hSumDecomp]
                exact hWrapTarget
              let stillInFlight :=
                anyTaskHasLoanScope lid hd.scopeId remFifo ||
                anyTaskHasLoanScope lid hd.scopeId remSteal
              let nextPh := match stillInFlight with
                | true => WfLoanPhase.spatialCheckedOut hd.scopeId
                | false => WfLoanPhase.activeMut
              refine ⟨⟨e.id, nextPh, e.lens, wrapU32 (e.val + hd.writeDelta)⟩,
                wfFindLoan_wfSetLoanEntryAt_same w.loans lid nextPh _ e hFindL,
                hId0, hLens0, hWrapStep, ?_⟩
              dsimp only [nextPh, stillInFlight]
              rw [hScF, hScS]
              cases hRemAny : (anyTaskHasLoan lid remFifo || anyTaskHasLoan lid remSteal) with
              | true => exact True.intro
              | false =>
                have hNoBoth := borFalseElim hRemAny
                have hRemSum0 : remSum = 0 := by
                  dsimp only [remSum]
                  rw [queueLoanDeltaSum_zero_of_not_hasLoan pol lid remFifo hNoBoth.1,
                    queueLoanDeltaSum_zero_of_not_hasLoan pol lid remSteal hNoBoth.2]
                refine ⟨rfl, ?_⟩
                rw [hRemSum0, ← natAdd_comm 0 _, natAdd_zero_left, wrapU32_idem] at hWrapStep
                exact hWrapStep

private theorem wavefrontStep_preserves_loanTrackInv (pol : SpawnPolicy)
    (hPol : PolicyAdmissible pol)
    (lid id0 : Pos4) (lens0 : V2026SubLens) (targetVal : Nat)
    (w wNext : WavefrontWorldV2026)
    (hQ : QueueMatchesLoansV2026 w)
    (hInv : LoanTrackInv pol lid id0 lens0 targetVal w)
    (hStep : evalHybridCmdV2026 (.poolWavefrontStep pol) w = .returned wNext) :
    LoanTrackInv pol lid id0 lens0 targetVal wNext := by
  dsimp only [evalHybridCmdV2026] at hStep
  have hQF := bandLeft hQ
  have hQS := bandRight hQ
  cases hF : w.fifoQueue with
  | cons hd ft =>
    rw [hF] at hStep hQF
    dsimp only [queueMatchesLoansBool, List.foldr] at hQF
    apply execWavefrontPopped_preserves_loanTrackInv pol hPol lid id0 lens0 targetVal
      hd ft w.stealDeque w wNext (bandRight hQF) hQS _ _ hInv hStep
    · rw [hF]; dsimp only [anyTaskHasLoan, List.foldr]
      cases Pos4.beq hd.loanId lid <;> rfl
    · dsimp only [worldLoanDeltaSum]; rw [hF]
      dsimp only [queueLoanDeltaSum, List.foldr]; rw [natAdd_assoc]
  | nil =>
    rw [hF] at hStep
    cases hS : w.stealDeque with
    | nil => rw [hS] at hStep; nomatch hStep
    | cons hd stTail =>
      rw [hS] at hStep hQS
      dsimp only [queueMatchesLoansBool, List.foldr] at hQS
      apply execWavefrontPopped_preserves_loanTrackInv pol hPol lid id0 lens0 targetVal
        hd [] stTail w wNext rfl (bandRight hQS) _ _ hInv hStep
      · rw [hF, hS]; rfl
      · dsimp only [worldLoanDeltaSum]; rw [hF, hS]
        dsimp only [queueLoanDeltaSum, List.foldr]
        rw [natAdd_zero_left, natAdd_zero_left]

private theorem wfFindLoan_some_of_hasLoan_queueMatches (lid : Pos4)
    (qs : List WorkerTask) (loans : List WfLoanEntryV2026)
    (hAny : anyTaskHasLoan lid qs = true)
    (hQ : queueMatchesLoansBool qs loans = true) :
    ∃ e0 : WfLoanEntryV2026, wfFindLoan lid loans = some e0 ∧
      loanPhaseIsLive e0.phase = true := by
  induction qs with
  | nil => exact False.elim (boolFalseNeTrue hAny)
  | cons t tl ih =>
    dsimp only [anyTaskHasLoan, List.foldr] at hAny
    dsimp only [queueMatchesLoansBool, List.foldr] at hQ
    cases hEq : Pos4.beq t.loanId lid with
    | false =>
      rw [hEq] at hAny
      exact ih hAny (bandRight hQ)
    | true =>
      have hSame := pos4_eq_of_beq t.loanId lid hEq
      have hHd := bandLeft hQ
      rw [hSame] at hHd
      cases hFl : wfFindLoan lid loans with
      | none => rw [hFl] at hHd; exact False.elim (boolFalseNeTrue hHd)
      | some e0 =>
        rw [hFl] at hHd
        dsimp only at hHd
        refine ⟨e0, rfl, ?_⟩
        cases hp : e0.phase with
        | spatialCheckedOut _ => rfl
        | activeMut | frozen | ended =>
          rw [hp] at hHd; exact False.elim (boolFalseNeTrue hHd)

/-- Universal post-drain `.activeMut` reclamation theorem (`[propext]`): across
any `WavefrontConvergesV2026 pol w0 wFinal` from a world satisfying
`Firewall`-shielded `LoansSyncedWithMemV2026` and `QueueMatchesLoansV2026`, every
loan `lid` with at least one queued task in `w0` finishes in `.activeMut` phase
in `wFinal` with `wrapU32 (e0.val + worldLoanDeltaSum pol lid w0)` encoded in
unmodified `V2026_06_01.MirSemantics.Memory`! -/
theorem universal_post_drain_activeMut_reclaim
    (pol : SpawnPolicy) (hPol : PolicyAdmissible pol)
    (w0 wFinal : WavefrontWorldV2026)
    (hSync0 : LoansSyncedWithMemV2026 w0.loans w0.mem)
    (hQ0 : QueueMatchesLoansV2026 w0)
    (hConv : WavefrontConvergesV2026 pol w0 wFinal)
    (lid : Pos4)
    (hQueued : (anyTaskHasLoan lid w0.fifoQueue || anyTaskHasLoan lid w0.stealDeque) = true) :
    ∃ e0 : WfLoanEntryV2026,
      wfFindLoan lid w0.loans = some e0 ∧
      wfFindLoan lid wFinal.loans =
        some ⟨e0.id, .activeMut, e0.lens,
          wrapU32 (e0.val + worldLoanDeltaSum pol lid w0)⟩ ∧
      ActivePureLoanAtV2026 lid e0.lens
        (wrapU32 (e0.val + worldLoanDeltaSum pol lid w0)) wFinal ∧
      v2026SubLensGet e0.lens wFinal.mem =
        some (wfEncodeU32LeAbsBytes (wrapU32 (e0.val + worldLoanDeltaSum pol lid w0))) := by
  have hExE0 : ∃ e0 : WfLoanEntryV2026, wfFindLoan lid w0.loans = some e0 ∧
      loanPhaseIsLive e0.phase = true := by
    cases hAF : anyTaskHasLoan lid w0.fifoQueue with
    | true =>
      exact wfFindLoan_some_of_hasLoan_queueMatches lid w0.fifoQueue w0.loans
        hAF (bandLeft hQ0)
    | false =>
      rw [hAF] at hQueued
      exact wfFindLoan_some_of_hasLoan_queueMatches lid w0.stealDeque w0.loans
        hQueued (bandRight hQ0)
  cases hExE0 with
  | intro e0 he0 =>
    let targetVal := wrapU32 (e0.val + worldLoanDeltaSum pol lid w0)
    have hInitInv : LoanTrackInv pol lid e0.id e0.lens targetVal w0 := by
      refine ⟨e0, he0.1, rfl, rfl, rfl, ?_⟩
      rw [hQueued]
      exact True.intro
    have hWalk : ∀ (u uF : WavefrontWorldV2026),
        WavefrontConvergesV2026 pol u uF →
        LoansSyncedWithMemV2026 u.loans u.mem →
        QueueMatchesLoansV2026 u →
        LoanTrackInv pol lid e0.id e0.lens targetVal u →
        LoansSyncedWithMemV2026 uF.loans uF.mem ∧
        LoanTrackInv pol lid e0.id e0.lens targetVal uF := by
      intro u uF hC
      induction hC with
      | quiescent _ _ =>
        intro hs _ hi
        exact ⟨hs, hi⟩
      | step u0 u1 _ hNe hSt _ _ ih =>
        intro hs hq hi
        cases nonEmptyPool_wavefrontStep_returns pol hPol u0 hNe hs hq with
        | intro u1' hu1' =>
          have hEq1 : u1' = u1 := by
            rw [hSt] at hu1'
            injection hu1'.1 with hSame
            exact hSame.symm
          rw [hEq1] at hu1'
          have hi1 := wavefrontStep_preserves_loanTrackInv pol hPol lid e0.id
            e0.lens targetVal u0 u1 hq hi hSt
          exact ih hu1'.2.1 hu1'.2.2.1 hi1
    have hEnd := hWalk w0 wFinal hConv hSync0 hQ0 hInitInv
    have hExEmp := wavefrontConvergesV2026_extract_fuel pol w0 wFinal hConv
    cases hEnd.2 with
    | intro eF heF =>
      have hNoF :
          (anyTaskHasLoan lid wFinal.fifoQueue || anyTaskHasLoan lid wFinal.stealDeque) = false := by
        rw [hExEmp.1, hExEmp.2.1]; rfl
      have hTailF := heF.2.2.2.2
      rw [hNoF] at hTailF
      have hEfEq : eF = ⟨e0.id, .activeMut, e0.lens, targetVal⟩ := by
        cases eF with
        | mk i p l v =>
          dsimp only at heF hTailF
          rw [heF.2.1, hTailF.1, heF.2.2.1, hTailF.2]
      have hFindFinal : wfFindLoan lid wFinal.loans =
          some ⟨e0.id, .activeMut, e0.lens, targetVal⟩ := by
        rw [← hEfEq]; exact heF.1
      have hSyncedF := wfFindLoan_synced_live_props wFinal.loans wFinal.mem lid
        ⟨e0.id, .activeMut, e0.lens, targetVal⟩ hEnd.1 hFindFinal rfl
      exact ⟨e0, he0.1, hFindFinal,
        ⟨⟨e0.id, .activeMut, e0.lens, targetVal⟩, hFindFinal, rfl, rfl, rfl⟩,
        hSyncedF.2.2.2⟩

/-- Compositional `VSepWpOrdRelV2026` wavefront drain (`[propext]`): drains any
`WavefrontWorldV2026` to quiescence while advancing `vMinStep` and preserving
every spatial `VProp` frame `F` and `Firewall`-shielded `WorldMatchesV2026`. -/
theorem vsepWpOrdRelV2026_wavefrontDrain
    (pol : SpawnPolicy) (hPol : PolicyAdmissible pol)
    (vIn : View) (F : VProp) (rIn : ResTrie ResElem) (wIn : WavefrontWorldV2026)
    (hPre : (vsep vemp F).holds vIn rIn)
    (hM : WorldMatchesV2026 vIn rIn wIn) :
    ∃ (wDrained : WavefrontWorldV2026) (rOut : ResTrie ResElem) (vOut : View),
      WavefrontConvergesV2026 pol wIn wDrained ∧
      ViewLe vIn vOut ∧
      extractPoolCap rOut = extractPoolCap rIn ∧
      (vsep (vMinStep wDrained.stepCount) F).holds vOut rOut ∧
      WorldMatchesV2026 vOut rOut wDrained := by
  have hStepWp := vsepWpOrdRelV2026_wavefrontStep_strict_descent pol hPol
  have hInd : ∀ (ord : CnfOrd), isCanonicalCnf ord = true →
      ∀ (vCur : View) (rCur : ResTrie ResElem) (wCur : WavefrontWorldV2026),
        worldMeasureV2026 wCur = ord →
        (vsep vemp F).holds vCur rCur →
        WorldMatchesV2026 vCur rCur wCur →
        ∃ (wDrained : WavefrontWorldV2026) (rOut : ResTrie ResElem) (vOut : View),
          WavefrontConvergesV2026 pol wCur wDrained ∧
          ViewLe vCur vOut ∧
          extractPoolCap rOut = extractPoolCap rCur ∧
          (vsep (vMinStep wDrained.stepCount) F).holds vOut rOut ∧
          WorldMatchesV2026 vOut rOut wDrained := by
    intro ord hCan
    induction cnfAcc_all ord hCan with
    | intro x _ ih =>
      intro vCur rCur wCur hMeas hPreCur hMCur
      cases hNe : wfPoolIsNonEmpty wCur with
      | false =>
        let vOut := bumpView0 vCur wCur.stepCount
        have hVLe : ViewLe vCur vOut :=
          viewLe_bumpView0 vCur wCur.stepCount hMCur.viewOk
        have hFOut : F.holds vOut rCur :=
          F.upClosed vCur vOut rCur rCur hVLe (resTrieSub_refl rCur)
            (vsep_vemp_elim vCur F rCur hPreCur)
        have hMinHold : (vMinStep wCur.stepCount).holds vOut .empty := by
          dsimp only [vMinStep, vOut]
          rw [viewGet_bumpView0_zero]
          exact natBle_refl wCur.stepCount
        have hViewOut : Nat.ble (viewGet vOut 0) wCur.stepCount = true := by
          dsimp only [vOut]
          rw [viewGet_bumpView0_zero]
          exact natBle_refl wCur.stepCount
        have hMOut : WorldMatchesV2026 vOut rCur wCur :=
          WorldMatchesV2026.mk hViewOut hMCur.loansMemOk hMCur.queueLoansOk
            hMCur.poolDebtOk hMCur.cellOk hMCur.checkedLoanOk
        exact ⟨wCur, rCur, vOut, WavefrontConvergesV2026.quiescent wCur hNe, hVLe, rfl,
          ⟨.empty, rCur, resTrieMerge_empty_left_fuel resFuel rCur, hMinHold, hFOut⟩,
          hMOut⟩
      | true =>
        cases hStepWp.run vCur F rCur wCur hNe hPreCur hMCur with
        | intro wNext hw =>
          cases hw with
          | intro rMid hr =>
            cases hr with
            | intro vMid hv =>
              have hStepEv := hv.1
              have hVLe1 := hv.2.1
              have hPc1 := hv.2.2.1
              have hPost1 := hv.2.2.2.1
              have hM1 := hv.2.2.2.2.1
              have hLtOrig :
                  cnfLt (worldMeasureV2026 wNext) (worldMeasureV2026 wCur) = true :=
                hv.2.2.2.2.2
              have hLtX : cnfLt (worldMeasureV2026 wNext) x = true := by
                rw [← hMeas]; exact hLtOrig
              have hFMid : F.holds vMid rMid :=
                vsep_drop_left (vMinStep wNext.stepCount) F vMid rMid hPost1
              have hPreMid : (vsep vemp F).holds vMid rMid :=
                vsep_vemp_intro vMid F rMid hFMid
              have hCanNext : isCanonicalCnf (worldMeasureV2026 wNext) = true :=
                worldMeasureV2026_canonical wNext
              -- Note: `vsepWpOrdRelV2026_wavefrontStep_strict_descent` preserves `rMid = rCur`
              -- up to `extractPoolCap` and `WorldMatchesV2026 vMid rMid wNext`.
              cases ih (worldMeasureV2026 wNext) hCanNext hLtX hCanNext
                  vMid rMid wNext rfl hPreMid hM1 with
              | intro wDrained hD =>
                cases hD with
                | intro rOut hrD =>
                  cases hrD with
                  | intro vOut hvD =>
                    exact ⟨wDrained, rOut, vOut,
                      WavefrontConvergesV2026.step wCur wNext wDrained hNe hStepEv hLtOrig hvD.1,
                      viewLe_trans vCur vMid vOut hVLe1 hvD.2.1,
                      Eq.trans hvD.2.2.1 hPc1,
                      hvD.2.2.2.1,
                      hvD.2.2.2.2⟩
  exact hInd (worldMeasureV2026 wIn) (worldMeasureV2026_canonical wIn) vIn rIn wIn rfl hPre hM

/-- Composes all five wavefront lifecycle stages across a single
`(View, ResTrie ResElem, WavefrontWorldV2026)` chain over unmodified
`V2026_06_01.MirSemantics.Memory`, preserving `WorldMatchesV2026` and spatial frame `F`:
(1) `.checkoutLoan`, (2) `.submitTaskBurst` consuming `ordDebtProp`,
(3) `WavefrontConvergesV2026` drain, (4) `.activeMut` reclamation with accumulated
`u32` delta, and (5) `.pureLiftSafe` direct mutation (`[propext]`). -/
theorem vsepWpOrdRelV2026_fiveStage_chained_lifecycle
    (pol : SpawnPolicy) (hPol : PolicyAdmissible pol)
    (lid : Pos4) (subL : V2026SubLens)
    (vInit scopeId rank remYields writeDelta pureDelta : Nat)
    (ordSpent : CnfOrd)
    (hCanSpent : isCanonicalCnf ordSpent = true)
    (hBudget : cnfLt (burstTaskDelta rank remYields) ordSpent = true)
    (v0 : View) (F : VProp) (r0 : ResTrie ResElem) (w0 : WavefrontWorldV2026)
    (hChkG : CheckoutLoanGuardV2026 lid subL vInit w0)
    (hPre0 : (vsep (ordDebtProp ordSpent) F).holds v0 r0)
    (hM0 : WorldMatchesV2026 v0 r0 w0) :
    let vDrained := wrapU32 (vInit + taskLeafMult pol rank remYields * writeDelta)
    let vFinal := wrapU32 (vDrained + pureDelta)
    ∃ (w1 w2 w3 w4 : WavefrontWorldV2026) (r1 r2 r3 r4 : ResTrie ResElem)
      (v1 v2 v3 v4 : View),
      evalHybridCmdV2026 (.checkoutLoan lid scopeId) w0 = .returned w1 ∧
      WorldMatchesV2026 v1 r1 w1 ∧
      OrdRelStepV2026 .preserve w0 w1 ∧
      evalHybridCmdV2026 (.submitTaskBurst rank remYields lid scopeId writeDelta) w1 =
        .returned w2 ∧
      WorldMatchesV2026 v2 r2 w2 ∧
      OrdRelStepV2026 (.amortized ordSpent) w1 w2 ∧
      WavefrontConvergesV2026 pol w2 w3 ∧
      WorldMatchesV2026 v3 r3 w3 ∧
      ActivePureLoanAtV2026 lid subL vDrained w3 ∧
      v2026SubLensGet subL w3.mem = some (wfEncodeU32LeAbsBytes vDrained) ∧
      evalHybridCmdV2026 (.pureLiftSafe lid pureDelta) w3 = .returned w4 ∧
      WorldMatchesV2026 v4 r4 w4 ∧
      OrdRelStepV2026 .preserve w3 w4 ∧
      ViewLe v0 v4 ∧
      extractPoolCap r4 = extractPoolCap r0 ∧
      (vsep (vMinStep w3.stepCount) F).holds v4 r4 ∧
      v2026SubLensGet subL w4.mem = some (wfEncodeU32LeAbsBytes vFinal) ∧
      (∀ otherL : V2026SubLens,
        v2026LensDisjoint subL otherL = true →
        v2026SubLensGet otherL w4.mem = v2026SubLensGet otherL w3.mem) := by
  intro vDrained vFinal
  cases hChkG.1 with
  | intro e0 he0 =>
    have hNoTasks0 := hChkG.2
    have hNoF0 : anyTaskHasLoan lid w0.fifoQueue = false :=
      trueOfBnotTrue (bandLeft hNoTasks0)
    have hNoS0 : anyTaskHasLoan lid w0.stealDeque = false :=
      trueOfBnotTrue (bandRight hNoTasks0)
    let wpChk := vsepWpOrdRelV2026_frame (.checkoutLoan lid scopeId) .preserve
      (CheckoutLoanGuardV2026 lid subL vInit) vemp (ordDebtProp ordSpent)
      (fun _ => checkedOutLoanProp lid scopeId vInit)
      (vsepWpOrdRelV2026_checkoutLoan lid subL vInit scopeId)
    have hPreChk : (vsep (vsep vemp (ordDebtProp ordSpent)) F).holds v0 r0 :=
      (vsep_assoc_rl vemp (ordDebtProp ordSpent) F).imp v0 r0
        (vsep_vemp_intro v0 (vsep (ordDebtProp ordSpent) F) r0 hPre0)
    cases wpChk.run v0 F r0 w0 hChkG hPreChk hM0 with
    | intro w1 hw1Ex =>
      cases hw1Ex with
      | intro r1 hr1Ex =>
        cases hr1Ex with
        | intro v1 hv1 =>
          have hEv1 := hv1.1
          have hV01 := hv1.2.1
          have hPc01 := hv1.2.2.1
          have hPost1 := hv1.2.2.2.1
          have hM1 := hv1.2.2.2.2.1
          have hOrd1 := hv1.2.2.2.2.2
          have hEv1Unf := hEv1
          dsimp only [evalHybridCmdV2026, execCheckoutLoanV2026] at hEv1Unf
          rw [hNoTasks0, he0.1] at hEv1Unf
          dsimp only at hEv1Unf
          rw [he0.2.1] at hEv1Unf
          injection hEv1Unf with hw1Eq
          have hFind1 : wfFindLoan lid w1.loans =
              some ⟨e0.id, .spatialCheckedOut scopeId, e0.lens, e0.val⟩ := by
            rw [← hw1Eq]
            exact wfFindLoan_wfSetLoanEntryAt_same w0.loans lid
              (.spatialCheckedOut scopeId) e0.val e0 he0.1
          have hPre2 : (vsep (vsep (ordDebtProp ordSpent)
              (checkedOutLoanProp lid scopeId vInit)) F).holds v1 r1 := by
            cases hPost1 with
            | intro ra hra =>
              cases hra with
              | intro rb hcab =>
                exact ⟨ra, rb, hcab.1,
                  (vsep_comm (checkedOutLoanProp lid scopeId vInit)
                    (ordDebtProp ordSpent)).imp v1 ra hcab.2.1,
                  hcab.2.2⟩
          let wpBurst := (vsepWpOrdRelV2026_submitTaskBurst_amortized_growth
            rank remYields lid scopeId writeDelta vInit ordSpent hCanSpent hBudget).1
          cases wpBurst.run v1 F r1 w1 True.intro hPre2 hM1 with
          | intro w2 hw2Ex =>
            cases hw2Ex with
            | intro r2 hr2Ex =>
              cases hr2Ex with
              | intro v2 hv2 =>
                have hEv2 := hv2.1
                have hV12 := hv2.2.1
                have hPc12 := hv2.2.2.1
                have hPost2 := hv2.2.2.2.1
                have hM2 := hv2.2.2.2.2.1
                have hOrd2 := hv2.2.2.2.2.2
                have hEv2Unf := hEv2
                dsimp only [evalHybridCmdV2026, execSubmitTaskBurstV2026] at hEv2Unf
                rw [hFind1] at hEv2Unf
                dsimp only [loanPhaseMatchesScope] at hEv2Unf
                rw [natBeq_refl scopeId] at hEv2Unf
                injection hEv2Unf with hw2Eq
                have hFind2 : wfFindLoan lid w2.loans =
                    some ⟨e0.id, .spatialCheckedOut scopeId, e0.lens, e0.val⟩ := by
                  rw [← hw2Eq]; exact hFind1
                have hQueued2 :
                    (anyTaskHasLoan lid w2.fifoQueue || anyTaskHasLoan lid w2.stealDeque) = true := by
                  rw [← hw2Eq]
                  dsimp only [anyTaskHasLoan, List.foldr]
                  rw [pos4_beq_refl lid]
                  rfl
                have hDeltaSum2 : worldLoanDeltaSum pol lid w2 =
                    taskLeafMult pol rank remYields * writeDelta := by
                  dsimp only [worldLoanDeltaSum]
                  rw [← hw2Eq]
                  change (taskLoanDelta pol lid (WorkerTask.mk w1.nextTaskId
                    rank remYields lid scopeId writeDelta) +
                    queueLoanDeltaSum pol lid w1.fifoQueue) +
                      queueLoanDeltaSum pol lid w1.stealDeque = _
                  dsimp only [taskLoanDelta]
                  rw [pos4_beq_refl lid, ← hw1Eq]
                  dsimp only
                  rw [queueLoanDeltaSum_zero_of_not_hasLoan pol lid w0.fifoQueue hNoF0,
                    queueLoanDeltaSum_zero_of_not_hasLoan pol lid w0.stealDeque hNoS0]
                  rfl
                cases vsepWpOrdRelV2026_wavefrontDrain pol hPol v2 F r2 w2 hPost2 hM2 with
                | intro w3 hw3Ex =>
                  cases hw3Ex with
                  | intro r3 hr3Ex =>
                    cases hr3Ex with
                    | intro v3 hv3 =>
                      have hConv := hv3.1
                      have hV23 := hv3.2.1
                      have hPc23 := hv3.2.2.1
                      have hPost3 := hv3.2.2.2.1
                      have hM3 := hv3.2.2.2.2
                      cases universal_post_drain_activeMut_reclaim pol hPol w2 w3
                          hM2.loansMemOk hM2.queueLoansOk hConv lid hQueued2 with
                      | intro e2 he2 =>
                        rw [hFind2] at he2
                        injection he2.1 with hSameE2
                        rw [← hSameE2] at he2
                        dsimp only at he2
                        rw [hDeltaSum2, he0.2.2.1, he0.2.2.2] at he2
                        have hAct3 : ActivePureLoanAtV2026 lid subL vDrained w3 :=
                          he2.2.2.1
                        have hGet3 : v2026SubLensGet subL w3.mem =
                            some (wfEncodeU32LeAbsBytes vDrained) := he2.2.2.2
                        let F3 := vsep (vMinStep w3.stepCount) F
                        let wpPurePair :=
                          vsepWpOrdRelV2026_pure_fastpath lid subL vDrained pureDelta
                        have hPre4 : (vsep vemp F3).holds v3 r3 :=
                          vsep_vemp_intro v3 F3 r3 hPost3
                        cases wpPurePair.1.run v3 F3 r3 w3 hAct3 hPre4 hM3 with
                        | intro w4 hw4Ex =>
                          cases hw4Ex with
                          | intro r4 hr4Ex =>
                            cases hr4Ex with
                            | intro v4 hv4 =>
                              have hEv4 := hv4.1
                              have hV34 := hv4.2.1
                              have hPc34 := hv4.2.2.1
                              have hPost4 : F3.holds v4 r4 :=
                                vsep_vemp_elim v4 F3 r4 hv4.2.2.2.1
                              have hM4 := hv4.2.2.2.2.1
                              have hOrd4 := hv4.2.2.2.2.2
                              cases wpPurePair.2 v3 F3 r3 w3 hAct3 hPre4 hM3 with
                              | intro w4' hw4' =>
                                have hSameW4 : w4' = w4 := by
                                  rw [hEv4] at hw4'
                                  injection hw4'.1 with hEqW4
                                  exact hEqW4.symm
                                rw [hSameW4] at hw4'
                                have hV04 : ViewLe v0 v4 :=
                                  viewLe_trans v0 v3 v4
                                    (viewLe_trans v0 v2 v3
                                      (viewLe_trans v0 v1 v2 hV01 hV12) hV23) hV34
                                have hPc04 : extractPoolCap r4 = extractPoolCap r0 :=
                                  Eq.trans hPc34 (Eq.trans hPc23 (Eq.trans hPc12 hPc01))
                                exact ⟨w1, w2, w3, w4, r1, r2, r3, r4, v1, v2, v3, v4,
                                  hEv1, hM1, hOrd1,
                                  hEv2, hM2, hOrd2,
                                  hConv, hM3, hAct3, hGet3,
                                  hEv4, hM4, hOrd4,
                                  hV04, hPc04, hPost4,
                                  hw4'.2.2.2.2.2.1, hw4'.2.2.2.2.2.2⟩

/-! ## 5. `Firewall` / `IndexedCut`-Shielded `stepMirFn` & `runCfgSteps` Operational Bridge -/

/-- `Anneal.Firewall`-shielded assertion that `m : Memory` owns `bs` at `L : V2026SubLens`,
keeping large `Memory` expressions opaque during `stepMirFn` / `runCfgSteps` transitions. -/
def MirGlobalSliceAtV2026 (m : Memory) (L : V2026SubLens) (bs : List AbstractByte) : Prop :=
  Firewall wfMirMemFrameFirewallTag (v2026SubLensGet L m = some bs)

/-- Seals a `v2026SubLensGet` fact behind `Firewall wfMirMemFrameFirewallTag`. -/
theorem seal_mirGlobalSliceAtV2026 {m : Memory} {L : V2026SubLens} {bs : List AbstractByte}
    (h : v2026SubLensGet L m = some bs) : MirGlobalSliceAtV2026 m L bs :=
  Firewall.wrap wfMirMemFrameFirewallTag h

/-- Unseals `MirGlobalSliceAtV2026` at an observation boundary. -/
theorem unseal_mirGlobalSliceAtV2026 {m : Memory} {L : V2026SubLens} {bs : List AbstractByte}
    (h : MirGlobalSliceAtV2026 m L bs) : v2026SubLensGet L m = some bs :=
  Firewall.unwrap h

/-- Transfers `MirGlobalSliceAtV2026` across any `Memory` transition preserving `.globals`
without unfolding `m` or `m'` (`[]` zero axioms). -/
theorem mirGlobalSliceAtV2026_of_globals_eq {m m' : Memory}
    {L : V2026SubLens} {bs : List AbstractByte}
    (hGlob : m'.globals = m.globals)
    (hAt : MirGlobalSliceAtV2026 m L bs) :
    MirGlobalSliceAtV2026 m' L bs := by
  apply seal_mirGlobalSliceAtV2026
  have h0 := unseal_mirGlobalSliceAtV2026 hAt
  unfold v2026SubLensGet at h0 ⊢
  rw [hGlob]
  exact h0

/-- Transfers `MirGlobalSliceAtV2026` across any disjoint `v2026SubLensPut` (`[propext]`). -/
theorem mirGlobalSliceAtV2026_of_put_disjoint {m m' : Memory}
    {wL fL : V2026SubLens} {rawPatch : List (Option UInt8)} {bs : List AbstractByte}
    (hDisj : v2026LensDisjoint wL fL = true)
    (hPut : v2026SubLensPut wL m rawPatch = some m')
    (hAt : MirGlobalSliceAtV2026 m fL bs) :
    MirGlobalSliceAtV2026 m' fL bs :=
  Firewall.map wfMirMemFrameFirewallTag
    (fun h0 => Eq.trans (v2026SubLens_get_put_disjoint wL fL m m' rawPatch hDisj hPut) h0)
    hAt

/-- Coupled state tuple `(MachineState, View, ResTrie ResElem, WavefrontWorldV2026)`
for `IndexedCut`-shielded `stepMirFn` / `runCfgSteps` wavefront loop proofs. -/
abbrev MirWavefrontCutState : Type :=
  MachineState × View × ResTrie ResElem × WavefrontWorldV2026

/-- Top-level stage-indexed predicate bound inside `Anneal.Firewall.IndexedCut` so
expanded `WorldMatchesV2026` / `Memory` bodies stay hidden from outer goals:
at `stage = 0`, the wavefront pool is quiescent (`wfPoolIsNonEmpty = false`). -/
def mirWavefrontCutAt (pol : SpawnPolicy) (F : VProp)
    (frameL : V2026SubLens) (frameBs : List AbstractByte)
    (stage : Nat) (st : MirWavefrontCutState) : Prop :=
  have _ := pol
  WorldMatchesV2026 st.2.1 st.2.2.1 st.2.2.2 ∧
  (vsep (vMinStep st.2.2.2.stepCount) F).holds st.2.1 st.2.2.1 ∧
  MirGlobalSliceAtV2026 st.1.memory frameL frameBs ∧
  match stage with
  | 0 => wfPoolIsNonEmpty st.2.2.2 = false ∧ worldMeasureV2026 st.2.2.2 = []
  | _ + 1 => True

/-- Single-step `V2026_06_01` `stepMirFn` ↔ wavefront-step bridge shielded by
`Anneal.Firewall.IndexedCut` and `MirGlobalSliceAtV2026` (`[propext]`):
any silent `stepMirFn body ms = .tau (.running msNext)` preserving global allocations
couples cleanly to an admissible `.poolWavefrontStep pol` transition, strictly
decreasing the `< ω^ω` ordinal `worldMeasureV2026` under `cnfLt`, preserving the
spatial `VProp` frame `F`, and advancing `IndexedCut` from `stage + 1` to `stage`. -/
theorem stepMirFn_wavefrontStep_firewall_bridge
    (body : CapturedMir) (pol : SpawnPolicy) (hPol : PolicyAdmissible pol)
    (F : VProp) (frameL : V2026SubLens) (frameBs : List AbstractByte)
    (stage : Nat) (ms msNext : MachineState)
    (vIn : View) (rIn : ResTrie ResElem) (wIn : WavefrontWorldV2026)
    (hMirStep : stepMirFn body ms = .tau (.running msNext))
    (hGlobEq : msNext.memory.globals = ms.memory.globals)
    (hNe : wfPoolIsNonEmpty wIn = true)
    (hQuiescentIfZero :
      ∀ wOut : WavefrontWorldV2026,
        evalHybridCmdV2026 (.poolWavefrontStep pol) wIn = .returned wOut →
        match stage with
        | 0 => wfPoolIsNonEmpty wOut = false
        | _ + 1 => True)
    (hCutIn : IndexedCut (mirWavefrontCutAt pol F frameL frameBs) (stage + 1)
      (ms, vIn, rIn, wIn)) :
    ∃ (wOut : WavefrontWorldV2026) (rOut : ResTrie ResElem) (vOut : View),
      stepMirFn body ms = .tau (.running msNext) ∧
      evalHybridCmdV2026 (.poolWavefrontStep pol) wIn = .returned wOut ∧
      cnfLt (worldMeasureV2026 wOut) (worldMeasureV2026 wIn) = true ∧
      ViewLe vIn vOut ∧
      extractPoolCap rOut = extractPoolCap rIn ∧
      IndexedCut (mirWavefrontCutAt pol F frameL frameBs) stage
        (msNext, vOut, rOut, wOut) := by
  have hOpened := open_cut hCutIn
  have hFIn : F.holds vIn rIn :=
    vsep_drop_left (vMinStep wIn.stepCount) F vIn rIn hOpened.2.1
  have hPreIn : (vsep vemp F).holds vIn rIn :=
    vsep_vemp_intro vIn F rIn hFIn
  cases (vsepWpOrdRelV2026_wavefrontStep_strict_descent pol hPol).run
      vIn F rIn wIn hNe hPreIn hOpened.1 with
  | intro wOut hw =>
    cases hw with
    | intro rOut hr =>
      cases hr with
      | intro vOut hv =>
        have hMemNext : MirGlobalSliceAtV2026 msNext.memory frameL frameBs :=
          mirGlobalSliceAtV2026_of_globals_eq hGlobEq hOpened.2.2.1
        have hQz := hQuiescentIfZero wOut hv.1
        have hCutOut :
            IndexedCut (mirWavefrontCutAt pol F frameL frameBs) stage
              (msNext, vOut, rOut, wOut) := by
          cases stage with
          | succ _ =>
            exact seal_cut ⟨hv.2.2.2.2.1, hv.2.2.2.1, hMemNext, True.intro⟩
          | zero =>
            have hEx := wavefrontConvergesV2026_extract_fuel pol wOut wOut
              (WavefrontConvergesV2026.quiescent wOut hQz)
            exact seal_cut ⟨hv.2.2.2.2.1, hv.2.2.2.1, hMemNext, ⟨hQz, hEx.2.2.1⟩⟩
        exact ⟨wOut, rOut, vOut, hMirStep, hv.1, hv.2.2.2.2.2, hv.2.1, hv.2.2.1, hCutOut⟩

/-- Multi-step `V2026_06_01` `runCfgSteps` ↔ `< ω^ω` wavefront drain & universal
`.activeMut` loan reclamation bridge (`[propext]`):
couples a real `CapturedMir` loop/return execution via `Anneal.PureMirExec.runCfgSteps`
directly to `WavefrontConvergesV2026`, `universal_post_drain_activeMut_reclaim`,
spatial `VProp` frame preservation, and a quiescent stage-`0` `IndexedCut`! -/
theorem runCfgSteps_wavefrontDrain_indexedCut_bridge
    (body : CapturedMir) (pol : SpawnPolicy) (hPol : PolicyAdmissible pol)
    (F : VProp) (frameL : V2026SubLens) (frameBs : List AbstractByte)
    (ms0 : MachineState) (cfgFuel : Nat) (retVal : Value) (memFinal : Memory)
    (vIn : View) (rIn : ResTrie ResElem) (wIn : WavefrontWorldV2026)
    (lid : Pos4)
    (hCfgRun : runCfgSteps body (.running true .none ms0) cfgFuel =
      .halted true (.normal (retVal, memFinal)))
    (hGlobEq : memFinal.globals = ms0.memory.globals)
    (hPre : (vsep vemp F).holds vIn rIn)
    (hMIn : WorldMatchesV2026 vIn rIn wIn)
    (hMemFrameIn : MirGlobalSliceAtV2026 ms0.memory frameL frameBs)
    (hQueued : (anyTaskHasLoan lid wIn.fifoQueue || anyTaskHasLoan lid wIn.stealDeque) = true) :
    ∃ (wDrained : WavefrontWorldV2026) (rOut : ResTrie ResElem) (vOut : View)
      (e0 : WfLoanEntryV2026),
      runCfgSteps body (.running true .none ms0) cfgFuel =
        .halted true (.normal (retVal, memFinal)) ∧
      WavefrontConvergesV2026 pol wIn wDrained ∧
      worldMeasureV2026 wDrained = [] ∧
      ActivePureLoanAtV2026 lid e0.lens
        (wrapU32 (e0.val + worldLoanDeltaSum pol lid wIn)) wDrained ∧
      v2026SubLensGet e0.lens wDrained.mem =
        some (wfEncodeU32LeAbsBytes (wrapU32 (e0.val + worldLoanDeltaSum pol lid wIn))) ∧
      (vsep (vMinStep wDrained.stepCount) F).holds vOut rOut ∧
      MirGlobalSliceAtV2026 memFinal frameL frameBs ∧
      IndexedCut (mirWavefrontCutAt pol F frameL frameBs) 0
        ({ ms0 with memory := memFinal }, vOut, rOut, wDrained) := by
  cases vsepWpOrdRelV2026_wavefrontDrain pol hPol vIn F rIn wIn hPre hMIn with
  | intro wDrained hw =>
    cases hw with
    | intro rOut hr =>
      cases hr with
      | intro vOut hv =>
        have hConv := hv.1
        have hEx := wavefrontConvergesV2026_extract_fuel pol wIn wDrained hConv
        have hEmpBool : wfPoolIsNonEmpty wDrained = false := by
          dsimp only [wfPoolIsNonEmpty]
          rw [hEx.1, hEx.2.1]
        cases universal_post_drain_activeMut_reclaim pol hPol wIn wDrained
            hMIn.loansMemOk hMIn.queueLoansOk hConv lid hQueued with
        | intro e0 he0 =>
          have hMemOut : MirGlobalSliceAtV2026 memFinal frameL frameBs :=
            mirGlobalSliceAtV2026_of_globals_eq hGlobEq hMemFrameIn
          have hCut0 :
              IndexedCut (mirWavefrontCutAt pol F frameL frameBs) 0
                ({ ms0 with memory := memFinal }, vOut, rOut, wDrained) :=
            seal_cut ⟨hv.2.2.2.2, hv.2.2.2.1, hMemOut, ⟨hEmpBool, hEx.2.2.1⟩⟩
          exact ⟨wDrained, rOut, vOut, e0, hCfgRun, hConv, hEx.2.2.1,
            he0.2.2.1, he0.2.2.2, hv.2.2.2.1, hMemOut, hCut0⟩

/-! ## 6. Concrete Positive Multi-Rank / 5-Stage / `CapturedMir` Witnesses & Fail-Closed Negatives -/

/-- Constructs a concrete unmodified `V2026_06_01.MirSemantics.Memory` holding:
- Allocation `0`: read-only (`.not`) 4-byte global (`0xCC`) for fail-closed write rejection;
- Allocation `2`: mutable (`.mut`, `align = 4`) 24-byte global holding six little-endian `u32`
  fields `(e, ac, s0, s1, s2, s3)`. -/
def wfMkCNodeMemV2026 (e ac s0 s1 s2 s3 : Nat) : Memory :=
  { emptyMemory with
    nextAllocId := 3
    globals :=
      [{ allocId := 0
         align := ⟨4⟩
         mutability := .not
         bytes := [some 0xCC, some 0xCC, some 0xCC, some 0xCC]
         relocations := [] },
       { allocId := 2
         align := ⟨4⟩
         mutability := .mut
         bytes :=
           wfEncodeU32LeRawBytes e ++ wfEncodeU32LeRawBytes ac ++
           wfEncodeU32LeRawBytes s0 ++ wfEncodeU32LeRawBytes s1 ++
           wfEncodeU32LeRawBytes s2 ++ wfEncodeU32LeRawBytes s3
         relocations := [] }] }

/-- Initial 24-byte `V2026_06_01` memory fixture (`epoch = 10`, `activeCount = 0`,
`s3 = 99` at `[20..24)`). -/
def wfCNode24Mem0 : Memory := wfMkCNodeMemV2026 10 0 0 77 0 99

/-- 4-byte `u32` sub-lens for `epoch` at offset `0` in allocation `2`. -/
def wfCNodeEpochLens : V2026SubLens := ⟨2, 0, 4, 4⟩

/-- 4-byte `u32` sub-lens for `activeCount` at offset `4` in allocation `2`. -/
def wfCNodeActiveCountLens : V2026SubLens := ⟨2, 4, 4, 4⟩

/-- Disjoint 4-byte `u32` sub-lens for `s3` (`99`) at offset `20` in allocation `2`. -/
def wfCNodeFrameSlotLens : V2026SubLens := ⟨2, 20, 4, 4⟩

private theorem wfCNode24Mem0_get_epoch :
    v2026SubLensGet wfCNodeEpochLens wfCNode24Mem0 = some (wfEncodeU32LeAbsBytes 10) := rfl

private theorem wfCNode24Mem0_get_activeCount :
    v2026SubLensGet wfCNodeActiveCountLens wfCNode24Mem0 = some (wfEncodeU32LeAbsBytes 0) := rfl

private theorem wfCNode24Mem0_get_frameSlot :
    v2026SubLensGet wfCNodeFrameSlotLens wfCNode24Mem0 = some (wfEncodeU32LeAbsBytes 99) := rfl

/-- Concrete world with both `fifoQueue` and `stealDeque` non-empty while `path0`
remains `.activeMut` (`10`) and `path1` is `.spatialCheckedOut 1`. -/
def nonemptyPoolWitnessWorld : WavefrontWorldV2026 :=
  { mem := wfCNode24Mem0
    loans := [
      WfLoanEntryV2026.mk path0 .activeMut wfCNodeEpochLens 10,
      WfLoanEntryV2026.mk path1 (.spatialCheckedOut 1) wfCNodeActiveCountLens 0
    ]
    cells := .empty
    fifoQueue := [WorkerTask.mk 0 2 1 path1 1 5]
    stealDeque := [WorkerTask.mk 1 0 0 path1 1 7]
    nextTaskId := 2
    completedCount := 0
    stepCount := 5 }

/-- Backing pool resource tree for `nonemptyPoolWitnessWorld`. -/
def nonemptyPoolWitnessRes : ResTrie ResElem :=
  singleRes poolPath (.pool [(5, 1), (4, 1), (1, 1)])

/-- **Positive Witness 1 (`[propext]`)**: mod-`2^32` wraparound, exact
`encodeValueToBytes` / `decodeValueFromBytes` round-trip, non-empty queues,
unbacked `.empty` refutation, and `.pureLiftSafe` `+ 32 -> 42` preserving
`worldMeasureV2026` and disjoint `wfCNodeFrameSlotLens` (`99`). -/
theorem witness_nonemptyPool_pureFastpath_v2026 :
    wrapU32 (4294967295 + 2) = 1 ∧
    encodeValueToBytes 2 { pointerBits := 64, isLittleEndian := true, entries := [] }
      wfU32Ty (.scalar ⟨42, 4⟩) = some (wfEncodeU32LeAbsBytes 42) ∧
    decodeValueFromBytes 2 { pointerBits := 64, isLittleEndian := true, entries := [] }
      wfU32Ty (wfEncodeU32LeAbsBytes 42) = some (.scalar ⟨42, 4⟩) ∧
    nonemptyPoolWitnessWorld.fifoQueue ≠ [] ∧
    nonemptyPoolWitnessWorld.stealDeque ≠ [] ∧
    WorldMatchesV2026 [5] nonemptyPoolWitnessRes nonemptyPoolWitnessWorld ∧
    (WorldMatchesV2026 [5] .empty nonemptyPoolWitnessWorld → False) ∧
    (∃ wOut : WavefrontWorldV2026,
      evalHybridCmdV2026 (.pureLiftSafe path0 32) nonemptyPoolWitnessWorld = .returned wOut ∧
      WorldMatchesV2026 [5] nonemptyPoolWitnessRes wOut ∧
      worldMeasureV2026 wOut = worldMeasureV2026 nonemptyPoolWitnessWorld ∧
      v2026SubLensGet wfCNodeEpochLens wOut.mem = some (wfEncodeU32LeAbsBytes 42) ∧
      v2026SubLensGet wfCNodeFrameSlotLens wOut.mem = some (wfEncodeU32LeAbsBytes 99) ∧
      (worldMeasureV2026 wOut = [] → False)) := by
  have hMWitness : WorldMatchesV2026 [5] nonemptyPoolWitnessRes nonemptyPoolWitnessWorld :=
    WorldMatchesV2026.mk rfl
      (seal_loansSyncedWithMemV2026
        ⟨rfl, ⟨rfl, True.intro⟩, rfl, rfl, wfCNode24Mem0_get_epoch,
         ⟨rfl, True.intro, rfl, rfl, wfCNode24Mem0_get_activeCount, True.intro⟩⟩)
      rfl rfl
      (fun cid => by
        dsimp only [nonemptyPoolWitnessRes]
        rw [singleRes_getBits_ne poolPath (cellPath cid) _ rfl rfl]
        exact True.intro)
      (fun lid2 => by
        dsimp only [nonemptyPoolWitnessRes]
        rw [singleRes_getBits_ne poolPath (checkedLoanPath lid2) _ rfl rfl]
        exact True.intro)
  have hUnbackedFalse : WorldMatchesV2026 [5] .empty nonemptyPoolWitnessWorld → False :=
    fun hBad => boolFalseNeTrue hBad.poolDebtOk
  have hActW : ActivePureLoanAtV2026 path0 wfCNodeEpochLens 10 nonemptyPoolWitnessWorld :=
    ⟨WfLoanEntryV2026.mk path0 .activeMut wfCNodeEpochLens 10, rfl, rfl, rfl, rfl⟩
  refine ⟨rfl, rfl,
    decodeValueFromBytes_wfEncodeU32LeAbsBytes 1
      { pointerBits := 64, isLittleEndian := true, entries := [] } 42,
    (fun h => by nomatch h), (fun h => by nomatch h),
    hMWitness, hUnbackedFalse, ?_⟩
  cases (vsepWpOrdRelV2026_pure_fastpath path0 wfCNodeEpochLens 10 32).2 [5] vemp
      nonemptyPoolWitnessRes nonemptyPoolWitnessWorld hActW
      (vsep_vemp_intro [5] vemp nonemptyPoolWitnessRes True.intro) hMWitness with
  | intro wOutW hwW =>
    have h42Eq : wrapU32 (10 + 32) = 42 := rfl
    have hGet42 := hwW.2.2.2.2.2.1
    rw [h42Eq] at hGet42
    have hFrame99 :
        v2026SubLensGet wfCNodeFrameSlotLens wOutW.mem = some (wfEncodeU32LeAbsBytes 99) :=
      Eq.trans (hwW.2.2.2.2.2.2 wfCNodeFrameSlotLens rfl) wfCNode24Mem0_get_frameSlot
    have hMeasW : worldMeasureV2026 wOutW = worldMeasureV2026 nonemptyPoolWitnessWorld :=
      hwW.2.2.1
    exact ⟨wOutW, hwW.1, hwW.2.1, hMeasW, hGet42, hFrame99,
      fun hEmpty => by rw [hMeasW] at hEmpty; nomatch hEmpty⟩

/-- Checked-out world fixture for amortized burst submission. -/
def burstWitnessWorld0 : WavefrontWorldV2026 :=
  { mem := wfCNode24Mem0
    loans := [WfLoanEntryV2026.mk path0 (.spatialCheckedOut 77) wfCNodeEpochLens 10]
    cells := .empty
    fifoQueue := []
    stealDeque := []
    nextTaskId := 1
    completedCount := 0
    stepCount := 0 }

/-- Resource tree carrying `ordDebtProp [(5, 2)]` and `checkedOutLoanProp path0 77 10`. -/
def burstWitnessRes0 : ResTrie ResElem :=
  ResTrie.modifyBits (checkedLoanPath path0)
    (fun _ => some (.checkedOutLoan 77 10))
    (ordDebtTree [(5, 2)])

/-- **Positive & Refutation Witness 2 (`[]` zero axioms)**: verifies strict ordinal growth
within the spent debt budget, consumes `ordDebtProp`, refutes retaining `ordDebtProp [(5, 2)]`
in the postcondition (no double-spend), and refutes unfunded zero-debt submission. -/
theorem witness_submitTaskBurst_amortized_and_unfunded_refutation_v2026 :
    WorldMatchesV2026 [0] burstWitnessRes0 burstWitnessWorld0 ∧
    (∃ (wOut : WavefrontWorldV2026) (rOut : ResTrie ResElem),
      evalHybridCmdV2026 (.submitTaskBurst 2 0 path0 77 5) burstWitnessWorld0 = .returned wOut ∧
      cnfLt (worldMeasureV2026 burstWitnessWorld0) (worldMeasureV2026 wOut) = true ∧
      cnfLt (worldMeasureV2026 wOut)
        (cnfAddOrd [(5, 2)] (worldMeasureV2026 burstWitnessWorld0)) = true ∧
      WorldMatchesV2026 [1] rOut wOut ∧
      (poolBackingProp [(5, 2)]).holds [1] rOut ∧
      ((ordDebtProp [(5, 2)]).holds [1] rOut → False)) ∧
    (VSepWpOrdRelV2026 (.submitTaskBurst 2 0 path0 77 5) (.amortized [(5, 2)])
      (fun _ => True)
      (vsep (ordDebtProp [(5, 2)]) (checkedOutLoanProp path0 77 10))
      (fun _ => ordDebtProp [(5, 2)]) → False) ∧
    (VSepWpOrdRelV2026 (.submitTaskBurst 2 0 path0 77 5) (.amortized [(5, 2)])
      (fun w =>
        wfFindLoan path0 w.loans =
          some ⟨path0, .spatialCheckedOut 77, wfCNodeEpochLens, 10⟩)
      vemp (fun _ => vemp) → False) := by
  have hM0 : WorldMatchesV2026 [0] burstWitnessRes0 burstWitnessWorld0 :=
    WorldMatchesV2026.mk rfl
      (seal_loansSyncedWithMemV2026
        ⟨rfl, True.intro, rfl, rfl, wfCNode24Mem0_get_epoch, True.intro⟩)
      rfl rfl
      (fun cid => by
        dsimp only [burstWitnessRes0, ordDebtTree]
        rw [resTrie_getBits_modifyBits_ne (checkedLoanPath path0) (cellPath cid) rfl rfl,
          resTrie_getBits_modifyBits_ne debtPath (cellPath cid) rfl rfl,
          singleRes_getBits_ne poolPath (cellPath cid) _ rfl rfl]
        exact True.intro)
      (fun lid2 => by
        cases hEq0 : Pos4.beq path0 lid2 with
        | true =>
          rw [← pos4_eq_of_beq path0 lid2 hEq0]
          dsimp only [burstWitnessRes0]
          rw [resTrie_getBits_modifyBits_same]
          exact ⟨rfl, ⟨⟨path0, .spatialCheckedOut 77, wfCNodeEpochLens, 10⟩, rfl, rfl, rfl⟩⟩
        | false =>
          have hNe0 : listBoolBeq (checkedLoanPath path0) (checkedLoanPath lid2) = false := by
            dsimp only [checkedLoanPath, listBoolBeq, Bool.and]
            exact hEq0
          dsimp only [burstWitnessRes0, ordDebtTree]
          rw [resTrie_getBits_modifyBits_ne (checkedLoanPath path0)
                (checkedLoanPath lid2) rfl hNe0,
            resTrie_getBits_modifyBits_ne debtPath (checkedLoanPath lid2) rfl rfl,
            singleRes_getBits_ne poolPath (checkedLoanPath lid2) _ rfl rfl]
          exact True.intro)
  let wOutB : WavefrontWorldV2026 :=
    { mem := wfCNode24Mem0
      loans := [WfLoanEntryV2026.mk path0 (.spatialCheckedOut 77) wfCNodeEpochLens 10]
      cells := .empty
      fifoQueue := [WorkerTask.mk 1 2 0 path0 77 5]
      stealDeque := []
      nextTaskId := 2
      completedCount := 0
      stepCount := 1 }
  let rOutB : ResTrie ResElem := singleRes poolPath (.pool [(5, 2)])
  have hMOutB : WorldMatchesV2026 [1] rOutB wOutB :=
    WorldMatchesV2026.mk rfl
      (seal_loansSyncedWithMemV2026
        ⟨rfl, True.intro, rfl, rfl, wfCNode24Mem0_get_epoch, True.intro⟩)
      rfl rfl
      (fun cid => by
        dsimp only [rOutB]
        rw [singleRes_getBits_ne poolPath (cellPath cid) _ rfl rfl]
        exact True.intro)
      (fun lid2 => by
        dsimp only [rOutB]
        rw [singleRes_getBits_ne poolPath (checkedLoanPath lid2) _ rfl rfl]
        exact True.intro)
  have hNoDoubleSpend : (ordDebtProp [(5, 2)]).holds [1] rOutB → False := by
    intro hD
    cases hD with
    | mk hEx =>
      cases hEx with
      | intro rf hMrg =>
        have hG :=
          resTrie_getBits_resTrieMerge debtPath (ordDebtTree [(5, 2)]) rf rOutB rfl hMrg
        have hGetD : ResTrie.getBits debtPath (ordDebtTree [(5, 2)]) =
            some (.debt [(5, 2)]) := rfl
        have hGetOut : ResTrie.getBits debtPath rOutB = none := rfl
        rw [hGetD, hGetOut] at hG
        cases hGf : ResTrie.getBits debtPath rf with
        | none =>
          rw [hGf] at hG
          dsimp only [optOp] at hG
          injection hG with hBad
          nomatch hBad
        | some ef =>
          rw [hGf] at hG
          cases ef with
          | pool _ | checkedOutLoan _ _ | cell _ =>
            dsimp only [optOp, resMerge] at hG; nomatch hG
          | debt _ =>
            dsimp only [optOp, resMerge] at hG
            injection hG with hBad
            nomatch hBad
  have hZeroDebtImpossible :
      VSepWpOrdRelV2026 (.submitTaskBurst 2 0 path0 77 5) (.amortized [(5, 2)])
        (fun w =>
          wfFindLoan path0 w.loans =
            some ⟨path0, .spatialCheckedOut 77, wfCNodeEpochLens, 10⟩)
        vemp (fun _ => vemp) → False := by
    intro hBadWp
    have hM0Empty : WorldMatchesV2026 [0] .empty burstWitnessWorld0 :=
      WorldMatchesV2026.mk rfl
        (seal_loansSyncedWithMemV2026
          ⟨rfl, True.intro, rfl, rfl, wfCNode24Mem0_get_epoch, True.intro⟩)
        rfl rfl
        (fun cid => by rw [resTrie_getBits_empty]; exact True.intro)
        (fun lid2 => by rw [resTrie_getBits_empty]; exact True.intro)
    cases hBadWp.run [0] vemp .empty burstWitnessWorld0 rfl
        (vsep_vemp_intro [0] vemp .empty True.intro) hM0Empty with
    | intro wOut hw =>
      cases hw with
      | intro rOut hr =>
        cases hr with
        | intro _ hv =>
          have hEv := hv.1
          dsimp only [evalHybridCmdV2026, execSubmitTaskBurstV2026, burstWitnessWorld0,
            wfFindLoan, List.foldr, Pos4.beq, pos4ToList, listBoolBeq,
            Bool.and, loanPhaseMatchesScope, Nat.beq] at hEv
          injection hEv with hwEq
          have hPd := hv.2.2.2.2.1.poolDebtOk
          dsimp only [checkWorldMatchesPoolBool] at hPd
          have hPcEmpty : extractPoolCap .empty = some [] := rfl
          rw [hv.2.2.1, hPcEmpty] at hPd
          dsimp only at hPd
          cases hDc : extractDebtCap rOut with
          | none => rw [hDc] at hPd; exact boolFalseNeTrue hPd
          | some _ =>
            rw [hDc] at hPd
            dsimp only at hPd
            have hLeNil := bandLeft hPd
            rw [← hwEq] at hLeNil
            exact boolFalseNeTrue hLeNil
  have hDoubleSpendImpossible :
      VSepWpOrdRelV2026 (.submitTaskBurst 2 0 path0 77 5) (.amortized [(5, 2)])
        (fun _ => True)
        (vsep (ordDebtProp [(5, 2)]) (checkedOutLoanProp path0 77 10))
        (fun _ => ordDebtProp [(5, 2)]) → False := by
    intro hBadDbl
    have hPreBurst :
        (vsep (vsep (ordDebtProp [(5, 2)]) (checkedOutLoanProp path0 77 10))
          vemp).holds [0] burstWitnessRes0 :=
      ⟨burstWitnessRes0, .empty, rfl,
        ⟨ordDebtTree [(5, 2)],
          singleRes (checkedLoanPath path0) (.checkedOutLoan 77 10),
          rfl, resTrieSub_refl _, resTrieSub_refl _⟩,
        True.intro⟩
    cases hBadDbl.run [0] vemp burstWitnessRes0 burstWitnessWorld0 True.intro
        hPreBurst hM0 with
    | intro wOut hw =>
      cases hw with
      | intro rOut hr =>
        cases hr with
        | intro _ hv =>
          have hEvB :
              evalHybridCmdV2026 (.submitTaskBurst 2 0 path0 77 5) burstWitnessWorld0 =
                .returned wOutB := rfl
          have hEv := hv.1
          rw [hEvB] at hEv
          injection hEv with hwEq
          have hPcInit : extractPoolCap burstWitnessRes0 = some [(5, 2)] := rfl
          have hPcOut : extractPoolCap rOut = some [(5, 2)] := Eq.trans hv.2.2.1 hPcInit
          cases hv.2.2.2.1 with
          | intro r1 hr1 =>
            cases hr1 with
            | intro r2 hm12 =>
              cases hm12.2.1 with
              | mk hEx1 =>
                cases hEx1 with
                | intro rf1 hM1 =>
                  cases resTrieMerge_assoc (ordDebtTree [(5, 2)]) rf1 r2 r1 rOut
                      hM1 hm12.1 with
                  | intro rf hAssoc =>
                    have hG :=
                      resTrie_getBits_resTrieMerge debtPath (ordDebtTree [(5, 2)])
                        rf rOut rfl hAssoc.2
                    have hGetD : ResTrie.getBits debtPath (ordDebtTree [(5, 2)]) =
                        some (.debt [(5, 2)]) := rfl
                    rw [hGetD] at hG
                    have hPd := hv.2.2.2.2.1.poolDebtOk
                    dsimp only [checkWorldMatchesPoolBool] at hPd
                    rw [hPcOut, ← hwEq] at hPd
                    cases hGf : ResTrie.getBits debtPath rf with
                    | none =>
                      rw [hGf] at hG
                      dsimp only [optOp] at hG
                      injection hG with hOutEq
                      have hDcOut : extractDebtCap rOut = some [(5, 2)] := by
                        dsimp only [extractDebtCap]
                        rw [← hOutEq]
                        rfl
                      rw [hDcOut] at hPd
                      dsimp only at hPd
                      exact boolFalseNeTrue (bandRight hPd)
                    | some ef =>
                      rw [hGf] at hG
                      cases ef with
                      | pool _ | checkedOutLoan _ _ | cell _ =>
                        dsimp only [optOp, resMerge] at hG; nomatch hG
                      | debt df =>
                        dsimp only [optOp, resMerge] at hG
                        injection hG with hOutEq
                        have hDcOut :
                            extractDebtCap rOut = some (cnfNatAdd [(5, 2)] df) := by
                          dsimp only [extractDebtCap]
                          rw [← hOutEq]
                          exact congrArg some
                            (cnfNorm_eq_of_canonical _ (isCanonicalCnf_cnfNatAdd [(5, 2)] df))
                        rw [hDcOut] at hPd
                        dsimp only at hPd
                        have hBle := bandRight hPd
                        have hMeasB : worldMeasureV2026 wOutB = [(5, 1)] := rfl
                        rw [hMeasB] at hBle
                        change cnfBle (cnfNatAdd (cnfNatAdd [(5, 2)] df) [(5, 1)]) [(5, 2)] =
                          true at hBle
                        rw [cnfNatAdd_comm [(5, 2)] df,
                          cnfNatAdd_assoc df [(5, 2)] [(5, 1)]] at hBle
                        have h23 : cnfNatAdd [(5, 2)] [(5, 1)] = [(5, 3)] := rfl
                        rw [h23] at hBle
                        have hLt3 : cnfLt [(5, 2)] (cnfNatAdd df [(5, 3)]) = true :=
                          cnfLt_cnfAddOrd_of_lt df [(5, 2)] [(5, 3)] rfl rfl
                        exact boolFalseNeTrue
                          (cnfLt_of_lt_of_ble [(5, 2)] (cnfNatAdd df [(5, 3)])
                            [(5, 2)] hLt3 hBle)
  exact ⟨hM0,
    ⟨wOutB, rOutB, rfl, rfl, rfl, hMOutB, resTrieSub_refl rOutB, hNoDoubleSpend⟩,
    hDoubleSpendImpossible,
    hZeroDebtImpossible⟩

/-- 5-tier strictly descending rank tower `[5, 3, 2, 1, 0]`. -/
def wfTower53210 : List Nat := [5, 3, 2, 1, 0]

/-- Admissible spawn policy descending along `wfTower53210` with fanout `1`. -/
def wfPolicyTower53210 : SpawnPolicy := towerLookupNext wfTower53210 1 0

/-- Concrete rank-5 initial world fixture with two leaves summing `+ 32`. -/
def multiRankWitnessWorld0 : WavefrontWorldV2026 :=
  { mem := wfCNode24Mem0
    loans := [WfLoanEntryV2026.mk path0 (.spatialCheckedOut 1) wfCNodeEpochLens 10]
    cells := .empty
    fifoQueue := [WorkerTask.mk 0 5 1 path0 1 16]
    stealDeque := []
    nextTaskId := 1
    completedCount := 0
    stepCount := 0 }

/-- Intermediate memory (`epoch = 26`) for 10-step drain witness. -/
def mwMem26 : Memory := wfMkCNodeMemV2026 26 0 0 77 0 99
/-- Final memory (`epoch = 42`) for 10-step drain witness. -/
def mwMem42 : Memory := wfMkCNodeMemV2026 42 0 0 77 0 99
def mwLoans10 : List WfLoanEntryV2026 :=
  [WfLoanEntryV2026.mk path0 (.spatialCheckedOut 1) wfCNodeEpochLens 10]
def mwLoans26 : List WfLoanEntryV2026 :=
  [WfLoanEntryV2026.mk path0 (.spatialCheckedOut 1) wfCNodeEpochLens 26]
def mwLoans42 : List WfLoanEntryV2026 :=
  [WfLoanEntryV2026.mk path0 .activeMut wfCNodeEpochLens 42]

def mwW1 : WavefrontWorldV2026 :=
  ⟨wfCNode24Mem0, mwLoans10, .empty,
    [⟨0, 5, 0, path0, 1, 16⟩], [⟨1, 3, 0, path0, 1, 16⟩], 2, 0, 1⟩
def mwW2 : WavefrontWorldV2026 :=
  ⟨wfCNode24Mem0, mwLoans10, .empty,
    [], [⟨2, 3, 0, path0, 1, 16⟩, ⟨1, 3, 0, path0, 1, 16⟩], 3, 1, 2⟩
def mwW3 : WavefrontWorldV2026 :=
  ⟨wfCNode24Mem0, mwLoans10, .empty,
    [], [⟨3, 2, 0, path0, 1, 16⟩, ⟨1, 3, 0, path0, 1, 16⟩], 4, 2, 3⟩
def mwW4 : WavefrontWorldV2026 :=
  ⟨wfCNode24Mem0, mwLoans10, .empty,
    [], [⟨4, 1, 0, path0, 1, 16⟩, ⟨1, 3, 0, path0, 1, 16⟩], 5, 3, 4⟩
def mwW5 : WavefrontWorldV2026 :=
  ⟨wfCNode24Mem0, mwLoans10, .empty,
    [], [⟨5, 0, 0, path0, 1, 16⟩, ⟨1, 3, 0, path0, 1, 16⟩], 6, 4, 5⟩
def mwW6 : WavefrontWorldV2026 :=
  ⟨mwMem26, mwLoans26, .empty, [], [⟨1, 3, 0, path0, 1, 16⟩], 6, 5, 6⟩
def mwW7 : WavefrontWorldV2026 :=
  ⟨mwMem26, mwLoans26, .empty, [], [⟨6, 2, 0, path0, 1, 16⟩], 7, 6, 7⟩
def mwW8 : WavefrontWorldV2026 :=
  ⟨mwMem26, mwLoans26, .empty, [], [⟨7, 1, 0, path0, 1, 16⟩], 8, 7, 8⟩
def mwW9 : WavefrontWorldV2026 :=
  ⟨mwMem26, mwLoans26, .empty, [], [⟨8, 0, 0, path0, 1, 16⟩], 9, 8, 9⟩
def mwW10 : WavefrontWorldV2026 :=
  ⟨mwMem42, mwLoans42, .empty, [], [], 9, 9, 10⟩

private theorem runWavefrontStepV2026_chain (f : Nat) (w next wf : WavefrontWorldV2026)
    (hNe : wfPoolIsNonEmpty w = true)
    (hStep : evalHybridCmdV2026 (.poolWavefrontStep wfPolicyTower53210) w = .returned next)
    (hRest : runWavefrontStepsV2026 f wfPolicyTower53210 next = some wf) :
    runWavefrontStepsV2026 (f + 1) wfPolicyTower53210 w = some wf := by
  change (match wfPoolIsNonEmpty w with
    | false => some w
    | true =>
      match evalHybridCmdV2026 (.poolWavefrontStep wfPolicyTower53210) w with
      | .returned wNext => runWavefrontStepsV2026 f wfPolicyTower53210 wNext
      | .faultInvalidSpawn | .faultLoanViolation => none) = some wf
  rw [hNe, hStep]
  exact hRest

/-- **Positive Witness 3 (`[]` zero axioms)**: concrete 10-step rank-`5 -> 3 -> 2 -> 1 -> 0`
drain terminating at `mwW10` (`completedCount = 9`, `stepCount = 10`, empty measure, and
`path0` reclaimed to `.activeMut` (`42`) in unmodified `V2026_06_01.MirSemantics.Memory`). -/
theorem witness_multiRank_5_to_0_wavefront_drain_v2026 :
    isStrictlyDescendingTower wfTower53210 = true ∧
    runWavefrontStepsV2026 11 wfPolicyTower53210 multiRankWitnessWorld0 = some mwW10 ∧
    mwW10.completedCount = 9 ∧
    mwW10.stepCount = 10 ∧
    worldMeasureV2026 mwW10 = [] ∧
    wfFindLoan path0 mwW10.loans =
      some (WfLoanEntryV2026.mk path0 .activeMut wfCNodeEpochLens 42) ∧
    v2026SubLensGet wfCNodeEpochLens mwW10.mem = some (wfEncodeU32LeAbsBytes 42) := by
  have hRun : runWavefrontStepsV2026 11 wfPolicyTower53210 multiRankWitnessWorld0 =
      some mwW10 :=
    runWavefrontStepV2026_chain 10 multiRankWitnessWorld0 mwW1 mwW10 rfl rfl
      (runWavefrontStepV2026_chain 9 mwW1 mwW2 mwW10 rfl rfl
        (runWavefrontStepV2026_chain 8 mwW2 mwW3 mwW10 rfl rfl
          (runWavefrontStepV2026_chain 7 mwW3 mwW4 mwW10 rfl rfl
            (runWavefrontStepV2026_chain 6 mwW4 mwW5 mwW10 rfl rfl
              (runWavefrontStepV2026_chain 5 mwW5 mwW6 mwW10 rfl rfl
                (runWavefrontStepV2026_chain 4 mwW6 mwW7 mwW10 rfl rfl
                  (runWavefrontStepV2026_chain 3 mwW7 mwW8 mwW10 rfl rfl
                    (runWavefrontStepV2026_chain 2 mwW8 mwW9 mwW10 rfl rfl
                      (runWavefrontStepV2026_chain 1 mwW9 mwW10 mwW10 rfl rfl rfl)))))))))
  exact ⟨rfl, hRun, rfl, rfl, rfl, rfl, rfl⟩

/-- 2-tier rank tower `[1, 0]` with fanout `2` for the 5-stage witness. -/
def policyTower10 : SpawnPolicy := towerLookupNext [1, 0] 2 0

/-- Initial world fixture for 5-stage lifecycle and spatial cell witnesses. -/
def reclaimDemoWorld0 : WavefrontWorldV2026 :=
  { mem := wfCNode24Mem0
    loans := [
      WfLoanEntryV2026.mk path0 .activeMut wfCNodeEpochLens 10,
      WfLoanEntryV2026.mk path1 .activeMut wfCNodeActiveCountLens 0
    ]
    cells := ResTrie.modifyBits (pos4ToList path2) (fun _ => some 99) .empty
    fifoQueue := []
    stealDeque := []
    nextTaskId := 1
    completedCount := 0
    stepCount := 0 }

/-- Initial resource trie carrying `ordDebtProp [(3, 2)]` and `cellAuthProp path2 99`. -/
def reclaimDemoRes0 : ResTrie ResElem :=
  ResTrie.modifyBits (cellPath path2) (fun _ => some (.cell (.capAndAuth 99)))
    (ordDebtTree [(3, 2)])

/-- **Positive Witness 4 (`[propext]`)**: full 5-stage chained lifecycle over
`V2026_06_01.MirSemantics.Memory` preserving spatial `cellAuthProp path2 99`. -/
theorem witness_fiveStage_checkout_burst_drain_reclaim_pureLift_v2026 :
    ∃ (w1 w2 w3 w4 : WavefrontWorldV2026) (r1 r2 r3 r4 : ResTrie ResElem)
      (v1 v2 v3 v4 : View),
      evalHybridCmdV2026 (.checkoutLoan path0 55) reclaimDemoWorld0 = .returned w1 ∧
      WorldMatchesV2026 v1 r1 w1 ∧
      evalHybridCmdV2026 (.submitTaskBurst 1 0 path0 55 6) w1 = .returned w2 ∧
      WorldMatchesV2026 v2 r2 w2 ∧
      WavefrontConvergesV2026 policyTower10 w2 w3 ∧
      WorldMatchesV2026 v3 r3 w3 ∧
      ActivePureLoanAtV2026 path0 wfCNodeEpochLens 22 w3 ∧
      v2026SubLensGet wfCNodeEpochLens w3.mem = some (wfEncodeU32LeAbsBytes 22) ∧
      evalHybridCmdV2026 (.pureLiftSafe path0 20) w3 = .returned w4 ∧
      WorldMatchesV2026 v4 r4 w4 ∧
      (vsep (vMinStep w3.stepCount) (cellAuthProp path2 99)).holds v4 r4 ∧
      v2026SubLensGet wfCNodeEpochLens w4.mem = some (wfEncodeU32LeAbsBytes 42) := by
  have hPol10 : PolicyAdmissible policyTower10 :=
    towerLookupNext_admissible [1, 0] 2 0 rfl
  have hChk0 : CheckoutLoanGuardV2026 path0 wfCNodeEpochLens 10 reclaimDemoWorld0 :=
    ⟨⟨WfLoanEntryV2026.mk path0 .activeMut wfCNodeEpochLens 10, rfl, rfl, rfl, rfl⟩, rfl⟩
  have hM0 : WorldMatchesV2026 [0] reclaimDemoRes0 reclaimDemoWorld0 :=
    WorldMatchesV2026.mk rfl
      (seal_loansSyncedWithMemV2026
        ⟨rfl, ⟨rfl, True.intro⟩, rfl, rfl, wfCNode24Mem0_get_epoch,
         ⟨rfl, True.intro, rfl, rfl, wfCNode24Mem0_get_activeCount, True.intro⟩⟩)
      rfl rfl
      (fun cid => by
        cases hEq2 : Pos4.beq path2 cid with
        | true =>
          rw [← pos4_eq_of_beq path2 cid hEq2]
          rfl
        | false =>
          have hNeCell : listBoolBeq (cellPath path2) (cellPath cid) = false := by
            dsimp only [cellPath, listBoolBeq, Bool.and]
            exact hEq2
          dsimp only [reclaimDemoRes0, ordDebtTree]
          rw [resTrie_getBits_modifyBits_ne (cellPath path2) (cellPath cid) rfl hNeCell,
            resTrie_getBits_modifyBits_ne debtPath (cellPath cid) rfl rfl,
            singleRes_getBits_ne poolPath (cellPath cid) _ rfl rfl]
          exact True.intro)
      (fun lid2 => by
        dsimp only [reclaimDemoRes0, ordDebtTree]
        rw [resTrie_getBits_modifyBits_ne (cellPath path2) (checkedLoanPath lid2) rfl rfl,
          resTrie_getBits_modifyBits_ne debtPath (checkedLoanPath lid2) rfl rfl,
          singleRes_getBits_ne poolPath (checkedLoanPath lid2) _ rfl rfl]
        exact True.intro)
  have hPre0 :
      (vsep (ordDebtProp [(3, 2)]) (cellAuthProp path2 99)).holds [0] reclaimDemoRes0 :=
    ⟨ordDebtTree [(3, 2)],
      singleRes (cellPath path2) (.cell (.capAndAuth 99)),
      rfl,
      resTrieSub_refl (ordDebtTree [(3, 2)]),
      ResTrieSub.mk ⟨singleRes (cellPath path2) (.cell .capOnly), rfl⟩⟩
  cases vsepWpOrdRelV2026_fiveStage_chained_lifecycle policyTower10 hPol10
      path0 wfCNodeEpochLens 10 55 1 0 6 20 [(3, 2)] rfl rfl
      [0] (cellAuthProp path2 99) reclaimDemoRes0 reclaimDemoWorld0 hChk0 hPre0 hM0 with
  | intro w1 hw1 =>
    cases hw1 with
    | intro w2 hw2 =>
      cases hw2 with
      | intro w3 hw3 =>
        cases hw3 with
        | intro w4 hw4 =>
          cases hw4 with
          | intro r1 hr1 =>
            cases hr1 with
            | intro r2 hr2 =>
              cases hr2 with
              | intro r3 hr3 =>
                cases hr3 with
                | intro r4 hr4 =>
                  cases hr4 with
                  | intro v1 hv1 =>
                    cases hv1 with
                    | intro v2 hv2 =>
                      cases hv2 with
                      | intro v3 hv3 =>
                        cases hv3 with
                        | intro v4 hv =>
                          have hMultEq :
                              wrapU32 (10 + taskLeafMult policyTower10 1 0 * 6) = 22 := rfl
                          have hFinalEq : wrapU32 (22 + 20) = 42 := rfl
                          have hAct22 := hv.2.2.2.2.2.2.2.2.1
                          have hGet22 := hv.2.2.2.2.2.2.2.2.2.1
                          have hGet42 := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                          rw [hMultEq] at hAct22 hGet22 hGet42
                          rw [hFinalEq] at hGet42
                          exact ⟨w1, w2, w3, w4, r1, r2, r3, r4, v1, v2, v3, v4,
                            hv.1, hv.2.1,
                            hv.2.2.2.1, hv.2.2.2.2.1,
                            hv.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.1,
                            hAct22, hGet22,
                            hv.2.2.2.2.2.2.2.2.2.2.1,
                            hv.2.2.2.2.2.2.2.2.2.2.2.1,
                            hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                            hGet42⟩

/-- **Positive Witness 5 (`[]` zero axioms)**: spatial cell capability/authority mutation
preserving `ordDebtProp [(3, 2)]` and `WorldMatchesV2026`. -/
theorem witness_updateSpatialCell_positive_v2026 :
    ∃ (wOut : WavefrontWorldV2026) (rOut : ResTrie ResElem) (vOut : View),
      evalHybridCmdV2026 (.updateSpatialCell path2 123) reclaimDemoWorld0 = .returned wOut ∧
      ResTrie.getBits (pos4ToList path2) wOut.cells = some 123 ∧
      WorldMatchesV2026 vOut rOut wOut ∧
      (vsep (vsep (cellCapProp path2) (cellAuthProp path2 123))
        (ordDebtProp [(3, 2)])).holds vOut rOut := by
  have hM0 : WorldMatchesV2026 [0] reclaimDemoRes0 reclaimDemoWorld0 :=
    WorldMatchesV2026.mk rfl
      (seal_loansSyncedWithMemV2026
        ⟨rfl, ⟨rfl, True.intro⟩, rfl, rfl, wfCNode24Mem0_get_epoch,
         ⟨rfl, True.intro, rfl, rfl, wfCNode24Mem0_get_activeCount, True.intro⟩⟩)
      rfl rfl
      (fun cid => by
        cases hEq2 : Pos4.beq path2 cid with
        | true => rw [← pos4_eq_of_beq path2 cid hEq2]; rfl
        | false =>
          have hNeCell : listBoolBeq (cellPath path2) (cellPath cid) = false := by
            dsimp only [cellPath, listBoolBeq, Bool.and]; exact hEq2
          dsimp only [reclaimDemoRes0, ordDebtTree]
          rw [resTrie_getBits_modifyBits_ne (cellPath path2) (cellPath cid) rfl hNeCell,
            resTrie_getBits_modifyBits_ne debtPath (cellPath cid) rfl rfl,
            singleRes_getBits_ne poolPath (cellPath cid) _ rfl rfl]
          exact True.intro)
      (fun lid2 => by
        dsimp only [reclaimDemoRes0, ordDebtTree]
        rw [resTrie_getBits_modifyBits_ne (cellPath path2) (checkedLoanPath lid2) rfl rfl,
          resTrie_getBits_modifyBits_ne debtPath (checkedLoanPath lid2) rfl rfl,
          singleRes_getBits_ne poolPath (checkedLoanPath lid2) _ rfl rfl]
        exact True.intro)
  have hPre :
      (vsep (vsep (cellCapProp path2) (cellAuthProp path2 99))
        (ordDebtProp [(3, 2)])).holds [0] reclaimDemoRes0 :=
    ⟨singleRes (cellPath path2) (.cell (.capAndAuth 99)),
      ordDebtTree [(3, 2)], rfl,
      ⟨singleRes (cellPath path2) (.cell .capOnly),
        singleRes (cellPath path2) (.cell (.authOnly 99)),
        rfl, resTrieSub_refl _, resTrieSub_refl _⟩,
      resTrieSub_refl _⟩
  cases (vsepWpOrdRelV2026_updateSpatialCell path2 99 123).run [0]
      (ordDebtProp [(3, 2)]) reclaimDemoRes0 reclaimDemoWorld0 True.intro hPre hM0 with
  | intro wOut hw =>
    cases hw with
    | intro rOut hr =>
      cases hr with
      | intro vOut hv =>
        have hEv :
            evalHybridCmdV2026 (.updateSpatialCell path2 123) reclaimDemoWorld0 =
              .returned
                (match evalHybridCmdV2026 (.updateSpatialCell path2 123) reclaimDemoWorld0 with
                 | .returned w => w
                 | .faultLoanViolation | .faultInvalidSpawn => reclaimDemoWorld0) := rfl
        have hEqW :
            wOut =
              (match evalHybridCmdV2026 (.updateSpatialCell path2 123) reclaimDemoWorld0 with
               | .returned w => w
               | .faultLoanViolation | .faultInvalidSpawn => reclaimDemoWorld0) := by
          have h1 := hv.1
          rw [hEv] at h1
          injection h1 with h2
          exact h2.symm
        have hCell123 : ResTrie.getBits (pos4ToList path2) wOut.cells = some 123 := by
          rw [hEqW]; rfl
        exact ⟨wOut, rOut, vOut, hv.1, hCell123, hv.2.2.2.2.1, hv.2.2.2.1⟩

/-- Concrete `u32` layout for the real `CapturedMir` wavefront drain loop witness. -/
def wfU32TypeLayout : TypeLayout :=
  { size := ⟨4⟩
    align := ⟨4⟩
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩)
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

/-- Layout table for `wfReclaimLoopBody`. -/
def wfLoopLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [wfU32TypeLayout] }

private def wfU32ConstOp (n : Nat) : Operand :=
  .constant { ty := wfU32Ty, val := .scalar (.int ⟨n, 4⟩) }

/-- Real 4-block `Runtime(Optimized)` `CapturedMir` wavefront drain/accumulate loop:
`fn reclaim_loop(mut rem: u32) -> u32 { let mut acc = 10u32; while rem != 0 { acc += 16; rem -= 1; } acc }`
carrying `wfCNode24Mem0.globals` as its live global allocation environment. -/
def wfReclaimLoopBody : CapturedMir :=
  { defPath := "anneal::wavefront::reclaim_loop"
    phase := .runtimeOptimized
    role := .subject
    argCount := 1
    localDecls :=
      [{ mutability := .mut, ty := wfU32Ty, debugName := none },
       { mutability := .mut, ty := wfU32Ty, debugName := some "rem" },
       { mutability := .mut, ty := wfU32Ty, debugName := some "acc" }]
    basicBlocks :=
      [{ statements :=
           [{ kind := .storageLive 2, span := "wf" },
            { kind := .assign ⟨2, []⟩ (.use (wfU32ConstOp 10)), span := "wf" }]
         terminator := { kind := .goto 1, span := "wf" }
         isCleanup := false },
       { statements := []
         terminator :=
           { kind := .switchInt (.copy ⟨1, []⟩) { branches := [(0, 3)], otherwise := 2 }
             span := "wf" }
         isCleanup := false },
       { statements :=
           [{ kind := .assign ⟨2, []⟩ (.binaryOp .add (.copy ⟨2, []⟩) (wfU32ConstOp 16))
              span := "wf" },
            { kind := .assign ⟨1, []⟩ (.binaryOp .sub (.copy ⟨1, []⟩) (wfU32ConstOp 1))
              span := "wf" }]
         terminator := { kind := .goto 1, span := "wf" }
         isCleanup := false },
       { statements :=
           [{ kind := .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩)), span := "wf" },
            { kind := .storageDead 2, span := "wf" }]
         terminator := { kind := .return_, span := "wf" }
         isCleanup := false }]
    fnAbi :=
      { args := [{ layout := wfU32TypeLayout, mode := .direct }]
        ret := { layout := wfU32TypeLayout, mode := .direct }
        conv := .rust
        canUnwind := false }
    layouts := wfLoopLayouts
    allocations := wfCNode24Mem0.globals }

/-- Initial `MachineState` for `wfReclaimLoopBody` with `rem = 2` and `wfCNode24Mem0`. -/
def wfLoopInitMs : MachineState :=
  { (initMachineState wfReclaimLoopBody [.scalar ⟨2, 4⟩]) with memory := wfCNode24Mem0 }

/-- Stepped `MachineState` after `stepMirFn wfReclaimLoopBody wfLoopInitMs`. -/
def wfLoopAfterStep1Ms : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 1
        locals := [.uninit, .init (.scalar ⟨2, 4⟩), .uninit] }
    memory := wfCNode24Mem0 }

/-- Backing resource trie for `multiRankWitnessWorld0` paired with spatial frame
`cellAuthProp path2 99`. -/
def wfLoopBridgeRes0 : ResTrie ResElem :=
  ResTrie.modifyBits (cellPath path2) (fun _ => some (.cell (.capAndAuth 99)))
    (singleRes poolPath (.pool [(11, 2)]))

/-- World coupling `multiRankWitnessWorld0` with `cells[path2] = 99`. -/
def wfLoopBridgeWorld0 : WavefrontWorldV2026 :=
  { multiRankWitnessWorld0 with
    cells := ResTrie.modifyBits (pos4ToList path2) (fun _ => some 99) .empty }

/-- **Positive Witness 6 (`[propext]`)**: end-to-end `Firewall` / `IndexedCut`-shielded
operational bridge on real `wfReclaimLoopBody` exercising BOTH:
1. Unmodified `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` coupled via
   `stepMirFn_wavefrontStep_firewall_bridge` to strict `< ω^ω` `cnfLt` descent and
   `IndexedCut` stage advancement, AND
2. Unmodified `Anneal.PureMirExec.runCfgSteps` (`15` CFG steps around the `SwitchInt`
   loop returning `.scalar ⟨42, 4⟩`) coupled via `runCfgSteps_wavefrontDrain_indexedCut_bridge`
   to full `WavefrontConvergesV2026` drain, universal `.activeMut` reclamation (`42`),
   spatial `cellAuthProp path2 99` preservation, and `Firewall`-shielded `Memory` framing! -/
theorem witness_v2026_stepMirFn_and_runCfgSteps_wavefront_loop :
    stepMirFn wfReclaimLoopBody wfLoopInitMs = .tau (.running wfLoopAfterStep1Ms) ∧
    runCfgSteps wfReclaimLoopBody (.running true .none wfLoopInitMs) 15 =
      .halted true (.normal (.scalar ⟨42, 4⟩, wfCNode24Mem0)) ∧
    (∃ (wStep1 : WavefrontWorldV2026) (rStep1 : ResTrie ResElem) (vStep1 : View),
      evalHybridCmdV2026 (.poolWavefrontStep wfPolicyTower53210) wfLoopBridgeWorld0 =
        .returned wStep1 ∧
      cnfLt (worldMeasureV2026 wStep1) (worldMeasureV2026 wfLoopBridgeWorld0) = true ∧
      IndexedCut (mirWavefrontCutAt wfPolicyTower53210 (cellAuthProp path2 99)
        wfCNodeFrameSlotLens (wfEncodeU32LeAbsBytes 99)) 9
        (wfLoopAfterStep1Ms, vStep1, rStep1, wStep1)) ∧
    (∃ (wDrained : WavefrontWorldV2026) (rOut : ResTrie ResElem) (vOut : View),
      WavefrontConvergesV2026 wfPolicyTower53210 wfLoopBridgeWorld0 wDrained ∧
      worldMeasureV2026 wDrained = [] ∧
      ActivePureLoanAtV2026 path0 wfCNodeEpochLens 42 wDrained ∧
      v2026SubLensGet wfCNodeEpochLens wDrained.mem = some (wfEncodeU32LeAbsBytes 42) ∧
      (vsep (vMinStep wDrained.stepCount) (cellAuthProp path2 99)).holds vOut rOut ∧
      MirGlobalSliceAtV2026 wfCNode24Mem0 wfCNodeFrameSlotLens (wfEncodeU32LeAbsBytes 99) ∧
      IndexedCut (mirWavefrontCutAt wfPolicyTower53210 (cellAuthProp path2 99)
        wfCNodeFrameSlotLens (wfEncodeU32LeAbsBytes 99)) 0
        ({ wfLoopInitMs with memory := wfCNode24Mem0 }, vOut, rOut, wDrained)) := by
  have hPol : PolicyAdmissible wfPolicyTower53210 :=
    towerLookupNext_admissible wfTower53210 1 0 rfl
  have hMir1 : stepMirFn wfReclaimLoopBody wfLoopInitMs = .tau (.running wfLoopAfterStep1Ms) :=
    rfl
  have hCfg15 :
      runCfgSteps wfReclaimLoopBody (.running true .none wfLoopInitMs) 15 =
        .halted true (.normal (.scalar ⟨42, 4⟩, wfCNode24Mem0)) := rfl
  have hM0 : WorldMatchesV2026 [0] wfLoopBridgeRes0 wfLoopBridgeWorld0 :=
    WorldMatchesV2026.mk rfl
      (seal_loansSyncedWithMemV2026
        ⟨rfl, True.intro, rfl, rfl, wfCNode24Mem0_get_epoch, True.intro⟩)
      rfl rfl
      (fun cid => by
        cases hEq2 : Pos4.beq path2 cid with
        | true => rw [← pos4_eq_of_beq path2 cid hEq2]; rfl
        | false =>
          have hNeCell : listBoolBeq (cellPath path2) (cellPath cid) = false := by
            dsimp only [cellPath, listBoolBeq, Bool.and]; exact hEq2
          dsimp only [wfLoopBridgeRes0]
          rw [resTrie_getBits_modifyBits_ne (cellPath path2) (cellPath cid) rfl hNeCell,
            singleRes_getBits_ne poolPath (cellPath cid) _ rfl rfl]
          exact True.intro)
      (fun lid2 => by
        dsimp only [wfLoopBridgeRes0]
        rw [resTrie_getBits_modifyBits_ne (cellPath path2) (checkedLoanPath lid2) rfl rfl,
          singleRes_getBits_ne poolPath (checkedLoanPath lid2) _ rfl rfl]
        exact True.intro)
  have hCellHold0 : (cellAuthProp path2 99).holds [0] wfLoopBridgeRes0 :=
    ResTrieSub.mk
      ⟨ResTrie.modifyBits (cellPath path2) (fun _ => some (.cell .capOnly))
        (singleRes poolPath (.pool [(11, 2)])), rfl⟩
  have hMinHold0 : (vsep (vMinStep wfLoopBridgeWorld0.stepCount) (cellAuthProp path2 99)).holds
      [0] wfLoopBridgeRes0 :=
    ⟨.empty, wfLoopBridgeRes0, rfl, rfl, hCellHold0⟩
  have hMemFr0 :
      MirGlobalSliceAtV2026 wfLoopInitMs.memory wfCNodeFrameSlotLens
        (wfEncodeU32LeAbsBytes 99) :=
    seal_mirGlobalSliceAtV2026 wfCNode24Mem0_get_frameSlot
  have hCut10 :
      IndexedCut (mirWavefrontCutAt wfPolicyTower53210 (cellAuthProp path2 99)
        wfCNodeFrameSlotLens (wfEncodeU32LeAbsBytes 99)) 10
        (wfLoopInitMs, [0], wfLoopBridgeRes0, wfLoopBridgeWorld0) :=
    seal_cut ⟨hM0, hMinHold0, hMemFr0, True.intro⟩
  refine ⟨hMir1, hCfg15, ?_, ?_⟩
  · cases stepMirFn_wavefrontStep_firewall_bridge wfReclaimLoopBody
        wfPolicyTower53210 hPol (cellAuthProp path2 99)
        wfCNodeFrameSlotLens (wfEncodeU32LeAbsBytes 99)
        9 wfLoopInitMs wfLoopAfterStep1Ms [0] wfLoopBridgeRes0 wfLoopBridgeWorld0
        hMir1 rfl rfl (fun _ _ => True.intro) hCut10 with
    | intro wStep1 hw1 =>
      cases hw1 with
      | intro rStep1 hr1 =>
        cases hr1 with
        | intro vStep1 hv1 =>
          exact ⟨wStep1, rStep1, vStep1, hv1.2.1, hv1.2.2.1, hv1.2.2.2.2.2⟩
  · cases runCfgSteps_wavefrontDrain_indexedCut_bridge wfReclaimLoopBody
        wfPolicyTower53210 hPol (cellAuthProp path2 99)
        wfCNodeFrameSlotLens (wfEncodeU32LeAbsBytes 99)
        wfLoopInitMs 15 (.scalar ⟨42, 4⟩) wfCNode24Mem0
        [0] wfLoopBridgeRes0 wfLoopBridgeWorld0 path0
        hCfg15 rfl (vsep_vemp_intro [0] _ wfLoopBridgeRes0 hCellHold0)
        hM0 hMemFr0 rfl with
    | intro wDrained hwD =>
      cases hwD with
      | intro rOut hrD =>
        cases hrD with
        | intro vOut hvD =>
          cases hvD with
          | intro e0 heD =>
            have hFind0 : wfFindLoan path0 wfLoopBridgeWorld0.loans =
                some (WfLoanEntryV2026.mk path0 (.spatialCheckedOut 1) wfCNodeEpochLens 10) := rfl
            have hReclaim :=
              universal_post_drain_activeMut_reclaim wfPolicyTower53210 hPol
                wfLoopBridgeWorld0 wDrained hM0.loansMemOk hM0.queueLoansOk
                heD.2.1 path0 rfl
            cases hReclaim with
            | intro e0' he0' =>
              rw [hFind0] at he0'
              injection he0'.1 with hSameE
              rw [← hSameE] at he0'
              dsimp only at he0'
              have hSum42 :
                  wrapU32 (10 + worldLoanDeltaSum wfPolicyTower53210 path0 wfLoopBridgeWorld0) =
                    42 := rfl
              rw [hSum42] at he0'
              exact ⟨wDrained, rOut, vOut, heD.2.1, heD.2.2.1,
                he0'.2.2.1, he0'.2.2.2,
                heD.2.2.2.2.2.1, heD.2.2.2.2.2.2.1, heD.2.2.2.2.2.2.2⟩

/-- Helper constructing single-cause negative test worlds over `wfCNode24Mem0`. -/
def mkNegWorldV2026 (loans : List WfLoanEntryV2026)
    (fifo : List WorkerTask) : WavefrontWorldV2026 :=
  { mem := wfCNode24Mem0
    loans := loans
    cells := .empty
    fifoQueue := fifo
    stealDeque := []
    nextTaskId := 1
    completedCount := 0
    stepCount := 0 }

/-- **16-Case Fail-Closed Negative Regression Suite (`[]` zero axioms)**:
1. Missing loan on leaf writeback -> `.faultLoanViolation`;
2. Stale scope on leaf writeback (`.spatialCheckedOut 88` vs `77`) -> `.faultLoanViolation`;
3. Active-not-checked-out loan on leaf writeback -> `.faultLoanViolation`;
4. Empty-queue wavefront step -> `.faultInvalidSpawn`;
5. Inadmissible equal-rank spawn (`pol _ = (1, 5, 0)` on rank `5`) -> `.faultInvalidSpawn`;
6. Inadmissible upward-rank spawn (`pol _ = (2, 7, 0)` on rank `5`) -> `.faultInvalidSpawn`;
7. Pure write to `.spatialCheckedOut` loan -> `.faultLoanViolation`;
8. Pure write to `.frozen` loan -> `.faultLoanViolation` (paired with positive pure read);
9. Pure write to `.ended` loan -> `.faultLoanViolation`;
10. Checkout of already `.spatialCheckedOut` loan -> `.faultLoanViolation`;
11. Checkout while a queued task references the loan -> `.faultLoanViolation`;
12. Burst submission with mismatched scope -> `.faultLoanViolation`;
13. Spatial cell update on missing cell -> `.faultLoanViolation`;
14. Pure write through dangling `allocId = 99` lens -> `.faultLoanViolation`;
15. Pure write through read-only `.not` global `allocId = 0` lens -> `.faultLoanViolation`;
16. Leaf writeback through out-of-bounds `[24..28)` lens in 24-byte allocation ->
    `.faultLoanViolation`. -/
theorem witness_wavefrontV2026_negative_fail_closed_suite :
    evalHybridCmdV2026 (.poolWavefrontStep (fun _ => (0, 0, 0)))
      (mkNegWorldV2026 [] [WorkerTask.mk 0 0 0 path0 77 5]) =
        .faultLoanViolation ∧
    evalHybridCmdV2026 (.poolWavefrontStep (fun _ => (0, 0, 0)))
      (mkNegWorldV2026
        [WfLoanEntryV2026.mk path0 (.spatialCheckedOut 88) wfCNodeEpochLens 10]
        [WorkerTask.mk 0 0 0 path0 77 5]) =
        .faultLoanViolation ∧
    evalHybridCmdV2026 (.poolWavefrontStep (fun _ => (0, 0, 0)))
      (mkNegWorldV2026
        [WfLoanEntryV2026.mk path0 .activeMut wfCNodeEpochLens 10]
        [WorkerTask.mk 0 0 0 path0 77 5]) =
        .faultLoanViolation ∧
    evalHybridCmdV2026 (.poolWavefrontStep (fun _ => (0, 0, 0)))
      (mkNegWorldV2026
        [WfLoanEntryV2026.mk path0 (.spatialCheckedOut 77) wfCNodeEpochLens 10] []) =
        .faultInvalidSpawn ∧
    evalHybridCmdV2026 (.poolWavefrontStep (fun _ => (1, 5, 0)))
      (mkNegWorldV2026
        [WfLoanEntryV2026.mk path0 (.spatialCheckedOut 77) wfCNodeEpochLens 10]
        [WorkerTask.mk 0 5 0 path0 77 5]) =
        .faultInvalidSpawn ∧
    evalHybridCmdV2026 (.poolWavefrontStep (fun _ => (2, 7, 0)))
      (mkNegWorldV2026
        [WfLoanEntryV2026.mk path0 (.spatialCheckedOut 77) wfCNodeEpochLens 10]
        [WorkerTask.mk 0 5 0 path0 77 5]) =
        .faultInvalidSpawn ∧
    evalHybridCmdV2026 (.pureLiftSafe path0 1)
      (mkNegWorldV2026
        [WfLoanEntryV2026.mk path0 (.spatialCheckedOut 77) wfCNodeEpochLens 10] []) =
        .faultLoanViolation ∧
    evalHybridCmdV2026 (.pureLiftSafe path0 1)
      (mkNegWorldV2026 [WfLoanEntryV2026.mk path0 .frozen wfCNodeEpochLens 10] []) =
        .faultLoanViolation ∧
    wfCanPureAccessLoan [WfLoanEntryV2026.mk path0 .frozen wfCNodeEpochLens 10]
      path0 false = true ∧
    evalHybridCmdV2026 (.pureLiftSafe path0 1)
      (mkNegWorldV2026 [WfLoanEntryV2026.mk path0 .ended wfCNodeEpochLens 10] []) =
        .faultLoanViolation ∧
    evalHybridCmdV2026 (.checkoutLoan path0 77)
      (mkNegWorldV2026
        [WfLoanEntryV2026.mk path0 (.spatialCheckedOut 77) wfCNodeEpochLens 10] []) =
        .faultLoanViolation ∧
    evalHybridCmdV2026 (.checkoutLoan path0 77)
      (mkNegWorldV2026
        [WfLoanEntryV2026.mk path0 .activeMut wfCNodeEpochLens 10]
        [WorkerTask.mk 0 0 0 path0 77 5]) =
        .faultLoanViolation ∧
    evalHybridCmdV2026 (.submitTaskBurst 1 0 path0 88 5)
      (mkNegWorldV2026
        [WfLoanEntryV2026.mk path0 (.spatialCheckedOut 77) wfCNodeEpochLens 10] []) =
        .faultLoanViolation ∧
    evalHybridCmdV2026 (.updateSpatialCell path2 100)
      (mkNegWorldV2026 [WfLoanEntryV2026.mk path0 .activeMut wfCNodeEpochLens 10] []) =
        .faultLoanViolation ∧
    evalHybridCmdV2026 (.pureLiftSafe path0 1)
      (mkNegWorldV2026 [WfLoanEntryV2026.mk path0 .activeMut ⟨99, 0, 4, 4⟩ 10] []) =
        .faultLoanViolation ∧
    evalHybridCmdV2026 (.pureLiftSafe path0 1)
      (mkNegWorldV2026 [WfLoanEntryV2026.mk path0 .activeMut ⟨0, 0, 4, 4⟩ 10] []) =
        .faultLoanViolation ∧
    evalHybridCmdV2026 (.poolWavefrontStep (fun _ => (0, 0, 0)))
      (mkNegWorldV2026
        [WfLoanEntryV2026.mk path0 (.spatialCheckedOut 77) ⟨2, 24, 4, 4⟩ 10]
        [WorkerTask.mk 0 0 0 path0 77 5]) =
        .faultLoanViolation :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.WavefrontReclaim.WavefrontV2026
