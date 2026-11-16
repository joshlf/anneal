-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Trusted
import Trusted.Correspondence
import Anneal.MirWp

namespace Anneal.MirCorrespondenceProof

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence

/-!
# MIR Correspondence Proofs (`Anneal.MirCorrespondenceProof`)

This module proves Anneal's MIR correspondence theorems and non-vacuity
canaries against `Trusted.Correspondence` and `vendor/lean-miri`:

1. **Unconditional codec round-trip (`decodeProg_encodeProg`), canonical
   type deduplication (`encodeProg_types_canonical`), and constructor
   preservation:** Every `p : Program` (including its `pointerWidthBits`)
   round-trips through `encodeProg` and `decodeProg` with zero preconditions,
   `encodeStmt_no_dormant_noops` guarantees that `encodeStmt` maps `.nop` and
   only `.nop` to `.nop`, and `encodeRvalue_binaryOp_iff`,
   `encodeRvalue_unaryOp_iff`, and `encodeStmt_assign_iff` keep the encoder
   from permuting operators or assignment constructors.
2. **Bijective simulation invariant (`SimulationInv`,
   `state_unique_of_simulationInv`, `refState_unique_of_simulationInv`):**
   Relates $M_{\text{anneal}}$ states (`State`) and $M_{\text{ref}}$ states
   (`RefState`) 1-to-1: the reference stack is the caller sentinel for the
   entry function's return type (`callerSentinelFrame`) beneath
   `liftFrame body.locals f`.
3. **End-to-end correspondence and fault equivalence
   (`correspondence_claim_holds`, `fault_equivalence_claim_holds`, and
   `miri_move_deinit_wiring_claim_holds`):** Proves `CorrespondenceClaim`
   (UB transfer plus exact terminal-behavior and divergence equivalence,
   from forward and backward step-indexed simulation),
   `FaultEquivalenceClaim`, and `MiriMoveDeinitWiringClaim`.
4. **Move-deinitialization and overflow canaries (`D6`–`D10`):** Proves use
   after move (`canary_D6_use_after_move_ub`), left-to-right binary-operand
   evaluation order (`canary_D7a_binop_copy_then_move_ok`,
   `canary_D7b_binop_move_then_copy_ub`, `canary_D7c_binop_move_then_move_ub`),
   self-move preservation (`canary_D8_self_move_ok`), 0-byte ZST unit move
   preservation (`canary_D9_move_unit_zst_ok`), and unchecked-overflow UB
   versus wrapping addition in both machines
   (`canary_D10_add_unchecked_overflow_ub`).
-/

theorem Bool.false_eq_true : (false = true) = False :=
  propext ⟨fun h => Bool.noConfusion h, False.elim⟩

theorem Nat.add_right_cancel_iff {n m k : Nat} : (n + k = m + k) ↔ (n = m) :=
  ⟨Nat.add_right_cancel, fun h => h ▸ rfl⟩

theorem IntWidth.beq_refl (w : IntWidth) : IntWidth.beq w w = true := by
  cases w <;> rfl

theorem IntWidth.eq_of_beq {w₁ w₂ : IntWidth}
    (h : IntWidth.beq w₁ w₂ = true) : w₁ = w₂ := by
  cases w₁ <;> cases w₂ <;> first | rfl | cases h

theorem Mutability.beq_refl (m : Mutability) : Mutability.beq m m = true := by
  cases m <;> rfl

theorem Mutability.eq_of_beq {m₁ m₂ : Mutability}
    (h : Mutability.beq m₁ m₂ = true) : m₁ = m₂ := by
  cases m₁ <;> cases m₂ <;> first | rfl | cases h

mutual
  theorem MirTy.beq_refl (t : MirTy) : MirTy.beq t t = true := by
    cases t with
    | bool => rfl
    | int w s =>
      change (IntWidth.beq w w && (s == s)) = true
      rw [IntWidth.beq_refl]
      cases s <;> rfl
    | unit => rfl
    | tuple fs =>
      change MirTy.beqList fs fs = true
      exact MirTy.beqList_refl fs
    | ref m p =>
      change (Mutability.beq m m && MirTy.beq p p) = true
      rw [Mutability.beq_refl, MirTy.beq_refl p]
      rfl
    | rawPtr m p =>
      change (Mutability.beq m m && MirTy.beq p p) = true
      rw [Mutability.beq_refl, MirTy.beq_refl p]
      rfl
    | unsupported => rfl

  theorem MirTy.beqList_refl
      (ts : List MirTy) : MirTy.beqList ts ts = true := by
    cases ts with
    | nil => rfl
    | cons t rest =>
      change (MirTy.beq t t && MirTy.beqList rest rest) = true
      rw [MirTy.beq_refl t, MirTy.beqList_refl rest]
      rfl
end

mutual
  theorem MirTy.eq_of_beq {a b : MirTy} (h : MirTy.beq a b = true) : a = b := by
    cases a with
    | bool => cases b <;> first | rfl | cases h
    | int w₁ s₁ =>
      cases b with
      | int w₂ s₂ =>
        change (IntWidth.beq w₁ w₂ && (s₁ == s₂)) = true at h
        cases h_w : IntWidth.beq w₁ w₂ <;> rw [h_w] at h
        · cases h
        · rw [IntWidth.eq_of_beq h_w]
          cases s₁ <;> cases s₂ <;> first | rfl | cases h
      | _ => cases h
    | unit => cases b <;> first | rfl | cases h
    | tuple fs₁ =>
      cases b with
      | tuple fs₂ =>
        change MirTy.beqList fs₁ fs₂ = true at h
        rw [MirTy.eq_of_beqList h]
      | _ => cases h
    | ref m₁ p₁ =>
      cases b with
      | ref m₂ p₂ =>
        change (Mutability.beq m₁ m₂ && MirTy.beq p₁ p₂) = true at h
        cases h_m : Mutability.beq m₁ m₂ <;> rw [h_m] at h
        · cases h
        · rw [Mutability.eq_of_beq h_m, MirTy.eq_of_beq h]
      | _ => cases h
    | rawPtr m₁ p₁ =>
      cases b with
      | rawPtr m₂ p₂ =>
        change (Mutability.beq m₁ m₂ && MirTy.beq p₁ p₂) = true at h
        cases h_m : Mutability.beq m₁ m₂ <;> rw [h_m] at h
        · cases h
        · rw [Mutability.eq_of_beq h_m, MirTy.eq_of_beq h]
      | _ => cases h
    | unsupported => cases b <;> first | rfl | cases h

  theorem MirTy.eq_of_beqList {xs ys : List MirTy}
      (h : MirTy.beqList xs ys = true) : xs = ys := by
    cases xs with
    | nil => cases ys <;> first | rfl | cases h
    | cons x xs' =>
      cases ys with
      | nil => cases h
      | cons y ys' =>
        change (MirTy.beq x y && MirTy.beqList xs' ys') = true at h
        cases h_x : MirTy.beq x y <;> rw [h_x] at h
        · cases h
        · rw [MirTy.eq_of_beq h_x, MirTy.eq_of_beqList h]
end

theorem MirTy.beq_eq_false_of_ne {a b : MirTy}
    (h : a ≠ b) : MirTy.beq a b = false := by
  cases h_b : MirTy.beq a b with
  | false => rfl
  | true => exact False.elim (h (MirTy.eq_of_beq h_b))

theorem MirTy.ne_of_beq_eq_false {a b : MirTy}
    (h : MirTy.beq a b = false) : a ≠ b := by
  intro h_eq
  subst h_eq
  rw [MirTy.beq_refl] at h
  cases h


theorem indexOfTy_insertTy_none {t ty : MirTy} {ts : List MirTy}
    (h_ne : t ≠ ty) (h_none : indexOfTy ts t = none) :
    indexOfTy (insertTy ty ts) t = none := by
  induction ts with
  | nil =>
    dsimp only [insertTy, indexOfTy]
    have h_dec : MirTy.beq ty t = false :=
      MirTy.beq_eq_false_of_ne (fun h => h_ne h.symm)
    rw [h_dec]
    rfl
  | cons a rest ih =>
    dsimp only [indexOfTy] at h_none
    cases h_at : MirTy.beq a t with
    | true => rw [h_at] at h_none; cases h_none
    | false =>
      rw [h_at] at h_none
      cases h_rest : indexOfTy rest t with
      | some _ => rw [h_rest] at h_none; cases h_none
      | none =>
        dsimp only [insertTy]
        cases h_ay : MirTy.beq a ty with
        | true =>
          change indexOfTy (a :: rest) t = none
          dsimp only [indexOfTy]
          rw [h_at, h_rest]
          rfl
        | false =>
          change indexOfTy (a :: insertTy ty rest) t = none
          dsimp only [indexOfTy]
          rw [h_at, ih h_rest]
          rfl

theorem typesAreCanonical_insertTy (ty : MirTy) (ts : List MirTy)
    (h_can : typesAreCanonical ts = true) :
    typesAreCanonical (insertTy ty ts) = true := by
  induction ts with
  | nil => rfl
  | cons a rest ih =>
    dsimp only [typesAreCanonical] at h_can
    cases h_none : indexOfTy rest a with
    | some _ => rw [h_none] at h_can; cases h_can
    | none =>
      rw [h_none] at h_can
      simp only [Option.isNone, Bool.true_and] at h_can
      dsimp only [insertTy]
      cases h_ay : MirTy.beq a ty with
      | true =>
        change typesAreCanonical (a :: rest) = true
        dsimp only [typesAreCanonical]
        rw [h_none]
        exact h_can
      | false =>
        have h_ne : a ≠ ty := MirTy.ne_of_beq_eq_false h_ay
        change typesAreCanonical (a :: insertTy ty rest) = true
        dsimp only [typesAreCanonical]
        rw [indexOfTy_insertTy_none h_ne h_none]
        exact ih h_can


/-- Componentwise structural homomorphism laws for `encodeBody` and
`encodeBasicBlock`. -/
theorem encodeBody_basicBlocks_eq (ts : List MirTy) (b : Body) :
    (encodeBody ts b).basicBlocks =
      b.basicBlocks.map (encodeBasicBlock ts) := rfl

theorem encodeBasicBlock_statements_eq (ts : List MirTy) (bb : BasicBlock) :
    (encodeBasicBlock ts bb).statements =
      bb.statements.map (encodeStmt ts) := rfl

/-- Anti-laundering guarantee: `encodeStmt` maps `.nop` and only `.nop` to
`.nop`. -/
theorem encodeStmt_no_dormant_noops : EncodeStmtNoDormantNoopsClaim := by
  intro ts s
  cases s <;> constructor <;> intro h <;> first | rfl | cases h

/-! ### Constructor preservation

`decodeProg_encodeProg` alone would still allow an encoder that permutes
semantic constructors (for example, `.add` ↔ `.addUnchecked`) as long as the
decoder permutes them back. The following lemmas lock the operator, operands,
and destination of every encoded assignment, binary operation, and unary
operation to the source constructor. -/

/-- `encodeRvalue` produces `.binaryOp op l' r'` exactly when the source is a
`.binaryOp` with the same operator `op` and operands encoding to `l'` and
`r'`. -/
theorem encodeRvalue_binaryOp_iff : EncodeRvalueBinaryOpIffClaim := by
  intro ts rv op l' r'
  cases rv with
  | binaryOp op₀ l r =>
    constructor
    · intro h
      injection h with h_op h_l h_r
      subst h_op
      exact ⟨l, r, rfl, h_l, h_r⟩
    · intro h
      let ⟨l₁, r₁, h_rv, h_l, h_r⟩ := h
      injection h_rv with h_op h_l₁ h_r₁
      subst h_op; subst h_l₁; subst h_r₁
      dsimp only [encodeRvalue]
      rw [h_l, h_r]
  | use _ | unaryOp _ _ | ref _ _ | addressOf _ _ | aggregateTuple _
  | unsupported =>
    constructor
    · intro h; cases h
    · intro h
      let ⟨_, _, h_rv, _, _⟩ := h
      cases h_rv

/-- `encodeRvalue` produces `.unaryOp op o'` exactly when the source is a
`.unaryOp` with the same operator `op` and an operand encoding to `o'`. -/
theorem encodeRvalue_unaryOp_iff : EncodeRvalueUnaryOpIffClaim := by
  intro ts rv op o'
  cases rv with
  | unaryOp op₀ o =>
    constructor
    · intro h
      injection h with h_op h_o
      subst h_op
      exact ⟨o, rfl, h_o⟩
    · intro h
      let ⟨o₁, h_rv, h_o⟩ := h
      injection h_rv with h_op h_o₁
      subst h_op; subst h_o₁
      dsimp only [encodeRvalue]
      rw [h_o]
  | use _ | binaryOp _ _ _ | ref _ _ | addressOf _ _ | aggregateTuple _
  | unsupported =>
    constructor
    · intro h; cases h
    · intro h
      let ⟨_, h_rv, _⟩ := h
      cases h_rv

/-- `encodeStmt` produces `.assign dst' rv'` exactly when the source is an
`.assign` whose destination and rvalue encode to `dst'` and `rv'`. -/
theorem encodeStmt_assign_iff : EncodeStmtAssignIffClaim := by
  intro ts s dst' rv'
  cases s with
  | assign dst rv =>
    constructor
    · intro h
      injection h with h_dst h_rv
      exact ⟨dst, rv, rfl, h_dst, h_rv⟩
    · intro h
      let ⟨dst₁, rv₁, h_s, h_dst, h_rv⟩ := h
      injection h_s with h_dst₁ h_rv₁
      subst h_dst₁; subst h_rv₁
      dsimp only [encodeStmt]
      rw [h_dst, h_rv]
  | storageLive _ | storageDead _ | nop | unsupported =>
    constructor
    · intro h; cases h
    · intro h
      let ⟨_, _, h_s, _, _⟩ := h
      cases h_s



abbrev SubTable (xs ys : List MirTy) : Prop :=
  ∀ t : MirTy, (∃ i, indexOfTy xs t = some i) → (∃ j, indexOfTy ys t = some j)

theorem SubTable.refl (xs : List MirTy) : SubTable xs xs :=
  fun _ h => h

theorem SubTable.trans {xs ys zs : List MirTy}
    (h₁ : SubTable xs ys) (h₂ : SubTable ys zs) : SubTable xs zs :=
  fun t ht => h₂ t (h₁ t ht)

theorem getElem?_of_indexOfTy {ts : List MirTy} {ty : MirTy} {i : TyId}
    (h : indexOfTy ts ty = some i) :
    MirSemantics.getElem? ts i = some ty := by
  induction ts generalizing i with
  | nil => cases h
  | cons t rest ih =>
    dsimp only [indexOfTy] at h
    cases h_eq : MirTy.beq t ty with
    | true =>
      rw [h_eq] at h
      injection h with h_zero
      subst h_zero
      have h_t : t = ty := MirTy.eq_of_beq h_eq
      subst h_t
      rfl
    | false =>
      rw [h_eq] at h
      cases h_idx : indexOfTy rest ty with
      | none => rw [h_idx] at h; cases h
      | some j =>
        rw [h_idx] at h
        injection h with h_succ
        subst h_succ
        exact ih h_idx

theorem indexOfTy_insertTy_self (ty : MirTy) (ts : List MirTy) :
    ∃ i, indexOfTy (insertTy ty ts) ty = some i := by
  induction ts with
  | nil =>
    refine ⟨0, ?_⟩
    dsimp only [insertTy, indexOfTy]
    rw [MirTy.beq_refl]
    rfl
  | cons t rest ih =>
    cases h_eq : MirTy.beq t ty with
    | true =>
      refine ⟨0, ?_⟩
      dsimp only [insertTy]
      rw [h_eq]
      change indexOfTy (t :: rest) ty = some 0
      dsimp only [indexOfTy]
      rw [h_eq]
      rfl
    | false =>
      let ⟨j, hj⟩ := ih
      refine ⟨j + 1, ?_⟩
      dsimp only [insertTy]
      rw [h_eq]
      change indexOfTy (t :: insertTy ty rest) ty = some (j + 1)
      dsimp only [indexOfTy]
      rw [h_eq, hj]
      rfl

theorem subTable_insertTy (ty : MirTy) (acc : List MirTy) :
    SubTable acc (insertTy ty acc) := by
  intro t ⟨i, hi⟩
  induction acc generalizing i with
  | nil => cases hi
  | cons a rest ih =>
    cases h_ay : MirTy.beq a ty with
    | true =>
      dsimp only [insertTy]; rw [h_ay]; exact ⟨i, hi⟩
    | false =>
      dsimp only [indexOfTy] at hi
      cases h_at : MirTy.beq a t with
      | true =>
        refine ⟨0, ?_⟩
        dsimp only [insertTy]
        rw [h_ay]
        change indexOfTy (a :: insertTy ty rest) t = some 0
        dsimp only [indexOfTy]
        rw [h_at]
        rfl
      | false =>
        rw [h_at] at hi
        cases h_rest : indexOfTy rest t with
        | none => rw [h_rest] at hi; cases hi
        | some j =>
          let ⟨k, hk⟩ := ih j h_rest
          refine ⟨k + 1, ?_⟩
          dsimp only [insertTy]
          rw [h_ay]
          change indexOfTy (a :: insertTy ty rest) t = some (k + 1)
          dsimp only [indexOfTy]
          rw [h_at, hk]
          rfl

theorem getElem?_lookupTyId_of_subTable {ty : MirTy} {acc ts : List MirTy}
    (h_sub : SubTable (insertTy ty acc) ts) :
    MirSemantics.getElem? ts (lookupTyId ts ty) = some ty := by
  let ⟨j, hj⟩ := h_sub ty (indexOfTy_insertTy_self ty acc)
  unfold lookupTyId
  rw [hj]
  exact getElem?_of_indexOfTy hj

mutual
  theorem collectTy_spec (acc : List MirTy) (ty : MirTy) :
      SubTable acc (collectTy acc ty) ∧
      (∀ ts, SubTable (collectTy acc ty) ts →
        MirSemantics.getElem? ts (lookupTyId ts ty) = some ty) := by
    cases ty with
    | bool =>
      dsimp only [collectTy]
      exact ⟨subTable_insertTy .bool acc,
        fun _ h_sub => getElem?_lookupTyId_of_subTable h_sub⟩
    | int w s =>
      dsimp only [collectTy]
      exact ⟨subTable_insertTy (.int w s) acc,
        fun _ h_sub => getElem?_lookupTyId_of_subTable h_sub⟩
    | unit =>
      dsimp only [collectTy]
      exact ⟨subTable_insertTy .unit acc,
        fun _ h_sub => getElem?_lookupTyId_of_subTable h_sub⟩
    | unsupported =>
      dsimp only [collectTy]
      exact ⟨subTable_insertTy .unsupported acc,
        fun _ h_sub => getElem?_lookupTyId_of_subTable h_sub⟩
    | ref m p =>
      dsimp only [collectTy]
      let ⟨h_sub_p, _⟩ := collectTy_spec acc p
      exact ⟨SubTable.trans h_sub_p
          (subTable_insertTy (.ref m p) (collectTy acc p)),
        fun _ h_sub => getElem?_lookupTyId_of_subTable h_sub⟩
    | rawPtr m p =>
      dsimp only [collectTy]
      let ⟨h_sub_p, _⟩ := collectTy_spec acc p
      exact ⟨SubTable.trans h_sub_p
          (subTable_insertTy (.rawPtr m p) (collectTy acc p)),
        fun _ h_sub => getElem?_lookupTyId_of_subTable h_sub⟩
    | tuple fs =>
      dsimp only [collectTy]
      let ⟨h_sub_fs, _⟩ := collectTyList_spec acc fs
      exact ⟨SubTable.trans h_sub_fs
          (subTable_insertTy (.tuple fs) (collectTyList acc fs)),
        fun _ h_sub => getElem?_lookupTyId_of_subTable h_sub⟩

  theorem collectTyList_spec (acc : List MirTy) (tys : List MirTy) :
      SubTable acc (collectTyList acc tys) ∧
      (∀ ts, SubTable (collectTyList acc tys) ts →
        decodeLocalTys ts (tys.map (lookupTyId ts)) = some tys) := by
    cases tys with
    | nil =>
      dsimp only [collectTyList]
      exact ⟨SubTable.refl acc, fun _ _ => rfl⟩
    | cons ty rest =>
      dsimp only [collectTyList]
      let ⟨h_sub₁, h_dec₁⟩ := collectTy_spec acc ty
      let ⟨h_sub₂, h_dec₂⟩ := collectTyList_spec (collectTy acc ty) rest
      refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
      dsimp only [List.map, decodeLocalTys]
      rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]
end

theorem collectProjElem_spec (acc : List MirTy) (e : ProjectionElem) :
    SubTable acc (collectProjElem acc e) ∧
    (∀ ts, SubTable (collectProjElem acc e) ts →
      decodeProjElem ts (encodeProjElem ts e) = some e) := by
  cases e with
  | deref => exact ⟨SubTable.refl acc, fun _ _ => rfl⟩
  | unsupported => exact ⟨SubTable.refl acc, fun _ _ => rfl⟩
  | field idx ty =>
    let ⟨h_sub₁, h_dec₁⟩ := collectTy_spec acc ty
    refine ⟨h_sub₁, fun ts h_sub => ?_⟩
    dsimp only [encodeProjElem, decodeProjElem]
    rw [h_dec₁ ts h_sub]

theorem collectProjList_spec (acc : List MirTy) (es : List ProjectionElem) :
    SubTable acc (collectProjList acc es) ∧
    (∀ ts, SubTable (collectProjList acc es) ts →
      decodeProjList ts (encodeProjList ts es) = some es) := by
  induction es generalizing acc with
  | nil => exact ⟨SubTable.refl acc, fun _ _ => rfl⟩
  | cons e rest ih =>
    let ⟨h_sub₁, h_dec₁⟩ := collectProjElem_spec acc e
    let ⟨h_sub₂, h_dec₂⟩ := ih (collectProjElem acc e)
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_sub => ?_⟩
    dsimp only [encodeProjList, decodeProjList]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_sub), h_dec₂ ts h_sub]

theorem collectPlace_spec (acc : List MirTy) (p : Place) :
    SubTable acc (collectPlace acc p) ∧
    (∀ ts, SubTable (collectPlace acc p) ts →
      decodePlace ts (encodePlace ts p) = some p) := by
  cases p with
  | mk localId proj =>
    let ⟨h_sub, h_dec⟩ := collectProjList_spec acc proj
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodePlace, decodePlace]
    rw [h_dec ts h_s]

theorem collectOperand_spec (acc : List MirTy) (op : Operand) :
    SubTable acc (collectOperand acc op) ∧
    (∀ ts, SubTable (collectOperand acc op) ts →
      decodeOperand ts (encodeOperand ts op) = some op) := by
  cases op with
  | copy p =>
    let ⟨h_sub, h_dec⟩ := collectPlace_spec acc p
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeOperand, decodeOperand]
    rw [h_dec ts h_s]
  | move p =>
    let ⟨h_sub, h_dec⟩ := collectPlace_spec acc p
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeOperand, decodeOperand]
    rw [h_dec ts h_s]
  | constant c =>
    cases c with
    | mk ty lit =>
      let ⟨h_sub₁, h_dec₁⟩ := collectTy_spec acc ty
      refine ⟨h_sub₁, fun ts h_s => ?_⟩
      dsimp only [encodeOperand, decodeOperand]
      rw [h_dec₁ ts h_s]

theorem collectOperandList_spec (acc : List MirTy) (ops : List Operand) :
    SubTable acc (collectOperandList acc ops) ∧
    (∀ ts, SubTable (collectOperandList acc ops) ts →
      decodeOperandList ts (encodeOperandList ts ops) = some ops) := by
  induction ops generalizing acc with
  | nil => exact ⟨SubTable.refl acc, fun _ _ => rfl⟩
  | cons op rest ih =>
    let ⟨h_sub₁, h_dec₁⟩ := collectOperand_spec acc op
    let ⟨h_sub₂, h_dec₂⟩ := ih (collectOperand acc op)
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_sub => ?_⟩
    dsimp only [encodeOperandList, decodeOperandList]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_sub), h_dec₂ ts h_sub]

theorem collectRvalue_spec (acc : List MirTy) (rv : Rvalue) :
    SubTable acc (collectRvalue acc rv) ∧
    (∀ ts, SubTable (collectRvalue acc rv) ts →
      decodeRvalue ts (encodeRvalue ts rv) = some rv) := by
  cases rv with
  | use op =>
    let ⟨h_sub, h_dec⟩ := collectOperand_spec acc op
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeRvalue, decodeRvalue]
    rw [h_dec ts h_s]
  | binaryOp op l r =>
    let ⟨h_sub₁, h_dec₁⟩ := collectOperand_spec acc l
    let ⟨h_sub₂, h_dec₂⟩ := collectOperand_spec (collectOperand acc l) r
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    dsimp only [encodeRvalue, decodeRvalue]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]
  | unaryOp op opnd =>
    let ⟨h_sub, h_dec⟩ := collectOperand_spec acc opnd
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeRvalue, decodeRvalue]
    rw [h_dec ts h_s]
  | ref m p =>
    let ⟨h_sub, h_dec⟩ := collectPlace_spec acc p
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeRvalue, decodeRvalue]
    rw [h_dec ts h_s]
  | addressOf m p =>
    let ⟨h_sub, h_dec⟩ := collectPlace_spec acc p
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeRvalue, decodeRvalue]
    rw [h_dec ts h_s]
  | aggregateTuple ops =>
    let ⟨h_sub, h_dec⟩ := collectOperandList_spec acc ops
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeRvalue, decodeRvalue]
    rw [h_dec ts h_s]
  | unsupported => exact ⟨SubTable.refl acc, fun _ _ => rfl⟩

theorem collectStmt_spec (acc : List MirTy) (s : StatementKind) :
    SubTable acc (collectStmt acc s) ∧
    (∀ ts, SubTable (collectStmt acc s) ts →
      decodeStmt ts (encodeStmt ts s) = some s) := by
  cases s with
  | assign dst rv =>
    let ⟨h_sub₁, h_dec₁⟩ := collectPlace_spec acc dst
    let ⟨h_sub₂, h_dec₂⟩ := collectRvalue_spec (collectPlace acc dst) rv
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    dsimp only [encodeStmt, decodeStmt]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]
  | storageLive _ | storageDead _ | nop | unsupported =>
    exact ⟨SubTable.refl acc, fun _ _ => rfl⟩

theorem collectStmtList_spec (acc : List MirTy) (ss : List StatementKind) :
    SubTable acc (collectStmtList acc ss) ∧
    (∀ ts, SubTable (collectStmtList acc ss) ts →
      decodeStmtList ts (ss.map (encodeStmt ts)) = some ss) := by
  induction ss generalizing acc with
  | nil => exact ⟨SubTable.refl acc, fun _ _ => rfl⟩
  | cons s rest ih =>
    let ⟨h_sub₁, h_dec₁⟩ := collectStmt_spec acc s
    let ⟨h_sub₂, h_dec₂⟩ := ih (collectStmt acc s)
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    dsimp only [List.map, decodeStmtList]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]

theorem collectTerminator_spec (acc : List MirTy) (term : TerminatorKind) :
    SubTable acc (collectTerminator acc term) ∧
    (∀ ts, SubTable (collectTerminator acc term) ts →
      decodeTerminator ts (encodeTerminator ts term) = some term) := by
  cases term with
  | goto _ | return_ | unreachable | unwindResume | unsupported =>
    exact ⟨SubTable.refl acc, fun _ _ => rfl⟩
  | switchInt d targets =>
    let ⟨h_sub, h_dec⟩ := collectOperand_spec acc d
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeTerminator, decodeTerminator]
    rw [h_dec ts h_s]
  | assert c exp msg t u =>
    let ⟨h_sub, h_dec⟩ := collectOperand_spec acc c
    refine ⟨h_sub, fun ts h_s => ?_⟩
    dsimp only [encodeTerminator, decodeTerminator]
    rw [h_dec ts h_s]
  | call callee args dst t u =>
    let ⟨h_sub₁, h_dec₁⟩ := collectOperandList_spec acc args
    let ⟨h_sub₂, h_dec₂⟩ := collectPlace_spec (collectOperandList acc args) dst
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    dsimp only [encodeTerminator, decodeTerminator]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]

theorem collectBasicBlock_spec (acc : List MirTy) (bb : BasicBlock) :
    SubTable acc (collectBasicBlock acc bb) ∧
    (∀ ts, SubTable (collectBasicBlock acc bb) ts →
      decodeBasicBlock ts (encodeBasicBlock ts bb) = some bb) := by
  cases bb with
  | mk stmts term cleanup =>
    let ⟨h_sub₁, h_dec₁⟩ := collectStmtList_spec acc stmts
    let ⟨h_sub₂, h_dec₂⟩ :=
      collectTerminator_spec (collectStmtList acc stmts) term
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    dsimp only [encodeBasicBlock, decodeBasicBlock]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]

theorem collectBasicBlockList_spec (acc : List MirTy) (bbs : List BasicBlock) :
    SubTable acc (collectBasicBlockList acc bbs) ∧
    (∀ ts, SubTable (collectBasicBlockList acc bbs) ts →
      decodeBasicBlockList ts (bbs.map (encodeBasicBlock ts)) = some bbs) := by
  induction bbs generalizing acc with
  | nil => exact ⟨SubTable.refl acc, fun _ _ => rfl⟩
  | cons bb rest ih =>
    let ⟨h_sub₁, h_dec₁⟩ := collectBasicBlock_spec acc bb
    let ⟨h_sub₂, h_dec₂⟩ := ih (collectBasicBlock acc bb)
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    dsimp only [List.map, decodeBasicBlockList]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]

theorem collectBody_spec (acc : List MirTy) (b : Body) :
    SubTable acc (collectBody acc b) ∧
    (∀ ts, SubTable (collectBody acc b) ts →
      decodeBody ts (encodeBody ts b) = some b) := by
  cases b with
  | mk argCount locals bbs =>
    let ⟨h_sub₁, h_dec₁⟩ := collectTyList_spec acc locals
    let ⟨h_sub₂, h_dec₂⟩ :=
      collectBasicBlockList_spec (collectTyList acc locals) bbs
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    dsimp only [encodeBody, decodeBody]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]

theorem collectBodyList_spec (acc : List MirTy) (bs : List Body) :
    SubTable acc (collectBodyList acc bs) ∧
    (∀ ts, SubTable (collectBodyList acc bs) ts →
      decodeBodyList ts (bs.map (encodeBody ts)) = some bs) := by
  induction bs generalizing acc with
  | nil => exact ⟨SubTable.refl acc, fun _ _ => rfl⟩
  | cons b rest ih =>
    let ⟨h_sub₁, h_dec₁⟩ := collectBody_spec acc b
    let ⟨h_sub₂, h_dec₂⟩ := ih (collectBody acc b)
    refine ⟨SubTable.trans h_sub₁ h_sub₂, fun ts h_s => ?_⟩
    dsimp only [List.map, decodeBodyList]
    rw [h_dec₁ ts (SubTable.trans h_sub₂ h_s), h_dec₂ ts h_s]

/-- Unconditional global anti-laundering theorem: every `p : Program` with
inline `MirTy` round-trips through `encodeProg` and `decodeProg` with zero
preconditions, including its target `pointerWidthBits` and
`mirProfileVersion`. -/
theorem decodeProg_encodeProg : DecodeProgEncodeProgClaim := by
  intro p
  cases p with
  | mk bodies entryDefId pointerWidthBits mirProfileVersion =>
    unfold encodeProg decodeProg collectProgTypes
    dsimp only
    let ⟨_, h_dec⟩ := collectBodyList_spec initTypeTable bodies
    rw [h_dec (collectBodyList initTypeTable bodies) (SubTable.refl _)]

mutual
  theorem collectTy_canonical (acc : List MirTy) (ty : MirTy)
      (h : typesAreCanonical acc = true) :
      typesAreCanonical (collectTy acc ty) = true := by
    cases ty with
    | bool =>
      dsimp only [collectTy]
      exact typesAreCanonical_insertTy .bool acc h
    | int w s =>
      dsimp only [collectTy]
      exact typesAreCanonical_insertTy (.int w s) acc h
    | unit =>
      dsimp only [collectTy]
      exact typesAreCanonical_insertTy .unit acc h
    | unsupported =>
      dsimp only [collectTy]
      exact typesAreCanonical_insertTy .unsupported acc h
    | ref m p =>
      dsimp only [collectTy]
      exact typesAreCanonical_insertTy (.ref m p) (collectTy acc p)
        (collectTy_canonical acc p h)
    | rawPtr m p =>
      dsimp only [collectTy]
      exact typesAreCanonical_insertTy (.rawPtr m p) (collectTy acc p)
        (collectTy_canonical acc p h)
    | tuple fs =>
      dsimp only [collectTy]
      exact typesAreCanonical_insertTy (.tuple fs) (collectTyList acc fs)
        (collectTyList_canonical acc fs h)

  theorem collectTyList_canonical (acc : List MirTy) (tys : List MirTy)
      (h : typesAreCanonical acc = true) :
      typesAreCanonical (collectTyList acc tys) = true := by
    cases tys with
    | nil =>
      dsimp only [collectTyList]
      exact h
    | cons ty rest =>
      dsimp only [collectTyList]
      exact collectTyList_canonical (collectTy acc ty) rest
        (collectTy_canonical acc ty h)
end

theorem collectProjElem_canonical {acc : List MirTy} (e : ProjectionElem)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectProjElem acc e) = true := by
  cases e with
  | deref | unsupported => exact h
  | field _ ty => exact collectTy_canonical acc ty h

theorem collectProjList_canonical {acc : List MirTy} (es : List ProjectionElem)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectProjList acc es) = true := by
  induction es generalizing acc with
  | nil => exact h
  | cons e rest ih => exact ih (collectProjElem_canonical e h)

theorem collectPlace_canonical {acc : List MirTy} (p : Place)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectPlace acc p) = true :=
  collectProjList_canonical p.projection h

theorem collectOperand_canonical {acc : List MirTy} (op : Operand)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectOperand acc op) = true := by
  cases op with
  | copy p | move p => exact collectPlace_canonical p h
  | constant c => exact collectTy_canonical acc c.ty h

theorem collectOperandList_canonical {acc : List MirTy} (ops : List Operand)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectOperandList acc ops) = true := by
  induction ops generalizing acc with
  | nil => exact h
  | cons op rest ih => exact ih (collectOperand_canonical op h)

theorem collectRvalue_canonical {acc : List MirTy} (rv : Rvalue)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectRvalue acc rv) = true := by
  cases rv with
  | use op | unaryOp _ op => exact collectOperand_canonical op h
  | binaryOp _ l r =>
    exact collectOperand_canonical r (collectOperand_canonical l h)
  | ref _ p | addressOf _ p => exact collectPlace_canonical p h
  | aggregateTuple ops => exact collectOperandList_canonical ops h
  | unsupported => exact h

theorem collectStmt_canonical {acc : List MirTy} (s : StatementKind)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectStmt acc s) = true := by
  cases s with
  | assign dst rv =>
    exact collectRvalue_canonical rv (collectPlace_canonical dst h)
  | storageLive _ | storageDead _ | nop | unsupported => exact h

theorem collectStmtList_canonical {acc : List MirTy} (ss : List StatementKind)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectStmtList acc ss) = true := by
  induction ss generalizing acc with
  | nil => exact h
  | cons s rest ih => exact ih (collectStmt_canonical s h)

theorem collectTerminator_canonical {acc : List MirTy} (term : TerminatorKind)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectTerminator acc term) = true := by
  cases term with
  | goto _ | return_ | unreachable | unwindResume | unsupported => exact h
  | switchInt d _ | assert d _ _ _ _ => exact collectOperand_canonical d h
  | call _ args dst _ _ =>
    exact collectPlace_canonical dst (collectOperandList_canonical args h)

theorem collectBasicBlock_canonical {acc : List MirTy} (bb : BasicBlock)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectBasicBlock acc bb) = true :=
  collectTerminator_canonical bb.terminator
    (collectStmtList_canonical bb.statements h)

theorem collectBasicBlockList_canonical {acc : List MirTy}
    (bbs : List BasicBlock)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectBasicBlockList acc bbs) = true := by
  induction bbs generalizing acc with
  | nil => exact h
  | cons bb rest ih => exact ih (collectBasicBlock_canonical bb h)

theorem collectBody_canonical {acc : List MirTy} (b : Body)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectBody acc b) = true :=
  collectBasicBlockList_canonical b.basicBlocks
    (collectTyList_canonical acc b.locals h)

theorem collectBodyList_canonical {acc : List MirTy} (bs : List Body)
    (h : typesAreCanonical acc = true) :
    typesAreCanonical (collectBodyList acc bs) = true := by
  induction bs generalizing acc with
  | nil => exact h
  | cons b rest ih => exact ih (collectBody_canonical b h)

/-- Canonical type deduplication theorem: for every `p : Program`,
`(encodeProg p).types` contains no duplicate `MirTy` entries, guaranteeing
that nominal `TyId` equality in `lean-miri` (`assertSameType`,
`assertRvalueLayout`) agrees with structural `MirTy` equality. -/
theorem encodeProg_types_canonical : EncodeProgTypesCanonicalClaim :=
  fun p => collectBodyList_canonical p.bodies rfl

/-! ## Bijective Simulation Invariant (`SimulationInv`) -/

theorem unzipRefSlots_zipRefLocals {bodyLocals : List MirTy}
    {slots : List LocalSlot}
    (h_len : slots.length = bodyLocals.length) :
    unzipRefSlots (zipRefLocals bodyLocals slots) = slots := by
  induction bodyLocals generalizing slots with
  | nil =>
    cases slots with
    | nil => rfl
    | cons _ _ => cases h_len
  | cons ty tys ih =>
    cases slots with
    | nil => cases h_len
    | cons s ss =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h_len
      exact congrArg (s :: ·) (ih h_len)

/-- Bijectivity of `SimulationInv` (left-injective): any `RefState` `rs`
corresponds to at most one $M_{\text{anneal}}$ `State`. -/
theorem state_unique_of_simulationInv : StateUniqueOfSimulationInvClaim := by
  intro p s₁ s₂ rs h₁ h₂
  let ⟨f₁, rf₁, _, hs₁, hrs₁, hcm₁, _, body₁, _, hlen₁, hrf₁⟩ := h₁
  let ⟨f₂, rf₂, _, hs₂, hrs₂, hcm₂, _, body₂, _, hlen₂, hrf₂⟩ := h₂
  rw [hrs₁] at hrs₂
  injection hrs₂ with _ h_tail
  injection h_tail with h_rf_eq
  subst h_rf_eq
  have h_def : f₁.defId = f₂.defId := by
    have := congrArg RefFrameState.defId (hrf₁.symm.trans hrf₂)
    exact this
  have h_blk : f₁.blockIdx = f₂.blockIdx := by
    have := congrArg RefFrameState.blockIdx (hrf₁.symm.trans hrf₂)
    exact this
  have h_stmt : f₁.stmtIdx = f₂.stmtIdx := by
    have := congrArg RefFrameState.stmtIdx (hrf₁.symm.trans hrf₂)
    exact this
  have h_loc_eq : zipRefLocals body₁.locals f₁.locals =
      zipRefLocals body₂.locals f₂.locals := by
    have := congrArg RefFrameState.locals (hrf₁.symm.trans hrf₂)
    exact this
  have h_slots : f₁.locals = f₂.locals := by
    have h_u := congrArg unzipRefSlots h_loc_eq
    rw [unzipRefSlots_zipRefLocals hlen₁,
      unzipRefSlots_zipRefLocals hlen₂] at h_u
    exact h_u
  have h_f : f₁ = f₂ := by
    cases f₁; cases f₂
    simp only [ FrameState.mk.injEq]
    exact ⟨h_def, h_blk, h_stmt, h_slots⟩
  subst h_f
  cases s₁; cases s₂
  simp only [State.mk.injEq]
  exact ⟨hs₁.trans hs₂.symm, hcm₁.symm.trans hcm₂⟩

/-- Bijectivity of `SimulationInv` (right-injective at fixed step counters):
any $M_{\text{anneal}}$ `State` `s` and step counters
`(stepsExecuted, maxSteps)` uniquely determine `rs`, including its caller
sentinel frame. -/
theorem refState_unique_of_simulationInv :
    RefStateUniqueOfSimulationInvClaim := by
  intro p s rs₁ rs₂ h₁ h₂ h_steps h_max
  let ⟨f₁, rf₁, retTy₁, hs₁, hrs₁, hcm₁, hret₁, body₁, hbody₁, _, hrf₁⟩ := h₁
  let ⟨f₂, rf₂, retTy₂, hs₂, hrs₂, hcm₂, hret₂, body₂, hbody₂, _, hrf₂⟩ := h₂
  rw [hs₁] at hs₂
  injection hs₂ with h_f_eq
  subst h_f_eq
  rw [hbody₁] at hbody₂
  injection hbody₂ with h_b_eq
  subst h_b_eq
  rw [hret₁] at hret₂
  injection hret₂ with h_ret_eq
  subst h_ret_eq
  subst hrf₁; subst hrf₂
  cases rs₁; cases rs₂
  simp only [RefState.mk.injEq]
  exact ⟨hrs₁.trans hrs₂.symm, hcm₁.trans hcm₂.symm, h_steps, h_max⟩

theorem getElem?_zipRefLocals_some {bodyLocals : List MirTy}
    {slots : List LocalSlot}
    {i : Nat} {ty : MirTy} {slot : LocalSlot}
    (h_ty : MirSemantics.getElem? bodyLocals i = some ty)
    (h_slot : MirSemantics.getElem? slots i = some slot) :
    MirSemantics.getElem? (zipRefLocals bodyLocals slots) i =
      some ⟨slot, some ty⟩ := by
  induction bodyLocals generalizing slots i with
  | nil => cases h_ty
  | cons t ts ih =>
    cases slots with
    | nil => cases h_slot
    | cons s ss =>
      cases i with
      | zero =>
        injection h_ty with h_t
        injection h_slot with h_s
        subst h_t; subst h_s
        rfl
      | succ j =>
        exact ih h_ty h_slot

theorem getElem?_zipRefLocals_none_left {bodyLocals : List MirTy}
    {slots : List LocalSlot}
    {i : Nat} (h_ty : MirSemantics.getElem? bodyLocals i = none) :
    MirSemantics.getElem? (zipRefLocals bodyLocals slots) i = none := by
  induction bodyLocals generalizing slots i with
  | nil => rfl
  | cons t ts ih =>
    cases slots with
    | nil => rfl
    | cons s ss =>
      cases i with
      | zero => cases h_ty
      | succ j => exact ih h_ty

theorem getElem?_zipRefLocals_none_right {bodyLocals : List MirTy}
    {slots : List LocalSlot}
    {i : Nat} (h_slot : MirSemantics.getElem? slots i = none) :
    MirSemantics.getElem? (zipRefLocals bodyLocals slots) i = none := by
  induction bodyLocals generalizing slots i with
  | nil => rfl
  | cons t ts ih =>
    cases slots with
    | nil => rfl
    | cons s ss =>
      cases i with
      | zero => cases h_slot
      | succ j => exact ih h_slot

theorem getElem?_some_of_length_eq {α β : Type} {xs : List α} {ys : List β}
    {i : Nat} {x : α}
    (h_len : xs.length = ys.length)
    (h_x : MirSemantics.getElem? xs i = some x) :
    ∃ y : β, MirSemantics.getElem? ys i = some y := by
  induction xs generalizing ys i with
  | nil => cases h_x
  | cons a as ih =>
    cases ys with
    | nil => cases h_len
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h_len
      cases i with
      | zero => exact ⟨b, rfl⟩
      | succ j => exact @ih bs j h_len h_x

theorem setElem?_length {α : Type} {xs xs' : List α} {i : Nat} {v : α}
    (h : MirSemantics.setElem? xs i v = some xs') :
    xs'.length = xs.length := by
  induction xs generalizing xs' i with
  | nil => cases h
  | cons x rest ih =>
    cases i with
    | zero =>
      injection h with h_eq
      subst h_eq
      rfl
    | succ j =>
      dsimp only [MirSemantics.setElem?] at h
      cases h_rest : MirSemantics.setElem? rest j v with
      | none => rw [h_rest] at h; cases h
      | some rest' =>
        rw [h_rest] at h
        injection h with h_eq
        subst h_eq
        simp only [List.length_cons, ih h_rest]

theorem setElem?_zipRefLocals_some {bodyLocals : List MirTy}
    {slots slots' : List LocalSlot}
    {i : Nat} {ty : MirTy} {slot' : LocalSlot}
    (h_ty : MirSemantics.getElem? bodyLocals i = some ty)
    (h_set : MirSemantics.setElem? slots i slot' = some slots') :
    MirSemantics.setElem? (zipRefLocals bodyLocals slots) i ⟨slot', some ty⟩ =
      some (zipRefLocals bodyLocals slots') := by
  induction bodyLocals generalizing slots slots' i with
  | nil => cases h_ty
  | cons t ts ih =>
    cases slots with
    | nil => cases h_set
    | cons s ss =>
      cases i with
      | zero =>
        injection h_ty with h_t
        injection h_set with h_s
        subst h_t; subst h_s
        rfl
      | succ j =>
        dsimp only [MirSemantics.setElem?] at h_set
        cases h_ss : MirSemantics.setElem? ss j slot' with
        | none => rw [h_ss] at h_set; cases h_set
        | some ss' =>
          rw [h_ss] at h_set
          injection h_set with h_s
          subst h_s
          dsimp only [zipRefLocals, MirSemantics.setElem?]
          rw [ih h_ty h_ss]

theorem setElem?_zipRefLocals_none {bodyLocals : List MirTy}
    {slots : List LocalSlot}
    {i : Nat} {rval : RefLocalState} {slot' : LocalSlot}
    (h_set : MirSemantics.setElem? slots i slot' = none) :
    MirSemantics.setElem? (zipRefLocals bodyLocals slots) i rval = none := by
  induction bodyLocals generalizing slots i with
  | nil => rfl
  | cons t ts ih =>
    cases slots with
    | nil => rfl
    | cons s ss =>
      cases i with
      | zero => cases h_set
      | succ j =>
        dsimp only [MirSemantics.setElem?] at h_set
        cases h_ss : MirSemantics.setElem? ss j slot' with
        | some _ => rw [h_ss] at h_set; cases h_set
        | none =>
          dsimp only [zipRefLocals, MirSemantics.setElem?]
          rw [ih h_ss]

theorem evalOperandToSlot_length {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot}
    {op : Operand} {ty : MirTy} {optVal : Option Val}
    (h : evalOperandToSlot bodyLocals locals op = .ok (ty, optVal, locals')) :
    locals'.length = locals.length := by
  cases op with
  | copy p =>
    dsimp only [evalOperandToSlot] at h
    cases h_emp : p.projection.isEmpty <;> rw [h_emp] at h
    · cases h
    · cases h_ty : MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [h_ty] at h; cases h
      | some ty₀ =>
        cases h_sl : MirSemantics.getElem? locals p.localId with
        | none => rw [h_ty, h_sl] at h; cases h
        | some slot =>
        rw [h_ty, h_sl] at h
        cases slot with
        | dead => cases h
        | live opt =>
          injection h with h_tup
          injection h_tup with _ h_rest
          injection h_rest with _ h_loc
          subst h_loc
          rfl
  | move p =>
    dsimp only [evalOperandToSlot] at h
    cases h_emp : p.projection.isEmpty <;> rw [h_emp] at h
    · cases h
    · cases h_ty : MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [h_ty] at h; cases h
      | some ty₀ =>
        cases h_sl : MirSemantics.getElem? locals p.localId with
        | none => rw [h_ty, h_sl] at h; cases h
        | some slot =>
        rw [h_ty, h_sl] at h
        cases slot with
        | dead => cases h
        | live opt =>
          dsimp only at h
          cases h_set :
              MirSemantics.setElem? locals p.localId (liveUninitSlot ty₀) <;>
            rw [h_set] at h
          · cases h
          · injection h with h_tup
            injection h_tup with _ h_rest
            injection h_rest with _ h_loc
            subst h_loc
            exact setElem?_length h_set
  | constant c =>
    dsimp only [evalOperandToSlot] at h
    cases h_lit : evalConstLit c.ty c.lit <;> rw [h_lit] at h
    · cases h
    · injection h with h_tup
      injection h_tup with _ h_rest
      injection h_rest with _ h_loc
      subst h_loc
      rfl

theorem evalPrimitiveOperand_length {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot}
    {opnd : Operand} {v : Val}
    (h : evalPrimitiveOperand bodyLocals locals opnd = .ok (v, locals')) :
    locals'.length = locals.length := by
  unfold evalPrimitiveOperand at h
  cases h_op : evalOperandToSlot bodyLocals locals opnd with
  | error _ => rw [h_op] at h; cases h
  | ok res =>
    let ⟨ty, optVal, l₁⟩ := res
    rw [h_op] at h
    dsimp only at h
    cases h_pr : isPrimitiveReadableTy ty <;> rw [h_pr] at h
    · cases h
    · cases optVal with
      | none => cases h
      | some v₀ =>
        injection h with h_tup
        injection h_tup with _ h_loc
        subst h_loc
        exact evalOperandToSlot_length h_op

theorem evalRvalue_length {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot}
    {dstTy : MirTy} {rv : Rvalue} {v : Val}
    (h : evalRvalue bodyLocals locals dstTy rv = .ok (v, locals')) :
    locals'.length = locals.length := by
  cases rv with
  | use opnd =>
    dsimp only [evalRvalue] at h
    cases h_op : evalOperandToSlot bodyLocals locals opnd with
    | error _ => rw [h_op] at h; cases h
    | ok res =>
      let ⟨srcTy, optVal, l₁⟩ := res
      rw [h_op] at h
      dsimp only at h
      cases h_eq_ty : MirTy.beq srcTy dstTy <;> rw [h_eq_ty] at h
      · cases h
      · cases optVal with
        | none => cases h
        | some v₀ =>
          injection h with h_tup
          injection h_tup with _ h_loc
          subst h_loc
          exact evalOperandToSlot_length h_op
  | binaryOp op lhs rhs =>
    dsimp only [evalRvalue] at h
    cases h_l : evalPrimitiveOperand bodyLocals locals lhs with
    | error _ => rw [h_l] at h; cases h
    | ok resL =>
      let ⟨lVal, l₁⟩ := resL
      rw [h_l] at h
      dsimp only at h
      cases h_r : evalPrimitiveOperand bodyLocals l₁ rhs with
      | error _ => rw [h_r] at h; cases h
      | ok resR =>
        let ⟨rVal, l₂⟩ := resR
        rw [h_r] at h
        dsimp only at h
        cases h_b : evalBinOp op lVal rVal <;> rw [h_b] at h
        · cases h
        · injection h with h_tup
          injection h_tup with _ h_loc
          subst h_loc
          exact (evalPrimitiveOperand_length h_r).trans
            (evalPrimitiveOperand_length h_l)
  | unaryOp op opnd =>
    dsimp only [evalRvalue] at h
    cases h_op : evalPrimitiveOperand bodyLocals locals opnd with
    | error _ => rw [h_op] at h; cases h
    | ok res =>
      let ⟨v₀, l₁⟩ := res
      rw [h_op] at h
      dsimp only at h
      cases h_u : evalUnOp op v₀ <;> rw [h_u] at h
      · cases h
      · injection h with h_tup
        injection h_tup with _ h_loc
        subst h_loc
        exact evalPrimitiveOperand_length h_op
  | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported =>
    cases h

theorem writePlace_length {locals locals' : List LocalSlot}
    {dstLocalId : LocalId} {dstTy : MirTy} {val : Val}
    (h : writePlace locals dstLocalId dstTy val = .ok locals') :
    locals'.length = locals.length := by
  unfold writePlace at h
  cases h_chk : checkVal val dstTy <;> rw [h_chk] at h
  · cases h
  · cases h_get : MirSemantics.getElem? locals dstLocalId with
    | none => rw [h_get] at h; cases h
    | some slot =>
      rw [h_get] at h
      cases slot with
      | dead => cases h
      | live _ =>
        dsimp only at h
        cases h_set :
            MirSemantics.setElem? locals dstLocalId (.live (some val)) <;>
          rw [h_set] at h
        · cases h
        · injection h with h_eq
          subst h_eq
          exact setElem?_length h_set

theorem decodeProjList_isEmpty {ts : List MirTy}
    {rproj : List RefProjectionElem}
    {proj : List ProjectionElem}
    (h : decodeProjList ts rproj = some proj) :
    rproj.isEmpty = proj.isEmpty := by
  cases rproj with
  | nil =>
    injection h with h_eq
    subst h_eq
    rfl
  | cons e es =>
    dsimp only [decodeProjList] at h
    cases h₁ : decodeProjElem ts e <;> cases h₂ : decodeProjList ts es <;>
      rw [h₁, h₂] at h <;> cases h
    rfl

theorem decodePlace_inv {ts : List MirTy} {rp : RefPlace} {p : Place}
    (h : decodePlace ts rp = some p) :
    rp.localId = p.localId ∧ rp.projection.isEmpty = p.projection.isEmpty := by
  unfold decodePlace at h
  cases h_proj : decodeProjList ts rp.projection with
  | none => rw [h_proj] at h; cases h
  | some proj =>
    rw [h_proj] at h
    injection h with h_eq
    subst h_eq
    exact ⟨rfl, decodeProjList_isEmpty h_proj⟩

noncomputable def mapSlotRes (bodyLocals : List MirTy) :
    Except FaultKind (MirTy × Option Val × List LocalSlot) →
    Except FaultKind (MirTy × Option Val × List RefLocalState)
  | .error k => .error k
  | .ok (ty, optVal, slots') => .ok (ty, optVal, zipRefLocals bodyLocals slots')

noncomputable def mapValRes (bodyLocals : List MirTy) :
    Except FaultKind (Val × List LocalSlot) →
    Except FaultKind (Val × List RefLocalState)
  | .error k => .error k
  | .ok (v, slots') => .ok (v, zipRefLocals bodyLocals slots')

noncomputable def mapSlotsRes (bodyLocals : List MirTy) :
    Except FaultKind (List LocalSlot) →
    Except FaultKind (List RefLocalState)
  | .error k => .error k
  | .ok slots' => .ok (zipRefLocals bodyLocals slots')

/-!
## Reference Arithmetic, Constant, and Branch Equivalence (`vendor/lean-miri`)
-/

section MiriEquiv

open Miri.ABI Miri.Memory Miri.Interpreter

theorem bitVec_zeroExtend_eq {w : Nat} (hw : w ≤ 128) (x : BitVec w) :
    BitVec.zeroExtend 128 x = bvZeroExtend 128 x := by
  apply BitVec.eq_of_toNat_eq
  dsimp only [BitVec.zeroExtend, BitVec.setWidth, bvZeroExtend]
  rw [dite_eq_left hw, BitVec.toNat_setWidth', BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (BitVec.setWidth'._proof_1 hw x)).symm

theorem bitVec_ofInt_eq (n : Nat) (i : Int) :
    BitVec.ofInt n i = bvOfInt n i := by
  apply BitVec.eq_of_toNat_eq
  dsimp only [bvOfInt]
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  change (intEmod i (Int.ofNat (HPow.hPow 2 n))).toNat =
    HMod.hMod (intEmod i (Int.ofNat (HPow.hPow 2 n))).toNat (HPow.hPow 2 n)
  exact (Nat.mod_eq_of_lt (BitVec.ofInt._proof_1 n i)).symm

theorem bitVec_signExtend_eq {w : Nat} (v : Nat) (x : BitVec w) :
    BitVec.signExtend v x = bvSignExtend v x := by
  dsimp only [BitVec.signExtend, bvSignExtend]
  rw [bitVec_ofInt_eq]
  rfl

theorem size_truncate_eq (w : IntWidth) (v : BitVec 128) :
    (toMiriSize w).truncate v = .ok (truncateBits w v) := by
  cases w <;> (
    change Except.ok (BitVec.zeroExtend 128 (BitVec.extractLsb _ 0 v)) =
      .ok (truncateBits _ v)
    rw [bitVec_zeroExtend_eq (by decide)]
    rfl)

theorem size_signExtend_eq (w : IntWidth) (v : BitVec 128) :
    (toMiriSize w).signExtend v = .ok (signExtendBits w v) := by
  cases w <;> (
    change Except.ok (BitVec.signExtend 128 (BitVec.extractLsb _ 0 v)).toInt =
      .ok (signExtendBits _ v)
    rw [bitVec_signExtend_eq]
    rfl)

theorem miriScalar_toUInt (w : IntWidth) (bits : BitVec 128) :
    (miriScalar w bits).toUInt (toMiriSize w) = .ok (truncateBits w bits) := by
  have h : (miriScalar w bits).toUInt (toMiriSize w) =
      ((toMiriSize w).truncate bits).mapError ScalarIntError.sizeError := by
    cases w <;> rfl
  rw [h, size_truncate_eq]
  rfl

theorem miriScalar_toInt (w : IntWidth) (bits : BitVec 128) :
    (miriScalar w bits).toInt (toMiriSize w) =
      .ok (signExtendBits w (truncateBits w bits)) := by
  have h : (miriScalar w bits).toInt (toMiriSize w) =
      match (toMiriSize w).truncate bits with
      | .ok b =>
        ((toMiriSize w).signExtend b).mapError ScalarIntError.sizeError
      | .error e => .error (.sizeError e) := by
    cases w <;> rfl
  rw [h, size_truncate_eq]
  dsimp only
  rw [size_signExtend_eq]
  rfl

theorem integerOps_decode_eq (sv : ScalarVal) :
    IntegerOps.decode (miriIntValue sv) = .ok (decodeScalar sv) := by
  cases sv with
  | mk w s bits =>
    have hs : (toMiriIntType w s).signed = s := by cases w <;> cases s <;> rfl
    dsimp only [IntegerOps.decode, miriIntValue, decodeScalar]
    rw [hs]
    cases s with
    | true =>
      change ((miriScalar w bits).toInt (toMiriSize w)).mapError
        IntegerOpError.scalar = _
      rw [miriScalar_toInt]
      rfl
    | false =>
      change bind
        (((miriScalar w bits).toUInt (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun u => pure (Int.ofNat u.toNat)) = _
      rw [miriScalar_toUInt]
      rfl

theorem toMiriIntType_signed (w : IntWidth) (s : Bool) :
    (toMiriIntType w s).signed = s := by
  cases w <;> cases s <;> rfl

theorem toMiriIntType_size (w : IntWidth) (s : Bool) :
    (toMiriIntType w s).size = toMiriSize w := rfl

theorem unary_truncate_signed_eq (w : IntWidth) (resInt : Int) :
    (match bind
        ((ScalarInt.truncateFromInt
          (BitVec.ofInt 128 resInt).toInt (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun x => pure x.1) with
    | .ok sc =>
      (Except.ok (Val.scalar ⟨w, true, sc.data⟩) : Except FaultKind Val)
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match truncateScalar w true resInt with
    | .ok (res, _) => .ok (.scalar res)
    | .error k => .error k) := by
  rw [bitVec_ofInt_eq]
  change (match bind
      ((ScalarInt.truncateFromInt
        (bvToInt (bvOfInt 128 resInt)) (toMiriSize w)).mapError
        IntegerOpError.scalar)
      (fun x => pure x.1) with
    | .ok sc =>
      (Except.ok (Val.scalar ⟨w, true, sc.data⟩) : Except FaultKind Val)
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match truncateScalar w true resInt with
    | .ok (res, _) => .ok (.scalar res)
    | .error k => .error k)
  dsimp only [truncateScalar]
  let ⟨wrapped, h_w⟩ : ∃ x, bvToInt (bvOfInt 128 resInt) = x := ⟨_, rfl⟩
  rw [h_w]
  cases h_oob : (decide (wrapped < Neg.neg (HPow.hPow (2 : Int) 127)) ||
      decide (wrapped ≥ HPow.hPow (2 : Int) 127)) with
  | true =>
    cases w <;> (
      dsimp only [ScalarInt.truncateFromInt]
      rw [h_oob]
      rfl)
  | false =>
    have h : (match bind
        ((ScalarInt.truncateFromInt wrapped (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun x => pure x.1) with
      | .ok sc =>
        (Except.ok (Val.scalar ⟨w, true, sc.data⟩) : Except FaultKind Val)
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported) =
      (match (toMiriSize w).truncate (BitVec.ofInt 128 wrapped) with
      | .ok b =>
        match (toMiriSize w).signExtend b with
        | .ok _ => .ok (.scalar ⟨w, true, b⟩)
        | .error _ => .error .unsupported
      | .error _ => .error .unsupported) := by
      cases w <;> (
        dsimp only [ScalarInt.truncateFromInt]
        rw [h_oob]
        rfl)
    rw [h, bitVec_ofInt_eq, size_truncate_eq]
    dsimp only
    rw [size_signExtend_eq]
    rfl

theorem unary_truncate_unsigned_eq (w : IntWidth) (resInt : Int) :
    (match bind
        ((ScalarInt.truncateFromUInt
          (BitVec.ofInt 128 resInt) (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun x => pure x.1) with
    | .ok sc =>
      (Except.ok (Val.scalar ⟨w, false, sc.data⟩) : Except FaultKind Val)
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match truncateScalar w false resInt with
    | .ok (res, _) => .ok (.scalar res)
    | .error k => .error k) := by
  rw [bitVec_ofInt_eq]
  dsimp only [truncateScalar]
  let ⟨raw, h_raw⟩ : ∃ x, bvOfInt 128 resInt = x := ⟨_, rfl⟩
  rw [h_raw]
  have h : (match bind
      ((ScalarInt.truncateFromUInt raw (toMiriSize w)).mapError
        IntegerOpError.scalar)
      (fun x => pure x.1) with
    | .ok sc =>
      (Except.ok (Val.scalar ⟨w, false, sc.data⟩) : Except FaultKind Val)
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match (toMiriSize w).truncate raw with
    | .ok b => .ok (.scalar ⟨w, false, b⟩)
    | .error _ => .error .unsupported) := by
    cases w <;> rfl
  rw [h, size_truncate_eq]
  rfl

theorem unary_truncate_eq (w : IntWidth) (s : Bool) (resInt : Int) :
    (match bind
        (if (toMiriIntType w s).signed then
          let wrapped := (BitVec.ofInt 128 resInt).toInt
          (ScalarInt.truncateFromInt wrapped (toMiriIntType w s).size).mapError
            IntegerOpError.scalar
        else
          (ScalarInt.truncateFromUInt
            (BitVec.ofInt 128 resInt) (toMiriIntType w s).size).mapError
            IntegerOpError.scalar)
        (fun x => pure x.1) with
    | .ok sc =>
      (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match truncateScalar w s resInt with
    | .ok (res, _) => .ok (.scalar res)
    | .error k => .error k) := by
  rw [toMiriIntType_signed, toMiriIntType_size]
  cases s with
  | true => exact unary_truncate_signed_eq w resInt
  | false => exact unary_truncate_unsigned_eq w resInt

theorem evalRefUnOp_eq (op : UnOp) (v : Val) :
    evalRefUnOp op v = evalUnOp op v := by
  cases v with
  | bool b => cases op <;> rfl
  | unit | ptr _ | tuple _ | bytes _ => cases op <;> rfl
  | scalar sv =>
    cases sv with
    | mk w s bits =>
      cases op with
      | not =>
        dsimp only [evalRefUnOp, evalUnOp, toMiriUnOp, IntegerOps.unary]
        rw [integerOps_decode_eq]
        exact unary_truncate_eq w s (intNot (decodeScalar ⟨w, s, bits⟩))
      | neg =>
        dsimp only [evalRefUnOp, evalUnOp, toMiriUnOp, IntegerOps.unary]
        rw [integerOps_decode_eq]
        change (match
            (let k := fun (result : Int) =>
              bind
                (if (toMiriIntType w s).signed then
                  let wrapped := (BitVec.ofInt 128 result).toInt
                  (ScalarInt.truncateFromInt wrapped
                    (toMiriIntType w s).size).mapError IntegerOpError.scalar
                else
                  (ScalarInt.truncateFromUInt (BitVec.ofInt 128 result)
                    (toMiriIntType w s).size).mapError IntegerOpError.scalar)
                (fun x => pure x.1)
            if (toMiriIntType w s).signed then
              bind (pure (Neg.neg (decodeScalar ⟨w, s, bits⟩))) k
            else
              bind (throw (IntegerOpError.invalidUnaryOperator .Neg
                (toMiriIntType w s).signed)) k) with
          | .ok sc =>
            (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
          | .error (.undefinedBehavior _) => .error .undefined
          | .error _ => .error .unsupported) =
          if s then
            match truncateScalar w s (Neg.neg (decodeScalar ⟨w, s, bits⟩)) with
            | .ok (res, _) => .ok (.scalar res)
            | .error k => .error k
          else
            .error .unsupported
        let ⟨resInt, h_res⟩ : ∃ x, Neg.neg (decodeScalar ⟨w, s, bits⟩) = x :=
          ⟨_, rfl⟩
        rw [h_res, toMiriIntType_signed, toMiriIntType_size]
        cases s with
        | false => rfl
        | true => exact unary_truncate_signed_eq w resInt
      | ptrMetadata =>
        dsimp only [evalRefUnOp, evalUnOp, toMiriUnOp, IntegerOps.unary]
        rw [integerOps_decode_eq]
        rfl

theorem size_signedIntMin_eq (w : IntWidth) :
    (toMiriSize w).signedIntMin = .ok (signedMinInt w) := by
  cases w <;> rfl

theorem bvAnd_eq (x y : BitVec 128) : HAnd.hAnd x y = bvAnd x y := by
  apply BitVec.eq_of_toNat_eq
  dsimp only [bvAnd]
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (BitVec.and._proof_1 x y)).symm

theorem bvOr_eq (x y : BitVec 128) : HOr.hOr x y = bvOr x y := by
  apply BitVec.eq_of_toNat_eq
  dsimp only [bvOr]
  rw [BitVec.toNat_or, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (BitVec.or._proof_1 x y)).symm

theorem bvXor_eq (x y : BitVec 128) : HXor.hXor x y = bvXor x y := by
  apply BitVec.eq_of_toNat_eq
  dsimp only [bvXor]
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (BitVec.xor._proof_1 x y)).symm

theorem toMiriBinOp_isUnchecked (op : BinOp) :
    (toMiriBinOp op).isUnchecked = op.isUnchecked := by
  cases op <;> rfl

theorem shift_truncate_eq (op : BinOp) (w : IntWidth) (s rs : Bool)
    (resInt r : Int) (overflow : Bool) :
    (match bind
        (if (toMiriIntType w s).signed then
          let wrapped := (BitVec.ofInt 128 resInt).toInt
          (ScalarInt.truncateFromInt wrapped
            (toMiriIntType w s).size).mapError IntegerOpError.scalar
        else
          (ScalarInt.truncateFromUInt (BitVec.ofInt 128 resInt)
            (toMiriIntType w s).size).mapError IntegerOpError.scalar)
        (fun (value, _) =>
          if overflow && (toMiriBinOp op).isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.shiftOverflow (toMiriBinOp op) r rs))
          else
            pure (IntegerResult.scalar value)) with
    | .ok (.scalar sc) =>
      (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
    | .ok (.boolean b) => .ok (.bool b)
    | .ok _ => .error .unsupported
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match truncateScalar w s resInt with
    | .error k => .error k
    | .ok (res, _) =>
      if overflow && op.isUnchecked then
        .error .undefined
      else
        .ok (.scalar res)) := by
  rw [toMiriIntType_signed, toMiriIntType_size, bitVec_ofInt_eq,
      toMiriBinOp_isUnchecked]
  cases s with
  | true =>
    change (match bind
        ((ScalarInt.truncateFromInt (bvToInt (bvOfInt 128 resInt))
          (toMiriSize w)).mapError IntegerOpError.scalar)
        (fun (value, _) =>
          if overflow && op.isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.shiftOverflow (toMiriBinOp op) r rs))
          else
            pure (IntegerResult.scalar value)) with
      | .ok (.scalar sc) =>
        (Except.ok (Val.scalar ⟨w, true, sc.data⟩) : Except FaultKind Val)
      | .ok (.boolean b) => .ok (.bool b)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported) =
      (match truncateScalar w true resInt with
      | .error k => .error k
      | .ok (res, _) =>
        if overflow && op.isUnchecked then
          .error .undefined
        else
          .ok (.scalar res))
    dsimp only [truncateScalar]
    let ⟨wrapped, h_w⟩ : ∃ x, bvToInt (bvOfInt 128 resInt) = x := ⟨_, rfl⟩
    rw [h_w]
    cases h_oob : (decide (wrapped < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (wrapped ≥ HPow.hPow (2 : Int) 127)) with
    | true =>
      cases w <;> (
        dsimp only [ScalarInt.truncateFromInt]
        rw [h_oob]
        rfl)
    | false =>
      have h : (match bind
          ((ScalarInt.truncateFromInt wrapped (toMiriSize w)).mapError
            IntegerOpError.scalar)
          (fun (value, _) =>
            if overflow && op.isUnchecked then
              throw (IntegerOpError.undefinedBehavior
                (.shiftOverflow (toMiriBinOp op) r rs))
            else
              pure (IntegerResult.scalar value)) with
        | .ok (.scalar sc) =>
          (Except.ok (Val.scalar ⟨w, true, sc.data⟩) : Except FaultKind Val)
        | .ok (.boolean b) => .ok (.bool b)
        | .ok _ => .error .unsupported
        | .error (.undefinedBehavior _) => .error .undefined
        | .error _ => .error .unsupported) =
        (match (toMiriSize w).truncate (BitVec.ofInt 128 wrapped) with
        | .ok b =>
          match (toMiriSize w).signExtend b with
          | .ok _ =>
            if overflow && op.isUnchecked then
              .error .undefined
            else
              .ok (.scalar ⟨w, true, b⟩)
          | .error _ => .error .unsupported
        | .error _ => .error .unsupported) := by
        cases w <;> (
          dsimp only [ScalarInt.truncateFromInt]
          rw [h_oob]
          cases (overflow && op.isUnchecked) <;> rfl)
      rw [h, bitVec_ofInt_eq, size_truncate_eq]
      dsimp only
      rw [size_signExtend_eq]
      rfl
  | false =>
    change (match bind
        ((ScalarInt.truncateFromUInt (bvOfInt 128 resInt)
          (toMiriSize w)).mapError IntegerOpError.scalar)
        (fun (value, _) =>
          if overflow && op.isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.shiftOverflow (toMiriBinOp op) r rs))
          else
            pure (IntegerResult.scalar value)) with
      | .ok (.scalar sc) =>
        (Except.ok (Val.scalar ⟨w, false, sc.data⟩) : Except FaultKind Val)
      | .ok (.boolean b) => .ok (.bool b)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported) =
      (match truncateScalar w false resInt with
      | .error k => .error k
      | .ok (res, _) =>
        if overflow && op.isUnchecked then
          .error .undefined
        else
          .ok (.scalar res))
    dsimp only [truncateScalar]
    let ⟨raw, h_raw⟩ : ∃ x, bvOfInt 128 resInt = x := ⟨_, rfl⟩
    rw [h_raw]
    have h : (match bind
        ((ScalarInt.truncateFromUInt raw (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun (value, _) =>
          if overflow && op.isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.shiftOverflow (toMiriBinOp op) r rs))
          else
            pure (IntegerResult.scalar value)) with
      | .ok (.scalar sc) =>
        (Except.ok (Val.scalar ⟨w, false, sc.data⟩) : Except FaultKind Val)
      | .ok (.boolean b) => .ok (.bool b)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported) =
      (match (toMiriSize w).truncate raw with
      | .ok b =>
        if overflow && op.isUnchecked then
          .error .undefined
        else
          .ok (.scalar ⟨w, false, b⟩)
      | .error _ => .error .unsupported) := by
      cases w <;> cases (overflow && op.isUnchecked) <;> rfl
    rw [h, size_truncate_eq]
    rfl

theorem binary_truncate_scalarResult_eq (op : BinOp) (w : IntWidth) (s : Bool)
    (resInt : Int) (hostOverflow : Bool)
    (h_ovf : (toMiriBinOp op).isOverflowing = false) :
    (match bind
        (if (toMiriIntType w s).signed then
          let wrapped := (BitVec.ofInt 128 resInt).toInt
          (ScalarInt.truncateFromInt wrapped
            (toMiriIntType w s).size).mapError IntegerOpError.scalar
        else
          (ScalarInt.truncateFromUInt (BitVec.ofInt 128 resInt)
            (toMiriIntType w s).size).mapError IntegerOpError.scalar)
        (fun (value, lossy) =>
          if (hostOverflow || lossy) && (toMiriBinOp op).isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if (toMiriBinOp op).isOverflowing then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else
              IntegerResult.scalar value)) with
    | .ok (.scalar sc) =>
      (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
    | .ok (.boolean b) => .ok (.bool b)
    | .ok _ => .error .unsupported
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match truncateScalar w s resInt with
    | .error k => .error k
    | .ok (val, lossy) =>
      if (hostOverflow || lossy) && op.isUnchecked then
        .error .undefined
      else
        .ok (.scalar val)) := by
  rw [toMiriIntType_signed, toMiriIntType_size, bitVec_ofInt_eq, h_ovf,
      toMiriBinOp_isUnchecked]
  cases s with
  | true =>
    change (match bind
        ((ScalarInt.truncateFromInt (bvToInt (bvOfInt 128 resInt))
          (toMiriSize w)).mapError IntegerOpError.scalar)
        (fun (value, lossy) =>
          if (hostOverflow || lossy) && op.isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if false then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else
              IntegerResult.scalar value)) with
      | .ok (.scalar sc) =>
        (Except.ok (Val.scalar ⟨w, true, sc.data⟩) : Except FaultKind Val)
      | .ok (.boolean b) => .ok (.bool b)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported) =
      (match truncateScalar w true resInt with
      | .error k => .error k
      | .ok (val, lossy) =>
        if (hostOverflow || lossy) && op.isUnchecked then
          .error .undefined
        else
          .ok (.scalar val))
    dsimp only [truncateScalar]
    let ⟨wrapped, h_w⟩ : ∃ x, bvToInt (bvOfInt 128 resInt) = x := ⟨_, rfl⟩
    rw [h_w]
    cases h_oob : (decide (wrapped < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (wrapped ≥ HPow.hPow (2 : Int) 127)) with
    | true =>
      cases w <;> (
        dsimp only [ScalarInt.truncateFromInt]
        rw [h_oob]
        rfl)
    | false =>
      have h : (match bind
          ((ScalarInt.truncateFromInt wrapped (toMiriSize w)).mapError
            IntegerOpError.scalar)
          (fun (value, lossy) =>
            if (hostOverflow || lossy) && op.isUnchecked then
              throw (IntegerOpError.undefinedBehavior
                (.arithmeticOverflow (toMiriBinOp op)))
            else
              pure (if false then
                IntegerResult.withOverflow value (hostOverflow || lossy)
              else
                IntegerResult.scalar value)) with
        | .ok (.scalar sc) =>
          (Except.ok (Val.scalar ⟨w, true, sc.data⟩) : Except FaultKind Val)
        | .ok (.boolean b) => .ok (.bool b)
        | .ok _ => .error .unsupported
        | .error (.undefinedBehavior _) => .error .undefined
        | .error _ => .error .unsupported) =
        (match (toMiriSize w).truncate (BitVec.ofInt 128 wrapped) with
        | .ok b =>
          match (toMiriSize w).signExtend b with
          | .ok dec =>
            if (hostOverflow || (dec != wrapped)) && op.isUnchecked then
              .error .undefined
            else
              .ok (.scalar ⟨w, true, b⟩)
          | .error _ => .error .unsupported
        | .error _ => .error .unsupported) := by
        cases w <;> (
          dsimp only [ScalarInt.truncateFromInt]
          rw [h_oob]
          change (match (if ((hostOverflow || _) && op.isUnchecked) = true then
              Except.error (IntegerOpError.undefinedBehavior
                (.arithmeticOverflow (toMiriBinOp op)))
            else
              Except.ok (IntegerResult.scalar _)) with
            | .ok (.scalar sc) =>
              (Except.ok (Val.scalar ⟨_, true, sc.data⟩) : Except FaultKind Val)
            | .ok (.boolean b) => .ok (.bool b)
            | .ok _ => .error .unsupported
            | .error (.undefinedBehavior _) => .error .undefined
            | .error _ => .error .unsupported) =
            if ((hostOverflow || _) && op.isUnchecked) = true then
              Except.error FaultKind.undefined
            else
              Except.ok (Val.scalar ⟨_, true, _⟩)
          cases ((hostOverflow || _) && op.isUnchecked) <;> rfl)
      rw [h, bitVec_ofInt_eq, size_truncate_eq]
      dsimp only
      rw [size_signExtend_eq]
      rfl
  | false =>
    change (match bind
        ((ScalarInt.truncateFromUInt (bvOfInt 128 resInt)
          (toMiriSize w)).mapError IntegerOpError.scalar)
        (fun (value, lossy) =>
          if (hostOverflow || lossy) && op.isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if false then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else
              IntegerResult.scalar value)) with
      | .ok (.scalar sc) =>
        (Except.ok (Val.scalar ⟨w, false, sc.data⟩) : Except FaultKind Val)
      | .ok (.boolean b) => .ok (.bool b)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported) =
      (match truncateScalar w false resInt with
      | .error k => .error k
      | .ok (val, lossy) =>
        if (hostOverflow || lossy) && op.isUnchecked then
          .error .undefined
        else
          .ok (.scalar val))
    dsimp only [truncateScalar]
    let ⟨raw, h_raw⟩ : ∃ x, bvOfInt 128 resInt = x := ⟨_, rfl⟩
    rw [h_raw]
    have h : (match bind
        ((ScalarInt.truncateFromUInt raw (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun (value, lossy) =>
          if (hostOverflow || lossy) && op.isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if false then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else
              IntegerResult.scalar value)) with
      | .ok (.scalar sc) =>
        (Except.ok (Val.scalar ⟨w, false, sc.data⟩) : Except FaultKind Val)
      | .ok (.boolean b) => .ok (.bool b)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported) =
      (match (toMiriSize w).truncate raw with
      | .ok b =>
        if (hostOverflow || (b != raw)) && op.isUnchecked then
          .error .undefined
        else
          .ok (.scalar ⟨w, false, b⟩)
      | .error _ => .error .unsupported) := by
      cases w <;> (
        change (match (if ((hostOverflow || _) && op.isUnchecked) = true then
            Except.error (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            Except.ok (IntegerResult.scalar _)) with
          | .ok (.scalar sc) =>
            (Except.ok (Val.scalar ⟨_, false, sc.data⟩) : Except FaultKind Val)
          | .ok (.boolean b) => .ok (.bool b)
          | .ok _ => .error .unsupported
          | .error (.undefinedBehavior _) => .error .undefined
          | .error _ => .error .unsupported) =
          if ((hostOverflow || _) && op.isUnchecked) = true then
            Except.error FaultKind.undefined
          else
            Except.ok (Val.scalar ⟨_, false, _⟩)
        cases ((hostOverflow || _) && op.isUnchecked) <;> rfl)
    rw [h, size_truncate_eq]
    rfl

theorem toMiriIntType_bne_of_false {w₁ w₂ : IntWidth} {s₁ s₂ : Bool}
    (h : (IntWidth.beq w₁ w₂ && (s₁ == s₂)) = false) :
    (toMiriIntType w₁ s₁ != toMiriIntType w₂ s₂) = true := by
  cases w₁ <;> cases w₂ <;> cases s₁ <;> cases s₂ <;>
    first | rfl | nomatch h

theorem eq_of_intWidth_beq_and_signed {w₁ w₂ : IntWidth} {s₁ s₂ : Bool}
    (h : (IntWidth.beq w₁ w₂ && (s₁ == s₂)) = true) : w₁ = w₂ ∧ s₁ = s₂ := by
  cases w₁ <;> cases w₂ <;> cases s₁ <;> cases s₂ <;>
    first | exact ⟨rfl, rfl⟩ | nomatch h

theorem toMiriIntType_bne_self (w : IntWidth) (s : Bool) :
    (toMiriIntType w s != toMiriIntType w s) = false := by
  cases w <;> cases s <;> rfl

theorem bitwise_truncate_eq (w : IntWidth) (s : Bool) (bits : BitVec 128) :
    (match bind
        ((ScalarInt.truncateFromUInt bits (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun (value, _) => pure (IntegerResult.scalar value)) with
    | .ok (.scalar sc) =>
      (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
    | .ok (.boolean b) => .ok (.bool b)
    | .ok _ => .error .unsupported
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    .ok (.scalar ⟨w, s, truncateBits w bits⟩) := by
  have h : (match bind
      ((ScalarInt.truncateFromUInt bits (toMiriSize w)).mapError
        IntegerOpError.scalar)
      (fun (value, _) => pure (IntegerResult.scalar value)) with
    | .ok (.scalar sc) =>
      (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
    | .ok (.boolean b) => .ok (.bool b)
    | .ok _ => .error .unsupported
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match (toMiriSize w).truncate bits with
    | .ok b => .ok (.scalar ⟨w, s, b⟩)
    | .error _ => .error .unsupported) := by
    cases w <;> rfl
  rw [h, size_truncate_eq]

theorem evalShiftOp_eq (op : BinOp) (w₁ w₂ : IntWidth) (s₁ s₂ : Bool)
    (bits₁ bits₂ : BitVec 128) (h_sh : op.isShift = true) :
    evalRefBinOp op (.scalar ⟨w₁, s₁, bits₁⟩) (.scalar ⟨w₂, s₂, bits₂⟩) =
    evalBinOp op (.scalar ⟨w₁, s₁, bits₁⟩) (.scalar ⟨w₂, s₂, bits₂⟩) := by
  have proveShift (op' : BinOp) (resInt rInt : Int) (w : IntWidth) :
      (match bind
          (if (toMiriIntType w s₁).signed then
            let wrapped := (BitVec.ofInt 128 resInt).toInt
            (ScalarInt.truncateFromInt wrapped
              (toMiriIntType w s₁).size).mapError IntegerOpError.scalar
          else
            (ScalarInt.truncateFromUInt (BitVec.ofInt 128 resInt)
              (toMiriIntType w s₁).size).mapError IntegerOpError.scalar)
          (fun (value, _) =>
            if (intEmod rInt (Int.ofNat w.bitWidth) != rInt) &&
                (toMiriBinOp op').isUnchecked then
              throw (IntegerOpError.undefinedBehavior
                (.shiftOverflow (toMiriBinOp op') rInt
                  (toMiriIntType w₂ s₂).signed))
            else
              pure (IntegerResult.scalar value)) with
      | .ok (.scalar sc) =>
        (Except.ok (Val.scalar ⟨w, s₁, sc.data⟩) : Except FaultKind Val)
      | .ok (.boolean b) => .ok (.bool b)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported) =
      (match truncateScalar w s₁ resInt with
      | .error k => .error k
      | .ok (res, _) =>
        if (intEmod rInt (Int.ofNat w.bitWidth) != rInt) && op'.isUnchecked then
          .error .undefined
        else
          .ok (.scalar res)) :=
    shift_truncate_eq op' w s₁ (toMiriIntType w₂ s₂).signed resInt rInt _
  cases op with
  | shl =>
    dsimp only [evalRefBinOp, evalBinOp, evalShiftOp, toMiriBinOp,
      IntegerOps.binary]
    rw [integerOps_decode_eq, integerOps_decode_eq]
    let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x := ⟨_, rfl⟩
    let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₂, s₂, bits₂⟩ = x := ⟨_, rfl⟩
    rw [h_l, h_r]
    cases w₁ with
    | i8 =>
      exact proveShift .shl
        (intShiftLeft lInt (intEmod rInt 8).toNat) rInt .i8
    | i16 =>
      exact proveShift .shl
        (intShiftLeft lInt (intEmod rInt 16).toNat) rInt .i16
    | i32 =>
      exact proveShift .shl
        (intShiftLeft lInt (intEmod rInt 32).toNat) rInt .i32
    | i64 =>
      exact proveShift .shl
        (intShiftLeft lInt (intEmod rInt 64).toNat) rInt .i64
    | i128 =>
      exact proveShift .shl
        (intShiftLeft lInt (intEmod rInt 128).toNat) rInt .i128
    | isize =>
      exact proveShift .shl
        (intShiftLeft lInt (intEmod rInt 64).toNat) rInt .isize
  | shr =>
    dsimp only [evalRefBinOp, evalBinOp, evalShiftOp, toMiriBinOp,
      IntegerOps.binary]
    rw [integerOps_decode_eq, integerOps_decode_eq]
    let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x := ⟨_, rfl⟩
    let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₂, s₂, bits₂⟩ = x := ⟨_, rfl⟩
    rw [h_l, h_r]
    cases w₁ with
    | i8 =>
      exact proveShift .shr
        (intShiftRight lInt (intEmod rInt 8).toNat) rInt .i8
    | i16 =>
      exact proveShift .shr
        (intShiftRight lInt (intEmod rInt 16).toNat) rInt .i16
    | i32 =>
      exact proveShift .shr
        (intShiftRight lInt (intEmod rInt 32).toNat) rInt .i32
    | i64 =>
      exact proveShift .shr
        (intShiftRight lInt (intEmod rInt 64).toNat) rInt .i64
    | i128 =>
      exact proveShift .shr
        (intShiftRight lInt (intEmod rInt 128).toNat) rInt .i128
    | isize =>
      exact proveShift .shr
        (intShiftRight lInt (intEmod rInt 64).toNat) rInt .isize
  | shlUnchecked =>
    dsimp only [evalRefBinOp, evalBinOp, evalShiftOp, toMiriBinOp,
      IntegerOps.binary]
    rw [integerOps_decode_eq, integerOps_decode_eq]
    let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x := ⟨_, rfl⟩
    let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₂, s₂, bits₂⟩ = x := ⟨_, rfl⟩
    rw [h_l, h_r]
    cases w₁ with
    | i8 =>
      exact proveShift .shlUnchecked
        (intShiftLeft lInt (intEmod rInt 8).toNat) rInt .i8
    | i16 =>
      exact proveShift .shlUnchecked
        (intShiftLeft lInt (intEmod rInt 16).toNat) rInt .i16
    | i32 =>
      exact proveShift .shlUnchecked
        (intShiftLeft lInt (intEmod rInt 32).toNat) rInt .i32
    | i64 =>
      exact proveShift .shlUnchecked
        (intShiftLeft lInt (intEmod rInt 64).toNat) rInt .i64
    | i128 =>
      exact proveShift .shlUnchecked
        (intShiftLeft lInt (intEmod rInt 128).toNat) rInt .i128
    | isize =>
      exact proveShift .shlUnchecked
        (intShiftLeft lInt (intEmod rInt 64).toNat) rInt .isize
  | shrUnchecked =>
    dsimp only [evalRefBinOp, evalBinOp, evalShiftOp, toMiriBinOp,
      IntegerOps.binary]
    rw [integerOps_decode_eq, integerOps_decode_eq]
    let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x := ⟨_, rfl⟩
    let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₂, s₂, bits₂⟩ = x := ⟨_, rfl⟩
    rw [h_l, h_r]
    cases w₁ with
    | i8 =>
      exact proveShift .shrUnchecked
        (intShiftRight lInt (intEmod rInt 8).toNat) rInt .i8
    | i16 =>
      exact proveShift .shrUnchecked
        (intShiftRight lInt (intEmod rInt 16).toNat) rInt .i16
    | i32 =>
      exact proveShift .shrUnchecked
        (intShiftRight lInt (intEmod rInt 32).toNat) rInt .i32
    | i64 =>
      exact proveShift .shrUnchecked
        (intShiftRight lInt (intEmod rInt 64).toNat) rInt .i64
    | i128 =>
      exact proveShift .shrUnchecked
        (intShiftRight lInt (intEmod rInt 128).toNat) rInt .i128
    | isize =>
      exact proveShift .shrUnchecked
        (intShiftRight lInt (intEmod rInt 64).toNat) rInt .isize
  | _ => nomatch h_sh

theorem miriIntValue_type_bne_of_false (w₁ w₂ : IntWidth) (s₁ s₂ : Bool)
    (b₁ b₂ : BitVec 128) (h : (IntWidth.beq w₁ w₂ && (s₁ == s₂)) = false) :
    ((miriIntValue ⟨w₁, s₁, b₁⟩).type != (miriIntValue ⟨w₂, s₂, b₂⟩).type) =
      true :=
  toMiriIntType_bne_of_false h

theorem miriIntValue_type_bne_self (w : IntWidth) (s : Bool)
    (b₁ b₂ : BitVec 128) :
    ((miriIntValue ⟨w, s, b₁⟩).type != (miriIntValue ⟨w, s, b₂⟩).type) =
      false :=
  toMiriIntType_bne_self w s

theorem miriIntValue_toUInt (w : IntWidth) (s : Bool) (bits : BitVec 128) :
    (miriIntValue ⟨w, s, bits⟩).scalar.toUInt
      (miriIntValue ⟨w, s, bits⟩).type.size =
    .ok (truncateBits w bits) :=
  miriScalar_toUInt w bits

theorem arith_after_rw_eq (op : BinOp) (w : IntWidth) (s : Bool) (resInt : Int)
    (h_ovf : (toMiriBinOp op).isOverflowing = false) :
    (match (let hostOverflow := if s then
          decide (resInt < Neg.neg (HPow.hPow (2 : Int) 127)) ||
            decide (resInt ≥ HPow.hPow (2 : Int) 127)
        else
          decide (resInt < 0) || decide (resInt ≥ HPow.hPow (2 : Int) 128)
      bind (if s then
          let wrapped := (BitVec.ofInt 128 resInt).toInt
          (ScalarInt.truncateFromInt wrapped (toMiriSize w)).mapError
            IntegerOpError.scalar
        else
          (ScalarInt.truncateFromUInt (BitVec.ofInt 128 resInt)
            (toMiriSize w)).mapError IntegerOpError.scalar)
        (fun (value, lossy) =>
          if (hostOverflow || lossy) && (toMiriBinOp op).isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if (toMiriBinOp op).isOverflowing then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else
              IntegerResult.scalar value))) with
    | .ok (.scalar sc) =>
      (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
    | .ok (.boolean b) => .ok (.bool b)
    | .ok _ => .error .unsupported
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match truncateScalar w s resInt with
    | .error k => .error k
    | .ok (val, lossy) =>
      if ((if s then
            decide (resInt < Neg.neg (HPow.hPow (2 : Int) 127)) ||
              decide (resInt ≥ HPow.hPow (2 : Int) 127)
          else
            decide (resInt < 0) ||
              decide (resInt ≥ HPow.hPow (2 : Int) 128)) ||
          lossy) && op.isUnchecked then
        .error .undefined
      else
        .ok (.scalar val)) := by
  have h := binary_truncate_scalarResult_eq op w s resInt
    (if s then
      decide (resInt < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (resInt ≥ HPow.hPow (2 : Int) 127)
    else
      decide (resInt < 0) || decide (resInt ≥ HPow.hPow (2 : Int) 128)) h_ovf
  rw [toMiriIntType_signed, toMiriIntType_size] at h
  exact h

theorem int_tdiv_eq (a b : Int) : Int.tdiv a b = intTdiv a b := by
  cases a <;> cases b <;> rfl

theorem int_tmod_eq (a b : Int) : Int.tmod a b = intTmod a b := by
  cases a <;> cases b <;> rfl

theorem div_rem_signed_eq (op : BinOp) (w : IntWidth) (lInt rInt resInt : Int)
    (h_ovf : (toMiriBinOp op).isOverflowing = false) :
    (match
      (let jp := fun (_ : PUnit) =>
        let hostOverflow := if true then
            decide (resInt < Neg.neg (HPow.hPow (2 : Int) 127)) ||
              decide (resInt ≥ HPow.hPow (2 : Int) 127)
          else
            decide (resInt < 0) || decide (resInt ≥ HPow.hPow (2 : Int) 128)
        bind (if true then
            let wrapped := (BitVec.ofInt 128 resInt).toInt
            (ScalarInt.truncateFromInt wrapped (toMiriSize w)).mapError
              IntegerOpError.scalar
          else
            (ScalarInt.truncateFromUInt (BitVec.ofInt 128 resInt)
              (toMiriSize w)).mapError IntegerOpError.scalar)
          (fun (value, lossy) =>
            if (hostOverflow || lossy) && (toMiriBinOp op).isUnchecked then
              throw (IntegerOpError.undefinedBehavior
                (.arithmeticOverflow (toMiriBinOp op)))
            else
              pure (if (toMiriBinOp op).isOverflowing then
                IntegerResult.withOverflow value (hostOverflow || lossy)
              else
                IntegerResult.scalar value))
      if lInt == signedMinInt w && rInt == Neg.neg 1 then
        bind (throw (IntegerOpError.undefinedBehavior
          (if toMiriBinOp op == Miri.MIR.BinOp.Div then
            .divisionOverflow
          else
            .remainderOverflow))) jp
      else
        jp PUnit.unit) with
    | .ok (.scalar sc) =>
      (Except.ok (Val.scalar ⟨w, true, sc.data⟩) : Except FaultKind Val)
    | .ok (.boolean b) => .ok (.bool b)
    | .ok _ => .error .unsupported
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (if (false : Bool) then
      .error .undefined
    else if lInt == signedMinInt w && rInt == Neg.neg 1 then
      .error .undefined
    else
      match truncateScalar w true resInt with
      | .error k => .error k
      | .ok (val, lossy) =>
        if ((if true then
              decide (resInt < Neg.neg (HPow.hPow (2 : Int) 127)) ||
                decide (resInt ≥ HPow.hPow (2 : Int) 127)
            else
              decide (resInt < 0) ||
                decide (resInt ≥ HPow.hPow (2 : Int) 128)) ||
            lossy) && op.isUnchecked then
          .error .undefined
        else
          .ok (.scalar val)) := by
  cases (lInt == signedMinInt w && rInt == Neg.neg 1) with
  | true => rfl
  | false => exact arith_after_rw_eq op w true resInt h_ovf

theorem arith_full_eq (op : BinOp) (w : IntWidth) (s : Bool) (lInt rInt : Int)
    (h_op : (match op with
      | .add | .sub | .mul | .addUnchecked | .subUnchecked | .mulUnchecked
      | .div | .rem => true
      | _ => false) = true) :
    (match
      (let jp3 := fun (result : Int) =>
        let hostOverflow := if (toMiriIntType w s).signed then
            decide (result < Neg.neg (HPow.hPow (2 : Int) 127)) ||
              decide (result ≥ HPow.hPow (2 : Int) 127)
          else
            decide (result < 0) || decide (result ≥ HPow.hPow (2 : Int) 128)
        bind (if (toMiriIntType w s).signed then
            let wrapped := (BitVec.ofInt 128 result).toInt
            (ScalarInt.truncateFromInt wrapped
              (toMiriIntType w s).size).mapError IntegerOpError.scalar
          else
            (ScalarInt.truncateFromUInt (BitVec.ofInt 128 result)
              (toMiriIntType w s).size).mapError IntegerOpError.scalar)
          (fun (value, lossy) =>
            if (hostOverflow || lossy) && (toMiriBinOp op).isUnchecked then
              throw (IntegerOpError.undefinedBehavior
                (.arithmeticOverflow (toMiriBinOp op)))
            else
              pure (if (toMiriBinOp op).isOverflowing then
                IntegerResult.withOverflow value (hostOverflow || lossy)
              else
                IntegerResult.scalar value))
      let jp2 := fun (_ : PUnit) =>
        match toMiriBinOp op with
        | .Add | .AddUnchecked | .AddWithOverflow =>
          bind (pure (lInt + rInt)) jp3
        | .Sub | .SubUnchecked | .SubWithOverflow =>
          bind (pure (lInt - rInt)) jp3
        | .Mul | .MulUnchecked | .MulWithOverflow =>
          bind (pure (lInt * rInt)) jp3
        | .Div => bind (pure (Int.tdiv lInt rInt)) jp3
        | .Rem => bind (pure (Int.tmod lInt rInt)) jp3
        | _ =>
          bind (throw (IntegerOpError.invalidBinaryOperator (toMiriBinOp op)))
            jp3
      let jp1 := fun (_ : PUnit) =>
        if (toMiriIntType w s).signed &&
            (toMiriBinOp op == Miri.MIR.BinOp.Div ||
              toMiriBinOp op == Miri.MIR.BinOp.Rem) then
          bind (((toMiriIntType w s).size.signedIntMin).mapError
              (Function.comp IntegerOpError.scalar ScalarIntError.sizeError))
            (fun min =>
              if lInt == min && rInt == Neg.neg 1 then
                bind (throw (IntegerOpError.undefinedBehavior
                  (if toMiriBinOp op == Miri.MIR.BinOp.Div then
                    .divisionOverflow
                  else
                    .remainderOverflow))) jp2
              else
                jp2 PUnit.unit)
        else
          jp2 PUnit.unit
      if rInt == 0 then
        let jp0 := fun (_ : PUnit) =>
          if toMiriBinOp op == Miri.MIR.BinOp.Rem then
            bind (throw (IntegerOpError.undefinedBehavior .remainderByZero))
              jp1
          else
            jp1 PUnit.unit
        if toMiriBinOp op == Miri.MIR.BinOp.Div then
          bind (throw (IntegerOpError.undefinedBehavior .divisionByZero)) jp0
        else
          jp0 PUnit.unit
      else
        jp1 PUnit.unit) with
    | .ok (.scalar sc) =>
      (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
    | .ok (.boolean b) => .ok (.bool b)
    | .ok _ => .error .unsupported
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    evalArithOp op w s lInt rInt := by
  rw [toMiriIntType_signed, toMiriIntType_size, size_signedIntMin_eq,
      int_tdiv_eq, int_tmod_eq]
  cases op with
  | add =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .add w false (lInt + rInt) rfl
    | true => exact arith_after_rw_eq .add w true (lInt + rInt) rfl
  | sub =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .sub w false (lInt - rInt) rfl
    | true => exact arith_after_rw_eq .sub w true (lInt - rInt) rfl
  | mul =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .mul w false (lInt * rInt) rfl
    | true => exact arith_after_rw_eq .mul w true (lInt * rInt) rfl
  | addUnchecked =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .addUnchecked w false (lInt + rInt) rfl
    | true => exact arith_after_rw_eq .addUnchecked w true (lInt + rInt) rfl
  | subUnchecked =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .subUnchecked w false (lInt - rInt) rfl
    | true => exact arith_after_rw_eq .subUnchecked w true (lInt - rInt) rfl
  | mulUnchecked =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .mulUnchecked w false (lInt * rInt) rfl
    | true => exact arith_after_rw_eq .mulUnchecked w true (lInt * rInt) rfl
  | div =>
    dsimp only [evalArithOp]
    cases (rInt == 0) with
    | true => rfl
    | false =>
      cases s with
      | false => exact arith_after_rw_eq .div w false (intTdiv lInt rInt) rfl
      | true => exact div_rem_signed_eq .div w lInt rInt (intTdiv lInt rInt) rfl
  | rem =>
    dsimp only [evalArithOp]
    cases (rInt == 0) with
    | true => rfl
    | false =>
      cases s with
      | false => exact arith_after_rw_eq .rem w false (intTmod lInt rInt) rfl
      | true => exact div_rem_signed_eq .rem w lInt rInt (intTmod lInt rInt) rfl
  | _ => nomatch h_op

theorem evalArithOp_eq (op : BinOp) (w : IntWidth) (s : Bool)
    (bits₁ bits₂ : BitVec 128)
    (h_op : (match op with
      | .add | .sub | .mul | .addUnchecked | .subUnchecked | .mulUnchecked
      | .div | .rem => true
      | _ => false) = true) :
    evalRefBinOp op (.scalar ⟨w, s, bits₁⟩) (.scalar ⟨w, s, bits₂⟩) =
    evalArithOp op w s (decodeScalar ⟨w, s, bits₁⟩)
      (decodeScalar ⟨w, s, bits₂⟩) := by
  have h_full := arith_full_eq op w s
    (decodeScalar ⟨w, s, bits₁⟩) (decodeScalar ⟨w, s, bits₂⟩) h_op
  cases op with
  | add | sub | mul | addUnchecked | subUnchecked | mulUnchecked | div | rem =>
    dsimp only [evalRefBinOp, toMiriBinOp, IntegerOps.binary]
    rw [integerOps_decode_eq, integerOps_decode_eq]
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [miriIntValue_type_bne_self]
    exact h_full
  | _ => nomatch h_op

theorem evalRefBinOp_eq (op : BinOp) (lhs rhs : Val) :
    evalRefBinOp op lhs rhs = evalBinOp op lhs rhs := by
  cases lhs with
  | unit | ptr _ | tuple _ | bytes _ => cases rhs <;> rfl
  | bool l =>
    cases rhs with
    | unit | ptr _ | tuple _ | bytes _ | scalar _ => rfl
    | bool r => cases op <;> cases l <;> cases r <;> rfl
  | scalar l =>
    cases rhs with
    | unit | ptr _ | tuple _ | bytes _ | bool _ => rfl
    | scalar r =>
      cases l with
      | mk w₁ s₁ bits₁ =>
        cases r with
        | mk w₂ s₂ bits₂ =>
          cases h_sh : op.isShift with
          | true => exact evalShiftOp_eq op w₁ w₂ s₁ s₂ bits₁ bits₂ h_sh
          | false =>
            cases h_ty : (IntWidth.beq w₁ w₂ && (s₁ == s₂)) with
            | false =>
              have h_bne :=
                miriIntValue_type_bne_of_false w₁ w₂ s₁ s₂ bits₁ bits₂ h_ty
              cases op with
              | shl | shr | shlUnchecked | shrUnchecked => nomatch h_sh
              | _ =>
                dsimp only [evalRefBinOp, evalBinOp, toMiriBinOp,
                  IntegerOps.binary]
                rw [h_ty]
                first | rfl | (
                  rw [integerOps_decode_eq, integerOps_decode_eq]
                  let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x :=
                    ⟨_, rfl⟩
                  let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₂, s₂, bits₂⟩ = x :=
                    ⟨_, rfl⟩
                  rw [h_l, h_r]
                  dsimp only [bind, Except.bind, pure, Except.pure]
                  rw [h_bne]
                  rfl)
            | true =>
              let ⟨h_w, h_s⟩ := eq_of_intWidth_beq_and_signed h_ty
              subst h_w
              subst h_s
              have h_bne := miriIntValue_type_bne_self w₁ s₁ bits₁ bits₂
              cases op with
              | shl | shr | shlUnchecked | shrUnchecked => nomatch h_sh
              | addWithOverflow | subWithOverflow | mulWithOverflow | offset =>
                dsimp only [evalRefBinOp, evalBinOp]
                rw [h_ty]
                rfl
              | eq | ne | lt | le | gt | ge =>
                dsimp only [evalRefBinOp, evalBinOp, toMiriBinOp,
                  IntegerOps.binary]
                rw [h_ty, integerOps_decode_eq, integerOps_decode_eq]
                let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x :=
                  ⟨_, rfl⟩
                let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₂⟩ = x :=
                  ⟨_, rfl⟩
                rw [h_l, h_r]
                dsimp only [bind, Except.bind, pure, Except.pure]
                rw [h_bne]
                rfl
              | bitAnd =>
                dsimp only [evalRefBinOp, evalBinOp, toMiriBinOp,
                  IntegerOps.binary]
                rw [h_ty, integerOps_decode_eq, integerOps_decode_eq]
                let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x :=
                  ⟨_, rfl⟩
                let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₂⟩ = x :=
                  ⟨_, rfl⟩
                rw [h_l, h_r]
                dsimp only [bind, Except.bind, pure, Except.pure]
                rw [h_bne, miriIntValue_toUInt, miriIntValue_toUInt]
                dsimp only [Except.mapError, bind, Except.bind]
                rw [bvAnd_eq]
                exact bitwise_truncate_eq w₁ s₁ _
              | bitOr =>
                dsimp only [evalRefBinOp, evalBinOp, toMiriBinOp,
                  IntegerOps.binary]
                rw [h_ty, integerOps_decode_eq, integerOps_decode_eq]
                let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x :=
                  ⟨_, rfl⟩
                let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₂⟩ = x :=
                  ⟨_, rfl⟩
                rw [h_l, h_r]
                dsimp only [bind, Except.bind, pure, Except.pure]
                rw [h_bne, miriIntValue_toUInt, miriIntValue_toUInt]
                dsimp only [Except.mapError, bind, Except.bind]
                rw [bvOr_eq]
                exact bitwise_truncate_eq w₁ s₁ _
              | bitXor =>
                dsimp only [evalRefBinOp, evalBinOp, toMiriBinOp,
                  IntegerOps.binary]
                rw [h_ty, integerOps_decode_eq, integerOps_decode_eq]
                let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x :=
                  ⟨_, rfl⟩
                let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₂⟩ = x :=
                  ⟨_, rfl⟩
                rw [h_l, h_r]
                dsimp only [bind, Except.bind, pure, Except.pure]
                rw [h_bne, miriIntValue_toUInt, miriIntValue_toUInt]
                dsimp only [Except.mapError, bind, Except.bind]
                rw [bvXor_eq]
                exact bitwise_truncate_eq w₁ s₁ _
              | add =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .add w₁ s₁ bits₁ bits₂ rfl
              | sub =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .sub w₁ s₁ bits₁ bits₂ rfl
              | mul =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .mul w₁ s₁ bits₁ bits₂ rfl
              | addUnchecked =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .addUnchecked w₁ s₁ bits₁ bits₂ rfl
              | subUnchecked =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .subUnchecked w₁ s₁ bits₁ bits₂ rfl
              | mulUnchecked =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .mulUnchecked w₁ s₁ bits₁ bits₂ rfl
              | div =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .div w₁ s₁ bits₁ bits₂ rfl
              | rem =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .rem w₁ s₁ bits₁ bits₂ rfl

theorem tryFromUInt_eq_truncateFromUInt (value : U128) (size : Size) :
    ScalarInt.tryFromUInt value size =
    bind (ScalarInt.truncateFromUInt value size)
      (fun (result, overflow) =>
        if overflow then pure none else pure (some result)) := rfl

theorem match_truncateFromUInt_eq {α : Type} (w : IntWidth) (raw : BitVec 128)
    (f : BitVec 128 → Bool → α) (d : α) :
    (match ScalarInt.truncateFromUInt raw (toMiriSize w) with
    | .ok (sc, lossy) => f sc.data lossy
    | .error _ => d) =
    f (truncateBits w raw) (truncateBits w raw != raw) := by
  have h : (match ScalarInt.truncateFromUInt raw (toMiriSize w) with
    | .ok (sc, lossy) => f sc.data lossy
    | .error _ => d) =
    (match (toMiriSize w).truncate raw with
    | .ok b => f b (b != raw)
    | .error _ => d) := by
    cases w <;> rfl
  rw [h, size_truncate_eq]

theorem match_tryFromUInt_eq {α : Type} (w : IntWidth) (raw : BitVec 128)
    (onSome : BitVec 128 → α) (onNone : α) :
    (match ScalarInt.tryFromUInt raw (toMiriSize w) with
    | .ok (some sc) => onSome sc.data
    | _ => onNone) =
    if truncateBits w raw != raw then onNone
    else onSome (truncateBits w raw) := by
  have h : (match ScalarInt.tryFromUInt raw (toMiriSize w) with
    | .ok (some sc) => onSome sc.data
    | _ => onNone) =
    (match ScalarInt.truncateFromUInt raw (toMiriSize w) with
    | .ok (sc, lossy) => if lossy then onNone else onSome sc.data
    | .error _ => onNone) := by
    rw [tryFromUInt_eq_truncateFromUInt]
    cases ScalarInt.truncateFromUInt raw (toMiriSize w) with
    | error _ => rfl
    | ok pair =>
      let ⟨sc, lossy⟩ := pair
      cases lossy <;> rfl
  rw [h, match_truncateFromUInt_eq w raw
    (fun d lossy => if lossy then onNone else onSome d) onNone]

theorem match_bool_uint8_eq {α : Type} (v : UInt8)
    (onBool : Bool → α) (onInvalidBool onErr : α) :
    (match ((if v == 0 then pure false
        else if v == 1 then pure true
        else throw (ScalarIntError.invalidBool v)) :
        Except ScalarIntError Bool) with
    | .ok b => onBool b
    | .error (.invalidBool _) => onInvalidBool
    | .error _ => onErr) =
    (if v == 0 then onBool false
     else if v == 1 then onBool true
     else onInvalidBool) := by
  cases (v == 0) with
  | true => rfl
  | false => cases (v == 1) <;> rfl

theorem match_tryFromUInt_tryToBool_eq {α : Type} (raw : BitVec 128)
    (onBool : Bool → α) (onInvalidBool onErr : α) :
    (match ScalarInt.tryFromUInt raw (toMiriSize .i8) with
    | .ok (some sc) =>
      match sc.tryToBool with
      | .ok b => onBool b
      | .error (.invalidBool _) => onInvalidBool
      | .error _ => onErr
    | _ => onErr) =
    if truncateBits .i8 raw != raw then
      onErr
    else
      let v := UInt8.ofNat (truncateBits .i8 raw).toNat
      if v == 0 then onBool false
      else if v == 1 then onBool true
      else onInvalidBool := by
  have h1 : (match ScalarInt.tryFromUInt raw (toMiriSize .i8) with
    | .ok (some sc) =>
      match sc.tryToBool with
      | .ok b => onBool b
      | .error (.invalidBool _) => onInvalidBool
      | .error _ => onErr
    | _ => onErr) =
    (match ScalarInt.truncateFromUInt raw (toMiriSize .i8) with
    | .ok (sc, lossy) =>
      if lossy then onErr
      else
        match sc.tryToBool with
        | .ok b => onBool b
        | .error (.invalidBool _) => onInvalidBool
        | .error _ => onErr
    | .error _ => onErr) := by
    rw [tryFromUInt_eq_truncateFromUInt]
    cases ScalarInt.truncateFromUInt raw (toMiriSize .i8) with
    | error _ => rfl
    | ok pair =>
      let ⟨sc, lossy⟩ := pair
      cases lossy <;> rfl
  have h2 : (match ScalarInt.truncateFromUInt raw (toMiriSize .i8) with
    | .ok (sc, lossy) =>
      if lossy then onErr
      else
        match sc.tryToBool with
        | .ok b => onBool b
        | .error (.invalidBool _) => onInvalidBool
        | .error _ => onErr
    | .error _ => onErr) =
    (match ScalarInt.truncateFromUInt raw (toMiriSize .i8) with
    | .ok (sc, lossy) =>
      if lossy then onErr
      else
        match ((let v := UInt8.ofNat sc.data.toNat
          if v == 0 then pure false
          else if v == 1 then pure true
          else throw (ScalarIntError.invalidBool v)) :
          Except ScalarIntError Bool) with
        | .ok b => onBool b
        | .error (.invalidBool _) => onInvalidBool
        | .error _ => onErr
    | .error _ => onErr) := rfl
  rw [h1, h2,
      match_truncateFromUInt_eq .i8 raw
        (fun d lossy =>
          if lossy then onErr
          else
            match ((let v := UInt8.ofNat d.toNat
              if v == 0 then pure false
              else if v == 1 then pure true
              else throw (ScalarIntError.invalidBool v)) :
              Except ScalarIntError Bool) with
            | .ok b => onBool b
            | .error (.invalidBool _) => onInvalidBool
            | .error _ => onErr)
        onErr,
      match_bool_uint8_eq]

theorem evalRefConstLit_eq (ty : MirTy) (lit : ConstLit) :
    evalRefConstLit ty lit = evalConstLit ty lit := by
  cases ty with
  | unit | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases lit <;> rfl
  | int w s =>
    cases lit with
    | zeroSized => rfl
    | scalar bits =>
      dsimp only [evalRefConstLit, evalConstLit]
      exact @match_tryFromUInt_eq (Except FaultKind Val) w bits
        (fun d => .ok (.scalar ⟨w, s, d⟩)) (.error .unsupported)
  | bool =>
    cases lit with
    | zeroSized => rfl
    | scalar bits =>
      dsimp only [evalRefConstLit, evalConstLit]
      exact @match_tryFromUInt_tryToBool_eq (Except FaultKind Val) bits
        (fun b => .ok (.bool b)) (.error .undefined) (.error .unsupported)

theorem checkRefVal_int_aux (b : Bool) (vw w : IntWidth) (vs s : Bool) :
    (if (!b) = true then false else IntWidth.beq vw w && (vs == s)) =
    (match if b = true then some (MirTy.int vw vs) else none with
    | some vTy => MirTy.beq vTy (MirTy.int w s)
    | none => false) := by
  cases b <;> rfl

theorem checkRefVal_eq (v : Val) (ty : MirTy) :
    checkRefVal v ty = checkVal v ty := by
  cases v with
  | unit | ptr _ | tuple _ | bytes _ => cases ty <;> rfl
  | bool b => cases ty <;> cases b <;> rfl
  | scalar sv =>
    cases sv with
    | mk vw vs vbits =>
      cases ty with
      | bool | unit | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
        dsimp only [checkRefVal, checkVal, Val.ty?]
        cases (ScalarVal.wf ⟨vw, vs, vbits⟩) <;> rfl
      | int w s =>
        have h_m :
            (match ScalarInt.tryFromUInt vbits (toMiriSize vw) with
            | .ok (some _) => IntWidth.beq vw w && (vs == s)
            | _ => false) =
            if truncateBits vw vbits != vbits then false
            else IntWidth.beq vw w && (vs == s) :=
          @match_tryFromUInt_eq Bool vw vbits
            (fun _ => IntWidth.beq vw w && (vs == s)) false
        exact h_m.trans
          (checkRefVal_int_aux (truncateBits vw vbits == vbits) vw w vs s)

theorem checkRefArgsMatch_eq (vs : List Val) (tys : List MirTy) :
    checkRefArgsMatch vs tys = checkArgsMatch vs tys := by
  induction vs generalizing tys with
  | nil => cases tys <;> rfl
  | cons v rest ih =>
    cases tys with
    | nil => rfl
    | cons ty tys' =>
      dsimp only [checkRefArgsMatch, checkArgsMatch]
      rw [checkRefVal_eq, ih]

theorem evalRefSwitchBranches_eq (w : IntWidth) (discrBits : BitVec 128)
    (otherwise : BasicBlockId) (branches : List (BitVec 128 × BasicBlockId)) :
    evalRefSwitchBranches w discrBits otherwise branches =
    evalSwitchBranches w discrBits otherwise branches := by
  induction branches with
  | nil => rfl
  | cons hd tl ih =>
    let ⟨caseBits, target⟩ := hd
    have h1 : (match ScalarInt.tryFromUInt caseBits (toMiriSize w),
                     ScalarInt.truncateFromUInt discrBits (toMiriSize w) with
      | .ok (some caseSc), .ok (discrSc, _) =>
        if discrSc.data == caseSc.data then
          Except.ok target
        else
          evalRefSwitchBranches w discrBits otherwise tl
      | _, _ => Except.error FaultKind.unsupported) =
      (match ScalarInt.tryFromUInt caseBits (toMiriSize w) with
      | .ok (some caseSc) =>
        match ScalarInt.truncateFromUInt discrBits (toMiriSize w) with
        | .ok (discrSc, _) =>
          if discrSc.data == caseSc.data then
            Except.ok target
          else
            evalRefSwitchBranches w discrBits otherwise tl
        | .error _ => Except.error FaultKind.unsupported
      | _ => Except.error FaultKind.unsupported) := by
      cases ScalarInt.tryFromUInt caseBits (toMiriSize w) with
      | error _ => rfl
      | ok opt =>
        cases opt with
        | none => rfl
        | some _ =>
          cases ScalarInt.truncateFromUInt discrBits (toMiriSize w) <;> rfl
    have h_step :
        (match ScalarInt.tryFromUInt caseBits (toMiriSize w),
               ScalarInt.truncateFromUInt discrBits (toMiriSize w) with
        | .ok (some caseSc), .ok (discrSc, _) =>
          if discrSc.data == caseSc.data then
            Except.ok target
          else
            evalRefSwitchBranches w discrBits otherwise tl
        | _, _ => Except.error FaultKind.unsupported) =
        evalSwitchBranches w discrBits otherwise
          ((caseBits, target) :: tl) := by
      rw [h1,
          match_tryFromUInt_eq w caseBits
            (fun cb =>
              match ScalarInt.truncateFromUInt discrBits (toMiriSize w) with
              | .ok (discrSc, _) =>
                if discrSc.data == cb then
                  Except.ok target
                else
                  evalRefSwitchBranches w discrBits otherwise tl
              | .error _ => Except.error FaultKind.unsupported)
            (Except.error FaultKind.unsupported)]
      cases h_ov : (truncateBits w caseBits != caseBits) with
      | true =>
        change Except.error FaultKind.unsupported =
          if truncateBits w caseBits != caseBits then
            Except.error FaultKind.unsupported
          else if truncateBits w discrBits == truncateBits w caseBits then
            Except.ok target
          else
            evalSwitchBranches w discrBits otherwise tl
        rw [h_ov]
        rfl
      | false =>
        rw [match_truncateFromUInt_eq w discrBits
              (fun db _ =>
                if db == truncateBits w caseBits then
                  Except.ok target
                else
                  evalRefSwitchBranches w discrBits otherwise tl)
              (Except.error FaultKind.unsupported),
            ih]
        change (if truncateBits w discrBits == truncateBits w caseBits then
            Except.ok target
          else
            evalSwitchBranches w discrBits otherwise tl) =
          if truncateBits w caseBits != caseBits then
            Except.error FaultKind.unsupported
          else if truncateBits w discrBits == truncateBits w caseBits then
            Except.ok target
          else
            evalSwitchBranches w discrBits otherwise tl
        rw [h_ov]
        rfl
    exact h_step

theorem evalRefBoolSwitchBranches_eq (discr : Bool)
    (otherwise : BasicBlockId) (branches : List (BitVec 128 × BasicBlockId)) :
    evalRefBoolSwitchBranches discr otherwise branches =
    evalBoolSwitchBranches discr otherwise branches := by
  induction branches with
  | nil => rfl
  | cons hd tl ih =>
    let ⟨caseBits, target⟩ := hd
    dsimp only [evalRefBoolSwitchBranches, evalBoolSwitchBranches]
    rw [evalRefConstLit_eq, ih]
    rfl

end MiriEquiv

private theorem evalMiriMoveOperand_dead (ty : MirTy) :
    evalMiriMoveOperand .dead ty = none := by
  cases ty <;> rfl

private theorem evalMiriMoveOperand_live (optVal : Option Val) (ty : MirTy) :
    evalMiriMoveOperand (.live optVal) ty =
      some (optVal, liveUninitSlot ty) := by
  cases ty <;> rfl

theorem evalRefOperandToSlot_eq {ts bodyLocals : List MirTy}
    {slots : List LocalSlot}
    {rop : RefOperand} {op : Operand}
    (h_dec : decodeOperand ts rop = some op) :
    evalRefOperandToSlot ts (zipRefLocals bodyLocals slots) rop =
      mapSlotRes bodyLocals (evalOperandToSlot bodyLocals slots op) := by
  cases rop with
  | copy rp =>
    dsimp only [decodeOperand] at h_dec
    cases h_pl : decodePlace ts rp with
    | none => rw [h_pl] at h_dec; cases h_dec
    | some p =>
      rw [h_pl] at h_dec
      injection h_dec with h_op
      subst h_op
      let ⟨h_id, h_emp⟩ := decodePlace_inv h_pl
      dsimp only [evalRefOperandToSlot, evalOperandToSlot]
      rw [h_emp, h_id]
      cases p.projection.isEmpty
      · rfl
      · cases h_ty : MirSemantics.getElem? bodyLocals p.localId with
        | none =>
          rw [getElem?_zipRefLocals_none_left h_ty]
          rfl
        | some ty =>
          cases h_sl : MirSemantics.getElem? slots p.localId with
          | none =>
            rw [getElem?_zipRefLocals_none_right h_sl]
            rfl
          | some slot =>
            rw [getElem?_zipRefLocals_some h_ty h_sl]
            cases ty <;> cases slot <;> rfl
  | move rp =>
    dsimp only [decodeOperand] at h_dec
    cases h_pl : decodePlace ts rp with
    | none => rw [h_pl] at h_dec; cases h_dec
    | some p =>
      rw [h_pl] at h_dec
      injection h_dec with h_op
      subst h_op
      let ⟨h_id, h_emp⟩ := decodePlace_inv h_pl
      dsimp only [evalRefOperandToSlot, evalOperandToSlot]
      rw [h_emp, h_id]
      cases p.projection.isEmpty
      · rfl
      · cases h_ty : MirSemantics.getElem? bodyLocals p.localId with
        | none =>
          rw [getElem?_zipRefLocals_none_left h_ty]
          rfl
        | some ty =>
          cases h_sl : MirSemantics.getElem? slots p.localId with
          | none =>
            rw [getElem?_zipRefLocals_none_right h_sl]
            rfl
          | some slot =>
            rw [getElem?_zipRefLocals_some h_ty h_sl]
            cases slot with
            | dead =>
              dsimp only
              rw [evalMiriMoveOperand_dead]
              rfl
            | live optVal =>
              dsimp only
              rw [evalMiriMoveOperand_live]
              dsimp only
              cases h_set :
                  MirSemantics.setElem? slots p.localId (liveUninitSlot ty) with
              | none =>
                rw [setElem?_zipRefLocals_none h_set]
                rfl
              | some slots' =>
                rw [setElem?_zipRefLocals_some h_ty h_set]
                rfl
  | constant rc =>
    dsimp only [decodeOperand] at h_dec
    cases h_ty : MirSemantics.getElem? ts rc.ty with
    | none => rw [h_ty] at h_dec; cases h_dec
    | some ty =>
      rw [h_ty] at h_dec
      injection h_dec with h_op
      subst h_op
      dsimp only [evalRefOperandToSlot, evalOperandToSlot]
      rw [h_ty]
      dsimp only
      rw [evalRefConstLit_eq]
      cases evalConstLit ty rc.lit <;> rfl

theorem evalRefPrimitiveOperand_eq {ts bodyLocals : List MirTy}
    {slots : List LocalSlot}
    {rop : RefOperand} {op : Operand}
    (h_dec : decodeOperand ts rop = some op) :
    evalRefPrimitiveOperand ts (zipRefLocals bodyLocals slots) rop =
      mapValRes bodyLocals (evalPrimitiveOperand bodyLocals slots op) := by
  unfold evalRefPrimitiveOperand evalPrimitiveOperand
  rw [evalRefOperandToSlot_eq h_dec]
  cases evalOperandToSlot bodyLocals slots op with
  | error _ => rfl
  | ok res =>
    cases res with | mk ty _rest => cases _rest with | mk optVal slots' =>
    dsimp only [mapSlotRes]
    cases isPrimitiveReadableTy ty
    · rfl
    · cases optVal <;> rfl

private theorem evalRefRvalue_use (ts : List MirTy)
    (rlocals : List RefLocalState) (dstTy : MirTy) (rop : RefOperand) :
    evalRefRvalue ts rlocals dstTy (.use rop) =
      match evalRefOperandToSlot ts rlocals rop with
      | .error k => .error k
      | .ok (srcTy, optVal, rlocals₁) =>
        if !(MirTy.beq srcTy dstTy) then
          .error .unsupported
        else
          match optVal with
          | some v => .ok (v, rlocals₁)
          | none => .error .undefined := rfl

private theorem evalRefRvalue_binaryOp (ts : List MirTy)
    (rlocals : List RefLocalState) (dstTy : MirTy) (op : BinOp)
    (lhs rhs : RefOperand) :
    evalRefRvalue ts rlocals dstTy (.binaryOp op lhs rhs) =
      match evalRefPrimitiveOperand ts rlocals lhs with
      | .error k => .error k
      | .ok (lVal, rlocals₁) =>
        match evalRefPrimitiveOperand ts rlocals₁ rhs with
        | .error k => .error k
        | .ok (rVal, rlocals₂) =>
          match evalRefBinOp op lVal rVal with
          | .error k => .error k
          | .ok v => .ok (v, rlocals₂) := rfl

private theorem evalRefRvalue_unaryOp (ts : List MirTy)
    (rlocals : List RefLocalState) (dstTy : MirTy) (op : UnOp)
    (rop : RefOperand) :
    evalRefRvalue ts rlocals dstTy (.unaryOp op rop) =
      match evalRefPrimitiveOperand ts rlocals rop with
      | .error k => .error k
      | .ok (v, rlocals₁) =>
        match evalRefUnOp op v with
        | .error k => .error k
        | .ok u => .ok (u, rlocals₁) := rfl

theorem evalRefRvalue_eq {ts bodyLocals : List MirTy} {slots : List LocalSlot}
    {dstTy : MirTy} {rrv : RefRvalue} {rv : Rvalue}
    (h_dec : decodeRvalue ts rrv = some rv) :
    evalRefRvalue ts (zipRefLocals bodyLocals slots) dstTy rrv =
      mapValRes bodyLocals (evalRvalue bodyLocals slots dstTy rv) := by
  cases rrv with
  | use rop =>
    dsimp only [decodeRvalue] at h_dec
    cases h_op : decodeOperand ts rop with
    | none => rw [h_op] at h_dec; cases h_dec
    | some op =>
      rw [h_op] at h_dec
      injection h_dec with h_eq
      subst h_eq
      rw [evalRefRvalue_use]
      dsimp only [evalRvalue]
      rw [evalRefOperandToSlot_eq h_op]
      cases evalOperandToSlot bodyLocals slots op with
      | error _ => rfl
      | ok res =>
        let ⟨srcTy, optVal, slots₁⟩ := res
        dsimp only [mapSlotRes]
        cases MirTy.beq srcTy dstTy
        · rfl
        · cases optVal <;> rfl
  | binaryOp op lhs rhs =>
    dsimp only [decodeRvalue] at h_dec
    cases h_l : decodeOperand ts lhs with
    | none => rw [h_l] at h_dec; cases h_dec
    | some l' =>
      cases h_r : decodeOperand ts rhs with
      | none => rw [h_l, h_r] at h_dec; cases h_dec
      | some r' =>
        rw [h_l, h_r] at h_dec
        injection h_dec with h_eq
        subst h_eq
        rw [evalRefRvalue_binaryOp]
        dsimp only [evalRvalue]
        rw [evalRefPrimitiveOperand_eq h_l]
        cases evalPrimitiveOperand bodyLocals slots l' with
        | error _ => rfl
        | ok resL =>
          let ⟨lVal, slots₁⟩ := resL
          dsimp only [mapValRes]
          rw [evalRefPrimitiveOperand_eq h_r]
          cases evalPrimitiveOperand bodyLocals slots₁ r' with
          | error _ => rfl
          | ok resR =>
            let ⟨rVal, slots₂⟩ := resR
            dsimp only [mapValRes]
            rw [evalRefBinOp_eq]
            cases evalBinOp op lVal rVal <;> rfl
  | unaryOp op rop =>
    dsimp only [decodeRvalue] at h_dec
    cases h_op : decodeOperand ts rop with
    | none => rw [h_op] at h_dec; cases h_dec
    | some op' =>
      rw [h_op] at h_dec
      injection h_dec with h_eq
      subst h_eq
      rw [evalRefRvalue_unaryOp]
      dsimp only [evalRvalue]
      rw [evalRefPrimitiveOperand_eq h_op]
      cases evalPrimitiveOperand bodyLocals slots op' with
      | error _ => rfl
      | ok res =>
        let ⟨v, slots₁⟩ := res
        dsimp only [mapValRes]
        rw [evalRefUnOp_eq]
        cases evalUnOp op v <;> rfl
  | ref _ rp =>
    dsimp only [decodeRvalue] at h_dec
    cases h_p : decodePlace ts rp with
    | none => rw [h_p] at h_dec; cases h_dec
    | some _ => rw [h_p] at h_dec; injection h_dec with h_eq; subst h_eq; rfl
  | addressOf _ rp =>
    dsimp only [decodeRvalue] at h_dec
    cases h_p : decodePlace ts rp with
    | none => rw [h_p] at h_dec; cases h_dec
    | some _ => rw [h_p] at h_dec; injection h_dec with h_eq; subst h_eq; rfl
  | aggregateTuple rops =>
    dsimp only [decodeRvalue] at h_dec
    cases h_ops : decodeOperandList ts rops with
    | none => rw [h_ops] at h_dec; cases h_dec
    | some _ => rw [h_ops] at h_dec; injection h_dec with h_eq; subst h_eq; rfl
  | unsupported =>
    injection h_dec with h_eq
    subst h_eq
    rfl

theorem writeRefPlace_eq {bodyLocals : List MirTy} {slots : List LocalSlot}
    {dstLocalId : LocalId} {dstTy : MirTy} {val : Val}
    (h_ty : MirSemantics.getElem? bodyLocals dstLocalId = some dstTy) :
    writeRefPlace (zipRefLocals bodyLocals slots) dstLocalId dstTy val =
      mapSlotsRes bodyLocals (writePlace slots dstLocalId dstTy val) := by
  unfold writeRefPlace writePlace
  rw [checkRefVal_eq]
  cases checkVal val dstTy
  · rfl
  · cases h_sl : MirSemantics.getElem? slots dstLocalId with
    | none =>
      rw [getElem?_zipRefLocals_none_right h_sl]
      rfl
    | some slot =>
      rw [getElem?_zipRefLocals_some h_ty h_sl]
      cases slot with
      | dead => rfl
      | live _ =>
        dsimp only
        cases h_set :
            MirSemantics.setElem? slots dstLocalId (.live (some val)) with
        | none =>
          rw [setElem?_zipRefLocals_none h_set]
          rfl
        | some slots' =>
          rw [setElem?_zipRefLocals_some h_ty h_set]
          rfl

theorem getElem?_none_of_setElem?_none {α : Type} {xs : List α} {i : Nat}
    {v : α}
    (h : MirSemantics.setElem? xs i v = none) :
    MirSemantics.getElem? xs i = none := by
  induction xs generalizing i with
  | nil => rfl
  | cons x rest ih =>
    cases i with
    | zero => cases h
    | succ j =>
      dsimp only [MirSemantics.setElem?] at h
      cases h_r : MirSemantics.setElem? rest j v with
      | some _ => rw [h_r] at h; cases h
      | none => exact ih h_r

theorem getElem?_some_of_setElem?_some {α : Type} {xs xs' : List α} {i : Nat}
    {v : α}
    (h : MirSemantics.setElem? xs i v = some xs') :
    ∃ x : α, MirSemantics.getElem? xs i = some x := by
  induction xs generalizing xs' i with
  | nil => cases h
  | cons x rest ih =>
    cases i with
    | zero => exact ⟨x, rfl⟩
    | succ j =>
      dsimp only [MirSemantics.setElem?] at h
      cases h_r : MirSemantics.setElem? rest j v with
      | none => rw [h_r] at h; cases h
      | some _ => exact ih h_r

private theorem evalRefStatement_storageLive (ts : List MirTy)
    (rframe : RefFrameState) (callerMem : CallerMemory) (localId : LocalId) :
    evalRefStatement ts rframe callerMem (.storageLive localId) =
      match MirSemantics.getElem? rframe.locals localId with
      | some ⟨_, some localTy⟩ =>
        match MirSemantics.setElem? rframe.locals localId
            ⟨liveUninitSlot localTy, some localTy⟩ with
        | some rlocals' =>
          .step {
            frames := [{
              rframe with
              stmtIdx := rframe.stmtIdx + 1
              locals := rlocals'
            }]
            callerMem
          }
        | none => .fault .unsupported
      | _ => .fault .unsupported := rfl

private theorem evalRefStatement_storageDead_zero (ts : List MirTy)
    (rframe : RefFrameState) (callerMem : CallerMemory) (localId : LocalId)
    (h0 : Nat.beq localId 0 = true) :
    evalRefStatement ts rframe callerMem (.storageDead localId) =
      .fault .unsupported := by
  dsimp only [evalRefStatement, toMiriStatementForDispatch]
  rw [h0]
  rfl

private theorem evalRefStatement_storageDead_nonzero (ts : List MirTy)
    (rframe : RefFrameState) (callerMem : CallerMemory) (localId : LocalId)
    (h0 : Nat.beq localId 0 = false) :
    evalRefStatement ts rframe callerMem (.storageDead localId) =
      match MirSemantics.getElem? rframe.locals localId with
      | some ⟨_, some localTy⟩ =>
        match MirSemantics.setElem? rframe.locals localId
            ⟨.dead, some localTy⟩ with
        | some rlocals' =>
          .step {
            frames := [{
              rframe with
              stmtIdx := rframe.stmtIdx + 1
              locals := rlocals'
            }]
            callerMem
          }
        | none => .fault .unsupported
      | _ => .fault .unsupported := by
  dsimp only [evalRefStatement, toMiriStatementForDispatch]
  rw [h0]
  rfl

private theorem evalRefStatement_assign (ts : List MirTy)
    (rframe : RefFrameState) (callerMem : CallerMemory) (dst : RefPlace)
    (rvalue : RefRvalue) :
    evalRefStatement ts rframe callerMem (.assign dst rvalue) =
      if !dst.projection.isEmpty then
        .fault .unsupported
      else
        match MirSemantics.getElem? rframe.locals dst.localId with
        | none => .fault .unsupported
        | some ⟨_, none⟩ => .fault .unsupported
        | some ⟨_, some dstTy⟩ =>
          match evalRefRvalue ts rframe.locals dstTy rvalue with
          | .error k => .fault k
          | .ok (val, rlocalsAfterRval) =>
            match writeRefPlace rlocalsAfterRval dst.localId dstTy val with
            | .error k => .fault k
            | .ok rlocalsAfterWrite =>
              .step {
                frames := [{
                  rframe with
                  stmtIdx := rframe.stmtIdx + 1
                  locals := rlocalsAfterWrite
                }]
                callerMem
              } := rfl

theorem evalRefStatement_eq {ts : List MirTy} {body : Body} {f : FrameState}
    {callerMem : CallerMemory} {rstmt : RefStatementKind} {stmt : StatementKind}
    (h_len : f.locals.length = body.locals.length)
    (h_dec : decodeStmt ts rstmt = some stmt) :
    evalRefStatement ts (liftFrame body.locals f) callerMem rstmt =
      mapStepRes body.locals (evalStatement body f callerMem stmt) := by
  cases rstmt with
  | nop =>
    injection h_dec with h_eq
    subst h_eq
    rfl
  | storageLive localId =>
    injection h_dec with h_eq
    subst h_eq
    rw [evalRefStatement_storageLive]
    dsimp only [evalStatement, liftFrame]
    cases h_ty : MirSemantics.getElem? body.locals localId with
    | none =>
      rw [getElem?_zipRefLocals_none_left h_ty]
      rfl
    | some localTy =>
      let ⟨slot, h_sl⟩ := getElem?_some_of_length_eq h_len.symm h_ty
      rw [getElem?_zipRefLocals_some h_ty h_sl]
      dsimp only
      cases h_set :
          MirSemantics.setElem? f.locals localId (liveUninitSlot localTy) with
      | none =>
        rw [setElem?_zipRefLocals_none h_set]
        rfl
      | some locals' =>
        rw [setElem?_zipRefLocals_some h_ty h_set]
        rfl
  | storageDead localId =>
    injection h_dec with h_eq
    subst h_eq
    dsimp only [evalStatement]
    cases h0 : Nat.beq localId 0
    · rw [evalRefStatement_storageDead_nonzero _ _ _ _ h0]
      dsimp only [liftFrame]
      cases h_set : MirSemantics.setElem? f.locals localId .dead with
      | none =>
        have h_sl_none := getElem?_none_of_setElem?_none h_set
        rw [getElem?_zipRefLocals_none_right h_sl_none]
        rfl
      | some locals' =>
        let ⟨slot, h_sl⟩ := getElem?_some_of_setElem?_some h_set
        let ⟨localTy, h_ty⟩ := getElem?_some_of_length_eq h_len h_sl
        rw [getElem?_zipRefLocals_some h_ty h_sl]
        dsimp only
        rw [setElem?_zipRefLocals_some h_ty h_set]
        rfl
    · rw [evalRefStatement_storageDead_zero _ _ _ _ h0]
      rfl
  | assign rdst rrv =>
    dsimp only [decodeStmt] at h_dec
    cases h_pl : decodePlace ts rdst with
    | none => rw [h_pl] at h_dec; cases h_dec
    | some dst =>
      cases h_rv : decodeRvalue ts rrv with
      | none => rw [h_pl, h_rv] at h_dec; cases h_dec
      | some rv =>
        rw [h_pl, h_rv] at h_dec
        injection h_dec with h_eq
        subst h_eq
        let ⟨h_id, h_emp⟩ := decodePlace_inv h_pl
        rw [evalRefStatement_assign]
        dsimp only [evalStatement, liftFrame]
        rw [h_emp, h_id]
        cases dst.projection.isEmpty
        · rfl
        · cases h_ty : MirSemantics.getElem? body.locals dst.localId with
          | none =>
            rw [getElem?_zipRefLocals_none_left h_ty]
            rfl
          | some dstTy =>
            let ⟨slot, h_sl⟩ := getElem?_some_of_length_eq h_len.symm h_ty
            rw [getElem?_zipRefLocals_some h_ty h_sl]
            dsimp only
            rw [evalRefRvalue_eq h_rv]
            cases evalRvalue body.locals f.locals dstTy rv with
            | error _ => rfl
            | ok res =>
              cases res with | mk val localsAfterRval =>
              dsimp only [mapValRes]
              rw [writeRefPlace_eq h_ty]
              cases writePlace localsAfterRval dst.localId dstTy val <;> rfl
  | unsupported =>
    injection h_dec with h_eq
    subst h_eq
    rfl

private theorem evalRefTerminator_return_false (ts : List MirTy)
    (rbb : RefBasicBlock) (rframe : RefFrameState) (callerMem : CallerMemory)
    (h_rt : rbb.terminator = .return_) (h_cl : rbb.cleanup = false) :
    evalRefTerminator ts rbb rframe callerMem =
      match MirSemantics.getElem? rframe.locals 0 with
      | some ⟨.live (some retVal), some _⟩ =>
        .done (.returned ⟨retVal, callerMem⟩)
      | some ⟨.live none, some _⟩ | some ⟨.dead, some _⟩ =>
        .fault .undefined
      | _ => .fault .unsupported := by
  unfold evalRefTerminator
  rw [h_rt, h_cl]
  rfl

private theorem evalRefTerminator_return_true (ts : List MirTy)
    (rbb : RefBasicBlock) (rframe : RefFrameState) (callerMem : CallerMemory)
    (h_rt : rbb.terminator = .return_) (h_cl : rbb.cleanup = true) :
    evalRefTerminator ts rbb rframe callerMem = .fault .unsupported := by
  unfold evalRefTerminator
  rw [h_rt, h_cl]
  rfl

private theorem evalRefTerminator_switchInt (ts : List MirTy)
    (rbb : RefBasicBlock) (rframe : RefFrameState) (callerMem : CallerMemory)
    (rdiscr : RefOperand) (targets : SwitchTargets)
    (h_rt : rbb.terminator = .switchInt rdiscr targets) :
    evalRefTerminator ts rbb rframe callerMem =
      match evalRefPrimitiveOperand ts rframe.locals rdiscr with
      | .error k => .fault k
      | .ok (discrVal, rlocalsAfterDiscr) =>
        let targetRes : Except FaultKind BasicBlockId :=
          match discrVal with
          | .scalar sv =>
            evalRefSwitchBranches sv.width sv.bits targets.otherwise
              targets.branches
          | .bool b =>
            evalRefBoolSwitchBranches b targets.otherwise targets.branches
          | _ => .error .unsupported
        match targetRes with
        | .error k => .fault k
        | .ok target =>
          jumpToRefBlock { rframe with locals := rlocalsAfterDiscr }
            callerMem target := by
  unfold evalRefTerminator
  rw [h_rt]
  rfl

theorem evalRefTerminator_eq {ts : List MirTy} {body : Body}
    {rbb : RefBasicBlock}
    {bb : BasicBlock} {f : FrameState} {callerMem : CallerMemory}
    (h_len : f.locals.length = body.locals.length)
    (h_cleanup : rbb.cleanup = bb.cleanup)
    (h_term : decodeTerminator ts rbb.terminator = some bb.terminator) :
    evalRefTerminator ts rbb (liftFrame body.locals f) callerMem =
      mapStepRes body.locals (evalTerminator body bb f callerMem) := by
  cases h_rt : rbb.terminator with
  | goto target =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    unfold evalRefTerminator evalTerminator
    rw [h_rt, ← h_eq]
    rfl
  | switchInt rdiscr targets =>
    rw [h_rt] at h_term
    dsimp only [decodeTerminator] at h_term
    cases h_d : decodeOperand ts rdiscr with
    | none => rw [h_d] at h_term; cases h_term
    | some discr =>
      rw [h_d] at h_term
      injection h_term with h_eq
      rw [evalRefTerminator_switchInt _ _ _ _ _ _ h_rt]
      unfold evalTerminator
      rw [← h_eq]
      dsimp only [liftFrame]
      rw [evalRefPrimitiveOperand_eq h_d]
      cases evalPrimitiveOperand body.locals f.locals discr with
      | error _ => rfl
      | ok res =>
        cases res with | mk discrVal localsAfterDiscr =>
        dsimp only [mapValRes]
        cases discrVal with
        | scalar sv =>
          dsimp only
          rw [evalRefSwitchBranches_eq]
          cases evalSwitchBranches sv.width sv.bits targets.otherwise
            targets.branches <;> rfl
        | bool b =>
          dsimp only
          rw [evalRefBoolSwitchBranches_eq]
          cases evalBoolSwitchBranches b targets.otherwise
            targets.branches <;> rfl
        | unit | tuple _ | ptr _ | bytes _ => rfl
  | return_ =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    cases h_cl : bb.cleanup
    · rw [evalRefTerminator_return_false _ _ _ _ h_rt (h_cleanup.trans h_cl)]
      unfold evalTerminator
      rw [← h_eq, h_cl]
      dsimp only [liftFrame]
      cases h_sl : MirSemantics.getElem? f.locals 0 with
      | none =>
        rw [getElem?_zipRefLocals_none_right h_sl]
        rfl
      | some s =>
        let ⟨ty₀, h_ty⟩ := getElem?_some_of_length_eq h_len h_sl
        rw [getElem?_zipRefLocals_some h_ty h_sl]
        cases s with
        | dead => rfl
        | live o => cases o <;> rfl
    · rw [evalRefTerminator_return_true _ _ _ _ h_rt (h_cleanup.trans h_cl)]
      unfold evalTerminator
      rw [← h_eq, h_cl]
      rfl
  | unreachable =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    unfold evalRefTerminator evalTerminator
    rw [h_rt, ← h_eq]
    rfl
  | unwindResume =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    unfold evalRefTerminator evalTerminator
    rw [h_rt, ← h_eq]
    rfl
  | assert rcond exp msg t u =>
    rw [h_rt] at h_term
    dsimp only [decodeTerminator] at h_term
    cases h_c : decodeOperand ts rcond with
    | none => rw [h_c] at h_term; cases h_term
    | some c =>
      rw [h_c] at h_term
      injection h_term with h_eq
      unfold evalRefTerminator evalTerminator
      rw [h_rt, ← h_eq]
      rfl
  | call callee rargs rdst t u =>
    rw [h_rt] at h_term
    dsimp only [decodeTerminator] at h_term
    cases h_a : decodeOperandList ts rargs with
    | none => rw [h_a] at h_term; cases h_term
    | some args =>
      cases h_dst : decodePlace ts rdst with
      | none => rw [h_a, h_dst] at h_term; cases h_term
      | some dst =>
        rw [h_a, h_dst] at h_term
        injection h_term with h_eq
        unfold evalRefTerminator evalTerminator
        rw [h_rt, ← h_eq]
        rfl
  | unsupported =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    unfold evalRefTerminator evalTerminator
    rw [h_rt, ← h_eq]
    rfl

theorem evalStatement_step_inv {body : Body} {f : FrameState}
    {callerMem : CallerMemory} {stmt : StatementKind} {s' : State}
    (h_len : f.locals.length = body.locals.length)
    (h_step : evalStatement body f callerMem stmt = .step s') :
    ∃ f' : FrameState,
      s' = { frames := [f'], callerMem := callerMem } ∧
      f'.defId = f.defId ∧
      f'.locals.length = body.locals.length := by
  cases stmt with
  | nop =>
    injection h_step with h_eq
    refine ⟨{ f with stmtIdx := f.stmtIdx + 1 }, h_eq.symm, rfl, h_len⟩
  | storageLive localId =>
    dsimp only [evalStatement] at h_step
    cases h_ty : MirSemantics.getElem? body.locals localId with
    | none => rw [h_ty] at h_step; cases h_step
    | some localTy =>
      rw [h_ty] at h_step
      dsimp only at h_step
      cases h_set :
          MirSemantics.setElem? f.locals localId (liveUninitSlot localTy) with
      | none => rw [h_set] at h_step; cases h_step
      | some locals' =>
        rw [h_set] at h_step
        injection h_step with h_eq
        refine ⟨{ f with stmtIdx := f.stmtIdx + 1, locals := locals' },
          h_eq.symm, rfl,
          (setElem?_length h_set).trans h_len⟩
  | storageDead localId =>
    dsimp only [evalStatement] at h_step
    cases h0 : Nat.beq localId 0 <;> rw [h0] at h_step
    · cases h_set : MirSemantics.setElem? f.locals localId .dead with
      | none => rw [h_set] at h_step; cases h_step
      | some locals' =>
        rw [h_set] at h_step
        injection h_step with h_eq
        refine ⟨{ f with stmtIdx := f.stmtIdx + 1, locals := locals' },
          h_eq.symm, rfl,
          (setElem?_length h_set).trans h_len⟩
    · cases h_step
  | assign dst rvalue =>
    dsimp only [evalStatement] at h_step
    cases h_emp : dst.projection.isEmpty <;> rw [h_emp] at h_step
    · cases h_step
    · cases h_ty : MirSemantics.getElem? body.locals dst.localId with
      | none => rw [h_ty] at h_step; cases h_step
      | some dstTy =>
        rw [h_ty] at h_step
        dsimp only at h_step
        cases h_rv : evalRvalue body.locals f.locals dstTy rvalue with
        | error _ => rw [h_rv] at h_step; cases h_step
        | ok res =>
          rw [h_rv] at h_step
          cases res with | mk val localsAfterRval =>
          dsimp only at h_step
          cases h_wr : writePlace localsAfterRval dst.localId dstTy val with
          | error _ => rw [h_wr] at h_step; cases h_step
          | ok localsAfterWrite =>
            rw [h_wr] at h_step
            injection h_step with h_eq
            have h_len₁ := (evalRvalue_length h_rv).trans h_len
            have h_len₂ := (writePlace_length h_wr).trans h_len₁
            refine ⟨{ f with
                stmtIdx := f.stmtIdx + 1, locals := localsAfterWrite },
              h_eq.symm, rfl, h_len₂⟩
  | unsupported => cases h_step

theorem evalTerminator_step_inv {body : Body} {bb : BasicBlock}
    {f : FrameState} {callerMem : CallerMemory} {s' : State}
    (h_len : f.locals.length = body.locals.length)
    (h_step : evalTerminator body bb f callerMem = .step s') :
    ∃ f' : FrameState,
      s' = { frames := [f'], callerMem := callerMem } ∧
      f'.defId = f.defId ∧
      f'.locals.length = body.locals.length := by
  cases bb with | mk stmts term cleanup =>
  cases term with
  | goto target =>
    injection h_step with h_eq
    refine ⟨{ f with blockIdx := target, stmtIdx := 0 }, h_eq.symm, rfl, h_len⟩
  | return_ =>
    dsimp only [evalTerminator] at h_step
    cases cleanup
    · cases h_sl : MirSemantics.getElem? f.locals 0 with
      | none => rw [h_sl] at h_step; cases h_step
      | some s =>
        rw [h_sl] at h_step
        cases s with
        | dead => cases h_step
        | live o => cases o <;> cases h_step
    · cases h_step
  | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _
  | unsupported =>
    cases h_step
  | switchInt discr targets =>
    dsimp only [evalTerminator] at h_step
    cases h_d : evalPrimitiveOperand body.locals f.locals discr with
    | error _ => rw [h_d] at h_step; cases h_step
    | ok res =>
      rw [h_d] at h_step
      cases res with | mk discrVal localsAfterDiscr =>
      have h_len₁ := (evalPrimitiveOperand_length h_d).trans h_len
      dsimp only at h_step
      cases discrVal with
      | scalar sv =>
        dsimp only at h_step
        cases h_sw : evalSwitchBranches sv.width sv.bits targets.otherwise
            targets.branches <;>
          rw [h_sw] at h_step
        · cases h_step
        · injection h_step with h_eq
          refine ⟨_, h_eq.symm, rfl, h_len₁⟩
      | bool b =>
        dsimp only at h_step
        cases h_sw : evalBoolSwitchBranches b targets.otherwise
            targets.branches <;>
          rw [h_sw] at h_step
        · cases h_step
        · injection h_step with h_eq
          refine ⟨_, h_eq.symm, rfl, h_len₁⟩
      | unit | tuple _ | ptr _ | bytes _ => cases h_step

theorem decodeStmtList_length {ts : List MirTy} {rstmts : List RefStatementKind}
    {stmts : List StatementKind}
    (h : decodeStmtList ts rstmts = some stmts) :
    rstmts.length = stmts.length := by
  induction rstmts generalizing stmts with
  | nil =>
    injection h with h_eq
    subst h_eq
    rfl
  | cons rs rss ih =>
    dsimp only [decodeStmtList] at h
    cases h₁ : decodeStmt ts rs <;> cases h₂ : decodeStmtList ts rss <;>
      rw [h₁, h₂] at h <;> cases h
    simp only [List.length_cons, ih h₂]

theorem decodeStmtList_getElem? {ts : List MirTy}
    {rstmts : List RefStatementKind}
    {stmts : List StatementKind}
    (h : decodeStmtList ts rstmts = some stmts) (i : Nat) :
    (MirSemantics.getElem? stmts i = none →
      MirSemantics.getElem? rstmts i = none) ∧
    (∀ stmt, MirSemantics.getElem? stmts i = some stmt →
      ∃ rstmt, MirSemantics.getElem? rstmts i = some rstmt ∧
        decodeStmt ts rstmt = some stmt) := by
  induction rstmts generalizing stmts i with
  | nil =>
    injection h with h_eq
    subst h_eq
    refine ⟨fun _ => rfl, ?_⟩
    intro _ hs
    cases hs
  | cons rs rss ih =>
    dsimp only [decodeStmtList] at h
    cases h₁ : decodeStmt ts rs with
    | none => rw [h₁] at h; cases h
    | some s =>
      cases h₂ : decodeStmtList ts rss with
      | none => rw [h₁, h₂] at h; cases h
      | some ss =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        cases i with
        | zero =>
          refine ⟨?_, ?_⟩
          · intro hs; cases hs
          · intro stmt hs
            injection hs with h_eq
            subst h_eq
            exact ⟨rs, rfl, h₁⟩
        | succ j =>
          exact ih h₂ j

theorem decodeBasicBlock_inv {ts : List MirTy} {rbb : RefBasicBlock}
    {bb : BasicBlock}
    (h : decodeBasicBlock ts rbb = some bb) :
    decodeStmtList ts rbb.statements = some bb.statements ∧
    decodeTerminator ts rbb.terminator = some bb.terminator ∧
    rbb.cleanup = bb.cleanup := by
  unfold decodeBasicBlock at h
  cases h₁ : decodeStmtList ts rbb.statements with
  | none => rw [h₁] at h; cases h
  | some stmts =>
    cases h₂ : decodeTerminator ts rbb.terminator with
    | none => rw [h₁, h₂] at h; cases h
    | some term =>
      rw [h₁, h₂] at h
      injection h with h_eq
      rw [← h_eq]
      exact ⟨rfl, rfl, rfl⟩

theorem decodeBasicBlockList_getElem? {ts : List MirTy}
    {rbbs : List RefBasicBlock}
    {bbs : List BasicBlock}
    (h : decodeBasicBlockList ts rbbs = some bbs) (i : Nat) :
    (MirSemantics.getElem? bbs i = none → MirSemantics.getElem? rbbs i = none) ∧
    (∀ bb, MirSemantics.getElem? bbs i = some bb →
      ∃ rbb, MirSemantics.getElem? rbbs i = some rbb ∧
        decodeBasicBlock ts rbb = some bb) := by
  induction rbbs generalizing bbs i with
  | nil =>
    injection h with h_eq
    subst h_eq
    refine ⟨fun _ => rfl, ?_⟩
    intro _ hb
    cases hb
  | cons rbb rbbs' ih =>
    dsimp only [decodeBasicBlockList] at h
    cases h₁ : decodeBasicBlock ts rbb with
    | none => rw [h₁] at h; cases h
    | some bb₀ =>
      cases h₂ : decodeBasicBlockList ts rbbs' with
      | none => rw [h₁, h₂] at h; cases h
      | some bbs₀ =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        cases i with
        | zero =>
          refine ⟨?_, ?_⟩
          · intro hb; cases hb
          · intro bb hb
            injection hb with h_eq
            subst h_eq
            exact ⟨rbb, rfl, h₁⟩
        | succ j =>
          exact ih h₂ j

theorem decodeBody_inv {ts : List MirTy} {rbody : RefBody} {body : Body}
    (h : decodeBody ts rbody = some body) :
    rbody.argumentCount = body.argumentCount ∧
    decodeLocalTys ts rbody.locals = some body.locals ∧
    decodeBasicBlockList ts rbody.basicBlocks = some body.basicBlocks := by
  unfold decodeBody at h
  cases h₁ : decodeLocalTys ts rbody.locals with
  | none => rw [h₁] at h; cases h
  | some locals =>
    cases h₂ : decodeBasicBlockList ts rbody.basicBlocks with
    | none => rw [h₁, h₂] at h; cases h
    | some bbs =>
      rw [h₁, h₂] at h
      injection h with h_eq
      rw [← h_eq]
      exact ⟨rfl, rfl, rfl⟩

theorem decodeBodyList_getElem? {ts : List MirTy} {rbodies : List RefBody}
    {bodies : List Body}
    (h : decodeBodyList ts rbodies = some bodies) (i : Nat) :
    (MirSemantics.getElem? bodies i = none →
      MirSemantics.getElem? rbodies i = none) ∧
    (∀ body, MirSemantics.getElem? bodies i = some body →
      ∃ rbody, MirSemantics.getElem? rbodies i = some rbody ∧
        decodeBody ts rbody = some body) := by
  induction rbodies generalizing bodies i with
  | nil =>
    injection h with h_eq
    subst h_eq
    refine ⟨fun _ => rfl, ?_⟩
    intro _ hb
    cases hb
  | cons rb rbs ih =>
    dsimp only [decodeBodyList] at h
    cases h₁ : decodeBody ts rb with
    | none => rw [h₁] at h; cases h
    | some b₀ =>
      cases h₂ : decodeBodyList ts rbs with
      | none => rw [h₁, h₂] at h; cases h
      | some bs₀ =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        cases i with
        | zero =>
          refine ⟨?_, ?_⟩
          · intro hb; cases hb
          · intro body hb
            injection hb with h_eq
            subst h_eq
            exact ⟨rb, rfl, h₁⟩
        | succ j =>
          exact ih h₂ j

theorem decodeProg_inv {rp : RefProg} {p : Program}
    (h : decodeProg rp = some p) :
    rp.entryDefId = p.entryDefId ∧
    rp.pointerWidthBits = p.pointerWidthBits ∧
    rp.mirProfileVersion = p.mirProfileVersion ∧
    decodeBodyList rp.types rp.bodies = some p.bodies := by
  unfold decodeProg at h
  cases h_b : decodeBodyList rp.types rp.bodies with
  | none => rw [h_b] at h; cases h
  | some b' =>
    rw [h_b] at h
    injection h with h_eq
    rw [← h_eq]
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem evalStep_step_inv {p : Program} {c : Choice} {s s' : State}
    {f : FrameState} {body : Body}
    (hs : s.frames = [f])
    (h_body : MirSemantics.getElem? p.bodies f.defId = some body)
    (h_len : f.locals.length = body.locals.length)
    (h_step : evalStep p c s = .step s') :
    ∃ f' : FrameState,
      s' = { frames := [f'], callerMem := s.callerMem } ∧
      f'.defId = f.defId ∧
      f'.locals.length = body.locals.length := by
  unfold evalStep at h_step
  rw [hs] at h_step
  dsimp only at h_step
  rw [h_body] at h_step
  dsimp only at h_step
  cases h_bb : MirSemantics.getElem? body.basicBlocks f.blockIdx with
  | none => rw [h_bb] at h_step; cases h_step
  | some bb =>
    rw [h_bb] at h_step
    dsimp only at h_step
    cases h_st : MirSemantics.getElem? bb.statements f.stmtIdx <;>
      rw [h_st] at h_step
    · dsimp only at h_step
      cases h_end : Nat.beq f.stmtIdx bb.statements.length <;>
        rw [h_end] at h_step
      · cases h_step
      · exact evalTerminator_step_inv h_len h_step
    · exact evalStatement_step_inv h_len h_step

/-- One $M_{\text{ref}}$ step from a simulated state computes exactly the
lifted $M_{\text{anneal}}$ step, with the caller sentinel restored beneath the
top frame. -/
theorem evalRefStep_eq : EvalRefStepEqClaim := by
  intro rp p s rs f rf retTy body h_dec hs hrs hcm h_body h_len hrf h_lt c
  let ⟨_, _, _, h_bodies⟩ := decodeProg_inv h_dec
  let ⟨rbody, h_rbody_get, h_rbody_dec⟩ :=
    (decodeBodyList_getElem? h_bodies f.defId).2 body h_body
  let ⟨_, _, h_bbs_dec⟩ := decodeBody_inv h_rbody_dec
  unfold evalRefStep evalStep
  rw [h_lt, hrs, hs, hrf, hcm]
  dsimp only [liftFrame, callerSentinelFrame]
  rw [h_rbody_get, h_body]
  dsimp only
  cases h_bb : MirSemantics.getElem? body.basicBlocks f.blockIdx with
  | none =>
    rw [(decodeBasicBlockList_getElem? h_bbs_dec f.blockIdx).1 h_bb]
    rfl
  | some bb =>
    let ⟨rbb, h_rbb_get, h_rbb_dec⟩ :=
      (decodeBasicBlockList_getElem? h_bbs_dec f.blockIdx).2 bb h_bb
    let ⟨h_stmts_dec, h_term_dec, h_cleanup⟩ := decodeBasicBlock_inv h_rbb_dec
    rw [h_rbb_get]
    dsimp only
    cases h_st : MirSemantics.getElem? bb.statements f.stmtIdx with
    | none =>
      rw [(decodeStmtList_getElem? h_stmts_dec f.stmtIdx).1 h_st]
      rw [decodeStmtList_length h_stmts_dec]
      dsimp only
      cases Nat.beq f.stmtIdx bb.statements.length
      · rfl
      · exact congrArg
          (stepResultToRefOutcome (callerSentinelFrame retTy)
            rs.stepsExecuted rs.maxSteps)
          (evalRefTerminator_eq h_len h_cleanup h_term_dec)
    | some stmt =>
      let ⟨rstmt, h_rstmt_get, h_rstmt_dec⟩ :=
        (decodeStmtList_getElem? h_stmts_dec f.stmtIdx).2 stmt h_st
      rw [h_rstmt_get]
      dsimp only
      exact congrArg
        (stepResultToRefOutcome (callerSentinelFrame retTy)
          rs.stepsExecuted rs.maxSteps)
        (evalRefStatement_eq h_len h_rstmt_dec)

/-! ## Entry Initialization Simulation (`initRefState_sim`) -/

theorem decodeLocalTys_length {ts : List MirTy} {rlocals : List TyId}
    {locals : List MirTy}
    (h : decodeLocalTys ts rlocals = some locals) :
    rlocals.length = locals.length := by
  induction rlocals generalizing locals with
  | nil =>
    injection h with h_eq
    subst h_eq
    rfl
  | cons id ids ih =>
    dsimp only [decodeLocalTys] at h
    cases h₁ : MirSemantics.getElem? ts id with
    | none => rw [h₁] at h; cases h
    | some ty =>
      cases h₂ : decodeLocalTys ts ids with
      | none => rw [h₁, h₂] at h; cases h
      | some tys =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        simp only [List.length_cons, ih h₂]

theorem decodeBasicBlockList_isEmpty {ts : List MirTy}
    {rbbs : List RefBasicBlock}
    {bbs : List BasicBlock}
    (h : decodeBasicBlockList ts rbbs = some bbs) :
    rbbs.isEmpty = bbs.isEmpty := by
  cases rbbs with
  | nil =>
    injection h with h_eq
    subst h_eq
    rfl
  | cons rbb rbbs' =>
    dsimp only [decodeBasicBlockList] at h
    cases h₁ : decodeBasicBlock ts rbb with
    | none => rw [h₁] at h; cases h
    | some bb =>
      cases h₂ : decodeBasicBlockList ts rbbs' with
      | none => rw [h₁, h₂] at h; cases h
      | some bbs' =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        rfl

theorem refStmtHasStorageMarker_eq {ts : List MirTy} {localId : LocalId}
    {rstmt : RefStatementKind} {stmt : StatementKind}
    (h : decodeStmt ts rstmt = some stmt) :
    refStmtHasStorageMarker localId rstmt =
      stmtHasStorageMarker localId stmt := by
  cases rstmt with
  | storageLive id =>
    injection h with h_eq; subst h_eq; rfl
  | storageDead id =>
    injection h with h_eq; subst h_eq; rfl
  | nop =>
    injection h with h_eq; subst h_eq; rfl
  | unsupported =>
    injection h with h_eq; subst h_eq; rfl
  | assign rdst rrv =>
    dsimp only [decodeStmt] at h
    cases h₁ : decodePlace ts rdst with
    | none => rw [h₁] at h; cases h
    | some dst =>
      cases h₂ : decodeRvalue ts rrv with
      | none => rw [h₁, h₂] at h; cases h
      | some rv =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        rfl

theorem refStmtList_any_storageMarker_eq {ts : List MirTy} {localId : LocalId}
    {rstmts : List RefStatementKind} {stmts : List StatementKind}
    (h : decodeStmtList ts rstmts = some stmts) :
    rstmts.any (refStmtHasStorageMarker localId) =
      stmts.any (stmtHasStorageMarker localId) := by
  induction rstmts generalizing stmts with
  | nil =>
    injection h with h_eq; subst h_eq; rfl
  | cons rs rss ih =>
    dsimp only [decodeStmtList] at h
    cases h₁ : decodeStmt ts rs with
    | none => rw [h₁] at h; cases h
    | some s =>
      cases h₂ : decodeStmtList ts rss with
      | none => rw [h₁, h₂] at h; cases h
      | some ss =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        simp only [List.any_cons, refStmtHasStorageMarker_eq h₁, ih h₂]

theorem refBasicBlockList_any_storageMarker_eq {ts : List MirTy}
    {localId : LocalId}
    {rbbs : List RefBasicBlock} {bbs : List BasicBlock}
    (h : decodeBasicBlockList ts rbbs = some bbs) :
    rbbs.any (fun bb => bb.statements.any (refStmtHasStorageMarker localId)) =
      bbs.any (fun bb => bb.statements.any (stmtHasStorageMarker localId)) := by
  induction rbbs generalizing bbs with
  | nil =>
    injection h with h_eq; subst h_eq; rfl
  | cons rbb rbbs' ih =>
    dsimp only [decodeBasicBlockList] at h
    cases h₁ : decodeBasicBlock ts rbb with
    | none => rw [h₁] at h; cases h
    | some bb =>
      cases h₂ : decodeBasicBlockList ts rbbs' with
      | none => rw [h₁, h₂] at h; cases h
      | some bbs' =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        let ⟨h_stmts, _, _⟩ := decodeBasicBlock_inv h₁
        simp only [List.any_cons, refStmtList_any_storageMarker_eq h_stmts,
          ih h₂]

theorem refHasStorageAnnotation_eq {ts : List MirTy} {rbody : RefBody}
    {body : Body}
    (h : decodeBody ts rbody = some body) (localId : LocalId) :
    refHasStorageAnnotation rbody localId =
      hasStorageAnnotation body localId := by
  let ⟨_, _, h_bbs⟩ := decodeBody_inv h
  unfold refHasStorageAnnotation hasStorageAnnotation
  exact refBasicBlockList_any_storageMarker_eq h_bbs

noncomputable def refStmtInBounds (n : Nat) : RefStatementKind → Bool
  | .storageLive id | .storageDead id => Nat.blt id n
  | _ => true

noncomputable def stmtInBounds (n : Nat) : StatementKind → Bool
  | .storageLive id | .storageDead id => Nat.blt id n
  | _ => true

theorem refStmtInBounds_eq {ts : List MirTy} {n : Nat}
    {rstmt : RefStatementKind} {stmt : StatementKind}
    (h : decodeStmt ts rstmt = some stmt) :
    refStmtInBounds n rstmt = stmtInBounds n stmt := by
  cases rstmt with
  | storageLive id => injection h with h_eq; subst h_eq; rfl
  | storageDead id => injection h with h_eq; subst h_eq; rfl
  | nop => injection h with h_eq; subst h_eq; rfl
  | unsupported => injection h with h_eq; subst h_eq; rfl
  | assign rdst rrv =>
    dsimp only [decodeStmt] at h
    cases h₁ : decodePlace ts rdst with
    | none => rw [h₁] at h; cases h
    | some dst =>
      cases h₂ : decodeRvalue ts rrv with
      | none => rw [h₁, h₂] at h; cases h
      | some rv =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        rfl

theorem refStmtList_all_storageBounds_eq {ts : List MirTy} {n : Nat}
    {rstmts : List RefStatementKind} {stmts : List StatementKind}
    (h : decodeStmtList ts rstmts = some stmts) :
    rstmts.all (refStmtInBounds n) = stmts.all (stmtInBounds n) := by
  induction rstmts generalizing stmts with
  | nil => injection h with h_eq; subst h_eq; rfl
  | cons rs rss ih =>
    dsimp only [decodeStmtList] at h
    cases h₁ : decodeStmt ts rs with
    | none => rw [h₁] at h; cases h
    | some s =>
      cases h₂ : decodeStmtList ts rss with
      | none => rw [h₁, h₂] at h; cases h
      | some ss =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        simp only [List.all_cons, refStmtInBounds_eq h₁, ih h₂]

theorem refBasicBlockList_all_storageBounds_eq {ts : List MirTy} {n : Nat}
    {rbbs : List RefBasicBlock} {bbs : List BasicBlock}
    (h : decodeBasicBlockList ts rbbs = some bbs) :
    rbbs.all (fun bb => bb.statements.all (refStmtInBounds n)) =
      bbs.all (fun bb => bb.statements.all (stmtInBounds n)) := by
  induction rbbs generalizing bbs with
  | nil => injection h with h_eq; subst h_eq; rfl
  | cons rbb rbbs' ih =>
    dsimp only [decodeBasicBlockList] at h
    cases h₁ : decodeBasicBlock ts rbb with
    | none => rw [h₁] at h; cases h
    | some bb =>
      cases h₂ : decodeBasicBlockList ts rbbs' with
      | none => rw [h₁, h₂] at h; cases h
      | some bbs' =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        let ⟨h_stmts, _, _⟩ := decodeBasicBlock_inv h₁
        simp only [List.all_cons, refStmtList_all_storageBounds_eq h_stmts,
          ih h₂]

theorem refStorageAnnotationsInBounds_eq {ts : List MirTy} {rbody : RefBody}
    {body : Body}
    (h : decodeBody ts rbody = some body) :
    refStorageAnnotationsInBounds rbody = storageAnnotationsInBounds body := by
  let ⟨_, h_loc, h_bbs⟩ := decodeBody_inv h
  unfold refStorageAnnotationsInBounds storageAnnotationsInBounds
  rw [decodeLocalTys_length h_loc]
  exact refBasicBlockList_all_storageBounds_eq h_bbs

theorem initLocalsLoop_length (body : Body) (args : List Val) (idx : Nat)
    (tys : List MirTy) :
    (initLocalsLoop body args idx tys).length = tys.length := by
  induction tys generalizing idx with
  | nil => rfl
  | cons ty rest ih =>
    dsimp only [initLocalsLoop, List.length_cons]; rw [ih (idx + 1)]

theorem initRefLocalsLoop_eq {ts : List MirTy} {rbody : RefBody} {body : Body}
    (h : decodeBody ts rbody = some body) (args : List Val) (idx : Nat)
    (tys : List MirTy) :
    initRefLocalsLoop rbody args idx tys =
      zipRefLocals tys (initLocalsLoop body args idx tys) := by
  induction tys generalizing idx with
  | nil => rfl
  | cons ty rest ih =>
    let ⟨h_arg, _, _⟩ := decodeBody_inv h
    dsimp only [initRefLocalsLoop, initLocalsLoop, zipRefLocals]
    rw [h_arg, refHasStorageAnnotation_eq h idx, ih (idx + 1)]
    rfl

theorem getElem?_zero_of_blt {α : Type} {xs : List α} {n : Nat}
    (h : Nat.blt n xs.length = true) :
    ∃ x : α, MirSemantics.getElem? xs 0 = some x := by
  cases xs with
  | nil => cases h
  | cons x _ => exact ⟨x, rfl⟩

theorem initRefState_sim : InitRefStateSimClaim := by
  intro rp p q maxSteps h_dec
  let ⟨h_entry, h_width, h_prof, h_bodies⟩ := decodeProg_inv h_dec
  unfold initRefState initState
  rw [h_entry, h_width, h_prof]
  cases Nat.beq p.pointerWidthBits 64
  · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
    intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
  · -- Zeta-reduce the `let`s in both initializers; the remaining
    -- `if (!true) = true` guards reduce definitionally where needed.
    dsimp only
    cases Nat.beq p.mirProfileVersion 1
    · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
      intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
    · cases q.callerMem.allocations.isEmpty
      · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
        intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
      · cases h_b : MirSemantics.getElem? p.bodies p.entryDefId with
        | none =>
          rw [(decodeBodyList_getElem? h_bodies p.entryDefId).1 h_b]
          refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
          intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
        | some body =>
          let ⟨rbody, h_rb_get, h_rb_dec⟩ :=
            (decodeBodyList_getElem? h_bodies p.entryDefId).2 body h_b
          let ⟨h_arg, h_loc_dec, h_bbs_dec⟩ := decodeBody_inv h_rb_dec
          rw [h_rb_get]
          dsimp only
          rw [h_loc_dec]
          dsimp only
          rw [decodeBasicBlockList_isEmpty h_bbs_dec, h_arg,
            refStorageAnnotationsInBounds_eq h_rb_dec]
          cases body.basicBlocks.isEmpty
          · cases h_blt : Nat.blt body.argumentCount body.locals.length
            · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
              intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
            · cases storageAnnotationsInBounds body
              · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
                intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
              · cases body.locals.all isSupportedScalarOrUnitTy
                · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
                  intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
                · rw [checkRefArgsMatch_eq]
                  cases checkArgsMatch q.args
                      ((body.locals.drop 1).take body.argumentCount)
                  · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
                    intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
                  · let ⟨retTy, h_ret⟩ := getElem?_zero_of_blt h_blt
                    rw [h_ret]
                    dsimp only
                    refine ⟨?_, ?_⟩
                    · intro k hk; cases hk
                    · intro s₀ hs₀
                      injection hs₀ with h_s₀
                      subst h_s₀
                      rw [initRefLocalsLoop_eq h_rb_dec q.args 0 body.locals]
                      have h_entry_ret : entryRetTy? p = some retTy := by
                        dsimp only [entryRetTy?]
                        rw [h_b]
                        exact h_ret
                      refine ⟨_, rfl, ?_, rfl, rfl⟩
                      exact ⟨_, _, retTy, rfl, rfl, rfl, h_entry_ret, body, h_b,
                        initLocalsLoop_length body q.args 0 body.locals, rfl⟩
          · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
            intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl

/-! ## Multi-Step Reachability and `anneal_corresponds_to_miri` -/

/-- Backward simulation for one step: a running $M_{\text{ref}}$ transition
from a simulated state is matched by an $M_{\text{anneal}}$ transition that
re-establishes `SimulationInv`. -/
theorem sim_of_refStep : SimOfRefStepClaim := by
  intro rp p s rs rs' h_dec h_sim h_rstep
  let ⟨f, rf, retTy, hs, hrs, hcm, hret, body, hbody, hlen, hrf⟩ := h_sim
  let ⟨c, hc, h_eval⟩ := h_rstep
  cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
  | false =>
    unfold evalRefStep at h_eval
    rw [h_lt] at h_eval
    cases h_eval
  | true =>
    rw [evalRefStep_eq h_dec hs hrs hcm hbody hlen hrf h_lt c] at h_eval
    cases h_es : evalStep p c s with
    | done out =>
      rw [h_es] at h_eval
      cases h_eval
    | fault k =>
      rw [h_es] at h_eval
      cases k <;> cases h_eval
    | step s₁ =>
      let ⟨f₁, hs₁, hdef₁, hlen₁⟩ := evalStep_step_inv hs hbody hlen h_es
      subst hs₁
      rw [h_es] at h_eval
      dsimp only [mapStepRes, stepResultToRefOutcome] at h_eval
      injection h_eval with h_rs'
      subst h_rs'
      have hbody₁ : MirSemantics.getElem? p.bodies f₁.defId = some body := by
        rw [hdef₁]; exact hbody
      exact ⟨_, ⟨c, hc, h_es⟩, f₁, liftFrame body.locals f₁, retTy, rfl, rfl,
        rfl, hret, body, hbody₁, hlen₁, rfl⟩

/-- Backward simulation: every $M_{\text{ref}}$ state reachable from a
simulated state is simulated by a reachable $M_{\text{anneal}}$ state. -/
theorem sim_of_refReaches : SimOfRefReachesClaim := by
  intro rp p s₀ rs₀ rs h_dec h_sim₀ h_reach
  induction h_reach with
  | refl => exact ⟨s₀, Reaches.refl s₀, h_sim₀⟩
  | tail _ h_rstep ih =>
    let ⟨s₂, h_reach₂, h_sim₂⟩ := ih
    let ⟨s₃, h_step, h_sim₃⟩ := sim_of_refStep h_dec h_sim₂ h_rstep
    exact ⟨s₃, Reaches.tail h_reach₂ h_step, h_sim₃⟩

/-- Step-indexed reachability in $M_{\text{anneal}}$: `s₂` is reached from `s₁`
in exactly `n` transitions. -/
inductive ReachesN (p : Program) (s₁ : State) : Nat → State → Prop where
  | refl : ReachesN p s₁ 0 s₁
  | tail {n : Nat} {s₂ s₃ : State} :
      ReachesN p s₁ n s₂ →
      Step p s₂ (.step s₃) →
      ReachesN p s₁ (n + 1) s₃

/-- Step-indexed reachability in $M_{\text{ref}}$: `rs₂` is reached from `rs₁`
in exactly `n` `.running` transitions. -/
inductive RefReachesN (rp : RefProg) (rs₁ : RefState) :
    Nat → RefState → Prop where
  | refl : RefReachesN rp rs₁ 0 rs₁
  | tail {n : Nat} {rs₂ rs₃ : RefState} :
      RefReachesN rp rs₁ n rs₂ →
      RefStep rp rs₂ (.running rs₃) →
      RefReachesN rp rs₁ (n + 1) rs₃

theorem exists_reachesN_of_reaches {p : Program} {s₁ s₂ : State}
    (h : Reaches p s₁ s₂) :
    ∃ n : Nat, ReachesN p s₁ n s₂ := by
  induction h with
  | refl => exact ⟨0, ReachesN.refl⟩
  | tail _ h_step ih =>
    let ⟨n, h_in⟩ := ih
    exact ⟨n + 1, ReachesN.tail h_in h_step⟩

theorem refReaches_of_refReachesN {rp : RefProg} {rs₁ rs₂ : RefState}
    {n : Nat} (h : RefReachesN rp rs₁ n rs₂) :
    RefReaches rp rs₁ rs₂ := by
  induction h with
  | refl => exact RefReaches.refl rs₁
  | tail _ h_step ih => exact RefReaches.tail ih h_step

theorem nat_blt_eq_true_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

/-- Forward simulation for one step: while the step budget is not exhausted,
an $M_{\text{anneal}}$ transition from a simulated state is matched by one
running $M_{\text{ref}}$ transition that re-establishes `SimulationInv`. -/
theorem refStep_of_step {rp : RefProg} {p : Program} {s s' : State}
    {rs : RefState}
    (h_dec : decodeProg rp = some p)
    (h_sim : SimulationInv p s rs)
    (h_step : Step p s (.step s'))
    (h_lt : Nat.blt rs.stepsExecuted rs.maxSteps = true) :
    ∃ rs' : RefState,
      RefStep rp rs (.running rs') ∧
      SimulationInv p s' rs' ∧
      rs'.stepsExecuted = rs.stepsExecuted + 1 ∧
      rs'.maxSteps = rs.maxSteps := by
  let ⟨f, rf, retTy, hs, hrs, hcm, hret, body, hbody, hlen, hrf⟩ := h_sim
  let ⟨c, hc, h_es⟩ := h_step
  have h_ref_eq := evalRefStep_eq h_dec hs hrs hcm hbody hlen hrf h_lt c
  let ⟨f', hs', hdef', hlen'⟩ := evalStep_step_inv hs hbody hlen h_es
  rw [h_es, hs'] at h_ref_eq
  dsimp only [mapStepRes, stepResultToRefOutcome] at h_ref_eq
  let rs' : RefState := {
    frames := [callerSentinelFrame retTy, liftFrame body.locals f']
    callerMem := s.callerMem
    stepsExecuted := rs.stepsExecuted + 1
    maxSteps := rs.maxSteps
  }
  have h_rstep : RefStep rp rs (.running rs') := ⟨c, hc, h_ref_eq⟩
  have hbody' : MirSemantics.getElem? p.bodies f'.defId = some body := by
    rw [hdef']; exact hbody
  refine ⟨rs', h_rstep, ?_, rfl, rfl⟩
  rw [hs']
  exact ⟨f', liftFrame body.locals f', retTy, rfl, rfl, rfl, hret, body,
    hbody', hlen', rfl⟩

/-- Step-indexed forward simulation: an `n`-step $M_{\text{anneal}}$ execution
from a simulated state is matched by an `n`-step $M_{\text{ref}}$ execution
whenever the reference step budget leaves room for `n` more steps. -/
theorem refReachesN_of_reachesN {rp : RefProg} {p : Program} {n : Nat}
    {s₁ s₂ : State} {rs₁ : RefState}
    (h_dec : decodeProg rp = some p)
    (h_in : ReachesN p s₁ n s₂)
    (h_sim₁ : SimulationInv p s₁ rs₁)
    (h_budget : rs₁.stepsExecuted + n ≤ rs₁.maxSteps) :
    ∃ rs₂ : RefState,
      RefReachesN rp rs₁ n rs₂ ∧
      SimulationInv p s₂ rs₂ ∧
      rs₂.stepsExecuted = rs₁.stepsExecuted + n ∧
      rs₂.maxSteps = rs₁.maxSteps := by
  induction h_in with
  | refl =>
    exact ⟨rs₁, RefReachesN.refl, h_sim₁, (Nat.add_zero _).symm, rfl⟩
  | @tail m s_mid s_next h_prev h_step ih =>
    have h_b₁ : rs₁.stepsExecuted + m ≤ rs₁.maxSteps :=
      Nat.le_of_succ_le h_budget
    let ⟨rs₂, h_rreach, h_sim₂, h_steps₂, h_max₂⟩ := ih h_b₁
    have h_lt : Nat.blt rs₂.stepsExecuted rs₂.maxSteps = true := by
      apply nat_blt_eq_true_of_lt
      rw [h_steps₂, h_max₂]
      exact h_budget
    let ⟨rs₃, h_rstep, h_sim₃, h_steps₃, h_max₃⟩ :=
      refStep_of_step h_dec h_sim₂ h_step h_lt
    refine ⟨rs₃, RefReachesN.tail h_rreach h_rstep, h_sim₃, ?_, ?_⟩
    · rw [h_steps₃, h_steps₂]
      rfl
    · rw [h_max₃, h_max₂]

/-- UB transfer: if `(p, q)` is well-formed in $M_{\text{anneal}}$, then
`encodeProg p` neither reaches `.ub` nor `.blocked` in $M_{\text{ref}}$ under
any step budget `maxSteps : Nat`. -/
theorem refWellFormed_of_wellFormed : RefWellFormedOfWellFormedClaim := by
  intro p q h_wf
  have h_dec : decodeProg (encodeProg p) = some p := decodeProg_encodeProg p
  let ⟨⟨s₀, h_init, _⟩, h_no_fault⟩ := h_wf
  intro maxSteps
  let ⟨rs₀, h_rinit, h_sim₀, _, _⟩ :=
    (initRefState_sim maxSteps h_dec).2 s₀ h_init
  refine ⟨⟨rs₀, h_rinit, fun _ _ => ⟨0, rfl⟩⟩, ?_, ?_⟩
  · intro h_ub
    unfold RefReachesOutcome at h_ub
    rw [h_rinit] at h_ub
    let ⟨rs, h_rreach, c, hc, h_reval⟩ := h_ub
    let ⟨s, h_reach, h_sim⟩ := sim_of_refReaches h_dec h_sim₀ h_rreach
    let ⟨f, rf, _, hs, hrs, hcm, _, body, hbody, hlen, hrf⟩ := h_sim
    cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
    | false =>
      unfold evalRefStep at h_reval
      rw [h_lt] at h_reval
      cases h_reval
    | true =>
      rw [evalRefStep_eq h_dec hs hrs hcm hbody hlen hrf h_lt c] at h_reval
      cases h_es : evalStep p c s with
      | step s' =>
        let ⟨_, hs', _, _⟩ := evalStep_step_inv hs hbody hlen h_es
        rw [h_es, hs'] at h_reval
        cases h_reval
      | done out =>
        rw [h_es] at h_reval
        cases h_reval
      | fault k =>
        rw [h_es] at h_reval
        cases k with
        | unsupported => cases h_reval
        | undefined =>
          apply h_no_fault .undefined
          unfold ReachesResult
          rw [h_init]
          exact ⟨s, h_reach, c, hc, h_es⟩
  · intro h_blk
    unfold RefReachesOutcome at h_blk
    rw [h_rinit] at h_blk
    let ⟨rs, h_rreach, c, hc, h_reval⟩ := h_blk
    let ⟨s, h_reach, h_sim⟩ := sim_of_refReaches h_dec h_sim₀ h_rreach
    let ⟨f, rf, _, hs, hrs, hcm, _, body, hbody, hlen, hrf⟩ := h_sim
    cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
    | false =>
      unfold evalRefStep at h_reval
      rw [h_lt] at h_reval
      cases h_reval
    | true =>
      rw [evalRefStep_eq h_dec hs hrs hcm hbody hlen hrf h_lt c] at h_reval
      cases h_es : evalStep p c s with
      | step s' =>
        let ⟨_, hs', _, _⟩ := evalStep_step_inv hs hbody hlen h_es
        rw [h_es, hs'] at h_reval
        cases h_reval
      | done out =>
        rw [h_es] at h_reval
        cases h_reval
      | fault k =>
        rw [h_es] at h_reval
        cases k with
        | undefined => cases h_reval
        | unsupported =>
          apply h_no_fault .unsupported
          unfold ReachesResult
          rw [h_init]
          exact ⟨s, h_reach, c, hc, h_es⟩

/-- Forward behavior transfer: every terminal behavior of `(p, q)` in
$M_{\text{anneal}}$ is a reference behavior of `encodeProg p` (witnessed by
step budget `n + 1` for an `n`-step execution). -/
theorem refBehavior_of_behavior : RefBehaviorOfBehaviorClaim := by
  intro p q out h_beh
  have h_dec : decodeProg (encodeProg p) = some p := decodeProg_encodeProg p
  unfold Behavior ReachesResult at h_beh
  cases h_init : initState p q with
  | error k =>
    rw [h_init] at h_beh
    cases h_beh
  | ok s₀ =>
    rw [h_init] at h_beh
    let ⟨s_end, h_reach, c, hc, h_es⟩ := h_beh
    let ⟨n, h_in⟩ := exists_reachesN_of_reaches h_reach
    let ⟨rs₀, h_rinit, h_sim₀, h_steps₀, h_max₀⟩ :=
      (initRefState_sim (n + 1) h_dec).2 s₀ h_init
    have h_budget : rs₀.stepsExecuted + n ≤ rs₀.maxSteps := by
      rw [h_steps₀, h_max₀, Nat.zero_add]
      exact Nat.le_succ n
    let ⟨rs_end, h_rreach, h_sim_end, h_steps_end, h_max_end⟩ :=
      refReachesN_of_reachesN h_dec h_in h_sim₀ h_budget
    let ⟨f, rf, _, hs, hrs, hcm, _, body, hbody, hlen, hrf⟩ := h_sim_end
    have h_lt : Nat.blt rs_end.stepsExecuted rs_end.maxSteps = true := by
      apply nat_blt_eq_true_of_lt
      rw [h_steps_end, h_steps₀, Nat.zero_add, h_max_end, h_max₀]
      exact Nat.lt_succ_self n
    have h_reval := evalRefStep_eq h_dec hs hrs hcm hbody hlen hrf h_lt c
    rw [h_es] at h_reval
    refine ⟨n + 1, ?_⟩
    unfold RefReachesOutcome
    rw [h_rinit]
    exact ⟨rs_end, refReaches_of_refReachesN h_rreach, c, hc, h_reval⟩

/-- Backward behavior transfer: every reference behavior of `encodeProg p` is
a terminal behavior of `(p, q)` in $M_{\text{anneal}}$, so $M_{\text{ref}}$
has no outcomes that $M_{\text{anneal}}$ omits. -/
theorem behavior_of_refBehavior : BehaviorOfRefBehaviorClaim := by
  intro p q out h_ref
  have h_dec : decodeProg (encodeProg p) = some p := decodeProg_encodeProg p
  let ⟨maxSteps, h_out⟩ := h_ref
  unfold RefReachesOutcome at h_out
  unfold Behavior ReachesResult
  cases h_init : initState p q with
  | error k =>
    rw [(initRefState_sim maxSteps h_dec).1 k h_init] at h_out
    cases k <;> cases h_out
  | ok s₀ =>
    let ⟨rs₀, h_rinit, h_sim₀, _, _⟩ :=
      (initRefState_sim maxSteps h_dec).2 s₀ h_init
    rw [h_rinit] at h_out
    let ⟨rs, h_rreach, c, hc, h_reval⟩ := h_out
    let ⟨s, h_reach, h_sim⟩ := sim_of_refReaches h_dec h_sim₀ h_rreach
    let ⟨f, rf, _, hs, hrs, hcm, _, body, hbody, hlen, hrf⟩ := h_sim
    cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
    | false =>
      unfold evalRefStep at h_reval
      rw [h_lt] at h_reval
      cases h_reval
    | true =>
      rw [evalRefStep_eq h_dec hs hrs hcm hbody hlen hrf h_lt c] at h_reval
      cases h_es : evalStep p c s with
      | step s' =>
        let ⟨_, hs', _, _⟩ := evalStep_step_inv hs hbody hlen h_es
        rw [h_es, hs'] at h_reval
        cases h_reval
      | fault k =>
        rw [h_es] at h_reval
        cases k <;> cases h_reval
      | done out' =>
        rw [h_es] at h_reval
        dsimp only [mapStepRes, stepResultToRefOutcome] at h_reval
        injection h_reval with h_out_eq
        subst h_out_eq
        exact ⟨s, h_reach, c, hc, h_es⟩

/-- Terminal behaviors coincide exactly in $M_{\text{anneal}}$ and
$M_{\text{ref}}$. -/
theorem behavior_iff_refBehavior : BehaviorIffRefBehaviorClaim :=
  fun p q out =>
    ⟨refBehavior_of_behavior p q out, behavior_of_refBehavior p q out⟩

/-- Total state-lifting function from $M_{\text{anneal}}$ to $M_{\text{ref}}$
at step counters `(0, 0)`. -/
noncomputable def liftState (p : Program) (s : State) : RefState :=
  match s.frames, entryRetTy? p with
  | [f], some retTy =>
    match MirSemantics.getElem? p.bodies f.defId with
    | some body =>
      { frames := [callerSentinelFrame retTy, liftFrame body.locals f]
        callerMem := s.callerMem
        stepsExecuted := 0
        maxSteps := 0 }
    | none =>
      { frames := []
        callerMem := s.callerMem
        stepsExecuted := 0
        maxSteps := 0 }
  | _, _ =>
    { frames := []
      callerMem := s.callerMem
      stepsExecuted := 0
      maxSteps := 0 }

/-- Total state-projection function from $M_{\text{ref}}$ to
$M_{\text{anneal}}$. -/
noncomputable def projectState (rs : RefState) : State :=
  match rs.frames with
  | [_, rf] =>
    { frames := [{
        defId := rf.defId
        blockIdx := rf.blockIdx
        stmtIdx := rf.stmtIdx
        locals := unzipRefSlots rf.locals
      }]
      callerMem := rs.callerMem }
  | _ =>
    { frames := [], callerMem := rs.callerMem }

theorem simulationInv_with_counters {p : Program} {s : State} {rs : RefState}
    (steps max : Nat) (h : SimulationInv p s rs) :
    SimulationInv p s { rs with stepsExecuted := steps, maxSteps := max } := by
  let ⟨f, rf, retTy, hs, hrs, hcm, hret, hframe⟩ := h
  exact ⟨f, rf, retTy, hs, hrs, hcm, hret, hframe⟩

theorem simulationInv_of_with_counters {p : Program} {s : State} {rs : RefState}
    {steps max : Nat}
    (h : SimulationInv p s
      { rs with stepsExecuted := steps, maxSteps := max }) :
    SimulationInv p s rs := by
  let ⟨f, rf, retTy, hs, hrs, hcm, hret, hframe⟩ := h
  exact ⟨f, rf, retTy, hs, hrs, hcm, hret, hframe⟩

theorem liftState_sim_of_sim {p : Program} {s : State} {rs : RefState}
    (h : SimulationInv p s rs) :
    SimulationInv p s (liftState p s) := by
  let ⟨f, rf, retTy, hs, _, _, hret, body, hbody, hlen, _⟩ := h
  unfold liftState
  rw [hs, hret]
  dsimp only
  rw [hbody]
  exact ⟨f, liftFrame body.locals f, retTy, hs, rfl, rfl, hret, body, hbody,
    hlen, rfl⟩

theorem liftState_steps (p : Program) (s : State) :
    (liftState p s).stepsExecuted = 0 ∧ (liftState p s).maxSteps = 0 := by
  unfold liftState
  cases s.frames with
  | nil => exact ⟨rfl, rfl⟩
  | cons f fs =>
    cases fs with
    | cons _ _ => exact ⟨rfl, rfl⟩
    | nil =>
      cases entryRetTy? p with
      | none => exact ⟨rfl, rfl⟩
      | some _ =>
        dsimp only
        cases MirSemantics.getElem? p.bodies f.defId <;> exact ⟨rfl, rfl⟩

theorem liftState_eq_of_sim {p : Program} {s : State} {rs : RefState}
    (h : SimulationInv p s rs) :
    { liftState p s with
      stepsExecuted := rs.stepsExecuted
      maxSteps := rs.maxSteps } = rs :=
  refState_unique_of_simulationInv
    (simulationInv_with_counters rs.stepsExecuted rs.maxSteps
      (liftState_sim_of_sim h))
    h rfl rfl

theorem projectState_sim_of_sim {p : Program} {s : State} {rs : RefState}
    (h : SimulationInv p s rs) :
    projectState rs = s := by
  let ⟨f, rf, retTy, hs, hrs, hcm, _, body, _, hlen, hrf⟩ := h
  unfold projectState
  rw [hrs, hrf]
  dsimp only [liftFrame]
  rw [unzipRefSlots_zipRefLocals hlen, hcm]
  cases f
  cases s with | mk frames callerMem =>
  dsimp only at hs
  dsimp only
  rw [hs]

/-- Divergence coincides exactly in $M_{\text{anneal}}$ and $M_{\text{ref}}$:
`(p, q)` has an infinite execution trace in $M_{\text{anneal}}$ if and only if
`encodeProg p` has an infinite running execution trace in $M_{\text{ref}}$. -/
theorem diverges_iff_refDiverges : DivergesIffRefDivergesClaim := by
  intro p q
  have h_dec : decodeProg (encodeProg p) = some p := decodeProg_encodeProg p
  constructor
  · intro h_div
    let ⟨s₀, h_init, trace, h_t0, h_step⟩ := h_div
    let ⟨rs₀, h_rinit, h_sim₀, h_steps₀, h_max₀⟩ :=
      (initRefState_sim 0 h_dec).2 s₀ h_init
    have h_inv : ∀ n : Nat, SimulationInv p (trace n) (liftState p (trace n)) :=
      fun n => by
        induction n with
        | zero =>
          rw [h_t0]
          exact liftState_sim_of_sim h_sim₀
        | succ m ih =>
          have h_sim_m := simulationInv_with_counters m (m + 1) ih
          have h_lt : Nat.blt m (m + 1) = true :=
            nat_blt_eq_true_of_lt (Nat.lt_succ_self m)
          let ⟨_, _, h_sim', _, _⟩ :=
            refStep_of_step h_dec h_sim_m (h_step m) h_lt
          exact liftState_sim_of_sim h_sim'
    refine ⟨rs₀, h_rinit, fun n => liftState p (trace n), ?_, ?_⟩
    · dsimp only
      rw [h_t0]
      exact refState_unique_of_simulationInv (liftState_sim_of_sim h_sim₀)
        h_sim₀ ((liftState_steps p s₀).1.trans h_steps₀.symm)
        ((liftState_steps p s₀).2.trans h_max₀.symm)
    · intro n
      dsimp only
      have h_sim_n := simulationInv_with_counters n (n + 1) (h_inv n)
      have h_lt : Nat.blt n (n + 1) = true :=
        nat_blt_eq_true_of_lt (Nat.lt_succ_self n)
      let ⟨rs', h_rstep, h_sim', h_steps', h_max'⟩ :=
        refStep_of_step h_dec h_sim_n (h_step n) h_lt
      have h_eq := liftState_eq_of_sim h_sim'
      rw [h_steps', h_max'] at h_eq
      rw [h_eq]
      exact h_rstep
  · intro h_rdiv
    let ⟨rs₀, h_rinit, rtrace, h_rt0, h_rstep⟩ := h_rdiv
    cases h_init : initState p q with
    | error k =>
      rw [(initRefState_sim 0 h_dec).1 k h_init] at h_rinit
      cases h_rinit
    | ok s₀ =>
      let ⟨rs₀', h_rinit', h_sim₀, _, _⟩ :=
        (initRefState_sim 0 h_dec).2 s₀ h_init
      rw [h_rinit'] at h_rinit
      injection h_rinit with h_eq
      subst h_eq
      have h_inv : ∀ n : Nat,
          SimulationInv p (projectState (rtrace n)) (rtrace n) := fun n => by
        induction n with
        | zero =>
          rw [h_rt0, projectState_sim_of_sim h_sim₀]
          exact h_sim₀
        | succ m ih =>
          have h_sim_m := simulationInv_with_counters m (m + 1) ih
          let ⟨_, _, h_sim'⟩ := sim_of_refStep h_dec h_sim_m (h_rstep m)
          have h_sim_succ := simulationInv_of_with_counters h_sim'
          rw [projectState_sim_of_sim h_sim_succ]
          exact h_sim_succ
      refine ⟨s₀, h_init, fun n => projectState (rtrace n), ?_, ?_⟩
      · dsimp only
        rw [h_rt0]
        exact projectState_sim_of_sim h_sim₀
      · intro n
        dsimp only
        have h_sim_n := simulationInv_with_counters n (n + 1) (h_inv n)
        let ⟨s', h_step_n, h_sim'⟩ := sim_of_refStep h_dec h_sim_n (h_rstep n)
        rw [projectState_sim_of_sim (simulationInv_of_with_counters h_sim')]
        exact h_step_n

/-- Main end-to-end operational correspondence theorem: for any
`p : Program` and `q : Query`, if `WellFormed p q` holds in
$M_{\text{anneal}}$, then:
1. `RefWellFormed (encodeProg p) q` holds across all step budgets
   `maxSteps : Nat` in the move-deinitializing reference machine
   $M_{\text{ref}}$;
2. `Behavior p q out` holds in $M_{\text{anneal}}$ exactly when
   `RefBehavior (encodeProg p) q out` holds in $M_{\text{ref}}$; and
3. `(p, q)` diverges in $M_{\text{anneal}}$ exactly when `encodeProg p`
   diverges in $M_{\text{ref}}$. -/
theorem anneal_corresponds_to_miri : CorrespondenceClaim :=
  fun p q h_wf =>
    ⟨refWellFormed_of_wellFormed p q h_wf, behavior_iff_refBehavior p q,
      diverges_iff_refDiverges p q⟩

/-- Bidirectional Fault-Kind Correspondence Theorem (`C3`, `NC4`):
Fault kinds `.undefined` and `.unsupported` in `M_anneal` correspond in exact
bijection to `.ub` and `.blocked` in `M_ref` (`faultToRefOutcome k`). -/
theorem reachesResult_fault_iff_refReachesOutcome :
    FaultEquivalenceClaim := by
  intro p q k
  have h_dec : decodeProg (encodeProg p) = some p := decodeProg_encodeProg p
  constructor
  · intro h_res
    unfold ReachesResult at h_res
    cases h_init : initState p q with
    | error k₀ =>
      rw [h_init] at h_res
      injection h_res with h_k
      subst h_k
      refine ⟨0, ?_⟩
      unfold RefReachesOutcome
      rw [(initRefState_sim 0 h_dec).1 k h_init]
    | ok s₀ =>
      rw [h_init] at h_res
      let ⟨s_end, h_reach, c, hc, h_es⟩ := h_res
      let ⟨n, h_in⟩ := exists_reachesN_of_reaches h_reach
      let ⟨rs₀, h_rinit, h_sim₀, h_steps₀, h_max₀⟩ :=
        (initRefState_sim (n + 1) h_dec).2 s₀ h_init
      have h_budget : rs₀.stepsExecuted + n ≤ rs₀.maxSteps := by
        rw [h_steps₀, h_max₀, Nat.zero_add]
        exact Nat.le_succ n
      let ⟨rs_end, h_rreach, h_sim_end, h_steps_end, h_max_end⟩ :=
        refReachesN_of_reachesN h_dec h_in h_sim₀ h_budget
      let ⟨f, rf, _, hs, hrs, hcm, _, body, hbody, hlen, hrf⟩ := h_sim_end
      have h_lt : Nat.blt rs_end.stepsExecuted rs_end.maxSteps = true := by
        apply nat_blt_eq_true_of_lt
        rw [h_steps_end, h_steps₀, Nat.zero_add, h_max_end, h_max₀]
        exact Nat.lt_succ_self n
      have h_reval := evalRefStep_eq h_dec hs hrs hcm hbody hlen hrf h_lt c
      rw [h_es] at h_reval
      refine ⟨n + 1, ?_⟩
      unfold RefReachesOutcome
      rw [h_rinit]
      exact ⟨rs_end, refReaches_of_refReachesN h_rreach, c, hc, h_reval⟩
  · intro h_ex
    let ⟨maxSteps, h_ref⟩ := h_ex
    unfold RefReachesOutcome at h_ref
    cases h_init : initState p q with
    | error k₀ =>
      rw [(initRefState_sim maxSteps h_dec).1 k₀ h_init] at h_ref
      unfold ReachesResult
      rw [h_init]
      cases k₀ <;> cases k <;> cases h_ref <;> rfl
    | ok s₀ =>
      let ⟨rs₀, h_rinit, h_sim₀, _, _⟩ :=
        (initRefState_sim maxSteps h_dec).2 s₀ h_init
      rw [h_rinit] at h_ref
      let ⟨rs, h_rreach, c, hc, h_reval⟩ := h_ref
      let ⟨s, h_reach, h_sim⟩ := sim_of_refReaches h_dec h_sim₀ h_rreach
      let ⟨f, rf, _, hs, hrs, hcm, _, body, hbody, hlen, hrf⟩ := h_sim
      cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
      | false =>
        unfold evalRefStep at h_reval
        rw [h_lt] at h_reval
        cases k <;> cases h_reval
      | true =>
        rw [evalRefStep_eq h_dec hs hrs hcm hbody hlen hrf h_lt c] at h_reval
        cases h_es : evalStep p c s with
        | step s' =>
          let ⟨_, hs', _, _⟩ := evalStep_step_inv hs hbody hlen h_es
          rw [h_es, hs'] at h_reval
          cases k <;> cases h_reval
        | done out =>
          rw [h_es] at h_reval
          cases k <;> cases h_reval
        | fault k₀ =>
          rw [h_es] at h_reval
          have hk_eq : k₀ = k := by
            cases k₀ <;> cases k <;> cases h_reval <;> rfl
          subst hk_eq
          unfold ReachesResult
          rw [h_init]
          exact ⟨s, h_reach, c, hc, h_es⟩

theorem correspondence_claim_holds : CorrespondenceClaim :=
  anneal_corresponds_to_miri

theorem fault_equivalence_claim_holds : FaultEquivalenceClaim :=
  reachesResult_fault_iff_refReachesOutcome

theorem list_length_concat {α : Type} (xs : List α) (v : α) :
    (xs.concat v).length = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    change (rest.concat v).length + 1 = rest.length + 1 + 1
    rw [ih]

theorem list_get_concat_last {α : Type} (xs : List α) (v : α)
    (h : xs.length < (xs.concat v).length) :
    (xs.concat v).get ⟨xs.length, h⟩ = v := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    exact ih (Nat.lt_of_succ_lt_succ h)

theorem dite_pos {P : Prop} [h_dec : Decidable P] {α : Type}
    (h : P) (t : P → α) (e : ¬ P → α) :
    dite P t e = t h := by
  cases h_dec with
  | isFalse h_not => exact False.elim (h_not h)
  | isTrue h_yes => rfl

theorem array_back?_push {α : Type} (xs : Array α) (v : α) :
    (xs.push v).back? = some v := by
  cases xs with
  | mk l =>
    dsimp only [Array.back?, Array.push, Array.size, GetElem?.getElem?,
      Array.instGetElem?NatLtSize, decidableGetElem?, GetElem.getElem,
      Array.instGetElemNatLtSize, Array.getInternal]
    have h_len : (l.concat v).length = l.length + 1 := list_length_concat l v
    have h_sub : (l.concat v).length - 1 = l.length := by
      rw [h_len]
      rfl
    have h_lt : (l.concat v).length - 1 < (l.concat v).length := by
      rw [h_sub, h_len]
      exact Nat.lt_succ_self l.length
    rw [dite_pos h_lt]
    apply congrArg some
    revert h_lt
    rw [h_sub]
    intro h_lt2
    exact list_get_concat_last l v h_lt2

theorem miri_move_deinit_wiring_claim_holds : MiriMoveDeinitWiringClaim := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K U C O X Host _ cfg limits c state
    rfl
  · intro K U C O X Host _ cfg limits h_true
    constructor
    · dsimp only [Miri.Interpreter.ExecutionMachine.withValidation]
      rw [h_true]
      rfl
    · dsimp only [Miri.Interpreter.ExecutionMachine.operandHooks]
      rw [h_true]
      rfl
  · intro Prov Extra State hooks frame state localId known h_false
    dsimp only [Miri.Interpreter.evalOperand]
    rw [h_false]
    rfl
  · intro Prov Extra State hooks frame frame₁ frame₂ state state₁ localId
        known imm layout h_true h_place h_rep
    dsimp only [Miri.Interpreter.evalOperand]
    rw [h_true, h_place]
    dsimp only [Array.isEmpty, Array.size, List.length]
    rw [h_rep]
    rfl
  · intro K U m mplace isMove
    dsimp only [Miri.Interpreter.MachineHooks.takeLastPendingMoveDeinit,
      Miri.Interpreter.MachineHooks.recordPendingMoveDeinit]
    rw [array_back?_push]
    cases isMove <;> rfl
  · intro P S C E Other Extern FnABI ArgABI h choice place snap
    exact ⟨rfl, rfl⟩

/-! ## `Operand.move` Deinitialization and Overflow Canaries (`D6`–`D10`) -/

open Trusted.Correspondence Anneal.MirWp

/-- `D6` (Use-After-Move UB):
`_2 = move _1; _0 = copy _1; return` deinitializes `_1` on `move _1` and
faults with `.fault .undefined` (`.ub` in $M_{\text{ref}}$) on the subsequent
`copy _1`. -/
theorem canary_D6_use_after_move_ub : CanaryD6UseAfterMoveUbClaim := by
  have h_wp : wpFaultProg progUseAfterMoveD6 2 queryU32_42 .undefined := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_ub, h_excl, _, h_nwf⟩ := reaches_fault_and_exclusive_of_wpFault
    progUseAfterMoveD6 queryU32_42 2 .undefined h_wp
  have h_ref_ub := (reachesResult_fault_iff_refReachesOutcome
    progUseAfterMoveD6 queryU32_42 .undefined).1 h_ub
  exact ⟨h_ub, h_excl .unsupported (fun h => FaultKind.noConfusion h), h_nwf,
    h_ref_ub⟩

/-- `D7a` (`BinaryOp` left-to-right `copy _1` then `move _1` succeeds):
`_0 = BinOp(Add, copy _1, move _1); return` reads `_1` in `lhs`, then reads
and deinitializes `_1` in `rhs`, and returns `84`. -/
theorem canary_D7a_binop_copy_then_move_ok :
    CanaryD7aBinopCopyThenMoveOkClaim := by
  have h_wp : wpProg progBinOpCopyThenMoveD7a 2 queryU32_42
      (fun out => out = .returned ⟨u32Val 84, ⟨[]⟩⟩) := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_sat, out, h_beh, h_eq⟩ := wellFormed_and_spec_of_wp
    progBinOpCopyThenMoveD7a queryU32_42 2 _ h_wp
  subst h_eq
  let ⟨h_rwf, h_rbeh, _⟩ := anneal_corresponds_to_miri
    progBinOpCopyThenMoveD7a queryU32_42 h_sat.1
  exact ⟨h_sat.1, h_beh, h_rwf, (h_rbeh _).1 h_beh⟩

/-- `D7b` (`BinaryOp` left-to-right `move _1` then `copy _1` faults with UB):
`_0 = BinOp(Add, move _1, copy _1); return` deinitializes `_1` in
`lhs = move _1` and faults with `.fault .undefined` (`.ub` in
$M_{\text{ref}}$) in `rhs = copy _1`. -/
theorem canary_D7b_binop_move_then_copy_ub :
    CanaryD7bBinopMoveThenCopyUbClaim := by
  have h_wp :
      wpFaultProg progBinOpMoveThenCopyD7b 1 queryU32_42 .undefined := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_ub, h_excl, _, h_nwf⟩ := reaches_fault_and_exclusive_of_wpFault
    progBinOpMoveThenCopyD7b queryU32_42 1 .undefined h_wp
  have h_ref_ub := (reachesResult_fault_iff_refReachesOutcome
    progBinOpMoveThenCopyD7b queryU32_42 .undefined).1 h_ub
  exact ⟨h_ub, h_excl .unsupported (fun h => FaultKind.noConfusion h), h_nwf,
    h_ref_ub⟩

/-- `D7c` (`BinaryOp` left-to-right `move _1` then `move _1` faults with UB):
`_0 = BinOp(Add, move _1, move _1); return` deinitializes `_1` in
`lhs = move _1` and faults with `.fault .undefined` (`.ub` in
$M_{\text{ref}}$) in `rhs = move _1`. -/
theorem canary_D7c_binop_move_then_move_ub :
    CanaryD7cBinopMoveThenMoveUbClaim := by
  have h_wp :
      wpFaultProg progBinOpMoveThenMoveD7c 1 queryU32_42 .undefined := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_ub, h_excl, _, h_nwf⟩ := reaches_fault_and_exclusive_of_wpFault
    progBinOpMoveThenMoveD7c queryU32_42 1 .undefined h_wp
  have h_ref_ub := (reachesResult_fault_iff_refReachesOutcome
    progBinOpMoveThenMoveD7c queryU32_42 .undefined).1 h_ub
  exact ⟨h_ub, h_excl .unsupported (fun h => FaultKind.noConfusion h), h_nwf,
    h_ref_ub⟩

/-- `D8` (Self-move `_1 = move _1` preserves initialized value):
`_1 = move _1; _0 = copy _1; return` reads `42` from `_1`, deinitializes `_1`
to `.live none`, and then writes `42` back into `_1`, so the subsequent
`_0 = copy _1` succeeds and returns `42`. -/
theorem canary_D8_self_move_ok : CanaryD8SelfMoveOkClaim := by
  have h_wp : wpProg progSelfMoveD8 3 queryU32_42
      (fun out => out = .returned ⟨u32Val 42, ⟨[]⟩⟩) := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_sat, out, h_beh, h_eq⟩ :=
    wellFormed_and_spec_of_wp progSelfMoveD8 queryU32_42 3 _ h_wp
  subst h_eq
  let ⟨h_rwf, h_rbeh, _⟩ :=
    anneal_corresponds_to_miri progSelfMoveD8 queryU32_42 h_sat.1
  exact ⟨h_sat.1, h_beh, h_rwf, (h_rbeh _).1 h_beh⟩

/-- `D9` (Move of 0-Byte ZST `MirTy.unit` Remains Initialized):
`_2 = move _1; _0 = copy _1; return` where `_1 : ()` sets `_1` to
`liveUninitSlot .unit = .live (some .unit)`, so subsequent `_0 = copy _1`
succeeds and returns `.unit`. -/
theorem canary_D9_move_unit_zst_ok : CanaryD9MoveUnitZstOkClaim := by
  have h_wp : wpProg progMoveUnitZstD9 3 queryEmpty
      (fun out => out = .returned ⟨.unit, ⟨[]⟩⟩) := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_sat, out, h_beh, h_eq⟩ :=
    wellFormed_and_spec_of_wp progMoveUnitZstD9 queryEmpty 3 _ h_wp
  subst h_eq
  let ⟨h_rwf, h_rbeh, _⟩ :=
    anneal_corresponds_to_miri progMoveUnitZstD9 queryEmpty h_sat.1
  exact ⟨h_sat.1, h_beh, h_rwf, (h_rbeh _).1 h_beh⟩

/-- `D10` (unchecked versus wrapping overflow): on `(u32::MAX, 1)`,
`_0 = AddUnchecked(_1, _2)` (`progAddUncheckedU32`) reaches UB in both
machines, while wrapping `_0 = Add(_1, _2)` (`progAddU32`) returns `0` in both
machines. `encodeRvalue_binaryOp_iff` keeps the codec from exchanging the two
operators, so a semantics or codec that confused them would falsify one half
of this canary. -/
theorem canary_D10_add_unchecked_overflow_ub :
    CanaryD10AddUncheckedOverflowUbClaim := by
  let ⟨⟨h_ub, _, h_nwf⟩, _, h_beh⟩ :=
    canary_negative_ub_add_unchecked_overflow_u32
  have h_ref_ub := (reachesResult_fault_iff_refReachesOutcome
    progAddUncheckedU32 queryU32MaxPlusOne .undefined).1 h_ub
  exact ⟨h_ub, h_nwf, h_ref_ub, h_beh,
    (behavior_iff_refBehavior progAddU32 queryU32MaxPlusOne _).1 h_beh⟩

end Anneal.MirCorrespondenceProof
