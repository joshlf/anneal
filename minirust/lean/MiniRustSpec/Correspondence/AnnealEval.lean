/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.MiniRustEval

/-!
# Symbolic evaluation of Anneal's MIR semantics on fragment bodies

Facts about `Trusted.Rustc.V2026_06_01.MirSemantics` (`evalOperand`,
`evalRvalue`, `evalScalarBinOp`, `evalStmt`, `evalTerminator`, `stepMirFn`)
on fragment statements and terminators. These lemmas only *compute* Anneal's
trusted definitions; they do not restate or modify them.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Sequence
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp

/-- Slot facts for Anneal locals (the Anneal half of `FrameOk`). -/
def SlotsOk (decls : List LocalDecl) (locals : List LocalSlot) : Prop :=
  ∀ (i : Nat) d slot, decls[i]? = some d → locals[i]? = some slot → SlotOk (itOf d) slot

theorem evalOperand_frag (decls : List LocalDecl) (locals : List LocalSlot)
    (hslots : SlotsOk decls locals) (hn : locals.length = decls.length)
    (it : Gen.IntType) (op : Operand) (hok : operandOk decls it op = true)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation) (layouts : Layout.LayoutTable)
    (callerLocals : List LocalSlot) :
    (∀ bits, opBits locals op = some bits →
      evalOperand locals op borrows globals layouts callerLocals =
        .ok (.scalar ⟨bits, it.size.bytes⟩) locals) ∧
    (opBits locals op = none → evalOperand locals op borrows globals layouts callerLocals = .ub) := by
  match op, hok with
  | .copy ⟨j, []⟩, hok =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hj, hty⟩ := hok
    have hjl : j < locals.length := by rw [hn]; exact hj
    obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨decls[j], by simp [hj]⟩
    have hit : itOf d = it := by
      simp [operandIntType, hd] at hty
      simp [itOf, hty]
    have hs : locals[j]? = some locals[j] := by simp [hjl]
    have hslot := hslots j d _ hd hs
    rw [hit] at hslot
    unfold evalOperand
    simp only [opBits, get?]
    generalize locals[j] = slot at hs hslot
    match slot, hslot with
    | .uninit, _ => simp [hs]
    | .init (.scalar sc), hsc =>
      obtain ⟨hsz, _⟩ := hsc
      refine ⟨fun bits hb => ?_, fun hnone => by simp [hs] at hnone⟩
      simp [hs] at hb
      subst hb
      simp [hs, readProjectedValue, ← hsz]
  | .constant c, hok =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hty, htr⟩ := hok
    simp only [operandIntType] at hty
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp htr
    simp only [translateOperand, hty] at he
    match hv : c.val, he with
    | .scalar (.int ⟨bits, sz⟩), he =>
      simp only at he
      split at he
      · next hc =>
        obtain ⟨hsz, _⟩ := hc
        refine ⟨fun bits' hb => ?_, fun hnone => by simp [opBits, hv] at hnone⟩
        simp [opBits, hv] at hb
        subst hb
        simp [evalOperand, hv, evalConstValue, hsz]
      · simp at he

theorem wrap_eq_toNat (v : Nat) (n : Nat) :
    MirSemantics.wrapScalarBits v (MirSemantics.scalarModulus n) = (((v : Int)) % 2 ^ (8 * n)).toNat := by
  rw [wrapScalarBits_eq, scalarModulus_eq]
  have : ((v : Int) % 2 ^ (8 * n)) = ((v % 2 ^ (8 * n) : Nat) : Int) := by
    rw [Int.natCast_emod]; push_cast; rfl
  rw [this, Int.toNat_natCast]

theorem evalScalarBinOp_frag (op : MirAst.BinOp) (iop : Gen.IntBinOp) (hop : translateBinOp op = some iop)
    (x y sz : Nat) (hsz : sz ≠ 0) (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz))
    (locals : List LocalSlot) (mem : MirSemantics.Memory) (isSigned : Bool) :
    evalScalarBinOp op ⟨x, sz⟩ ⟨y, sz⟩ locals mem isSigned =
      .ok (.scalar ⟨(intArith iop x y % 2 ^ (8 * sz)).toNat, sz⟩) locals mem := by
  have hm := scalarModulus_eq sz
  have hbeq : Nat.beq sz 0 = false := by
    cases h : Nat.beq sz 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) hsz
  have hpos : 0 < 2 ^ (8 * sz) := Nat.two_pow_pos _
  have hp : ((2 : Nat) ^ (8 * sz) : Int) = 2 ^ (8 * sz) := by push_cast; rfl
  cases op <;> simp [translateBinOp] at hop <;> subst hop
  · -- add
    simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.add_eq, wrap_eq_toNat, intArith]
    push_cast; rfl
  · -- sub
    simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.sub_eq, Nat.add_eq, wrapScalarBits_eq, hm,
      intArith]
    by_cases hle : y ≤ x
    · have hble : Nat.ble y x = true := Nat.ble_eq.mpr hle
      simp only [hble]
      have hlt : x - y < 2 ^ (8 * sz) := by omega
      rw [Nat.mod_eq_of_lt hlt]
      have : ((x : Int) - y) % 2 ^ (8 * sz) = ((x : Int) - y) :=
        Int.emod_eq_of_lt (by omega) (by omega)
      rw [this]
      congr 3; omega
    · have hble : Nat.ble y x = false := by
        cases h : Nat.ble y x
        · rfl
        · exact absurd (Nat.ble_eq.mp h) hle
      simp only [hble, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
      have hlt : 2 ^ (8 * sz) + x - y < 2 ^ (8 * sz) := by omega
      rw [Nat.mod_eq_of_lt hlt]
      have : ((x : Int) - y) % 2 ^ (8 * sz) = ((x : Int) - y) + 2 ^ (8 * sz) := by
        rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
      rw [this]
      congr 3; omega
  · -- mul
    simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.mul_eq, wrap_eq_toNat, intArith]
    push_cast; rfl

theorem opBits_lt (decls : List LocalDecl) (locals : List LocalSlot) (hslots : SlotsOk decls locals)
    (it : Gen.IntType) (op : Operand) (hok : operandOk decls it op = true) (bits : Nat)
    (hb : opBits locals op = some bits) : bits < 2 ^ (8 * it.size.bytes) := by
  match op, hok, hb with
  | .copy ⟨j, []⟩, hok, hb =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hj, hty⟩ := hok
    obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨decls[j], by simp [hj]⟩
    have hit : itOf d = it := by
      simp [operandIntType, hd] at hty
      simp [itOf, hty]
    simp only [opBits] at hb
    match hs : locals[j]?, hb with
    | some (.init (.scalar sc)), hb =>
      simp at hb; subst hb
      have := hslots j d _ hd hs
      rw [hit] at this
      exact this.2
  | .constant c, hok, hb =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hty, htr⟩ := hok
    simp only [operandIntType] at hty
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp htr
    simp only [translateOperand, hty] at he
    simp only [opBits] at hb
    match hv : c.val, he, hb with
    | .scalar (.int ⟨bits', sz⟩), he, hb =>
      simp only at he hb
      simp at hb; subst hb
      split at he
      · next hc => obtain ⟨hsz, hlt⟩ := hc; subst hsz; exact hlt
      · simp at he

theorem wrap_neg_eq_toNat (x sz : Nat) (hx : x < 2 ^ (8 * sz)) :
    let m := MirSemantics.scalarModulus sz
    MirSemantics.wrapScalarBits (m - MirSemantics.wrapScalarBits x m) m =
      ((- (x : Int)) % 2 ^ (8 * sz)).toNat := by
  dsimp only
  have hm := scalarModulus_eq sz
  have hpos : 0 < 2 ^ (8 * sz) := Nat.two_pow_pos _
  have hp : ((2 : Nat) ^ (8 * sz) : Int) = 2 ^ (8 * sz) := by push_cast; rfl
  simp only [wrapScalarBits_eq, hm, Nat.mod_eq_of_lt hx]
  by_cases hx0 : x = 0
  · subst hx0; simp
  · have hlt : 2 ^ (8 * sz) - x < 2 ^ (8 * sz) := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have : (- (x : Int)) % 2 ^ (8 * sz) = (- (x : Int)) + 2 ^ (8 * sz) := by
      rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [this]
    omega

theorem wrap_not_eq_toNat (x sz : Nat) (hx : x < 2 ^ (8 * sz)) :
    let m := MirSemantics.scalarModulus sz
    (m - 1) - MirSemantics.wrapScalarBits x m =
      ((- (x : Int) - 1) % 2 ^ (8 * sz)).toNat := by
  dsimp only
  have hm := scalarModulus_eq sz
  have hpos : 0 < 2 ^ (8 * sz) := Nat.two_pow_pos _
  have hp : ((2 : Nat) ^ (8 * sz) : Int) = 2 ^ (8 * sz) := by push_cast; rfl
  simp only [wrapScalarBits_eq, hm, Nat.mod_eq_of_lt hx]
  have : (- (x : Int) - 1) % 2 ^ (8 * sz) = (- (x : Int) - 1) + 2 ^ (8 * sz) := by
    rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
  rw [this]
  omega

theorem operandTy_of_operandOk (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (srcIt : Gen.IntType) (op : Operand) (hok : operandOk decls srcIt op = true) :
    ∃ ty, MirSemantics.operandTy decls layouts op = some ty ∧ intTypeOf ty = some srcIt := by
  match op, hok with
  | .copy ⟨j, []⟩, hok =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq, operandIntType] at hok
    obtain ⟨hj, hty⟩ := hok
    obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨decls[j], by simp [hj]⟩
    simp [hd] at hty
    exact ⟨d.ty, by simp [MirSemantics.operandTy, MirSemantics.placeTy, get?, hd,
      MirSemantics.resolveProjectedTy], hty⟩
  | .constant c, hok =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hty, _⟩ := hok
    simp only [operandIntType] at hty
    exact ⟨c.ty, rfl, hty⟩

theorem intTypeOf_kind {ty : MirAst.Ty} {it : Gen.IntType} (h : intTypeOf ty = some it) :
    ((∃ u, ty.kind = .uint u) ∧ it.signed = .Unsigned) ∨
    ((∃ i, ty.kind = .int i) ∧ it.signed = .Signed) := by
  unfold intTypeOf intTyBytes at h
  split at h <;> simp at h <;> subst h <;> simp_all

theorem evalUnaryNot_frag (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (it : Gen.IntType) (hsz : it.size.bytes ≠ 0) (op : Operand) (hok : operandOk decls it op = true)
    (x : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (locals : List LocalSlot)
    (mem : MirSemantics.Memory) :
    MirSemantics.evalUnaryNot ⟨x, it.size.bytes⟩ (MirSemantics.operandTy decls layouts op) locals mem =
      .ok (.scalar ⟨((- (x : Int) - 1) % 2 ^ (8 * it.size.bytes)).toNat, it.size.bytes⟩) locals mem := by
  obtain ⟨ty, hty, hit⟩ := operandTy_of_operandOk decls layouts it op hok
  have hbeq : Nat.beq it.size.bytes 0 = false := by
    cases h : Nat.beq it.size.bytes 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) hsz
  rcases intTypeOf_kind hit with ⟨⟨u, hu⟩, _⟩ | ⟨⟨i, hi⟩, _⟩
  · simp [MirSemantics.evalUnaryNot, hty, hu, hbeq, Nat.sub_eq, wrap_not_eq_toNat x _ hx]
  · simp [MirSemantics.evalUnaryNot, hty, hi, hbeq, Nat.sub_eq, wrap_not_eq_toNat x _ hx]

theorem intCastTargetBytes_of_intTypeOf {ty : MirAst.Ty} {it : Gen.IntType}
    (h : intTypeOf ty = some it) :
    MirSemantics.intCastTargetBytes ty.kind = some it.size.bytes := by
  unfold intTypeOf intTyBytes at h
  split at h <;> simp at h <;> subst h <;> simp_all [MirSemantics.intCastTargetBytes]

theorem operandIsSigned_of_operandOk (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (srcIt : Gen.IntType) (op : Operand) (hok : operandOk decls srcIt op = true) :
    MirSemantics.operandIsSigned decls op layouts =
      match srcIt.signed with | .Unsigned => false | .Signed => true := by
  obtain ⟨ty, hty, hit⟩ := operandTy_of_operandOk decls layouts srcIt op hok
  simp only [MirSemantics.operandIsSigned, hty, MirSemantics.tyIsSigned]
  rcases intTypeOf_kind hit with ⟨⟨u, hu⟩, hs⟩ | ⟨⟨i, hi⟩, hs⟩
  · simp [hu, hs]
  · simp [hi, hs]

theorem two_pow_div_two (n : Nat) (hn : 0 < n) : Nat.div (2 ^ n) 2 = 2 ^ (n - 1) := by
  change 2 ^ n / 2 = 2 ^ (n - 1)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp [Nat.pow_succ]

theorem castBits_eq_toNat (srcIt it : Gen.IntType) (hsrcGood : GoodSize srcIt.size.bytes)
    (x : Nat) (hx : x < 2 ^ (8 * srcIt.size.bytes)) :
    let m := MirSemantics.scalarModulus it.size.bytes
    (match srcIt.signed with
      | .Unsigned => MirSemantics.wrapScalarBits x m
      | .Signed =>
        match Nat.ble it.size.bytes srcIt.size.bytes with
        | true => MirSemantics.wrapScalarBits x m
        | false => MirSemantics.signExtendBits x srcIt.size.bytes it.size.bytes) =
      (intFromBits x srcIt % 2 ^ (8 * it.size.bytes)).toNat := by
  dsimp only
  rcases srcIt with ⟨s, ⟨srcBytes⟩⟩
  rcases it with ⟨_, ⟨dstBytes⟩⟩
  dsimp only at hsrcGood hx ⊢
  have hsrcPos : 0 < srcBytes := hsrcGood.pos
  cases s with
  | Unsigned =>
    rw [wrap_eq_toNat]
    rfl
  | Signed =>
    simp only [intFromBits]
    cases hble : Nat.ble dstBytes srcBytes with
    | true =>
      dsimp only
      have hle : dstBytes ≤ srcBytes := Nat.ble_eq.mp hble
      rw [wrap_eq_toNat]
      by_cases hneg : x < 2 ^ (8 * srcBytes - 1)
      · simp [hneg]
      · simp only [hneg, ↓reduceIte]
        congr 1
        have hdvd : ((2 : Int) ^ (8 * dstBytes)) ∣ (2 : Int) ^ (8 * srcBytes) := by
          have hdvdNat : (2 : Nat) ^ (8 * dstBytes) ∣ 2 ^ (8 * srcBytes) :=
            Nat.pow_dvd_pow 2 (by omega)
          exact_mod_cast hdvdNat
        rw [Int.sub_emod, Int.emod_eq_zero_of_dvd hdvd, Int.sub_zero,
          Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
    | false =>
      dsimp only
      have hlt : srcBytes < dstBytes :=
        Nat.lt_of_not_ge (fun hle => by rw [Nat.ble_eq.mpr hle] at hble; cases hble)
      have hsrcBeq : Nat.beq srcBytes 0 = false := by
        cases h : Nat.beq srcBytes 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) (by omega)
      have hpowLe : 2 ^ (8 * srcBytes) ≤ 2 ^ (8 * dstBytes) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hdstPos : 0 < 2 ^ (8 * dstBytes) := Nat.two_pow_pos _
      have hpSrc : ((2 : Nat) ^ (8 * srcBytes) : Int) = 2 ^ (8 * srcBytes) := by push_cast; rfl
      have hpDst : ((2 : Nat) ^ (8 * dstBytes) : Int) = 2 ^ (8 * dstBytes) := by push_cast; rfl
      have hhalf : Nat.div (2 ^ (8 * srcBytes)) 2 = 2 ^ (8 * srcBytes - 1) :=
        two_pow_div_two (8 * srcBytes) (by omega)
      simp only [MirSemantics.signExtendBits, hble, MirSemantics.isSignedNegative, hsrcBeq,
        scalarModulus_eq, wrapScalarBits_eq, Nat.mod_eq_of_lt hx, hhalf,
        Nat.add_eq, Nat.sub_eq]
      by_cases hneg : x < 2 ^ (8 * srcBytes - 1)
      · have hbleNeg : Nat.ble (2 ^ (8 * srcBytes - 1)) x = false := by
          cases h : Nat.ble (2 ^ (8 * srcBytes - 1)) x
          · rfl
          · exact absurd (Nat.ble_eq.mp h) (by omega)
        simp only [hneg, ↓reduceIte, hbleNeg]
        have hxDst : (x : Int) < 2 ^ (8 * dstBytes) := by omega
        rw [Int.emod_eq_of_lt (by omega) hxDst, Int.toNat_natCast]
      · have hbleNeg : Nat.ble (2 ^ (8 * srcBytes - 1)) x = true :=
          Nat.ble_eq.mpr (by omega)
        simp only [hneg, ↓reduceIte, hbleNeg]
        have : ((x : Int) - 2 ^ (8 * srcBytes)) % 2 ^ (8 * dstBytes) =
            ((x : Int) - 2 ^ (8 * srcBytes)) + 2 ^ (8 * dstBytes) := by
          rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
        rw [this]
        omega

theorem evalRvalue_frag (decls : List LocalDecl) (locals : List LocalSlot)
    (hslots : SlotsOk decls locals) (hn : locals.length = decls.length)
    (it : Gen.IntType) (hsz : it.size.bytes ≠ 0) (rv : Rvalue) (hok : rvalueOk decls it rv = true)
    (mem : MirSemantics.Memory) (layouts : Layout.LayoutTable) :
    (∀ r, rvBits decls locals it rv = some r →
      evalRvalue locals rv mem decls layouts = .ok (.scalar ⟨r, it.size.bytes⟩) locals mem) ∧
    (rvBits decls locals it rv = none → evalRvalue locals rv mem decls layouts = .ub) := by
  match rv, hok with
  | .use op, hok =>
    simp only [rvalueOk] at hok
    obtain ⟨hsome, hnone⟩ :=
      evalOperand_frag decls locals hslots hn it op hok mem.borrows mem.globals layouts mem.callerLocals
    refine ⟨fun r hr => ?_, fun h => ?_⟩
    · simp [evalRvalue, hsome r hr]
    · simp [evalRvalue, hnone h]
  | .unaryOp uop op, hok =>
    simp only [rvalueOk, Bool.and_eq_true] at hok
    obtain ⟨huop, hok⟩ := hok
    obtain ⟨iuop, hiuop⟩ := Option.isSome_iff_exists.mp huop
    obtain ⟨ha, hanone⟩ :=
      evalOperand_frag decls locals hslots hn it op hok mem.borrows mem.globals layouts mem.callerLocals
    have hbeq : Nat.beq it.size.bytes 0 = false := by
      cases h : Nat.beq it.size.bytes 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hsz
    cases hxo : opBits locals op with
    | none =>
      refine ⟨fun r hr => by simp [rvBits, hiuop, hxo] at hr, fun _ => ?_⟩
      cases uop <;> simp [translateUnOp] at hiuop <;> simp [evalRvalue, hanone hxo]
    | some x =>
      refine ⟨fun r hr => ?_, fun h => by simp [rvBits, hiuop, hxo] at h⟩
      simp [rvBits, hiuop, hxo] at hr
      subst hr
      have hx := opBits_lt decls locals hslots it op hok x hxo
      cases uop <;> simp [translateUnOp] at hiuop <;> subst hiuop
      · simp only [evalRvalue, ha x hxo, evalUnaryNot_frag decls layouts it hsz op hok x hx, intUnArith]
      · simp [evalRvalue, ha x hxo, hbeq, Nat.sub_eq, wrap_neg_eq_toNat x _ hx, intUnArith]
  | .binaryOp op a b, hok =>
    simp only [rvalueOk, Bool.and_eq_true] at hok
    obtain ⟨⟨hop, hoka⟩, hokb⟩ := hok
    obtain ⟨iop, hiop⟩ := Option.isSome_iff_exists.mp hop
    obtain ⟨ha, hanone⟩ :=
      evalOperand_frag decls locals hslots hn it a hoka mem.borrows mem.globals layouts mem.callerLocals
    obtain ⟨hb, hbnone⟩ :=
      evalOperand_frag decls locals hslots hn it b hokb mem.borrows mem.globals layouts mem.callerLocals
    cases hxa : opBits locals a with
    | none =>
      refine ⟨fun r hr => by simp [rvBits, hiop, hxa] at hr, fun _ => ?_⟩
      simp [evalRvalue, hanone hxa]
    | some x =>
      cases hyb : opBits locals b with
      | none =>
        refine ⟨fun r hr => by simp [rvBits, hiop, hxa, hyb] at hr, fun _ => ?_⟩
        simp [evalRvalue, ha x hxa, hbnone hyb]
      | some y =>
        refine ⟨fun r hr => ?_, fun h => by simp [rvBits, hiop, hxa, hyb] at h⟩
        simp [rvBits, hiop, hxa, hyb] at hr
        subst hr
        have hx := opBits_lt decls locals hslots it a hoka x hxa
        have hy := opBits_lt decls locals hslots it b hokb y hyb
        simp [evalRvalue, ha x hxa, hb y hyb, evalScalarBinOp_frag op iop hiop x y _ hsz hx hy]
  | .cast .intToInt op targetTy, hok =>
    simp only [rvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨htgt, hsrc⟩ := hok
    cases hsrcIt : operandIntType decls op with
    | none => simp [hsrcIt] at hsrc
    | some srcIt =>
      simp only [hsrcIt] at hsrc
      obtain ⟨ha, hanone⟩ :=
        evalOperand_frag decls locals hslots hn srcIt op hsrc mem.borrows mem.globals layouts mem.callerLocals
      obtain ⟨ty, _, hsrcTy⟩ := operandTy_of_operandOk decls layouts srcIt op hsrc
      have hsrcGood : GoodSize srcIt.size.bytes := intTypeOf_good hsrcTy
      have hsrcBeq : Nat.beq srcIt.size.bytes 0 = false := by
        cases h : Nat.beq srcIt.size.bytes 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) (Nat.ne_of_gt hsrcGood.pos)
      have htgtBytes := intCastTargetBytes_of_intTypeOf htgt
      have hsigned := operandIsSigned_of_operandOk decls layouts srcIt op hsrc
      cases hxo : opBits locals op with
      | none =>
        refine ⟨fun r hr => by simp [rvBits, hsrcIt, hxo] at hr, fun _ => ?_⟩
        simp [evalRvalue, hanone hxo]
      | some x =>
        refine ⟨fun r hr => ?_, fun h => by simp [rvBits, hsrcIt, hxo] at h⟩
        simp [rvBits, hsrcIt, hxo] at hr
        subst hr
        have hx := opBits_lt decls locals hslots srcIt op hsrc x hxo
        have hcast := castBits_eq_toNat srcIt it hsrcGood x hx
        dsimp only at hcast
        simp only [evalRvalue, ha x hxo, hsrcBeq, htgtBytes, hsigned]
        cases hs : srcIt.signed <;> simp only [hs] at hcast ⊢
        · rw [hcast]
        · cases hble : Nat.ble it.size.bytes srcIt.size.bytes <;> simp only [hble] at hcast ⊢ <;> rw [hcast]

theorem evalStmt_assign (s : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (i : Nat) (rv : Rvalue) (span : String) (hslots : SlotsOk decls s.frame.locals)
    (hn : s.frame.locals.length = decls.length) (d : LocalDecl) (hd : decls[i]? = some d)
    (hsz : (itOf d).size.bytes ≠ 0) (hok : rvalueOk decls (itOf d) rv = true)
    (hbor : s.memory.borrows = []) (hprot : s.memory.activeProtectors = []) :
    (∀ r, rvBits decls s.frame.locals (itOf d) rv = some r →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts =
        .tau (.running (advanceStmt s (s.frame.locals.set i (.init (.scalar ⟨r, (itOf d).size.bytes⟩)))
          { s.memory with borrows := [] }))) ∧
    (rvBits decls s.frame.locals (itOf d) rv = none →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  have hi : i < s.frame.locals.length := by rw [hn]; exact (List.getElem?_eq_some_iff.mp hd).1
  have hs : s.frame.locals[i]? = some s.frame.locals[i] := by simp [hi]
  have hslot := hslots i d _ hd hs
  have hlive : s.frame.locals[i] ≠ .dead := by
    intro h; rw [h] at hslot; exact hslot
  obtain ⟨hok', hnone⟩ := evalRvalue_frag decls s.frame.locals hslots hn (itOf d) hsz rv hok s.memory layouts
  refine ⟨fun r hr => ?_, fun h => ?_⟩
  · simp only [evalStmt, hok' r hr, get?, hs, set?, hi, hprot, hbor, invalidateConflictingBorrows_nil]
    cases hsl : s.frame.locals[i] with
    | dead => exact absurd hsl hlive
    | uninit => simp [MirStepNode.step]
    | init v => simp [MirStepNode.step]
  · simp [evalStmt, hnone h]

theorem evalStmt_placeMention (s : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (i : Nat) (span : String) (hslots : SlotsOk decls s.frame.locals)
    (hn : s.frame.locals.length = decls.length) (hi : i < decls.length) :
    evalStmt s ⟨.placeMention ⟨i, []⟩, span⟩ decls layouts =
      .tau (.running (advanceStmt s s.frame.locals)) := by
  have hil : i < s.frame.locals.length := by rw [hn]; exact hi
  obtain ⟨d, hd⟩ : ∃ d, decls[i]? = some d := ⟨decls[i], by simp [hi]⟩
  have hs : s.frame.locals[i]? = some s.frame.locals[i] := by simp [hil]
  have hslot := hslots i d _ hd hs
  have hlive : s.frame.locals[i] ≠ .dead := by
    intro h; rw [h] at hslot; exact hslot
  simp only [evalStmt, get?, hs]
  cases hsl : s.frame.locals[i] with
  | dead => exact absurd hsl hlive
  | uninit => simp [MirStepNode.step]
  | init v => simp [MirStepNode.step]

theorem stepMirFn_stmt (body : CapturedMir) (s : MachineState) (bb : BasicBlockData)
    (stmt : MirAst.Statement) (hcallee : s.memory.activeCallee = none)
    (hphase : body.phase = .runtimePostCleanup)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some stmt) :
    stepMirFn body s = evalStmt s stmt body.localDecls body.layouts := by
  simp [stepMirFn, hcallee, hphase, get?, hbb, hst]

theorem stepMirFn_term (body : CapturedMir) (s : MachineState) (bb : BasicBlockData)
    (hcallee : s.memory.activeCallee = none) (hphase : body.phase = .runtimePostCleanup)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hlen : s.frame.stmtIdx = bb.statements.length) :
    stepMirFn body s = evalTerminator s bb.terminator (some body) := by
  simp [stepMirFn, hcallee, hphase, get?, hbb, hlen, length]

end MiniRustSpec.Correspondence
