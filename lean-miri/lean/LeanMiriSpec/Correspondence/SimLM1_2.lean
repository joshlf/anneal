/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.Simulation

/-!
# `LM-1.2`: Booleans, Comparisons, `IntToInt` Casts, and `SwitchInt`

Correspondence between Anneal's `MirSemantics` and `lean-miri`'s
`Miri.Interpreter.{IntegerOps, ScalarOps, Cast, ControlFlow}` for the `LM-1.2`
fragment, layered on the `LM-1.1` machinery in `Simulation.lean`:

* Value level: boolean `UnOp.Not` (`evalUnOp_bool_not_simulation`); `Eq`..`Ge`
  on `bool`, signed, and unsigned operands (`evalBinOp_rel_simulation`); the
  three-way `Cmp`, whose 1-byte `i8` result `-1 = 0xFF / 0 / 1` is the encoding
  of `lean-miri`'s `Ordering` (`evalBinOp_cmp_simulation` for
  `IntegerOps.binary`, `scalarOps_cmp_simulation` for `ScalarOps.binary`); and
  `CastKind.IntToInt` from `bool` or any integer to any integer, covering sign
  extension, zero extension, truncation, and `bool -> int`
  (`evalCast_intToInt_simulation`, with `cast_intToInt_uninit` for UB reads).
* `SwitchInt`: `lean-miri` evaluates it inline in `ControlFlow.evalTerminator`
  (there is no separate `evalSwitchInt`), comparing the discriminant with each
  case through `TerminatorHooks.compareSwitchCase` (`compareSwitchCase_simulation`)
  and falling back to `otherwise`; `evalTerminator_switchInt_ok` shows the case
  loop selects Anneal's `lookupSwitchTarget` over arbitrary `SwitchTargets`.
* Step level: `step_terminator_switchInt_simulation` (`StepObsRel`, the branch
  emits `MirObs.event`) and `step_assign_lm1_2_simulation` (`StepRel`, for
  `bool` comparisons and `IntToInt` casts into immediate locals), composed with
  the `LM-1.1` statement and terminator theorems into
  `step_stmt_lm1_2_simulation` and `step_terminator_lm1_2_simulation`.

Scope notes:

* A `SwitchInt` case value must fit the discriminant's width and a `bool`
  discriminant may only be compared against `0`/`1` (`SwitchCasesFit`), as
  rustc's MIR guarantees: `lean-miri` builds each case as an `ImmTy` of the
  discriminant's layout, so an oversized value is an error and a `bool` case
  `2` is UB (`to_bool`), while Anneal's `lookupSwitchTarget` skips both.
  `char` discriminants are not covered.
* `Cmp` is not covered at the statement level. rustc types its destination as
  `core::cmp::Ordering`, but `annealScalarOpsHooks.orderingLayout` returns the
  layout of `i8`, so `evalRvalueIntoPlace`'s `assertRvalueLayout` rejects a
  `Cmp` assignment to an `Ordering` local with `invalidProgram` while Anneal
  stores the scalar. Closing this needs an `Ordering`-aware `orderingLayout`
  in `Translate.lean`.
-/

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

namespace LeanMiriSpec.Correspondence

/-! ## 1. Shared Helpers -/

theorem decodeBitsInt_unsigned (sz x : Nat) : decodeBitsInt false sz x = (x : Int) := rfl

/-- Byte width of a `bool` or fixed-width integer type on Anneal's 64-bit target
(`0` for every other type). -/
def boolOrIntByteWidth (ty : Ty) : Nat :=
  match ty.kind with
  | .bool => 1
  | .int k => k.byteWidth 64
  | .uint k => k.byteWidth 64
  | _ => 0

/-- `translateTy` gives a `bool` or integer type the scalar layout of its byte
width, for every layout table. -/
theorem boolOrInt_translateTy_size {ty : Ty}
    (hty : ty.kind = .bool ∨ (∃ k, ty.kind = .int k) ∨ (∃ k, ty.kind = .uint k))
    (layouts : LayoutTable) :
    (translateTy ty layouts).layout.size = translateSizeBytes (boolOrIntByteWidth ty) ∧
      ValidScalarBytes (boolOrIntByteWidth ty) := by
  rcases ty with ⟨tk, tIdx⟩
  rcases hty with h | ⟨k, h⟩ | ⟨k, h⟩ <;> dsimp only at h <;> subst h
  · exact ⟨rfl, Or.inl rfl⟩
  · cases k <;> exact ⟨rfl, by dsimp only [boolOrIntByteWidth, ValidScalarBytes]; decide⟩
  · cases k <;> exact ⟨rfl, by dsimp only [boolOrIntByteWidth, ValidScalarBytes]; decide⟩

/-- A valid scalar whose width matches the layout of a `bool` or integer type has
that type's byte width, in both forms used below. -/
theorem sizeBytes_eq_of_translateTy {sc : MirAst.ScalarInt} {ty : Ty} {layouts : LayoutTable}
    (hty : ty.kind = .bool ∨ (∃ k, ty.kind = .int k) ∨ (∃ k, ty.kind = .uint k))
    (hvalid : ValidScalarBytes sc.sizeBytes)
    (hsz : (translateTy ty layouts).layout.size = translateSizeBytes sc.sizeBytes) :
    sc.sizeBytes = boolOrIntByteWidth ty ∧
      sc.sizeBytes = match ty.kind with
        | .bool => 1 | .int k => k.byteWidth 64 | .uint k => k.byteWidth 64 | _ => sc.sizeBytes := by
  obtain ⟨hwsz, hwvalid⟩ := boolOrInt_translateTy_size hty layouts
  have hwidth : sc.sizeBytes = boolOrIntByteWidth ty :=
    translateSizeBytes_inj hvalid hwvalid (by rw [← hsz, hwsz])
  refine ⟨hwidth, ?_⟩
  rw [hwidth]
  rcases ty with ⟨tk, tIdx⟩
  rcases hty with h | ⟨k, h⟩ | ⟨k, h⟩ <;> dsimp only at h <;> subst h <;> rfl

/-! ## 2. Boolean `Not` -/

/-- Boolean `UnOp.Not` on a valid `bool` (`sizeBytes = 1`, bits `0`/`1`) agrees with
`ScalarOps.unary .Not` and produces a valid `bool`. -/
theorem evalUnOp_bool_not_simulation
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (locals : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (ty : Ty) (hty : ty.kind = .bool) (hsz : sc.sizeBytes = 1)
    (hbits : sc.bits = 0 ∨ sc.bits = 1) :
    ∃ sc' msc',
      evalUnaryNot sc (some ty) locals mem = .ok (.scalar sc') locals mem ∧
      Miri.Interpreter.ScalarOps.unary (annealScalarOpsHooks localDecls layouts) () .Not
        ⟨.scalar (.fromScalarInt msc), translateTy ty layouts⟩ =
        .ok ⟨.scalar (.fromScalarInt msc'), translateTy ty layouts⟩ ∧
      ScalarRel sc' msc' ∧
      sc'.sizeBytes = 1 ∧ (sc'.bits = 0 ∨ sc'.bits = 1) := by
  have hb : ∃ b : Bool, sc = boolToScalar b ∧ msc = Miri.Memory.ScalarInt.ofBool b := by
    rcases sc with ⟨sc_bits, sc_size⟩
    rcases msc with ⟨msc_data, msc_size⟩
    have hsize := hrel.size_eq; have hdata := hrel.data_eq
    dsimp at hsz hsize hdata
    rcases hbits with h0 | h1
    · dsimp at h0; subst h0 hsz; dsimp [translateSizeBytes] at hsize
      subst hsize hdata; exact ⟨false, rfl, rfl⟩
    · dsimp at h1; subst h1 hsz; dsimp [translateSizeBytes] at hsize
      subst hsize hdata; exact ⟨true, rfl, rfl⟩
  rcases hb with ⟨b, rfl, rfl⟩
  refine ⟨boolToScalar (!b), Miri.Memory.ScalarInt.ofBool (!b), ?_, ?_,
    ScalarRel.of_boolToScalar (!b), by cases b <;> rfl, by cases b <;> simp [boolToScalar]⟩
  · simp [evalUnaryNot, hty, boolToScalar]
    cases b <;> rfl
  · have he : encodeTyId ty = 1 := by
      rcases ty with ⟨kind, idx⟩
      cases kind <;> try contradiction
      rfl
    unfold Miri.Interpreter.ScalarOps.unary
    simp only [he, hty, annealScalarOpsHooks, classifyEncodedTyId, translateTy]
    cases b <;> rfl

/-! ## 3. Relational Operators (`Eq`, `Ne`, `Lt`, `Le`, `Gt`, `Ge`) -/

/-- `lean-miri`'s result of a relational operator on the decoded operand values
(`IntegerOps.binary`'s comparison branch); `false` for non-relational operators. -/
def relOpBool (op : MirAst.BinOp) (l r : Int) : Bool :=
  match op with
  | .eq => l == r
  | .ne => l != r
  | .lt => decide (l < r)
  | .le => decide (l ≤ r)
  | .gt => decide (l > r)
  | .ge => decide (l ≥ r)
  | _ => false

/-- Anneal's relational operators on same-width canonical scalars compare the
operands' values: two's complement (`signedLt`/`signedLe`) when `signed`, and
unsigned (`Nat.ble`) otherwise. -/
theorem evalScalarBinOp_rel_eq {op : MirAst.BinOp} (hop : IsCmpBinOp op)
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (hsz : sc₁.sizeBytes = sc₂.sizeBytes)
    (locals : List LocalSlot) (mem : Memory) (signed : Bool) :
    evalScalarBinOp op sc₁ sc₂ locals mem signed =
      .ok (.scalar (boolToScalar (relOpBool op (decodeBitsInt signed sc₁.sizeBytes sc₁.bits)
        (decodeBitsInt signed sc₁.sizeBytes sc₂.bits)))) locals mem := by
  have hbeq0 : sc₁.sizeBytes.beq 0 = false := hrel₁.beq_sizeBytes_zero
  have hbeq_eq : sc₁.sizeBytes.beq sc₂.sizeBytes = true := by rw [hsz, Nat.beq_refl]
  have hx : sc₁.bits < 2 ^ (8 * sc₁.sizeBytes) := by
    rw [← scalarModulus_eq_two_pow]; exact hrel₁.canonical
  have hy : sc₂.bits < 2 ^ (8 * sc₁.sizeBytes) := by
    rw [hsz, ← scalarModulus_eq_two_pow]; exact hrel₂.canonical
  have hinj := decodeBitsInt_inj (signed := signed) hrel₁.validBytes hx hy
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [evalScalarBinOp, hbeq0, hbeq_eq, relOpBool]
  · congr 3
    rw [nat_beq_eq_decide]
    exact Bool.eq_iff_iff.mpr (by simp [hinj])
  · congr 3
    rw [nat_beq_eq_decide]
    exact Bool.eq_iff_iff.mpr (by simp [hinj])
  · cases signed
    · congr 3
      rw [nat_ble_eq_decide]
      exact Bool.eq_iff_iff.mpr (by simp [decodeBitsInt])
    · congr 3
      exact signedLt_eq hrel₁.validBytes hx hy
  · cases signed
    · congr 3
      rw [nat_ble_eq_decide]
      exact Bool.eq_iff_iff.mpr (by simp [decodeBitsInt])
    · congr 3
      exact signedLe_eq hrel₁.validBytes hx hy
  · cases signed
    · congr 3
      rw [nat_ble_eq_decide]
      exact Bool.eq_iff_iff.mpr (by simp [decodeBitsInt])
    · congr 3
      exact signedLt_eq hrel₁.validBytes hy hx
  · cases signed
    · congr 3
      rw [nat_ble_eq_decide]
      exact Bool.eq_iff_iff.mpr (by simp [decodeBitsInt])
    · congr 3
      exact signedLe_eq hrel₁.validBytes hy hx

/-- `lean-miri`'s `IntegerOps.binary` on a relational operator compares the
operands' `IntegerOps.decode` values (`ScalarInt.toInt` for signed kinds,
`toUInt` for unsigned ones). -/
theorem integerOps_binary_rel_eq {op : MirAst.BinOp} (hop : IsCmpBinOp op)
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (hsz : sc₁.sizeBytes = sc₂.sizeBytes) (kind : Miri.MIR.IntegerKind) :
    Miri.Interpreter.IntegerOps.binary (translateBinOp op)
      ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
      ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩ =
      .ok (.boolean (relOpBool op (decodeBitsInt kind.signed sc₁.sizeBytes sc₁.bits)
        (decodeBitsInt kind.signed sc₁.sizeBytes sc₂.bits))) := by
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact integerOps_binary_sameType_eq hrel₁ hrel₂ hsz kind _ rfl

/-- Relational operators on `bool`, signed, and unsigned operands of the same type:
Anneal's `evalScalarBinOp` (signed exactly when `tyIsSigned ty`, comparing two's
complement values via `signedLt`/`signedLe`) and `lean-miri`'s
`ScalarOps.binary` (comparing `IntegerOps.decode` values, which use
`ScalarInt.toInt` for signed and `toUInt` for unsigned kinds, or `toBool` values
for `bool`) return the same `bool`, under any `localDecls` and layout table. -/
theorem evalBinOp_rel_simulation
    (op : MirAst.BinOp) (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (locals : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (ty : Ty) (hty : ty.kind = .bool ∨ (∃ k, ty.kind = .int k) ∨ (∃ k, ty.kind = .uint k))
    (hsz : sc₁.sizeBytes = sc₂.sizeBytes)
    (hsz_ty : sc₁.sizeBytes = match ty.kind with | .bool => 1 | .int k => k.byteWidth 64 | .uint k => k.byteWidth 64 | _ => sc₁.sizeBytes)
    (hbits₁ : ty.kind = .bool → sc₁.bits = 0 ∨ sc₁.bits = 1)
    (hbits₂ : ty.kind = .bool → sc₂.bits = 0 ∨ sc₂.bits = 1)
    (mop : Miri.MIR.BinOp) (hmop : translateBinOp op = some mop) :
    ∃ b : Bool,
      evalScalarBinOp op sc₁ sc₂ locals mem (tyIsSigned ty) =
        .ok (.scalar (boolToScalar b)) locals mem ∧
      Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks localDecls layouts) () mop
        ⟨.scalar (.fromScalarInt msc₁), translateTy ty layouts⟩
        ⟨.scalar (.fromScalarInt msc₂), translateTy ty layouts⟩ =
        .ok ⟨.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofBool b)),
          translateTy { kind := .bool, layoutIdx := 0 } emptyLayoutTable⟩ := by
  injection hmop with hmop
  subst hmop
  rcases hty with hbool | hint₀
  · -- `bool`: both operands are `boolToScalar`s; enumerate the four value pairs.
    have hvalid : ∀ {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}, ScalarRel sc msc →
        sc.sizeBytes = 1 → (sc.bits = 0 ∨ sc.bits = 1) →
        ∃ b, sc = boolToScalar b ∧ msc = Miri.Memory.ScalarInt.ofBool b := by
      intro sc msc hrel hsz1 hbits
      rcases sc with ⟨bits, sz⟩
      rcases msc with ⟨data, size⟩
      have hd := hrel.data_eq
      have hs := hrel.size_eq
      dsimp only at hsz1 hbits hd hs
      subst hsz1 hs hd
      rcases hbits with rfl | rfl
      · exact ⟨false, rfl, rfl⟩
      · exact ⟨true, rfl, rfl⟩
    have hsz1 : sc₁.sizeBytes = 1 := by rw [hsz_ty, hbool]
    obtain ⟨b₁, rfl, rfl⟩ := hvalid hrel₁ hsz1 (hbits₁ hbool)
    obtain ⟨b₂, rfl, rfl⟩ := hvalid hrel₂ (hsz ▸ hsz1) (hbits₂ hbool)
    have he : encodeTyId ty = 1 := by
      rcases ty with ⟨tk, tIdx⟩
      dsimp only at hbool
      subst hbool
      rfl
    have hunsigned : tyIsSigned ty = false := by simp [tyIsSigned, hbool]
    rw [hunsigned]
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl <;>
      cases b₁ <;> cases b₂ <;>
      exact ⟨_, rfl, by
        unfold Miri.Interpreter.ScalarOps.binary
        simp only [translateTy, he, hbool, annealScalarOpsHooks, classifyEncodedTyId, boolToScalar]
        rfl⟩
  · -- Integers: compare the decoded values on both sides.
    obtain ⟨kind, hint, hsz₁⟩ : ∃ kind, IsIntegralTy ty kind ∧
        (translateTy ty layouts).layout.size = translateSizeBytes sc₁.sizeBytes := by
      rcases ty with ⟨tk, tIdx⟩
      rcases hint₀ with ⟨k, hk⟩ | ⟨k, hk⟩ <;> dsimp only at hk <;> subst hk
      · exact ⟨_, .int k rfl, by rw [hsz_ty]; cases k <;> rfl⟩
      · exact ⟨_, .uint k rfl, by rw [hsz_ty]; cases k <;> rfl⟩
    have hsz₂ : (translateTy ty layouts).layout.size = translateSizeBytes sc₂.sizeBytes := by
      rw [← hsz]; exact hsz₁
    refine ⟨_, evalScalarBinOp_rel_eq hop hrel₁ hrel₂ hsz locals mem (tyIsSigned ty), ?_⟩
    rw [hint.signed_eq]
    funext m₂
    rw [scalarOps_binary_integer_step localDecls hint hint hrel₁ hrel₂ hsz₁ hsz₂ (Or.inr rfl) m₂,
      integerOps_binary_rel_eq hop hrel₁ hrel₂ hsz kind]
    rfl

/-! ## 4. Three-Way Comparison (`Cmp`) -/

/-- The 1-byte two's-complement `i8` encoding of an `Ordering` (`Less = -1 = 0xFF`,
`Equal = 0`, `Greater = 1`) that Anneal's `evalScalarBinOp .cmp` produces. -/
def orderingI8Bits : Ordering → Nat
  | .lt => 255
  | .eq => 0
  | .gt => 1

private theorem evalBinOp_cmp_simulation_aux
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (locals : List LocalSlot) (mem : Memory)
    (isSigned : Bool)
    (kind : Miri.MIR.IntegerKind)
    (hsz : sc₁.sizeBytes = sc₂.sizeBytes) :
    ∃ (sc'' : MirAst.ScalarInt) (msc'' : Ordering),
      evalScalarBinOp .cmp sc₁ sc₂ locals mem isSigned =
        .ok (.scalar sc'') locals mem ∧
      Miri.Interpreter.IntegerOps.binary .Cmp
        ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
        ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩ =
        .ok (.ordering msc'') ∧
      (kind.signed = isSigned →
        sc'' = ⟨match msc'' with | .lt => 255 | .eq => 0 | .gt => 1, 1⟩) := by
  have hbeq0 : sc₁.sizeBytes.beq 0 = false := hrel₁.beq_sizeBytes_zero
  have hbeq_eq : sc₁.sizeBytes.beq sc₂.sizeBytes = true := by rw [hsz, Nat.beq_refl]
  have hxMod : wrapScalarBits sc₁.bits (scalarModulus sc₁.sizeBytes) = sc₁.bits := hrel₁.wrapScalarBits_self
  have hyMod : wrapScalarBits sc₂.bits (scalarModulus sc₁.sizeBytes) = sc₂.bits := by rw [hsz]; exact hrel₂.wrapScalarBits_self
  have hx_bits : sc₁.bits < 2 ^ (8 * sc₁.sizeBytes) := by
    rw [← scalarModulus_eq_two_pow]; exact hrel₁.canonical
  have hy_bits : sc₂.bits < 2 ^ (8 * sc₁.sizeBytes) := by
    rw [hsz, ← scalarModulus_eq_two_pow]; exact hrel₂.canonical
  have hmiri := integerOps_binary_sameType_eq hrel₁ hrel₂ hsz kind .Cmp rfl
  cases isSigned
  · cases h_eq : Nat.beq sc₁.bits sc₂.bits
    · cases h_ble : Nat.ble sc₁.bits sc₂.bits
      · refine ⟨⟨1, 1⟩, _, ?_, hmiri, ?_⟩
        · unfold evalScalarBinOp; simp only [hbeq0, hbeq_eq, h_eq, h_ble]
        · intro hks; rw [hks]; dsimp [Ord.compare, compareOfLessAndEq, decodeBitsInt]
          rw [nat_beq_eq_decide] at h_eq; rw [nat_ble_eq_decide] at h_ble
          simp only [decide_eq_false_iff_not] at h_eq h_ble
          have h1 : ¬ ((sc₁.bits : Int) < (sc₂.bits : Int)) := by omega
          have h2 : ¬ ((sc₁.bits : Int) = (sc₂.bits : Int)) := by omega
          simp [h1, h2]
      · refine ⟨⟨255, 1⟩, _, ?_, hmiri, ?_⟩
        · unfold evalScalarBinOp; simp only [hbeq0, hbeq_eq, h_eq, h_ble]
        · intro hks; rw [hks]; dsimp [Ord.compare, compareOfLessAndEq, decodeBitsInt]
          rw [nat_beq_eq_decide] at h_eq; rw [nat_ble_eq_decide] at h_ble
          simp only [decide_eq_false_iff_not, decide_eq_true_eq] at h_eq h_ble
          have h1 : (sc₁.bits : Int) < (sc₂.bits : Int) := by omega
          simp [h1]
    · refine ⟨⟨0, 1⟩, _, ?_, hmiri, ?_⟩
      · unfold evalScalarBinOp; simp only [hbeq0, hbeq_eq, h_eq]
      · intro hks; rw [hks]; dsimp [Ord.compare, compareOfLessAndEq, decodeBitsInt]
        rw [nat_beq_eq_decide] at h_eq
        simp only [decide_eq_true_eq] at h_eq
        simp [h_eq]
  · cases h_eq : Nat.beq sc₁.bits sc₂.bits
    · cases h_slt : signedLt sc₁.bits sc₂.bits sc₁.sizeBytes
      · refine ⟨⟨1, 1⟩, _, ?_, hmiri, ?_⟩
        · unfold evalScalarBinOp; simp only [hbeq0, hbeq_eq, hxMod, hyMod, h_eq, h_slt]
        · intro hks; rw [hks]; dsimp only [Ord.compare, compareOfLessAndEq]
          rw [nat_beq_eq_decide] at h_eq
          rw [signedLt_eq hrel₁.validBytes hx_bits hy_bits] at h_slt
          simp only [decide_eq_false_iff_not] at h_eq h_slt
          have h2 : ¬ (decodeBitsInt true sc₁.sizeBytes sc₁.bits = decodeBitsInt true sc₁.sizeBytes sc₂.bits) :=
            fun h => h_eq ((decodeBitsInt_inj hrel₁.validBytes hx_bits hy_bits).mp h)
          simp only [h_slt, h2, ↓reduceIte]
      · refine ⟨⟨255, 1⟩, _, ?_, hmiri, ?_⟩
        · unfold evalScalarBinOp; simp only [hbeq0, hbeq_eq, hxMod, hyMod, h_eq, h_slt]
        · intro hks; rw [hks]; dsimp only [Ord.compare, compareOfLessAndEq]
          rw [signedLt_eq hrel₁.validBytes hx_bits hy_bits] at h_slt
          simp only [decide_eq_true_eq] at h_slt
          simp only [h_slt, ↓reduceIte]
    · refine ⟨⟨0, 1⟩, _, ?_, hmiri, ?_⟩
      · unfold evalScalarBinOp; simp only [hbeq0, hbeq_eq, hxMod, hyMod, h_eq]
      · intro hks; rw [hks]; dsimp only [Ord.compare, compareOfLessAndEq]
        rw [nat_beq_eq_decide] at h_eq
        simp only [decide_eq_true_eq] at h_eq
        simp [h_eq]

/-- `Cmp` on same-width integers: when the `IntegerKind`'s signedness is
Anneal's `isSigned` flag, Anneal's 1-byte result is the `i8` encoding of the
`Ordering` that `lean-miri`'s `IntegerOps.binary .Cmp` returns. -/
theorem evalBinOp_cmp_simulation
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (locals : List LocalSlot) (mem : Memory)
    (isSigned : Bool) (kind : Miri.MIR.IntegerKind)
    (hsz : sc₁.sizeBytes = sc₂.sizeBytes)
    (hsigned : kind.signed = isSigned) :
    ∃ o : Ordering,
      evalScalarBinOp .cmp sc₁ sc₂ locals mem isSigned =
        .ok (.scalar ⟨orderingI8Bits o, 1⟩) locals mem ∧
      Miri.Interpreter.IntegerOps.binary .Cmp
        ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
        ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩ =
        .ok (.ordering o) := by
  obtain ⟨sc'', o, ha, hm, hsc⟩ :=
    evalBinOp_cmp_simulation_aux hrel₁ hrel₂ locals mem isSigned kind hsz
  refine ⟨o, ?_, hm⟩
  rw [ha, hsc hsigned]
  cases o <;> rfl

theorem scalar_fromInt_ordering (o : Ordering) :
    ∃ msc : Miri.Memory.ScalarInt,
      Miri.Memory.Scalar.fromInt (Prov := AnnealProv)
        (match o with | .lt => -1 | .eq => 0 | .gt => 1) (Miri.ABI.Size.ofBytes 1) =
        .ok (.fromScalarInt msc) ∧
      ScalarRel ⟨orderingI8Bits o, 1⟩ msc := by
  cases o
  · exact ⟨_, rfl, Or.inl rfl, by decide, rfl, rfl⟩
  · exact ⟨_, rfl, Or.inl rfl, by decide, rfl, rfl⟩
  · exact ⟨_, rfl, Or.inl rfl, by decide, rfl, rfl⟩

/-- `Cmp` through `ScalarOps.binary`: the `Ordering` is that of the operands'
decoded values, and `lean-miri`'s `i8` scalar result is `ScalarRel`-related to
Anneal's. -/
theorem scalarOps_cmp_simulation
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (locals : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    {ty : Ty} {kind : Miri.MIR.IntegerKind} (hty : IsIntegralTy ty kind)
    (hsz_ty : (translateTy ty layouts).layout.size = translateSizeBytes sc₁.sizeBytes)
    (hsz : sc₁.sizeBytes = sc₂.sizeBytes) :
    ∃ (o : Ordering) (msc'' : Miri.Memory.ScalarInt),
      o = compare (decodeBitsInt kind.signed sc₁.sizeBytes sc₁.bits)
        (decodeBitsInt kind.signed sc₁.sizeBytes sc₂.bits) ∧
      evalScalarBinOp .cmp sc₁ sc₂ locals mem (tyIsSigned ty) =
        .ok (.scalar ⟨orderingI8Bits o, 1⟩) locals mem ∧
      Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks localDecls layouts) () .Cmp
        ⟨.scalar (.fromScalarInt msc₁), translateTy ty layouts⟩
        ⟨.scalar (.fromScalarInt msc₂), translateTy ty layouts⟩ =
        .ok ⟨.scalar (.fromScalarInt msc''),
          translateTy { kind := .int .i8, layoutIdx := 0 } emptyLayoutTable⟩ ∧
      ScalarRel ⟨orderingI8Bits o, 1⟩ msc'' := by
  obtain ⟨o, ha, hm⟩ :=
    evalBinOp_cmp_simulation hrel₁ hrel₂ locals mem (tyIsSigned ty) kind hsz hty.signed_eq.symm
  have hsame := integerOps_binary_sameType_eq hrel₁ hrel₂ hsz kind .Cmp rfl
  dsimp only at hsame
  have ho : o = compare (decodeBitsInt kind.signed sc₁.sizeBytes sc₁.bits)
      (decodeBitsInt kind.signed sc₁.sizeBytes sc₂.bits) := by
    rw [hm] at hsame
    injection hsame with h
    injection h
  obtain ⟨msc'', hfrom, hrel''⟩ := scalar_fromInt_ordering o
  refine ⟨o, msc'', ho, ha, ?_, hrel''⟩
  have hsz₂ : (translateTy ty layouts).layout.size = translateSizeBytes sc₂.sizeBytes := by
    rw [← hsz]; exact hsz_ty
  funext st
  have hstep := scalarOps_binary_integer_step localDecls (bop := .cmp) hty hty hrel₁ hrel₂
    hsz_ty hsz₂ (Or.inr rfl) st
  have htr : translateBinOp .cmp = .Cmp := rfl
  rw [htr] at hstep
  rw [hstep, hm]
  dsimp only [liftScalarResult, Except.mapError, scalarOpsFinish, annealScalarOpsHooks,
    bind, pure, EStateM.bind, EStateM.pure]
  cases o <;> (dsimp only at hfrom ⊢; rw [hfrom]; rfl)

/-! ## 5. `CastKind.IntToInt` -/

theorem valid_bytes_pow_dvd {sz₁ sz₂ : Nat}
    (h : sz₁ ≤ sz₂) :
    ((2 : Int) ^ (8 * sz₁)) ∣ ((2 : Int) ^ (8 * sz₂)) := by
  have hdvdNat : (2 : Nat) ^ (8 * sz₁) ∣ (2 : Nat) ^ (8 * sz₂) :=
    Nat.pow_dvd_pow 2 (by omega)
  have hp₁ : (2 : Int) ^ (8 * sz₁) = ((2 ^ (8 * sz₁) : Nat) : Int) := by push_cast; rfl
  have hp₂ : (2 : Int) ^ (8 * sz₂) = ((2 ^ (8 * sz₂) : Nat) : Int) := by push_cast; rfl
  rw [hp₁, hp₂]
  exact_mod_cast hdvdNat

theorem signedCastBits_eq_decodeBitsInt_mod {srcBytes dstBytes x : Nat}
    (hsrc : ValidScalarBytes srcBytes) (_hdst : ValidScalarBytes dstBytes)
    (hx : x < 2 ^ (8 * srcBytes)) :
    (match Nat.ble dstBytes srcBytes with
      | true => wrapScalarBits x (scalarModulus dstBytes)
      | false => signExtendBits x srcBytes dstBytes) =
      (decodeBitsInt true srcBytes x % (2 : Int) ^ (8 * dstBytes)).toNat := by
  have hp_src : ((2 ^ (8 * srcBytes) : Nat) : Int) = (2 : Int) ^ (8 * srcBytes) := by push_cast; rfl
  have hp_dst : ((2 ^ (8 * dstBytes) : Nat) : Int) = (2 : Int) ^ (8 * dstBytes) := by push_cast; rfl
  cases hble : Nat.ble dstBytes srcBytes with
  | true =>
    have hle : dstBytes ≤ srcBytes := by
      rw [nat_ble_eq_decide] at hble
      exact of_decide_eq_true hble
    rw [wrap_eq_toNat]
    congr 1
    unfold decodeBitsInt
    simp only [↓reduceIte, hp_src]
    split
    · rfl
    · rw [Int.sub_emod, Int.emod_eq_zero_of_dvd (valid_bytes_pow_dvd hle),
        Int.sub_zero, Int.emod_emod]
  | false =>
    have hlt_bytes : srcBytes < dstBytes := by
      rw [nat_ble_eq_decide] at hble
      have := of_decide_eq_false hble
      omega
    have hpow_lt : 2 ^ (8 * srcBytes) < 2 ^ (8 * dstBytes) :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    unfold signExtendBits
    simp only [hble, scalarModulus_eq_two_pow,
      wrapScalarBits_eq_mod, Nat.mod_eq_of_lt hx, isSignedNegative_eq hsrc hx]
    unfold decodeBitsInt
    simp only [↓reduceIte, hp_src, ← hp_dst]
    by_cases hxH : 2 ^ (8 * srcBytes - 1) ≤ x
    · rw [decide_eq_true hxH]
      simp only [show ¬(x < 2 ^ (8 * srcBytes - 1)) by omega, ↓reduceIte, Nat.add_eq, Nat.sub_eq]
      rw [← hp_src]
      have hemod : ((x : Int) - ((2 ^ (8 * srcBytes) : Nat) : Int)) % ((2 ^ (8 * dstBytes) : Nat) : Int) =
          (x : Int) - ((2 ^ (8 * srcBytes) : Nat) : Int) + ((2 ^ (8 * dstBytes) : Nat) : Int) := by
        rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
      rw [hemod]
      omega
    · rw [decide_eq_false hxH]
      simp only [show x < 2 ^ (8 * srcBytes - 1) by omega, ↓reduceIte]
      have hlt_dst : (x : Int) < ((2 ^ (8 * dstBytes) : Nat) : Int) := by
        have : x < 2 ^ (8 * dstBytes) := Nat.lt_trans hx hpow_lt
        exact_mod_cast this
      rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) hlt_dst, Int.toNat_natCast]

theorem unsignedCastBits_eq_decodeBitsInt_mod (srcBytes dstBytes x : Nat) :
    wrapScalarBits x (scalarModulus dstBytes) =
      (decodeBitsInt false srcBytes x % (2 : Int) ^ (8 * dstBytes)).toNat := by
  have hp : ((2 ^ (8 * dstBytes) : Nat) : Int) = (2 : Int) ^ (8 * dstBytes) := by push_cast; rfl
  rw [wrapScalarBits_eq_mod, scalarModulus_eq_two_pow, decodeBitsInt_unsigned, ← hp, ← Int.natCast_emod, Int.toNat_natCast]

theorem integerCast_ofUInt128_eq (data : BitVec 128) (dstSize : Miri.ABI.Size)
    (dstKind : Miri.MIR.IntegerKind) :
    Miri.Interpreter.IntegerCast.cast
      (.integer ⟨Miri.ABI.Size.ofBytes 16, .u128⟩)
      (.ofUInt128 data)
      (.integer ⟨dstSize, dstKind⟩) =
      ((Miri.Memory.ScalarInt.truncateFromUInt data dstSize).mapError .scalar).map Prod.fst := by
  unfold Miri.Interpreter.IntegerCast.cast
  change (do
    let decoded ← Except.ok data.toNat
    let (result, _) ← Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofNat 128 decoded) dstSize
      |>.mapError Miri.Interpreter.IntegerCastError.scalar
    return result) = _
  simp only [bind, Except.bind, pure, Except.pure, BitVec.ofNat_toNat, BitVec.setWidth_eq, Except.map, Except.mapError]

theorem scalar_fromScalarInt_toBits_eq [Miri.Memory.PointerProvenance Prov]
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := Prov) msc).toBits (translateSizeBytes sc.sizeBytes) =
      .ok (BitVec.ofNat 128 sc.bits) := by
  have hzero : ((translateSizeBytes sc.sizeBytes).bytes == 0) = false := by
    have hv := hrel.validBytes
    rcases hv with h | h | h | h | h <;> (rw [h]; rfl)
  unfold Miri.Memory.Scalar.toBits
  have hts : (Miri.Memory.Scalar.fromScalarInt (Prov := Prov) msc).toScalarInt = .ok msc := rfl
  simp only [hzero, Bool.false_eq_true, ↓reduceIte, hts, hrel.toBits_eq,
    Except.mapError, bind, Except.bind]

theorem scalar_fromScalarInt_toInt_eq [Miri.Memory.PointerProvenance Prov]
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := Prov) msc).toInt (translateSizeBytes sc.sizeBytes) =
      .ok (decodeBitsInt true sc.sizeBytes sc.bits) := by
  unfold Miri.Memory.Scalar.toInt
  have htoNat := bitVec_ofNat_toNat_of_valid hrel.validBytes hrel.canonical
  have hlt : sc.bits < 2 ^ (8 * sc.sizeBytes) := by
    rw [← scalarModulus_eq_two_pow]; exact hrel.canonical
  simp only [scalar_fromScalarInt_toBits_eq hrel, size_signExtend_translateSizeBytes hrel.validBytes,
    htoNat, Nat.mod_eq_of_lt hlt, bind, Except.bind, Except.mapError]

/-- `Cast.intLikeValue` reads a `bool` or integer scalar as its value under the
source type's signedness (`tyIsSigned`), as a 128-bit pattern. -/
theorem intLikeValue_eq {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (layouts : LayoutTable) (srcTy : Ty)
    (hsrc : srcTy.kind = .bool ∨ (∃ k, srcTy.kind = .int k) ∨ (∃ k, srcTy.kind = .uint k))
    (hsz_src : sc.sizeBytes = match srcTy.kind with | .bool => 1 | .int k => k.byteWidth 64 | .uint k => k.byteWidth 64 | _ => sc.sizeBytes)
    (hbits_src : srcTy.kind = .bool → sc.bits = 0 ∨ sc.bits = 1) :
    Miri.Interpreter.Cast.intLikeValue (annealCastHooks layouts) ()
      (.fromScalarInt msc) (translateTy srcTy layouts) =
      pure (BitVec.ofInt 128 (decodeBitsInt (tyIsSigned srcTy) sc.sizeBytes sc.bits),
        tyIsSigned srcTy) := by
  rcases srcTy with ⟨kind, layoutIdx⟩
  rcases hsrc with rfl | ⟨k, rfl⟩ | ⟨uk, rfl⟩
  · have hb : ∃ b : Bool, sc = boolToScalar b ∧ msc = Miri.Memory.ScalarInt.ofBool b := by
      rcases sc with ⟨sc_bits, sc_size⟩
      rcases msc with ⟨msc_data, msc_size⟩
      have hsize := hrel.size_eq; have hdata := hrel.data_eq
      dsimp at hsz_src hsize hdata
      rcases hbits_src rfl with h0 | h1
      · dsimp at h0; subst h0 hsz_src; dsimp [translateSizeBytes] at hsize
        subst hsize hdata; exact ⟨false, rfl, rfl⟩
      · dsimp at h1; subst h1 hsz_src; dsimp [translateSizeBytes] at hsize
        subst hsize hdata; exact ⟨true, rfl, rfl⟩
    rcases hb with ⟨b, rfl, rfl⟩
    cases b <;> rfl
  · have hrepr : (translateTy { kind := .int k, layoutIdx := layoutIdx } layouts).layout.backendRepr.isSigned = .ok true := by
      cases k <;> rfl
    have hti : castTypeInfoOfEncodedTyId (translateTy { kind := .int k, layoutIdx := layoutIdx } layouts).ty = .ok (.integer (translateIntTy k)) := by
      cases k <;> rfl
    have hks : (translateIntTy k).signed = true := by
      cases k <;> rfl
    have hsz : (translateTy { kind := .int k, layoutIdx := layoutIdx } layouts).layout.size = translateSizeBytes sc.sizeBytes := by
      rw [hsz_src]; cases k <;> rfl
    funext s
    unfold Miri.Interpreter.Cast.intLikeValue
    dsimp only [annealCastHooks, tyIsSigned, bind, pure, EStateM.bind, EStateM.pure]
    rw [hrepr, hti, hsz]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hks]
    simp only [↓reduceIte, scalar_fromScalarInt_toInt_eq hrel, Except.mapError]
    rfl
  · have hrepr : (translateTy { kind := .uint uk, layoutIdx := layoutIdx } layouts).layout.backendRepr.isSigned = .ok false := by
      cases uk <;> rfl
    have hti : castTypeInfoOfEncodedTyId (translateTy { kind := .uint uk, layoutIdx := layoutIdx } layouts).ty = .ok (.integer (translateUintTy uk)) := by
      cases uk <;> rfl
    have hks : (translateUintTy uk).signed = false := by
      cases uk <;> rfl
    have hsz : (translateTy { kind := .uint uk, layoutIdx := layoutIdx } layouts).layout.size = translateSizeBytes sc.sizeBytes := by
      rw [hsz_src]; cases uk <;> rfl
    funext s
    unfold Miri.Interpreter.Cast.intLikeValue
    dsimp only [annealCastHooks, tyIsSigned, decodeBitsInt, bind, pure, EStateM.bind, EStateM.pure]
    rw [hrepr, hti, hsz]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hks]
    simp only [Bool.false_eq_true, ↓reduceIte, Miri.Memory.Scalar.toUInt,
      scalar_fromScalarInt_toBits_eq hrel, Except.mapError]
    rfl

/-- The `IntegerKind` of an integer `RigidTy` (`u8` for every other type). -/
private def dstIntKind (kind : RigidTy) : Miri.MIR.IntegerKind :=
  match kind with
  | .int k => translateIntTy k
  | .uint uk => translateUintTy uk
  | _ => .u8

/-- `CastKind.IntToInt` from a `bool` or integer operand to any integer type: Anneal
produces the source value (decoded with the source's signedness) reduced modulo
`2 ^ (8 * dstBytes)`, which is sign extension, zero extension, or truncation as
the widths dictate; `lean-miri`'s `castFromIntLike` produces a `ScalarRel`-related
scalar, and `Cast.cast` writes exactly that scalar to the destination. -/
theorem evalCast_intToInt_simulation
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc)
    {locals locals' : List LocalSlot} {mem : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {op : MirAst.Operand} {srcTy dstTy : Ty}
    (dest : Miri.Interpreter.RuntimePlace AnnealProv)
    (hop : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar sc) locals')
    (hopTy : operandTy localDecls layouts op = some srcTy)
    (hsrc : srcTy.kind = .bool ∨ (∃ k, srcTy.kind = .int k) ∨ (∃ k, srcTy.kind = .uint k))
    (hdst : (∃ k, dstTy.kind = .int k) ∨ (∃ k, dstTy.kind = .uint k))
    (hsz_src : sc.sizeBytes = match srcTy.kind with | .bool => 1 | .int k => k.byteWidth 64 | .uint k => k.byteWidth 64 | _ => sc.sizeBytes)
    (hbits_src : srcTy.kind = .bool → sc.bits = 0 ∨ sc.bits = 1)
    (h_dest : dest.layout = translateTy dstTy layouts) :
    ∃ msc',
      evalRvalue locals (.cast .intToInt op dstTy) mem localDecls layouts =
        .ok (.scalar ⟨(decodeBitsInt (tyIsSigned srcTy) sc.sizeBytes sc.bits %
          (2 : Int) ^ (8 * boolOrIntByteWidth dstTy)).toNat, boolOrIntByteWidth dstTy⟩) locals' mem ∧
      Miri.Interpreter.Cast.castFromIntLike (annealCastHooks layouts) ()
        (.fromScalarInt msc) (translateTy srcTy layouts) (translateTy dstTy layouts) =
        .ok ⟨.scalar (.fromScalarInt msc'), translateTy dstTy layouts⟩ ∧
      Miri.Interpreter.Cast.cast (annealCastHooks layouts) () 16
        ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩ .IntToInt
        (encodeTyId dstTy) dest =
        annealWriteImmediate (.scalar (.fromScalarInt msc')) dest ∧
      ScalarRel ⟨(decodeBitsInt (tyIsSigned srcTy) sc.sizeBytes sc.bits %
          (2 : Int) ^ (8 * boolOrIntByteWidth dstTy)).toNat, boolOrIntByteWidth dstTy⟩ msc' := by
  rcases dstTy with ⟨dk, dIdx⟩
  rcases dest with ⟨dRef, dLay⟩
  dsimp only at h_dest
  subst h_dest
  let dstBytes := boolOrIntByteWidth { kind := dk, layoutIdx := dIdx }
  let dKind := dstIntKind dk
  let val := decodeBitsInt (tyIsSigned srcTy) sc.sizeBytes sc.bits
  have hdst_valid : ValidScalarBytes dstBytes := by
    rcases hdst with ⟨k, rfl⟩ | ⟨uk, rfl⟩
    · cases k <;> (dsimp [dstBytes, boolOrIntByteWidth, ValidScalarBytes]; decide)
    · cases uk <;> (dsimp [dstBytes, boolOrIntByteWidth, ValidScalarBytes]; decide)
  have htargetBytes : intCastTargetBytes dk = some dstBytes := by
    rcases hdst with ⟨k, rfl⟩ | ⟨uk, rfl⟩
    · cases k <;> rfl
    · cases uk <;> rfl
  have hdst_size : (translateTy { kind := dk, layoutIdx := dIdx } layouts).layout.size = translateSizeBytes dstBytes := by
    rcases hdst with ⟨k, rfl⟩ | ⟨uk, rfl⟩
    · cases k <;> rfl
    · cases uk <;> rfl
  have hdst_ti : castTypeInfoOfEncodedTyId (translateTy { kind := dk, layoutIdx := dIdx } layouts).ty = .ok (.integer dKind) := by
    rcases hdst with ⟨k, rfl⟩ | ⟨uk, rfl⟩
    · cases k <;> rfl
    · cases uk <;> rfl
  have hdst_ti_enc : castTypeInfoOfEncodedTyId (encodeTyId { kind := dk, layoutIdx := dIdx }) = .ok (.integer dKind) := by
    rcases hdst with ⟨k, rfl⟩ | ⟨uk, rfl⟩
    · cases k <;> rfl
    · cases uk <;> rfl
  have hdst_ty_eq : (translateTy { kind := dk, layoutIdx := dIdx } layouts).ty = encodeTyId { kind := dk, layoutIdx := dIdx } := by
    rcases hdst with ⟨k, rfl⟩ | ⟨uk, rfl⟩
    · cases k <;> rfl
    · cases uk <;> rfl
  have hsrc_ti : ∃ info, castTypeInfoOfEncodedTyId (translateTy srcTy layouts).ty = .ok info ∧
      (info = .boolean ∨ ∃ sk, info = .integer sk) := by
    rcases srcTy with ⟨sk, sIdx⟩
    rcases hsrc with rfl | ⟨k, rfl⟩ | ⟨uk, rfl⟩
    · exact ⟨.boolean, rfl, Or.inl rfl⟩
    · refine ⟨.integer (translateIntTy k), ?_, Or.inr ⟨_, rfl⟩⟩; cases k <;> rfl
    · refine ⟨.integer (translateUintTy uk), ?_, Or.inr ⟨_, rfl⟩⟩; cases uk <;> rfl
  have hop_signed : operandIsSigned localDecls op layouts = tyIsSigned srcTy := by
    simp [operandIsSigned, hopTy]
  obtain ⟨msc', hmsc', hrel'⟩ := truncateFromUInt_ofInt_translateSizeBytes_spec hdst_valid val
  have hcastFrom : Miri.Interpreter.Cast.castFromIntLike (annealCastHooks layouts) ()
      (.fromScalarInt msc) (translateTy srcTy layouts) (translateTy { kind := dk, layoutIdx := dIdx } layouts) =
      .ok ⟨.scalar (.fromScalarInt msc'), translateTy { kind := dk, layoutIdx := dIdx } layouts⟩ := by
    funext s
    unfold Miri.Interpreter.Cast.castFromIntLike
    rw [intLikeValue_eq hrel layouts srcTy hsrc hsz_src hbits_src]
    dsimp only [annealCastHooks, bind, pure, EStateM.bind, EStateM.pure]
    rw [hdst_ti]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hdst_size]
    have hic := integerCast_ofUInt128_eq (BitVec.ofInt 128 val) (translateSizeBytes dstBytes) dKind
    rw [hic, hmsc']
    rfl
  refine ⟨msc', ?_, hcastFrom, ?_, hrel'⟩
  · unfold evalRvalue
    dsimp only
    rw [hop]
    dsimp only
    rw [hrel.beq_sizeBytes_zero, htargetBytes, hop_signed]
    have hx_lt : sc.bits < 2 ^ (8 * sc.sizeBytes) := by
      rw [← scalarModulus_eq_two_pow]; exact hrel.canonical
    cases hs : tyIsSigned srcTy
    · dsimp only [val]
      exact congrArg (fun b => RvalueEvalResult.ok (.scalar ⟨b, dstBytes⟩) locals' mem)
        (unsignedCastBits_eq_decodeBitsInt_mod sc.sizeBytes dstBytes sc.bits)
    · dsimp only [val]
      exact congrArg (fun b => RvalueEvalResult.ok (.scalar ⟨b, dstBytes⟩) locals' mem)
        (signedCastBits_eq_decodeBitsInt_mod hrel.validBytes hdst_valid hx_lt)
  · unfold Miri.Interpreter.Cast.cast
    rcases hsrc_ti with ⟨sInfo, hsInfo, hboolOrInt⟩
    rcases hboolOrInt with rfl | ⟨sk, rfl⟩ <;> (
      simp only [annealCastHooks, annealReadImmediate, hdst_ty_eq, beq_self_eq_true,
        Bool.false_eq_true, ↓reduceIte, hsInfo, hdst_ti_enc, pure_bind]
      with_unfolding_all
        change
          (do
            let result ←
              Miri.Interpreter.Cast.castFromIntLike (annealCastHooks layouts) ()
                (.fromScalarInt msc) (translateTy srcTy layouts)
                (translateTy { kind := dk, layoutIdx := dIdx } layouts)
            annealWriteImmediate result.imm
              { ref := dRef, layout := translateTy { kind := dk, layoutIdx := dIdx } layouts }) = _
      rw [hcastFrom]
      rfl
    )

/-- `Cast.cast` reports UB on an uninitialized `bool`/integer source, as Anneal's
`evalOperand` does. -/
theorem cast_intToInt_uninit (layouts : LayoutTable) (srcTy dstTy : Ty)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv)
    (hsrc : srcTy.kind = .bool ∨ (∃ k, srcTy.kind = .int k) ∨ (∃ k, srcTy.kind = .uint k))
    (hdst : (∃ k, dstTy.kind = .int k) ∨ (∃ k, dstTy.kind = .uint k))
    (h_dest : dest.layout = translateTy dstTy layouts) (st : AnnealStepState) :
    Miri.Interpreter.Cast.cast (annealCastHooks layouts) () 16
      ⟨.immediate .uninit, translateTy srcTy layouts⟩ .IntToInt (encodeTyId dstTy) dest st =
      .error (.undefinedBehavior "read of uninitialized local") st := by
  rcases dstTy with ⟨dk, dIdx⟩
  rcases dest with ⟨dRef, dLay⟩
  dsimp only at h_dest
  subst h_dest
  have hdst_ty_eq : (translateTy { kind := dk, layoutIdx := dIdx } layouts).ty = encodeTyId { kind := dk, layoutIdx := dIdx } := by
    rcases hdst with ⟨k, rfl⟩ | ⟨uk, rfl⟩
    · cases k <;> rfl
    · cases uk <;> rfl
  have hsrc_ti : ∃ info, castTypeInfoOfEncodedTyId (translateTy srcTy layouts).ty = .ok info ∧
      (info = .boolean ∨ ∃ sk, info = .integer sk) := by
    rcases srcTy with ⟨sk, sIdx⟩
    rcases hsrc with rfl | ⟨k, rfl⟩ | ⟨uk, rfl⟩
    · exact ⟨.boolean, rfl, Or.inl rfl⟩
    · refine ⟨.integer (translateIntTy k), ?_, Or.inr ⟨_, rfl⟩⟩; cases k <;> rfl
    · refine ⟨.integer (translateUintTy uk), ?_, Or.inr ⟨_, rfl⟩⟩; cases uk <;> rfl
  unfold Miri.Interpreter.Cast.cast
  rcases hsrc_ti with ⟨sInfo, hsInfo, hboolOrInt⟩
  rcases hboolOrInt with rfl | ⟨sk, rfl⟩ <;> (
    simp only [annealCastHooks, annealReadImmediate, hdst_ty_eq, beq_self_eq_true,
      Bool.false_eq_true, ↓reduceIte, hsInfo, pure_bind]
    rfl)

/-! ## 6. `SwitchInt` -/

theorem scalar_fromUInt_translateSizeBytes_spec {sz : Nat} (hsz : ValidScalarBytes sz)
    {caseVal : Nat} (hcase_lt : caseVal < scalarModulus sz) :
    ∃ msc₂ : Miri.Memory.ScalarInt,
      Miri.Memory.Scalar.fromUInt (Prov := AnnealProv) (BitVec.ofNat 128 caseVal) (translateSizeBytes sz) =
        .ok (.fromScalarInt msc₂) ∧
      ScalarRel ⟨caseVal, sz⟩ msc₂ := by
  obtain ⟨msc₂, hmsc₂, hrel₂⟩ := truncateFromUInt_translateSizeBytes_spec hsz (BitVec.ofNat 128 caseVal)
  have hmod : (BitVec.ofNat 128 caseVal).toNat % 2 ^ (8 * sz) = caseVal := by
    rw [bitVec_ofNat_toNat_of_valid hsz hcase_lt, ← scalarModulus_eq_two_pow]
    exact Nat.mod_eq_of_lt hcase_lt
  rw [hmod, bne_self_eq_false] at hmsc₂
  rw [hmod] at hrel₂
  refine ⟨msc₂, ?_, hrel₂⟩
  unfold Miri.Memory.Scalar.fromUInt Miri.Memory.ScalarInt.tryFromUInt
  change (do
    let scalar ← (do
      let (result, overflow) ← Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofNat 128 caseVal) (translateSizeBytes sz)
      if overflow then return none else return some result) |>.mapError _
    match scalar with
    | some scalar => return Miri.Memory.Scalar.fromScalarInt scalar
    | none => throw _) = _
  rw [hmsc₂]
  rfl

/-- `annealTerminatorHooks.compareSwitchCase` (MIR `Eq` against a same-layout
`ImmTy::from_uint`, then `to_bool`) answers `Nat.beq sc.bits caseVal` without
changing the state, for every case value that fits the discriminant. -/
theorem compareSwitchCase_simulation
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (ty : Ty) (hty : ty.kind = .bool ∨ (∃ k, ty.kind = .int k) ∨ (∃ k, ty.kind = .uint k))
    (hsz_ty : sc.sizeBytes = match ty.kind with | .bool => 1 | .int k => k.byteWidth 64 | .uint k => k.byteWidth 64 | _ => sc.sizeBytes)
    (hbits : ty.kind = .bool → sc.bits = 0 ∨ sc.bits = 1)
    (caseVal : Nat)
    (hcase_lt : caseVal < scalarModulus sc.sizeBytes)
    (hcase_bool : ty.kind = .bool → caseVal = 0 ∨ caseVal = 1)
    (state : AnnealStepState) :
    (annealTerminatorHooks localDecls layouts).compareSwitchCase ()
      ⟨.scalar (.fromScalarInt msc), translateTy ty layouts⟩ caseVal state =
      (state, .ok (Nat.beq sc.bits caseVal)) := by
  have hlay_sz : (translateTy ty layouts).layout.size = translateSizeBytes sc.sizeBytes := by
    rcases ty with ⟨tk, tIdx⟩
    dsimp only at hty hsz_ty
    rw [hsz_ty]
    rcases hty with rfl | ⟨k, rfl⟩ | ⟨uk, rfl⟩
    · rfl
    · cases k <;> rfl
    · cases uk <;> rfl
  obtain ⟨msc₂, hmsc₂, hrel₂⟩ := scalar_fromUInt_translateSizeBytes_spec hrel.validBytes hcase_lt
  obtain ⟨b, hevalEq, hmiriEq⟩ :=
    evalBinOp_rel_simulation .eq (Or.inl rfl) hrel hrel₂ [] {} localDecls layouts ty hty rfl hsz_ty hbits hcase_bool .Eq rfl
  have hb : b = Nat.beq sc.bits caseVal := by
    unfold evalScalarBinOp at hevalEq
    have hbeq0 : sc.sizeBytes.beq 0 = false := hrel.beq_sizeBytes_zero
    have hbeq_sz : sc.sizeBytes.beq sc.sizeBytes = true := Nat.beq_refl _
    simp only [hbeq0, hbeq_sz] at hevalEq
    injection hevalEq with hval _ _
    injection hval with hsc
    unfold boolToScalar at hsc
    cases b <;> cases h : Nat.beq sc.bits caseVal <;> simp [h] at hsc <;> rfl
  subst hb
  unfold annealTerminatorHooks Miri.Interpreter.runRvalue
  dsimp only [bind, pure, EStateM.bind, EStateM.pure]
  rw [hlay_sz, hmsc₂]
  dsimp only [EStateM.bind, EStateM.pure]
  have hmiriEq' := congrFun hmiriEq state
  rw [hmiriEq']
  dsimp only [EStateM.bind, EStateM.pure, Miri.Interpreter.Immediate.toScalar]
  cases Nat.beq sc.bits caseVal <;> rfl

/-- `lean-miri`'s `SwitchInt` case loop, abstracted over its body `f`: if each case
`Case v b` stops with target `b` when `bits = v` and continues otherwise, leaving
the state unchanged, the loop selects `lookupSwitchTarget bits cases tgt`. -/
theorem switchCases_forIn_eq {R σ : Type}
    (f : Miri.MIR.SwitchTarget → Option R × σ × Nat → Id (ForInStep (Option R × σ × Nat)))
    (bits : Nat) (st : σ) :
    ∀ (cases : List (Nat × Nat)) (tgt : Nat),
      (∀ v b, (v, b) ∈ cases → ∀ t, f (.Case v b) (none, st, t) =
          if Nat.beq bits v then ForInStep.done (none, st, b) else ForInStep.yield (none, st, t)) →
      forIn (cases.map fun c => Miri.MIR.SwitchTarget.Case c.1 c.2) (none, st, tgt) f =
        (none, st, lookupSwitchTarget bits cases tgt) := by
  intro cases
  induction cases with
  | nil => intro tgt _; rfl
  | cons hd tl ih =>
    intro tgt hf
    rcases hd with ⟨v, b⟩
    rw [List.map_cons, List.forIn_cons]
    have hfv := hf v b List.mem_cons_self tgt
    dsimp only
    rw [hfv]
    unfold lookupSwitchTarget
    cases hbeq : Nat.beq bits v
    · exact ih tgt (fun v' b' hmem t => hf v' b' (List.mem_cons_of_mem _ hmem) t)
    · rfl

theorem translateSwitchTargets_cases (targets : SwitchTargets) :
    (translateSwitchTargets targets).cases =
      (targets.branches.map fun c => Miri.MIR.SwitchTarget.Case c.1 c.2).toArray := rfl

/-- `ControlFlow.evalTerminator` on a translated `SwitchInt`: after the
discriminant evaluates to `value`, comparing every case like `Nat.beq bits v`
jumps to Anneal's `lookupSwitchTarget bits branches otherwise`, including the
fallback to `otherwise` when no case matches. -/
theorem evalTerminator_switchInt_ok
    {P L E M C Op Imm : Type}
    (hooks : Miri.Interpreter.TerminatorHooks P L E M C Op Imm) (choice : C)
    (si : Miri.MIR.SourceInfo) (discr : Miri.MIR.Operand) (targets : SwitchTargets)
    (state state' : Miri.Interpreter.StepState P L E M) (value : Imm) (bits : Nat)
    (hdisc : hooks.evalDiscriminant choice discr state = (state', .ok value))
    (hcmp : ∀ v b, (v, b) ∈ targets.branches →
      hooks.compareSwitchCase choice value v state' = (state', .ok (Nat.beq bits v))) :
    Miri.Interpreter.ControlFlow.evalTerminator hooks choice
        { sourceInfo := si, kind := .SwitchInt discr (translateSwitchTargets targets) } state =
      Miri.Interpreter.ControlFlow.goToBlock
        (lookupSwitchTarget bits targets.branches targets.otherwise) state' := by
  unfold Miri.Interpreter.ControlFlow.evalTerminator
  simp only [hdisc]
  dsimp only [Id.run]
  rw [translateSwitchTargets_cases]
  simp only [List.forIn_toArray, pure_bind]
  rw [switchCases_forIn_eq _ bits state' targets.branches (translateSwitchTargets targets).otherwise]
  · rfl
  · intro v b hmem t
    simp only [hcmp v b hmem]
    cases Nat.beq bits v <;> rfl

/-- A failing discriminant evaluation aborts `SwitchInt` with its error. -/
theorem evalTerminator_switchInt_error
    {P L E M C Op Imm : Type}
    (hooks : Miri.Interpreter.TerminatorHooks P L E M C Op Imm) (choice : C)
    (si : Miri.MIR.SourceInfo) (discr : Miri.MIR.Operand) (targets : Miri.MIR.SwitchTargets)
    (state state' : Miri.Interpreter.StepState P L E M) (err : Miri.Interpreter.StepError)
    (hdisc : hooks.evalDiscriminant choice discr state = (state', .error err)) :
    Miri.Interpreter.ControlFlow.evalTerminator hooks choice
        { sourceInfo := si, kind := .SwitchInt discr targets } state = (state', .error err) := by
  unfold Miri.Interpreter.ControlFlow.evalTerminator
  simp only [hdisc]
  rfl

/-- Well-formed `SwitchInt` case values for a discriminant of type `ty`: each fits
in `ty`'s width, and a `bool` discriminant is only compared against `0`/`1`. -/
def SwitchCasesFit (ty : Ty) (targets : SwitchTargets) : Prop :=
  ∀ v b, (v, b) ∈ targets.branches →
    v < scalarModulus (boolOrIntByteWidth ty) ∧ (ty.kind = .bool → v = 0 ∨ v = 1)

/-- `SwitchInt` step simulation: from `StateRel`-related states, a `SwitchInt` on a
well-typed `bool` or integer operand steps both machines in lockstep to the same
target block (Anneal emitting `MirObs.event` with the discriminant bits), or
both report UB when the discriminant read is UB. -/
theorem step_terminator_switchInt_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {discr : MirAst.Operand} {targets : SwitchTargets} {ty : Ty}
    (hterm : bb.terminator.kind = .switchInt discr targets)
    (hty : ty.kind = .bool ∨ (∃ k, ty.kind = .int k) ∨ (∃ k, ty.kind = .uint k))
    (hdiscr : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame discr ty)
    (hcases : SwitchCasesFit ty targets) :
    StepObsRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by
    simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [miri_step_at_terminator hframes hframe.body_eq hframe.location_eq hbb hstmt_none]
  have hop_sim := evalOperand_scalar_simulation hframes hframe (hdiscr topFrame hframes)
    s.memory.globals none
  have hm_term : translateTerminator bb.terminator =
      { sourceInfo := defaultSourceInfo,
        kind := .SwitchInt (translateOperand discr) (translateSwitchTargets targets) } := by
    unfold translateTerminator; rw [hterm]; rfl
  have hdisc_eq : (annealTerminatorHooks body.localDecls body.layouts).evalDiscriminant ()
      (translateOperand discr) m =
      Miri.Interpreter.runRvalue
        (annealEvalOperand body.localDecls body.layouts (translateOperand discr) none >>=
          annealReadImmediate) m := rfl
  unfold evalTerminator
  rw [hterm]
  dsimp only
  rw [hbor, hcaller, hm_term]
  generalize ha_op : evalOperand s.frame.locals discr .nil s.memory.globals body.layouts .nil = aOp
    at hop_sim
  generalize hm_op : (annealEvalOperand body.localDecls body.layouts (translateOperand discr) none >>=
    annealReadImmediate) m = mOp at hop_sim
  cases hop_sim with
  | ub m' msg =>
    have hdisc : (annealTerminatorHooks body.localDecls body.layouts).evalDiscriminant ()
        (translateOperand discr) m = (m', .error (.undefinedBehavior msg)) := by
      rw [hdisc_eq]; unfold Miri.Interpreter.runRvalue; rw [hm_op]
    rw [evalTerminator_switchInt_error _ () _ _ _ m m' _ hdisc]
    exact StepObsRel.ub m' msg
  | ok v locals' topFrame' imm hframe' himm _ htf' =>
    have hprim : ty.kind = .bool ∨ ty.kind = .char ∨
        (∃ it, ty.kind = .int it) ∨ (∃ ut, ty.kind = .uint ut) := by
      rcases hty with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    obtain ⟨sc, msc, rfl, rfl, hrel, hsz, hbool, _⟩ := himm.of_primitive_scalar hprim
    have hdisc : (annealTerminatorHooks body.localDecls body.layouts).evalDiscriminant ()
        (translateOperand discr) m =
        ({ m with stack := ⟨#[topFrame']⟩ },
          .ok ⟨.scalar (.fromScalarInt msc), translateTy ty body.layouts⟩) := by
      rw [hdisc_eq]; unfold Miri.Interpreter.runRvalue; rw [hm_op]
    obtain ⟨hwsz, hwvalid⟩ := boolOrInt_translateTy_size hty body.layouts
    have hwidth : sc.sizeBytes = boolOrIntByteWidth ty :=
      translateSizeBytes_inj hrel.validBytes hwvalid (by rw [← hsz, hwsz])
    have hsz_ty : sc.sizeBytes = match ty.kind with
        | .bool => 1 | .int k => k.byteWidth 64 | .uint k => k.byteWidth 64 | _ => sc.sizeBytes := by
      rw [hwidth]
      rcases ty with ⟨tk, tIdx⟩
      rcases hty with h | ⟨k, h⟩ | ⟨k, h⟩ <;> dsimp only at h <;> subst h <;> rfl
    have hbits : ty.kind = .bool → sc.bits = 0 ∨ sc.bits = 1 := fun h => (hbool h).2
    have hcmp : ∀ v b, (v, b) ∈ targets.branches →
        (annealTerminatorHooks body.localDecls body.layouts).compareSwitchCase ()
          ⟨.scalar (.fromScalarInt msc), translateTy ty body.layouts⟩ v
          { m with stack := ⟨#[topFrame']⟩ } =
        ({ m with stack := ⟨#[topFrame']⟩ }, .ok (Nat.beq sc.bits v)) := by
      intro v b hmem
      obtain ⟨hlt, hcase_bool⟩ := hcases v b hmem
      rw [← hwidth] at hlt
      exact compareSwitchCase_simulation hrel body.localDecls body.layouts ty hty hsz_ty hbits
        v hlt hcase_bool _
    rw [evalTerminator_switchInt_ok _ () _ _ _ m _ _ sc.bits hdisc hcmp]
    unfold Miri.Interpreter.ControlFlow.goToBlock Miri.Interpreter.ControlFlow.setLocation
    rw [stack_currentFrame?_singleton _ topFrame' rfl]
    dsimp only [Except.map]
    apply StepObsRel.emitStep
    have hrc' : topFrame'.returnContinuation = .stop false := by rw [htf']; exact hretCont
    have hrp' : topFrame'.returnPlace =
        .frameLocal 0 0 none retLay topFrame'.localsIdentity := by rw [htf']; exact hretPlace
    exact StateRel.mk
      { topFrame' with location := .mir ⟨lookupSwitchTarget sc.bits targets.branches targets.otherwise, 0⟩ }
      rfl hrc' ⟨retLay, hrp'⟩
      ⟨hframe'.body_eq, rfl, hframe'.af_locals_len, hframe'.mf_locals_size, hframe'.locals_rel⟩
      hcal hstack hbor hprot hcaller

/-! ## 7. Statement Simulation for `bool` Comparisons and `IntToInt` Casts -/

/-- Joint outcome of Anneal's `evalOperand` and `lean-miri`'s `annealEvalOperand`
before `annealReadImmediate`, for consumers such as `Cast.cast` that read the
`OpTy` themselves. An uninitialized immediate local is UB in Anneal and an
`.uninit` operand in `lean-miri`. -/
inductive OperandOpTySimRel
    (body : CapturedMir) (af : StackFrame)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (m : AnnealStepState) (ty : Ty) :
    PlaceReadResult →
    EStateM.Result Miri.Interpreter.StepError AnnealStepState (Miri.Interpreter.OpTy AnnealProv) →
    Prop where
  | ok (v : Value) (locals' : List LocalSlot)
      (topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (imm : Miri.Interpreter.Immediate AnnealProv) :
      FrameRel body m.machine { af with locals := locals' } topFrame' →
      ImmediateRel ty body.layouts v imm →
      (∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame' j) →
      topFrame' = { topFrame with locals := topFrame'.locals } →
      OperandOpTySimRel body af topFrame m ty
        (.ok v locals')
        (.ok ⟨.immediate imm, translateTy ty body.layouts⟩ { m with stack := ⟨#[topFrame']⟩ })
  | uninit (m' : AnnealStepState) :
      OperandOpTySimRel body af topFrame m ty
        .ub (.ok ⟨.immediate .uninit, translateTy ty body.layouts⟩ m')
  | ub (m' : AnnealStepState) (msg : String) :
      OperandOpTySimRel body af topFrame m ty
        .ub (.error (.undefinedBehavior msg) m')

/-- `OperandOpTySimRel` holds for every well-typed scalar operand. -/
theorem evalOperand_scalar_simulation_opTy
    {body : CapturedMir} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m : AnnealStepState} {op : MirAst.Operand} {ty : Ty}
    (hframes : m.stack.frames = #[topFrame])
    (hframe : FrameRel body m.machine af topFrame)
    (hop : WellTypedScalarOperand body topFrame op ty)
    (globals : List CapturedAllocation)
    (known : Option Miri.Interpreter.LocalLayout) :
    OperandOpTySimRel body af topFrame m ty
      (evalOperand af.locals op .nil globals body.layouts .nil)
      (annealEvalOperand body.localDecls body.layouts (translateOperand op) known m) := by
  have hsame : { m with stack := ⟨#[topFrame]⟩ } = m :=
    stepState_with_same_singleton m topFrame hframes
  cases hop with
  | constScalar c sc hval hprim hsz hcan hlaysz hbool hchar =>
    obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
    have heval_a : evalOperand af.locals (.constant c) .nil globals body.layouts .nil =
        .ok (.scalar sc) af.locals := by
      unfold evalOperand
      dsimp only
      rw [hval]; rfl
    have heval_m : annealEvalOperand body.localDecls body.layouts
        (translateOperand (.constant c)) known m =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩ m := by
      with_unfolding_all
        unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
        dsimp only
        rw [hval]
        simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
          EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          stack_currentFrame?_singleton m.stack topFrame hframes, Option.isNone_some,
          Bool.false_eq_true, ↓reduceIte, htry, hprim.layoutOfEncoded]
    rw [heval_a, heval_m]
    conv => rhs; rw [← hsame]
    exact .ok (.scalar sc) af.locals topFrame (.scalar (.fromScalarInt msc))
      hframe (.scalar sc msc hrel hlaysz hbool hchar) (fun _ h => h) rfl
  | copyLocal idx decl hdecl hsz_nz himm =>
    obtain ⟨slot, mls, _, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
    have hcache := hloc.layout_eq
    have himm' := himm mls hmls
    have htr : translateOperand (.copy ⟨idx, .nil⟩) = .Copy ⟨idx, #[]⟩ := rfl
    rw [htr]
    cases hloc with
    | dead cachedLayout _ =>
      have ha : evalOperand af.locals (.copy ⟨idx, .nil⟩) .nil globals body.layouts .nil = .ub := by
        simp [evalOperand, hslot]
      rw [ha, annealEvalOperand_copy_dead hframes hlt_mf hdecl hmls_eq hcache]
      exact .ub _ _
    | indirect _ mp _ _ _ _ =>
      exact False.elim (himm' mp rfl)
    | immediate _ imm cachedLayout _ hval =>
      rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
      · have ha : evalOperand af.locals (.copy ⟨idx, .nil⟩) .nil globals body.layouts .nil = .ub := by
          simp [evalOperand, hslot]
        rw [ha, annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache]
        exact .uninit _
      · have ha : evalOperand af.locals (.copy ⟨idx, .nil⟩) .nil globals body.layouts .nil =
            .ok v af.locals := by
          simp [evalOperand, readProjectedValue, hslot]
        rw [ha, annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache]
        exact .ok v af.locals _ imm
          (hframe.cache_local_layout hdecl hlt_mf)
          himmRel
          (fun _ hj => hj.cache_layout hlt_mf _)
          rfl

/-- A relational operator on `bool` operands, evaluated as in `evalRvalueIntoPlace`
(`ScalarOps.binary`, then the destination layout check), agrees with Anneal and
yields an `ImmediateRel`-related `bool`. -/
theorem scalarOps_binary_boolCmp_simulation
    {body : CapturedMir} {locals₂ : List LocalSlot} {mem : Memory}
    {m₂ : AnnealStepState}
    {bop : MirAst.BinOp} {lhsOp : MirAst.Operand} {lhsTy rhsTy dstTy : Ty}
    {v₁ v₂ : Value} {imm₁ imm₂ : Miri.Interpreter.Immediate AnnealProv}
    (hbop : IsCmpBinOp bop)
    (hlhs_op : operandTy body.localDecls body.layouts lhsOp = some lhsTy)
    (hlhs : lhsTy.kind = .bool) (hrhs : rhsTy.kind = .bool) (hdst : dstTy.kind = .bool)
    (himm₁ : ImmediateRel lhsTy body.layouts v₁ imm₁)
    (himm₂ : ImmediateRel rhsTy body.layouts v₂ imm₂) :
    ∃ v₁_sc v₂_sc,
      v₁ = .scalar v₁_sc ∧ v₂ = .scalar v₂_sc ∧
      BinaryRvalueSimRel dstTy body.layouts locals₂ mem m₂
        (evalScalarBinOp bop v₁_sc v₂_sc locals₂ mem
          (operandIsSigned body.localDecls lhsOp body.layouts))
        ((do
          let result ← Miri.Interpreter.ScalarOps.binary
            (annealScalarOpsHooks body.localDecls body.layouts) ()
            (translateBinOp bop)
            ⟨imm₁, translateTy lhsTy body.layouts⟩
            ⟨imm₂, translateTy rhsTy body.layouts⟩
          assertRvalueLayoutPub result.layout (translateTy dstTy body.layouts)
          pure result.imm) m₂) := by
  have hisSigned : operandIsSigned body.localDecls lhsOp body.layouts = tyIsSigned lhsTy := by
    simp [operandIsSigned, hlhs_op]
  obtain ⟨sc₁, msc₁, rfl, rfl, hrel₁, _, hbool₁, _⟩ := himm₁.of_primitive_scalar (Or.inl hlhs)
  obtain ⟨sc₂, msc₂, rfl, rfl, hrel₂, _, hbool₂, _⟩ := himm₂.of_primitive_scalar (Or.inl hrhs)
  obtain ⟨hsz₁, hbits₁⟩ := hbool₁ hlhs
  obtain ⟨hsz₂, hbits₂⟩ := hbool₂ hrhs
  refine ⟨sc₁, sc₂, rfl, rfl, ?_⟩
  rw [hisSigned]
  have hrhsTy : translateTy rhsTy body.layouts = translateTy lhsTy body.layouts := by
    rw [translateTy_bool_eq hrhs, translateTy_bool_eq hlhs]
  rw [hrhsTy]
  have hsz_ty : sc₁.sizeBytes = match lhsTy.kind with
      | .bool => 1 | .int k => k.byteWidth 64 | .uint k => k.byteWidth 64 | _ => sc₁.sizeBytes := by
    rw [hlhs]; exact hsz₁
  obtain ⟨b, ha, hm⟩ := evalBinOp_rel_simulation bop hbop hrel₁ hrel₂ locals₂ mem
    body.localDecls body.layouts lhsTy (Or.inl hlhs) (hsz₁.trans hsz₂.symm) hsz_ty
    (fun _ => hbits₁) (fun _ => hbits₂) (translateBinOp bop) rfl
  rw [ha]
  have hdstTy : translateTy dstTy body.layouts =
      translateTy { kind := .bool, layoutIdx := 0 } emptyLayoutTable :=
    translateTy_bool_eq hdst body.layouts
  have hcomp : (do
      let result ← Miri.Interpreter.ScalarOps.binary
        (annealScalarOpsHooks body.localDecls body.layouts) ()
        (translateBinOp bop)
        ⟨.scalar (.fromScalarInt msc₁), translateTy lhsTy body.layouts⟩
        ⟨.scalar (.fromScalarInt msc₂), translateTy lhsTy body.layouts⟩
      assertRvalueLayoutPub result.layout (translateTy dstTy body.layouts)
      pure result.imm : Miri.Interpreter.RvalueM AnnealStepState _) m₂ =
      .ok (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofBool b))) m₂ := by
    rw [EStateM.bind_eq_ok (congrFun hm m₂)]
    dsimp only
    rw [EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ hdstTy.symm m₂)]
    rfl
  rw [hcomp]
  refine .ok _ _ (.scalar (boolToScalar b) (Miri.Memory.ScalarInt.ofBool b)
    (ScalarRel.of_boolToScalar b) ?_ ?_ ?_)
  · rw [hdstTy]; cases b <;> rfl
  · intro _; cases b <;> simp [boolToScalar]
  · intro hc; rw [hdst] at hc; cases hc

/-- `LM-1.2` scalar statements outside `LM-1.1`'s `WellTypedScalarStmt`. -/
inductive WellTypedLM12Stmt
    (body : CapturedMir)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    MirAst.Statement → Prop where
  /-- `_d = Op(lhs, rhs)` for `Op ∈ {Eq, Ne, Lt, Le, Gt, Ge}` on `bool` operands. -/
  | boolCmp (stmt : Statement) (dstIdx : Local) (dstDecl : LocalDecl) (bop : MirAst.BinOp)
      (lhsOp rhsOp : MirAst.Operand) (lhsTy rhsTy : Ty) :
      stmt.kind = .assign ⟨dstIdx, .nil⟩ (.binaryOp bop lhsOp rhsOp) →
      get? body.localDecls dstIdx = some dstDecl →
      IsImmediateFrameLocal topFrame dstIdx →
      IsCmpBinOp bop →
      WellTypedScalarOperand body topFrame lhsOp lhsTy →
      WellTypedScalarOperand body topFrame rhsOp rhsTy →
      lhsTy.kind = .bool → rhsTy.kind = .bool → dstDecl.ty.kind = .bool →
      WellTypedLM12Stmt body topFrame stmt
  /-- `_d = op as T (IntToInt)` from a `bool` or integer operand to an integer `T`. -/
  | intToInt (stmt : Statement) (dstIdx : Local) (dstDecl : LocalDecl)
      (op : MirAst.Operand) (srcTy : Ty) :
      stmt.kind = .assign ⟨dstIdx, .nil⟩ (.cast .intToInt op dstDecl.ty) →
      get? body.localDecls dstIdx = some dstDecl →
      IsImmediateFrameLocal topFrame dstIdx →
      WellTypedScalarOperand body topFrame op srcTy →
      (srcTy.kind = .bool ∨ (∃ k, srcTy.kind = .int k) ∨ (∃ k, srcTy.kind = .uint k)) →
      ((∃ k, dstDecl.ty.kind = .int k) ∨ (∃ k, dstDecl.ty.kind = .uint k)) →
      WellTypedLM12Stmt body topFrame stmt

/-- Statement step simulation for `WellTypedLM12Stmt`: assigning a `bool`
comparison or an `IntToInt` cast to an immediate local steps both machines to
`StateRel`-related states, or both report UB. -/
theorem step_assign_lm1_2_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] → WellTypedLM12Stmt body topFrame stmt) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot
    generalize s.memory = mem
    intro hbor hprot
    cases mem
    dsimp only at hbor hprot
    subst hbor hprot
    rfl
  dsimp only at hmem_same
  cases hwt topFrame hframes with
  | boolCmp dstIdx dstDecl bop lhsOp rhsOp lhsTy rhsTy hkind hdecl_dst himm_dst hbop
      hlhsOp hrhsOp hlhs hrhs hdst =>
    obtain ⟨_, mls_dst0, _, hlt_dst0, _, _, hmls_eq0, hloc_dst0⟩ := hframe.lookup_local hdecl_dst
    let topFrame₀ := cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy dstDecl.ty body.layouts)
    let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
    have hcache_dst0 : ∀ l, (topFrame.locals[dstIdx]'hlt_dst0).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_eq0]; exact hloc_dst0.layout_eq
    have hevalPlace_dst : annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m =
        .ok ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩ m₀ :=
      annealEvalPlace_unprojected hframes hlt_dst0 hdecl_dst hcache_dst0
    have hframe₀ : FrameRel body m₀.machine s.frame topFrame₀ :=
      hframe.cache_local_layout hdecl_dst hlt_dst0
    have hmono₀ : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₀ j :=
      fun _ hj => hj.cache_layout hlt_dst0 _
    have htf₀ : topFrame₀ = { topFrame with locals := topFrame₀.locals } := rfl
    let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
    have hlhsOp := hlhsOp.mono_immediate hmono₀
    have hrhsOp := hrhsOp.mono_immediate hmono₀
    let knownL := if (translateBinOp bop).leftHomogeneous then some (translateTy dstDecl.ty body.layouts) else none
    have hlhs_sim := evalOperand_scalar_simulation (m := m₀) rfl hframe₀ hlhsOp s.memory.globals knownL
    have hm_eval : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
        Miri.Interpreter.runRvalue
          ((annealEvalOperand body.localDecls body.layouts (translateOperand lhsOp) knownL >>=
              annealReadImmediate) >>=
            fun left =>
              ((annealEvalOperand body.localDecls body.layouts (translateOperand rhsOp)
                  (if (translateBinOp bop).rightHomogeneous then some left.layout else none) >>=
                  annealReadImmediate) >>=
                fun right => do
                  let result ← Miri.Interpreter.ScalarOps.binary
                    (annealScalarOpsHooks body.localDecls body.layouts) ()
                    (translateBinOp bop) left right
                  assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts)
                  annealWriteImmediate result.imm destPlace)) m₀ := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt
      rw [hkind]
      dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
        translateRvalue, annealStepHooks]
      apply runRvalue_eq_of_eq
      rw [evalRvalueIntoPlace_binaryOp_def]
      unfold annealRvalueHooks
      dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
      rw [EStateM.bind_eq_ok hevalPlace_dst, EStateM.bind_assoc_apply]
      dsimp only [knownL, destPlace]
      with_unfolding_all
        simp only [Bind.bind, EStateM.bind]
        cases annealEvalOperand body.localDecls body.layouts (translateOperand lhsOp)
          (if (translateBinOp bop).leftHomogeneous = true then some (translateTy dstDecl.ty body.layouts) else none) m₀ with
        | error _ _ => rfl
        | ok opL st₁ =>
          dsimp only
          cases annealReadImmediate opL st₁ with
          | error _ _ => rfl
          | ok left st₂ =>
            dsimp only
            cases annealEvalOperand body.localDecls body.layouts (translateOperand rhsOp)
              (if (translateBinOp bop).rightHomogeneous = true then some left.layout else none) st₂ <;> rfl
    generalize ha_lhs : evalOperand s.frame.locals lhsOp .nil s.memory.globals body.layouts .nil = aLhs at hlhs_sim
    generalize hm_lhs : (annealEvalOperand body.localDecls body.layouts (translateOperand lhsOp) knownL >>=
      annealReadImmediate) m₀ = mLhs at hlhs_sim
    cases hlhs_sim with
    | ub m' msg =>
      have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; rw [hkind]
        simp [evalRvalue, hbor, hcaller, ha_lhs]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
          (m', .error (.undefinedBehavior msg)) := by
        rw [hm_eval]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_error hm_lhs]
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
      exact .ub _ _
    | ok v₁ locals₁ topFrame₁ imm₁ hframe₁ himm₁ hmono₁ htf₁ =>
      let m₁ : AnnealStepState := { m with stack := ⟨#[topFrame₁]⟩ }
      let knownR := if (translateBinOp bop).rightHomogeneous then some (translateTy lhsTy body.layouts) else none
      have hrhs_sim := evalOperand_scalar_simulation (m := m₁) rfl hframe₁
        (hrhsOp.mono_immediate hmono₁) s.memory.globals knownR
      dsimp only at hrhs_sim
      generalize ha_rhs : evalOperand locals₁ rhsOp .nil s.memory.globals body.layouts .nil = aRhs at hrhs_sim
      generalize hm_rhs : (annealEvalOperand body.localDecls body.layouts (translateOperand rhsOp) knownR >>=
        annealReadImmediate) m₁ = mRhs at hrhs_sim
      cases hrhs_sim with
      | ub m'' msg =>
        have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt; rw [hkind]
          simp [evalRvalue, hbor, hcaller, ha_lhs, ha_rhs]
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
            (m'', .error (.undefinedBehavior msg)) := by
          rw [hm_eval]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hm_lhs]
          dsimp only
          rw [EStateM.bind_eq_error hm_rhs]
        rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
        exact .ub _ _
      | ok v₂ locals₂ topFrame₂ imm₂ hframe₂ himm₂ hmono₂ htf₂ =>
        let m₂ : AnnealStepState := { m with stack := ⟨#[topFrame₂]⟩ }
        obtain ⟨sc₁, sc₂, rfl, rfl, hbin_sim⟩ :=
          scalarOps_binary_boolCmp_simulation (locals₂ := locals₂) (mem := s.memory) (m₂ := m₂)
            hbop hlhsOp.operandTy_eq hlhs hrhs hdst himm₁ himm₂
        have hbind₂ := estate_bind_pure_assoc
          (Miri.Interpreter.ScalarOps.binary
            (annealScalarOpsHooks body.localDecls body.layouts) ()
            (translateBinOp bop) ⟨imm₁, translateTy lhsTy body.layouts⟩
            ⟨imm₂, translateTy rhsTy body.layouts⟩)
          (fun result => assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts))
          (fun result => result.imm)
          (fun i => annealWriteImmediate i destPlace)
          m₂
        generalize ha_bin : evalScalarBinOp bop sc₁ sc₂ locals₂ s.memory
          (operandIsSigned body.localDecls lhsOp body.layouts) = aBin at hbin_sim
        generalize hm_bin : (do
          let result ← Miri.Interpreter.ScalarOps.binary
            (annealScalarOpsHooks body.localDecls body.layouts) ()
            (translateBinOp bop) ⟨imm₁, translateTy lhsTy body.layouts⟩
            ⟨imm₂, translateTy rhsTy body.layouts⟩
          assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts)
          pure result.imm) m₂ = mBin at hbin_sim
        cases hbin_sim with
        | ub msg =>
          have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
            unfold evalStmt; rw [hkind]; dsimp only
            unfold evalRvalue; dsimp only
            rw [hbor, hcaller, ha_lhs]
            dsimp only
            rw [ha_rhs]
            dsimp only
            rw [ha_bin]
          have hm_err : Miri.Interpreter.Step.evalStatement
              (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
              (m₂, .error (.undefinedBehavior msg)) := by
            rw [hm_eval]
            unfold Miri.Interpreter.runRvalue
            rw [EStateM.bind_eq_ok hm_lhs]
            dsimp only
            rw [EStateM.bind_eq_ok hm_rhs]
            rw [hbind₂, EStateM.bind_eq_error hm_bin]
          rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
          exact .ub _ _
        | ok v' imm' himmRel' =>
          have ha_ok : evalStmt s stmt body.localDecls body.layouts =
              match get? locals₂ dstIdx with
              | .some .dead => MirStepNode.fail .ub
              | .some _ =>
                match set? locals₂ dstIdx (.init v') with
                | .some locals₃ => MirStepNode.step (advanceStmt s locals₃ s.memory)
                | .none => MirStepNode.fail .ub
              | .none => MirStepNode.fail .ub := by
            unfold evalStmt; rw [hkind]; dsimp only
            have hrv_ok : evalRvalue s.frame.locals (.binaryOp bop lhsOp rhsOp) s.memory body.localDecls body.layouts =
                .ok v' locals₂ s.memory := by
              unfold evalRvalue; dsimp only
              rw [hbor, hcaller, ha_lhs]
              dsimp only
              rw [ha_rhs]
              dsimp only
              exact ha_bin
            rw [hrv_ok]
            dsimp only
            rw [hprot, hbor]
            dsimp only [invalidateConflictingBorrows]
            rw [hmem_same]; rfl
          have hm_write : Miri.Interpreter.Step.evalStatement
              (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
              Miri.Interpreter.runRvalue
                (annealWriteImmediate imm' destPlace)
                m₂ := by
            rw [hm_eval]
            apply runRvalue_eq_of_eq
            rw [EStateM.bind_eq_ok hm_lhs]
            dsimp only
            rw [EStateM.bind_eq_ok hm_rhs]
            rw [hbind₂, EStateM.bind_eq_ok hm_bin]
          have hrc₂ : topFrame₂.returnContinuation = .stop false := by
            rw [htf₂, htf₁, htf₀]; exact hretCont
          have hrp₂ : ∃ rl, topFrame₂.returnPlace = .frameLocal 0 0 none rl topFrame₂.localsIdentity := by
            rw [htf₂, htf₁, htf₀]; exact ⟨retLay, hretPlace⟩
          exact (write_after_rvalue_simulation_ext hrc₂ hrp₂ hcal hstack hbor hprot hcaller
            hframes hframe.body_eq hframe.location_eq
            (fun j hj => hmono₂ j (hmono₁ j (hmono₀ j hj)))
            hbb hstmt hframe₂ hdecl_dst
            (hmono₂ dstIdx (hmono₁ dstIdx (hmono₀ dstIdx himm_dst)))
            himmRel' ha_ok hm_write).1
  | intToInt dstIdx dstDecl op srcTy hkind hdecl_dst himm_dst hop hsrc hdst =>
    obtain ⟨_, mls_dst0, _, hlt_dst0, _, _, hmls_eq0, hloc_dst0⟩ := hframe.lookup_local hdecl_dst
    let topFrame₀ := cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy dstDecl.ty body.layouts)
    let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
    have hcache_dst0 : ∀ l, (topFrame.locals[dstIdx]'hlt_dst0).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_eq0]; exact hloc_dst0.layout_eq
    have hevalPlace_dst : annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m =
        .ok ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩ m₀ :=
      annealEvalPlace_unprojected hframes hlt_dst0 hdecl_dst hcache_dst0
    have hframe₀ : FrameRel body m₀.machine s.frame topFrame₀ :=
      hframe.cache_local_layout hdecl_dst hlt_dst0
    have hmono₀ : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₀ j :=
      fun _ hj => hj.cache_layout hlt_dst0 _
    have htf₀ : topFrame₀ = { topFrame with locals := topFrame₀.locals } := rfl
    let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
    have hopTy := hop.operandTy_eq
    have hop_sim := evalOperand_scalar_simulation_opTy (m := m₀) rfl hframe₀
      (hop.mono_immediate hmono₀) s.memory.globals none
    have hm_eval : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
        Miri.Interpreter.runRvalue
          (annealEvalOperand body.localDecls body.layouts (translateOperand op) none >>= fun src =>
            Miri.Interpreter.Cast.cast (annealCastHooks body.layouts) () 16 src .IntToInt
              (encodeTyId dstDecl.ty) destPlace) m₀ := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt
      rw [hkind]
      dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
        translateRvalue, translateCastKind, annealStepHooks]
      apply runRvalue_eq_of_eq
      unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
      dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
      rw [EStateM.bind_eq_ok hevalPlace_dst]
      rfl
    generalize ha_op : evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil = aOp
      at hop_sim
    generalize hm_op : annealEvalOperand body.localDecls body.layouts (translateOperand op) none m₀ = mOp
      at hop_sim
    have ha_ub : aOp = .ub → evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
      intro hub
      unfold evalStmt; rw [hkind]
      simp [evalRvalue, hbor, hcaller, ha_op, hub]
    cases hop_sim with
    | ub m' msg =>
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
          (m', .error (.undefinedBehavior msg)) := by
        rw [hm_eval]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_error hm_op]
      rw [ha_ub rfl, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
      exact .ub _ _
    | uninit m' =>
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
          (m', .error (.undefinedBehavior "read of uninitialized local")) := by
        rw [hm_eval]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hm_op, cast_intToInt_uninit body.layouts srcTy dstDecl.ty destPlace hsrc hdst rfl m']
      rw [ha_ub rfl, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
      exact .ub _ _
    | ok v locals₁ topFrame₁ imm hframe₁ himmRel hmono htf₁ =>
      have hprim : srcTy.kind = .bool ∨ srcTy.kind = .char ∨
          (∃ it, srcTy.kind = .int it) ∨ (∃ ut, srcTy.kind = .uint ut) := by
        rcases hsrc with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
      obtain ⟨sc, msc, rfl, rfl, hrel, hsz, hbool, _⟩ := himmRel.of_primitive_scalar hprim
      obtain ⟨_, hsz_src⟩ := sizeBytes_eq_of_translateTy hsrc hrel.validBytes hsz
      have hop_a : evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
          s.memory.callerLocals = .ok (.scalar sc) locals₁ := by
        rw [hbor, hcaller]; exact ha_op
      obtain ⟨msc', hrv_ok, _, hcast, hrel'⟩ :=
        evalCast_intToInt_simulation hrel destPlace hop_a hopTy hsrc hdst hsz_src
          (fun h => (hbool h).2) rfl
      have ha_ok : evalStmt s stmt body.localDecls body.layouts =
          match get? locals₁ dstIdx with
          | .some .dead => MirStepNode.fail .ub
          | .some _ =>
            match set? locals₁ dstIdx (.init (.scalar ⟨(decodeBitsInt (tyIsSigned srcTy) sc.sizeBytes sc.bits %
                (2 : Int) ^ (8 * boolOrIntByteWidth dstDecl.ty)).toNat, boolOrIntByteWidth dstDecl.ty⟩)) with
            | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
            | .none => MirStepNode.fail .ub
          | .none => MirStepNode.fail .ub := by
        unfold evalStmt; rw [hkind]; dsimp only
        rw [hrv_ok]
        dsimp only
        rw [hprot, hbor]
        dsimp only [invalidateConflictingBorrows]
        rw [hmem_same]; rfl
      have hm_write : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
          Miri.Interpreter.runRvalue
            (annealWriteImmediate (.scalar (.fromScalarInt msc')) destPlace)
            { m with stack := ⟨#[topFrame₁]⟩ } := by
        rw [hm_eval]
        apply runRvalue_eq_of_eq
        rw [EStateM.bind_eq_ok hm_op]
        exact congrFun hcast _
      have hdst' : dstDecl.ty.kind = .bool ∨ (∃ k, dstDecl.ty.kind = .int k) ∨
          (∃ k, dstDecl.ty.kind = .uint k) := Or.inr hdst
      obtain ⟨hwsz_dst, _⟩ := boolOrInt_translateTy_size hdst' body.layouts
      have himmRel' : ImmediateRel dstDecl.ty body.layouts
          (.scalar ⟨(decodeBitsInt (tyIsSigned srcTy) sc.sizeBytes sc.bits %
            (2 : Int) ^ (8 * boolOrIntByteWidth dstDecl.ty)).toNat, boolOrIntByteWidth dstDecl.ty⟩)
          (.scalar (.fromScalarInt msc')) := by
        refine .scalar _ _ hrel' hwsz_dst ?_ ?_
        · intro hb; rcases hdst with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] at hb <;> cases hb
        · intro hc; rcases hdst with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] at hc <;> cases hc
      have hrc₁ : topFrame₁.returnContinuation = .stop false := by
        rw [htf₁, htf₀]; exact hretCont
      have hrp₁ : ∃ rl, topFrame₁.returnPlace = .frameLocal 0 0 none rl topFrame₁.localsIdentity := by
        rw [htf₁, htf₀]; exact ⟨retLay, hretPlace⟩
      exact (write_after_rvalue_simulation_ext hrc₁ hrp₁ hcal hstack hbor hprot hcaller
        hframes hframe.body_eq hframe.location_eq (fun j hj => hmono j (hmono₀ j hj))
        hbb hstmt hframe₁ hdecl_dst (hmono dstIdx (hmono₀ dstIdx himm_dst)) himmRel' ha_ok
        hm_write).1

/-! ## 8. Composed `LM-1.2` Step Simulation -/

/-- Composed statement simulation: every statement of the `LM-1.1` scalar fragment
(`WellTypedScalarStmt`) or of its `LM-1.2` extension (`WellTypedLM12Stmt`) steps
Anneal's `stepMirFn` and `lean-miri`'s `Step.step` in lockstep. -/
theorem step_stmt_lm1_2_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarStmt body topFrame stmt ∨ WellTypedLM12Stmt body topFrame stmt) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨topFrame, hframes, _, _, _, _, _, _, _, _⟩ := id hstate
  have huniq : ∀ tf, m.stack.frames = #[tf] → tf = topFrame := by
    intro tf htf
    rw [hframes] at htf
    injection htf with h_arr
    injection h_arr with h_eq _
    exact h_eq.symm
  rcases hwt topFrame hframes with h | h
  · exact step_assign_scalar_simulation hstate hphase hbb hstmt
      (fun tf htf => huniq tf htf ▸ h)
  · exact step_assign_lm1_2_simulation hstate hphase hbb hstmt
      (fun tf htf => huniq tf htf ▸ h)

/-- Composed terminator simulation (observation-aware): `Goto`, `Return`, and
`Unreachable` (`LM-1.1`) and `SwitchInt` (`LM-1.2`) step Anneal's `stepMirFn` and
`lean-miri`'s `Step.step` in lockstep. -/
theorem step_terminator_lm1_2_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hterm :
      ((∃ target, bb.terminator.kind = .goto target) ∨
        (bb.terminator.kind = .return_ ∧
          ∃ decl0,
            get? body.localDecls 0 = some decl0 ∧
            (translateTy decl0.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO ∧
            ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 0) ∨
        bb.terminator.kind = .unreachable) ∨
      (∃ discr targets ty,
        bb.terminator.kind = .switchInt discr targets ∧
        (ty.kind = .bool ∨ (∃ k, ty.kind = .int k) ∨ (∃ k, ty.kind = .uint k)) ∧
        (∀ topFrame, m.stack.frames = #[topFrame] →
          WellTypedScalarOperand body topFrame discr ty) ∧
        SwitchCasesFit ty targets)) :
    StepObsRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hterm with h | ⟨_, _, _, hk, hty, hdiscr, hcases⟩
  · exact (step_terminator_goto_return_simulation hstate hphase hbb hstmt_none hstmt_len
      hcleanup h).toStepObsRel
  · exact step_terminator_switchInt_simulation hstate hphase hbb hstmt_none hstmt_len hk hty
      hdiscr hcases

end LeanMiriSpec.Correspondence
