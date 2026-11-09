/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.IntrinsicLM4_2
import LeanMiriSpec.Correspondence.BitsLM4_2

/-!
# Numeric Bit-Intrinsic Arm for `LM-4.2`

Simulation of the numeric (`IntegerIntrinsic`) arm of the vendored
`Intrinsics.eval` under `annealIntrinsicHooks` (`annealNumericEval`, which
mirrors `Miri/Interpreter/Intrinsics.lean`) against Anneal's
`evalIntegerBitIntrinsic`, on an initialized integer immediate operand.

* `annealNumericEval_scalar_eq` evaluates the prefix of `annealNumericEval`
  (operand read, integer kinds of the argument and destination types, operand
  width check) on such an operand.
* `annealNumericEval_simulation` combines it with
  `integerBitIntrinsic_run_simulation` (`BitsLM4_2.lean`).
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Encoded integral types -/

/-- `encodeTyId` of an integral type depends only on its kind. -/
theorem IsIntegralTy.encodeTyId_kindOnly {ty : Ty} {kind : Miri.MIR.IntegerKind}
    (h : IsIntegralTy ty kind) :
    encodeTyId { kind := ty.kind, layoutIdx := 0 } = encodeTyId ty := by
  rcases h with ⟨it, hk⟩ | ⟨ut, hk⟩
  · cases it <;> simp [encodeTyId, hk]
  · cases ut <;> simp [encodeTyId, hk]

/-- The layout decoded from the `TyId` of an integral type's kind is the
type's translated layout. -/
theorem IsIntegralTy.layoutOfEncoded_kindOnly {ty : Ty} {kind : Miri.MIR.IntegerKind}
    (h : IsIntegralTy ty kind) (ly : LayoutTable) :
    layoutOfEncodedTyId (encodeTyId { kind := ty.kind, layoutIdx := 0 }) ly =
      translateTy ty ly := by
  rw [h.encodeTyId_kindOnly]
  exact h.prim.layoutOfEncoded

/-- `annealIntegerKindOf` returns the kind that `classifyEncodedTyId` reports. -/
theorem annealIntegerKindOf_of_classify {tyId : Miri.MIR.TyId} {kind : Miri.MIR.IntegerKind}
    (h : classifyEncodedTyId tyId = .ok (.integer kind)) :
    annealIntegerKindOf tyId = pure kind := by
  unfold annealIntegerKindOf
  rw [h]

/-! ## 2. Result width -/

/-- The result of `evalIntegerBitIntrinsic op x` is `bitIntrinsicOutBytes op
x.sizeBytes` bytes wide. -/
theorem evalIntegerBitIntrinsic_sizeBytes {op : IntegerBitIntrinsic} {x r : MirAst.ScalarInt}
    (h : evalIntegerBitIntrinsic op x = some r) :
    r.sizeBytes = bitIntrinsicOutBytes op x.sizeBytes := by
  cases op <;> simp only [evalIntegerBitIntrinsic] at h
  all_goals first
    | (cases h; rfl)
    | (split at h
       · cases h
       · cases h; rfl)

/-! ## 3. `annealNumericEval` on an integer immediate -/

/-- `annealNumericEval` on an initialized integer immediate operand `msc`,
once the decoded argument layout, the integer kinds of the argument and
destination types, and the operand width check are known: reject a
`bswap`/`bitreverse` whose argument and destination layouts differ, run
`IntegerIntrinsic.run`, and write its result to `dest`. -/
theorem annealNumericEval_scalar_eq (ly : LayoutTable)
    (numeric : Miri.Interpreter.IntegerIntrinsic) (argTy : Miri.MIR.TyId)
    {layout : Miri.Interpreter.LocalLayout} (hlay : layoutOfEncodedTyId argTy ly = layout)
    {kind retKind : Miri.MIR.IntegerKind}
    (hkind : classifyEncodedTyId layout.ty = .ok (.integer kind))
    (dest : Miri.Interpreter.RuntimePlace AnnealProv)
    (hret : classifyEncodedTyId dest.layout.ty = .ok (.integer retKind))
    (msc : Miri.Memory.ScalarInt) {bits : Miri.ABI.U128}
    (hbits : msc.toBits layout.layout.size = .ok bits)
    (opLayout : Miri.Interpreter.LocalLayout) (target : Option Miri.MIR.BasicBlockId) :
    annealNumericEval ly numeric argTy ⟨.immediate (.scalar (.fromScalarInt msc)), opLayout⟩
        dest target =
      (do
        if (numeric == .bswap || numeric == .bitreverse) && layout != dest.layout then
          throw (.invalidProgram "numeric intrinsic layout mismatch")
        let result ← liftScalarResult (Miri.Interpreter.IntegerIntrinsic.run numeric msc
          ⟨layout.layout.size, kind⟩ ⟨dest.layout.layout.size, retKind⟩ |>.mapError fun e =>
            match e with
            | .scalar e => Miri.Interpreter.ScalarOps.scalarIntError e
            | .undefinedBehaviorOnZero _ =>
              .undefinedBehavior "nonzero count intrinsic called on zero"
            | .layoutMismatch _ _ => .invalidProgram "numeric intrinsic layout mismatch")
        annealWriteImmediate (.scalar (.fromScalarInt result)) dest
        annealReturnToBlock target
        pure true) := by
  subst hlay
  have h1 : intrinsicScalar
      (⟨.immediate (.scalar (.fromScalarInt msc)), opLayout⟩ : Miri.Interpreter.OpTy AnnealProv) =
        pure (.fromScalarInt msc) := rfl
  have h2 := annealIntegerKindOf_of_classify hkind
  have h3 := annealIntegerKindOf_of_classify hret
  have h4 : liftScalarResult (S := AnnealStepState)
      ((Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toScalarInt
        |>.mapError Miri.Interpreter.ScalarOps.scalarError) = pure msc := rfl
  have h5 : liftScalarResult (S := AnnealStepState)
      (msc.toBits (layoutOfEncodedTyId argTy ly).layout.size
        |>.mapError Miri.Interpreter.ScalarOps.scalarIntError) = pure bits := by
    rw [hbits]
    rfl
  unfold annealNumericEval
  simp only [h1, h2, h3, h4, h5, pure_bind]
  rfl

/-! ## 4. Simulation -/

/-- **The numeric bit-intrinsic arm of `Intrinsics.eval` simulates
`evalIntegerBitIntrinsic` (`LM-4.2`).**

Let `op` be applied at the integral type `ty` (generic type argument
`encodeTyId { kind := ty.kind, layoutIdx := 0 }`) to the initialized
`lean-miri` integer immediate `msc`, related by `ScalarRel` to the Anneal
scalar `sc` of `ty`'s width, with result written to `dest` of the integral
type `dstTy`, where `dstTy` is `u32` for the counting intrinsics and has
`ty`'s integer kind for `bswap` and `bitreverse` (`hcount`, `hperm`). Then:

* when Anneal reports undefined behavior (a zero operand to `ctlz_nonzero` or
  `cttz_nonzero`), `annealNumericEval` reports undefined behavior without
  changing the state;
* otherwise Anneal returns a scalar `r` of `dstTy`'s width, and
  `annealNumericEval` writes a `ScalarRel`-related scalar `mr` to `dest` and
  returns to `target`. -/
theorem annealNumericEval_simulation
    {ly : LayoutTable} (op : IntegerBitIntrinsic) {ty dstTy : Ty}
    {kind dstKind : Miri.MIR.IntegerKind}
    (hint : IsIntegralTy ty kind) (hdst : IsIntegralTy dstTy dstKind)
    (hcount : (op = .bswap ∨ op = .bitreverse) ∨ dstKind = .u32)
    (hperm : (op = .bswap ∨ op = .bitreverse) → dstKind = kind)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc)
    (hsz : (translateTy ty ly).layout.size = translateSizeBytes sc.sizeBytes)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) (hdest : dest.layout = translateTy dstTy ly)
    (target : Option Miri.MIR.BasicBlockId) (m : AnnealStepState) :
    (evalIntegerBitIntrinsic op sc = none ∧
      ∃ msg, annealNumericEval ly (toMiriIntegerIntrinsic op)
          (encodeTyId { kind := ty.kind, layoutIdx := 0 })
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy ty ly⟩ dest target m =
        .error (.undefinedBehavior msg) m) ∨
    (∃ r mr, evalIntegerBitIntrinsic op sc = some r ∧ ScalarRel r mr ∧
      (translateTy dstTy ly).layout.size = translateSizeBytes r.sizeBytes ∧
      annealNumericEval ly (toMiriIntegerIntrinsic op)
          (encodeTyId { kind := ty.kind, layoutIdx := 0 })
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy ty ly⟩ dest target m =
        (do annealWriteImmediate (.scalar (.fromScalarInt mr)) dest
            annealReturnToBlock target
            pure true) m) := by
  have hdkind : classifyEncodedTyId dest.layout.ty = .ok (.integer dstKind) := by
    rw [hdest]
    exact hdst.classify
  have hbits : msc.toBits (translateTy ty ly).layout.size = .ok (BitVec.ofNat 128 sc.bits) := by
    rw [hsz]
    exact hrel.toBits_eq
  rw [annealNumericEval_scalar_eq ly _ _ (hint.layoutOfEncoded_kindOnly ly) hint.classify dest
    hdkind msc hbits]
  -- `bswap` and `bitreverse` write a value of the operand's own layout.
  have hlayEq : (op = .bswap ∨ op = .bitreverse) → translateTy ty ly = dest.layout := by
    intro hop
    have hk := hperm hop
    subst hk
    rw [hdest]
    exact hint.translateTy_eq hdst ly ly
  have hcond : ((toMiriIntegerIntrinsic op == .bswap || toMiriIntegerIntrinsic op == .bitreverse) &&
      translateTy ty ly != dest.layout) = false := by
    cases op
    case bswap => rw [← hlayEq (Or.inl rfl), bne_self_eq_false, Bool.and_false]
    case bitreverse => rw [← hlayEq (Or.inr rfl), bne_self_eq_false, Bool.and_false]
    all_goals rfl
  have hout :
      dest.layout.layout.size = translateSizeBytes (bitIntrinsicOutBytes op sc.sizeBytes) := by
    by_cases hop : op = .bswap ∨ op = .bitreverse
    · rw [← hlayEq hop, hsz]
      rcases hop with rfl | rfl <;> rfl
    · have hu32 : dstKind = .u32 := hcount.resolve_left hop
      subst hu32
      have h4 : bitIntrinsicOutBytes op sc.sizeBytes = 4 := by
        cases op <;> first | rfl | exact absurd (Or.inl rfl) hop | exact absurd (Or.inr rfl) hop
      rw [hdest, hdst.size_eq ly, h4]
      rfl
  rw [hcond, hsz, hout]
  obtain ⟨hsome, hnone⟩ := integerBitIntrinsic_run_simulation hrel op kind dstKind hperm
  cases hev : evalIntegerBitIntrinsic op sc with
  | none =>
    refine Or.inl ⟨rfl, "nonzero count intrinsic called on zero", ?_⟩
    rw [hnone hev]
    rfl
  | some r =>
    obtain ⟨mr, hrun, hrel'⟩ := hsome r hev
    refine Or.inr ⟨r, mr, rfl, hrel', ?_, ?_⟩
    · rw [← hdest, hout, evalIntegerBitIntrinsic_sizeBytes hev]
    · rw [hrun]
      rfl

end LeanMiriSpec.Correspondence
