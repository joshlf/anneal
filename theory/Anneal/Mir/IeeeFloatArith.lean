/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted
import Trusted.Rustc.V2026_08_01.MirSemantics.Places
import Anneal.Mir.IeeeFloatCast

/-!
# Pure IEEE-754 `binary32` / `binary64` arithmetic, comparisons, negation, `Ptr2IntTransmutePolicy`, and dialect parity: theory

Constructive (`[propext, Quot.sound]`, zero `Classical.choice`, zero host
`Float`, zero `sorry`) derived theory directly over the ground definitions in
`Trusted.Rustc.{V2026_06_01,V2026_08_01}.MirSemantics.{Scalars,Places}`:

- **§1**: Finding 1 resolution & `evalRvalue` witnesses (`-1.0_f32`,
  `1.0_f32 + 1.0_f32`, `-0.0 == +0.0`, `qNaN == qNaN`, `qNaN != qNaN`,
  `f16`/`f128` fail-closed `.unsupported`);
- **§2**: Bitwise `evalFloatNeg` / `evalFloatAbs` involution, idempotence,
  `decodeBits` commutation, sNaN/qNaN payload & quiet-bit preservation, and
  `evalFloatCmp` NaN unorderedness, `.ne` duality, trichotomy, reflexivity /
  symmetry / antisymmetry, `-0.0 == +0.0`, and mode-independence;
- **§3**: Single-rounding `roundTiesToEven` characterizations (`add`, `sub`,
  `mul`, `div`), exact grid representability (`roundRatioTiesToEven_exact_grid`),
  Sterbenz's exact subtraction (`y / 2 ≤ x ∧ x ≤ 2 * y`), exact addition,
  gradual underflow (`a - b = ±0 ↔ a == b`, `a + b = ±0 ↔ a == -b`), `1.0`
  multiplicative identity, exact Euclidean `rem` (`|a % b| < |b|`, sign &
  magnitude bounds, `|a| < |b| → a % b = a`, `a % ±a = ±0`, `rem = ±0 ↔
  divisibility`), the exact closed-form rational overflow threshold
  (`maxFiniteBits`, `maxFiniteVal`,
  `overflowThreshold = (2^(fb+2) - 1) * 2^(bias - fb - 1)`,
  `roundRatioTiesToEven_eq_inf_iff`, `roundRatioTiesToEven_lt_inf_isFinite`,
  `roundRatioTiesToEven_eq_maxFiniteBits`, boundary witnesses, the operation-level
  overflow threshold for finite `add` / `sub` / `mul` / `div`
  (`evalFloatArithBase_*_finite_overflow_iff`), and `f32` / `f64`
  `MAX + ulp(MAX) / 2` overflow-tie witnesses), and subnormal / gradual-underflow
  precision laws (`minSubnormalBits`, `maxSubnormalBits`, `minNormalBits`,
  `minSubnormalDen`, `minSubnormalVal`, uniform subnormal step spacing, exact
  closed-form underflow-to-zero threshold `roundRatioTiesToEven_eq_zero_iff` &
  operation-level `mul`/`div` underflow-to-zero thresholds + tie witnesses, and
  unconditional zero-error subnormal addition/subtraction
  `exact_subnormal_add` / `exact_subnormal_sub` / `exact_subnormal_add_sub`);
- **§4**: `FloatArithMode` inclusion (`EvalFloatBinOpRel.det_imp_nondet`,
  `EvalRvalueFloatRel.det_imp_nondet`, `evalFloatBinOp` realizes `.deterministic`),
  `nanChoices` membership / width / NaN / quietness / `4`-vs-`6` sNaN structure,
  `sub` vs `add ∘ neg` ordered-list swap witness, relational sign-symmetry
  (`rem` right-negation invariance in both modes, `.deterministic`
  `(+0.0) * (+Inf)` counterexample, `.nondeterministic` unconditional left/right
  sign symmetry for `mul`/`div`/`rem` and non-zero-canceling `add`/`sub`), and
  mode-independence of finite `rem` (`EvalFloatBinOpRel_rem_finite_deterministic`);
- **§5**: `Ptr2IntTransmutePolicy` refinement (`strictUcg630Ub` refines
  `stripProvenance`), exact cast split (`strip = strict ∨ strict = .ub`),
  provenance-free equivalence, closed-form provenance erasure on non-pointer
  primitives and composite types (`.array`, `.tuple`, single-variant `.adt`
  structs / scalar pairs / arrays / primitives, multi-variant enums, and
  `RichAdtSpec` structs / direct-tagged enums / scalar-niche enums), selective
  per-field provenance preservation on mixed pointer + integer/float composites
  (tuples, `.scalarPair` structs, `RichAdtSpec.structFields`, and intact
  `RichAdtSpec.nichePointerEnum`), policy independence on
  `.rawPtr`/`.ref`/`.fnPtr`/pointer-array/union targets,
  32-bit `usize`/`isize` & unresolved-slot-0 tuple/ref witnesses, and struct &
  enum `.ref`/`.fnPtr` no-forgery (`evalByteCastRichWithPolicy`);
- **§6**: `V2026_06_01` <-> `V2026_08_01` dialect parity over explicit
  constructor-preserving translation maps (`fmt08`, `binOp08`, `mode08`,
  `floatKind08`, `scalarInt08`, `policy08`, `abstractByte08`, `floatTy08`,
  `tyFloat08`, `wrappingRange08`, `primitiveKind08`, `scalarLayout08`, and the
  total injective value embedding `value06` / `rvalueResWith06`): `Scalars`-level
  `evalFloatNeg`, `evalFloatAbs`, `decodeBits`, `roundRatioTiesToEven`,
  `evalFloatPartialCompare`, `evalFloatCmp`, `evalFloatArithBase`,
  `evalFloatToFloatRoundTiesToEven`, `nanChoices` (element-for-element),
  `evalFloatBinOp`, `EvalFloatBinOpRel` (`↔`), and `Places`-level
  `policyRejectsProv`, `stripAbstractBytesProv`, `ieeeFormatOfTy?`, `isFloatTy`,
  `isFloatOptTy`, `evalFloatUnaryNeg`, `evalFloatScalarBinOp`,
  `decodeLittleEndianBytes`, `decodeScalarBytes`, `abstractBytesUniformProv`,
  `scalarLayoutByteWidth`, `wrappingRangeContains`, `isValidCharCode`,
  `decodeScalarLayoutBytesNoForge`, and compositional `evalRvalue` /
  `EvalRvalueFloatRel` cross-dialect parity on float `.unaryOp .neg`, float
  `.binaryOp`, and `.cast .floatToFloat` (plus direct specializations to scalar
  constants and locals via `.copy` / `.move`). Parity of the layout-table-driven
  decoders (`decodeTypedValueFromBytes`, `evalByteCast`) is NOT proved here: their
  `LayoutTable` / `Memory` types are dialect-specific (`V2026_08_01.Value` has
  no `.uninit`) and require full `LayoutTable`/`Memory` structural translations;
- **§7**: IEEE 754-2008 special-case table over both formats and all signs (NaN
  infectiousness, signed-zero sums, exact cancellation `x + (-x) = +0`, invalid
  operations, `finite / ±0 = ±∞` with XOR sign, `x % ±0 = NaN`, `±∞ % y = NaN`,
  `finite % ±∞ = finite`, `±0 % finite = ±0`), the documented signed-zero rule
  for arbitrary zero-valued sums and differences, the no-NaN-input `nanChoices`
  closed form (`[preferred, -preferred]`), admissibility of `evalRvalue`'s
  quieting `floatToFloat` NaN in `.nondeterministic` (but not `.deterministic`)
  mode, `evalRvalue`-level realization & dispatcher laws for `EvalRvalueFloatRel`
  (including the concrete NaN `floatToFloat` separation witness), and
  unconditional subtraction-as-negated-addition laws across `evalFloatBinOp`,
  `EvalFloatBinOpRel`, `evalFloatScalarBinOp`, `evalRvalue`, and
  `EvalRvalueFloatRel`, and the Episode 2 readiness laws at ANY `FloatArithMode`
  and ANY `Ptr2IntTransmutePolicy`: mode-invariant supportedness / totality /
  well-formedness of `EvalFloatBinOpRel` (`isFloatBinOp`), policy irrelevance
  outside byte casts and mode irrelevance outside float arithmetic, mode
  invariance and `evalRvalue`-exactness of every `.ub` / `.unsupported` outcome,
  totality, the executable `evalRvalueDet` characterizing `.deterministic` mode
  exactly, generic-mode float `.binaryOp` and NaN `.cast .floatToFloat`
  dispatchers, relation-level and decoder-level `Ptr2IntTransmutePolicy`
  refinement / exact split / provenance-necessity bridges for every (composite)
  type, and concrete witnesses (float operands and NaN choices read from locals,
  pointer-to-integer and array / tuple / struct-with-padding / union / float
  policy separation, `{to,from}_bits`);
- **§8**: `#guard_msgs in #print axioms` bundles pinning every public theorem to
  `[propext, Quot.sound]`.
-/

namespace Anneal.Mir.IeeeFloatArith

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.Mir.IeeeFloatCast

/-! ## §0. Constructive helpers -/

/-- Opaque wrapper that hides a proposition from `omega`. `omega` case-splits on
hypotheses containing `→` / `↔` through `Classical.em`, which silently adds
`Classical.choice` to the proof term; wrapping such a hypothesis in `Hold` keeps
the surrounding `omega` calls constructive (`[propext, Quot.sound]`). -/
private structure Hold (P : Prop) : Prop where
  /-- The wrapped proof. -/
  val : P

private theorem nat_mul_le_mul_right_iff {a b c : Nat} (hc : 0 < c) :
    a * c ≤ b * c ↔ a ≤ b := by
  refine ⟨fun h => ?_, fun h => Nat.mul_le_mul_right c h⟩
  cases Nat.lt_or_ge b a with
  | inl hlt =>
    have hmul : b * c < a * c := Nat.mul_lt_mul_of_pos_right hlt hc
    omega
  | inr hle => exact hle

private theorem nat_mul_eq_mul_right_iff {a b c : Nat} (hc : 0 < c) :
    a * c = b * c ↔ a = b := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have h1 : a ≤ b := (nat_mul_le_mul_right_iff hc).mp (Nat.le_of_eq h)
  have h2 : b ≤ a := (nat_mul_le_mul_right_iff hc).mp (Nat.le_of_eq h.symm)
  omega

private theorem bool_xor_not_left (a b : Bool) : Bool.xor (Bool.not a) b = Bool.not (Bool.xor a b) := by
  cases a <;> cases b <;> rfl

private theorem bool_xor_not_right (a b : Bool) : Bool.xor a (Bool.not b) = Bool.not (Bool.xor a b) := by
  cases a <;> cases b <;> rfl

private theorem bool_xor_not_both (a b : Bool) : Bool.xor (Bool.not a) (Bool.not b) = Bool.xor a b := by
  cases a <;> cases b <;> rfl

theorem unpackBits_mod (f : IeeeFormat) (bits : Nat) :
    unpackBits f (bits % 2 ^ f.width) = unpackBits f bits := by
  cases f
  · simp only [unpackBits, IeeeFormat.width, IeeeFormat.fractionBits, IeeeFormat.exponentBits,
      Nat.reducePow, Nat.reduceSub, FloatComponents.mk.injEq, nat_beq_eq_decide]
    refine ⟨?_, ?_, ?_⟩
    · have h : bits % 4294967296 / 2147483648 % 2 = bits / 2147483648 % 2 := by omega
      rw [h]
    · omega
    · omega
  · simp only [unpackBits, IeeeFormat.width, IeeeFormat.fractionBits, IeeeFormat.exponentBits,
      Nat.reducePow, Nat.reduceSub, FloatComponents.mk.injEq, nat_beq_eq_decide]
    refine ⟨?_, ?_, ?_⟩
    · have h : bits % 18446744073709551616 / 9223372036854775808 % 2 =
          bits / 9223372036854775808 % 2 := by omega
      rw [h]
    · omega
    · omega

theorem decodeBits_mod (f : IeeeFormat) (bits : Nat) :
    decodeBits f (bits % 2 ^ f.width) = decodeBits f bits := by
  unfold decodeBits
  rw [unpackBits_mod]

theorem decodeBits_finite_num_pos (f : IeeeFormat) (bits : Nat) (neg : Bool) (n d : Nat)
    (h : decodeBits f bits = .finite neg n d) : 0 < n := by
  unfold decodeBits at h
  simp only at h
  split at h
  · split at h <;> cases h
  · split at h
    · split at h
      · cases h
      · rename_i hF
        injection h with _ hn _
        rw [← hn]
        exact powScale_fst_pos _ 1 _ (Nat.pos_of_ne_zero hF)
    · injection h with _ hn _
      rw [← hn]
      have hpos : 0 < 2 ^ f.fractionBits + (unpackBits f bits).fraction := by
        have := Nat.two_pow_pos f.fractionBits
        omega
      exact powScale_fst_pos _ 1 _ hpos

theorem isNaNBits_eq_true_iff (f : IeeeFormat) (bits : Nat) :
    isNaNBits f bits = true ↔ ∃ neg q payload, decodeBits f bits = .nan neg q payload := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold isNaNBits at h
    cases hd : decodeBits f bits with
    | nan neg q payload => exact ⟨neg, q, payload, rfl⟩
    | _ => rw [hd] at h; cases h
  · rcases h with ⟨neg, q, payload, hd⟩
    unfold isNaNBits
    rw [hd]

theorem isNaNBits_zeroBits (f : IeeeFormat) (neg : Bool) :
    isNaNBits f (zeroBits f neg) = false := by
  unfold isNaNBits
  rw [decodeBits_zeroBits]

theorem isNaNBits_infBits (f : IeeeFormat) (neg : Bool) :
    isNaNBits f (infBits f neg) = false := by
  unfold isNaNBits
  rw [decodeBits_infBits]

theorem isNaNBits_preferredNaNBits (f : IeeeFormat) :
    isNaNBits f (preferredNaNBits f) = true := by
  cases f <;> decide

theorem isQuietNaNBits_preferredNaNBits (f : IeeeFormat) :
    isQuietNaNBits f (preferredNaNBits f) = true := by
  cases f <;> decide

theorem isNaNBits_roundRatioTiesToEven (f : IeeeFormat) (neg : Bool) (n d : Nat) (hd : 0 < d) :
    isNaNBits f (roundRatioTiesToEven f neg n d) = false := by
  rw [← roundRatioBits_tiesToEven]
  exact (roundRatioBits_valid_and_not_nan .tiesToEven f neg n d hd).2

theorem roundRatioTiesToEven_zero (f : IeeeFormat) (neg : Bool) (d : Nat) (hd : 0 < d) :
    roundRatioTiesToEven f neg 0 d = zeroBits f neg := by
  have hne : ¬ (d = 0) := by omega
  unfold roundRatioTiesToEven
  rw [if_neg' hne, if_pos' rfl]

theorem signedNum_not (neg : Bool) (n : Nat) :
    signedNum (Bool.not neg) n = -signedNum neg n := by
  cases neg <;> simp [signedNum]

theorem signedNum_neg_iff (neg : Bool) (n : Nat) (hn : 0 < n) :
    signedNum neg n < 0 ↔ neg = true := by
  cases neg with
  | true =>
    refine ⟨fun _ => rfl, fun _ => ?_⟩
    simp only [signedNum, ↓reduceIte]
    omega
  | false =>
    refine ⟨fun h => ?_, fun h => Bool.noConfusion h⟩
    simp only [signedNum, Bool.false_eq_true, ↓reduceIte] at h
    omega

/-! ## §1. Finding 1 resolution & `evalRvalue` witnesses -/

/-- Canonical `f32` `Ty` for concrete `evalRvalue` witnesses. -/
private abbrev f32Ty : Ty := { kind := .float .f32, layoutIdx := 0 }

/-- Canonical `f16` `Ty` for fail-closed witnesses. -/
private abbrev f16Ty : Ty := { kind := .float .f16, layoutIdx := 0 }

/-- Canonical `f128` `Ty` for fail-closed witnesses. -/
private abbrev f128Ty : Ty := { kind := .float .f128, layoutIdx := 0 }

/-- Helper `ConstOperand` for a raw scalar constant of type `ty`. -/
private abbrev mkFloatConstOp (ty : Ty) (bits sizeBytes : Nat) : Operand :=
  .constant { ty := ty, val := .scalar (.int ⟨bits, sizeBytes⟩) }

/-- Finding 1 witness (unary `-`): `-1.0_f32` evaluates to `0xBF800000` (not integer
two's-complement negation) both at `evalFloatNeg` and through full `evalRvalue`. -/
theorem finding1_neg_one_f32 :
    evalFloatNeg .binary32 0x3F800000 = 0xBF800000 ∧
    evalRvalue .nil (.unaryOp .neg (mkFloatConstOp f32Ty 0x3F800000 4)) =
      .ok (.scalar ⟨0xBF800000, 4⟩) .nil emptyMemory := by
  exact ⟨rfl, rfl⟩

/-- Finding 1 witness (binary `+`): `1.0_f32 + 1.0_f32 = 2.0_f32` (`0x40000000`) both
at `evalFloatBinOp` and through full `evalRvalue`. -/
theorem finding1_add_one_one_f32 :
    evalFloatBinOp .add .binary32 0x3F800000 0x3F800000 = .some ⟨0x40000000, 4⟩ ∧
    evalRvalue .nil
        (.binaryOp .add (mkFloatConstOp f32Ty 0x3F800000 4) (mkFloatConstOp f32Ty 0x3F800000 4)) =
      .ok (.scalar ⟨0x40000000, 4⟩) .nil emptyMemory := by
  exact ⟨rfl, rfl⟩

/-- Finding 1 witness (IEEE comparisons): `-0.0_f32 == +0.0_f32` is `true`,
`qNaN == qNaN` is `false`, and `qNaN != qNaN` is `true` at both `evalFloatCmp`
and full `evalRvalue`. -/
theorem finding1_cmp_zero_and_nan_f32 :
    evalFloatCmp .eq .binary32 0x80000000 0x00000000 = .some true ∧
    evalFloatCmp .eq .binary32 0x7FC00000 0x7FC00000 = .some false ∧
    evalFloatCmp .ne .binary32 0x7FC00000 0x7FC00000 = .some true ∧
    evalRvalue .nil
        (.binaryOp .eq (mkFloatConstOp f32Ty 0x80000000 4) (mkFloatConstOp f32Ty 0x00000000 4)) =
      .ok (.scalar (boolToScalar true)) .nil emptyMemory ∧
    evalRvalue .nil
        (.binaryOp .eq (mkFloatConstOp f32Ty 0x7FC00000 4) (mkFloatConstOp f32Ty 0x7FC00000 4)) =
      .ok (.scalar (boolToScalar false)) .nil emptyMemory ∧
    evalRvalue .nil
        (.binaryOp .ne (mkFloatConstOp f32Ty 0x7FC00000 4) (mkFloatConstOp f32Ty 0x7FC00000 4)) =
      .ok (.scalar (boolToScalar true)) .nil emptyMemory := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Finding 1 fail-closed witness: unmodeled IEEE formats `f16` and `f128` return
`.unsupported` (never falling through to integer arithmetic) for both `.unaryOp .neg`
and `.binaryOp`. -/
theorem finding1_f16_f128_fail_closed :
    evalRvalue .nil (.unaryOp .neg (mkFloatConstOp f16Ty 0x3C00 2)) = .unsupported ∧
    evalRvalue .nil (.unaryOp .neg (mkFloatConstOp f128Ty 0 16)) = .unsupported ∧
    evalRvalue .nil
        (.binaryOp .add (mkFloatConstOp f16Ty 0x3C00 2) (mkFloatConstOp f16Ty 0x3C00 2)) =
      .unsupported ∧
    evalRvalue .nil
        (.binaryOp .add (mkFloatConstOp f128Ty 0 16) (mkFloatConstOp f128Ty 0 16)) =
      .unsupported := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## §2. Bitwise unary negation / abs & IEEE-754 comparisons -/

theorem evalFloatNeg_lt (f : IeeeFormat) (bits : Nat) :
    evalFloatNeg f bits < 2 ^ f.width := by
  have hw : 2 ^ f.width = 2 * 2 ^ (f.width - 1) := by
    have hpos : f.width = (f.width - 1) + 1 :=
      (show ∀ g : IeeeFormat, g.width = (g.width - 1) + 1 from fun g => by cases g <;> rfl) f
    calc 2 ^ f.width
      _ = 2 ^ ((f.width - 1) + 1) := congrArg (2 ^ ·) hpos
      _ = 2 ^ (f.width - 1) * 2 := Nat.pow_succ 2 (f.width - 1)
      _ = 2 * 2 ^ (f.width - 1) := Nat.mul_comm _ _
  have hmod : bits % 2 ^ f.width < 2 ^ f.width := Nat.mod_lt bits (Nat.two_pow_pos f.width)
  unfold evalFloatNeg
  dsimp only
  by_cases h : 2 ^ (f.width - 1) ≤ bits % 2 ^ f.width
  · rw [if_pos' h]; omega
  · rw [if_neg' h]; omega

theorem evalFloatNeg_mod (f : IeeeFormat) (bits : Nat) :
    evalFloatNeg f (bits % 2 ^ f.width) = evalFloatNeg f bits := by
  simp only [evalFloatNeg, Nat.mod_mod]

theorem evalFloatNeg_involutive (f : IeeeFormat) (bits : Nat) (h : bits < 2 ^ f.width) :
    evalFloatNeg f (evalFloatNeg f bits) = bits := by
  have hw : 2 ^ f.width = 2 * 2 ^ (f.width - 1) := by
    have hpos : f.width = (f.width - 1) + 1 :=
      (show ∀ g : IeeeFormat, g.width = (g.width - 1) + 1 from fun g => by cases g <;> rfl) f
    calc 2 ^ f.width
      _ = 2 ^ ((f.width - 1) + 1) := congrArg (2 ^ ·) hpos
      _ = 2 ^ (f.width - 1) * 2 := Nat.pow_succ 2 (f.width - 1)
      _ = 2 * 2 ^ (f.width - 1) := Nat.mul_comm _ _
  unfold evalFloatNeg
  dsimp only
  rw [Nat.mod_eq_of_lt h]
  by_cases h1 : 2 ^ (f.width - 1) ≤ bits
  · rw [if_pos' h1, Nat.mod_eq_of_lt (by omega), if_neg' (by omega)]; omega
  · rw [if_neg' h1, Nat.mod_eq_of_lt (by omega), if_pos' (by omega)]; omega

theorem evalFloatNeg_ne_self (f : IeeeFormat) (bits : Nat) (h : bits < 2 ^ f.width) :
    evalFloatNeg f bits ≠ bits := by
  have hs : 0 < 2 ^ (f.width - 1) := Nat.two_pow_pos (f.width - 1)
  unfold evalFloatNeg
  dsimp only
  rw [Nat.mod_eq_of_lt h]
  by_cases h1 : 2 ^ (f.width - 1) ≤ bits
  · rw [if_pos' h1]; omega
  · rw [if_neg' h1]; omega

theorem evalFloatAbs_lt (f : IeeeFormat) (bits : Nat) :
    evalFloatAbs f bits < 2 ^ (f.width - 1) :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

theorem evalFloatAbs_idempotent (f : IeeeFormat) (bits : Nat) :
    evalFloatAbs f (evalFloatAbs f bits) = evalFloatAbs f bits := by
  simp only [evalFloatAbs, Nat.mod_mod]

theorem evalFloatAbs_evalFloatNeg (f : IeeeFormat) (bits : Nat) :
    evalFloatAbs f (evalFloatNeg f bits) = evalFloatAbs f bits := by
  unfold evalFloatAbs evalFloatNeg
  dsimp only
  by_cases h : 2 ^ (f.width - 1) ≤ bits % 2 ^ f.width
  · rw [if_pos' h]
    cases f <;> simp only [IeeeFormat.width, Nat.reducePow, Nat.reduceSub] at h ⊢ <;> omega
  · rw [if_neg' h]
    cases f <;> simp only [IeeeFormat.width, Nat.reducePow, Nat.reduceSub] at h ⊢ <;> omega

theorem unpackBits_evalFloatNeg (f : IeeeFormat) (bits : Nat) :
    unpackBits f (evalFloatNeg f bits) =
      { neg := Bool.not (unpackBits f bits).neg
        exponent := (unpackBits f bits).exponent
        fraction := (unpackBits f bits).fraction } := by
  unfold evalFloatNeg
  dsimp only
  by_cases h : 2 ^ (f.width - 1) ≤ bits % 2 ^ f.width
  · rw [if_pos' h]
    cases f
    · simp only [unpackBits, IeeeFormat.width, IeeeFormat.fractionBits,
        IeeeFormat.exponentBits, Nat.reducePow, Nat.reduceSub, FloatComponents.mk.injEq,
        nat_beq_eq_decide] at h ⊢
      have h1 : (bits % 4294967296 - 2147483648) / 2147483648 % 2 = 0 := by omega
      have h2 : bits / 2147483648 % 2 = 1 := by omega
      rw [h1, h2]
      exact ⟨rfl, by omega, by omega⟩
    · simp only [unpackBits, IeeeFormat.width, IeeeFormat.fractionBits,
        IeeeFormat.exponentBits, Nat.reducePow, Nat.reduceSub, FloatComponents.mk.injEq,
        nat_beq_eq_decide] at h ⊢
      have h1 : (bits % 18446744073709551616 - 9223372036854775808) / 9223372036854775808 % 2 = 0 := by omega
      have h2 : bits / 9223372036854775808 % 2 = 1 := by omega
      rw [h1, h2]
      exact ⟨rfl, by omega, by omega⟩
  · rw [if_neg' h]
    cases f
    · simp only [unpackBits, IeeeFormat.width, IeeeFormat.fractionBits,
        IeeeFormat.exponentBits, Nat.reducePow, Nat.reduceSub, FloatComponents.mk.injEq,
        nat_beq_eq_decide] at h ⊢
      have h1 : (bits % 4294967296 + 2147483648) / 2147483648 % 2 = 1 := by omega
      have h2 : bits / 2147483648 % 2 = 0 := by omega
      rw [h1, h2]
      exact ⟨rfl, by omega, by omega⟩
    · simp only [unpackBits, IeeeFormat.width, IeeeFormat.fractionBits,
        IeeeFormat.exponentBits, Nat.reducePow, Nat.reduceSub, FloatComponents.mk.injEq,
        nat_beq_eq_decide] at h ⊢
      have h1 : (bits % 18446744073709551616 + 9223372036854775808) / 9223372036854775808 % 2 = 1 := by omega
      have h2 : bits / 9223372036854775808 % 2 = 0 := by omega
      rw [h1, h2]
      exact ⟨rfl, by omega, by omega⟩

theorem evalFloatNeg_encodeBits (f : IeeeFormat) (neg : Bool) (E F : Nat)
    (hE : E < 2 ^ f.exponentBits) (hF : F < 2 ^ f.fractionBits) :
    evalFloatNeg f (encodeBits f neg E F) = encodeBits f (Bool.not neg) E F := by
  have hlt := evalFloatNeg_lt f (encodeBits f neg E F)
  rw [← encodeBits_unpackBits f (evalFloatNeg f (encodeBits f neg E F)) hlt,
    unpackBits_evalFloatNeg, unpackBits_encodeBits f neg E F hE hF]

theorem evalFloatNeg_zeroBits (f : IeeeFormat) (neg : Bool) :
    evalFloatNeg f (zeroBits f neg) = zeroBits f (Bool.not neg) := by
  cases f <;> cases neg <;> decide

theorem evalFloatNeg_infBits (f : IeeeFormat) (neg : Bool) :
    evalFloatNeg f (infBits f neg) = infBits f (Bool.not neg) := by
  cases f <;> cases neg <;> decide

theorem decodeBits_evalFloatNeg (f : IeeeFormat) (bits : Nat) :
    decodeBits f (evalFloatNeg f bits) = negateFloatKind (decodeBits f bits) := by
  unfold decodeBits
  rw [unpackBits_evalFloatNeg]
  dsimp only
  split
  · split <;> rfl
  · split
    · split <;> rfl
    · rfl

theorem negateFloatKind_involutive (k : FloatKind) :
    negateFloatKind (negateFloatKind k) = k := by
  cases k <;> simp [negateFloatKind]

theorem isNaNBits_evalFloatNeg (f : IeeeFormat) (bits : Nat) :
    isNaNBits f (evalFloatNeg f bits) = isNaNBits f bits := by
  unfold isNaNBits
  rw [decodeBits_evalFloatNeg]
  cases decodeBits f bits <;> rfl

theorem isQuietNaNBits_evalFloatNeg (f : IeeeFormat) (bits : Nat) :
    isQuietNaNBits f (evalFloatNeg f bits) = isQuietNaNBits f bits := by
  unfold isQuietNaNBits
  rw [decodeBits_evalFloatNeg]
  cases decodeBits f bits <;> rfl

theorem isSignalingNaNBits_evalFloatNeg (f : IeeeFormat) (bits : Nat) :
    isSignalingNaNBits f (evalFloatNeg f bits) = isSignalingNaNBits f bits := by
  unfold isSignalingNaNBits
  rw [decodeBits_evalFloatNeg]
  cases decodeBits f bits <;> rfl

/-- Bitwise unary negation preserves every NaN's quiet/signaling bit and full payload
verbatim while flipping only its sign bit (matching Rust `core::primitive::f32` /
`f64` non-arithmetic NaN rules and `cl/1023458250`). -/
theorem evalFloatNeg_preserves_nan_payload (f : IeeeFormat) (bits : Nat) (neg q : Bool)
    (payload : Nat) (h : decodeBits f bits = .nan neg q payload) :
    decodeBits f (evalFloatNeg f bits) = .nan (Bool.not neg) q payload := by
  rw [decodeBits_evalFloatNeg, h]
  rfl

/-! ### IEEE-754 partial ordering and boolean comparisons -/

theorem evalFloatPartialCompare_none_iff (f : IeeeFormat) (a b : Nat) :
    evalFloatPartialCompare f a b = .none ↔ isNaNBits f a = true ∨ isNaNBits f b = true := by
  unfold evalFloatPartialCompare isNaNBits
  rw [decodeBits_mod, decodeBits_mod]
  cases decodeBits f a <;> cases decodeBits f b <;>
    simp [Bool.false_eq_true]

theorem evalFloatPartialCompare_nan_left (f : IeeeFormat) (a b : Nat)
    (ha : isNaNBits f a = true) :
    evalFloatPartialCompare f a b = .none :=
  (evalFloatPartialCompare_none_iff f a b).mpr (Or.inl ha)

theorem evalFloatPartialCompare_nan_right (f : IeeeFormat) (a b : Nat)
    (hb : isNaNBits f b = true) :
    evalFloatPartialCompare f a b = .none :=
  (evalFloatPartialCompare_none_iff f a b).mpr (Or.inr hb)

/-- Whenever either operand is NaN, `.ne` returns `.some true` and every other IEEE
comparison (`eq`, `lt`, `le`, `gt`, `ge`) returns `.some false`. -/
theorem evalFloatCmp_of_nan (f : IeeeFormat) (a b : Nat)
    (hnan : isNaNBits f a = true ∨ isNaNBits f b = true) :
    evalFloatCmp .eq f a b = .some false ∧
    evalFloatCmp .ne f a b = .some true ∧
    evalFloatCmp .lt f a b = .some false ∧
    evalFloatCmp .le f a b = .some false ∧
    evalFloatCmp .gt f a b = .some false ∧
    evalFloatCmp .ge f a b = .some false := by
  have hord : evalFloatPartialCompare f a b = .none :=
    (evalFloatPartialCompare_none_iff f a b).mpr hnan
  simp [evalFloatCmp, hord]

/-- `.ne` is always the boolean negation of `.eq`, including on NaNs. -/
theorem evalFloatCmp_ne_eq_not_eq (f : IeeeFormat) (a b : Nat) :
    evalFloatCmp .ne f a b = Option.map Bool.not (evalFloatCmp .eq f a b) := by
  unfold evalFloatCmp
  cases evalFloatPartialCompare f a b with
  | none => rfl
  | some ord => cases ord <;> rfl

/-- `-0.0 == +0.0` (and `+0.0 == -0.0`) holds in both `binary32` and `binary64`. -/
theorem evalFloatCmp_signed_zeros_eq (f : IeeeFormat) (neg₁ neg₂ : Bool) :
    evalFloatCmp .eq f (zeroBits f neg₁) (zeroBits f neg₂) = .some true ∧
    evalFloatCmp .ne f (zeroBits f neg₁) (zeroBits f neg₂) = .some false ∧
    evalFloatCmp .lt f (zeroBits f neg₁) (zeroBits f neg₂) = .some false ∧
    evalFloatCmp .gt f (zeroBits f neg₁) (zeroBits f neg₂) = .some false := by
  have hord : evalFloatPartialCompare f (zeroBits f neg₁) (zeroBits f neg₂) = .some .eq := by
    unfold evalFloatPartialCompare
    rw [decodeBits_mod, decodeBits_mod, decodeBits_zeroBits, decodeBits_zeroBits]
  simp [evalFloatCmp, hord]

/-- Trichotomy on non-NaN IEEE-754 bit patterns: `evalFloatPartialCompare` returns
exactly one of `.lt`, `.eq`, or `.gt`, so exactly one of `<`, `==`, `>` holds. -/
theorem evalFloatCmp_trichotomy (f : IeeeFormat) (a b : Nat)
    (ha : isNaNBits f a = false) (hb : isNaNBits f b = false) :
    (evalFloatCmp .lt f a b = .some true ∧
      evalFloatCmp .eq f a b = .some false ∧
      evalFloatCmp .gt f a b = .some false) ∨
    (evalFloatCmp .lt f a b = .some false ∧
      evalFloatCmp .eq f a b = .some true ∧
      evalFloatCmp .gt f a b = .some false) ∨
    (evalFloatCmp .lt f a b = .some false ∧
      evalFloatCmp .eq f a b = .some false ∧
      evalFloatCmp .gt f a b = .some true) := by
  cases hord : evalFloatPartialCompare f a b with
  | none =>
    have hnan := (evalFloatPartialCompare_none_iff f a b).mp hord
    rcases hnan with h | h
    · rw [ha] at h; cases h
    · rw [hb] at h; cases h
  | some ord =>
    cases ord
    · exact Or.inl (by simp [evalFloatCmp, hord])
    · exact Or.inr (Or.inl (by simp [evalFloatCmp, hord]))
    · exact Or.inr (Or.inr (by simp [evalFloatCmp, hord]))

/-- Reflexivity of `==` on non-NaN bit patterns. -/
theorem evalFloatPartialCompare_refl (f : IeeeFormat) (a : Nat)
    (ha : isNaNBits f a = false) :
    evalFloatPartialCompare f a a = .some .eq := by
  unfold evalFloatPartialCompare
  rw [decodeBits_mod]
  unfold isNaNBits at ha
  cases hdec : decodeBits f a with
  | nan _ _ _ => rw [hdec] at ha; cases ha
  | zero _ => rfl
  | inf neg => cases neg <;> rfl
  | finite neg n d =>
    dsimp only
    rw [if_neg' (by omega), if_pos' rfl]

theorem evalFloatCmp_eq_refl (f : IeeeFormat) (a : Nat) (ha : isNaNBits f a = false) :
    evalFloatCmp .eq f a a = .some true := by
  simp [evalFloatCmp, evalFloatPartialCompare_refl f a ha]

private def swapOrdering : Ordering → Ordering
  | .lt => .gt
  | .eq => .eq
  | .gt => .lt

/-- Antisymmetry of `evalFloatPartialCompare`: swapping operands swaps `.lt` and `.gt`
and preserves `.eq` and `.none`. -/
theorem evalFloatPartialCompare_swap (f : IeeeFormat) (a b : Nat) :
    evalFloatPartialCompare f b a = Option.map swapOrdering (evalFloatPartialCompare f a b) := by
  unfold evalFloatPartialCompare
  rw [decodeBits_mod, decodeBits_mod]
  cases ha : decodeBits f a with
  | zero ln =>
    cases hb : decodeBits f b with
    | zero rn => rfl
    | finite rn rnum rden =>
      dsimp only
      by_cases h0 : rnum = 0
      · rw [if_pos' h0, if_pos' h0]; rfl
      · rw [if_neg' h0, if_neg' h0]; cases rn <;> rfl
    | inf rn => cases rn <;> rfl
    | nan _ _ _ => rfl
  | finite ln lnum lden =>
    cases hb : decodeBits f b with
    | zero rn =>
      dsimp only
      by_cases h0 : lnum = 0
      · rw [if_pos' h0, if_pos' h0]; rfl
      · rw [if_neg' h0, if_neg' h0]; cases ln <;> rfl
    | finite rn rnum rden =>
      dsimp only
      by_cases hlt : signedNum ln lnum * (rden : Int) < signedNum rn rnum * (lden : Int)
      · rw [if_pos' hlt, if_neg' (by omega), if_neg' (by omega)]; rfl
      · rw [if_neg' hlt]
        by_cases heq : signedNum ln lnum * (rden : Int) = signedNum rn rnum * (lden : Int)
        · rw [if_pos' heq, if_neg' (by omega), if_pos' heq.symm]; rfl
        · rw [if_neg' heq, if_pos' (by omega)]; rfl
    | inf rn => cases rn <;> rfl
    | nan _ _ _ => rfl
  | inf ln =>
    cases hb : decodeBits f b with
    | zero _ => cases ln <;> rfl
    | finite _ _ _ => cases ln <;> rfl
    | inf rn => cases ln <;> cases rn <;> rfl
    | nan _ _ _ => rfl
  | nan _ _ _ =>
    cases hb : decodeBits f b <;> rfl

theorem evalFloatCmp_eq_symm (f : IeeeFormat) (a b : Nat) :
    evalFloatCmp .eq f b a = evalFloatCmp .eq f a b := by
  unfold evalFloatCmp
  rw [evalFloatPartialCompare_swap]
  cases evalFloatPartialCompare f a b with
  | none => rfl
  | some ord => cases ord <;> rfl

theorem evalFloatCmp_lt_gt_symm (f : IeeeFormat) (a b : Nat) :
    evalFloatCmp .lt f b a = evalFloatCmp .gt f a b := by
  unfold evalFloatCmp
  rw [evalFloatPartialCompare_swap]
  cases evalFloatPartialCompare f a b with
  | none => rfl
  | some ord => cases ord <;> rfl

theorem evalFloatCmp_le_ge_symm (f : IeeeFormat) (a b : Nat) :
    evalFloatCmp .le f b a = evalFloatCmp .ge f a b := by
  unfold evalFloatCmp
  rw [evalFloatPartialCompare_swap]
  cases evalFloatPartialCompare f a b with
  | none => rfl
  | some ord => cases ord <;> rfl

/-- Comparisons in `EvalFloatBinOpRel` are completely independent of `FloatArithMode`. -/
theorem EvalFloatBinOpRel_cmp_mode_independent
    (op : BinOp) (f : IeeeFormat) (a b : Nat) (out : ScalarInt) (res : Bool)
    (hcmp : evalFloatCmp op f a b = .some res) :
    EvalFloatBinOpRel .deterministic op f a b out ↔
      EvalFloatBinOpRel .nondeterministic op f a b out := by
  unfold EvalFloatBinOpRel
  rw [hcmp]

/-! ## §3. Single-rounding `roundTiesToEven`, Sterbenz's lemma, gradual underflow, `1.0` identity, & exact Euclidean `rem` -/

/-- Multiplicative numerator scale of `powScale X 1 t`. -/
private def powScaleMul : Int → Nat
  | .ofNat k => 2 ^ k
  | .negSucc _ => 1

/-- Denominator scale of `powScale X 1 t`. -/
private def powScaleDen : Int → Nat
  | .ofNat _ => 1
  | .negSucc k => 1 * 2 ^ (k + 1)

private theorem powScale_one_eq (X : Nat) (t : Int) :
    powScale X 1 t = (X * powScaleMul t, powScaleDen t) := by
  cases t with
  | ofNat k => rfl
  | negSucc k => simp [powScale, powScaleMul, powScaleDen]

private theorem powScaleMul_pos (t : Int) : 0 < powScaleMul t := by
  cases t with
  | ofNat k => exact Nat.two_pow_pos k
  | negSucc _ => exact Nat.zero_lt_one

private theorem powScaleDen_pos (t : Int) : 0 < powScaleDen t := by
  cases t with
  | ofNat _ => exact Nat.zero_lt_one
  | negSucc k =>
    simp only [powScaleDen, Nat.one_mul]
    exact Nat.two_pow_pos (k + 1)

/-- Every decoded finite float lies on the IEEE-754 dyadic grid `S * 2^t` with
`0 < S < 2^(fb + 1)` and `minExponent - fb ≤ t ≤ maxExponent - fb`. -/
theorem decodeBits_finite_grid (f : IeeeFormat) (bits : Nat) (neg : Bool) (n d : Nat)
    (h : decodeBits f bits = .finite neg n d) :
    ∃ (S : Nat) (t : Int),
      n = (powScale S 1 t).1 ∧
      d = (powScale S 1 t).2 ∧
      0 < S ∧
      S < 2 ^ (f.fractionBits + 1) ∧
      f.minExponent - (f.fractionBits : Int) ≤ t ∧
      t ≤ f.maxExponent - (f.fractionBits : Int) := by
  have hEl := unpackBits_exponent_lt f bits
  have hFl := unpackBits_fraction_lt f bits
  have h2b := IeeeFormat.two_bias_lt f
  unfold decodeBits at h
  simp only at h
  split at h
  · split at h <;> cases h
  · rename_i hEne
    split at h
    · split at h
      · cases h
      · rename_i hE0 hFne
        injection h with _ hn hd
        refine ⟨(unpackBits f bits).fraction, f.minExponent - (f.fractionBits : Int),
          hn.symm, hd.symm, Nat.pos_of_ne_zero hFne, ?_, Int.le_refl _, ?_⟩
        · have hlt := two_pow_lt_two_pow (Nat.lt_succ_self f.fractionBits)
          omega
        · simp only [IeeeFormat.minExponent, IeeeFormat.maxExponent]
          cases f <;> decide
    · rename_i hE0
      injection h with _ hn hd
      refine ⟨2 ^ f.fractionBits + (unpackBits f bits).fraction,
        ((unpackBits f bits).exponent : Int) - (f.bias : Int) - (f.fractionBits : Int),
        hn.symm, hd.symm, ?_, ?_, ?_, ?_⟩
      · have := Nat.two_pow_pos f.fractionBits; omega
      · have hpow : 2 ^ (f.fractionBits + 1) = 2 * 2 ^ f.fractionBits := by
          rw [Nat.pow_succ]; omega
        omega
      · simp only [IeeeFormat.minExponent]; omega
      · simp only [IeeeFormat.maxExponent]
        have hbias : 2 ^ f.exponentBits - 1 = 2 * f.bias + 1 := by cases f <;> decide
        omega

/-- **Exact IEEE-754 grid representability**: any positive dyadic rational `D * 2^t`
with `0 < D < 2^(fb + 1)` and `minExponent - fb ≤ t ≤ maxExponent - fb` rounds with
ZERO rounding error under `roundRatioTiesToEven` (across both normal and subnormal
regimes). -/
theorem roundRatioTiesToEven_exact_grid (f : IeeeFormat) (neg : Bool) (D : Nat) (t : Int)
    (hD0 : 0 < D) (hDlt : D < 2 ^ (f.fractionBits + 1))
    (htLo : f.minExponent - (f.fractionBits : Int) ≤ t)
    (htHi : t ≤ f.maxExponent - (f.fractionBits : Int)) :
    ∃ n' d',
      decodeBits f (roundRatioTiesToEven f neg (powScale D 1 t).1 (powScale D 1 t).2) =
        .finite neg n' d' ∧
      n' * (powScale D 1 t).2 = (powScale D 1 t).1 * d' ∧
      0 < d' := by
  by_cases hnorm : 2 ^ f.fractionBits ≤ D
  · rw [← roundRatioBits_tiesToEven]
    refine ⟨(powScale D 1 t).1, (powScale D 1 t).2, ?_, rfl, powScale_snd_pos D t⟩
    exact decodeBits_roundRatio_normal .tiesToEven f neg D t hnorm hDlt (by omega) (by omega)
  · have hDfb : D < 2 ^ f.fractionBits := Nat.lt_of_not_le hnorm
    have hDne : D ≠ 0 := Nat.pos_iff_ne_zero.mp hD0
    have hL1 : 2 ^ Nat.log2 D ≤ D := Nat.log2_self_le hDne
    have hL2 : D < 2 ^ (Nat.log2 D + 1) := Nat.lt_log2_self
    have hLlt : Nat.log2 D < f.fractionBits := (Nat.log2_lt hDne).mpr hDfb
    let k : Nat := f.fractionBits - Nat.log2 D
    let room : Nat := (t - (f.minExponent - (f.fractionBits : Int))).toNat
    have hroom_eq : (room : Int) = t - (f.minExponent - (f.fractionBits : Int)) :=
      Int.toNat_of_nonneg (by omega)
    by_cases hk : k ≤ room
    · let S' : Nat := D * 2 ^ k
      let t' : Int := t - (k : Int)
      have hS1 : 2 ^ f.fractionBits ≤ S' := by
        have hsum : Nat.log2 D + k = f.fractionBits := by omega
        rw [← hsum, ← pow_mul_pow]
        exact Nat.mul_le_mul_right (2 ^ k) hL1
      have hS2 : S' < 2 ^ (f.fractionBits + 1) := by
        have hsum : Nat.log2 D + 1 + k = f.fractionBits + 1 := by omega
        rw [← hsum, ← pow_mul_pow]
        exact Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos k)
      have hcross := powScale_shift_cross D k t
      have hcongr :
          roundRatioBits .tiesToEven f neg (powScale D 1 t).1 (powScale D 1 t).2 =
            roundRatioBits .tiesToEven f neg (powScale S' 1 t').1 (powScale S' 1 t').2 :=
        roundRatioBits_congr .tiesToEven f neg _ _ _ _
          (powScale_snd_pos D t) (powScale_snd_pos S' t') hcross.symm
      rw [← roundRatioBits_tiesToEven, hcongr]
      refine ⟨(powScale S' 1 t').1, (powScale S' 1 t').2, ?_, hcross, powScale_snd_pos S' t'⟩
      exact decodeBits_roundRatio_normal .tiesToEven f neg S' t' hS1 hS2 (by omega) (by omega)
    · let S' : Nat := D * 2 ^ room
      have hS0 : 0 < S' := Nat.mul_pos hD0 (Nat.two_pow_pos room)
      have hSlt : S' < 2 ^ f.fractionBits := by
        have hmul : S' < 2 ^ (Nat.log2 D + 1 + room) := by
          rw [← pow_mul_pow]
          exact Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos room)
        have hle : 2 ^ (Nat.log2 D + 1 + room) ≤ 2 ^ f.fractionBits :=
          two_pow_le_two_pow (by omega)
        exact Nat.lt_of_lt_of_le hmul hle
      have ht'_eq : t - (room : Int) = f.minExponent - (f.fractionBits : Int) := by omega
      have hcross := powScale_shift_cross D room t
      rw [ht'_eq] at hcross
      have hcongr :
          roundRatioBits .tiesToEven f neg (powScale D 1 t).1 (powScale D 1 t).2 =
            roundRatioBits .tiesToEven f neg
              (powScale S' 1 (f.minExponent - (f.fractionBits : Int))).1
              (powScale S' 1 (f.minExponent - (f.fractionBits : Int))).2 :=
        roundRatioBits_congr .tiesToEven f neg _ _ _ _
          (powScale_snd_pos D t) (powScale_snd_pos S' _) hcross.symm
      rw [← roundRatioBits_tiesToEven, hcongr]
      refine ⟨(powScale S' 1 (f.minExponent - (f.fractionBits : Int))).1,
        (powScale S' 1 (f.minExponent - (f.fractionBits : Int))).2,
        decodeBits_roundRatio_subnormal .tiesToEven f neg S' hS0 hSlt,
        hcross, powScale_snd_pos S' _⟩

/-- Align two grid points `(n1, d1) = powScale S1 1 t1` and `(n2, d2) = powScale S2 1 t2`
onto their common finer grid `t = min t1 t2`. -/
private theorem powScale_common_grid (S1 S2 : Nat) (t1 t2 : Int) :
    let t := min t1 t2
    let A := S1 * 2 ^ (t1 - t).toNat
    let B := S2 * 2 ^ (t2 - t).toNat
    (powScale A 1 t).1 * (powScale S1 1 t1).2 = (powScale S1 1 t1).1 * (powScale A 1 t).2 ∧
    (powScale B 1 t).1 * (powScale S2 1 t2).2 = (powScale S2 1 t2).1 * (powScale B 1 t).2 := by
  dsimp only
  have h1 : t1 - ((t1 - min t1 t2).toNat : Int) = min t1 t2 := by
    have hnn : ((t1 - min t1 t2).toNat : Int) = t1 - min t1 t2 := Int.toNat_of_nonneg (by omega)
    omega
  have h2 : t2 - ((t2 - min t1 t2).toNat : Int) = min t1 t2 := by
    have hnn : ((t2 - min t1 t2).toNat : Int) = t2 - min t1 t2 := Int.toNat_of_nonneg (by omega)
    omega
  have hc1 := powScale_shift_cross S1 (t1 - min t1 t2).toNat t1
  have hc2 := powScale_shift_cross S2 (t2 - min t1 t2).toNat t2
  rw [h1] at hc1
  rw [h2] at hc2
  exact ⟨hc1, hc2⟩

/-! ### Single-rounding `roundTiesToEven` characterizations (`add`, `sub`, `mul`, `div`) -/

/-- Exact single-rounding characterization of `evalFloatArithBase .add` on finite operands:
the result is `roundRatioTiesToEven` applied once to the exact rational sum
`((-1)^ln * lnum/lden) + ((-1)^rn * rnum/rden)`. -/
theorem evalFloatArithBase_add_finite (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (ha : decodeBits f (a % 2 ^ f.width) = .finite ln lnum lden)
    (hb : decodeBits f (b % 2 ^ f.width) = .finite rn rnum rden) :
    let n : Int := signedNum ln lnum * (rden : Int) + signedNum rn rnum * (lden : Int)
    let sign : Bool := if n = 0 then false else decide (n < 0)
    evalFloatArithBase .add f a b = .some (roundRatioTiesToEven f sign n.natAbs (lden * rden)) := by
  have hlpos := decodeBits_finite_num_pos f (a % 2 ^ f.width) ln lnum lden ha
  have hlne : Nat.beq lnum 0 = false := by
    rw [nat_beq_eq_decide]; exact decide_eq_false (by omega)
  unfold evalFloatArithBase
  simp only [ha, hb, exactSumFloat, hlne, Bool.false_and]

/-- Exact single-rounding characterization of `evalFloatArithBase .sub` on finite operands. -/
theorem evalFloatArithBase_sub_finite (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (ha : decodeBits f (a % 2 ^ f.width) = .finite ln lnum lden)
    (hb : decodeBits f (b % 2 ^ f.width) = .finite rn rnum rden) :
    let n : Int := signedNum ln lnum * (rden : Int) + signedNum (Bool.not rn) rnum * (lden : Int)
    let sign : Bool := if n = 0 then false else decide (n < 0)
    evalFloatArithBase .sub f a b = .some (roundRatioTiesToEven f sign n.natAbs (lden * rden)) := by
  have hlpos := decodeBits_finite_num_pos f (a % 2 ^ f.width) ln lnum lden ha
  have hlne : Nat.beq lnum 0 = false := by
    rw [nat_beq_eq_decide]; exact decide_eq_false (by omega)
  unfold evalFloatArithBase
  simp only [ha, hb, negateFloatKind, exactSumFloat, hlne, Bool.false_and]

/-- Exact single-rounding characterization of `evalFloatArithBase .mul` on finite operands. -/
theorem evalFloatArithBase_mul_finite (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (ha : decodeBits f (a % 2 ^ f.width) = .finite ln lnum lden)
    (hb : decodeBits f (b % 2 ^ f.width) = .finite rn rnum rden) :
    evalFloatArithBase .mul f a b =
      .some (roundRatioTiesToEven f (Bool.xor ln rn) (lnum * rnum) (lden * rden)) := by
  unfold evalFloatArithBase
  simp only [ha, hb]

/-- Exact single-rounding characterization of `evalFloatArithBase .div` on finite operands. -/
theorem evalFloatArithBase_div_finite (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (ha : decodeBits f (a % 2 ^ f.width) = .finite ln lnum lden)
    (hb : decodeBits f (b % 2 ^ f.width) = .finite rn rnum rden) :
    evalFloatArithBase .div f a b =
      .some (roundRatioTiesToEven f (Bool.xor ln rn) (lnum * rden) (lden * rnum)) := by
  have hrpos := decodeBits_finite_num_pos f (b % 2 ^ f.width) rn rnum rden hb
  unfold evalFloatArithBase
  simp only [ha, hb]
  rw [if_neg' (by omega)]

/-- Direct bridge connecting `evalFloatArithBase .mul` on finite operands to
`roundRatioTiesToEven_correctly_rounded` (half-ULP + ties-to-even). -/
theorem evalFloatArithBase_mul_correctly_rounded (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (ha : decodeBits f (a % 2 ^ f.width) = .finite ln lnum lden)
    (hb : decodeBits f (b % 2 ^ f.width) = .finite rn rnum rden) :
    let n := lnum * rnum
    let d := lden * rden
    let exponent := max (ratioExponent n d) f.minExponent
    let scaled := powScale n d ((f.fractionBits : Int) - exponent)
    let sig := roundQuotientTiesToEven scaled.1 scaled.2
    ∃ outBits,
      evalFloatArithBase .mul f a b = .some outBits ∧
      2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs ≤ scaled.2 ∧
      (2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs = scaled.2 → sig % 2 = 0) ∧
      (decodeBits f outBits ≠ .inf (Bool.xor ln rn) →
        floatKindSameValue (decodeBits f outBits)
          (if sig = 0 then .zero (Bool.xor ln rn)
           else .finite (Bool.xor ln rn) (powScale sig 1 (exponent - f.fractionBits)).1
             (powScale sig 1 (exponent - f.fractionBits)).2)) := by
  have hln := decodeBits_finite_num_pos f _ ln lnum lden ha
  have hld := decodeBits_finite_den_pos f _ ln lnum lden ha
  have hrn := decodeBits_finite_num_pos f _ rn rnum rden hb
  have hrd := decodeBits_finite_den_pos f _ rn rnum rden hb
  have hh := roundRatioTiesToEven_float_half_ulp f (Bool.xor ln rn) (lnum * rnum) (lden * rden)
    (Nat.mul_pos hln hrn) (Nat.mul_pos hld hrd)
  refine ⟨roundRatioTiesToEven f (Bool.xor ln rn) (lnum * rnum) (lden * rden),
    evalFloatArithBase_mul_finite f a b ln rn lnum lden rnum rden ha hb, hh⟩

/-- Direct bridge connecting `evalFloatArithBase .div` on finite operands to
`roundRatioTiesToEven_correctly_rounded` (half-ULP + ties-to-even). -/
theorem evalFloatArithBase_div_correctly_rounded (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (ha : decodeBits f (a % 2 ^ f.width) = .finite ln lnum lden)
    (hb : decodeBits f (b % 2 ^ f.width) = .finite rn rnum rden) :
    let n := lnum * rden
    let d := lden * rnum
    let exponent := max (ratioExponent n d) f.minExponent
    let scaled := powScale n d ((f.fractionBits : Int) - exponent)
    let sig := roundQuotientTiesToEven scaled.1 scaled.2
    ∃ outBits,
      evalFloatArithBase .div f a b = .some outBits ∧
      2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs ≤ scaled.2 ∧
      (2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs = scaled.2 → sig % 2 = 0) ∧
      (decodeBits f outBits ≠ .inf (Bool.xor ln rn) →
        floatKindSameValue (decodeBits f outBits)
          (if sig = 0 then .zero (Bool.xor ln rn)
           else .finite (Bool.xor ln rn) (powScale sig 1 (exponent - f.fractionBits)).1
             (powScale sig 1 (exponent - f.fractionBits)).2)) := by
  have hln := decodeBits_finite_num_pos f _ ln lnum lden ha
  have hld := decodeBits_finite_den_pos f _ ln lnum lden ha
  have hrn := decodeBits_finite_num_pos f _ rn rnum rden hb
  have hrd := decodeBits_finite_den_pos f _ rn rnum rden hb
  have hh := roundRatioTiesToEven_float_half_ulp f (Bool.xor ln rn) (lnum * rden) (lden * rnum)
    (Nat.mul_pos hln hrd) (Nat.mul_pos hld hrn)
  refine ⟨roundRatioTiesToEven f (Bool.xor ln rn) (lnum * rden) (lden * rnum),
    evalFloatArithBase_div_finite f a b ln rn lnum lden rnum rden ha hb, hh⟩

/-! ### Sterbenz's exact subtraction, exact addition, gradual underflow, `1.0` identity, & exact Euclidean `rem` -/

/-- **Sterbenz's Lemma (exact subtraction)**: for any two positive finite IEEE-754
floats `x = lnum / lden` and `y = rnum / rden` satisfying `y / 2 ≤ x ≤ 2 * y`
(expressed without division as `rnum * lden ≤ 2 * lnum * rden ∧ lnum * rden ≤ 2 * rnum * lden`),
`evalFloatArithBase .sub f a b` represents the exact rational difference `x - y`
with **zero rounding error** (producing `+0.0` when `x = y`, and an exact finite
value matching `|x - y|` with sign `x < y` otherwise). -/
theorem sterbenz_sub_exact (f : IeeeFormat) (a b : Nat)
    (lnum lden rnum rden : Nat)
    (ha : decodeBits f (a % 2 ^ f.width) = .finite false lnum lden)
    (hb : decodeBits f (b % 2 ^ f.width) = .finite false rnum rden)
    (hlo : rnum * lden ≤ 2 * (lnum * rden))
    (hhi : lnum * rden ≤ 2 * (rnum * lden)) :
    ∃ outBits,
      evalFloatArithBase .sub f a b = .some outBits ∧
      if lnum * rden = rnum * lden then
        outBits = zeroBits f false
      else
        let sign := decide (lnum * rden < rnum * lden)
        let diff := if lnum * rden < rnum * lden then rnum * lden - lnum * rden
                    else lnum * rden - rnum * lden
        ∃ n' d', decodeBits f outBits = .finite sign n' d' ∧
          n' * (lden * rden) = diff * d' := by
  have hsub := evalFloatArithBase_sub_finite f a b false false lnum lden rnum rden ha hb
  dsimp only [signedNum, Bool.not_false] at hsub
  obtain ⟨S1, t1, hn1, hd1, _, hS1lt, ht1Lo, ht1Hi⟩ := decodeBits_finite_grid f _ false lnum lden ha
  obtain ⟨S2, t2, hn2, hd2, _, hS2lt, ht2Lo, ht2Hi⟩ := decodeBits_finite_grid f _ false rnum rden hb
  have hld : 0 < lden := decodeBits_finite_den_pos f _ false lnum lden ha
  have hrd : 0 < rden := decodeBits_finite_den_pos f _ false rnum rden hb
  let t : Int := min t1 t2
  let A : Nat := S1 * 2 ^ (t1 - t).toNat
  let B : Nat := S2 * 2 ^ (t2 - t).toNat
  have hgrid := powScale_common_grid S1 S2 t1 t2
  have hAeq : A * powScaleMul t * lden = lnum * powScaleDen t := by
    have hc := hgrid.1
    rw [← hn1, ← hd1, powScale_one_eq] at hc
    exact hc
  have hBeq : B * powScaleMul t * rden = rnum * powScaleDen t := by
    have hc := hgrid.2
    rw [← hn2, ← hd2, powScale_one_eq] at hc
    exact hc
  have hDenPos : 0 < powScaleDen t := powScaleDen_pos t
  have hMulPos : 0 < powScaleMul t := powScaleMul_pos t
  have hCpos : 0 < powScaleMul t * (lden * rden) := Nat.mul_pos hMulPos (Nat.mul_pos hld hrd)
  have hAC : lnum * rden * powScaleDen t = A * (powScaleMul t * (lden * rden)) := by
    calc lnum * rden * powScaleDen t
      _ = (lnum * powScaleDen t) * rden := by rw [Nat.mul_right_comm]
      _ = (A * powScaleMul t * lden) * rden := by rw [← hAeq]
      _ = A * (powScaleMul t * (lden * rden)) := by rw [Nat.mul_assoc, Nat.mul_assoc]
  have hBC : rnum * lden * powScaleDen t = B * (powScaleMul t * (lden * rden)) := by
    calc rnum * lden * powScaleDen t
      _ = (rnum * powScaleDen t) * lden := by rw [Nat.mul_right_comm]
      _ = (B * powScaleMul t * rden) * lden := by rw [← hBeq]
      _ = B * (powScaleMul t * (lden * rden)) := by
        rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm rden lden]
  have hB_le_2A : B ≤ 2 * A := by
    apply (nat_mul_le_mul_right_iff hCpos).mp
    calc B * (powScaleMul t * (lden * rden))
      _ = rnum * lden * powScaleDen t := hBC.symm
      _ ≤ 2 * (lnum * rden) * powScaleDen t := Nat.mul_le_mul_right (powScaleDen t) hlo
      _ = 2 * (lnum * rden * powScaleDen t) := Nat.mul_assoc 2 (lnum * rden) (powScaleDen t)
      _ = 2 * (A * (powScaleMul t * (lden * rden))) := by rw [hAC]
      _ = 2 * A * (powScaleMul t * (lden * rden)) := (Nat.mul_assoc 2 A _).symm
  have hA_le_2B : A ≤ 2 * B := by
    apply (nat_mul_le_mul_right_iff hCpos).mp
    calc A * (powScaleMul t * (lden * rden))
      _ = lnum * rden * powScaleDen t := hAC.symm
      _ ≤ 2 * (rnum * lden) * powScaleDen t := Nat.mul_le_mul_right (powScaleDen t) hhi
      _ = 2 * (rnum * lden * powScaleDen t) := Nat.mul_assoc 2 (rnum * lden) (powScaleDen t)
      _ = 2 * (B * (powScaleMul t * (lden * rden))) := by rw [hBC]
      _ = 2 * B * (powScaleMul t * (lden * rden)) := (Nat.mul_assoc 2 B _).symm
  have htLo : f.minExponent - (f.fractionBits : Int) ≤ t := by
    show f.minExponent - (f.fractionBits : Int) ≤ min t1 t2
    omega
  have htHi : t ≤ f.maxExponent - (f.fractionBits : Int) := by
    show min t1 t2 ≤ f.maxExponent - (f.fractionBits : Int)
    omega
  have hmin_lt : A < 2 ^ (f.fractionBits + 1) ∨ B < 2 ^ (f.fractionBits + 1) := by
    by_cases h : t1 ≤ t2
    · left
      have h0 : (t1 - t).toNat = 0 := by
        show (t1 - min t1 t2).toNat = 0; omega
      show S1 * 2 ^ (t1 - t).toNat < 2 ^ (f.fractionBits + 1)
      rw [h0, Nat.pow_zero, Nat.mul_one]
      exact hS1lt
    · right
      have h0 : (t2 - t).toNat = 0 := by
        show (t2 - min t1 t2).toNat = 0; omega
      show S2 * 2 ^ (t2 - t).toNat < 2 ^ (f.fractionBits + 1)
      rw [h0, Nat.pow_zero, Nat.mul_one]
      exact hS2lt
  let nInt : Int := (lnum : Int) * (rden : Int) + -((rnum : Int)) * (lden : Int)
  let sign0 : Bool := if nInt = 0 then false else decide (nInt < 0)
  refine ⟨roundRatioTiesToEven f sign0 nInt.natAbs (lden * rden), hsub, ?_⟩
  by_cases heq : lnum * rden = rnum * lden
  · rw [if_pos' heq]
    have hn0 : nInt = 0 := by
      show (lnum : Int) * (rden : Int) + -((rnum : Int)) * (lden : Int) = 0
      have hcast : ((lnum * rden : Nat) : Int) = ((rnum * lden : Nat) : Int) := congrArg Int.ofNat heq
      simp only [Int.natCast_mul] at hcast
      rw [Int.neg_mul]
      omega
    have hsign0 : sign0 = false := by simp only [sign0, hn0, ↓reduceIte]
    rw [hsign0, hn0]
    exact roundRatioTiesToEven_zero f false (lden * rden) (Nat.mul_pos hld hrd)
  · rw [if_neg' heq]
    dsimp only
    by_cases hlt : lnum * rden < rnum * lden
    · rw [if_pos' hlt]
      have hABlt : A < B := by
        apply (nat_mul_lt_mul_right_iff hCpos).mp
        rw [← hAC, ← hBC]
        exact Nat.mul_lt_mul_of_pos_right hlt hDenPos
      have hD0 : 0 < B - A := by omega
      have hDlt : B - A < 2 ^ (f.fractionBits + 1) := by
        rcases hmin_lt with hA | hB <;> omega
      have hnNeg : nInt < 0 := by
        show (lnum : Int) * (rden : Int) + -((rnum : Int)) * (lden : Int) < 0
        have hcast : ((lnum * rden : Nat) : Int) < ((rnum * lden : Nat) : Int) :=
          Int.ofNat_lt.mpr hlt
        simp only [Int.natCast_mul] at hcast
        rw [Int.neg_mul]
        omega
      have hsign0 : sign0 = true := by
        simp only [sign0]
        rw [if_neg' (by omega)]
        exact decide_eq_true hnNeg
      have hnatAbs : nInt.natAbs = rnum * lden - lnum * rden := by
        have hcast : ((rnum * lden - lnum * rden : Nat) : Int) = -nInt := by
          have hle : lnum * rden ≤ rnum * lden := Nat.le_of_lt hlt
          rw [Int.ofNat_sub hle]
          simp only [nInt, Int.natCast_mul, Int.neg_mul]
          omega
        have := congrArg Int.natAbs hcast
        simpa using this.symm
      have hcross : (rnum * lden - lnum * rden) * (powScale (B - A) 1 t).2 =
          (powScale (B - A) 1 t).1 * (lden * rden) := by
        rw [powScale_one_eq]
        dsimp only
        rw [Nat.sub_mul, hBC, hAC, ← Nat.sub_mul, Nat.mul_assoc]
      have hcongr :
          roundRatioTiesToEven f true (rnum * lden - lnum * rden) (lden * rden) =
            roundRatioTiesToEven f true (powScale (B - A) 1 t).1 (powScale (B - A) 1 t).2 := by
        rw [← roundRatioBits_tiesToEven, ← roundRatioBits_tiesToEven]
        exact roundRatioBits_congr .tiesToEven f true _ _ _ _
          (Nat.mul_pos hld hrd) (powScale_snd_pos (B - A) t) hcross
      obtain ⟨n', d', hdec, hrat, _⟩ :=
        roundRatioTiesToEven_exact_grid f true (B - A) t hD0 hDlt htLo htHi
      rw [decide_eq_true hlt, hsign0, hnatAbs, hcongr]
      refine ⟨n', d', hdec, ?_⟩
      apply (nat_mul_eq_mul_right_iff hDenPos).mp
      have hden_eq : (powScale (B - A) 1 t).2 = powScaleDen t := by
        rw [powScale_one_eq]
      calc n' * (lden * rden) * powScaleDen t
        _ = n' * (powScale (B - A) 1 t).2 * (lden * rden) := by
          rw [hden_eq, Nat.mul_right_comm]
        _ = (powScale (B - A) 1 t).1 * d' * (lden * rden) := by rw [hrat]
        _ = (powScale (B - A) 1 t).1 * (lden * rden) * d' := by rw [Nat.mul_right_comm]
        _ = (rnum * lden - lnum * rden) * (powScale (B - A) 1 t).2 * d' := by rw [← hcross]
        _ = (rnum * lden - lnum * rden) * d' * powScaleDen t := by
          rw [hden_eq, Nat.mul_right_comm]
    · rw [if_neg' hlt]
      have hgt : rnum * lden < lnum * rden := by omega
      have hBAlt : B < A := by
        apply (nat_mul_lt_mul_right_iff hCpos).mp
        rw [← hAC, ← hBC]
        exact Nat.mul_lt_mul_of_pos_right hgt hDenPos
      have hD0 : 0 < A - B := by omega
      have hDlt : A - B < 2 ^ (f.fractionBits + 1) := by
        rcases hmin_lt with hA | hB <;> omega
      have hnPos : 0 < nInt := by
        show 0 < (lnum : Int) * (rden : Int) + -((rnum : Int)) * (lden : Int)
        have hcast : ((rnum * lden : Nat) : Int) < ((lnum * rden : Nat) : Int) :=
          Int.ofNat_lt.mpr hgt
        simp only [Int.natCast_mul] at hcast
        rw [Int.neg_mul]
        omega
      have hsign0 : sign0 = false := by
        simp only [sign0]
        rw [if_neg' (by omega)]
        exact decide_eq_false (by omega)
      have hnatAbs : nInt.natAbs = lnum * rden - rnum * lden := by
        have hcast : ((lnum * rden - rnum * lden : Nat) : Int) = nInt := by
          have hle : rnum * lden ≤ lnum * rden := Nat.le_of_lt hgt
          rw [Int.ofNat_sub hle]
          simp only [nInt, Int.natCast_mul, Int.neg_mul]
          omega
        have := congrArg Int.natAbs hcast
        simpa using this.symm
      have hcross : (lnum * rden - rnum * lden) * (powScale (A - B) 1 t).2 =
          (powScale (A - B) 1 t).1 * (lden * rden) := by
        rw [powScale_one_eq]
        dsimp only
        rw [Nat.sub_mul, hAC, hBC, ← Nat.sub_mul, Nat.mul_assoc]
      have hcongr :
          roundRatioTiesToEven f false (lnum * rden - rnum * lden) (lden * rden) =
            roundRatioTiesToEven f false (powScale (A - B) 1 t).1 (powScale (A - B) 1 t).2 := by
        rw [← roundRatioBits_tiesToEven, ← roundRatioBits_tiesToEven]
        exact roundRatioBits_congr .tiesToEven f false _ _ _ _
          (Nat.mul_pos hld hrd) (powScale_snd_pos (A - B) t) hcross
      obtain ⟨n', d', hdec, hrat, _⟩ :=
        roundRatioTiesToEven_exact_grid f false (A - B) t hD0 hDlt htLo htHi
      rw [decide_eq_false hlt, hsign0, hnatAbs, hcongr]
      refine ⟨n', d', hdec, ?_⟩
      apply (nat_mul_eq_mul_right_iff hDenPos).mp
      have hden_eq : (powScale (A - B) 1 t).2 = powScaleDen t := by
        rw [powScale_one_eq]
      calc n' * (lden * rden) * powScaleDen t
        _ = n' * (powScale (A - B) 1 t).2 * (lden * rden) := by
          rw [hden_eq, Nat.mul_right_comm]
        _ = (powScale (A - B) 1 t).1 * d' * (lden * rden) := by rw [hrat]
        _ = (powScale (A - B) 1 t).1 * (lden * rden) * d' := by rw [Nat.mul_right_comm]
        _ = (lnum * rden - rnum * lden) * (powScale (A - B) 1 t).2 * d' := by rw [← hcross]
        _ = (lnum * rden - rnum * lden) * d' * powScaleDen t := by
          rw [hden_eq, Nat.mul_right_comm]

/-- **Exact addition on bounded-significand same-sign grid operands**: whenever two
same-sign finite values on a common grid `t ∈ [minExponent - fb, maxExponent - fb]`
satisfy `S1 + S2 < 2^(fb + 1)`, `evalFloatArithBase .add` produces the exact sum with
zero rounding error. -/
theorem exact_add_same_sign_grid (f : IeeeFormat) (a b : Nat) (neg : Bool)
    (S1 S2 : Nat) (t : Int)
    (ha : decodeBits f (a % 2 ^ f.width) = .finite neg (powScale S1 1 t).1 (powScale S1 1 t).2)
    (hb : decodeBits f (b % 2 ^ f.width) = .finite neg (powScale S2 1 t).1 (powScale S2 1 t).2)
    (hsum : S1 + S2 < 2 ^ (f.fractionBits + 1))
    (htLo : f.minExponent - (f.fractionBits : Int) ≤ t)
    (htHi : t ≤ f.maxExponent - (f.fractionBits : Int)) :
    ∃ outBits n' d',
      evalFloatArithBase .add f a b = .some outBits ∧
      decodeBits f outBits = .finite neg n' d' ∧
      n' * (powScale (S1 + S2) 1 t).2 = (powScale (S1 + S2) 1 t).1 * d' := by
  have hadd := evalFloatArithBase_add_finite f a b neg neg _ _ _ _ ha hb
  have hS1pos : 0 < (powScale S1 1 t).1 := decodeBits_finite_num_pos f _ neg _ _ ha
  have hS1 : 0 < S1 := by
    rw [powScale_one_eq] at hS1pos
    cases S1 with
    | zero => simp at hS1pos
    | succ k => exact Nat.succ_pos k
  have hDenPos := powScaleDen_pos t
  have hMulPos := powScaleMul_pos t
  have hnum_eq :
      (signedNum neg (powScale S1 1 t).1 * ((powScale S2 1 t).2 : Int) +
       signedNum neg (powScale S2 1 t).1 * ((powScale S1 1 t).2 : Int)) =
        signedNum neg ((powScale (S1 + S2) 1 t).1 * powScaleDen t) := by
    rw [powScale_one_eq S1 t, powScale_one_eq S2 t, powScale_one_eq (S1 + S2) t]
    dsimp only
    cases neg with
    | false =>
      simp only [signedNum, Bool.false_eq_true, ↓reduceIte, Nat.add_mul, Int.natCast_add, Int.natCast_mul]
    | true =>
      simp only [signedNum, ↓reduceIte, Nat.add_mul, Int.natCast_add, Int.natCast_mul, Int.neg_mul]
      omega
  have hpos_prod : 0 < (powScale (S1 + S2) 1 t).1 * powScaleDen t := by
    rw [powScale_one_eq]
    exact Nat.mul_pos (Nat.mul_pos (by omega) hMulPos) hDenPos
  have hne0 : signedNum neg ((powScale (S1 + S2) 1 t).1 * powScaleDen t) ≠ 0 := by
    cases neg with
    | false => simp only [signedNum, Bool.false_eq_true, ↓reduceIte]; omega
    | true => simp only [signedNum, ↓reduceIte]; omega
  have hsign : (if signedNum neg ((powScale (S1 + S2) 1 t).1 * powScaleDen t) = 0 then false
      else decide (signedNum neg ((powScale (S1 + S2) 1 t).1 * powScaleDen t) < 0)) = neg := by
    rw [if_neg' hne0]
    cases neg with
    | true => exact decide_eq_true ((signedNum_neg_iff true _ hpos_prod).mpr rfl)
    | false =>
      exact decide_eq_false (fun h => Bool.noConfusion ((signedNum_neg_iff false _ hpos_prod).mp h))
  have hnatAbs : (signedNum neg ((powScale (S1 + S2) 1 t).1 * powScaleDen t)).natAbs =
      (powScale (S1 + S2) 1 t).1 * powScaleDen t := by
    cases neg with
    | false => exact Int.natAbs_natCast ((powScale (S1 + S2) 1 t).1 * powScaleDen t)
    | true =>
      change (-(((powScale (S1 + S2) 1 t).1 * powScaleDen t : Nat) : Int)).natAbs = _
      rw [Int.natAbs_neg, Int.natAbs_natCast]
  dsimp only at hadd
  rw [hnum_eq, hsign, hnatAbs] at hadd
  have hden_mul : (powScale S1 1 t).2 * (powScale S2 1 t).2 =
      (powScale (S1 + S2) 1 t).2 * powScaleDen t := by
    rw [powScale_one_eq S1 t, powScale_one_eq S2 t, powScale_one_eq (S1 + S2) t]
  rw [hden_mul, ← roundRatioBits_tiesToEven,
    roundRatioBits_mul .tiesToEven f neg _ _ (powScaleDen t) hDenPos,
    roundRatioBits_tiesToEven] at hadd
  obtain ⟨n', d', hdec, hrat, _⟩ :=
    roundRatioTiesToEven_exact_grid f neg (S1 + S2) t (by omega) hsum htLo htHi
  exact ⟨roundRatioTiesToEven f neg (powScale (S1 + S2) 1 t).1 (powScale (S1 + S2) 1 t).2,
    n', d', hadd, hdec, hrat⟩

/-- Helper: any positive rational at least as large as the smallest positive subnormal
`2^(minExponent - fb)` never rounds to `±0.0`. -/
private theorem roundRatioTiesToEven_ne_zeroBits_of_ge_minSubnormal
    (f : IeeeFormat) (sign zsign : Bool) (n d : Nat)
    (hn : 0 < n) (hd : 0 < d)
    (hge : (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).1 * d ≤
      n * (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).2) :
    roundRatioTiesToEven f sign n d ≠ zeroBits f zsign := by
  intro heq
  have hcr := roundRatioTiesToEven_correctly_rounded f sign n d hn hd
  dsimp only at hcr
  have hdec0 : decodeBits f (roundRatioTiesToEven f sign n d) = .zero zsign := by
    rw [heq, decodeBits_zeroBits]
  have hneInf : decodeBits f (roundRatioTiesToEven f sign n d) ≠ .inf sign := by
    rw [hdec0]; intro h; cases h
  let e := ratioExponent n d
  let exponent := max e f.minExponent
  let scaled := powScale n d ((f.fractionBits : Int) - exponent)
  let sig := roundQuotientTiesToEven scaled.1 scaled.2
  have hsame : floatKindSameValue (.zero zsign)
      (if sig = 0 then .zero sign
       else .finite sign (powScale sig 1 (exponent - f.fractionBits)).1
         (powScale sig 1 (exponent - f.fractionBits)).2) := by
    have htmp := hcr.2.2.2.2.2 hneInf
    rw [hdec0] at htmp
    exact htmp
  have hsig0 : sig = 0 := by
    by_cases h0 : sig = 0
    · exact h0
    · rw [if_neg' h0] at hsame
      exact False.elim hsame
  have hhalf : 2 * scaled.1 ≤ scaled.2 := by
    have hh : 2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs ≤ scaled.2 :=
      hcr.2.2.2.1
    rw [hsig0, Nat.zero_mul] at hh
    have hzero : (((0 : Nat) : Int) - (scaled.1 : Int)).natAbs = scaled.1 := by omega
    rw [hzero] at hh
    exact hh
  have hds : 0 < scaled.2 := powScale_snd_pos_gen n d hd _
  by_cases hnorm : f.minExponent ≤ e
  · have hge_sig : 2 ^ f.fractionBits * scaled.2 ≤ scaled.1 := hcr.2.2.1 hnorm
    have h1 : 1 ≤ 2 ^ f.fractionBits := Nat.one_le_two_pow
    have h2 : scaled.2 ≤ scaled.1 := by
      have hm := Nat.mul_le_mul_right scaled.2 h1
      rw [Nat.one_mul] at hm
      exact Nat.le_trans hm hge_sig
    omega
  · have hexp_eq : exponent = f.minExponent := by
      show max e f.minExponent = f.minExponent
      exact int_max_eq_right hnorm
    have hshift_ge : scaled.2 ≤ scaled.1 := by
      let shift : Nat := ((f.fractionBits : Int) - f.minExponent).toNat
      have hfb_pos : (f.fractionBits : Int) - exponent = Int.ofNat shift := by
        rw [hexp_eq]
        exact (show ∀ g : IeeeFormat, (g.fractionBits : Int) - g.minExponent =
            Int.ofNat ((g.fractionBits : Int) - g.minExponent).toNat from
          fun g => by cases g <;> rfl) f
      have hsub_neg : f.minExponent - (f.fractionBits : Int) = Int.negSucc (shift - 1) :=
        (show ∀ g : IeeeFormat, g.minExponent - (g.fractionBits : Int) =
            Int.negSucc (((g.fractionBits : Int) - g.minExponent).toNat - 1) from
          fun g => by cases g <;> rfl) f
      have hsc_eq : scaled = (n * 2 ^ shift, d) := by
        show powScale n d ((f.fractionBits : Int) - exponent) = _
        rw [hfb_pos]; rfl
      have hsub_eq : powScale 1 1 (f.minExponent - (f.fractionBits : Int)) = (1, 2 ^ shift) := by
        rw [hsub_neg]
        have hshift_eq : shift - 1 + 1 = shift :=
          (show ∀ g : IeeeFormat,
              ((g.fractionBits : Int) - g.minExponent).toNat - 1 + 1 =
                ((g.fractionBits : Int) - g.minExponent).toNat from
            fun g => by cases g <;> rfl) f
        simp only [powScale, Nat.one_mul, hshift_eq]
      rw [hsub_eq] at hge
      dsimp only at hge
      rw [Nat.one_mul] at hge
      rw [hsc_eq]
      dsimp only
      exact hge
    omega

/-- **Gradual underflow (`a - b = ±0 ↔ a == b`)**: for any two finite (including signed
zero) IEEE-754 bit patterns `a` and `b`, `evalFloatArithBase .sub f a b` returns a
signed zero IF AND ONLY IF `a == b` (`evalFloatCmp .eq f a b = .some true`). IEEE-754
subnormals guarantee that distinct finite floats never flush their difference to zero! -/
theorem gradual_underflow_sub_zero_iff (f : IeeeFormat) (a b : Nat)
    (haFin : isNaNBits f a = false ∧ ∀ s, decodeBits f a ≠ .inf s)
    (hbFin : isNaNBits f b = false ∧ ∀ s, decodeBits f b ≠ .inf s) :
    (∃ zsign, evalFloatArithBase .sub f a b = .some (zeroBits f zsign)) ↔
      evalFloatCmp .eq f a b = .some true := by
  have haM : decodeBits f (a % 2 ^ f.width) = decodeBits f a := decodeBits_mod f a
  have hbM : decodeBits f (b % 2 ^ f.width) = decodeBits f b := decodeBits_mod f b
  have hzero_ne_finite : ∀ z neg n d, decodeBits f (zeroBits f z) ≠ .finite neg n d := by
    intro z neg n d h; rw [decodeBits_zeroBits] at h; cases h
  unfold evalFloatArithBase evalFloatCmp evalFloatPartialCompare
  dsimp only
  rw [haM, hbM]
  cases ha : decodeBits f a with
  | nan _ _ _ =>
    have hnan := haFin.1; unfold isNaNBits at hnan; rw [ha] at hnan; cases hnan
  | inf s => exact absurd ha (haFin.2 s)
  | zero ln =>
    cases hb : decodeBits f b with
    | nan _ _ _ =>
      have hnan := hbFin.1; unfold isNaNBits at hnan; rw [hb] at hnan; cases hnan
    | inf s => exact absurd hb (hbFin.2 s)
    | zero rn =>
      dsimp only
      refine ⟨fun _ => rfl, fun _ => ⟨Bool.and ln (Bool.not rn), rfl⟩⟩
    | finite rn rnum rden =>
      dsimp only
      have hrn := decodeBits_finite_num_pos f b rn rnum rden hb
      have hrd := decodeBits_finite_den_pos f b rn rnum rden hb
      have hrne : ¬ (rnum = 0) := by omega
      simp only [negateFloatKind, exactSumFloat, if_neg' hrne]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases h with ⟨zsign, hz⟩
        injection hz with hz
        obtain ⟨S2, t2, hn2, hd2, hS20, _, ht2Lo, _⟩ := decodeBits_finite_grid f b rn rnum rden hb
        have hge : (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).1 * rden ≤
            rnum * (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).2 := by
          let j := (t2 - (f.minExponent - (f.fractionBits : Int))).toNat
          have hj : t2 - (j : Int) = f.minExponent - (f.fractionBits : Int) := by
            have hnn : ((t2 - (f.minExponent - (f.fractionBits : Int))).toNat : Int) =
                t2 - (f.minExponent - (f.fractionBits : Int)) := Int.toNat_of_nonneg (by omega)
            omega
          have hcross := powScale_shift_cross S2 j t2
          rw [hj, ← hn2, ← hd2, powScale_one_eq] at hcross
          dsimp only at hcross
          rw [powScale_one_eq]
          dsimp only
          rw [Nat.one_mul]
          have h1le : 1 ≤ S2 * 2 ^ j := Nat.mul_le_mul hS20 (Nat.one_le_two_pow)
          have hmul := Nat.mul_le_mul_right (powScaleMul (f.minExponent - (f.fractionBits : Int)) * rden) h1le
          rw [Nat.one_mul, ← Nat.mul_assoc, hcross] at hmul
          exact hmul
        exact absurd hz (roundRatioTiesToEven_ne_zeroBits_of_ge_minSubnormal f (Bool.not rn) zsign rnum rden hrn hrd hge)
      · cases rn <;> simp at h
  | finite ln lnum lden =>
    have hln := decodeBits_finite_num_pos f a ln lnum lden ha
    have hld := decodeBits_finite_den_pos f a ln lnum lden ha
    have hlne : ¬ (lnum = 0) := by omega
    cases hb : decodeBits f b with
    | nan _ _ _ =>
      have hnan := hbFin.1; unfold isNaNBits at hnan; rw [hb] at hnan; cases hnan
    | inf s => exact absurd hb (hbFin.2 s)
    | zero rn =>
      dsimp only
      simp only [negateFloatKind, exactSumFloat, if_neg' hlne]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases h with ⟨zsign, hz⟩
        injection hz with hz
        obtain ⟨S1, t1, hn1, hd1, hS10, _, ht1Lo, _⟩ := decodeBits_finite_grid f a ln lnum lden ha
        have hge : (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).1 * lden ≤
            lnum * (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).2 := by
          let j := (t1 - (f.minExponent - (f.fractionBits : Int))).toNat
          have hj : t1 - (j : Int) = f.minExponent - (f.fractionBits : Int) := by
            have hnn : ((t1 - (f.minExponent - (f.fractionBits : Int))).toNat : Int) =
                t1 - (f.minExponent - (f.fractionBits : Int)) := Int.toNat_of_nonneg (by omega)
            omega
          have hcross := powScale_shift_cross S1 j t1
          rw [hj, ← hn1, ← hd1, powScale_one_eq] at hcross
          dsimp only at hcross
          rw [powScale_one_eq]
          dsimp only
          rw [Nat.one_mul]
          have h1le : 1 ≤ S1 * 2 ^ j := Nat.mul_le_mul hS10 (Nat.one_le_two_pow)
          have hmul := Nat.mul_le_mul_right (powScaleMul (f.minExponent - (f.fractionBits : Int)) * lden) h1le
          rw [Nat.one_mul, ← Nat.mul_assoc, hcross] at hmul
          exact hmul
        exact absurd hz (roundRatioTiesToEven_ne_zeroBits_of_ge_minSubnormal f ln zsign lnum lden hln hld hge)
      · cases ln <;> simp at h
    | finite rn rnum rden =>
      dsimp only
      have hrn := decodeBits_finite_num_pos f b rn rnum rden hb
      have hrd := decodeBits_finite_den_pos f b rn rnum rden hb
      have hlbeq : Nat.beq lnum 0 = false := by
        rw [nat_beq_eq_decide]; exact decide_eq_false hlne
      simp only [negateFloatKind, exactSumFloat, hlbeq, Bool.false_and]
      let lv : Int := signedNum ln lnum * (rden : Int)
      let rv : Int := signedNum rn rnum * (lden : Int)
      have hdiff_eq : signedNum ln lnum * (rden : Int) + signedNum (Bool.not rn) rnum * (lden : Int) =
          lv - rv := by
        rw [signedNum_not, Int.neg_mul]; simp only [lv, rv]; omega
      rw [hdiff_eq]
      change (∃ zsign, some (roundRatioTiesToEven f (if lv - rv = 0 then false else decide (lv - rv < 0))
            (lv - rv).natAbs (lden * rden)) = some (zeroBits f zsign)) ↔
        some (match some (if lv < rv then Ordering.lt else if lv = rv then Ordering.eq else Ordering.gt) with
          | some Ordering.eq => true | _ => false) = some true
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases h with ⟨zsign, hz⟩
        injection hz with hz
        by_cases heqv : lv = rv
        · rw [if_neg' (by omega), if_pos' heqv]
        · have hnz : (lv - rv).natAbs > 0 := by omega
          obtain ⟨S1, t1, hn1, hd1, _, _, ht1Lo, _⟩ := decodeBits_finite_grid f a ln lnum lden ha
          obtain ⟨S2, t2, hn2, hd2, _, _, ht2Lo, _⟩ := decodeBits_finite_grid f b rn rnum rden hb
          let tmin : Int := f.minExponent - (f.fractionBits : Int)
          let j1 := (t1 - tmin).toNat
          let j2 := (t2 - tmin).toNat
          let A1 : Nat := S1 * 2 ^ j1
          let A2 : Nat := S2 * 2 ^ j2
          have hj1 : t1 - (j1 : Int) = tmin := by
            have hnn : ((t1 - tmin).toNat : Int) = t1 - tmin := Int.toNat_of_nonneg (by omega)
            omega
          have hj2 : t2 - (j2 : Int) = tmin := by
            have hnn : ((t2 - tmin).toNat : Int) = t2 - tmin := Int.toNat_of_nonneg (by omega)
            omega
          have hc1 : A1 * powScaleMul tmin * lden = lnum * powScaleDen tmin := by
            have h := powScale_shift_cross S1 j1 t1
            rw [hj1, ← hn1, ← hd1, powScale_one_eq] at h
            exact h
          have hc2 : A2 * powScaleMul tmin * rden = rnum * powScaleDen tmin := by
            have h := powScale_shift_cross S2 j2 t2
            rw [hj2, ← hn2, ← hd2, powScale_one_eq] at h
            exact h
          let M : Int := signedNum ln A1 - signedNum rn A2
          have hscaleInt : (lv - rv) * (powScaleDen tmin : Int) =
              M * ((powScaleMul tmin * (lden * rden) : Nat) : Int) := by
            have h1I : (A1 : Int) * (powScaleMul tmin : Int) * (lden : Int) =
                (lnum : Int) * (powScaleDen tmin : Int) := by
              have h := congrArg (fun x : Nat => (x : Int)) hc1
              rw [Int.natCast_mul, Int.natCast_mul, Int.natCast_mul] at h
              exact h
            have h2I : (A2 : Int) * (powScaleMul tmin : Int) * (rden : Int) =
                (rnum : Int) * (powScaleDen tmin : Int) := by
              have h := congrArg (fun x : Nat => (x : Int)) hc2
              rw [Int.natCast_mul, Int.natCast_mul, Int.natCast_mul] at h
              exact h
            have hlvI : lv * (powScaleDen tmin : Int) =
                signedNum ln A1 * ((powScaleMul tmin : Int) * (lden : Int) * (rden : Int)) := by
              cases ln with
              | true =>
                simp only [lv, signedNum, ↓reduceIte, Int.neg_mul]
                congr 1
                calc (lnum : Int) * (rden : Int) * (powScaleDen tmin : Int)
                  _ = (lnum : Int) * (powScaleDen tmin : Int) * (rden : Int) := Int.mul_right_comm _ _ _
                  _ = (A1 : Int) * (powScaleMul tmin : Int) * (lden : Int) * (rden : Int) := by rw [← h1I]
                  _ = (A1 : Int) * ((powScaleMul tmin : Int) * (lden : Int) * (rden : Int)) := by
                    simp only [Int.mul_assoc]
              | false =>
                simp only [lv, signedNum, Bool.false_eq_true, ↓reduceIte]
                calc (lnum : Int) * (rden : Int) * (powScaleDen tmin : Int)
                  _ = (lnum : Int) * (powScaleDen tmin : Int) * (rden : Int) := Int.mul_right_comm _ _ _
                  _ = (A1 : Int) * (powScaleMul tmin : Int) * (lden : Int) * (rden : Int) := by rw [← h1I]
                  _ = (A1 : Int) * ((powScaleMul tmin : Int) * (lden : Int) * (rden : Int)) := by
                    simp only [Int.mul_assoc]
            have hrvI : rv * (powScaleDen tmin : Int) =
                signedNum rn A2 * ((powScaleMul tmin : Int) * (lden : Int) * (rden : Int)) := by
              cases rn with
              | true =>
                simp only [rv, signedNum, ↓reduceIte, Int.neg_mul]
                congr 1
                calc (rnum : Int) * (lden : Int) * (powScaleDen tmin : Int)
                  _ = (rnum : Int) * (powScaleDen tmin : Int) * (lden : Int) := Int.mul_right_comm _ _ _
                  _ = (A2 : Int) * (powScaleMul tmin : Int) * (rden : Int) * (lden : Int) := by rw [← h2I]
                  _ = (A2 : Int) * ((powScaleMul tmin : Int) * (rden : Int) * (lden : Int)) := by
                    simp only [Int.mul_assoc]
                  _ = (A2 : Int) * ((powScaleMul tmin : Int) * (lden : Int) * (rden : Int)) := by
                    rw [Int.mul_right_comm (powScaleMul tmin : Int)]
              | false =>
                simp only [rv, signedNum, Bool.false_eq_true, ↓reduceIte]
                calc (rnum : Int) * (lden : Int) * (powScaleDen tmin : Int)
                  _ = (rnum : Int) * (powScaleDen tmin : Int) * (lden : Int) := Int.mul_right_comm _ _ _
                  _ = (A2 : Int) * (powScaleMul tmin : Int) * (rden : Int) * (lden : Int) := by rw [← h2I]
                  _ = (A2 : Int) * ((powScaleMul tmin : Int) * (rden : Int) * (lden : Int)) := by
                    simp only [Int.mul_assoc]
                  _ = (A2 : Int) * ((powScaleMul tmin : Int) * (lden : Int) * (rden : Int)) := by
                    rw [Int.mul_right_comm (powScaleMul tmin : Int)]
            rw [Int.sub_mul, hlvI, hrvI]
            simp only [M, Int.sub_mul, Int.natCast_mul, Int.mul_assoc]
          have hscaleNat : (lv - rv).natAbs * powScaleDen tmin =
              M.natAbs * (powScaleMul tmin * (lden * rden)) := by
            have habs := congrArg Int.natAbs hscaleInt
            simp only [Int.natAbs_mul, Int.natAbs_natCast] at habs
            exact habs
          have hMpos : 1 ≤ M.natAbs := by
            have hdp : 0 < powScaleDen tmin := powScaleDen_pos tmin
            have hprod_pos : 0 < (lv - rv).natAbs * powScaleDen tmin := Nat.mul_pos hnz hdp
            rw [hscaleNat] at hprod_pos
            have hMne : M.natAbs ≠ 0 := fun h0 => by
              rw [h0, Nat.zero_mul] at hprod_pos
              exact Nat.lt_irrefl 0 hprod_pos
            omega
          have hge : (powScale 1 1 tmin).1 * (lden * rden) ≤
              (lv - rv).natAbs * (powScale 1 1 tmin).2 := by
            rw [powScale_one_eq]
            dsimp only
            rw [Nat.one_mul, hscaleNat]
            have := Nat.mul_le_mul_right (powScaleMul tmin * (lden * rden)) hMpos
            rw [Nat.one_mul] at this
            exact this
          exact absurd hz
            (roundRatioTiesToEven_ne_zeroBits_of_ge_minSubnormal f _ zsign (lv - rv).natAbs
              (lden * rden) hnz (Nat.mul_pos hld hrd) hge)
      · by_cases hlt : lv < rv
        · rw [if_pos' hlt] at h; cases h
        · rw [if_neg' hlt] at h
          by_cases heqv : lv = rv
          · refine ⟨false, ?_⟩
            have h0 : lv - rv = 0 := by omega
            rw [h0, if_pos' rfl]
            exact congrArg Option.some (roundRatioTiesToEven_zero f false (lden * rden) (Nat.mul_pos hld hrd))
          · rw [if_neg' heqv] at h; cases h

/-- Canonical `1.0` bit pattern in format `f` (`encodeBits f false f.bias 0`). -/
def oneBits (f : IeeeFormat) : Nat := encodeBits f false f.bias 0

theorem decodeBits_oneBits (f : IeeeFormat) :
    decodeBits f (oneBits f) =
      .finite false (powScale (2 ^ f.fractionBits) 1 (-(f.fractionBits : Int))).1
        (powScale (2 ^ f.fractionBits) 1 (-(f.fractionBits : Int))).2 := by
  unfold oneBits
  have hE : f.bias < 2 ^ f.exponentBits := by cases f <;> decide
  have hEne : ¬ (f.bias = 2 ^ f.exponentBits - 1) := by cases f <;> decide
  have hE0 : ¬ (f.bias = 0) := by cases f <;> decide
  rw [decodeBits_encodeBits f false f.bias 0 hE (Nat.two_pow_pos _),
    if_neg' hEne, if_neg' hE0, Nat.add_zero]
  have hs : (f.bias : Int) - (f.bias : Int) - (f.fractionBits : Int) = -(f.fractionBits : Int) := by
    omega
  rw [hs]

/-- **`1.0` multiplicative identity**: for every non-NaN bit pattern `a`,
`a * 1.0 = a % 2^f.width` (preserving signed zeros, infinities, subnormals, and normals). -/
theorem evalFloatArithBase_mul_oneBits (f : IeeeFormat) (a : Nat)
    (ha : isNaNBits f a = false) :
    evalFloatArithBase .mul f a (oneBits f) = .some (a % 2 ^ f.width) := by
  have honeLt : oneBits f < 2 ^ f.width := by cases f <;> decide
  have honeDec : decodeBits f (oneBits f % 2 ^ f.width) =
      .finite false (2 ^ f.fractionBits) (2 ^ f.fractionBits) := by
    rw [Nat.mod_eq_of_lt honeLt, decodeBits_oneBits]
    cases f <;> rfl
  have hself := evalFloatToFloatRoundTiesToEven_self_eq f (a % 2 ^ f.width)
    (Nat.mod_lt a (Nat.two_pow_pos f.width))
  unfold evalFloatArithBase
  dsimp only
  rw [honeDec]
  have h2pos : 0 < 2 ^ f.fractionBits := Nat.two_pow_pos f.fractionBits
  have h2ne : ¬ (2 ^ f.fractionBits = 0) := by omega
  cases hdec : decodeBits f (a % 2 ^ f.width) with
  | nan _ _ _ =>
    rw [decodeBits_mod] at hdec
    unfold isNaNBits at ha; rw [hdec] at ha; cases ha
  | inf ln =>
    dsimp only
    rw [if_neg' h2ne]
    simp only [Bool.xor_false]
    have hself' : infBits f ln = a % 2 ^ f.width := by
      unfold evalFloatToFloatRoundTiesToEven at hself
      rw [hdec] at hself
      exact hself
    rw [hself']
  | zero ln =>
    dsimp only
    simp only [Bool.xor_false]
    have hself' : zeroBits f ln = a % 2 ^ f.width := by
      unfold evalFloatToFloatRoundTiesToEven at hself
      rw [hdec] at hself
      exact hself
    rw [hself']
  | finite ln lnum lden =>
    dsimp only
    simp only [Bool.xor_false]
    rw [← roundRatioBits_tiesToEven,
      roundRatioBits_mul .tiesToEven f ln lnum lden (2 ^ f.fractionBits) h2pos,
      roundRatioBits_tiesToEven]
    have hself' : roundRatioTiesToEven f ln lnum lden = a % 2 ^ f.width := by
      unfold evalFloatToFloatRoundTiesToEven at hself
      rw [hdec] at hself
      exact hself
    rw [hself']

/-- **Exact Euclidean `rem` on finite floats**: for any two finite IEEE-754 floats
`a` and `b` with `decodeBits f (a % 2^w) = .finite ln lnum lden` and
`decodeBits f (b % 2^w) = .finite rn rnum rden`, `evalFloatArithBase .rem f a b`
computes the **exact** remainder `rem = (lnum * rden) % (lden * rnum)` divided by
`lden * rden` with **zero rounding error** and strict bound `|a % b| < |b|`. -/
theorem evalFloatArithBase_rem_finite_exact (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (ha : decodeBits f (a % 2 ^ f.width) = .finite ln lnum lden)
    (hb : decodeBits f (b % 2 ^ f.width) = .finite rn rnum rden) :
    let q := (lnum * rden) / (lden * rnum)
    let rem := lnum * rden - q * (lden * rnum)
    ∃ outBits,
      evalFloatArithBase .rem f a b = .some outBits ∧
      rem = (lnum * rden) % (lden * rnum) ∧
      rem < lden * rnum ∧
      (if rem = 0 then
        outBits = zeroBits f ln
      else
        ∃ n' d',
          decodeBits f outBits = .finite ln n' d' ∧
          n' * (lden * rden) = rem * d' ∧
          n' * rden < rnum * d') := by
  have hln := decodeBits_finite_num_pos f _ ln lnum lden ha
  have hld := decodeBits_finite_den_pos f _ ln lnum lden ha
  have hrn := decodeBits_finite_num_pos f _ rn rnum rden hb
  have hrd := decodeBits_finite_den_pos f _ rn rnum rden hb
  have hdenomPos : 0 < lden * rnum := Nat.mul_pos hld hrn
  let q := (lnum * rden) / (lden * rnum)
  let rem := lnum * rden - q * (lden * rnum)
  have hrem_eq : rem = (lnum * rden) % (lden * rnum) := by
    have hdm := Nat.div_add_mod (lnum * rden) (lden * rnum)
    have hcomm : (lden * rnum) * ((lnum * rden) / (lden * rnum)) = q * (lden * rnum) := Nat.mul_comm _ _
    rw [hcomm] at hdm
    dsimp only [rem]
    omega
  have hrem_lt : rem < lden * rnum := by
    rw [hrem_eq]
    exact Nat.mod_lt _ hdenomPos
  have hrem_eval : evalFloatArithBase .rem f a b =
      .some (roundRatioTiesToEven f ln rem (lden * rden)) := by
    unfold evalFloatArithBase
    dsimp only
    rw [ha, hb]
    dsimp only
    rw [if_neg' (by omega)]
  refine ⟨roundRatioTiesToEven f ln rem (lden * rden), hrem_eval, hrem_eq, hrem_lt, ?_⟩
  by_cases hrem0 : rem = 0
  · rw [if_pos' hrem0, hrem0]
    exact roundRatioTiesToEven_zero f ln (lden * rden) (Nat.mul_pos hld hrd)
  · rw [if_neg' hrem0]
    obtain ⟨S1, t1, hn1, hd1, _, hS1lt, ht1Lo, ht1Hi⟩ := decodeBits_finite_grid f _ ln lnum lden ha
    obtain ⟨S2, t2, hn2, hd2, hS20, hS2lt, ht2Lo, ht2Hi⟩ := decodeBits_finite_grid f _ rn rnum rden hb
    let t : Int := min t1 t2
    let A : Nat := S1 * 2 ^ (t1 - t).toNat
    let B : Nat := S2 * 2 ^ (t2 - t).toNat
    have hgrid := powScale_common_grid S1 S2 t1 t2
    have hAeq : A * powScaleMul t * lden = lnum * powScaleDen t := by
      have hc := hgrid.1; rw [← hn1, ← hd1, powScale_one_eq] at hc; exact hc
    have hBeq : B * powScaleMul t * rden = rnum * powScaleDen t := by
      have hc := hgrid.2; rw [← hn2, ← hd2, powScale_one_eq] at hc; exact hc
    have hDenPos : 0 < powScaleDen t := powScaleDen_pos t
    have hMulPos : 0 < powScaleMul t := powScaleMul_pos t
    have hCpos : 0 < powScaleMul t * (lden * rden) := Nat.mul_pos hMulPos (Nat.mul_pos hld hrd)
    have hBpos : 0 < B := Nat.mul_pos hS20 (Nat.two_pow_pos _)
    have hAC : lnum * rden * powScaleDen t = A * (powScaleMul t * (lden * rden)) := by
      calc lnum * rden * powScaleDen t
        _ = (lnum * powScaleDen t) * rden := by rw [Nat.mul_right_comm]
        _ = (A * powScaleMul t * lden) * rden := by rw [← hAeq]
        _ = A * (powScaleMul t * (lden * rden)) := by rw [Nat.mul_assoc, Nat.mul_assoc]
    have hBC : lden * rnum * powScaleDen t = B * (powScaleMul t * (lden * rden)) := by
      calc lden * rnum * powScaleDen t
        _ = (rnum * powScaleDen t) * lden := by rw [Nat.mul_comm lden rnum, Nat.mul_right_comm]
        _ = (B * powScaleMul t * rden) * lden := by rw [← hBeq]
        _ = B * (powScaleMul t * (lden * rden)) := by
          rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm rden lden]
    have hq_eq : q = A / B := by
      show (lnum * rden) / (lden * rnum) = A / B
      rw [← Nat.mul_div_mul_right (lnum * rden) (lden * rnum) hDenPos, hAC, hBC,
        Nat.mul_div_mul_right A B hCpos]
    let R : Nat := A % B
    have hRC : rem * powScaleDen t = R * (powScaleMul t * (lden * rden)) := by
      have hdmA := Nat.div_add_mod A B
      have hR_sub : R = A - (A / B) * B := by
        have hcomm : B * (A / B) = (A / B) * B := Nat.mul_comm _ _
        rw [hcomm] at hdmA
        dsimp only [R]
        omega
      calc rem * powScaleDen t
        _ = (lnum * rden - q * (lden * rnum)) * powScaleDen t := rfl
        _ = lnum * rden * powScaleDen t - q * (lden * rnum * powScaleDen t) := by
          rw [Nat.sub_mul, Nat.mul_assoc q (lden * rnum) (powScaleDen t)]
        _ = A * (powScaleMul t * (lden * rden)) - (A / B) * (B * (powScaleMul t * (lden * rden))) := by
          rw [hAC, hBC, hq_eq]
        _ = (A - (A / B) * B) * (powScaleMul t * (lden * rden)) := by
          rw [← Nat.mul_assoc (A / B) B (powScaleMul t * (lden * rden)), ← Nat.sub_mul]
        _ = R * (powScaleMul t * (lden * rden)) := by rw [← hR_sub]
    have hR0 : 0 < R := by
      have hprod : 0 < rem * powScaleDen t := Nat.mul_pos (Nat.pos_of_ne_zero hrem0) hDenPos
      rw [hRC] at hprod
      have hRne : R ≠ 0 := fun h0 => by
        rw [h0, Nat.zero_mul] at hprod
        exact Nat.lt_irrefl 0 hprod
      exact Nat.pos_of_ne_zero hRne
    have hRlt : R < 2 ^ (f.fractionBits + 1) := by
      by_cases h : t1 ≤ t2
      · have h0 : (t1 - t).toNat = 0 := by
          show (t1 - min t1 t2).toNat = 0; omega
        have hAeqS1 : A = S1 := by
          show S1 * 2 ^ (t1 - t).toNat = S1
          rw [h0, Nat.pow_zero, Nat.mul_one]
        have hRleA : R ≤ A := Nat.mod_le A B
        omega
      · have h0 : (t2 - t).toNat = 0 := by
          show (t2 - min t1 t2).toNat = 0; omega
        have hBeqS2 : B = S2 := by
          show S2 * 2 ^ (t2 - t).toNat = S2
          rw [h0, Nat.pow_zero, Nat.mul_one]
        have hRltB : R < B := Nat.mod_lt A hBpos
        omega
    have htLo : f.minExponent - (f.fractionBits : Int) ≤ t := by
      show f.minExponent - (f.fractionBits : Int) ≤ min t1 t2
      omega
    have htHi : t ≤ f.maxExponent - (f.fractionBits : Int) := by
      show min t1 t2 ≤ f.maxExponent - (f.fractionBits : Int)
      omega
    have hcross : rem * (powScale R 1 t).2 = (powScale R 1 t).1 * (lden * rden) := by
      rw [powScale_one_eq]; dsimp only; rw [hRC, Nat.mul_assoc]
    have hcongr :
        roundRatioTiesToEven f ln rem (lden * rden) =
          roundRatioTiesToEven f ln (powScale R 1 t).1 (powScale R 1 t).2 := by
      rw [← roundRatioBits_tiesToEven, ← roundRatioBits_tiesToEven]
      exact roundRatioBits_congr .tiesToEven f ln _ _ _ _
        (Nat.mul_pos hld hrd) (powScale_snd_pos R t) hcross
    obtain ⟨n', d', hdec, hrat, hd'pos⟩ :=
      roundRatioTiesToEven_exact_grid f ln R t hR0 hRlt htLo htHi
    rw [hcongr]
    have hrat_rem : n' * (lden * rden) = rem * d' := by
      apply (nat_mul_eq_mul_right_iff hDenPos).mp
      have hden_eq : (powScale R 1 t).2 = powScaleDen t := by rw [powScale_one_eq]
      calc n' * (lden * rden) * powScaleDen t
        _ = n' * (powScale R 1 t).2 * (lden * rden) := by rw [hden_eq, Nat.mul_right_comm]
        _ = (powScale R 1 t).1 * d' * (lden * rden) := by rw [hrat]
        _ = (powScale R 1 t).1 * (lden * rden) * d' := by rw [Nat.mul_right_comm]
        _ = rem * (powScale R 1 t).2 * d' := by rw [← hcross]
        _ = rem * d' * powScaleDen t := by rw [hden_eq, Nat.mul_right_comm]
    have hlt_b : n' * rden < rnum * d' := by
      apply (nat_mul_lt_mul_right_iff hld).mp
      calc n' * rden * lden
        _ = n' * (lden * rden) := by rw [Nat.mul_assoc, Nat.mul_comm rden lden]
        _ = rem * d' := hrat_rem
        _ < (lden * rnum) * d' := Nat.mul_lt_mul_of_pos_right hrem_lt hd'pos
        _ = rnum * d' * lden := by rw [Nat.mul_comm lden rnum, Nat.mul_right_comm]
    exact ⟨n', d', hdec, hrat_rem, hlt_b⟩

/-- Exact divisibility biconditional for finite IEEE-754 `rem`: `a % b` equals `±0.0`
(specifically `zeroBits f ln`) IF AND ONLY IF `b` divides `a` as exact rationals
(`(lden * rnum) ∣ (lnum * rden)`). -/
theorem evalFloatArithBase_rem_finite_eq_zero_iff (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (ha : decodeBits f (a % 2 ^ f.width) = .finite ln lnum lden)
    (hb : decodeBits f (b % 2 ^ f.width) = .finite rn rnum rden) :
    evalFloatArithBase .rem f a b = .some (zeroBits f ln) ↔
      (lden * rnum) ∣ (lnum * rden) := by
  obtain ⟨outBits, heval, hrem_eq, _, hexact⟩ :=
    evalFloatArithBase_rem_finite_exact f a b ln rn lnum lden rnum rden ha hb
  rw [heval]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · injection h with hout
    by_cases hrem0 : lnum * rden - (lnum * rden) / (lden * rnum) * (lden * rnum) = 0
    · rw [hrem0] at hrem_eq
      exact Nat.dvd_of_mod_eq_zero hrem_eq.symm
    · rw [if_neg' hrem0] at hexact
      rcases hexact with ⟨n', d', hdec, _, _⟩
      rw [hout, decodeBits_zeroBits] at hdec
      cases hdec
  · have hmod0 : (lnum * rden) % (lden * rnum) = 0 := Nat.mod_eq_zero_of_dvd h
    have hrem0 : lnum * rden - (lnum * rden) / (lden * rnum) * (lden * rnum) = 0 := by
      rw [hrem_eq, hmod0]
    rw [if_pos' hrem0] at hexact
    rw [hexact]

/-! ### Closed-form finite rational overflow threshold (`roundTiesToEven`) -/

/-- Bit pattern of the largest finite magnitude in format `f` (`f32::MAX` / `f64::MAX`
for `neg = false`, `f32::MIN` / `f64::MIN` for `neg = true`): exponent `2^eb - 2`,
all-ones fraction `2^fb - 1`. -/
def maxFiniteBits (f : IeeeFormat) (neg : Bool) : Nat :=
  encodeBits f neg (2 ^ f.exponentBits - 2) (2 ^ f.fractionBits - 1)

/-- Exact natural-number magnitude of `maxFiniteBits f neg`:
`(2^(fb + 1) - 1) * 2^(bias - fb)` (`(2 - 2^-fb) * 2^bias`). -/
def maxFiniteVal (f : IeeeFormat) : Nat :=
  (2 ^ (f.fractionBits + 1) - 1) * 2 ^ (f.bias - f.fractionBits)

/-- Exact `roundTiesToEven` overflow threshold in `Nat`:
`MAX + (1/2) ulp(MAX) = (2^(fb + 2) - 1) * 2^(bias - fb - 1) = 2^(bias + 1) - 2^(bias - fb - 1)`,
matching `core`'s documented `f32::MAX + 2^(f32::MAX_EXP - f32::MANTISSA_DIGITS - 1)`
(and identically for `f64`). Because `f.fractionBits + 1 ≤ f.bias` for both
`binary32` (`24 ≤ 127`) and `binary64` (`53 ≤ 1023`), the threshold is an exact `Nat`. -/
def overflowThreshold (f : IeeeFormat) : Nat :=
  (2 ^ (f.fractionBits + 2) - 1) * 2 ^ (f.bias - f.fractionBits - 1)

private theorem format_overflow_params (f : IeeeFormat) :
    f.minExponent < f.maxExponent ∧
    f.fractionBits + 1 ≤ f.bias ∧
    2 ^ f.exponentBits - 2 = 2 * f.bias ∧
    (f.fractionBits : Int) - f.maxExponent = Int.negSucc (f.bias - f.fractionBits - 1) ∧
    f.bias - f.fractionBits = (f.bias - f.fractionBits - 1) + 1 := by
  cases f <;> refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- Equivalent closed forms and binade bounds for `overflowThreshold f`:
`MAX + 2^(bias - fb - 1) = 2^(bias + 1) - 2^(bias - fb - 1) ∈ (2^bias, 2^(bias + 1))`. -/
theorem overflowThreshold_eq (f : IeeeFormat) :
    overflowThreshold f = maxFiniteVal f + 2 ^ (f.bias - f.fractionBits - 1) ∧
    overflowThreshold f = 2 ^ (f.bias + 1) - 2 ^ (f.bias - f.fractionBits - 1) ∧
    2 ^ f.bias < overflowThreshold f ∧
    overflowThreshold f < 2 ^ (f.bias + 1) := by
  have hp := format_overflow_params f
  have hsh : f.bias - f.fractionBits = (f.bias - f.fractionBits - 1) + 1 := hp.2.2.2.2
  have h1 : 1 ≤ 2 ^ (f.fractionBits + 1) := Nat.one_le_two_pow
  have h2 : 2 ^ (f.fractionBits + 2) = 2 * 2 ^ (f.fractionBits + 1) := by
    rw [show f.fractionBits + 2 = (f.fractionBits + 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  have h2s : 2 ^ (f.bias - f.fractionBits) = 2 * 2 ^ (f.bias - f.fractionBits - 1) := by
    calc 2 ^ (f.bias - f.fractionBits)
      _ = 2 ^ ((f.bias - f.fractionBits - 1) + 1) := congrArg (2 ^ ·) hsh
      _ = 2 ^ (f.bias - f.fractionBits - 1) * 2 := Nat.pow_succ _ _
      _ = 2 * 2 ^ (f.bias - f.fractionBits - 1) := Nat.mul_comm _ _
  have hsum_exp : (f.fractionBits + 2) + (f.bias - f.fractionBits - 1) = f.bias + 1 := by
    have := hp.2.1; omega
  have heq1 : overflowThreshold f = maxFiniteVal f + 2 ^ (f.bias - f.fractionBits - 1) := by
    unfold overflowThreshold maxFiniteVal
    rw [h2, h2s, ← Nat.mul_assoc,
      show (2 ^ (f.fractionBits + 1) - 1) * 2 = 2 * 2 ^ (f.fractionBits + 1) - 2 by omega]
    rw [show 2 * 2 ^ (f.fractionBits + 1) - 1 = (2 * 2 ^ (f.fractionBits + 1) - 2) + 1 by omega,
      Nat.add_mul, Nat.one_mul]
  have heq2 : overflowThreshold f = 2 ^ (f.bias + 1) - 2 ^ (f.bias - f.fractionBits - 1) := by
    unfold overflowThreshold
    rw [Nat.sub_mul, Nat.one_mul, pow_mul_pow, hsum_exp]
  have hlt1 : 2 ^ f.bias < overflowThreshold f := by
    have hlt_pow : 2 ^ (f.bias - f.fractionBits - 1) < 2 ^ f.bias := by
      have hsub_lt : f.bias - f.fractionBits - 1 < f.bias := by
        have := hp.2.1; omega
      have hle : 2 ^ ((f.bias - f.fractionBits - 1) + 1) ≤ 2 ^ f.bias := two_pow_le_two_pow hsub_lt
      rw [Nat.pow_succ] at hle
      have := Nat.two_pow_pos (f.bias - f.fractionBits - 1)
      omega
    have h2b : 2 ^ (f.bias + 1) = 2 * 2 ^ f.bias := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [heq2, h2b]
    omega
  have hlt2 : overflowThreshold f < 2 ^ (f.bias + 1) := by
    have hpos : 0 < 2 ^ (f.bias - f.fractionBits - 1) := Nat.two_pow_pos _
    have h2b : 2 ^ f.bias < 2 ^ (f.bias + 1) := by
      rw [Nat.pow_succ]; have := Nat.two_pow_pos f.bias; omega
    rw [heq2]
    omega
  exact ⟨heq1, heq2, hlt1, hlt2⟩

/-- `maxFiniteBits f neg` immediately precedes `infBits f neg`, lies within `2 ^ f.width`,
and decodes to `.finite neg (maxFiniteVal f) 1`. -/
theorem maxFiniteBits_props (f : IeeeFormat) (neg : Bool) :
    maxFiniteBits f neg + 1 = infBits f neg ∧
    maxFiniteBits f neg < 2 ^ f.width ∧
    decodeBits f (maxFiniteBits f neg) = .finite neg (maxFiniteVal f) 1 := by
  have hE : 2 ^ f.exponentBits - 2 < 2 ^ f.exponentBits := by cases f <;> decide
  have hF : 2 ^ f.fractionBits - 1 < 2 ^ f.fractionBits := by cases f <;> decide
  have hsucc : maxFiniteBits f neg + 1 = infBits f neg := by
    unfold maxFiniteBits infBits encodeBits
    have hEge : 2 ≤ 2 ^ f.exponentBits := by cases f <;> decide
    have hFpos : 1 ≤ 2 ^ f.fractionBits := Nat.one_le_two_pow
    have h1 : (2 ^ f.exponentBits - 1) * 2 ^ f.fractionBits =
        (2 ^ f.exponentBits - 2) * 2 ^ f.fractionBits + 2 ^ f.fractionBits := by
      rw [show 2 ^ f.exponentBits - 1 = (2 ^ f.exponentBits - 2) + 1 by omega,
        Nat.add_mul, Nat.one_mul]
    rw [h1]
    omega
  have hlt : maxFiniteBits f neg < 2 ^ f.width := encodeBits_lt f neg _ _ hE hF
  have hdec : decodeBits f (maxFiniteBits f neg) = .finite neg (maxFiniteVal f) 1 := by
    unfold maxFiniteBits
    rw [decodeBits_encodeBits f neg _ _ hE hF]
    have hne1 : ¬ (2 ^ f.exponentBits - 2 = 2 ^ f.exponentBits - 1) := by cases f <;> decide
    have hne0 : ¬ (2 ^ f.exponentBits - 2 = 0) := by cases f <;> decide
    rw [if_neg' hne1, if_neg' hne0]
    have hp := format_overflow_params f
    have hsig : 2 ^ f.fractionBits + (2 ^ f.fractionBits - 1) = 2 ^ (f.fractionBits + 1) - 1 := by
      rw [Nat.pow_succ]; have := Nat.two_pow_pos f.fractionBits; omega
    have hexp : (((2 ^ f.exponentBits - 2 : Nat) : Int) - (f.bias : Int) - (f.fractionBits : Int)) =
        ((f.bias - f.fractionBits : Nat) : Int) := by
      have h2b := hp.2.2.1
      have hfb := hp.2.1
      omega
    rw [hsig, hexp]
    rfl
  exact ⟨hsucc, hlt, hdec⟩

/-- Every finite decoded value in format `f` has magnitude `≤ maxFiniteVal f`
(`n ≤ maxFiniteVal f * d`). -/
theorem decodeBits_finite_le_maxFiniteVal (f : IeeeFormat) (bits : Nat) (neg : Bool) (n d : Nat)
    (h : decodeBits f bits = .finite neg n d) :
    n ≤ maxFiniteVal f * d := by
  obtain ⟨S, t, hn, hd, _, hSlt, _, htHi⟩ := decodeBits_finite_grid f bits neg n d h
  have hSle : S ≤ 2 ^ (f.fractionBits + 1) - 1 := by omega
  have hfb := (format_overflow_params f).2.1
  rw [hn, hd]
  cases t with
  | ofNat k =>
    simp only [powScale, Nat.mul_one]
    have hkle : k ≤ f.bias - f.fractionBits := by
      have hk : (k : Int) ≤ (f.bias : Int) - (f.fractionBits : Int) := htHi
      omega
    exact Nat.mul_le_mul hSle (two_pow_le_two_pow hkle)
  | negSucc k =>
    simp only [powScale, Nat.one_mul]
    have h1 : 1 ≤ 2 ^ (f.bias - f.fractionBits) * 2 ^ (k + 1) :=
      Nat.mul_le_mul Nat.one_le_two_pow Nat.one_le_two_pow
    have hmul := Nat.mul_le_mul hSle h1
    rw [Nat.mul_one, ← Nat.mul_assoc] at hmul
    exact hmul

private theorem powScale_neg_ofNat (n d k : Nat) :
    powScale n d (-(k : Int)) = (n, d * 2 ^ k) := by
  cases k with
  | zero => simp [powScale]
  | succ m => rfl

private theorem roundQuotientTiesToEven_eq_even_top_iff (n D M : Nat)
    (hD : 0 < D) (hMpos : 2 ≤ M) (hMeven : M % 2 = 0) (hlt : n < M * D) :
    roundQuotientTiesToEven n D = M ↔ (2 * M - 1) * D ≤ 2 * n := by
  have hdm := Nat.div_add_mod n D
  have hrlt := Nat.mod_lt n hD
  have hqlt : n / D < M := (Nat.div_lt_iff_lt_mul hD).mpr hlt
  have hM1odd : (M - 1) % 2 = 1 := by omega
  have h2m : (2 * M - 1) * D = 2 * ((M - 1) * D) + D := by
    have h1 : 2 * M - 1 = 2 * (M - 1) + 1 := by omega
    rw [h1, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  unfold roundQuotientTiesToEven
  dsimp only
  constructor
  · intro heq
    by_cases hc : n % D * 2 > D ∨ (n % D * 2 = D ∧ (n / D) % 2 = 1)
    · rw [if_pos' hc] at heq
      have hq : n / D = M - 1 := by omega
      have hr : D ≤ n % D * 2 := by
        rcases hc with hgt | ⟨he, _⟩ <;> omega
      have hn_eq : n = (M - 1) * D + n % D := by
        have hdm' := hdm
        rw [hq, Nat.mul_comm] at hdm'
        exact hdm'.symm
      rw [hn_eq, h2m]
      omega
    · rw [if_neg' hc] at heq
      omega
  · intro hge
    have hq_ge : M - 1 ≤ n / D := by
      cases Nat.lt_or_ge (n / D) (M - 1) with
      | inr hle => exact hle
      | inl hltq =>
        have hle2 : n / D + 1 ≤ M - 1 := by omega
        have hstep : (n / D + 1) * D ≤ (M - 1) * D := Nat.mul_le_mul_right D hle2
        have hnlt : n < (n / D + 1) * D := by
          rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / D) D]; omega
        have hltm : 2 * n < 2 * ((M - 1) * D) := by omega
        omega
    have hq : n / D = M - 1 := by omega
    have hn_eq : n = (M - 1) * D + n % D := by
      have hdm' := hdm
      rw [hq, Nat.mul_comm] at hdm'
      exact hdm'.symm
    have hr : D ≤ n % D * 2 := by rw [hn_eq, h2m] at hge; omega
    have hc : n % D * 2 > D ∨ (n % D * 2 = D ∧ (n / D) % 2 = 1) := by
      by_cases hgt : n % D * 2 > D
      · exact Or.inl hgt
      · exact Or.inr ⟨by omega, by rw [hq]; exact hM1odd⟩
    rw [if_pos' hc, hq]
    omega

/-- **Exact closed-form rational overflow threshold (`roundTiesToEven`)**:
for every `f`, `neg`, and rational `n / d` (`0 < d`), `roundRatioTiesToEven f neg n d`
overflows to `infBits f neg` IF AND ONLY IF `n / d ≥ overflowThreshold f`
(`d * overflowThreshold f ≤ n`). -/
theorem roundRatioTiesToEven_eq_inf_iff (f : IeeeFormat) (neg : Bool) (n d : Nat) (hd : 0 < d) :
    roundRatioTiesToEven f neg n d = infBits f neg ↔ d * overflowThreshold f ≤ n := by
  have hT := overflowThreshold_eq f
  have hTpos : 0 < overflowThreshold f := by
    have := Nat.two_pow_pos f.bias; omega
  by_cases hn0 : n = 0
  · subst hn0
    rw [roundRatioTiesToEven_zero f neg d hd]
    have hne : zeroBits f neg ≠ infBits f neg := by cases f <;> cases neg <;> decide
    have hprod : 0 < d * overflowThreshold f := Nat.mul_pos hd hTpos
    exact ⟨fun h => absurd h hne, fun h => by omega⟩
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hov := (roundRatioTiesToEven_overflow_iff f neg n d hn hd).1
    rw [hov]
    have hp := format_overflow_params f
    have hmin_lt_max : f.minExponent < f.maxExponent := hp.1
    have hbd := powScale_neg_ratioExponent_bounds n d hn hd
    generalize he : ratioExponent n d = e at hbd ⊢
    by_cases hgt : f.maxExponent < e
    · have hmax_gt : f.maxExponent < max e f.minExponent := by omega
      have he_pos : 0 ≤ e := by simp only [IeeeFormat.maxExponent] at hgt; omega
      have hto : ((e.toNat : Nat) : Int) = e := Int.toNat_of_nonneg he_pos
      have hge_exp : f.bias + 1 ≤ e.toNat := by simp only [IeeeFormat.maxExponent] at hgt; omega
      have hlo : d * 2 ^ e.toNat ≤ n := by
        have h1 := hbd.1
        rw [← hto, powScale_neg_ofNat] at h1
        exact h1
      have hge_T : d * overflowThreshold f ≤ n := by
        have h1 : overflowThreshold f ≤ 2 ^ e.toNat :=
          Nat.le_trans (Nat.le_of_lt hT.2.2.2) (two_pow_le_two_pow hge_exp)
        exact Nat.le_trans (Nat.mul_le_mul_left d h1) hlo
      exact ⟨fun _ => hge_T, fun _ => Or.inl hmax_gt⟩
    · by_cases heq : e = f.maxExponent
      · have hmax_eq : max e f.minExponent = f.maxExponent := by omega
        rw [hmax_eq]
        have hlo_hi : d * 2 ^ f.bias ≤ n ∧ n < 2 * (d * 2 ^ f.bias) := by
          have h1 := hbd.1
          have h2 := hbd.2
          rw [heq] at h1 h2
          simp only [IeeeFormat.maxExponent] at h1 h2
          rw [powScale_neg_ofNat] at h1 h2
          exact ⟨h1, h2⟩
        have hsc_eq : powScale n d ((f.fractionBits : Int) - f.maxExponent) =
            (n, d * 2 ^ (f.bias - f.fractionBits)) := by
          rw [hp.2.2.2.1]
          simp only [powScale, ← hp.2.2.2.2]
        rw [hsc_eq]
        dsimp only
        let D : Nat := d * 2 ^ (f.bias - f.fractionBits)
        let M : Nat := 2 ^ (f.fractionBits + 1)
        have hDpos : 0 < D := Nat.mul_pos hd (Nat.two_pow_pos _)
        have hMpos : 2 ≤ M := by cases f <;> decide
        have hMeven : M % 2 = 0 := by cases f <;> decide
        have hMD : M * D = 2 * (d * 2 ^ f.bias) := by
          have hexp_sum : (f.fractionBits + 1) + (f.bias - f.fractionBits) = f.bias + 1 := by
            have := hp.2.1; omega
          calc M * D
            _ = d * (2 ^ (f.fractionBits + 1) * 2 ^ (f.bias - f.fractionBits)) := by
              simp only [M, D]; rw [Nat.mul_left_comm]
            _ = d * 2 ^ (f.bias + 1) := by rw [pow_mul_pow, hexp_sum]
            _ = 2 * (d * 2 ^ f.bias) := by
              rw [Nat.pow_succ, Nat.mul_comm (2 ^ f.bias) 2, Nat.mul_left_comm]
        have hnlt : n < M * D := by rw [hMD]; exact hlo_hi.2
        have hrq := roundQuotientTiesToEven_eq_even_top_iff n D M hDpos hMpos hMeven hnlt
        have h2M : 2 * M - 1 = 2 ^ (f.fractionBits + 2) - 1 := by
          have hpow2 : 2 * M = 2 ^ (f.fractionBits + 2) := by
            show 2 * 2 ^ (f.fractionBits + 1) = 2 ^ (f.fractionBits + 2)
            rw [show f.fractionBits + 2 = (f.fractionBits + 1) + 1 by omega,
              Nat.pow_succ 2 (f.fractionBits + 1), Nat.mul_comm]
          rw [hpow2]
        have hD2 : D = 2 * (d * 2 ^ (f.bias - f.fractionBits - 1)) := by
          calc D
            _ = d * 2 ^ ((f.bias - f.fractionBits - 1) + 1) := by
              simp only [D]; exact congrArg (fun k => d * 2 ^ k) hp.2.2.2.2
            _ = d * (2 ^ (f.bias - f.fractionBits - 1) * 2) := by rw [Nat.pow_succ]
            _ = 2 * (d * 2 ^ (f.bias - f.fractionBits - 1)) := by
              rw [Nat.mul_comm _ 2, Nat.mul_left_comm]
        have hrhs_eq : (2 * M - 1) * D = 2 * (d * overflowThreshold f) := by
          unfold overflowThreshold
          rw [h2M, hD2, Nat.mul_left_comm, Nat.mul_left_comm d]
        constructor
        · intro h
          rcases h with h1 | ⟨_, h2⟩
          · exact absurd h1 (Int.lt_irrefl _)
          · have h2n : 2 * (d * overflowThreshold f) ≤ 2 * n := by
              rw [← hrhs_eq]; exact hrq.mp h2
            omega
        · intro hle
          right
          refine ⟨rfl, hrq.mpr ?_⟩
          rw [hrhs_eq]
          omega
      · have hlt_e : e < f.maxExponent := by omega
        have hmax_lt : max e f.minExponent < f.maxExponent := by omega
        have hn_lt_2b : n < d * 2 ^ f.bias := by
          by_cases he0 : 0 ≤ e
          · have hto : ((e.toNat : Nat) : Int) = e := Int.toNat_of_nonneg he0
            have hhi := hbd.2
            rw [← hto, powScale_neg_ofNat] at hhi
            have hle_b : e.toNat + 1 ≤ f.bias := by simp only [IeeeFormat.maxExponent] at hlt_e; omega
            have hmul : 2 * (d * 2 ^ e.toNat) = d * 2 ^ (e.toNat + 1) := by
              rw [Nat.pow_succ, Nat.mul_comm (2 ^ e.toNat) 2, Nat.mul_left_comm]
            have hstep : d * 2 ^ (e.toNat + 1) ≤ d * 2 ^ f.bias :=
              Nat.mul_le_mul_left d (two_pow_le_two_pow hle_b)
            omega
          · have hneg : ∃ k : Nat, -e = Int.ofNat (k + 1) := by
              cases e with
              | ofNat m => exact absurd (Int.natCast_nonneg m) he0
              | negSucc m => exact ⟨m, rfl⟩
            rcases hneg with ⟨k, hk⟩
            have hhi := hbd.2
            rw [hk] at hhi
            simp only [powScale] at hhi
            have h2le : 2 ≤ 2 ^ (k + 1) := two_pow_le_two_pow (Nat.succ_le_succ (Nat.zero_le k))
            have h2n : 2 * n ≤ n * 2 ^ (k + 1) := by
              rw [Nat.mul_comm 2 n]; exact Nat.mul_le_mul_left n h2le
            have h1le : 1 ≤ 2 ^ f.bias := Nat.one_le_two_pow
            have hdle : d ≤ d * 2 ^ f.bias := by
              have := Nat.mul_le_mul_left d h1le; rwa [Nat.mul_one] at this
            omega
        have hn_lt_T : n < d * overflowThreshold f := by
          have hstep : d * 2 ^ f.bias < d * overflowThreshold f := by
            rw [Nat.mul_comm d (2 ^ f.bias), Nat.mul_comm d (overflowThreshold f)]
            exact (nat_mul_lt_mul_right_iff hd).mpr hT.2.2.1
          omega
        constructor
        · intro h
          rcases h with h1 | ⟨h2, _⟩ <;> omega
        · intro hle; omega

/-- Decoded form of `roundRatioTiesToEven_eq_inf_iff`: `decodeBits` yields `.inf neg`
IF AND ONLY IF `d * overflowThreshold f ≤ n`. -/
theorem decodeBits_roundRatioTiesToEven_eq_inf_iff (f : IeeeFormat) (neg : Bool) (n d : Nat)
    (hd : 0 < d) :
    decodeBits f (roundRatioTiesToEven f neg n d) = .inf neg ↔ d * overflowThreshold f ≤ n := by
  by_cases hn0 : n = 0
  · subst hn0
    rw [roundRatioTiesToEven_zero f neg d hd, decodeBits_zeroBits]
    have hTpos : 0 < overflowThreshold f := by
      have := (overflowThreshold_eq f).2.2.1
      have := Nat.two_pow_pos f.bias; omega
    have hprod : 0 < d * overflowThreshold f := Nat.mul_pos hd hTpos
    constructor
    · intro h; cases h
    · intro h; omega
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    rw [(roundRatioTiesToEven_overflow_iff f neg n d hn hd).2]
    exact roundRatioTiesToEven_eq_inf_iff f neg n d hd

private theorem bits_le_maxFiniteBits_of_zero_or_finite (f : IeeeFormat) (neg : Bool) (bits : Nat)
    (hlt : bits < 2 ^ f.width)
    (h : decodeBits f bits = .zero neg ∨ ∃ n' d', decodeBits f bits = .finite neg n' d') :
    bits ≤ maxFiniteBits f neg := by
  have henc := encodeBits_unpackBits f bits hlt
  have hEl := unpackBits_exponent_lt f bits
  have hFl := unpackBits_fraction_lt f bits
  have hfields : (unpackBits f bits).neg = neg ∧
      (unpackBits f bits).exponent ≤ 2 ^ f.exponentBits - 2 := by
    unfold decodeBits at h
    dsimp only at h
    split at h
    · split at h
      · rcases h with h | ⟨_, _, h⟩ <;> cases h
      · rcases h with h | ⟨_, _, h⟩ <;> cases h
    · rename_i hEne
      split at h
      · split at h
        · rcases h with h | ⟨_, _, h⟩
          · injection h with hneg; exact ⟨hneg, by omega⟩
          · cases h
        · rcases h with h | ⟨_, _, h⟩
          · cases h
          · injection h with hneg _ _; exact ⟨hneg, by omega⟩
      · rcases h with h | ⟨_, _, h⟩
        · cases h
        · injection h with hneg _ _; exact ⟨hneg, by omega⟩
  rw [← henc]
  unfold maxFiniteBits encodeBits
  rw [hfields.1]
  have hmul : (unpackBits f bits).exponent * 2 ^ f.fractionBits ≤
      (2 ^ f.exponentBits - 2) * 2 ^ f.fractionBits :=
    Nat.mul_le_mul_right _ hfields.2
  omega

/-- **Strict-sub-threshold finiteness**: whenever `n < d * overflowThreshold f` (`0 < d`),
`roundRatioTiesToEven f neg n d` never overflows: its bit pattern satisfies
`≤ maxFiniteBits f neg` and decodes to either `.zero neg` or `.finite neg n' d'`
with `n' / d' ≤ maxFiniteVal f`. -/
theorem roundRatioTiesToEven_lt_inf_isFinite (f : IeeeFormat) (neg : Bool) (n d : Nat)
    (hd : 0 < d) (hlt : n < d * overflowThreshold f) :
    roundRatioTiesToEven f neg n d ≤ maxFiniteBits f neg ∧
    (decodeBits f (roundRatioTiesToEven f neg n d) = .zero neg ∨
      ∃ n' d',
        decodeBits f (roundRatioTiesToEven f neg n d) = .finite neg n' d' ∧
        0 < n' ∧ 0 < d' ∧ n' ≤ maxFiniteVal f * d') := by
  have hbits_lt := roundRatioTiesToEven_lt f neg n d hd
  by_cases hn0 : n = 0
  · subst hn0
    rw [roundRatioTiesToEven_zero f neg d hd]
    have hz : decodeBits f (zeroBits f neg) = .zero neg := decodeBits_zeroBits f neg
    refine ⟨bits_le_maxFiniteBits_of_zero_or_finite f neg _ (by
      rw [← roundRatioTiesToEven_zero f neg d hd]; exact hbits_lt) (Or.inl hz), Or.inl hz⟩
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hnot_inf : decodeBits f (roundRatioTiesToEven f neg n d) ≠ .inf neg := by
      intro hinf
      have hge := (decodeBits_roundRatioTiesToEven_eq_inf_iff f neg n d hd).mp hinf
      omega
    have hsame := (roundRatioTiesToEven_float_half_ulp f neg n d hn hd).2.2 hnot_inf
    have hzf : decodeBits f (roundRatioTiesToEven f neg n d) = .zero neg ∨
        ∃ n' d', decodeBits f (roundRatioTiesToEven f neg n d) = .finite neg n' d' := by
      cases hdec : decodeBits f (roundRatioTiesToEven f neg n d) with
      | zero s =>
        rw [hdec] at hsame
        split at hsame
        · exact Or.inl (by unfold floatKindSameValue at hsame; rw [hsame])
        · exact False.elim hsame
      | finite s n' d' =>
        rw [hdec] at hsame
        split at hsame
        · exact False.elim hsame
        · exact Or.inr ⟨n', d', by unfold floatKindSameValue at hsame; rw [hsame.1]⟩
      | inf s =>
        rw [hdec] at hsame
        split at hsame <;> exact False.elim hsame
      | nan s q p =>
        rw [hdec] at hsame
        split at hsame <;> exact False.elim hsame
    refine ⟨bits_le_maxFiniteBits_of_zero_or_finite f neg _ hbits_lt hzf, ?_⟩
    rcases hzf with hz | ⟨n', d', hf⟩
    · exact Or.inl hz
    · exact Or.inr ⟨n', d', hf,
        decodeBits_finite_num_pos f _ neg n' d' hf,
        decodeBits_finite_den_pos f _ neg n' d' hf,
        decodeBits_finite_le_maxFiniteVal f _ neg n' d' hf⟩

/-- Every rational in the top half-ulp interval `[maxFiniteVal f, overflowThreshold f)`
rounds to `maxFiniteBits f neg` under `roundTiesToEven`. -/
theorem roundRatioTiesToEven_eq_maxFiniteBits (f : IeeeFormat) (neg : Bool) (n d : Nat)
    (hd : 0 < d) (hlo : d * maxFiniteVal f ≤ n) (hhi : n < d * overflowThreshold f) :
    roundRatioTiesToEven f neg n d = maxFiniteBits f neg := by
  have hp := format_overflow_params f
  have hT := overflowThreshold_eq f
  have hmaxV_ge : 2 ^ f.bias ≤ maxFiniteVal f := by
    have h1 : 2 ^ f.fractionBits ≤ 2 ^ (f.fractionBits + 1) - 1 := by
      rw [Nat.pow_succ]; have := Nat.two_pow_pos f.fractionBits; omega
    have hsum : f.fractionBits + (f.bias - f.fractionBits) = f.bias := by
      have := hp.2.1; omega
    calc 2 ^ f.bias
      _ = 2 ^ f.fractionBits * 2 ^ (f.bias - f.fractionBits) := by rw [pow_mul_pow, hsum]
      _ ≤ (2 ^ (f.fractionBits + 1) - 1) * 2 ^ (f.bias - f.fractionBits) :=
        Nat.mul_le_mul_right _ h1
  have hn_pos : 0 < n := by
    have := Nat.mul_le_mul_left d hmaxV_ge
    have := Nat.mul_pos hd (Nat.two_pow_pos f.bias)
    omega
  have hdn_lo : d * 2 ^ f.bias ≤ n := Nat.le_trans (Nat.mul_le_mul_left d hmaxV_ge) hlo
  have hdn_hi : n < 2 * (d * 2 ^ f.bias) := by
    have h2b : 2 * (d * 2 ^ f.bias) = d * 2 ^ (f.bias + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ f.bias) 2, Nat.mul_left_comm]
    have hlt2 : d * overflowThreshold f < d * 2 ^ (f.bias + 1) := by
      rw [Nat.mul_comm d (overflowThreshold f), Nat.mul_comm d (2 ^ (f.bias + 1))]
      exact (nat_mul_lt_mul_right_iff hd).mpr hT.2.2.2
    omega
  have he : ratioExponent n d = f.maxExponent := by
    apply (ratioExponent_eq_iff_powScale_bounds n d f.maxExponent hn_pos hd).mpr
    simp only [IeeeFormat.maxExponent]
    rw [powScale_neg_ofNat]
    exact ⟨hdn_lo, hdn_hi⟩
  let D : Nat := d * 2 ^ (f.bias - f.fractionBits)
  let M : Nat := 2 ^ (f.fractionBits + 1)
  have hDpos : 0 < D := Nat.mul_pos hd (Nat.two_pow_pos _)
  have hMpos : 2 ≤ M := by cases f <;> decide
  have hMeven : M % 2 = 0 := by cases f <;> decide
  have hMD : M * D = 2 * (d * 2 ^ f.bias) := by
    have hexp_sum : (f.fractionBits + 1) + (f.bias - f.fractionBits) = f.bias + 1 := by
      have := hp.2.1; omega
    calc M * D
      _ = d * (2 ^ (f.fractionBits + 1) * 2 ^ (f.bias - f.fractionBits)) := by
        simp only [M, D]; rw [Nat.mul_left_comm]
      _ = d * 2 ^ (f.bias + 1) := by rw [pow_mul_pow, hexp_sum]
      _ = 2 * (d * 2 ^ f.bias) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ f.bias) 2, Nat.mul_left_comm]
  have hloD : (M - 1) * D ≤ n := by
    have heq : (M - 1) * D = d * maxFiniteVal f := by
      simp only [M, D, maxFiniteVal]; rw [Nat.mul_left_comm]
    rw [heq]; exact hlo
  have hhiD : n < M * D := by rw [hMD]; exact hdn_hi
  have hq : n / D = M - 1 := by
    have h1 : M - 1 ≤ n / D := (Nat.le_div_iff_mul_le hDpos).mpr hloD
    have h2 : n / D < M := (Nat.div_lt_iff_lt_mul hDpos).mpr hhiD
    omega
  have hnot_top : roundQuotientTiesToEven n D ≠ M := by
    intro htop
    have hge := (roundQuotientTiesToEven_eq_even_top_iff n D M hDpos hMpos hMeven hhiD).mp htop
    have h2M : 2 * M - 1 = 2 ^ (f.fractionBits + 2) - 1 := by
      have hpow2 : 2 * M = 2 ^ (f.fractionBits + 2) := by
        show 2 * 2 ^ (f.fractionBits + 1) = 2 ^ (f.fractionBits + 2)
        rw [show f.fractionBits + 2 = (f.fractionBits + 1) + 1 by omega,
          Nat.pow_succ 2 (f.fractionBits + 1), Nat.mul_comm]
      rw [hpow2]
    have hD2 : D = 2 * (d * 2 ^ (f.bias - f.fractionBits - 1)) := by
      calc D
        _ = d * 2 ^ ((f.bias - f.fractionBits - 1) + 1) := by
          simp only [D]; exact congrArg (fun k => d * 2 ^ k) hp.2.2.2.2
        _ = d * (2 ^ (f.bias - f.fractionBits - 1) * 2) := by rw [Nat.pow_succ]
        _ = 2 * (d * 2 ^ (f.bias - f.fractionBits - 1)) := by
          rw [Nat.mul_comm _ 2, Nat.mul_left_comm]
    have hrhs_eq : (2 * M - 1) * D = 2 * (d * overflowThreshold f) := by
      unfold overflowThreshold
      rw [h2M, hD2, Nat.mul_left_comm, Nat.mul_left_comm d]
    rw [hrhs_eq] at hge
    omega
  have hsig_eq : roundQuotientTiesToEven n D = M - 1 := by
    unfold roundQuotientTiesToEven at hnot_top ⊢
    dsimp only at hnot_top ⊢
    rw [hq] at hnot_top ⊢
    split at hnot_top
    · exfalso; apply hnot_top; omega
    · rename_i hc; rw [if_neg' hc]
  have hsc_eq : powScale n d ((f.fractionBits : Int) - f.maxExponent) = (n, D) := by
    rw [hp.2.2.2.1]; simp only [powScale, ← hp.2.2.2.2, D]
  have hmax_eq : max (ratioExponent n d) f.minExponent = f.maxExponent := by
    rw [he]; have := hp.1; omega
  unfold roundRatioTiesToEven
  rw [if_neg' (Nat.ne_of_gt hd), if_neg' (Nat.ne_of_gt hn_pos)]
  dsimp only
  rw [hmax_eq, if_neg' (by omega : ¬ (f.maxExponent > f.maxExponent)), hsc_eq]
  dsimp only
  rw [hsig_eq]
  have hncarry : ¬ (2 ^ (f.fractionBits + 1) ≤ M - 1) := by
    have := Nat.two_pow_pos (f.fractionBits + 1); simp only [M]; omega
  have hnsub : ¬ (M - 1 < 2 ^ f.fractionBits) := by
    simp only [M]; rw [Nat.pow_succ]; have := Nat.two_pow_pos f.fractionBits; omega
  simp only [hncarry, decide_false, Bool.false_eq_true, ↓reduceIte,
    if_neg' (by omega : ¬ (f.maxExponent > f.maxExponent)), if_neg' hnsub]
  have hEeq : (f.maxExponent + (f.bias : Int)).toNat = 2 ^ f.exponentBits - 2 := by
    have h2b := hp.2.2.1
    simp only [IeeeFormat.maxExponent]; omega
  have hFeq : M - 1 - 2 ^ f.fractionBits = 2 ^ f.fractionBits - 1 := by
    simp only [M]; rw [Nat.pow_succ]; have := Nat.two_pow_pos f.fractionBits; omega
  rw [hEeq, hFeq]
  rfl

/-- Sharpness of `overflowThreshold f` on both formats and both signs:
- at `overflowThreshold f`, `roundRatioTiesToEven` yields `infBits f neg` (ties to even
  carries out of the odd all-ones significand `2^(fb + 1) - 1`);
- at `overflowThreshold f - 1`, `overflowThreshold f - 1/2`, and `maxFiniteVal f`,
  `roundRatioTiesToEven` yields `maxFiniteBits f neg`. -/
theorem roundRatioTiesToEven_overflow_boundary (f : IeeeFormat) (neg : Bool) :
    roundRatioTiesToEven f neg (overflowThreshold f) 1 = infBits f neg ∧
    roundRatioTiesToEven f neg (overflowThreshold f - 1) 1 = maxFiniteBits f neg ∧
    roundRatioTiesToEven f neg (2 * overflowThreshold f - 1) 2 = maxFiniteBits f neg ∧
    roundRatioTiesToEven f neg (maxFiniteVal f) 1 = maxFiniteBits f neg := by
  have hT := overflowThreshold_eq f
  have hpos : 0 < 2 ^ (f.bias - f.fractionBits - 1) := Nat.two_pow_pos _
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (roundRatioTiesToEven_eq_inf_iff f neg _ 1 Nat.one_pos).mpr
      (by rw [Nat.one_mul]; exact Nat.le_refl _)
  · exact roundRatioTiesToEven_eq_maxFiniteBits f neg _ 1 Nat.one_pos (by omega) (by omega)
  · exact roundRatioTiesToEven_eq_maxFiniteBits f neg _ 2 (by decide) (by omega) (by omega)
  · exact roundRatioTiesToEven_eq_maxFiniteBits f neg _ 1 Nat.one_pos (by omega) (by omega)

/-! ### Operation-level overflow threshold (`add`, `sub`, `mul`, `div`) -/

/-- **Operation-level overflow threshold for finite `add`**: the sum of two finite operands
overflows to the correctly signed infinity IF AND ONLY IF the magnitude of the exact rational
sum is `≥ overflowThreshold f` (`MAX + 2^(MAX_EXP − MANTISSA_DIGITS − 1)`). -/
theorem evalFloatArithBase_add_finite_overflow_iff (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (ha : decodeBits f (a % 2 ^ f.width) = .finite ln lnum lden)
    (hb : decodeBits f (b % 2 ^ f.width) = .finite rn rnum rden) :
    let n : Int := signedNum ln lnum * (rden : Int) + signedNum rn rnum * (lden : Int)
    let sign : Bool := if n = 0 then false else decide (n < 0)
    evalFloatArithBase .add f a b = .some (infBits f sign) ↔
      (lden * rden) * overflowThreshold f ≤ n.natAbs := by
  have hd : 0 < lden * rden :=
    Nat.mul_pos (decodeBits_finite_den_pos f _ ln lnum lden ha)
      (decodeBits_finite_den_pos f _ rn rnum rden hb)
  have hfin := evalFloatArithBase_add_finite f a b ln rn lnum lden rnum rden ha hb
  dsimp only at hfin ⊢
  rw [hfin]
  constructor
  · intro h
    injection h with h
    exact (roundRatioTiesToEven_eq_inf_iff f _ _ _ hd).mp h
  · intro h
    rw [(roundRatioTiesToEven_eq_inf_iff f _ _ _ hd).mpr h]

/-- **Operation-level overflow threshold for finite `sub`** (`a - b` regarded as `a + (-b)`). -/
theorem evalFloatArithBase_sub_finite_overflow_iff (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (ha : decodeBits f (a % 2 ^ f.width) = .finite ln lnum lden)
    (hb : decodeBits f (b % 2 ^ f.width) = .finite rn rnum rden) :
    let n : Int := signedNum ln lnum * (rden : Int) + signedNum (Bool.not rn) rnum * (lden : Int)
    let sign : Bool := if n = 0 then false else decide (n < 0)
    evalFloatArithBase .sub f a b = .some (infBits f sign) ↔
      (lden * rden) * overflowThreshold f ≤ n.natAbs := by
  have hd : 0 < lden * rden :=
    Nat.mul_pos (decodeBits_finite_den_pos f _ ln lnum lden ha)
      (decodeBits_finite_den_pos f _ rn rnum rden hb)
  have hfin := evalFloatArithBase_sub_finite f a b ln rn lnum lden rnum rden ha hb
  dsimp only at hfin ⊢
  rw [hfin]
  constructor
  · intro h
    injection h with h
    exact (roundRatioTiesToEven_eq_inf_iff f _ _ _ hd).mp h
  · intro h
    rw [(roundRatioTiesToEven_eq_inf_iff f _ _ _ hd).mpr h]

/-- **Operation-level overflow threshold for finite `mul`**: the product of two finite operands
overflows to the XOR-signed infinity IF AND ONLY IF the exact rational product is
`≥ overflowThreshold f`. -/
theorem evalFloatArithBase_mul_finite_overflow_iff (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (ha : decodeBits f (a % 2 ^ f.width) = .finite ln lnum lden)
    (hb : decodeBits f (b % 2 ^ f.width) = .finite rn rnum rden) :
    evalFloatArithBase .mul f a b = .some (infBits f (Bool.xor ln rn)) ↔
      (lden * rden) * overflowThreshold f ≤ lnum * rnum := by
  have hd : 0 < lden * rden :=
    Nat.mul_pos (decodeBits_finite_den_pos f _ ln lnum lden ha)
      (decodeBits_finite_den_pos f _ rn rnum rden hb)
  rw [evalFloatArithBase_mul_finite f a b ln rn lnum lden rnum rden ha hb]
  constructor
  · intro h
    injection h with h
    exact (roundRatioTiesToEven_eq_inf_iff f _ _ _ hd).mp h
  · intro h
    rw [(roundRatioTiesToEven_eq_inf_iff f _ _ _ hd).mpr h]

/-- **Operation-level overflow threshold for finite `div`**: the quotient of two finite
operands overflows to the XOR-signed infinity IF AND ONLY IF the exact rational quotient is
`≥ overflowThreshold f`. -/
theorem evalFloatArithBase_div_finite_overflow_iff (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (ha : decodeBits f (a % 2 ^ f.width) = .finite ln lnum lden)
    (hb : decodeBits f (b % 2 ^ f.width) = .finite rn rnum rden) :
    evalFloatArithBase .div f a b = .some (infBits f (Bool.xor ln rn)) ↔
      (lden * rnum) * overflowThreshold f ≤ lnum * rden := by
  have hd : 0 < lden * rnum :=
    Nat.mul_pos (decodeBits_finite_den_pos f _ ln lnum lden ha)
      (decodeBits_finite_num_pos f _ rn rnum rden hb)
  rw [evalFloatArithBase_div_finite f a b ln rn lnum lden rnum rden ha hb]
  constructor
  · intro h
    injection h with h
    exact (roundRatioTiesToEven_eq_inf_iff f _ _ _ hd).mp h
  · intro h
    rw [(roundRatioTiesToEven_eq_inf_iff f _ _ _ hd).mpr h]

/-- **Operation-level `roundTiesToEven` overflow-tie witnesses** (`f32` and `f64`, both signs):
`MAX + ulp(MAX) / 2` lies EXACTLY halfway between `MAX` (odd all-ones significand) and
`2 ^ (bias + 1)`, so ties-to-even carries out and overflows to `±∞`, whereas adding the
predecessor of `ulp(MAX) / 2` leaves `±MAX` unchanged. The operands are `maxFiniteBits`
(`0x7F7FFFFF` / `0x7FEFFFFFFFFFFFFF`) and the half-ulp `2 ^ (bias − fb − 1)`
(`2^103 = 0x73000000` / `2^970 = 0x7C90000000000000`), i.e. the exact sum is
`overflowThreshold f`. -/
theorem evalFloatBinOp_overflow_tie_witness :
    evalFloatBinOp .add .binary32 0x7F7FFFFF 0x73000000 = .some ⟨0x7F800000, 4⟩ ∧
    evalFloatBinOp .add .binary32 0x7F7FFFFF 0x72FFFFFF = .some ⟨0x7F7FFFFF, 4⟩ ∧
    evalFloatBinOp .sub .binary32 0xFF7FFFFF 0x73000000 = .some ⟨0xFF800000, 4⟩ ∧
    evalFloatBinOp .sub .binary32 0xFF7FFFFF 0x72FFFFFF = .some ⟨0xFF7FFFFF, 4⟩ ∧
    evalFloatBinOp .add .binary64 0x7FEFFFFFFFFFFFFF 0x7C90000000000000 =
      .some ⟨0x7FF0000000000000, 8⟩ ∧
    evalFloatBinOp .add .binary64 0x7FEFFFFFFFFFFFFF 0x7C8FFFFFFFFFFFFF =
      .some ⟨0x7FEFFFFFFFFFFFFF, 8⟩ ∧
    evalFloatBinOp .sub .binary64 0xFFEFFFFFFFFFFFFF 0x7C90000000000000 =
      .some ⟨0xFFF0000000000000, 8⟩ ∧
    evalFloatBinOp .sub .binary64 0xFFEFFFFFFFFFFFFF 0x7C8FFFFFFFFFFFFF =
      .some ⟨0xFFEFFFFFFFFFFFFF, 8⟩ ∧
    maxFiniteBits .binary32 false = 0x7F7FFFFF ∧
    maxFiniteBits .binary64 false = 0x7FEFFFFFFFFFFFFF ∧
    decodeBits .binary32 0x73000000 =
      .finite false (2 ^ (IeeeFormat.binary32.bias - IeeeFormat.binary32.fractionBits - 1)) 1 ∧
    decodeBits .binary64 0x7C90000000000000 =
      .finite false (2 ^ (IeeeFormat.binary64.bias - IeeeFormat.binary64.fractionBits - 1)) 1 := by
  have hbin : ∀ (op : BinOp) (f : IeeeFormat) (a b bits : Nat),
      evalFloatCmp op f a b = .none → evalFloatArithBase op f a b = .some bits →
      evalFloatBinOp op f a b = .some ⟨bits, f.byteWidth⟩ := by
    intro op f a b bits hcmp h
    unfold evalFloatBinOp
    rw [hcmp, h]
  refine ⟨
    hbin .add .binary32 0x7F7FFFFF 0x73000000 0x7F800000 rfl (by decide +kernel),
    hbin .add .binary32 0x7F7FFFFF 0x72FFFFFF 0x7F7FFFFF rfl (by decide +kernel),
    hbin .sub .binary32 0xFF7FFFFF 0x73000000 0xFF800000 rfl (by decide +kernel),
    hbin .sub .binary32 0xFF7FFFFF 0x72FFFFFF 0xFF7FFFFF rfl (by decide +kernel),
    hbin .add .binary64 0x7FEFFFFFFFFFFFFF 0x7C90000000000000 0x7FF0000000000000 rfl (by decide +kernel),
    hbin .add .binary64 0x7FEFFFFFFFFFFFFF 0x7C8FFFFFFFFFFFFF 0x7FEFFFFFFFFFFFFF rfl (by decide +kernel),
    hbin .sub .binary64 0xFFEFFFFFFFFFFFFF 0x7C90000000000000 0xFFF0000000000000 rfl (by decide +kernel),
    hbin .sub .binary64 0xFFEFFFFFFFFFFFFF 0x7C8FFFFFFFFFFFFF 0xFFEFFFFFFFFFFFFF rfl (by decide +kernel),
    ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ### Subnormal step spacing, exact underflow-to-zero threshold, exact subnormal `add`/`sub`, & IEEE `rem` bounds -/

/-- Bit pattern of the smallest positive/negative subnormal in format `f`
(`0x00000001` / `0x80000001` for `f32`, `0x0000000000000001` / `0x8000000000000001` for `f64`). -/
def minSubnormalBits (f : IeeeFormat) (neg : Bool) : Nat :=
  encodeBits f neg 0 1

/-- Bit pattern of the largest-magnitude subnormal in format `f`. -/
def maxSubnormalBits (f : IeeeFormat) (neg : Bool) : Nat :=
  encodeBits f neg 0 (2 ^ f.fractionBits - 1)

/-- Bit pattern of the smallest-magnitude normal in format `f` (`f32::MIN_POSITIVE` / `f64::MIN_POSITIVE`). -/
def minNormalBits (f : IeeeFormat) (neg : Bool) : Nat :=
  encodeBits f neg 1 0

/-- Denominator `2 ^ (fb - minExponent)` of the uniform subnormal step spacing in format `f`
(`2^149` for `f32`, `2^1074` for `f64`). -/
def minSubnormalDen (f : IeeeFormat) : Nat :=
  2 ^ ((f.fractionBits : Int) - f.minExponent).toNat

/-- Exact positive rational `(1, 2 ^ (fb - minExponent))` representing the subnormal step
spacing `2 ^ (minExponent - fb)` in format `f`. -/
def minSubnormalVal (f : IeeeFormat) : Nat × Nat :=
  (1, minSubnormalDen f)

private theorem powScale_minSubnormal (f : IeeeFormat) (k : Nat) :
    powScale k 1 (f.minExponent - (f.fractionBits : Int)) = (k, minSubnormalDen f) := by
  have hexp : f.minExponent - (f.fractionBits : Int) =
      Int.negSucc (((f.fractionBits : Int) - f.minExponent).toNat - 1) := by
    cases f <;> rfl
  have hpos : ((f.fractionBits : Int) - f.minExponent).toNat - 1 + 1 =
      ((f.fractionBits : Int) - f.minExponent).toNat := by
    cases f <;> rfl
  rw [hexp]
  unfold powScale minSubnormalDen
  dsimp only
  rw [hpos, Nat.one_mul]

private theorem powScale_to_minSubnormal (f : IeeeFormat) (n d : Nat) :
    powScale n d ((f.fractionBits : Int) - f.minExponent) = (n * minSubnormalDen f, d) := by
  have hexp : (f.fractionBits : Int) - f.minExponent =
      Int.ofNat ((f.fractionBits : Int) - f.minExponent).toNat := by
    cases f <;> rfl
  rw [hexp]
  rfl

private theorem encodeBits_zero_zero (f : IeeeFormat) (neg : Bool) :
    encodeBits f neg 0 0 = zeroBits f neg := by
  unfold encodeBits
  rw [Nat.zero_mul]
  rfl

/-- Closed-form identification of `minSubnormalVal f` with `powScale 1 1 (minExponent - fb)`. -/
theorem minSubnormalVal_eq (f : IeeeFormat) :
    minSubnormalVal f = powScale 1 1 (f.minExponent - (f.fractionBits : Int)) ∧
    0 < minSubnormalDen f ∧
    (minSubnormalVal f).1 = 1 ∧
    (minSubnormalVal f).2 = minSubnormalDen f := by
  refine ⟨(powScale_minSubnormal f 1).symm, ?_, rfl, rfl⟩
  unfold minSubnormalDen
  exact Nat.two_pow_pos _

/-- **Uniform subnormal step spacing**: every subnormal bit pattern `encodeBits f neg 0 F`
(`0 < F < 2^fb`) decodes literally to the exact rational `F / minSubnormalDen f`
(`F * 2^(minExponent - fb)`). -/
theorem decodeBits_subnormal_spacing (f : IeeeFormat) (neg : Bool) (F : Nat)
    (hF0 : 0 < F) (hFlt : F < 2 ^ f.fractionBits) :
    decodeBits f (encodeBits f neg 0 F) = .finite neg F (minSubnormalDen f) := by
  rw [decodeBits_encodeBits f neg 0 F (Nat.two_pow_pos _) hFlt,
    if_neg' (IeeeFormat.max_exp_ne_zero f), if_pos' rfl, if_neg' (Nat.ne_of_gt hF0),
    powScale_minSubnormal]

/-- Exact rational decodings of `minSubnormalBits`, `maxSubnormalBits`, and `minNormalBits`,
showing the seamless unit-step continuation from subnormals (`(2^fb - 1) / minSubnormalDen f`)
into the lowest normal binade (`2^fb / minSubnormalDen f`). -/
theorem decodeBits_minSubnormal_and_minNormal (f : IeeeFormat) (neg : Bool) :
    decodeBits f (minSubnormalBits f neg) = .finite neg 1 (minSubnormalDen f) ∧
    decodeBits f (maxSubnormalBits f neg) = .finite neg (2 ^ f.fractionBits - 1) (minSubnormalDen f) ∧
    decodeBits f (minNormalBits f neg) = .finite neg (2 ^ f.fractionBits) (minSubnormalDen f) := by
  have h1lt : 1 < 2 ^ f.fractionBits := by cases f <;> decide
  have hmax0 : 0 < 2 ^ f.fractionBits - 1 := by omega
  have hmaxLt : 2 ^ f.fractionBits - 1 < 2 ^ f.fractionBits := by omega
  refine ⟨decodeBits_subnormal_spacing f neg 1 Nat.one_pos h1lt,
    decodeBits_subnormal_spacing f neg (2 ^ f.fractionBits - 1) hmax0 hmaxLt, ?_⟩
  unfold minNormalBits
  have hE1 : 1 < 2 ^ f.exponentBits := by cases f <;> decide
  have hEneMax : ¬ (1 = 2 ^ f.exponentBits - 1) := by cases f <;> decide
  have hEne0 : ¬ (1 = 0) := by decide
  rw [decodeBits_encodeBits f neg 1 0 hE1 (Nat.two_pow_pos _),
    if_neg' hEneMax, if_neg' hEne0, Nat.add_zero]
  have hexp : ((1 : Nat) : Int) - (f.bias : Int) - (f.fractionBits : Int) =
      f.minExponent - (f.fractionBits : Int) := by
    cases f <;> rfl
  rw [hexp, powScale_minSubnormal]

/-- **Universal subnormal grid quantization**: EVERY finite IEEE-754 float `n / d` is a
positive integer multiple of `minSubnormalVal f` (`1 / minSubnormalDen f`), and in particular
satisfies `1 / minSubnormalDen f ≤ n / d` (`d ≤ n * minSubnormalDen f`). -/
theorem decodeBits_finite_subnormal_step (f : IeeeFormat) (bits : Nat) (neg : Bool) (n d : Nat)
    (h : decodeBits f bits = .finite neg n d) :
    (∃ k : Nat, 0 < k ∧ k * d = n * minSubnormalDen f) ∧ d ≤ n * minSubnormalDen f := by
  obtain ⟨S, t, hn, hd, hS0, _, htLo, _⟩ := decodeBits_finite_grid f bits neg n d h
  let tmin : Int := f.minExponent - (f.fractionBits : Int)
  let j : Nat := (t - tmin).toNat
  have hj : t - (j : Int) = tmin := by
    have hnn : ((t - tmin).toNat : Int) = t - tmin := Int.toNat_of_nonneg (by omega)
    omega
  have hcross := powScale_shift_cross S j t
  rw [hj, ← hn, ← hd, powScale_minSubnormal] at hcross
  dsimp only at hcross
  have hk0 : 0 < S * 2 ^ j := Nat.mul_pos hS0 (Nat.two_pow_pos j)
  refine ⟨⟨S * 2 ^ j, hk0, hcross⟩, ?_⟩
  have h1le : 1 ≤ S * 2 ^ j := hk0
  have hmul := Nat.mul_le_mul_right d h1le
  rw [Nat.one_mul, hcross] at hmul
  exact hmul

/-- **Exact closed-form rational underflow-to-zero threshold (`roundTiesToEven`)**:
for every `f`, `neg`, and rational `n / d` (`0 < d`), `roundRatioTiesToEven f neg n d`
underflows to `zeroBits f neg` IF AND ONLY IF `n / d ≤ 1 / (2 * minSubnormalDen f)`
(`2 * n * minSubnormalDen f ≤ d`), because the exact halfway tie `1 / (2 * minSubnormalDen f)`
rounds down to the even significand `0`. -/
theorem roundRatioTiesToEven_eq_zero_iff (f : IeeeFormat) (neg : Bool) (n d : Nat) (hd : 0 < d) :
    roundRatioTiesToEven f neg n d = zeroBits f neg ↔ 2 * n * minSubnormalDen f ≤ d := by
  by_cases hn0 : n = 0
  · subst hn0
    rw [roundRatioTiesToEven_zero f neg d hd]
    exact ⟨fun _ => by rw [Nat.mul_zero, Nat.zero_mul]; exact Nat.zero_le d, fun _ => rfl⟩
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hDpos : 0 < minSubnormalDen f := (minSubnormalVal_eq f).2.1
    constructor
    · intro heq
      have hcr := roundRatioTiesToEven_correctly_rounded f neg n d hn hd
      dsimp only at hcr
      have hdec0 : decodeBits f (roundRatioTiesToEven f neg n d) = .zero neg := by
        rw [heq, decodeBits_zeroBits]
      have hneInf : decodeBits f (roundRatioTiesToEven f neg n d) ≠ .inf neg := by
        rw [hdec0]; intro h; cases h
      let e := ratioExponent n d
      let exponent := max e f.minExponent
      let scaled := powScale n d ((f.fractionBits : Int) - exponent)
      let sig := roundQuotientTiesToEven scaled.1 scaled.2
      have hsame : floatKindSameValue (.zero neg)
          (if sig = 0 then .zero neg
           else .finite neg (powScale sig 1 (exponent - f.fractionBits)).1
             (powScale sig 1 (exponent - f.fractionBits)).2) := by
        have htmp := hcr.2.2.2.2.2 hneInf
        rw [hdec0] at htmp
        exact htmp
      have hsig0 : sig = 0 := by
        by_cases h0 : sig = 0
        · exact h0
        · rw [if_neg' h0] at hsame
          exact False.elim hsame
      have hhalf : 2 * scaled.1 ≤ scaled.2 := by
        have hh : 2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs ≤ scaled.2 :=
          hcr.2.2.2.1
        rw [hsig0, Nat.zero_mul] at hh
        have hzero : (((0 : Nat) : Int) - (scaled.1 : Int)).natAbs = scaled.1 := by omega
        rw [hzero] at hh
        exact hh
      by_cases hnorm : f.minExponent ≤ e
      · have hge_sig : 2 ^ f.fractionBits * scaled.2 ≤ scaled.1 := hcr.2.2.1 hnorm
        have h1 : 1 ≤ 2 ^ f.fractionBits := Nat.one_le_two_pow
        have h2 : scaled.2 ≤ scaled.1 := by
          have hm := Nat.mul_le_mul_right scaled.2 h1
          rw [Nat.one_mul] at hm
          exact Nat.le_trans hm hge_sig
        have hds : 0 < scaled.2 := powScale_snd_pos_gen n d hd _
        omega
      · have hexp_eq : exponent = f.minExponent := int_max_eq_right hnorm
        have hsc_eq : scaled = (n * minSubnormalDen f, d) := by
          show powScale n d ((f.fractionBits : Int) - exponent) = _
          rw [hexp_eq, powScale_to_minSubnormal]
        rw [hsc_eq] at hhalf
        dsimp only at hhalf
        rw [Nat.mul_assoc]
        exact hhalf
    · intro hle
      have hle' : 2 * (n * minSubnormalDen f) ≤ d := by rw [← Nat.mul_assoc]; exact hle
      have hbd := powScale_neg_ratioExponent_bounds n d hn hd
      have he_lt : ratioExponent n d < f.minExponent := by
        by_cases hge : f.minExponent ≤ ratioExponent n d
        · exfalso
          have hlo := hbd.1
          by_cases h0 : 0 ≤ ratioExponent n d
          · have hto : (((ratioExponent n d).toNat : Nat) : Int) = ratioExponent n d :=
              Int.toNat_of_nonneg h0
            rw [← hto, powScale_neg_ofNat] at hlo
            dsimp only at hlo
            have h1 : 1 ≤ 2 ^ (ratioExponent n d).toNat := Nat.one_le_two_pow
            have hd_le_n : d ≤ n := by
              have hm := Nat.mul_le_mul_left d h1
              rw [Nat.mul_one] at hm
              exact Nat.le_trans hm hlo
            have hn_le : n ≤ n * minSubnormalDen f := by
              have hm := Nat.mul_le_mul_left n hDpos
              rw [Nat.mul_one] at hm
              exact hm
            omega
          · have hneg : ∃ k : Nat, - ratioExponent n d = Int.ofNat (k + 1) := by
              cases hre : ratioExponent n d with
              | ofNat m => rw [hre] at h0; exact absurd (Int.natCast_nonneg m) h0
              | negSucc m => exact ⟨m, rfl⟩
            rcases hneg with ⟨k, hk⟩
            have hkInt : - ratioExponent n d = (k : Int) + 1 := by
              rw [hk]; exact Int.natCast_succ k
            rw [hk] at hlo
            simp only [powScale] at hlo
            have hk_le : k + 1 ≤ ((f.fractionBits : Int) - f.minExponent).toNat := by
              cases f <;> simp only [IeeeFormat.minExponent, IeeeFormat.fractionBits, IeeeFormat.bias] at hge ⊢ <;> omega
            have h2le : 2 ^ (k + 1) ≤ minSubnormalDen f := two_pow_le_two_pow hk_le
            have hmul : n * 2 ^ (k + 1) ≤ n * minSubnormalDen f := Nat.mul_le_mul_left n h2le
            have hpos : 0 < n * minSubnormalDen f := Nat.mul_pos hn hDpos
            omega
        · omega
      have hmax_eq : max (ratioExponent n d) f.minExponent = f.minExponent := by omega
      have hnot_ov : ¬ (f.minExponent > f.maxExponent) := by cases f <;> decide
      have hsig0 : roundQuotientTiesToEven (n * minSubnormalDen f) d = 0 := by
        unfold roundQuotientTiesToEven
        dsimp only
        have hpos : 0 < n * minSubnormalDen f := Nat.mul_pos hn hDpos
        have hlt : n * minSubnormalDen f < d := by omega
        rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
        have hcond : ¬ (n * minSubnormalDen f * 2 > d ∨ (n * minSubnormalDen f * 2 = d ∧ 0 % 2 = 1)) := by
          intro hc
          rcases hc with h1 | ⟨_, h2⟩ <;> omega
        rw [if_neg' hcond]
      unfold roundRatioTiesToEven
      rw [if_neg' (Nat.ne_of_gt hd), if_neg' (Nat.ne_of_gt hn)]
      dsimp only
      rw [hmax_eq, if_neg' hnot_ov, powScale_to_minSubnormal]
      dsimp only
      rw [hsig0]
      have hncarry : ¬ (2 ^ (f.fractionBits + 1) ≤ 0) := by
        have := Nat.two_pow_pos (f.fractionBits + 1); omega
      have hsub : 0 < 2 ^ f.fractionBits := Nat.two_pow_pos _
      simp only [hncarry, decide_false, Bool.false_eq_true, ↓reduceIte, if_neg' hnot_ov, if_pos' hsub]
      exact encodeBits_zero_zero f neg

/-- Sharpness of the underflow-to-zero boundary on both formats and both signs:
- at the exact tie `1 / (2 * minSubnormalDen f)`, `roundRatioTiesToEven` yields `zeroBits f neg`
  (ties-to-even rounds to the even significand `0`);
- strictly above the tie (`3 / (4 * minSubnormalDen f)`) and at `1 / minSubnormalDen f`, it
  yields `minSubnormalBits f neg`;
- at `3 / (2 * minSubnormalDen f)` (halfway between odd `1` and even `2`), ties-to-even rounds
  up to `encodeBits f neg 0 2`. -/
theorem roundRatioTiesToEven_underflow_boundary (f : IeeeFormat) (neg : Bool) :
    roundRatioTiesToEven f neg 1 (2 * minSubnormalDen f) = zeroBits f neg ∧
    roundRatioTiesToEven f neg 3 (4 * minSubnormalDen f) = minSubnormalBits f neg ∧
    roundRatioTiesToEven f neg 1 (minSubnormalDen f) = minSubnormalBits f neg ∧
    roundRatioTiesToEven f neg 3 (2 * minSubnormalDen f) = encodeBits f neg 0 2 := by
  have hDpos : 0 < minSubnormalDen f := (minSubnormalVal_eq f).2.1
  have hsub_round : ∀ (n d S : Nat), 0 < n → 0 < d →
      n * minSubnormalDen f < 2 ^ f.fractionBits * d →
      roundQuotientTiesToEven (n * minSubnormalDen f) d = S →
      S < 2 ^ f.fractionBits →
      roundRatioTiesToEven f neg n d = encodeBits f neg 0 S := by
    intro n d S hn hd hlt hsig hSlt
    have he_lt : ratioExponent n d < f.minExponent := by
      have hbd := powScale_neg_ratioExponent_bounds n d hn hd
      by_cases hge : f.minExponent ≤ ratioExponent n d
      · exfalso
        have hlo := hbd.1
        have hfb_le : ((f.fractionBits : Int) - f.minExponent).toNat =
            f.fractionBits + (f.bias - 1) := by cases f <;> rfl
        have hfb_pow : 2 ^ f.fractionBits * 2 ^ (f.bias - 1) = minSubnormalDen f := by
          unfold minSubnormalDen
          rw [hfb_le, pow_mul_pow]
        by_cases h0 : 0 ≤ ratioExponent n d
        · have hto : (((ratioExponent n d).toNat : Nat) : Int) = ratioExponent n d :=
            Int.toNat_of_nonneg h0
          rw [← hto, powScale_neg_ofNat] at hlo
          dsimp only at hlo
          have h1 : 1 ≤ 2 ^ (ratioExponent n d).toNat := Nat.one_le_two_pow
          have hd_le_n : d ≤ n := by
            have hm := Nat.mul_le_mul_left d h1
            rw [Nat.mul_one] at hm
            exact Nat.le_trans hm hlo
          have hpow_ge : 2 ^ f.fractionBits ≤ minSubnormalDen f := by
            rw [← hfb_pow]
            have h1b : 1 ≤ 2 ^ (f.bias - 1) := Nat.one_le_two_pow
            have hm := Nat.mul_le_mul_left (2 ^ f.fractionBits) h1b
            rwa [Nat.mul_one] at hm
          have hprod : 2 ^ f.fractionBits * d ≤ n * minSubnormalDen f := by
            rw [Nat.mul_comm (2 ^ f.fractionBits) d]
            exact Nat.mul_le_mul hd_le_n hpow_ge
          omega
        · have hneg : ∃ k : Nat, - ratioExponent n d = Int.ofNat (k + 1) := by
            cases hre : ratioExponent n d with
            | ofNat m => rw [hre] at h0; exact absurd (Int.natCast_nonneg m) h0
            | negSucc m => exact ⟨m, rfl⟩
          rcases hneg with ⟨k, hk⟩
          have hkInt : - ratioExponent n d = (k : Int) + 1 := by
            rw [hk]; exact Int.natCast_succ k
          rw [hk] at hlo
          simp only [powScale] at hlo
          have hk_le : k + 1 ≤ f.bias - 1 := by
            cases f <;> simp only [IeeeFormat.minExponent, IeeeFormat.bias] at hge ⊢ <;> omega
          have h2le : 2 ^ (k + 1) ≤ 2 ^ (f.bias - 1) := two_pow_le_two_pow hk_le
          have hnd : d ≤ n * 2 ^ (f.bias - 1) := Nat.le_trans hlo (Nat.mul_le_mul_left n h2le)
          have hprod : 2 ^ f.fractionBits * d ≤ n * minSubnormalDen f := by
            calc 2 ^ f.fractionBits * d
              _ ≤ 2 ^ f.fractionBits * (n * 2 ^ (f.bias - 1)) := Nat.mul_le_mul_left _ hnd
              _ = n * (2 ^ f.fractionBits * 2 ^ (f.bias - 1)) := by rw [Nat.mul_left_comm]
              _ = n * minSubnormalDen f := by rw [hfb_pow]
          omega
      · omega
    have hmax_eq : max (ratioExponent n d) f.minExponent = f.minExponent := by omega
    have hnot_ov : ¬ (f.minExponent > f.maxExponent) := by cases f <;> decide
    have hncarry : ¬ (2 ^ (f.fractionBits + 1) ≤ S) := by
      have := two_pow_lt_two_pow (Nat.lt_succ_self f.fractionBits); omega
    unfold roundRatioTiesToEven
    rw [if_neg' (Nat.ne_of_gt hd), if_neg' (Nat.ne_of_gt hn)]
    dsimp only
    rw [hmax_eq, if_neg' hnot_ov, powScale_to_minSubnormal]
    dsimp only
    rw [hsig]
    simp only [hncarry, decide_false, Bool.false_eq_true, ↓reduceIte, if_neg' hnot_ov, if_pos' hSlt]
  have h1lt : 1 < 2 ^ f.fractionBits := by cases f <;> decide
  have h2lt : 2 < 2 ^ f.fractionBits := by cases f <;> decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (roundRatioTiesToEven_eq_zero_iff f neg 1 (2 * minSubnormalDen f) (by omega)).mpr (by omega)
  · apply hsub_round 3 (4 * minSubnormalDen f) 1 (by decide) (by omega)
    · have h1 : 1 ≤ 2 ^ f.fractionBits := Nat.one_le_two_pow
      have hm := Nat.mul_le_mul_right (4 * minSubnormalDen f) h1
      rw [Nat.one_mul] at hm; omega
    · unfold roundQuotientTiesToEven
      dsimp only
      have hlt : 3 * minSubnormalDen f < 4 * minSubnormalDen f := by omega
      rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
      rw [if_pos' (Or.inl (by omega))]
    · exact h1lt
  · rw [← roundRatioBits_tiesToEven]
    have hps := powScale_minSubnormal f 1
    have h1 : (1, minSubnormalDen f) = powScale 1 1 (f.minExponent - (f.fractionBits : Int)) := hps.symm
    have hfst : 1 = (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).1 := congrArg Prod.fst h1
    have hsnd : minSubnormalDen f = (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).2 := congrArg Prod.snd h1
    rw [hfst, hsnd]
    exact roundRatioBits_subnormal .tiesToEven f neg 1 Nat.one_pos h1lt
  · apply hsub_round 3 (2 * minSubnormalDen f) 2 (by decide) (by omega)
    · have hm := Nat.mul_le_mul_right (2 * minSubnormalDen f) (Nat.le_of_lt h2lt)
      omega
    · unfold roundQuotientTiesToEven
      dsimp only
      have hq : 3 * minSubnormalDen f / (2 * minSubnormalDen f) = 1 := by
        rw [Nat.mul_div_mul_right 3 2 hDpos]
      have hr : 3 * minSubnormalDen f % (2 * minSubnormalDen f) = minSubnormalDen f := by
        have hdm := Nat.div_add_mod (3 * minSubnormalDen f) (2 * minSubnormalDen f)
        rw [hq] at hdm; omega
      rw [hq, hr]
      rw [if_pos' (Or.inr ⟨by omega, rfl⟩)]
    · exact h2lt

/-- **Operation-level underflow-to-zero threshold for finite `mul`**: the product of two
finite operands underflows to the XOR-signed zero IF AND ONLY IF its exact rational magnitude
is `≤ 1 / (2 * minSubnormalDen f)`. -/
theorem evalFloatArithBase_mul_finite_underflow_zero_iff (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (ha : decodeBits f (a % 2 ^ f.width) = .finite ln lnum lden)
    (hb : decodeBits f (b % 2 ^ f.width) = .finite rn rnum rden) :
    evalFloatArithBase .mul f a b = .some (zeroBits f (Bool.xor ln rn)) ↔
      2 * (lnum * rnum) * minSubnormalDen f ≤ lden * rden := by
  have hd : 0 < lden * rden :=
    Nat.mul_pos (decodeBits_finite_den_pos f _ ln lnum lden ha)
      (decodeBits_finite_den_pos f _ rn rnum rden hb)
  rw [evalFloatArithBase_mul_finite f a b ln rn lnum lden rnum rden ha hb]
  constructor
  · intro h
    injection h with h
    exact (roundRatioTiesToEven_eq_zero_iff f _ _ _ hd).mp h
  · intro h
    rw [(roundRatioTiesToEven_eq_zero_iff f _ _ _ hd).mpr h]

/-- **Operation-level underflow-to-zero threshold for finite `div`**: the quotient of two
finite operands underflows to the XOR-signed zero IF AND ONLY IF its exact rational magnitude
is `≤ 1 / (2 * minSubnormalDen f)`. -/
theorem evalFloatArithBase_div_finite_underflow_zero_iff (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (ha : decodeBits f (a % 2 ^ f.width) = .finite ln lnum lden)
    (hb : decodeBits f (b % 2 ^ f.width) = .finite rn rnum rden) :
    evalFloatArithBase .div f a b = .some (zeroBits f (Bool.xor ln rn)) ↔
      2 * (lnum * rden) * minSubnormalDen f ≤ lden * rnum := by
  have hd : 0 < lden * rnum :=
    Nat.mul_pos (decodeBits_finite_den_pos f _ ln lnum lden ha)
      (decodeBits_finite_num_pos f _ rn rnum rden hb)
  rw [evalFloatArithBase_div_finite f a b ln rn lnum lden rnum rden ha hb]
  constructor
  · intro h
    injection h with h
    exact (roundRatioTiesToEven_eq_zero_iff f _ _ _ hd).mp h
  · intro h
    rw [(roundRatioTiesToEven_eq_zero_iff f _ _ _ hd).mpr h]

/-- **Operation-level subnormal underflow-tie witnesses** (`f32` and `f64`):
- `minSubnormal * 0.5 = +0.0` and `(-minSubnormal) * 0.5 = -0.0` (exact tie rounds down to even `0`);
- `minSubnormal / 2.0 = +0.0`;
- `minSubnormal * 0.75 = minSubnormal` (above tie rounds up to `1`);
- `minSubnormal * 1.5 = 2 * minSubnormal` (tie between odd `1` and even `2` rounds up to `2`). -/
theorem evalFloatBinOp_underflow_tie_witness :
    evalFloatBinOp .mul .binary32 0x00000001 0x3F000000 = .some ⟨0x00000000, 4⟩ ∧
    evalFloatBinOp .mul .binary32 0x80000001 0x3F000000 = .some ⟨0x80000000, 4⟩ ∧
    evalFloatBinOp .div .binary32 0x00000001 0x40000000 = .some ⟨0x00000000, 4⟩ ∧
    evalFloatBinOp .mul .binary32 0x00000001 0x3F400000 = .some ⟨0x00000001, 4⟩ ∧
    evalFloatBinOp .mul .binary32 0x00000001 0x3FC00000 = .some ⟨0x00000002, 4⟩ ∧
    evalFloatBinOp .mul .binary64 0x0000000000000001 0x3FE0000000000000 = .some ⟨0x0000000000000000, 8⟩ ∧
    evalFloatBinOp .mul .binary64 0x8000000000000001 0x3FE0000000000000 = .some ⟨0x8000000000000000, 8⟩ ∧
    evalFloatBinOp .div .binary64 0x0000000000000001 0x4000000000000000 = .some ⟨0x0000000000000000, 8⟩ ∧
    evalFloatBinOp .mul .binary64 0x0000000000000001 0x3FE8000000000000 = .some ⟨0x0000000000000001, 8⟩ ∧
    evalFloatBinOp .mul .binary64 0x0000000000000001 0x3FF8000000000000 = .some ⟨0x0000000000000002, 8⟩ := by
  have hbin : ∀ (op : BinOp) (f : IeeeFormat) (a b bits : Nat),
      evalFloatCmp op f a b = .none → evalFloatArithBase op f a b = .some bits →
      evalFloatBinOp op f a b = .some ⟨bits, f.byteWidth⟩ := by
    intro op f a b bits hcmp h
    unfold evalFloatBinOp
    rw [hcmp, h]
  refine ⟨
    hbin .mul .binary32 0x00000001 0x3F000000 0x00000000 rfl (by decide +kernel),
    hbin .mul .binary32 0x80000001 0x3F000000 0x80000000 rfl (by decide +kernel),
    hbin .div .binary32 0x00000001 0x40000000 0x00000000 rfl (by decide +kernel),
    hbin .mul .binary32 0x00000001 0x3F400000 0x00000001 rfl (by decide +kernel),
    hbin .mul .binary32 0x00000001 0x3FC00000 0x00000002 rfl (by decide +kernel),
    hbin .mul .binary64 0x0000000000000001 0x3FE0000000000000 0x0000000000000000 rfl (by decide +kernel),
    hbin .mul .binary64 0x8000000000000001 0x3FE0000000000000 0x8000000000000000 rfl (by decide +kernel),
    hbin .div .binary64 0x0000000000000001 0x4000000000000000 0x0000000000000000 rfl (by decide +kernel),
    hbin .mul .binary64 0x0000000000000001 0x3FE8000000000000 0x0000000000000001 rfl (by decide +kernel),
    hbin .mul .binary64 0x0000000000000001 0x3FF8000000000000 0x0000000000000002 rfl (by decide +kernel)⟩

/-- **Exact subnormal (and signed-zero) addition without rounding error**: for ANY two
zero-or-subnormal bit patterns `encodeBits f sa 0 fa` and `encodeBits f sb 0 fb`
(`fa, fb < 2^fb`) of arbitrary signs `sa, sb`, `evalFloatArithBase .add` computes the exact
rational sum `(signedNum sa fa + signedNum sb fb) / minSubnormalDen f` with ZERO rounding
error (whether the result stays subnormal, cancels to `+0.0`/`-0.0`, or carries seamlessly
into the lowest normal binade `exponent = 1`). -/
theorem exact_subnormal_add (f : IeeeFormat) (sa sb : Bool) (fa fb : Nat)
    (hfa : fa < 2 ^ f.fractionBits) (hfb : fb < 2 ^ f.fractionBits) :
    let a := encodeBits f sa 0 fa
    let b := encodeBits f sb 0 fb
    let sInt : Int := signedNum sa fa + signedNum sb fb
    if sInt = 0 then
      evalFloatArithBase .add f a b =
        .some (zeroBits f (if fa = 0 ∧ fb = 0 then Bool.and sa sb else false))
    else
      let mag := sInt.natAbs
      let sign := decide (sInt < 0)
      let outBits :=
        if mag < 2 ^ f.fractionBits then encodeBits f sign 0 mag
        else encodeBits f sign 1 (mag - 2 ^ f.fractionBits)
      0 < mag ∧ mag < 2 ^ (f.fractionBits + 1) ∧
      evalFloatArithBase .add f a b = .some outBits ∧
      decodeBits f outBits = .finite sign mag (minSubnormalDen f) := by
  have hE0 : (0 : Nat) < 2 ^ f.exponentBits := Nat.two_pow_pos _
  have hE1 : (1 : Nat) < 2 ^ f.exponentBits := by cases f <;> decide
  have hE1neMax : ¬ (1 = 2 ^ f.exponentBits - 1) := by cases f <;> decide
  have hDpos : 0 < minSubnormalDen f := (minSubnormalVal_eq f).2.1
  have haLt : encodeBits f sa 0 fa < 2 ^ f.width := encodeBits_lt f sa 0 fa hE0 hfa
  have hbLt : encodeBits f sb 0 fb < 2 ^ f.width := encodeBits_lt f sb 0 fb hE0 hfb
  have hdecA : decodeBits f (encodeBits f sa 0 fa % 2 ^ f.width) =
      if fa = 0 then .zero sa else .finite sa fa (minSubnormalDen f) := by
    rw [Nat.mod_eq_of_lt haLt]
    by_cases h0 : fa = 0
    · subst h0; rw [if_pos' rfl, encodeBits_zero_zero]; exact decodeBits_zeroBits f sa
    · rw [if_neg' h0]; exact decodeBits_subnormal_spacing f sa fa (Nat.pos_of_ne_zero h0) hfa
  have hdecB : decodeBits f (encodeBits f sb 0 fb % 2 ^ f.width) =
      if fb = 0 then .zero sb else .finite sb fb (minSubnormalDen f) := by
    rw [Nat.mod_eq_of_lt hbLt]
    by_cases h0 : fb = 0
    · subst h0; rw [if_pos' rfl, encodeBits_zero_zero]; exact decodeBits_zeroBits f sb
    · rw [if_neg' h0]; exact decodeBits_subnormal_spacing f sb fb (Nat.pos_of_ne_zero h0) hfb
  have hroundExact : ∀ (sign : Bool) (mag : Nat),
      0 < mag → mag < 2 ^ (f.fractionBits + 1) →
      let outBits :=
        if mag < 2 ^ f.fractionBits then encodeBits f sign 0 mag
        else encodeBits f sign 1 (mag - 2 ^ f.fractionBits)
      roundRatioTiesToEven f sign mag (minSubnormalDen f) = outBits ∧
      decodeBits f outBits = .finite sign mag (minSubnormalDen f) := by
    intro sign mag hmag0 hmagLt
    dsimp only
    have hps := powScale_minSubnormal f mag
    by_cases hsub : mag < 2 ^ f.fractionBits
    · rw [if_pos' hsub]
      refine ⟨?_, decodeBits_subnormal_spacing f sign mag hmag0 hsub⟩
      have hsc := roundRatioBits_subnormal .tiesToEven f sign mag hmag0 hsub
      rw [hps] at hsc
      rw [← roundRatioBits_tiesToEven]
      exact hsc
    · rw [if_neg' hsub]
      have hge : 2 ^ f.fractionBits ≤ mag := Nat.le_of_not_lt hsub
      have hsubLt : mag - 2 ^ f.fractionBits < 2 ^ f.fractionBits := by
        have hpow : 2 ^ (f.fractionBits + 1) = 2 * 2 ^ f.fractionBits := by rw [Nat.pow_succ]; omega
        omega
      have hEmin : f.minExponent ≤ f.minExponent - (f.fractionBits : Int) + (f.fractionBits : Int) := by
        omega
      have hEmax : f.minExponent - (f.fractionBits : Int) + (f.fractionBits : Int) ≤ f.maxExponent := by
        cases f <;> decide
      have hEtoNat : (f.minExponent - (f.fractionBits : Int) + (f.fractionBits : Int) + (f.bias : Int)).toNat = 1 := by
        cases f <;> rfl
      refine ⟨?_, ?_⟩
      · have hrn := roundRatioBits_normal .tiesToEven f sign mag (f.minExponent - (f.fractionBits : Int))
          hge hmagLt hEmin hEmax
        rw [hps, hEtoNat] at hrn
        rw [← roundRatioBits_tiesToEven]
        exact hrn
      · rw [decodeBits_encodeBits f sign 1 (mag - 2 ^ f.fractionBits) hE1 hsubLt,
          if_neg' hE1neMax, if_neg' (by decide)]
        have hexp : ((1 : Nat) : Int) - (f.bias : Int) - (f.fractionBits : Int) =
            f.minExponent - (f.fractionBits : Int) := by cases f <;> rfl
        have hadd : 2 ^ f.fractionBits + (mag - 2 ^ f.fractionBits) = mag := by omega
        rw [hexp, hadd, powScale_minSubnormal]
  dsimp only
  have hpow2 : 2 ^ (f.fractionBits + 1) = 2 * 2 ^ f.fractionBits := by rw [Nat.pow_succ]; omega
  by_cases hfa0 : fa = 0
  · subst hfa0
    by_cases hfb0 : fb = 0
    · subst hfb0
      have hs0 : signedNum sa 0 + signedNum sb 0 = 0 := by cases sa <;> cases sb <;> rfl
      rw [if_pos' hs0, if_pos' ⟨rfl, rfl⟩]
      unfold evalFloatArithBase
      dsimp only
      rw [hdecA, hdecB, if_pos' rfl, if_pos' rfl]
      rfl
    · have hfbPos : 0 < fb := Nat.pos_of_ne_zero hfb0
      have hsEq : signedNum sa 0 + signedNum sb fb = signedNum sb fb := by
        cases sa <;> simp [signedNum]
      have hsNe : signedNum sa 0 + signedNum sb fb ≠ 0 := by
        rw [hsEq]; cases sb <;> simp only [signedNum, ↓reduceIte, Bool.false_eq_true] <;> omega
      rw [if_neg' hsNe]
      have hmagEq : (signedNum sa 0 + signedNum sb fb).natAbs = fb := by
        rw [hsEq]; cases sb <;> simp [signedNum]
      have hsignEq : decide (signedNum sa 0 + signedNum sb fb < 0) = sb := by
        rw [hsEq]
        cases sb with
        | true => exact decide_eq_true ((signedNum_neg_iff true fb hfbPos).mpr rfl)
        | false =>
          exact decide_eq_false (fun h => Bool.noConfusion ((signedNum_neg_iff false fb hfbPos).mp h))
      rw [hmagEq, hsignEq, if_pos' hfb]
      have hre := hroundExact sb fb hfbPos (by omega)
      rw [if_pos' hfb] at hre
      refine ⟨hfbPos, by omega, ?_, hre.2⟩
      unfold evalFloatArithBase
      dsimp only
      rw [hdecA, hdecB, if_pos' rfl, if_neg' hfb0]
      dsimp only [exactSumFloat]
      rw [if_neg' hfb0, hre.1]
  · have hfaPos : 0 < fa := Nat.pos_of_ne_zero hfa0
    by_cases hfb0 : fb = 0
    · subst hfb0
      have hsEq : signedNum sa fa + signedNum sb 0 = signedNum sa fa := by
        cases sb <;> simp [signedNum]
      have hsNe : signedNum sa fa + signedNum sb 0 ≠ 0 := by
        rw [hsEq]; cases sa <;> simp only [signedNum, ↓reduceIte, Bool.false_eq_true] <;> omega
      rw [if_neg' hsNe]
      have hmagEq : (signedNum sa fa + signedNum sb 0).natAbs = fa := by
        rw [hsEq]; cases sa <;> simp [signedNum]
      have hsignEq : decide (signedNum sa fa + signedNum sb 0 < 0) = sa := by
        rw [hsEq]
        cases sa with
        | true => exact decide_eq_true ((signedNum_neg_iff true fa hfaPos).mpr rfl)
        | false =>
          exact decide_eq_false (fun h => Bool.noConfusion ((signedNum_neg_iff false fa hfaPos).mp h))
      rw [hmagEq, hsignEq, if_pos' hfa]
      have hre := hroundExact sa fa hfaPos (by omega)
      rw [if_pos' hfa] at hre
      refine ⟨hfaPos, by omega, ?_, hre.2⟩
      unfold evalFloatArithBase
      dsimp only
      rw [hdecA, hdecB, if_neg' hfa0, if_pos' rfl]
      dsimp only [exactSumFloat]
      rw [if_neg' hfa0, hre.1]
    · have hfbPos : 0 < fb := Nat.pos_of_ne_zero hfb0
      have hdecA' : decodeBits f (encodeBits f sa 0 fa % 2 ^ f.width) =
          .finite sa fa (minSubnormalDen f) := by rw [hdecA, if_neg' hfa0]
      have hdecB' : decodeBits f (encodeBits f sb 0 fb % 2 ^ f.width) =
          .finite sb fb (minSubnormalDen f) := by rw [hdecB, if_neg' hfb0]
      have hadd := evalFloatArithBase_add_finite f (encodeBits f sa 0 fa) (encodeBits f sb 0 fb)
        sa sb fa (minSubnormalDen f) fb (minSubnormalDen f) hdecA' hdecB'
      dsimp only at hadd
      have hnumEq : signedNum sa fa * (minSubnormalDen f : Int) +
          signedNum sb fb * (minSubnormalDen f : Int) =
          (signedNum sa fa + signedNum sb fb) * (minSubnormalDen f : Int) := by
        rw [Int.add_mul]
      rw [hnumEq] at hadd
      by_cases hs0 : signedNum sa fa + signedNum sb fb = 0
      · rw [if_pos' hs0, if_neg' (fun h => hfa0 h.1)]
        rw [hs0, Int.zero_mul, if_pos' rfl] at hadd
        rw [hadd]
        exact congrArg Option.some
          (roundRatioTiesToEven_zero f false (minSubnormalDen f * minSubnormalDen f) (Nat.mul_pos hDpos hDpos))
      · rw [if_neg' hs0]
        have hmagPos : 0 < (signedNum sa fa + signedNum sb fb).natAbs := by omega
        have hmagLt : (signedNum sa fa + signedNum sb fb).natAbs < 2 ^ (f.fractionBits + 1) := by
          cases sa <;> cases sb <;> simp only [signedNum, ↓reduceIte, Bool.false_eq_true] <;> omega
        have hre := hroundExact (decide (signedNum sa fa + signedNum sb fb < 0))
          (signedNum sa fa + signedNum sb fb).natAbs hmagPos hmagLt
        refine ⟨hmagPos, hmagLt, ?_, hre.2⟩
        have hprodNe : (signedNum sa fa + signedNum sb fb) * (minSubnormalDen f : Int) ≠ 0 := by
          intro h
          rcases Int.mul_eq_zero.mp h with h1 | h2
          · exact hs0 h1
          · omega
        have hnegIff : ((signedNum sa fa + signedNum sb fb) * (minSubnormalDen f : Int) < 0) ↔
            (signedNum sa fa + signedNum sb fb < 0) := by
          have hDpI : (0 : Int) < (minSubnormalDen f : Int) := Int.natCast_pos.mpr hDpos
          constructor
          · intro hlt
            by_cases hs : signedNum sa fa + signedNum sb fb < 0
            · exact hs
            · exfalso
              have hnn : 0 ≤ (signedNum sa fa + signedNum sb fb) * (minSubnormalDen f : Int) :=
                Int.mul_nonneg (by omega) (by omega)
              omega
          · intro hlt
            have h1 : 0 < -(signedNum sa fa + signedNum sb fb) := by omega
            have h2 := Int.mul_pos h1 hDpI
            rw [Int.neg_mul] at h2
            omega
        have hsignEq : decide ((signedNum sa fa + signedNum sb fb) * (minSubnormalDen f : Int) < 0) =
            decide (signedNum sa fa + signedNum sb fb < 0) := by
          by_cases hs : signedNum sa fa + signedNum sb fb < 0
          · rw [decide_eq_true (hnegIff.mpr hs), decide_eq_true hs]
          · rw [decide_eq_false (fun h => hs (hnegIff.mp h)), decide_eq_false hs]
        have habsEq : ((signedNum sa fa + signedNum sb fb) * (minSubnormalDen f : Int)).natAbs =
            (signedNum sa fa + signedNum sb fb).natAbs * minSubnormalDen f := by
          rw [Int.natAbs_mul, Int.natAbs_natCast]
        rw [if_neg' hprodNe, hsignEq, habsEq] at hadd
        rw [hadd, ← roundRatioBits_tiesToEven,
          roundRatioBits_mul .tiesToEven f _ _ _ (minSubnormalDen f) hDpos,
          roundRatioBits_tiesToEven, hre.1]

/-- **Exact subnormal (and signed-zero) subtraction without rounding error**: for ANY two
zero-or-subnormal bit patterns `encodeBits f sa 0 fa` and `encodeBits f sb 0 fb`
(`fa, fb < 2^fb`), `evalFloatArithBase .sub` computes the exact difference with ZERO rounding
error (reducing to `exact_subnormal_add` on the negated RHS). -/
theorem exact_subnormal_sub (f : IeeeFormat) (sa sb : Bool) (fa fb : Nat)
    (hfa : fa < 2 ^ f.fractionBits) (hfb : fb < 2 ^ f.fractionBits) :
    let a := encodeBits f sa 0 fa
    let b := encodeBits f sb 0 fb
    let sInt : Int := signedNum sa fa + signedNum (Bool.not sb) fb
    if sInt = 0 then
      evalFloatArithBase .sub f a b =
        .some (zeroBits f (if fa = 0 ∧ fb = 0 then Bool.and sa (Bool.not sb) else false))
    else
      let mag := sInt.natAbs
      let sign := decide (sInt < 0)
      let outBits :=
        if mag < 2 ^ f.fractionBits then encodeBits f sign 0 mag
        else encodeBits f sign 1 (mag - 2 ^ f.fractionBits)
      0 < mag ∧ mag < 2 ^ (f.fractionBits + 1) ∧
      evalFloatArithBase .sub f a b = .some outBits ∧
      decodeBits f outBits = .finite sign mag (minSubnormalDen f) := by
  have hE0 : (0 : Nat) < 2 ^ f.exponentBits := Nat.two_pow_pos _
  have hsub_eq : evalFloatArithBase .sub f (encodeBits f sa 0 fa) (encodeBits f sb 0 fb) =
      evalFloatArithBase .add f (encodeBits f sa 0 fa) (encodeBits f (Bool.not sb) 0 fb) := by
    have hneg := evalFloatNeg_encodeBits f sb 0 fb hE0 hfb
    rw [← hneg]
    unfold evalFloatArithBase
    dsimp only
    simp only [decodeBits_mod, decodeBits_evalFloatNeg]
  have hadd := exact_subnormal_add f sa (Bool.not sb) fa fb hfa hfb
  dsimp only at hadd ⊢
  rw [hsub_eq]
  exact hadd

/-- **Combined exact subnormal addition and subtraction (`exact_subnormal_add_sub`)**:
for any two zero-or-subnormal operands `a = encodeBits f sa 0 fa` and `b = encodeBits f sb 0 fb`,
BOTH `a + b` and `a - b` are represented with zero rounding error (exact rational value
`(signedNum sa fa ± signedNum sb fb) / minSubnormalDen f`, with IEEE-754 signed-zero sign on
exact zero). -/
theorem exact_subnormal_add_sub (f : IeeeFormat) (sa sb : Bool) (fa fb : Nat)
    (hfa : fa < 2 ^ f.fractionBits) (hfb : fb < 2 ^ f.fractionBits) :
    let a := encodeBits f sa 0 fa
    let b := encodeBits f sb 0 fb
    let sumInt : Int := signedNum sa fa + signedNum sb fb
    let diffInt : Int := signedNum sa fa + signedNum (Bool.not sb) fb
    (if sumInt = 0 then
       evalFloatArithBase .add f a b =
         .some (zeroBits f (if fa = 0 ∧ fb = 0 then Bool.and sa sb else false))
     else
       ∃ outBits,
         evalFloatArithBase .add f a b = .some outBits ∧
         decodeBits f outBits = .finite (decide (sumInt < 0)) sumInt.natAbs (minSubnormalDen f)) ∧
    (if diffInt = 0 then
       evalFloatArithBase .sub f a b =
         .some (zeroBits f (if fa = 0 ∧ fb = 0 then Bool.and sa (Bool.not sb) else false))
     else
       ∃ outBits,
         evalFloatArithBase .sub f a b = .some outBits ∧
         decodeBits f outBits = .finite (decide (diffInt < 0)) diffInt.natAbs (minSubnormalDen f)) := by
  have ha := exact_subnormal_add f sa sb fa fb hfa hfb
  have hs := exact_subnormal_sub f sa sb fa fb hfa hfb
  dsimp only at ha hs ⊢
  constructor
  · by_cases h0 : signedNum sa fa + signedNum sb fb = 0
    · rw [if_pos' h0] at ha ⊢; exact ha
    · rw [if_neg' h0] at ha ⊢; exact ⟨_, ha.2.2.1, ha.2.2.2⟩
  · by_cases h0 : signedNum sa fa + signedNum (Bool.not sb) fb = 0
    · rw [if_pos' h0] at hs ⊢; exact hs
    · rw [if_neg' h0] at hs ⊢; exact ⟨_, hs.2.2.1, hs.2.2.2⟩

/-- **Gradual underflow for addition (`a + b = ±0 ↔ a == -b`)**: for any two finite (including
signed zero) IEEE-754 bit patterns `a` and `b`, `evalFloatArithBase .add f a b` returns a
signed zero IF AND ONLY IF `a == -b` (`evalFloatCmp .eq f a (evalFloatNeg f b) = .some true`). -/
theorem gradual_underflow_add_zero_iff (f : IeeeFormat) (a b : Nat)
    (haFin : isNaNBits f a = false ∧ ∀ s, decodeBits f a ≠ .inf s)
    (hbFin : isNaNBits f b = false ∧ ∀ s, decodeBits f b ≠ .inf s) :
    (∃ zsign, evalFloatArithBase .add f a b = .some (zeroBits f zsign)) ↔
      evalFloatCmp .eq f a (evalFloatNeg f b) = .some true := by
  have hnbFin : isNaNBits f (evalFloatNeg f b) = false ∧
      ∀ s, decodeBits f (evalFloatNeg f b) ≠ .inf s := by
    refine ⟨by rw [isNaNBits_evalFloatNeg]; exact hbFin.1, fun s h => ?_⟩
    rw [decodeBits_evalFloatNeg] at h
    cases hb : decodeBits f b with
    | inf t =>
      rw [hb] at h
      exact hbFin.2 t hb
    | zero _ => rw [hb] at h; cases h
    | finite _ _ _ => rw [hb] at h; cases h
    | nan _ _ _ => rw [hb] at h; cases h
  have hsub_eq : evalFloatArithBase .sub f a (evalFloatNeg f b) = evalFloatArithBase .add f a b := by
    unfold evalFloatArithBase
    dsimp only
    simp only [decodeBits_mod, decodeBits_evalFloatNeg, negateFloatKind_involutive]
  rw [← hsub_eq]
  exact gradual_underflow_sub_zero_iff f a (evalFloatNeg f b) haFin hnbFin

private theorem unpackBits_evalFloatAbs (f : IeeeFormat) (bits : Nat) :
    unpackBits f (evalFloatAbs f bits) =
      { neg := false
        exponent := (unpackBits f bits).exponent
        fraction := (unpackBits f bits).fraction } := by
  cases f
  · simp only [evalFloatAbs, unpackBits, IeeeFormat.width, IeeeFormat.fractionBits,
      IeeeFormat.exponentBits, Nat.reducePow, Nat.reduceSub, FloatComponents.mk.injEq,
      nat_beq_eq_decide]
    have h1 : bits % 2147483648 / 2147483648 % 2 = 0 := by omega
    rw [h1]
    exact ⟨rfl, by omega, by omega⟩
  · simp only [evalFloatAbs, unpackBits, IeeeFormat.width, IeeeFormat.fractionBits,
      IeeeFormat.exponentBits, Nat.reducePow, Nat.reduceSub, FloatComponents.mk.injEq,
      nat_beq_eq_decide]
    have h1 : bits % 9223372036854775808 / 9223372036854775808 % 2 = 0 := by omega
    rw [h1]
    exact ⟨rfl, by omega, by omega⟩

private theorem decodeBits_evalFloatAbs (f : IeeeFormat) (bits : Nat) :
    decodeBits f (evalFloatAbs f bits) =
      match decodeBits f bits with
      | .zero _ => .zero false
      | .finite _ n d => .finite false n d
      | .inf _ => .inf false
      | .nan _ q p => .nan false q p := by
  unfold decodeBits
  rw [unpackBits_evalFloatAbs]
  dsimp only
  split
  · split <;> rfl
  · split
    · split <;> rfl
    · rfl

/-- **IEEE `rem` sign and strict magnitude-bound law**: for ANY zero-or-finite dividend `a`
(with sign `ln`) and ANY finite nonzero divisor `b` (`decodeBits f (b % 2^w) = .finite rn rnum rden`),
`evalFloatArithBase .rem f a b` returns `.some outBits` with:
1. canonical bit width (`outBits < 2^f.width`), never NaN and never `±∞`;
2. sign bit `(unpackBits f outBits).neg = ln` (always matching the dividend, even on `±0.0`,
   independent of the divisor's sign `rn`);
3. strict float-comparison bound `|a % b| < |b|` (`evalFloatCmp .lt f (evalFloatAbs f outBits) (evalFloatAbs f b) = .some true`);
4. exact zero-or-finite rational bound `0 ≤ |a % b| < |b|`. -/
theorem evalFloatArithBase_rem_finite_sign_and_bound (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (rnum rden : Nat)
    (ha : decodeBits f (a % 2 ^ f.width) = .zero ln ∨
      ∃ lnum lden, decodeBits f (a % 2 ^ f.width) = .finite ln lnum lden)
    (hb : decodeBits f (b % 2 ^ f.width) = .finite rn rnum rden) :
    ∃ outBits,
      evalFloatArithBase .rem f a b = .some outBits ∧
      outBits < 2 ^ f.width ∧
      isNaNBits f outBits = false ∧
      (∀ s, decodeBits f outBits ≠ .inf s) ∧
      (unpackBits f outBits).neg = ln ∧
      evalFloatCmp .lt f (evalFloatAbs f outBits) (evalFloatAbs f b) = .some true ∧
      (outBits = zeroBits f ln ∨
        ∃ n' d', decodeBits f outBits = .finite ln n' d' ∧ n' * rden < rnum * d') := by
  have hrn : 0 < rnum := decodeBits_finite_num_pos f _ rn rnum rden hb
  have hdecAbsB : decodeBits f (evalFloatAbs f b % 2 ^ f.width) = .finite false rnum rden := by
    rw [decodeBits_mod, decodeBits_evalFloatAbs, ← decodeBits_mod, hb]
  have hunpackSign : ∀ x s,
      (decodeBits f x = .zero s ∨ ∃ n d, decodeBits f x = .finite s n d) →
      (unpackBits f x).neg = s := by
    intro x s hx
    unfold decodeBits at hx
    dsimp only at hx
    split at hx
    · split at hx <;> rcases hx with h | ⟨_, _, h⟩ <;> cases h
    · split at hx
      · split at hx
        · rcases hx with h | ⟨_, _, h⟩
          · injection h
          · cases h
        · rcases hx with h | ⟨_, _, h⟩
          · cases h
          · injection h
      · rcases hx with h | ⟨_, _, h⟩
        · cases h
        · injection h
  rcases ha with ha0 | ⟨lnum, lden, haFin⟩
  · have hrem : evalFloatArithBase .rem f a b = .some (zeroBits f ln) := by
      unfold evalFloatArithBase
      dsimp only
      rw [ha0, hb]
      dsimp only
      rw [if_neg' (Nat.ne_of_gt hrn)]
    have hzLt : zeroBits f ln < 2 ^ f.width := by cases f <;> cases ln <;> decide
    have hzDec : decodeBits f (zeroBits f ln) = .zero ln := decodeBits_zeroBits f ln
    have hltCmp : evalFloatCmp .lt f (evalFloatAbs f (zeroBits f ln)) (evalFloatAbs f b) = .some true := by
      unfold evalFloatCmp evalFloatPartialCompare
      dsimp only
      rw [decodeBits_mod, decodeBits_evalFloatAbs, hzDec, hdecAbsB]
      dsimp only
      rw [if_neg' (Nat.ne_of_gt hrn)]
      rfl
    refine ⟨zeroBits f ln, hrem, hzLt, isNaNBits_zeroBits f ln,
      (fun s h => by rw [hzDec] at h; cases h),
      hunpackSign _ ln (Or.inl hzDec), hltCmp, Or.inl rfl⟩
  · obtain ⟨outBits, heval, _, _, hexact⟩ :=
      evalFloatArithBase_rem_finite_exact f a b ln rn lnum lden rnum rden haFin hb
    have hld : 0 < lden := decodeBits_finite_den_pos f _ ln lnum lden haFin
    have hrd : 0 < rden := decodeBits_finite_den_pos f _ rn rnum rden hb
    have houtLt : outBits < 2 ^ f.width := by
      unfold evalFloatArithBase at heval
      dsimp only at heval
      rw [haFin, hb] at heval
      dsimp only at heval
      rw [if_neg' (Nat.ne_of_gt hrn)] at heval
      injection heval with hEq
      rw [← hEq]
      exact roundRatioTiesToEven_lt f ln _ _ (Nat.mul_pos hld hrd)
    by_cases hrem0 : lnum * rden - (lnum * rden) / (lden * rnum) * (lden * rnum) = 0
    · rw [if_pos' hrem0] at hexact
      subst hexact
      have hzDec : decodeBits f (zeroBits f ln) = .zero ln := decodeBits_zeroBits f ln
      have hltCmp : evalFloatCmp .lt f (evalFloatAbs f (zeroBits f ln)) (evalFloatAbs f b) = .some true := by
        unfold evalFloatCmp evalFloatPartialCompare
        dsimp only
        rw [decodeBits_mod, decodeBits_evalFloatAbs, hzDec, hdecAbsB]
        dsimp only
        rw [if_neg' (Nat.ne_of_gt hrn)]
        rfl
      exact ⟨zeroBits f ln, heval, houtLt, isNaNBits_zeroBits f ln,
        (fun s h => by rw [hzDec] at h; cases h),
        hunpackSign _ ln (Or.inl hzDec), hltCmp, Or.inl rfl⟩
    · rw [if_neg' hrem0] at hexact
      rcases hexact with ⟨n', d', hdec, _, hlt_b⟩
      have hnotNan : isNaNBits f outBits = false := by unfold isNaNBits; rw [hdec]
      have hnotInf : ∀ s, decodeBits f outBits ≠ .inf s := fun s h => by rw [hdec] at h; cases h
      have hltCmp : evalFloatCmp .lt f (evalFloatAbs f outBits) (evalFloatAbs f b) = .some true := by
        unfold evalFloatCmp evalFloatPartialCompare
        dsimp only
        rw [decodeBits_mod, decodeBits_evalFloatAbs, hdec, hdecAbsB]
        simp only [signedNum, Bool.false_eq_true, ↓reduceIte]
        have hltI : (n' : Int) * (rden : Int) < (rnum : Int) * (d' : Int) := by
          have := Int.ofNat_lt.mpr hlt_b
          simp only [Int.natCast_mul] at this
          exact this
        rw [if_pos' hltI]
      exact ⟨outBits, heval, houtLt, hnotNan, hnotInf,
        hunpackSign _ ln (Or.inr ⟨n', d', hdec⟩), hltCmp, Or.inr ⟨n', d', hdec, hlt_b⟩⟩

/-- **IEEE `rem` identity when `|a| < |b|`**: whenever two finite floats `a` and `b` satisfy
`|a| < |b|` (`lnum * rden < lden * rnum`), `evalFloatArithBase .rem f a b` returns `a % 2^f.width`
verbatim (preserving sign and bit pattern). -/
theorem evalFloatArithBase_rem_finite_lt_self (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (ha : decodeBits f (a % 2 ^ f.width) = .finite ln lnum lden)
    (hb : decodeBits f (b % 2 ^ f.width) = .finite rn rnum rden)
    (hlt : lnum * rden < lden * rnum) :
    evalFloatArithBase .rem f a b = .some (a % 2 ^ f.width) := by
  have hrn : 0 < rnum := decodeBits_finite_num_pos f _ rn rnum rden hb
  have hrd : 0 < rden := decodeBits_finite_den_pos f _ rn rnum rden hb
  have hself := evalFloatToFloatRoundTiesToEven_self_eq f (a % 2 ^ f.width)
    (Nat.mod_lt a (Nat.two_pow_pos f.width))
  unfold evalFloatToFloatRoundTiesToEven at hself
  rw [ha] at hself
  dsimp only at hself
  unfold evalFloatArithBase
  dsimp only
  rw [ha, hb]
  dsimp only
  rw [if_neg' (Nat.ne_of_gt hrn), Nat.div_eq_of_lt hlt, Nat.zero_mul, Nat.sub_zero,
    ← roundRatioBits_tiesToEven, roundRatioBits_mul .tiesToEven f ln lnum lden rden hrd,
    roundRatioBits_tiesToEven, hself]

/-- **IEEE `rem` self-annihilation (`a % a = ±0`, `a % (-a) = ±0`)**: for every finite nonzero
float `a` with sign `ln`, both `a % a` and `a % (-a)` equal `zeroBits f ln`. -/
theorem evalFloatArithBase_rem_self_eq_zero (f : IeeeFormat) (a : Nat)
    (ln : Bool) (lnum lden : Nat)
    (ha : decodeBits f (a % 2 ^ f.width) = .finite ln lnum lden) :
    evalFloatArithBase .rem f a a = .some (zeroBits f ln) ∧
    evalFloatArithBase .rem f a (evalFloatNeg f a) = .some (zeroBits f ln) := by
  have hneg : decodeBits f (evalFloatNeg f a % 2 ^ f.width) = .finite (Bool.not ln) lnum lden := by
    rw [decodeBits_mod, decodeBits_evalFloatNeg, ← decodeBits_mod, ha]; rfl
  have hdvd : (lden * lnum) ∣ (lnum * lden) := by rw [Nat.mul_comm]; exact Nat.dvd_refl _
  exact ⟨(evalFloatArithBase_rem_finite_eq_zero_iff f a a ln ln lnum lden lnum lden ha ha).mpr hdvd,
    (evalFloatArithBase_rem_finite_eq_zero_iff f a (evalFloatNeg f a) ln (Bool.not ln)
      lnum lden lnum lden ha hneg).mpr hdvd⟩

/-! ## §4. `FloatArithMode` inclusion, `nanChoices` structure, & relational sign symmetry -/

/-- Flipping the sign argument of `roundRatioTiesToEven` flips the output sign bit
whenever `0 < d`. -/
theorem roundRatioTiesToEven_neg (f : IeeeFormat) (neg : Bool) (n d : Nat) (hd : 0 < d) :
    roundRatioTiesToEven f (Bool.not neg) n d = evalFloatNeg f (roundRatioTiesToEven f neg n d) := by
  have hd0 : ¬ (d = 0) := by omega
  unfold roundRatioTiesToEven
  rw [if_neg' hd0, if_neg' hd0]
  by_cases hn0 : n = 0
  · rw [if_pos' hn0, if_pos' hn0]
    exact (evalFloatNeg_zeroBits f neg).symm
  · rw [if_neg' hn0, if_neg' hn0]
    have hcons := roundRatioTiesToEven_consistent f n d (Nat.pos_of_ne_zero hn0) hd
    dsimp only at hcons ⊢
    generalize hexp : max (ratioExponent n d) f.minExponent = exponent at hcons ⊢
    generalize hsc : powScale n d ((f.fractionBits : Int) - exponent) = scaled at hcons ⊢
    generalize hsig : roundQuotientTiesToEven scaled.1 scaled.2 = sig at hcons ⊢
    -- Keep the implication half of `hcons` out of `omega`'s reach (see `Hold`).
    have hsig_le : sig ≤ 2 ^ (f.fractionBits + 1) := hcons.1
    have hsub_min : Hold (sig < 2 ^ f.fractionBits → exponent = f.minExponent) := ⟨hcons.2⟩
    clear hcons
    have hmin_le : f.minExponent ≤ exponent := by
      rw [← hexp]; omega
    by_cases hov1 : exponent > f.maxExponent
    · rw [if_pos' hov1, if_pos' hov1]
      exact (evalFloatNeg_infBits f neg).symm
    · rw [if_neg' hov1, if_neg' hov1]
      have h2b := IeeeFormat.two_bias_lt f
      have hpow : 2 ^ (f.fractionBits + 1) = 2 * 2 ^ f.fractionBits := by
        rw [Nat.pow_succ]; omega
      by_cases hcarry : 2 ^ (f.fractionBits + 1) ≤ sig
      · have hsig_eq : sig = 2 ^ (f.fractionBits + 1) := by omega
        have hdiv2 : sig / 2 = 2 ^ f.fractionBits := by rw [hsig_eq, hpow]; omega
        simp only [hcarry, decide_true, ↓reduceIte, hdiv2]
        by_cases hov2 : exponent + 1 > f.maxExponent
        · rw [if_pos' hov2, if_pos' hov2]
          exact (evalFloatNeg_infBits f neg).symm
        · rw [if_neg' hov2, if_neg' hov2]
          have hltF : ¬ (2 ^ f.fractionBits < 2 ^ f.fractionBits) := Nat.lt_irrefl _
          have hgeF : ¬ (2 ^ (f.fractionBits + 1) ≤ 2 ^ f.fractionBits) := by
            have := two_pow_lt_two_pow (Nat.lt_succ_self f.fractionBits); omega
          rw [if_neg' hltF, if_neg' hltF, if_neg' hgeF, if_neg' hgeF, Nat.sub_self]
          have hE : (exponent + 1 + (f.bias : Int)).toNat < 2 ^ f.exponentBits := by
            simp only [IeeeFormat.minExponent, IeeeFormat.maxExponent] at hmin_le hov2; omega
          exact (evalFloatNeg_encodeBits f neg _ 0 hE (Nat.two_pow_pos _)).symm
      · simp only [hcarry, decide_false, Bool.false_eq_true, ↓reduceIte, if_neg' hov1]
        by_cases hsub : sig < 2 ^ f.fractionBits
        · have heqMin : exponent = f.minExponent := hsub_min.val hsub
          rw [if_pos' hsub, if_pos' hsub, if_pos' heqMin, if_pos' heqMin]
          exact (evalFloatNeg_encodeBits f neg 0 sig (Nat.two_pow_pos _) hsub).symm
        · rw [if_neg' hsub, if_neg' hsub]
          have hE : (exponent + (f.bias : Int)).toNat < 2 ^ f.exponentBits := by
            simp only [IeeeFormat.minExponent, IeeeFormat.maxExponent] at hmin_le hov1; omega
          have hF : sig - 2 ^ f.fractionBits < 2 ^ f.fractionBits := by omega
          exact (evalFloatNeg_encodeBits f neg _ _ hE hF).symm

/-- `evalFloatToFloatRoundTiesToEven` commutes with bitwise unary negation on every
bit pattern (zeros, subnormals, normals, infinities, and NaNs). -/
theorem evalFloatToFloatRoundTiesToEven_evalFloatNeg (src dst : IeeeFormat) (bits : Nat) :
    evalFloatToFloatRoundTiesToEven src dst (evalFloatNeg src bits) =
      evalFloatNeg dst (evalFloatToFloatRoundTiesToEven src dst bits) := by
  unfold evalFloatToFloatRoundTiesToEven
  rw [decodeBits_evalFloatNeg]
  cases hdec : decodeBits src bits with
  | zero neg =>
    exact (evalFloatNeg_zeroBits dst neg).symm
  | finite neg n d =>
    exact roundRatioTiesToEven_neg dst neg n d (decodeBits_finite_den_pos src bits neg n d hdec)
  | inf neg =>
    exact (evalFloatNeg_infBits dst neg).symm
  | nan neg q payload =>
    obtain ⟨_, _, hp, _⟩ := decodeBits_nan_payload src bits neg q payload hdec
    have hE : 2 ^ dst.exponentBits - 1 < 2 ^ dst.exponentBits :=
      Nat.sub_lt (Nat.two_pow_pos _) (by decide)
    have hF := convertNaNPayload_lt src dst payload hp
    exact (evalFloatNeg_encodeBits dst neg _ _ hE hF).symm

/-! ### `nanChoices` membership, width bounds, NaN classification, & quietness -/

theorem mem_expandNanSigns_iff (f : IeeeFormat) (x : Nat) (cs : List Nat) :
    x ∈ expandNanSigns f cs ↔ ∃ c, c ∈ cs ∧ (x = c ∨ x = evalFloatNeg f c) := by
  induction cs with
  | nil =>
    constructor
    · intro h; cases h
    · intro ⟨_, hc, _⟩; cases hc
  | cons c rest ih =>
    unfold expandNanSigns
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases List.mem_cons.mp h with rfl | h1
      · exact ⟨x, List.mem_cons_self, Or.inl rfl⟩
      · rcases List.mem_cons.mp h1 with rfl | h2
        · exact ⟨c, List.mem_cons_self, Or.inr rfl⟩
        · rcases ih.mp h2 with ⟨c', hc', heq⟩
          exact ⟨c', List.mem_cons_of_mem c hc', heq⟩
    · rcases h with ⟨c', hc', heq⟩
      rcases List.mem_cons.mp hc' with rfl | hrest
      · rcases heq with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem c' List.mem_cons_self
      · exact List.mem_cons_of_mem c (List.mem_cons_of_mem _ (ih.mpr ⟨c', hrest, heq⟩))

theorem mem_expandNanSigns_evalFloatNeg (f : IeeeFormat) (x : Nat) (cs : List Nat)
    (hcs : ∀ c, c ∈ cs → c < 2 ^ f.width)
    (hx : x ∈ expandNanSigns f cs) :
    evalFloatNeg f x ∈ expandNanSigns f cs := by
  rcases (mem_expandNanSigns_iff f x cs).mp hx with ⟨c, hc, rfl | rfl⟩
  · exact (mem_expandNanSigns_iff f _ cs).mpr ⟨x, hc, Or.inr rfl⟩
  · rw [evalFloatNeg_involutive f c (hcs c hc)]
    exact (mem_expandNanSigns_iff f _ cs).mpr ⟨c, hc, Or.inl rfl⟩

theorem mem_nanChoicesQuieted_props (dst : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (c : Nat) (hc : c ∈ nanChoicesQuieted dst inputs) :
    c < 2 ^ dst.width ∧ isQuietNaNBits dst c = true ∧ isNaNBits dst c = true := by
  induction inputs with
  | nil => cases hc
  | cons inp rest ih =>
    unfold nanChoicesQuieted at hc
    dsimp only at hc
    cases hnan : isNaNBits inp.1 (inp.2 % 2 ^ inp.1.width) with
    | false =>
      rw [hnan] at hc
      exact ih hc
    | true =>
      rw [hnan] at hc
      rcases List.mem_cons.mp hc with rfl | hrest
      · obtain ⟨neg, q, payload, hdec⟩ := (isNaNBits_eq_true_iff inp.1 _).mp hnan
        have hconv := decodeBits_evalFloatToFloatRoundTiesToEven_of_nan inp.1 dst _ neg q payload hdec
        refine ⟨evalFloatToFloatRoundTiesToEven_lt inp.1 dst _, ?_, ?_⟩
        · unfold isQuietNaNBits; rw [hconv]
        · unfold isNaNBits; rw [hconv]
      · exact ih hrest

theorem mem_nanChoicesSignaling_props (dst : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (c : Nat) (hc : c ∈ nanChoicesSignaling dst inputs) :
    c < 2 ^ dst.width ∧ isSignalingNaNBits dst c = true ∧ isNaNBits dst c = true := by
  induction inputs with
  | nil => cases hc
  | cons inp rest ih =>
    unfold nanChoicesSignaling at hc
    dsimp only at hc
    cases hsnan : isSignalingNaNBits inp.1 (inp.2 % 2 ^ inp.1.width) with
    | false =>
      simp only [hsnan, Bool.false_eq_true, ↓reduceIte] at hc
      exact ih hc
    | true =>
      simp only [hsnan, ↓reduceIte] at hc
      by_cases hlow0 :
          (unpackBits dst (evalFloatToFloatRoundTiesToEven inp.1 dst (inp.2 % 2 ^ inp.1.width))).fraction %
            2 ^ (dst.fractionBits - 1) = 0
      · rw [if_pos' hlow0] at hc
        exact ih hc
      · rw [if_neg' hlow0] at hc
        rcases List.mem_cons.mp hc with rfl | hrest
        · have hE : 2 ^ dst.exponentBits - 1 < 2 ^ dst.exponentBits :=
            Nat.sub_lt (Nat.two_pow_pos _) (by decide)
          have hlowLtHalf :
              (unpackBits dst (evalFloatToFloatRoundTiesToEven inp.1 dst (inp.2 % 2 ^ inp.1.width))).fraction %
                2 ^ (dst.fractionBits - 1) < 2 ^ (dst.fractionBits - 1) :=
            Nat.mod_lt _ (Nat.two_pow_pos _)
          have hhalfLtFull : 2 ^ (dst.fractionBits - 1) < 2 ^ dst.fractionBits :=
            two_pow_lt_two_pow (Nat.sub_lt (IeeeFormat.one_le_fb dst) (by decide))
          have hlowLtFull :
              (unpackBits dst (evalFloatToFloatRoundTiesToEven inp.1 dst (inp.2 % 2 ^ inp.1.width))).fraction %
                2 ^ (dst.fractionBits - 1) < 2 ^ dst.fractionBits :=
            Nat.lt_trans hlowLtHalf hhalfLtFull
          have hdiv0 :
              ((unpackBits dst (evalFloatToFloatRoundTiesToEven inp.1 dst (inp.2 % 2 ^ inp.1.width))).fraction %
                2 ^ (dst.fractionBits - 1)) / 2 ^ (dst.fractionBits - 1) = 0 :=
            Nat.div_eq_of_lt hlowLtHalf
          have hdec := decodeBits_encodeBits dst
            (unpackBits dst (evalFloatToFloatRoundTiesToEven inp.1 dst (inp.2 % 2 ^ inp.1.width))).neg
            (2 ^ dst.exponentBits - 1) _ hE hlowLtFull
          rw [if_pos' rfl, if_neg' hlow0, hdiv0] at hdec
          refine ⟨encodeBits_lt dst _ _ _ hE hlowLtFull, ?_, ?_⟩
          · unfold isSignalingNaNBits; rw [hdec]; rfl
          · unfold isNaNBits; rw [hdec]
        · exact ih hrest

/-- `preferredNaNBits f` belongs to `nanChoices f inputs mode` in both modes. -/
theorem preferredNaNBits_mem_nanChoices (f : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (mode : FloatArithMode) :
    preferredNaNBits f ∈ nanChoices f inputs mode := by
  cases mode with
  | deterministic => exact List.mem_cons_self
  | nondeterministic =>
    unfold nanChoices expandNanSigns
    exact List.mem_cons_self

/-- Every element of `nanChoices f inputs mode` is canonical (`< 2^f.width`) and a NaN. -/
theorem mem_nanChoices_props (f : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (mode : FloatArithMode) (c : Nat) (hc : c ∈ nanChoices f inputs mode) :
    c < 2 ^ f.width ∧ isNaNBits f c = true := by
  cases mode with
  | deterministic =>
    unfold nanChoices at hc
    rcases List.mem_cons.mp hc with rfl | hnil
    · exact ⟨preferredNaNBits_lt f, isNaNBits_preferredNaNBits f⟩
    · cases hnil
  | nondeterministic =>
    unfold nanChoices at hc
    rcases (mem_expandNanSigns_iff f c _).mp hc with ⟨base, hbase, rfl | rfl⟩
    · rcases List.mem_cons.mp hbase with rfl | hrest
      · exact ⟨preferredNaNBits_lt f, isNaNBits_preferredNaNBits f⟩
      · rcases List.mem_append.mp hrest with hq | hs
        · have hp := mem_nanChoicesQuieted_props f inputs c hq
          exact ⟨hp.1, hp.2.2⟩
        · have hp := mem_nanChoicesSignaling_props f inputs c hs
          exact ⟨hp.1, hp.2.2⟩
    · rcases List.mem_cons.mp hbase with rfl | hrest
      · exact ⟨evalFloatNeg_lt f _, by rw [isNaNBits_evalFloatNeg]; exact isNaNBits_preferredNaNBits f⟩
      · rcases List.mem_append.mp hrest with hq | hs
        · have hp := mem_nanChoicesQuieted_props f inputs base hq
          exact ⟨evalFloatNeg_lt f _, by rw [isNaNBits_evalFloatNeg]; exact hp.2.2⟩
        · have hp := mem_nanChoicesSignaling_props f inputs base hs
          exact ⟨evalFloatNeg_lt f _, by rw [isNaNBits_evalFloatNeg]; exact hp.2.2⟩

theorem natListMem_eq_true_iff (x : Nat) (xs : List Nat) :
    natListMem x xs = true ↔ x ∈ xs := by
  induction xs with
  | nil =>
    constructor
    · intro h; cases h
    · intro h; cases h
  | cons y ys ih =>
    unfold natListMem
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases hxy : Nat.beq x y with
      | true =>
        rw [Nat.eq_of_beq_eq_true hxy]
        exact List.mem_cons_self
      | false =>
        rw [hxy, Bool.false_or] at h
        exact List.mem_cons_of_mem y (ih.mp h)
    · rcases List.mem_cons.mp h with rfl | hrest
      · rw [Nat.beq_refl, Bool.true_or]
      · rw [ih.mpr hrest, Bool.or_true]

/-- If no input operand is a signaling NaN, then `nanChoicesSignaling` is empty and
every candidate in `nanChoices f inputs mode` is a quiet NaN satisfying
`isAdmissibleQuietNaN`. -/
theorem nanChoices_all_quiet_of_no_snan (f : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (hNoSnan : ∀ inp, inp ∈ inputs → isSignalingNaNBits inp.1 (inp.2 % 2 ^ inp.1.width) = false) :
    nanChoicesSignaling f inputs = .nil ∧
    ∀ mode c, c ∈ nanChoices f inputs mode →
      isQuietNaNBits f c = true ∧ isAdmissibleQuietNaN f inputs c = true := by
  have hsnan_nil : nanChoicesSignaling f inputs = .nil := by
    induction inputs with
    | nil => rfl
    | cons inp rest ih =>
      unfold nanChoicesSignaling
      dsimp only
      rw [hNoSnan inp List.mem_cons_self]
      exact ih (fun i hi => hNoSnan i (List.mem_cons_of_mem inp hi))
  refine ⟨hsnan_nil, fun mode c hc => ?_⟩
  have hlt := (mem_nanChoices_props f inputs mode c hc).1
  have hmem_nondet : c ∈ nanChoices f inputs .nondeterministic := by
    cases mode with
    | nondeterministic => exact hc
    | deterministic =>
      unfold nanChoices at hc
      rcases List.mem_cons.mp hc with rfl | hnil
      · exact preferredNaNBits_mem_nanChoices f inputs .nondeterministic
      · cases hnil
  have hquiet : isQuietNaNBits f c = true := by
    unfold nanChoices at hmem_nondet
    rw [hsnan_nil, List.append_nil] at hmem_nondet
    rcases (mem_expandNanSigns_iff f c _).mp hmem_nondet with ⟨base, hbase, rfl | rfl⟩
    · rcases List.mem_cons.mp hbase with rfl | hq
      · exact isQuietNaNBits_preferredNaNBits f
      · exact (mem_nanChoicesQuieted_props f inputs c hq).2.1
    · rw [isQuietNaNBits_evalFloatNeg]
      rcases List.mem_cons.mp hbase with rfl | hq
      · exact isQuietNaNBits_preferredNaNBits f
      · exact (mem_nanChoicesQuieted_props f inputs base hq).2.1
  refine ⟨hquiet, ?_⟩
  unfold isAdmissibleQuietNaN
  dsimp only
  rw [Nat.mod_eq_of_lt hlt, hquiet, (natListMem_eq_true_iff c _).mpr hmem_nondet, Bool.and_self]

/-- Concrete `4`-element qNaN vs `6`-element nonzero-payload sNaN `nanChoices` witness. -/
theorem nanChoices_4_qnan_vs_6_snan_witness :
    (nanChoices .binary32 [(.binary32, 0x7FC00001)] .nondeterministic).length = 4 ∧
    (nanChoices .binary32 [(.binary32, 0x7F800001)] .nondeterministic).length = 6 ∧
    isAdmissibleQuietNaN .binary32 [(.binary32, 0x7FC00001)] 0x7FC00001 = true ∧
    isAdmissibleQuietNaN .binary32 [(.binary32, 0x7F800001)] 0x7F800001 = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `sub` vs `add ∘ neg` ordered-list swap witness: negating the second NaN operand
swaps the order of `[+qNaN(1), -qNaN(1)]` vs `[-qNaN(1), +qNaN(1)]` in `nanChoices`
while preserving the exact admissible set. -/
theorem nanChoices_sub_vs_add_neg_order_witness :
    let a := 0x3F800000
    let b := 0x7FC00001
    nanChoices .binary32 [(.binary32, a), (.binary32, b)] .nondeterministic ≠
      nanChoices .binary32 [(.binary32, a), (.binary32, evalFloatNeg .binary32 b)] .nondeterministic ∧
    ∀ x,
      x ∈ nanChoices .binary32 [(.binary32, a), (.binary32, b)] .nondeterministic ↔
        x ∈ nanChoices .binary32 [(.binary32, a), (.binary32, evalFloatNeg .binary32 b)] .nondeterministic := by
  have h1 : nanChoices .binary32 [(.binary32, 0x3F800000), (.binary32, 0x7FC00001)] .nondeterministic =
      [0x7FC00000, 0xFFC00000, 0x7FC00001, 0xFFC00001] := by decide +kernel
  have h2 : nanChoices .binary32 [(.binary32, 0x3F800000), (.binary32, evalFloatNeg .binary32 0x7FC00001)] .nondeterministic =
      [0x7FC00000, 0xFFC00000, 0xFFC00001, 0x7FC00001] := by decide +kernel
  dsimp only
  rw [h1, h2]
  refine ⟨by decide, fun x => ?_⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases List.mem_cons.mp h with rfl | h1
    · exact List.mem_cons_self
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · rcases List.mem_cons.mp h2 with rfl | h3
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        · rcases List.mem_cons.mp h3 with rfl | h4
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
          · cases h4
  · rcases List.mem_cons.mp h with rfl | h1
    · exact List.mem_cons_self
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · rcases List.mem_cons.mp h2 with rfl | h3
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        · rcases List.mem_cons.mp h3 with rfl | h4
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
          · cases h4

/-! ### `FloatArithMode` inclusion & deterministic realization -/

theorem EvalFloatBinOpRel.det_imp_nondet
    (op : BinOp) (f : IeeeFormat) (a b : Nat) (out : ScalarInt)
    (h : EvalFloatBinOpRel .deterministic op f a b out) :
    EvalFloatBinOpRel .nondeterministic op f a b out := by
  unfold EvalFloatBinOpRel at h ⊢
  cases hcmp : evalFloatCmp op f a b with
  | some res => rw [hcmp] at h; exact h
  | none =>
    rw [hcmp] at h
    dsimp only at h ⊢
    cases heval : evalFloatArithBase op f a b with
    | none => rw [heval] at h; exact h
    | some baseBits =>
      rw [heval] at h
      dsimp only at h ⊢
      by_cases hnan : isNaNBits f baseBits = true
      · rw [if_pos' hnan] at h ⊢
        rcases h with ⟨cand, hcand, hout⟩
        unfold nanChoices at hcand
        rcases List.mem_cons.mp hcand with rfl | hnil
        · exact ⟨preferredNaNBits f, preferredNaNBits_mem_nanChoices f _ .nondeterministic, hout⟩
        · cases hnil
      · rw [if_neg' hnan] at h ⊢
        exact h

theorem EvalRvalueFloatRel.det_imp_nondet
    (policy : Ptr2IntTransmutePolicy)
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (res : RvalueEvalResult)
    (h : EvalRvalueFloatRel .deterministic policy locals rv mem localDecls layouts res) :
    EvalRvalueFloatRel .nondeterministic policy locals rv mem localDecls layouts res := by
  unfold EvalRvalueFloatRel at h ⊢
  revert h
  cases rv with
  | binaryOp op lhsOp rhsOp =>
    dsimp only
    have hnon_offset : ∀ (op' : BinOp) (lhs rhs : ScalarInt) (locals₂ : List LocalSlot),
        (match Bool.or (isFloatOptTy (operandTy localDecls layouts lhsOp))
            (isFloatOptTy (operandTy localDecls layouts rhsOp)) with
         | true =>
           match operandTy localDecls layouts lhsOp, operandTy localDecls layouts rhsOp with
           | .some lTy, .some rTy =>
             match ieeeFormatOfTy? lTy, ieeeFormatOfTy? rTy with
             | .some fL, .some fR =>
               match Bool.and
                   (match fL, fR with | .binary32, .binary32 => true | .binary64, .binary64 => true | _, _ => false)
                   (Bool.and (Nat.beq lhs.sizeBytes fL.byteWidth) (Nat.beq rhs.sizeBytes fL.byteWidth)) with
               | true =>
                 match evalFloatBinOp op' fL lhs.bits rhs.bits with
                 | .some _ =>
                   ∃ outSc,
                     EvalFloatBinOpRel .deterministic op' fL lhs.bits rhs.bits outSc ∧
                     res = .ok (.scalar outSc) locals₂ mem
                 | .none => res = .unsupported
               | false => res = .unsupported
             | _, _ => res = .unsupported
           | _, _ => res = .unsupported
         | false => res = evalScalarBinOp op' lhs rhs locals₂ mem (operandIsSigned localDecls lhsOp layouts)) →
        (match Bool.or (isFloatOptTy (operandTy localDecls layouts lhsOp))
            (isFloatOptTy (operandTy localDecls layouts rhsOp)) with
         | true =>
           match operandTy localDecls layouts lhsOp, operandTy localDecls layouts rhsOp with
           | .some lTy, .some rTy =>
             match ieeeFormatOfTy? lTy, ieeeFormatOfTy? rTy with
             | .some fL, .some fR =>
               match Bool.and
                   (match fL, fR with | .binary32, .binary32 => true | .binary64, .binary64 => true | _, _ => false)
                   (Bool.and (Nat.beq lhs.sizeBytes fL.byteWidth) (Nat.beq rhs.sizeBytes fL.byteWidth)) with
               | true =>
                 match evalFloatBinOp op' fL lhs.bits rhs.bits with
                 | .some _ =>
                   ∃ outSc,
                     EvalFloatBinOpRel .nondeterministic op' fL lhs.bits rhs.bits outSc ∧
                     res = .ok (.scalar outSc) locals₂ mem
                 | .none => res = .unsupported
               | false => res = .unsupported
             | _, _ => res = .unsupported
           | _, _ => res = .unsupported
         | false => res = evalScalarBinOp op' lhs rhs locals₂ mem (operandIsSigned localDecls lhsOp layouts)) := by
      intro op' lhs rhs locals₂
      cases Bool.or (isFloatOptTy (operandTy localDecls layouts lhsOp))
          (isFloatOptTy (operandTy localDecls layouts rhsOp)) with
      | false => exact id
      | true =>
        dsimp only
        cases operandTy localDecls layouts lhsOp with
        | none => exact id
        | some lTy =>
          cases operandTy localDecls layouts rhsOp with
          | none => exact id
          | some rTy =>
            dsimp only
            cases ieeeFormatOfTy? lTy with
            | none => exact id
            | some fL =>
              cases ieeeFormatOfTy? rTy with
              | none => exact id
              | some fR =>
                dsimp only
                cases Bool.and
                    (match fL, fR with | .binary32, .binary32 => true | .binary64, .binary64 => true | _, _ => false)
                    (Bool.and (Nat.beq lhs.sizeBytes fL.byteWidth) (Nat.beq rhs.sizeBytes fL.byteWidth)) with
                | false => exact id
                | true =>
                  dsimp only
                  cases evalFloatBinOp op' fL lhs.bits rhs.bits with
                  | none => exact id
                  | some _ =>
                    dsimp only
                    rintro ⟨outSc, hrel, hres⟩
                    exact ⟨outSc, EvalFloatBinOpRel.det_imp_nondet op' fL lhs.bits rhs.bits outSc hrel, hres⟩
    cases evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
    | ub => exact id
    | unsupported => exact id
    | ok lhsVal locals₁ =>
      dsimp only
      cases evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
      | ub => exact id
      | unsupported => exact id
      | ok rhsVal locals₂ =>
        dsimp only
        cases lhsVal with
        | scalar lhs =>
          cases rhsVal with
          | scalar rhs =>
            dsimp only
            cases hop : op with
            | offset => exact id
            | _ => dsimp only; rw [← hop]; exact hnon_offset op lhs rhs locals₂
          | _ => exact id
        | _ => exact id
  | cast kind op targetTy =>
    cases kind with
    | floatToFloat =>
      dsimp only
      cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
      | ub => exact id
      | unsupported => exact id
      | ok v locals' =>
        dsimp only
        cases operandTy localDecls layouts op with
        | none => exact id
        | some srcTy =>
          cases v with
          | scalar sc =>
            dsimp only
            cases ieeeFormatOfTy? srcTy with
            | none => exact id
            | some src =>
              cases ieeeFormatOfTy? targetTy with
              | none => exact id
              | some dst =>
                dsimp only
                cases Nat.beq sc.sizeBytes src.byteWidth with
                | false => exact id
                | true =>
                  dsimp only
                  intro h
                  by_cases hnan : isNaNBits src sc.bits = true
                  · rw [if_pos' hnan] at h ⊢
                    rcases h with ⟨cand, hcand, hres⟩
                    unfold nanChoices at hcand
                    rcases List.mem_cons.mp hcand with rfl | hnil
                    · exact ⟨preferredNaNBits dst, preferredNaNBits_mem_nanChoices dst _ .nondeterministic, hres⟩
                    · cases hnil
                  · rw [if_neg' hnan] at h ⊢
                    exact h
          | _ => exact id
    | _ => exact id
  | _ => exact id

/-- Whenever `evalFloatArithBase op f a b = .some baseBits` and `isNaNBits f baseBits = true`,
`baseBits` is specifically `preferredNaNBits f`. -/
theorem evalFloatArithBase_nan_eq_preferred (op : BinOp) (f : IeeeFormat) (a b baseBits : Nat)
    (heval : evalFloatArithBase op f a b = .some baseBits)
    (hnan : isNaNBits f baseBits = true) :
    baseBits = preferredNaNBits f := by
  have hnot_zero : ∀ s, isNaNBits f (zeroBits f s) = true → False := by
    intro s h; rw [isNaNBits_zeroBits] at h; cases h
  have hnot_inf : ∀ s, isNaNBits f (infBits f s) = true → False := by
    intro s h; rw [isNaNBits_infBits] at h; cases h
  have hnot_round : ∀ s n d, 0 < d → isNaNBits f (roundRatioTiesToEven f s n d) = true → False := by
    intro s n d hd h; rw [isNaNBits_roundRatioTiesToEven f s n d hd] at h; cases h
  have hsum_nan : ∀ (l r : FloatKind),
      (∀ s n d, l = .finite s n d → 0 < d) →
      (∀ s n d, r = .finite s n d → 0 < d) →
      isNaNBits f (exactSumFloat f l r) = true →
      exactSumFloat f l r = preferredNaNBits f := by
    intro l r hld hrd hn
    cases l with
    | nan _ _ _ => rfl
    | zero _ =>
      cases r with
      | zero _ => exact False.elim (hnot_zero _ hn)
      | finite _ _ _ => exact False.elim (hnot_round _ _ _ (hrd _ _ _ rfl) hn)
      | inf _ => exact False.elim (hnot_inf _ hn)
      | nan _ _ _ => rfl
    | finite _ _ _ =>
      cases r with
      | zero _ => exact False.elim (hnot_round _ _ _ (hld _ _ _ rfl) hn)
      | finite _ _ _ =>
        exact False.elim (hnot_round _ _ _ (Nat.mul_pos (hld _ _ _ rfl) (hrd _ _ _ rfl)) hn)
      | inf _ => exact False.elim (hnot_inf _ hn)
      | nan _ _ _ => rfl
    | inf ln =>
      cases r with
      | zero _ => exact False.elim (hnot_inf _ hn)
      | finite _ _ _ => exact False.elim (hnot_inf _ hn)
      | inf rn =>
        unfold exactSumFloat at hn ⊢
        dsimp only at hn ⊢
        cases hxor : Bool.xor ln rn with
        | true => rfl
        | false => rw [hxor] at hn; exact False.elim (hnot_inf _ hn)
      | nan _ _ _ => rfl
  have hld_a : ∀ s n d, decodeBits f (a % 2 ^ f.width) = .finite s n d → 0 < d :=
    fun s n d h => decodeBits_finite_den_pos f _ s n d h
  have hrd_b : ∀ s n d, decodeBits f (b % 2 ^ f.width) = .finite s n d → 0 < d :=
    fun s n d h => decodeBits_finite_den_pos f _ s n d h
  unfold evalFloatArithBase at heval
  cases op <;> simp only at heval
  all_goals try cases heval
  · exact hsum_nan _ _ hld_a hrd_b hnan
  · refine hsum_nan _ _ hld_a ?_ hnan
    intro s n d hneg
    cases hdb : decodeBits f (b % 2 ^ f.width) with
    | finite rn rnum rden =>
      rw [hdb] at hneg; injection hneg with _ _ hd; rw [← hd]
      exact decodeBits_finite_den_pos f _ rn rnum rden hdb
    | _ => rw [hdb] at hneg; cases hneg
  · cases ha : decodeBits f (a % 2 ^ f.width) <;> cases hb : decodeBits f (b % 2 ^ f.width) <;>
      simp only [ha, hb] at hnan ⊢
    all_goals try rfl
    all_goals try exact False.elim (hnot_zero _ hnan)
    all_goals try exact False.elim (hnot_inf _ hnan)
    · exact False.elim (hnot_round _ _ _ (Nat.mul_pos (hld_a _ _ _ ha) (hrd_b _ _ _ hb)) hnan)
    · rename_i ln lnum lden rn
      by_cases h0 : lnum = 0
      · rw [if_pos' h0]
      · rw [if_neg' h0] at hnan; exact False.elim (hnot_inf _ hnan)
    · rename_i ln rn rnum rden
      by_cases h0 : rnum = 0
      · rw [if_pos' h0]
      · rw [if_neg' h0] at hnan; exact False.elim (hnot_inf _ hnan)
  · cases ha : decodeBits f (a % 2 ^ f.width) <;> cases hb : decodeBits f (b % 2 ^ f.width) <;>
      simp only [ha, hb] at hnan ⊢
    all_goals try rfl
    all_goals try exact False.elim (hnot_zero _ hnan)
    all_goals try exact False.elim (hnot_inf _ hnan)
    · rename_i ln rn rnum rden
      by_cases h0 : rnum = 0
      · rw [if_pos' h0]
      · rw [if_neg' h0] at hnan; exact False.elim (hnot_zero _ hnan)
    · rename_i ln lnum lden rn
      by_cases h0 : lnum = 0
      · rw [if_pos' h0]
      · rw [if_neg' h0] at hnan; exact False.elim (hnot_inf _ hnan)
    · rename_i ln lnum lden rn rnum rden
      by_cases hr0 : rnum = 0
      · rw [if_pos' hr0] at hnan ⊢
        by_cases hl0 : lnum = 0
        · rw [if_pos' hl0]
        · rw [if_neg' hl0] at hnan; exact False.elim (hnot_inf _ hnan)
      · rw [if_neg' hr0] at hnan
        exact False.elim (hnot_round _ _ _ (Nat.mul_pos (hld_a _ _ _ ha) (Nat.pos_of_ne_zero hr0)) hnan)
  · cases ha : decodeBits f (a % 2 ^ f.width) <;> cases hb : decodeBits f (b % 2 ^ f.width) <;>
      simp only [ha, hb] at hnan ⊢
    all_goals try rfl
    · rename_i ln rn rnum rden
      by_cases h0 : rnum = 0
      · rw [if_pos' h0]
      · rw [if_neg' h0] at hnan; exact False.elim (hnot_zero _ hnan)
    · unfold isNaNBits at hnan; rw [ha] at hnan; cases hnan
    · rename_i ln lnum lden rn rnum rden
      by_cases hr0 : rnum = 0
      · rw [if_pos' hr0]
      · rw [if_neg' hr0] at hnan
        exact False.elim (hnot_round _ _ _ (Nat.mul_pos (hld_a _ _ _ ha) (hrd_b _ _ _ hb)) hnan)
    · unfold isNaNBits at hnan; rw [ha] at hnan; cases hnan

/-- `evalFloatBinOp` realizes `EvalFloatBinOpRel .deterministic` exactly. -/
theorem evalFloatBinOp_iff_rel_det (op : BinOp) (f : IeeeFormat) (a b : Nat) (out : ScalarInt) :
    evalFloatBinOp op f a b = .some out ↔ EvalFloatBinOpRel .deterministic op f a b out := by
  unfold evalFloatBinOp EvalFloatBinOpRel
  cases evalFloatCmp op f a b with
  | some res =>
    refine ⟨fun h => by injection h with h; exact h.symm, fun h => by rw [h]⟩
  | none =>
    cases heval : evalFloatArithBase op f a b with
    | none =>
      constructor
      · intro h; cases h
      · intro h; exact False.elim h
    | some baseBits =>
      dsimp only
      by_cases hnan : isNaNBits f baseBits = true
      · rw [if_pos' hnan]
        have hpref := evalFloatArithBase_nan_eq_preferred op f a b baseBits heval hnan
        refine ⟨fun h => ?_, fun h => ?_⟩
        · injection h with h
          exact ⟨preferredNaNBits f, List.mem_cons_self, by rw [← h, hpref]⟩
        · rcases h with ⟨cand, hcand, hout⟩
          unfold nanChoices at hcand
          rcases List.mem_cons.mp hcand with rfl | hnil
          · rw [hout, hpref]
          · cases hnil
      · rw [if_neg' hnan]
        refine ⟨fun h => by injection h with h; exact h.symm, fun h => by rw [h]⟩

/-! ### Relational sign symmetry (`rem`, `mul`, `div`, `add`, `sub`) -/

/-- Negating an input in `nanChoices f inputs .nondeterministic` preserves the admissible
NaN set exactly. -/
private theorem mem_nanChoices_nondet_neg_input_aux (dst : IeeeFormat)
    (src : IeeeFormat) (b : Nat) (rest : List (IeeeFormat × Nat)) (x : Nat) :
    x ∈ nanChoices dst ((src, evalFloatNeg src b) :: rest) .nondeterministic ↔
      x ∈ nanChoices dst ((src, b) :: rest) .nondeterministic := by
  have hneg_elem : ∀ (target : IeeeFormat) (s : IeeeFormat) (u : Nat),
      (∀ c, c ∈ nanChoicesQuieted target [(s, evalFloatNeg s u)] ↔
        ∃ c', c' ∈ nanChoicesQuieted target [(s, u)] ∧ c = evalFloatNeg target c') ∧
      (∀ c, c ∈ nanChoicesSignaling target [(s, evalFloatNeg s u)] ↔
        ∃ c', c' ∈ nanChoicesSignaling target [(s, u)] ∧ c = evalFloatNeg target c') := by
    intro target s u
    have hmod_neg : evalFloatNeg s u % 2 ^ s.width = evalFloatNeg s (u % 2 ^ s.width) := by
      rw [Nat.mod_eq_of_lt (evalFloatNeg_lt s u), evalFloatNeg_mod]
    refine ⟨fun c => ?_, fun c => ?_⟩
    · unfold nanChoicesQuieted
      dsimp only
      rw [hmod_neg, isNaNBits_evalFloatNeg, evalFloatToFloatRoundTiesToEven_evalFloatNeg]
      cases isNaNBits s (u % 2 ^ s.width) with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        constructor
        · intro h; cases h
        · intro ⟨_, hc, _⟩; cases hc
      | true =>
        simp only [↓reduceIte]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rcases List.mem_cons.mp h with rfl | hnil
          · exact ⟨_, List.mem_cons_self, rfl⟩
          · cases hnil
        · rcases h with ⟨c', hc', rfl⟩
          rcases List.mem_cons.mp hc' with rfl | hnil
          · exact List.mem_cons_self
          · cases hnil
    · unfold nanChoicesSignaling
      dsimp only
      rw [hmod_neg, isSignalingNaNBits_evalFloatNeg, evalFloatToFloatRoundTiesToEven_evalFloatNeg,
        unpackBits_evalFloatNeg]
      cases isSignalingNaNBits s (u % 2 ^ s.width) with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        constructor
        · intro h; cases h
        · intro ⟨_, hc, _⟩; cases hc
      | true =>
        simp only [↓reduceIte]
        by_cases hlow0 :
            (unpackBits target (evalFloatToFloatRoundTiesToEven s target (u % 2 ^ s.width))).fraction %
              2 ^ (target.fractionBits - 1) = 0
        · rw [if_pos' hlow0, if_pos' hlow0]
          constructor
          · intro h; cases h
          · intro ⟨_, hc, _⟩; cases hc
        · rw [if_neg' hlow0, if_neg' hlow0]
          have hE : 2 ^ target.exponentBits - 1 < 2 ^ target.exponentBits :=
            Nat.sub_lt (Nat.two_pow_pos _) (by decide)
          have hF :
              (unpackBits target (evalFloatToFloatRoundTiesToEven s target (u % 2 ^ s.width))).fraction %
                2 ^ (target.fractionBits - 1) < 2 ^ target.fractionBits :=
            Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos _))
              (two_pow_lt_two_pow (Nat.sub_lt (IeeeFormat.one_le_fb target) (by decide)))
          have heq := evalFloatNeg_encodeBits target
            (unpackBits target (evalFloatToFloatRoundTiesToEven s target (u % 2 ^ s.width))).neg
            (2 ^ target.exponentBits - 1) _ hE hF
          refine ⟨fun h => ?_, fun h => ?_⟩
          · rcases List.mem_cons.mp h with rfl | hnil
            · exact ⟨_, List.mem_cons_self, heq.symm⟩
            · cases hnil
          · rcases h with ⟨c', hc', rfl⟩
            rcases List.mem_cons.mp hc' with rfl | hnil
            · rw [heq]; exact List.mem_cons_self
            · cases hnil
  have hq_split : ∀ (inp : IeeeFormat × Nat) (l : List (IeeeFormat × Nat)),
      nanChoicesQuieted dst (inp :: l) =
        nanChoicesQuieted dst [inp] ++ nanChoicesQuieted dst l := by
    intro inp l
    change (if isNaNBits inp.1 (inp.2 % 2 ^ inp.1.width) then
        evalFloatToFloatRoundTiesToEven inp.1 dst (inp.2 % 2 ^ inp.1.width) :: nanChoicesQuieted dst l
      else nanChoicesQuieted dst l) =
      (if isNaNBits inp.1 (inp.2 % 2 ^ inp.1.width) then
        [evalFloatToFloatRoundTiesToEven inp.1 dst (inp.2 % 2 ^ inp.1.width)]
      else []) ++ nanChoicesQuieted dst l
    cases isNaNBits inp.1 (inp.2 % 2 ^ inp.1.width) <;> rfl
  have hs_split : ∀ (inp : IeeeFormat × Nat) (l : List (IeeeFormat × Nat)),
      nanChoicesSignaling dst (inp :: l) =
        nanChoicesSignaling dst [inp] ++ nanChoicesSignaling dst l := by
    intro inp l
    change (if isSignalingNaNBits inp.1 (inp.2 % 2 ^ inp.1.width) then
        if (unpackBits dst (evalFloatToFloatRoundTiesToEven inp.1 dst (inp.2 % 2 ^ inp.1.width))).fraction %
            2 ^ (dst.fractionBits - 1) = 0 then
          nanChoicesSignaling dst l
        else
          encodeBits dst (unpackBits dst (evalFloatToFloatRoundTiesToEven inp.1 dst (inp.2 % 2 ^ inp.1.width))).neg
              (2 ^ dst.exponentBits - 1)
              ((unpackBits dst (evalFloatToFloatRoundTiesToEven inp.1 dst (inp.2 % 2 ^ inp.1.width))).fraction %
                2 ^ (dst.fractionBits - 1)) :: nanChoicesSignaling dst l
      else nanChoicesSignaling dst l) =
      (if isSignalingNaNBits inp.1 (inp.2 % 2 ^ inp.1.width) then
        if (unpackBits dst (evalFloatToFloatRoundTiesToEven inp.1 dst (inp.2 % 2 ^ inp.1.width))).fraction %
            2 ^ (dst.fractionBits - 1) = 0 then []
        else
          [encodeBits dst (unpackBits dst (evalFloatToFloatRoundTiesToEven inp.1 dst (inp.2 % 2 ^ inp.1.width))).neg
              (2 ^ dst.exponentBits - 1)
              ((unpackBits dst (evalFloatToFloatRoundTiesToEven inp.1 dst (inp.2 % 2 ^ inp.1.width))).fraction %
                2 ^ (dst.fractionBits - 1))]
      else []) ++ nanChoicesSignaling dst l
    cases isSignalingNaNBits inp.1 (inp.2 % 2 ^ inp.1.width) with
    | false => rfl
    | true =>
      simp only [↓reduceIte]
      by_cases hlow0 :
          (unpackBits dst (evalFloatToFloatRoundTiesToEven inp.1 dst (inp.2 % 2 ^ inp.1.width))).fraction %
            2 ^ (dst.fractionBits - 1) = 0
      · rw [if_pos' hlow0, if_pos' hlow0]; rfl
      · rw [if_neg' hlow0, if_neg' hlow0]; rfl
  have hpair := hneg_elem dst src b
  have hlt_q : ∀ c, c ∈ nanChoicesQuieted dst [(src, b)] → c < 2 ^ dst.width :=
    fun c hc => (mem_nanChoicesQuieted_props dst _ c hc).1
  have hlt_s : ∀ c, c ∈ nanChoicesSignaling dst [(src, b)] → c < 2 ^ dst.width :=
    fun c hc => (mem_nanChoicesSignaling_props dst _ c hc).1
  unfold nanChoices
  rw [mem_expandNanSigns_iff, mem_expandNanSigns_iff,
    hq_split (src, evalFloatNeg src b) rest, hq_split (src, b) rest,
    hs_split (src, evalFloatNeg src b) rest, hs_split (src, b) rest]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨c, hc, hxeq⟩
    rcases List.mem_cons.mp hc with rfl | hrest
    · exact ⟨preferredNaNBits dst, List.mem_cons_self, hxeq⟩
    · rcases List.mem_append.mp hrest with hq | hs
      · rcases List.mem_append.mp hq with hq1 | hq2
        · rcases (hpair.1 c).mp hq1 with ⟨c', hc', rfl⟩
          refine ⟨c', List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hc')))), ?_⟩
          rcases hxeq with rfl | rfl
          · exact Or.inr rfl
          · exact Or.inl (evalFloatNeg_involutive dst c' (hlt_q c' hc'))
        · exact ⟨c, List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hq2)))), hxeq⟩
      · rcases List.mem_append.mp hs with hs1 | hs2
        · rcases (hpair.2 c).mp hs1 with ⟨c', hc', rfl⟩
          refine ⟨c', List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hc')))), ?_⟩
          rcases hxeq with rfl | rfl
          · exact Or.inr rfl
          · exact Or.inl (evalFloatNeg_involutive dst c' (hlt_s c' hc'))
        · exact ⟨c, List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hs2)))), hxeq⟩
  · rcases h with ⟨c, hc, hxeq⟩
    rcases List.mem_cons.mp hc with rfl | hrest
    · exact ⟨preferredNaNBits dst, List.mem_cons_self, hxeq⟩
    · rcases List.mem_append.mp hrest with hq | hs
      · rcases List.mem_append.mp hq with hq1 | hq2
        · have hmem' : evalFloatNeg dst c ∈ nanChoicesQuieted dst [(src, evalFloatNeg src b)] :=
            (hpair.1 _).mpr ⟨c, hq1, rfl⟩
          refine ⟨evalFloatNeg dst c, List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hmem')))), ?_⟩
          rcases hxeq with rfl | rfl
          · exact Or.inr (evalFloatNeg_involutive dst x (hlt_q x hq1)).symm
          · exact Or.inl rfl
        · exact ⟨c, List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hq2)))), hxeq⟩
      · rcases List.mem_append.mp hs with hs1 | hs2
        · have hmem' : evalFloatNeg dst c ∈ nanChoicesSignaling dst [(src, evalFloatNeg src b)] :=
            (hpair.2 _).mpr ⟨c, hs1, rfl⟩
          refine ⟨evalFloatNeg dst c, List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hmem')))), ?_⟩
          rcases hxeq with rfl | rfl
          · exact Or.inr (evalFloatNeg_involutive dst x (hlt_s x hs1)).symm
          · exact Or.inl rfl
        · exact ⟨c, List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hs2)))), hxeq⟩

private theorem mem_nanChoices_nondet_swap (f : IeeeFormat) (a b x : Nat) :
    x ∈ nanChoices f [(f, a), (f, b)] .nondeterministic ↔
      x ∈ nanChoices f [(f, b), (f, a)] .nondeterministic := by
  have hmem2 : ∀ (u v c : Nat), c ∈ [u, v] ↔ c ∈ [v, u] := by
    intro u v c
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases List.mem_cons.mp h with rfl | h1
      · exact List.mem_cons_of_mem v List.mem_cons_self
      · rcases List.mem_cons.mp h1 with rfl | h2
        · exact List.mem_cons_self
        · cases h2
    · rcases List.mem_cons.mp h with rfl | h1
      · exact List.mem_cons_of_mem u List.mem_cons_self
      · rcases List.mem_cons.mp h1 with rfl | h2
        · exact List.mem_cons_self
        · cases h2
  have hq : ∀ c, c ∈ nanChoicesQuieted f [(f, a), (f, b)] ↔ c ∈ nanChoicesQuieted f [(f, b), (f, a)] := by
    intro c
    simp only [nanChoicesQuieted]
    cases isNaNBits f (a % 2 ^ f.width) <;> cases isNaNBits f (b % 2 ^ f.width)
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [↓reduceIte]; exact hmem2 _ _ c
  have hs : ∀ c, c ∈ nanChoicesSignaling f [(f, a), (f, b)] ↔ c ∈ nanChoicesSignaling f [(f, b), (f, a)] := by
    intro c
    simp only [nanChoicesSignaling]
    cases isSignalingNaNBits f (a % 2 ^ f.width) <;> cases isSignalingNaNBits f (b % 2 ^ f.width)
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [↓reduceIte]
      by_cases ha0 :
          (unpackBits f (evalFloatToFloatRoundTiesToEven f f (a % 2 ^ f.width))).fraction %
            2 ^ (f.fractionBits - 1) = 0 <;>
      by_cases hb0 :
          (unpackBits f (evalFloatToFloatRoundTiesToEven f f (b % 2 ^ f.width))).fraction %
            2 ^ (f.fractionBits - 1) = 0
      · simp only [if_pos' ha0, if_pos' hb0]
      · simp only [if_pos' ha0, if_neg' hb0]
      · simp only [if_neg' ha0, if_pos' hb0]
      · simp only [if_neg' ha0, if_neg' hb0]; exact hmem2 _ _ c
  unfold nanChoices
  rw [mem_expandNanSigns_iff, mem_expandNanSigns_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨c, hc, hx⟩
    refine ⟨c, ?_, hx⟩
    rcases List.mem_cons.mp hc with rfl | hr
    · exact List.mem_cons_self
    · rcases List.mem_append.mp hr with h1 | h2
      · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl ((hq c).mp h1)))
      · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr ((hs c).mp h2)))
  · rcases h with ⟨c, hc, hx⟩
    refine ⟨c, ?_, hx⟩
    rcases List.mem_cons.mp hc with rfl | hr
    · exact List.mem_cons_self
    · rcases List.mem_append.mp hr with h1 | h2
      · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl ((hq c).mpr h1)))
      · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr ((hs c).mpr h2)))

theorem mem_nanChoices_nondet_neg_left (f : IeeeFormat) (a b x : Nat) :
    x ∈ nanChoices f [(f, evalFloatNeg f a), (f, b)] .nondeterministic ↔
      x ∈ nanChoices f [(f, a), (f, b)] .nondeterministic :=
  mem_nanChoices_nondet_neg_input_aux f f a [(f, b)] x

theorem mem_nanChoices_nondet_neg_right (f : IeeeFormat) (a b x : Nat) :
    x ∈ nanChoices f [(f, a), (f, evalFloatNeg f b)] .nondeterministic ↔
      x ∈ nanChoices f [(f, a), (f, b)] .nondeterministic := by
  calc x ∈ nanChoices f [(f, a), (f, evalFloatNeg f b)] .nondeterministic
    _ ↔ x ∈ nanChoices f [(f, evalFloatNeg f b), (f, a)] .nondeterministic :=
      mem_nanChoices_nondet_swap f a (evalFloatNeg f b) x
    _ ↔ x ∈ nanChoices f [(f, b), (f, a)] .nondeterministic :=
      mem_nanChoices_nondet_neg_left f b a x
    _ ↔ x ∈ nanChoices f [(f, a), (f, b)] .nondeterministic :=
      mem_nanChoices_nondet_swap f b a x

theorem mem_nanChoices_nondet_evalFloatNeg (f : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (x : Nat) (hx : x ∈ nanChoices f inputs .nondeterministic) :
    evalFloatNeg f x ∈ nanChoices f inputs .nondeterministic := by
  unfold nanChoices at hx ⊢
  apply mem_expandNanSigns_evalFloatNeg f x _ _ hx
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hr
  · exact preferredNaNBits_lt f
  · rcases List.mem_append.mp hr with hq | hs
    · exact (mem_nanChoicesQuieted_props f inputs c hq).1
    · exact (mem_nanChoicesSignaling_props f inputs c hs).1

theorem evalFloatArithBase_rem_neg_right (f : IeeeFormat) (a b : Nat) :
    evalFloatArithBase .rem f a (evalFloatNeg f b) = evalFloatArithBase .rem f a b := by
  unfold evalFloatArithBase
  dsimp only
  simp only [decodeBits_mod, decodeBits_evalFloatNeg]
  cases decodeBits f a <;> cases decodeBits f b <;> rfl

/-- Right-negation invariance of `rem` holds in BOTH `.deterministic` and
`.nondeterministic` modes (`a % (-b) = a % b`). -/
theorem EvalFloatBinOpRel.rem_neg_right (mode : FloatArithMode) (f : IeeeFormat)
    (a b : Nat) (out : ScalarInt) :
    EvalFloatBinOpRel mode .rem f a (evalFloatNeg f b) out ↔
      EvalFloatBinOpRel mode .rem f a b out := by
  unfold EvalFloatBinOpRel
  have hcmp1 : evalFloatCmp .rem f a (evalFloatNeg f b) = .none := rfl
  have hcmp2 : evalFloatCmp .rem f a b = .none := rfl
  rw [hcmp1, hcmp2, evalFloatArithBase_rem_neg_right]
  dsimp only
  cases evalFloatArithBase .rem f a b with
  | none => exact Iff.rfl
  | some baseBits =>
    dsimp only
    by_cases hnan : isNaNBits f baseBits = true
    · rw [if_pos' hnan, if_pos' hnan]
      cases mode with
      | deterministic => exact Iff.rfl
      | nondeterministic =>
        have hmod_neg : evalFloatNeg f b % 2 ^ f.width = evalFloatNeg f (b % 2 ^ f.width) := by
          rw [Nat.mod_eq_of_lt (evalFloatNeg_lt f b), evalFloatNeg_mod]
        rw [hmod_neg]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rcases h with ⟨cand, hcand, hout⟩
          exact ⟨cand, (mem_nanChoices_nondet_neg_right f _ _ cand).mp hcand, hout⟩
        · rcases h with ⟨cand, hcand, hout⟩
          exact ⟨cand, (mem_nanChoices_nondet_neg_right f _ _ cand).mpr hcand, hout⟩
    · rw [if_neg' hnan, if_neg' hnan]

/-- `.deterministic` sign-symmetry counterexample: `(+0.0) * (+Inf)` and `(-0.0) * (+Inf)`
both deterministically return `+preferredNaNBits f`, breaking `(-a) * b = -(a * b)` on NaN. -/
theorem EvalFloatBinOpRel.det_mul_zero_inf_sign_symmetry_counterexample (f : IeeeFormat) :
    evalFloatBinOp .mul f (zeroBits f false) (infBits f false) =
      .some ⟨preferredNaNBits f, f.byteWidth⟩ ∧
    evalFloatBinOp .mul f (evalFloatNeg f (zeroBits f false)) (infBits f false) =
      .some ⟨preferredNaNBits f, f.byteWidth⟩ ∧
    preferredNaNBits f ≠ evalFloatNeg f (preferredNaNBits f) := by
  refine ⟨?_, ?_, (evalFloatNeg_ne_self f (preferredNaNBits f) (preferredNaNBits_lt f)).symm⟩
  · cases f <;> rfl
  · cases f <;> rfl

/-- Helper: negating the left operand of `mul`/`div`/`rem` either keeps a NaN outcome
as `preferredNaNBits f` or flips the sign bit of the non-NaN output. -/
private theorem evalFloatArithBase_mul_div_rem_neg_left
    (op : BinOp) (hop : op = .mul ∨ op = .div ∨ op = .rem)
    (f : IeeeFormat) (a b : Nat) :
    ∃ base base',
      evalFloatArithBase op f a b = .some base ∧
      evalFloatArithBase op f (evalFloatNeg f a) b = .some base' ∧
      isNaNBits f base' = isNaNBits f base ∧
      (isNaNBits f base = false → base' = evalFloatNeg f base) := by
  have haMod : evalFloatNeg f a % 2 ^ f.width = evalFloatNeg f a :=
    Nat.mod_eq_of_lt (evalFloatNeg_lt f a)
  rcases hop with rfl | rfl | rfl
  · unfold evalFloatArithBase
    dsimp only
    rw [haMod, decodeBits_evalFloatNeg, decodeBits_mod, decodeBits_mod]
    cases ha : decodeBits f a <;> cases hb : decodeBits f b <;> simp only [negateFloatKind]
    · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_zeroBits, isNaNBits_zeroBits], fun _ => ?_⟩
      rw [bool_xor_not_left, evalFloatNeg_zeroBits]
    · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_zeroBits, isNaNBits_zeroBits], fun _ => ?_⟩
      rw [bool_xor_not_left, evalFloatNeg_zeroBits]
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_zeroBits, isNaNBits_zeroBits], fun _ => ?_⟩
      rw [bool_xor_not_left, evalFloatNeg_zeroBits]
    · rename_i ln lnum lden rn rnum rden
      have hd : 0 < lden * rden :=
        Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden ha)
          (decodeBits_finite_den_pos f b rn rnum rden hb)
      refine ⟨_, _, rfl, rfl,
        by rw [isNaNBits_roundRatioTiesToEven f _ _ _ hd, isNaNBits_roundRatioTiesToEven f _ _ _ hd],
        fun _ => ?_⟩
      rw [bool_xor_not_left, roundRatioTiesToEven_neg f _ _ _ hd]
    · rename_i ln lnum lden rn
      have hlpos := decodeBits_finite_num_pos f a ln lnum lden ha
      refine ⟨_, _, rfl, rfl, ?_, ?_⟩
      · simp only [if_neg' (by omega : ¬ lnum = 0), isNaNBits_infBits]
      · intro _; simp only [if_neg' (by omega : ¬ lnum = 0), bool_xor_not_left, evalFloatNeg_infBits]
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · rename_i ln rn rnum rden
      have hrpos := decodeBits_finite_num_pos f b rn rnum rden hb
      refine ⟨_, _, rfl, rfl, ?_, ?_⟩
      · simp only [if_neg' (by omega : ¬ rnum = 0), isNaNBits_infBits]
      · intro _; simp only [if_neg' (by omega : ¬ rnum = 0), bool_xor_not_left, evalFloatNeg_infBits]
    · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_infBits, isNaNBits_infBits], fun _ => ?_⟩
      rw [bool_xor_not_left, evalFloatNeg_infBits]
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
  · unfold evalFloatArithBase
    dsimp only
    rw [haMod, decodeBits_evalFloatNeg, decodeBits_mod, decodeBits_mod]
    cases ha : decodeBits f a <;> cases hb : decodeBits f b <;> simp only [negateFloatKind]
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · rename_i ln rn rnum rden
      have hrpos := decodeBits_finite_num_pos f b rn rnum rden hb
      refine ⟨_, _, rfl, rfl, ?_, ?_⟩
      · simp only [if_neg' (by omega : ¬ rnum = 0), isNaNBits_zeroBits]
      · intro _; simp only [if_neg' (by omega : ¬ rnum = 0), bool_xor_not_left, evalFloatNeg_zeroBits]
    · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_zeroBits, isNaNBits_zeroBits], fun _ => ?_⟩
      rw [bool_xor_not_left, evalFloatNeg_zeroBits]
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · rename_i ln lnum lden rn
      have hlpos := decodeBits_finite_num_pos f a ln lnum lden ha
      refine ⟨_, _, rfl, rfl, ?_, ?_⟩
      · simp only [if_neg' (by omega : ¬ lnum = 0), isNaNBits_infBits]
      · intro _; simp only [if_neg' (by omega : ¬ lnum = 0), bool_xor_not_left, evalFloatNeg_infBits]
    · rename_i ln lnum lden rn rnum rden
      have hrpos := decodeBits_finite_num_pos f b rn rnum rden hb
      have hd : 0 < lden * rnum := Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden ha) hrpos
      refine ⟨_, _, rfl, rfl, ?_, ?_⟩
      · simp only [if_neg' (by omega : ¬ rnum = 0),
          isNaNBits_roundRatioTiesToEven f _ _ _ hd]
      · intro _
        simp only [if_neg' (by omega : ¬ rnum = 0), bool_xor_not_left,
          roundRatioTiesToEven_neg f _ _ _ hd]
    · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_zeroBits, isNaNBits_zeroBits], fun _ => ?_⟩
      rw [bool_xor_not_left, evalFloatNeg_zeroBits]
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_infBits, isNaNBits_infBits], fun _ => ?_⟩
      rw [bool_xor_not_left, evalFloatNeg_infBits]
    · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_infBits, isNaNBits_infBits], fun _ => ?_⟩
      rw [bool_xor_not_left, evalFloatNeg_infBits]
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
  · unfold evalFloatArithBase
    dsimp only
    rw [haMod, decodeBits_evalFloatNeg, decodeBits_mod, decodeBits_mod]
    cases ha : decodeBits f a <;> cases hb : decodeBits f b <;> simp only [negateFloatKind]
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · rename_i ln rn rnum rden
      have hrpos := decodeBits_finite_num_pos f b rn rnum rden hb
      refine ⟨_, _, rfl, rfl, ?_, ?_⟩
      · simp only [if_neg' (by omega : ¬ rnum = 0), isNaNBits_zeroBits]
      · intro _; simp only [if_neg' (by omega : ¬ rnum = 0), evalFloatNeg_zeroBits]
    · refine ⟨_, _, rfl, rfl, ?_, fun _ => (evalFloatNeg_mod f a).symm⟩
      rw [isNaNBits_evalFloatNeg]; unfold isNaNBits; rw [decodeBits_mod]
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · rename_i ln lnum lden rn rnum rden
      have hrpos := decodeBits_finite_num_pos f b rn rnum rden hb
      have hd : 0 < lden * rden :=
        Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden ha)
          (decodeBits_finite_den_pos f b rn rnum rden hb)
      refine ⟨_, _, rfl, rfl, ?_, ?_⟩
      · simp only [if_neg' (by omega : ¬ rnum = 0),
          isNaNBits_roundRatioTiesToEven f _ _ _ hd]
      · intro _
        simp only [if_neg' (by omega : ¬ rnum = 0),
          roundRatioTiesToEven_neg f _ _ _ hd]
    · refine ⟨_, _, rfl, rfl, ?_, fun _ => (evalFloatNeg_mod f a).symm⟩
      rw [isNaNBits_evalFloatNeg]; unfold isNaNBits; rw [decodeBits_mod]
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩

private theorem evalFloatArithBase_mul_div_neg_right
    (op : BinOp) (hop : op = .mul ∨ op = .div)
    (f : IeeeFormat) (a b : Nat) :
    ∃ base base',
      evalFloatArithBase op f a b = .some base ∧
      evalFloatArithBase op f a (evalFloatNeg f b) = .some base' ∧
      isNaNBits f base' = isNaNBits f base ∧
      (isNaNBits f base = false → base' = evalFloatNeg f base) := by
  have hbMod : evalFloatNeg f b % 2 ^ f.width = evalFloatNeg f b :=
    Nat.mod_eq_of_lt (evalFloatNeg_lt f b)
  rcases hop with rfl | rfl
  · unfold evalFloatArithBase
    dsimp only
    rw [hbMod, decodeBits_evalFloatNeg, decodeBits_mod, decodeBits_mod]
    cases ha : decodeBits f a <;> cases hb : decodeBits f b <;> simp only [negateFloatKind]
    · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_zeroBits, isNaNBits_zeroBits], fun _ => ?_⟩
      rw [bool_xor_not_right, evalFloatNeg_zeroBits]
    · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_zeroBits, isNaNBits_zeroBits], fun _ => ?_⟩
      rw [bool_xor_not_right, evalFloatNeg_zeroBits]
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_zeroBits, isNaNBits_zeroBits], fun _ => ?_⟩
      rw [bool_xor_not_right, evalFloatNeg_zeroBits]
    · rename_i ln lnum lden rn rnum rden
      have hd : 0 < lden * rden :=
        Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden ha)
          (decodeBits_finite_den_pos f b rn rnum rden hb)
      refine ⟨_, _, rfl, rfl,
        by rw [isNaNBits_roundRatioTiesToEven f _ _ _ hd, isNaNBits_roundRatioTiesToEven f _ _ _ hd],
        fun _ => ?_⟩
      rw [bool_xor_not_right, roundRatioTiesToEven_neg f _ _ _ hd]
    · rename_i ln lnum lden rn
      have hlpos := decodeBits_finite_num_pos f a ln lnum lden ha
      refine ⟨_, _, rfl, rfl, ?_, ?_⟩
      · simp only [if_neg' (by omega : ¬ lnum = 0), isNaNBits_infBits]
      · intro _; simp only [if_neg' (by omega : ¬ lnum = 0), bool_xor_not_right, evalFloatNeg_infBits]
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · rename_i ln rn rnum rden
      have hrpos := decodeBits_finite_num_pos f b rn rnum rden hb
      refine ⟨_, _, rfl, rfl, ?_, ?_⟩
      · simp only [if_neg' (by omega : ¬ rnum = 0), isNaNBits_infBits]
      · intro _; simp only [if_neg' (by omega : ¬ rnum = 0), bool_xor_not_right, evalFloatNeg_infBits]
    · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_infBits, isNaNBits_infBits], fun _ => ?_⟩
      rw [bool_xor_not_right, evalFloatNeg_infBits]
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
  · unfold evalFloatArithBase
    dsimp only
    rw [hbMod, decodeBits_evalFloatNeg, decodeBits_mod, decodeBits_mod]
    cases ha : decodeBits f a <;> cases hb : decodeBits f b <;> simp only [negateFloatKind]
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · rename_i ln rn rnum rden
      have hrpos := decodeBits_finite_num_pos f b rn rnum rden hb
      refine ⟨_, _, rfl, rfl, ?_, ?_⟩
      · simp only [if_neg' (by omega : ¬ rnum = 0), isNaNBits_zeroBits]
      · intro _; simp only [if_neg' (by omega : ¬ rnum = 0), bool_xor_not_right, evalFloatNeg_zeroBits]
    · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_zeroBits, isNaNBits_zeroBits], fun _ => ?_⟩
      rw [bool_xor_not_right, evalFloatNeg_zeroBits]
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · rename_i ln lnum lden rn
      have hlpos := decodeBits_finite_num_pos f a ln lnum lden ha
      refine ⟨_, _, rfl, rfl, ?_, ?_⟩
      · simp only [if_neg' (by omega : ¬ lnum = 0), isNaNBits_infBits]
      · intro _; simp only [if_neg' (by omega : ¬ lnum = 0), bool_xor_not_right, evalFloatNeg_infBits]
    · rename_i ln lnum lden rn rnum rden
      have hrpos := decodeBits_finite_num_pos f b rn rnum rden hb
      have hd : 0 < lden * rnum := Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden ha) hrpos
      refine ⟨_, _, rfl, rfl, ?_, ?_⟩
      · simp only [if_neg' (by omega : ¬ rnum = 0),
          isNaNBits_roundRatioTiesToEven f _ _ _ hd]
      · intro _
        simp only [if_neg' (by omega : ¬ rnum = 0), bool_xor_not_right,
          roundRatioTiesToEven_neg f _ _ _ hd]
    · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_zeroBits, isNaNBits_zeroBits], fun _ => ?_⟩
      rw [bool_xor_not_right, evalFloatNeg_zeroBits]
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_infBits, isNaNBits_infBits], fun _ => ?_⟩
      rw [bool_xor_not_right, evalFloatNeg_infBits]
    · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_infBits, isNaNBits_infBits], fun _ => ?_⟩
      rw [bool_xor_not_right, evalFloatNeg_infBits]
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩

private theorem evalFloatArithBase_lt (op : BinOp) (f : IeeeFormat) (a b bits : Nat)
    (h : evalFloatArithBase op f a b = .some bits) : bits < 2 ^ f.width := by
  have hsum_lt : ∀ (l r : FloatKind),
      (∀ s n d, l = .finite s n d → 0 < d) →
      (∀ s n d, r = .finite s n d → 0 < d) →
      exactSumFloat f l r < 2 ^ f.width := by
    intro l r hld hrd
    cases l <;> cases r <;> (unfold exactSumFloat; dsimp only)
    · exact zeroBits_lt f _
    · exact roundRatioTiesToEven_lt f _ _ _ (hrd _ _ _ rfl)
    · exact infBits_lt f _
    · exact preferredNaNBits_lt f
    · exact roundRatioTiesToEven_lt f _ _ _ (hld _ _ _ rfl)
    · exact roundRatioTiesToEven_lt f _ _ _ (Nat.mul_pos (hld _ _ _ rfl) (hrd _ _ _ rfl))
    · exact infBits_lt f _
    · exact preferredNaNBits_lt f
    · exact infBits_lt f _
    · exact infBits_lt f _
    · rename_i ln rn
      cases Bool.xor ln rn with
      | true => exact preferredNaNBits_lt f
      | false => exact infBits_lt f ln
    · exact preferredNaNBits_lt f
    · exact preferredNaNBits_lt f
    · exact preferredNaNBits_lt f
    · exact preferredNaNBits_lt f
    · exact preferredNaNBits_lt f
  have hld_a : ∀ s n d, decodeBits f (a % 2 ^ f.width) = .finite s n d → 0 < d :=
    fun s n d hd => decodeBits_finite_den_pos f _ s n d hd
  have hrd_b : ∀ s n d, decodeBits f (b % 2 ^ f.width) = .finite s n d → 0 < d :=
    fun s n d hd => decodeBits_finite_den_pos f _ s n d hd
  unfold evalFloatArithBase at h
  cases op <;> simp only at h
  all_goals try cases h
  · exact hsum_lt _ _ hld_a hrd_b
  · refine hsum_lt _ _ hld_a ?_
    intro s n d hneg
    cases hdb : decodeBits f (b % 2 ^ f.width) with
    | finite rn rnum rden =>
      rw [hdb] at hneg; injection hneg with _ _ hd; rw [← hd]; exact hrd_b _ _ _ hdb
    | _ => rw [hdb] at hneg; cases hneg
  · cases ha : decodeBits f (a % 2 ^ f.width) <;> cases hb : decodeBits f (b % 2 ^ f.width) <;>
      dsimp only
    all_goals try exact preferredNaNBits_lt f
    all_goals try exact zeroBits_lt f _
    all_goals try exact infBits_lt f _
    · exact roundRatioTiesToEven_lt f _ _ _ (Nat.mul_pos (hld_a _ _ _ ha) (hrd_b _ _ _ hb))
    · split
      · exact preferredNaNBits_lt f
      · exact infBits_lt f _
    · split
      · exact preferredNaNBits_lt f
      · exact infBits_lt f _
  · cases ha : decodeBits f (a % 2 ^ f.width) <;> cases hb : decodeBits f (b % 2 ^ f.width) <;>
      dsimp only
    all_goals try exact preferredNaNBits_lt f
    all_goals try exact zeroBits_lt f _
    all_goals try exact infBits_lt f _
    · split
      · exact preferredNaNBits_lt f
      · exact zeroBits_lt f _
    · split
      · exact preferredNaNBits_lt f
      · exact infBits_lt f _
    · rename_i ln lnum lden rn rnum rden
      by_cases hr0 : rnum = 0
      · rw [if_pos' hr0]
        split
        · exact preferredNaNBits_lt f
        · exact infBits_lt f _
      · rw [if_neg' hr0]
        exact roundRatioTiesToEven_lt f _ _ _ (Nat.mul_pos (hld_a _ _ _ ha) (Nat.pos_of_ne_zero hr0))
  · cases ha : decodeBits f (a % 2 ^ f.width) <;> cases hb : decodeBits f (b % 2 ^ f.width) <;>
      dsimp only
    all_goals try exact preferredNaNBits_lt f
    · split
      · exact preferredNaNBits_lt f
      · exact zeroBits_lt f _
    · exact Nat.mod_lt a (Nat.two_pow_pos f.width)
    · split
      · exact preferredNaNBits_lt f
      · exact roundRatioTiesToEven_lt f _ _ _ (Nat.mul_pos (hld_a _ _ _ ha) (hrd_b _ _ _ hb))
    · exact Nat.mod_lt a (Nat.two_pow_pos f.width)

/-- **Unconditional `.nondeterministic` left sign-symmetry for `mul`, `div`, `rem`**:
for ALL `a b : Nat` and EVERY canonical `outBits < 2^f.width` (including every finite,
zero, infinite, and NaN outcome), `(-a) op b` admits `-outBits` iff `a op b` admits
`outBits`. -/
theorem EvalFloatBinOpRel.nondet_mul_div_rem_neg_left
    (op : BinOp) (hop : op = .mul ∨ op = .div ∨ op = .rem)
    (f : IeeeFormat) (a b outBits : Nat) (houtLt : outBits < 2 ^ f.width) :
    EvalFloatBinOpRel .nondeterministic op f (evalFloatNeg f a) b
        ⟨evalFloatNeg f outBits, f.byteWidth⟩ ↔
      EvalFloatBinOpRel .nondeterministic op f a b ⟨outBits, f.byteWidth⟩ := by
  have hcmp : ∀ x y, evalFloatCmp op f x y = .none := by
    intro x y; rcases hop with rfl | rfl | rfl <;> rfl
  obtain ⟨base, base', hbase, hbase', hnan_eq, hnonnan⟩ :=
    evalFloatArithBase_mul_div_rem_neg_left op hop f a b
  have hbaseLt : base < 2 ^ f.width := evalFloatArithBase_lt op f a b base hbase
  have hmod_neg : evalFloatNeg f a % 2 ^ f.width = evalFloatNeg f (a % 2 ^ f.width) := by
    rw [Nat.mod_eq_of_lt (evalFloatNeg_lt f a), evalFloatNeg_mod]
  unfold EvalFloatBinOpRel
  rw [hcmp, hcmp, hbase, hbase']
  dsimp only
  rw [hnan_eq, hmod_neg]
  by_cases hnan : isNaNBits f base = true
  · rw [if_pos' hnan, if_pos' hnan]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with ⟨cand, hcand, heq⟩
      injection heq with hcand_eq _
      have hmem1 : evalFloatNeg f outBits ∈ nanChoices f [(f, a % 2 ^ f.width), (f, b % 2 ^ f.width)] .nondeterministic := by
        rw [hcand_eq]
        exact (mem_nanChoices_nondet_neg_left f _ _ cand).mp hcand
      have hmem2 := mem_nanChoices_nondet_evalFloatNeg f _ _ hmem1
      rw [evalFloatNeg_involutive f outBits houtLt] at hmem2
      exact ⟨outBits, hmem2, rfl⟩
    · rcases h with ⟨cand, hcand, heq⟩
      injection heq with hcand_eq _
      have hmem1 : evalFloatNeg f outBits ∈ nanChoices f [(f, a % 2 ^ f.width), (f, b % 2 ^ f.width)] .nondeterministic := by
        rw [hcand_eq]
        exact mem_nanChoices_nondet_evalFloatNeg f _ _ hcand
      exact ⟨evalFloatNeg f outBits, (mem_nanChoices_nondet_neg_left f _ _ _).mpr hmem1, rfl⟩
  · have hnanF : isNaNBits f base = false := by
      cases hb : isNaNBits f base with
      | false => rfl
      | true => exact absurd hb hnan
    rw [if_neg' hnan, if_neg' hnan, hnonnan hnanF]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · injection h with hbits _
      have := congrArg (evalFloatNeg f) hbits
      rw [evalFloatNeg_involutive f outBits houtLt, evalFloatNeg_involutive f base hbaseLt] at this
      rw [this]
    · injection h with hbits _
      rw [hbits]

/-- **Unconditional `.nondeterministic` right sign-symmetry for `mul` and `div`**:
for ALL `a b : Nat` and EVERY canonical `outBits < 2^f.width`, `a op (-b)` admits
`-outBits` iff `a op b` admits `outBits`. -/
theorem EvalFloatBinOpRel.nondet_mul_div_neg_right
    (op : BinOp) (hop : op = .mul ∨ op = .div)
    (f : IeeeFormat) (a b outBits : Nat) (houtLt : outBits < 2 ^ f.width) :
    EvalFloatBinOpRel .nondeterministic op f a (evalFloatNeg f b)
        ⟨evalFloatNeg f outBits, f.byteWidth⟩ ↔
      EvalFloatBinOpRel .nondeterministic op f a b ⟨outBits, f.byteWidth⟩ := by
  have hcmp : ∀ x y, evalFloatCmp op f x y = .none := by
    intro x y; rcases hop with rfl | rfl <;> rfl
  obtain ⟨base, base', hbase, hbase', hnan_eq, hnonnan⟩ :=
    evalFloatArithBase_mul_div_neg_right op hop f a b
  have hbaseLt : base < 2 ^ f.width := evalFloatArithBase_lt op f a b base hbase
  have hmod_neg : evalFloatNeg f b % 2 ^ f.width = evalFloatNeg f (b % 2 ^ f.width) := by
    rw [Nat.mod_eq_of_lt (evalFloatNeg_lt f b), evalFloatNeg_mod]
  unfold EvalFloatBinOpRel
  rw [hcmp, hcmp, hbase, hbase']
  dsimp only
  rw [hnan_eq, hmod_neg]
  by_cases hnan : isNaNBits f base = true
  · rw [if_pos' hnan, if_pos' hnan]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with ⟨cand, hcand, heq⟩
      injection heq with hcand_eq _
      have hmem1 : evalFloatNeg f outBits ∈ nanChoices f [(f, a % 2 ^ f.width), (f, b % 2 ^ f.width)] .nondeterministic := by
        rw [hcand_eq]
        exact (mem_nanChoices_nondet_neg_right f _ _ cand).mp hcand
      have hmem2 := mem_nanChoices_nondet_evalFloatNeg f _ _ hmem1
      rw [evalFloatNeg_involutive f outBits houtLt] at hmem2
      exact ⟨outBits, hmem2, rfl⟩
    · rcases h with ⟨cand, hcand, heq⟩
      injection heq with hcand_eq _
      have hmem1 : evalFloatNeg f outBits ∈ nanChoices f [(f, a % 2 ^ f.width), (f, b % 2 ^ f.width)] .nondeterministic := by
        rw [hcand_eq]
        exact mem_nanChoices_nondet_evalFloatNeg f _ _ hcand
      exact ⟨evalFloatNeg f outBits, (mem_nanChoices_nondet_neg_right f _ _ _).mpr hmem1, rfl⟩
  · have hnanF : isNaNBits f base = false := by
      cases hb : isNaNBits f base with
      | false => rfl
      | true => exact absurd hb hnan
    rw [if_neg' hnan, if_neg' hnan, hnonnan hnanF]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · injection h with hbits _
      have := congrArg (evalFloatNeg f) hbits
      rw [evalFloatNeg_involutive f outBits houtLt, evalFloatNeg_involutive f base hbaseLt] at this
      rw [this]
    · injection h with hbits _
      rw [hbits]

/-- Exact IEEE 754-2008 §6.3 opposite-sign zero-cancellation predicate for `add`:
holds iff `a + b` cancels to `+0.0` (`(+0.0) + (-0.0)`, `(-0.0) + (+0.0)`, or
`(+x) + (-x)` for finite nonzero `x`), the sole exception to `(-a) + (-b) = -(a + b)`
under `roundTiesToEven`. -/
def isAddZeroCancel (f : IeeeFormat) (a b : Nat) : Prop :=
  (decodeBits f a = .zero false ∧ decodeBits f b = .zero true) ∨
  (decodeBits f a = .zero true ∧ decodeBits f b = .zero false) ∨
  (∃ ln lnum lden rn rnum rden,
    decodeBits f a = .finite ln lnum lden ∧
    decodeBits f b = .finite rn rnum rden ∧
    signedNum ln lnum * (rden : Int) + signedNum rn rnum * (lden : Int) = 0)

/-- Exact zero-cancellation predicate for `sub`: `a - b` cancels to `+0.0`
(`(+0.0) - (+0.0)`, `(-0.0) - (-0.0)`, or `x - x` for finite nonzero `x`). -/
def isSubZeroCancel (f : IeeeFormat) (a b : Nat) : Prop :=
  isAddZeroCancel f a (evalFloatNeg f b)

/-- **`.nondeterministic` simultaneous sign-symmetry for `add`** across ALL NaNs, ALL
infinities, `(+0.0) + (+0.0)`, `(-0.0) + (-0.0)`, and ALL non-canceling finite pairs
(isolating only IEEE 754-2008 §6.3 `+0.0` zero-cancellation `isAddZeroCancel`). -/
theorem EvalFloatBinOpRel.nondet_add_neg_both_iff
    (f : IeeeFormat) (a b outBits : Nat)
    (houtLt : outBits < 2 ^ f.width)
    (hNotCancel : ¬ isAddZeroCancel f a b) :
    EvalFloatBinOpRel .nondeterministic .add f (evalFloatNeg f a) (evalFloatNeg f b)
        ⟨evalFloatNeg f outBits, f.byteWidth⟩ ↔
      EvalFloatBinOpRel .nondeterministic .add f a b ⟨outBits, f.byteWidth⟩ := by
  have haMod : evalFloatNeg f a % 2 ^ f.width = evalFloatNeg f (a % 2 ^ f.width) := by
    rw [Nat.mod_eq_of_lt (evalFloatNeg_lt f a), evalFloatNeg_mod]
  have hbMod : evalFloatNeg f b % 2 ^ f.width = evalFloatNeg f (b % 2 ^ f.width) := by
    rw [Nat.mod_eq_of_lt (evalFloatNeg_lt f b), evalFloatNeg_mod]
  have hnan_both : ∀ x,
      x ∈ nanChoices f [(f, evalFloatNeg f (a % 2 ^ f.width)), (f, evalFloatNeg f (b % 2 ^ f.width))] .nondeterministic ↔
        x ∈ nanChoices f [(f, a % 2 ^ f.width), (f, b % 2 ^ f.width)] .nondeterministic := by
    intro x
    exact (mem_nanChoices_nondet_neg_left f _ _ x).trans (mem_nanChoices_nondet_neg_right f _ _ x)
  have hbase_rel :
      ∃ base base',
        evalFloatArithBase .add f a b = .some base ∧
        evalFloatArithBase .add f (evalFloatNeg f a) (evalFloatNeg f b) = .some base' ∧
        isNaNBits f base' = isNaNBits f base ∧
        (isNaNBits f base = false → base' = evalFloatNeg f base) := by
    unfold evalFloatArithBase
    dsimp only
    simp only [decodeBits_mod, decodeBits_evalFloatNeg]
    cases ha : decodeBits f a <;> cases hb : decodeBits f b <;> simp only [negateFloatKind, exactSumFloat]
    · rename_i ln rn
      cases ln <;> cases rn
      · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_zeroBits, isNaNBits_zeroBits], fun _ => ?_⟩
        exact (evalFloatNeg_zeroBits f false).symm
      · exact False.elim (hNotCancel (Or.inl ⟨ha, hb⟩))
      · exact False.elim (hNotCancel (Or.inr (Or.inl ⟨ha, hb⟩)))
      · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_zeroBits, isNaNBits_zeroBits], fun _ => ?_⟩
        exact (evalFloatNeg_zeroBits f true).symm
    · rename_i ln rn rnum rden
      have hrn := decodeBits_finite_num_pos f b rn rnum rden hb
      have hrd := decodeBits_finite_den_pos f b rn rnum rden hb
      refine ⟨_, _, rfl, rfl, ?_, ?_⟩
      · simp only [if_neg' (by omega : ¬ rnum = 0), isNaNBits_roundRatioTiesToEven f _ _ _ hrd]
      · intro _; simp only [if_neg' (by omega : ¬ rnum = 0), roundRatioTiesToEven_neg f _ _ _ hrd]
    · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_infBits, isNaNBits_infBits], fun _ => ?_⟩
      exact (evalFloatNeg_infBits f _).symm
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · rename_i ln lnum lden rn
      have hln := decodeBits_finite_num_pos f a ln lnum lden ha
      have hld := decodeBits_finite_den_pos f a ln lnum lden ha
      refine ⟨_, _, rfl, rfl, ?_, ?_⟩
      · simp only [if_neg' (by omega : ¬ lnum = 0), isNaNBits_roundRatioTiesToEven f _ _ _ hld]
      · intro _; simp only [if_neg' (by omega : ¬ lnum = 0), roundRatioTiesToEven_neg f _ _ _ hld]
    · rename_i ln lnum lden rn rnum rden
      have hld := decodeBits_finite_den_pos f a ln lnum lden ha
      have hrd := decodeBits_finite_den_pos f b rn rnum rden hb
      have hd : 0 < lden * rden := Nat.mul_pos hld hrd
      let n : Int := signedNum ln lnum * (rden : Int) + signedNum rn rnum * (lden : Int)
      have hnNe0 : n ≠ 0 := fun h0 =>
        hNotCancel (Or.inr (Or.inr ⟨ln, lnum, lden, rn, rnum, rden, ha, hb, h0⟩))
      have hn' : signedNum (Bool.not ln) lnum * (rden : Int) +
          signedNum (Bool.not rn) rnum * (lden : Int) = -n := by
        rw [signedNum_not, signedNum_not]; simp only [n, Int.neg_mul]; omega
      have hnegNe0 : -n ≠ 0 := by omega
      have hdecNeg : decide (-n < 0) = Bool.not (decide (n < 0)) := by
        by_cases hlt : n < 0
        · rw [decide_eq_true hlt, decide_eq_false (by omega)]; rfl
        · rw [decide_eq_false hlt, decide_eq_true (by omega)]; rfl
      refine ⟨_, _, rfl, rfl, ?_, ?_⟩
      · rw [isNaNBits_roundRatioTiesToEven f _ _ _ hd, isNaNBits_roundRatioTiesToEven f _ _ _ hd]
      · intro _
        rw [hn', if_neg' hnegNe0, if_neg' hnNe0, Int.natAbs_neg, hdecNeg,
          roundRatioTiesToEven_neg f _ _ _ hd]
    · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_infBits, isNaNBits_infBits], fun _ => ?_⟩
      exact (evalFloatNeg_infBits f _).symm
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_infBits, isNaNBits_infBits], fun _ => ?_⟩
      exact (evalFloatNeg_infBits f _).symm
    · refine ⟨_, _, rfl, rfl, by rw [isNaNBits_infBits, isNaNBits_infBits], fun _ => ?_⟩
      exact (evalFloatNeg_infBits f _).symm
    · rename_i ln rn
      cases hxor : Bool.xor ln rn with
      | true =>
        have hxor2 : Bool.xor (Bool.not ln) (Bool.not rn) = true := by
          rw [bool_xor_not_both, hxor]
        refine ⟨_, _, rfl, rfl, by simp only [hxor2, ↓reduceIte], fun h => ?_⟩
        simp only [↓reduceIte, isNaNBits_preferredNaNBits] at h; cases h
      | false =>
        have hxor2 : Bool.xor (Bool.not ln) (Bool.not rn) = false := by
          rw [bool_xor_not_both, hxor]
        refine ⟨_, _, rfl, rfl, by simp only [hxor2, Bool.false_eq_true, ↓reduceIte, isNaNBits_infBits], fun _ => ?_⟩
        simp only [hxor2, Bool.false_eq_true, ↓reduceIte]
        exact (evalFloatNeg_infBits f ln).symm
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun h => by rw [isNaNBits_preferredNaNBits] at h; cases h⟩
  obtain ⟨base, base', hbase, hbase', hnan_eq, hnonnan⟩ := hbase_rel
  have hbaseLt : base < 2 ^ f.width := evalFloatArithBase_lt .add f a b base hbase
  unfold EvalFloatBinOpRel
  change (match evalFloatArithBase .add f (evalFloatNeg f a) (evalFloatNeg f b) with
      | .some baseBits =>
        if isNaNBits f baseBits = true then
          ∃ cand, cand ∈ nanChoices f [(f, evalFloatNeg f a % 2 ^ f.width),
            (f, evalFloatNeg f b % 2 ^ f.width)] .nondeterministic ∧
            ScalarInt.mk (evalFloatNeg f outBits) f.byteWidth = ⟨cand, f.byteWidth⟩
        else ScalarInt.mk (evalFloatNeg f outBits) f.byteWidth = ⟨baseBits, f.byteWidth⟩
      | .none => False) ↔
    (match evalFloatArithBase .add f a b with
      | .some baseBits =>
        if isNaNBits f baseBits = true then
          ∃ cand, cand ∈ nanChoices f [(f, a % 2 ^ f.width), (f, b % 2 ^ f.width)] .nondeterministic ∧
            ScalarInt.mk outBits f.byteWidth = ⟨cand, f.byteWidth⟩
        else ScalarInt.mk outBits f.byteWidth = ⟨baseBits, f.byteWidth⟩
      | .none => False)
  rw [hbase, hbase']
  dsimp only
  rw [hnan_eq, haMod, hbMod]
  by_cases hnan : isNaNBits f base = true
  · rw [if_pos' hnan, if_pos' hnan]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with ⟨cand, hcand, heq⟩
      injection heq with hcand_eq _
      have hmem1 : evalFloatNeg f outBits ∈ nanChoices f [(f, a % 2 ^ f.width), (f, b % 2 ^ f.width)] .nondeterministic := by
        rw [hcand_eq]; exact (hnan_both cand).mp hcand
      have hmem2 := mem_nanChoices_nondet_evalFloatNeg f _ _ hmem1
      rw [evalFloatNeg_involutive f outBits houtLt] at hmem2
      exact ⟨outBits, hmem2, rfl⟩
    · rcases h with ⟨cand, hcand, heq⟩
      injection heq with hcand_eq _
      have hmem1 : evalFloatNeg f outBits ∈ nanChoices f [(f, a % 2 ^ f.width), (f, b % 2 ^ f.width)] .nondeterministic := by
        rw [hcand_eq]; exact mem_nanChoices_nondet_evalFloatNeg f _ _ hcand
      exact ⟨evalFloatNeg f outBits, (hnan_both _).mpr hmem1, rfl⟩
  · have hnanF : isNaNBits f base = false := by
      cases hb : isNaNBits f base with
      | false => rfl
      | true => exact absurd hb hnan
    rw [if_neg' hnan, if_neg' hnan, hnonnan hnanF]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · injection h with hbits _
      have := congrArg (evalFloatNeg f) hbits
      rw [evalFloatNeg_involutive f outBits houtLt, evalFloatNeg_involutive f base hbaseLt] at this
      rw [this]
    · injection h with hbits _
      rw [hbits]

/-- Relation bridge: in `.nondeterministic` mode, `sub a b` and `add a (-b)` admit the
exact same outputs (even on NaNs, despite `nanChoices` ordering). -/
theorem EvalFloatBinOpRel.nondet_sub_iff_add_neg (f : IeeeFormat) (a b : Nat) (out : ScalarInt) :
    EvalFloatBinOpRel .nondeterministic .sub f a b out ↔
      EvalFloatBinOpRel .nondeterministic .add f a (evalFloatNeg f b) out := by
  have hbase_eq : evalFloatArithBase .sub f a b = evalFloatArithBase .add f a (evalFloatNeg f b) := by
    unfold evalFloatArithBase
    dsimp only
    simp only [decodeBits_mod, decodeBits_evalFloatNeg]
  have hbMod : evalFloatNeg f b % 2 ^ f.width = evalFloatNeg f (b % 2 ^ f.width) := by
    rw [Nat.mod_eq_of_lt (evalFloatNeg_lt f b), evalFloatNeg_mod]
  unfold EvalFloatBinOpRel
  have hcmp1 : evalFloatCmp .sub f a b = .none := rfl
  have hcmp2 : evalFloatCmp .add f a (evalFloatNeg f b) = .none := rfl
  rw [hcmp1, hcmp2, hbase_eq, hbMod]
  dsimp only
  cases evalFloatArithBase .add f a (evalFloatNeg f b) with
  | none => exact Iff.rfl
  | some baseBits =>
    dsimp only
    by_cases hnan : isNaNBits f baseBits = true
    · rw [if_pos' hnan, if_pos' hnan]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases h with ⟨cand, hcand, hout⟩
        exact ⟨cand, (mem_nanChoices_nondet_neg_right f _ _ cand).mpr hcand, hout⟩
      · rcases h with ⟨cand, hcand, hout⟩
        exact ⟨cand, (mem_nanChoices_nondet_neg_right f _ _ cand).mp hcand, hout⟩
    · rw [if_neg' hnan, if_neg' hnan]

/-- **`.nondeterministic` simultaneous sign-symmetry for `sub`** across ALL NaNs, ALL
infinities, `(+0.0) - (-0.0)`, `(-0.0) - (+0.0)`, and ALL non-canceling finite pairs
(isolating only IEEE 754-2008 §6.3 `+0.0` zero-cancellation `isSubZeroCancel`). -/
theorem EvalFloatBinOpRel.nondet_sub_neg_both_iff
    (f : IeeeFormat) (a b outBits : Nat)
    (houtLt : outBits < 2 ^ f.width)
    (hNotCancel : ¬ isSubZeroCancel f a b) :
    EvalFloatBinOpRel .nondeterministic .sub f (evalFloatNeg f a) (evalFloatNeg f b)
        ⟨evalFloatNeg f outBits, f.byteWidth⟩ ↔
      EvalFloatBinOpRel .nondeterministic .sub f a b ⟨outBits, f.byteWidth⟩ := by
  rw [EvalFloatBinOpRel.nondet_sub_iff_add_neg, EvalFloatBinOpRel.nondet_sub_iff_add_neg]
  exact EvalFloatBinOpRel.nondet_add_neg_both_iff f a (evalFloatNeg f b) outBits houtLt hNotCancel

/-- **Mode-independence of finite IEEE `rem`**: whenever the dividend is zero-or-finite and the
divisor is finite nonzero, `EvalFloatBinOpRel mode .rem` never produces NaN and coincides
exactly with `evalFloatBinOp .rem` in BOTH `.deterministic` and `.nondeterministic` modes. -/
theorem EvalFloatBinOpRel_rem_finite_deterministic (mode : FloatArithMode) (f : IeeeFormat)
    (a b : Nat) (out : ScalarInt) (ln rn : Bool) (rnum rden : Nat)
    (ha : decodeBits f (a % 2 ^ f.width) = .zero ln ∨
      ∃ lnum lden, decodeBits f (a % 2 ^ f.width) = .finite ln lnum lden)
    (hb : decodeBits f (b % 2 ^ f.width) = .finite rn rnum rden) :
    EvalFloatBinOpRel mode .rem f a b out ↔ evalFloatBinOp .rem f a b = .some out := by
  obtain ⟨outBits, heval, _, hnotNan, _, _, _, _⟩ :=
    evalFloatArithBase_rem_finite_sign_and_bound f a b ln rn rnum rden ha hb
  unfold EvalFloatBinOpRel evalFloatBinOp
  have hcmp : evalFloatCmp .rem f a b = .none := rfl
  rw [hcmp, heval]
  dsimp only
  rw [if_neg' (by rw [hnotNan]; exact Bool.false_ne_true)]
  exact ⟨fun h => congrArg Option.some h.symm, fun h => (Option.some.inj h).symm⟩

/-! ## §5. `Ptr2IntTransmutePolicy` laws, 32-bit/slot-0 witnesses, & rich ADT no-forgery -/

/-! ### Byte-level provenance helpers -/

theorem length_stripAbstractBytesProv (bs : List AbstractByte) :
    length (stripAbstractBytesProv bs) = length bs := by
  induction bs with
  | nil => rfl
  | cons _ _ ih => exact congrArg (· + 1) ih

theorem abstractBytesHaveProv_stripAbstractBytesProv (bs : List AbstractByte) :
    abstractBytesHaveProv (stripAbstractBytesProv bs) = false := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | uninit => exact ih
    | init byte prov => exact ih

theorem takeAbstractBytes_stripAbstractBytesProv (n : Nat) (bs : List AbstractByte) :
    takeAbstractBytes n (stripAbstractBytesProv bs) =
      stripAbstractBytesProv (takeAbstractBytes n bs) := by
  induction n generalizing bs with
  | zero => rfl
  | succ k ih =>
    cases bs with
    | nil => rfl
    | cons b rest =>
      simp only [stripAbstractBytesProv, takeAbstractBytes, ih]

theorem dropAbstractBytes_stripAbstractBytesProv (n : Nat) (bs : List AbstractByte) :
    dropAbstractBytes n (stripAbstractBytesProv bs) =
      stripAbstractBytesProv (dropAbstractBytes n bs) := by
  induction n generalizing bs with
  | zero => rfl
  | succ k ih =>
    cases bs with
    | nil => rfl
    | cons b rest =>
      simp only [dropAbstractBytes, ih]

theorem sliceAbstractBytes_stripAbstractBytesProv (bs : List AbstractByte) (off sz : Nat) :
    sliceAbstractBytes (stripAbstractBytesProv bs) off sz =
      Option.map stripAbstractBytesProv (sliceAbstractBytes bs off sz) := by
  unfold sliceAbstractBytes
  rw [length_stripAbstractBytesProv]
  cases Nat.ble (Nat.add off sz) (length bs) with
  | false => rfl
  | true =>
    simp only [Option.map, dropAbstractBytes_stripAbstractBytesProv,
      takeAbstractBytes_stripAbstractBytesProv]

theorem decodeLittleEndianBytes_stripAbstractBytesProv (bs : List AbstractByte) :
    decodeLittleEndianBytes (stripAbstractBytesProv bs) =
      match decodeLittleEndianBytes bs with
      | .some res => .some (res.1, .none)
      | .none => .none := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | uninit => rfl
    | init byte prov =>
      simp only [decodeLittleEndianBytes, ih]
      cases decodeLittleEndianBytes rest with
      | none => rfl
      | some res => rfl

theorem decodeScalarBytes_stripAbstractBytesProv (bs : List AbstractByte) (isSigned : Bool) :
    decodeScalarBytes (stripAbstractBytesProv bs) isSigned =
      match decodeScalarBytes bs isSigned with
      | .some res => .some (res.1, .none)
      | .none => .none := by
  unfold decodeScalarBytes
  dsimp only
  rw [length_stripAbstractBytesProv, decodeLittleEndianBytes_stripAbstractBytesProv]
  cases Nat.beq (length bs) 0 with
  | true => rfl
  | false =>
    dsimp only
    cases decodeLittleEndianBytes bs with
    | none => rfl
    | some res => rcases res with ⟨bits, prov⟩; rfl

theorem abstractBytesHaveProv_takeAbstractBytes_false (n : Nat) (bs : List AbstractByte)
    (h : abstractBytesHaveProv bs = false) :
    abstractBytesHaveProv (takeAbstractBytes n bs) = false := by
  induction n generalizing bs with
  | zero => rfl
  | succ k ih =>
    cases bs with
    | nil => rfl
    | cons b rest =>
      cases b with
      | uninit => exact ih rest h
      | init byte prov =>
        cases prov with
        | none => exact ih rest h
        | some p => cases h

theorem abstractBytesHaveProv_dropAbstractBytes_false (n : Nat) (bs : List AbstractByte)
    (h : abstractBytesHaveProv bs = false) :
    abstractBytesHaveProv (dropAbstractBytes n bs) = false := by
  induction n generalizing bs with
  | zero => exact h
  | succ k ih =>
    cases bs with
    | nil => rfl
    | cons b rest =>
      cases b with
      | uninit => exact ih rest h
      | init byte prov =>
        cases prov with
        | none => exact ih rest h
        | some p => cases h

theorem abstractBytesHaveProv_sliceAbstractBytes_false (bs sl : List AbstractByte) (off sz : Nat)
    (h : abstractBytesHaveProv bs = false)
    (hsl : sliceAbstractBytes bs off sz = .some sl) :
    abstractBytesHaveProv sl = false := by
  unfold sliceAbstractBytes at hsl
  cases hle : Nat.ble (Nat.add off sz) (length bs) with
  | false => rw [hle] at hsl; cases hsl
  | true =>
    rw [hle] at hsl
    injection hsl with hsl
    rw [← hsl]
    exact abstractBytesHaveProv_takeAbstractBytes_false sz _
      (abstractBytesHaveProv_dropAbstractBytes_false off bs h)

/-! ### Refinement (`strictUcg630Ub` refines `stripProvenance`) & exact cast split -/

theorem decodeScalarLayoutBytesNoForge_strict_imp_strip
    (sl : ScalarLayout) (bs : List AbstractByte) (v : Value)
    (h : decodeScalarLayoutBytesNoForge sl bs .strictUcg630Ub = .some v) :
    decodeScalarLayoutBytesNoForge sl bs .stripProvenance = .some v := by
  unfold decodeScalarLayoutBytesNoForge at h ⊢
  revert h
  cases scalarLayoutByteWidth sl with
  | none => intro h; cases h
  | some sz =>
    dsimp only
    cases Nat.beq (length bs) sz with
    | false => intro h; cases h
    | true =>
      dsimp only
      cases sl with
      | initialized pk vr =>
        cases pk with
        | pointer _ => exact id
        | int _ _ =>
          dsimp only
          cases abstractBytesHaveProv bs with
          | true => intro h; cases h
          | false => exact id
        | float _ =>
          dsimp only
          cases abstractBytesHaveProv bs with
          | true => intro h; cases h
          | false => exact id
      | union pk =>
        cases pk with
        | pointer _ => exact id
        | int _ _ =>
          dsimp only
          cases abstractBytesHaveProv bs with
          | true => intro h; cases h
          | false => exact id
        | float _ =>
          dsimp only
          cases abstractBytesHaveProv bs with
          | true => intro h; cases h
          | false => exact id

private theorem decodeArrayChunksWith_mono
    (f g : List AbstractByte → Option Value)
    (hmono : ∀ bs v, f bs = .some v → g bs = .some v)
    (elemSize : Nat) :
    ∀ count bs vs,
      decodeArrayChunksWith f elemSize count bs = .some vs →
      decodeArrayChunksWith g elemSize count bs = .some vs := by
  intro count
  induction count with
  | zero =>
    intro bs vs h
    cases bs with
    | nil => exact h
    | cons _ _ => cases h
  | succ k ih =>
    intro bs vs h
    unfold decodeArrayChunksWith at h ⊢
    cases hle : Nat.ble elemSize (length bs) with
    | false => rw [hle] at h; cases h
    | true =>
      rw [hle] at h
      dsimp only at h ⊢
      cases hf : f (takeAbstractBytes elemSize bs) with
      | none => rw [hf] at h; cases h
      | some v =>
        rw [hf] at h
        rw [hmono _ v hf]
        dsimp only at h ⊢
        cases hr : decodeArrayChunksWith f elemSize k (dropAbstractBytes elemSize bs) with
        | none => rw [hr] at h; cases h
        | some rest =>
          rw [hr] at h
          rw [ih _ rest hr]
          exact h

private theorem decodeFieldsAtOffsetsWith_mono
    (f g : RigidTy → List AbstractByte → Option Value)
    (hmono : ∀ k bs v, f k bs = .some v → g k bs = .some v)
    (sizeOfKind : RigidTy → Option Nat) (bytes : List AbstractByte) :
    ∀ offsets ks vs,
      decodeFieldsAtOffsetsWith f sizeOfKind bytes offsets ks = .some vs →
      decodeFieldsAtOffsetsWith g sizeOfKind bytes offsets ks = .some vs := by
  intro offsets
  induction offsets with
  | nil =>
    intro ks vs h
    cases ks with
    | nil => exact h
    | cons _ _ => cases h
  | cons off offRest ih =>
    intro ks vs h
    cases ks with
    | nil => cases h
    | cons k kRest =>
      unfold decodeFieldsAtOffsetsWith at h ⊢
      cases hsz : sizeOfKind k with
      | none => rw [hsz] at h; cases h
      | some fSize =>
        rw [hsz] at h
        dsimp only at h ⊢
        cases hsl : sliceAbstractBytes bytes off.bytes fSize with
        | none => rw [hsl] at h; cases h
        | some fSlice =>
          rw [hsl] at h
          dsimp only at h ⊢
          cases hf : f k fSlice with
          | none => rw [hf] at h; cases h
          | some v =>
            rw [hf] at h
            rw [hmono k fSlice v hf]
            dsimp only at h ⊢
            cases hr : decodeFieldsAtOffsetsWith f sizeOfKind bytes offRest kRest with
            | none => rw [hr] at h; cases h
            | some rest =>
              rw [hr] at h
              rw [ih kRest rest hr]
              exact h

private theorem decodeSeqFieldsWith_mono
    (f g : RigidTy → List AbstractByte → Option Value)
    (hmono : ∀ k bs v, f k bs = .some v → g k bs = .some v)
    (sizeOfKind : RigidTy → Option Nat) :
    ∀ ks bytes vs,
      decodeSeqFieldsWith f sizeOfKind ks bytes = .some vs →
      decodeSeqFieldsWith g sizeOfKind ks bytes = .some vs := by
  intro ks
  induction ks with
  | nil =>
    intro bytes vs h
    cases bytes with
    | nil => exact h
    | cons _ _ => cases h
  | cons k kRest ih =>
    intro bytes vs h
    unfold decodeSeqFieldsWith at h ⊢
    cases hsz : sizeOfKind k with
    | none => rw [hsz] at h; cases h
    | some fSize =>
      rw [hsz] at h
      dsimp only at h ⊢
      cases hle : Nat.ble fSize (length bytes) with
      | false => rw [hle] at h; cases h
      | true =>
        rw [hle] at h
        dsimp only at h ⊢
        cases hf : f k (takeAbstractBytes fSize bytes) with
        | none => rw [hf] at h; cases h
        | some v =>
          rw [hf] at h
          rw [hmono k _ v hf]
          dsimp only at h ⊢
          cases hr : decodeSeqFieldsWith f sizeOfKind kRest (dropAbstractBytes fSize bytes) with
          | none => rw [hr] at h; cases h
          | some rest =>
            rw [hr] at h
            rw [ih _ rest hr]
            exact h

private theorem decodeTypedKindsAndLayoutsAtOffsets_mono
    (f g : Ty → List AbstractByte → Option Value)
    (hmono : ∀ ty bs v, f ty bs = .some v → g ty bs = .some v)
    (layouts : LayoutTable) (bytes : List AbstractByte) :
    ∀ offsets ks fls vs,
      decodeTypedKindsAndLayoutsAtOffsets f layouts bytes offsets ks fls = .some vs →
      decodeTypedKindsAndLayoutsAtOffsets g layouts bytes offsets ks fls = .some vs := by
  intro offsets
  induction offsets with
  | nil =>
    intro ks fls vs h
    cases ks <;> cases fls <;> exact h
  | cons off offRest ih =>
    intro ks fls vs h
    cases ks with
    | nil => cases h
    | cons k kRest =>
      cases fls with
      | nil => cases h
      | cons fIdx fRest =>
        unfold decodeTypedKindsAndLayoutsAtOffsets at h ⊢
        cases hlu : LayoutTable.lookup layouts fIdx with
        | none => rw [hlu] at h; cases h
        | some fl =>
          rw [hlu] at h
          dsimp only at h ⊢
          cases hsl : sliceAbstractBytes bytes off.bytes fl.size.bytes with
          | none => rw [hsl] at h; cases h
          | some fSlice =>
            rw [hsl] at h
            dsimp only at h ⊢
            cases hf : f { kind := k, layoutIdx := fIdx } fSlice with
            | none => rw [hf] at h; cases h
            | some v =>
              rw [hf] at h
              rw [hmono _ fSlice v hf]
              dsimp only at h ⊢
              cases hr : decodeTypedKindsAndLayoutsAtOffsets f layouts bytes offRest kRest fRest with
              | none => rw [hr] at h; cases h
              | some rest =>
                rw [hr] at h
                rw [ih kRest fRest rest hr]
                exact h

private theorem decodeFieldsByLayoutIdxs_mono
    (f g : Nat → List AbstractByte → Option Value)
    (hmono : ∀ fIdx bs v, f fIdx bs = .some v → g fIdx bs = .some v)
    (layouts : LayoutTable) (bytes : List AbstractByte) :
    ∀ offsets fls vs,
      decodeFieldsByLayoutIdxs f layouts bytes offsets fls = .some vs →
      decodeFieldsByLayoutIdxs g layouts bytes offsets fls = .some vs := by
  intro offsets
  induction offsets with
  | nil =>
    intro fls vs h
    cases fls <;> exact h
  | cons off offRest ih =>
    intro fls vs h
    cases fls with
    | nil => cases h
    | cons fIdx fRest =>
      unfold decodeFieldsByLayoutIdxs at h ⊢
      cases hlu : LayoutTable.lookup layouts fIdx with
      | none => rw [hlu] at h; cases h
      | some fl =>
        rw [hlu] at h
        dsimp only at h ⊢
        cases hsl : sliceAbstractBytes bytes off.bytes fl.size.bytes with
        | none => rw [hsl] at h; cases h
        | some fSlice =>
          rw [hsl] at h
          dsimp only at h ⊢
          cases hf : f fIdx fSlice with
          | none => rw [hf] at h; cases h
          | some v =>
            rw [hf] at h
            rw [hmono fIdx fSlice v hf]
            dsimp only at h ⊢
            cases hr : decodeFieldsByLayoutIdxs f layouts bytes offRest fRest with
            | none => rw [hr] at h; cases h
            | some rest =>
              rw [hr] at h
              rw [ih fRest rest hr]
              exact h

private theorem decodeRichFieldSpecs_mono
    (f g : Ty → List AbstractByte → Option Value)
    (hmono : ∀ ty bs v, f ty bs = .some v → g ty bs = .some v)
    (bytes : List AbstractByte) :
    ∀ specs vs,
      decodeRichFieldSpecs f bytes specs = .some vs →
      decodeRichFieldSpecs g bytes specs = .some vs := by
  intro specs
  induction specs with
  | nil => intro vs h; exact h
  | cons spec rest ih =>
    intro vs h
    unfold decodeRichFieldSpecs at h ⊢
    cases hsl : sliceAbstractBytes bytes spec.1 spec.2.1 with
    | none => rw [hsl] at h; cases h
    | some fSlice =>
      rw [hsl] at h
      dsimp only at h ⊢
      cases hf : f spec.2.2 fSlice with
      | none => rw [hf] at h; cases h
      | some v =>
        rw [hf] at h
        rw [hmono spec.2.2 fSlice v hf]
        dsimp only at h ⊢
        cases hr : decodeRichFieldSpecs f bytes rest with
        | none => rw [hr] at h; cases h
        | some restVals =>
          rw [hr] at h
          rw [ih restVals hr]
          exact h

/-- **Refinement for `decodeTypedValueFromBytes`**: every value accepted under
`.strictUcg630Ub` is accepted with the exact same `Value` under `.stripProvenance`. -/
theorem decodeTypedValueFromBytes_strictUcg630Ub_refines_stripProvenance
    (fuel : Nat) (layouts : LayoutTable) (ty : Ty) (bytes : List AbstractByte) (v : Value)
    (h : decodeTypedValueFromBytes fuel layouts ty bytes .strictUcg630Ub = .some v) :
    decodeTypedValueFromBytes fuel layouts ty bytes .stripProvenance = .some v := by
  induction fuel generalizing ty bytes v with
  | zero => cases h
  | succ fuel' ih =>
    unfold decodeTypedValueFromBytes at h ⊢
    dsimp only at h ⊢
    revert h
    cases (normalizeCodecTy ty).kind with
    | array elemKind n =>
      dsimp only
      cases Nat.beq n 0 with
      | true => exact id
      | false =>
        dsimp only
        have hfb : ∀ (elemSzOpt : Option Nat),
            ((match elemSzOpt with
              | none => none
              | some elemSz =>
                match Nat.beq (length bytes) (Nat.mul elemSz n) with
                | false => none
                | true =>
                  match decodeArrayChunksWith
                      (fun bs => decodeTypedValueFromBytes fuel' layouts
                        { kind := elemKind, layoutIdx := 0 } bs .strictUcg630Ub)
                      elemSz n bytes with
                  | some elems => some (.aggregate 0 elems)
                  | none => none) = some v) →
            ((match elemSzOpt with
              | none => none
              | some elemSz =>
                match Nat.beq (length bytes) (Nat.mul elemSz n) with
                | false => none
                | true =>
                  match decodeArrayChunksWith
                      (fun bs => decodeTypedValueFromBytes fuel' layouts
                        { kind := elemKind, layoutIdx := 0 } bs .stripProvenance)
                      elemSz n bytes with
                  | some elems => some (.aggregate 0 elems)
                  | none => none) = some v) := by
          intro elemSzOpt
          cases elemSzOpt with
          | none => intro h; cases h
          | some elemSz =>
            dsimp only
            cases Nat.beq (length bytes) (Nat.mul elemSz n) with
            | false => intro h; cases h
            | true =>
              dsimp only
              intro h
              cases hd : decodeArrayChunksWith
                  (fun bs => decodeTypedValueFromBytes fuel' layouts
                    { kind := elemKind, layoutIdx := 0 } bs .strictUcg630Ub)
                  elemSz n bytes with
              | none => rw [hd] at h; cases h
              | some elems =>
                rw [hd] at h
                rw [decodeArrayChunksWith_mono _ _ (fun bs w hw => ih _ bs w hw) elemSz n bytes elems hd]
                exact h
        cases LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
        | none => exact hfb _
        | some l =>
          rcases l with ⟨_, _, _, lfields, _, _, lfls, _⟩
          cases lfields with
          | array stride count =>
            cases lfls with
            | cons elemFlIdx restFl =>
              dsimp only
              cases Nat.beq (length bytes) (Nat.mul stride.bytes n) with
              | false => intro h; cases h
              | true =>
                dsimp only
                intro h
                cases hd : decodeArrayChunksWith
                    (fun bs => decodeTypedValueFromBytes fuel' layouts
                      { kind := elemKind, layoutIdx := elemFlIdx } bs .strictUcg630Ub)
                    stride.bytes n bytes with
                | none => rw [hd] at h; cases h
                | some elems =>
                  rw [hd] at h
                  rw [decodeArrayChunksWith_mono _ _ (fun bs w hw => ih _ bs w hw) stride.bytes n bytes elems hd]
                  exact h
            | nil => exact hfb _
          | _ => exact hfb _
    | tuple ks =>
      cases ks with
      | nil => exact id
      | cons kHead kTail =>
        dsimp only
        have hseq :
            ((match decodeSeqFieldsWith
                  (fun k bs => decodeTypedValueFromBytes fuel' layouts
                    { kind := k, layoutIdx := unresolvedLayoutIdx layouts } bs .strictUcg630Ub)
                  (decodeTypedKindByteSize layouts) (kHead :: kTail) bytes with
              | some vals => some (.aggregate 0 vals)
              | none => none) = some v) →
            ((match decodeSeqFieldsWith
                  (fun k bs => decodeTypedValueFromBytes fuel' layouts
                    { kind := k, layoutIdx := unresolvedLayoutIdx layouts } bs .stripProvenance)
                  (decodeTypedKindByteSize layouts) (kHead :: kTail) bytes with
              | some vals => some (.aggregate 0 vals)
              | none => none) = some v) := by
          intro h
          cases hs : decodeSeqFieldsWith
              (fun k bs => decodeTypedValueFromBytes fuel' layouts
                { kind := k, layoutIdx := unresolvedLayoutIdx layouts } bs .strictUcg630Ub)
              (decodeTypedKindByteSize layouts) (kHead :: kTail) bytes with
          | none => rw [hs] at h; cases h
          | some vals =>
            rw [hs] at h
            rw [decodeSeqFieldsWith_mono _ _ (fun k bs w hw => ih _ bs w hw) _ _ _ vals hs]
            exact h
        cases Bool.not (isUnresolvedLayoutIdx layouts (normalizeCodecTy ty).layoutIdx) with
        | false => exact hseq
        | true =>
          dsimp only
          cases LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
          | none => exact hseq
          | some l =>
            dsimp only
            cases layoutMatchesAggregateVariant l 0 (length (kHead :: kTail)) with
            | false => exact hseq
            | true =>
              dsimp only
              cases Nat.beq (length bytes) l.size.bytes with
              | false => intro h; cases h
              | true =>
                cases l.fields with
                | arbitrary offsets memIdx =>
                  dsimp only
                  cases Bool.and (Nat.beq (length (kHead :: kTail)) (length offsets))
                      (Nat.beq (length l.fieldLayouts) (length offsets)) with
                  | true =>
                    dsimp only
                    intro h
                    cases hd : decodeTypedKindsAndLayoutsAtOffsets
                        (fun cTy bs => decodeTypedValueFromBytes fuel' layouts cTy bs .strictUcg630Ub)
                        layouts bytes offsets (kHead :: kTail) l.fieldLayouts with
                    | none => rw [hd] at h; cases h
                    | some vals =>
                      rw [hd] at h
                      rw [decodeTypedKindsAndLayoutsAtOffsets_mono _ _ (fun cTy bs w hw => ih cTy bs w hw)
                        layouts bytes offsets (kHead :: kTail) l.fieldLayouts vals hd]
                      exact h
                  | false =>
                    dsimp only
                    intro h
                    cases hd : decodeFieldsAtOffsetsWith
                        (fun k bs => decodeTypedValueFromBytes fuel' layouts
                          { kind := k, layoutIdx := unresolvedLayoutIdx layouts } bs .strictUcg630Ub)
                        (decodeTypedKindByteSize layouts) bytes offsets (kHead :: kTail) with
                    | none => rw [hd] at h; cases h
                    | some vals =>
                      rw [hd] at h
                      rw [decodeFieldsAtOffsetsWith_mono _ _ (fun k bs w hw => ih _ bs w hw)
                        _ bytes offsets (kHead :: kTail) vals hd]
                      exact h
                | _ => exact hseq
    | adt defPath args =>
      dsimp only
      cases LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
      | none => exact id
      | some l =>
        dsimp only
        cases Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
        | true => intro h; cases h
        | false =>
          dsimp only
          cases l.variants with
          | empty => exact id
          | multiple tag tagField varShapes =>
            dsimp only
            cases Bool.or (scalarLayoutIsPointer tag) (backendReprHasPointer l.backendRepr) with
            | true => exact id
            | false =>
              dsimp only
              cases abstractBytesHaveProv bytes with
              | true => intro h; cases h
              | false => exact id
          | single variantIdx =>
            cases variantIdx <;>
            cases l.fields with
            | union count => exact id
            | primitive =>
              simp only
              cases Nat.beq l.size.bytes 0 with
              | true => exact id
              | false =>
                dsimp only
                cases l.backendRepr with
                | scalar s0 =>
                  dsimp only
                  exact decodeScalarLayoutBytesNoForge_strict_imp_strip s0 bytes v
                | _ =>
                  dsimp only
                  cases abstractBytesHaveProv bytes with
                  | true => intro h; cases h
                  | false => exact id
            | array stride count =>
              simp only
              cases Nat.beq count 0 with
              | true => exact id
              | false =>
                dsimp only
                cases l.fieldLayouts with
                | cons elemFlIdx _ =>
                  dsimp only
                  intro h
                  cases hd : decodeArrayChunksWith
                      (fun bs => decodeTypedValueFromBytes fuel' layouts
                        { kind := .adt "" .nil, layoutIdx := elemFlIdx } bs .strictUcg630Ub)
                      stride.bytes count bytes with
                  | none => rw [hd] at h; cases h
                  | some vals =>
                    rw [hd] at h
                    rw [decodeArrayChunksWith_mono _ _ (fun bs w hw => ih _ bs w hw) stride.bytes count bytes vals hd]
                    exact h
                | nil =>
                  dsimp only
                  cases abstractBytesHaveProv bytes with
                  | true => intro h; cases h
                  | false => exact id
            | arbitrary offsets memIdx =>
              cases offsets with
              | nil => exact id
              | cons off0 offTail =>
                simp only
                cases Nat.beq (length l.fieldLayouts) (length (off0 :: offTail)) with
                | true =>
                  dsimp only
                  intro h
                  cases hd : decodeFieldsByLayoutIdxs
                      (fun fIdx fSlice => decodeTypedValueFromBytes fuel' layouts
                        { kind := .adt "" .nil, layoutIdx := fIdx } fSlice .strictUcg630Ub)
                      layouts bytes (off0 :: offTail) l.fieldLayouts with
                  | none => rw [hd] at h; cases h
                  | some vals =>
                    rw [hd] at h
                    rw [decodeFieldsByLayoutIdxs_mono _ _ (fun fIdx fSlice w hw => ih _ fSlice w hw)
                      layouts bytes (off0 :: offTail) l.fieldLayouts vals hd]
                    exact h
                | false =>
                  dsimp only
                  cases offTail with
                  | nil =>
                    cases l.backendRepr with
                    | scalar s0 =>
                      dsimp only
                      cases scalarLayoutByteWidth s0 with
                      | none => intro h; cases h
                      | some sz0 =>
                        dsimp only
                        cases sliceAbstractBytes bytes off0.bytes sz0 with
                        | none => intro h; cases h
                        | some slice0 =>
                          dsimp only
                          intro h
                          cases hd0 : decodeScalarLayoutBytesNoForge s0 slice0 .strictUcg630Ub with
                          | none => rw [hd0] at h; cases h
                          | some v0 =>
                            rw [hd0] at h
                            rw [decodeScalarLayoutBytesNoForge_strict_imp_strip s0 slice0 v0 hd0]
                            exact h
                    | _ =>
                      dsimp only
                      cases abstractBytesHaveProv bytes with
                      | true => intro h; cases h
                      | false => exact id
                  | cons off1 offTail2 =>
                    cases offTail2 with
                    | nil =>
                      cases l.backendRepr with
                      | scalarPair s0 s1 =>
                        dsimp only
                        cases scalarLayoutByteWidth s0 with
                        | none => intro h; cases h
                        | some sz0 =>
                          cases scalarLayoutByteWidth s1 with
                          | none => intro h; cases h
                          | some sz1 =>
                            dsimp only
                            cases sliceAbstractBytes bytes off0.bytes sz0 with
                            | none => intro h; cases h
                            | some slice0 =>
                              cases sliceAbstractBytes bytes off1.bytes sz1 with
                              | none => intro h; cases h
                              | some slice1 =>
                                dsimp only
                                intro h
                                cases hd0 : decodeScalarLayoutBytesNoForge s0 slice0 .strictUcg630Ub with
                                | none => rw [hd0] at h; cases h
                                | some v0 =>
                                  cases hd1 : decodeScalarLayoutBytesNoForge s1 slice1 .strictUcg630Ub with
                                  | none => rw [hd0, hd1] at h; cases h
                                  | some v1 =>
                                    rw [hd0, hd1] at h
                                    rw [decodeScalarLayoutBytesNoForge_strict_imp_strip s0 slice0 v0 hd0,
                                      decodeScalarLayoutBytesNoForge_strict_imp_strip s1 slice1 v1 hd1]
                                    exact h
                      | _ =>
                        dsimp only
                        cases abstractBytesHaveProv bytes with
                        | true => intro h; cases h
                        | false => exact id
                    | cons _ _ =>
                      dsimp only
                      cases abstractBytesHaveProv bytes with
                      | true => intro h; cases h
                      | false => exact id
    | uint w =>
      cases w <;>
      · dsimp only
        cases abstractBytesHaveProv bytes with
        | true => intro h; cases h
        | false => exact id
    | int w =>
      cases w <;>
      · dsimp only
        cases abstractBytesHaveProv bytes with
        | true => intro h; cases h
        | false => exact id
    | bool =>
      dsimp only
      cases abstractBytesHaveProv bytes with
      | true => intro h; cases h
      | false => exact id
    | char =>
      dsimp only
      cases abstractBytesHaveProv bytes with
      | true => intro h; cases h
      | false => exact id
    | _ => exact id

/-- **Refinement for `decodeTypedValueRichWithPolicy`**: every value accepted under
`.strictUcg630Ub` is accepted identically under `.stripProvenance`. -/
theorem decodeTypedValueRichWithPolicy_strictUcg630Ub_refines_stripProvenance
    (fuel : Nat) (layouts : LayoutTable) (richSpecs : List (DefPath × RichAdtSpec))
    (ty : Ty) (bytes : List AbstractByte) (v : Value)
    (h : decodeTypedValueRichWithPolicy fuel layouts richSpecs ty bytes .strictUcg630Ub = .some v) :
    decodeTypedValueRichWithPolicy fuel layouts richSpecs ty bytes .stripProvenance = .some v := by
  induction fuel generalizing ty bytes v with
  | zero => cases h
  | succ fuel' ih =>
    unfold decodeTypedValueRichWithPolicy at h ⊢
    dsimp only at h ⊢
    revert h
    cases (normalizeCodecTy ty).kind with
    | adt defPath args =>
      dsimp only
      cases lookupRichAdtSpec defPath richSpecs with
      | none =>
        dsimp only
        exact decodeTypedValueFromBytes_strictUcg630Ub_refines_stripProvenance
          (.succ fuel') layouts ty bytes v
      | some spec =>
        cases spec with
        | structFields varIdx totalBytes fields =>
          dsimp only
          cases Nat.beq (length bytes) totalBytes with
          | false => intro h; cases h
          | true =>
            dsimp only
            intro h
            cases hd : decodeRichFieldSpecs
                (fun cTy bs => decodeTypedValueRichWithPolicy fuel' layouts richSpecs cTy bs .strictUcg630Ub)
                bytes fields with
            | none => rw [hd] at h; cases h
            | some vals =>
              rw [hd] at h
              rw [decodeRichFieldSpecs_mono _ _ (fun cTy bs w hw => ih cTy bs w hw) bytes fields vals hd]
              exact h
        | taggedEnum totalBytes tagOff tagBytes variants =>
          dsimp only
          cases Nat.beq (length bytes) totalBytes with
          | false => intro h; cases h
          | true =>
            dsimp only
            cases sliceAbstractBytes bytes tagOff tagBytes with
            | none => intro h; cases h
            | some tagSlice =>
              dsimp only [policyRejectsProv]
              cases abstractBytesHaveProv tagSlice with
              | true => intro h; cases h
              | false =>
                dsimp only
                cases decodeScalarBytes tagSlice false with
                | none => intro h; cases h
                | some tagRes =>
                  dsimp only
                  cases findRichTaggedVariant tagRes.1.bits variants with
                  | none => intro h; cases h
                  | some varEntry =>
                    dsimp only
                    intro h
                    cases hd : decodeRichFieldSpecs
                        (fun cTy bs => decodeTypedValueRichWithPolicy fuel' layouts richSpecs cTy bs .strictUcg630Ub)
                        bytes varEntry.2 with
                    | none => rw [hd] at h; cases h
                    | some vals =>
                      rw [hd] at h
                      rw [decodeRichFieldSpecs_mono _ _ (fun cTy bs w hw => ih cTy bs w hw) bytes varEntry.2 vals hd]
                      exact h
        | nichePointerEnum totalBytes nicheOff nicheBytes noneVar noneFields someVar someFields =>
          dsimp only
          cases Nat.beq (length bytes) totalBytes with
          | false => intro h; cases h
          | true =>
            dsimp only
            cases sliceAbstractBytes bytes nicheOff nicheBytes with
            | none => intro h; cases h
            | some nicheSlice =>
              dsimp only
              cases abstractBytesUniformProv nicheSlice with
              | true =>
                dsimp only
                intro h
                cases hd : decodeRichFieldSpecs
                    (fun cTy bs => decodeTypedValueRichWithPolicy fuel' layouts richSpecs cTy bs .strictUcg630Ub)
                    bytes someFields with
                | none => rw [hd] at h; cases h
                | some vals =>
                  rw [hd] at h
                  rw [decodeRichFieldSpecs_mono _ _ (fun cTy bs w hw => ih cTy bs w hw) bytes someFields vals hd]
                  exact h
              | false =>
                dsimp only [policyRejectsProv]
                cases abstractBytesHaveProv nicheSlice with
                | true => intro h; cases h
                | false =>
                  dsimp only
                  cases decodeScalarBytes nicheSlice false with
                  | none => intro h; cases h
                  | some nicheRes =>
                    dsimp only
                    cases Nat.beq nicheRes.1.bits 0 with
                    | false => intro h; cases h
                    | true =>
                      dsimp only
                      intro h
                      cases hd : decodeRichFieldSpecs
                          (fun cTy bs => decodeTypedValueRichWithPolicy fuel' layouts richSpecs cTy bs .strictUcg630Ub)
                          bytes noneFields with
                      | none => rw [hd] at h; cases h
                      | some vals =>
                        rw [hd] at h
                        rw [decodeRichFieldSpecs_mono _ _ (fun cTy bs w hw => ih cTy bs w hw) bytes noneFields vals hd]
                        exact h
        | nicheScalarEnum totalBytes nicheOff nicheBytes nicheVal nicheVar nicheFields payVar payFields =>
          dsimp only
          cases Nat.beq (length bytes) totalBytes with
          | false => intro h; cases h
          | true =>
            dsimp only
            cases sliceAbstractBytes bytes nicheOff nicheBytes with
            | none => intro h; cases h
            | some nicheSlice =>
              dsimp only [policyRejectsProv]
              cases abstractBytesHaveProv nicheSlice with
              | true => intro h; cases h
              | false =>
                dsimp only
                cases decodeScalarBytes nicheSlice false with
                | none => intro h; cases h
                | some nicheRes =>
                  dsimp only
                  cases Nat.beq nicheRes.1.bits nicheVal with
                  | true =>
                    dsimp only
                    intro h
                    cases hd : decodeRichFieldSpecs
                        (fun cTy bs => decodeTypedValueRichWithPolicy fuel' layouts richSpecs cTy bs .strictUcg630Ub)
                        bytes nicheFields with
                    | none => rw [hd] at h; cases h
                    | some vals =>
                      rw [hd] at h
                      rw [decodeRichFieldSpecs_mono _ _ (fun cTy bs w hw => ih cTy bs w hw) bytes nicheFields vals hd]
                      exact h
                  | false =>
                    dsimp only
                    intro h
                    cases hd : decodeRichFieldSpecs
                        (fun cTy bs => decodeTypedValueRichWithPolicy fuel' layouts richSpecs cTy bs .strictUcg630Ub)
                        bytes payFields with
                    | none => rw [hd] at h; cases h
                    | some vals =>
                      rw [hd] at h
                      rw [decodeRichFieldSpecs_mono _ _ (fun cTy bs w hw => ih cTy bs w hw) bytes payFields vals hd]
                      exact h
    | ref _ _ => exact id
    | rawPtr _ _ => exact id
    | fnPtr _ _ _ _ => exact id
    | array elemKind n =>
      dsimp only
      cases Nat.beq n 0 with
      | true => exact id
      | false =>
        dsimp only
        have hfb : ∀ (elemSzOpt : Option Nat),
            ((match elemSzOpt with
              | none => none
              | some elemSz =>
                match Nat.beq (length bytes) (Nat.mul elemSz n) with
                | false => none
                | true =>
                  match decodeArrayChunksWith
                      (fun bs => decodeTypedValueRichWithPolicy fuel' layouts richSpecs
                        { kind := elemKind, layoutIdx := unresolvedLayoutIdx layouts } bs .strictUcg630Ub)
                      elemSz n bytes with
                  | some elems => some (.aggregate 0 elems)
                  | none => none) = some v) →
            ((match elemSzOpt with
              | none => none
              | some elemSz =>
                match Nat.beq (length bytes) (Nat.mul elemSz n) with
                | false => none
                | true =>
                  match decodeArrayChunksWith
                      (fun bs => decodeTypedValueRichWithPolicy fuel' layouts richSpecs
                        { kind := elemKind, layoutIdx := unresolvedLayoutIdx layouts } bs .stripProvenance)
                      elemSz n bytes with
                  | some elems => some (.aggregate 0 elems)
                  | none => none) = some v) := by
          intro elemSzOpt
          cases elemSzOpt with
          | none => intro h; cases h
          | some elemSz =>
            dsimp only
            cases Nat.beq (length bytes) (Nat.mul elemSz n) with
            | false => intro h; cases h
            | true =>
              dsimp only
              intro h
              cases hd : decodeArrayChunksWith
                  (fun bs => decodeTypedValueRichWithPolicy fuel' layouts richSpecs
                    { kind := elemKind, layoutIdx := unresolvedLayoutIdx layouts } bs .strictUcg630Ub)
                  elemSz n bytes with
              | none => rw [hd] at h; cases h
              | some elems =>
                rw [hd] at h
                rw [decodeArrayChunksWith_mono _ _ (fun bs w hw => ih _ bs w hw) elemSz n bytes elems hd]
                exact h
        cases LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
        | none => exact hfb _
        | some l =>
          rcases l with ⟨_, _, _, lfields, _, _, lfls, _⟩
          cases lfields with
          | array stride count =>
            cases lfls with
            | cons elemFlIdx _ =>
              dsimp only
              cases Nat.beq (length bytes) (Nat.mul stride.bytes n) with
              | false => intro h; cases h
              | true =>
                dsimp only
                intro h
                cases hd : decodeArrayChunksWith
                    (fun bs => decodeTypedValueRichWithPolicy fuel' layouts richSpecs
                      { kind := elemKind, layoutIdx := elemFlIdx } bs .strictUcg630Ub)
                    stride.bytes n bytes with
                | none => rw [hd] at h; cases h
                | some elems =>
                  rw [hd] at h
                  rw [decodeArrayChunksWith_mono _ _ (fun bs w hw => ih _ bs w hw) stride.bytes n bytes elems hd]
                  exact h
            | nil => exact hfb _
          | _ => exact hfb _
    | tuple ks =>
      cases ks with
      | nil =>
        dsimp only
        exact decodeTypedValueFromBytes_strictUcg630Ub_refines_stripProvenance
          (.succ fuel') layouts ty bytes v
      | cons kHead kTail =>
        dsimp only
        have hseq :
            ((match decodeSeqFieldsWith
                  (fun k bs => decodeTypedValueRichWithPolicy fuel' layouts richSpecs
                    { kind := k, layoutIdx := unresolvedLayoutIdx layouts } bs .strictUcg630Ub)
                  (decodeTypedKindByteSize layouts) (kHead :: kTail) bytes with
              | some vals => some (.aggregate 0 vals)
              | none => none) = some v) →
            ((match decodeSeqFieldsWith
                  (fun k bs => decodeTypedValueRichWithPolicy fuel' layouts richSpecs
                    { kind := k, layoutIdx := unresolvedLayoutIdx layouts } bs .stripProvenance)
                  (decodeTypedKindByteSize layouts) (kHead :: kTail) bytes with
              | some vals => some (.aggregate 0 vals)
              | none => none) = some v) := by
          intro h
          cases hs : decodeSeqFieldsWith
              (fun k bs => decodeTypedValueRichWithPolicy fuel' layouts richSpecs
                { kind := k, layoutIdx := unresolvedLayoutIdx layouts } bs .strictUcg630Ub)
              (decodeTypedKindByteSize layouts) (kHead :: kTail) bytes with
          | none => rw [hs] at h; cases h
          | some vals =>
            rw [hs] at h
            rw [decodeSeqFieldsWith_mono _ _ (fun k bs w hw => ih _ bs w hw) _ _ _ vals hs]
            exact h
        cases Bool.not (isUnresolvedLayoutIdx layouts (normalizeCodecTy ty).layoutIdx) with
        | false => exact hseq
        | true =>
          dsimp only
          cases LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
          | none => exact hseq
          | some l =>
            dsimp only
            cases layoutMatchesAggregateVariant l 0 (length (kHead :: kTail)) with
            | false => exact hseq
            | true =>
              dsimp only
              cases Nat.beq (length bytes) l.size.bytes with
              | false => intro h; cases h
              | true =>
                cases l.fields with
                | arbitrary offsets memIdx =>
                  dsimp only
                  cases Bool.and (Nat.beq (length (kHead :: kTail)) (length offsets))
                      (Nat.beq (length l.fieldLayouts) (length offsets)) with
                  | true =>
                    dsimp only
                    intro h
                    cases hd : decodeTypedKindsAndLayoutsAtOffsets
                        (fun cTy bs => decodeTypedValueRichWithPolicy fuel' layouts richSpecs cTy bs .strictUcg630Ub)
                        layouts bytes offsets (kHead :: kTail) l.fieldLayouts with
                    | none => rw [hd] at h; cases h
                    | some vals =>
                      rw [hd] at h
                      rw [decodeTypedKindsAndLayoutsAtOffsets_mono _ _ (fun cTy bs w hw => ih cTy bs w hw)
                        layouts bytes offsets (kHead :: kTail) l.fieldLayouts vals hd]
                      exact h
                  | false =>
                    dsimp only
                    intro h
                    cases hd : decodeFieldsAtOffsetsWith
                        (fun k bs => decodeTypedValueRichWithPolicy fuel' layouts richSpecs
                          { kind := k, layoutIdx := unresolvedLayoutIdx layouts } bs .strictUcg630Ub)
                        (decodeTypedKindByteSize layouts) bytes offsets (kHead :: kTail) with
                    | none => rw [hd] at h; cases h
                    | some vals =>
                      rw [hd] at h
                      rw [decodeFieldsAtOffsetsWith_mono _ _ (fun k bs w hw => ih _ bs w hw)
                        _ bytes offsets (kHead :: kTail) vals hd]
                      exact h
                | _ => exact hseq
    | _ =>
      dsimp only
      exact decodeTypedValueFromBytes_strictUcg630Ub_refines_stripProvenance
        (.succ fuel') layouts ty bytes v

/-- **Refinement for `evalByteCast`**: `.strictUcg630Ub` refines `.stripProvenance`. -/
theorem evalByteCast_strictUcg630Ub_refines_stripProvenance
    (locals locals' : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem mem' : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) (v : Value)
    (h : evalByteCast locals op targetTy mem localDecls layouts .strictUcg630Ub =
      .ok v locals' mem') :
    evalByteCast locals op targetTy mem localDecls layouts .stripProvenance =
      .ok v locals' mem' := by
  unfold evalByteCast at h ⊢
  revert h
  cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
  | ub => intro h; cases h
  | unsupported => intro h; cases h
  | ok srcVal l' =>
    dsimp only
    cases tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts targetTy) with
    | none => intro h; cases h
    | some dstSize =>
      dsimp only
      cases operandTy localDecls layouts op with
      | some srcTy =>
        dsimp only
        cases resolveByteCastSrcTyAndSize localDecls layouts op srcTy with
        | none => intro h; cases h
        | some srcPair =>
          rcases srcPair with ⟨rSrcTy, srcSize⟩
          dsimp only
          cases Nat.beq srcSize dstSize with
          | false => intro h; cases h
          | true =>
            dsimp only
            cases encodeByteCastSourceBytes layouts rSrcTy srcVal with
            | none => intro h; cases h
            | some bs =>
              dsimp only
              cases Nat.beq (length bs) dstSize with
              | false => intro h; cases h
              | true =>
                dsimp only
                intro h
                cases hd : decodeTypedValueFromBytes defaultCodecFuel layouts
                    (resolveTyWithLocalDecls localDecls layouts targetTy) bs .strictUcg630Ub with
                | none => rw [hd] at h; cases h
                | some v' =>
                  rw [hd] at h
                  rw [decodeTypedValueFromBytes_strictUcg630Ub_refines_stripProvenance _ _ _ _ v' hd]
                  exact h
      | none =>
        dsimp only
        cases encodeUntypedValueToBytes defaultCodecFuel srcVal with
        | none => intro h; cases h
        | some bs =>
          dsimp only
          cases Nat.beq (length bs) dstSize with
          | false => intro h; cases h
          | true =>
            dsimp only
            intro h
            cases hd : decodeTypedValueFromBytes defaultCodecFuel layouts
                (resolveTyWithLocalDecls localDecls layouts targetTy) bs .strictUcg630Ub with
            | none => rw [hd] at h; cases h
            | some v' =>
              rw [hd] at h
              rw [decodeTypedValueFromBytes_strictUcg630Ub_refines_stripProvenance _ _ _ _ v' hd]
              exact h

/-- **Exact cast split for `evalByteCast`**: either `.stripProvenance` and `.strictUcg630Ub`
return the exact same `RvalueEvalResult`, or `.strictUcg630Ub` returns `.ub`. -/
theorem evalByteCast_strip_eq_strict_or_strict_ub
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalByteCast locals op targetTy mem localDecls layouts .stripProvenance =
      evalByteCast locals op targetTy mem localDecls layouts .strictUcg630Ub ∨
    evalByteCast locals op targetTy mem localDecls layouts .strictUcg630Ub = .ub := by
  unfold evalByteCast
  cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
  | ub => exact Or.inl rfl
  | unsupported => exact Or.inl rfl
  | ok srcVal l' =>
    dsimp only
    cases tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts targetTy) with
    | none => exact Or.inl rfl
    | some dstSize =>
      dsimp only
      cases operandTy localDecls layouts op with
      | some srcTy =>
        dsimp only
        cases resolveByteCastSrcTyAndSize localDecls layouts op srcTy with
        | none => exact Or.inl rfl
        | some srcPair =>
          rcases srcPair with ⟨rSrcTy, srcSize⟩
          dsimp only
          cases Nat.beq srcSize dstSize with
          | false => exact Or.inl rfl
          | true =>
            dsimp only
            cases encodeByteCastSourceBytes layouts rSrcTy srcVal with
            | none => exact Or.inl rfl
            | some bs =>
              dsimp only
              cases Nat.beq (length bs) dstSize with
              | false => exact Or.inl rfl
              | true =>
                dsimp only
                cases hd : decodeTypedValueFromBytes defaultCodecFuel layouts
                    (resolveTyWithLocalDecls localDecls layouts targetTy) bs .strictUcg630Ub with
                | none => exact Or.inr rfl
                | some v' =>
                  rw [decodeTypedValueFromBytes_strictUcg630Ub_refines_stripProvenance _ _ _ _ v' hd]
                  exact Or.inl rfl
      | none =>
        dsimp only
        cases encodeUntypedValueToBytes defaultCodecFuel srcVal with
        | none => exact Or.inl rfl
        | some bs =>
          dsimp only
          cases Nat.beq (length bs) dstSize with
          | false => exact Or.inl rfl
          | true =>
            dsimp only
            cases hd : decodeTypedValueFromBytes defaultCodecFuel layouts
                (resolveTyWithLocalDecls localDecls layouts targetTy) bs .strictUcg630Ub with
            | none => exact Or.inr rfl
            | some v' =>
              rw [decodeTypedValueFromBytes_strictUcg630Ub_refines_stripProvenance _ _ _ _ v' hd]
              exact Or.inl rfl

/-- **Refinement & exact cast split for `evalByteCastRichWithPolicy`**. -/
theorem evalByteCastRichWithPolicy_strip_eq_strict_or_strict_ub
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (richSpecs : List (DefPath × RichAdtSpec)) :
    evalByteCastRichWithPolicy locals op targetTy mem localDecls layouts richSpecs .stripProvenance =
      evalByteCastRichWithPolicy locals op targetTy mem localDecls layouts richSpecs .strictUcg630Ub ∨
    evalByteCastRichWithPolicy locals op targetTy mem localDecls layouts richSpecs .strictUcg630Ub = .ub := by
  unfold evalByteCastRichWithPolicy
  cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
  | ub => exact Or.inl rfl
  | unsupported => exact Or.inl rfl
  | ok srcVal l' =>
    dsimp only
    cases richTyByteSize localDecls layouts richSpecs (resolveTyWithLocalDecls localDecls layouts targetTy) with
    | none => exact Or.inl rfl
    | some dstSize =>
      dsimp only
      cases operandTy localDecls layouts op with
      | some srcTy =>
        dsimp only
        cases richTyByteSize localDecls layouts richSpecs (resolveTyWithLocalDecls localDecls layouts srcTy) with
        | none => exact Or.inl rfl
        | some srcSize =>
          dsimp only
          cases Nat.beq srcSize dstSize with
          | false => exact Or.inl rfl
          | true =>
            dsimp only
            cases encodeByteCastSourceBytes layouts (resolveTyWithLocalDecls localDecls layouts srcTy) srcVal with
            | none => exact Or.inl rfl
            | some bs =>
              dsimp only
              cases Nat.beq (length bs) dstSize with
              | false => exact Or.inl rfl
              | true =>
                dsimp only
                cases hd : decodeTypedValueRichWithPolicy defaultCodecFuel layouts richSpecs
                    (resolveTyWithLocalDecls localDecls layouts targetTy) bs .strictUcg630Ub with
                | none => exact Or.inr rfl
                | some v' =>
                  rw [decodeTypedValueRichWithPolicy_strictUcg630Ub_refines_stripProvenance _ _ _ _ _ v' hd]
                  exact Or.inl rfl
      | none =>
        dsimp only
        cases encodeUntypedValueToBytes defaultCodecFuel srcVal with
        | none => exact Or.inl rfl
        | some bs =>
          dsimp only
          cases Nat.beq (length bs) dstSize with
          | false => exact Or.inl rfl
          | true =>
            dsimp only
            cases hd : decodeTypedValueRichWithPolicy defaultCodecFuel layouts richSpecs
                (resolveTyWithLocalDecls localDecls layouts targetTy) bs .strictUcg630Ub with
            | none => exact Or.inr rfl
            | some v' =>
              rw [decodeTypedValueRichWithPolicy_strictUcg630Ub_refines_stripProvenance _ _ _ _ _ v' hd]
              exact Or.inl rfl

theorem evalByteCastRichWithPolicy_strictUcg630Ub_refines_stripProvenance
    (locals locals' : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem mem' : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (richSpecs : List (DefPath × RichAdtSpec)) (v : Value)
    (h : evalByteCastRichWithPolicy locals op targetTy mem localDecls layouts richSpecs .strictUcg630Ub =
      .ok v locals' mem') :
    evalByteCastRichWithPolicy locals op targetTy mem localDecls layouts richSpecs .stripProvenance =
      .ok v locals' mem' := by
  rcases evalByteCastRichWithPolicy_strip_eq_strict_or_strict_ub
      locals op targetTy mem localDecls layouts richSpecs with heq | hub
  · rw [heq, h]
  · rw [h] at hub; cases hub

/-! ### Provenance-free equivalence (`valueHasProv v = false → strict = strip`) -/

private theorem decodeArrayChunksWith_congr_provFree
    (f g : List AbstractByte → Option Value)
    (hcongr : ∀ bs, abstractBytesHaveProv bs = false → f bs = g bs)
    (elemSize : Nat) :
    ∀ count bs, abstractBytesHaveProv bs = false →
      decodeArrayChunksWith f elemSize count bs = decodeArrayChunksWith g elemSize count bs := by
  intro count
  induction count with
  | zero => intro bs _; cases bs <;> rfl
  | succ k ih =>
    intro bs hbs
    unfold decodeArrayChunksWith
    cases Nat.ble elemSize (length bs) with
    | false => rfl
    | true =>
      dsimp only
      rw [hcongr _ (abstractBytesHaveProv_takeAbstractBytes_false elemSize bs hbs),
        ih _ (abstractBytesHaveProv_dropAbstractBytes_false elemSize bs hbs)]

private theorem decodeFieldsAtOffsetsWith_congr_provFree
    (f g : RigidTy → List AbstractByte → Option Value)
    (hcongr : ∀ k bs, abstractBytesHaveProv bs = false → f k bs = g k bs)
    (sizeOfKind : RigidTy → Option Nat) (bytes : List AbstractByte)
    (hbs : abstractBytesHaveProv bytes = false) :
    ∀ offsets ks,
      decodeFieldsAtOffsetsWith f sizeOfKind bytes offsets ks =
        decodeFieldsAtOffsetsWith g sizeOfKind bytes offsets ks := by
  intro offsets
  induction offsets with
  | nil => intro ks; cases ks <;> rfl
  | cons off offRest ih =>
    intro ks
    cases ks with
    | nil => rfl
    | cons k kRest =>
      unfold decodeFieldsAtOffsetsWith
      cases sizeOfKind k with
      | none => rfl
      | some fSize =>
        dsimp only
        cases hsl : sliceAbstractBytes bytes off.bytes fSize with
        | none => rfl
        | some fSlice =>
          dsimp only
          rw [hcongr k fSlice (abstractBytesHaveProv_sliceAbstractBytes_false bytes fSlice off.bytes fSize hbs hsl),
            ih kRest]

private theorem decodeSeqFieldsWith_congr_provFree
    (f g : RigidTy → List AbstractByte → Option Value)
    (hcongr : ∀ k bs, abstractBytesHaveProv bs = false → f k bs = g k bs)
    (sizeOfKind : RigidTy → Option Nat) :
    ∀ ks bytes, abstractBytesHaveProv bytes = false →
      decodeSeqFieldsWith f sizeOfKind ks bytes = decodeSeqFieldsWith g sizeOfKind ks bytes := by
  intro ks
  induction ks with
  | nil => intro bytes _; cases bytes <;> rfl
  | cons k kRest ih =>
    intro bytes hbs
    unfold decodeSeqFieldsWith
    cases sizeOfKind k with
    | none => rfl
    | some fSize =>
      dsimp only
      cases Nat.ble fSize (length bytes) with
      | false => rfl
      | true =>
        dsimp only
        rw [hcongr k _ (abstractBytesHaveProv_takeAbstractBytes_false fSize bytes hbs),
          ih _ (abstractBytesHaveProv_dropAbstractBytes_false fSize bytes hbs)]

private theorem decodeTypedKindsAndLayoutsAtOffsets_congr_provFree
    (f g : Ty → List AbstractByte → Option Value)
    (hcongr : ∀ ty bs, abstractBytesHaveProv bs = false → f ty bs = g ty bs)
    (layouts : LayoutTable) (bytes : List AbstractByte)
    (hbs : abstractBytesHaveProv bytes = false) :
    ∀ offsets ks fls,
      decodeTypedKindsAndLayoutsAtOffsets f layouts bytes offsets ks fls =
        decodeTypedKindsAndLayoutsAtOffsets g layouts bytes offsets ks fls := by
  intro offsets
  induction offsets with
  | nil => intro ks fls; cases ks <;> cases fls <;> rfl
  | cons off offRest ih =>
    intro ks fls
    cases ks with
    | nil => rfl
    | cons k kRest =>
      cases fls with
      | nil => rfl
      | cons fIdx fRest =>
        unfold decodeTypedKindsAndLayoutsAtOffsets
        cases LayoutTable.lookup layouts fIdx with
        | none => rfl
        | some fl =>
          dsimp only
          cases hsl : sliceAbstractBytes bytes off.bytes fl.size.bytes with
          | none => rfl
          | some fSlice =>
            dsimp only
            rw [hcongr _ fSlice (abstractBytesHaveProv_sliceAbstractBytes_false bytes fSlice off.bytes fl.size.bytes hbs hsl),
              ih kRest fRest]

private theorem decodeFieldsByLayoutIdxs_congr_provFree
    (f g : Nat → List AbstractByte → Option Value)
    (hcongr : ∀ fIdx bs, abstractBytesHaveProv bs = false → f fIdx bs = g fIdx bs)
    (layouts : LayoutTable) (bytes : List AbstractByte)
    (hbs : abstractBytesHaveProv bytes = false) :
    ∀ offsets fls,
      decodeFieldsByLayoutIdxs f layouts bytes offsets fls =
        decodeFieldsByLayoutIdxs g layouts bytes offsets fls := by
  intro offsets
  induction offsets with
  | nil => intro fls; cases fls <;> rfl
  | cons off offRest ih =>
    intro fls
    cases fls with
    | nil => rfl
    | cons fIdx fRest =>
      unfold decodeFieldsByLayoutIdxs
      cases LayoutTable.lookup layouts fIdx with
      | none => rfl
      | some fl =>
        dsimp only
        cases hsl : sliceAbstractBytes bytes off.bytes fl.size.bytes with
        | none => rfl
        | some fSlice =>
          dsimp only
          rw [hcongr fIdx fSlice (abstractBytesHaveProv_sliceAbstractBytes_false bytes fSlice off.bytes fl.size.bytes hbs hsl),
            ih fRest]

private theorem decodeRichFieldSpecs_congr_provFree
    (f g : Ty → List AbstractByte → Option Value)
    (hcongr : ∀ ty bs, abstractBytesHaveProv bs = false → f ty bs = g ty bs)
    (bytes : List AbstractByte) (hbs : abstractBytesHaveProv bytes = false) :
    ∀ specs,
      decodeRichFieldSpecs f bytes specs = decodeRichFieldSpecs g bytes specs := by
  intro specs
  induction specs with
  | nil => rfl
  | cons spec rest ih =>
    unfold decodeRichFieldSpecs
    cases hsl : sliceAbstractBytes bytes spec.1 spec.2.1 with
    | none => rfl
    | some fSlice =>
      dsimp only
      rw [hcongr spec.2.2 fSlice (abstractBytesHaveProv_sliceAbstractBytes_false bytes fSlice spec.1 spec.2.1 hbs hsl), ih]

theorem decodeScalarLayoutBytesNoForge_eq_of_provFree
    (sl : ScalarLayout) (bs : List AbstractByte)
    (hbs : abstractBytesHaveProv bs = false) :
    decodeScalarLayoutBytesNoForge sl bs .strictUcg630Ub =
      decodeScalarLayoutBytesNoForge sl bs .stripProvenance := by
  unfold decodeScalarLayoutBytesNoForge
  cases scalarLayoutByteWidth sl with
  | none => rfl
  | some sz =>
    dsimp only
    cases Nat.beq (length bs) sz with
    | false => rfl
    | true =>
      dsimp only
      cases sl with
      | initialized pk vr =>
        cases pk with
        | pointer _ => rfl
        | int _ _ => dsimp only; rw [hbs]
        | float _ => dsimp only; rw [hbs]
      | union pk =>
        cases pk with
        | pointer _ => rfl
        | int _ _ => dsimp only; rw [hbs]
        | float _ => dsimp only; rw [hbs]

/-- On provenance-free bytes, `decodeTypedValueFromBytes` is policy-independent. -/
theorem decodeTypedValueFromBytes_eq_of_provFree
    (fuel : Nat) (layouts : LayoutTable) (ty : Ty) (bytes : List AbstractByte)
    (hbs : abstractBytesHaveProv bytes = false) :
    decodeTypedValueFromBytes fuel layouts ty bytes .strictUcg630Ub =
      decodeTypedValueFromBytes fuel layouts ty bytes .stripProvenance := by
  induction fuel generalizing ty bytes with
  | zero => rfl
  | succ fuel' ih =>
    unfold decodeTypedValueFromBytes
    dsimp only
    cases (normalizeCodecTy ty).kind with
    | array elemKind n =>
      dsimp only
      cases Nat.beq n 0 with
      | true => rfl
      | false =>
        dsimp only
        have hfb : ∀ (elemSzOpt : Option Nat),
            (match elemSzOpt with
             | none => none
             | some elemSz =>
               match Nat.beq (length bytes) (Nat.mul elemSz n) with
               | false => none
               | true =>
                 match decodeArrayChunksWith
                     (fun bs => decodeTypedValueFromBytes fuel' layouts
                       { kind := elemKind, layoutIdx := 0 } bs .strictUcg630Ub)
                     elemSz n bytes with
                 | some elems => some (Value.aggregate 0 elems)
                 | none => none) =
            (match elemSzOpt with
             | none => none
             | some elemSz =>
               match Nat.beq (length bytes) (Nat.mul elemSz n) with
               | false => none
               | true =>
                 match decodeArrayChunksWith
                     (fun bs => decodeTypedValueFromBytes fuel' layouts
                       { kind := elemKind, layoutIdx := 0 } bs .stripProvenance)
                     elemSz n bytes with
                 | some elems => some (Value.aggregate 0 elems)
                 | none => none) := by
          intro elemSzOpt
          cases elemSzOpt with
          | none => rfl
          | some elemSz =>
            dsimp only
            cases Nat.beq (length bytes) (Nat.mul elemSz n) with
            | false => rfl
            | true =>
              dsimp only
              rw [decodeArrayChunksWith_congr_provFree _ _ (fun bs hb => ih _ bs hb) elemSz n bytes hbs]
        cases LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
        | none => exact hfb _
        | some l =>
          rcases l with ⟨_, _, _, lfields, _, _, lfls, _⟩
          cases lfields with
          | array stride count =>
            cases lfls with
            | cons elemFlIdx _ =>
              dsimp only
              cases Nat.beq (length bytes) (Nat.mul stride.bytes n) with
              | false => rfl
              | true =>
                dsimp only
                rw [decodeArrayChunksWith_congr_provFree _ _ (fun bs hb => ih _ bs hb) stride.bytes n bytes hbs]
            | nil => exact hfb _
          | _ => exact hfb _
    | tuple ks =>
      cases ks with
      | nil => rfl
      | cons kHead kTail =>
        dsimp only
        have hseq := decodeSeqFieldsWith_congr_provFree
          (fun k bs => decodeTypedValueFromBytes fuel' layouts
            { kind := k, layoutIdx := unresolvedLayoutIdx layouts } bs .strictUcg630Ub)
          (fun k bs => decodeTypedValueFromBytes fuel' layouts
            { kind := k, layoutIdx := unresolvedLayoutIdx layouts } bs .stripProvenance)
          (fun k bs hb => ih _ bs hb) (decodeTypedKindByteSize layouts) (kHead :: kTail) bytes hbs
        cases Bool.not (isUnresolvedLayoutIdx layouts (normalizeCodecTy ty).layoutIdx) with
        | false => dsimp only; rw [hseq]
        | true =>
          dsimp only
          cases LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
          | none => dsimp only; rw [hseq]
          | some l =>
            dsimp only
            cases layoutMatchesAggregateVariant l 0 (length (kHead :: kTail)) with
            | false => dsimp only; rw [hseq]
            | true =>
              dsimp only
              cases Nat.beq (length bytes) l.size.bytes with
              | false => rfl
              | true =>
                cases l.fields with
                | arbitrary offsets _ =>
                  dsimp only
                  cases Bool.and (Nat.beq (length (kHead :: kTail)) (length offsets))
                      (Nat.beq (length l.fieldLayouts) (length offsets)) with
                  | true =>
                    dsimp only
                    rw [decodeTypedKindsAndLayoutsAtOffsets_congr_provFree _ _ (fun cTy bs hb => ih cTy bs hb)
                      layouts bytes hbs offsets (kHead :: kTail) l.fieldLayouts]
                  | false =>
                    dsimp only
                    rw [decodeFieldsAtOffsetsWith_congr_provFree _ _ (fun k bs hb => ih _ bs hb)
                      _ bytes hbs offsets (kHead :: kTail)]
                | _ => dsimp only; rw [hseq]
    | adt _ _ =>
      dsimp only
      cases LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
      | none => rfl
      | some l =>
        dsimp only
        cases Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
        | true => rfl
        | false =>
          dsimp only
          cases l.variants with
          | empty => rfl
          | multiple tag _ _ =>
            dsimp only
            cases Bool.or (scalarLayoutIsPointer tag) (backendReprHasPointer l.backendRepr) with
            | true => rfl
            | false => dsimp only; rw [hbs]
          | single varIdx =>
            cases varIdx <;>
            cases l.fields with
            | union _ => rfl
            | primitive =>
              simp only
              cases Nat.beq l.size.bytes 0 with
              | true => rfl
              | false =>
                dsimp only
                cases l.backendRepr with
                | scalar s0 => dsimp only; exact decodeScalarLayoutBytesNoForge_eq_of_provFree s0 bytes hbs
                | _ => dsimp only; rw [hbs]
            | array stride count =>
              simp only
              cases Nat.beq count 0 with
              | true => rfl
              | false =>
                dsimp only
                cases l.fieldLayouts with
                | cons elemFlIdx _ =>
                  dsimp only
                  rw [decodeArrayChunksWith_congr_provFree _ _ (fun bs hb => ih _ bs hb) stride.bytes count bytes hbs]
                | nil => dsimp only; rw [hbs]
            | arbitrary offsets _ =>
              cases offsets with
              | nil => rfl
              | cons off0 offTail =>
                simp only
                cases Nat.beq (length l.fieldLayouts) (length (off0 :: offTail)) with
                | true =>
                  dsimp only
                  rw [decodeFieldsByLayoutIdxs_congr_provFree _ _ (fun fIdx bs hb => ih _ bs hb)
                    layouts bytes hbs (off0 :: offTail) l.fieldLayouts]
                | false =>
                  dsimp only
                  cases offTail with
                  | nil =>
                    cases l.backendRepr with
                    | scalar s0 =>
                      dsimp only
                      cases scalarLayoutByteWidth s0 with
                      | none => rfl
                      | some sz0 =>
                        dsimp only
                        cases hsl0 : sliceAbstractBytes bytes off0.bytes sz0 with
                        | none => rfl
                        | some slice0 =>
                          dsimp only
                          rw [decodeScalarLayoutBytesNoForge_eq_of_provFree s0 slice0
                            (abstractBytesHaveProv_sliceAbstractBytes_false bytes slice0 off0.bytes sz0 hbs hsl0)]
                    | _ => dsimp only; rw [hbs]
                  | cons off1 offTail2 =>
                    cases offTail2 with
                    | nil =>
                      cases l.backendRepr with
                      | scalarPair s0 s1 =>
                        dsimp only
                        cases scalarLayoutByteWidth s0 with
                        | none => rfl
                        | some sz0 =>
                          cases scalarLayoutByteWidth s1 with
                          | none => rfl
                          | some sz1 =>
                            dsimp only
                            cases hsl0 : sliceAbstractBytes bytes off0.bytes sz0 with
                            | none => rfl
                            | some slice0 =>
                              cases hsl1 : sliceAbstractBytes bytes off1.bytes sz1 with
                              | none => rfl
                              | some slice1 =>
                                dsimp only
                                rw [decodeScalarLayoutBytesNoForge_eq_of_provFree s0 slice0
                                    (abstractBytesHaveProv_sliceAbstractBytes_false bytes slice0 off0.bytes sz0 hbs hsl0),
                                  decodeScalarLayoutBytesNoForge_eq_of_provFree s1 slice1
                                    (abstractBytesHaveProv_sliceAbstractBytes_false bytes slice1 off1.bytes sz1 hbs hsl1)]
                      | _ => dsimp only; rw [hbs]
                    | cons _ _ => dsimp only; rw [hbs]
    | uint w => cases w <;> (dsimp only; rw [hbs])
    | int w => cases w <;> (dsimp only; rw [hbs])
    | bool => dsimp only; rw [hbs]
    | char => dsimp only; rw [hbs]
    | _ => rfl

/-- On provenance-free bytes, `decodeTypedValueRichWithPolicy` is policy-independent. -/
theorem decodeTypedValueRichWithPolicy_eq_of_provFree
    (fuel : Nat) (layouts : LayoutTable) (richSpecs : List (DefPath × RichAdtSpec))
    (ty : Ty) (bytes : List AbstractByte)
    (hbs : abstractBytesHaveProv bytes = false) :
    decodeTypedValueRichWithPolicy fuel layouts richSpecs ty bytes .strictUcg630Ub =
      decodeTypedValueRichWithPolicy fuel layouts richSpecs ty bytes .stripProvenance := by
  induction fuel generalizing ty bytes with
  | zero => rfl
  | succ fuel' ih =>
    unfold decodeTypedValueRichWithPolicy
    dsimp only
    cases (normalizeCodecTy ty).kind with
    | adt defPath _ =>
      dsimp only
      cases lookupRichAdtSpec defPath richSpecs with
      | none =>
        dsimp only
        exact decodeTypedValueFromBytes_eq_of_provFree (.succ fuel') layouts ty bytes hbs
      | some spec =>
        cases spec with
        | structFields varIdx totalBytes fields =>
          dsimp only
          cases Nat.beq (length bytes) totalBytes with
          | false => rfl
          | true =>
            dsimp only
            rw [decodeRichFieldSpecs_congr_provFree _ _ (fun cTy bs hb => ih cTy bs hb) bytes hbs fields]
        | taggedEnum totalBytes tagOff tagBytes variants =>
          dsimp only
          cases Nat.beq (length bytes) totalBytes with
          | false => rfl
          | true =>
            dsimp only
            cases hsl : sliceAbstractBytes bytes tagOff tagBytes with
            | none => rfl
            | some tagSlice =>
              dsimp only [policyRejectsProv]
              rw [abstractBytesHaveProv_sliceAbstractBytes_false bytes tagSlice tagOff tagBytes hbs hsl]
              dsimp only
              cases decodeScalarBytes tagSlice false with
              | none => rfl
              | some tagRes =>
                dsimp only
                cases findRichTaggedVariant tagRes.1.bits variants with
                | none => rfl
                | some varEntry =>
                  dsimp only
                  rw [decodeRichFieldSpecs_congr_provFree _ _ (fun cTy bs hb => ih cTy bs hb) bytes hbs varEntry.2]
        | nichePointerEnum totalBytes nicheOff nicheBytes noneVar noneFields someVar someFields =>
          dsimp only
          cases Nat.beq (length bytes) totalBytes with
          | false => rfl
          | true =>
            dsimp only
            cases hsl : sliceAbstractBytes bytes nicheOff nicheBytes with
            | none => rfl
            | some nicheSlice =>
              dsimp only
              cases abstractBytesUniformProv nicheSlice with
              | true =>
                dsimp only
                rw [decodeRichFieldSpecs_congr_provFree _ _ (fun cTy bs hb => ih cTy bs hb) bytes hbs someFields]
              | false =>
                dsimp only [policyRejectsProv]
                rw [abstractBytesHaveProv_sliceAbstractBytes_false bytes nicheSlice nicheOff nicheBytes hbs hsl]
                dsimp only
                cases decodeScalarBytes nicheSlice false with
                | none => rfl
                | some nicheRes =>
                  dsimp only
                  cases Nat.beq nicheRes.1.bits 0 with
                  | false => rfl
                  | true =>
                    dsimp only
                    rw [decodeRichFieldSpecs_congr_provFree _ _ (fun cTy bs hb => ih cTy bs hb) bytes hbs noneFields]
        | nicheScalarEnum totalBytes nicheOff nicheBytes nicheVal nicheVar nicheFields payVar payFields =>
          dsimp only
          cases Nat.beq (length bytes) totalBytes with
          | false => rfl
          | true =>
            dsimp only
            cases hsl : sliceAbstractBytes bytes nicheOff nicheBytes with
            | none => rfl
            | some nicheSlice =>
              dsimp only [policyRejectsProv]
              rw [abstractBytesHaveProv_sliceAbstractBytes_false bytes nicheSlice nicheOff nicheBytes hbs hsl]
              dsimp only
              cases decodeScalarBytes nicheSlice false with
              | none => rfl
              | some nicheRes =>
                dsimp only
                cases Nat.beq nicheRes.1.bits nicheVal with
                | true =>
                  dsimp only
                  rw [decodeRichFieldSpecs_congr_provFree _ _ (fun cTy bs hb => ih cTy bs hb) bytes hbs nicheFields]
                | false =>
                  dsimp only
                  rw [decodeRichFieldSpecs_congr_provFree _ _ (fun cTy bs hb => ih cTy bs hb) bytes hbs payFields]
    | ref _ _ => rfl
    | rawPtr _ _ => rfl
    | fnPtr _ _ _ _ => rfl
    | array elemKind n =>
      dsimp only
      cases Nat.beq n 0 with
      | true => rfl
      | false =>
        dsimp only
        have hfb : ∀ (elemSzOpt : Option Nat),
            (match elemSzOpt with
             | none => none
             | some elemSz =>
               match Nat.beq (length bytes) (Nat.mul elemSz n) with
               | false => none
               | true =>
                 match decodeArrayChunksWith
                     (fun bs => decodeTypedValueRichWithPolicy fuel' layouts richSpecs
                       { kind := elemKind, layoutIdx := unresolvedLayoutIdx layouts } bs .strictUcg630Ub)
                     elemSz n bytes with
                 | some elems => some (Value.aggregate 0 elems)
                 | none => none) =
            (match elemSzOpt with
             | none => none
             | some elemSz =>
               match Nat.beq (length bytes) (Nat.mul elemSz n) with
               | false => none
               | true =>
                 match decodeArrayChunksWith
                     (fun bs => decodeTypedValueRichWithPolicy fuel' layouts richSpecs
                       { kind := elemKind, layoutIdx := unresolvedLayoutIdx layouts } bs .stripProvenance)
                     elemSz n bytes with
                 | some elems => some (Value.aggregate 0 elems)
                 | none => none) := by
          intro elemSzOpt
          cases elemSzOpt with
          | none => rfl
          | some elemSz =>
            dsimp only
            cases Nat.beq (length bytes) (Nat.mul elemSz n) with
            | false => rfl
            | true =>
              dsimp only
              rw [decodeArrayChunksWith_congr_provFree _ _ (fun bs hb => ih _ bs hb) elemSz n bytes hbs]
        cases LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
        | none => exact hfb _
        | some l =>
          rcases l with ⟨_, _, _, lfields, _, _, lfls, _⟩
          cases lfields with
          | array stride count =>
            cases lfls with
            | cons elemFlIdx _ =>
              dsimp only
              cases Nat.beq (length bytes) (Nat.mul stride.bytes n) with
              | false => rfl
              | true =>
                dsimp only
                rw [decodeArrayChunksWith_congr_provFree _ _ (fun bs hb => ih _ bs hb) stride.bytes n bytes hbs]
            | nil => exact hfb _
          | _ => exact hfb _
    | tuple ks =>
      cases ks with
      | nil =>
        dsimp only
        exact decodeTypedValueFromBytes_eq_of_provFree (.succ fuel') layouts ty bytes hbs
      | cons kHead kTail =>
        dsimp only
        have hseq := decodeSeqFieldsWith_congr_provFree
          (fun k bs => decodeTypedValueRichWithPolicy fuel' layouts richSpecs
            { kind := k, layoutIdx := unresolvedLayoutIdx layouts } bs .strictUcg630Ub)
          (fun k bs => decodeTypedValueRichWithPolicy fuel' layouts richSpecs
            { kind := k, layoutIdx := unresolvedLayoutIdx layouts } bs .stripProvenance)
          (fun k bs hb => ih _ bs hb) (decodeTypedKindByteSize layouts) (kHead :: kTail) bytes hbs
        cases Bool.not (isUnresolvedLayoutIdx layouts (normalizeCodecTy ty).layoutIdx) with
        | false => dsimp only; rw [hseq]
        | true =>
          dsimp only
          cases LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
          | none => dsimp only; rw [hseq]
          | some l =>
            dsimp only
            cases layoutMatchesAggregateVariant l 0 (length (kHead :: kTail)) with
            | false => dsimp only; rw [hseq]
            | true =>
              dsimp only
              cases Nat.beq (length bytes) l.size.bytes with
              | false => rfl
              | true =>
                cases l.fields with
                | arbitrary offsets _ =>
                  dsimp only
                  cases Bool.and (Nat.beq (length (kHead :: kTail)) (length offsets))
                      (Nat.beq (length l.fieldLayouts) (length offsets)) with
                  | true =>
                    dsimp only
                    rw [decodeTypedKindsAndLayoutsAtOffsets_congr_provFree _ _ (fun cTy bs hb => ih cTy bs hb)
                      layouts bytes hbs offsets (kHead :: kTail) l.fieldLayouts]
                  | false =>
                    dsimp only
                    rw [decodeFieldsAtOffsetsWith_congr_provFree _ _ (fun k bs hb => ih _ bs hb)
                      _ bytes hbs offsets (kHead :: kTail)]
                | _ => dsimp only; rw [hseq]
    | _ =>
      dsimp only
      exact decodeTypedValueFromBytes_eq_of_provFree (.succ fuel') layouts ty bytes hbs

/-! ### Encoding provenance-free values produces provenance-free bytes -/

private theorem abstractBytesHaveProv_encodeLittleEndianBytes_none (bits n : Nat) :
    abstractBytesHaveProv (encodeLittleEndianBytes bits n .none) = false := by
  induction n generalizing bits with
  | zero => rfl
  | succ k ih => exact ih (Nat.div bits 256)

private theorem abstractBytesHaveProv_encodeScalarBytes_none (sv : ScalarVal) (bs : List AbstractByte)
    (h : encodeScalarBytes sv .none = .some bs) :
    abstractBytesHaveProv bs = false := by
  unfold encodeScalarBytes at h
  cases hz : Nat.beq sv.sizeBytes 0 with
  | true => rw [hz] at h; cases h
  | false =>
    rw [hz] at h
    injection h with h
    rw [← h]
    exact abstractBytesHaveProv_encodeLittleEndianBytes_none sv.bits sv.sizeBytes

private theorem abstractBytesHaveProv_replicateUninitBytes (n : Nat) :
    abstractBytesHaveProv (replicateUninitBytes n) = false := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

private theorem abstractBytesHaveProv_appendAbstractBytes (xs ys : List AbstractByte) :
    abstractBytesHaveProv (appendAbstractBytes xs ys) =
      Bool.or (abstractBytesHaveProv xs) (abstractBytesHaveProv ys) := by
  induction xs with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | uninit => exact ih
    | init byte prov =>
      cases prov with
      | none => exact ih
      | some p => rfl

private theorem abstractBytesHaveProv_writeAbstractBytesAt
    (buf patch out : List AbstractByte) (off : Nat)
    (hbuf : abstractBytesHaveProv buf = false)
    (hpatch : abstractBytesHaveProv patch = false)
    (hw : writeAbstractBytesAt buf off patch = .some out) :
    abstractBytesHaveProv out = false := by
  induction off generalizing buf patch out with
  | zero =>
    induction patch generalizing buf out with
    | nil =>
      unfold writeAbstractBytesAt at hw
      injection hw with hw
      rw [← hw]; exact hbuf
    | cons p pRest ihp =>
      cases buf with
      | nil => cases hw
      | cons b bRest =>
        unfold writeAbstractBytesAt at hw
        cases hrec : writeAbstractBytesAt bRest 0 pRest with
        | none => rw [hrec] at hw; cases hw
        | some tail' =>
          rw [hrec] at hw
          injection hw with hw
          rw [← hw]
          have hbRest : abstractBytesHaveProv bRest = false := by
            cases b with
            | uninit => exact hbuf
            | init _ prov => cases prov with | none => exact hbuf | some _ => cases hbuf
          cases p with
          | uninit => exact ihp bRest tail' hbRest hpatch hrec
          | init _ prov =>
            cases prov with
            | none => exact ihp bRest tail' hbRest hpatch hrec
            | some _ => cases hpatch
  | succ off' iho =>
    cases patch with
    | nil =>
      unfold writeAbstractBytesAt at hw
      injection hw with hw; rw [← hw]; exact hbuf
    | cons p pRest =>
      cases buf with
      | nil => cases hw
      | cons b bRest =>
        unfold writeAbstractBytesAt at hw
        cases hrec : writeAbstractBytesAt bRest off' (p :: pRest) with
        | none => rw [hrec] at hw; cases hw
        | some tail' =>
          rw [hrec] at hw
          injection hw with hw
          rw [← hw]
          cases b with
          | uninit => exact iho bRest (p :: pRest) tail' hbuf hpatch hrec
          | init _ prov =>
            cases prov with
            | none => exact iho bRest (p :: pRest) tail' hbuf hpatch hrec
            | some _ => cases hbuf

private theorem abstractBytesHaveProv_mergeMaskedAbstractBytes
    (a b : List AbstractByte) (am bm : List Bool) (out : List AbstractByte × List Bool)
    (ha : abstractBytesHaveProv a = false) (hb : abstractBytesHaveProv b = false)
    (hm : mergeMaskedAbstractBytes a am b bm = .some out) :
    abstractBytesHaveProv out.1 = false := by
  induction b generalizing a am bm out with
  | nil =>
    unfold mergeMaskedAbstractBytes at hm
    injection hm with hm
    rw [← hm]; exact ha
  | cons bHead bRest ih =>
    cases a with
    | nil => cases hm
    | cons aHead aRest =>
      cases am with
      | nil => cases hm
      | cons amHead amRest =>
        unfold mergeMaskedAbstractBytes at hm
        dsimp only at hm
        have haRest : abstractBytesHaveProv aRest = false := by
          cases aHead with
          | uninit => exact ha
          | init _ prov => cases prov with | none => exact ha | some _ => cases ha
        have hbRest : abstractBytesHaveProv bRest = false := by
          cases bHead with
          | uninit => exact hb
          | init _ prov => cases prov with | none => exact hb | some _ => cases hb
        have hstep : ∀ (bm0 : Bool) (bmRest : List Bool),
            (match mergeMaskedAbstractBytes aRest amRest bRest bmRest with
             | none => none
             | some (tailB, tailM) =>
               match (match (generalizing := false) bHead with | .init _ _ => true | .uninit => bm0) with
               | false => some (aHead :: tailB, amHead :: tailM)
               | true =>
                 match (generalizing := false) amHead with
                 | false => some (bHead :: tailB, true :: tailM)
                 | true =>
                   match abstractByteEq aHead bHead with
                   | true => some (aHead :: tailB, true :: tailM)
                   | false => none) = some out →
            abstractBytesHaveProv out.1 = false := by
          intro bm0 bmRest hm'
          cases hrec : mergeMaskedAbstractBytes aRest amRest bRest bmRest with
          | none => rw [hrec] at hm'; cases hm'
          | some tail =>
            rcases tail with ⟨tailB, tailM⟩
            rw [hrec] at hm'
            dsimp only at hm'
            have htail : abstractBytesHaveProv tailB = false :=
              ih aRest amRest bmRest (tailB, tailM) haRest hbRest hrec
            have heff : ∀ (eff : Bool),
                (match eff with
                 | false => some (aHead :: tailB, amHead :: tailM)
                 | true =>
                   match (generalizing := false) amHead with
                   | false => some (bHead :: tailB, true :: tailM)
                   | true =>
                     match abstractByteEq aHead bHead with
                     | true => some (aHead :: tailB, true :: tailM)
                     | false => none) = some out →
                abstractBytesHaveProv out.1 = false := by
              intro eff
              cases eff with
              | false =>
                intro hm''
                injection hm'' with hm''; subst hm''
                cases aHead with
                | uninit => exact htail
                | init _ prov => cases prov with | none => exact htail | some _ => cases ha
              | true =>
                cases amHead with
                | false =>
                  intro hm''
                  injection hm'' with hm''; subst hm''
                  cases bHead with
                  | uninit => exact htail
                  | init _ prov => cases prov with | none => exact htail | some _ => cases hb
                | true =>
                  intro hm''
                  cases heq : abstractByteEq aHead bHead with
                  | false => rw [heq] at hm''; cases hm''
                  | true =>
                    rw [heq] at hm''; dsimp only at hm''
                    injection hm'' with hm''; subst hm''
                    cases aHead with
                    | uninit => exact htail
                    | init _ prov => cases prov with | none => exact htail | some _ => cases ha
            exact heff _ hm'
        cases bm with
        | nil => exact hstep true .nil hm
        | cons m mRest => exact hstep m mRest hm

private theorem abstractBytesHaveProv_overlayRawAbstractByteVals
    (vs : List Value) (buf out : List AbstractByte)
    (hvs : valueListHasProv vs = false)
    (hbuf : abstractBytesHaveProv buf = false)
    (ho : overlayRawAbstractByteVals vs buf = .some out) :
    abstractBytesHaveProv out = false := by
  induction vs generalizing buf out with
  | nil =>
    unfold overlayRawAbstractByteVals at ho
    injection ho with ho; rw [← ho]; exact hbuf
  | cons v vRest ih =>
    cases buf with
    | nil => cases ho
    | cons bHead bRest =>
      have hv : valueHasProv v = false := by
        unfold valueListHasProv at hvs
        cases h1 : valueHasProv v with
        | false => rfl
        | true => rw [h1] at hvs; cases hvs
      have hvRest : valueListHasProv vRest = false := by
        unfold valueListHasProv at hvs
        rw [hv] at hvs; exact hvs
      have hbRest : abstractBytesHaveProv bRest = false := by
        cases bHead with
        | uninit => exact hbuf
        | init _ prov => cases prov with | none => exact hbuf | some _ => cases hbuf
      cases v with
      | ptr _ _ => cases hv
      | scalar sc =>
        cases sc with
        | mk bits sz =>
          cases sz with
          | zero =>
            cases bits with
            | zero =>
              unfold overlayRawAbstractByteVals at ho
              simp only at ho
              cases hrec : overlayRawAbstractByteVals vRest bRest with
              | none => rw [hrec] at ho; cases ho
              | some tail =>
                rw [hrec] at ho; dsimp only at ho; injection ho with ho; subst ho
                exact ih bRest tail hvRest hbRest hrec
            | succ _ => cases ho
          | succ sz' =>
            cases sz' with
            | zero =>
              unfold overlayRawAbstractByteVals at ho
              simp only at ho
              cases hrec : overlayRawAbstractByteVals vRest bRest with
              | none => rw [hrec] at ho; cases ho
              | some tail =>
                rw [hrec] at ho; dsimp only at ho; injection ho with ho; subst ho
                exact ih bRest tail hvRest hbRest hrec
            | succ _ => cases bits <;> cases ho
      | unit => cases ho
      | uninit => cases ho
      | aggregate _ _ => cases ho

private theorem valueListHasProv_splitUnionTypedAndOverlay
    (count : Nat) (fieldVals : List Value) (res : List Value × Option (List Value))
    (hvs : valueListHasProv fieldVals = false)
    (hsp : splitUnionTypedAndOverlay count fieldVals = .some res) :
    valueListHasProv res.1 = false ∧
    ∀ rawVals, res.2 = .some rawVals → valueListHasProv rawVals = false := by
  induction count generalizing fieldVals res with
  | zero =>
    cases fieldVals with
    | nil =>
      unfold splitUnionTypedAndOverlay at hsp
      injection hsp with hsp; rw [← hsp]
      exact ⟨rfl, fun _ h => by cases h⟩
    | cons v rest =>
      cases v with
      | aggregate varIdx rawVals =>
        cases varIdx with
        | zero =>
          cases rest with
          | nil =>
            unfold splitUnionTypedAndOverlay at hsp
            injection hsp with hsp; rw [← hsp]
            refine ⟨rfl, fun rv hrv => ?_⟩
            injection hrv with hrv; rw [← hrv]
            simp only [valueListHasProv, valueHasProv, Bool.or_false] at hvs
            exact hvs
          | cons _ _ => cases hsp
        | succ _ => cases hsp
      | _ => cases hsp
  | succ k ih =>
    cases fieldVals with
    | nil =>
      unfold splitUnionTypedAndOverlay at hsp
      injection hsp with hsp; rw [← hsp]
      exact ⟨rfl, fun _ h => by cases h⟩
    | cons v rest =>
      have hv : valueHasProv v = false := by
        unfold valueListHasProv at hvs
        cases h1 : valueHasProv v with
        | false => rfl
        | true => rw [h1] at hvs; cases hvs
      have hrest : valueListHasProv rest = false := by
        unfold valueListHasProv at hvs; rw [hv] at hvs; exact hvs
      unfold splitUnionTypedAndOverlay at hsp
      cases hrec : splitUnionTypedAndOverlay k rest with
      | none => rw [hrec] at hsp; cases hsp
      | some sub =>
        rcases sub with ⟨typedVals, overlayOpt⟩
        rw [hrec] at hsp; dsimp only at hsp
        injection hsp with hsp; subst hsp
        have hsub := ih rest (typedVals, overlayOpt) hrest hrec
        refine ⟨?_, hsub.2⟩
        unfold valueListHasProv; rw [hv, hsub.1, Bool.or_false]

private theorem abstractBytesHaveProv_encodeUntypedValueToBytes
    (fuel : Nat) (v : Value) (bs : List AbstractByte)
    (hv : valueHasProv v = false)
    (henc : encodeUntypedValueToBytes fuel v = .some bs) :
    abstractBytesHaveProv bs = false := by
  induction fuel generalizing v bs with
  | zero => unfold encodeUntypedValueToBytes at henc; cases henc
  | succ fuel' ih =>
    cases v with
    | unit =>
      unfold encodeUntypedValueToBytes at henc
      injection henc with henc; subst henc; rfl
    | uninit => unfold encodeUntypedValueToBytes at henc; cases henc
    | ptr _ _ => cases hv
    | scalar sv =>
      unfold encodeUntypedValueToBytes at henc
      exact abstractBytesHaveProv_encodeScalarBytes_none sv bs henc
    | aggregate varIdx fields =>
      unfold valueHasProv at hv
      induction fields generalizing bs with
      | nil =>
        change Option.some .nil = Option.some bs at henc
        injection henc with henc; subst henc; rfl
      | cons f fs ihf =>
        have hf : valueHasProv f = false := by
          unfold valueListHasProv at hv
          cases h1 : valueHasProv f with
          | false => rfl
          | true => rw [h1] at hv; cases hv
        have hfs : valueListHasProv fs = false := by
          unfold valueListHasProv at hv; rw [hf] at hv; exact hv
        change (match encodeUntypedValueToBytes fuel' f,
            encodeUntypedValueToBytes (fuel' + 1) (.aggregate varIdx fs) with
          | some b1, some b2 => some (appendAbstractBytes b1 b2)
          | _, _ => none) = some bs at henc
        cases h1 : encodeUntypedValueToBytes fuel' f with
        | none => rw [h1] at henc; cases henc
        | some b1 =>
          cases h2 : encodeUntypedValueToBytes (fuel' + 1) (.aggregate varIdx fs) with
          | none => rw [h1, h2] at henc; cases henc
          | some b2 =>
            rw [h1, h2] at henc
            dsimp only at henc
            injection henc with henc; subst henc
            rw [abstractBytesHaveProv_appendAbstractBytes,
              ih f b1 hf h1, ihf b2 h2 hfs, Bool.or_false]

private theorem abstractBytesHaveProv_encodeListWith
    (enc : Value → Option (List AbstractByte))
    (henc : ∀ v bs, valueHasProv v = false → enc v = .some bs → abstractBytesHaveProv bs = false)
    (sz : Nat) :
    ∀ vs bs, valueListHasProv vs = false → encodeListWith enc sz vs = .some bs →
      abstractBytesHaveProv bs = false := by
  intro vs
  induction vs with
  | nil => intro bs _ h; injection h with h; subst h; rfl
  | cons v rest ih =>
    intro bs hvs h
    have hv : valueHasProv v = false := by
      unfold valueListHasProv at hvs
      cases h1 : valueHasProv v with | false => rfl | true => rw [h1] at hvs; cases hvs
    have hrest : valueListHasProv rest = false := by
      unfold valueListHasProv at hvs; rw [hv] at hvs; exact hvs
    unfold encodeListWith at h
    cases h1 : enc v with
    | none => rw [h1] at h; cases h
    | some b1 =>
      rw [h1] at h
      dsimp only at h
      cases hlen : Nat.beq (length b1) sz with
      | false => rw [hlen] at h; cases h
      | true =>
        rw [hlen] at h
        dsimp only at h
        cases h2 : encodeListWith enc sz rest with
        | none => rw [h2] at h; cases h
        | some b2 =>
          rw [h2] at h; dsimp only at h
          injection h with h; subst h
          rw [abstractBytesHaveProv_appendAbstractBytes, henc v b1 hv h1, ih b2 hrest h2, Bool.or_false]

private theorem abstractBytesHaveProv_encodeFieldsAtOffsetsWith
    (encT : RigidTy → Value → Option (List AbstractByte))
    (encF : Value → Option (List AbstractByte))
    (hT : ∀ k v bs, valueHasProv v = false → encT k v = .some bs → abstractBytesHaveProv bs = false)
    (hF : ∀ v bs, valueHasProv v = false → encF v = .some bs → abstractBytesHaveProv bs = false) :
    ∀ offsets kinds vals buf out,
      valueListHasProv vals = false →
      abstractBytesHaveProv buf = false →
      encodeFieldsAtOffsetsWith encT encF offsets kinds vals buf = .some out →
      abstractBytesHaveProv out = false := by
  intro offsets
  induction offsets with
  | nil =>
    intro kinds vals buf out _ hbuf h
    cases vals with
    | nil => unfold encodeFieldsAtOffsetsWith at h; injection h with h; rw [← h]; exact hbuf
    | cons _ _ => cases h
  | cons off offRest ih =>
    intro kinds vals buf out hvals hbuf h
    cases vals with
    | nil => cases h
    | cons v vRest =>
      have hv : valueHasProv v = false := by
        unfold valueListHasProv at hvals
        cases h1 : valueHasProv v with | false => rfl | true => rw [h1] at hvals; cases hvals
      have hvRest : valueListHasProv vRest = false := by
        unfold valueListHasProv at hvals; rw [hv] at hvals; exact hvals
      unfold encodeFieldsAtOffsetsWith at h
      cases kinds with
      | nil =>
        dsimp only at h
        cases hf : encF v with
        | none => rw [hf] at h; cases h
        | some fBytes =>
          rw [hf] at h; dsimp only at h
          cases hw : writeAbstractBytesAt buf off.bytes fBytes with
          | none => rw [hw] at h; cases h
          | some buf' =>
            rw [hw] at h; dsimp only at h
            exact ih .nil vRest buf' out hvRest
              (abstractBytesHaveProv_writeAbstractBytesAt buf fBytes buf' off.bytes hbuf (hF v fBytes hv hf) hw) h
      | cons k kRest =>
        dsimp only at h
        cases h1 : encT k v with
        | some fBytes =>
          rw [h1] at h; dsimp only at h
          cases hw : writeAbstractBytesAt buf off.bytes fBytes with
          | none => rw [hw] at h; cases h
          | some buf' =>
            rw [hw] at h; dsimp only at h
            exact ih kRest vRest buf' out hvRest
              (abstractBytesHaveProv_writeAbstractBytesAt buf fBytes buf' off.bytes hbuf (hT k v fBytes hv h1) hw) h
        | none =>
          rw [h1] at h; dsimp only at h
          cases hsz : rigidTyKindByteSize k with
          | some _ => rw [hsz] at h; cases h
          | none =>
            rw [hsz] at h; dsimp only at h
            cases hf : encF v with
            | none => rw [hf] at h; cases h
            | some fBytes =>
              rw [hf] at h; dsimp only at h
              cases hw : writeAbstractBytesAt buf off.bytes fBytes with
              | none => rw [hw] at h; cases h
              | some buf' =>
                rw [hw] at h; dsimp only at h
                exact ih kRest vRest buf' out hvRest
                  (abstractBytesHaveProv_writeAbstractBytesAt buf fBytes buf' off.bytes hbuf (hF v fBytes hv hf) hw) h

private theorem abstractBytesHaveProv_encodeSeqFieldsWith
    (encT : RigidTy → Value → Option (List AbstractByte))
    (hT : ∀ k v bs, valueHasProv v = false → encT k v = .some bs → abstractBytesHaveProv bs = false) :
    ∀ kinds vals out,
      valueListHasProv vals = false →
      encodeSeqFieldsWith encT kinds vals = .some out →
      abstractBytesHaveProv out = false := by
  intro kinds
  induction kinds with
  | nil =>
    intro vals out _ h
    cases vals with
    | nil => injection h with h; subst h; rfl
    | cons _ _ => cases h
  | cons k kRest ih =>
    intro vals out hvals h
    cases vals with
    | nil => cases h
    | cons v vRest =>
      have hv : valueHasProv v = false := by
        unfold valueListHasProv at hvals
        cases h1 : valueHasProv v with | false => rfl | true => rw [h1] at hvals; cases hvals
      have hvRest : valueListHasProv vRest = false := by
        unfold valueListHasProv at hvals; rw [hv] at hvals; exact hvals
      unfold encodeSeqFieldsWith at h
      cases h1 : encT k v with
      | none => rw [h1] at h; cases h
      | some b1 =>
        cases h2 : encodeSeqFieldsWith encT kRest vRest with
        | none => rw [h1, h2] at h; cases h
        | some b2 =>
          rw [h1, h2] at h; dsimp only at h
          injection h with h; subst h
          rw [abstractBytesHaveProv_appendAbstractBytes, hT k v b1 hv h1, ih vRest b2 hvRest h2, Bool.or_false]

private theorem abstractBytesHaveProv_encodeUnionFieldsWith_untyped
    (fuel' totalSize : Nat) (fieldVals : List Value) (out : List AbstractByte)
    (hvals : valueListHasProv fieldVals = false)
    (h : encodeUnionFieldsWith (fun fv => encodeUntypedValueToBytes fuel' fv) totalSize fieldVals = .some out) :
    abstractBytesHaveProv out = false := by
  have hfind : ∀ fs out',
      valueListHasProv fs = false →
      encodeUnionFieldsWith (fun fv => encodeUntypedValueToBytes fuel' fv) totalSize (.scalar ⟨0, 0⟩ :: fs) = .some out' →
      abstractBytesHaveProv out' = false := by
    intro fs
    induction fs with
    | nil =>
      intro out' _ hf
      have h0 : encodeUntypedValueToBytes fuel' (.scalar ⟨0, 0⟩) = .none := by cases fuel' <;> rfl
      unfold encodeUnionFieldsWith at hf
      dsimp only at hf
      rw [h0] at hf
      cases hf
    | cons fv rest ih =>
      intro out' hfs hf
      have hfv : valueHasProv fv = false := by
        unfold valueListHasProv at hfs
        cases h1 : valueHasProv fv with | false => rfl | true => rw [h1] at hfs; cases hfs
      have hrest : valueListHasProv rest = false := by
        unfold valueListHasProv at hfs; rw [hfv] at hfs; exact hfs
      have h0 : encodeUntypedValueToBytes fuel' (.scalar ⟨0, 0⟩) = .none := by cases fuel' <;> rfl
      have hfStep :
          encodeUnionFieldsWith (fun fv => encodeUntypedValueToBytes fuel' fv) totalSize
              (.scalar ⟨0, 0⟩ :: fv :: rest) =
            match encodeUntypedValueToBytes fuel' fv with
            | .some fBytes =>
              match Nat.beq (length fBytes) totalSize with
              | true => writeAbstractBytesAt (replicateUninitBytes totalSize) 0 fBytes
              | false =>
                encodeUnionFieldsWith (fun fv => encodeUntypedValueToBytes fuel' fv) totalSize
                  (.scalar ⟨0, 0⟩ :: rest)
            | .none =>
              encodeUnionFieldsWith (fun fv => encodeUntypedValueToBytes fuel' fv) totalSize
                (.scalar ⟨0, 0⟩ :: rest) := by
        cases fuel' <;> rfl
      rw [hfStep] at hf
      cases he : encodeUntypedValueToBytes fuel' fv with
      | none => rw [he] at hf; exact ih out' hrest hf
      | some fBytes =>
        rw [he] at hf; dsimp only at hf
        cases hlen : Nat.beq (length fBytes) totalSize with
        | false => rw [hlen] at hf; exact ih out' hrest hf
        | true =>
          rw [hlen] at hf; dsimp only at hf
          exact abstractBytesHaveProv_writeAbstractBytesAt _ fBytes out' 0
            (abstractBytesHaveProv_replicateUninitBytes totalSize)
            (abstractBytesHaveProv_encodeUntypedValueToBytes fuel' fv fBytes hfv he) hf
  cases fieldVals with
  | nil => cases h
  | cons firstField rest =>
    have hf1 : valueHasProv firstField = false := by
      unfold valueListHasProv at hvals
      cases h1 : valueHasProv firstField with | false => rfl | true => rw [h1] at hvals; cases hvals
    have hrest : valueListHasProv rest = false := by
      unfold valueListHasProv at hvals; rw [hf1] at hvals; exact hvals
    have hstep :
        encodeUnionFieldsWith (fun fv => encodeUntypedValueToBytes fuel' fv) totalSize (firstField :: rest) =
          match encodeUntypedValueToBytes fuel' firstField with
          | .some firstBytes =>
            match Nat.beq (length firstBytes) totalSize with
            | true =>
              match encodeUnionFieldsWith (fun fv => encodeUntypedValueToBytes fuel' fv) totalSize
                  (.scalar ⟨0, 0⟩ :: firstField :: rest) with
              | .some bs => .some bs
              | .none => writeAbstractBytesAt (replicateUninitBytes totalSize) 0 firstBytes
            | false =>
              match Nat.beq (length firstBytes) 0 with
              | true =>
                match encodeUnionFieldsWith (fun fv => encodeUntypedValueToBytes fuel' fv) totalSize
                    (.scalar ⟨0, 0⟩ :: rest) with
                | .some bs => .some bs
                | .none => writeAbstractBytesAt (replicateUninitBytes totalSize) 0 firstBytes
              | false =>
                let baseBuf :=
                  match encodeUnionFieldsWith (fun fv => encodeUntypedValueToBytes fuel' fv) totalSize
                      (.scalar ⟨0, 0⟩ :: rest) with
                  | .some bs => bs
                  | .none => replicateUninitBytes totalSize
                writeAbstractBytesAt baseBuf 0 firstBytes
          | .none =>
            encodeUnionFieldsWith (fun fv => encodeUntypedValueToBytes fuel' fv) totalSize
              (.scalar ⟨0, 0⟩ :: rest) := by
      cases fuel' <;> rfl
    rw [hstep] at h
    cases he1 : encodeUntypedValueToBytes fuel' firstField with
    | none => rw [he1] at h; exact hfind rest out hrest h
    | some firstBytes =>
      rw [he1] at h; dsimp only at h
      have hfb1 := abstractBytesHaveProv_encodeUntypedValueToBytes fuel' firstField firstBytes hf1 he1
      cases hlen : Nat.beq (length firstBytes) totalSize with
      | true =>
        rw [hlen] at h; dsimp only at h
        cases hf : encodeUnionFieldsWith (fun fv => encodeUntypedValueToBytes fuel' fv) totalSize
            (.scalar ⟨0, 0⟩ :: firstField :: rest) with
        | some bs =>
          rw [hf] at h; dsimp only at h; injection h with h; subst h
          exact hfind (firstField :: rest) bs hvals hf
        | none =>
          rw [hf] at h; dsimp only at h
          exact abstractBytesHaveProv_writeAbstractBytesAt _ firstBytes out 0
            (abstractBytesHaveProv_replicateUninitBytes totalSize) hfb1 h
      | false =>
        rw [hlen] at h; dsimp only at h
        cases hz : Nat.beq (length firstBytes) 0 with
        | true =>
          rw [hz] at h; dsimp only at h
          cases hf : encodeUnionFieldsWith (fun fv => encodeUntypedValueToBytes fuel' fv) totalSize
              (.scalar ⟨0, 0⟩ :: rest) with
          | some bs =>
            rw [hf] at h; dsimp only at h; injection h with h; subst h
            exact hfind rest bs hrest hf
          | none =>
            rw [hf] at h; dsimp only at h
            exact abstractBytesHaveProv_writeAbstractBytesAt _ firstBytes out 0
              (abstractBytesHaveProv_replicateUninitBytes totalSize) hfb1 h
        | false =>
          rw [hz] at h; dsimp only at h
          cases hf : encodeUnionFieldsWith (fun fv => encodeUntypedValueToBytes fuel' fv) totalSize
              (.scalar ⟨0, 0⟩ :: rest) with
          | some bs =>
            rw [hf] at h; dsimp only at h
            exact abstractBytesHaveProv_writeAbstractBytesAt bs firstBytes out 0
              (hfind rest bs hrest hf) hfb1 h
          | none =>
            rw [hf] at h; dsimp only at h
            exact abstractBytesHaveProv_writeAbstractBytesAt _ firstBytes out 0
              (abstractBytesHaveProv_replicateUninitBytes totalSize) hfb1 h

private theorem abstractBytesHaveProv_encodeValueToBytes
    (fuel : Nat) (layouts : LayoutTable) (ty : Ty) (v : Value) (bs : List AbstractByte)
    (hv : valueHasProv v = false)
    (henc : encodeValueToBytes fuel layouts ty v = .some bs) :
    abstractBytesHaveProv bs = false := by
  induction fuel generalizing ty v bs with
  | zero => cases henc
  | succ fuel' ih =>
    unfold encodeValueToBytes at henc
    have hwide_enc : ∀ (isWide : Bool),
        (match isWide, v with
         | false, .ptr p 8 => encodeScalarBytes ⟨p.offsetBytes, 8⟩ (.some (p.allocId, p.tag))
         | false, .scalar sv =>
           match Nat.beq sv.sizeBytes 8 with
           | true => encodeScalarBytes sv .none
           | false => .none
         | true, .aggregate 0 (.ptr p 8 :: .scalar metaSc :: .nil) =>
           match encodeScalarBytes ⟨p.offsetBytes, 8⟩ (.some (p.allocId, p.tag)),
                 encodeScalarBytes ⟨metaSc.bits, 8⟩ .none with
           | .some b1, .some b2 => .some (appendAbstractBytes b1 b2)
           | _, _ => .none
         | _, _ => .none) = .some bs →
        abstractBytesHaveProv bs = false := by
      intro isWide
      cases isWide with
      | false =>
        cases v with
        | ptr _ _ => intro _; cases hv
        | scalar sv =>
          intro h'; dsimp only at h'
          cases hsz : Nat.beq sv.sizeBytes 8 with
          | false => rw [hsz] at h'; cases h'
          | true => rw [hsz] at h'; dsimp only at h'; exact abstractBytesHaveProv_encodeScalarBytes_none sv bs h'
        | _ => intro h'; cases h'
      | true =>
        cases v with
        | aggregate varIdx fs =>
          cases varIdx with
          | succ _ => intro h'; cases h'
          | zero =>
            cases fs with
            | nil => intro h'; cases h'
            | cons f0 fRest =>
              cases f0 with
              | ptr _ _ => intro _; cases hv
              | _ => intro h'; cases h'
        | _ => intro h'; cases h'
    cases hkind : ty.kind with
    | bool =>
      rw [hkind] at henc; dsimp only at henc
      cases v with
      | scalar sv =>
        dsimp only at henc
        cases hsz : Nat.beq sv.sizeBytes 1 with
        | false => rw [hsz] at henc; cases henc
        | true =>
          rw [hsz] at henc; dsimp only at henc
          cases hb0 : Nat.beq sv.bits 0 with
          | true => rw [hb0] at henc; dsimp only at henc; injection henc with henc; subst henc; rfl
          | false =>
            rw [hb0] at henc; dsimp only at henc
            cases hb1 : Nat.beq sv.bits 1 with
            | true => rw [hb1] at henc; dsimp only at henc; injection henc with henc; subst henc; rfl
            | false => rw [hb1] at henc; cases henc
      | _ => cases henc
    | char =>
      rw [hkind] at henc; dsimp only at henc
      cases v with
      | scalar sv =>
        dsimp only at henc
        cases hc : Bool.and (Nat.beq sv.sizeBytes 4) (isValidCharCode sv.bits) with
        | false => rw [hc] at henc; cases henc
        | true => rw [hc] at henc; dsimp only at henc; exact abstractBytesHaveProv_encodeScalarBytes_none sv bs henc
      | _ => cases henc
    | uint w =>
      rw [hkind] at henc; dsimp only at henc
      cases hsz : intCastTargetBytes (.uint w) with
      | none => rw [hsz] at henc; cases henc
      | some exp =>
        rw [hsz] at henc
        cases v with
        | scalar sv =>
          dsimp only at henc
          cases heq : Nat.beq sv.sizeBytes exp with
          | false => rw [heq] at henc; cases henc
          | true => rw [heq] at henc; dsimp only at henc; exact abstractBytesHaveProv_encodeScalarBytes_none sv bs henc
        | _ => cases henc
    | int w =>
      rw [hkind] at henc; dsimp only at henc
      cases hsz : intCastTargetBytes (.int w) with
      | none => rw [hsz] at henc; cases henc
      | some exp =>
        rw [hsz] at henc
        cases v with
        | scalar sv =>
          dsimp only at henc
          cases heq : Nat.beq sv.sizeBytes exp with
          | false => rw [heq] at henc; cases henc
          | true => rw [heq] at henc; dsimp only at henc; exact abstractBytesHaveProv_encodeScalarBytes_none sv bs henc
        | _ => cases henc
    | fnDef _ _ =>
      rw [hkind] at henc; dsimp only at henc
      cases v with
      | unit => dsimp only at henc; injection henc with henc; subst henc; rfl
      | aggregate varIdx fs =>
        cases varIdx with
        | zero => cases fs with | nil => simp only at henc; injection henc with henc; subst henc; rfl | cons _ _ => cases henc
        | succ _ => cases henc
      | _ => cases henc
    | fnPtr _ _ _ _ =>
      rw [hkind] at henc; dsimp only at henc
      cases v with
      | ptr _ _ => cases hv
      | scalar sv =>
        dsimp only at henc
        cases hsz : Nat.beq sv.sizeBytes 8 with
        | false => rw [hsz] at henc; cases henc
        | true => rw [hsz] at henc; dsimp only at henc; exact abstractBytesHaveProv_encodeScalarBytes_none sv bs henc
      | _ => cases henc
    | rawPtr _ pointee =>
      rw [hkind] at henc; dsimp only at henc
      exact hwide_enc _ henc
    | ref _ pointee =>
      rw [hkind] at henc; dsimp only at henc
      exact hwide_enc _ henc
    | array elemKind n =>
      rw [hkind] at henc; dsimp only at henc
      cases hn0 : Nat.beq n 0 with
      | true =>
        rw [hn0] at henc; dsimp only at henc
        cases v with
        | unit => dsimp only at henc; injection henc with henc; subst henc; rfl
        | aggregate varIdx fs =>
          cases varIdx with
          | zero => cases fs with | nil => simp only at henc; injection henc with henc; subst henc; rfl | cons _ _ => cases henc
          | succ _ => cases henc
        | _ => cases henc
      | false =>
        rw [hn0] at henc; dsimp only at henc
        cases v with
        | aggregate varIdx elems =>
          cases varIdx with
          | succ _ => cases henc
          | zero =>
            simp only at henc
            cases hlen : Nat.beq (length elems) n with
            | false => rw [hlen] at henc; cases henc
            | true =>
              rw [hlen] at henc; dsimp only at henc
              have helem : ∀ (elemSzOpt : Option Nat),
                  (match elemSzOpt with
                   | none => none
                   | some elemSz =>
                     encodeListWith
                       (fun e => encodeValueToBytes fuel' layouts { kind := elemKind, layoutIdx := 0 } e)
                       elemSz elems) = some bs →
                  abstractBytesHaveProv bs = false := by
                intro elemSzOpt
                cases elemSzOpt with
                | none => intro h'; cases h'
                | some elemSz =>
                  intro h'; dsimp only at h'
                  exact abstractBytesHaveProv_encodeListWith _ (fun e b he hb => ih _ e b he hb) elemSz elems bs hv h'
              exact helem _ henc
        | _ => cases henc
    | tuple ks =>
      rw [hkind] at henc
      cases ks with
      | nil =>
        dsimp only at henc
        cases v with
        | unit => dsimp only at henc; injection henc with henc; subst henc; rfl
        | aggregate varIdx fs =>
          cases varIdx with
          | zero => cases fs with | nil => simp only at henc; injection henc with henc; subst henc; rfl | cons _ _ => cases henc
          | succ _ => cases henc
        | _ => cases henc
      | cons kHead kTail =>
        dsimp only at henc
        cases v with
        | aggregate varIdx fieldVals =>
          cases varIdx with
          | succ _ => cases henc
          | zero =>
            simp only at henc
            cases hlen : Nat.beq (length fieldVals) (length (kHead :: kTail)) with
            | false => rw [hlen] at henc; cases henc
            | true =>
              rw [hlen] at henc; dsimp only at henc
              cases hlu : LayoutTable.lookup layouts ty.layoutIdx with
              | none =>
                rw [hlu] at henc; dsimp only at henc
                exact abstractBytesHaveProv_encodeSeqFieldsWith _ (fun k fv b hfv hb => ih _ fv b hfv hb)
                  (kHead :: kTail) fieldVals bs hv henc
              | some l =>
                rw [hlu] at henc; dsimp only at henc
                cases hlf : l.fields with
                | arbitrary offsets _ =>
                  rw [hlf] at henc; dsimp only at henc
                  cases ho : Nat.beq (length offsets) (length fieldVals) with
                  | true =>
                    rw [ho] at henc; dsimp only at henc
                    exact abstractBytesHaveProv_encodeFieldsAtOffsetsWith _ _
                      (fun k fv b hfv hb => ih _ fv b hfv hb)
                      (fun fv b hfv hb => abstractBytesHaveProv_encodeUntypedValueToBytes fuel' fv b hfv hb)
                      offsets (kHead :: kTail) fieldVals (replicateUninitBytes l.size.bytes) bs hv
                      (abstractBytesHaveProv_replicateUninitBytes l.size.bytes) henc
                  | false =>
                    rw [ho] at henc; dsimp only at henc
                    exact abstractBytesHaveProv_encodeSeqFieldsWith _ (fun k fv b hfv hb => ih _ fv b hfv hb)
                      (kHead :: kTail) fieldVals bs hv henc
                | _ =>
                  rw [hlf] at henc; dsimp only at henc
                  exact abstractBytesHaveProv_encodeSeqFieldsWith _ (fun k fv b hfv hb => ih _ fv b hfv hb)
                    (kHead :: kTail) fieldVals bs hv henc
        | _ => cases henc
    | adt _ args =>
      rw [hkind] at henc; dsimp only at henc
      cases hlu : LayoutTable.lookup layouts ty.layoutIdx with
      | none =>
        rw [hlu] at henc; dsimp only at henc
        cases v with
        | unit => dsimp only at henc; injection henc with henc; subst henc; rfl
        | aggregate varIdx fs =>
          cases varIdx with
          | zero =>
            cases fs with
            | nil => simp only at henc; injection henc with henc; subst henc; rfl
            | cons _ _ => exact abstractBytesHaveProv_encodeUntypedValueToBytes fuel' _ bs hv henc
          | succ _ => exact abstractBytesHaveProv_encodeUntypedValueToBytes fuel' _ bs hv henc
        | _ => dsimp only at henc; exact abstractBytesHaveProv_encodeUntypedValueToBytes fuel' _ bs hv henc
      | some l =>
        rw [hlu] at henc; dsimp only at henc
        cases hun : l.isUninhabited with
        | true => rw [hun] at henc; cases henc
        | false =>
          rw [hun] at henc; dsimp only at henc
          cases hlv : l.variants with
          | empty => rw [hlv] at henc; cases henc
          | single expectedVar =>
            rw [hlv] at henc; dsimp only at henc
            cases hlf : l.fields with
            | arbitrary offsets _ =>
              rw [hlf] at henc
              cases v with
              | aggregate varIdx fieldVals =>
                dsimp only at henc
                cases hok : Bool.and (Nat.beq varIdx expectedVar) (Nat.beq (length offsets) (length fieldVals)) with
                | false => rw [hok] at henc; cases henc
                | true =>
                  rw [hok] at henc; dsimp only at henc
                  exact abstractBytesHaveProv_encodeFieldsAtOffsetsWith _ _
                    (fun k fv b hfv hb => ih _ fv b hfv hb)
                    (fun fv b hfv hb => abstractBytesHaveProv_encodeUntypedValueToBytes fuel' fv b hfv hb)
                    offsets _ fieldVals (replicateUninitBytes l.size.bytes) bs hv
                    (abstractBytesHaveProv_replicateUninitBytes l.size.bytes) henc
              | unit =>
                cases offsets with
                | nil => dsimp only at henc; injection henc with henc; subst henc; exact abstractBytesHaveProv_replicateUninitBytes l.size.bytes
                | cons _ _ => cases henc
              | _ => cases henc
            | primitive =>
              rw [hlf] at henc
              cases v with
              | scalar sv =>
                dsimp only at henc
                cases hsz : Nat.beq sv.sizeBytes l.size.bytes with
                | false => rw [hsz] at henc; cases henc
                | true => rw [hsz] at henc; dsimp only at henc; exact abstractBytesHaveProv_encodeScalarBytes_none sv bs henc
              | _ => cases henc
            | union _ =>
              rw [hlf] at henc
              cases v with
              | aggregate _ fieldVals =>
                dsimp only at henc
                exact abstractBytesHaveProv_encodeUnionFieldsWith_untyped fuel' l.size.bytes fieldVals bs hv henc
              | _ => cases henc
            | array _ _ => rw [hlf] at henc; cases henc
          | multiple tagLayout tagField variantShapes =>
            rw [hlv] at henc; dsimp only at henc
            cases v with
            | aggregate varIdx fieldVals =>
              dsimp only at henc
              cases hlf : l.fields with
              | arbitrary outerOffsets _ =>
                rw [hlf] at henc
                cases htsz : scalarLayoutByteWidth tagLayout with
                | none => rw [htsz] at henc; cases henc
                | some tagSz =>
                  rw [htsz] at henc
                  cases hvs : get? variantShapes varIdx with
                  | none => rw [hvs] at henc; cases henc
                  | some vshape =>
                    rw [hvs] at henc
                    cases vshape with
                    | arbitrary varOffsets _ =>
                      dsimp only at henc
                      cases htoff : get? outerOffsets tagField with
                      | none => rw [htoff] at henc; cases henc
                      | some tagOff =>
                        rw [htoff] at henc; dsimp only at henc
                        cases hdsc : resolveEnumDiscriminantForVariant tagLayout tagSz l.variantDiscriminants varIdx with
                        | none => rw [hdsc] at henc; cases henc
                        | some tagBits =>
                          rw [hdsc] at henc; dsimp only at henc
                          cases htb : encodeScalarBytes ⟨tagBits, tagSz⟩ .none with
                          | none => rw [htb] at henc; cases henc
                          | some tagBytes =>
                            rw [htb] at henc; dsimp only at henc
                            cases hwt : writeAbstractBytesAt (replicateUninitBytes l.size.bytes) tagOff.bytes tagBytes with
                            | none => rw [hwt] at henc; cases henc
                            | some bufWithTag =>
                              rw [hwt] at henc; dsimp only at henc
                              have hbufTag := abstractBytesHaveProv_writeAbstractBytesAt _ tagBytes bufWithTag tagOff.bytes
                                (abstractBytesHaveProv_replicateUninitBytes l.size.bytes)
                                (abstractBytesHaveProv_encodeScalarBytes_none _ tagBytes htb) hwt
                              exact abstractBytesHaveProv_encodeFieldsAtOffsetsWith _ _
                                (fun k fv b hfv hb => ih _ fv b hfv hb)
                                (fun fv b hfv hb => abstractBytesHaveProv_encodeUntypedValueToBytes fuel' fv b hfv hb)
                                varOffsets .nil fieldVals bufWithTag bs hv hbufTag henc
                    | _ => cases henc
              | _ => rw [hlf] at henc; cases henc
            | _ => cases henc
    | _ => rw [hkind] at henc; cases henc

private theorem abstractBytesHaveProv_encodeArbitrarySlotsIntoBufAux
    (enc : Nat → Value → Option (List AbstractByte))
    (henc : ∀ flIdx v bs, valueHasProv v = false → enc flIdx v = .some bs → abstractBytesHaveProv bs = false)
    (fallbackIdx : Nat) :
    ∀ offsets flIdxs vals buf out,
      valueListHasProv vals = false →
      abstractBytesHaveProv buf = false →
      encodeArbitrarySlotsIntoBufAux enc fallbackIdx offsets flIdxs vals buf = .some out →
      abstractBytesHaveProv out = false := by
  intro offsets
  induction offsets with
  | nil =>
    intro flIdxs vals buf out _ hbuf h
    cases vals with
    | nil => unfold encodeArbitrarySlotsIntoBufAux at h; injection h with h; rw [← h]; exact hbuf
    | cons _ _ => cases h
  | cons off offRest ih =>
    intro flIdxs vals buf out hvals hbuf h
    cases vals with
    | nil => cases h
    | cons fv vRest =>
      have hfv : valueHasProv fv = false := by
        unfold valueListHasProv at hvals
        cases h1 : valueHasProv fv with | false => rfl | true => rw [h1] at hvals; cases hvals
      have hvRest : valueListHasProv vRest = false := by
        unfold valueListHasProv at hvals; rw [hfv] at hvals; exact hvals
      unfold encodeArbitrarySlotsIntoBufAux at h
      dsimp only at h
      have hstep : ∀ (flIdx : Nat) (nextIdxs : List Nat),
          (match enc flIdx fv with
           | none => none
           | some fBytes =>
             match writeAbstractBytesAt buf off.bytes fBytes with
             | none => none
             | some buf' =>
               encodeArbitrarySlotsIntoBufAux enc fallbackIdx offRest nextIdxs vRest buf') = some out →
          abstractBytesHaveProv out = false := by
        intro flIdx nextIdxs h'
        cases he : enc flIdx fv with
        | none => rw [he] at h'; cases h'
        | some fBytes =>
          rw [he] at h'; dsimp only at h'
          cases hw : writeAbstractBytesAt buf off.bytes fBytes with
          | none => rw [hw] at h'; cases h'
          | some buf' =>
            rw [hw] at h'; dsimp only at h'
            exact ih nextIdxs vRest buf' out hvRest
              (abstractBytesHaveProv_writeAbstractBytesAt buf fBytes buf' off.bytes hbuf (henc flIdx fv fBytes hfv he) hw) h'
      cases flIdxs with
      | nil => exact hstep fallbackIdx .nil h
      | cons f fRest => exact hstep f fRest h

private theorem abstractBytesHaveProv_encodeArraySlotsIntoBufAux
    (enc : Nat → Value → Option (List AbstractByte))
    (henc : ∀ flIdx v bs, valueHasProv v = false → enc flIdx v = .some bs → abstractBytesHaveProv bs = false)
    (elemFlIdx strideBytes : Nat) :
    ∀ runningOff elems buf out,
      valueListHasProv elems = false →
      abstractBytesHaveProv buf = false →
      encodeArraySlotsIntoBufAux enc elemFlIdx strideBytes runningOff elems buf = .some out →
      abstractBytesHaveProv out = false := by
  intro runningOff elems
  induction elems generalizing runningOff with
  | nil =>
    intro buf out _ hbuf h
    unfold encodeArraySlotsIntoBufAux at h; injection h with h; rw [← h]; exact hbuf
  | cons ev eRest ih =>
    intro buf out helems hbuf h
    have hev : valueHasProv ev = false := by
      unfold valueListHasProv at helems
      cases h1 : valueHasProv ev with | false => rfl | true => rw [h1] at helems; cases helems
    have heRest : valueListHasProv eRest = false := by
      unfold valueListHasProv at helems; rw [hev] at helems; exact helems
    unfold encodeArraySlotsIntoBufAux at h
    cases he : enc elemFlIdx ev with
    | none => rw [he] at h; cases h
    | some eBytes =>
      rw [he] at h; dsimp only at h
      cases hw : writeAbstractBytesAt buf runningOff eBytes with
      | none => rw [hw] at h; cases h
      | some buf' =>
        rw [hw] at h; dsimp only at h
        exact ih (Nat.add runningOff strideBytes) buf' out heRest
          (abstractBytesHaveProv_writeAbstractBytesAt buf eBytes buf' runningOff hbuf (henc elemFlIdx ev eBytes hev he) hw) h

private theorem abstractBytesHaveProv_mergeUnionTypedSlotsAux
    (layouts : LayoutTable)
    (enc : Nat → Value → Option (List AbstractByte))
    (henc : ∀ flIdx v bs, valueHasProv v = false → enc flIdx v = .some bs → abstractBytesHaveProv bs = false)
    (fallbackIdx : Nat) (hasOverlay : Bool) (unionSize : Nat) :
    ∀ flIdxs vals buf bufMask out,
      valueListHasProv vals = false →
      abstractBytesHaveProv buf = false →
      mergeUnionTypedSlotsAux layouts enc fallbackIdx hasOverlay unionSize flIdxs vals buf bufMask = .some out →
      abstractBytesHaveProv out = false := by
  intro flIdxs vals
  induction vals generalizing flIdxs with
  | nil =>
    intro buf bufMask out _ hbuf h
    unfold mergeUnionTypedSlotsAux at h; injection h with h; rw [← h]; exact hbuf
  | cons fv vRest ih =>
    intro buf bufMask out hvals hbuf h
    have hfv : valueHasProv fv = false := by
      unfold valueListHasProv at hvals
      cases h1 : valueHasProv fv with | false => rfl | true => rw [h1] at hvals; cases hvals
    have hvRest : valueListHasProv vRest = false := by
      unfold valueListHasProv at hvals; rw [hfv] at hvals; exact hvals
    unfold mergeUnionTypedSlotsAux at h
    dsimp only at h
    cases fv with
    | unit => exact ih _ buf bufMask out hvRest hbuf h
    | uninit => exact ih _ buf bufMask out hvRest hbuf h
    | ptr _ _ => cases hfv
    | scalar sc =>
      cases flIdxs with
      | cons flIdx nextIdxs =>
        dsimp only at h
        cases he : enc flIdx (.scalar sc) with
        | none => rw [he] at h; cases h
        | some fBytes =>
          rw [he] at h; dsimp only at h
          cases hm : mergeMaskedAbstractBytes buf bufMask fBytes (layoutValueMaskAux 8 layouts flIdx) with
          | none => rw [hm] at h; cases h
          | some merged =>
            rcases merged with ⟨buf', bufMask'⟩
            rw [hm] at h; dsimp only at h
            exact ih nextIdxs buf' bufMask' out hvRest
              (abstractBytesHaveProv_mergeMaskedAbstractBytes buf fBytes bufMask _ (buf', bufMask') hbuf (henc flIdx _ fBytes hfv he) hm) h
      | nil =>
        dsimp only at h
        cases he : enc fallbackIdx (.scalar sc) with
        | none => rw [he] at h; cases h
        | some fBytes =>
          rw [he] at h
          cases fBytes with
          | nil =>
            dsimp only at h
            cases hu : valueContainsUnit (.scalar sc) with
            | false => rw [hu] at h; dsimp only at h; exact ih .nil buf bufMask out hvRest hbuf h
            | true =>
              rw [hu] at h; dsimp only at h
              cases hm : mergeMaskedAbstractBytes buf bufMask (replicateUninitBytes unionSize) (replicateBool unionSize true) with
              | none => rw [hm] at h; cases h
              | some merged =>
                rcases merged with ⟨buf', bufMask'⟩
                rw [hm] at h; dsimp only at h
                exact ih .nil buf' bufMask' out hvRest
                  (abstractBytesHaveProv_mergeMaskedAbstractBytes buf _ bufMask _ (buf', bufMask') hbuf
                    (abstractBytesHaveProv_replicateUninitBytes unionSize) hm) h
          | cons b bs =>
            dsimp only at h
            cases hm : mergeMaskedAbstractBytes buf bufMask (b :: bs) (replicateBool (length (b :: bs)) true) with
            | none => rw [hm] at h; cases h
            | some merged =>
              rcases merged with ⟨buf', bufMask'⟩
              rw [hm] at h; dsimp only at h
              exact ih .nil buf' bufMask' out hvRest
                (abstractBytesHaveProv_mergeMaskedAbstractBytes buf (b :: bs) bufMask _ (buf', bufMask') hbuf
                  (henc fallbackIdx _ (b :: bs) hfv he) hm) h
    | aggregate varIdx afs =>
      cases flIdxs with
      | cons flIdx nextIdxs =>
        dsimp only at h
        cases he : enc flIdx (.aggregate varIdx afs) with
        | none => rw [he] at h; cases h
        | some fBytes =>
          rw [he] at h; dsimp only at h
          cases hm : mergeMaskedAbstractBytes buf bufMask fBytes (layoutValueMaskAux 8 layouts flIdx) with
          | none => rw [hm] at h; cases h
          | some merged =>
            rcases merged with ⟨buf', bufMask'⟩
            rw [hm] at h; dsimp only at h
            exact ih nextIdxs buf' bufMask' out hvRest
              (abstractBytesHaveProv_mergeMaskedAbstractBytes buf fBytes bufMask _ (buf', bufMask') hbuf (henc flIdx _ fBytes hfv he) hm) h
      | nil =>
        dsimp only at h
        cases hasOverlay with
        | true =>
          cases afs with
          | nil =>
            dsimp only at h
            have hst : ∀ (b : Bool),
                (match b with
                 | false => mergeUnionTypedSlotsAux layouts enc fallbackIdx true unionSize .nil vRest buf bufMask
                 | true => .none) = .some out →
                abstractBytesHaveProv out = false := by
              intro b
              cases b with
              | true => intro h'; cases h'
              | false => intro h'; exact ih .nil buf bufMask out hvRest hbuf h'
            exact hst _ h
          | cons a0 aRest =>
            dsimp only at h
            cases heu : encodeUntypedValueToBytes defaultCodecFuel (.aggregate varIdx (a0 :: aRest)) with
            | none => rw [heu] at h; cases h
            | some uBytes =>
              rw [heu] at h
              cases uBytes with
              | nil =>
                dsimp only at h
                cases hu : valueContainsUnit (.aggregate varIdx (a0 :: aRest)) with
                | false => rw [hu] at h; dsimp only at h; exact ih .nil buf bufMask out hvRest hbuf h
                | true =>
                  rw [hu] at h; dsimp only at h
                  cases hm : mergeMaskedAbstractBytes buf bufMask (replicateUninitBytes unionSize) (replicateBool unionSize true) with
                  | none => rw [hm] at h; cases h
                  | some merged =>
                    rcases merged with ⟨buf', bufMask'⟩
                    rw [hm] at h; dsimp only at h
                    exact ih .nil buf' bufMask' out hvRest
                      (abstractBytesHaveProv_mergeMaskedAbstractBytes buf _ bufMask _ (buf', bufMask') hbuf
                        (abstractBytesHaveProv_replicateUninitBytes unionSize) hm) h
              | cons b bs =>
                dsimp only at h
                cases hsub : abstractByteSubseq (b :: bs) buf with
                | false => rw [hsub] at h; cases h
                | true => rw [hsub] at h; dsimp only at h; exact ih .nil buf bufMask out hvRest hbuf h
        | false =>
          have h :
              (match enc fallbackIdx (.aggregate varIdx afs) with
               | none => none
               | some .nil =>
                 match valueContainsUnit (.aggregate varIdx afs) with
                 | false =>
                   mergeUnionTypedSlotsAux layouts enc fallbackIdx false unionSize .nil vRest buf bufMask
                 | true =>
                   match mergeMaskedAbstractBytes buf bufMask
                       (replicateUninitBytes unionSize) (replicateBool unionSize true) with
                   | none => none
                   | some (buf', bufMask') =>
                     mergeUnionTypedSlotsAux layouts enc fallbackIdx false unionSize .nil vRest buf' bufMask'
               | some (b :: bs) =>
                 match mergeMaskedAbstractBytes buf bufMask (b :: bs) (replicateBool (length (b :: bs)) true) with
                 | none => none
                 | some (buf', bufMask') =>
                   mergeUnionTypedSlotsAux layouts enc fallbackIdx false unionSize .nil vRest buf' bufMask') = some out := by
            cases afs <;> exact h
          cases he : enc fallbackIdx (.aggregate varIdx afs) with
          | none => rw [he] at h; cases h
          | some fBytes =>
            rw [he] at h
            cases fBytes with
            | nil =>
              dsimp only at h
              cases hu : valueContainsUnit (.aggregate varIdx afs) with
              | false => rw [hu] at h; dsimp only at h; exact ih .nil buf bufMask out hvRest hbuf h
              | true =>
                rw [hu] at h; dsimp only at h
                cases hm : mergeMaskedAbstractBytes buf bufMask (replicateUninitBytes unionSize) (replicateBool unionSize true) with
                | none => rw [hm] at h; cases h
                | some merged =>
                  rcases merged with ⟨buf', bufMask'⟩
                  rw [hm] at h; dsimp only at h
                  exact ih .nil buf' bufMask' out hvRest
                    (abstractBytesHaveProv_mergeMaskedAbstractBytes buf _ bufMask _ (buf', bufMask') hbuf
                      (abstractBytesHaveProv_replicateUninitBytes unionSize) hm) h
            | cons b bs =>
              dsimp only at h
              cases hm : mergeMaskedAbstractBytes buf bufMask (b :: bs) (replicateBool (length (b :: bs)) true) with
              | none => rw [hm] at h; cases h
              | some merged =>
                rcases merged with ⟨buf', bufMask'⟩
                rw [hm] at h; dsimp only at h
                exact ih .nil buf' bufMask' out hvRest
                  (abstractBytesHaveProv_mergeMaskedAbstractBytes buf (b :: bs) bufMask _ (buf', bufMask') hbuf
                    (henc fallbackIdx _ (b :: bs) hfv he) hm) h

private theorem abstractBytesHaveProv_encodeByLayoutIdxAux
    (fuel : Nat) (layouts : LayoutTable) (layoutIdx : Nat) (v : Value) (bs : List AbstractByte)
    (hv : valueHasProv v = false)
    (henc : encodeByLayoutIdxAux fuel layouts layoutIdx v = .some bs) :
    abstractBytesHaveProv bs = false := by
  induction fuel generalizing layoutIdx v bs with
  | zero => cases henc
  | succ fuel' ih =>
    cases v with
    | uninit => cases henc
    | unit => injection henc with henc; subst henc; rfl
    | ptr _ _ => cases hv
    | scalar sv =>
      unfold encodeByLayoutIdxAux at henc
      dsimp only at henc
      have hsc : ∀ (ok : Bool),
          (match ok with | true => encodeScalarBytes sv .none | false => .none) = .some bs →
          abstractBytesHaveProv bs = false := by
        intro ok
        cases ok with
        | false => intro h'; cases h'
        | true => intro h'; exact abstractBytesHaveProv_encodeScalarBytes_none sv bs h'
      exact hsc _ henc
    | aggregate varIdx fieldVals =>
      unfold encodeByLayoutIdxAux at henc
      dsimp only at henc
      cases hlu : LayoutTable.lookup layouts layoutIdx with
      | none =>
        rw [hlu] at henc; dsimp only at henc
        exact abstractBytesHaveProv_encodeUntypedValueToBytes defaultCodecFuel _ bs hv henc
      | some l =>
        rw [hlu] at henc; dsimp only at henc
        cases hun : l.isUninhabited with
        | true => rw [hun] at henc; cases henc
        | false =>
          rw [hun] at henc; dsimp only at henc
          cases hlf : l.fields with
          | union count =>
            rw [hlf] at henc; dsimp only at henc
            cases hv0 : Nat.beq varIdx 0 with
            | false => rw [hv0] at henc; cases henc
            | true =>
              rw [hv0] at henc; dsimp only at henc
              unfold encodeUnionSlotsIntoBufAux at henc
              cases hsp : splitUnionTypedAndOverlay count fieldVals with
              | none => rw [hsp] at henc; cases henc
              | some splitRes =>
                rcases splitRes with ⟨typedVals, overlayOpt⟩
                rw [hsp] at henc; dsimp only at henc
                have hspPf := valueListHasProv_splitUnionTypedAndOverlay count fieldVals (typedVals, overlayOpt) hv hsp
                have hamb : ∀ (amb : Bool),
                    (match (generalizing := false) amb, overlayOpt with
                     | true, _ => none
                     | false, none =>
                       mergeUnionTypedSlotsAux layouts
                         (fun cIdx cv => encodeByLayoutIdxAux fuel' layouts cIdx cv)
                         (unresolvedLayoutIdx layouts) false l.size.bytes
                         l.fieldLayouts typedVals (replicateUninitBytes l.size.bytes)
                         (replicateBool l.size.bytes false)
                     | false, some rawVals =>
                       match Nat.ble (unionNonUnitNonZstTypedSlotCount layouts count l.fieldLayouts typedVals) 1 with
                       | false => none
                       | true =>
                         match overlayRawAbstractByteVals rawVals (replicateUninitBytes l.size.bytes) with
                         | none => none
                         | some rawImage =>
                           mergeUnionTypedSlotsAux layouts
                             (fun cIdx cv => encodeByLayoutIdxAux fuel' layouts cIdx cv)
                             (unresolvedLayoutIdx layouts) true l.size.bytes
                             l.fieldLayouts typedVals rawImage
                             (replicateBool l.size.bytes true)) = some bs →
                    abstractBytesHaveProv bs = false := by
                  intro amb
                  cases amb with
                  | true => intro h'; cases h'
                  | false =>
                    cases hov : overlayOpt with
                    | none =>
                      intro h'; dsimp only at h'
                      exact abstractBytesHaveProv_mergeUnionTypedSlotsAux layouts _
                        (fun cIdx cv b hcv hb => ih cIdx cv b hcv hb) _ false l.size.bytes
                        l.fieldLayouts typedVals (replicateUninitBytes l.size.bytes)
                        (replicateBool l.size.bytes false) bs hspPf.1
                        (abstractBytesHaveProv_replicateUninitBytes l.size.bytes) h'
                    | some rawVals =>
                      intro h'; dsimp only at h'
                      cases hcnt : Nat.ble (unionNonUnitNonZstTypedSlotCount layouts count l.fieldLayouts typedVals) 1 with
                      | false => rw [hcnt] at h'; cases h'
                      | true =>
                        rw [hcnt] at h'; dsimp only at h'
                        cases hraw : overlayRawAbstractByteVals rawVals (replicateUninitBytes l.size.bytes) with
                        | none => rw [hraw] at h'; cases h'
                        | some rawImg =>
                          rw [hraw] at h'; dsimp only at h'
                          have hrawPf := abstractBytesHaveProv_overlayRawAbstractByteVals rawVals _ rawImg
                            (hspPf.2 rawVals hov) (abstractBytesHaveProv_replicateUninitBytes l.size.bytes) hraw
                          exact abstractBytesHaveProv_mergeUnionTypedSlotsAux layouts _
                            (fun cIdx cv b hcv hb => ih cIdx cv b hcv hb) _ true l.size.bytes
                            l.fieldLayouts typedVals rawImg (replicateBool l.size.bytes true) bs hspPf.1 hrawPf h'
                exact hamb _ henc
          | arbitrary offsets _ =>
            rw [hlf] at henc; dsimp only at henc
            cases hlv : l.variants with
            | single expectedVar =>
              rw [hlv] at henc; dsimp only at henc
              cases hok : Bool.and (Nat.beq varIdx expectedVar) (Nat.beq (length offsets) (length fieldVals)) with
              | false => rw [hok] at henc; cases henc
              | true =>
                rw [hok] at henc; dsimp only at henc
                exact abstractBytesHaveProv_encodeArbitrarySlotsIntoBufAux _
                  (fun cIdx cv b hcv hb => ih cIdx cv b hcv hb) _ offsets l.fieldLayouts fieldVals
                  (replicateUninitBytes l.size.bytes) bs hv
                  (abstractBytesHaveProv_replicateUninitBytes l.size.bytes) henc
            | _ =>
              rw [hlv] at henc; dsimp only at henc
              exact abstractBytesHaveProv_encodeValueToBytes defaultCodecFuel layouts _ _ bs hv henc
          | array stride count =>
            rw [hlf] at henc; dsimp only at henc
            cases hok : Bool.and (Nat.beq varIdx 0) (Nat.beq (length fieldVals) count) with
            | false => rw [hok] at henc; cases henc
            | true =>
              rw [hok] at henc; dsimp only at henc
              exact abstractBytesHaveProv_encodeArraySlotsIntoBufAux _
                (fun cIdx cv b hcv hb => ih cIdx cv b hcv hb) _ stride.bytes 0 fieldVals
                (replicateUninitBytes l.size.bytes) bs hv
                (abstractBytesHaveProv_replicateUninitBytes l.size.bytes) henc
          | primitive =>
            rw [hlf] at henc; dsimp only at henc
            cases hu : encodeUntypedValueToBytes defaultCodecFuel (.aggregate varIdx fieldVals) with
            | none => rw [hu] at henc; cases henc
            | some ubs =>
              rw [hu] at henc; dsimp only at henc
              cases hlen : Nat.beq (length ubs) l.size.bytes with
              | false => rw [hlen] at henc; cases henc
              | true =>
                rw [hlen] at henc; dsimp only at henc; injection henc with henc; subst henc
                exact abstractBytesHaveProv_encodeUntypedValueToBytes defaultCodecFuel _ ubs hv hu

/-- Encoding any provenance-free `Value` via `encodeByteCastSourceBytes` produces
provenance-free bytes (across scalars, structs, tuples, arrays, enums, and unions). -/
theorem abstractBytesHaveProv_encodeByteCastSourceBytes
    (layouts : LayoutTable) (srcTy : Ty) (v : Value) (bs : List AbstractByte)
    (hv : valueHasProv v = false)
    (henc : encodeByteCastSourceBytes layouts srcTy v = .some bs) :
    abstractBytesHaveProv bs = false := by
  unfold encodeByteCastSourceBytes encodeTypedValueToBytes at henc
  dsimp only at henc
  cases hun : isUnionLayout layouts (normalizeCodecTy srcTy) with
  | true =>
    rw [hun] at henc
    cases he1 : encodeByLayoutIdxAux 8 layouts (normalizeCodecTy srcTy).layoutIdx v with
    | some b1 =>
      rw [he1] at henc; injection henc with henc; rw [← henc]
      exact abstractBytesHaveProv_encodeByLayoutIdxAux 8 layouts _ v b1 hv he1
    | none => rw [he1] at henc; cases henc
  | false =>
    rw [hun] at henc
    cases he1 : encodeValueToBytes defaultCodecFuel layouts (normalizeCodecTy srcTy) v with
    | some b1 =>
      rw [he1] at henc; injection henc with henc; rw [← henc]
      exact abstractBytesHaveProv_encodeValueToBytes defaultCodecFuel layouts _ v b1 hv he1
    | none =>
      rw [he1] at henc
      cases hk : (normalizeCodecTy srcTy).kind with
      | adt _ _ =>
        rw [hk] at henc
        cases hlu : LayoutTable.lookup layouts (normalizeCodecTy srcTy).layoutIdx with
        | none =>
          rw [hlu] at henc
          exact abstractBytesHaveProv_encodeUntypedValueToBytes defaultCodecFuel v bs hv henc
        | some _ =>
          rw [hlu] at henc
          cases he2 : encodeByLayoutIdxAux 8 layouts (normalizeCodecTy srcTy).layoutIdx v with
          | some b2 =>
            rw [he2] at henc; injection henc with henc; rw [← henc]
            exact abstractBytesHaveProv_encodeByLayoutIdxAux 8 layouts _ v b2 hv he2
          | none =>
            rw [he2] at henc
            exact abstractBytesHaveProv_encodeUntypedValueToBytes defaultCodecFuel v bs hv henc
      | tuple ks =>
        rw [hk] at henc
        cases ks with
        | nil => exact abstractBytesHaveProv_encodeUntypedValueToBytes defaultCodecFuel v bs hv henc
        | cons _ _ =>
          cases hlu : LayoutTable.lookup layouts (normalizeCodecTy srcTy).layoutIdx with
          | none =>
            rw [hlu] at henc
            exact abstractBytesHaveProv_encodeUntypedValueToBytes defaultCodecFuel v bs hv henc
          | some _ =>
            rw [hlu] at henc
            cases he2 : encodeByLayoutIdxAux 8 layouts (normalizeCodecTy srcTy).layoutIdx v with
            | some b2 =>
              rw [he2] at henc; injection henc with henc; rw [← henc]
              exact abstractBytesHaveProv_encodeByLayoutIdxAux 8 layouts _ v b2 hv he2
            | none =>
              rw [he2] at henc
              exact abstractBytesHaveProv_encodeUntypedValueToBytes defaultCodecFuel v bs hv henc
      | array _ _ =>
        rw [hk] at henc
        cases hlu : LayoutTable.lookup layouts (normalizeCodecTy srcTy).layoutIdx with
        | none =>
          rw [hlu] at henc
          exact abstractBytesHaveProv_encodeUntypedValueToBytes defaultCodecFuel v bs hv henc
        | some _ =>
          rw [hlu] at henc
          cases he2 : encodeByLayoutIdxAux 8 layouts (normalizeCodecTy srcTy).layoutIdx v with
          | some b2 =>
            rw [he2] at henc; injection henc with henc; rw [← henc]
            exact abstractBytesHaveProv_encodeByLayoutIdxAux 8 layouts _ v b2 hv he2
          | none =>
            rw [he2] at henc
            exact abstractBytesHaveProv_encodeUntypedValueToBytes defaultCodecFuel v bs hv henc
      | _ =>
        rw [hk] at henc
        exact abstractBytesHaveProv_encodeUntypedValueToBytes defaultCodecFuel v bs hv henc

/-- **Provenance-free equivalence for `evalByteCast`**: when the source operand evaluates
to a provenance-free `Value` (`valueHasProv v = false`), `.strictUcg630Ub` and
`.stripProvenance` agree unconditionally. -/
theorem evalByteCast_eq_of_provFree
    (locals locals' : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) (v : Value)
    (hop : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok v locals')
    (hv : valueHasProv v = false) :
    evalByteCast locals op targetTy mem localDecls layouts .strictUcg630Ub =
      evalByteCast locals op targetTy mem localDecls layouts .stripProvenance := by
  unfold evalByteCast
  rw [hop]
  dsimp only
  cases tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts targetTy) with
  | none => rfl
  | some dstSize =>
    dsimp only
    cases operandTy localDecls layouts op with
    | some srcTy =>
      dsimp only
      cases resolveByteCastSrcTyAndSize localDecls layouts op srcTy with
      | none => rfl
      | some srcPair =>
        rcases srcPair with ⟨rSrcTy, srcSize⟩
        dsimp only
        cases Nat.beq srcSize dstSize with
        | false => rfl
        | true =>
          dsimp only
          cases henc : encodeByteCastSourceBytes layouts rSrcTy v with
          | none => rfl
          | some bs =>
            dsimp only
            cases Nat.beq (length bs) dstSize with
            | false => rfl
            | true =>
              dsimp only
              rw [decodeTypedValueFromBytes_eq_of_provFree defaultCodecFuel layouts _ bs
                (abstractBytesHaveProv_encodeByteCastSourceBytes layouts rSrcTy v bs hv henc)]
    | none =>
      dsimp only
      cases henc : encodeUntypedValueToBytes defaultCodecFuel v with
      | none => rfl
      | some bs =>
        dsimp only
        cases Nat.beq (length bs) dstSize with
        | false => rfl
        | true =>
          dsimp only
          rw [decodeTypedValueFromBytes_eq_of_provFree defaultCodecFuel layouts _ bs
            (abstractBytesHaveProv_encodeUntypedValueToBytes defaultCodecFuel v bs hv henc)]

/-- **Provenance-free equivalence for `evalByteCastRichWithPolicy`**. -/
theorem evalByteCastRichWithPolicy_eq_of_provFree
    (locals locals' : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (richSpecs : List (DefPath × RichAdtSpec)) (v : Value)
    (hop : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok v locals')
    (hv : valueHasProv v = false) :
    evalByteCastRichWithPolicy locals op targetTy mem localDecls layouts richSpecs .strictUcg630Ub =
      evalByteCastRichWithPolicy locals op targetTy mem localDecls layouts richSpecs .stripProvenance := by
  unfold evalByteCastRichWithPolicy
  rw [hop]
  dsimp only
  cases richTyByteSize localDecls layouts richSpecs (resolveTyWithLocalDecls localDecls layouts targetTy) with
  | none => rfl
  | some dstSize =>
    dsimp only
    cases operandTy localDecls layouts op with
    | some srcTy =>
      dsimp only
      cases richTyByteSize localDecls layouts richSpecs (resolveTyWithLocalDecls localDecls layouts srcTy) with
      | none => rfl
      | some srcSize =>
        dsimp only
        cases Nat.beq srcSize dstSize with
        | false => rfl
        | true =>
          dsimp only
          cases henc : encodeByteCastSourceBytes layouts (resolveTyWithLocalDecls localDecls layouts srcTy) v with
          | none => rfl
          | some bs =>
            dsimp only
            cases Nat.beq (length bs) dstSize with
            | false => rfl
            | true =>
              dsimp only
              rw [decodeTypedValueRichWithPolicy_eq_of_provFree defaultCodecFuel layouts richSpecs _ bs
                (abstractBytesHaveProv_encodeByteCastSourceBytes layouts _ v bs hv henc)]
    | none =>
      dsimp only
      cases henc : encodeUntypedValueToBytes defaultCodecFuel v with
      | none => rfl
      | some bs =>
        dsimp only
        cases Nat.beq (length bs) dstSize with
        | false => rfl
        | true =>
          dsimp only
          rw [decodeTypedValueRichWithPolicy_eq_of_provFree defaultCodecFuel layouts richSpecs _ bs
            (abstractBytesHaveProv_encodeUntypedValueToBytes defaultCodecFuel v bs hv henc)]

/-! ### Closed-form provenance erasure (`strip(bytes) = strict(stripAbstractBytesProv bytes)`) & policy independence -/

/-- Closed-form provenance erasure for non-pointer `ScalarLayout`s: decoding under
`.stripProvenance` equals decoding `stripAbstractBytesProv bs` under `.strictUcg630Ub`. -/
theorem decodeScalarLayoutBytesNoForge_strip_eq_strict_stripProv
    (sl : ScalarLayout) (bs : List AbstractByte)
    (hNonPtr : scalarLayoutIsPointer sl = false) :
    decodeScalarLayoutBytesNoForge sl bs .stripProvenance =
      decodeScalarLayoutBytesNoForge sl (stripAbstractBytesProv bs) .strictUcg630Ub := by
  unfold decodeScalarLayoutBytesNoForge
  rw [length_stripAbstractBytesProv, abstractBytesHaveProv_stripAbstractBytesProv,
    decodeScalarBytes_stripAbstractBytesProv]
  cases scalarLayoutByteWidth sl with
  | none => rfl
  | some sz =>
    dsimp only
    cases Nat.beq (length bs) sz with
    | false => rfl
    | true =>
      dsimp only
      cases sl with
      | initialized pk vr =>
        cases pk with
        | pointer _ => cases hNonPtr
        | int _ _ =>
          dsimp only
          cases decodeScalarBytes bs false with
          | none => rfl
          | some res => rcases res with ⟨sv, prov⟩; rfl
        | float _ =>
          dsimp only
          cases decodeScalarBytes bs false with
          | none => rfl
          | some res => rcases res with ⟨sv, prov⟩; rfl
      | union pk =>
        cases pk with
        | pointer _ => cases hNonPtr
        | int _ _ =>
          dsimp only
          cases decodeScalarBytes bs false with
          | none => rfl
          | some res => rcases res with ⟨sv, prov⟩; rfl
        | float _ =>
          dsimp only
          cases decodeScalarBytes bs false with
          | none => rfl
          | some res => rcases res with ⟨sv, prov⟩; rfl

/-- Closed-form provenance erasure on primitive non-pointer targets (`bool`, `char`,
integers, and floats): decoding `bs` under `.stripProvenance` equals decoding
`stripAbstractBytesProv bs` under `.strictUcg630Ub`. -/
theorem decodeTypedValueFromBytes_prim_strip_eq_strict_stripProv
    (fuel : Nat) (layouts : LayoutTable) (ty : Ty) (bs : List AbstractByte)
    (hPrim : ty.kind = .bool ∨ ty.kind = .char ∨ (∃ w, ty.kind = .int w) ∨
      (∃ w, ty.kind = .uint w) ∨ (∃ fk, ty.kind = .float fk)) :
    decodeTypedValueFromBytes (fuel + 1) layouts ty bs .stripProvenance =
      decodeTypedValueFromBytes (fuel + 1) layouts ty (stripAbstractBytesProv bs) .strictUcg630Ub := by
  have hdv_bool : decodeValueFromBytes (fuel + 1) layouts { kind := .bool, layoutIdx := ty.layoutIdx } bs =
      decodeValueFromBytes (fuel + 1) layouts { kind := .bool, layoutIdx := ty.layoutIdx } (stripAbstractBytesProv bs) := by
    cases bs with
    | nil => rfl
    | cons b rest =>
      cases rest with
      | nil => cases b <;> rfl
      | cons _ _ => cases b <;> rfl
  have hdv_char : decodeValueFromBytes (fuel + 1) layouts { kind := .char, layoutIdx := ty.layoutIdx } bs =
      decodeValueFromBytes (fuel + 1) layouts { kind := .char, layoutIdx := ty.layoutIdx } (stripAbstractBytesProv bs) := by
    unfold decodeValueFromBytes
    dsimp only
    rw [length_stripAbstractBytesProv, decodeScalarBytes_stripAbstractBytesProv]
    cases Nat.beq (length bs) 4 with
    | false => rfl
    | true =>
      dsimp only
      cases decodeScalarBytes bs false with
      | none => rfl
      | some res => rcases res with ⟨sv, prov⟩; rfl
  have hdv_uint : ∀ (w : UintTy) (li : LayoutIdx),
      decodeValueFromBytes (fuel + 1) layouts { kind := .uint w, layoutIdx := li } bs =
        decodeValueFromBytes (fuel + 1) layouts { kind := .uint w, layoutIdx := li } (stripAbstractBytesProv bs) := by
    intro w li
    unfold decodeValueFromBytes
    dsimp only
    rw [length_stripAbstractBytesProv, decodeScalarBytes_stripAbstractBytesProv]
    cases intCastTargetBytes (.uint w) with
    | none => rfl
    | some exp =>
      dsimp only
      cases Nat.beq (length bs) exp with
      | false => rfl
      | true =>
        dsimp only
        cases decodeScalarBytes bs false with
        | none => rfl
        | some res => rcases res with ⟨sv, prov⟩; rfl
  have hdv_int : ∀ (w : IntTy) (li : LayoutIdx),
      decodeValueFromBytes (fuel + 1) layouts { kind := .int w, layoutIdx := li } bs =
        decodeValueFromBytes (fuel + 1) layouts { kind := .int w, layoutIdx := li } (stripAbstractBytesProv bs) := by
    intro w li
    unfold decodeValueFromBytes
    dsimp only
    rw [length_stripAbstractBytesProv, decodeScalarBytes_stripAbstractBytesProv]
    cases intCastTargetBytes (.int w) with
    | none => rfl
    | some exp =>
      dsimp only
      cases Nat.beq (length bs) exp with
      | false => rfl
      | true =>
        dsimp only
        cases decodeScalarBytes bs true with
        | none => rfl
        | some res => rcases res with ⟨sv, prov⟩; rfl
  rcases ty with ⟨kind, li⟩
  dsimp only at hPrim
  rcases hPrim with rfl | rfl | ⟨w, rfl⟩ | ⟨w, rfl⟩ | ⟨fk, rfl⟩
  · unfold decodeTypedValueFromBytes normalizeCodecTy
    dsimp only
    rw [abstractBytesHaveProv_stripAbstractBytesProv]
    exact hdv_bool
  · unfold decodeTypedValueFromBytes normalizeCodecTy
    dsimp only
    rw [abstractBytesHaveProv_stripAbstractBytesProv]
    exact hdv_char
  · unfold decodeTypedValueFromBytes normalizeCodecTy
    dsimp only
    rw [abstractBytesHaveProv_stripAbstractBytesProv]
    cases w with
    | isize =>
      dsimp only
      rw [length_stripAbstractBytesProv, decodeScalarBytes_stripAbstractBytesProv]
      cases Nat.beq (layoutPointerBytes layouts) 4 with
      | true =>
        dsimp only
        cases Nat.beq (length bs) 4 with
        | false => rfl
        | true =>
          dsimp only
          cases decodeScalarBytes bs true with
          | none => rfl
          | some res => rcases res with ⟨sv, prov⟩; rfl
      | false => exact hdv_int .isize li
    | _ => exact hdv_int _ li
  · unfold decodeTypedValueFromBytes normalizeCodecTy
    dsimp only
    rw [abstractBytesHaveProv_stripAbstractBytesProv]
    cases w with
    | usize =>
      dsimp only
      rw [length_stripAbstractBytesProv, decodeScalarBytes_stripAbstractBytesProv]
      cases Nat.beq (layoutPointerBytes layouts) 4 with
      | true =>
        dsimp only
        cases Nat.beq (length bs) 4 with
        | false => rfl
        | true =>
          dsimp only
          cases decodeScalarBytes bs false with
          | none => rfl
          | some res => rcases res with ⟨sv, prov⟩; rfl
      | false => exact hdv_uint .usize li
    | _ => exact hdv_uint _ li
  · unfold decodeTypedValueFromBytes normalizeCodecTy
    dsimp only
    cases fk <;>
    · simp only [byteCodecScalarKind, abstractBytesHaveProv_stripAbstractBytesProv]
      exact hdv_uint _ 0

/-- Closed-form provenance erasure on non-pointer scalar-tagged multi-variant enums
(`VariantsShape.multiple` with `scalarLayoutIsPointer tag = false` and
`backendReprHasPointer l.backendRepr = false`). -/
theorem decodeTypedValueFromBytes_adt_multiple_strip_eq_strict_stripProv
    (fuel : Nat) (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy)
    (li : LayoutIdx) (l : TypeLayout) (tag : ScalarLayout) (tagField : Nat)
    (varShapes : List FieldsShape) (bs : List AbstractByte)
    (hlu : LayoutTable.lookup layouts li = .some l)
    (hvar : l.variants = .multiple tag tagField varShapes)
    (hTagNp : scalarLayoutIsPointer tag = false)
    (hBrNp : backendReprHasPointer l.backendRepr = false) :
    decodeTypedValueFromBytes (fuel + 1) layouts { kind := .adt defPath args, layoutIdx := li } bs .stripProvenance =
      decodeTypedValueFromBytes (fuel + 1) layouts { kind := .adt defPath args, layoutIdx := li }
        (stripAbstractBytesProv bs) .strictUcg630Ub := by
  have hdecSpan : ∀ totalSize offsets,
      decodeFieldsBySpan (stripAbstractBytesProv bs) totalSize offsets =
        decodeFieldsBySpan bs totalSize offsets := by
    intro totalSize offsets
    induction offsets with
    | nil => rfl
    | cons off offRest ih =>
      unfold decodeFieldsBySpan
      dsimp only
      have hspan_step : ∀ (nextOff : Nat),
          (match Nat.ble off.bytes nextOff with
           | false => none
           | true =>
             let span := Nat.sub nextOff off.bytes
             match sliceAbstractBytes (stripAbstractBytesProv bs) off.bytes span with
             | none => none
             | some fSlice =>
               match (match Nat.beq span 0 with
                      | true => some Value.unit
                      | false =>
                        match decodeScalarBytes fSlice false with
                        | some (sv, _) => some (.scalar sv)
                        | none => none) with
               | none => none
               | some v =>
                 match decodeFieldsBySpan (stripAbstractBytesProv bs) totalSize offRest with
                 | some vs => some (v :: vs)
                 | none => none) =
          (match Nat.ble off.bytes nextOff with
           | false => none
           | true =>
             let span := Nat.sub nextOff off.bytes
             match sliceAbstractBytes bs off.bytes span with
             | none => none
             | some fSlice =>
               match (match Nat.beq span 0 with
                      | true => some Value.unit
                      | false =>
                        match decodeScalarBytes fSlice false with
                        | some (sv, _) => some (.scalar sv)
                        | none => none) with
               | none => none
               | some v =>
                 match decodeFieldsBySpan bs totalSize offRest with
                 | some vs => some (v :: vs)
                 | none => none) := by
        intro nextOff
        cases Nat.ble off.bytes nextOff with
        | false => rfl
        | true =>
          dsimp only
          rw [sliceAbstractBytes_stripAbstractBytesProv]
          cases sliceAbstractBytes bs off.bytes (Nat.sub nextOff off.bytes) with
          | none => rfl
          | some fSlice =>
            dsimp only [Option.map]
            cases Nat.beq (Nat.sub nextOff off.bytes) 0 with
            | true => dsimp only; rw [ih]
            | false =>
              dsimp only
              rw [decodeScalarBytes_stripAbstractBytesProv, ih]
              cases decodeScalarBytes fSlice false with
              | none => rfl
              | some res => rcases res with ⟨sv, prov⟩; rfl
      exact hspan_step _
  have hdecTag : ∀ tagSlice,
      decodeScalarLayoutBytes tag (stripAbstractBytesProv tagSlice) =
        decodeScalarLayoutBytes tag tagSlice := by
    intro tagSlice
    unfold decodeScalarLayoutBytes
    rw [length_stripAbstractBytesProv, decodeScalarBytes_stripAbstractBytesProv]
    cases scalarLayoutByteWidth tag with
    | none => rfl
    | some sz =>
      dsimp only
      cases Nat.beq (length tagSlice) sz with
      | false => rfl
      | true =>
        dsimp only
        cases tag with
        | initialized pk vr =>
          dsimp only
          cases pk with
          | pointer _ => cases hTagNp
          | int _ _ =>
            cases decodeScalarBytes tagSlice false with
            | none => rfl
            | some res => rcases res with ⟨sv, prov⟩; rfl
          | float _ =>
            cases decodeScalarBytes tagSlice false with
            | none => rfl
            | some res => rcases res with ⟨sv, prov⟩; rfl
        | union pk =>
          dsimp only
          cases pk with
          | pointer _ => cases hTagNp
          | int _ _ =>
            cases decodeScalarBytes tagSlice false with
            | none => rfl
            | some res => rcases res with ⟨sv, prov⟩; rfl
          | float _ =>
            cases decodeScalarBytes tagSlice false with
            | none => rfl
            | some res => rcases res with ⟨sv, prov⟩; rfl
  unfold decodeTypedValueFromBytes normalizeCodecTy
  dsimp only
  rw [hlu]
  dsimp only
  rw [length_stripAbstractBytesProv]
  cases hsz : Bool.or l.isUninhabited (Bool.not (Nat.beq (length bs) l.size.bytes)) with
  | true => rfl
  | false =>
    dsimp only
    rw [hvar]
    dsimp only
    rw [hTagNp, hBrNp, abstractBytesHaveProv_stripAbstractBytesProv]
    dsimp only [Bool.or]
    unfold decodeValueFromBytes
    dsimp only
    rw [hlu]
    dsimp only
    rw [length_stripAbstractBytesProv, hsz]
    dsimp only
    rw [hvar]
    dsimp only
    cases l.fields with
    | arbitrary outerOffsets _ =>
      cases scalarLayoutByteWidth tag with
      | none => rfl
      | some tagSz =>
        dsimp only
        cases get? outerOffsets tagField with
        | none => rfl
        | some tagOff =>
          dsimp only
          rw [sliceAbstractBytes_stripAbstractBytesProv]
          cases sliceAbstractBytes bs tagOff.bytes tagSz with
          | none => rfl
          | some tagSlice =>
            dsimp only [Option.map]
            rw [hdecTag tagSlice]
            cases decodeScalarLayoutBytes tag tagSlice with
            | none => rfl
            | some tagVal =>
              cases tagVal with
              | scalar tagSc =>
                dsimp only
                cases resolveEnumVariantIdxByTag l.variantDiscriminants tagSc.bits with
                | none => rfl
                | some varIdx =>
                  dsimp only
                  cases get? varShapes varIdx with
                  | none => rfl
                  | some vshape =>
                    cases vshape with
                    | arbitrary varOffsets _ =>
                      dsimp only
                      rw [hdecSpan l.size.bytes varOffsets]
                    | _ => rfl
              | _ => rfl
    | _ => rfl

/-- Stripping provenance from every byte destroys uniform pointer provenance on every buffer. -/
theorem abstractBytesUniformProv_stripAbstractBytesProv (bs : List AbstractByte) :
    abstractBytesUniformProv (stripAbstractBytesProv bs) = false := by
  cases bs with
  | nil => rfl
  | cons b _ => cases b <;> rfl

private theorem decodeArrayChunksWith_stripAbstractBytesProv
    (f g : List AbstractByte → Option Value)
    (hfg : ∀ chunk, f chunk = g (stripAbstractBytesProv chunk))
    (elemSize : Nat) :
    ∀ count bs,
      decodeArrayChunksWith f elemSize count bs =
        decodeArrayChunksWith g elemSize count (stripAbstractBytesProv bs) := by
  intro count
  induction count with
  | zero =>
    intro bs
    cases bs <;> rfl
  | succ k ih =>
    intro bs
    unfold decodeArrayChunksWith
    rw [length_stripAbstractBytesProv]
    cases Nat.ble elemSize (length bs) with
    | false => rfl
    | true =>
      dsimp only
      rw [takeAbstractBytes_stripAbstractBytesProv, dropAbstractBytes_stripAbstractBytesProv,
        hfg (takeAbstractBytes elemSize bs)]
      cases g (stripAbstractBytesProv (takeAbstractBytes elemSize bs)) with
      | none => rfl
      | some _ => dsimp only; rw [ih (dropAbstractBytes elemSize bs)]

private theorem decodeArrayChunksWith_congr
    (f g : List AbstractByte → Option Value)
    (hfg : ∀ chunk, f chunk = g chunk)
    (elemSize : Nat) :
    ∀ count bs,
      decodeArrayChunksWith f elemSize count bs =
        decodeArrayChunksWith g elemSize count bs := by
  intro count
  induction count with
  | zero => intro bs; cases bs <;> rfl
  | succ k ih =>
    intro bs
    unfold decodeArrayChunksWith
    cases Nat.ble elemSize (length bs) with
    | false => rfl
    | true =>
      dsimp only
      rw [hfg (takeAbstractBytes elemSize bs)]
      cases g (takeAbstractBytes elemSize bs) with
      | none => rfl
      | some _ => dsimp only; rw [ih (dropAbstractBytes elemSize bs)]

private theorem decodeFieldsAtOffsetsWith_stripAbstractBytesProv
    (f g : RigidTy → List AbstractByte → Option Value)
    (sizeOfKind : RigidTy → Option Nat)
    (bs : List AbstractByte) :
    ∀ offsets ks,
      (∀ k, k ∈ ks → ∀ chunk, f k chunk = g k (stripAbstractBytesProv chunk)) →
      decodeFieldsAtOffsetsWith f sizeOfKind bs offsets ks =
        decodeFieldsAtOffsetsWith g sizeOfKind (stripAbstractBytesProv bs) offsets ks := by
  intro offsets
  induction offsets with
  | nil => intro ks _; cases ks <;> rfl
  | cons off offRest ih =>
    intro ks hfg
    cases ks with
    | nil => rfl
    | cons k kRest =>
      unfold decodeFieldsAtOffsetsWith
      cases sizeOfKind k with
      | none => rfl
      | some fSize =>
        dsimp only
        rw [sliceAbstractBytes_stripAbstractBytesProv]
        cases sliceAbstractBytes bs off.bytes fSize with
        | none => rfl
        | some fSlice =>
          dsimp only [Option.map]
          rw [hfg k List.mem_cons_self fSlice]
          cases g k (stripAbstractBytesProv fSlice) with
          | none => rfl
          | some _ =>
            dsimp only
            rw [ih kRest (fun k' hk' => hfg k' (List.mem_cons_of_mem k hk'))]

private theorem decodeSeqFieldsWith_stripAbstractBytesProv
    (f g : RigidTy → List AbstractByte → Option Value)
    (sizeOfKind : RigidTy → Option Nat) :
    ∀ ks bs,
      (∀ k, k ∈ ks → ∀ chunk, f k chunk = g k (stripAbstractBytesProv chunk)) →
      decodeSeqFieldsWith f sizeOfKind ks bs =
        decodeSeqFieldsWith g sizeOfKind ks (stripAbstractBytesProv bs) := by
  intro ks
  induction ks with
  | nil => intro bs _; cases bs <;> rfl
  | cons k kRest ih =>
    intro bs hfg
    unfold decodeSeqFieldsWith
    cases sizeOfKind k with
    | none => rfl
    | some fSize =>
      dsimp only
      rw [length_stripAbstractBytesProv]
      cases Nat.ble fSize (length bs) with
      | false => rfl
      | true =>
        dsimp only
        rw [takeAbstractBytes_stripAbstractBytesProv, dropAbstractBytes_stripAbstractBytesProv,
          hfg k List.mem_cons_self (takeAbstractBytes fSize bs)]
        cases g k (stripAbstractBytesProv (takeAbstractBytes fSize bs)) with
        | none => rfl
        | some _ =>
          dsimp only
          rw [ih (dropAbstractBytes fSize bs) (fun k' hk' => hfg k' (List.mem_cons_of_mem k hk'))]

private theorem decodeTypedKindsAndLayoutsAtOffsets_stripAbstractBytesProv
    (f g : Ty → List AbstractByte → Option Value)
    (layouts : LayoutTable) (bs : List AbstractByte) :
    ∀ offsets ks fls,
      (∀ k, k ∈ ks → ∀ fIdx chunk,
        f { kind := k, layoutIdx := fIdx } chunk =
          g { kind := k, layoutIdx := fIdx } (stripAbstractBytesProv chunk)) →
      decodeTypedKindsAndLayoutsAtOffsets f layouts bs offsets ks fls =
        decodeTypedKindsAndLayoutsAtOffsets g layouts (stripAbstractBytesProv bs) offsets ks fls := by
  intro offsets
  induction offsets with
  | nil =>
    intro ks fls _
    cases ks <;> cases fls <;> rfl
  | cons off offRest ih =>
    intro ks fls hfg
    cases ks with
    | nil => cases fls <;> rfl
    | cons k kRest =>
      cases fls with
      | nil => rfl
      | cons fIdx fRest =>
        unfold decodeTypedKindsAndLayoutsAtOffsets
        cases LayoutTable.lookup layouts fIdx with
        | none => rfl
        | some fl =>
          dsimp only
          rw [sliceAbstractBytes_stripAbstractBytesProv]
          cases sliceAbstractBytes bs off.bytes fl.size.bytes with
          | none => rfl
          | some fSlice =>
            dsimp only [Option.map]
            rw [hfg k List.mem_cons_self fIdx fSlice]
            cases g { kind := k, layoutIdx := fIdx } (stripAbstractBytesProv fSlice) with
            | none => rfl
            | some _ =>
              dsimp only
              rw [ih kRest fRest (fun k' hk' => hfg k' (List.mem_cons_of_mem k hk'))]

private theorem decodeFieldsByLayoutIdxs_stripAbstractBytesProv
    (f g : Nat → List AbstractByte → Option Value)
    (layouts : LayoutTable) (bs : List AbstractByte) :
    ∀ offsets fls,
      (∀ fIdx, fIdx ∈ fls → ∀ chunk, f fIdx chunk = g fIdx (stripAbstractBytesProv chunk)) →
      decodeFieldsByLayoutIdxs f layouts bs offsets fls =
        decodeFieldsByLayoutIdxs g layouts (stripAbstractBytesProv bs) offsets fls := by
  intro offsets
  induction offsets with
  | nil => intro fls _; cases fls <;> rfl
  | cons off offRest ih =>
    intro fls hfg
    cases fls with
    | nil => rfl
    | cons fIdx fRest =>
      unfold decodeFieldsByLayoutIdxs
      cases LayoutTable.lookup layouts fIdx with
      | none => rfl
      | some fl =>
        dsimp only
        rw [sliceAbstractBytes_stripAbstractBytesProv]
        cases sliceAbstractBytes bs off.bytes fl.size.bytes with
        | none => rfl
        | some fSlice =>
          dsimp only [Option.map]
          rw [hfg fIdx List.mem_cons_self fSlice]
          cases g fIdx (stripAbstractBytesProv fSlice) with
          | none => rfl
          | some _ =>
            dsimp only
            rw [ih fRest (fun fIdx' hf' => hfg fIdx' (List.mem_cons_of_mem fIdx hf'))]

private theorem decodeRichFieldSpecs_stripAbstractBytesProv
    (f g : Ty → List AbstractByte → Option Value)
    (bs : List AbstractByte) :
    ∀ specs,
      (∀ spec, spec ∈ specs → ∀ chunk, f spec.2.2 chunk = g spec.2.2 (stripAbstractBytesProv chunk)) →
      decodeRichFieldSpecs f bs specs =
        decodeRichFieldSpecs g (stripAbstractBytesProv bs) specs := by
  intro specs
  induction specs with
  | nil => intro _; rfl
  | cons spec rest ih =>
    intro hfg
    unfold decodeRichFieldSpecs
    rw [sliceAbstractBytes_stripAbstractBytesProv]
    cases sliceAbstractBytes bs spec.1 spec.2.1 with
    | none => rfl
    | some fSlice =>
      dsimp only [Option.map]
      rw [hfg spec List.mem_cons_self fSlice]
      cases g spec.2.2 (stripAbstractBytesProv fSlice) with
      | none => rfl
      | some _ =>
        dsimp only
        rw [ih (fun s hs => hfg s (List.mem_cons_of_mem spec hs))]

private theorem normalizeCodecTy_array (elemKind : RigidTy) (n : Nat) (li : LayoutIdx) :
    normalizeCodecTy { kind := .array elemKind n, layoutIdx := li } =
      { kind := .array (byteCodecScalarKind elemKind) n, layoutIdx := li } := by
  cases elemKind <;> rfl

private theorem decodeTypedValueFromBytes_byteCodecScalarKind
    (fuel : Nat) (layouts : LayoutTable) (k : RigidTy) (li : LayoutIdx)
    (bs : List AbstractByte) (p : Ptr2IntTransmutePolicy) :
    decodeTypedValueFromBytes fuel layouts { kind := byteCodecScalarKind k, layoutIdx := li } bs p =
      decodeTypedValueFromBytes fuel layouts { kind := k, layoutIdx := li } bs p := by
  cases fuel with
  | zero => rfl
  | succ _ =>
    cases k with
    | float fk => cases fk <;> rfl
    | _ => rfl

private theorem decodeTypedKindByteSize_byteCodecScalarKind
    (layouts : LayoutTable) (k : RigidTy) :
    decodeTypedKindByteSize layouts (byteCodecScalarKind k) = decodeTypedKindByteSize layouts k := by
  cases k with
  | float fk => cases fk <;> rfl
  | _ => rfl

private theorem mem_mapByteCodecScalarKinds {k : RigidTy} :
    ∀ ks, k ∈ mapByteCodecScalarKinds ks → ∃ k₀, k₀ ∈ ks ∧ k = byteCodecScalarKind k₀
  | .nil, h => by cases h
  | k₀ :: ks, h => by
    cases h with
    | head => exact ⟨k₀, List.mem_cons_self, rfl⟩
    | tail _ h' =>
      obtain ⟨k₁, hm, heq⟩ := mem_mapByteCodecScalarKinds ks h'
      exact ⟨k₁, List.mem_cons_of_mem k₀ hm, heq⟩

/-- **Closed-form provenance erasure for arrays (`[T; n]`)**: whenever decoding an element
under `.stripProvenance` equals decoding `stripAbstractBytesProv chunk` under `.strictUcg630Ub`
(e.g. any array of integers, floats, `bool`, `char`, or nested non-pointer composites),
the same closed-form erasure holds for the entire array `[T; n]`. -/
theorem decodeTypedValueFromBytes_array_strip_eq_strict_stripProv
    (fuel : Nat) (layouts : LayoutTable) (elemKind : RigidTy) (n : Nat) (li : LayoutIdx)
    (bs : List AbstractByte)
    (hElem : ∀ elemLi chunk,
      decodeTypedValueFromBytes fuel layouts { kind := elemKind, layoutIdx := elemLi } chunk .stripProvenance =
        decodeTypedValueFromBytes fuel layouts { kind := elemKind, layoutIdx := elemLi }
          (stripAbstractBytesProv chunk) .strictUcg630Ub) :
    decodeTypedValueFromBytes (fuel + 1) layouts { kind := .array elemKind n, layoutIdx := li } bs .stripProvenance =
      decodeTypedValueFromBytes (fuel + 1) layouts { kind := .array elemKind n, layoutIdx := li }
        (stripAbstractBytesProv bs) .strictUcg630Ub := by
  have hElem' : ∀ elemLi chunk,
      decodeTypedValueFromBytes fuel layouts { kind := byteCodecScalarKind elemKind, layoutIdx := elemLi } chunk .stripProvenance =
        decodeTypedValueFromBytes fuel layouts { kind := byteCodecScalarKind elemKind, layoutIdx := elemLi }
          (stripAbstractBytesProv chunk) .strictUcg630Ub := fun elemLi chunk => by
    rw [decodeTypedValueFromBytes_byteCodecScalarKind, decodeTypedValueFromBytes_byteCodecScalarKind]
    exact hElem elemLi chunk
  unfold decodeTypedValueFromBytes
  rw [normalizeCodecTy_array]
  dsimp only
  cases Nat.beq n 0 with
  | true =>
    cases bs <;> rfl
  | false =>
    dsimp only
    let ek := byteCodecScalarKind elemKind
    have hfallback : ∀ (elemSzOpt : Option Nat),
        (match elemSzOpt with
         | .none => (.none : Option Value)
         | .some elemSz =>
           match Nat.beq (length bs) (Nat.mul elemSz n) with
           | false => .none
           | true =>
             match decodeArrayChunksWith
                 (fun chunk => decodeTypedValueFromBytes fuel layouts { kind := ek, layoutIdx := 0 } chunk .stripProvenance)
                 elemSz n bs with
             | .some elems => .some (.aggregate 0 elems)
             | .none => .none) =
        (match elemSzOpt with
         | .none => (.none : Option Value)
         | .some elemSz =>
           match Nat.beq (length (stripAbstractBytesProv bs)) (Nat.mul elemSz n) with
           | false => .none
           | true =>
             match decodeArrayChunksWith
                 (fun chunk => decodeTypedValueFromBytes fuel layouts { kind := ek, layoutIdx := 0 } chunk .strictUcg630Ub)
                 elemSz n (stripAbstractBytesProv bs) with
             | .some elems => .some (.aggregate 0 elems)
             | .none => .none) := by
      intro elemSzOpt
      rw [length_stripAbstractBytesProv]
      cases elemSzOpt with
      | none => rfl
      | some elemSz =>
        dsimp only
        cases Nat.beq (length bs) (Nat.mul elemSz n) with
        | false => rfl
        | true =>
          dsimp only
          rw [decodeArrayChunksWith_stripAbstractBytesProv
            (fun chunk => decodeTypedValueFromBytes fuel layouts { kind := ek, layoutIdx := 0 } chunk .stripProvenance)
            (fun chunk => decodeTypedValueFromBytes fuel layouts { kind := ek, layoutIdx := 0 } chunk .strictUcg630Ub)
            (hElem' 0) elemSz n bs]
    cases LayoutTable.lookup layouts li with
    | none => exact hfallback _
    | some l =>
      rcases l with ⟨_, _, _, fields, _, _, fieldLayouts, _⟩
      cases fields with
      | array stride _ =>
        cases fieldLayouts with
        | nil => exact hfallback _
        | cons elemFlIdx _ =>
          dsimp only
          rw [length_stripAbstractBytesProv]
          cases Nat.beq (length bs) (Nat.mul stride.bytes n) with
          | false => rfl
          | true =>
            dsimp only
            rw [decodeArrayChunksWith_stripAbstractBytesProv
              (fun chunk => decodeTypedValueFromBytes fuel layouts { kind := ek, layoutIdx := elemFlIdx } chunk .stripProvenance)
              (fun chunk => decodeTypedValueFromBytes fuel layouts { kind := ek, layoutIdx := elemFlIdx } chunk .strictUcg630Ub)
              (hElem' elemFlIdx) stride.bytes n bs]
      | _ => exact hfallback _

/-- **Policy independence on pointer arrays (`[*const T; n]`, `[&T; n]`, `[fn(); n]`)**:
decoding an array whose element type is a pointer/reference/function pointer does not depend
on `Ptr2IntTransmutePolicy` and preserves intact pointer provenance on every element. -/
theorem decodeTypedValueFromBytes_array_policy_independent_ptr
    (fuel : Nat) (layouts : LayoutTable) (elemKind : RigidTy) (n : Nat) (li : LayoutIdx)
    (bs : List AbstractByte)
    (hPtr : (∃ m p, elemKind = .rawPtr m p) ∨ (∃ m p, elemKind = .ref m p) ∨
      (∃ ins out s abi, elemKind = .fnPtr ins out s abi)) :
    decodeTypedValueFromBytes (fuel + 1) layouts { kind := .array elemKind n, layoutIdx := li } bs .strictUcg630Ub =
      decodeTypedValueFromBytes (fuel + 1) layouts { kind := .array elemKind n, layoutIdx := li } bs .stripProvenance := by
  have hbc : byteCodecScalarKind elemKind = elemKind := by
    rcases hPtr with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> rfl
  have hElemEq : ∀ elemLi chunk,
      decodeTypedValueFromBytes fuel layouts { kind := elemKind, layoutIdx := elemLi } chunk .strictUcg630Ub =
        decodeTypedValueFromBytes fuel layouts { kind := elemKind, layoutIdx := elemLi } chunk .stripProvenance := by
    intro elemLi chunk
    cases fuel with
    | zero => rfl
    | succ _ =>
      rcases hPtr with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> rfl
  unfold decodeTypedValueFromBytes
  rw [normalizeCodecTy_array, hbc]
  dsimp only
  cases Nat.beq n 0 with
  | true => rfl
  | false =>
    dsimp only
    have hfallback : ∀ (elemSzOpt : Option Nat),
        (match elemSzOpt with
         | .none => (.none : Option Value)
         | .some elemSz =>
           match Nat.beq (length bs) (Nat.mul elemSz n) with
           | false => .none
           | true =>
             match decodeArrayChunksWith
                 (fun chunk => decodeTypedValueFromBytes fuel layouts { kind := elemKind, layoutIdx := 0 } chunk .strictUcg630Ub)
                 elemSz n bs with
             | .some elems => .some (.aggregate 0 elems)
             | .none => .none) =
        (match elemSzOpt with
         | .none => (.none : Option Value)
         | .some elemSz =>
           match Nat.beq (length bs) (Nat.mul elemSz n) with
           | false => .none
           | true =>
             match decodeArrayChunksWith
                 (fun chunk => decodeTypedValueFromBytes fuel layouts { kind := elemKind, layoutIdx := 0 } chunk .stripProvenance)
                 elemSz n bs with
             | .some elems => .some (.aggregate 0 elems)
             | .none => .none) := by
      intro elemSzOpt
      cases elemSzOpt with
      | none => rfl
      | some elemSz =>
        dsimp only
        cases Nat.beq (length bs) (Nat.mul elemSz n) with
        | false => rfl
        | true =>
          dsimp only
          rw [decodeArrayChunksWith_congr _ _ (hElemEq 0) elemSz n bs]
    cases LayoutTable.lookup layouts li with
    | none => exact hfallback _
    | some l =>
      rcases l with ⟨_, _, _, fields, _, _, fieldLayouts, _⟩
      cases fields with
      | array stride _ =>
        cases fieldLayouts with
        | nil => exact hfallback _
        | cons elemFlIdx _ =>
          dsimp only
          cases Nat.beq (length bs) (Nat.mul stride.bytes n) with
          | false => rfl
          | true =>
            dsimp only
            rw [decodeArrayChunksWith_congr
              (fun chunk => decodeTypedValueFromBytes fuel layouts { kind := elemKind, layoutIdx := elemFlIdx } chunk .strictUcg630Ub)
              (fun chunk => decodeTypedValueFromBytes fuel layouts { kind := elemKind, layoutIdx := elemFlIdx } chunk .stripProvenance)
              (hElemEq elemFlIdx) stride.bytes n bs]
      | _ => exact hfallback _

/-- **Closed-form provenance erasure for non-empty tuples (`(T₀, …, Tₙ)`)**: whenever every
field kind `k ∈ kHead :: kTail` satisfies closed-form erasure at `fuel`, the whole tuple
satisfies `strip(bs) = strict(stripAbstractBytesProv bs)` across both resolved layouts
(`fieldLayouts` or offset fallback) and unresolved sequential layouts. -/
theorem decodeTypedValueFromBytes_tuple_strip_eq_strict_stripProv
    (fuel : Nat) (layouts : LayoutTable) (kHead : RigidTy) (kTail : List RigidTy)
    (li : LayoutIdx) (bs : List AbstractByte)
    (hFields : ∀ k, k ∈ (kHead :: kTail) → ∀ fLi chunk,
      decodeTypedValueFromBytes fuel layouts { kind := k, layoutIdx := fLi } chunk .stripProvenance =
        decodeTypedValueFromBytes fuel layouts { kind := k, layoutIdx := fLi }
          (stripAbstractBytesProv chunk) .strictUcg630Ub) :
    decodeTypedValueFromBytes (fuel + 1) layouts { kind := .tuple (kHead :: kTail), layoutIdx := li } bs .stripProvenance =
      decodeTypedValueFromBytes (fuel + 1) layouts { kind := .tuple (kHead :: kTail), layoutIdx := li }
        (stripAbstractBytesProv bs) .strictUcg630Ub := by
  let ks' := byteCodecScalarKind kHead :: mapByteCodecScalarKinds kTail
  have hFields' : ∀ k, k ∈ ks' → ∀ fLi chunk,
      decodeTypedValueFromBytes fuel layouts { kind := k, layoutIdx := fLi } chunk .stripProvenance =
        decodeTypedValueFromBytes fuel layouts { kind := k, layoutIdx := fLi }
          (stripAbstractBytesProv chunk) .strictUcg630Ub := by
    intro k hk fLi chunk
    obtain ⟨k₀, hm, rfl⟩ := mem_mapByteCodecScalarKinds (kHead :: kTail) hk
    rw [decodeTypedValueFromBytes_byteCodecScalarKind, decodeTypedValueFromBytes_byteCodecScalarKind]
    exact hFields k₀ hm fLi chunk
  have hseq :
      decodeSeqFieldsWith
        (fun k chunk => decodeTypedValueFromBytes fuel layouts { kind := k, layoutIdx := unresolvedLayoutIdx layouts } chunk .stripProvenance)
        (fun k => decodeTypedKindByteSize layouts k) ks' bs =
      decodeSeqFieldsWith
        (fun k chunk => decodeTypedValueFromBytes fuel layouts { kind := k, layoutIdx := unresolvedLayoutIdx layouts } chunk .strictUcg630Ub)
        (fun k => decodeTypedKindByteSize layouts k) ks' (stripAbstractBytesProv bs) :=
    decodeSeqFieldsWith_stripAbstractBytesProv _ _ (fun k => decodeTypedKindByteSize layouts k) ks' bs
      (fun k hk chunk => hFields' k hk (unresolvedLayoutIdx layouts) chunk)
  unfold decodeTypedValueFromBytes normalizeCodecTy
  dsimp only
  cases Bool.not (isUnresolvedLayoutIdx layouts li) with
  | false => dsimp only; rw [hseq]
  | true =>
    dsimp only
    cases LayoutTable.lookup layouts li with
    | none => dsimp only; rw [hseq]
    | some l =>
      dsimp only
      cases layoutMatchesAggregateVariant l 0 (length ks') with
      | false => dsimp only; rw [hseq]
      | true =>
        dsimp only
        rw [length_stripAbstractBytesProv]
        cases Nat.beq (length bs) l.size.bytes with
        | false => rfl
        | true =>
          cases l.fields with
          | arbitrary offsets _ =>
            dsimp only
            cases Bool.and (Nat.beq (length ks') (length offsets))
                (Nat.beq (length l.fieldLayouts) (length offsets)) with
            | true =>
              dsimp only
              rw [decodeTypedKindsAndLayoutsAtOffsets_stripAbstractBytesProv
                (fun cTy chunk => decodeTypedValueFromBytes fuel layouts cTy chunk .stripProvenance)
                (fun cTy chunk => decodeTypedValueFromBytes fuel layouts cTy chunk .strictUcg630Ub)
                layouts bs offsets ks' l.fieldLayouts
                (fun k hk fIdx chunk => hFields' k hk fIdx chunk)]
            | false =>
              dsimp only
              rw [decodeFieldsAtOffsetsWith_stripAbstractBytesProv
                (fun k chunk => decodeTypedValueFromBytes fuel layouts { kind := k, layoutIdx := unresolvedLayoutIdx layouts } chunk .stripProvenance)
                (fun k chunk => decodeTypedValueFromBytes fuel layouts { kind := k, layoutIdx := unresolvedLayoutIdx layouts } chunk .strictUcg630Ub)
                (fun k => decodeTypedKindByteSize layouts k)
                bs offsets ks'
                (fun k hk chunk => hFields' k hk (unresolvedLayoutIdx layouts) chunk)]
          | _ => dsimp only; rw [hseq]

/-- **Closed-form provenance erasure for single-variant layout-backed structs**
(`l.variants = .single variantIdx`, `l.fields = .arbitrary offsets _` with matching
`l.fieldLayouts`): whenever every field layout `fIdx ∈ l.fieldLayouts` satisfies erasure at
`fuel`, the whole struct satisfies `strip(bs) = strict(stripAbstractBytesProv bs)`. -/
theorem decodeTypedValueFromBytes_adt_single_arbitrary_fieldLayouts_strip_eq_strict_stripProv
    (fuel : Nat) (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy)
    (li : LayoutIdx) (l : TypeLayout) (variantIdx : VariantIdx)
    (offsets : List Size) (memOrder : List Nat) (bs : List AbstractByte)
    (hlu : LayoutTable.lookup layouts li = .some l)
    (hvar : l.variants = .single variantIdx)
    (hfld : l.fields = .arbitrary offsets memOrder)
    (hflLen : Nat.beq (length l.fieldLayouts) (length offsets) = true)
    (hFields : ∀ fIdx, fIdx ∈ l.fieldLayouts → ∀ chunk,
      decodeTypedValueFromBytes fuel layouts { kind := .adt "" .nil, layoutIdx := fIdx } chunk .stripProvenance =
        decodeTypedValueFromBytes fuel layouts { kind := .adt "" .nil, layoutIdx := fIdx }
          (stripAbstractBytesProv chunk) .strictUcg630Ub) :
    decodeTypedValueFromBytes (fuel + 1) layouts { kind := .adt defPath args, layoutIdx := li } bs .stripProvenance =
      decodeTypedValueFromBytes (fuel + 1) layouts { kind := .adt defPath args, layoutIdx := li }
        (stripAbstractBytesProv bs) .strictUcg630Ub := by
  unfold decodeTypedValueFromBytes normalizeCodecTy
  dsimp only
  rw [hlu]
  dsimp only
  rw [length_stripAbstractBytesProv]
  cases Bool.or l.isUninhabited (Bool.not (Nat.beq (length bs) l.size.bytes)) with
  | true => rfl
  | false =>
    dsimp only
    rw [hvar, hfld]
    cases variantIdx <;> (
      cases offsets with
      | nil => rfl
      | cons off0 offRest =>
        simp only
        rw [hflLen]
        dsimp only
        rw [decodeFieldsByLayoutIdxs_stripAbstractBytesProv
          (fun fIdx fSlice => decodeTypedValueFromBytes fuel layouts { kind := .adt "" .nil, layoutIdx := fIdx } fSlice .stripProvenance)
          (fun fIdx fSlice => decodeTypedValueFromBytes fuel layouts { kind := .adt "" .nil, layoutIdx := fIdx } fSlice .strictUcg630Ub)
          layouts bs (off0 :: offRest) l.fieldLayouts hFields])

/-- **Closed-form provenance erasure for single-variant `.scalarPair` structs without
`fieldLayouts`**: when both scalar layouts `s₀, s₁` are non-pointer (`scalarLayoutIsPointer = false`),
decoding under `.stripProvenance` equals decoding `stripAbstractBytesProv bs` under `.strictUcg630Ub`. -/
theorem decodeTypedValueFromBytes_adt_single_scalarPair_strip_eq_strict_stripProv
    (fuel : Nat) (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy)
    (li : LayoutIdx) (l : TypeLayout) (variantIdx : VariantIdx)
    (off0 off1 : Size) (memOrder : List Nat) (s0 s1 : ScalarLayout) (bs : List AbstractByte)
    (hlu : LayoutTable.lookup layouts li = .some l)
    (hvar : l.variants = .single variantIdx)
    (hfld : l.fields = .arbitrary [off0, off1] memOrder)
    (hflNe : Nat.beq (length l.fieldLayouts) 2 = false)
    (hbr : l.backendRepr = .scalarPair s0 s1)
    (hs0 : scalarLayoutIsPointer s0 = false)
    (hs1 : scalarLayoutIsPointer s1 = false) :
    decodeTypedValueFromBytes (fuel + 1) layouts { kind := .adt defPath args, layoutIdx := li } bs .stripProvenance =
      decodeTypedValueFromBytes (fuel + 1) layouts { kind := .adt defPath args, layoutIdx := li }
        (stripAbstractBytesProv bs) .strictUcg630Ub := by
  unfold decodeTypedValueFromBytes normalizeCodecTy
  dsimp only
  rw [hlu]
  dsimp only
  rw [length_stripAbstractBytesProv]
  cases Bool.or l.isUninhabited (Bool.not (Nat.beq (length bs) l.size.bytes)) with
  | true => rfl
  | false =>
    dsimp only
    rw [hvar, hfld]
    have hlen2 : length [off0, off1] = 2 := rfl
    cases variantIdx <;> (
      simp only
      rw [hlen2, hflNe, hbr]
      dsimp only
      cases scalarLayoutByteWidth s0 with
      | none => rfl
      | some sz0 =>
        cases scalarLayoutByteWidth s1 with
        | none => rfl
        | some sz1 =>
          dsimp only
          rw [sliceAbstractBytes_stripAbstractBytesProv, sliceAbstractBytes_stripAbstractBytesProv]
          cases sliceAbstractBytes bs off0.bytes sz0 with
          | none => rfl
          | some slice0 =>
            cases sliceAbstractBytes bs off1.bytes sz1 with
            | none => rfl
            | some slice1 =>
              dsimp only [Option.map]
              rw [decodeScalarLayoutBytesNoForge_strip_eq_strict_stripProv s0 slice0 hs0,
                decodeScalarLayoutBytesNoForge_strip_eq_strict_stripProv s1 slice1 hs1])

/-- **Closed-form provenance erasure for single-variant `.primitive` ADTs** (non-pointer
scalar or non-`.scalar` backend representation). -/
theorem decodeTypedValueFromBytes_adt_single_primitive_strip_eq_strict_stripProv
    (fuel : Nat) (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy)
    (li : LayoutIdx) (l : TypeLayout) (variantIdx : VariantIdx) (bs : List AbstractByte)
    (hlu : LayoutTable.lookup layouts li = .some l)
    (hvar : l.variants = .single variantIdx)
    (hfld : l.fields = .primitive)
    (hNonPtr : ∀ s0, l.backendRepr = .scalar s0 → scalarLayoutIsPointer s0 = false) :
    decodeTypedValueFromBytes (fuel + 1) layouts { kind := .adt defPath args, layoutIdx := li } bs .stripProvenance =
      decodeTypedValueFromBytes (fuel + 1) layouts { kind := .adt defPath args, layoutIdx := li }
        (stripAbstractBytesProv bs) .strictUcg630Ub := by
  unfold decodeTypedValueFromBytes normalizeCodecTy
  dsimp only
  rw [hlu]
  dsimp only
  rw [length_stripAbstractBytesProv]
  cases Bool.or l.isUninhabited (Bool.not (Nat.beq (length bs) l.size.bytes)) with
  | true => rfl
  | false =>
    dsimp only
    rw [hvar, hfld]
    cases variantIdx <;> (
      cases Nat.beq l.size.bytes 0 with
      | true => rfl
      | false =>
        dsimp only
        cases hbr : l.backendRepr with
        | scalar s0 =>
          exact decodeScalarLayoutBytesNoForge_strip_eq_strict_stripProv s0 bs (hNonPtr s0 hbr)
        | scalarPair _ _ =>
          rw [abstractBytesHaveProv_stripAbstractBytesProv, decodeScalarBytes_stripAbstractBytesProv]
          dsimp only
          cases decodeScalarBytes bs false with
          | none => rfl
          | some res => rcases res with ⟨sv, _⟩; rfl
        | memory =>
          rw [abstractBytesHaveProv_stripAbstractBytesProv, decodeScalarBytes_stripAbstractBytesProv]
          dsimp only
          cases decodeScalarBytes bs false with
          | none => rfl
          | some res => rcases res with ⟨sv, _⟩; rfl)

/-- **Closed-form provenance erasure for single-variant `.array` ADTs** (`l.fields = .array stride count`):
covers both `l.fieldLayouts = elemFlIdx :: _` (when `elemFlIdx` satisfies erasure) and
`l.fieldLayouts = .nil` (scalar-chunk fallback). -/
theorem decodeTypedValueFromBytes_adt_single_array_strip_eq_strict_stripProv
    (fuel : Nat) (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy)
    (li : LayoutIdx) (l : TypeLayout) (variantIdx : VariantIdx)
    (stride : Size) (count : Nat) (bs : List AbstractByte)
    (hlu : LayoutTable.lookup layouts li = .some l)
    (hvar : l.variants = .single variantIdx)
    (hfld : l.fields = .array stride count)
    (hElem : ∀ elemFlIdx rest, l.fieldLayouts = elemFlIdx :: rest → ∀ chunk,
      decodeTypedValueFromBytes fuel layouts { kind := .adt "" .nil, layoutIdx := elemFlIdx } chunk .stripProvenance =
        decodeTypedValueFromBytes fuel layouts { kind := .adt "" .nil, layoutIdx := elemFlIdx }
          (stripAbstractBytesProv chunk) .strictUcg630Ub) :
    decodeTypedValueFromBytes (fuel + 1) layouts { kind := .adt defPath args, layoutIdx := li } bs .stripProvenance =
      decodeTypedValueFromBytes (fuel + 1) layouts { kind := .adt defPath args, layoutIdx := li }
        (stripAbstractBytesProv bs) .strictUcg630Ub := by
  unfold decodeTypedValueFromBytes normalizeCodecTy
  dsimp only
  rw [hlu]
  dsimp only
  rw [length_stripAbstractBytesProv]
  cases hsz : Bool.or l.isUninhabited (Bool.not (Nat.beq (length bs) l.size.bytes)) with
  | true => rfl
  | false =>
    dsimp only
    rw [hvar, hfld]
    cases variantIdx <;> (
      simp only
      cases Nat.beq count 0 with
      | true => cases bs <;> rfl
      | false =>
        dsimp only
        cases hfl : l.fieldLayouts with
        | cons elemFlIdx rest =>
          dsimp only
          rw [decodeArrayChunksWith_stripAbstractBytesProv
            (fun chunk => decodeTypedValueFromBytes fuel layouts { kind := .adt "" .nil, layoutIdx := elemFlIdx } chunk .stripProvenance)
            (fun chunk => decodeTypedValueFromBytes fuel layouts { kind := .adt "" .nil, layoutIdx := elemFlIdx } chunk .strictUcg630Ub)
            (hElem elemFlIdx rest hfl) stride.bytes count bs]
        | nil =>
          dsimp only
          rw [abstractBytesHaveProv_stripAbstractBytesProv]
          dsimp only
          unfold decodeValueFromBytes
          dsimp only
          rw [hlu]
          dsimp only
          rw [length_stripAbstractBytesProv, hsz]
          dsimp only
          rw [hvar, hfld]
          dsimp only
          congr 1
          exact decodeArrayChunksWith_stripAbstractBytesProv _ _
            (fun chunk => by
              rw [decodeScalarBytes_stripAbstractBytesProv]
              cases decodeScalarBytes chunk false with
              | none => rfl
              | some res => rcases res with ⟨sv, _⟩; rfl)
            stride.bytes count bs)

/-- **Closed-form provenance erasure for `RichAdtSpec.structFields`**: whenever every field spec
satisfies closed-form erasure at `fuel`, the whole rich struct satisfies
`strip(bs) = strict(stripAbstractBytesProv bs)`. -/
theorem decodeTypedValueRichWithPolicy_structFields_strip_eq_strict_stripProv
    (fuel : Nat) (layouts : LayoutTable) (richSpecs : List (DefPath × RichAdtSpec))
    (defPath : DefPath) (args : List RigidTy) (li : LayoutIdx)
    (variantIdx : VariantIdx) (totalBytes : Nat) (fields : List (Nat × Nat × Ty))
    (bs : List AbstractByte)
    (hspec : lookupRichAdtSpec defPath richSpecs = .some (.structFields variantIdx totalBytes fields))
    (hFields : ∀ spec, spec ∈ fields → ∀ chunk,
      decodeTypedValueRichWithPolicy fuel layouts richSpecs spec.2.2 chunk .stripProvenance =
        decodeTypedValueRichWithPolicy fuel layouts richSpecs spec.2.2
          (stripAbstractBytesProv chunk) .strictUcg630Ub) :
    decodeTypedValueRichWithPolicy (fuel + 1) layouts richSpecs
        { kind := .adt defPath args, layoutIdx := li } bs .stripProvenance =
      decodeTypedValueRichWithPolicy (fuel + 1) layouts richSpecs
        { kind := .adt defPath args, layoutIdx := li } (stripAbstractBytesProv bs) .strictUcg630Ub := by
  unfold decodeTypedValueRichWithPolicy normalizeCodecTy
  dsimp only
  rw [hspec]
  dsimp only
  rw [length_stripAbstractBytesProv]
  cases Nat.beq (length bs) totalBytes with
  | false => rfl
  | true =>
    dsimp only
    rw [decodeRichFieldSpecs_stripAbstractBytesProv
      (fun cTy chunk => decodeTypedValueRichWithPolicy fuel layouts richSpecs cTy chunk .stripProvenance)
      (fun cTy chunk => decodeTypedValueRichWithPolicy fuel layouts richSpecs cTy chunk .strictUcg630Ub)
      bs fields hFields]

/-- **Closed-form provenance erasure for `RichAdtSpec.taggedEnum`** (`TagEncoding::Direct`):
the discriminant tag check strips provenance identically to `stripAbstractBytesProv`, so
whenever every variant's payload fields satisfy closed-form erasure at `fuel`, the whole
tagged enum satisfies `strip(bs) = strict(stripAbstractBytesProv bs)`. -/
theorem decodeTypedValueRichWithPolicy_taggedEnum_strip_eq_strict_stripProv
    (fuel : Nat) (layouts : LayoutTable) (richSpecs : List (DefPath × RichAdtSpec))
    (defPath : DefPath) (args : List RigidTy) (li : LayoutIdx)
    (totalBytes tagOff tagBytes : Nat)
    (variants : List (Nat × VariantIdx × List (Nat × Nat × Ty)))
    (bs : List AbstractByte)
    (hspec : lookupRichAdtSpec defPath richSpecs =
      .some (.taggedEnum totalBytes tagOff tagBytes variants))
    (hFields : ∀ entry, entry ∈ variants → ∀ spec, spec ∈ entry.2.2 → ∀ chunk,
      decodeTypedValueRichWithPolicy fuel layouts richSpecs spec.2.2 chunk .stripProvenance =
        decodeTypedValueRichWithPolicy fuel layouts richSpecs spec.2.2
          (stripAbstractBytesProv chunk) .strictUcg630Ub) :
    decodeTypedValueRichWithPolicy (fuel + 1) layouts richSpecs
        { kind := .adt defPath args, layoutIdx := li } bs .stripProvenance =
      decodeTypedValueRichWithPolicy (fuel + 1) layouts richSpecs
        { kind := .adt defPath args, layoutIdx := li } (stripAbstractBytesProv bs) .strictUcg630Ub := by
  have hfindMem : ∀ (tagVal : Nat) (vs : List (Nat × VariantIdx × List (Nat × Nat × Ty)))
      (res : VariantIdx × List (Nat × Nat × Ty)),
      findRichTaggedVariant tagVal vs = .some res →
      ∃ tv, (tv, res) ∈ vs := by
    intro tagVal vs
    induction vs with
    | nil => intro _ h; cases h
    | cons entry rest ih =>
      intro res h
      unfold findRichTaggedVariant at h
      cases hbeq : Nat.beq entry.1 tagVal with
      | true =>
        rw [hbeq] at h; injection h with h; rw [← h]
        exact ⟨entry.1, List.mem_cons_self⟩
      | false =>
        rw [hbeq] at h
        obtain ⟨tv, hmem⟩ := ih res h
        exact ⟨tv, List.mem_cons_of_mem entry hmem⟩
  unfold decodeTypedValueRichWithPolicy normalizeCodecTy
  dsimp only
  rw [hspec]
  dsimp only
  rw [length_stripAbstractBytesProv]
  cases Nat.beq (length bs) totalBytes with
  | false => rfl
  | true =>
    dsimp only
    rw [sliceAbstractBytes_stripAbstractBytesProv]
    cases sliceAbstractBytes bs tagOff tagBytes with
    | none => rfl
    | some tagSlice =>
      dsimp only [Option.map, policyRejectsProv]
      rw [abstractBytesHaveProv_stripAbstractBytesProv, decodeScalarBytes_stripAbstractBytesProv]
      dsimp only
      cases decodeScalarBytes tagSlice false with
      | none => rfl
      | some tagRes =>
        dsimp only
        cases hfv : findRichTaggedVariant tagRes.1.bits variants with
        | none => rfl
        | some varEntry =>
          dsimp only
          obtain ⟨tv, hmem⟩ := hfindMem tagRes.1.bits variants varEntry hfv
          rw [decodeRichFieldSpecs_stripAbstractBytesProv
            (fun cTy chunk => decodeTypedValueRichWithPolicy fuel layouts richSpecs cTy chunk .stripProvenance)
            (fun cTy chunk => decodeTypedValueRichWithPolicy fuel layouts richSpecs cTy chunk .strictUcg630Ub)
            bs varEntry.2 (hFields (tv, varEntry) hmem)]

/-- **Closed-form provenance erasure for `RichAdtSpec.nicheScalarEnum`** (e.g. `Option<bool>`,
`Option<NonZero<u32>>`): whenever all niche and payload fields satisfy closed-form erasure
at `fuel`, the whole scalar-niche enum satisfies `strip(bs) = strict(stripAbstractBytesProv bs)`. -/
theorem decodeTypedValueRichWithPolicy_nicheScalarEnum_strip_eq_strict_stripProv
    (fuel : Nat) (layouts : LayoutTable) (richSpecs : List (DefPath × RichAdtSpec))
    (defPath : DefPath) (args : List RigidTy) (li : LayoutIdx)
    (totalBytes nicheOff nicheBytes nicheValue : Nat)
    (nicheVar : VariantIdx) (nicheFields : List (Nat × Nat × Ty))
    (payloadVar : VariantIdx) (payloadFields : List (Nat × Nat × Ty))
    (bs : List AbstractByte)
    (hspec : lookupRichAdtSpec defPath richSpecs =
      .some (.nicheScalarEnum totalBytes nicheOff nicheBytes nicheValue nicheVar nicheFields payloadVar payloadFields))
    (hNiche : ∀ spec, spec ∈ nicheFields → ∀ chunk,
      decodeTypedValueRichWithPolicy fuel layouts richSpecs spec.2.2 chunk .stripProvenance =
        decodeTypedValueRichWithPolicy fuel layouts richSpecs spec.2.2
          (stripAbstractBytesProv chunk) .strictUcg630Ub)
    (hPayload : ∀ spec, spec ∈ payloadFields → ∀ chunk,
      decodeTypedValueRichWithPolicy fuel layouts richSpecs spec.2.2 chunk .stripProvenance =
        decodeTypedValueRichWithPolicy fuel layouts richSpecs spec.2.2
          (stripAbstractBytesProv chunk) .strictUcg630Ub) :
    decodeTypedValueRichWithPolicy (fuel + 1) layouts richSpecs
        { kind := .adt defPath args, layoutIdx := li } bs .stripProvenance =
      decodeTypedValueRichWithPolicy (fuel + 1) layouts richSpecs
        { kind := .adt defPath args, layoutIdx := li } (stripAbstractBytesProv bs) .strictUcg630Ub := by
  unfold decodeTypedValueRichWithPolicy normalizeCodecTy
  dsimp only
  rw [hspec]
  dsimp only
  rw [length_stripAbstractBytesProv]
  cases Nat.beq (length bs) totalBytes with
  | false => rfl
  | true =>
    dsimp only
    rw [sliceAbstractBytes_stripAbstractBytesProv]
    cases sliceAbstractBytes bs nicheOff nicheBytes with
    | none => rfl
    | some nicheSlice =>
      dsimp only [Option.map, policyRejectsProv]
      rw [abstractBytesHaveProv_stripAbstractBytesProv, decodeScalarBytes_stripAbstractBytesProv]
      dsimp only
      cases decodeScalarBytes nicheSlice false with
      | none => rfl
      | some nicheRes =>
        dsimp only
        cases Nat.beq nicheRes.1.bits nicheValue with
        | true =>
          dsimp only
          rw [decodeRichFieldSpecs_stripAbstractBytesProv
            (fun cTy chunk => decodeTypedValueRichWithPolicy fuel layouts richSpecs cTy chunk .stripProvenance)
            (fun cTy chunk => decodeTypedValueRichWithPolicy fuel layouts richSpecs cTy chunk .strictUcg630Ub)
            bs nicheFields hNiche]
        | false =>
          dsimp only
          rw [decodeRichFieldSpecs_stripAbstractBytesProv
            (fun cTy chunk => decodeTypedValueRichWithPolicy fuel layouts richSpecs cTy chunk .stripProvenance)
            (fun cTy chunk => decodeTypedValueRichWithPolicy fuel layouts richSpecs cTy chunk .strictUcg630Ub)
            bs payloadFields hPayload]

/-! ### Selective per-field provenance preservation on mixed pointer + integer/float composites

Unlike naive whole-buffer `stripAbstractBytesProv`, `Ptr2IntTransmutePolicy.stripProvenance`
operates **per field**: on a composite mixing a pointer/reference/fnPtr field with a
non-pointer primitive field (integer/float/`bool`/`char`), `.stripProvenance` preserves
intact pointer provenance on the pointer field (identical to `.strictUcg630Ub` on the
unstripped slice) while stripping provenance ONLY on the non-pointer field. -/

/-- **Selective per-field erasure on a resolved 2-field mixed `(ptr, prim)` tuple**:
under `.stripProvenance`, field 0 (`.rawPtr`/`.ref`/`.fnPtr`) decodes `slice₀` identically
to `.strictUcg630Ub` WITHOUT stripping provenance (preserving intact `Value.ptr`), while
field 1 (integer/float/`bool`/`char`) decodes `stripAbstractBytesProv slice₁` under
`.strictUcg630Ub`. -/
theorem decodeTypedValueFromBytes_tuple_pair_mixed_strip
    (fuel : Nat) (layouts : LayoutTable) (k0 k1 : RigidTy) (li : LayoutIdx)
    (l l0 l1 : TypeLayout) (off0 off1 : Size) (memOrder : List Nat) (fl0 fl1 : Nat)
    (bs slice0 slice1 : List AbstractByte)
    (hres : isUnresolvedLayoutIdx layouts li = false)
    (hlu : LayoutTable.lookup layouts li = .some l)
    (hmatch : layoutMatchesAggregateVariant l 0 2 = true)
    (hlen : length bs = l.size.bytes)
    (hfld : l.fields = .arbitrary [off0, off1] memOrder)
    (hfls : l.fieldLayouts = [fl0, fl1])
    (hlu0 : LayoutTable.lookup layouts fl0 = .some l0)
    (hlu1 : LayoutTable.lookup layouts fl1 = .some l1)
    (hsl0 : sliceAbstractBytes bs off0.bytes l0.size.bytes = .some slice0)
    (hsl1 : sliceAbstractBytes bs off1.bytes l1.size.bytes = .some slice1)
    (hPtr0 : (∃ m p, k0 = .rawPtr m p) ∨ (∃ m p, k0 = .ref m p) ∨
      (∃ ins out s abi, k0 = .fnPtr ins out s abi))
    (hPrim1 : k1 = .bool ∨ k1 = .char ∨ (∃ w, k1 = .int w) ∨
      (∃ w, k1 = .uint w) ∨ (∃ fk, k1 = .float fk)) :
    decodeTypedValueFromBytes (fuel + 2) layouts { kind := .tuple [k0, k1], layoutIdx := li } bs .stripProvenance =
      match
        decodeTypedValueFromBytes (fuel + 1) layouts { kind := k0, layoutIdx := fl0 } slice0 .strictUcg630Ub,
        decodeTypedValueFromBytes (fuel + 1) layouts { kind := k1, layoutIdx := fl1 } (stripAbstractBytesProv slice1) .strictUcg630Ub
      with
      | .some v0, .some v1 => .some (.aggregate 0 [v0, v1])
      | _, _ => .none := by
  have hbc0 : byteCodecScalarKind k0 = k0 := by
    rcases hPtr0 with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> rfl
  have h0eq :
      decodeTypedValueFromBytes (fuel + 1) layouts { kind := k0, layoutIdx := fl0 } slice0 .stripProvenance =
        decodeTypedValueFromBytes (fuel + 1) layouts { kind := k0, layoutIdx := fl0 } slice0 .strictUcg630Ub := by
    rcases hPtr0 with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> rfl
  have h1eq :
      decodeTypedValueFromBytes (fuel + 1) layouts { kind := byteCodecScalarKind k1, layoutIdx := fl1 } slice1 .stripProvenance =
        decodeTypedValueFromBytes (fuel + 1) layouts { kind := k1, layoutIdx := fl1 }
          (stripAbstractBytesProv slice1) .strictUcg630Ub := by
    rw [decodeTypedValueFromBytes_byteCodecScalarKind]
    exact decodeTypedValueFromBytes_prim_strip_eq_strict_stripProv fuel layouts { kind := k1, layoutIdx := fl1 }
      slice1 hPrim1
  conv => lhs; unfold decodeTypedValueFromBytes normalizeCodecTy
  dsimp only
  rw [hbc0, hres]
  dsimp only [Bool.not]
  rw [hlu]
  dsimp only
  have hlen2 : length [k0, byteCodecScalarKind k1] = 2 := rfl
  rw [hlen2, hmatch]
  dsimp only
  rw [hlen, Nat.beq_refl, hfld, hfls]
  dsimp only
  have hcond : Bool.and (Nat.beq 2 (length [off0, off1])) (Nat.beq (length [fl0, fl1]) (length [off0, off1])) = true := rfl
  rw [hcond]
  dsimp only
  unfold decodeTypedKindsAndLayoutsAtOffsets
  rw [hlu0]
  dsimp only
  rw [hsl0]
  dsimp only
  rw [h0eq]
  cases decodeTypedValueFromBytes (fuel + 1) layouts { kind := k0, layoutIdx := fl0 } slice0 .strictUcg630Ub with
  | none => rfl
  | some _ =>
    dsimp only
    unfold decodeTypedKindsAndLayoutsAtOffsets
    rw [hlu1]
    dsimp only
    rw [hsl1]
    dsimp only
    rw [h1eq]
    cases decodeTypedValueFromBytes (fuel + 1) layouts { kind := k1, layoutIdx := fl1 }
        (stripAbstractBytesProv slice1) .strictUcg630Ub with
    | none => rfl
    | some _ => rfl

/-- **Selective per-field erasure on an unresolved sequential 2-field mixed `(ptr, prim)` tuple**:
field 0 (`ptr`) keeps intact pointer provenance from `takeAbstractBytes sz0 bs` identically to
`.strictUcg630Ub`, while field 1 (`prim`) decodes `stripAbstractBytesProv` of the remaining
`sz1` bytes under `.strictUcg630Ub`. -/
theorem decodeTypedValueFromBytes_tuple_pair_seq_mixed_strip
    (fuel : Nat) (layouts : LayoutTable) (k0 k1 : RigidTy) (li : LayoutIdx)
    (sz0 sz1 : Nat) (bs : List AbstractByte)
    (hunres : isUnresolvedLayoutIdx layouts li = true)
    (hsz0 : decodeTypedKindByteSize layouts k0 = .some sz0)
    (hsz1 : decodeTypedKindByteSize layouts k1 = .some sz1)
    (hlen : length bs = sz0 + sz1)
    (hPtr0 : (∃ m p, k0 = .rawPtr m p) ∨ (∃ m p, k0 = .ref m p) ∨
      (∃ ins out s abi, k0 = .fnPtr ins out s abi))
    (hPrim1 : k1 = .bool ∨ k1 = .char ∨ (∃ w, k1 = .int w) ∨
      (∃ w, k1 = .uint w) ∨ (∃ fk, k1 = .float fk)) :
    let uLi := unresolvedLayoutIdx layouts
    let slice0 := takeAbstractBytes sz0 bs
    let slice1 := dropAbstractBytes sz0 bs
    decodeTypedValueFromBytes (fuel + 2) layouts { kind := .tuple [k0, k1], layoutIdx := li } bs .stripProvenance =
      match
        decodeTypedValueFromBytes (fuel + 1) layouts { kind := k0, layoutIdx := uLi } slice0 .strictUcg630Ub,
        decodeTypedValueFromBytes (fuel + 1) layouts { kind := k1, layoutIdx := uLi } (stripAbstractBytesProv slice1) .strictUcg630Ub
      with
      | .some v0, .some v1 => .some (.aggregate 0 [v0, v1])
      | _, _ => .none := by
  have hbc0 : byteCodecScalarKind k0 = k0 := by
    rcases hPtr0 with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> rfl
  have hsz1' : decodeTypedKindByteSize layouts (byteCodecScalarKind k1) = .some sz1 := by
    rw [decodeTypedKindByteSize_byteCodecScalarKind]; exact hsz1
  have hdropLen : ∀ n xs, length (dropAbstractBytes n xs) = length xs - n := by
    intro n
    induction n with
    | zero => intro xs; rfl
    | succ k ih =>
      intro xs
      cases xs with
      | nil => exact (Nat.zero_sub (k + 1)).symm
      | cons _ rest =>
        show length (dropAbstractBytes k rest) = (length rest + 1) - (k + 1)
        rw [ih rest, Nat.succ_sub_succ]
  have htakeDropAll : ∀ n xs, length xs = n → takeAbstractBytes n xs = xs ∧ dropAbstractBytes n xs = .nil := by
    intro n
    induction n with
    | zero =>
      intro xs h
      cases xs with
      | nil => exact ⟨rfl, rfl⟩
      | cons _ _ => cases h
    | succ k ih =>
      intro xs h
      cases xs with
      | nil => cases h
      | cons x rest =>
        have hr : length rest = k := Nat.succ.inj h
        obtain ⟨ht, hd⟩ := ih rest hr
        exact ⟨congrArg (List.cons x) ht, hd⟩
  have hble0 : Nat.ble sz0 (length bs) = true := by
    rw [hlen]; exact Nat.ble_eq.mpr (Nat.le_add_right sz0 sz1)
  have hlen1 : length (dropAbstractBytes sz0 bs) = sz1 := by
    rw [hdropLen, hlen, Nat.add_sub_cancel_left]
  have hble1 : Nat.ble sz1 (length (dropAbstractBytes sz0 bs)) = true := by
    rw [hlen1]; exact Nat.ble_eq.mpr (Nat.le_refl sz1)
  obtain ⟨htake1, hdrop1⟩ := htakeDropAll sz1 (dropAbstractBytes sz0 bs) hlen1
  have h0eq :
      decodeTypedValueFromBytes (fuel + 1) layouts { kind := k0, layoutIdx := unresolvedLayoutIdx layouts }
          (takeAbstractBytes sz0 bs) .stripProvenance =
        decodeTypedValueFromBytes (fuel + 1) layouts { kind := k0, layoutIdx := unresolvedLayoutIdx layouts }
          (takeAbstractBytes sz0 bs) .strictUcg630Ub := by
    rcases hPtr0 with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> rfl
  have h1eq :
      decodeTypedValueFromBytes (fuel + 1) layouts { kind := byteCodecScalarKind k1, layoutIdx := unresolvedLayoutIdx layouts }
          (dropAbstractBytes sz0 bs) .stripProvenance =
        decodeTypedValueFromBytes (fuel + 1) layouts { kind := k1, layoutIdx := unresolvedLayoutIdx layouts }
          (stripAbstractBytesProv (dropAbstractBytes sz0 bs)) .strictUcg630Ub := by
    rw [decodeTypedValueFromBytes_byteCodecScalarKind]
    exact decodeTypedValueFromBytes_prim_strip_eq_strict_stripProv fuel layouts
      { kind := k1, layoutIdx := unresolvedLayoutIdx layouts } (dropAbstractBytes sz0 bs) hPrim1
  dsimp only
  conv => lhs; unfold decodeTypedValueFromBytes normalizeCodecTy
  dsimp only
  rw [hbc0, hunres]
  dsimp only [Bool.not]
  unfold decodeSeqFieldsWith
  rw [hsz0]
  dsimp only
  rw [hble0]
  dsimp only
  rw [h0eq]
  cases decodeTypedValueFromBytes (fuel + 1) layouts { kind := k0, layoutIdx := unresolvedLayoutIdx layouts }
      (takeAbstractBytes sz0 bs) .strictUcg630Ub with
  | none => rfl
  | some _ =>
    dsimp only
    unfold decodeSeqFieldsWith
    rw [hsz1']
    dsimp only
    rw [hble1]
    dsimp only
    rw [htake1, hdrop1, h1eq]
    cases decodeTypedValueFromBytes (fuel + 1) layouts { kind := k1, layoutIdx := unresolvedLayoutIdx layouts }
        (stripAbstractBytesProv (dropAbstractBytes sz0 bs)) .strictUcg630Ub with
    | none => rfl
    | some _ => rfl

/-- **Selective per-field erasure on a mixed `(ptr, non-ptr)` `.scalarPair` struct**:
field 0 (`scalarLayoutIsPointer s0 = true`) decodes `slice0` identically to `.strictUcg630Ub`
(preserving intact pointer provenance), while field 1 (`scalarLayoutIsPointer s1 = false`)
decodes `stripAbstractBytesProv slice1` under `.strictUcg630Ub`. -/
theorem decodeTypedValueFromBytes_adt_scalarPair_mixed_strip
    (fuel : Nat) (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy)
    (li : LayoutIdx) (l : TypeLayout) (variantIdx : VariantIdx)
    (off0 off1 : Size) (memOrder : List Nat) (s0 s1 : ScalarLayout)
    (sz0 sz1 : Nat) (bs slice0 slice1 : List AbstractByte)
    (hlu : LayoutTable.lookup layouts li = .some l)
    (hinh : l.isUninhabited = false)
    (hlen : length bs = l.size.bytes)
    (hvar : l.variants = .single variantIdx)
    (hfld : l.fields = .arbitrary [off0, off1] memOrder)
    (hflNe : Nat.beq (length l.fieldLayouts) 2 = false)
    (hbr : l.backendRepr = .scalarPair s0 s1)
    (hw0 : scalarLayoutByteWidth s0 = .some sz0)
    (hw1 : scalarLayoutByteWidth s1 = .some sz1)
    (hsl0 : sliceAbstractBytes bs off0.bytes sz0 = .some slice0)
    (hsl1 : sliceAbstractBytes bs off1.bytes sz1 = .some slice1)
    (hs0 : scalarLayoutIsPointer s0 = true)
    (hs1 : scalarLayoutIsPointer s1 = false) :
    decodeTypedValueFromBytes (fuel + 1) layouts { kind := .adt defPath args, layoutIdx := li } bs .stripProvenance =
      match
        decodeScalarLayoutBytesNoForge s0 slice0 .strictUcg630Ub,
        decodeScalarLayoutBytesNoForge s1 (stripAbstractBytesProv slice1) .strictUcg630Ub
      with
      | .some v0, .some v1 => .some (.aggregate variantIdx [v0, v1])
      | _, _ => .none := by
  have h0eq : decodeScalarLayoutBytesNoForge s0 slice0 .stripProvenance =
      decodeScalarLayoutBytesNoForge s0 slice0 .strictUcg630Ub := by
    unfold decodeScalarLayoutBytesNoForge
    cases s0 with
    | initialized pk _ =>
      cases pk with
      | pointer _ => rfl
      | int _ _ => cases hs0
      | float _ => cases hs0
    | union pk =>
      cases pk with
      | pointer _ => rfl
      | int _ _ => cases hs0
      | float _ => cases hs0
  unfold decodeTypedValueFromBytes normalizeCodecTy
  dsimp only
  rw [hlu]
  dsimp only
  rw [hinh, hlen, Nat.beq_refl]
  dsimp only [Bool.not, Bool.or]
  rw [hvar, hfld]
  have hlen2 : length [off0, off1] = 2 := rfl
  cases variantIdx <;> (
    simp only
    rw [hlen2, hflNe, hbr]
    dsimp only
    rw [hw0, hw1]
    dsimp only
    rw [hsl0, hsl1]
    dsimp only
    rw [h0eq, decodeScalarLayoutBytesNoForge_strip_eq_strict_stripProv s1 slice1 hs1]
    rfl)

/-- **Policy independence on pointer and union targets** in `decodeTypedValueFromBytes`
and `decodeTypedValueRichWithPolicy`. -/
theorem decodeTypedValueFromBytes_policy_independent_ptr_and_union
    (fuel : Nat) (layouts : LayoutTable) (ty : Ty) (bs : List AbstractByte)
    (hTarget : (∃ m p, ty.kind = .rawPtr m p) ∨
      (∃ m p, ty.kind = .ref m p) ∨
      (∃ ins out s abi, ty.kind = .fnPtr ins out s abi) ∨
      (∃ dp args l count, ty.kind = .adt dp args ∧
        LayoutTable.lookup layouts ty.layoutIdx = .some l ∧
        l.variants = .single 0 ∧ l.fields = .union count)) :
    decodeTypedValueFromBytes fuel layouts ty bs .strictUcg630Ub =
      decodeTypedValueFromBytes fuel layouts ty bs .stripProvenance := by
  cases fuel with
  | zero => rfl
  | succ fuel' =>
    rcases ty with ⟨kind, li⟩
    dsimp only at hTarget
    rcases hTarget with ⟨m, p, rfl⟩ | ⟨m, p, rfl⟩ | ⟨ins, out, s, abi, rfl⟩ | ⟨dp, args, l, count, rfl, hlu, hvar, hfld⟩
    · rfl
    · rfl
    · rfl
    · unfold decodeTypedValueFromBytes normalizeCodecTy
      dsimp only
      rw [hlu]
      dsimp only
      rw [hvar, hfld]
      cases Bool.or l.isUninhabited (Bool.not (Nat.beq (length bs) l.size.bytes)) <;> rfl

theorem decodeTypedValueRichWithPolicy_policy_independent_ptr
    (fuel : Nat) (layouts : LayoutTable) (richSpecs : List (DefPath × RichAdtSpec))
    (ty : Ty) (bs : List AbstractByte)
    (hTarget : (∃ m p, ty.kind = .rawPtr m p) ∨
      (∃ m p, ty.kind = .ref m p) ∨
      (∃ ins out s abi, ty.kind = .fnPtr ins out s abi)) :
    decodeTypedValueRichWithPolicy fuel layouts richSpecs ty bs .strictUcg630Ub =
      decodeTypedValueRichWithPolicy fuel layouts richSpecs ty bs .stripProvenance := by
  cases fuel with
  | zero => rfl
  | succ fuel' =>
    rcases ty with ⟨kind, li⟩
    dsimp only at hTarget
    rcases hTarget with ⟨m, p, rfl⟩ | ⟨m, p, rfl⟩ | ⟨ins, out, s, abi, rfl⟩ <;> rfl

/-- **Selective per-field erasure on a mixed 2-field `RichAdtSpec.structFields`**:
field 0 (pointer/reference/fnPtr) decodes `slice0` via `.strictUcg630Ub` without stripping
provenance, while field 1 (non-pointer primitive) decodes `stripAbstractBytesProv slice1` via
`.strictUcg630Ub`. -/
theorem decodeTypedValueRichWithPolicy_structFields_mixed_strip
    (fuel : Nat) (layouts : LayoutTable) (richSpecs : List (DefPath × RichAdtSpec))
    (defPath : DefPath) (args : List RigidTy) (li : LayoutIdx)
    (variantIdx : VariantIdx) (totalBytes off0 sz0 off1 sz1 : Nat) (ty0 ty1 : Ty)
    (bs slice0 slice1 : List AbstractByte)
    (hspec : lookupRichAdtSpec defPath richSpecs =
      .some (.structFields variantIdx totalBytes [(off0, sz0, ty0), (off1, sz1, ty1)]))
    (hlen : length bs = totalBytes)
    (hsl0 : sliceAbstractBytes bs off0 sz0 = .some slice0)
    (hsl1 : sliceAbstractBytes bs off1 sz1 = .some slice1)
    (hPtr0 : (∃ m p, ty0.kind = .rawPtr m p) ∨ (∃ m p, ty0.kind = .ref m p) ∨
      (∃ ins out s abi, ty0.kind = .fnPtr ins out s abi))
    (hPrim1 : ty1.kind = .bool ∨ ty1.kind = .char ∨ (∃ w, ty1.kind = .int w) ∨
      (∃ w, ty1.kind = .uint w) ∨ (∃ fk, ty1.kind = .float fk)) :
    decodeTypedValueRichWithPolicy (fuel + 2) layouts richSpecs
        { kind := .adt defPath args, layoutIdx := li } bs .stripProvenance =
      match
        decodeTypedValueRichWithPolicy (fuel + 1) layouts richSpecs ty0 slice0 .strictUcg630Ub,
        decodeTypedValueRichWithPolicy (fuel + 1) layouts richSpecs ty1 (stripAbstractBytesProv slice1) .strictUcg630Ub
      with
      | .some v0, .some v1 => .some (.aggregate variantIdx [v0, v1])
      | _, _ => .none := by
  have h0eq :
      decodeTypedValueRichWithPolicy (fuel + 1) layouts richSpecs ty0 slice0 .stripProvenance =
        decodeTypedValueRichWithPolicy (fuel + 1) layouts richSpecs ty0 slice0 .strictUcg630Ub :=
    (decodeTypedValueRichWithPolicy_policy_independent_ptr (fuel + 1) layouts richSpecs ty0 slice0 hPtr0).symm
  have h1eq :
      decodeTypedValueRichWithPolicy (fuel + 1) layouts richSpecs ty1 slice1 .stripProvenance =
        decodeTypedValueRichWithPolicy (fuel + 1) layouts richSpecs ty1
          (stripAbstractBytesProv slice1) .strictUcg630Ub := by
    have hfall : ∀ p,
        decodeTypedValueRichWithPolicy (fuel + 1) layouts richSpecs ty1 slice1 p =
          decodeTypedValueFromBytes (fuel + 1) layouts ty1 slice1 p := by
      intro p
      rcases ty1 with ⟨k1, _⟩
      dsimp only at hPrim1
      rcases hPrim1 with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨fk, rfl⟩
      · rfl
      · rfl
      · rfl
      · rfl
      · cases fk <;> rfl
    have hfallS : ∀ p,
        decodeTypedValueRichWithPolicy (fuel + 1) layouts richSpecs ty1 (stripAbstractBytesProv slice1) p =
          decodeTypedValueFromBytes (fuel + 1) layouts ty1 (stripAbstractBytesProv slice1) p := by
      intro p
      rcases ty1 with ⟨k1, _⟩
      dsimp only at hPrim1
      rcases hPrim1 with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨fk, rfl⟩
      · rfl
      · rfl
      · rfl
      · rfl
      · cases fk <;> rfl
    rw [hfall, hfallS]
    exact decodeTypedValueFromBytes_prim_strip_eq_strict_stripProv fuel layouts ty1 slice1 hPrim1
  conv => lhs; unfold decodeTypedValueRichWithPolicy normalizeCodecTy
  dsimp only
  rw [hspec]
  dsimp only
  rw [hlen, Nat.beq_refl]
  dsimp only
  unfold decodeRichFieldSpecs
  rw [hsl0]
  dsimp only
  rw [h0eq]
  cases decodeTypedValueRichWithPolicy (fuel + 1) layouts richSpecs ty0 slice0 .strictUcg630Ub with
  | none => rfl
  | some _ =>
    dsimp only
    unfold decodeRichFieldSpecs
    rw [hsl1]
    dsimp only
    rw [h1eq]
    cases decodeTypedValueRichWithPolicy (fuel + 1) layouts richSpecs ty1
        (stripAbstractBytesProv slice1) .strictUcg630Ub with
    | none => rfl
    | some _ => rfl

/-- **Intact pointer-niche preservation under `.stripProvenance` (`RichAdtSpec.nichePointerEnum`)**:
when the niche slice carries intact uniform pointer provenance (`abstractBytesUniformProv nicheSlice = true`),
`.stripProvenance` selects the payload variant `someVar` and decodes `someFields` with
`.stripProvenance` (preserving pointer provenance in the niche/pointer fields while stripping
non-pointer fields), whereas naive whole-buffer `stripAbstractBytesProv` forces
`abstractBytesUniformProv (stripAbstractBytesProv nicheSlice) = false` and destroys the intact
pointer niche. -/
theorem decodeTypedValueRichWithPolicy_nichePointerEnum_intact_strip
    (fuel : Nat) (layouts : LayoutTable) (richSpecs : List (DefPath × RichAdtSpec))
    (defPath : DefPath) (args : List RigidTy) (li : LayoutIdx)
    (totalBytes nicheOff nicheBytes : Nat)
    (noneVar : VariantIdx) (noneFields : List (Nat × Nat × Ty))
    (someVar : VariantIdx) (someFields : List (Nat × Nat × Ty))
    (bs nicheSlice : List AbstractByte)
    (hspec : lookupRichAdtSpec defPath richSpecs =
      .some (.nichePointerEnum totalBytes nicheOff nicheBytes noneVar noneFields someVar someFields))
    (hlen : length bs = totalBytes)
    (hsl : sliceAbstractBytes bs nicheOff nicheBytes = .some nicheSlice)
    (hunif : abstractBytesUniformProv nicheSlice = true) :
    decodeTypedValueRichWithPolicy (fuel + 1) layouts richSpecs
        { kind := .adt defPath args, layoutIdx := li } bs .stripProvenance =
      (match decodeRichFieldSpecs
          (fun cTy chunk => decodeTypedValueRichWithPolicy fuel layouts richSpecs cTy chunk .stripProvenance)
          bs someFields with
       | .some vals => .some (.aggregate someVar vals)
       | .none => .none) ∧
    abstractBytesUniformProv (stripAbstractBytesProv nicheSlice) = false := by
  refine ⟨?_, abstractBytesUniformProv_stripAbstractBytesProv nicheSlice⟩
  conv => lhs; unfold decodeTypedValueRichWithPolicy normalizeCodecTy
  dsimp only
  rw [hspec]
  dsimp only
  rw [hlen, Nat.beq_refl]
  dsimp only
  rw [hsl]
  dsimp only
  rw [hunif]
  rfl

/-! ### Concrete 32-bit `usize`/`isize`, unresolved-slot-0 tuple/DST, & rich ADT no-forgery theorems -/

/-- 32-bit `LayoutTable` witness (`pointerBits = 32`). -/
private abbrev layoutTable32 : LayoutTable :=
  { pointerBits := 32, isLittleEndian := true, entries := .nil }

/-- **32-bit `usize` / `isize` width witness**: on a 32-bit layout table, 4-byte
sequences decode to `usize` / `isize` scalars of width 4 while 8-byte sequences are
rejected (`.none`). -/
theorem decodeTypedValueFromBytes_32bit_usize_isize_witness :
    let bs4 := encodeLittleEndianBytes 0x12345678 4 .none
    let bs8 := encodeLittleEndianBytes 0x12345678 8 .none
    decodeTypedValueFromBytes defaultCodecFuel layoutTable32 { kind := .uint .usize, layoutIdx := 0 } bs4 .strictUcg630Ub =
      .some (.scalar ⟨0x12345678, 4⟩) ∧
    decodeTypedValueFromBytes defaultCodecFuel layoutTable32 { kind := .int .isize, layoutIdx := 0 } bs4 .strictUcg630Ub =
      .some (.scalar ⟨0x12345678, 4⟩) ∧
    decodeTypedValueFromBytes defaultCodecFuel layoutTable32 { kind := .uint .usize, layoutIdx := 0 } bs8 .strictUcg630Ub =
      .none ∧
    decodeTypedValueFromBytes defaultCodecFuel layoutTable32 { kind := .int .isize, layoutIdx := 0 } bs8 .strictUcg630Ub =
      .none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Unrelated 16-byte `.scalarPair` layout placed at `entries[0]` (unresolved slot `0`)
and a resolved custom-DST `.scalarPair` at `entries[1]`. -/
private abbrev slot0CollisionLayouts : LayoutTable :=
  let pairLayout : TypeLayout :=
    { size := ⟨16⟩
      align := ⟨8⟩
      backendRepr := .scalarPair
        (.initialized (.pointer 0) ⟨1, 0xFFFFFFFFFFFFFFFF⟩)
        (.initialized (.int 64 false) ⟨0, 0xFFFFFFFFFFFFFFFF⟩)
      fields := .arbitrary [⟨0⟩, ⟨8⟩] [0, 1]
      variants := .single 0
      isUninhabited := false
      fieldLayouts := .nil }
  { pointerBits := 64, isLittleEndian := true, entries := [pairLayout, pairLayout] }

/-- **Unresolved-slot-0 tuple & custom-DST guard witnesses**:
1. Slot `0` holding a 16-byte layout does NOT corrupt decoding `(u32, u32)` at
   `layoutIdx = 0` (8 bytes still decode to `(1, 2)`).
2. Slot `0` holding a 16-byte `.scalarPair` does NOT trick `decodeTypedValueRichWithPolicy`
   into accepting 16 bytes for a thin `&u32` at `layoutIdx = 0`.
3. A resolved custom-DST `&MyDst` at `layoutIdx = 1` (16-byte `.scalarPair`) DOES
   accept a 16-byte intact-provenance wide pointer while rejecting a provenance-free
   16-byte image under BOTH `.strictUcg630Ub` and `.stripProvenance`. -/
theorem unresolved_slot0_tuple_and_custom_dst_witnesses :
    let u32PairBytes := appendAbstractBytes
      (encodeLittleEndianBytes 1 4 .none) (encodeLittleEndianBytes 2 4 .none)
    let thinRefBytes := encodeLittleEndianBytes 0x1000 8 (.some (7, 7))
    let wideDstProvBytes := appendAbstractBytes
      (encodeLittleEndianBytes 0x1000 8 (.some (7, 7))) (encodeLittleEndianBytes 42 8 .none)
    let wideDstNoProvBytes := appendAbstractBytes
      (encodeLittleEndianBytes 0x1000 8 .none) (encodeLittleEndianBytes 42 8 .none)
    let tupleTy : Ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 0 }
    let thinRefSlot0Ty : Ty := { kind := .ref .not (.uint .u32), layoutIdx := 0 }
    let customDstRefTy : Ty := { kind := .ref .not (.adt "MyDst" .nil), layoutIdx := 1 }
    decodeTypedValueFromBytes defaultCodecFuel slot0CollisionLayouts tupleTy u32PairBytes .strictUcg630Ub =
      .some (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩]) ∧
    decodeTypedValueRichWithPolicy defaultCodecFuel slot0CollisionLayouts .nil thinRefSlot0Ty wideDstProvBytes .strictUcg630Ub =
      .none ∧
    decodeTypedValueRichWithPolicy defaultCodecFuel slot0CollisionLayouts .nil thinRefSlot0Ty thinRefBytes .strictUcg630Ub =
      .some (.ptr { allocId := 7, offsetBytes := 0x1000 } 8) ∧
    decodeTypedValueRichWithPolicy defaultCodecFuel slot0CollisionLayouts .nil customDstRefTy wideDstProvBytes .strictUcg630Ub =
      .some (.aggregate 0 [.ptr { allocId := 7, offsetBytes := 0x1000 } 8, .scalar ⟨42, 8⟩]) ∧
    decodeTypedValueRichWithPolicy defaultCodecFuel slot0CollisionLayouts .nil customDstRefTy wideDstNoProvBytes .strictUcg630Ub =
      .none ∧
    decodeTypedValueRichWithPolicy defaultCodecFuel slot0CollisionLayouts .nil customDstRefTy wideDstNoProvBytes .stripProvenance =
      .none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Struct & enum `.ref` and `.fnPtr` no-forgery under EVERY `Ptr2IntTransmutePolicy` -/

private theorem abstractBytesUniformProv_false_of_haveProv_false (bs : List AbstractByte)
    (h : abstractBytesHaveProv bs = false) :
    abstractBytesUniformProv bs = false := by
  cases bs with
  | nil => rfl
  | cons b rest =>
    cases b with
    | uninit => rfl
    | init _ prov =>
      cases prov with
      | none => rfl
      | some _ => cases h

private theorem decodePtrBytesNoForge_ref_none_of_provFree
    (pointee : RigidTy) (ptrBytes : Nat) (bs : List AbstractByte)
    (hbs : abstractBytesHaveProv bs = false) :
    decodePtrBytesNoForge true pointee ptrBytes bs = .none := by
  unfold decodePtrBytesNoForge
  dsimp only
  cases pointee with
  | slice _ =>
    dsimp only
    cases Nat.beq (length bs) (Nat.add ptrBytes ptrBytes) with
    | false => rfl
    | true =>
      dsimp only
      cases Nat.beq (length (takeAbstractBytes ptrBytes bs)) ptrBytes with
      | false => rfl
      | true =>
        cases decodeScalarBytes (takeAbstractBytes ptrBytes bs) false with
        | none => rfl
        | some res =>
          rcases res with ⟨sv, prov⟩
          dsimp only
          rw [abstractBytesUniformProv_false_of_haveProv_false _
            (abstractBytesHaveProv_takeAbstractBytes_false ptrBytes bs hbs)]
  | str =>
    dsimp only
    cases Nat.beq (length bs) (Nat.add ptrBytes ptrBytes) with
    | false => rfl
    | true =>
      dsimp only
      cases Nat.beq (length (takeAbstractBytes ptrBytes bs)) ptrBytes with
      | false => rfl
      | true =>
        cases decodeScalarBytes (takeAbstractBytes ptrBytes bs) false with
        | none => rfl
        | some res =>
          rcases res with ⟨sv, prov⟩
          dsimp only
          rw [abstractBytesUniformProv_false_of_haveProv_false _
            (abstractBytesHaveProv_takeAbstractBytes_false ptrBytes bs hbs)]
  | dynamic _ =>
    dsimp only
    cases Nat.beq (length bs) (Nat.add ptrBytes ptrBytes) with
    | false => rfl
    | true =>
      dsimp only
      cases Nat.beq (length (takeAbstractBytes ptrBytes bs)) ptrBytes with
      | false => rfl
      | true =>
        cases decodeScalarBytes (takeAbstractBytes ptrBytes bs) false with
        | none => rfl
        | some res =>
          rcases res with ⟨sv, prov⟩
          dsimp only
          rw [abstractBytesUniformProv_false_of_haveProv_false _
            (abstractBytesHaveProv_takeAbstractBytes_false ptrBytes bs hbs)]
  | _ =>
    dsimp only
    cases Nat.beq (length bs) ptrBytes with
    | false => rfl
    | true =>
      cases decodeScalarBytes bs false with
      | none => rfl
      | some res =>
        rcases res with ⟨sv, prov⟩
        dsimp only
        rw [abstractBytesUniformProv_false_of_haveProv_false bs hbs]

private theorem decodePtrBytesRichNoForge_ref_none_of_provFree
    (layouts : LayoutTable) (layoutIdx : LayoutIdx) (pointee : RigidTy) (bs : List AbstractByte)
    (hbs : abstractBytesHaveProv bs = false) :
    decodePtrBytesRichNoForge true layouts layoutIdx pointee bs = .none := by
  unfold decodePtrBytesRichNoForge
  dsimp only
  cases pointee
  all_goals dsimp only
  all_goals try exact decodePtrBytesNoForge_ref_none_of_provFree _ _ bs hbs
  all_goals (
    cases Bool.not (isUnresolvedLayoutIdx layouts layoutIdx) with
    | false => exact decodePtrBytesNoForge_ref_none_of_provFree _ _ bs hbs
    | true =>
      dsimp only
      cases LayoutTable.lookup layouts layoutIdx with
      | none => exact decodePtrBytesNoForge_ref_none_of_provFree _ _ bs hbs
      | some l =>
        dsimp only
        cases Nat.beq l.size.bytes (Nat.add (layoutPointerBytes layouts) (layoutPointerBytes layouts)) with
        | false => exact decodePtrBytesNoForge_ref_none_of_provFree _ _ bs hbs
        | true =>
          cases l.backendRepr with
          | scalarPair _ sMeta =>
            dsimp only
            cases scalarLayoutIsPointer sMeta <;>
              exact decodePtrBytesNoForge_ref_none_of_provFree _ _ bs hbs
          | _ => exact decodePtrBytesNoForge_ref_none_of_provFree _ _ bs hbs)

private theorem decodeRichFieldSpecs_none_of_mem_none
    (f : Ty → List AbstractByte → Option Value) (bytes : List AbstractByte) :
    ∀ specs, (∃ s, s ∈ specs ∧
        match sliceAbstractBytes bytes s.1 s.2.1 with
        | .none => True
        | .some sl => f s.2.2 sl = .none) →
      decodeRichFieldSpecs f bytes specs = .none := by
  intro specs
  induction specs with
  | nil => intro h; rcases h with ⟨_, hs, _⟩; cases hs
  | cons spec rest ih =>
    intro h
    unfold decodeRichFieldSpecs
    rcases h with ⟨s, hs, hfail⟩
    rcases List.mem_cons.mp hs with rfl | hrest
    · cases hsl : sliceAbstractBytes bytes s.1 s.2.1 with
      | none => rfl
      | some sl =>
        dsimp only
        rw [hsl] at hfail
        dsimp only at hfail
        rw [hfail]
    · cases hsl : sliceAbstractBytes bytes spec.1 spec.2.1 with
      | none => rfl
      | some sl =>
        dsimp only
        cases hf : f spec.2.2 sl with
        | none => rfl
        | some v =>
          dsimp only
          rw [ih ⟨s, hrest, hfail⟩]

private theorem resolveTyWithLocalDecls_kind
    (localDecls : List LocalDecl) (layouts : LayoutTable) (ty : Ty) :
    (resolveTyWithLocalDecls localDecls layouts ty).kind = ty.kind := by
  unfold resolveTyWithLocalDecls
  cases isUnresolvedLayoutIdx layouts ty.layoutIdx with
  | false => rfl
  | true =>
    cases findDeclOrContainerElemTyWithKind? localDecls layouts ty.kind with
    | some _ => rfl
    | none =>
      cases Nat.beq ty.layoutIdx 0 with
      | false => rfl
      | true =>
        cases localDecls with
        | nil => rfl
        | cons _ _ => cases isPrimitiveScalarKind ty.kind <;> rfl

/-- **Struct `.ref` no-forgery (both policies)**: transmuting any provenance-free source
value (`valueHasProv v = false`) into a struct with any `.ref` field in its `RichAdtSpec`
always yields `.ub` (never `.ok`) under BOTH `.strictUcg630Ub` and `.stripProvenance`. -/
theorem evalByteCastRichWithPolicy_struct_ref_no_forge
    (policy : Ptr2IntTransmutePolicy)
    (locals locals' : List LocalSlot) (op : Operand) (defPath : DefPath) (args : List RigidTy)
    (li : LayoutIdx) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (richSpecs : List (DefPath × RichAdtSpec))
    (varIdx totalBytes : Nat) (fields : List (Nat × Nat × Ty))
    (fOff fBytes : Nat) (m : Mutability) (pointee : RigidTy) (fLi : LayoutIdx)
    (v : Value)
    (hspec : lookupRichAdtSpec defPath richSpecs = .some (.structFields varIdx totalBytes fields))
    (hfield : (fOff, fBytes, { kind := .ref m pointee, layoutIdx := fLi }) ∈ fields)
    (hop : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok v locals')
    (hv : valueHasProv v = false) :
    ∀ outV outL outM,
      evalByteCastRichWithPolicy locals op { kind := .adt defPath args, layoutIdx := li }
        mem localDecls layouts richSpecs policy ≠ .ok outV outL outM := by
  have hdec_none : ∀ bs li', abstractBytesHaveProv bs = false →
      decodeTypedValueRichWithPolicy defaultCodecFuel layouts richSpecs
        { kind := .adt defPath args, layoutIdx := li' } bs policy = .none := by
    intro bs li' hbs
    unfold decodeTypedValueRichWithPolicy normalizeCodecTy
    dsimp only
    rw [hspec]
    dsimp only
    cases Nat.beq (length bs) totalBytes with
    | false => rfl
    | true =>
      dsimp only
      have hfail : decodeRichFieldSpecs
          (fun cTy sl => decodeTypedValueRichWithPolicy 15 layouts richSpecs cTy sl policy)
          bs fields = .none := by
        apply decodeRichFieldSpecs_none_of_mem_none
        refine ⟨(fOff, fBytes, { kind := .ref m pointee, layoutIdx := fLi }), hfield, ?_⟩
        dsimp only
        cases hsl : sliceAbstractBytes bs fOff fBytes with
        | none => trivial
        | some sl =>
          dsimp only
          unfold decodeTypedValueRichWithPolicy normalizeCodecTy
          dsimp only
          exact decodePtrBytesRichNoForge_ref_none_of_provFree layouts fLi pointee sl
            (abstractBytesHaveProv_sliceAbstractBytes_false bs sl fOff fBytes hbs hsl)
      rw [hfail]
  intro outV outL outM heq
  unfold evalByteCastRichWithPolicy at heq
  rw [hop] at heq
  dsimp only at heq
  have hrKind : (resolveTyWithLocalDecls localDecls layouts { kind := .adt defPath args, layoutIdx := li }).kind =
      .adt defPath args :=
    resolveTyWithLocalDecls_kind localDecls layouts { kind := .adt defPath args, layoutIdx := li }
  generalize hrTy : resolveTyWithLocalDecls localDecls layouts { kind := .adt defPath args, layoutIdx := li } = rTy at heq hrKind
  rcases rTy with ⟨rKind, rLi⟩
  dsimp only at hrKind; subst hrKind
  cases hdsz : richTyByteSize localDecls layouts richSpecs { kind := .adt defPath args, layoutIdx := rLi } with
  | none => rw [hdsz] at heq; cases heq
  | some dstSize =>
    rw [hdsz] at heq; dsimp only at heq
    cases hopTy : operandTy localDecls layouts op with
    | some srcTy =>
      rw [hopTy] at heq; dsimp only at heq
      cases hssz : richTyByteSize localDecls layouts richSpecs (resolveTyWithLocalDecls localDecls layouts srcTy) with
      | none => rw [hssz] at heq; cases heq
      | some srcSize =>
        rw [hssz] at heq; dsimp only at heq
        cases hszEq : Nat.beq srcSize dstSize with
        | false => rw [hszEq] at heq; cases heq
        | true =>
          rw [hszEq] at heq; dsimp only at heq
          cases henc : encodeByteCastSourceBytes layouts (resolveTyWithLocalDecls localDecls layouts srcTy) v with
          | none => rw [henc] at heq; cases heq
          | some bs =>
            rw [henc] at heq; dsimp only at heq
            cases hbl : Nat.beq (length bs) dstSize with
            | false => rw [hbl] at heq; cases heq
            | true =>
              rw [hbl] at heq; dsimp only at heq
              rw [hdec_none bs rLi (abstractBytesHaveProv_encodeByteCastSourceBytes layouts _ v bs hv henc)] at heq
              cases heq
    | none =>
      rw [hopTy] at heq; dsimp only at heq
      cases henc : encodeUntypedValueToBytes defaultCodecFuel v with
      | none => rw [henc] at heq; cases heq
      | some bs =>
        rw [henc] at heq; dsimp only at heq
        cases hbl : Nat.beq (length bs) dstSize with
        | false => rw [hbl] at heq; cases heq
        | true =>
          rw [hbl] at heq; dsimp only at heq
          rw [hdec_none bs rLi (abstractBytesHaveProv_encodeUntypedValueToBytes defaultCodecFuel v bs hv henc)] at heq
          cases heq

/-- **Struct `.fnPtr` no-forgery (both policies)**: transmuting any provenance-free source
value into a struct with any `.fnPtr` field in its `RichAdtSpec` never succeeds under
either `.strictUcg630Ub` or `.stripProvenance`. -/
theorem evalByteCastRichWithPolicy_struct_fnPtr_no_forge
    (policy : Ptr2IntTransmutePolicy)
    (locals locals' : List LocalSlot) (op : Operand) (defPath : DefPath) (args : List RigidTy)
    (li : LayoutIdx) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (richSpecs : List (DefPath × RichAdtSpec))
    (varIdx totalBytes : Nat) (fields : List (Nat × Nat × Ty))
    (fOff fBytes : Nat) (ins : List RigidTy) (outTy : RigidTy) (safety : Safety) (abi : CallConv) (fLi : LayoutIdx)
    (v : Value)
    (hspec : lookupRichAdtSpec defPath richSpecs = .some (.structFields varIdx totalBytes fields))
    (hfield : (fOff, fBytes, { kind := .fnPtr ins outTy safety abi, layoutIdx := fLi }) ∈ fields)
    (hop : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok v locals')
    (hv : valueHasProv v = false) :
    ∀ outV outL outM,
      evalByteCastRichWithPolicy locals op { kind := .adt defPath args, layoutIdx := li }
        mem localDecls layouts richSpecs policy ≠ .ok outV outL outM := by
  have hdec_none : ∀ bs li', abstractBytesHaveProv bs = false →
      decodeTypedValueRichWithPolicy defaultCodecFuel layouts richSpecs
        { kind := .adt defPath args, layoutIdx := li' } bs policy = .none := by
    intro bs li' hbs
    unfold decodeTypedValueRichWithPolicy normalizeCodecTy
    dsimp only
    rw [hspec]
    dsimp only
    cases Nat.beq (length bs) totalBytes with
    | false => rfl
    | true =>
      dsimp only
      have hfail : decodeRichFieldSpecs
          (fun cTy sl => decodeTypedValueRichWithPolicy 15 layouts richSpecs cTy sl policy)
          bs fields = .none := by
        apply decodeRichFieldSpecs_none_of_mem_none
        refine ⟨(fOff, fBytes, { kind := .fnPtr ins outTy safety abi, layoutIdx := fLi }), hfield, ?_⟩
        dsimp only
        cases hsl : sliceAbstractBytes bs fOff fBytes with
        | none => trivial
        | some sl =>
          dsimp only
          unfold decodeTypedValueRichWithPolicy normalizeCodecTy
          dsimp only
          exact decodePtrBytesNoForge_ref_none_of_provFree (.tuple .nil) (layoutPointerBytes layouts) sl
            (abstractBytesHaveProv_sliceAbstractBytes_false bs sl fOff fBytes hbs hsl)
      rw [hfail]
  intro outV outL outM heq
  unfold evalByteCastRichWithPolicy at heq
  rw [hop] at heq
  dsimp only at heq
  have hrKind : (resolveTyWithLocalDecls localDecls layouts { kind := .adt defPath args, layoutIdx := li }).kind =
      .adt defPath args :=
    resolveTyWithLocalDecls_kind localDecls layouts { kind := .adt defPath args, layoutIdx := li }
  generalize hrTy : resolveTyWithLocalDecls localDecls layouts { kind := .adt defPath args, layoutIdx := li } = rTy at heq hrKind
  rcases rTy with ⟨rKind, rLi⟩
  dsimp only at hrKind; subst hrKind
  cases hdsz : richTyByteSize localDecls layouts richSpecs { kind := .adt defPath args, layoutIdx := rLi } with
  | none => rw [hdsz] at heq; cases heq
  | some dstSize =>
    rw [hdsz] at heq; dsimp only at heq
    cases hopTy : operandTy localDecls layouts op with
    | some srcTy =>
      rw [hopTy] at heq; dsimp only at heq
      cases hssz : richTyByteSize localDecls layouts richSpecs (resolveTyWithLocalDecls localDecls layouts srcTy) with
      | none => rw [hssz] at heq; cases heq
      | some srcSize =>
        rw [hssz] at heq; dsimp only at heq
        cases hszEq : Nat.beq srcSize dstSize with
        | false => rw [hszEq] at heq; cases heq
        | true =>
          rw [hszEq] at heq; dsimp only at heq
          cases henc : encodeByteCastSourceBytes layouts (resolveTyWithLocalDecls localDecls layouts srcTy) v with
          | none => rw [henc] at heq; cases heq
          | some bs =>
            rw [henc] at heq; dsimp only at heq
            cases hbl : Nat.beq (length bs) dstSize with
            | false => rw [hbl] at heq; cases heq
            | true =>
              rw [hbl] at heq; dsimp only at heq
              rw [hdec_none bs rLi (abstractBytesHaveProv_encodeByteCastSourceBytes layouts _ v bs hv henc)] at heq
              cases heq
    | none =>
      rw [hopTy] at heq; dsimp only at heq
      cases henc : encodeUntypedValueToBytes defaultCodecFuel v with
      | none => rw [henc] at heq; cases heq
      | some bs =>
        rw [henc] at heq; dsimp only at heq
        cases hbl : Nat.beq (length bs) dstSize with
        | false => rw [hbl] at heq; cases heq
        | true =>
          rw [hbl] at heq; dsimp only at heq
          rw [hdec_none bs rLi (abstractBytesHaveProv_encodeUntypedValueToBytes defaultCodecFuel v bs hv henc)] at heq
          cases heq

/-- **Enum `.ref` and `.fnPtr` no-forgery (both policies)** covering all three enum
forms in `RichAdtSpec`:
1. `taggedEnum` (`TagEncoding::Direct`): a provenance-free source value never decodes
   a variant containing a `.ref` or `.fnPtr` field under either policy;
2. `nichePointerEnum` (`Option<&T>` / `Option<fn()>`):
   - any provenance-free source value with nonzero niche bits is rejected as `.none` / `.ub`
     under BOTH policies (never forging `Some(&T)` or `Some(fn())`);
   - an intact provenance-carrying pointer at offset `0` (null-offset provenance) decodes
     as `Some` rather than collapsing into the `None` niche (both policies);
3. `nicheScalarEnum` (`Option<bool>` / `Option<NonZero>` with `.ref`/`.fnPtr` payload):
   a provenance-free source value with non-niche discriminant never decodes a payload
   variant carrying a `.ref` or `.fnPtr` field under either policy. -/
theorem evalByteCastRichWithPolicy_enum_no_forge_ref_and_fnPtr
    (policy : Ptr2IntTransmutePolicy) (layouts : LayoutTable)
    (richSpecs : List (DefPath × RichAdtSpec)) :
    -- (1) `taggedEnum`: no-forgery on any variant carrying `.ref` or `.fnPtr`
    (∀ defPath args li totalBytes tagOff tagBytes variants bs,
        lookupRichAdtSpec defPath richSpecs = .some (.taggedEnum totalBytes tagOff tagBytes variants) →
        abstractBytesHaveProv bs = false →
        (∀ entry, entry ∈ variants →
          ∃ fOff fBytes fTy, (fOff, fBytes, fTy) ∈ entry.2.2 ∧
            ((∃ m pt, fTy.kind = .ref m pt) ∨ (∃ ins out s abi, fTy.kind = .fnPtr ins out s abi))) →
      decodeTypedValueRichWithPolicy defaultCodecFuel layouts richSpecs
        { kind := .adt defPath args, layoutIdx := li } bs policy = .none) ∧
    -- (2a) `nichePointerEnum`: provenance-free nonzero niche bits always fail closed (both policies)
    (∀ defPath args li totalBytes nicheOff nicheBytes noneVar noneFields someVar someFields bs
        nicheSlice nicheRes,
        lookupRichAdtSpec defPath richSpecs =
          .some (.nichePointerEnum totalBytes nicheOff nicheBytes noneVar noneFields someVar someFields) →
        abstractBytesHaveProv bs = false →
        sliceAbstractBytes bs nicheOff nicheBytes = .some nicheSlice →
        decodeScalarBytes nicheSlice false = .some nicheRes →
        nicheRes.1.bits ≠ 0 →
      decodeTypedValueRichWithPolicy defaultCodecFuel layouts richSpecs
        { kind := .adt defPath args, layoutIdx := li } bs policy = .none) ∧
    -- (2b) `nichePointerEnum`: intact offset-0 provenance pointer decodes `Some`, NOT `None`
    (let optRefSpecs : List (DefPath × RichAdtSpec) :=
        [("OptionRefU32", .nichePointerEnum 8 0 8 0 .nil 1 [(0, 8, { kind := .ref .not (.uint .u32), layoutIdx := 0 })])]
     let optFnSpecs : List (DefPath × RichAdtSpec) :=
        [("OptionFn", .nichePointerEnum 8 0 8 0 .nil 1 [(0, 8, { kind := .fnPtr .nil (.tuple .nil) .safe .rust, layoutIdx := 0 })])]
     let zeroOffPtrBytes := encodeLittleEndianBytes 0 8 (.some (9, 9))
     decodeTypedValueRichWithPolicy defaultCodecFuel emptyLayoutTable optRefSpecs
       { kind := .adt "OptionRefU32" .nil, layoutIdx := 0 } zeroOffPtrBytes policy =
         .some (.aggregate 1 [.ptr { allocId := 9, offsetBytes := 0 } 8]) ∧
     decodeTypedValueRichWithPolicy defaultCodecFuel emptyLayoutTable optFnSpecs
       { kind := .adt "OptionFn" .nil, layoutIdx := 0 } zeroOffPtrBytes policy =
         .some (.aggregate 1 [.ptr { allocId := 9, offsetBytes := 0 } 8])) ∧
    -- (3) `nicheScalarEnum`: provenance-free non-niche bytes never forge `.ref`/`.fnPtr` payload
    (∀ defPath args li totalBytes nicheOff nicheBytes nicheVal nicheVar nicheFields payVar payFields bs
        nicheSlice nicheRes,
        lookupRichAdtSpec defPath richSpecs =
          .some (.nicheScalarEnum totalBytes nicheOff nicheBytes nicheVal nicheVar nicheFields payVar payFields) →
        abstractBytesHaveProv bs = false →
        sliceAbstractBytes bs nicheOff nicheBytes = .some nicheSlice →
        decodeScalarBytes nicheSlice false = .some nicheRes →
        nicheRes.1.bits ≠ nicheVal →
        (∃ fOff fBytes fTy, (fOff, fBytes, fTy) ∈ payFields ∧
          ((∃ m pt, fTy.kind = .ref m pt) ∨ (∃ ins out s abi, fTy.kind = .fnPtr ins out s abi))) →
      decodeTypedValueRichWithPolicy defaultCodecFuel layouts richSpecs
        { kind := .adt defPath args, layoutIdx := li } bs policy = .none) := by
  have hfind_mem : ∀ tagVal variants varEntry,
      findRichTaggedVariant tagVal variants = .some varEntry →
      (tagVal, varEntry) ∈ variants := by
    intro tagVal variants
    induction variants with
    | nil => intro _ h; cases h
    | cons entry rest ih =>
      intro varEntry h
      unfold findRichTaggedVariant at h
      cases hbeq : Nat.beq entry.1 tagVal with
      | true =>
        rw [hbeq] at h
        dsimp only at h
        injection h with h
        have h1 : entry.1 = tagVal := Nat.eq_of_beq_eq_true hbeq
        have hentry : entry = (tagVal, varEntry) := by
          cases entry; dsimp only at h1 h; rw [h1, h]
        rw [hentry]; exact List.mem_cons_self
      | false =>
        rw [hbeq] at h
        dsimp only at h
        exact List.mem_cons_of_mem entry (ih varEntry h)
  have hfield_none : ∀ bs fields,
      abstractBytesHaveProv bs = false →
      (∃ fOff fBytes fTy, (fOff, fBytes, fTy) ∈ fields ∧
        ((∃ m pt, fTy.kind = .ref m pt) ∨ (∃ ins out s abi, fTy.kind = .fnPtr ins out s abi))) →
      decodeRichFieldSpecs
        (fun cTy sl => decodeTypedValueRichWithPolicy 15 layouts richSpecs cTy sl policy)
        bs fields = .none := by
    intro bs fields hbs hmem
    rcases hmem with ⟨fOff, fBytes, fTy, hfm, hkind⟩
    apply decodeRichFieldSpecs_none_of_mem_none
    refine ⟨(fOff, fBytes, fTy), hfm, ?_⟩
    dsimp only
    cases hsl : sliceAbstractBytes bs fOff fBytes with
    | none => trivial
    | some sl =>
      dsimp only
      have hslPf := abstractBytesHaveProv_sliceAbstractBytes_false bs sl fOff fBytes hbs hsl
      rcases fTy with ⟨fk, fli⟩
      dsimp only at hkind
      rcases hkind with ⟨m, pt, rfl⟩ | ⟨ins, out, s, abi, rfl⟩
      · unfold decodeTypedValueRichWithPolicy normalizeCodecTy
        dsimp only
        exact decodePtrBytesRichNoForge_ref_none_of_provFree layouts fli pt sl hslPf
      · unfold decodeTypedValueRichWithPolicy normalizeCodecTy
        dsimp only
        exact decodePtrBytesNoForge_ref_none_of_provFree (.tuple .nil) (layoutPointerBytes layouts) sl hslPf
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro defPath args li totalBytes tagOff tagBytes variants bs hspec hbs hall
    unfold decodeTypedValueRichWithPolicy normalizeCodecTy
    dsimp only
    rw [hspec]
    dsimp only
    cases Nat.beq (length bs) totalBytes with
    | false => rfl
    | true =>
      dsimp only
      cases sliceAbstractBytes bs tagOff tagBytes with
      | none => rfl
      | some tagSlice =>
        dsimp only
        cases policyRejectsProv policy tagSlice with
        | true => rfl
        | false =>
          dsimp only
          cases decodeScalarBytes tagSlice false with
          | none => rfl
          | some tagRes =>
            dsimp only
            cases hfv : findRichTaggedVariant tagRes.1.bits variants with
            | none => rfl
            | some varEntry =>
              dsimp only
              have hmem := hfind_mem tagRes.1.bits variants varEntry hfv
              rw [hfield_none bs varEntry.2 hbs (hall _ hmem)]
  · intro defPath args li totalBytes nicheOff nicheBytes noneVar noneFields someVar someFields bs
      nicheSlice nicheRes hspec hbs hsl hdec hnz
    unfold decodeTypedValueRichWithPolicy normalizeCodecTy
    dsimp only
    rw [hspec]
    dsimp only
    cases Nat.beq (length bs) totalBytes with
    | false => rfl
    | true =>
      dsimp only
      rw [hsl]
      dsimp only
      have hnp := abstractBytesHaveProv_sliceAbstractBytes_false bs nicheSlice nicheOff nicheBytes hbs hsl
      rw [abstractBytesUniformProv_false_of_haveProv_false nicheSlice hnp]
      dsimp only
      cases policyRejectsProv policy nicheSlice with
      | true => rfl
      | false =>
        dsimp only
        rw [hdec]
        dsimp only
        have hbeq : Nat.beq nicheRes.1.bits 0 = false := by
          rw [nat_beq_eq_decide]; exact decide_eq_false hnz
        rw [hbeq]
  · cases policy <;> exact ⟨rfl, rfl⟩
  · intro defPath args li totalBytes nicheOff nicheBytes nicheVal nicheVar nicheFields payVar payFields bs
      nicheSlice nicheRes hspec hbs hsl hdec hne hpay
    unfold decodeTypedValueRichWithPolicy normalizeCodecTy
    dsimp only
    rw [hspec]
    dsimp only
    cases Nat.beq (length bs) totalBytes with
    | false => rfl
    | true =>
      dsimp only
      rw [hsl]
      dsimp only
      cases policyRejectsProv policy nicheSlice with
      | true => rfl
      | false =>
        dsimp only
        rw [hdec]
        dsimp only
        have hbeq : Nat.beq nicheRes.1.bits nicheVal = false := by
          rw [nat_beq_eq_decide]; exact decide_eq_false hne
        rw [hbeq]
        dsimp only
        rw [hfield_none bs payFields hbs hpay]

/-! ## §6. `V2026_06_01` <-> `V2026_08_01` dialect parity

The two dialects declare distinct (textually mirrored) inductive types and
evaluators, so parity is not definitional: `Trusted.Rustc.V2026_08_01` constants
are related to their `V2026_06_01` counterparts through the explicit
constructor-preserving translation maps below (`fmt08`, `binOp08`, `mode08`,
`floatKind08`, `scalarInt08`, `policy08`, `abstractByte08`). Every theorem in
this section is an unconditional equation (or `↔`) over ALL inputs, stated
directly over the `Trusted` ground definitions of both dialects.
-/

section DialectParity

open Trusted.Rustc

/-- Dialect translation of `IeeeFormat` (`V2026_06_01 → V2026_08_01`). -/
def fmt08 : IeeeFormat → V2026_08_01.MirSemantics.IeeeFormat
  | .binary32 => .binary32
  | .binary64 => .binary64

/-- Dialect translation of `FloatArithMode` (`V2026_06_01 → V2026_08_01`). -/
def mode08 : FloatArithMode → V2026_08_01.MirSemantics.FloatArithMode
  | .deterministic => .deterministic
  | .nondeterministic => .nondeterministic

/-- Dialect translation of `Ptr2IntTransmutePolicy` (`V2026_06_01 → V2026_08_01`). -/
def policy08 : Ptr2IntTransmutePolicy → V2026_08_01.MirSemantics.Ptr2IntTransmutePolicy
  | .strictUcg630Ub => .strictUcg630Ub
  | .stripProvenance => .stripProvenance

/-- Dialect translation of `FloatKind` (`V2026_06_01 → V2026_08_01`). -/
def floatKind08 : FloatKind → V2026_08_01.MirSemantics.FloatKind
  | .zero neg => .zero neg
  | .finite neg n d => .finite neg n d
  | .inf neg => .inf neg
  | .nan neg q p => .nan neg q p

/-- Dialect translation of `ScalarInt` (`V2026_06_01 → V2026_08_01`). -/
def scalarInt08 (s : ScalarInt) : V2026_08_01.MirAst.ScalarInt :=
  ⟨s.bits, s.sizeBytes⟩

/-- Dialect translation of `AbstractByte` (`V2026_06_01 → V2026_08_01`). -/
def abstractByte08 : AbstractByte → V2026_08_01.MirSemantics.AbstractByte
  | .uninit => .uninit
  | .init b prov => .init b prov

/-- Dialect translation of a `nanChoices` input (`V2026_06_01 → V2026_08_01`). -/
def nanInput08 (inp : IeeeFormat × Nat) : V2026_08_01.MirSemantics.IeeeFormat × Nat :=
  (fmt08 inp.1, inp.2)

/-- Dialect translation of `BinOp` (`V2026_06_01 → V2026_08_01`). -/
def binOp08 : BinOp → V2026_08_01.MirAst.BinOp
  | .add => .add
  | .addUnchecked => .addUnchecked
  | .addWithOverflow => .addWithOverflow
  | .sub => .sub
  | .subUnchecked => .subUnchecked
  | .subWithOverflow => .subWithOverflow
  | .mul => .mul
  | .mulUnchecked => .mulUnchecked
  | .mulWithOverflow => .mulWithOverflow
  | .div => .div
  | .rem => .rem
  | .bitXor => .bitXor
  | .bitAnd => .bitAnd
  | .bitOr => .bitOr
  | .shl => .shl
  | .shlUnchecked => .shlUnchecked
  | .shr => .shr
  | .shrUnchecked => .shrUnchecked
  | .eq => .eq
  | .lt => .lt
  | .le => .le
  | .ne => .ne
  | .ge => .ge
  | .gt => .gt
  | .cmp => .cmp
  | .offset => .offset

theorem scalarInt08_injective (s t : ScalarInt) (h : scalarInt08 s = scalarInt08 t) : s = t := by
  cases s; cases t
  unfold scalarInt08 at h
  injection h with h1 h2
  subst h1; subst h2; rfl

/-- Format parameters agree across dialects. -/
theorem fmt08_params (f : IeeeFormat) :
    (fmt08 f).width = f.width ∧ (fmt08 f).exponentBits = f.exponentBits ∧
    (fmt08 f).fractionBits = f.fractionBits ∧ (fmt08 f).bias = f.bias ∧
    (fmt08 f).byteWidth = f.byteWidth ∧ (fmt08 f).minExponent = f.minExponent ∧
    (fmt08 f).maxExponent = f.maxExponent := by
  cases f <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Bit-pattern constructors agree across dialects. -/
theorem bitPatterns_parity (f : IeeeFormat) (neg : Bool) (e fr : Nat) :
    V2026_08_01.MirSemantics.zeroBits (fmt08 f) neg = zeroBits f neg ∧
    V2026_08_01.MirSemantics.infBits (fmt08 f) neg = infBits f neg ∧
    V2026_08_01.MirSemantics.preferredNaNBits (fmt08 f) = preferredNaNBits f ∧
    V2026_08_01.MirSemantics.encodeBits (fmt08 f) neg e fr = encodeBits f neg e fr := by
  cases f <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- `evalFloatNeg` (bitwise `UnOp.neg`) agrees across dialects on ALL bit patterns. -/
theorem evalFloatNeg_parity (f : IeeeFormat) (bits : Nat) :
    V2026_08_01.MirSemantics.evalFloatNeg (fmt08 f) bits = evalFloatNeg f bits := by
  cases f <;> rfl

/-- `evalFloatAbs` agrees across dialects on ALL bit patterns. -/
theorem evalFloatAbs_parity (f : IeeeFormat) (bits : Nat) :
    V2026_08_01.MirSemantics.evalFloatAbs (fmt08 f) bits = evalFloatAbs f bits := by
  cases f <;> rfl

/-- `roundRatioTiesToEven` agrees across dialects on ALL rationals. -/
theorem roundRatioTiesToEven_parity (f : IeeeFormat) (neg : Bool) (n d : Nat) :
    V2026_08_01.MirSemantics.roundRatioTiesToEven (fmt08 f) neg n d =
      roundRatioTiesToEven f neg n d := by
  cases f <;> rfl

/-- `decodeBits` agrees across dialects (modulo `floatKind08`) on ALL bit patterns. -/
theorem decodeBits_parity (f : IeeeFormat) (bits : Nat) :
    V2026_08_01.MirSemantics.decodeBits (fmt08 f) bits = floatKind08 (decodeBits f bits) := by
  cases f <;> simp only [decodeBits, apply_ite floatKind08] <;> rfl

/-- NaN classification predicates agree across dialects on ALL bit patterns. -/
theorem isNaNBits_parity (f : IeeeFormat) (bits : Nat) :
    V2026_08_01.MirSemantics.isNaNBits (fmt08 f) bits = isNaNBits f bits ∧
    V2026_08_01.MirSemantics.isQuietNaNBits (fmt08 f) bits = isQuietNaNBits f bits ∧
    V2026_08_01.MirSemantics.isSignalingNaNBits (fmt08 f) bits = isSignalingNaNBits f bits := by
  unfold V2026_08_01.MirSemantics.isNaNBits V2026_08_01.MirSemantics.isQuietNaNBits
    V2026_08_01.MirSemantics.isSignalingNaNBits isNaNBits isQuietNaNBits isSignalingNaNBits
  rw [decodeBits_parity]
  cases decodeBits f bits <;> exact ⟨rfl, rfl, rfl⟩

/-- `evalFloatPartialCompare` (IEEE-754 partial order) agrees across dialects on
ALL operand bit patterns. -/
theorem evalFloatPartialCompare_parity (f : IeeeFormat) (a b : Nat) :
    V2026_08_01.MirSemantics.evalFloatPartialCompare (fmt08 f) a b =
      evalFloatPartialCompare f a b := by
  unfold V2026_08_01.MirSemantics.evalFloatPartialCompare evalFloatPartialCompare
  rw [(fmt08_params f).1, decodeBits_parity, decodeBits_parity]
  cases decodeBits f (a % 2 ^ f.width) <;> cases decodeBits f (b % 2 ^ f.width) <;> rfl

/-- `evalFloatCmp` (`==`, `!=`, `<`, `<=`, `>`, `>=`) agrees across dialects for
EVERY `BinOp` and ALL operand bit patterns. -/
theorem evalFloatCmp_parity (op : BinOp) (f : IeeeFormat) (a b : Nat) :
    V2026_08_01.MirSemantics.evalFloatCmp (binOp08 op) (fmt08 f) a b = evalFloatCmp op f a b := by
  unfold V2026_08_01.MirSemantics.evalFloatCmp evalFloatCmp
  rw [evalFloatPartialCompare_parity]
  cases op <;> rfl

/-- `exactSumFloat` agrees across dialects on ALL decoded operand pairs. -/
theorem exactSumFloat_parity (f : IeeeFormat) (l r : FloatKind) :
    V2026_08_01.MirSemantics.exactSumFloat (fmt08 f) (floatKind08 l) (floatKind08 r) =
      exactSumFloat f l r := by
  cases f <;> cases l <;> cases r <;> rfl

/-- `negateFloatKind` commutes with the dialect translation. -/
theorem negateFloatKind_parity (k : FloatKind) :
    V2026_08_01.MirSemantics.negateFloatKind (floatKind08 k) = floatKind08 (negateFloatKind k) := by
  cases k <;> rfl

/-- `evalFloatArithBase` (`add`, `sub`, `mul`, `div`, `rem` under `roundTiesToEven`
with the deterministic preferred NaN) agrees across dialects for EVERY `BinOp`
and ALL operand bit patterns. -/
theorem evalFloatArithBase_parity (op : BinOp) (f : IeeeFormat) (a b : Nat) :
    V2026_08_01.MirSemantics.evalFloatArithBase (binOp08 op) (fmt08 f) a b =
      evalFloatArithBase op f a b := by
  unfold V2026_08_01.MirSemantics.evalFloatArithBase evalFloatArithBase
  dsimp only
  rw [(fmt08_params f).1, decodeBits_parity, decodeBits_parity]
  generalize decodeBits f (a % 2 ^ f.width) = l
  generalize decodeBits f (b % 2 ^ f.width) = r
  cases op
  case add => exact congrArg some (exactSumFloat_parity f l r)
  case sub =>
    show some (V2026_08_01.MirSemantics.exactSumFloat (fmt08 f) (floatKind08 l)
      (V2026_08_01.MirSemantics.negateFloatKind (floatKind08 r))) = _
    rw [negateFloatKind_parity, exactSumFloat_parity]
  case mul => cases f <;> cases l <;> cases r <;> rfl
  case div => cases f <;> cases l <;> cases r <;> rfl
  case rem => cases f <;> cases l <;> cases r <;> rfl
  all_goals rfl

/-- `evalFloatToFloatRoundTiesToEven` (`CastKind.floatToFloat`) agrees across
dialects for every source/target format pair and ALL bit patterns. -/
theorem evalFloatToFloatRoundTiesToEven_parity (src dst : IeeeFormat) (bits : Nat) :
    V2026_08_01.MirSemantics.evalFloatToFloatRoundTiesToEven (fmt08 src) (fmt08 dst) bits =
      evalFloatToFloatRoundTiesToEven src dst bits := by
  unfold V2026_08_01.MirSemantics.evalFloatToFloatRoundTiesToEven evalFloatToFloatRoundTiesToEven
  rw [decodeBits_parity]
  cases decodeBits src bits <;> cases src <;> cases dst <;> rfl

/-- `unpackBits` field projections agree across dialects on ALL bit patterns. -/
theorem unpackBits_parity (f : IeeeFormat) (bits : Nat) :
    (V2026_08_01.MirSemantics.unpackBits (fmt08 f) bits).neg = (unpackBits f bits).neg ∧
    (V2026_08_01.MirSemantics.unpackBits (fmt08 f) bits).exponent = (unpackBits f bits).exponent ∧
    (V2026_08_01.MirSemantics.unpackBits (fmt08 f) bits).fraction = (unpackBits f bits).fraction := by
  cases f <;> exact ⟨rfl, rfl, rfl⟩

/-- Quieted NaN candidate lists agree across dialects (element-for-element, in order). -/
theorem nanChoicesQuieted_parity (t : IeeeFormat) (inputs : List (IeeeFormat × Nat)) :
    V2026_08_01.MirSemantics.nanChoicesQuieted (fmt08 t) (inputs.map nanInput08) =
      nanChoicesQuieted t inputs := by
  induction inputs with
  | nil => rfl
  | cons inp rest ih =>
    show V2026_08_01.MirSemantics.nanChoicesQuieted (fmt08 t)
      (nanInput08 inp :: rest.map nanInput08) = nanChoicesQuieted t (inp :: rest)
    unfold V2026_08_01.MirSemantics.nanChoicesQuieted nanChoicesQuieted
    dsimp only [nanInput08]
    rw [ih, (fmt08_params inp.1).1, (isNaNBits_parity inp.1 _).1,
      evalFloatToFloatRoundTiesToEven_parity]

/-- Unchanged-signaling NaN candidate lists agree across dialects (element-for-element,
in order). -/
theorem nanChoicesSignaling_parity (t : IeeeFormat) (inputs : List (IeeeFormat × Nat)) :
    V2026_08_01.MirSemantics.nanChoicesSignaling (fmt08 t) (inputs.map nanInput08) =
      nanChoicesSignaling t inputs := by
  induction inputs with
  | nil => rfl
  | cons inp rest ih =>
    show V2026_08_01.MirSemantics.nanChoicesSignaling (fmt08 t)
      (nanInput08 inp :: rest.map nanInput08) = nanChoicesSignaling t (inp :: rest)
    unfold V2026_08_01.MirSemantics.nanChoicesSignaling nanChoicesSignaling
    dsimp only [nanInput08]
    rw [ih, (fmt08_params inp.1).1, (isNaNBits_parity inp.1 _).2.2,
      evalFloatToFloatRoundTiesToEven_parity, (unpackBits_parity t _).1,
      (unpackBits_parity t _).2.2, (fmt08_params t).2.2.1, (fmt08_params t).2.1,
      (bitPatterns_parity t _ _ _).2.2.2]

/-- Sign expansion of NaN candidates agrees across dialects. -/
theorem expandNanSigns_parity (t : IeeeFormat) (cs : List Nat) :
    V2026_08_01.MirSemantics.expandNanSigns (fmt08 t) cs = expandNanSigns t cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    unfold V2026_08_01.MirSemantics.expandNanSigns expandNanSigns
    rw [ih, evalFloatNeg_parity]

/-- **`nanChoices` parity**: the ordered admissible-NaN candidate list agrees
across dialects element-for-element for EVERY target format, input list, and
`FloatArithMode`. -/
theorem nanChoices_parity (t : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (mode : FloatArithMode) :
    V2026_08_01.MirSemantics.nanChoices (fmt08 t) (inputs.map nanInput08) (mode08 mode) =
      nanChoices t inputs mode := by
  cases mode with
  | deterministic =>
    show [V2026_08_01.MirSemantics.preferredNaNBits (fmt08 t)] = [preferredNaNBits t]
    rw [(bitPatterns_parity t false 0 0).2.2.1]
  | nondeterministic =>
    show V2026_08_01.MirSemantics.expandNanSigns (fmt08 t)
        (V2026_08_01.MirSemantics.preferredNaNBits (fmt08 t) ::
          (V2026_08_01.MirSemantics.nanChoicesQuieted (fmt08 t) (inputs.map nanInput08) ++
            V2026_08_01.MirSemantics.nanChoicesSignaling (fmt08 t) (inputs.map nanInput08))) =
      expandNanSigns t
        (preferredNaNBits t :: (nanChoicesQuieted t inputs ++ nanChoicesSignaling t inputs))
    rw [expandNanSigns_parity, (bitPatterns_parity t false 0 0).2.2.1, nanChoicesQuieted_parity,
      nanChoicesSignaling_parity]

/-- `natListMem` agrees across dialects. -/
theorem natListMem_parity (x : Nat) (xs : List Nat) :
    V2026_08_01.MirSemantics.natListMem x xs = natListMem x xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    unfold V2026_08_01.MirSemantics.natListMem natListMem
    rw [ih]

/-- `isAdmissibleQuietNaN` agrees across dialects. -/
theorem isAdmissibleQuietNaN_parity (f : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (bits : Nat) :
    V2026_08_01.MirSemantics.isAdmissibleQuietNaN (fmt08 f) (inputs.map nanInput08) bits =
      isAdmissibleQuietNaN f inputs bits := by
  unfold V2026_08_01.MirSemantics.isAdmissibleQuietNaN isAdmissibleQuietNaN
  dsimp only
  rw [(fmt08_params f).1, (isNaNBits_parity f _).2.1, natListMem_parity]
  exact congrArg (fun l => Bool.and (isQuietNaNBits f (bits % 2 ^ f.width))
    (natListMem (bits % 2 ^ f.width) l)) (nanChoices_parity f inputs .nondeterministic)

/-- `scalarInt08` reflects equality with an anonymous-constructor scalar. -/
theorem scalarInt08_eq_mk_iff (s : ScalarInt) (bits sz : Nat) :
    scalarInt08 s = ⟨bits, sz⟩ ↔ s = ⟨bits, sz⟩ := by
  cases s with
  | mk sb ss =>
    constructor
    · intro h
      unfold scalarInt08 at h
      injection h with h1 h2
      subst h1; subst h2; rfl
    · intro h
      injection h with h1 h2
      subst h1; subst h2; rfl

/-- **`evalFloatBinOp` parity**: the deterministic executable float binary-operation
evaluator agrees across dialects (modulo `scalarInt08`) for EVERY `BinOp`, format,
and operand bit patterns. -/
theorem evalFloatBinOp_parity (op : BinOp) (f : IeeeFormat) (a b : Nat) :
    V2026_08_01.MirSemantics.evalFloatBinOp (binOp08 op) (fmt08 f) a b =
      Option.map scalarInt08 (evalFloatBinOp op f a b) := by
  unfold V2026_08_01.MirSemantics.evalFloatBinOp evalFloatBinOp
  rw [evalFloatCmp_parity, evalFloatArithBase_parity, (fmt08_params f).2.2.2.2.1]
  cases evalFloatCmp op f a b with
  | some c => cases c <;> rfl
  | none => cases evalFloatArithBase op f a b <;> rfl

/-- **`EvalFloatBinOpRel` parity**: the mode-parametric relational specification
(including the full `.nondeterministic` NaN admissibility set) agrees across dialects
for EVERY mode, `BinOp`, format, operand bit patterns, and output scalar. -/
theorem EvalFloatBinOpRel_parity (mode : FloatArithMode) (op : BinOp) (f : IeeeFormat)
    (a b : Nat) (out : ScalarInt) :
    V2026_08_01.MirSemantics.EvalFloatBinOpRel (mode08 mode) (binOp08 op) (fmt08 f) a b
        (scalarInt08 out) ↔
      EvalFloatBinOpRel mode op f a b out := by
  unfold V2026_08_01.MirSemantics.EvalFloatBinOpRel EvalFloatBinOpRel
  rw [evalFloatCmp_parity, evalFloatArithBase_parity]
  cases evalFloatCmp op f a b with
  | some c =>
    cases c
    · exact scalarInt08_eq_mk_iff out 0 1
    · exact scalarInt08_eq_mk_iff out 1 1
  | none =>
    cases evalFloatArithBase op f a b with
    | none => exact Iff.rfl
    | some baseBits =>
      dsimp only
      rw [(isNaNBits_parity f baseBits).1, (fmt08_params f).1, (fmt08_params f).2.2.2.2.1]
      have hch :
          V2026_08_01.MirSemantics.nanChoices (fmt08 f)
              [(fmt08 f, a % 2 ^ f.width), (fmt08 f, b % 2 ^ f.width)] (mode08 mode) =
            nanChoices f [(f, a % 2 ^ f.width), (f, b % 2 ^ f.width)] mode :=
        nanChoices_parity f [(f, a % 2 ^ f.width), (f, b % 2 ^ f.width)] mode
      rw [hch]
      by_cases hnan : isNaNBits f baseBits = true
      · rw [if_pos' hnan, if_pos' hnan]
        constructor
        · rintro ⟨cand, hmem, hout⟩
          exact ⟨cand, hmem, (scalarInt08_eq_mk_iff out cand f.byteWidth).mp hout⟩
        · rintro ⟨cand, hmem, hout⟩
          exact ⟨cand, hmem, (scalarInt08_eq_mk_iff out cand f.byteWidth).mpr hout⟩
      · rw [if_neg' hnan, if_neg' hnan]
        exact scalarInt08_eq_mk_iff out baseBits f.byteWidth

/-- `abstractBytesHaveProv` agrees across dialects on ALL byte sequences. -/
theorem abstractBytesHaveProv_parity (bs : List AbstractByte) :
    V2026_08_01.MirSemantics.abstractBytesHaveProv (bs.map abstractByte08) =
      abstractBytesHaveProv bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | uninit => exact ih
    | init byte prov =>
      cases prov with
      | none => exact ih
      | some _ => rfl

/-- **`policyRejectsProv` parity**: the `Ptr2IntTransmutePolicy` provenance gate
agrees across dialects for BOTH policies on ALL byte sequences. -/
theorem policyRejectsProv_parity (policy : Ptr2IntTransmutePolicy) (bs : List AbstractByte) :
    V2026_08_01.MirSemantics.policyRejectsProv (policy08 policy) (bs.map abstractByte08) =
      policyRejectsProv policy bs := by
  cases policy with
  | strictUcg630Ub => exact abstractBytesHaveProv_parity bs
  | stripProvenance => rfl

/-- `stripAbstractBytesProv` commutes with the dialect translation. -/
theorem stripAbstractBytesProv_parity (bs : List AbstractByte) :
    V2026_08_01.MirSemantics.stripAbstractBytesProv (bs.map abstractByte08) =
      (stripAbstractBytesProv bs).map abstractByte08 := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    show V2026_08_01.MirSemantics.stripAbstractByteProv (abstractByte08 b) ::
        V2026_08_01.MirSemantics.stripAbstractBytesProv (rest.map abstractByte08) =
      abstractByte08 (stripAbstractByteProv b) :: (stripAbstractBytesProv rest).map abstractByte08
    rw [ih]
    cases b <;> rfl

/-! ### `Places`-level dialect parity (`evalFloatUnaryNeg`, `evalFloatScalarBinOp`, `decodeScalarLayoutBytesNoForge`) -/

/-- Dialect translation of `FloatTy` (`V2026_06_01 → V2026_08_01`). -/
def floatTy08 : FloatTy → V2026_08_01.MirAst.FloatTy
  | .f16 => .f16
  | .f32 => .f32
  | .f64 => .f64
  | .f128 => .f128

/-- Float-preserving dialect projection of `Ty` (`V2026_06_01 → V2026_08_01`): preserves
every `.float w` kind verbatim and maps non-float kinds to `.bool`. -/
def tyFloat08 (ty : Ty) : V2026_08_01.MirAst.Ty :=
  { kind := match ty.kind with
      | .float w => .float (floatTy08 w)
      | _ => .bool
    layoutIdx := ty.layoutIdx }

/-- Dialect translation of `WrappingRange` (`V2026_06_01 → V2026_08_01`). -/
def wrappingRange08 (r : WrappingRange) : V2026_08_01.Layout.WrappingRange :=
  { start := r.start, end_ := r.end_ }

/-- Dialect translation of `PrimitiveKind` (`V2026_06_01 → V2026_08_01`). -/
def primitiveKind08 : PrimitiveKind → V2026_08_01.Layout.PrimitiveKind
  | .int bits signed => .int bits signed
  | .float bits => .float bits
  | .pointer a => .pointer a

/-- Dialect translation of `ScalarLayout` (`V2026_06_01 → V2026_08_01`). -/
def scalarLayout08 : ScalarLayout → V2026_08_01.Layout.ScalarLayout
  | .initialized pk vr => .initialized (primitiveKind08 pk) (wrappingRange08 vr)
  | .union pk => .union (primitiveKind08 pk)

/-- Reverse dialect translation of `ScalarInt` (`V2026_08_01 → V2026_06_01`). -/
def scalarInt06 (s : V2026_08_01.MirAst.ScalarInt) : ScalarInt :=
  ⟨s.bits, s.sizeBytes⟩

/-- Reverse dialect translation of `ProvenancePtr` (`V2026_08_01 → V2026_06_01`). -/
def provenancePtr06 (p : V2026_08_01.MirAst.ProvenancePtr) : ProvenancePtr :=
  { allocId := p.allocId, offsetBytes := p.offsetBytes }

mutual
  /-- Total injective embedding of `V2026_08_01.MirSemantics.Value` into
  `V2026_06_01.MirSemantics.Value` (`V2026_08_01.Value` has no `.uninit` constructor). -/
  def value06 : V2026_08_01.MirSemantics.Value → Value
    | .unit => .unit
    | .scalar s => .scalar (scalarInt06 s)
    | .ptr p sz => .ptr (provenancePtr06 p) sz
    | .aggregate v fs => .aggregate v (valueList06 fs)

  /-- Elementwise embedding of `List V2026_08_01.MirSemantics.Value`. -/
  def valueList06 : List V2026_08_01.MirSemantics.Value → List Value
    | .nil => .nil
    | x :: xs => value06 x :: valueList06 xs
end

/-- Map a `V2026_08_01` `RvalueEvalResult` back to `V2026_06_01` at fixed state
`(locals06, mem06)`, preserving `.ok`/`.ub`/`.unsupported` and embedding the value
losslessly via `value06`. -/
def rvalueResWith06 (locals06 : List LocalSlot) (mem06 : Memory) :
    V2026_08_01.MirSemantics.RvalueEvalResult → RvalueEvalResult
  | .ok v _ _ => .ok (value06 v) locals06 mem06
  | .ub => .ub
  | .unsupported => .unsupported

private theorem length_map_abstractByte08 (bs : List AbstractByte) :
    length (bs.map abstractByte08) = length bs := by
  unfold length
  exact List.length_map abstractByte08

/-- `scalarInt06` is the left inverse of `scalarInt08`. -/
theorem scalarInt06_scalarInt08 (s : ScalarInt) : scalarInt06 (scalarInt08 s) = s := by
  cases s; rfl

mutual
  /-- `value06` is injective on all `V2026_08_01.MirSemantics.Value`s, so parity
  statements transported through `Option.map value06` / `rvalueResWith06` are lossless. -/
  theorem value06_injective : ∀ (v₁ v₂ : V2026_08_01.MirSemantics.Value),
      value06 v₁ = value06 v₂ → v₁ = v₂
    | .unit, .unit, _ => rfl
    | .scalar ⟨b₁, s₁⟩, .scalar ⟨b₂, s₂⟩, h => by
      unfold value06 scalarInt06 at h
      injection h with hs; injection hs with h1 h2; subst h1; subst h2; rfl
    | .ptr ⟨a₁, o₁⟩ sz₁, .ptr ⟨a₂, o₂⟩ sz₂, h => by
      unfold value06 provenancePtr06 at h
      injection h with hp hsz; injection hp with h1 h2; subst h1; subst h2; subst hsz; rfl
    | .aggregate v₁ fs₁, .aggregate v₂ fs₂, h => by
      unfold value06 at h
      injection h with hv hfs
      rw [hv, valueList06_injective fs₁ fs₂ hfs]
    | .unit, .scalar _, h | .unit, .ptr _ _, h | .unit, .aggregate _ _, h
    | .scalar _, .unit, h | .scalar _, .ptr _ _, h | .scalar _, .aggregate _ _, h
    | .ptr _ _, .unit, h | .ptr _ _, .scalar _, h | .ptr _ _, .aggregate _ _, h
    | .aggregate _ _, .unit, h | .aggregate _ _, .scalar _, h | .aggregate _ _, .ptr _ _, h => by
      cases h

  /-- `valueList06` is injective on all lists of `V2026_08_01.MirSemantics.Value`. -/
  theorem valueList06_injective : ∀ (xs ys : List V2026_08_01.MirSemantics.Value),
      valueList06 xs = valueList06 ys → xs = ys
    | .nil, .nil, _ => rfl
    | x :: xs, y :: ys, h => by
      unfold valueList06 at h
      injection h with hxy hrest
      rw [value06_injective x y hxy, valueList06_injective xs ys hrest]
    | .nil, _ :: _, h | _ :: _, .nil, h => by cases h
end

/-- `ieeeFormatOfTy?` agrees across dialects under `tyFloat08`. -/
theorem ieeeFormatOfTy?_parity (ty : Ty) :
    V2026_08_01.MirSemantics.ieeeFormatOfTy? (tyFloat08 ty) =
      Option.map fmt08 (ieeeFormatOfTy? ty) := by
  unfold V2026_08_01.MirSemantics.ieeeFormatOfTy? ieeeFormatOfTy? tyFloat08
  cases ty.kind with
  | float w => cases w <;> rfl
  | _ => rfl

/-- `isFloatTy` agrees across dialects under `tyFloat08`. -/
theorem isFloatTy_parity (ty : Ty) :
    V2026_08_01.MirSemantics.isFloatTy (tyFloat08 ty) = isFloatTy ty := by
  unfold V2026_08_01.MirSemantics.isFloatTy isFloatTy tyFloat08
  cases ty.kind <;> rfl

/-- `isFloatOptTy` agrees across dialects under `Option.map tyFloat08`. -/
theorem isFloatOptTy_parity (ty? : Option Ty) :
    V2026_08_01.MirSemantics.isFloatOptTy (Option.map tyFloat08 ty?) = isFloatOptTy ty? := by
  cases ty? with
  | none => rfl
  | some ty => exact isFloatTy_parity ty

/-- **`evalFloatUnaryNeg` parity (format-general)**: whenever `opTy06?` and `opTy08?`
resolve to the same modeled `IeeeFormat`, `V2026_08_01.evalFloatUnaryNeg` agrees
with `V2026_06_01.evalFloatUnaryNeg` and leaves `(locals08, mem08)` unchanged. -/
theorem evalFloatUnaryNeg_parity_of_fmt
    (sc : ScalarInt) (opTy06? : Option Ty) (opTy08? : Option V2026_08_01.MirAst.Ty)
    (locals06 : List LocalSlot) (mem06 : Memory)
    (locals08 : List V2026_08_01.MirSemantics.LocalSlot) (mem08 : V2026_08_01.MirSemantics.Memory)
    (hfmt : Option.bind opTy08? V2026_08_01.MirSemantics.ieeeFormatOfTy? =
      Option.map fmt08 (Option.bind opTy06? ieeeFormatOfTy?)) :
    rvalueResWith06 locals06 mem06
      (V2026_08_01.MirSemantics.evalFloatUnaryNeg (scalarInt08 sc) opTy08? locals08 mem08) =
      evalFloatUnaryNeg sc opTy06? locals06 mem06 ∧
    (∀ v l' m',
      V2026_08_01.MirSemantics.evalFloatUnaryNeg (scalarInt08 sc) opTy08? locals08 mem08 = .ok v l' m' →
        l' = locals08 ∧ m' = mem08) := by
  have h1 : V2026_08_01.MirSemantics.evalFloatUnaryNeg (scalarInt08 sc) opTy08? locals08 mem08 =
      match Option.bind opTy08? V2026_08_01.MirSemantics.ieeeFormatOfTy? with
      | .some f =>
        match Nat.beq sc.sizeBytes f.byteWidth with
        | true => .ok (.scalar ⟨V2026_08_01.MirSemantics.evalFloatNeg f sc.bits, f.byteWidth⟩) locals08 mem08
        | false => .unsupported
      | .none => .unsupported := by
    cases opTy08? <;> rfl
  have h2 : evalFloatUnaryNeg sc opTy06? locals06 mem06 =
      match Option.bind opTy06? ieeeFormatOfTy? with
      | .some f =>
        match Nat.beq sc.sizeBytes f.byteWidth with
        | true => .ok (.scalar ⟨evalFloatNeg f sc.bits, f.byteWidth⟩) locals06 mem06
        | false => .unsupported
      | .none => .unsupported := by
    cases opTy06? <;> rfl
  rw [h1, h2, hfmt]
  cases Option.bind opTy06? ieeeFormatOfTy? with
  | none => exact ⟨rfl, fun _ _ _ h => by cases h⟩
  | some f =>
    dsimp only [Option.map]
    rw [(fmt08_params f).2.2.2.2.1, evalFloatNeg_parity]
    cases Nat.beq sc.sizeBytes f.byteWidth with
    | false => exact ⟨rfl, fun _ _ _ h => by cases h⟩
    | true => exact ⟨rfl, fun _ _ _ h => by injection h with _ hl hm; exact ⟨hl.symm, hm.symm⟩⟩

/-- **`evalFloatUnaryNeg` parity** under `tyFloat08`. -/
theorem evalFloatUnaryNeg_parity
    (sc : ScalarInt) (opTy? : Option Ty)
    (locals06 : List LocalSlot) (mem06 : Memory)
    (locals08 : List V2026_08_01.MirSemantics.LocalSlot) (mem08 : V2026_08_01.MirSemantics.Memory) :
    rvalueResWith06 locals06 mem06
      (V2026_08_01.MirSemantics.evalFloatUnaryNeg (scalarInt08 sc) (Option.map tyFloat08 opTy?) locals08 mem08) =
      evalFloatUnaryNeg sc opTy? locals06 mem06 ∧
    (∀ v l' m',
      V2026_08_01.MirSemantics.evalFloatUnaryNeg (scalarInt08 sc) (Option.map tyFloat08 opTy?) locals08 mem08 = .ok v l' m' →
        l' = locals08 ∧ m' = mem08) := by
  apply evalFloatUnaryNeg_parity_of_fmt
  cases opTy? with
  | none => rfl
  | some ty => exact ieeeFormatOfTy?_parity ty

/-- **`evalFloatScalarBinOp` parity (format-general)**: whenever `lhsTy06?`/`lhsTy08?`
and `rhsTy06?`/`rhsTy08?` agree on their modeled `IeeeFormat`, `V2026_08_01.evalFloatScalarBinOp`
agrees with `V2026_06_01.evalFloatScalarBinOp` for every `BinOp` and leaves
`(locals08, mem08)` unchanged. -/
theorem evalFloatScalarBinOp_parity_of_fmt
    (op : BinOp) (lhs rhs : ScalarInt)
    (lhsTy06? rhsTy06? : Option Ty)
    (lhsTy08? rhsTy08? : Option V2026_08_01.MirAst.Ty)
    (locals06 : List LocalSlot) (mem06 : Memory)
    (locals08 : List V2026_08_01.MirSemantics.LocalSlot) (mem08 : V2026_08_01.MirSemantics.Memory)
    (hfmtL : Option.bind lhsTy08? V2026_08_01.MirSemantics.ieeeFormatOfTy? =
      Option.map fmt08 (Option.bind lhsTy06? ieeeFormatOfTy?))
    (hfmtR : Option.bind rhsTy08? V2026_08_01.MirSemantics.ieeeFormatOfTy? =
      Option.map fmt08 (Option.bind rhsTy06? ieeeFormatOfTy?)) :
    rvalueResWith06 locals06 mem06
      (V2026_08_01.MirSemantics.evalFloatScalarBinOp (binOp08 op) (scalarInt08 lhs) (scalarInt08 rhs)
        lhsTy08? rhsTy08? locals08 mem08) =
      evalFloatScalarBinOp op lhs rhs lhsTy06? rhsTy06? locals06 mem06 ∧
    (∀ v l' m',
      V2026_08_01.MirSemantics.evalFloatScalarBinOp (binOp08 op) (scalarInt08 lhs) (scalarInt08 rhs)
        lhsTy08? rhsTy08? locals08 mem08 = .ok v l' m' →
        l' = locals08 ∧ m' = mem08) := by
  have h1 : V2026_08_01.MirSemantics.evalFloatScalarBinOp (binOp08 op) (scalarInt08 lhs) (scalarInt08 rhs)
        lhsTy08? rhsTy08? locals08 mem08 =
      match Option.bind lhsTy08? V2026_08_01.MirSemantics.ieeeFormatOfTy?,
          Option.bind rhsTy08? V2026_08_01.MirSemantics.ieeeFormatOfTy? with
      | .some fL, .some fR =>
        let sameFmt : Bool :=
          match fL, fR with | .binary32, .binary32 => true | .binary64, .binary64 => true | _, _ => false
        match Bool.and sameFmt
            (Bool.and (Nat.beq lhs.sizeBytes fL.byteWidth) (Nat.beq rhs.sizeBytes fL.byteWidth)) with
        | true =>
          match V2026_08_01.MirSemantics.evalFloatBinOp (binOp08 op) fL lhs.bits rhs.bits with
          | .some outSc => .ok (.scalar outSc) locals08 mem08
          | .none => .unsupported
        | false => .unsupported
      | _, _ => .unsupported := by
    cases lhsTy08? with
    | none => rfl
    | some lTy =>
      cases rhsTy08? with
      | none =>
        unfold V2026_08_01.MirSemantics.evalFloatScalarBinOp; dsimp only [Option.bind]
        cases V2026_08_01.MirSemantics.ieeeFormatOfTy? lTy <;> rfl
      | some rTy => rfl
  have h2 : evalFloatScalarBinOp op lhs rhs lhsTy06? rhsTy06? locals06 mem06 =
      match Option.bind lhsTy06? ieeeFormatOfTy?, Option.bind rhsTy06? ieeeFormatOfTy? with
      | .some fL, .some fR =>
        let sameFmt : Bool :=
          match fL, fR with | .binary32, .binary32 => true | .binary64, .binary64 => true | _, _ => false
        match Bool.and sameFmt
            (Bool.and (Nat.beq lhs.sizeBytes fL.byteWidth) (Nat.beq rhs.sizeBytes fL.byteWidth)) with
        | true =>
          match evalFloatBinOp op fL lhs.bits rhs.bits with
          | .some outSc => .ok (.scalar outSc) locals06 mem06
          | .none => .unsupported
        | false => .unsupported
      | _, _ => .unsupported := by
    cases lhsTy06? with
    | none => rfl
    | some lTy =>
      cases rhsTy06? with
      | none =>
        unfold evalFloatScalarBinOp; dsimp only [Option.bind]
        cases ieeeFormatOfTy? lTy <;> rfl
      | some rTy => rfl
  rw [h1, h2, hfmtL, hfmtR]
  cases Option.bind lhsTy06? ieeeFormatOfTy? with
  | none => exact ⟨rfl, fun _ _ _ h => by cases h⟩
  | some fL =>
    cases Option.bind rhsTy06? ieeeFormatOfTy? with
    | none => exact ⟨rfl, fun _ _ _ h => by cases h⟩
    | some fR =>
      dsimp only [Option.map]
      cases fL <;> cases fR
      · rw [evalFloatBinOp_parity]
        dsimp only [fmt08, V2026_08_01.MirSemantics.IeeeFormat.byteWidth, IeeeFormat.byteWidth,
          Bool.true_and]
        cases Bool.and (Nat.beq lhs.sizeBytes 4) (Nat.beq rhs.sizeBytes 4) with
        | false => exact ⟨rfl, fun _ _ _ h => by cases h⟩
        | true =>
          cases evalFloatBinOp op .binary32 lhs.bits rhs.bits with
          | none => exact ⟨rfl, fun _ _ _ h => by cases h⟩
          | some outSc =>
            dsimp only [Option.map]
            refine ⟨?_, fun _ _ _ h => by injection h with _ hl hm; exact ⟨hl.symm, hm.symm⟩⟩
            show RvalueEvalResult.ok (Value.scalar (scalarInt06 (scalarInt08 outSc))) locals06 mem06 = _
            rw [scalarInt06_scalarInt08]; rfl
      · exact ⟨rfl, fun _ _ _ h => by cases h⟩
      · exact ⟨rfl, fun _ _ _ h => by cases h⟩
      · rw [evalFloatBinOp_parity]
        dsimp only [fmt08, V2026_08_01.MirSemantics.IeeeFormat.byteWidth, IeeeFormat.byteWidth,
          Bool.true_and]
        cases Bool.and (Nat.beq lhs.sizeBytes 8) (Nat.beq rhs.sizeBytes 8) with
        | false => exact ⟨rfl, fun _ _ _ h => by cases h⟩
        | true =>
          cases evalFloatBinOp op .binary64 lhs.bits rhs.bits with
          | none => exact ⟨rfl, fun _ _ _ h => by cases h⟩
          | some outSc =>
            dsimp only [Option.map]
            refine ⟨?_, fun _ _ _ h => by injection h with _ hl hm; exact ⟨hl.symm, hm.symm⟩⟩
            show RvalueEvalResult.ok (Value.scalar (scalarInt06 (scalarInt08 outSc))) locals06 mem06 = _
            rw [scalarInt06_scalarInt08]; rfl

/-- **`evalFloatScalarBinOp` parity** under `tyFloat08`. -/
theorem evalFloatScalarBinOp_parity
    (op : BinOp) (lhs rhs : ScalarInt) (lhsTy? rhsTy? : Option Ty)
    (locals06 : List LocalSlot) (mem06 : Memory)
    (locals08 : List V2026_08_01.MirSemantics.LocalSlot) (mem08 : V2026_08_01.MirSemantics.Memory) :
    rvalueResWith06 locals06 mem06
      (V2026_08_01.MirSemantics.evalFloatScalarBinOp (binOp08 op) (scalarInt08 lhs) (scalarInt08 rhs)
        (Option.map tyFloat08 lhsTy?) (Option.map tyFloat08 rhsTy?) locals08 mem08) =
      evalFloatScalarBinOp op lhs rhs lhsTy? rhsTy? locals06 mem06 ∧
    (∀ v l' m',
      V2026_08_01.MirSemantics.evalFloatScalarBinOp (binOp08 op) (scalarInt08 lhs) (scalarInt08 rhs)
        (Option.map tyFloat08 lhsTy?) (Option.map tyFloat08 rhsTy?) locals08 mem08 = .ok v l' m' →
        l' = locals08 ∧ m' = mem08) := by
  apply evalFloatScalarBinOp_parity_of_fmt
  · cases lhsTy? with | none => rfl | some ty => exact ieeeFormatOfTy?_parity ty
  · cases rhsTy? with | none => rfl | some ty => exact ieeeFormatOfTy?_parity ty

private theorem mergeByteProvenance_parity (p₁ p₂ : Option (Nat × Nat)) :
    V2026_08_01.MirSemantics.mergeByteProvenance p₁ p₂ = mergeByteProvenance p₁ p₂ := by
  cases p₂ with
  | none => rfl
  | some _ => cases p₁ <;> rfl

/-- `decodeLittleEndianBytes` agrees across dialects on all byte sequences. -/
theorem decodeLittleEndianBytes_parity (bs : List AbstractByte) :
    V2026_08_01.MirSemantics.decodeLittleEndianBytes (bs.map abstractByte08) =
      decodeLittleEndianBytes bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | uninit => rfl
    | init byte prov =>
      unfold V2026_08_01.MirSemantics.decodeLittleEndianBytes decodeLittleEndianBytes
      dsimp only [List.map, abstractByte08]
      rewrite [ih]
      cases decodeLittleEndianBytes rest with
      | none => rfl
      | some res =>
        rcases res with ⟨highBits, restProv⟩
        exact congrArg
          (fun p => Option.some (Nat.add byte.toBitVec.toNat (Nat.mul 256 highBits), p))
          (mergeByteProvenance_parity prov restProv)

/-- `decodeScalarBytes` agrees across dialects on all byte sequences. -/
theorem decodeScalarBytes_parity (bs : List AbstractByte) (signed : Bool) :
    V2026_08_01.MirSemantics.decodeScalarBytes (bs.map abstractByte08) signed =
      Option.map (fun p => (scalarInt08 p.1, p.2)) (decodeScalarBytes bs signed) := by
  unfold V2026_08_01.MirSemantics.decodeScalarBytes decodeScalarBytes
  dsimp only
  rw [length_map_abstractByte08, decodeLittleEndianBytes_parity]
  cases Nat.beq (length bs) 0 with
  | true => rfl
  | false =>
    cases decodeLittleEndianBytes bs with
    | none => rfl
    | some res => rcases res with ⟨bits, prov⟩; rfl

/-- `abstractBytesAllProvAux` agrees across dialects on all byte sequences. -/
theorem abstractBytesAllProvAux_parity (allocId tag : Nat) (bs : List AbstractByte) :
    V2026_08_01.MirSemantics.abstractBytesAllProvAux allocId tag (bs.map abstractByte08) =
      abstractBytesAllProvAux allocId tag bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | uninit => rfl
    | init _ prov =>
      cases prov with
      | none => rfl
      | some p =>
        rcases p with ⟨a, t⟩
        show Bool.and (Bool.and (Nat.beq a allocId) (Nat.beq t tag))
            (V2026_08_01.MirSemantics.abstractBytesAllProvAux allocId tag (rest.map abstractByte08)) = _
        rw [ih]; rfl

/-- `abstractBytesUniformProv` agrees across dialects on all byte sequences. -/
theorem abstractBytesUniformProv_parity (bs : List AbstractByte) :
    V2026_08_01.MirSemantics.abstractBytesUniformProv (bs.map abstractByte08) =
      abstractBytesUniformProv bs := by
  cases bs with
  | nil => rfl
  | cons b rest =>
    cases b with
    | uninit => rfl
    | init _ prov =>
      cases prov with
      | none => rfl
      | some p => rcases p with ⟨a, t⟩; exact abstractBytesAllProvAux_parity a t rest

/-- `primitiveKindByteWidth` agrees across dialects. -/
theorem primitiveKindByteWidth_parity (pk : PrimitiveKind) :
    V2026_08_01.MirSemantics.primitiveKindByteWidth (primitiveKind08 pk) =
      primitiveKindByteWidth pk := by
  cases pk <;> rfl

/-- `scalarLayoutByteWidth` agrees across dialects. -/
theorem scalarLayoutByteWidth_parity (sl : ScalarLayout) :
    V2026_08_01.MirSemantics.scalarLayoutByteWidth (scalarLayout08 sl) =
      scalarLayoutByteWidth sl := by
  cases sl with
  | initialized pk _ => exact primitiveKindByteWidth_parity pk
  | union pk => exact primitiveKindByteWidth_parity pk

/-- `wrappingRangeContains` agrees across dialects. -/
theorem wrappingRangeContains_parity (vr : WrappingRange) (v : Nat) :
    V2026_08_01.MirSemantics.wrappingRangeContains (wrappingRange08 vr) v =
      wrappingRangeContains vr v := by
  cases vr; rfl

/-- `isValidCharCode` agrees across dialects. -/
theorem isValidCharCode_parity (code : Nat) :
    V2026_08_01.MirSemantics.isValidCharCode code = isValidCharCode code := rfl

/-- **`decodeScalarLayoutBytesNoForge` parity**: the UCG-630 policy-parametric scalar
byte decoder agrees across dialects for EVERY `ScalarLayout`, byte sequence, and
`Ptr2IntTransmutePolicy` (transported losslessly through injective `value06`). -/
theorem decodeScalarLayoutBytesNoForge_parity
    (sl : ScalarLayout) (bs : List AbstractByte) (policy : Ptr2IntTransmutePolicy) :
    Option.map value06
      (V2026_08_01.MirSemantics.decodeScalarLayoutBytesNoForge
        (scalarLayout08 sl) (bs.map abstractByte08) (policy08 policy)) =
      decodeScalarLayoutBytesNoForge sl bs policy := by
  unfold V2026_08_01.MirSemantics.decodeScalarLayoutBytesNoForge decodeScalarLayoutBytesNoForge
  rw [scalarLayoutByteWidth_parity, length_map_abstractByte08]
  cases scalarLayoutByteWidth sl with
  | none => rfl
  | some sz =>
    dsimp only
    cases Nat.beq (length bs) sz with
    | false => dsimp only; rfl
    | true =>
      dsimp only
      have hdec_init : ∀ vr : WrappingRange,
          Option.map value06
            (match V2026_08_01.MirSemantics.decodeScalarBytes (bs.map abstractByte08) false with
             | .none => .none
             | .some (sv, _) =>
               match V2026_08_01.MirSemantics.wrappingRangeContains (wrappingRange08 vr) sv.bits with
               | false => .none
               | true =>
                 match Bool.and (Nat.beq sv.sizeBytes 4)
                     (Bool.and (Nat.beq (wrappingRange08 vr).start 0) (Nat.beq (wrappingRange08 vr).end_ 0x10FFFF)) with
                 | true =>
                   match V2026_08_01.MirSemantics.isValidCharCode sv.bits with
                   | true => .some (.scalar sv)
                   | false => .none
                 | false => .some (.scalar sv)) =
            (match decodeScalarBytes bs false with
             | .none => .none
             | .some (sv, _) =>
               match wrappingRangeContains vr sv.bits with
               | false => .none
               | true =>
                 match Bool.and (Nat.beq sv.sizeBytes 4)
                     (Bool.and (Nat.beq vr.start 0) (Nat.beq vr.end_ 0x10FFFF)) with
                 | true =>
                   match isValidCharCode sv.bits with
                   | true => .some (.scalar sv)
                   | false => .none
                 | false => .some (.scalar sv)) := by
        intro vr
        rw [decodeScalarBytes_parity]
        cases decodeScalarBytes bs false with
        | none => rfl
        | some res =>
          rcases res with ⟨sv, _⟩
          dsimp only [Option.map, scalarInt08]
          rw [wrappingRangeContains_parity]
          cases wrappingRangeContains vr sv.bits with
          | false => rfl
          | true =>
            dsimp only [wrappingRange08]
            cases Bool.and (Nat.beq sv.sizeBytes 4)
                (Bool.and (Nat.beq vr.start 0) (Nat.beq vr.end_ 0x10FFFF)) with
            | false =>
              show Option.some (Value.scalar (scalarInt06 (scalarInt08 sv))) = _
              rw [scalarInt06_scalarInt08]
            | true =>
              rw [isValidCharCode_parity]
              cases isValidCharCode sv.bits with
              | false => rfl
              | true =>
                show Option.some (Value.scalar (scalarInt06 (scalarInt08 sv))) = _
                rw [scalarInt06_scalarInt08]
      have hdec_union :
          Option.map value06
            (match V2026_08_01.MirSemantics.decodeScalarBytes (bs.map abstractByte08) false with
             | .some (sv, _) => .some (.scalar sv)
             | .none => .none) =
            (match decodeScalarBytes bs false with
             | .some (sv, _) => .some (.scalar sv)
             | .none => .none) := by
        rw [decodeScalarBytes_parity]
        cases decodeScalarBytes bs false with
        | none => rfl
        | some res =>
          rcases res with ⟨sv, _⟩
          dsimp only [Option.map]
          show Option.some (Value.scalar (scalarInt06 (scalarInt08 sv))) = _
          rw [scalarInt06_scalarInt08]
      cases sl with
      | initialized pk vr =>
        cases pk with
        | pointer _ =>
          dsimp only [scalarLayout08, primitiveKind08]
          rw [decodeScalarBytes_parity, abstractBytesUniformProv_parity]
          cases decodeScalarBytes bs false with
          | none => rfl
          | some res =>
            rcases res with ⟨sv, prov⟩
            dsimp only [Option.map, scalarInt08]
            cases abstractBytesUniformProv bs with
            | true =>
              cases prov with
              | some p => rcases p with ⟨allocId, _⟩; rfl
              | none =>
                rw [wrappingRangeContains_parity]
                cases wrappingRangeContains vr sv.bits with
                | true =>
                  show Option.some (Value.scalar (scalarInt06 (scalarInt08 sv))) = _
                  rw [scalarInt06_scalarInt08]
                | false => rfl
            | false =>
              rw [wrappingRangeContains_parity]
              cases wrappingRangeContains vr sv.bits with
              | true =>
                show Option.some (Value.scalar (scalarInt06 (scalarInt08 sv))) = _
                rw [scalarInt06_scalarInt08]
              | false => rfl
        | int _ _ =>
          dsimp only [scalarLayout08, primitiveKind08]
          cases policy with
          | strictUcg630Ub =>
            dsimp only [policy08]
            rw [abstractBytesHaveProv_parity]
            cases abstractBytesHaveProv bs with
            | true => rfl
            | false => exact hdec_init vr
          | stripProvenance =>
            dsimp only [policy08]
            exact hdec_init vr
        | float _ =>
          dsimp only [scalarLayout08, primitiveKind08]
          cases policy with
          | strictUcg630Ub =>
            dsimp only [policy08]
            rw [abstractBytesHaveProv_parity]
            cases abstractBytesHaveProv bs with
            | true => rfl
            | false => exact hdec_init vr
          | stripProvenance =>
            dsimp only [policy08]
            exact hdec_init vr
      | union pk =>
        cases pk with
        | pointer _ =>
          dsimp only [scalarLayout08, primitiveKind08]
          rw [decodeScalarBytes_parity, abstractBytesUniformProv_parity]
          cases decodeScalarBytes bs false with
          | none => rfl
          | some res =>
            rcases res with ⟨sv, prov⟩
            dsimp only [Option.map, scalarInt08]
            cases abstractBytesUniformProv bs with
            | true =>
              cases prov with
              | some p => rcases p with ⟨allocId, _⟩; rfl
              | none =>
                show Option.some (Value.scalar (scalarInt06 (scalarInt08 sv))) = _
                rw [scalarInt06_scalarInt08]
            | false =>
              show Option.some (Value.scalar (scalarInt06 (scalarInt08 sv))) = _
              rw [scalarInt06_scalarInt08]
        | int _ _ =>
          dsimp only [scalarLayout08, primitiveKind08]
          cases policy with
          | strictUcg630Ub =>
            dsimp only [policy08]
            rw [abstractBytesHaveProv_parity]
            cases abstractBytesHaveProv bs with
            | true => rfl
            | false => exact hdec_union
          | stripProvenance =>
            dsimp only [policy08]
            exact hdec_union
        | float _ =>
          dsimp only [scalarLayout08, primitiveKind08]
          cases policy with
          | strictUcg630Ub =>
            dsimp only [policy08]
            rw [abstractBytesHaveProv_parity]
            cases abstractBytesHaveProv bs with
            | true => rfl
            | false => exact hdec_union
          | stripProvenance =>
            dsimp only [policy08]
            exact hdec_union

/-! ### `EvalRvalueFloatRel` cross-dialect parity (`V2026_06_01` <-> `V2026_08_01`)

Compositional cross-dialect parity for `evalRvalue` and `EvalRvalueFloatRel` on float
`.unaryOp .neg`, float `.binaryOp`, and `.cast .floatToFloat` parameterized by dialect-matching
`evalOperand` and `operandTy` hypotheses (so no monolithic `Memory`/`LayoutTable` bijection is
needed), followed by direct specializations to scalar constants and local variables (`.copy` and
`.move`). -/

/-- `V2026_08_01` scalar constant operand constructor matching `mkFloatConstOp`. -/
def mkFloatConstOp08 (ty : V2026_08_01.MirAst.Ty) (bits sizeBytes : Nat) :
    V2026_08_01.MirAst.Operand :=
  .constant { ty := ty, val := .scalar (.int ⟨bits, sizeBytes⟩) }

/-- Injectivity of `rvalueResWith06 locals06 mem06` on `V2026_08_01` results sharing a fixed
post-state `(locals08, mem08)` whenever `.ok`. -/
theorem rvalueResWith06_injective_at
    (locals06 : List LocalSlot) (mem06 : Memory)
    (locals08 : List V2026_08_01.MirSemantics.LocalSlot) (mem08 : V2026_08_01.MirSemantics.Memory)
    (r₁ r₂ : V2026_08_01.MirSemantics.RvalueEvalResult)
    (heq : rvalueResWith06 locals06 mem06 r₁ = rvalueResWith06 locals06 mem06 r₂)
    (h₁ : ∀ v l' m', r₁ = .ok v l' m' → l' = locals08 ∧ m' = mem08)
    (h₂ : ∀ v l' m', r₂ = .ok v l' m' → l' = locals08 ∧ m' = mem08) :
    r₁ = r₂ := by
  cases r₁ with
  | ub =>
    cases r₂ with
    | ub => rfl
    | unsupported => cases heq
    | ok _ _ _ => cases heq
  | unsupported =>
    cases r₂ with
    | ub => cases heq
    | unsupported => rfl
    | ok _ _ _ => cases heq
  | ok v₁ l₁ m₁ =>
    cases r₂ with
    | ub => cases heq
    | unsupported => cases heq
    | ok v₂ l₂ m₂ =>
      unfold rvalueResWith06 at heq
      injection heq with hv _ _
      obtain ⟨hl₁, hm₁⟩ := h₁ v₁ l₁ m₁ rfl
      obtain ⟨hl₂, hm₂⟩ := h₂ v₂ l₂ m₂ rfl
      rw [value06_injective v₁ v₂ hv, hl₁, hl₂, hm₁, hm₂]

/-- **`evalRvalue` cross-dialect parity on float `.unaryOp .neg`**: whenever `op06` and `op08`
evaluate to matching scalar values with float static types agreeing on `ieeeFormatOfTy?`,
`V2026_08_01.evalRvalue` agrees with `V2026_06_01.evalRvalue` (transported via `rvalueResWith06`)
and preserves `(locals08', mem08)` on every `.ok` outcome. -/
theorem evalRvalue_unaryNeg_float_parity
    (locals06 locals06' : List LocalSlot) (op06 : Operand)
    (mem06 : Memory) (localDecls06 : List LocalDecl) (layouts06 : LayoutTable)
    (locals08 locals08' : List V2026_08_01.MirSemantics.LocalSlot) (op08 : V2026_08_01.MirAst.Operand)
    (mem08 : V2026_08_01.MirSemantics.Memory)
    (localDecls08 : List V2026_08_01.MirAst.LocalDecl) (layouts08 : V2026_08_01.Layout.LayoutTable)
    (sc : ScalarInt)
    (hEval06 : evalOperand locals06 op06 mem06.borrows mem06.globals layouts06 mem06.callerLocals localDecls06 mem06.callStack =
      .ok (.scalar sc) locals06')
    (hEval08 : V2026_08_01.MirSemantics.evalOperand locals08 op08 mem08.borrows mem08.globals layouts08 mem08.callerLocals localDecls08 mem08.callStack =
      .ok (.scalar (scalarInt08 sc)) locals08')
    (hFloat06 : isFloatOptTy (operandTy localDecls06 layouts06 op06) = true)
    (hFloat08 : V2026_08_01.MirSemantics.isFloatOptTy (V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 op08) = true)
    (hFmt : Option.bind (V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 op08) V2026_08_01.MirSemantics.ieeeFormatOfTy? =
      Option.map fmt08 (Option.bind (operandTy localDecls06 layouts06 op06) ieeeFormatOfTy?)) :
    rvalueResWith06 locals06' mem06
      (V2026_08_01.MirSemantics.evalRvalue locals08 (.unaryOp .neg op08) mem08 localDecls08 layouts08) =
      evalRvalue locals06 (.unaryOp .neg op06) mem06 localDecls06 layouts06 ∧
    (∀ v l' m',
      V2026_08_01.MirSemantics.evalRvalue locals08 (.unaryOp .neg op08) mem08 localDecls08 layouts08 = .ok v l' m' →
        l' = locals08' ∧ m' = mem08) := by
  have he06 : evalRvalue locals06 (.unaryOp .neg op06) mem06 localDecls06 layouts06 =
      evalFloatUnaryNeg sc (operandTy localDecls06 layouts06 op06) locals06' mem06 := by
    unfold evalRvalue; dsimp only; rw [hEval06]; dsimp only; rw [hFloat06]
  have he08 : V2026_08_01.MirSemantics.evalRvalue locals08 (.unaryOp .neg op08) mem08 localDecls08 layouts08 =
      V2026_08_01.MirSemantics.evalFloatUnaryNeg (scalarInt08 sc)
        (V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 op08) locals08' mem08 := by
    unfold V2026_08_01.MirSemantics.evalRvalue; dsimp only; rw [hEval08]; dsimp only; rw [hFloat08]
  rw [he06, he08]
  exact evalFloatUnaryNeg_parity_of_fmt sc _ _ locals06' mem06 locals08' mem08 hFmt

/-- **`EvalRvalueFloatRel` cross-dialect parity on float `.unaryOp .neg`** (BOTH modes, ANY
policy): `V2026_08_01.EvalRvalueFloatRel` admits `res08` IF AND ONLY IF `V2026_06_01.EvalRvalueFloatRel`
admits `rvalueResWith06 locals06' mem06 res08` and every `.ok` outcome has post-state `(locals08', mem08)`. -/
theorem EvalRvalueFloatRel_unaryNeg_float_parity
    (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (locals06 locals06' : List LocalSlot) (op06 : Operand)
    (mem06 : Memory) (localDecls06 : List LocalDecl) (layouts06 : LayoutTable)
    (locals08 locals08' : List V2026_08_01.MirSemantics.LocalSlot) (op08 : V2026_08_01.MirAst.Operand)
    (mem08 : V2026_08_01.MirSemantics.Memory)
    (localDecls08 : List V2026_08_01.MirAst.LocalDecl) (layouts08 : V2026_08_01.Layout.LayoutTable)
    (sc : ScalarInt) (res08 : V2026_08_01.MirSemantics.RvalueEvalResult)
    (hEval06 : evalOperand locals06 op06 mem06.borrows mem06.globals layouts06 mem06.callerLocals localDecls06 mem06.callStack =
      .ok (.scalar sc) locals06')
    (hEval08 : V2026_08_01.MirSemantics.evalOperand locals08 op08 mem08.borrows mem08.globals layouts08 mem08.callerLocals localDecls08 mem08.callStack =
      .ok (.scalar (scalarInt08 sc)) locals08')
    (hFloat06 : isFloatOptTy (operandTy localDecls06 layouts06 op06) = true)
    (hFloat08 : V2026_08_01.MirSemantics.isFloatOptTy (V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 op08) = true)
    (hFmt : Option.bind (V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 op08) V2026_08_01.MirSemantics.ieeeFormatOfTy? =
      Option.map fmt08 (Option.bind (operandTy localDecls06 layouts06 op06) ieeeFormatOfTy?)) :
    V2026_08_01.MirSemantics.EvalRvalueFloatRel (mode08 mode) (policy08 policy)
        locals08 (.unaryOp .neg op08) mem08 localDecls08 layouts08 res08 ↔
      (EvalRvalueFloatRel mode policy locals06 (.unaryOp .neg op06) mem06 localDecls06 layouts06
          (rvalueResWith06 locals06' mem06 res08) ∧
        ∀ v l' m', res08 = .ok v l' m' → l' = locals08' ∧ m' = mem08) := by
  obtain ⟨hEq, hPost⟩ :=
    evalRvalue_unaryNeg_float_parity locals06 locals06' op06 mem06 localDecls06 layouts06
      locals08 locals08' op08 mem08 localDecls08 layouts08 sc hEval06 hEval08 hFloat06 hFloat08 hFmt
  unfold V2026_08_01.MirSemantics.EvalRvalueFloatRel EvalRvalueFloatRel
  dsimp only
  constructor
  · intro h08
    rw [h08]
    exact ⟨hEq, hPost⟩
  · rintro ⟨h06, hResPost⟩
    exact rvalueResWith06_injective_at locals06' mem06 locals08' mem08 res08 _
      (h06.trans hEq.symm) hResPost hPost

/-- **`evalRvalue` cross-dialect parity on float `.binaryOp`**: for EVERY non-`.offset` `BinOp`
(including `f16`/`f128`, mismatched formats/widths, and non-float `BinOp`s failing closed to
`.unsupported`), whenever both operands evaluate to matching scalars with at least one float type
in each dialect and dialect-matching `ieeeFormatOfTy?`, `V2026_08_01.evalRvalue` agrees with
`V2026_06_01.evalRvalue` and preserves `(locals08₂, mem08)` on every `.ok` outcome. -/
theorem evalRvalue_binaryOp_float_parity
    (op : BinOp) (hNotOff : op ≠ .offset)
    (locals06 locals06₁ locals06₂ : List LocalSlot) (lhsOp06 rhsOp06 : Operand)
    (mem06 : Memory) (localDecls06 : List LocalDecl) (layouts06 : LayoutTable)
    (locals08 locals08₁ locals08₂ : List V2026_08_01.MirSemantics.LocalSlot)
    (lhsOp08 rhsOp08 : V2026_08_01.MirAst.Operand)
    (mem08 : V2026_08_01.MirSemantics.Memory)
    (localDecls08 : List V2026_08_01.MirAst.LocalDecl) (layouts08 : V2026_08_01.Layout.LayoutTable)
    (lhs rhs : ScalarInt)
    (hl06 : evalOperand locals06 lhsOp06 mem06.borrows mem06.globals layouts06 mem06.callerLocals localDecls06 mem06.callStack =
      .ok (.scalar lhs) locals06₁)
    (hr06 : evalOperand locals06₁ rhsOp06 mem06.borrows mem06.globals layouts06 mem06.callerLocals localDecls06 mem06.callStack =
      .ok (.scalar rhs) locals06₂)
    (hl08 : V2026_08_01.MirSemantics.evalOperand locals08 lhsOp08 mem08.borrows mem08.globals layouts08 mem08.callerLocals localDecls08 mem08.callStack =
      .ok (.scalar (scalarInt08 lhs)) locals08₁)
    (hr08 : V2026_08_01.MirSemantics.evalOperand locals08₁ rhsOp08 mem08.borrows mem08.globals layouts08 mem08.callerLocals localDecls08 mem08.callStack =
      .ok (.scalar (scalarInt08 rhs)) locals08₂)
    (hFloat06 : Bool.or (isFloatOptTy (operandTy localDecls06 layouts06 lhsOp06))
        (isFloatOptTy (operandTy localDecls06 layouts06 rhsOp06)) = true)
    (hFloat08 : Bool.or (V2026_08_01.MirSemantics.isFloatOptTy (V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 lhsOp08))
        (V2026_08_01.MirSemantics.isFloatOptTy (V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 rhsOp08)) = true)
    (hFmtL : Option.bind (V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 lhsOp08) V2026_08_01.MirSemantics.ieeeFormatOfTy? =
      Option.map fmt08 (Option.bind (operandTy localDecls06 layouts06 lhsOp06) ieeeFormatOfTy?))
    (hFmtR : Option.bind (V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 rhsOp08) V2026_08_01.MirSemantics.ieeeFormatOfTy? =
      Option.map fmt08 (Option.bind (operandTy localDecls06 layouts06 rhsOp06) ieeeFormatOfTy?)) :
    rvalueResWith06 locals06₂ mem06
      (V2026_08_01.MirSemantics.evalRvalue locals08 (.binaryOp (binOp08 op) lhsOp08 rhsOp08) mem08 localDecls08 layouts08) =
      evalRvalue locals06 (.binaryOp op lhsOp06 rhsOp06) mem06 localDecls06 layouts06 ∧
    (∀ v l' m',
      V2026_08_01.MirSemantics.evalRvalue locals08 (.binaryOp (binOp08 op) lhsOp08 rhsOp08) mem08 localDecls08 layouts08 = .ok v l' m' →
        l' = locals08₂ ∧ m' = mem08) := by
  have he06 : evalRvalue locals06 (.binaryOp op lhsOp06 rhsOp06) mem06 localDecls06 layouts06 =
      evalFloatScalarBinOp op lhs rhs (operandTy localDecls06 layouts06 lhsOp06)
        (operandTy localDecls06 layouts06 rhsOp06) locals06₂ mem06 := by
    unfold evalRvalue; dsimp only; rw [hl06]; dsimp only; rw [hr06]; dsimp only
    cases op with
    | offset => exact absurd rfl hNotOff
    | _ => dsimp only; rw [hFloat06]
  have he08 : V2026_08_01.MirSemantics.evalRvalue locals08 (.binaryOp (binOp08 op) lhsOp08 rhsOp08) mem08 localDecls08 layouts08 =
      V2026_08_01.MirSemantics.evalFloatScalarBinOp (binOp08 op) (scalarInt08 lhs) (scalarInt08 rhs)
        (V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 lhsOp08)
        (V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 rhsOp08) locals08₂ mem08 := by
    unfold V2026_08_01.MirSemantics.evalRvalue; dsimp only; rw [hl08]; dsimp only; rw [hr08]; dsimp only
    cases op with
    | offset => exact absurd rfl hNotOff
    | _ => dsimp only [binOp08]; rw [hFloat08]
  rw [he06, he08]
  exact evalFloatScalarBinOp_parity_of_fmt op lhs rhs _ _ _ _ locals06₂ mem06 locals08₂ mem08 hFmtL hFmtR

/-- **`EvalRvalueFloatRel` cross-dialect parity on float `.binaryOp`** (BOTH `.deterministic` and
`.nondeterministic` modes, ANY `Ptr2IntTransmutePolicy`, ALL non-`.offset` `BinOp`s):
`V2026_08_01.EvalRvalueFloatRel` admits `res08` IF AND ONLY IF `V2026_06_01.EvalRvalueFloatRel`
admits `rvalueResWith06 locals06₂ mem06 res08` and every `.ok` outcome has post-state
`(locals08₂, mem08)`. -/
theorem EvalRvalueFloatRel_binaryOp_float_parity
    (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (op : BinOp) (hNotOff : op ≠ .offset)
    (locals06 locals06₁ locals06₂ : List LocalSlot) (lhsOp06 rhsOp06 : Operand)
    (mem06 : Memory) (localDecls06 : List LocalDecl) (layouts06 : LayoutTable)
    (locals08 locals08₁ locals08₂ : List V2026_08_01.MirSemantics.LocalSlot)
    (lhsOp08 rhsOp08 : V2026_08_01.MirAst.Operand)
    (mem08 : V2026_08_01.MirSemantics.Memory)
    (localDecls08 : List V2026_08_01.MirAst.LocalDecl) (layouts08 : V2026_08_01.Layout.LayoutTable)
    (lhs rhs : ScalarInt) (res08 : V2026_08_01.MirSemantics.RvalueEvalResult)
    (hl06 : evalOperand locals06 lhsOp06 mem06.borrows mem06.globals layouts06 mem06.callerLocals localDecls06 mem06.callStack =
      .ok (.scalar lhs) locals06₁)
    (hr06 : evalOperand locals06₁ rhsOp06 mem06.borrows mem06.globals layouts06 mem06.callerLocals localDecls06 mem06.callStack =
      .ok (.scalar rhs) locals06₂)
    (hl08 : V2026_08_01.MirSemantics.evalOperand locals08 lhsOp08 mem08.borrows mem08.globals layouts08 mem08.callerLocals localDecls08 mem08.callStack =
      .ok (.scalar (scalarInt08 lhs)) locals08₁)
    (hr08 : V2026_08_01.MirSemantics.evalOperand locals08₁ rhsOp08 mem08.borrows mem08.globals layouts08 mem08.callerLocals localDecls08 mem08.callStack =
      .ok (.scalar (scalarInt08 rhs)) locals08₂)
    (hFloat06 : Bool.or (isFloatOptTy (operandTy localDecls06 layouts06 lhsOp06))
        (isFloatOptTy (operandTy localDecls06 layouts06 rhsOp06)) = true)
    (hFloat08 : Bool.or (V2026_08_01.MirSemantics.isFloatOptTy (V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 lhsOp08))
        (V2026_08_01.MirSemantics.isFloatOptTy (V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 rhsOp08)) = true)
    (hFmtL : Option.bind (V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 lhsOp08) V2026_08_01.MirSemantics.ieeeFormatOfTy? =
      Option.map fmt08 (Option.bind (operandTy localDecls06 layouts06 lhsOp06) ieeeFormatOfTy?))
    (hFmtR : Option.bind (V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 rhsOp08) V2026_08_01.MirSemantics.ieeeFormatOfTy? =
      Option.map fmt08 (Option.bind (operandTy localDecls06 layouts06 rhsOp06) ieeeFormatOfTy?)) :
    V2026_08_01.MirSemantics.EvalRvalueFloatRel (mode08 mode) (policy08 policy)
        locals08 (.binaryOp (binOp08 op) lhsOp08 rhsOp08) mem08 localDecls08 layouts08 res08 ↔
      (EvalRvalueFloatRel mode policy locals06 (.binaryOp op lhsOp06 rhsOp06) mem06 localDecls06 layouts06
          (rvalueResWith06 locals06₂ mem06 res08) ∧
        ∀ v l' m', res08 = .ok v l' m' → l' = locals08₂ ∧ m' = mem08) := by
  have hunsup : res08 = .unsupported ↔
      (rvalueResWith06 locals06₂ mem06 res08 = .unsupported ∧
        ∀ v l' m', res08 = .ok v l' m' → l' = locals08₂ ∧ m' = mem08) := by
    cases res08 with
    | unsupported => exact ⟨fun _ => ⟨rfl, fun _ _ _ h => nomatch h⟩, fun _ => rfl⟩
    | ub => exact ⟨(fun h => by cases h), (fun ⟨h, _⟩ => by cases h)⟩
    | ok _ _ _ => exact ⟨(fun h => by cases h), (fun ⟨h, _⟩ => by cases h)⟩
  have hrel06 : EvalRvalueFloatRel mode policy locals06 (.binaryOp op lhsOp06 rhsOp06) mem06 localDecls06 layouts06
        (rvalueResWith06 locals06₂ mem06 res08) ↔
      (match Option.bind (operandTy localDecls06 layouts06 lhsOp06) ieeeFormatOfTy?,
          Option.bind (operandTy localDecls06 layouts06 rhsOp06) ieeeFormatOfTy? with
       | .some fL, .some fR =>
         match Bool.and
             (match fL, fR with | .binary32, .binary32 => true | .binary64, .binary64 => true | _, _ => false)
             (Bool.and (Nat.beq lhs.sizeBytes fL.byteWidth) (Nat.beq rhs.sizeBytes fL.byteWidth)) with
         | true =>
           match evalFloatBinOp op fL lhs.bits rhs.bits with
           | .some _ =>
             ∃ outSc, EvalFloatBinOpRel mode op fL lhs.bits rhs.bits outSc ∧
               rvalueResWith06 locals06₂ mem06 res08 = .ok (.scalar outSc) locals06₂ mem06
           | .none => rvalueResWith06 locals06₂ mem06 res08 = .unsupported
         | false => rvalueResWith06 locals06₂ mem06 res08 = .unsupported
       | _, _ => rvalueResWith06 locals06₂ mem06 res08 = .unsupported) := by
    have hbind : ∀ (oL oR : Option Ty),
        (match oL, oR with
         | .some lTy, .some rTy =>
           match ieeeFormatOfTy? lTy, ieeeFormatOfTy? rTy with
           | .some fL, .some fR =>
             match Bool.and
                 (match fL, fR with | .binary32, .binary32 => true | .binary64, .binary64 => true | _, _ => false)
                 (Bool.and (Nat.beq lhs.sizeBytes fL.byteWidth) (Nat.beq rhs.sizeBytes fL.byteWidth)) with
             | true =>
               match evalFloatBinOp op fL lhs.bits rhs.bits with
               | .some _ =>
                 ∃ outSc, EvalFloatBinOpRel mode op fL lhs.bits rhs.bits outSc ∧
                   rvalueResWith06 locals06₂ mem06 res08 = .ok (.scalar outSc) locals06₂ mem06
               | .none => rvalueResWith06 locals06₂ mem06 res08 = .unsupported
             | false => rvalueResWith06 locals06₂ mem06 res08 = .unsupported
           | _, _ => rvalueResWith06 locals06₂ mem06 res08 = .unsupported
         | _, _ => rvalueResWith06 locals06₂ mem06 res08 = .unsupported) ↔
        (match Option.bind oL ieeeFormatOfTy?, Option.bind oR ieeeFormatOfTy? with
         | .some fL, .some fR =>
           match Bool.and
               (match fL, fR with | .binary32, .binary32 => true | .binary64, .binary64 => true | _, _ => false)
               (Bool.and (Nat.beq lhs.sizeBytes fL.byteWidth) (Nat.beq rhs.sizeBytes fL.byteWidth)) with
           | true =>
             match evalFloatBinOp op fL lhs.bits rhs.bits with
             | .some _ =>
               ∃ outSc, EvalFloatBinOpRel mode op fL lhs.bits rhs.bits outSc ∧
                 rvalueResWith06 locals06₂ mem06 res08 = .ok (.scalar outSc) locals06₂ mem06
             | .none => rvalueResWith06 locals06₂ mem06 res08 = .unsupported
           | false => rvalueResWith06 locals06₂ mem06 res08 = .unsupported
         | _, _ => rvalueResWith06 locals06₂ mem06 res08 = .unsupported) := by
      intro oL oR
      cases oL with
      | none => exact Iff.rfl
      | some lTy =>
        cases oR with
        | none => dsimp only [Option.bind]; cases ieeeFormatOfTy? lTy <;> exact Iff.rfl
        | some rTy => exact Iff.rfl
    unfold EvalRvalueFloatRel
    dsimp only
    rw [hl06]; dsimp only; rw [hr06]; dsimp only
    cases hop : op with
    | offset => exact absurd hop hNotOff
    | _ =>
      dsimp only
      rw [← hop, hFloat06]
      dsimp only
      exact hbind _ _
  have hrel08 : V2026_08_01.MirSemantics.EvalRvalueFloatRel (mode08 mode) (policy08 policy)
        locals08 (.binaryOp (binOp08 op) lhsOp08 rhsOp08) mem08 localDecls08 layouts08 res08 ↔
      (match Option.bind (V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 lhsOp08) V2026_08_01.MirSemantics.ieeeFormatOfTy?,
          Option.bind (V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 rhsOp08) V2026_08_01.MirSemantics.ieeeFormatOfTy? with
       | .some fL, .some fR =>
         match Bool.and
             (match fL, fR with | .binary32, .binary32 => true | .binary64, .binary64 => true | _, _ => false)
             (Bool.and (Nat.beq lhs.sizeBytes fL.byteWidth) (Nat.beq rhs.sizeBytes fL.byteWidth)) with
         | true =>
           match V2026_08_01.MirSemantics.evalFloatBinOp (binOp08 op) fL lhs.bits rhs.bits with
           | .some _ =>
             ∃ outSc, V2026_08_01.MirSemantics.EvalFloatBinOpRel (mode08 mode) (binOp08 op) fL lhs.bits rhs.bits outSc ∧
               res08 = .ok (.scalar outSc) locals08₂ mem08
           | .none => res08 = .unsupported
         | false => res08 = .unsupported
       | _, _ => res08 = .unsupported) := by
    have hbind : ∀ (oL oR : Option V2026_08_01.MirAst.Ty),
        (match oL, oR with
         | .some lTy, .some rTy =>
           match V2026_08_01.MirSemantics.ieeeFormatOfTy? lTy, V2026_08_01.MirSemantics.ieeeFormatOfTy? rTy with
           | .some fL, .some fR =>
             match Bool.and
                 (match fL, fR with | .binary32, .binary32 => true | .binary64, .binary64 => true | _, _ => false)
                 (Bool.and (Nat.beq lhs.sizeBytes fL.byteWidth) (Nat.beq rhs.sizeBytes fL.byteWidth)) with
             | true =>
               match V2026_08_01.MirSemantics.evalFloatBinOp (binOp08 op) fL lhs.bits rhs.bits with
               | .some _ =>
                 ∃ outSc, V2026_08_01.MirSemantics.EvalFloatBinOpRel (mode08 mode) (binOp08 op) fL lhs.bits rhs.bits outSc ∧
                   res08 = .ok (.scalar outSc) locals08₂ mem08
               | .none => res08 = .unsupported
             | false => res08 = .unsupported
           | _, _ => res08 = .unsupported
         | _, _ => res08 = .unsupported) ↔
        (match Option.bind oL V2026_08_01.MirSemantics.ieeeFormatOfTy?,
            Option.bind oR V2026_08_01.MirSemantics.ieeeFormatOfTy? with
         | .some fL, .some fR =>
           match Bool.and
               (match fL, fR with | .binary32, .binary32 => true | .binary64, .binary64 => true | _, _ => false)
               (Bool.and (Nat.beq lhs.sizeBytes fL.byteWidth) (Nat.beq rhs.sizeBytes fL.byteWidth)) with
           | true =>
             match V2026_08_01.MirSemantics.evalFloatBinOp (binOp08 op) fL lhs.bits rhs.bits with
             | .some _ =>
               ∃ outSc, V2026_08_01.MirSemantics.EvalFloatBinOpRel (mode08 mode) (binOp08 op) fL lhs.bits rhs.bits outSc ∧
                 res08 = .ok (.scalar outSc) locals08₂ mem08
             | .none => res08 = .unsupported
           | false => res08 = .unsupported
         | _, _ => res08 = .unsupported) := by
      intro oL oR
      cases oL with
      | none => exact Iff.rfl
      | some lTy =>
        cases oR with
        | none => dsimp only [Option.bind]; cases V2026_08_01.MirSemantics.ieeeFormatOfTy? lTy <;> exact Iff.rfl
        | some rTy => exact Iff.rfl
    unfold V2026_08_01.MirSemantics.EvalRvalueFloatRel
    dsimp only
    rw [hl08]; dsimp only; rw [hr08]; dsimp only
    have hNotOff08 : binOp08 op ≠ .offset := by
      cases op with
      | offset => exact absurd rfl hNotOff
      | _ => intro h; cases h
    cases hop08 : binOp08 op with
    | offset => exact absurd hop08 hNotOff08
    | _ =>
      dsimp only
      rw [← hop08, hFloat08]
      dsimp only
      exact hbind _ _
  rw [hrel08, hrel06, hFmtL, hFmtR]
  cases Option.bind (operandTy localDecls06 layouts06 lhsOp06) ieeeFormatOfTy? with
  | none => exact hunsup
  | some fL =>
    cases Option.bind (operandTy localDecls06 layouts06 rhsOp06) ieeeFormatOfTy? with
    | none => exact hunsup
    | some fR =>
      dsimp only [Option.map]
      have hdiag : ∀ f : IeeeFormat,
          (match Bool.and (Nat.beq lhs.sizeBytes (fmt08 f).byteWidth) (Nat.beq rhs.sizeBytes (fmt08 f).byteWidth) with
           | true =>
             match V2026_08_01.MirSemantics.evalFloatBinOp (binOp08 op) (fmt08 f) lhs.bits rhs.bits with
             | .some _ =>
               ∃ outSc, V2026_08_01.MirSemantics.EvalFloatBinOpRel (mode08 mode) (binOp08 op) (fmt08 f) lhs.bits rhs.bits outSc ∧
                 res08 = .ok (.scalar outSc) locals08₂ mem08
             | .none => res08 = .unsupported
           | false => res08 = .unsupported) ↔
          ((match Bool.and (Nat.beq lhs.sizeBytes f.byteWidth) (Nat.beq rhs.sizeBytes f.byteWidth) with
            | true =>
              match evalFloatBinOp op f lhs.bits rhs.bits with
              | .some _ =>
                ∃ outSc, EvalFloatBinOpRel mode op f lhs.bits rhs.bits outSc ∧
                  rvalueResWith06 locals06₂ mem06 res08 = .ok (.scalar outSc) locals06₂ mem06
              | .none => rvalueResWith06 locals06₂ mem06 res08 = .unsupported
            | false => rvalueResWith06 locals06₂ mem06 res08 = .unsupported) ∧
            ∀ v l' m', res08 = .ok v l' m' → l' = locals08₂ ∧ m' = mem08) := by
        intro f
        rw [(fmt08_params f).2.2.2.2.1, evalFloatBinOp_parity]
        cases Bool.and (Nat.beq lhs.sizeBytes f.byteWidth) (Nat.beq rhs.sizeBytes f.byteWidth) with
        | false => exact hunsup
        | true =>
          dsimp only
          cases evalFloatBinOp op f lhs.bits rhs.bits with
          | none => exact hunsup
          | some _ =>
            dsimp only [Option.map]
            constructor
            · rintro ⟨outSc08, hRel08, hRes⟩
              have hscEq : scalarInt08 (scalarInt06 outSc08) = outSc08 := by cases outSc08; rfl
              rw [← hscEq] at hRel08
              refine ⟨⟨scalarInt06 outSc08, (EvalFloatBinOpRel_parity mode op f lhs.bits rhs.bits _).mp hRel08, ?_⟩, ?_⟩
              · rw [hRes]; rfl
              · intro _ _ _ h
                rw [hRes] at h
                injection h with _ hl hm
                exact ⟨hl.symm, hm.symm⟩
            · rintro ⟨⟨outSc06, hRel06, hRes06⟩, hPost⟩
              cases res08 with
              | ub => cases hRes06
              | unsupported => cases hRes06
              | ok v l' m' =>
                unfold rvalueResWith06 at hRes06
                injection hRes06 with hv _ _
                obtain ⟨hl', hm'⟩ := hPost v l' m' rfl
                have hvEq : v = .scalar (scalarInt08 outSc06) := by
                  cases v with
                  | scalar sc08 =>
                    unfold value06 scalarInt06 at hv
                    injection hv with hsc
                    cases sc08; cases outSc06
                    injection hsc with h1 h2
                    subst h1; subst h2; rfl
                  | unit => cases hv
                  | ptr _ _ => cases hv
                  | aggregate _ _ => cases hv
                exact ⟨scalarInt08 outSc06,
                  (EvalFloatBinOpRel_parity mode op f lhs.bits rhs.bits outSc06).mpr hRel06,
                  by rw [hvEq, hl', hm']⟩
      cases fL <;> cases fR
      · dsimp only [fmt08, Bool.true_and]; exact hdiag .binary32
      · dsimp only [fmt08, Bool.false_and]; exact hunsup
      · dsimp only [fmt08, Bool.false_and]; exact hunsup
      · dsimp only [fmt08, Bool.true_and]; exact hdiag .binary64

/-- **`EvalRvalueFloatRel` cross-dialect parity on `.cast .floatToFloat`** (BOTH modes, ANY
policy, covering both NaN-input non-deterministic choices and non-NaN rounding, as well as
`f16`/`f128` and width-mismatch `.unsupported` fallback). -/
theorem EvalRvalueFloatRel_floatToFloat_parity
    (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (locals06 locals06' : List LocalSlot) (op06 : Operand) (targetTy06 : Ty)
    (mem06 : Memory) (localDecls06 : List LocalDecl) (layouts06 : LayoutTable)
    (locals08 locals08' : List V2026_08_01.MirSemantics.LocalSlot)
    (op08 : V2026_08_01.MirAst.Operand) (targetTy08 : V2026_08_01.MirAst.Ty)
    (mem08 : V2026_08_01.MirSemantics.Memory)
    (localDecls08 : List V2026_08_01.MirAst.LocalDecl) (layouts08 : V2026_08_01.Layout.LayoutTable)
    (sc : ScalarInt) (res08 : V2026_08_01.MirSemantics.RvalueEvalResult)
    (hEval06 : evalOperand locals06 op06 mem06.borrows mem06.globals layouts06 mem06.callerLocals localDecls06 mem06.callStack =
      .ok (.scalar sc) locals06')
    (hEval08 : V2026_08_01.MirSemantics.evalOperand locals08 op08 mem08.borrows mem08.globals layouts08 mem08.callerLocals localDecls08 mem08.callStack =
      .ok (.scalar (scalarInt08 sc)) locals08')
    (hFmtSrc : Option.bind (V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 op08) V2026_08_01.MirSemantics.ieeeFormatOfTy? =
      Option.map fmt08 (Option.bind (operandTy localDecls06 layouts06 op06) ieeeFormatOfTy?))
    (hFmtDst : V2026_08_01.MirSemantics.ieeeFormatOfTy? targetTy08 =
      Option.map fmt08 (ieeeFormatOfTy? targetTy06)) :
    V2026_08_01.MirSemantics.EvalRvalueFloatRel (mode08 mode) (policy08 policy)
        locals08 (.cast .floatToFloat op08 targetTy08) mem08 localDecls08 layouts08 res08 ↔
      (EvalRvalueFloatRel mode policy locals06 (.cast .floatToFloat op06 targetTy06) mem06 localDecls06 layouts06
          (rvalueResWith06 locals06' mem06 res08) ∧
        ∀ v l' m', res08 = .ok v l' m' → l' = locals08' ∧ m' = mem08) := by
  have hunsup : res08 = .unsupported ↔
      (rvalueResWith06 locals06' mem06 res08 = .unsupported ∧
        ∀ v l' m', res08 = .ok v l' m' → l' = locals08' ∧ m' = mem08) := by
    cases res08 with
    | unsupported => exact ⟨fun _ => ⟨rfl, fun _ _ _ h => nomatch h⟩, fun _ => rfl⟩
    | ub => exact ⟨(fun h => by cases h), (fun ⟨h, _⟩ => by cases h)⟩
    | ok _ _ _ => exact ⟨(fun h => by cases h), (fun ⟨h, _⟩ => by cases h)⟩
  have h06 : EvalRvalueFloatRel mode policy locals06 (.cast .floatToFloat op06 targetTy06) mem06 localDecls06 layouts06
        (rvalueResWith06 locals06' mem06 res08) ↔
      (match Option.bind (operandTy localDecls06 layouts06 op06) ieeeFormatOfTy?, ieeeFormatOfTy? targetTy06 with
       | .some src, .some dst =>
         match Nat.beq sc.sizeBytes src.byteWidth with
         | true =>
           if isNaNBits src sc.bits = true then
             ∃ cand, cand ∈ nanChoices dst [(src, sc.bits % 2 ^ src.width)] mode ∧
               rvalueResWith06 locals06' mem06 res08 = .ok (.scalar ⟨cand, dst.byteWidth⟩) locals06' mem06
           else
             rvalueResWith06 locals06' mem06 res08 =
               .ok (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩) locals06' mem06
         | false => rvalueResWith06 locals06' mem06 res08 = .unsupported
       | _, _ => rvalueResWith06 locals06' mem06 res08 = .unsupported) := by
    unfold EvalRvalueFloatRel; dsimp only; rw [hEval06]; dsimp only
    cases operandTy localDecls06 layouts06 op06 <;> rfl
  have h08 : V2026_08_01.MirSemantics.EvalRvalueFloatRel (mode08 mode) (policy08 policy)
        locals08 (.cast .floatToFloat op08 targetTy08) mem08 localDecls08 layouts08 res08 ↔
      (match Option.bind (V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 op08) V2026_08_01.MirSemantics.ieeeFormatOfTy?,
          V2026_08_01.MirSemantics.ieeeFormatOfTy? targetTy08 with
       | .some src, .some dst =>
         match Nat.beq sc.sizeBytes src.byteWidth with
         | true =>
           if V2026_08_01.MirSemantics.isNaNBits src sc.bits = true then
             ∃ cand, cand ∈ V2026_08_01.MirSemantics.nanChoices dst [(src, sc.bits % 2 ^ src.width)] (mode08 mode) ∧
               res08 = .ok (.scalar ⟨cand, dst.byteWidth⟩) locals08' mem08
           else
             res08 =
               .ok (.scalar ⟨V2026_08_01.MirSemantics.evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩) locals08' mem08
         | false => res08 = .unsupported
       | _, _ => res08 = .unsupported) := by
    unfold V2026_08_01.MirSemantics.EvalRvalueFloatRel; dsimp only; rw [hEval08]; dsimp only
    cases V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 op08 <;> rfl
  rw [h08, h06, hFmtSrc, hFmtDst]
  cases Option.bind (operandTy localDecls06 layouts06 op06) ieeeFormatOfTy? with
  | none => exact hunsup
  | some src =>
    cases ieeeFormatOfTy? targetTy06 with
    | none => exact hunsup
    | some dst =>
      dsimp only [Option.map]
      rw [(fmt08_params src).2.2.2.2.1, (fmt08_params src).1, (fmt08_params dst).2.2.2.2.1,
        (isNaNBits_parity src sc.bits).1, evalFloatToFloatRoundTiesToEven_parity]
      cases Nat.beq sc.sizeBytes src.byteWidth with
      | false => exact hunsup
      | true =>
        dsimp only
        have hch : V2026_08_01.MirSemantics.nanChoices (fmt08 dst) [(fmt08 src, sc.bits % 2 ^ src.width)] (mode08 mode) =
            nanChoices dst [(src, sc.bits % 2 ^ src.width)] mode :=
          nanChoices_parity dst [(src, sc.bits % 2 ^ src.width)] mode
        have hscOk : ∀ bits : Nat,
            res08 = .ok (.scalar ⟨bits, dst.byteWidth⟩) locals08' mem08 ↔
              (rvalueResWith06 locals06' mem06 res08 = .ok (.scalar ⟨bits, dst.byteWidth⟩) locals06' mem06 ∧
                ∀ v l' m', res08 = .ok v l' m' → l' = locals08' ∧ m' = mem08) := by
          intro bits
          constructor
          · intro hr
            rw [hr]
            exact ⟨rfl, fun _ _ _ h => by injection h with _ hl hm; exact ⟨hl.symm, hm.symm⟩⟩
          · rintro ⟨hr06, hPost⟩
            exact rvalueResWith06_injective_at locals06' mem06 locals08' mem08 res08
              (.ok (.scalar ⟨bits, dst.byteWidth⟩) locals08' mem08) hr06 hPost
              (fun _ _ _ h => by injection h with _ hl hm; exact ⟨hl.symm, hm.symm⟩)
        cases isNaNBits src sc.bits with
        | true =>
          rw [if_pos' rfl, if_pos' rfl, hch]
          constructor
          · rintro ⟨cand, hc, hr⟩
            obtain ⟨hr06, hPost⟩ := (hscOk cand).mp hr
            exact ⟨⟨cand, hc, hr06⟩, hPost⟩
          · rintro ⟨⟨cand, hc, hr06⟩, hPost⟩
            exact ⟨cand, hc, (hscOk cand).mpr ⟨hr06, hPost⟩⟩
        | false =>
          rw [if_neg' Bool.false_ne_true, if_neg' Bool.false_ne_true]
          exact hscOk _

/-- **Constant-operand specialization**: `EvalRvalueFloatRel` cross-dialect parity on float
`.unaryOp .neg` over any typed scalar constant (under `tyFloat08`). -/
theorem EvalRvalueFloatRel_unaryNeg_float_const_parity
    (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (ty : Ty) (hFloat : isFloatTy ty = true) (bits sizeBytes : Nat)
    (locals06 : List LocalSlot) (mem06 : Memory) (localDecls06 : List LocalDecl) (layouts06 : LayoutTable)
    (locals08 : List V2026_08_01.MirSemantics.LocalSlot) (mem08 : V2026_08_01.MirSemantics.Memory)
    (localDecls08 : List V2026_08_01.MirAst.LocalDecl) (layouts08 : V2026_08_01.Layout.LayoutTable)
    (res08 : V2026_08_01.MirSemantics.RvalueEvalResult) :
    V2026_08_01.MirSemantics.EvalRvalueFloatRel (mode08 mode) (policy08 policy)
        locals08 (.unaryOp .neg (mkFloatConstOp08 (tyFloat08 ty) bits sizeBytes)) mem08 localDecls08 layouts08 res08 ↔
      (EvalRvalueFloatRel mode policy
          locals06 (.unaryOp .neg (mkFloatConstOp ty bits sizeBytes)) mem06 localDecls06 layouts06
          (rvalueResWith06 locals06 mem06 res08) ∧
        ∀ v l' m', res08 = .ok v l' m' → l' = locals08 ∧ m' = mem08) :=
  EvalRvalueFloatRel_unaryNeg_float_parity mode policy
    locals06 locals06 (mkFloatConstOp ty bits sizeBytes) mem06 localDecls06 layouts06
    locals08 locals08 (mkFloatConstOp08 (tyFloat08 ty) bits sizeBytes) mem08 localDecls08 layouts08
    ⟨bits, sizeBytes⟩ res08 rfl rfl hFloat
    (by show V2026_08_01.MirSemantics.isFloatTy (tyFloat08 ty) = true; rw [isFloatTy_parity]; exact hFloat)
    (ieeeFormatOfTy?_parity ty)

/-- **Constant-operand specialization**: `EvalRvalueFloatRel` cross-dialect parity on float
`.binaryOp` over any pair of typed scalar constants (at least one float, under `tyFloat08`). -/
theorem EvalRvalueFloatRel_binaryOp_float_const_parity
    (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (op : BinOp) (hNotOff : op ≠ .offset)
    (lTy rTy : Ty) (hFloat : Bool.or (isFloatTy lTy) (isFloatTy rTy) = true)
    (lBits lSz rBits rSz : Nat)
    (locals06 : List LocalSlot) (mem06 : Memory) (localDecls06 : List LocalDecl) (layouts06 : LayoutTable)
    (locals08 : List V2026_08_01.MirSemantics.LocalSlot) (mem08 : V2026_08_01.MirSemantics.Memory)
    (localDecls08 : List V2026_08_01.MirAst.LocalDecl) (layouts08 : V2026_08_01.Layout.LayoutTable)
    (res08 : V2026_08_01.MirSemantics.RvalueEvalResult) :
    V2026_08_01.MirSemantics.EvalRvalueFloatRel (mode08 mode) (policy08 policy)
        locals08 (.binaryOp (binOp08 op) (mkFloatConstOp08 (tyFloat08 lTy) lBits lSz)
          (mkFloatConstOp08 (tyFloat08 rTy) rBits rSz)) mem08 localDecls08 layouts08 res08 ↔
      (EvalRvalueFloatRel mode policy
          locals06 (.binaryOp op (mkFloatConstOp lTy lBits lSz) (mkFloatConstOp rTy rBits rSz))
          mem06 localDecls06 layouts06 (rvalueResWith06 locals06 mem06 res08) ∧
        ∀ v l' m', res08 = .ok v l' m' → l' = locals08 ∧ m' = mem08) :=
  EvalRvalueFloatRel_binaryOp_float_parity mode policy op hNotOff
    locals06 locals06 locals06 (mkFloatConstOp lTy lBits lSz) (mkFloatConstOp rTy rBits rSz)
    mem06 localDecls06 layouts06
    locals08 locals08 locals08 (mkFloatConstOp08 (tyFloat08 lTy) lBits lSz)
    (mkFloatConstOp08 (tyFloat08 rTy) rBits rSz) mem08 localDecls08 layouts08
    ⟨lBits, lSz⟩ ⟨rBits, rSz⟩ res08 rfl rfl rfl rfl hFloat
    (by show Bool.or (V2026_08_01.MirSemantics.isFloatTy (tyFloat08 lTy))
          (V2026_08_01.MirSemantics.isFloatTy (tyFloat08 rTy)) = true
        rw [isFloatTy_parity, isFloatTy_parity]; exact hFloat)
    (ieeeFormatOfTy?_parity lTy) (ieeeFormatOfTy?_parity rTy)

/-- **Constant-operand specialization**: `EvalRvalueFloatRel` cross-dialect parity on
`.cast .floatToFloat` over any typed scalar constant (under `tyFloat08`). -/
theorem EvalRvalueFloatRel_floatToFloat_const_parity
    (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (srcTy targetTy : Ty) (bits sizeBytes : Nat)
    (locals06 : List LocalSlot) (mem06 : Memory) (localDecls06 : List LocalDecl) (layouts06 : LayoutTable)
    (locals08 : List V2026_08_01.MirSemantics.LocalSlot) (mem08 : V2026_08_01.MirSemantics.Memory)
    (localDecls08 : List V2026_08_01.MirAst.LocalDecl) (layouts08 : V2026_08_01.Layout.LayoutTable)
    (res08 : V2026_08_01.MirSemantics.RvalueEvalResult) :
    V2026_08_01.MirSemantics.EvalRvalueFloatRel (mode08 mode) (policy08 policy)
        locals08 (.cast .floatToFloat (mkFloatConstOp08 (tyFloat08 srcTy) bits sizeBytes) (tyFloat08 targetTy))
        mem08 localDecls08 layouts08 res08 ↔
      (EvalRvalueFloatRel mode policy
          locals06 (.cast .floatToFloat (mkFloatConstOp srcTy bits sizeBytes) targetTy)
          mem06 localDecls06 layouts06 (rvalueResWith06 locals06 mem06 res08) ∧
        ∀ v l' m', res08 = .ok v l' m' → l' = locals08 ∧ m' = mem08) :=
  EvalRvalueFloatRel_floatToFloat_parity mode policy
    locals06 locals06 (mkFloatConstOp srcTy bits sizeBytes) targetTy mem06 localDecls06 layouts06
    locals08 locals08 (mkFloatConstOp08 (tyFloat08 srcTy) bits sizeBytes) (tyFloat08 targetTy)
    mem08 localDecls08 layouts08 ⟨bits, sizeBytes⟩ res08 rfl rfl
    (ieeeFormatOfTy?_parity srcTy) (ieeeFormatOfTy?_parity targetTy)

/-- **Local-variable specialization (`copy _idx`)**: `EvalRvalueFloatRel` cross-dialect parity
on float `.unaryOp .neg` reading scalar local `_idx`. -/
theorem EvalRvalueFloatRel_unaryNeg_float_local_copy_parity
    (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy) (idx : Nat) (sc : ScalarInt)
    (locals06 : List LocalSlot) (mem06 : Memory) (localDecls06 : List LocalDecl) (layouts06 : LayoutTable)
    (locals08 : List V2026_08_01.MirSemantics.LocalSlot) (mem08 : V2026_08_01.MirSemantics.Memory)
    (localDecls08 : List V2026_08_01.MirAst.LocalDecl) (layouts08 : V2026_08_01.Layout.LayoutTable)
    (decl06 : LocalDecl) (decl08 : V2026_08_01.MirAst.LocalDecl)
    (res08 : V2026_08_01.MirSemantics.RvalueEvalResult)
    (hLoc06 : get? locals06 idx = .some (.init (.scalar sc)))
    (hLoc08 : get? locals08 idx = .some (.init (.scalar (scalarInt08 sc))))
    (hDecl06 : get? localDecls06 idx = .some decl06)
    (hDecl08 : get? localDecls08 idx = .some decl08)
    (hFloat06 : isFloatTy decl06.ty = true)
    (hFloat08 : V2026_08_01.MirSemantics.isFloatTy decl08.ty = true)
    (hFmt : V2026_08_01.MirSemantics.ieeeFormatOfTy? decl08.ty = Option.map fmt08 (ieeeFormatOfTy? decl06.ty)) :
    V2026_08_01.MirSemantics.EvalRvalueFloatRel (mode08 mode) (policy08 policy)
        locals08 (.unaryOp .neg (.copy ⟨idx, .nil⟩)) mem08 localDecls08 layouts08 res08 ↔
      (EvalRvalueFloatRel mode policy
          locals06 (.unaryOp .neg (.copy ⟨idx, .nil⟩)) mem06 localDecls06 layouts06
          (rvalueResWith06 locals06 mem06 res08) ∧
        ∀ v l' m', res08 = .ok v l' m' → l' = locals08 ∧ m' = mem08) := by
  have hEval06 : evalOperand locals06 (.copy ⟨idx, .nil⟩) mem06.borrows mem06.globals layouts06 mem06.callerLocals localDecls06 mem06.callStack =
      .ok (.scalar sc) locals06 := by
    unfold evalOperand; dsimp only; rw [hLoc06]; rfl
  have hEval08 : V2026_08_01.MirSemantics.evalOperand locals08 (.copy ⟨idx, .nil⟩) mem08.borrows mem08.globals layouts08 mem08.callerLocals localDecls08 mem08.callStack =
      .ok (.scalar (scalarInt08 sc)) locals08 := by
    unfold V2026_08_01.MirSemantics.evalOperand; dsimp only; rw [hLoc08]; rfl
  have hTy06 : operandTy localDecls06 layouts06 (.copy ⟨idx, .nil⟩) = .some decl06.ty := by
    unfold operandTy placeTy; dsimp only; rw [hDecl06]
  have hTy08 : V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 (.copy ⟨idx, .nil⟩) = .some decl08.ty := by
    unfold V2026_08_01.MirSemantics.operandTy V2026_08_01.MirSemantics.placeTy; dsimp only; rw [hDecl08]
  exact EvalRvalueFloatRel_unaryNeg_float_parity mode policy
    locals06 locals06 (.copy ⟨idx, .nil⟩) mem06 localDecls06 layouts06
    locals08 locals08 (.copy ⟨idx, .nil⟩) mem08 localDecls08 layouts08
    sc res08 hEval06 hEval08
    (by rw [hTy06]; exact hFloat06)
    (by rw [hTy08]; exact hFloat08)
    (by rw [hTy06, hTy08]; exact hFmt)

/-- **Local-variable specialization (`copy _lhs`, `copy _rhs`)**: `EvalRvalueFloatRel`
cross-dialect parity on float `.binaryOp` reading two scalar locals. -/
theorem EvalRvalueFloatRel_binaryOp_float_local_copy_parity
    (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (op : BinOp) (hNotOff : op ≠ .offset) (lhsIdx rhsIdx : Nat) (lhs rhs : ScalarInt)
    (locals06 : List LocalSlot) (mem06 : Memory) (localDecls06 : List LocalDecl) (layouts06 : LayoutTable)
    (locals08 : List V2026_08_01.MirSemantics.LocalSlot) (mem08 : V2026_08_01.MirSemantics.Memory)
    (localDecls08 : List V2026_08_01.MirAst.LocalDecl) (layouts08 : V2026_08_01.Layout.LayoutTable)
    (lDecl06 rDecl06 : LocalDecl) (lDecl08 rDecl08 : V2026_08_01.MirAst.LocalDecl)
    (res08 : V2026_08_01.MirSemantics.RvalueEvalResult)
    (hL06 : get? locals06 lhsIdx = .some (.init (.scalar lhs)))
    (hR06 : get? locals06 rhsIdx = .some (.init (.scalar rhs)))
    (hL08 : get? locals08 lhsIdx = .some (.init (.scalar (scalarInt08 lhs))))
    (hR08 : get? locals08 rhsIdx = .some (.init (.scalar (scalarInt08 rhs))))
    (hLD06 : get? localDecls06 lhsIdx = .some lDecl06)
    (hRD06 : get? localDecls06 rhsIdx = .some rDecl06)
    (hLD08 : get? localDecls08 lhsIdx = .some lDecl08)
    (hRD08 : get? localDecls08 rhsIdx = .some rDecl08)
    (hFloat06 : Bool.or (isFloatTy lDecl06.ty) (isFloatTy rDecl06.ty) = true)
    (hFloat08 : Bool.or (V2026_08_01.MirSemantics.isFloatTy lDecl08.ty)
        (V2026_08_01.MirSemantics.isFloatTy rDecl08.ty) = true)
    (hFmtL : V2026_08_01.MirSemantics.ieeeFormatOfTy? lDecl08.ty = Option.map fmt08 (ieeeFormatOfTy? lDecl06.ty))
    (hFmtR : V2026_08_01.MirSemantics.ieeeFormatOfTy? rDecl08.ty = Option.map fmt08 (ieeeFormatOfTy? rDecl06.ty)) :
    V2026_08_01.MirSemantics.EvalRvalueFloatRel (mode08 mode) (policy08 policy)
        locals08 (.binaryOp (binOp08 op) (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩))
        mem08 localDecls08 layouts08 res08 ↔
      (EvalRvalueFloatRel mode policy
          locals06 (.binaryOp op (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩))
          mem06 localDecls06 layouts06 (rvalueResWith06 locals06 mem06 res08) ∧
        ∀ v l' m', res08 = .ok v l' m' → l' = locals08 ∧ m' = mem08) := by
  have hl06 : evalOperand locals06 (.copy ⟨lhsIdx, .nil⟩) mem06.borrows mem06.globals layouts06 mem06.callerLocals localDecls06 mem06.callStack =
      .ok (.scalar lhs) locals06 := by unfold evalOperand; dsimp only; rw [hL06]; rfl
  have hr06 : evalOperand locals06 (.copy ⟨rhsIdx, .nil⟩) mem06.borrows mem06.globals layouts06 mem06.callerLocals localDecls06 mem06.callStack =
      .ok (.scalar rhs) locals06 := by unfold evalOperand; dsimp only; rw [hR06]; rfl
  have hl08 : V2026_08_01.MirSemantics.evalOperand locals08 (.copy ⟨lhsIdx, .nil⟩) mem08.borrows mem08.globals layouts08 mem08.callerLocals localDecls08 mem08.callStack =
      .ok (.scalar (scalarInt08 lhs)) locals08 := by unfold V2026_08_01.MirSemantics.evalOperand; dsimp only; rw [hL08]; rfl
  have hr08 : V2026_08_01.MirSemantics.evalOperand locals08 (.copy ⟨rhsIdx, .nil⟩) mem08.borrows mem08.globals layouts08 mem08.callerLocals localDecls08 mem08.callStack =
      .ok (.scalar (scalarInt08 rhs)) locals08 := by unfold V2026_08_01.MirSemantics.evalOperand; dsimp only; rw [hR08]; rfl
  have hLT06 : operandTy localDecls06 layouts06 (.copy ⟨lhsIdx, .nil⟩) = .some lDecl06.ty := by
    unfold operandTy placeTy; dsimp only; rw [hLD06]
  have hRT06 : operandTy localDecls06 layouts06 (.copy ⟨rhsIdx, .nil⟩) = .some rDecl06.ty := by
    unfold operandTy placeTy; dsimp only; rw [hRD06]
  have hLT08 : V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 (.copy ⟨lhsIdx, .nil⟩) = .some lDecl08.ty := by
    unfold V2026_08_01.MirSemantics.operandTy V2026_08_01.MirSemantics.placeTy; dsimp only; rw [hLD08]
  have hRT08 : V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 (.copy ⟨rhsIdx, .nil⟩) = .some rDecl08.ty := by
    unfold V2026_08_01.MirSemantics.operandTy V2026_08_01.MirSemantics.placeTy; dsimp only; rw [hRD08]
  exact EvalRvalueFloatRel_binaryOp_float_parity mode policy op hNotOff
    locals06 locals06 locals06 (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)
    mem06 localDecls06 layouts06
    locals08 locals08 locals08 (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)
    mem08 localDecls08 layouts08 lhs rhs res08 hl06 hr06 hl08 hr08
    (by rw [hLT06, hRT06]; exact hFloat06)
    (by rw [hLT08, hRT08]; exact hFloat08)
    (by rw [hLT06, hLT08]; exact hFmtL)
    (by rw [hRT06, hRT08]; exact hFmtR)

/-- **Local-variable specialization (`copy _lhs`, `move _rhs`)**: `EvalRvalueFloatRel`
cross-dialect parity on float `.binaryOp` when moving out of `_rhs`, threading the updated
`locals06'` / `locals08'` post-states across both dialects. -/
theorem EvalRvalueFloatRel_binaryOp_float_local_move_parity
    (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (op : BinOp) (hNotOff : op ≠ .offset) (lhsIdx rhsIdx : Nat) (lhs rhs : ScalarInt)
    (locals06 locals06' : List LocalSlot) (mem06 : Memory) (localDecls06 : List LocalDecl) (layouts06 : LayoutTable)
    (locals08 locals08' : List V2026_08_01.MirSemantics.LocalSlot) (mem08 : V2026_08_01.MirSemantics.Memory)
    (localDecls08 : List V2026_08_01.MirAst.LocalDecl) (layouts08 : V2026_08_01.Layout.LayoutTable)
    (lDecl06 rDecl06 : LocalDecl) (lDecl08 rDecl08 : V2026_08_01.MirAst.LocalDecl)
    (res08 : V2026_08_01.MirSemantics.RvalueEvalResult)
    (hL06 : get? locals06 lhsIdx = .some (.init (.scalar lhs)))
    (hR06 : get? locals06 rhsIdx = .some (.init (.scalar rhs)))
    (hSet06 : set? locals06 rhsIdx .uninit = .some locals06')
    (hL08 : get? locals08 lhsIdx = .some (.init (.scalar (scalarInt08 lhs))))
    (hR08 : get? locals08 rhsIdx = .some (.init (.scalar (scalarInt08 rhs))))
    (hSet08 : set? locals08 rhsIdx .uninit = .some locals08')
    (hLD06 : get? localDecls06 lhsIdx = .some lDecl06)
    (hRD06 : get? localDecls06 rhsIdx = .some rDecl06)
    (hLD08 : get? localDecls08 lhsIdx = .some lDecl08)
    (hRD08 : get? localDecls08 rhsIdx = .some rDecl08)
    (hFloat06 : Bool.or (isFloatTy lDecl06.ty) (isFloatTy rDecl06.ty) = true)
    (hFloat08 : Bool.or (V2026_08_01.MirSemantics.isFloatTy lDecl08.ty)
        (V2026_08_01.MirSemantics.isFloatTy rDecl08.ty) = true)
    (hFmtL : V2026_08_01.MirSemantics.ieeeFormatOfTy? lDecl08.ty = Option.map fmt08 (ieeeFormatOfTy? lDecl06.ty))
    (hFmtR : V2026_08_01.MirSemantics.ieeeFormatOfTy? rDecl08.ty = Option.map fmt08 (ieeeFormatOfTy? rDecl06.ty)) :
    V2026_08_01.MirSemantics.EvalRvalueFloatRel (mode08 mode) (policy08 policy)
        locals08 (.binaryOp (binOp08 op) (.copy ⟨lhsIdx, .nil⟩) (.move ⟨rhsIdx, .nil⟩))
        mem08 localDecls08 layouts08 res08 ↔
      (EvalRvalueFloatRel mode policy
          locals06 (.binaryOp op (.copy ⟨lhsIdx, .nil⟩) (.move ⟨rhsIdx, .nil⟩))
          mem06 localDecls06 layouts06 (rvalueResWith06 locals06' mem06 res08) ∧
        ∀ v l' m', res08 = .ok v l' m' → l' = locals08' ∧ m' = mem08) := by
  have hl06 : evalOperand locals06 (.copy ⟨lhsIdx, .nil⟩) mem06.borrows mem06.globals layouts06 mem06.callerLocals localDecls06 mem06.callStack =
      .ok (.scalar lhs) locals06 := by unfold evalOperand; dsimp only; rw [hL06]; rfl
  have hr06 : evalOperand locals06 (.move ⟨rhsIdx, .nil⟩) mem06.borrows mem06.globals layouts06 mem06.callerLocals localDecls06 mem06.callStack =
      .ok (.scalar rhs) locals06' := by unfold evalOperand; dsimp only; rw [hR06]; dsimp only [readProjectedValue, valueContainsUninit]; rw [hSet06]
  have hl08 : V2026_08_01.MirSemantics.evalOperand locals08 (.copy ⟨lhsIdx, .nil⟩) mem08.borrows mem08.globals layouts08 mem08.callerLocals localDecls08 mem08.callStack =
      .ok (.scalar (scalarInt08 lhs)) locals08 := by unfold V2026_08_01.MirSemantics.evalOperand; dsimp only; rw [hL08]; rfl
  have hr08 : V2026_08_01.MirSemantics.evalOperand locals08 (.move ⟨rhsIdx, .nil⟩) mem08.borrows mem08.globals layouts08 mem08.callerLocals localDecls08 mem08.callStack =
      .ok (.scalar (scalarInt08 rhs)) locals08' := by unfold V2026_08_01.MirSemantics.evalOperand; dsimp only; rw [hR08]; dsimp only [V2026_08_01.MirSemantics.readProjectedValue]; rw [hSet08]
  have hLT06 : operandTy localDecls06 layouts06 (.copy ⟨lhsIdx, .nil⟩) = .some lDecl06.ty := by
    unfold operandTy placeTy; dsimp only; rw [hLD06]
  have hRT06 : operandTy localDecls06 layouts06 (.move ⟨rhsIdx, .nil⟩) = .some rDecl06.ty := by
    unfold operandTy placeTy; dsimp only; rw [hRD06]
  have hLT08 : V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 (.copy ⟨lhsIdx, .nil⟩) = .some lDecl08.ty := by
    unfold V2026_08_01.MirSemantics.operandTy V2026_08_01.MirSemantics.placeTy; dsimp only; rw [hLD08]
  have hRT08 : V2026_08_01.MirSemantics.operandTy localDecls08 layouts08 (.move ⟨rhsIdx, .nil⟩) = .some rDecl08.ty := by
    unfold V2026_08_01.MirSemantics.operandTy V2026_08_01.MirSemantics.placeTy; dsimp only; rw [hRD08]
  exact EvalRvalueFloatRel_binaryOp_float_parity mode policy op hNotOff
    locals06 locals06 locals06' (.copy ⟨lhsIdx, .nil⟩) (.move ⟨rhsIdx, .nil⟩)
    mem06 localDecls06 layouts06
    locals08 locals08 locals08' (.copy ⟨lhsIdx, .nil⟩) (.move ⟨rhsIdx, .nil⟩)
    mem08 localDecls08 layouts08 lhs rhs res08 hl06 hr06 hl08 hr08
    (by rw [hLT06, hRT06]; exact hFloat06)
    (by rw [hLT08, hRT08]; exact hFloat08)
    (by rw [hLT06, hLT08]; exact hFmtL)
    (by rw [hRT06, hRT08]; exact hFmtR)

end DialectParity

/-! ## §7. IEEE 754-2008 special-case table, documented signed-zero rule, & no-NaN-input `nanChoices`

Universally quantified (over both formats and all sign combinations) closed
forms for the special cases of `evalFloatArithBase`: NaN infectiousness, signed
zero sums (`(-0) + (-0) = -0`, `(+0) + (-0) = +0`, `(-0) - (+0) = -0`,
`(-0) - (-0) = +0`), exact cancellation (`x + (-x) = +0`, `x - x = +0`), invalid
operations (`0 * ∞`, `∞ - ∞`, `0 / 0`, `∞ / ∞`, `x % 0`, `∞ % y`), division of a
finite nonzero value by a signed zero (`±∞` with XOR sign, never `.ub`),
`finite % ±∞ = finite`, and `±0 % finite = ±0` with the dividend's sign.
-/

/-- **NaN operands are infectious** for every arithmetic `BinOp`: the
deterministic base evaluator returns exactly `preferredNaNBits f`. -/
theorem evalFloatArithBase_of_nan (f : IeeeFormat) (a b : Nat)
    (h : isNaNBits f a = true ∨ isNaNBits f b = true) :
    evalFloatArithBase .add f a b = .some (preferredNaNBits f) ∧
    evalFloatArithBase .sub f a b = .some (preferredNaNBits f) ∧
    evalFloatArithBase .mul f a b = .some (preferredNaNBits f) ∧
    evalFloatArithBase .div f a b = .some (preferredNaNBits f) ∧
    evalFloatArithBase .rem f a b = .some (preferredNaNBits f) := by
  unfold evalFloatArithBase
  dsimp only
  rw [decodeBits_mod, decodeBits_mod]
  rcases h with h | h
  · obtain ⟨neg, q, p, hd⟩ := (isNaNBits_eq_true_iff f a).mp h
    rw [hd]
    cases decodeBits f b <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨neg, q, p, hd⟩ := (isNaNBits_eq_true_iff f b).mp h
    rw [hd]
    cases decodeBits f a <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Signed-zero sums** (IEEE 754-2008 §6.3 under `roundTiesToEven`):
`(±0) + (±0)` is `-0` iff both operands are `-0`, and `(±0) - (±0)` is `-0` iff
the minuend is `-0` and the subtrahend is `+0`. In particular
`(-0) + (-0) = -0`, `(+0) + (-0) = +0`, `(-0) - (+0) = -0`, `(-0) - (-0) = +0`. -/
theorem evalFloatArithBase_signed_zero_sums (f : IeeeFormat) (s t : Bool) :
    evalFloatArithBase .add f (zeroBits f s) (zeroBits f t) =
      .some (zeroBits f (Bool.and s t)) ∧
    evalFloatArithBase .sub f (zeroBits f s) (zeroBits f t) =
      .some (zeroBits f (Bool.and s (Bool.not t))) := by
  cases f <;> cases s <;> cases t <;> exact ⟨rfl, rfl⟩

/-- **Exact cancellation yields `+0`** (IEEE 754-2008 §6.3 under `roundTiesToEven`):
for EVERY finite nonzero `x` (either sign, normal or subnormal),
`x + (-x) = +0.0` and `x - x = +0.0`. -/
theorem evalFloatArithBase_cancel_finite (f : IeeeFormat) (a : Nat) (neg : Bool) (n d : Nat)
    (ha : decodeBits f a = .finite neg n d) :
    evalFloatArithBase .add f a (evalFloatNeg f a) = .some (zeroBits f false) ∧
    evalFloatArithBase .sub f a a = .some (zeroBits f false) := by
  have hn : 0 < n := decodeBits_finite_num_pos f a neg n d ha
  have hd : 0 < d := decodeBits_finite_den_pos f a neg n d ha
  have hsum : exactSumFloat f (.finite neg n d) (.finite (Bool.not neg) n d) = zeroBits f false := by
    have h0 : signedNum neg n * (d : Int) + signedNum (Bool.not neg) n * (d : Int) = 0 := by
      rw [signedNum_not, Int.neg_mul, Int.add_right_neg]
    have hbeq : Nat.beq n 0 = false := by
      cases n with
      | zero => exact absurd hn (Nat.lt_irrefl 0)
      | succ k => rfl
    unfold exactSumFloat
    dsimp only
    rw [h0, if_pos' rfl, hbeq]
    exact roundRatioTiesToEven_zero f _ (d * d) (Nat.mul_pos hd hd)
  refine ⟨?_, ?_⟩
  · unfold evalFloatArithBase
    dsimp only
    rw [decodeBits_mod, decodeBits_mod, decodeBits_evalFloatNeg, ha]
    exact congrArg some hsum
  · unfold evalFloatArithBase
    dsimp only
    rw [decodeBits_mod, ha]
    exact congrArg some hsum

/-- **Invalid operations produce NaN** (IEEE 754-2008 §7.2): `0 * ∞`, `∞ * 0`,
`∞ + (-∞)`, `∞ - ∞`, `0 / 0`, and `∞ / ∞` return `preferredNaNBits f` for EVERY
sign combination. -/
theorem evalFloatArithBase_invalid_operations (f : IeeeFormat) (s t : Bool) :
    evalFloatArithBase .mul f (zeroBits f s) (infBits f t) = .some (preferredNaNBits f) ∧
    evalFloatArithBase .mul f (infBits f s) (zeroBits f t) = .some (preferredNaNBits f) ∧
    evalFloatArithBase .add f (infBits f s) (infBits f (Bool.not s)) = .some (preferredNaNBits f) ∧
    evalFloatArithBase .sub f (infBits f s) (infBits f s) = .some (preferredNaNBits f) ∧
    evalFloatArithBase .div f (zeroBits f s) (zeroBits f t) = .some (preferredNaNBits f) ∧
    evalFloatArithBase .div f (infBits f s) (infBits f t) = .some (preferredNaNBits f) := by
  cases f <;> cases s <;> cases t <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Infinity arithmetic**: same-signed infinities add to that infinity,
opposite-signed infinities subtract to the minuend, and `∞ * ∞`, `∞ / 0` carry
the XOR sign. -/
theorem evalFloatArithBase_inf_valid_operations (f : IeeeFormat) (s t : Bool) :
    evalFloatArithBase .add f (infBits f s) (infBits f s) = .some (infBits f s) ∧
    evalFloatArithBase .sub f (infBits f s) (infBits f (Bool.not s)) = .some (infBits f s) ∧
    evalFloatArithBase .mul f (infBits f s) (infBits f t) = .some (infBits f (Bool.xor s t)) ∧
    evalFloatArithBase .div f (infBits f s) (zeroBits f t) = .some (infBits f (Bool.xor s t)) ∧
    evalFloatArithBase .div f (zeroBits f s) (infBits f t) = .some (zeroBits f (Bool.xor s t)) := by
  cases f <;> cases s <;> cases t <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Finite nonzero `/ ±0.0 = ±∞` with XOR sign** (IEEE 754-2008 §7.3
`divideByZero`; never `.none` / `.ub`, unlike integer division by zero): e.g.
`(-1.0) / (-0.0) = +∞` and `1.0 / (-0.0) = -∞`. -/
theorem evalFloatArithBase_div_finite_by_zero (f : IeeeFormat) (a : Nat) (neg : Bool) (n d : Nat)
    (s : Bool) (ha : decodeBits f a = .finite neg n d) :
    evalFloatArithBase .div f a (zeroBits f s) = .some (infBits f (Bool.xor neg s)) := by
  have hn : 0 < n := decodeBits_finite_num_pos f a neg n d ha
  unfold evalFloatArithBase
  dsimp only
  rw [decodeBits_mod, decodeBits_mod, ha, decodeBits_zeroBits]
  show some (if n = 0 then preferredNaNBits f else infBits f (Bool.xor neg s)) = _
  rw [if_neg' (Nat.ne_of_gt hn)]

/-- **`x % ±0.0 = NaN`** for EVERY dividend `x` (never `.none` / `.ub`, unlike
integer remainder by zero). -/
theorem evalFloatArithBase_rem_by_zero (f : IeeeFormat) (a : Nat) (s : Bool) :
    evalFloatArithBase .rem f a (zeroBits f s) = .some (preferredNaNBits f) := by
  unfold evalFloatArithBase
  dsimp only
  rw [decodeBits_mod, decodeBits_mod, decodeBits_zeroBits]
  cases decodeBits f a <;> rfl

/-- **`±∞ % y = NaN`** for EVERY divisor `y`. -/
theorem evalFloatArithBase_rem_inf_dividend (f : IeeeFormat) (s : Bool) (b : Nat) :
    evalFloatArithBase .rem f (infBits f s) b = .some (preferredNaNBits f) := by
  unfold evalFloatArithBase
  dsimp only
  rw [decodeBits_mod, decodeBits_mod, decodeBits_infBits]
  cases decodeBits f b <;> rfl

/-- **`finite % ±∞ = finite`**: for every zero or finite nonzero dividend `x`
(either sign, including subnormals), `x % ±∞` returns the canonical bit pattern
of `x` unchanged. -/
theorem evalFloatArithBase_rem_by_inf (f : IeeeFormat) (a : Nat) (s : Bool)
    (hnan : isNaNBits f a = false) (hinf : ∀ t, decodeBits f a ≠ .inf t) :
    evalFloatArithBase .rem f a (infBits f s) = .some (a % 2 ^ f.width) := by
  unfold evalFloatArithBase
  dsimp only
  rw [decodeBits_mod, decodeBits_mod, decodeBits_infBits]
  unfold isNaNBits at hnan
  cases hk : decodeBits f a with
  | zero neg => rfl
  | finite neg n d => rfl
  | inf neg => exact absurd hk (hinf neg)
  | nan neg q p => rw [hk] at hnan; cases hnan

/-- **`±0.0 % y = ±0.0`** for every finite nonzero divisor `y`: the result keeps
the DIVIDEND's sign, independent of the divisor's sign. -/
theorem evalFloatArithBase_rem_zero_dividend (f : IeeeFormat) (s : Bool) (b : Nat)
    (rn : Bool) (rnum rden : Nat) (hb : decodeBits f b = .finite rn rnum rden) :
    evalFloatArithBase .rem f (zeroBits f s) b = .some (zeroBits f s) := by
  have hn : 0 < rnum := decodeBits_finite_num_pos f b rn rnum rden hb
  unfold evalFloatArithBase
  dsimp only
  rw [decodeBits_mod, decodeBits_mod, hb, decodeBits_zeroBits]
  show some (if rnum = 0 then preferredNaNBits f else zeroBits f s) = _
  rw [if_neg' (Nat.ne_of_gt hn)]

/-- A non-NaN bit pattern is not a signaling NaN. -/
theorem isSignalingNaNBits_eq_false_of_not_nan (f : IeeeFormat) (bits : Nat)
    (h : isNaNBits f bits = false) : isSignalingNaNBits f bits = false := by
  unfold isNaNBits at h
  unfold isSignalingNaNBits
  cases hk : decodeBits f bits with
  | zero neg => rfl
  | finite neg n d => rfl
  | inf neg => rfl
  | nan neg q p => rw [hk] at h; cases h

/-- With no NaN inputs, no quieted-propagation candidate exists. -/
theorem nanChoicesQuieted_of_no_nan (t : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (h : ∀ inp, inp ∈ inputs → isNaNBits inp.1 inp.2 = false) :
    nanChoicesQuieted t inputs = [] := by
  induction inputs with
  | nil => rfl
  | cons inp rest ih =>
    have hmod : isNaNBits inp.1 (inp.2 % 2 ^ inp.1.width) = false := by
      unfold isNaNBits
      rw [decodeBits_mod]
      exact h inp List.mem_cons_self
    unfold nanChoicesQuieted
    dsimp only
    rw [hmod, if_neg' Bool.false_ne_true]
    exact ih (fun i hi => h i (List.mem_cons_of_mem _ hi))

/-- With no NaN inputs, no unchanged-signaling-propagation candidate exists. -/
theorem nanChoicesSignaling_of_no_nan (t : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (h : ∀ inp, inp ∈ inputs → isNaNBits inp.1 inp.2 = false) :
    nanChoicesSignaling t inputs = [] := by
  induction inputs with
  | nil => rfl
  | cons inp rest ih =>
    have hmod : isNaNBits inp.1 (inp.2 % 2 ^ inp.1.width) = false := by
      unfold isNaNBits
      rw [decodeBits_mod]
      exact h inp List.mem_cons_self
    unfold nanChoicesSignaling
    dsimp only
    rw [isSignalingNaNBits_eq_false_of_not_nan inp.1 _ hmod, if_neg' Bool.false_ne_true]
    exact ih (fun i hi => h i (List.mem_cons_of_mem _ hi))

/-- **No NaN inputs ⇒ only the preferred NaN (either sign)**: when no input is
NaN (the invalid-operation cases `0 * ∞`, `∞ - ∞`, `0 / 0`, `∞ / ∞`, `x % 0`,
`∞ % y`), the `.nondeterministic` candidate list is exactly
`[preferredNaNBits, -preferredNaNBits]`, formalizing the `core` guarantee that
"if all input NaNs are preferred (or if there are no input NaNs) and the target
does not have any “extra” NaN payloads, then the output NaN is guaranteed to be
preferred." -/
theorem nanChoices_nondet_of_no_nan (t : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (h : ∀ inp, inp ∈ inputs → isNaNBits inp.1 inp.2 = false) :
    nanChoices t inputs .nondeterministic =
      [preferredNaNBits t, evalFloatNeg t (preferredNaNBits t)] := by
  show expandNanSigns t
      (preferredNaNBits t :: (nanChoicesQuieted t inputs ++ nanChoicesSignaling t inputs)) = _
  rw [nanChoicesQuieted_of_no_nan t inputs h, nanChoicesSignaling_of_no_nan t inputs h]
  rfl

/-- **Relational invalid-operation law**: whenever neither operand is NaN but
the base result is NaN (an IEEE 754-2008 §7.2 invalid operation), the
`.nondeterministic` relation admits EXACTLY the preferred NaN with either sign. -/
theorem EvalFloatBinOpRel.nondet_invalid_operation_iff (op : BinOp) (f : IeeeFormat)
    (a b baseBits : Nat) (out : ScalarInt)
    (hcmp : evalFloatCmp op f a b = .none)
    (hbase : evalFloatArithBase op f a b = .some baseBits)
    (hnan : isNaNBits f baseBits = true)
    (ha : isNaNBits f a = false) (hb : isNaNBits f b = false) :
    EvalFloatBinOpRel .nondeterministic op f a b out ↔
      (out = ⟨preferredNaNBits f, f.byteWidth⟩ ∨
       out = ⟨evalFloatNeg f (preferredNaNBits f), f.byteWidth⟩) := by
  have hmodA : isNaNBits f (a % 2 ^ f.width) = false := by
    unfold isNaNBits; rw [decodeBits_mod]; exact ha
  have hmodB : isNaNBits f (b % 2 ^ f.width) = false := by
    unfold isNaNBits; rw [decodeBits_mod]; exact hb
  have hch : nanChoices f [(f, a % 2 ^ f.width), (f, b % 2 ^ f.width)] .nondeterministic =
      [preferredNaNBits f, evalFloatNeg f (preferredNaNBits f)] := by
    apply nanChoices_nondet_of_no_nan
    intro inp hinp
    rcases List.mem_cons.mp hinp with rfl | hinp
    · exact hmodA
    · rcases List.mem_cons.mp hinp with rfl | hinp
      · exact hmodB
      · cases hinp
  unfold EvalFloatBinOpRel
  rw [hcmp, hbase]
  dsimp only
  rw [if_pos' hnan, hch]
  constructor
  · rintro ⟨cand, hmem, hout⟩
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact Or.inl hout
    · rcases List.mem_cons.mp hmem with rfl | hmem
      · exact Or.inr hout
      · cases hmem
  · rintro (hout | hout)
    · exact ⟨_, List.mem_cons_self, hout⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hout⟩

/-- **`evalRvalue`'s NaN `floatToFloat` result is `.nondeterministic`-admissible**:
for a NaN input, the executable quieting conversion
`evalFloatToFloatRoundTiesToEven src dst bits` is a member of the cast candidate
list `nanChoices dst [(src, bits % 2 ^ src.width)] .nondeterministic` used by
`EvalRvalueFloatRel` on `.cast .floatToFloat`. -/
theorem evalFloatToFloat_nan_mem_nanChoices_nondet (src dst : IeeeFormat) (bits : Nat)
    (hnan : isNaNBits src bits = true) :
    evalFloatToFloatRoundTiesToEven src dst bits ∈
      nanChoices dst [(src, bits % 2 ^ src.width)] .nondeterministic := by
  have hmod : isNaNBits src (bits % 2 ^ src.width % 2 ^ src.width) = true := by
    unfold isNaNBits
    rw [decodeBits_mod, decodeBits_mod]
    exact hnan
  have hconv : evalFloatToFloatRoundTiesToEven src dst (bits % 2 ^ src.width % 2 ^ src.width) =
      evalFloatToFloatRoundTiesToEven src dst bits := by
    unfold evalFloatToFloatRoundTiesToEven
    rw [decodeBits_mod, decodeBits_mod]
  have hq : evalFloatToFloatRoundTiesToEven src dst bits ∈
      nanChoicesQuieted dst [(src, bits % 2 ^ src.width)] := by
    unfold nanChoicesQuieted
    dsimp only
    rw [hmod, if_pos' rfl, hconv]
    exact List.mem_cons_self
  show evalFloatToFloatRoundTiesToEven src dst bits ∈
    expandNanSigns dst (preferredNaNBits dst ::
      (nanChoicesQuieted dst [(src, bits % 2 ^ src.width)] ++
        nanChoicesSignaling dst [(src, bits % 2 ^ src.width)]))
  exact (mem_expandNanSigns_iff dst _ _).mpr
    ⟨_, List.mem_cons_of_mem _ (List.mem_append_left _ hq), Or.inl rfl⟩

/-- **`.deterministic` NaN `floatToFloat` discrepancy witness**: for the quiet NaN
`0x7FC00001_f32` (nonzero payload), the executable quieting conversion to `f64` is
`0x7FF8000020000000`, which is NOT the single `.deterministic` candidate
`preferredNaNBits .binary64 = 0x7FF8000000000000`. Hence `evalRvalue` realizes
`EvalRvalueFloatRel` on NaN `floatToFloat` casts in `.nondeterministic` mode only. -/
theorem evalFloatToFloat_nan_not_mem_nanChoices_det_witness :
    isNaNBits .binary32 0x7FC00001 = true ∧
    evalFloatToFloatRoundTiesToEven .binary32 .binary64 0x7FC00001 = 0x7FF8000020000000 ∧
    nanChoices .binary64 [(.binary32, 0x7FC00001)] .deterministic = [0x7FF8000000000000] ∧
    evalFloatToFloatRoundTiesToEven .binary32 .binary64 0x7FC00001 ∉
      nanChoices .binary64 [(.binary32, 0x7FC00001)] .deterministic := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  decide +kernel

/-- `zeroBits` determines its sign argument. -/
theorem zeroBits_injective (f : IeeeFormat) (s t : Bool) (h : zeroBits f s = zeroBits f t) :
    s = t := by
  cases f <;> cases s <;> cases t <;> first | rfl | exact absurd h (by decide)

/-- `sub a b` is definitionally the base sum `add a (-b)` on ALL bit patterns
("Subtraction a - b is regarded as a sum a + (-b)"). -/
theorem evalFloatArithBase_sub_eq_add_neg (f : IeeeFormat) (a b : Nat) :
    evalFloatArithBase .sub f a b = evalFloatArithBase .add f a (evalFloatNeg f b) := by
  unfold evalFloatArithBase
  dsimp only
  simp only [decodeBits_mod, decodeBits_evalFloatNeg]

/-- Double negation of the right operand does not change the base sum. -/
theorem evalFloatArithBase_add_neg_neg (f : IeeeFormat) (a b : Nat) :
    evalFloatArithBase .add f a (evalFloatNeg f (evalFloatNeg f b)) =
      evalFloatArithBase .add f a b := by
  unfold evalFloatArithBase
  dsimp only
  simp only [decodeBits_mod, decodeBits_evalFloatNeg, negateFloatKind_involutive]

/-- **Documented signed-zero rule for sums** (`core` `f32` documentation: "If the
result of a sum exactly equals zero, the outcome is +0.0 unless both arguments
were negative, then it is -0.0"): whenever `a + b` of two zero-or-finite operands
with sign bits `sa`, `sb` is a zero, that zero's sign bit is exactly `sa && sb`. -/
theorem evalFloatArithBase_add_zero_sign (f : IeeeFormat) (a b : Nat) (sa sb s : Bool)
    (ha : decodeBits f a = .zero sa ∨ ∃ n d, decodeBits f a = .finite sa n d)
    (hb : decodeBits f b = .zero sb ∨ ∃ n d, decodeBits f b = .finite sb n d)
    (h : evalFloatArithBase .add f a b = .some (zeroBits f s)) :
    s = Bool.and sa sb := by
  -- `a + b = ±0` forces `a == -b` (gradual underflow: no nonzero sum rounds to zero).
  have haFin : isNaNBits f a = false ∧ ∀ t, decodeBits f a ≠ .inf t := by
    unfold isNaNBits
    rcases ha with ha | ⟨n, d, ha⟩ <;> rw [ha] <;>
      exact ⟨rfl, fun t ht => by cases ht⟩
  have hnbFin : isNaNBits f (evalFloatNeg f b) = false ∧
      ∀ t, decodeBits f (evalFloatNeg f b) ≠ .inf t := by
    unfold isNaNBits
    rw [decodeBits_evalFloatNeg]
    rcases hb with hb | ⟨n, d, hb⟩ <;> rw [hb] <;>
      exact ⟨rfl, fun t ht => by cases ht⟩
  have hsub : evalFloatArithBase .sub f a (evalFloatNeg f b) = .some (zeroBits f s) := by
    rw [evalFloatArithBase_sub_eq_add_neg, evalFloatArithBase_add_neg_neg]
    exact h
  have hcmp : evalFloatCmp .eq f a (evalFloatNeg f b) = .some true :=
    (gradual_underflow_sub_zero_iff f a (evalFloatNeg f b) haFin hnbFin).mp ⟨s, hsub⟩
  unfold evalFloatCmp evalFloatPartialCompare at hcmp
  dsimp only at hcmp
  rw [decodeBits_mod, decodeBits_mod, decodeBits_evalFloatNeg] at hcmp
  rcases ha with ha | ⟨ln, ld, ha⟩
  · rcases hb with hb | ⟨rn, rd, hb⟩
    · -- (±0) + (±0)
      unfold evalFloatArithBase at h
      dsimp only at h
      rw [decodeBits_mod, decodeBits_mod, ha, hb] at h
      have hz : zeroBits f (Bool.and sa sb) = zeroBits f s := Option.some.inj h
      exact (zeroBits_injective f _ _ hz).symm
    · -- (±0) + finite nonzero is never a zero
      have hrn : 0 < rn := decodeBits_finite_num_pos f b sb rn rd hb
      rw [ha, hb] at hcmp
      dsimp only [negateFloatKind] at hcmp
      rw [if_neg' (Nat.ne_of_gt hrn)] at hcmp
      cases sb <;> cases hcmp
  · have hln : 0 < ln := decodeBits_finite_num_pos f a sa ln ld ha
    rcases hb with hb | ⟨rn, rd, hb⟩
    · -- finite nonzero + (±0) is never a zero
      rw [ha, hb] at hcmp
      dsimp only [negateFloatKind] at hcmp
      rw [if_neg' (Nat.ne_of_gt hln)] at hcmp
      cases sa <;> cases hcmp
    · -- finite + finite: exact cancellation, operands of opposite sign
      have hrn : 0 < rn := decodeBits_finite_num_pos f b sb rn rd hb
      have hld : 0 < ld := decodeBits_finite_den_pos f a sa ln ld ha
      have hrd : 0 < rd := decodeBits_finite_den_pos f b sb rn rd hb
      rw [ha, hb] at hcmp
      dsimp only [negateFloatKind] at hcmp
      have heq : signedNum sa ln * (rd : Int) = signedNum (Bool.not sb) rn * (ld : Int) := by
        by_cases hlt : signedNum sa ln * (rd : Int) < signedNum (Bool.not sb) rn * (ld : Int)
        · rw [if_pos' hlt] at hcmp; cases hcmp
        · rw [if_neg' hlt] at hcmp
          by_cases he : signedNum sa ln * (rd : Int) = signedNum (Bool.not sb) rn * (ld : Int)
          · exact he
          · rw [if_neg' he] at hcmp; cases hcmp
      have hn0 : signedNum sa ln * (rd : Int) + signedNum sb rn * (ld : Int) = 0 := by
        rw [heq, signedNum_not, Int.neg_mul, Int.add_left_neg]
      have hadd := evalFloatArithBase_add_finite f a b sa sb ln ld rn rd
        (by rw [decodeBits_mod]; exact ha) (by rw [decodeBits_mod]; exact hb)
      dsimp only at hadd
      rw [hn0, if_pos' rfl, h] at hadd
      have hz : zeroBits f s = zeroBits f false := by
        have := Option.some.inj hadd
        rw [this]
        exact roundRatioTiesToEven_zero f false (ld * rd) (Nat.mul_pos hld hrd)
      have hs : s = false := zeroBits_injective f _ _ hz
      -- both operands negative would make the exact sum strictly negative
      have hP : (0 : Int) < (ln : Int) * (rd : Int) :=
        Int.mul_pos (Int.natCast_pos.mpr hln) (Int.natCast_pos.mpr hrd)
      have hQ : (0 : Int) < (rn : Int) * (ld : Int) :=
        Int.mul_pos (Int.natCast_pos.mpr hrn) (Int.natCast_pos.mpr hld)
      rw [hs]
      cases sa
      · rfl
      · cases sb
        · rfl
        · exfalso
          have hn0' : -((ln : Int) * (rd : Int)) + -((rn : Int) * (ld : Int)) = 0 := by
            have := hn0
            unfold signedNum at this
            rw [if_pos' rfl, if_pos' rfl, Int.neg_mul, Int.neg_mul] at this
            exact this
          omega

/-- **Documented signed-zero rule for differences** ("Subtraction a - b is regarded
as a sum a + (-b)"): whenever `a - b` of two zero-or-finite operands with sign bits
`sa`, `sb` is a zero, that zero's sign bit is exactly `sa && !sb`. -/
theorem evalFloatArithBase_sub_zero_sign (f : IeeeFormat) (a b : Nat) (sa sb s : Bool)
    (ha : decodeBits f a = .zero sa ∨ ∃ n d, decodeBits f a = .finite sa n d)
    (hb : decodeBits f b = .zero sb ∨ ∃ n d, decodeBits f b = .finite sb n d)
    (h : evalFloatArithBase .sub f a b = .some (zeroBits f s)) :
    s = Bool.and sa (Bool.not sb) := by
  have hnb : decodeBits f (evalFloatNeg f b) = .zero (Bool.not sb) ∨
      ∃ n d, decodeBits f (evalFloatNeg f b) = .finite (Bool.not sb) n d := by
    rw [decodeBits_evalFloatNeg]
    rcases hb with hb | ⟨n, d, hb⟩
    · exact Or.inl (by rw [hb]; rfl)
    · exact Or.inr ⟨n, d, by rw [hb]; rfl⟩
  rw [evalFloatArithBase_sub_eq_add_neg] at h
  exact evalFloatArithBase_add_zero_sign f a (evalFloatNeg f b) sa (Bool.not sb) s ha hnb h

/-! ### `evalRvalue`-level realization, dispatcher laws, & subtraction-as-negated-addition -/

/-- `evalFloatBinOp .sub` coincides unconditionally with `evalFloatBinOp .add` on the
negated right operand (including on NaN inputs, because deterministic `evalFloatArithBase`
always returns `preferredNaNBits f` on any NaN). -/
theorem evalFloatBinOp_sub_eq_add_neg (f : IeeeFormat) (a b : Nat) :
    evalFloatBinOp .sub f a b = evalFloatBinOp .add f a (evalFloatNeg f b) := by
  have hsub : evalFloatCmp .sub f a b = .none := rfl
  have hadd : evalFloatCmp .add f a (evalFloatNeg f b) = .none := rfl
  unfold evalFloatBinOp
  rw [hsub, hadd, evalFloatArithBase_sub_eq_add_neg]

/-- Mode-parametric subtraction-as-negated-addition for `EvalFloatBinOpRel`: holds
unconditionally in BOTH `.deterministic` and `.nondeterministic` modes. -/
theorem EvalFloatBinOpRel.sub_iff_add_neg (mode : FloatArithMode) (f : IeeeFormat) (a b : Nat)
    (out : ScalarInt) :
    EvalFloatBinOpRel mode .sub f a b out ↔
      EvalFloatBinOpRel mode .add f a (evalFloatNeg f b) out := by
  cases mode with
  | deterministic =>
    rw [← evalFloatBinOp_iff_rel_det, ← evalFloatBinOp_iff_rel_det, evalFloatBinOp_sub_eq_add_neg]
  | nondeterministic =>
    exact EvalFloatBinOpRel.nondet_sub_iff_add_neg f a b out

private theorem evalFloatScalarBinOp_rel_det_iff
    (op : BinOp) (lhs rhs : ScalarInt) (lhsTy? rhsTy? : Option Ty)
    (locals : List LocalSlot) (mem : Memory) (res : RvalueEvalResult) :
    (match lhsTy?, rhsTy? with
     | .some lTy, .some rTy =>
       match ieeeFormatOfTy? lTy, ieeeFormatOfTy? rTy with
       | .some fL, .some fR =>
         match Bool.and
             (match fL, fR with | .binary32, .binary32 => true | .binary64, .binary64 => true | _, _ => false)
             (Bool.and (Nat.beq lhs.sizeBytes fL.byteWidth) (Nat.beq rhs.sizeBytes fL.byteWidth)) with
         | true =>
           match evalFloatBinOp op fL lhs.bits rhs.bits with
           | .some _ =>
             ∃ outSc, EvalFloatBinOpRel .deterministic op fL lhs.bits rhs.bits outSc ∧
               res = .ok (.scalar outSc) locals mem
           | .none => res = .unsupported
         | false => res = .unsupported
       | _, _ => res = .unsupported
     | _, _ => res = .unsupported) ↔
      res = evalFloatScalarBinOp op lhs rhs lhsTy? rhsTy? locals mem := by
  unfold evalFloatScalarBinOp
  cases lhsTy? with
  | none => exact Iff.rfl
  | some lTy =>
    cases rhsTy? with
    | none => exact Iff.rfl
    | some rTy =>
      dsimp only
      cases ieeeFormatOfTy? lTy with
      | none => exact Iff.rfl
      | some fL =>
        cases ieeeFormatOfTy? rTy with
        | none => exact Iff.rfl
        | some fR =>
          have hdiag (f : IeeeFormat) :
              (match evalFloatBinOp op f lhs.bits rhs.bits with
               | .some _ =>
                 ∃ outSc, EvalFloatBinOpRel .deterministic op f lhs.bits rhs.bits outSc ∧
                   res = .ok (.scalar outSc) locals mem
               | .none => res = .unsupported) ↔
                res = match evalFloatBinOp op f lhs.bits rhs.bits with
                  | .some outSc => .ok (.scalar outSc) locals mem
                  | .none => .unsupported := by
            cases hbin : evalFloatBinOp op f lhs.bits rhs.bits with
            | none => exact Iff.rfl
            | some outSc =>
              dsimp only
              constructor
              · rintro ⟨outSc', hrel, hres⟩
                have heq : evalFloatBinOp op f lhs.bits rhs.bits = .some outSc' :=
                  (evalFloatBinOp_iff_rel_det op f lhs.bits rhs.bits outSc').mpr hrel
                rw [hbin] at heq
                injection heq with hsc
                rw [hres, hsc]
              · intro hres
                exact ⟨outSc, (evalFloatBinOp_iff_rel_det op f lhs.bits rhs.bits outSc).mp hbin, hres⟩
          cases fL <;> cases fR <;> dsimp only
          · cases Bool.and (Nat.beq lhs.sizeBytes IeeeFormat.binary32.byteWidth)
                (Nat.beq rhs.sizeBytes IeeeFormat.binary32.byteWidth) with
            | false => exact Iff.rfl
            | true => exact hdiag .binary32
          · exact Iff.rfl
          · exact Iff.rfl
          · cases Bool.and (Nat.beq lhs.sizeBytes IeeeFormat.binary64.byteWidth)
                (Nat.beq rhs.sizeBytes IeeeFormat.binary64.byteWidth) with
            | false => exact Iff.rfl
            | true => exact hdiag .binary64

/-- On every `Rvalue.binaryOp` (at any `Ptr2IntTransmutePolicy`), `EvalRvalueFloatRel .deterministic`
is equivalent to `res = evalRvalue ...`. -/
theorem EvalRvalueFloatRel_det_binaryOp_iff
    (policy : Ptr2IntTransmutePolicy) (locals : List LocalSlot)
    (op : BinOp) (lhsOp rhsOp : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (res : RvalueEvalResult) :
    EvalRvalueFloatRel .deterministic policy locals (.binaryOp op lhsOp rhsOp) mem localDecls layouts res ↔
      res = evalRvalue locals (.binaryOp op lhsOp rhsOp) mem localDecls layouts := by
  have hnon_offset : ∀ (op' : BinOp) (lhs rhs : ScalarInt) (locals₂ : List LocalSlot),
      (match Bool.or (isFloatOptTy (operandTy localDecls layouts lhsOp))
          (isFloatOptTy (operandTy localDecls layouts rhsOp)) with
       | true =>
         match operandTy localDecls layouts lhsOp, operandTy localDecls layouts rhsOp with
         | .some lTy, .some rTy =>
           match ieeeFormatOfTy? lTy, ieeeFormatOfTy? rTy with
           | .some fL, .some fR =>
             match Bool.and
                 (match fL, fR with | .binary32, .binary32 => true | .binary64, .binary64 => true | _, _ => false)
                 (Bool.and (Nat.beq lhs.sizeBytes fL.byteWidth) (Nat.beq rhs.sizeBytes fL.byteWidth)) with
             | true =>
               match evalFloatBinOp op' fL lhs.bits rhs.bits with
               | .some _ =>
                 ∃ outSc, EvalFloatBinOpRel .deterministic op' fL lhs.bits rhs.bits outSc ∧
                   res = .ok (.scalar outSc) locals₂ mem
               | .none => res = .unsupported
             | false => res = .unsupported
           | _, _ => res = .unsupported
         | _, _ => res = .unsupported
       | false => res = evalScalarBinOp op' lhs rhs locals₂ mem (operandIsSigned localDecls lhsOp layouts)) ↔
      res =
        match Bool.or (isFloatOptTy (operandTy localDecls layouts lhsOp))
            (isFloatOptTy (operandTy localDecls layouts rhsOp)) with
        | true => evalFloatScalarBinOp op' lhs rhs (operandTy localDecls layouts lhsOp)
            (operandTy localDecls layouts rhsOp) locals₂ mem
        | false => evalScalarBinOp op' lhs rhs locals₂ mem (operandIsSigned localDecls lhsOp layouts) := by
    intro op' lhs rhs locals₂
    cases Bool.or (isFloatOptTy (operandTy localDecls layouts lhsOp))
        (isFloatOptTy (operandTy localDecls layouts rhsOp)) with
    | false => exact Iff.rfl
    | true => exact evalFloatScalarBinOp_rel_det_iff op' lhs rhs _ _ locals₂ mem res
  unfold EvalRvalueFloatRel
  dsimp only
  cases hl : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
  | ub => unfold evalRvalue; dsimp only; rw [hl]
  | unsupported => unfold evalRvalue; dsimp only; rw [hl]
  | ok lhsVal locals₁ =>
    dsimp only
    cases hr : evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
    | ub => unfold evalRvalue; dsimp only; rw [hl]; dsimp only; rw [hr]
    | unsupported => unfold evalRvalue; dsimp only; rw [hl]; dsimp only; rw [hr]
    | ok rhsVal locals₂ =>
      dsimp only
      cases lhsVal with
      | scalar lhs =>
        cases rhsVal with
        | scalar rhs =>
          dsimp only
          have heval_sc :
              evalRvalue locals (.binaryOp op lhsOp rhsOp) mem localDecls layouts =
                match op with
                | .offset => evalScalarPtrOffsetBinOp locals₂ mem localDecls layouts lhsOp lhs rhs
                | _ =>
                  let lhsTy := operandTy localDecls layouts lhsOp
                  let rhsTy := operandTy localDecls layouts rhsOp
                  match Bool.or (isFloatOptTy lhsTy) (isFloatOptTy rhsTy) with
                  | true => evalFloatScalarBinOp op lhs rhs lhsTy rhsTy locals₂ mem
                  | false =>
                    let isSigned := operandIsSigned localDecls lhsOp layouts
                    evalScalarBinOp op lhs rhs locals₂ mem isSigned := by
            unfold evalRvalue; dsimp only; rw [hl]; dsimp only; rewrite [hr]; cases op <;> rfl
          rw [heval_sc]
          have hop := hnon_offset op lhs rhs locals₂
          cases op with
          | offset => exact Iff.rfl
          | _ => exact hop
        | _ => exact Iff.rfl
      | _ => exact Iff.rfl

/-- For every `rv` other than `.cast .floatToFloat`, `EvalRvalueFloatRel .deterministic .strictUcg630Ub`
coincides exactly with `evalRvalue`. -/
theorem EvalRvalueFloatRel_det_iff_evalRvalue
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (res : RvalueEvalResult)
    (hNotF2F : ∀ op targetTy, rv ≠ .cast .floatToFloat op targetTy) :
    EvalRvalueFloatRel .deterministic .strictUcg630Ub locals rv mem localDecls layouts res ↔
      res = evalRvalue locals rv mem localDecls layouts := by
  cases rv with
  | binaryOp op lhsOp rhsOp =>
    exact EvalRvalueFloatRel_det_binaryOp_iff .strictUcg630Ub locals op lhsOp rhsOp mem localDecls layouts res
  | cast kind op targetTy =>
    cases kind with
    | floatToFloat => exact absurd rfl (hNotF2F op targetTy)
    | _ => exact Iff.rfl
  | _ => exact Iff.rfl

/-- On `.cast .floatToFloat` with a non-NaN source scalar, `EvalRvalueFloatRel` agrees
exactly with `evalRvalue` in BOTH `.deterministic` and `.nondeterministic` modes (at any
`Ptr2IntTransmutePolicy`). -/
theorem EvalRvalueFloatRel_floatToFloat_of_not_nan
    (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (locals locals' : List LocalSlot) (op : Operand) (targetTy srcTy : Ty)
    (sc : ScalarInt) (src : IeeeFormat)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) (res : RvalueEvalResult)
    (hop : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar sc) locals')
    (hty : operandTy localDecls layouts op = .some srcTy)
    (hfmt : ieeeFormatOfTy? srcTy = .some src)
    (hnotNan : isNaNBits src sc.bits = false) :
    EvalRvalueFloatRel mode policy locals (.cast .floatToFloat op targetTy) mem localDecls layouts res ↔
      res = evalRvalue locals (.cast .floatToFloat op targetTy) mem localDecls layouts := by
  unfold EvalRvalueFloatRel evalRvalue evalFloatCastRvalue evalFloatCast
  dsimp only
  rw [hop]
  dsimp only
  rw [hty]
  dsimp only
  rw [hfmt]
  cases ieeeFormatOfTy? targetTy with
  | none => exact Iff.rfl
  | some dst =>
    dsimp only
    cases Nat.beq sc.sizeBytes src.byteWidth with
    | false => exact Iff.rfl
    | true =>
      dsimp only
      rw [if_neg' (by rw [hnotNan]; exact Bool.false_ne_true)]

/-- **Universal `.nondeterministic` realization**: for EVERY `rv : Rvalue` (including
float `.unaryOp .neg`, float `.binaryOp`, NaN-input `.cast .floatToFloat`, `.cast .transmute`,
and every fallback arm), the executable `evalRvalue` result satisfies
`EvalRvalueFloatRel .nondeterministic .strictUcg630Ub`. -/
theorem evalRvalue_realizes_EvalRvalueFloatRel_nondet
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    EvalRvalueFloatRel .nondeterministic .strictUcg630Ub locals rv mem localDecls layouts
      (evalRvalue locals rv mem localDecls layouts) := by
  cases rv with
  | binaryOp op lhsOp rhsOp =>
    exact EvalRvalueFloatRel.det_imp_nondet .strictUcg630Ub locals (.binaryOp op lhsOp rhsOp)
      mem localDecls layouts _
      ((EvalRvalueFloatRel_det_binaryOp_iff .strictUcg630Ub locals op lhsOp rhsOp mem localDecls layouts _).mpr rfl)
  | cast kind op targetTy =>
    cases kind with
    | floatToFloat =>
      unfold EvalRvalueFloatRel evalRvalue evalFloatCastRvalue evalFloatCast
      dsimp only
      cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
      | ub => rfl
      | unsupported => rfl
      | ok v locals' =>
        dsimp only
        cases operandTy localDecls layouts op with
        | none => rfl
        | some srcTy =>
          cases v with
          | scalar sc =>
            dsimp only
            cases ieeeFormatOfTy? srcTy with
            | none => rfl
            | some src =>
              cases ieeeFormatOfTy? targetTy with
              | none => rfl
              | some dst =>
                dsimp only
                cases Nat.beq sc.sizeBytes src.byteWidth with
                | false => rfl
                | true =>
                  dsimp only
                  by_cases hnan : isNaNBits src sc.bits = true
                  · rw [if_pos' hnan]
                    exact ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits,
                      evalFloatToFloat_nan_mem_nanChoices_nondet src dst sc.bits hnan, rfl⟩
                  · rw [if_neg' hnan]
          | _ => rfl
    | _ => rfl
  | _ => rfl

/-- Any `.ok` result of `evalRvalue` on `.unaryOp .neg` realizes `EvalRvalueFloatRel` in
BOTH `.deterministic` and `.nondeterministic` modes (at any `Ptr2IntTransmutePolicy`). -/
theorem evalRvalue_ok_realizes_EvalRvalueFloatRel_unaryNeg
    (policy : Ptr2IntTransmutePolicy) (locals locals' : List LocalSlot)
    (op : Operand) (val : Value) (mem mem' : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (heval : evalRvalue locals (.unaryOp .neg op) mem localDecls layouts = .ok val locals' mem') :
    EvalRvalueFloatRel .deterministic policy locals (.unaryOp .neg op) mem localDecls layouts (.ok val locals' mem') ∧
    EvalRvalueFloatRel .nondeterministic policy locals (.unaryOp .neg op) mem localDecls layouts (.ok val locals' mem') :=
  ⟨heval.symm, heval.symm⟩

/-- Any `.ok` result of `evalRvalue` on `.binaryOp` realizes `EvalRvalueFloatRel` in
BOTH `.deterministic` and `.nondeterministic` modes (at any `Ptr2IntTransmutePolicy`). -/
theorem evalRvalue_ok_realizes_EvalRvalueFloatRel_binaryOp
    (policy : Ptr2IntTransmutePolicy) (locals locals' : List LocalSlot)
    (binOp : BinOp) (lhsOp rhsOp : Operand) (val : Value) (mem mem' : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (heval : evalRvalue locals (.binaryOp binOp lhsOp rhsOp) mem localDecls layouts = .ok val locals' mem') :
    EvalRvalueFloatRel .deterministic policy locals (.binaryOp binOp lhsOp rhsOp) mem localDecls layouts (.ok val locals' mem') ∧
    EvalRvalueFloatRel .nondeterministic policy locals (.binaryOp binOp lhsOp rhsOp) mem localDecls layouts (.ok val locals' mem') := by
  have hdet := (EvalRvalueFloatRel_det_binaryOp_iff policy locals binOp lhsOp rhsOp mem localDecls layouts _).mpr heval.symm
  exact ⟨hdet, EvalRvalueFloatRel.det_imp_nondet policy locals (.binaryOp binOp lhsOp rhsOp) mem localDecls layouts _ hdet⟩

/-- Any `.ok` result of `evalRvalue` realizes `EvalRvalueFloatRel .nondeterministic .strictUcg630Ub`
unconditionally, and also realizes `.deterministic` whenever `rv` is not `.cast .floatToFloat`. -/
theorem evalRvalue_ok_realizes_EvalRvalueFloatRel
    (locals locals' : List LocalSlot) (rv : Rvalue) (val : Value) (mem mem' : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (heval : evalRvalue locals rv mem localDecls layouts = .ok val locals' mem') :
    EvalRvalueFloatRel .nondeterministic .strictUcg630Ub locals rv mem localDecls layouts (.ok val locals' mem') ∧
    ((∀ op targetTy, rv ≠ .cast .floatToFloat op targetTy) →
      EvalRvalueFloatRel .deterministic .strictUcg630Ub locals rv mem localDecls layouts (.ok val locals' mem')) := by
  refine ⟨by rw [← heval]; exact evalRvalue_realizes_EvalRvalueFloatRel_nondet locals rv mem localDecls layouts, ?_⟩
  intro hnot
  exact (EvalRvalueFloatRel_det_iff_evalRvalue locals rv mem localDecls layouts _ hnot).mpr heval.symm

/-- **`evalRvalue`-level NaN `floatToFloat` separation witness**: casting `0x7FC00001_f32`
to `f64` evaluates via `evalRvalue` to `0x7FF8000020000000`, which IS admitted by
`EvalRvalueFloatRel .nondeterministic` and is NOT admitted by `EvalRvalueFloatRel .deterministic`,
proving that the `rv ≠ .cast .floatToFloat` side condition in `EvalRvalueFloatRel_det_iff_evalRvalue`
is necessary. -/
theorem evalRvalue_floatToFloat_nan_rel_separation_witness :
    let f64Ty : Ty := { kind := .float .f64, layoutIdx := 0 }
    let op := mkFloatConstOp f32Ty 0x7FC00001 4
    let rv : Rvalue := .cast .floatToFloat op f64Ty
    let res : RvalueEvalResult := .ok (.scalar ⟨0x7FF8000020000000, 8⟩) .nil emptyMemory
    evalRvalue .nil rv emptyMemory .nil emptyLayoutTable = res ∧
    EvalRvalueFloatRel .nondeterministic .strictUcg630Ub .nil rv emptyMemory .nil emptyLayoutTable res ∧
    ¬ EvalRvalueFloatRel .deterministic .strictUcg630Ub .nil rv emptyMemory .nil emptyLayoutTable res := by
  dsimp only
  have heval :
      evalRvalue .nil (.cast .floatToFloat (mkFloatConstOp f32Ty 0x7FC00001 4)
        { kind := .float .f64, layoutIdx := 0 }) emptyMemory .nil emptyLayoutTable =
        .ok (.scalar ⟨0x7FF8000020000000, 8⟩) .nil emptyMemory := rfl
  refine ⟨heval, ?_, ?_⟩
  · rw [← heval]
    exact evalRvalue_realizes_EvalRvalueFloatRel_nondet .nil _ emptyMemory .nil emptyLayoutTable
  · intro hdet
    unfold EvalRvalueFloatRel at hdet
    dsimp only at hdet
    have hop :
        evalOperand .nil (mkFloatConstOp f32Ty 0x7FC00001 4)
          emptyMemory.borrows emptyMemory.globals emptyLayoutTable
          emptyMemory.callerLocals .nil emptyMemory.callStack =
        .ok (.scalar ⟨0x7FC00001, 4⟩) .nil := rfl
    have hfmtSrc : ieeeFormatOfTy? f32Ty = .some .binary32 := rfl
    have hfmtDst : ieeeFormatOfTy? { kind := .float .f64, layoutIdx := 0 } = .some .binary64 := rfl
    have hsz : Nat.beq 4 IeeeFormat.binary32.byteWidth = true := rfl
    have hnan : isNaNBits .binary32 0x7FC00001 = true := rfl
    have hmod : 0x7FC00001 % 2 ^ IeeeFormat.binary32.width = 0x7FC00001 := rfl
    have hch : nanChoices .binary64 [(.binary32, 0x7FC00001)] .deterministic = [0x7FF8000000000000] := rfl
    rw [hop] at hdet
    dsimp only at hdet
    rw [hfmtSrc, hfmtDst] at hdet
    dsimp only at hdet
    rw [hsz] at hdet
    dsimp only at hdet
    rw [if_pos' hnan, hmod, hch] at hdet
    rcases hdet with ⟨cand, hmem, hres⟩
    rcases List.mem_cons.mp hmem with rfl | hnil
    · injection hres with hval _ _
      injection hval with hsc
      injection hsc with hbits _
      exact absurd hbits (by decide)
    · cases hnil

/-- Dispatcher law for `evalRvalue` on `.unaryOp .neg` over a float scalar operand. -/
theorem evalRvalue_unaryOp_neg_float
    (locals locals' : List LocalSlot) (op : Operand) (sc : ScalarInt)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hop : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar sc) locals')
    (hfloat : isFloatOptTy (operandTy localDecls layouts op) = true) :
    evalRvalue locals (.unaryOp .neg op) mem localDecls layouts =
      evalFloatUnaryNeg sc (operandTy localDecls layouts op) locals' mem := by
  unfold evalRvalue
  dsimp only
  rw [hop]
  dsimp only
  rw [hfloat]

/-- Dispatcher law for `evalRvalue` on any non-`.offset` `.binaryOp` over scalar operands
when at least one operand has a floating-point static type. -/
theorem evalRvalue_binaryOp_float
    (locals locals₁ locals₂ : List LocalSlot) (op : BinOp) (lhsOp rhsOp : Operand)
    (lhs rhs : ScalarInt) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hnotOff : op ≠ .offset)
    (hl : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar lhs) locals₁)
    (hr : evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar rhs) locals₂)
    (hfloat : Bool.or (isFloatOptTy (operandTy localDecls layouts lhsOp))
        (isFloatOptTy (operandTy localDecls layouts rhsOp)) = true) :
    evalRvalue locals (.binaryOp op lhsOp rhsOp) mem localDecls layouts =
      evalFloatScalarBinOp op lhs rhs (operandTy localDecls layouts lhsOp)
        (operandTy localDecls layouts rhsOp) locals₂ mem := by
  unfold evalRvalue
  dsimp only
  rw [hl]
  dsimp only
  rw [hr]
  dsimp only
  cases op with
  | offset => exact absurd rfl hnotOff
  | _ => dsimp only; rw [hfloat]

/-- **`evalFloatScalarBinOp` subtraction-as-negated-addition**: whenever `evalFloatUnaryNeg`
negates `rhs` to `rhsNeg`, `evalFloatScalarBinOp .sub lhs rhs` equals
`evalFloatScalarBinOp .add lhs rhsNeg` unconditionally (for all bit patterns including NaNs). -/
theorem evalFloatScalarBinOp_sub_eq_add_neg
    (lhs rhs rhsNeg : ScalarInt) (lhsTy? rhsTy? : Option Ty)
    (locals : List LocalSlot) (mem : Memory)
    (hneg : evalFloatUnaryNeg rhs rhsTy? locals mem = .ok (.scalar rhsNeg) locals mem) :
    evalFloatScalarBinOp .sub lhs rhs lhsTy? rhsTy? locals mem =
      evalFloatScalarBinOp .add lhs rhsNeg lhsTy? rhsTy? locals mem := by
  unfold evalFloatUnaryNeg at hneg
  cases hrty : rhsTy? with
  | none => rw [hrty] at hneg; cases hneg
  | some rTy =>
    rw [hrty] at hneg
    dsimp only at hneg
    cases hrf : ieeeFormatOfTy? rTy with
    | none => rw [hrf] at hneg; cases hneg
    | some fR =>
      rw [hrf] at hneg
      dsimp only at hneg
      cases hsz : Nat.beq rhs.sizeBytes fR.byteWidth with
      | false => rw [hsz] at hneg; cases hneg
      | true =>
        rw [hsz] at hneg
        dsimp only at hneg
        injection hneg with hval _ _
        injection hval with hsc
        rw [← hsc]
        unfold evalFloatScalarBinOp
        cases lhsTy? with
        | none => rfl
        | some lTy =>
          dsimp only
          rw [hrf]
          cases ieeeFormatOfTy? lTy with
          | none => rfl
          | some fL =>
            dsimp only
            cases fL <;> cases fR <;> dsimp only
            · have hsz_eq : Nat.beq IeeeFormat.binary32.byteWidth IeeeFormat.binary32.byteWidth = true := rfl
              rw [hsz, hsz_eq]
              cases Nat.beq lhs.sizeBytes IeeeFormat.binary32.byteWidth with
              | false => rfl
              | true => rw [evalFloatBinOp_sub_eq_add_neg]
            · rfl
            · rfl
            · have hsz_eq : Nat.beq IeeeFormat.binary64.byteWidth IeeeFormat.binary64.byteWidth = true := rfl
              rw [hsz, hsz_eq]
              cases Nat.beq lhs.sizeBytes IeeeFormat.binary64.byteWidth with
              | false => rfl
              | true => rw [evalFloatBinOp_sub_eq_add_neg]

/-- Direct bit-level form of `evalFloatScalarBinOp_sub_eq_add_neg` using `evalFloatNeg`
on the RHS scalar bits. -/
theorem evalFloatScalarBinOp_sub_eq_add_neg_bits
    (lhs rhs : ScalarInt) (lhsTy? : Option Ty) (rTy : Ty) (f : IeeeFormat)
    (locals : List LocalSlot) (mem : Memory)
    (hrf : ieeeFormatOfTy? rTy = .some f) (hsz : rhs.sizeBytes = f.byteWidth) :
    evalFloatScalarBinOp .sub lhs rhs lhsTy? (.some rTy) locals mem =
      evalFloatScalarBinOp .add lhs ⟨evalFloatNeg f rhs.bits, rhs.sizeBytes⟩ lhsTy? (.some rTy) locals mem := by
  have hneg : evalFloatUnaryNeg rhs (.some rTy) locals mem =
      .ok (.scalar ⟨evalFloatNeg f rhs.bits, rhs.sizeBytes⟩) locals mem := by
    unfold evalFloatUnaryNeg
    dsimp only
    rw [hrf]
    dsimp only
    rw [hsz, Nat.beq_refl]
  exact evalFloatScalarBinOp_sub_eq_add_neg lhs rhs _ lhsTy? (.some rTy) locals mem hneg

/-- **`evalRvalue` subtraction-as-negated-addition**: evaluating `lhsOp - rhsOp` coincides
with evaluating `lhsOp + negRhsOp` whenever `negRhsOp` has the same float type as `rhsOp`
and evaluates to its `evalFloatUnaryNeg` negation. -/
theorem evalRvalue_sub_eq_add_neg_float
    (locals locals₁ locals₂ : List LocalSlot)
    (lhsOp rhsOp negRhsOp : Operand)
    (lhs rhs rhsNeg : ScalarInt)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hl : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar lhs) locals₁)
    (hr : evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar rhs) locals₂)
    (hrn : evalOperand locals₁ negRhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar rhsNeg) locals₂)
    (hty : operandTy localDecls layouts negRhsOp = operandTy localDecls layouts rhsOp)
    (hneg : evalFloatUnaryNeg rhs (operandTy localDecls layouts rhsOp) locals₂ mem =
      .ok (.scalar rhsNeg) locals₂ mem) :
    evalRvalue locals (.binaryOp .sub lhsOp rhsOp) mem localDecls layouts =
      evalRvalue locals (.binaryOp .add lhsOp negRhsOp) mem localDecls layouts := by
  have hfloatR : isFloatOptTy (operandTy localDecls layouts rhsOp) = true := by
    unfold evalFloatUnaryNeg at hneg
    cases hrty : operandTy localDecls layouts rhsOp with
    | none => rw [hrty] at hneg; cases hneg
    | some rTy =>
      rw [hrty] at hneg
      dsimp only at hneg
      unfold isFloatOptTy isFloatTy
      cases hrf : ieeeFormatOfTy? rTy with
      | none => rw [hrf] at hneg; cases hneg
      | some _ =>
        unfold ieeeFormatOfTy? at hrf
        cases hrk : rTy.kind with
        | float _ => dsimp only; rw [hrk]
        | _ => rw [hrk] at hrf; cases hrf
  rw [evalRvalue_binaryOp_float locals locals₁ locals₂ .sub lhsOp rhsOp lhs rhs mem localDecls layouts
        (fun h => nomatch h) hl hr (by rw [hfloatR, Bool.or_true]),
      evalRvalue_binaryOp_float locals locals₁ locals₂ .add lhsOp negRhsOp lhs rhsNeg mem localDecls layouts
        (fun h => nomatch h) hl hrn (by rw [hty, hfloatR, Bool.or_true]),
      hty]
  exact evalFloatScalarBinOp_sub_eq_add_neg lhs rhs rhsNeg _ _ locals₂ mem hneg

/-- **`EvalRvalueFloatRel` subtraction-as-negated-addition (both modes)**:
`EvalRvalueFloatRel mode policy` admits the exact same result set for `lhsOp - rhsOp` and
`lhsOp + negRhsOp` in BOTH `.deterministic` and `.nondeterministic` modes (at any
`Ptr2IntTransmutePolicy`). -/
theorem EvalRvalueFloatRel_sub_iff_add_neg_float
    (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (locals locals₁ locals₂ : List LocalSlot)
    (lhsOp rhsOp negRhsOp : Operand)
    (lhs rhs rhsNeg : ScalarInt)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (res : RvalueEvalResult)
    (hl : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar lhs) locals₁)
    (hr : evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar rhs) locals₂)
    (hrn : evalOperand locals₁ negRhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar rhsNeg) locals₂)
    (hty : operandTy localDecls layouts negRhsOp = operandTy localDecls layouts rhsOp)
    (hneg : evalFloatUnaryNeg rhs (operandTy localDecls layouts rhsOp) locals₂ mem =
      .ok (.scalar rhsNeg) locals₂ mem) :
    EvalRvalueFloatRel mode policy locals (.binaryOp .sub lhsOp rhsOp) mem localDecls layouts res ↔
      EvalRvalueFloatRel mode policy locals (.binaryOp .add lhsOp negRhsOp) mem localDecls layouts res := by
  have hrfmt : ∃ rTy fR,
      operandTy localDecls layouts rhsOp = .some rTy ∧
      ieeeFormatOfTy? rTy = .some fR ∧
      Nat.beq rhs.sizeBytes fR.byteWidth = true ∧
      rhsNeg = ⟨evalFloatNeg fR rhs.bits, fR.byteWidth⟩ := by
    unfold evalFloatUnaryNeg at hneg
    cases hrty : operandTy localDecls layouts rhsOp with
    | none => rw [hrty] at hneg; cases hneg
    | some rTy =>
      rw [hrty] at hneg
      dsimp only at hneg
      cases hrf : ieeeFormatOfTy? rTy with
      | none => rw [hrf] at hneg; cases hneg
      | some fR =>
        rw [hrf] at hneg
        dsimp only at hneg
        cases hsz : Nat.beq rhs.sizeBytes fR.byteWidth with
        | false => rw [hsz] at hneg; cases hneg
        | true =>
          rw [hsz] at hneg
          dsimp only at hneg
          injection hneg with hval _ _
          injection hval with hsc
          exact ⟨rTy, fR, rfl, hrf, hsz, hsc.symm⟩
  obtain ⟨rTy, fR, hrTy, hrf, hszR, hrNeg⟩ := hrfmt
  have hfloatR : isFloatOptTy (.some rTy) = true := by
    unfold isFloatOptTy isFloatTy
    unfold ieeeFormatOfTy? at hrf
    cases hrk : rTy.kind with
    | float _ => dsimp only; rw [hrk]
    | _ => rw [hrk] at hrf; cases hrf
  unfold EvalRvalueFloatRel
  dsimp only
  rw [hl]
  dsimp only
  rw [hr, hrn]
  dsimp only
  rw [hty, hrTy]
  rw [hfloatR, Bool.or_true]
  dsimp only
  rw [hrNeg]
  cases operandTy localDecls layouts lhsOp with
  | none => exact Iff.rfl
  | some lTy =>
    dsimp only
    rw [hrf]
    cases ieeeFormatOfTy? lTy with
    | none => exact Iff.rfl
    | some fL =>
      dsimp only
      cases fL <;> cases fR <;> dsimp only
      · have hsz_eq : Nat.beq IeeeFormat.binary32.byteWidth IeeeFormat.binary32.byteWidth = true := rfl
        rw [hszR, hsz_eq]
        cases Nat.beq lhs.sizeBytes IeeeFormat.binary32.byteWidth with
        | false => exact Iff.rfl
        | true =>
          rw [evalFloatBinOp_sub_eq_add_neg]
          cases evalFloatBinOp .add .binary32 lhs.bits (evalFloatNeg .binary32 rhs.bits) with
          | none => exact Iff.rfl
          | some _ =>
            constructor
            · rintro ⟨outSc, hrel, hres⟩
              exact ⟨outSc, (EvalFloatBinOpRel.sub_iff_add_neg mode _ _ _ _).mp hrel, hres⟩
            · rintro ⟨outSc, hrel, hres⟩
              exact ⟨outSc, (EvalFloatBinOpRel.sub_iff_add_neg mode _ _ _ _).mpr hrel, hres⟩
      · exact Iff.rfl
      · exact Iff.rfl
      · have hsz_eq : Nat.beq IeeeFormat.binary64.byteWidth IeeeFormat.binary64.byteWidth = true := rfl
        rw [hszR, hsz_eq]
        cases Nat.beq lhs.sizeBytes IeeeFormat.binary64.byteWidth with
        | false => exact Iff.rfl
        | true =>
          rw [evalFloatBinOp_sub_eq_add_neg]
          cases evalFloatBinOp .add .binary64 lhs.bits (evalFloatNeg .binary64 rhs.bits) with
          | none => exact Iff.rfl
          | some _ =>
            constructor
            · rintro ⟨outSc, hrel, hres⟩
              exact ⟨outSc, (EvalFloatBinOpRel.sub_iff_add_neg mode _ _ _ _).mp hrel, hres⟩
            · rintro ⟨outSc, hrel, hres⟩
              exact ⟨outSc, (EvalFloatBinOpRel.sub_iff_add_neg mode _ _ _ _).mpr hrel, hres⟩

/-! ### Episode 2 readiness: supportedness, `.ub` / `.unsupported` exactness, and mode / policy invariance

Laws that Episode 2's `FloatArithLM` / `FloatArithMR` step simulations apply directly to
`EvalRvalueFloatRel` at ANY `FloatArithMode` and ANY `Ptr2IntTransmutePolicy` (in particular the
Miri / MiniRust default `.nondeterministic` + `.stripProvenance`):
- `EvalFloatBinOpRel` is non-empty exactly on the eleven float `BinOp`s (`isFloatBinOp`),
  independently of `mode`, format, and operands;
- `policy` is irrelevant outside `.cast .transmute` / `.cast .subtype`, and `mode` is irrelevant
  outside `.binaryOp` / `.cast .floatToFloat`;
- every non-`.ok` outcome (`.ub`, `.unsupported`) admitted by the relation is mode-invariant and,
  outside byte casts, coincides EXACTLY with the executable `evalRvalue` outcome;
- generic-mode dispatchers for float `.binaryOp` and NaN-input `.cast .floatToFloat`.
-/

/-- `true` exactly on the eleven `BinOp`s given IEEE-754 semantics by `evalFloatBinOp`:
arithmetic `add`, `sub`, `mul`, `div`, `rem` and comparisons `eq`, `ne`, `lt`, `le`, `gt`, `ge`. -/
def isFloatBinOp : BinOp → Bool
  | .add | .sub | .mul | .div | .rem | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

/-- **Closed-form supportedness of `evalFloatBinOp`**: it returns `.none` exactly on the
non-float `BinOp`s, independently of the format and of both operands (in particular float
division and remainder by zero, NaN operands, and overflow are never `.none`). -/
theorem evalFloatBinOp_eq_none_iff (op : BinOp) (f : IeeeFormat) (a b : Nat) :
    evalFloatBinOp op f a b = .none ↔ isFloatBinOp op = false := by
  cases op <;>
    first
    | exact ⟨fun _ => rfl, fun _ => rfl⟩
    | exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

/-- **Mode-invariant emptiness of `EvalFloatBinOpRel`**: in BOTH `.deterministic` and
`.nondeterministic` modes the relation admits no output IF AND ONLY IF the executable
`evalFloatBinOp` returns `.none`. -/
theorem EvalFloatBinOpRel_none_iff (mode : FloatArithMode) (op : BinOp) (f : IeeeFormat)
    (a b : Nat) :
    (∀ out, ¬ EvalFloatBinOpRel mode op f a b out) ↔ evalFloatBinOp op f a b = .none := by
  constructor
  · intro h
    cases hbin : evalFloatBinOp op f a b with
    | none => rfl
    | some out =>
      have hdet := (evalFloatBinOp_iff_rel_det op f a b out).mp hbin
      cases mode with
      | deterministic => exact absurd hdet (h out)
      | nondeterministic =>
        exact absurd (EvalFloatBinOpRel.det_imp_nondet op f a b out hdet) (h out)
  · intro hnone out hrel
    unfold evalFloatBinOp at hnone
    unfold EvalFloatBinOpRel at hrel
    cases hcmp : evalFloatCmp op f a b with
    | some c => rw [hcmp] at hnone; cases hnone
    | none =>
      rw [hcmp] at hnone hrel
      dsimp only at hnone hrel
      cases harith : evalFloatArithBase op f a b with
      | some bits => rw [harith] at hnone; cases hnone
      | none => rw [harith] at hrel; exact hrel

/-- **Mode-invariant totality of `EvalFloatBinOpRel`**: in BOTH modes, for EVERY format and
EVERY pair of operand bit patterns, some output is admitted IF AND ONLY IF `op` is one of the
eleven float `BinOp`s. -/
theorem EvalFloatBinOpRel_exists_iff (mode : FloatArithMode) (op : BinOp) (f : IeeeFormat)
    (a b : Nat) :
    (∃ out, EvalFloatBinOpRel mode op f a b out) ↔ isFloatBinOp op = true := by
  constructor
  · rintro ⟨out, hrel⟩
    cases hop : isFloatBinOp op with
    | true => rfl
    | false =>
      exact absurd hrel
        ((EvalFloatBinOpRel_none_iff mode op f a b).mpr
          ((evalFloatBinOp_eq_none_iff op f a b).mpr hop) out)
  · intro hop
    cases hbin : evalFloatBinOp op f a b with
    | none =>
      have hfalse := (evalFloatBinOp_eq_none_iff op f a b).mp hbin
      rw [hop] at hfalse
      cases hfalse
    | some out =>
      have hdet := (evalFloatBinOp_iff_rel_det op f a b out).mp hbin
      cases mode with
      | deterministic => exact ⟨out, hdet⟩
      | nondeterministic => exact ⟨out, EvalFloatBinOpRel.det_imp_nondet op f a b out hdet⟩

/-- **Well-formedness of every admitted `EvalFloatBinOpRel` output (both modes)**: the output
is either the `bool` scalar of a comparison, or an arithmetic scalar of width `f.byteWidth`
with a canonical bit pattern (`< 2 ^ f.width`), including every `.nondeterministic` NaN choice. -/
theorem EvalFloatBinOpRel_out_wf (mode : FloatArithMode) (op : BinOp) (f : IeeeFormat)
    (a b : Nat) (out : ScalarInt) (h : EvalFloatBinOpRel mode op f a b out) :
    (∃ c, evalFloatCmp op f a b = .some c ∧ out = boolToScalar c) ∨
    (evalFloatCmp op f a b = .none ∧ out.sizeBytes = f.byteWidth ∧ out.bits < 2 ^ f.width) := by
  unfold EvalFloatBinOpRel at h
  cases hcmp : evalFloatCmp op f a b with
  | some c => rw [hcmp] at h; exact Or.inl ⟨c, rfl, h⟩
  | none =>
    rw [hcmp] at h
    dsimp only at h
    cases harith : evalFloatArithBase op f a b with
    | none => rw [harith] at h; exact False.elim h
    | some baseBits =>
      rw [harith] at h
      dsimp only at h
      by_cases hnan : isNaNBits f baseBits = true
      · rw [if_pos' hnan] at h
        rcases h with ⟨cand, hmem, hout⟩
        rw [hout]
        exact Or.inr ⟨rfl, rfl, (mem_nanChoices_props f _ mode cand hmem).1⟩
      · rw [if_neg' hnan] at h
        rw [h]
        exact Or.inr ⟨rfl, rfl, evalFloatArithBase_lt op f a b baseBits harith⟩

/-- **Policy irrelevance outside byte casts**: for every `rv` other than `.cast .transmute` and
`.cast .subtype`, `EvalRvalueFloatRel` does not depend on the `Ptr2IntTransmutePolicy`. -/
theorem EvalRvalueFloatRel_policy_irrelevant
    (mode : FloatArithMode) (policy₁ policy₂ : Ptr2IntTransmutePolicy)
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (res : RvalueEvalResult)
    (hNotTransmute : ∀ op targetTy, rv ≠ .cast .transmute op targetTy)
    (hNotSubtype : ∀ op targetTy, rv ≠ .cast .subtype op targetTy) :
    EvalRvalueFloatRel mode policy₁ locals rv mem localDecls layouts res ↔
      EvalRvalueFloatRel mode policy₂ locals rv mem localDecls layouts res := by
  cases rv with
  | cast kind op targetTy =>
    cases kind with
    | transmute => exact absurd rfl (hNotTransmute op targetTy)
    | subtype => exact absurd rfl (hNotSubtype op targetTy)
    | _ => exact Iff.rfl
  | _ => exact Iff.rfl

/-- **Byte-cast dispatcher (both modes, any policy)**: on `.cast .transmute` and
`.cast .subtype`, `EvalRvalueFloatRel` is exactly `evalByteCast` at `policy`. -/
theorem EvalRvalueFloatRel_byteCast_iff
    (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (locals : List LocalSlot) (kind : CastKind) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (res : RvalueEvalResult)
    (hkind : kind = .transmute ∨ kind = .subtype) :
    EvalRvalueFloatRel mode policy locals (.cast kind op targetTy) mem localDecls layouts res ↔
      res = evalByteCast locals op targetTy mem localDecls layouts policy := by
  rcases hkind with rfl | rfl <;> exact Iff.rfl

/-- **Mode irrelevance outside float arithmetic**: for every `rv` other than `.binaryOp` and
`.cast .floatToFloat` (in particular for the bitwise, NaN-payload-preserving `.unaryOp .neg`
and for byte casts), `EvalRvalueFloatRel` does not depend on the `FloatArithMode`. -/
theorem EvalRvalueFloatRel_mode_irrelevant
    (mode₁ mode₂ : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (res : RvalueEvalResult)
    (hNotBin : ∀ op lhsOp rhsOp, rv ≠ .binaryOp op lhsOp rhsOp)
    (hNotF2F : ∀ op targetTy, rv ≠ .cast .floatToFloat op targetTy) :
    EvalRvalueFloatRel mode₁ policy locals rv mem localDecls layouts res ↔
      EvalRvalueFloatRel mode₂ policy locals rv mem localDecls layouts res := by
  cases rv with
  | binaryOp op lhsOp rhsOp => exact absurd rfl (hNotBin op lhsOp rhsOp)
  | cast kind op targetTy =>
    cases kind with
    | floatToFloat => exact absurd rfl (hNotF2F op targetTy)
    | _ => exact Iff.rfl
  | _ => exact Iff.rfl

/-- **`.unaryOp .neg` dispatcher (both modes, any policy, EVERY result)**: on unary negation
(float or integer), `EvalRvalueFloatRel` is exactly `evalRvalue`, including its `.ub` and
`.unsupported` outcomes (generalizing `evalRvalue_ok_realizes_EvalRvalueFloatRel_unaryNeg`
from `.ok` results to all results). -/
theorem EvalRvalueFloatRel_unaryNeg_iff
    (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (locals : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (res : RvalueEvalResult) :
    EvalRvalueFloatRel mode policy locals (.unaryOp .neg op) mem localDecls layouts res ↔
      res = evalRvalue locals (.unaryOp .neg op) mem localDecls layouts :=
  Iff.rfl

/-- **Mode invariance of every non-`.ok` outcome**: for EVERY `rv` and EVERY policy, a result
that is not `.ok` (`.ub` or `.unsupported`) is admitted by `EvalRvalueFloatRel` in one
`FloatArithMode` IF AND ONLY IF it is admitted in the other (the mode only ever selects among
`.ok` NaN candidates). -/
theorem EvalRvalueFloatRel_mode_irrelevant_of_not_ok
    (mode₁ mode₂ : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (res : RvalueEvalResult)
    (hres : ∀ v l m, res ≠ .ok v l m) :
    EvalRvalueFloatRel mode₁ policy locals rv mem localDecls layouts res ↔
      EvalRvalueFloatRel mode₂ policy locals rv mem localDecls layouts res := by
  unfold EvalRvalueFloatRel
  cases rv with
  | binaryOp op lhsOp rhsOp =>
    dsimp only
    have hnon_offset : ∀ (op' : BinOp) (lhs rhs : ScalarInt) (locals₂ : List LocalSlot),
        (match Bool.or (isFloatOptTy (operandTy localDecls layouts lhsOp))
            (isFloatOptTy (operandTy localDecls layouts rhsOp)) with
         | true =>
           match operandTy localDecls layouts lhsOp, operandTy localDecls layouts rhsOp with
           | .some lTy, .some rTy =>
             match ieeeFormatOfTy? lTy, ieeeFormatOfTy? rTy with
             | .some fL, .some fR =>
               match Bool.and
                   (match fL, fR with | .binary32, .binary32 => true | .binary64, .binary64 => true | _, _ => false)
                   (Bool.and (Nat.beq lhs.sizeBytes fL.byteWidth) (Nat.beq rhs.sizeBytes fL.byteWidth)) with
               | true =>
                 match evalFloatBinOp op' fL lhs.bits rhs.bits with
                 | .some _ =>
                   ∃ outSc,
                     EvalFloatBinOpRel mode₁ op' fL lhs.bits rhs.bits outSc ∧
                     res = .ok (.scalar outSc) locals₂ mem
                 | .none => res = .unsupported
               | false => res = .unsupported
             | _, _ => res = .unsupported
           | _, _ => res = .unsupported
         | false => res = evalScalarBinOp op' lhs rhs locals₂ mem (operandIsSigned localDecls lhsOp layouts)) ↔
        (match Bool.or (isFloatOptTy (operandTy localDecls layouts lhsOp))
            (isFloatOptTy (operandTy localDecls layouts rhsOp)) with
         | true =>
           match operandTy localDecls layouts lhsOp, operandTy localDecls layouts rhsOp with
           | .some lTy, .some rTy =>
             match ieeeFormatOfTy? lTy, ieeeFormatOfTy? rTy with
             | .some fL, .some fR =>
               match Bool.and
                   (match fL, fR with | .binary32, .binary32 => true | .binary64, .binary64 => true | _, _ => false)
                   (Bool.and (Nat.beq lhs.sizeBytes fL.byteWidth) (Nat.beq rhs.sizeBytes fL.byteWidth)) with
               | true =>
                 match evalFloatBinOp op' fL lhs.bits rhs.bits with
                 | .some _ =>
                   ∃ outSc,
                     EvalFloatBinOpRel mode₂ op' fL lhs.bits rhs.bits outSc ∧
                     res = .ok (.scalar outSc) locals₂ mem
                 | .none => res = .unsupported
               | false => res = .unsupported
             | _, _ => res = .unsupported
           | _, _ => res = .unsupported
         | false => res = evalScalarBinOp op' lhs rhs locals₂ mem (operandIsSigned localDecls lhsOp layouts)) := by
      intro op' lhs rhs locals₂
      cases Bool.or (isFloatOptTy (operandTy localDecls layouts lhsOp))
          (isFloatOptTy (operandTy localDecls layouts rhsOp)) with
      | false => exact Iff.rfl
      | true =>
        dsimp only
        cases operandTy localDecls layouts lhsOp with
        | none => exact Iff.rfl
        | some lTy =>
          cases operandTy localDecls layouts rhsOp with
          | none => exact Iff.rfl
          | some rTy =>
            dsimp only
            cases ieeeFormatOfTy? lTy with
            | none => exact Iff.rfl
            | some fL =>
              cases ieeeFormatOfTy? rTy with
              | none => exact Iff.rfl
              | some fR =>
                dsimp only
                cases Bool.and
                    (match fL, fR with | .binary32, .binary32 => true | .binary64, .binary64 => true | _, _ => false)
                    (Bool.and (Nat.beq lhs.sizeBytes fL.byteWidth) (Nat.beq rhs.sizeBytes fL.byteWidth)) with
                | false => exact Iff.rfl
                | true =>
                  dsimp only
                  cases evalFloatBinOp op' fL lhs.bits rhs.bits with
                  | none => exact Iff.rfl
                  | some _ =>
                    dsimp only
                    exact ⟨fun ⟨_, _, h⟩ => absurd h (hres _ _ _), fun ⟨_, _, h⟩ => absurd h (hres _ _ _)⟩
    cases evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
    | ub => exact Iff.rfl
    | unsupported => exact Iff.rfl
    | ok lhsVal locals₁ =>
      dsimp only
      cases evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
      | ub => exact Iff.rfl
      | unsupported => exact Iff.rfl
      | ok rhsVal locals₂ =>
        dsimp only
        cases lhsVal with
        | scalar lhs =>
          cases rhsVal with
          | scalar rhs =>
            dsimp only
            cases hop : op with
            | offset => exact Iff.rfl
            | _ => dsimp only; rw [← hop]; exact hnon_offset op lhs rhs locals₂
          | _ => exact Iff.rfl
        | _ => exact Iff.rfl
  | cast kind op targetTy =>
    cases kind with
    | floatToFloat =>
      dsimp only
      cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
      | ub => exact Iff.rfl
      | unsupported => exact Iff.rfl
      | ok v locals' =>
        dsimp only
        cases operandTy localDecls layouts op with
        | none => exact Iff.rfl
        | some srcTy =>
          cases v with
          | scalar sc =>
            dsimp only
            cases ieeeFormatOfTy? srcTy with
            | none => exact Iff.rfl
            | some src =>
              cases ieeeFormatOfTy? targetTy with
              | none => exact Iff.rfl
              | some dst =>
                dsimp only
                cases Nat.beq sc.sizeBytes src.byteWidth with
                | false => exact Iff.rfl
                | true =>
                  dsimp only
                  by_cases hnan : isNaNBits src sc.bits = true
                  · rw [if_pos' hnan, if_pos' hnan]
                    exact ⟨fun ⟨_, _, h⟩ => absurd h (hres _ _ _), fun ⟨_, _, h⟩ => absurd h (hres _ _ _)⟩
                  · rw [if_neg' hnan, if_neg' hnan]
          | _ => exact Iff.rfl
    | _ => exact Iff.rfl
  | _ => exact Iff.rfl

/-- **`.ub` mode invariance**: `EvalRvalueFloatRel` admits `.ub` in `.deterministic` mode IF
AND ONLY IF it admits `.ub` in `.nondeterministic` mode (for EVERY `rv` and EVERY policy). -/
theorem EvalRvalueFloatRel_ub_iff
    (policy : Ptr2IntTransmutePolicy) (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    EvalRvalueFloatRel .deterministic policy locals rv mem localDecls layouts .ub ↔
      EvalRvalueFloatRel .nondeterministic policy locals rv mem localDecls layouts .ub :=
  EvalRvalueFloatRel_mode_irrelevant_of_not_ok .deterministic .nondeterministic policy locals rv
    mem localDecls layouts .ub (fun _ _ _ h => nomatch h)

/-- **`.unsupported` mode invariance**: `EvalRvalueFloatRel` admits `.unsupported` in
`.deterministic` mode IF AND ONLY IF it admits `.unsupported` in `.nondeterministic` mode
(for EVERY `rv` and EVERY policy). -/
theorem EvalRvalueFloatRel_unsupported_iff
    (policy : Ptr2IntTransmutePolicy) (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    EvalRvalueFloatRel .deterministic policy locals rv mem localDecls layouts .unsupported ↔
      EvalRvalueFloatRel .nondeterministic policy locals rv mem localDecls layouts .unsupported :=
  EvalRvalueFloatRel_mode_irrelevant_of_not_ok .deterministic .nondeterministic policy locals rv
    mem localDecls layouts .unsupported (fun _ _ _ h => nomatch h)

private theorem EvalRvalueFloatRel_floatToFloat_not_ok_iff_evalRvalue
    (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (res : RvalueEvalResult)
    (hres : ∀ v l m, res ≠ .ok v l m) :
    EvalRvalueFloatRel mode policy locals (.cast .floatToFloat op targetTy) mem localDecls layouts res ↔
      res = evalRvalue locals (.cast .floatToFloat op targetTy) mem localDecls layouts := by
  unfold EvalRvalueFloatRel evalRvalue evalFloatCastRvalue evalFloatCast
  dsimp only
  cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
  | ub => exact Iff.rfl
  | unsupported => exact Iff.rfl
  | ok v locals' =>
    dsimp only
    cases operandTy localDecls layouts op with
    | none => exact Iff.rfl
    | some srcTy =>
      cases v with
      | scalar sc =>
        dsimp only
        cases ieeeFormatOfTy? srcTy with
        | none => exact Iff.rfl
        | some src =>
          cases ieeeFormatOfTy? targetTy with
          | none => exact Iff.rfl
          | some dst =>
            dsimp only
            cases Nat.beq sc.sizeBytes src.byteWidth with
            | false => exact Iff.rfl
            | true =>
              dsimp only
              by_cases hnan : isNaNBits src sc.bits = true
              · rw [if_pos' hnan]
                exact ⟨fun ⟨_, _, h⟩ => absurd h (hres _ _ _), fun h => absurd h (hres _ _ _)⟩
              · rw [if_neg' hnan]
      | _ => exact Iff.rfl

/-- **Exactness of every non-`.ok` outcome against the executable `evalRvalue`**: for every
`rv` other than `.cast .transmute` / `.cast .subtype`, in BOTH modes and at ANY policy, a
non-`.ok` result (`.ub` or `.unsupported`) is admitted by `EvalRvalueFloatRel` IF AND ONLY IF
it is exactly the `evalRvalue` result. Unlike `EvalRvalueFloatRel_det_iff_evalRvalue`, this
also covers `.nondeterministic` mode, `.stripProvenance`, and `.cast .floatToFloat`. -/
theorem EvalRvalueFloatRel_not_ok_iff_evalRvalue
    (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (res : RvalueEvalResult)
    (hres : ∀ v l m, res ≠ .ok v l m)
    (hNotTransmute : ∀ op targetTy, rv ≠ .cast .transmute op targetTy)
    (hNotSubtype : ∀ op targetTy, rv ≠ .cast .subtype op targetTy) :
    EvalRvalueFloatRel mode policy locals rv mem localDecls layouts res ↔
      res = evalRvalue locals rv mem localDecls layouts := by
  cases rv with
  | binaryOp op lhsOp rhsOp =>
    exact (EvalRvalueFloatRel_mode_irrelevant_of_not_ok mode .deterministic policy locals
        (.binaryOp op lhsOp rhsOp) mem localDecls layouts res hres).trans
      (EvalRvalueFloatRel_det_binaryOp_iff policy locals op lhsOp rhsOp mem localDecls layouts res)
  | cast kind op targetTy =>
    cases kind with
    | floatToFloat =>
      exact EvalRvalueFloatRel_floatToFloat_not_ok_iff_evalRvalue mode policy locals op targetTy
        mem localDecls layouts res hres
    | transmute => exact absurd rfl (hNotTransmute op targetTy)
    | subtype => exact absurd rfl (hNotSubtype op targetTy)
    | _ => exact Iff.rfl
  | _ => exact Iff.rfl

/-- **`.ub` exactness**: outside byte casts, `EvalRvalueFloatRel` admits `.ub` (in either mode,
at any policy) IF AND ONLY IF `evalRvalue` returns `.ub`. -/
theorem EvalRvalueFloatRel_ub_iff_evalRvalue
    (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hNotTransmute : ∀ op targetTy, rv ≠ .cast .transmute op targetTy)
    (hNotSubtype : ∀ op targetTy, rv ≠ .cast .subtype op targetTy) :
    EvalRvalueFloatRel mode policy locals rv mem localDecls layouts .ub ↔
      evalRvalue locals rv mem localDecls layouts = .ub :=
  (EvalRvalueFloatRel_not_ok_iff_evalRvalue mode policy locals rv mem localDecls layouts .ub
    (fun _ _ _ h => nomatch h) hNotTransmute hNotSubtype).trans ⟨Eq.symm, Eq.symm⟩

/-- **`.unsupported` exactness**: outside byte casts, `EvalRvalueFloatRel` admits
`.unsupported` (in either mode, at any policy) IF AND ONLY IF `evalRvalue` returns
`.unsupported`. -/
theorem EvalRvalueFloatRel_unsupported_iff_evalRvalue
    (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hNotTransmute : ∀ op targetTy, rv ≠ .cast .transmute op targetTy)
    (hNotSubtype : ∀ op targetTy, rv ≠ .cast .subtype op targetTy) :
    EvalRvalueFloatRel mode policy locals rv mem localDecls layouts .unsupported ↔
      evalRvalue locals rv mem localDecls layouts = .unsupported :=
  (EvalRvalueFloatRel_not_ok_iff_evalRvalue mode policy locals rv mem localDecls layouts .unsupported
    (fun _ _ _ h => nomatch h) hNotTransmute hNotSubtype).trans ⟨Eq.symm, Eq.symm⟩

/-- **Universal `.nondeterministic` realization at ANY policy**: for every `rv` other than
`.cast .transmute` / `.cast .subtype`, the executable `evalRvalue` result satisfies
`EvalRvalueFloatRel .nondeterministic policy` for EVERY `policy` (generalizing
`evalRvalue_realizes_EvalRvalueFloatRel_nondet` beyond `.strictUcg630Ub`, as required by the
Miri / MiniRust default `.stripProvenance`). -/
theorem evalRvalue_realizes_EvalRvalueFloatRel_nondet_of_not_byteCast
    (policy : Ptr2IntTransmutePolicy)
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hNotTransmute : ∀ op targetTy, rv ≠ .cast .transmute op targetTy)
    (hNotSubtype : ∀ op targetTy, rv ≠ .cast .subtype op targetTy) :
    EvalRvalueFloatRel .nondeterministic policy locals rv mem localDecls layouts
      (evalRvalue locals rv mem localDecls layouts) :=
  (EvalRvalueFloatRel_policy_irrelevant .nondeterministic .strictUcg630Ub policy locals rv mem
    localDecls layouts _ hNotTransmute hNotSubtype).mp
    (evalRvalue_realizes_EvalRvalueFloatRel_nondet locals rv mem localDecls layouts)

/-- **`.deterministic` exactness at ANY policy**: for every `rv` other than
`.cast .floatToFloat`, `.cast .transmute`, and `.cast .subtype`,
`EvalRvalueFloatRel .deterministic policy` coincides exactly with `evalRvalue` for EVERY
`policy` (generalizing `EvalRvalueFloatRel_det_iff_evalRvalue` beyond `.strictUcg630Ub`). -/
theorem EvalRvalueFloatRel_det_iff_evalRvalue_of_not_byteCast
    (policy : Ptr2IntTransmutePolicy)
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (res : RvalueEvalResult)
    (hNotF2F : ∀ op targetTy, rv ≠ .cast .floatToFloat op targetTy)
    (hNotTransmute : ∀ op targetTy, rv ≠ .cast .transmute op targetTy)
    (hNotSubtype : ∀ op targetTy, rv ≠ .cast .subtype op targetTy) :
    EvalRvalueFloatRel .deterministic policy locals rv mem localDecls layouts res ↔
      res = evalRvalue locals rv mem localDecls layouts :=
  (EvalRvalueFloatRel_policy_irrelevant .deterministic policy .strictUcg630Ub locals rv mem
    localDecls layouts res hNotTransmute hNotSubtype).trans
    (EvalRvalueFloatRel_det_iff_evalRvalue locals rv mem localDecls layouts res hNotF2F)

/-- **Totality (non-vacuity) of `EvalRvalueFloatRel`**: for EVERY mode, policy, state, and
`rv`, the relation admits at least one result, so simulation statements quantifying over
admitted results are never vacuous. -/
theorem EvalRvalueFloatRel_total
    (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    ∃ res, EvalRvalueFloatRel mode policy locals rv mem localDecls layouts res := by
  cases rv with
  | binaryOp op lhsOp rhsOp =>
    have hdet := (EvalRvalueFloatRel_det_binaryOp_iff policy locals op lhsOp rhsOp mem localDecls
      layouts _).mpr rfl
    cases mode with
    | deterministic => exact ⟨_, hdet⟩
    | nondeterministic =>
      exact ⟨_, EvalRvalueFloatRel.det_imp_nondet policy locals (.binaryOp op lhsOp rhsOp) mem
        localDecls layouts _ hdet⟩
  | cast kind op targetTy =>
    cases kind with
    | floatToFloat =>
      unfold EvalRvalueFloatRel
      dsimp only
      cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
      | ub => exact ⟨_, rfl⟩
      | unsupported => exact ⟨_, rfl⟩
      | ok v locals' =>
        dsimp only
        cases operandTy localDecls layouts op with
        | none => exact ⟨_, rfl⟩
        | some srcTy =>
          cases v with
          | scalar sc =>
            dsimp only
            cases ieeeFormatOfTy? srcTy with
            | none => exact ⟨_, rfl⟩
            | some src =>
              cases ieeeFormatOfTy? targetTy with
              | none => exact ⟨_, rfl⟩
              | some dst =>
                dsimp only
                cases Nat.beq sc.sizeBytes src.byteWidth with
                | false => exact ⟨_, rfl⟩
                | true =>
                  dsimp only
                  by_cases hnan : isNaNBits src sc.bits = true
                  · exact ⟨.ok (.scalar ⟨preferredNaNBits dst, dst.byteWidth⟩) locals' mem, by
                      rw [if_pos' hnan]
                      exact ⟨preferredNaNBits dst, preferredNaNBits_mem_nanChoices dst _ mode, rfl⟩⟩
                  · exact ⟨.ok (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)
                      locals' mem, by rw [if_neg' hnan]⟩
          | _ => exact ⟨_, rfl⟩
    | _ => exact ⟨_, rfl⟩
  | _ => exact ⟨_, rfl⟩

/-- Executable evaluator realizing `EvalRvalueFloatRel .deterministic policy` EXACTLY for
every `rv` (`EvalRvalueFloatRel_det_iff_evalRvalueDet`). It coincides with `evalRvalue` except
that (1) `.cast .transmute` / `.cast .subtype` use `evalByteCast` at `policy` (rather than the
fixed `.strictUcg630Ub`), and (2) a NaN source of `.cast .floatToFloat` yields
`preferredNaNBits dst` (Miri's deterministic-float mode) instead of `evalRvalue`'s quieting
conversion. -/
def evalRvalueDet
    (policy : Ptr2IntTransmutePolicy) (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : RvalueEvalResult :=
  match rv with
  | .cast .floatToFloat op targetTy =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
    | .ub => .ub
    | .unsupported => .unsupported
    | .ok v locals' =>
      match operandTy localDecls layouts op, v with
      | .some srcTy, .scalar sc =>
        match ieeeFormatOfTy? srcTy, ieeeFormatOfTy? targetTy with
        | .some src, .some dst =>
          match Nat.beq sc.sizeBytes src.byteWidth with
          | true =>
            match isNaNBits src sc.bits with
            | true => .ok (.scalar ⟨preferredNaNBits dst, dst.byteWidth⟩) locals' mem
            | false =>
              .ok (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩) locals' mem
          | false => .unsupported
        | _, _ => .unsupported
      | _, _ => .unsupported
  | .cast .transmute op targetTy => evalByteCast locals op targetTy mem localDecls layouts policy
  | .cast .subtype op targetTy => evalByteCast locals op targetTy mem localDecls layouts policy
  | _ => evalRvalue locals rv mem localDecls layouts

/-- **Exact executable characterization of `.deterministic` mode** (EVERY `rv`, EVERY policy):
`EvalRvalueFloatRel .deterministic policy` admits `res` IF AND ONLY IF
`res = evalRvalueDet policy ...`. Unlike `EvalRvalueFloatRel_det_iff_evalRvalue`, there is no
side condition: NaN-input `.cast .floatToFloat` and `.stripProvenance` byte casts are covered. -/
theorem EvalRvalueFloatRel_det_iff_evalRvalueDet
    (policy : Ptr2IntTransmutePolicy)
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (res : RvalueEvalResult) :
    EvalRvalueFloatRel .deterministic policy locals rv mem localDecls layouts res ↔
      res = evalRvalueDet policy locals rv mem localDecls layouts := by
  cases rv with
  | binaryOp op lhsOp rhsOp =>
    exact EvalRvalueFloatRel_det_binaryOp_iff policy locals op lhsOp rhsOp mem localDecls layouts res
  | cast kind op targetTy =>
    cases kind with
    | floatToFloat =>
      unfold EvalRvalueFloatRel evalRvalueDet
      dsimp only
      cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
      | ub => exact Iff.rfl
      | unsupported => exact Iff.rfl
      | ok v locals' =>
        dsimp only
        cases operandTy localDecls layouts op with
        | none => exact Iff.rfl
        | some srcTy =>
          cases v with
          | scalar sc =>
            dsimp only
            cases ieeeFormatOfTy? srcTy with
            | none => exact Iff.rfl
            | some src =>
              cases ieeeFormatOfTy? targetTy with
              | none => exact Iff.rfl
              | some dst =>
                dsimp only
                cases Nat.beq sc.sizeBytes src.byteWidth with
                | false => exact Iff.rfl
                | true =>
                  dsimp only
                  cases isNaNBits src sc.bits with
                  | true =>
                    dsimp only
                    rw [if_pos' rfl]
                    unfold nanChoices
                    constructor
                    · rintro ⟨cand, hc, hr⟩
                      rcases List.mem_cons.mp hc with rfl | hnil
                      · exact hr
                      · cases hnil
                    · intro h
                      exact ⟨preferredNaNBits dst, List.mem_cons_self, h⟩
                  | false =>
                    dsimp only
                    rw [if_neg' Bool.false_ne_true]
          | _ => exact Iff.rfl
    | _ => exact Iff.rfl
  | _ => exact Iff.rfl

/-- **Functionality of `.deterministic` mode**: for EVERY policy, state, and `rv`,
`EvalRvalueFloatRel .deterministic` admits at most one result (together with
`EvalRvalueFloatRel_total`, exactly one: `evalRvalueDet`). -/
theorem EvalRvalueFloatRel_det_functional
    (policy : Ptr2IntTransmutePolicy)
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (res₁ res₂ : RvalueEvalResult)
    (h₁ : EvalRvalueFloatRel .deterministic policy locals rv mem localDecls layouts res₁)
    (h₂ : EvalRvalueFloatRel .deterministic policy locals rv mem localDecls layouts res₂) :
    res₁ = res₂ :=
  ((EvalRvalueFloatRel_det_iff_evalRvalueDet policy locals rv mem localDecls layouts res₁).mp h₁).trans
    ((EvalRvalueFloatRel_det_iff_evalRvalueDet policy locals rv mem localDecls layouts res₂).mp h₂).symm

/-- `evalRvalueDet .strictUcg630Ub` coincides with `evalRvalue` on every `rv` other than
`.cast .floatToFloat` (where the two differ exactly on NaN sources, see
`evalRvalue_floatToFloat_nan_rel_separation_witness`). -/
theorem evalRvalueDet_strict_eq_evalRvalue
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hNotF2F : ∀ op targetTy, rv ≠ .cast .floatToFloat op targetTy) :
    evalRvalueDet .strictUcg630Ub locals rv mem localDecls layouts =
      evalRvalue locals rv mem localDecls layouts := by
  cases rv with
  | cast kind op targetTy =>
    cases kind with
    | floatToFloat => exact absurd rfl (hNotF2F op targetTy)
    | _ => rfl
  | _ => rfl

/-- `evalRvalueDet policy` does not depend on `policy` outside byte casts, where it coincides
with `evalRvalue` on every `rv` other than `.cast .floatToFloat`. -/
theorem evalRvalueDet_eq_evalRvalue_of_not_byteCast
    (policy : Ptr2IntTransmutePolicy)
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hNotF2F : ∀ op targetTy, rv ≠ .cast .floatToFloat op targetTy)
    (hNotTransmute : ∀ op targetTy, rv ≠ .cast .transmute op targetTy)
    (hNotSubtype : ∀ op targetTy, rv ≠ .cast .subtype op targetTy) :
    evalRvalueDet policy locals rv mem localDecls layouts =
      evalRvalue locals rv mem localDecls layouts := by
  cases rv with
  | cast kind op targetTy =>
    cases kind with
    | floatToFloat => exact absurd rfl (hNotF2F op targetTy)
    | transmute => exact absurd rfl (hNotTransmute op targetTy)
    | subtype => exact absurd rfl (hNotSubtype op targetTy)
    | _ => rfl
  | _ => rfl

/-- **Generic-mode float `.binaryOp` dispatcher** (BOTH modes, ANY policy): when both operands
evaluate to scalars of the same modeled IEEE-754 format `f` (read through `evalOperand` from
constants, locals, caller locals, globals, or memory, with `locals₂` threading any moves),
`EvalRvalueFloatRel` admits EXACTLY the `.ok` results carrying an `EvalFloatBinOpRel mode`
output, or `.unsupported` when `op` is not a float `BinOp`. Float binary operations never
admit `.ub`. -/
theorem EvalRvalueFloatRel_binaryOp_float_iff
    (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (locals locals₁ locals₂ : List LocalSlot) (op : BinOp) (lhsOp rhsOp : Operand)
    (lhs rhs : ScalarInt) (lTy rTy : Ty) (f : IeeeFormat)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) (res : RvalueEvalResult)
    (hnotOff : op ≠ .offset)
    (hl : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar lhs) locals₁)
    (hr : evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar rhs) locals₂)
    (hlTy : operandTy localDecls layouts lhsOp = .some lTy)
    (hrTy : operandTy localDecls layouts rhsOp = .some rTy)
    (hlf : ieeeFormatOfTy? lTy = .some f)
    (hrf : ieeeFormatOfTy? rTy = .some f)
    (hlsz : lhs.sizeBytes = f.byteWidth)
    (hrsz : rhs.sizeBytes = f.byteWidth) :
    EvalRvalueFloatRel mode policy locals (.binaryOp op lhsOp rhsOp) mem localDecls layouts res ↔
      ((∃ outSc, EvalFloatBinOpRel mode op f lhs.bits rhs.bits outSc ∧
          res = .ok (.scalar outSc) locals₂ mem) ∨
        (isFloatBinOp op = false ∧ res = .unsupported)) := by
  have hfloatL : isFloatOptTy (.some lTy) = true := by
    unfold isFloatOptTy isFloatTy
    unfold ieeeFormatOfTy? at hlf
    cases hlk : lTy.kind with
    | float _ => dsimp only; rw [hlk]
    | _ => rw [hlk] at hlf; cases hlf
  have hcore : ∀ op' : BinOp,
      (match evalFloatBinOp op' f lhs.bits rhs.bits with
       | .some _ =>
         ∃ outSc, EvalFloatBinOpRel mode op' f lhs.bits rhs.bits outSc ∧
           res = .ok (.scalar outSc) locals₂ mem
       | .none => res = .unsupported) ↔
      ((∃ outSc, EvalFloatBinOpRel mode op' f lhs.bits rhs.bits outSc ∧
          res = .ok (.scalar outSc) locals₂ mem) ∨
        (isFloatBinOp op' = false ∧ res = .unsupported)) := by
    intro op'
    cases hbin : evalFloatBinOp op' f lhs.bits rhs.bits with
    | none =>
      dsimp only
      have hnone := (evalFloatBinOp_eq_none_iff op' f lhs.bits rhs.bits).mp hbin
      constructor
      · intro h; exact Or.inr ⟨hnone, h⟩
      · rintro (⟨outSc, hrel, _⟩ | ⟨_, h⟩)
        · exact absurd hrel ((EvalFloatBinOpRel_none_iff mode op' f lhs.bits rhs.bits).mpr hbin outSc)
        · exact h
    | some x =>
      dsimp only
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨hf, _⟩)
        · exact h
        · have hnone := (evalFloatBinOp_eq_none_iff op' f lhs.bits rhs.bits).mpr hf
          rw [hbin] at hnone
          cases hnone
  have hfmt : ∀ op' : BinOp,
      (match Bool.or (isFloatOptTy (operandTy localDecls layouts lhsOp))
          (isFloatOptTy (operandTy localDecls layouts rhsOp)) with
       | true =>
         match operandTy localDecls layouts lhsOp, operandTy localDecls layouts rhsOp with
         | .some lTy, .some rTy =>
           match ieeeFormatOfTy? lTy, ieeeFormatOfTy? rTy with
           | .some fL, .some fR =>
             match Bool.and
                 (match fL, fR with | .binary32, .binary32 => true | .binary64, .binary64 => true | _, _ => false)
                 (Bool.and (Nat.beq lhs.sizeBytes fL.byteWidth) (Nat.beq rhs.sizeBytes fL.byteWidth)) with
             | true =>
               match evalFloatBinOp op' fL lhs.bits rhs.bits with
               | .some _ =>
                 ∃ outSc,
                   EvalFloatBinOpRel mode op' fL lhs.bits rhs.bits outSc ∧
                   res = .ok (.scalar outSc) locals₂ mem
               | .none => res = .unsupported
             | false => res = .unsupported
           | _, _ => res = .unsupported
         | _, _ => res = .unsupported
       | false => res = evalScalarBinOp op' lhs rhs locals₂ mem (operandIsSigned localDecls lhsOp layouts)) ↔
      ((∃ outSc, EvalFloatBinOpRel mode op' f lhs.bits rhs.bits outSc ∧
          res = .ok (.scalar outSc) locals₂ mem) ∨
        (isFloatBinOp op' = false ∧ res = .unsupported)) := by
    intro op'
    rw [hlTy, hrTy, hfloatL, Bool.true_or]
    dsimp only
    rw [hlf, hrf]
    dsimp only
    rw [hlsz, hrsz, Nat.beq_refl]
    cases f with
    | binary32 => exact hcore op'
    | binary64 => exact hcore op'
  unfold EvalRvalueFloatRel
  dsimp only
  rw [hl]
  dsimp only
  rw [hr]
  dsimp only
  cases hop : op with
  | offset => exact absurd hop hnotOff
  | _ => dsimp only; rw [← hop]; exact hfmt op

/-- **Generic-mode NaN-input `.cast .floatToFloat` dispatcher** (BOTH modes, ANY policy): on a
NaN source scalar of modeled format `src` cast to modeled format `dst`, `EvalRvalueFloatRel`
admits EXACTLY the `.ok` results carrying a candidate of
`nanChoices dst [(src, sc.bits % 2 ^ src.width)] mode` (complementing the non-NaN law
`EvalRvalueFloatRel_floatToFloat_of_not_nan`). -/
theorem EvalRvalueFloatRel_floatToFloat_nan_iff
    (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy)
    (locals locals' : List LocalSlot) (op : Operand) (targetTy srcTy : Ty)
    (sc : ScalarInt) (src dst : IeeeFormat)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) (res : RvalueEvalResult)
    (hop : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok (.scalar sc) locals')
    (hty : operandTy localDecls layouts op = .some srcTy)
    (hsrc : ieeeFormatOfTy? srcTy = .some src)
    (hdst : ieeeFormatOfTy? targetTy = .some dst)
    (hsz : sc.sizeBytes = src.byteWidth)
    (hnan : isNaNBits src sc.bits = true) :
    EvalRvalueFloatRel mode policy locals (.cast .floatToFloat op targetTy) mem localDecls layouts res ↔
      ∃ cand,
        cand ∈ nanChoices dst [(src, sc.bits % 2 ^ src.width)] mode ∧
        res = .ok (.scalar ⟨cand, dst.byteWidth⟩) locals' mem := by
  unfold EvalRvalueFloatRel
  dsimp only
  rw [hop]
  dsimp only
  rw [hty]
  dsimp only
  rw [hsrc, hdst]
  dsimp only
  rw [hsz, Nat.beq_refl]
  dsimp only
  rw [if_pos' hnan]

/-! ### `Ptr2IntTransmutePolicy` at the `EvalRvalueFloatRel` level & type-generic composite bridges

The laws below hold uniformly for EVERY target type (scalars, floats, structs, tuples, arrays,
niche and tagged enums, unions): they are stated over arbitrary `Ty` / `Operand` and lift the
§5 refinement, exact split, and provenance-free equivalence to the decoders and to
`EvalRvalueFloatRel` itself. -/

/-- **Decoder-level exact split (`decodeTypedValueFromBytes`, every type)**: either both
policies decode identically, or `.strictUcg630Ub` rejects (`.none`). -/
theorem decodeTypedValueFromBytes_strip_eq_strict_or_strict_none
    (fuel : Nat) (layouts : LayoutTable) (ty : Ty) (bytes : List AbstractByte) :
    decodeTypedValueFromBytes fuel layouts ty bytes .stripProvenance =
      decodeTypedValueFromBytes fuel layouts ty bytes .strictUcg630Ub ∨
    decodeTypedValueFromBytes fuel layouts ty bytes .strictUcg630Ub = .none := by
  cases h : decodeTypedValueFromBytes fuel layouts ty bytes .strictUcg630Ub with
  | none => exact Or.inr rfl
  | some v =>
    exact Or.inl
      (decodeTypedValueFromBytes_strictUcg630Ub_refines_stripProvenance fuel layouts ty bytes v h)

/-- **Decoder-level exact split (`decodeTypedValueRichWithPolicy`, every type)**. -/
theorem decodeTypedValueRichWithPolicy_strip_eq_strict_or_strict_none
    (fuel : Nat) (layouts : LayoutTable) (richSpecs : List (DefPath × RichAdtSpec))
    (ty : Ty) (bytes : List AbstractByte) :
    decodeTypedValueRichWithPolicy fuel layouts richSpecs ty bytes .stripProvenance =
      decodeTypedValueRichWithPolicy fuel layouts richSpecs ty bytes .strictUcg630Ub ∨
    decodeTypedValueRichWithPolicy fuel layouts richSpecs ty bytes .strictUcg630Ub = .none := by
  cases h : decodeTypedValueRichWithPolicy fuel layouts richSpecs ty bytes .strictUcg630Ub with
  | none => exact Or.inr rfl
  | some v =>
    exact Or.inl
      (decodeTypedValueRichWithPolicy_strictUcg630Ub_refines_stripProvenance fuel layouts richSpecs
        ty bytes v h)

/-- **Policies can only differ on provenance-carrying bytes (`decodeTypedValueFromBytes`, every
type)**: whenever the two policies decode `bytes` differently, some byte of `bytes` carries
pointer provenance. -/
theorem decodeTypedValueFromBytes_policy_differs_imp_haveProv
    (fuel : Nat) (layouts : LayoutTable) (ty : Ty) (bytes : List AbstractByte)
    (h : decodeTypedValueFromBytes fuel layouts ty bytes .strictUcg630Ub ≠
      decodeTypedValueFromBytes fuel layouts ty bytes .stripProvenance) :
    abstractBytesHaveProv bytes = true := by
  cases hp : abstractBytesHaveProv bytes with
  | true => rfl
  | false => exact absurd (decodeTypedValueFromBytes_eq_of_provFree fuel layouts ty bytes hp) h

/-- **Policies can only differ on provenance-carrying bytes (`decodeTypedValueRichWithPolicy`,
every type)**. -/
theorem decodeTypedValueRichWithPolicy_policy_differs_imp_haveProv
    (fuel : Nat) (layouts : LayoutTable) (richSpecs : List (DefPath × RichAdtSpec))
    (ty : Ty) (bytes : List AbstractByte)
    (h : decodeTypedValueRichWithPolicy fuel layouts richSpecs ty bytes .strictUcg630Ub ≠
      decodeTypedValueRichWithPolicy fuel layouts richSpecs ty bytes .stripProvenance) :
    abstractBytesHaveProv bytes = true := by
  cases hp : abstractBytesHaveProv bytes with
  | true => rfl
  | false =>
    exact absurd (decodeTypedValueRichWithPolicy_eq_of_provFree fuel layouts richSpecs ty bytes hp) h

/-- **`evalByteCast` policies differ only as `.strictUcg630Ub = .ub` on a provenance-carrying
source (every source and target type)**: whenever the two policies evaluate a byte cast
differently, `.strictUcg630Ub` returns `.ub` and the evaluated source value carries pointer
provenance (`valueHasProv v = true`). -/
theorem evalByteCast_policy_differs_imp
    (locals locals' : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) (v : Value)
    (hop : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok v locals')
    (h : evalByteCast locals op targetTy mem localDecls layouts .strictUcg630Ub ≠
      evalByteCast locals op targetTy mem localDecls layouts .stripProvenance) :
    evalByteCast locals op targetTy mem localDecls layouts .strictUcg630Ub = .ub ∧
    valueHasProv v = true := by
  constructor
  · rcases evalByteCast_strip_eq_strict_or_strict_ub locals op targetTy mem localDecls layouts with
      heq | hub
    · exact absurd heq.symm h
    · exact hub
  · cases hp : valueHasProv v with
    | true => rfl
    | false =>
      exact absurd
        (evalByteCast_eq_of_provFree locals locals' op targetTy mem localDecls layouts v hop hp) h

/-- **Relation-level refinement on byte casts (both modes)**: every `.ok` result admitted by
`EvalRvalueFloatRel mode .strictUcg630Ub` on `.cast .transmute` / `.cast .subtype` is admitted
identically by `EvalRvalueFloatRel mode .stripProvenance`. -/
theorem EvalRvalueFloatRel_byteCast_strict_refines_strip
    (mode : FloatArithMode) (locals locals' : List LocalSlot) (kind : CastKind) (op : Operand)
    (targetTy : Ty) (mem mem' : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (v : Value) (hkind : kind = .transmute ∨ kind = .subtype)
    (h : EvalRvalueFloatRel mode .strictUcg630Ub locals (.cast kind op targetTy) mem localDecls layouts
      (.ok v locals' mem')) :
    EvalRvalueFloatRel mode .stripProvenance locals (.cast kind op targetTy) mem localDecls layouts
      (.ok v locals' mem') := by
  have hs := (EvalRvalueFloatRel_byteCast_iff mode .strictUcg630Ub locals kind op targetTy mem
    localDecls layouts _ hkind).mp h
  exact (EvalRvalueFloatRel_byteCast_iff mode .stripProvenance locals kind op targetTy mem
    localDecls layouts _ hkind).mpr
    (evalByteCast_strictUcg630Ub_refines_stripProvenance locals locals' op targetTy mem mem'
      localDecls layouts v hs.symm).symm

/-- **Relation-level exact split on byte casts (both modes)**: every result admitted by
`EvalRvalueFloatRel mode .stripProvenance` on `.cast .transmute` / `.cast .subtype` is either
admitted identically under `.strictUcg630Ub`, or `.strictUcg630Ub` admits `.ub`. -/
theorem EvalRvalueFloatRel_byteCast_strip_split
    (mode : FloatArithMode) (locals : List LocalSlot) (kind : CastKind) (op : Operand)
    (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (res : RvalueEvalResult) (hkind : kind = .transmute ∨ kind = .subtype)
    (h : EvalRvalueFloatRel mode .stripProvenance locals (.cast kind op targetTy) mem localDecls layouts res) :
    EvalRvalueFloatRel mode .strictUcg630Ub locals (.cast kind op targetTy) mem localDecls layouts res ∨
    EvalRvalueFloatRel mode .strictUcg630Ub locals (.cast kind op targetTy) mem localDecls layouts .ub := by
  have hs := (EvalRvalueFloatRel_byteCast_iff mode .stripProvenance locals kind op targetTy mem
    localDecls layouts _ hkind).mp h
  rcases evalByteCast_strip_eq_strict_or_strict_ub locals op targetTy mem localDecls layouts with
    heq | hub
  · exact Or.inl ((EvalRvalueFloatRel_byteCast_iff mode .strictUcg630Ub locals kind op targetTy mem
      localDecls layouts _ hkind).mpr (hs.trans heq))
  · exact Or.inr ((EvalRvalueFloatRel_byteCast_iff mode .strictUcg630Ub locals kind op targetTy mem
      localDecls layouts _ hkind).mpr hub.symm)

/-- **Relation-level provenance-free equivalence on byte casts (both modes)**: when the source
operand evaluates to a provenance-free `Value`, `EvalRvalueFloatRel` on `.cast .transmute` /
`.cast .subtype` does not depend on the `Ptr2IntTransmutePolicy` (for every source and target
type, including composites). -/
theorem EvalRvalueFloatRel_byteCast_policy_irrelevant_of_provFree
    (mode : FloatArithMode) (policy₁ policy₂ : Ptr2IntTransmutePolicy)
    (locals locals' : List LocalSlot) (kind : CastKind) (op : Operand)
    (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (v : Value) (res : RvalueEvalResult) (hkind : kind = .transmute ∨ kind = .subtype)
    (hop : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack =
      .ok v locals')
    (hv : valueHasProv v = false) :
    EvalRvalueFloatRel mode policy₁ locals (.cast kind op targetTy) mem localDecls layouts res ↔
      EvalRvalueFloatRel mode policy₂ locals (.cast kind op targetTy) mem localDecls layouts res := by
  have heq := evalByteCast_eq_of_provFree locals locals' op targetTy mem localDecls layouts v hop hv
  have hall : evalByteCast locals op targetTy mem localDecls layouts policy₁ =
      evalByteCast locals op targetTy mem localDecls layouts policy₂ := by
    cases policy₁ <;> cases policy₂
    · rfl
    · exact heq
    · exact heq.symm
    · rfl
  exact (EvalRvalueFloatRel_byteCast_iff mode policy₁ locals kind op targetTy mem localDecls
      layouts res hkind).trans
    (Iff.trans ⟨fun h => h.trans hall, fun h => h.trans hall.symm⟩
      (EvalRvalueFloatRel_byteCast_iff mode policy₂ locals kind op targetTy mem localDecls
        layouts res hkind).symm)

/-! ### Concrete Episode 2 witnesses: operands from locals, NaN choices, & `Ptr2IntTransmutePolicy` separation -/

/-- `copy _i` operand for concrete witnesses. -/
private abbrev b2Copy (i : Nat) : Operand := .copy ⟨i, .nil⟩

/-- `move _i` operand for concrete witnesses. -/
private abbrev b2Move (i : Nat) : Operand := .move ⟨i, .nil⟩

/-- Two `f32` local declarations (`_0 : f32`, `_1 : f32`). -/
private abbrev b2F32Decls : List LocalDecl := [⟨.not, f32Ty, .none⟩, ⟨.not, f32Ty, .none⟩]

/-- Primitive scalar `TypeLayout` of `bytes` bytes for concrete witnesses. -/
private def b2PrimLayout (bytes : Nat) (pk : PrimitiveKind) (maxVal : Nat) : TypeLayout :=
  { size := ⟨bytes⟩, align := ⟨bytes⟩, backendRepr := .scalar (.initialized pk ⟨0, maxVal⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- 16-byte two-field aggregate `TypeLayout` (fields at byte offsets `0` and `8`) whose fields
have layout indices `fl0` and `fl1`. -/
private def b2PairLayout (fl0 fl1 : Nat) : TypeLayout :=
  { size := ⟨16⟩, align := ⟨8⟩, backendRepr := .memory, fields := .arbitrary [⟨0⟩, ⟨8⟩] [0, 1],
    variants := .single 0, isUninhabited := false, fieldLayouts := [fl0, fl1] }

/-- 64-bit `LayoutTable` for concrete witnesses: `0 ↦ ()`, `1 ↦ f32`, `2 ↦ f64`, `3 ↦ u64`,
`4 ↦ *const u8`, `5 ↦ u8`, `6 ↦ (*const u8, u64)`, `7 ↦ (u64, u64)`,
`8 ↦ struct S { a: u8, b: u64 }` (7 padding bytes at offsets `1..8`),
`9 ↦ struct P { p: *const u8, q: *const u8 }`, `10 ↦ union U { p: *const u8, n: u64 }`. -/
private def b2Layouts : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries :=
      [ { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory, fields := .arbitrary [] [],
          variants := .single 0, isUninhabited := false },
        b2PrimLayout 4 (.float 32) 0xFFFFFFFF,
        b2PrimLayout 8 (.float 64) 0xFFFFFFFFFFFFFFFF,
        b2PrimLayout 8 (.int 64 false) 0xFFFFFFFFFFFFFFFF,
        b2PrimLayout 8 (.pointer 0) 0xFFFFFFFFFFFFFFFF,
        b2PrimLayout 1 (.int 8 false) 0xFF,
        b2PairLayout 4 3,
        b2PairLayout 3 3,
        b2PairLayout 5 3,
        b2PairLayout 4 4,
        { size := ⟨8⟩, align := ⟨8⟩, backendRepr := .memory, fields := .union 2,
          variants := .single 0, isUninhabited := false, fieldLayouts := [4, 3] } ] }

private abbrev b2U32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
private abbrev b2UsizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
private abbrev b2PtrTy : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 0 }
private abbrev b2PtrArrTy : Ty := { kind := .array (.rawPtr .not (.uint .u8)) 2, layoutIdx := 0 }
private abbrev b2UsizeArrTy : Ty := { kind := .array (.uint .usize) 2, layoutIdx := 0 }
private abbrev b2F32T : Ty := { kind := .float .f32, layoutIdx := 1 }
private abbrev b2F64T : Ty := { kind := .float .f64, layoutIdx := 2 }
private abbrev b2U64T : Ty := { kind := .uint .u64, layoutIdx := 3 }
private abbrev b2PtrT : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 4 }
private abbrev b2PtrU64TupT : Ty :=
  { kind := .tuple [.rawPtr .not (.uint .u8), .uint .u64], layoutIdx := 6 }
private abbrev b2U64PairTupT : Ty := { kind := .tuple [.uint .u64, .uint .u64], layoutIdx := 7 }
private abbrev b2PadStructT : Ty := { kind := .adt "S" .nil, layoutIdx := 8 }
private abbrev b2PtrPairStructT : Ty := { kind := .adt "P" .nil, layoutIdx := 9 }
private abbrev b2UnionT : Ty := { kind := .adt "U" .nil, layoutIdx := 10 }

/-- Pointer value `(alloc 7) + 0x1000` for concrete witnesses. -/
private abbrev b2PtrA : Value := .ptr { allocId := 7, offsetBytes := 0x1000 } 8

/-- **Float operands read from locals through `evalOperand`** (not only typed constants):
with `localDecls` resolving `_0, _1 : f32`, `evalRvalue` evaluates `1.0 + 2.0 = 3.0`
(threading the `move` of `_1` into the resulting locals), `-(1.0) = -1.0`, and `1.0 < 2.0`
with IEEE-754 semantics.

**Hazard pin (documented type-directed dispatch)**: with `localDecls := .nil` the same locals
are NOT recognized as floats and follow the INTEGER path (`0x3F800000 + 0x40000000 =
0x7F800000`, two's-complement negation `0xC0800000`). Episode 2 simulations must therefore
supply `localDecls` resolving the static type of every float operand. -/
theorem evalRvalue_float_operands_from_locals_witness :
    let locals : List LocalSlot := [.init (.scalar ⟨0x3F800000, 4⟩), .init (.scalar ⟨0x40000000, 4⟩)]
    evalRvalue locals (.binaryOp .add (b2Copy 0) (b2Move 1)) emptyMemory b2F32Decls emptyLayoutTable =
      .ok (.scalar ⟨0x40400000, 4⟩) [.init (.scalar ⟨0x3F800000, 4⟩), .uninit] emptyMemory ∧
    evalRvalue locals (.unaryOp .neg (b2Copy 0)) emptyMemory b2F32Decls emptyLayoutTable =
      .ok (.scalar ⟨0xBF800000, 4⟩) locals emptyMemory ∧
    evalRvalue locals (.binaryOp .lt (b2Copy 0) (b2Copy 1)) emptyMemory b2F32Decls emptyLayoutTable =
      .ok (.scalar (boolToScalar true)) locals emptyMemory ∧
    evalRvalue locals (.binaryOp .add (b2Copy 0) (b2Copy 1)) emptyMemory .nil emptyLayoutTable =
      .ok (.scalar ⟨0x7F800000, 4⟩) locals emptyMemory ∧
    evalRvalue locals (.unaryOp .neg (b2Copy 0)) emptyMemory .nil emptyLayoutTable =
      .ok (.scalar ⟨0xC0800000, 4⟩) locals emptyMemory := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **NaN operands read from locals: exact admissible result sets in both modes** (at any
policy). For `_0 + move _1` with `_0 = sNaN 0x7FA00001_f32` and `_1 = 1.0_f32`:
- `evalRvalue` returns the preferred NaN `0x7FC00000` and marks `_1` as moved-out;
- `EvalRvalueFloatRel .nondeterministic` admits `.ok` EXACTLY for the six NaNs
  `±preferred`, `±quieted input (0x7FE00001)`, `±unchanged signaling input (0x7FA00001)`;
- `EvalRvalueFloatRel .deterministic` admits `.ok` EXACTLY for the preferred NaN;
- neither mode admits `.ub` or `.unsupported`. -/
theorem EvalRvalueFloatRel_nan_operands_from_locals_witness :
    let locals : List LocalSlot := [.init (.scalar ⟨0x7FA00001, 4⟩), .init (.scalar ⟨0x3F800000, 4⟩)]
    let locals₂ : List LocalSlot := [.init (.scalar ⟨0x7FA00001, 4⟩), .uninit]
    let rv : Rvalue := .binaryOp .add (b2Copy 0) (b2Move 1)
    evalRvalue locals rv emptyMemory b2F32Decls emptyLayoutTable =
      .ok (.scalar ⟨0x7FC00000, 4⟩) locals₂ emptyMemory ∧
    (∀ policy bits,
      EvalRvalueFloatRel .nondeterministic policy locals rv emptyMemory b2F32Decls emptyLayoutTable
          (.ok (.scalar ⟨bits, 4⟩) locals₂ emptyMemory) ↔
        bits ∈ [0x7FC00000, 0xFFC00000, 0x7FE00001, 0xFFE00001, 0x7FA00001, 0xFFA00001]) ∧
    (∀ policy bits,
      EvalRvalueFloatRel .deterministic policy locals rv emptyMemory b2F32Decls emptyLayoutTable
          (.ok (.scalar ⟨bits, 4⟩) locals₂ emptyMemory) ↔
        bits = 0x7FC00000) ∧
    (∀ mode policy,
      ¬ EvalRvalueFloatRel mode policy locals rv emptyMemory b2F32Decls emptyLayoutTable .ub ∧
      ¬ EvalRvalueFloatRel mode policy locals rv emptyMemory b2F32Decls emptyLayoutTable .unsupported) := by
  dsimp only
  have hdisp := fun (mode : FloatArithMode) (policy : Ptr2IntTransmutePolicy) (res : RvalueEvalResult) =>
    EvalRvalueFloatRel_binaryOp_float_iff mode policy
      [.init (.scalar ⟨0x7FA00001, 4⟩), .init (.scalar ⟨0x3F800000, 4⟩)]
      [.init (.scalar ⟨0x7FA00001, 4⟩), .init (.scalar ⟨0x3F800000, 4⟩)]
      [.init (.scalar ⟨0x7FA00001, 4⟩), .uninit]
      .add (b2Copy 0) (b2Move 1) ⟨0x7FA00001, 4⟩ ⟨0x3F800000, 4⟩ f32Ty f32Ty .binary32
      emptyMemory b2F32Decls emptyLayoutTable res (fun h => nomatch h) rfl rfl rfl rfl rfl rfl rfl rfl
  have hcmp : evalFloatCmp .add .binary32 0x7FA00001 0x3F800000 = .none := rfl
  have harith : evalFloatArithBase .add .binary32 0x7FA00001 0x3F800000 = .some 0x7FC00000 := by
    decide +kernel
  have hnanb : isNaNBits .binary32 0x7FC00000 = true := by decide +kernel
  have hchN : nanChoices .binary32
      [(.binary32, 0x7FA00001 % 2 ^ IeeeFormat.binary32.width),
       (.binary32, 0x3F800000 % 2 ^ IeeeFormat.binary32.width)] .nondeterministic =
      [0x7FC00000, 0xFFC00000, 0x7FE00001, 0xFFE00001, 0x7FA00001, 0xFFA00001] := by decide +kernel
  have hchD : nanChoices .binary32
      [(.binary32, 0x7FA00001 % 2 ^ IeeeFormat.binary32.width),
       (.binary32, 0x3F800000 % 2 ^ IeeeFormat.binary32.width)] .deterministic =
      [0x7FC00000] := by decide +kernel
  have hrel : ∀ (mode : FloatArithMode) (out : ScalarInt),
      EvalFloatBinOpRel mode .add .binary32 0x7FA00001 0x3F800000 out ↔
        ∃ cand,
          cand ∈ nanChoices .binary32
            [(.binary32, 0x7FA00001 % 2 ^ IeeeFormat.binary32.width),
             (.binary32, 0x3F800000 % 2 ^ IeeeFormat.binary32.width)] mode ∧
          out = ⟨cand, IeeeFormat.binary32.byteWidth⟩ := by
    intro mode out
    unfold EvalFloatBinOpRel
    rw [hcmp]
    dsimp only
    rw [harith]
    dsimp only
    rw [if_pos' hnanb]
  have hrelN : ∀ out : ScalarInt,
      EvalFloatBinOpRel .nondeterministic .add .binary32 0x7FA00001 0x3F800000 out ↔
        ∃ cand, cand ∈ [0x7FC00000, 0xFFC00000, 0x7FE00001, 0xFFE00001, 0x7FA00001, 0xFFA00001] ∧
          out = ⟨cand, IeeeFormat.binary32.byteWidth⟩ := by
    intro out
    rw [← hchN]
    exact hrel .nondeterministic out
  have hrelD : ∀ out : ScalarInt,
      EvalFloatBinOpRel .deterministic .add .binary32 0x7FA00001 0x3F800000 out ↔
        ∃ cand, cand ∈ [0x7FC00000] ∧ out = ⟨cand, IeeeFormat.binary32.byteWidth⟩ := by
    intro out
    rw [← hchD]
    exact hrel .deterministic out
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro policy bits
    refine (hdisp .nondeterministic policy _).trans ⟨?_, ?_⟩
    · rintro (⟨outSc, hrel, hres⟩ | ⟨hf, _⟩)
      · obtain ⟨cand, hmem, hout⟩ := (hrelN outSc).mp hrel
        injection hres with hval _ _
        injection hval with hsc
        rw [← hsc] at hout
        injection hout with hb _
        rw [hb]
        exact hmem
      · cases hf
    · intro hmem
      exact Or.inl ⟨⟨bits, 4⟩, (hrelN _).mpr ⟨bits, hmem, rfl⟩, rfl⟩
  · intro policy bits
    refine (hdisp .deterministic policy _).trans ⟨?_, ?_⟩
    · rintro (⟨outSc, hrel, hres⟩ | ⟨hf, _⟩)
      · obtain ⟨cand, hmem, hout⟩ := (hrelD outSc).mp hrel
        injection hres with hval _ _
        injection hval with hsc
        rw [← hsc] at hout
        injection hout with hb _
        rcases List.mem_cons.mp hmem with rfl | hnil
        · exact hb
        · cases hnil
      · cases hf
    · intro hb
      exact Or.inl ⟨⟨bits, 4⟩, (hrelD _).mpr ⟨bits, by rw [hb]; exact List.mem_cons_self, rfl⟩, rfl⟩
  · intro mode policy
    constructor
    · intro h
      rcases (hdisp mode policy .ub).mp h with ⟨_, _, hres⟩ | ⟨hf, _⟩
      · cases hres
      · cases hf
    · intro h
      rcases (hdisp mode policy .unsupported).mp h with ⟨_, _, hres⟩ | ⟨hf, _⟩
      · cases hres
      · cases hf

/-- **Pointer-to-integer transmute: policy separation at every level** (`*const u8 → usize`
on a pointer with provenance):
- `evalRvalue` (always `.strictUcg630Ub`) and `evalByteCast .strictUcg630Ub` return `.ub`;
- `evalByteCast .stripProvenance` returns the provenance-less address `0x1000`;
- in BOTH modes, `EvalRvalueFloatRel _ .strictUcg630Ub` admits exactly `.ub` and
  `EvalRvalueFloatRel _ .stripProvenance` admits exactly `.ok 0x1000`;
- consequently the `evalRvalue` result does NOT satisfy `EvalRvalueFloatRel _ .stripProvenance`:
  the byte-cast side conditions of `evalRvalue_realizes_EvalRvalueFloatRel_nondet_of_not_byteCast`
  and `EvalRvalueFloatRel_policy_irrelevant` are necessary, and the policy parameter is
  semantically meaningful (the §5 refinement is strict). -/
theorem transmute_ptr_to_usize_policy_separation_witness :
    let locals : List LocalSlot := [.init b2PtrA]
    let decls : List LocalDecl := [⟨.not, b2PtrTy, .none⟩]
    let rv : Rvalue := .cast .transmute (b2Copy 0) b2UsizeTy
    evalRvalue locals rv emptyMemory decls emptyLayoutTable = .ub ∧
    evalByteCast locals (b2Copy 0) b2UsizeTy emptyMemory decls emptyLayoutTable .strictUcg630Ub = .ub ∧
    evalByteCast locals (b2Copy 0) b2UsizeTy emptyMemory decls emptyLayoutTable .stripProvenance =
      .ok (.scalar ⟨0x1000, 8⟩) locals emptyMemory ∧
    (∀ mode res,
      EvalRvalueFloatRel mode .strictUcg630Ub locals rv emptyMemory decls emptyLayoutTable res ↔
        res = .ub) ∧
    (∀ mode res,
      EvalRvalueFloatRel mode .stripProvenance locals rv emptyMemory decls emptyLayoutTable res ↔
        res = .ok (.scalar ⟨0x1000, 8⟩) locals emptyMemory) ∧
    (∀ mode,
      ¬ EvalRvalueFloatRel mode .stripProvenance locals rv emptyMemory decls emptyLayoutTable
        (evalRvalue locals rv emptyMemory decls emptyLayoutTable)) := by
  dsimp only
  refine ⟨rfl, rfl, rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, ?_⟩
  intro mode h
  have h' : evalRvalue [.init b2PtrA] (.cast .transmute (b2Copy 0) b2UsizeTy) emptyMemory
      [⟨.not, b2PtrTy, .none⟩] emptyLayoutTable =
      evalByteCast [.init b2PtrA] (b2Copy 0) b2UsizeTy emptyMemory [⟨.not, b2PtrTy, .none⟩]
        emptyLayoutTable .stripProvenance := h
  have hub : evalRvalue [.init b2PtrA] (.cast .transmute (b2Copy 0) b2UsizeTy) emptyMemory
      [⟨.not, b2PtrTy, .none⟩] emptyLayoutTable = .ub := rfl
  have hok : evalByteCast [.init b2PtrA] (b2Copy 0) b2UsizeTy emptyMemory [⟨.not, b2PtrTy, .none⟩]
      emptyLayoutTable .stripProvenance = .ok (.scalar ⟨0x1000, 8⟩) [.init b2PtrA] emptyMemory := rfl
  rw [hub, hok] at h'
  cases h'

/-- **Composite `Ptr2IntTransmutePolicy` separation witnesses** (`evalByteCast`, concrete
compiler-style layouts):
1. array `[*const u8; 2] → [usize; 2]`: `.strictUcg630Ub` is `.ub`, `.stripProvenance` yields
   both provenance-less addresses, and the identity cast `[*const u8; 2] → [*const u8; 2]`
   preserves both pointers under `.strictUcg630Ub`;
2. tuple `(*const u8, u64) → (u64, u64)`: `.ub` vs. `(0x1000, 42)`, while the identity tuple
   cast preserves the pointer field under `.strictUcg630Ub`;
3. struct `P { p, q : *const u8 } → S { a: u8, b: u64 }` (pointer bytes land in the `u8` field,
   in padding, and in the `u64` field): `.ub` vs. `(0x11, 0x2000)`;
4. float target `*const u8 → f64`: `.ub` vs. the provenance-less bit pattern `0x1000`;
5. union target `*const u8 → union U { p: *const u8, n: u64 }`: policy-independent and never
   `.ub` (the raw byte image keeps its provenance);
6. union source `U → u64`: `.ub` vs. `0x1000`, while `U → *const u8` preserves the pointer
   under `.strictUcg630Ub`. -/
theorem evalByteCast_composite_policy_separation_witness :
    let ptrB : Value := .ptr { allocId := 9, offsetBytes := 0x2000 } 8
    let arrLocals : List LocalSlot := [.init (.aggregate 0 [b2PtrA, ptrB])]
    let arrDecls : List LocalDecl := [⟨.not, b2PtrArrTy, .none⟩]
    let tupLocals : List LocalSlot := [.init (.aggregate 0 [b2PtrA, .scalar ⟨42, 8⟩])]
    let tupDecls : List LocalDecl := [⟨.not, b2PtrU64TupT, .none⟩]
    let structLocals : List LocalSlot :=
      [.init (.aggregate 0 [.ptr { allocId := 7, offsetBytes := 0x1011 } 8, ptrB])]
    let structDecls : List LocalDecl := [⟨.not, b2PtrPairStructT, .none⟩]
    let ptrLocals : List LocalSlot := [.init b2PtrA]
    let ptrDecls : List LocalDecl := [⟨.not, b2PtrT, .none⟩]
    let unionLocals : List LocalSlot := [.init (.aggregate 0 [b2PtrA, b2PtrA])]
    let unionDecls : List LocalDecl := [⟨.not, b2UnionT, .none⟩]
    -- (1) arrays
    evalByteCast arrLocals (b2Copy 0) b2UsizeArrTy emptyMemory arrDecls emptyLayoutTable .strictUcg630Ub = .ub ∧
    evalByteCast arrLocals (b2Copy 0) b2UsizeArrTy emptyMemory arrDecls emptyLayoutTable .stripProvenance =
      .ok (.aggregate 0 [.scalar ⟨0x1000, 8⟩, .scalar ⟨0x2000, 8⟩]) arrLocals emptyMemory ∧
    evalByteCast arrLocals (b2Copy 0) b2PtrArrTy emptyMemory arrDecls emptyLayoutTable .strictUcg630Ub =
      .ok (.aggregate 0 [b2PtrA, ptrB]) arrLocals emptyMemory ∧
    -- (2) tuples
    evalByteCast tupLocals (b2Copy 0) b2U64PairTupT emptyMemory tupDecls b2Layouts .strictUcg630Ub = .ub ∧
    evalByteCast tupLocals (b2Copy 0) b2U64PairTupT emptyMemory tupDecls b2Layouts .stripProvenance =
      .ok (.aggregate 0 [.scalar ⟨0x1000, 8⟩, .scalar ⟨42, 8⟩]) tupLocals emptyMemory ∧
    evalByteCast tupLocals (b2Copy 0) b2PtrU64TupT emptyMemory tupDecls b2Layouts .strictUcg630Ub =
      .ok (.aggregate 0 [b2PtrA, .scalar ⟨42, 8⟩]) tupLocals emptyMemory ∧
    -- (3) structs with padding
    evalByteCast structLocals (b2Copy 0) b2PadStructT emptyMemory structDecls b2Layouts .strictUcg630Ub = .ub ∧
    evalByteCast structLocals (b2Copy 0) b2PadStructT emptyMemory structDecls b2Layouts .stripProvenance =
      .ok (.aggregate 0 [.scalar ⟨0x11, 1⟩, .scalar ⟨0x2000, 8⟩]) structLocals emptyMemory ∧
    -- (4) float target
    evalByteCast ptrLocals (b2Copy 0) b2F64T emptyMemory ptrDecls b2Layouts .strictUcg630Ub = .ub ∧
    evalByteCast ptrLocals (b2Copy 0) b2F64T emptyMemory ptrDecls b2Layouts .stripProvenance =
      .ok (.scalar ⟨0x1000, 8⟩) ptrLocals emptyMemory ∧
    -- (5) union target
    (∃ v,
      evalByteCast ptrLocals (b2Copy 0) b2UnionT emptyMemory ptrDecls b2Layouts .strictUcg630Ub =
        .ok v ptrLocals emptyMemory ∧
      evalByteCast ptrLocals (b2Copy 0) b2UnionT emptyMemory ptrDecls b2Layouts .stripProvenance =
        .ok v ptrLocals emptyMemory) ∧
    -- (6) union source
    evalByteCast unionLocals (b2Copy 0) b2U64T emptyMemory unionDecls b2Layouts .strictUcg630Ub = .ub ∧
    evalByteCast unionLocals (b2Copy 0) b2U64T emptyMemory unionDecls b2Layouts .stripProvenance =
      .ok (.scalar ⟨0x1000, 8⟩) unionLocals emptyMemory ∧
    evalByteCast unionLocals (b2Copy 0) b2PtrT emptyMemory unionDecls b2Layouts .strictUcg630Ub =
      .ok b2PtrA unionLocals emptyMemory := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- **Provenance in padding vs. provenance in a field** (`decodeTypedValueFromBytes` at
`struct S { a: u8, b: u64 }`, 7 padding bytes at offsets `1..8`):
- pointer provenance (and even `.uninit` bytes) confined to PADDING is never read, so
  `.strictUcg630Ub` and `.stripProvenance` both decode `(0x11, 42)` although
  `abstractBytesHaveProv` holds for the whole image;
- pointer provenance on the `u8` FIELD byte is rejected by `.strictUcg630Ub` and stripped by
  `.stripProvenance`.
In particular the converse of `decodeTypedValueFromBytes_policy_differs_imp_haveProv` fails. -/
theorem decodeTypedValueFromBytes_padding_vs_field_provenance_witness :
    let tail : List AbstractByte :=
      [.init 42 .none, .init 0 .none, .init 0 .none, .init 0 .none,
       .init 0 .none, .init 0 .none, .init 0 .none, .init 0 .none]
    let paddingProv : List AbstractByte :=
      .init 0x11 .none ::
        .init 0 (.some (7, 7)) :: .init 0 (.some (7, 7)) :: .init 0 (.some (7, 7)) ::
        .uninit :: .uninit :: .uninit :: .uninit :: tail
    let fieldProv : List AbstractByte :=
      .init 0x11 (.some (7, 7)) ::
        .uninit :: .uninit :: .uninit :: .uninit :: .uninit :: .uninit :: .uninit :: tail
    let decoded : Value := .aggregate 0 [.scalar ⟨0x11, 1⟩, .scalar ⟨42, 8⟩]
    abstractBytesHaveProv paddingProv = true ∧
    decodeTypedValueFromBytes defaultCodecFuel b2Layouts b2PadStructT paddingProv .strictUcg630Ub =
      .some decoded ∧
    decodeTypedValueFromBytes defaultCodecFuel b2Layouts b2PadStructT paddingProv .stripProvenance =
      .some decoded ∧
    decodeTypedValueFromBytes defaultCodecFuel b2Layouts b2PadStructT fieldProv .strictUcg630Ub =
      .none ∧
    decodeTypedValueFromBytes defaultCodecFuel b2Layouts b2PadStructT fieldProv .stripProvenance =
      .some decoded := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Mixed pointer + integer composite witness (`(*const u8, usize)`, `(&u8, usize)`,
`struct Mixed { p: *const u8, n: u64 }`, and `Option<&u8>`)**:
demonstrates concretely that `Ptr2IntTransmutePolicy.stripProvenance` is NOT naive
whole-buffer `stripAbstractBytesProv` on composites mixing pointer and integer fields:
1. Unresolved `(*const u8, usize)` on `[ptrA, ptrB]` bytes:
   - `.strictUcg630Ub` returns `.none` (field 1 carries provenance);
   - `.stripProvenance` preserves `ptrA`'s provenance (`Value.ptr { allocId := 7, offsetBytes := 0x1000 } 8`)
     while stripping provenance ONLY on the `usize` field (`Value.scalar ⟨0x2000, 8⟩`);
   - naive whole-buffer `stripAbstractBytesProv` under `.strictUcg630Ub` destroys `ptrA`'s
     provenance, producing two provenance-less scalars `(0x1000, 0x2000)` (`≠` `.stripProvenance`)!
2. Resolved `(*const u8, u64)` and layout-backed `struct Mixed { p: *const u8, n: u64 }`
   (at both `decodeTypedValueFromBytes` and `evalByteCast` from `struct P { p, q: *const u8 }`):
   same separation — `.stripProvenance` preserves field 0's `Value.ptr` while stripping field 1,
   whereas whole-buffer `stripAbstractBytesProv` destroys field 0's provenance.
3. Mixed reference + integer `(&u8, usize)`:
   - `.strictUcg630Ub` returns `.none`;
   - `.stripProvenance` decodes `(ptrA, 0x2000)` (valid reference + stripped integer);
   - naive whole-buffer `stripAbstractBytesProv` under `.strictUcg630Ub` returns `.none`
     (stripping destroyed the reference's required provenance!).
4. Pointer-niche enum `Option<&u8>` (`RichAdtSpec.nichePointerEnum`):
   - on intact `ptrA` bytes, `.stripProvenance` decodes `Some(ptrA)` preserving provenance,
     whereas naive whole-buffer `stripAbstractBytesProv` yields `.none`. -/
theorem decodeTypedValueFromBytes_mixed_ptr_int_strip_vs_whole_buffer_witness :
    let ptrBytesA := encodeLittleEndianBytes 0x1000 8 (.some (7, 7))
    let ptrBytesB := encodeLittleEndianBytes 0x2000 8 (.some (9, 9))
    let twoPtrBytes := appendAbstractBytes ptrBytesA ptrBytesB
    let ptrUsizeTup : Ty := { kind := .tuple [.rawPtr .not (.uint .u8), .uint .usize], layoutIdx := 0 }
    let refUsizeTup : Ty := { kind := .tuple [.ref .not (.uint .u8), .uint .usize], layoutIdx := 0 }
    let mixedStructT : Ty := { kind := .adt "Mixed" .nil, layoutIdx := 6 }
    let keptPtrAndInt : Value := .aggregate 0 [b2PtrA, .scalar ⟨0x2000, 8⟩]
    let strippedBoth : Value := .aggregate 0 [.scalar ⟨0x1000, 8⟩, .scalar ⟨0x2000, 8⟩]
    let ptrB : Value := .ptr { allocId := 9, offsetBytes := 0x2000 } 8
    let structLocals : List LocalSlot := [.init (.aggregate 0 [b2PtrA, ptrB])]
    let structDecls : List LocalDecl := [⟨.not, b2PtrPairStructT, .none⟩]
    let optRefSpec : List (DefPath × RichAdtSpec) :=
      [("OptionRef", .nichePointerEnum 8 0 8 0 .nil 1 [(0, 8, { kind := .ref .not (.uint .u8), layoutIdx := 0 })])]
    let optRefTy : Ty := { kind := .adt "OptionRef" .nil, layoutIdx := 0 }
    -- (1) unresolved (*const u8, usize)
    decodeTypedValueFromBytes defaultCodecFuel emptyLayoutTable ptrUsizeTup twoPtrBytes .strictUcg630Ub = .none ∧
    decodeTypedValueFromBytes defaultCodecFuel emptyLayoutTable ptrUsizeTup twoPtrBytes .stripProvenance =
      .some keptPtrAndInt ∧
    decodeTypedValueFromBytes defaultCodecFuel emptyLayoutTable ptrUsizeTup (stripAbstractBytesProv twoPtrBytes) .strictUcg630Ub =
      .some strippedBoth ∧
    keptPtrAndInt ≠ strippedBoth ∧
    -- (2) resolved (*const u8, u64) tuple & layout-backed struct Mixed { p: *const u8, n: u64 }
    decodeTypedValueFromBytes defaultCodecFuel b2Layouts b2PtrU64TupT twoPtrBytes .strictUcg630Ub = .none ∧
    decodeTypedValueFromBytes defaultCodecFuel b2Layouts b2PtrU64TupT twoPtrBytes .stripProvenance =
      .some keptPtrAndInt ∧
    decodeTypedValueFromBytes defaultCodecFuel b2Layouts b2PtrU64TupT (stripAbstractBytesProv twoPtrBytes) .strictUcg630Ub =
      .some strippedBoth ∧
    decodeTypedValueFromBytes defaultCodecFuel b2Layouts mixedStructT twoPtrBytes .strictUcg630Ub = .none ∧
    decodeTypedValueFromBytes defaultCodecFuel b2Layouts mixedStructT twoPtrBytes .stripProvenance =
      .some keptPtrAndInt ∧
    decodeTypedValueFromBytes defaultCodecFuel b2Layouts mixedStructT (stripAbstractBytesProv twoPtrBytes) .strictUcg630Ub =
      .some strippedBoth ∧
    evalByteCast structLocals (b2Copy 0) mixedStructT emptyMemory structDecls b2Layouts .strictUcg630Ub = .ub ∧
    evalByteCast structLocals (b2Copy 0) mixedStructT emptyMemory structDecls b2Layouts .stripProvenance =
      .ok keptPtrAndInt structLocals emptyMemory ∧
    -- (3) (&u8, usize): whole-buffer strip turns a valid decode into .none
    decodeTypedValueFromBytes defaultCodecFuel emptyLayoutTable refUsizeTup twoPtrBytes .strictUcg630Ub = .none ∧
    decodeTypedValueFromBytes defaultCodecFuel emptyLayoutTable refUsizeTup twoPtrBytes .stripProvenance =
      .some keptPtrAndInt ∧
    decodeTypedValueFromBytes defaultCodecFuel emptyLayoutTable refUsizeTup (stripAbstractBytesProv twoPtrBytes) .strictUcg630Ub =
      .none ∧
    -- (4) Option<&u8> nichePointerEnum: intact Some(&x) preserved by .stripProvenance, destroyed by whole-buffer strip
    decodeTypedValueRichWithPolicy defaultCodecFuel emptyLayoutTable optRefSpec optRefTy ptrBytesA .stripProvenance =
      .some (.aggregate 1 [b2PtrA]) ∧
    decodeTypedValueRichWithPolicy defaultCodecFuel emptyLayoutTable optRefSpec optRefTy
        (stripAbstractBytesProv ptrBytesA) .strictUcg630Ub = .none := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  intro h
  injection h with _ hfs
  injection hfs with h0 _
  cases h0

/-- **`{to,from}_bits` byte casts preserve float bit patterns verbatim** (documented bitwise
operations): with a compiler-supplied `f32` layout, `transmute::<u32, f32>` and
`transmute::<f32, u32>` on the signaling NaN `0x7FA00001` return the unchanged bit pattern
(no quieting, no NaN choice), and `EvalRvalueFloatRel` admits EXACTLY that result in both
modes and under both policies.

**Fail-closed pin**: without a layout entry for the float type (`emptyLayoutTable`), float
byte casts are `.unsupported` (never a wrong value), so Episode 2 simulations of
`{to,from}_bits` must supply the float `TypeLayout`. -/
theorem transmute_float_bits_witness :
    let locals : List LocalSlot := [.init (.scalar ⟨0x7FA00001, 4⟩)]
    let res : RvalueEvalResult := .ok (.scalar ⟨0x7FA00001, 4⟩) locals emptyMemory
    evalRvalue locals (.cast .transmute (b2Copy 0) b2F32T) emptyMemory [⟨.not, b2U32Ty, .none⟩] b2Layouts = res ∧
    evalRvalue locals (.cast .transmute (b2Copy 0) b2U32Ty) emptyMemory [⟨.not, b2F32T, .none⟩] b2Layouts = res ∧
    (∀ mode policy r,
      EvalRvalueFloatRel mode policy locals (.cast .transmute (b2Copy 0) b2F32T) emptyMemory
          [⟨.not, b2U32Ty, .none⟩] b2Layouts r ↔ r = res) ∧
    (∀ mode policy r,
      EvalRvalueFloatRel mode policy locals (.cast .transmute (b2Copy 0) b2U32Ty) emptyMemory
          [⟨.not, b2F32T, .none⟩] b2Layouts r ↔ r = res) ∧
    evalRvalue locals (.cast .transmute (b2Copy 0) f32Ty) emptyMemory [⟨.not, b2U32Ty, .none⟩]
      emptyLayoutTable = .unsupported ∧
    evalRvalue locals (.cast .transmute (b2Copy 0) b2U32Ty) emptyMemory [⟨.not, f32Ty, .none⟩]
      emptyLayoutTable = .unsupported := by
  dsimp only
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩
  · intro mode policy r
    cases policy <;> exact Iff.rfl
  · intro mode policy r
    cases policy <;> exact Iff.rfl

/-! ## §8. Axiom guards

Every public theorem of this file is pinned to `[propext, Quot.sound]` (zero
`Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`).

The exact `#print axioms` output of an individual theorem varies between
"does not depend on any axioms", `[propext]`, and `[propext, Quot.sound]`, so
each bundle below instead conjoins ALL audited theorems of its group with the
anchor `Anneal.Mir.IeeeFloatCast.pack_unpack_f32` (itself guarded as exactly
`[propext, Quot.sound]` in `IeeeFloatCast.lean`). The bundle's axiom set is then
exactly `[propext, Quot.sound]` if and only if no audited theorem (nor any lemma
it uses) depends on any other axiom; `#guard_msgs` fails the build otherwise. In
particular this catches `omega` silently adding `Classical.choice` when an
`→` / `↔` hypothesis is in scope (see `Hold`).
-/

section AxiomGuards

set_option linter.defProp false in
/-- Axiom-audit bundle for the `Scalars`-level theory: every public `Scalars`-level theorem of §0, §2, §3, §4, §6, and §7. -/
def axiomAudit_scalars :=
  And.intro (@pack_unpack_f32) <|
  And.intro (@unpackBits_mod) <|
  And.intro (@decodeBits_mod) <|
  And.intro (@decodeBits_finite_num_pos) <|
  And.intro (@isNaNBits_eq_true_iff) <|
  And.intro (@isNaNBits_zeroBits) <|
  And.intro (@isNaNBits_infBits) <|
  And.intro (@isNaNBits_preferredNaNBits) <|
  And.intro (@isQuietNaNBits_preferredNaNBits) <|
  And.intro (@isNaNBits_roundRatioTiesToEven) <|
  And.intro (@roundRatioTiesToEven_zero) <|
  And.intro (@signedNum_not) <|
  And.intro (@signedNum_neg_iff) <|
  And.intro (@evalFloatNeg_lt) <|
  And.intro (@evalFloatNeg_mod) <|
  And.intro (@evalFloatNeg_involutive) <|
  And.intro (@evalFloatNeg_ne_self) <|
  And.intro (@evalFloatAbs_lt) <|
  And.intro (@evalFloatAbs_idempotent) <|
  And.intro (@evalFloatAbs_evalFloatNeg) <|
  And.intro (@unpackBits_evalFloatNeg) <|
  And.intro (@evalFloatNeg_encodeBits) <|
  And.intro (@evalFloatNeg_zeroBits) <|
  And.intro (@evalFloatNeg_infBits) <|
  And.intro (@decodeBits_evalFloatNeg) <|
  And.intro (@negateFloatKind_involutive) <|
  And.intro (@isNaNBits_evalFloatNeg) <|
  And.intro (@isQuietNaNBits_evalFloatNeg) <|
  And.intro (@isSignalingNaNBits_evalFloatNeg) <|
  And.intro (@evalFloatNeg_preserves_nan_payload) <|
  And.intro (@evalFloatPartialCompare_none_iff) <|
  And.intro (@evalFloatPartialCompare_nan_left) <|
  And.intro (@evalFloatPartialCompare_nan_right) <|
  And.intro (@evalFloatCmp_of_nan) <|
  And.intro (@evalFloatCmp_ne_eq_not_eq) <|
  And.intro (@evalFloatCmp_signed_zeros_eq) <|
  And.intro (@evalFloatCmp_trichotomy) <|
  And.intro (@evalFloatPartialCompare_refl) <|
  And.intro (@evalFloatCmp_eq_refl) <|
  And.intro (@evalFloatPartialCompare_swap) <|
  And.intro (@evalFloatCmp_eq_symm) <|
  And.intro (@evalFloatCmp_lt_gt_symm) <|
  And.intro (@evalFloatCmp_le_ge_symm) <|
  And.intro (@EvalFloatBinOpRel_cmp_mode_independent) <|
  And.intro (@decodeBits_finite_grid) <|
  And.intro (@roundRatioTiesToEven_exact_grid) <|
  And.intro (@evalFloatArithBase_add_finite) <|
  And.intro (@evalFloatArithBase_sub_finite) <|
  And.intro (@evalFloatArithBase_mul_finite) <|
  And.intro (@evalFloatArithBase_div_finite) <|
  And.intro (@evalFloatArithBase_mul_correctly_rounded) <|
  And.intro (@evalFloatArithBase_div_correctly_rounded) <|
  And.intro (@sterbenz_sub_exact) <|
  And.intro (@exact_add_same_sign_grid) <|
  And.intro (@gradual_underflow_sub_zero_iff) <|
  And.intro (@decodeBits_oneBits) <|
  And.intro (@evalFloatArithBase_mul_oneBits) <|
  And.intro (@evalFloatArithBase_rem_finite_exact) <|
  And.intro (@evalFloatArithBase_rem_finite_eq_zero_iff) <|
  And.intro (@overflowThreshold_eq) <|
  And.intro (@maxFiniteBits_props) <|
  And.intro (@decodeBits_finite_le_maxFiniteVal) <|
  And.intro (@roundRatioTiesToEven_eq_inf_iff) <|
  And.intro (@decodeBits_roundRatioTiesToEven_eq_inf_iff) <|
  And.intro (@roundRatioTiesToEven_lt_inf_isFinite) <|
  And.intro (@roundRatioTiesToEven_eq_maxFiniteBits) <|
  And.intro (@roundRatioTiesToEven_overflow_boundary) <|
  And.intro (@roundRatioTiesToEven_neg) <|
  And.intro (@evalFloatToFloatRoundTiesToEven_evalFloatNeg) <|
  And.intro (@mem_expandNanSigns_iff) <|
  And.intro (@mem_expandNanSigns_evalFloatNeg) <|
  And.intro (@mem_nanChoicesQuieted_props) <|
  And.intro (@mem_nanChoicesSignaling_props) <|
  And.intro (@preferredNaNBits_mem_nanChoices) <|
  And.intro (@mem_nanChoices_props) <|
  And.intro (@natListMem_eq_true_iff) <|
  And.intro (@nanChoices_all_quiet_of_no_snan) <|
  And.intro (@nanChoices_4_qnan_vs_6_snan_witness) <|
  And.intro (@nanChoices_sub_vs_add_neg_order_witness) <|
  And.intro (@EvalFloatBinOpRel.det_imp_nondet) <|
  And.intro (@evalFloatArithBase_nan_eq_preferred) <|
  And.intro (@evalFloatBinOp_iff_rel_det) <|
  And.intro (@mem_nanChoices_nondet_neg_left) <|
  And.intro (@mem_nanChoices_nondet_neg_right) <|
  And.intro (@mem_nanChoices_nondet_evalFloatNeg) <|
  And.intro (@evalFloatArithBase_rem_neg_right) <|
  And.intro (@EvalFloatBinOpRel.rem_neg_right) <|
  And.intro (@EvalFloatBinOpRel.det_mul_zero_inf_sign_symmetry_counterexample) <|
  And.intro (@EvalFloatBinOpRel.nondet_mul_div_rem_neg_left) <|
  And.intro (@EvalFloatBinOpRel.nondet_mul_div_neg_right) <|
  And.intro (@EvalFloatBinOpRel.nondet_add_neg_both_iff) <|
  And.intro (@EvalFloatBinOpRel.nondet_sub_iff_add_neg) <|
  And.intro (@EvalFloatBinOpRel.nondet_sub_neg_both_iff) <|
  And.intro (@scalarInt08_injective) <|
  And.intro (@fmt08_params) <|
  And.intro (@bitPatterns_parity) <|
  And.intro (@evalFloatNeg_parity) <|
  And.intro (@evalFloatAbs_parity) <|
  And.intro (@roundRatioTiesToEven_parity) <|
  And.intro (@decodeBits_parity) <|
  And.intro (@isNaNBits_parity) <|
  And.intro (@evalFloatPartialCompare_parity) <|
  And.intro (@evalFloatCmp_parity) <|
  And.intro (@exactSumFloat_parity) <|
  And.intro (@negateFloatKind_parity) <|
  And.intro (@evalFloatArithBase_parity) <|
  And.intro (@evalFloatToFloatRoundTiesToEven_parity) <|
  And.intro (@unpackBits_parity) <|
  And.intro (@nanChoicesQuieted_parity) <|
  And.intro (@nanChoicesSignaling_parity) <|
  And.intro (@expandNanSigns_parity) <|
  And.intro (@nanChoices_parity) <|
  And.intro (@natListMem_parity) <|
  And.intro (@isAdmissibleQuietNaN_parity) <|
  And.intro (@scalarInt08_eq_mk_iff) <|
  And.intro (@evalFloatBinOp_parity) <|
  And.intro (@EvalFloatBinOpRel_parity) <|
  And.intro (@abstractBytesHaveProv_parity) <|
  And.intro (@policyRejectsProv_parity) <|
  And.intro (@stripAbstractBytesProv_parity) <|
  And.intro (@evalFloatArithBase_of_nan) <|
  And.intro (@evalFloatArithBase_signed_zero_sums) <|
  And.intro (@evalFloatArithBase_cancel_finite) <|
  And.intro (@evalFloatArithBase_invalid_operations) <|
  And.intro (@evalFloatArithBase_inf_valid_operations) <|
  And.intro (@evalFloatArithBase_div_finite_by_zero) <|
  And.intro (@evalFloatArithBase_rem_by_zero) <|
  And.intro (@evalFloatArithBase_rem_inf_dividend) <|
  And.intro (@evalFloatArithBase_rem_by_inf) <|
  And.intro (@evalFloatArithBase_rem_zero_dividend) <|
  And.intro (@isSignalingNaNBits_eq_false_of_not_nan) <|
  And.intro (@nanChoicesQuieted_of_no_nan) <|
  And.intro (@nanChoicesSignaling_of_no_nan) <|
  And.intro (@nanChoices_nondet_of_no_nan) <|
  And.intro (@EvalFloatBinOpRel.nondet_invalid_operation_iff) <|
  And.intro (@evalFloatToFloat_nan_mem_nanChoices_nondet) <|
  And.intro (@evalFloatToFloat_nan_not_mem_nanChoices_det_witness) <|
  And.intro (@zeroBits_injective) <|
  And.intro (@evalFloatArithBase_sub_eq_add_neg) <|
  And.intro (@evalFloatArithBase_add_neg_neg) <|
  And.intro (@evalFloatArithBase_add_zero_sign) <|
  And.intro (@evalFloatArithBase_sub_zero_sign) <|
  And.intro (@evalFloatBinOp_sub_eq_add_neg) <|
  And.intro (@EvalFloatBinOpRel.sub_iff_add_neg) <|
  And.intro (@evalFloatArithBase_add_finite_overflow_iff) <|
  And.intro (@evalFloatArithBase_sub_finite_overflow_iff) <|
  And.intro (@evalFloatArithBase_mul_finite_overflow_iff) <|
  And.intro (@evalFloatArithBase_div_finite_overflow_iff) <|
  And.intro (@evalFloatBinOp_overflow_tie_witness) <|
  And.intro (@evalFloatBinOp_eq_none_iff) <|
  And.intro (@EvalFloatBinOpRel_none_iff) <|
  And.intro (@EvalFloatBinOpRel_exists_iff) <|
  And.intro (@EvalFloatBinOpRel_out_wf) <|
  And.intro (@minSubnormalVal_eq) <|
  And.intro (@decodeBits_subnormal_spacing) <|
  And.intro (@decodeBits_minSubnormal_and_minNormal) <|
  And.intro (@decodeBits_finite_subnormal_step) <|
  And.intro (@roundRatioTiesToEven_eq_zero_iff) <|
  And.intro (@roundRatioTiesToEven_underflow_boundary) <|
  And.intro (@evalFloatArithBase_mul_finite_underflow_zero_iff) <|
  And.intro (@evalFloatArithBase_div_finite_underflow_zero_iff) <|
  And.intro (@evalFloatBinOp_underflow_tie_witness) <|
  And.intro (@exact_subnormal_add) <|
  And.intro (@exact_subnormal_sub) <|
  And.intro (@exact_subnormal_add_sub) <|
  And.intro (@gradual_underflow_add_zero_iff) <|
  And.intro (@evalFloatArithBase_rem_finite_sign_and_bound) <|
  And.intro (@evalFloatArithBase_rem_finite_lt_self) <|
  And.intro (@evalFloatArithBase_rem_self_eq_zero) <|
  @EvalFloatBinOpRel_rem_finite_deterministic

/--
info: 'Anneal.Mir.IeeeFloatArith.axiomAudit_scalars'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms axiomAudit_scalars

set_option linter.defProp false in
/-- Axiom-audit bundle for the `Places`-level theory: every public `Places`-level theorem of §1, §4, §5, §6, and §7. -/
def axiomAudit_places :=
  And.intro (@pack_unpack_f32) <|
  And.intro (@finding1_neg_one_f32) <|
  And.intro (@finding1_add_one_one_f32) <|
  And.intro (@finding1_cmp_zero_and_nan_f32) <|
  And.intro (@finding1_f16_f128_fail_closed) <|
  And.intro (@EvalRvalueFloatRel.det_imp_nondet) <|
  And.intro (@length_stripAbstractBytesProv) <|
  And.intro (@abstractBytesHaveProv_stripAbstractBytesProv) <|
  And.intro (@takeAbstractBytes_stripAbstractBytesProv) <|
  And.intro (@dropAbstractBytes_stripAbstractBytesProv) <|
  And.intro (@sliceAbstractBytes_stripAbstractBytesProv) <|
  And.intro (@decodeLittleEndianBytes_stripAbstractBytesProv) <|
  And.intro (@decodeScalarBytes_stripAbstractBytesProv) <|
  And.intro (@abstractBytesHaveProv_takeAbstractBytes_false) <|
  And.intro (@abstractBytesHaveProv_dropAbstractBytes_false) <|
  And.intro (@abstractBytesHaveProv_sliceAbstractBytes_false) <|
  And.intro (@decodeScalarLayoutBytesNoForge_strict_imp_strip) <|
  And.intro (@decodeTypedValueFromBytes_strictUcg630Ub_refines_stripProvenance) <|
  And.intro (@decodeTypedValueRichWithPolicy_strictUcg630Ub_refines_stripProvenance) <|
  And.intro (@evalByteCast_strictUcg630Ub_refines_stripProvenance) <|
  And.intro (@evalByteCast_strip_eq_strict_or_strict_ub) <|
  And.intro (@evalByteCastRichWithPolicy_strip_eq_strict_or_strict_ub) <|
  And.intro (@evalByteCastRichWithPolicy_strictUcg630Ub_refines_stripProvenance) <|
  And.intro (@decodeScalarLayoutBytesNoForge_eq_of_provFree) <|
  And.intro (@decodeTypedValueFromBytes_eq_of_provFree) <|
  And.intro (@decodeTypedValueRichWithPolicy_eq_of_provFree) <|
  And.intro (@abstractBytesHaveProv_encodeByteCastSourceBytes) <|
  And.intro (@evalByteCast_eq_of_provFree) <|
  And.intro (@evalByteCastRichWithPolicy_eq_of_provFree) <|
  And.intro (@decodeScalarLayoutBytesNoForge_strip_eq_strict_stripProv) <|
  And.intro (@decodeTypedValueFromBytes_prim_strip_eq_strict_stripProv) <|
  And.intro (@decodeTypedValueFromBytes_adt_multiple_strip_eq_strict_stripProv) <|
  And.intro (@abstractBytesUniformProv_stripAbstractBytesProv) <|
  And.intro (@decodeTypedValueFromBytes_array_strip_eq_strict_stripProv) <|
  And.intro (@decodeTypedValueFromBytes_array_policy_independent_ptr) <|
  And.intro (@decodeTypedValueFromBytes_tuple_strip_eq_strict_stripProv) <|
  And.intro (@decodeTypedValueFromBytes_adt_single_arbitrary_fieldLayouts_strip_eq_strict_stripProv) <|
  And.intro (@decodeTypedValueFromBytes_adt_single_scalarPair_strip_eq_strict_stripProv) <|
  And.intro (@decodeTypedValueFromBytes_adt_single_primitive_strip_eq_strict_stripProv) <|
  And.intro (@decodeTypedValueFromBytes_adt_single_array_strip_eq_strict_stripProv) <|
  And.intro (@decodeTypedValueRichWithPolicy_structFields_strip_eq_strict_stripProv) <|
  And.intro (@decodeTypedValueRichWithPolicy_taggedEnum_strip_eq_strict_stripProv) <|
  And.intro (@decodeTypedValueRichWithPolicy_nicheScalarEnum_strip_eq_strict_stripProv) <|
  And.intro (@decodeTypedValueFromBytes_tuple_pair_mixed_strip) <|
  And.intro (@decodeTypedValueFromBytes_tuple_pair_seq_mixed_strip) <|
  And.intro (@decodeTypedValueFromBytes_adt_scalarPair_mixed_strip) <|
  And.intro (@decodeTypedValueRichWithPolicy_structFields_mixed_strip) <|
  And.intro (@decodeTypedValueRichWithPolicy_nichePointerEnum_intact_strip) <|
  And.intro (@decodeTypedValueFromBytes_policy_independent_ptr_and_union) <|
  And.intro (@decodeTypedValueRichWithPolicy_policy_independent_ptr) <|
  And.intro (@decodeTypedValueFromBytes_32bit_usize_isize_witness) <|
  And.intro (@unresolved_slot0_tuple_and_custom_dst_witnesses) <|
  And.intro (@evalByteCastRichWithPolicy_struct_ref_no_forge) <|
  And.intro (@evalByteCastRichWithPolicy_struct_fnPtr_no_forge) <|
  And.intro (@evalByteCastRichWithPolicy_enum_no_forge_ref_and_fnPtr) <|
  And.intro (@scalarInt06_scalarInt08) <|
  And.intro (@value06_injective) <|
  And.intro (@valueList06_injective) <|
  And.intro (@ieeeFormatOfTy?_parity) <|
  And.intro (@isFloatTy_parity) <|
  And.intro (@isFloatOptTy_parity) <|
  And.intro (@evalFloatUnaryNeg_parity_of_fmt) <|
  And.intro (@evalFloatUnaryNeg_parity) <|
  And.intro (@evalFloatScalarBinOp_parity_of_fmt) <|
  And.intro (@evalFloatScalarBinOp_parity) <|
  And.intro (@decodeLittleEndianBytes_parity) <|
  And.intro (@decodeScalarBytes_parity) <|
  And.intro (@abstractBytesAllProvAux_parity) <|
  And.intro (@abstractBytesUniformProv_parity) <|
  And.intro (@primitiveKindByteWidth_parity) <|
  And.intro (@scalarLayoutByteWidth_parity) <|
  And.intro (@wrappingRangeContains_parity) <|
  And.intro (@isValidCharCode_parity) <|
  And.intro (@decodeScalarLayoutBytesNoForge_parity) <|
  And.intro (@rvalueResWith06_injective_at) <|
  And.intro (@evalRvalue_unaryNeg_float_parity) <|
  And.intro (@EvalRvalueFloatRel_unaryNeg_float_parity) <|
  And.intro (@evalRvalue_binaryOp_float_parity) <|
  And.intro (@EvalRvalueFloatRel_binaryOp_float_parity) <|
  And.intro (@EvalRvalueFloatRel_floatToFloat_parity) <|
  And.intro (@EvalRvalueFloatRel_unaryNeg_float_const_parity) <|
  And.intro (@EvalRvalueFloatRel_binaryOp_float_const_parity) <|
  And.intro (@EvalRvalueFloatRel_floatToFloat_const_parity) <|
  And.intro (@EvalRvalueFloatRel_unaryNeg_float_local_copy_parity) <|
  And.intro (@EvalRvalueFloatRel_binaryOp_float_local_copy_parity) <|
  And.intro (@EvalRvalueFloatRel_binaryOp_float_local_move_parity) <|
  And.intro (@EvalRvalueFloatRel_det_binaryOp_iff) <|
  And.intro (@EvalRvalueFloatRel_det_iff_evalRvalue) <|
  And.intro (@EvalRvalueFloatRel_floatToFloat_of_not_nan) <|
  And.intro (@evalRvalue_realizes_EvalRvalueFloatRel_nondet) <|
  And.intro (@evalRvalue_ok_realizes_EvalRvalueFloatRel_unaryNeg) <|
  And.intro (@evalRvalue_ok_realizes_EvalRvalueFloatRel_binaryOp) <|
  And.intro (@evalRvalue_ok_realizes_EvalRvalueFloatRel) <|
  And.intro (@evalRvalue_floatToFloat_nan_rel_separation_witness) <|
  And.intro (@evalRvalue_unaryOp_neg_float) <|
  And.intro (@evalRvalue_binaryOp_float) <|
  And.intro (@evalFloatScalarBinOp_sub_eq_add_neg) <|
  And.intro (@evalFloatScalarBinOp_sub_eq_add_neg_bits) <|
  And.intro (@evalRvalue_sub_eq_add_neg_float) <|
  And.intro (@EvalRvalueFloatRel_sub_iff_add_neg_float) <|
  And.intro (@EvalRvalueFloatRel_policy_irrelevant) <|
  And.intro (@EvalRvalueFloatRel_byteCast_iff) <|
  And.intro (@EvalRvalueFloatRel_mode_irrelevant) <|
  And.intro (@EvalRvalueFloatRel_unaryNeg_iff) <|
  And.intro (@EvalRvalueFloatRel_mode_irrelevant_of_not_ok) <|
  And.intro (@EvalRvalueFloatRel_ub_iff) <|
  And.intro (@EvalRvalueFloatRel_unsupported_iff) <|
  And.intro (@EvalRvalueFloatRel_not_ok_iff_evalRvalue) <|
  And.intro (@EvalRvalueFloatRel_ub_iff_evalRvalue) <|
  And.intro (@EvalRvalueFloatRel_unsupported_iff_evalRvalue) <|
  And.intro (@evalRvalue_realizes_EvalRvalueFloatRel_nondet_of_not_byteCast) <|
  And.intro (@EvalRvalueFloatRel_det_iff_evalRvalue_of_not_byteCast) <|
  And.intro (@EvalRvalueFloatRel_total) <|
  And.intro (@EvalRvalueFloatRel_det_iff_evalRvalueDet) <|
  And.intro (@EvalRvalueFloatRel_det_functional) <|
  And.intro (@evalRvalueDet_strict_eq_evalRvalue) <|
  And.intro (@evalRvalueDet_eq_evalRvalue_of_not_byteCast) <|
  And.intro (@EvalRvalueFloatRel_binaryOp_float_iff) <|
  And.intro (@EvalRvalueFloatRel_floatToFloat_nan_iff) <|
  And.intro (@decodeTypedValueFromBytes_strip_eq_strict_or_strict_none) <|
  And.intro (@decodeTypedValueRichWithPolicy_strip_eq_strict_or_strict_none) <|
  And.intro (@decodeTypedValueFromBytes_policy_differs_imp_haveProv) <|
  And.intro (@decodeTypedValueRichWithPolicy_policy_differs_imp_haveProv) <|
  And.intro (@evalByteCast_policy_differs_imp) <|
  And.intro (@EvalRvalueFloatRel_byteCast_strict_refines_strip) <|
  And.intro (@EvalRvalueFloatRel_byteCast_strip_split) <|
  And.intro (@EvalRvalueFloatRel_byteCast_policy_irrelevant_of_provFree) <|
  And.intro (@evalRvalue_float_operands_from_locals_witness) <|
  And.intro (@EvalRvalueFloatRel_nan_operands_from_locals_witness) <|
  And.intro (@transmute_ptr_to_usize_policy_separation_witness) <|
  And.intro (@evalByteCast_composite_policy_separation_witness) <|
  And.intro (@decodeTypedValueFromBytes_padding_vs_field_provenance_witness) <|
  And.intro (@decodeTypedValueFromBytes_mixed_ptr_int_strip_vs_whole_buffer_witness) <|
  @transmute_float_bits_witness

/--
info: 'Anneal.Mir.IeeeFloatArith.axiomAudit_places'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms axiomAudit_places

end AxiomGuards

end Anneal.Mir.IeeeFloatArith
