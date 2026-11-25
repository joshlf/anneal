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
  gradual underflow (`a - b = ±0 ↔ a == b`), `1.0` multiplicative identity, and
  exact Euclidean `rem` (`|a % b| < |b|`, `rem = ±0 ↔ divisibility`);
- **§4**: `FloatArithMode` inclusion (`EvalFloatBinOpRel.det_imp_nondet`,
  `EvalRvalueFloatRel.det_imp_nondet`, `evalFloatBinOp` realizes `.deterministic`),
  `nanChoices` membership / width / NaN / quietness / `4`-vs-`6` sNaN structure,
  `sub` vs `add ∘ neg` ordered-list swap witness, and relational sign-symmetry
  (`rem` right-negation invariance in both modes, `.deterministic`
  `(+0.0) * (+Inf)` counterexample, `.nondeterministic` unconditional left/right
  sign symmetry for `mul`/`div`/`rem` and non-zero-canceling `add`/`sub`);
- **§5**: `Ptr2IntTransmutePolicy` refinement (`strictUcg630Ub` refines
  `stripProvenance`), exact cast split (`strip = strict ∨ strict = .ub`),
  provenance-free equivalence, closed-form provenance erasure on non-pointer
  targets, policy independence on `.rawPtr`/`.ref`/`.fnPtr`/union targets,
  32-bit `usize`/`isize` & unresolved-slot-0 tuple/ref witnesses, and struct &
  enum `.ref`/`.fnPtr` no-forgery (`evalByteCastRichWithPolicy`);
- **§6**: `V2026_06_01` <-> `V2026_08_01` dialect parity over explicit
  constructor-preserving translation maps (`fmt08`, `binOp08`, `mode08`,
  `floatKind08`, `scalarInt08`, `policy08`, `abstractByte08`): `evalFloatNeg`,
  `evalFloatAbs`, `decodeBits`, `roundRatioTiesToEven`, `evalFloatPartialCompare`,
  `evalFloatCmp`, `evalFloatArithBase`, `evalFloatToFloatRoundTiesToEven`,
  `nanChoices` (element-for-element), `evalFloatBinOp`, `EvalFloatBinOpRel`
  (`↔`), and the `Ptr2IntTransmutePolicy` byte gate (`policyRejectsProv`,
  `stripAbstractBytesProv`). Parity of the layout-table-driven decoders
  (`decodeTypedValueFromBytes`, `evalByteCast`) is NOT proved here: their
  `Value` / `LayoutTable` / `Memory` types are dialect-specific
  (`V2026_08_01.Value` has no `.uninit`) and require full structural
  translations;
- **§7**: IEEE 754-2008 special-case table over both formats and all signs (NaN
  infectiousness, signed-zero sums, exact cancellation `x + (-x) = +0`, invalid
  operations, `finite / ±0 = ±∞` with XOR sign, `x % ±0 = NaN`, `±∞ % y = NaN`,
  `finite % ±∞ = finite`, `±0 % finite = ±0`), the documented signed-zero rule
  for arbitrary zero-valued sums and differences, the no-NaN-input `nanChoices`
  closed form (`[preferred, -preferred]`), and admissibility of `evalRvalue`'s
  quieting `floatToFloat` NaN in `.nondeterministic` (but not `.deterministic`)
  mode;
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
/-- Axiom-audit bundle for the `Scalars`-level theory: every public theorem of §0, §2, §3, §4 (except `EvalRvalueFloatRel.det_imp_nondet`), §6, and §7. -/
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
  @evalFloatArithBase_sub_zero_sign

/--
info: 'Anneal.Mir.IeeeFloatArith.axiomAudit_scalars'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms axiomAudit_scalars

set_option linter.defProp false in
/-- Axiom-audit bundle for the `Places`-level theory: every public theorem of §1 and §5, plus `EvalRvalueFloatRel.det_imp_nondet`. -/
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
  And.intro (@decodeTypedValueFromBytes_policy_independent_ptr_and_union) <|
  And.intro (@decodeTypedValueRichWithPolicy_policy_independent_ptr) <|
  And.intro (@decodeTypedValueFromBytes_32bit_usize_isize_witness) <|
  And.intro (@unresolved_slot0_tuple_and_custom_dst_witnesses) <|
  And.intro (@evalByteCastRichWithPolicy_struct_ref_no_forge) <|
  And.intro (@evalByteCastRichWithPolicy_struct_fnPtr_no_forge) <|
  @evalByteCastRichWithPolicy_enum_no_forge_ref_and_fnPtr

/--
info: 'Anneal.Mir.IeeeFloatArith.axiomAudit_places'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms axiomAudit_places

end AxiomGuards

end Anneal.Mir.IeeeFloatArith
