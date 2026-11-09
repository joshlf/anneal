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
# `LM-4.2`: Integer Bit-Manipulation Intrinsics

Correspondence between Anneal's inline integer bit intrinsics
(`evalIntegerBitIntrinsic`: `ctpop`, `ctlz`, `ctlz_nonzero`, `cttz`,
`cttz_nonzero`, `bswap`, and `bitreverse`) and `lean-miri`'s
`Miri.Interpreter.IntegerIntrinsic.run`.

1. **Public mirror (`miriIntegerIntrinsicRun`)**: `IntegerIntrinsic.run` calls
   the private loops `countTrailingZeros` and `reverseBytes`, which other
   modules cannot name. `miriIntegerIntrinsicRun` copies `run` with public
   copies of those loops, and `integerIntrinsic_run_eq_mirror` proves the copy
   definitionally equal to `run`, so the copy cannot drift from the vendored
   source without breaking that proof.
2. **Per-intrinsic arithmetic**: each of Anneal's structurally recursive bit
   helpers equals the `lean-miri` computation that it models:
   `countOnesBits_eq_cpop` (`BitVec.cpop`), `bitLengthBits_eq_log2`
   (`Nat.log2`), `miriCountTrailingZeros_eq`, `miriReverseBytes_eq`, and
   `reverse_shiftLeft_toNat_eq` (`BitVec.reverse` of the operand shifted to
   the top of the `u128`).
3. **Simulation (`integerBitIntrinsic_run_simulation`)**: on a
   `ScalarRel`-related operand, every result that Anneal defines matches a
   successful `lean-miri` run, and Anneal's undefined behavior (a zero operand
   to `ctlz_nonzero` or `cttz_nonzero`) matches `lean-miri`'s
   `undefinedBehaviorOnZero` error.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## Public mirror of `IntegerIntrinsic.run` -/

/-- Public copy of the private loop
`Miri.Interpreter.IntegerIntrinsic.countTrailingZeros`: the index of the lowest
set bit among the low `width` bits of `bits`, or `width` if there is none. -/
def miriCountTrailingZeros (bits : Nat) (width : Nat) : Nat := Id.run do
  for index in [:width] do
    if Nat.testBit bits index then return index
  return width

/-- Public copy of the private loop
`Miri.Interpreter.IntegerIntrinsic.reverseBytes`: the low `byteCount` bytes of
`bits` in reverse order. -/
def miriReverseBytes (bits : Nat) (byteCount : Nat) : Nat := Id.run do
  let mut result := 0
  for index in [:byteCount] do
    let byte := (bits / (2 ^ (index * 8))) % 256
    result := result + byte * (2 ^ ((byteCount - index - 1) * 8))
  return result

/-- Public copy of `Miri.Interpreter.IntegerIntrinsic.run` that calls
`miriCountTrailingZeros` and `miriReverseBytes` in place of the private loops.

The body must stay identical to the vendored `run`:
`integerIntrinsic_run_eq_mirror` checks that the two are definitionally equal.
-/
def miriIntegerIntrinsicRun (intrinsic : Miri.Interpreter.IntegerIntrinsic)
    (value : Miri.Memory.ScalarInt)
    (inputType outputType : Miri.Interpreter.IntegerType) :
    Except Miri.Interpreter.IntegerIntrinsicError Miri.Memory.ScalarInt := do
  let bits ← value.toBits inputType.size |>.mapError .scalar
  let width ← inputType.size.bits |>.mapError (fun e => .scalar (.sizeError e))
  let width := width.toNat
  let raw := bits.toNat
  if (intrinsic == .cttzNonzero || intrinsic == .ctlzNonzero) && raw == 0 then
    throw (.undefinedBehaviorOnZero intrinsic)
  let result ← match intrinsic with
    | .ctpop => pure bits.cpop.toNat
    | .cttz | .cttzNonzero => pure (miriCountTrailingZeros raw width)
    | .ctlz | .ctlzNonzero =>
        if raw == 0 then pure width
        else pure (width - (Nat.log2 raw + 1))
    | .bswap =>
        if inputType != outputType then throw (.layoutMismatch inputType outputType)
        pure (miriReverseBytes raw inputType.size.bytes.toNat)
    | .bitreverse =>
        if inputType != outputType then throw (.layoutMismatch inputType outputType)
        let extra := 128 - width
        let aligned : Miri.ABI.U128 := bits <<< extra
        pure aligned.reverse.toNat
  let (out, _) ← Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofNat 128 result)
      outputType.size
    |>.mapError .scalar
  return out

/-- `Miri.Interpreter.IntegerIntrinsic.run` is definitionally equal to its
public copy `miriIntegerIntrinsicRun`. -/
theorem integerIntrinsic_run_eq_mirror :
    Miri.Interpreter.IntegerIntrinsic.run = miriIntegerIntrinsicRun := rfl

/-! ## Population count -/

/-- `countOnesBits (k + 1) x` adds bit `k` of `x` to `countOnesBits k x`. -/
theorem countOnesBits_succ_top (k x : Nat) :
    countOnesBits (k + 1) x = countOnesBits k x + (x.testBit k).toNat := by
  induction k generalizing x with
  | zero =>
    show x % 2 + 0 = 0 + (x.testBit 0).toNat
    rw [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]
  | succ k ih =>
    show x % 2 + countOnesBits (k + 1) (x / 2) =
      (x % 2 + countOnesBits k (x / 2)) + (x.testBit (k + 1)).toNat
    rw [ih (x / 2), Nat.testBit_div_two]
    omega

/-- Bits at or above `w` do not contribute to `countOnesBits` when
`x < 2 ^ w`. -/
theorem countOnesBits_add_of_lt {w x : Nat} (hx : x < 2 ^ w) (j : Nat) :
    countOnesBits (w + j) x = countOnesBits w x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hlt : x < 2 ^ (w + j) :=
      Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (Nat.le_add_right w j))
    rw [← Nat.add_assoc, countOnesBits_succ_top, ih, Nat.testBit_lt_two_pow hlt]
    rfl

/-- Over the low `n ≤ 128` bits, `BitVec.cpopNatRec` of the zero-extended `x`
adds `countOnesBits n x` to its accumulator. -/
theorem cpopNatRec_ofNat_eq (x : Nat) : ∀ (n acc : Nat), n ≤ 128 →
    (BitVec.ofNat 128 x).cpopNatRec n acc = acc + countOnesBits n x := by
  intro n
  induction n with
  | zero => intro acc _; rfl
  | succ n ih =>
    intro acc hn
    rw [BitVec.cpopNatRec_succ, ih _ (by omega), countOnesBits_succ_top,
      BitVec.getLsbD_ofNat]
    simp only [show n < 128 by omega, decide_true, Bool.true_and]
    omega

/-- For `x < 2 ^ w` with `w ≤ 128`, `countOnesBits w x` is the population count
`BitVec.cpop` of `x` zero-extended to a `u128`, as `lean-miri` computes it. -/
theorem countOnesBits_eq_cpop {w x : Nat} (hw : w ≤ 128) (hx : x < 2 ^ w) :
    countOnesBits w x = (BitVec.ofNat 128 x).cpop.toNat := by
  rw [BitVec.toNat_cpop, cpopNatRec_ofNat_eq x 128 0 (Nat.le_refl _), Nat.zero_add]
  have h := countOnesBits_add_of_lt hx (128 - w)
  rw [Nat.add_sub_cancel' hw] at h
  exact h.symm

/-- `countOnesBits n x` is at most `n`. -/
theorem countOnesBits_le : ∀ (n x : Nat), countOnesBits n x ≤ n := by
  intro n
  induction n with
  | zero => intro x; exact Nat.le_refl _
  | succ k ih =>
    intro x
    show x % 2 + countOnesBits k (x / 2) ≤ k + 1
    have := ih (x / 2)
    have := Nat.mod_lt x (show 2 > 0 by decide)
    omega

/-! ## Leading zeros -/

/-- For `x < 2 ^ w`, `bitLengthBits w x` is `0` when `x = 0` and
`Nat.log2 x + 1` otherwise. -/
theorem bitLengthBits_eq_log2 : ∀ (w x : Nat), x < 2 ^ w →
    bitLengthBits w x = if x = 0 then 0 else Nat.log2 x + 1 := by
  intro w
  induction w with
  | zero =>
    intro x hx
    rw [Nat.pow_zero] at hx
    have hx0 : x = 0 := by omega
    subst hx0
    rfl
  | succ k ih =>
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      rfl
    · show (match Nat.beq x 0 with
          | true => 0
          | false => Nat.add 1 (bitLengthBits k (Nat.div x 2))) = _
      rw [nat_beq_eq_decide, decide_eq_false hx0, ite_eq_right hx0]
      show 1 + bitLengthBits k (x / 2) = _
      rw [Nat.pow_succ] at hx
      rw [ih (x / 2) (by omega), Nat.log2_def x]
      by_cases h2 : 2 ≤ x
      · rw [ite_eq_left h2, ite_eq_right (by omega)]
        omega
      · rw [ite_eq_right h2, ite_eq_left (by omega)]

/-! ## Trailing zeros -/

/-- The index of the first set bit of `bits` in `[s, s + n)`, or `s + n` if
there is none, is `s` plus the trailing-zero count of `bits / 2 ^ s` over `n`
bits. -/
theorem find?_range'_testBit_getD (bits : Nat) : ∀ (n s : Nat),
    ((List.range' s n).find? (fun i => bits.testBit i)).getD (s + n) =
      s + countTrailingZerosBits n (bits / 2 ^ s) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    rw [List.range'_succ, List.find?_cons]
    have hdiv : bits / 2 ^ s / 2 = bits / 2 ^ (s + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
    have htb := (Nat.testBit_eq_decide_div_mod_eq (x := bits) (i := s))
    show _ = s + (match Nat.beq (Nat.mod (bits / 2 ^ s) 2) 0 with
      | false => 0
      | true => Nat.add 1 (countTrailingZerosBits n (Nat.div (bits / 2 ^ s) 2)))
    cases hb : bits.testBit s with
    | true =>
      have hmod : bits / 2 ^ s % 2 = 1 := by
        rw [hb] at htb
        exact of_decide_eq_true htb.symm
      show s = s + (match Nat.beq (bits / 2 ^ s % 2) 0 with
        | false => 0
        | true => Nat.add 1 (countTrailingZerosBits n (Nat.div (bits / 2 ^ s) 2)))
      rw [hmod]
      rfl
    | false =>
      have hmod : bits / 2 ^ s % 2 = 0 := by
        rw [hb] at htb
        have := of_decide_eq_false htb.symm
        omega
      show ((List.range' (s + 1) n).find? (fun i => bits.testBit i)).getD (s + (n + 1)) =
        s + (match Nat.beq (bits / 2 ^ s % 2) 0 with
          | false => 0
          | true => Nat.add 1 (countTrailingZerosBits n (Nat.div (bits / 2 ^ s) 2)))
      rw [hmod]
      show _ = s + (1 + countTrailingZerosBits n (bits / 2 ^ s / 2))
      rw [hdiv, show s + (n + 1) = (s + 1) + n by omega, ih (s + 1)]
      omega

/-- The loop of `miriCountTrailingZeros`, run over any list of bit indices,
stops at the first index of a set bit. -/
theorem ctzLoop_eq_find? (bits : Nat) (L : List Nat) :
    (forIn (m := Id) L ((none : Option Nat), ()) fun index (_ : Option Nat × Unit) =>
        if bits.testBit index = true then pure (ForInStep.done (some index, ()))
        else pure (ForInStep.yield (none, ()))) =
      (L.find? (fun i => bits.testBit i), ()) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.forIn_cons, List.find?_cons]
    cases ha : bits.testBit a with
    | true => rfl
    | false => exact ih

/-- `lean-miri`'s `countTrailingZeros` loop computes
`countTrailingZerosBits`. -/
theorem miriCountTrailingZeros_eq (bits width : Nat) :
    miriCountTrailingZeros bits width = countTrailingZerosBits width bits := by
  have h := find?_range'_testBit_getD bits width 0
  rw [Nat.zero_add, Nat.pow_zero, Nat.div_one, Nat.zero_add] at h
  rw [← h]
  unfold miriCountTrailingZeros
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [ctzLoop_eq_find?]
  cases (List.range' 0 width).find? (fun i => bits.testBit i) <;> rfl

/-- `countTrailingZerosBits n x` is at most `n`. -/
theorem countTrailingZerosBits_le : ∀ (n x : Nat), countTrailingZerosBits n x ≤ n := by
  intro n
  induction n with
  | zero => intro x; exact Nat.le_refl _
  | succ k ih =>
    intro x
    show (match Nat.beq (Nat.mod x 2) 0 with
      | false => 0
      | true => Nat.add 1 (countTrailingZerosBits k (Nat.div x 2))) ≤ k + 1
    cases Nat.beq (Nat.mod x 2) 0 with
    | false => exact Nat.zero_le _
    | true =>
      show 1 + countTrailingZerosBits k (x / 2) ≤ k + 1
      have := ih (x / 2)
      omega

/-! ## Byte swap -/

/-- The loop of `miriReverseBytes bits n`, run over the byte indices
`[s, s + m)` with `s + m = n` from the accumulator `acc`, adds the byte reversal
`reverseBytesBits m` of the bytes of `bits` from index `s` on. -/
theorem reverseBytesLoop_eq (bits n : Nat) : ∀ (m s acc : Nat), s + m = n →
    (forIn (m := Id) (List.range' s m) acc fun index (acc : Nat) =>
        pure (ForInStep.yield
          (acc + bits / 2 ^ (index * 8) % 256 * 2 ^ ((n - index - 1) * 8)))) =
      acc + reverseBytesBits m (bits / 2 ^ (s * 8)) := by
  intro m
  induction m with
  | zero => intro s acc _; rfl
  | succ m ih =>
    intro s acc hsm
    rw [List.range'_succ, List.forIn_cons]
    simp only [pure_bind]
    rw [ih (s + 1) _ (by omega)]
    show _ = acc + (bits / 2 ^ (s * 8) % 256 * scalarModulus m +
      reverseBytesBits m (bits / 2 ^ (s * 8) / 256))
    have hexp : n - s - 1 = m := by omega
    have hdiv : bits / 2 ^ (s * 8) / 256 = bits / 2 ^ ((s + 1) * 8) := by
      rw [Nat.div_div_eq_div_mul, Nat.add_mul, Nat.one_mul, Nat.pow_add]
    rw [hexp, hdiv, scalarModulus_eq_two_pow, Nat.mul_comm 8 m]
    omega

/-- `lean-miri`'s `reverseBytes` loop computes `reverseBytesBits`. -/
theorem miriReverseBytes_eq (bits n : Nat) :
    miriReverseBytes bits n = reverseBytesBits n bits := by
  unfold miriReverseBytes
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  have h := reverseBytesLoop_eq bits n n 0 0 (Nat.zero_add n)
  rw [Nat.zero_mul, Nat.pow_zero, Nat.div_one, Nat.zero_add] at h
  exact h

/-- `reverseBytesBits n b` is below `scalarModulus n`. -/
theorem reverseBytesBits_lt : ∀ (n b : Nat), reverseBytesBits n b < scalarModulus n := by
  intro n
  induction n with
  | zero => intro b; show 0 < 1; decide
  | succ k ih =>
    intro b
    show b % 256 * scalarModulus k + reverseBytesBits k (b / 256) < 256 * scalarModulus k
    have h1 := ih (b / 256)
    have h2 : b % 256 * scalarModulus k ≤ 255 * scalarModulus k :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-! ## Bit reversal -/

/-- `reverseBitsBits n b` is below `2 ^ n`. -/
theorem reverseBitsBits_lt : ∀ (n b : Nat), reverseBitsBits n b < 2 ^ n := by
  intro n
  induction n with
  | zero => intro b; show 0 < 1; decide
  | succ k ih =>
    intro b
    show b % 2 * scalarPow2 k + reverseBitsBits k (b / 2) < 2 ^ (k + 1)
    have h1 := ih (b / 2)
    have h2 : b % 2 * scalarPow2 k ≤ 1 * 2 ^ k := by
      rw [scalarPow2_eq_two_pow]
      exact Nat.mul_le_mul_right _ (by omega)
    rw [Nat.pow_succ]
    omega

/-- Bit `i` of `reverseBitsBits n b` is bit `n - 1 - i` of `b` for `i < n`,
and is clear otherwise. -/
theorem testBit_reverseBitsBits : ∀ (n b i : Nat),
    (reverseBitsBits n b).testBit i = (decide (i < n) && b.testBit (n - 1 - i)) := by
  intro n
  induction n with
  | zero => intro b i; exact Nat.zero_testBit i
  | succ k ih =>
    intro b i
    show (b % 2 * scalarPow2 k + reverseBitsBits k (b / 2)).testBit i = _
    rw [scalarPow2_eq_two_pow, Nat.mul_comm,
      Nat.testBit_two_pow_mul_add _ (reverseBitsBits_lt k (b / 2))]
    by_cases hik : i < k
    · rw [ite_eq_left hik, ih, Nat.testBit_div_two]
      simp [hik, show i < k + 1 by omega, show k - 1 - i + 1 = k + 1 - 1 - i by omega]
    · rw [ite_eq_right hik, show b % 2 = b % 2 ^ 1 by rfl, Nat.testBit_mod_two_pow]
      by_cases hik' : i = k
      · subst hik'
        simp
      · simp [show ¬ (i - k < 1) by omega, show ¬ (i < k + 1) by omega]

/-- For a `w`-bit operand with `w ≤ 128`, `lean-miri`'s `bitreverse`, which
reverses the `u128` holding the operand shifted to its top `w` bits, computes
`reverseBitsBits w`. -/
theorem reverse_shiftLeft_toNat_eq {w : Nat} (hw : w ≤ 128) (x : Nat) :
    ((BitVec.ofNat 128 x) <<< (128 - w)).reverse.toNat = reverseBitsBits w x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [BitVec.testBit_toNat, BitVec.getLsbD_reverse, BitVec.getMsbD_shiftLeft,
    BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_ofNat, testBit_reverseBitsBits]
  by_cases hi : i < w
  · simp [hi, show i + (128 - w) < 128 by omega,
      show 128 - 1 - (i + (128 - w)) = w - 1 - i by omega, show w - 1 - i < 128 by omega]
  · simp [hi, show ¬ (i + (128 - w) < 128) by omega]

/-! ## Simulation of `IntegerIntrinsic.run` -/

/-- Translate an Anneal `IntegerBitIntrinsic` to the corresponding
`lean-miri` `Miri.Interpreter.IntegerIntrinsic`. -/
def toMiriIntegerIntrinsic : IntegerBitIntrinsic → Miri.Interpreter.IntegerIntrinsic
  | .ctpop => .ctpop
  | .ctlz => .ctlz
  | .ctlzNonzero => .ctlzNonzero
  | .cttz => .cttz
  | .cttzNonzero => .cttzNonzero
  | .bswap => .bswap
  | .bitreverse => .bitreverse

/-- Byte width of the result of `op` applied to a `sz`-byte operand: the
counting intrinsics return a `u32`, while `bswap` and `bitreverse` return a
value of the operand's own type. -/
def bitIntrinsicOutBytes : IntegerBitIntrinsic → Nat → Nat :=
  fun op sz =>
    match op with
    | .bswap | .bitreverse => sz
    | _ => 4

/-- Truncating a canonical `c < scalarModulus sz` to `translateSizeBytes sz`
succeeds with a scalar `ScalarRel`-related to `⟨c, sz⟩`. -/
theorem truncateFromUInt_ofNat_rel {sz c : Nat} (hsz : ValidScalarBytes sz)
    (hc : c < scalarModulus sz) :
    ∃ msc b, Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofNat 128 c)
        (translateSizeBytes sz) = .ok (msc, b) ∧ ScalarRel ⟨c, sz⟩ msc := by
  obtain ⟨msc, hmsc, hrel⟩ :=
    truncateFromUInt_translateSizeBytes_spec hsz (BitVec.ofNat 128 c)
  have hc' : (BitVec.ofNat 128 c).toNat % 2 ^ (8 * sz) = c := by
    rw [bitVec_ofNat_toNat_of_valid hsz hc]
    exact Nat.mod_eq_of_lt (scalarModulus_eq_two_pow sz ▸ hc)
  rw [hc'] at hrel
  exact ⟨msc, _, hmsc, hrel⟩

/-- Conclude the statement shape of `integerBitIntrinsic_run_simulation` for
an intrinsic that Anneal evaluates to `r₀` and that `lean-miri` runs to a
`ScalarRel`-related `mr`. -/
theorem bitIntrinsic_simulation_of_some {e : Option MirAst.ScalarInt}
    {run : Except Miri.Interpreter.IntegerIntrinsicError Miri.Memory.ScalarInt}
    {err : Miri.Interpreter.IntegerIntrinsicError} {r₀ : MirAst.ScalarInt}
    {mr : Miri.Memory.ScalarInt} (hev : e = some r₀) (hrun : run = .ok mr)
    (hrel : ScalarRel r₀ mr) :
    (∀ r, e = some r → ∃ mr, run = .ok mr ∧ ScalarRel r mr) ∧
      (e = none → run = .error err) := by
  subst hev
  exact ⟨fun r hr => (by cases hr; exact ⟨mr, hrun, hrel⟩), fun h => (by cases h)⟩

/-- Conclude the statement shape of `integerBitIntrinsic_run_simulation` for
an intrinsic that is undefined behavior in Anneal and that `lean-miri` rejects
with `err`. -/
theorem bitIntrinsic_simulation_of_none {e : Option MirAst.ScalarInt}
    {run : Except Miri.Interpreter.IntegerIntrinsicError Miri.Memory.ScalarInt}
    {err : Miri.Interpreter.IntegerIntrinsicError} (hev : e = none)
    (hrun : run = .error err) :
    (∀ r, e = some r → ∃ mr, run = .ok mr ∧ ScalarRel r mr) ∧
      (e = none → run = .error err) := by
  subst hev
  exact ⟨fun _ hr => (by cases hr), fun _ => hrun⟩

/-- Anneal's inline integer bit intrinsics agree with `lean-miri`'s
`Miri.Interpreter.IntegerIntrinsic.run` on every related operand.

Let `sc` be a valid, canonical Anneal scalar related to `msc`. Run
`lean-miri` with input layout `⟨translateSizeBytes sc.sizeBytes, kind⟩` and
output layout `⟨translateSizeBytes (bitIntrinsicOutBytes op sc.sizeBytes),
outKind⟩`. Whenever `evalIntegerBitIntrinsic op sc` returns `some r`, the run
succeeds with a scalar related to `r`. Whenever it returns `none` (a zero
operand to `ctlz_nonzero` or `cttz_nonzero`), the run reports
`undefinedBehaviorOnZero`.

The counting intrinsics ignore signedness, so `kind` and `outKind` are
arbitrary for them. `bswap` and `bitreverse` reject mismatched input and output
layouts, so `hkind` requires `outKind = kind` for those two intrinsics. -/
theorem integerBitIntrinsic_run_simulation
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc)
    (op : IntegerBitIntrinsic) (kind outKind : Miri.MIR.IntegerKind)
    (hkind : (op = .bswap ∨ op = .bitreverse) → outKind = kind) :
    (∀ r, evalIntegerBitIntrinsic op sc = some r →
      ∃ mr, Miri.Interpreter.IntegerIntrinsic.run (toMiriIntegerIntrinsic op) msc
          ⟨translateSizeBytes sc.sizeBytes, kind⟩
          ⟨translateSizeBytes (bitIntrinsicOutBytes op sc.sizeBytes), outKind⟩ = .ok mr ∧
        ScalarRel r mr) ∧
    (evalIntegerBitIntrinsic op sc = none →
      Miri.Interpreter.IntegerIntrinsic.run (toMiriIntegerIntrinsic op) msc
          ⟨translateSizeBytes sc.sizeBytes, kind⟩
          ⟨translateSizeBytes (bitIntrinsicOutBytes op sc.sizeBytes), outKind⟩ =
        .error (.undefinedBehaviorOnZero (toMiriIntegerIntrinsic op))) := by
  have hsz := hrel.validBytes
  have hw128 := (validScalarBytes_bits_le_128 hsz).1
  obtain ⟨hbits, hbitsNat⟩ := translateSizeBytes_bits_eq hsz
  have hraw : (BitVec.ofNat 128 sc.bits).toNat = sc.bits :=
    bitVec_ofNat_toNat_of_valid hsz hrel.canonical
  have hwrap := hrel.wrapScalarBits_self
  have hcan : sc.bits < 2 ^ (sc.sizeBytes * 8) := by
    have h := hrel.canonical
    rwa [scalarModulus_eq_two_pow, Nat.mul_comm] at h
  -- The counting intrinsics return a `u32`, which holds any count up to the
  -- operand's bit width.
  have h4 : ValidScalarBytes 4 := Or.inr (Or.inr (Or.inl rfl))
  have hcount : ∀ c, c ≤ sc.sizeBytes * 8 → c < scalarModulus 4 := by
    intro c hc
    have h32 : scalarModulus 4 = 4294967296 := rfl
    omega
  rw [integerIntrinsic_run_eq_mirror]
  cases op with
  | ctpop =>
    have hc := countOnesBits_eq_cpop (w := sc.sizeBytes * 8) (by omega) hcan
    obtain ⟨mr, _, htr, hrel'⟩ := truncateFromUInt_ofNat_rel h4
      (hcount (countOnesBits (sc.sizeBytes * 8) sc.bits) (countOnesBits_le _ _))
    refine bitIntrinsic_simulation_of_some ?_ ?_ hrel'
    · simp only [evalIntegerBitIntrinsic, hwrap, Nat.mul_eq]
    · simp only [miriIntegerIntrinsicRun, toMiriIntegerIntrinsic, bitIntrinsicOutBytes,
        hrel.toBits_eq, hbits, Except.mapError, bind, Except.bind, pure, Except.pure,
        hraw, BEq.beq, reduceCtorEq, decide_false, Bool.false_or, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte, ← hc, htr]
  | ctlz =>
    have hlen := bitLengthBits_eq_log2 _ _ hcan
    by_cases hx0 : sc.bits = 0
    · have hres : sc.sizeBytes * 8 - bitLengthBits (sc.sizeBytes * 8) sc.bits =
          sc.sizeBytes * 8 := by
        rw [hlen, ite_eq_left hx0, Nat.sub_zero]
      obtain ⟨mr, _, htr, hrel'⟩ := truncateFromUInt_ofNat_rel h4
        (hcount (sc.sizeBytes * 8) (Nat.le_refl _))
      refine bitIntrinsic_simulation_of_some ?_ ?_ hrel'
      · simp only [evalIntegerBitIntrinsic, hwrap, Nat.mul_eq, Nat.sub_eq, hres]
      · simp only [miriIntegerIntrinsicRun, toMiriIntegerIntrinsic, bitIntrinsicOutBytes,
          hrel.toBits_eq, hbits, Except.mapError, bind, Except.bind, pure, Except.pure,
          hraw, hbitsNat, BEq.beq, reduceCtorEq, decide_false, Bool.false_or,
          Bool.false_and, Bool.false_eq_true, ↓reduceIte, decide_eq_true hx0, htr]
    · have hres : sc.sizeBytes * 8 - bitLengthBits (sc.sizeBytes * 8) sc.bits =
          sc.sizeBytes * 8 - (Nat.log2 sc.bits + 1) := by
        rw [hlen, ite_eq_right hx0]
      obtain ⟨mr, _, htr, hrel'⟩ := truncateFromUInt_ofNat_rel h4
        (hcount (sc.sizeBytes * 8 - (Nat.log2 sc.bits + 1)) (Nat.sub_le _ _))
      refine bitIntrinsic_simulation_of_some ?_ ?_ hrel'
      · simp only [evalIntegerBitIntrinsic, hwrap, Nat.mul_eq, Nat.sub_eq, hres]
      · simp only [miriIntegerIntrinsicRun, toMiriIntegerIntrinsic, bitIntrinsicOutBytes,
          hrel.toBits_eq, hbits, Except.mapError, bind, Except.bind, pure, Except.pure,
          hraw, hbitsNat, BEq.beq, reduceCtorEq, decide_false, Bool.false_or,
          Bool.false_and, Bool.false_eq_true, ↓reduceIte, decide_eq_false hx0, htr]
  | ctlzNonzero =>
    have hlen := bitLengthBits_eq_log2 _ _ hcan
    by_cases hx0 : sc.bits = 0
    · refine bitIntrinsic_simulation_of_none ?_ ?_
      · simp only [evalIntegerBitIntrinsic, hwrap]
        rw [hx0]
      · simp only [miriIntegerIntrinsicRun, toMiriIntegerIntrinsic, hrel.toBits_eq, hbits,
          Except.mapError, bind, Except.bind, hx0]
        rfl
    · have hres : sc.sizeBytes * 8 - bitLengthBits (sc.sizeBytes * 8) sc.bits =
          sc.sizeBytes * 8 - (Nat.log2 sc.bits + 1) := by
        rw [hlen, ite_eq_right hx0]
      obtain ⟨mr, _, htr, hrel'⟩ := truncateFromUInt_ofNat_rel h4
        (hcount (sc.sizeBytes * 8 - (Nat.log2 sc.bits + 1)) (Nat.sub_le _ _))
      refine bitIntrinsic_simulation_of_some ?_ ?_ hrel'
      · simp only [evalIntegerBitIntrinsic, hwrap, Nat.mul_eq, Nat.sub_eq,
          nat_beq_eq_decide, decide_eq_false hx0, hres]
      · simp only [miriIntegerIntrinsicRun, toMiriIntegerIntrinsic, bitIntrinsicOutBytes,
          hrel.toBits_eq, hbits, Except.mapError, bind, Except.bind, pure, Except.pure,
          hraw, hbitsNat, BEq.beq, reduceCtorEq, decide_false, decide_true, Bool.or_true,
          Bool.and_false, Bool.false_eq_true, ↓reduceIte, decide_eq_false hx0, htr]
  | cttz =>
    obtain ⟨mr, _, htr, hrel'⟩ := truncateFromUInt_ofNat_rel h4
      (hcount (countTrailingZerosBits (sc.sizeBytes * 8) sc.bits)
        (countTrailingZerosBits_le _ _))
    refine bitIntrinsic_simulation_of_some ?_ ?_ hrel'
    · simp only [evalIntegerBitIntrinsic, hwrap, Nat.mul_eq]
    · simp only [miriIntegerIntrinsicRun, toMiriIntegerIntrinsic, bitIntrinsicOutBytes,
        hrel.toBits_eq, hbits, Except.mapError, bind, Except.bind, pure, Except.pure,
        hraw, hbitsNat, BEq.beq, reduceCtorEq, decide_false, Bool.false_or,
        Bool.false_and, Bool.false_eq_true, ↓reduceIte, miriCountTrailingZeros_eq, htr]
  | cttzNonzero =>
    by_cases hx0 : sc.bits = 0
    · refine bitIntrinsic_simulation_of_none ?_ ?_
      · simp only [evalIntegerBitIntrinsic, hwrap]
        rw [hx0]
      · simp only [miriIntegerIntrinsicRun, toMiriIntegerIntrinsic, hrel.toBits_eq, hbits,
          Except.mapError, bind, Except.bind, hx0]
        rfl
    · obtain ⟨mr, _, htr, hrel'⟩ := truncateFromUInt_ofNat_rel h4
        (hcount (countTrailingZerosBits (sc.sizeBytes * 8) sc.bits)
          (countTrailingZerosBits_le _ _))
      refine bitIntrinsic_simulation_of_some ?_ ?_ hrel'
      · simp only [evalIntegerBitIntrinsic, hwrap, Nat.mul_eq, nat_beq_eq_decide,
          decide_eq_false hx0]
      · simp only [miriIntegerIntrinsicRun, toMiriIntegerIntrinsic, bitIntrinsicOutBytes,
          hrel.toBits_eq, hbits, Except.mapError, bind, Except.bind, pure, Except.pure,
          hraw, hbitsNat, BEq.beq, reduceCtorEq, decide_false, decide_true, Bool.true_or,
          Bool.and_false, Bool.false_eq_true, ↓reduceIte, decide_eq_false hx0,
          miriCountTrailingZeros_eq, htr]
  | bswap =>
    have hk : outKind = kind := hkind (Or.inl rfl)
    subst hk
    have hbytes : (translateSizeBytes sc.sizeBytes).bytes.toNat = sc.sizeBytes := by
      rcases hsz with h | h | h | h | h <;> rw [h] <;> rfl
    obtain ⟨mr, _, htr, hrel'⟩ :=
      truncateFromUInt_ofNat_rel hsz (reverseBytesBits_lt sc.sizeBytes sc.bits)
    refine bitIntrinsic_simulation_of_some ?_ ?_ hrel'
    · simp only [evalIntegerBitIntrinsic, hwrap]
    · simp only [miriIntegerIntrinsicRun, toMiriIntegerIntrinsic, bitIntrinsicOutBytes,
        hrel.toBits_eq, hbits, Except.mapError, bind, Except.bind, pure, Except.pure,
        hraw, BEq.beq, reduceCtorEq, decide_false, Bool.false_or, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, hbytes, miriReverseBytes_eq,
        htr]
  | bitreverse =>
    have hk : outKind = kind := hkind (Or.inr rfl)
    subst hk
    have hrb := reverse_shiftLeft_toNat_eq (w := sc.sizeBytes * 8) (by omega) sc.bits
    have hlt :
        reverseBitsBits (sc.sizeBytes * 8) sc.bits < scalarModulus sc.sizeBytes := by
      rw [scalarModulus_eq_two_pow, Nat.mul_comm 8]
      exact reverseBitsBits_lt _ _
    obtain ⟨mr, _, htr, hrel'⟩ := truncateFromUInt_ofNat_rel hsz hlt
    refine bitIntrinsic_simulation_of_some ?_ ?_ hrel'
    · simp only [evalIntegerBitIntrinsic, hwrap, Nat.mul_eq]
    · simp only [miriIntegerIntrinsicRun, toMiriIntegerIntrinsic, bitIntrinsicOutBytes,
        hrel.toBits_eq, hbits, Except.mapError, bind, Except.bind, pure, Except.pure,
        hraw, hbitsNat, BEq.beq, reduceCtorEq, decide_false, Bool.false_or,
        Bool.false_and, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, hrb, htr]

end LeanMiriSpec.Correspondence
