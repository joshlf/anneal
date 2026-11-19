/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.Mir.IeeeFloatCast
import Trusted.Rustc.V2026_06_01.MirSemantics.Places

/-!
# Pure-Kernel IEEE-754 Arithmetic, `miri#5643` NaN Choices & `ucg#630` Ptr-to-Int Policy Prototype

Pure-kernel constructive (`[propext, Quot.sound]`, zero `Classical.choice`, zero
`sorry`, zero host `Float`) prototype covering two coupled Tier-3 TCB extensions
for `Trusted.Rustc.V2026_06_01.MirSemantics`:

1. **IEEE-754 `f32`/`f64` (`binary32`/`binary64`) operations & `miri#5643` NaN
   choices** (§1–§5):
   - Sign-flip negation (`evalFloatNegProto`) preserving all NaN payloads and
     signaling bits;
   - Exact IEEE-754 partial order (`evalFloatPartialCompareProto`) and all six
     comparisons (`evalFloatCmpProto`: `eq`, `ne`, `lt`, `le`, `gt`, `ge`);
   - Single-rounding ties-to-even arithmetic (`evalFloatArithBaseProto`: `add`,
     `sub`, `mul`, `div`, `rem`) matching pinned `Miri.Interpreter.FloatBits`;
   - Mode-parametric `miri#5643` NaN-choice relational semantics
     (`FloatArithMode`, `nanChoicesProto`, `EvalFloatBinOpRel`);
   - Prototype MIR `Rvalue` float dispatcher (`evalRvalueFloatProto`,
     `EvalRvalueFloatRelProto`) plus a constructive witness that existing
     `Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue` silently misdispatches
     `.float` `.unaryOp .neg` and `.binaryOp` to integer scalar operations.

2. **Mode-parametric pointer-to-integer transmute policy** (§6):
   - `Ptr2IntTransmutePolicy` (`.stripProvenance` per `rust-lang/reference#1752`
     vs. `.strictUcg630Ub` per `rust-lang/unsafe-code-guidelines#630`) over
     `AbstractByte`;
   - Policy-parameterized decoders (`decodePtrBytesNoForgeWithPolicy`,
     `decodeScalarLayoutBytesWithPolicy`, `decodeTypedValueFromBytesWithPolicy`,
     `evalByteCastWithPolicy`);
   - Exact correspondence at `.strictUcg630Ub`, structural policy refinement
     (`.strictUcg630Ub → .stripProvenance`), provenance-free equivalence,
     `MaybeUninit<u8>` / raw-pointer policy independence, no-provenance-forgery
     under both policies, and `by rfl` flip-direction separation witnesses.

Every definition and theorem follows projection discipline (`.1`/`.2` instead of
`Prod.casesOn`/`Prod.rec`/`Prod.recOn`).
-/

namespace Anneal.FloatArithAndUcg630Prototype

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.Mir.IeeeFloatCast

/-! ## §1. Bit-Level Helpers & IEEE-754 Sign-Flip Negation (`evalFloatNegProto`) -/

/-- Flip the sign field of a decoded `FloatKind` without quieting NaNs or
altering payloads. -/
def negateFloatKind : FloatKind → FloatKind
  | .zero neg => .zero (!neg)
  | .finite neg n d => .finite (!neg) n d
  | .inf neg => .inf (!neg)
  | .nan neg quiet payload => .nan (!neg) quiet payload

/-- `true` iff `bits` decodes to a signaling NaN (all-ones exponent, nonzero
fraction, and quiet bit `0`). -/
def isSignalingNaNBits (f : IeeeFormat) (bits : Nat) : Bool :=
  match decodeBits f bits with
  | .nan _ false _ => true
  | _ => false

/-- `true` iff `bits` fits in `f.width` bits and decodes to a quiet NaN. -/
def isAdmissibleQuietNaN (f : IeeeFormat) (bits : Nat) : Bool :=
  decide (bits < 2 ^ f.width) && isQuietNaNBits f bits

/-- Bitwise IEEE-754 negation: flips bit `f.width - 1` on canonical
`bits % 2 ^ f.width` without NaN quieting or payload modification (matching
`Miri.Interpreter.FloatBits.negate`, LLVM `fneg`, and IEEE-754 `negate`). -/
def evalFloatNegProto (f : IeeeFormat) (bits : Nat) : Nat :=
  let c := bits % 2 ^ f.width
  let signBit := 2 ^ (f.width - 1)
  if c < signBit then c + signBit else c - signBit

theorem ieeeFormat_width_split (f : IeeeFormat) :
    2 ^ f.width = 2 * 2 ^ (f.width - 1) ∧
    2 ^ (f.width - 1) = 2 ^ f.exponentBits * 2 ^ f.fractionBits ∧
    2 ^ f.fractionBits = 2 * 2 ^ (f.fractionBits - 1) ∧
    0 < 2 ^ (f.width - 1) ∧
    0 < 2 ^ f.fractionBits ∧
    0 < 2 ^ f.exponentBits := by
  cases f <;> decide

private theorem nat_mod_mul_right_div_self (a b c : Nat) (hb : 0 < b) (hc : 0 < c) :
    (a % (b * c)) / b = (a / b) % c := by
  have hbc : 0 < b * c := Nat.mul_pos hb hc
  have h1 : a = b * c * (a / (b * c)) + a % (b * c) := (Nat.div_add_mod a (b * c)).symm
  have h2 : a / b = c * (a / (b * c)) + (a % (b * c)) / b := by
    have heq : a = (a % (b * c)) + b * (c * (a / (b * c))) := by
      rw [← Nat.mul_assoc, Nat.add_comm]; exact h1
    conv => lhs; rw [heq]
    rw [Nat.add_mul_div_left _ _ hb, Nat.add_comm]
  have hlt : (a % (b * c)) / b < c :=
    nat_div_lt_of_lt_mul (Nat.mod_lt a hbc)
  rw [h2, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hlt]

theorem unpackBits_mod_width (f : IeeeFormat) (bits : Nat) :
    unpackBits f (bits % 2 ^ f.width) = unpackBits f bits := by
  unfold unpackBits
  have hw : 2 ^ f.width = 2 ^ (f.width - 1) * 2 := by cases f <;> decide
  have hfe : 2 ^ f.width = 2 ^ f.fractionBits * (2 ^ f.exponentBits * 2) := by cases f <;> decide
  have h1 : ((bits % 2 ^ f.width) / 2 ^ (f.width - 1)) % 2 = (bits / 2 ^ (f.width - 1)) % 2 := by
    rw [hw]
    have hlt : (bits % (2 ^ (f.width - 1) * 2)) / 2 ^ (f.width - 1) < 2 :=
      nat_div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact Nat.mod_lt _ (by cases f <;> decide))
    rw [Nat.mod_eq_of_lt hlt,
        nat_mod_mul_right_div_self bits (2 ^ (f.width - 1)) 2
          (ieeeFormat_width_split f).2.2.2.1 (by decide)]
  have h2 : ((bits % 2 ^ f.width) / 2 ^ f.fractionBits) % 2 ^ f.exponentBits =
      (bits / 2 ^ f.fractionBits) % 2 ^ f.exponentBits := by
    rw [hfe,
        nat_mod_mul_right_div_self bits (2 ^ f.fractionBits) (2 ^ f.exponentBits * 2)
          (ieeeFormat_width_split f).2.2.2.2.1 (by cases f <;> decide)]
    exact Nat.mod_mul_right_mod _ _ 2
  have h3 : (bits % 2 ^ f.width) % 2 ^ f.fractionBits = bits % 2 ^ f.fractionBits := by
    rw [hfe]
    exact Nat.mod_mul_right_mod bits (2 ^ f.fractionBits) (2 ^ f.exponentBits * 2)
  rw [h1, h2, h3]

theorem decodeBits_mod_width (f : IeeeFormat) (bits : Nat) :
    decodeBits f (bits % 2 ^ f.width) = decodeBits f bits := by
  unfold decodeBits
  rw [unpackBits_mod_width]

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
      exact powScale_fst_pos _ 1 _ (Nat.add_pos_left (Nat.two_pow_pos _) _)

theorem evalFloatNegProto_lt (f : IeeeFormat) (bits : Nat) :
    evalFloatNegProto f bits < 2 ^ f.width := by
  unfold evalFloatNegProto
  dsimp only
  have hsplit := (ieeeFormat_width_split f).1
  have hmod : bits % 2 ^ f.width < 2 ^ f.width := Nat.mod_lt _ (Nat.two_pow_pos _)
  split <;> omega

theorem evalFloatNegProto_mod (f : IeeeFormat) (bits : Nat) :
    evalFloatNegProto f (bits % 2 ^ f.width) = evalFloatNegProto f bits := by
  unfold evalFloatNegProto
  rw [Nat.mod_mod]

theorem evalFloatNegProto_involutive (f : IeeeFormat) (bits : Nat) (h : bits < 2 ^ f.width) :
    evalFloatNegProto f (evalFloatNegProto f bits) = bits := by
  have hlt := evalFloatNegProto_lt f bits
  unfold evalFloatNegProto at hlt ⊢
  dsimp only at hlt ⊢
  rw [Nat.mod_eq_of_lt h] at hlt ⊢
  rw [Nat.mod_eq_of_lt hlt]
  have hsplit := (ieeeFormat_width_split f).1
  split <;> split <;> omega

theorem unpackBits_evalFloatNegProto (f : IeeeFormat) (bits : Nat) :
    unpackBits f (evalFloatNegProto f bits) =
      { unpackBits f bits with neg := !(unpackBits f bits).neg } := by
  have hmod_unpack := unpackBits_mod_width f bits
  rw [← hmod_unpack]
  have hc : bits % 2 ^ f.width < 2 ^ f.width := Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold evalFloatNegProto
  dsimp only
  generalize bits % 2 ^ f.width = c at hc ⊢
  have hsplit := ieeeFormat_width_split f
  have hws : 2 ^ f.width = 2 * 2 ^ (f.width - 1) := hsplit.1
  have hef : 2 ^ (f.width - 1) = 2 ^ f.exponentBits * 2 ^ f.fractionBits := hsplit.2.1
  have hfb_pos : 0 < 2 ^ f.fractionBits := hsplit.2.2.2.2.1
  have hsb_pos : 0 < 2 ^ (f.width - 1) := hsplit.2.2.2.1
  unfold unpackBits
  dsimp only
  by_cases hlt : c < 2 ^ (f.width - 1)
  · rw [if_pos' hlt]
    have hdiv_c : c / 2 ^ (f.width - 1) = 0 := Nat.div_eq_of_lt hlt
    have hdiv_add : (c + 2 ^ (f.width - 1)) / 2 ^ (f.width - 1) = 1 := by
      rw [Nat.add_div_right _ hsb_pos, hdiv_c]
    have hexp : ((c + 2 ^ (f.width - 1)) / 2 ^ f.fractionBits) % 2 ^ f.exponentBits =
        (c / 2 ^ f.fractionBits) % 2 ^ f.exponentBits := by
      rw [hef, Nat.add_mul_div_right _ _ hfb_pos, Nat.add_mod_right]
    have hfrac : (c + 2 ^ (f.width - 1)) % 2 ^ f.fractionBits = c % 2 ^ f.fractionBits := by
      rw [hef, Nat.add_mul_mod_self_right]
    rw [hdiv_c, hdiv_add, hexp, hfrac]
    rfl
  · rw [if_neg' hlt]
    have hge : 2 ^ (f.width - 1) ≤ c := Nat.le_of_not_lt hlt
    have hsub_lt : c - 2 ^ (f.width - 1) < 2 ^ (f.width - 1) := by omega
    have hdiv_sub : (c - 2 ^ (f.width - 1)) / 2 ^ (f.width - 1) = 0 := Nat.div_eq_of_lt hsub_lt
    have hdiv_c : c / 2 ^ (f.width - 1) = 1 := by
      have hc_eq : c = (c - 2 ^ (f.width - 1)) + 2 ^ (f.width - 1) := by omega
      conv => lhs; rw [hc_eq]
      rw [Nat.add_div_right _ hsb_pos, hdiv_sub]
    have hexp : ((c - 2 ^ (f.width - 1)) / 2 ^ f.fractionBits) % 2 ^ f.exponentBits =
        (c / 2 ^ f.fractionBits) % 2 ^ f.exponentBits := by
      have hc_eq : c = (c - 2 ^ (f.width - 1)) + 2 ^ (f.width - 1) := by omega
      conv => rhs; rw [hc_eq]
      rw [hef, Nat.add_mul_div_right _ _ hfb_pos, Nat.add_mod_right]
    have hfrac : (c - 2 ^ (f.width - 1)) % 2 ^ f.fractionBits = c % 2 ^ f.fractionBits := by
      have hc_eq : c = (c - 2 ^ (f.width - 1)) + 2 ^ (f.width - 1) := by omega
      conv => rhs; rw [hc_eq]
      rw [hef, Nat.add_mul_mod_self_right]
    rw [hdiv_c, hdiv_sub, hexp, hfrac]
    rfl

theorem decodeBits_evalFloatNegProto (f : IeeeFormat) (bits : Nat) :
    decodeBits f (evalFloatNegProto f bits) = negateFloatKind (decodeBits f bits) := by
  unfold decodeBits
  rw [unpackBits_evalFloatNegProto]
  dsimp only
  split
  · split <;> rfl
  · split
    · split <;> rfl
    · rfl

theorem decodeBits_evalFloatNegProto_nan (f : IeeeFormat) (bits : Nat) (neg quiet : Bool)
    (payload : Nat) (h : decodeBits f bits = .nan neg quiet payload) :
    decodeBits f (evalFloatNegProto f bits) = .nan (!neg) quiet payload := by
  rw [decodeBits_evalFloatNegProto, h]; rfl

theorem isNaNBits_evalFloatNegProto (f : IeeeFormat) (bits : Nat) :
    isNaNBits f (evalFloatNegProto f bits) = isNaNBits f bits := by
  unfold isNaNBits
  rw [decodeBits_evalFloatNegProto]
  cases decodeBits f bits <;> rfl

theorem isQuietNaNBits_evalFloatNegProto (f : IeeeFormat) (bits : Nat) :
    isQuietNaNBits f (evalFloatNegProto f bits) = isQuietNaNBits f bits := by
  unfold isQuietNaNBits
  rw [decodeBits_evalFloatNegProto]
  cases decodeBits f bits <;> rfl

theorem isSignalingNaNBits_evalFloatNegProto (f : IeeeFormat) (bits : Nat) :
    isSignalingNaNBits f (evalFloatNegProto f bits) = isSignalingNaNBits f bits := by
  unfold isSignalingNaNBits
  rw [decodeBits_evalFloatNegProto]
  cases decodeBits f bits with
  | nan _ q _ => cases q <;> rfl
  | _ => rfl

theorem isAdmissibleQuietNaN_evalFloatNegProto (f : IeeeFormat) (bits : Nat)
    (hq : isQuietNaNBits f bits = true) :
    isAdmissibleQuietNaN f (evalFloatNegProto f bits) = true := by
  unfold isAdmissibleQuietNaN
  rw [decide_eq_true (evalFloatNegProto_lt f bits), isQuietNaNBits_evalFloatNegProto, hq]
  rfl

theorem evalFloatNegProto_encodeBits (f : IeeeFormat) (neg : Bool) (E F : Nat)
    (hE : E < 2 ^ f.exponentBits) (hF : F < 2 ^ f.fractionBits) :
    evalFloatNegProto f (encodeBits f neg E F) = encodeBits f (!neg) E F := by
  have hlt1 := encodeBits_lt f neg E F hE hF
  have hlt2 := encodeBits_lt f (!neg) E F hE hF
  have hsb : E * 2 ^ f.fractionBits + F < 2 ^ (f.width - 1) := by
    have hef := (ieeeFormat_width_split f).2.1
    have hmul : E * 2 ^ f.fractionBits + 2 ^ f.fractionBits ≤ 2 ^ f.exponentBits * 2 ^ f.fractionBits := by
      have : (E + 1) * 2 ^ f.fractionBits ≤ 2 ^ f.exponentBits * 2 ^ f.fractionBits :=
        Nat.mul_le_mul_right _ hE
      rw [Nat.add_mul, Nat.one_mul] at this
      exact this
    omega
  unfold evalFloatNegProto
  dsimp only
  rw [Nat.mod_eq_of_lt hlt1]
  unfold encodeBits zeroBits
  cases neg <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  · rw [if_pos' hsb]; omega
  · rw [if_neg' (by omega)]; omega

theorem evalFloatNegProto_zeroBits (f : IeeeFormat) (neg : Bool) :
    evalFloatNegProto f (zeroBits f neg) = zeroBits f (!neg) := by
  rw [zeroBits_eq_encodeBits, zeroBits_eq_encodeBits]
  exact evalFloatNegProto_encodeBits f neg 0 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _)

theorem evalFloatNegProto_infBits (f : IeeeFormat) (neg : Bool) :
    evalFloatNegProto f (infBits f neg) = infBits f (!neg) :=
  evalFloatNegProto_encodeBits f neg (2 ^ f.exponentBits - 1) 0
    (Nat.sub_lt (Nat.two_pow_pos _) (by decide)) (Nat.two_pow_pos _)

theorem evalFloatNegProto_xor (f : IeeeFormat) (bits : Nat) :
    evalFloatNegProto f bits = Nat.xor (bits % 2 ^ f.width) (2 ^ (f.width - 1)) := by
  have hc : bits % 2 ^ f.width < 2 ^ f.width := Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold evalFloatNegProto
  dsimp only
  generalize bits % 2 ^ f.width = c at hc ⊢
  have hws := (ieeeFormat_width_split f).1
  change (if c < 2 ^ (f.width - 1) then c + 2 ^ (f.width - 1) else c - 2 ^ (f.width - 1)) =
    c ^^^ 2 ^ (f.width - 1)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hlt : c < 2 ^ (f.width - 1)
  · rw [if_pos' hlt]
    have hlor : c + 2 ^ (f.width - 1) = c ||| 2 ^ (f.width - 1) := by
      have h1 := mul_two_pow_add_eq_lor 1 c (f.width - 1) hlt
      rw [Nat.one_mul] at h1
      change c + 2 ^ (f.width - 1) = c ||| 2 ^ (f.width - 1)
      rw [Nat.add_comm, h1]
      exact Nat.or_comm (2 ^ (f.width - 1)) c
    rw [hlor, Nat.testBit_or, Nat.testBit_two_pow]
    by_cases hi : f.width - 1 = i
    · subst hi
      have htb : c.testBit (f.width - 1) = false := Nat.testBit_lt_two_pow hlt
      simp [htb]
    · simp [hi]
  · rw [if_neg' hlt]
    have hd : c - 2 ^ (f.width - 1) < 2 ^ (f.width - 1) := by omega
    have hc_eq : c = (c - 2 ^ (f.width - 1)) + 2 ^ (f.width - 1) := by omega
    have hlor : c = (c - 2 ^ (f.width - 1)) ||| 2 ^ (f.width - 1) := by
      have h1 := mul_two_pow_add_eq_lor 1 (c - 2 ^ (f.width - 1)) (f.width - 1) hd
      rw [Nat.one_mul] at h1
      conv => lhs; rw [hc_eq, Nat.add_comm, h1]
      exact Nat.or_comm (2 ^ (f.width - 1)) (c - 2 ^ (f.width - 1))
    conv => rhs; rw [hlor]
    rw [Nat.testBit_or, Nat.testBit_two_pow]
    by_cases hi : f.width - 1 = i
    · subst hi
      have htb : (c - 2 ^ (f.width - 1)).testBit (f.width - 1) = false := Nat.testBit_lt_two_pow hd
      simp [htb]
    · simp [hi]

/-! ## §2. IEEE-754 Partial Order & Comparisons (`evalFloatPartialCompareProto`, `evalFloatCmpProto`) -/

/-- Signed numerator `(-1)^neg * n`. -/
def signedNum (neg : Bool) (n : Nat) : Int :=
  if neg then -(Int.ofNat n) else Int.ofNat n

theorem signedNum_neg (neg : Bool) (n : Nat) :
    signedNum (!neg) n = -signedNum neg n := by
  cases neg <;> simp [signedNum]

/-- `true` iff `op` is one of the 6 IEEE-754 comparison `BinOp`s. -/
def isFloatCmpBinOp : BinOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

/-- IEEE-754 partial order on two bit patterns of format `f`:
- either operand NaN → `none`;
- `-0.0` and `+0.0` compare `.some .eq`;
- `-Inf < finite/zero < +Inf`;
- nonzero finite values compare exact cross-multiplied signed rationals. -/
def evalFloatPartialCompareProto (f : IeeeFormat) (lhs rhs : Nat) : Option Ordering :=
  match decodeBits f lhs, decodeBits f rhs with
  | .nan _ _ _, _ | _, .nan _ _ _ => .none
  | .inf ln, .inf rn =>
    .some (if ln == rn then .eq else if ln then .lt else .gt)
  | .inf ln, _ => .some (if ln then .lt else .gt)
  | _, .inf rn => .some (if rn then .gt else .lt)
  | .zero _, .zero _ => .some .eq
  | .zero _, .finite rn _ _ => .some (if rn then .gt else .lt)
  | .finite ln _ _, .zero _ => .some (if ln then .lt else .gt)
  | .finite ln lnum lden, .finite rn rnum rden =>
    .some (compare (signedNum ln lnum * Int.ofNat rden) (signedNum rn rnum * Int.ofNat lden))

/-- IEEE-754 comparison result (`Bool`) for the six MIR comparison `BinOp`s
(`eq`, `ne`, `lt`, `le`, `gt`, `ge`). Non-comparison `BinOp`s return `false`. -/
def evalFloatCmpProto (op : BinOp) (f : IeeeFormat) (lhs rhs : Nat) : Bool :=
  let ord := evalFloatPartialCompareProto f lhs rhs
  match op with
  | .eq => ord == .some .eq
  | .ne => ord != .some .eq
  | .lt => ord == .some .lt
  | .le => ord == .some .lt || ord == .some .eq
  | .gt => ord == .some .gt
  | .ge => ord == .some .gt || ord == .some .eq
  | _ => false

/-- Partial `Option Bool` variant returning `.none` on non-comparison `BinOp`s. -/
def evalFloatCmpProto? (op : BinOp) (f : IeeeFormat) (lhs rhs : Nat) : Option Bool :=
  if isFloatCmpBinOp op then .some (evalFloatCmpProto op f lhs rhs) else .none

private theorem int_compare_swap (a b : Int) :
    compare a b = (compare b a).swap := by
  simp only [compare, compareOfLessAndEq]
  by_cases h1 : a < b
  · rw [if_pos' h1, if_neg' (by omega), if_neg' (by omega)]; rfl
  · by_cases h2 : a = b
    · rw [if_neg' h1, if_pos' h2, if_neg' (by omega), if_pos' h2.symm]; rfl
    · rw [if_neg' h1, if_neg' h2, if_pos' (by omega)]; rfl

private theorem int_compare_neg (a b : Int) :
    compare (-a) (-b) = compare b a := by
  simp only [compare, compareOfLessAndEq]
  by_cases h1 : b < a
  · rw [if_pos' h1, if_pos' (by omega)]
  · by_cases h2 : b = a
    · rw [if_neg' h1, if_pos' h2, if_neg' (by omega), if_pos' (by omega)]
    · rw [if_neg' h1, if_neg' h2, if_neg' (by omega), if_neg' (by omega)]

private theorem int_compare_eq_lt_iff (a b : Int) :
    compare a b = .lt ↔ a < b := by
  simp only [compare, compareOfLessAndEq]
  by_cases h1 : a < b
  · rw [if_pos' h1]; exact ⟨fun _ => h1, fun _ => rfl⟩
  · rw [if_neg' h1]
    by_cases h2 : a = b
    · rw [if_pos' h2]; exact ⟨fun h => (by cases h), fun h => absurd h h1⟩
    · rw [if_neg' h2]; exact ⟨fun h => (by cases h), fun h => absurd h h1⟩

private theorem int_compare_eq_eq_iff (a b : Int) :
    compare a b = .eq ↔ a = b := by
  simp only [compare, compareOfLessAndEq]
  by_cases h1 : a < b
  · rw [if_pos' h1]; exact ⟨fun h => (by cases h), fun h => (by omega)⟩
  · rw [if_neg' h1]
    by_cases h2 : a = b
    · rw [if_pos' h2]; exact ⟨fun _ => h2, fun _ => rfl⟩
    · rw [if_neg' h2]; exact ⟨fun h => (by cases h), fun h => absurd h h2⟩

private theorem int_compare_eq_gt_iff (a b : Int) :
    compare a b = .gt ↔ b < a := by
  simp only [compare, compareOfLessAndEq]
  by_cases h1 : a < b
  · rw [if_pos' h1]; exact ⟨fun h => (by cases h), fun h => (by omega)⟩
  · rw [if_neg' h1]
    by_cases h2 : a = b
    · rw [if_pos' h2]; exact ⟨fun h => (by cases h), fun h => (by omega)⟩
    · rw [if_neg' h2]; exact ⟨fun _ => (by omega), fun _ => rfl⟩

theorem evalFloatPartialCompareProto_swap (f : IeeeFormat) (a b : Nat) :
    evalFloatPartialCompareProto f a b = (evalFloatPartialCompareProto f b a).map Ordering.swap := by
  unfold evalFloatPartialCompareProto
  cases decodeBits f a with
  | nan _ _ _ => cases decodeBits f b <;> rfl
  | inf ln =>
    cases decodeBits f b with
    | nan _ _ _ => rfl
    | inf rn => cases ln <;> cases rn <;> rfl
    | zero _ => cases ln <;> rfl
    | finite _ _ _ => cases ln <;> rfl
  | zero _ =>
    cases decodeBits f b with
    | nan _ _ _ => rfl
    | inf rn => cases rn <;> rfl
    | zero _ => rfl
    | finite rn _ _ => cases rn <;> rfl
  | finite ln lnum lden =>
    cases decodeBits f b with
    | nan _ _ _ => rfl
    | inf rn => cases rn <;> rfl
    | zero _ => cases ln <;> rfl
    | finite rn rnum rden =>
      simp only [Option.map_some]
      exact congrArg Option.some (int_compare_swap _ _)

theorem evalFloatPartialCompareProto_neg (f : IeeeFormat) (a b : Nat) :
    evalFloatPartialCompareProto f (evalFloatNegProto f a) (evalFloatNegProto f b) =
      evalFloatPartialCompareProto f b a := by
  unfold evalFloatPartialCompareProto
  rw [decodeBits_evalFloatNegProto, decodeBits_evalFloatNegProto]
  cases decodeBits f a with
  | nan _ _ _ => cases decodeBits f b <;> rfl
  | inf ln =>
    cases decodeBits f b with
    | nan _ _ _ => rfl
    | inf rn => cases ln <;> cases rn <;> rfl
    | zero _ => cases ln <;> rfl
    | finite _ _ _ => cases ln <;> rfl
  | zero _ =>
    cases decodeBits f b with
    | nan _ _ _ => rfl
    | inf rn => cases rn <;> rfl
    | zero _ => rfl
    | finite rn _ _ => cases rn <;> rfl
  | finite ln lnum lden =>
    cases decodeBits f b with
    | nan _ _ _ => rfl
    | inf rn => cases rn <;> rfl
    | zero _ => cases ln <;> rfl
    | finite rn rnum rden =>
      dsimp only [negateFloatKind]
      rw [signedNum_neg, signedNum_neg, Int.neg_mul, Int.neg_mul, int_compare_neg]

theorem evalFloatCmpProto_ne_eq_not_eq (f : IeeeFormat) (a b : Nat) :
    evalFloatCmpProto .ne f a b = !evalFloatCmpProto .eq f a b := by
  unfold evalFloatCmpProto
  cases evalFloatPartialCompareProto f a b with
  | none => rfl
  | some o => cases o <;> rfl

theorem evalFloatCmpProto_gt_eq_lt_swap (f : IeeeFormat) (a b : Nat) :
    evalFloatCmpProto .gt f a b = evalFloatCmpProto .lt f b a := by
  unfold evalFloatCmpProto
  rw [evalFloatPartialCompareProto_swap]
  cases evalFloatPartialCompareProto f b a with
  | none => rfl
  | some o => cases o <;> rfl

theorem evalFloatCmpProto_ge_eq_le_swap (f : IeeeFormat) (a b : Nat) :
    evalFloatCmpProto .ge f a b = evalFloatCmpProto .le f b a := by
  unfold evalFloatCmpProto
  rw [evalFloatPartialCompareProto_swap]
  cases evalFloatPartialCompareProto f b a with
  | none => rfl
  | some o => cases o <;> rfl

theorem evalFloatCmpProto_eq_refl_iff_not_nan (f : IeeeFormat) (x : Nat) :
    evalFloatCmpProto .eq f x x = !isNaNBits f x := by
  unfold evalFloatCmpProto evalFloatPartialCompareProto isNaNBits
  cases decodeBits f x with
  | nan _ _ _ => rfl
  | inf n => cases n <;> rfl
  | zero _ => rfl
  | finite n num den =>
    dsimp only
    rw [(int_compare_eq_eq_iff _ _).mpr rfl]
    rfl

theorem evalFloatCmpProto_lt_irrefl (f : IeeeFormat) (x : Nat) :
    evalFloatCmpProto .lt f x x = false := by
  unfold evalFloatCmpProto evalFloatPartialCompareProto
  cases decodeBits f x with
  | nan _ _ _ => rfl
  | inf n => cases n <;> rfl
  | zero _ => rfl
  | finite n num den =>
    dsimp only
    rw [(int_compare_eq_eq_iff _ _).mpr rfl]
    rfl

theorem evalFloatCmpProto_eq_symm (f : IeeeFormat) (a b : Nat) :
    evalFloatCmpProto .eq f a b = evalFloatCmpProto .eq f b a := by
  unfold evalFloatCmpProto
  rw [evalFloatPartialCompareProto_swap]
  cases evalFloatPartialCompareProto f b a with
  | none => rfl
  | some o => cases o <;> rfl

theorem evalFloatCmpProto_nan_left (op : BinOp) (f : IeeeFormat) (a b : Nat)
    (ha : isNaNBits f a = true) :
    evalFloatCmpProto op f a b =
      match op with
      | .ne => true
      | _ => false := by
  have hord : evalFloatPartialCompareProto f a b = .none := by
    unfold evalFloatPartialCompareProto
    unfold isNaNBits at ha
    cases hd : decodeBits f a with
    | nan _ _ _ => rfl
    | _ => rw [hd] at ha; cases ha
  unfold evalFloatCmpProto
  rw [hord]
  cases op <;> rfl

theorem evalFloatCmpProto_nan_right (op : BinOp) (f : IeeeFormat) (a b : Nat)
    (hb : isNaNBits f b = true) :
    evalFloatCmpProto op f a b =
      match op with
      | .ne => true
      | _ => false := by
  have hord : evalFloatPartialCompareProto f a b = .none := by
    unfold evalFloatPartialCompareProto
    unfold isNaNBits at hb
    cases hd : decodeBits f b with
    | nan _ _ _ => cases decodeBits f a <;> rfl
    | _ => rw [hd] at hb; cases hb
  unfold evalFloatCmpProto
  rw [hord]
  cases op <;> rfl

theorem evalFloatCmpProto_negZero_eq_posZero (f : IeeeFormat) :
    evalFloatCmpProto .eq f (zeroBits f true) (zeroBits f false) = true ∧
    evalFloatCmpProto .ne f (zeroBits f true) (zeroBits f false) = false ∧
    evalFloatCmpProto .lt f (zeroBits f true) (zeroBits f false) = false ∧
    evalFloatCmpProto .le f (zeroBits f true) (zeroBits f false) = true ∧
    evalFloatCmpProto .gt f (zeroBits f true) (zeroBits f false) = false ∧
    evalFloatCmpProto .ge f (zeroBits f true) (zeroBits f false) = true := by
  have hord : evalFloatPartialCompareProto f (zeroBits f true) (zeroBits f false) = .some .eq := by
    unfold evalFloatPartialCompareProto
    rw [decodeBits_zeroBits, decodeBits_zeroBits]
  unfold evalFloatCmpProto
  rw [hord]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact bit-pattern recovery when `decodeBits` yields `.zero`, `.inf`, or `.finite`. -/
theorem bits_eq_zeroBits_of_decodeBits_zero (f : IeeeFormat) (bits : Nat) (neg : Bool)
    (hbits : bits < 2 ^ f.width) (hdec : decodeBits f bits = .zero neg) :
    bits = zeroBits f neg := by
  have hself := evalFloatToFloatRoundTiesToEven_self_eq f bits hbits
  unfold evalFloatToFloatRoundTiesToEven at hself
  rw [hdec] at hself
  exact hself.symm

theorem bits_eq_infBits_of_decodeBits_inf (f : IeeeFormat) (bits : Nat) (neg : Bool)
    (hbits : bits < 2 ^ f.width) (hdec : decodeBits f bits = .inf neg) :
    bits = infBits f neg := by
  have hself := evalFloatToFloatRoundTiesToEven_self_eq f bits hbits
  unfold evalFloatToFloatRoundTiesToEven at hself
  rw [hdec] at hself
  exact hself.symm

theorem roundRatioTiesToEven_eq_bits_of_decodeBits_finite (f : IeeeFormat) (bits : Nat)
    (neg : Bool) (n d : Nat) (hbits : bits < 2 ^ f.width)
    (hdec : decodeBits f bits = .finite neg n d) :
    roundRatioTiesToEven f neg n d = bits := by
  have hself := evalFloatToFloatRoundTiesToEven_self_eq f bits hbits
  unfold evalFloatToFloatRoundTiesToEven at hself
  rw [hdec] at hself
  exact hself

/-- Exact IEEE-754 equality characterization: two in-width bit patterns compare
equal iff either they are identical non-NaNs or they are `-0.0` and `+0.0`. -/
theorem evalFloatCmpProto_eq_iff_bits_or_signedZero (f : IeeeFormat) (a b : Nat)
    (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    evalFloatCmpProto .eq f a b = true ↔
      (isNaNBits f a = false ∧
        (a = b ∨
         (a = zeroBits f false ∧ b = zeroBits f true) ∨
         (a = zeroBits f true ∧ b = zeroBits f false))) := by
  constructor
  · intro heq
    unfold evalFloatCmpProto evalFloatPartialCompareProto at heq
    cases hda : decodeBits f a with
    | nan _ _ _ => rw [hda] at heq; cases heq
    | inf ln =>
      have hna : isNaNBits f a = false := by unfold isNaNBits; rw [hda]
      refine ⟨hna, ?_⟩
      cases hdb : decodeBits f b with
      | inf rn =>
        rw [hda, hdb] at heq
        have hlr : ln = rn := by cases ln <;> cases rn <;> first | rfl | cases heq
        subst hlr
        left
        rw [bits_eq_infBits_of_decodeBits_inf f a ln ha hda,
            bits_eq_infBits_of_decodeBits_inf f b ln hb hdb]
      | nan _ _ _ => rw [hda, hdb] at heq; cases heq
      | zero _ => rw [hda, hdb] at heq; cases ln <;> cases heq
      | finite _ _ _ => rw [hda, hdb] at heq; cases ln <;> cases heq
    | zero ln =>
      have hna : isNaNBits f a = false := by unfold isNaNBits; rw [hda]
      refine ⟨hna, ?_⟩
      cases hdb : decodeBits f b with
      | zero rn =>
        have ha0 := bits_eq_zeroBits_of_decodeBits_zero f a ln ha hda
        have hb0 := bits_eq_zeroBits_of_decodeBits_zero f b rn hb hdb
        cases ln <;> cases rn
        · exact Or.inl (ha0.trans hb0.symm)
        · exact Or.inr (Or.inl ⟨ha0, hb0⟩)
        · exact Or.inr (Or.inr ⟨ha0, hb0⟩)
        · exact Or.inl (ha0.trans hb0.symm)
      | nan _ _ _ => rw [hda, hdb] at heq; cases heq
      | inf rn => rw [hda, hdb] at heq; cases rn <;> cases heq
      | finite rn _ _ => rw [hda, hdb] at heq; cases rn <;> cases heq
    | finite ln lnum lden =>
      have hna : isNaNBits f a = false := by unfold isNaNBits; rw [hda]
      refine ⟨hna, ?_⟩
      cases hdb : decodeBits f b with
      | finite rn rnum rden =>
        rw [hda, hdb] at heq
        dsimp only at heq
        have hcmp : compare (signedNum ln lnum * Int.ofNat rden) (signedNum rn rnum * Int.ofNat lden) = .eq := by
          cases hc : compare (signedNum ln lnum * Int.ofNat rden) (signedNum rn rnum * Int.ofNat lden) <;>
            rw [hc] at heq <;> first | rfl | cases heq
        have hcross : signedNum ln lnum * Int.ofNat rden = signedNum rn rnum * Int.ofNat lden :=
          (int_compare_eq_eq_iff _ _).mp hcmp
        have hlnum_pos := decodeBits_finite_num_pos f a ln lnum lden hda
        have hlden_pos := decodeBits_finite_den_pos f a ln lnum lden hda
        have hrnum_pos := decodeBits_finite_num_pos f b rn rnum rden hdb
        have hrden_pos := decodeBits_finite_den_pos f b rn rnum rden hdb
        have hsign : ln = rn := by
          cases ln <;> cases rn
          · rfl
          · unfold signedNum at hcross
            have h1 : (0 : Int) < Int.ofNat lnum * Int.ofNat rden :=
              Int.mul_pos (Int.ofNat_lt.mpr hlnum_pos) (Int.ofNat_lt.mpr hrden_pos)
            have h2 : (0 : Int) < Int.ofNat rnum * Int.ofNat lden :=
              Int.mul_pos (Int.ofNat_lt.mpr hrnum_pos) (Int.ofNat_lt.mpr hlden_pos)
            simp only [Bool.false_eq_true, ↓reduceIte, Int.neg_mul] at hcross
            omega
          · unfold signedNum at hcross
            have h1 : (0 : Int) < Int.ofNat lnum * Int.ofNat rden :=
              Int.mul_pos (Int.ofNat_lt.mpr hlnum_pos) (Int.ofNat_lt.mpr hrden_pos)
            have h2 : (0 : Int) < Int.ofNat rnum * Int.ofNat lden :=
              Int.mul_pos (Int.ofNat_lt.mpr hrnum_pos) (Int.ofNat_lt.mpr hlden_pos)
            simp only [Bool.false_eq_true, ↓reduceIte, Int.neg_mul] at hcross
            omega
          · rfl
        subst hsign
        have hnat : lnum * rden = rnum * lden := by
          unfold signedNum at hcross
          cases ln
          · simp only [Bool.false_eq_true, ↓reduceIte] at hcross
            exact Int.ofNat.inj hcross
          · simp only [↓reduceIte, Int.neg_mul] at hcross
            have hpos := Int.neg_inj.mp hcross
            exact Int.ofNat.inj hpos
        left
        rw [← roundRatioTiesToEven_eq_bits_of_decodeBits_finite f a ln lnum lden ha hda,
            ← roundRatioTiesToEven_eq_bits_of_decodeBits_finite f b ln rnum rden hb hdb,
            ← roundRatioBits_tiesToEven, ← roundRatioBits_tiesToEven]
        exact roundRatioBits_congr .tiesToEven f ln lnum lden rnum rden hlden_pos hrden_pos hnat
      | nan _ _ _ => rw [hda, hdb] at heq; cases heq
      | inf rn => rw [hda, hdb] at heq; cases rn <;> cases heq
      | zero _ => rw [hda, hdb] at heq; cases ln <;> cases heq
  · rintro ⟨hna, hdisj⟩
    rcases hdisj with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [evalFloatCmpProto_eq_refl_iff_not_nan, hna]; rfl
    · rw [evalFloatCmpProto_eq_symm]; exact (evalFloatCmpProto_negZero_eq_posZero f).1
    · exact (evalFloatCmpProto_negZero_eq_posZero f).1

/-- Antisymmetry of `<=` up to signed-zero equivalence. -/
theorem evalFloatCmpProto_le_antisym (f : IeeeFormat) (a b : Nat)
    (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width)
    (hab : evalFloatCmpProto .le f a b = true)
    (hba : evalFloatCmpProto .le f b a = true) :
    evalFloatCmpProto .eq f a b = true ∧
      (a = b ∨
       (a = zeroBits f false ∧ b = zeroBits f true) ∨
       (a = zeroBits f true ∧ b = zeroBits f false)) := by
  have heq : evalFloatCmpProto .eq f a b = true := by
    unfold evalFloatCmpProto at hab hba ⊢
    rw [evalFloatPartialCompareProto_swap f b a] at hba
    cases hord : evalFloatPartialCompareProto f a b with
    | none => rw [hord] at hab; cases hab
    | some o =>
      rw [hord] at hab hba
      cases o with
      | lt => cases hba
      | eq => rfl
      | gt => cases hab
  exact ⟨heq, ((evalFloatCmpProto_eq_iff_bits_or_signedZero f a b ha hb).mp heq).2⟩

/-- Helper encoding non-NaN `FloatKind` into an ordered extended-rational view for
uniform transitivity and totality proofs. -/
private inductive ExtRat : Type where
  | negInf : ExtRat
  | fin (num : Int) (den : Nat) : ExtRat
  | posInf : ExtRat

private def floatKindToExtRat : FloatKind → Option ExtRat
  | .nan _ _ _ => .none
  | .inf true => .some .negInf
  | .inf false => .some .posInf
  | .zero _ => .some (.fin 0 1)
  | .finite neg n d => .some (.fin (signedNum neg n) d)

private def extRatCmp : ExtRat → ExtRat → Ordering
  | .negInf, .negInf => .eq
  | .negInf, _ => .lt
  | _, .negInf => .gt
  | .posInf, .posInf => .eq
  | .posInf, _ => .gt
  | _, .posInf => .lt
  | .fin a da, .fin b db => compare (a * Int.ofNat db) (b * Int.ofNat da)

private theorem evalFloatPartialCompareProto_eq_extRatCmp (f : IeeeFormat) (a b : Nat) :
    evalFloatPartialCompareProto f a b =
      match floatKindToExtRat (decodeBits f a), floatKindToExtRat (decodeBits f b) with
      | .some ea, .some eb => .some (extRatCmp ea eb)
      | _, _ => .none := by
  unfold evalFloatPartialCompareProto
  cases hda : decodeBits f a with
  | nan _ _ _ => cases decodeBits f b <;> rfl
  | inf ln =>
    cases hdb : decodeBits f b with
    | nan _ _ _ => cases ln <;> rfl
    | inf rn => cases ln <;> cases rn <;> rfl
    | zero _ => cases ln <;> rfl
    | finite _ _ _ => cases ln <;> rfl
  | zero _ =>
    cases hdb : decodeBits f b with
    | nan _ _ _ => rfl
    | inf rn => cases rn <;> rfl
    | zero _ => rfl
    | finite rn rnum rden =>
      have hpos : (0 : Int) < Int.ofNat rnum := Int.ofNat_lt.mpr (decodeBits_finite_num_pos f b rn rnum rden hdb)
      dsimp only [floatKindToExtRat, extRatCmp, signedNum]
      cases rn
      · simp only [Bool.false_eq_true, ↓reduceIte, Int.zero_mul]
        have hmul : Int.ofNat rnum * Int.ofNat 1 = Int.ofNat rnum := Int.mul_one _
        rw [hmul]
        exact congrArg Option.some ((int_compare_eq_lt_iff 0 (Int.ofNat rnum)).mpr hpos).symm
      · simp only [↓reduceIte, Int.zero_mul]
        have hmul : -Int.ofNat rnum * Int.ofNat 1 = -Int.ofNat rnum := Int.mul_one _
        rw [hmul]
        exact congrArg Option.some ((int_compare_eq_gt_iff 0 (-Int.ofNat rnum)).mpr (by omega)).symm
  | finite ln lnum lden =>
    cases hdb : decodeBits f b with
    | nan _ _ _ => rfl
    | inf rn => cases rn <;> rfl
    | zero _ =>
      have hpos : (0 : Int) < Int.ofNat lnum := Int.ofNat_lt.mpr (decodeBits_finite_num_pos f a ln lnum lden hda)
      dsimp only [floatKindToExtRat, extRatCmp, signedNum]
      cases ln
      · simp only [Bool.false_eq_true, ↓reduceIte, Int.zero_mul]
        have hmul : Int.ofNat lnum * Int.ofNat 1 = Int.ofNat lnum := Int.mul_one _
        rw [hmul]
        exact congrArg Option.some ((int_compare_eq_gt_iff (Int.ofNat lnum) 0).mpr hpos).symm
      · simp only [↓reduceIte, Int.zero_mul]
        have hmul : -Int.ofNat lnum * Int.ofNat 1 = -Int.ofNat lnum := Int.mul_one _
        rw [hmul]
        exact congrArg Option.some ((int_compare_eq_lt_iff (-Int.ofNat lnum) 0).mpr (by omega)).symm
    | finite rn rnum rden => rfl

private theorem floatKindToExtRat_den_pos (f : IeeeFormat) (bits : Nat) (num : Int) (den : Nat)
    (h : floatKindToExtRat (decodeBits f bits) = .some (.fin num den)) : 0 < den := by
  cases hd : decodeBits f bits with
  | nan _ _ _ => rw [hd] at h; cases h
  | inf b => rw [hd] at h; cases b <;> cases h
  | zero _ => rw [hd] at h; injection h with heq; injection heq with _ hden; omega
  | finite neg n d =>
    rw [hd] at h; injection h with heq; injection heq with _ hden; subst hden
    exact decodeBits_finite_den_pos f bits neg n d hd

private theorem int_mul_lt_cancel_right {x y z : Int} (hz : 0 < z) (h : x * z < y * z) : x < y := by
  have hsub : 0 < (y - x) * z := by
    rw [Int.sub_mul]
    omega
  by_cases hxy : x < y
  · exact hxy
  · have hle : y - x ≤ 0 := by omega
    have : (y - x) * z ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hle (by omega)
    omega

private theorem int_mul_le_cancel_right {x y z : Int} (hz : 0 < z) (h : x * z ≤ y * z) : x ≤ y := by
  by_cases hle : x ≤ y
  · exact hle
  · have hlt : y < x := by omega
    have : y * z < x * z := Int.mul_lt_mul_of_pos_right hlt hz
    omega

theorem evalFloatCmpProto_lt_trans (f : IeeeFormat) (a b c : Nat)
    (hab : evalFloatCmpProto .lt f a b = true)
    (hbc : evalFloatCmpProto .lt f b c = true) :
    evalFloatCmpProto .lt f a c = true := by
  unfold evalFloatCmpProto at hab hbc ⊢
  rw [evalFloatPartialCompareProto_eq_extRatCmp] at hab hbc ⊢
  cases hea : floatKindToExtRat (decodeBits f a) with
  | none => rw [hea] at hab; cases hab
  | some ea =>
    cases heb : floatKindToExtRat (decodeBits f b) with
    | none => rw [hea, heb] at hab; cases hab
    | some eb =>
      cases hec : floatKindToExtRat (decodeBits f c) with
      | none => rw [heb, hec] at hbc; cases hbc
      | some ec =>
        rw [hea, heb] at hab
        rw [heb, hec] at hbc
        cases ea with
        | negInf =>
          cases eb with
          | negInf => cases hab
          | fin _ _ => cases ec <;> first | rfl | cases hbc
          | posInf => cases ec <;> cases hbc
        | posInf => cases eb <;> cases hab
        | fin na da =>
          cases eb with
          | negInf => cases hab
          | posInf => cases ec <;> cases hbc
          | fin nb db =>
            cases ec with
            | negInf => cases hbc
            | posInf => rfl
            | fin nc dc =>
              dsimp only [extRatCmp] at hab hbc ⊢
              have hlt1 : na * Int.ofNat db < nb * Int.ofNat da := by
                apply (int_compare_eq_lt_iff _ _).mp
                cases hc : compare (na * Int.ofNat db) (nb * Int.ofNat da) <;>
                  rw [hc] at hab <;> first | rfl | cases hab
              have hlt2 : nb * Int.ofNat dc < nc * Int.ofNat db := by
                apply (int_compare_eq_lt_iff _ _).mp
                cases hc : compare (nb * Int.ofNat dc) (nc * Int.ofNat db) <;>
                  rw [hc] at hbc <;> first | rfl | cases hbc
              have hda : (0 : Int) < Int.ofNat da :=
                Int.ofNat_lt.mpr (floatKindToExtRat_den_pos f a na da hea)
              have hdb : (0 : Int) < Int.ofNat db :=
                Int.ofNat_lt.mpr (floatKindToExtRat_den_pos f b nb db heb)
              have hdc : (0 : Int) < Int.ofNat dc :=
                Int.ofNat_lt.mpr (floatKindToExtRat_den_pos f c nc dc hec)
              have hm1 : (na * Int.ofNat db) * Int.ofNat dc < (nb * Int.ofNat da) * Int.ofNat dc :=
                Int.mul_lt_mul_of_pos_right hlt1 hdc
              have hm2 : (nb * Int.ofNat dc) * Int.ofNat da < (nc * Int.ofNat db) * Int.ofNat da :=
                Int.mul_lt_mul_of_pos_right hlt2 hda
              have hmid : (nb * Int.ofNat da) * Int.ofNat dc = (nb * Int.ofNat dc) * Int.ofNat da := by
                rw [Int.mul_assoc, Int.mul_comm (Int.ofNat da), ← Int.mul_assoc]
              have hcomb : (na * Int.ofNat dc) * Int.ofNat db < (nc * Int.ofNat da) * Int.ofNat db := by
                have hl : (na * Int.ofNat dc) * Int.ofNat db = (na * Int.ofNat db) * Int.ofNat dc := by
                  rw [Int.mul_assoc, Int.mul_comm (Int.ofNat dc), ← Int.mul_assoc]
                have hr : (nc * Int.ofNat da) * Int.ofNat db = (nc * Int.ofNat db) * Int.ofNat da := by
                  rw [Int.mul_assoc, Int.mul_comm (Int.ofNat da), ← Int.mul_assoc]
                rw [hl, hr]; omega
              have hlt3 : na * Int.ofNat dc < nc * Int.ofNat da :=
                int_mul_lt_cancel_right hdb hcomb
              rw [(int_compare_eq_lt_iff _ _).mpr hlt3]
              rfl

theorem evalFloatCmpProto_le_trans (f : IeeeFormat) (a b c : Nat)
    (hab : evalFloatCmpProto .le f a b = true)
    (hbc : evalFloatCmpProto .le f b c = true) :
    evalFloatCmpProto .le f a c = true := by
  unfold evalFloatCmpProto at hab hbc ⊢
  rw [evalFloatPartialCompareProto_eq_extRatCmp] at hab hbc ⊢
  cases hea : floatKindToExtRat (decodeBits f a) with
  | none => rw [hea] at hab; cases hab
  | some ea =>
    cases heb : floatKindToExtRat (decodeBits f b) with
    | none => rw [hea, heb] at hab; cases hab
    | some eb =>
      cases hec : floatKindToExtRat (decodeBits f c) with
      | none => rw [heb, hec] at hbc; cases hbc
      | some ec =>
        rw [hea, heb] at hab
        rw [heb, hec] at hbc
        cases ea with
        | negInf => cases ec <;> rfl
        | posInf =>
          cases eb with
          | posInf => cases ec <;> first | rfl | cases hbc
          | negInf => cases hab
          | fin _ _ => cases hab
        | fin na da =>
          cases eb with
          | negInf => cases hab
          | posInf => cases ec <;> first | rfl | cases hbc
          | fin nb db =>
            cases ec with
            | negInf => cases hbc
            | posInf => rfl
            | fin nc dc =>
              dsimp only [extRatCmp] at hab hbc ⊢
              have hle1 : na * Int.ofNat db ≤ nb * Int.ofNat da := by
                cases hc : compare (na * Int.ofNat db) (nb * Int.ofNat da) with
                | lt => exact Int.le_of_lt ((int_compare_eq_lt_iff _ _).mp hc)
                | eq => exact Int.le_of_eq ((int_compare_eq_eq_iff _ _).mp hc)
                | gt => rw [hc] at hab; cases hab
              have hle2 : nb * Int.ofNat dc ≤ nc * Int.ofNat db := by
                cases hc : compare (nb * Int.ofNat dc) (nc * Int.ofNat db) with
                | lt => exact Int.le_of_lt ((int_compare_eq_lt_iff _ _).mp hc)
                | eq => exact Int.le_of_eq ((int_compare_eq_eq_iff _ _).mp hc)
                | gt => rw [hc] at hbc; cases hbc
              have hda : (0 : Int) < Int.ofNat da :=
                Int.ofNat_lt.mpr (floatKindToExtRat_den_pos f a na da hea)
              have hdb : (0 : Int) < Int.ofNat db :=
                Int.ofNat_lt.mpr (floatKindToExtRat_den_pos f b nb db heb)
              have hdc : (0 : Int) < Int.ofNat dc :=
                Int.ofNat_lt.mpr (floatKindToExtRat_den_pos f c nc dc hec)
              have hm1 : (na * Int.ofNat db) * Int.ofNat dc ≤ (nb * Int.ofNat da) * Int.ofNat dc :=
                Int.mul_le_mul_of_nonneg_right hle1 (Int.le_of_lt hdc)
              have hm2 : (nb * Int.ofNat dc) * Int.ofNat da ≤ (nc * Int.ofNat db) * Int.ofNat da :=
                Int.mul_le_mul_of_nonneg_right hle2 (Int.le_of_lt hda)
              have hmid : (nb * Int.ofNat da) * Int.ofNat dc = (nb * Int.ofNat dc) * Int.ofNat da := by
                rw [Int.mul_assoc, Int.mul_comm (Int.ofNat da), ← Int.mul_assoc]
              have hcomb : (na * Int.ofNat dc) * Int.ofNat db ≤ (nc * Int.ofNat da) * Int.ofNat db := by
                have hl : (na * Int.ofNat dc) * Int.ofNat db = (na * Int.ofNat db) * Int.ofNat dc := by
                  rw [Int.mul_assoc, Int.mul_comm (Int.ofNat dc), ← Int.mul_assoc]
                have hr : (nc * Int.ofNat da) * Int.ofNat db = (nc * Int.ofNat db) * Int.ofNat da := by
                  rw [Int.mul_assoc, Int.mul_comm (Int.ofNat da), ← Int.mul_assoc]
                rw [hl, hr]; omega
              have hle3 : na * Int.ofNat dc ≤ nc * Int.ofNat da :=
                int_mul_le_cancel_right hdb hcomb
              cases hc : compare (na * Int.ofNat dc) (nc * Int.ofNat da) with
              | lt => rfl
              | eq => rfl
              | gt =>
                have hgt := (int_compare_eq_gt_iff _ _).mp hc
                omega

theorem evalFloatCmpProto_le_total_of_not_nan (f : IeeeFormat) (a b : Nat)
    (ha : isNaNBits f a = false) (hb : isNaNBits f b = false) :
    evalFloatCmpProto .le f a b = true ∨ evalFloatCmpProto .le f b a = true := by
  unfold evalFloatCmpProto
  rw [evalFloatPartialCompareProto_swap f b a]
  have hsome : ∃ o, evalFloatPartialCompareProto f a b = .some o := by
    rw [evalFloatPartialCompareProto_eq_extRatCmp]
    unfold isNaNBits at ha hb
    cases hda : decodeBits f a with
    | nan _ _ _ => rw [hda] at ha; cases ha
    | inf ln =>
      cases hdb : decodeBits f b with
      | nan _ _ _ => rw [hdb] at hb; cases hb
      | inf rn => cases ln <;> cases rn <;> exact ⟨_, rfl⟩
      | zero _ => cases ln <;> exact ⟨_, rfl⟩
      | finite _ _ _ => cases ln <;> exact ⟨_, rfl⟩
    | zero _ =>
      cases hdb : decodeBits f b with
      | nan _ _ _ => rw [hdb] at hb; cases hb
      | inf rn => cases rn <;> exact ⟨_, rfl⟩
      | zero _ => exact ⟨_, rfl⟩
      | finite _ _ _ => exact ⟨_, rfl⟩
    | finite _ _ _ =>
      cases hdb : decodeBits f b with
      | nan _ _ _ => rw [hdb] at hb; cases hb
      | inf rn => cases rn <;> exact ⟨_, rfl⟩
      | zero _ => exact ⟨_, rfl⟩
      | finite _ _ _ => exact ⟨_, rfl⟩
  obtain ⟨o, ho⟩ := hsome
  rw [ho]
  cases o with
  | lt => exact Or.inl rfl
  | eq => exact Or.inl rfl
  | gt => exact Or.inr rfl

theorem evalFloatCmpProto_lt_neg_reverse (f : IeeeFormat) (a b : Nat) :
    evalFloatCmpProto .lt f (evalFloatNegProto f a) (evalFloatNegProto f b) =
      evalFloatCmpProto .lt f b a := by
  unfold evalFloatCmpProto
  rw [evalFloatPartialCompareProto_neg]

theorem evalFloatCmpProto_le_neg_reverse (f : IeeeFormat) (a b : Nat) :
    evalFloatCmpProto .le f (evalFloatNegProto f a) (evalFloatNegProto f b) =
      evalFloatCmpProto .le f b a := by
  unfold evalFloatCmpProto
  rw [evalFloatPartialCompareProto_neg]

theorem evalFloatCmpProto_eq_neg_preserve (f : IeeeFormat) (a b : Nat) :
    evalFloatCmpProto .eq f (evalFloatNegProto f a) (evalFloatNegProto f b) =
      evalFloatCmpProto .eq f a b := by
  unfold evalFloatCmpProto
  rw [evalFloatPartialCompareProto_neg, evalFloatPartialCompareProto_swap f b a]
  cases evalFloatPartialCompareProto f a b with
  | none => rfl
  | some o => cases o <;> rfl

/-! ## §3. Single-Rounding Ties-to-Even Arithmetic (`evalFloatArithBaseProto`) -/

/-- `true` iff `op` is one of the five MIR floating-point arithmetic `BinOp`s
(`add`, `sub`, `mul`, `div`, `rem`). -/
def isFloatArithBinOp : BinOp → Bool
  | .add | .sub | .mul | .div | .rem => true
  | _ => false

/-- Exact rational sum of two decoded `FloatKind`s rounded once with
`roundRatioTiesToEven`, matching `Miri.Interpreter.FloatBits.exactSum`. -/
def exactSumProto (f : IeeeFormat) (l r : FloatKind) : Nat :=
  match l, r with
  | .nan _ _ _, _ | _, .nan _ _ _ => preferredNaNBits f
  | .inf ln, .inf rn => if ln != rn then preferredNaNBits f else infBits f ln
  | .inf ln, _ => infBits f ln
  | _, .inf rn => infBits f rn
  | .zero ln, .zero rn => zeroBits f (ln && rn)
  | .zero _, .finite rn rnum rden => roundRatioTiesToEven f rn rnum rden
  | .finite ln lnum lden, .zero _ => roundRatioTiesToEven f ln lnum lden
  | .finite ln lnum lden, .finite rn rnum rden =>
    let n : Int := signedNum ln lnum * Int.ofNat rden + signedNum rn rnum * Int.ofNat lden
    roundRatioTiesToEven f (decide (n < 0)) n.natAbs (lden * rden)

/-- Deterministic single-rounding ties-to-even base result for IEEE-754
`add`, `sub`, `mul`, `div`, and `rem` (matching `Miri.Interpreter.FloatBits.arithmetic`).
Unsupported `BinOp`s return `preferredNaNBits f` (see `evalFloatArithBaseProto?`
for the `Option Nat` discriminator). -/
def evalFloatArithBaseProto (op : BinOp) (f : IeeeFormat) (lhs rhs : Nat) : Nat :=
  match op with
  | .add => exactSumProto f (decodeBits f lhs) (decodeBits f rhs)
  | .sub => exactSumProto f (decodeBits f lhs) (negateFloatKind (decodeBits f rhs))
  | .mul =>
    match decodeBits f lhs, decodeBits f rhs with
    | .nan _ _ _, _ | _, .nan _ _ _ => preferredNaNBits f
    | .inf _, .zero _ | .zero _, .inf _ => preferredNaNBits f
    | .inf ln, .inf rn => infBits f (xor ln rn)
    | .inf ln, .finite rn _ _ => infBits f (xor ln rn)
    | .finite ln _ _, .inf rn => infBits f (xor ln rn)
    | .zero ln, .zero rn => zeroBits f (xor ln rn)
    | .zero ln, .finite rn _ _ => zeroBits f (xor ln rn)
    | .finite ln _ _, .zero rn => zeroBits f (xor ln rn)
    | .finite ln lnum lden, .finite rn rnum rden =>
      roundRatioTiesToEven f (xor ln rn) (lnum * rnum) (lden * rden)
  | .div =>
    match decodeBits f lhs, decodeBits f rhs with
    | .nan _ _ _, _ | _, .nan _ _ _ => preferredNaNBits f
    | .inf _, .inf _ | .zero _, .zero _ => preferredNaNBits f
    | .inf ln, .zero rn => infBits f (xor ln rn)
    | .inf ln, .finite rn _ _ => infBits f (xor ln rn)
    | .finite ln _ _, .zero rn => infBits f (xor ln rn)
    | .zero ln, .inf rn => zeroBits f (xor ln rn)
    | .zero ln, .finite rn _ _ => zeroBits f (xor ln rn)
    | .finite ln _ _, .inf rn => zeroBits f (xor ln rn)
    | .finite ln lnum lden, .finite rn rnum rden =>
      roundRatioTiesToEven f (xor ln rn) (lnum * rden) (lden * rnum)
  | .rem =>
    match decodeBits f lhs, decodeBits f rhs with
    | .nan _ _ _, _ | _, .nan _ _ _ => preferredNaNBits f
    | .inf _, _ | _, .zero _ => preferredNaNBits f
    | .zero _, .inf _ | .finite _ _ _, .inf _ => lhs % 2 ^ f.width
    | .zero ln, .finite _ _ _ => zeroBits f ln
    | .finite ln lnum lden, .finite _ rnum rden =>
      let num := lnum * rden
      let den := lden * rnum
      let q := num / den
      let r := num - q * den
      roundRatioTiesToEven f ln r (lden * rden)
  | _ => preferredNaNBits f

/-- Partial `Option Nat` variant returning `.none` on non-arithmetic `BinOp`s. -/
def evalFloatArithBaseProto? (op : BinOp) (f : IeeeFormat) (lhs rhs : Nat) : Option Nat :=
  if isFloatArithBinOp op then .some (evalFloatArithBaseProto op f lhs rhs) else .none

private theorem exactSumProto_lt (f : IeeeFormat) (l r : FloatKind)
    (hl : ∀ neg n d, l = .finite neg n d → 0 < d)
    (hr : ∀ neg n d, r = .finite neg n d → 0 < d) :
    exactSumProto f l r < 2 ^ f.width := by
  unfold exactSumProto
  cases l with
  | nan _ _ _ => exact preferredNaNBits_lt f
  | inf ln =>
    cases r with
    | nan _ _ _ => exact preferredNaNBits_lt f
    | inf rn =>
      cases ln <;> cases rn <;> first | exact preferredNaNBits_lt f | exact infBits_lt f _
    | zero _ => exact infBits_lt f ln
    | finite _ _ _ => exact infBits_lt f ln
  | zero ln =>
    cases r with
    | nan _ _ _ => exact preferredNaNBits_lt f
    | inf rn => exact infBits_lt f rn
    | zero rn => exact zeroBits_lt f (ln && rn)
    | finite rn rnum rden => exact roundRatioTiesToEven_lt f rn rnum rden (hr rn rnum rden rfl)
  | finite ln lnum lden =>
    cases r with
    | nan _ _ _ => exact preferredNaNBits_lt f
    | inf rn => exact infBits_lt f rn
    | zero _ => exact roundRatioTiesToEven_lt f ln lnum lden (hl ln lnum lden rfl)
    | finite rn rnum rden =>
      exact roundRatioTiesToEven_lt f _ _ (lden * rden)
        (Nat.mul_pos (hl ln lnum lden rfl) (hr rn rnum rden rfl))

theorem evalFloatArithBaseProto_lt (op : BinOp) (f : IeeeFormat) (lhs rhs : Nat) :
    evalFloatArithBaseProto op f lhs rhs < 2 ^ f.width := by
  unfold evalFloatArithBaseProto
  cases op with
  | add =>
    exact exactSumProto_lt f _ _
      (fun neg n d h => decodeBits_finite_den_pos f lhs neg n d h)
      (fun neg n d h => decodeBits_finite_den_pos f rhs neg n d h)
  | sub =>
    apply exactSumProto_lt f _ _
      (fun neg n d h => decodeBits_finite_den_pos f lhs neg n d h)
    intro neg n d h
    cases hr : decodeBits f rhs with
    | finite rn rn' rd' =>
      rw [hr] at h; injection h with _ _ hd; subst hd
      exact decodeBits_finite_den_pos f rhs rn rn' rd' hr
    | _ => rw [hr] at h; cases h
  | mul =>
    cases hl : decodeBits f lhs with
    | nan _ _ _ => exact preferredNaNBits_lt f
    | inf ln =>
      cases hr : decodeBits f rhs with
      | nan _ _ _ => exact preferredNaNBits_lt f
      | zero _ => exact preferredNaNBits_lt f
      | inf rn => exact infBits_lt f _
      | finite rn _ _ => exact infBits_lt f _
    | zero ln =>
      cases hr : decodeBits f rhs with
      | nan _ _ _ => exact preferredNaNBits_lt f
      | inf _ => exact preferredNaNBits_lt f
      | zero rn => exact zeroBits_lt f _
      | finite rn _ _ => exact zeroBits_lt f _
    | finite ln lnum lden =>
      cases hr : decodeBits f rhs with
      | nan _ _ _ => exact preferredNaNBits_lt f
      | inf rn => exact infBits_lt f _
      | zero rn => exact zeroBits_lt f _
      | finite rn rnum rden =>
        exact roundRatioTiesToEven_lt f _ _ _
          (Nat.mul_pos (decodeBits_finite_den_pos f lhs ln lnum lden hl)
            (decodeBits_finite_den_pos f rhs rn rnum rden hr))
  | div =>
    cases hl : decodeBits f lhs with
    | nan _ _ _ => exact preferredNaNBits_lt f
    | inf ln =>
      cases hr : decodeBits f rhs with
      | nan _ _ _ => exact preferredNaNBits_lt f
      | inf _ => exact preferredNaNBits_lt f
      | zero rn => exact infBits_lt f _
      | finite rn _ _ => exact infBits_lt f _
    | zero ln =>
      cases hr : decodeBits f rhs with
      | nan _ _ _ => exact preferredNaNBits_lt f
      | zero _ => exact preferredNaNBits_lt f
      | inf rn => exact zeroBits_lt f _
      | finite rn _ _ => exact zeroBits_lt f _
    | finite ln lnum lden =>
      cases hr : decodeBits f rhs with
      | nan _ _ _ => exact preferredNaNBits_lt f
      | zero rn => exact infBits_lt f _
      | inf rn => exact zeroBits_lt f _
      | finite rn rnum rden =>
        exact roundRatioTiesToEven_lt f _ _ _
          (Nat.mul_pos (decodeBits_finite_den_pos f lhs ln lnum lden hl)
            (decodeBits_finite_num_pos f rhs rn rnum rden hr))
  | rem =>
    cases hl : decodeBits f lhs with
    | nan _ _ _ => exact preferredNaNBits_lt f
    | inf _ => cases decodeBits f rhs <;> exact preferredNaNBits_lt f
    | zero ln =>
      cases hr : decodeBits f rhs with
      | nan _ _ _ => exact preferredNaNBits_lt f
      | zero _ => exact preferredNaNBits_lt f
      | inf _ => exact Nat.mod_lt _ (Nat.two_pow_pos _)
      | finite _ _ _ => exact zeroBits_lt f _
    | finite ln lnum lden =>
      cases hr : decodeBits f rhs with
      | nan _ _ _ => exact preferredNaNBits_lt f
      | zero _ => exact preferredNaNBits_lt f
      | inf _ => exact Nat.mod_lt _ (Nat.two_pow_pos _)
      | finite rn rnum rden =>
        exact roundRatioTiesToEven_lt f _ _ _
          (Nat.mul_pos (decodeBits_finite_den_pos f lhs ln lnum lden hl)
            (decodeBits_finite_den_pos f rhs rn rnum rden hr))
  | _ => exact preferredNaNBits_lt f

theorem evalFloatArithBaseProto_sub_eq_add_neg (f : IeeeFormat) (lhs rhs : Nat) :
    evalFloatArithBaseProto .sub f lhs rhs =
      evalFloatArithBaseProto .add f lhs (evalFloatNegProto f rhs) := by
  unfold evalFloatArithBaseProto
  rw [decodeBits_evalFloatNegProto]

theorem exactSumProto_comm (f : IeeeFormat) (l r : FloatKind) :
    exactSumProto f l r = exactSumProto f r l := by
  unfold exactSumProto
  cases l with
  | nan _ _ _ => cases r <;> rfl
  | inf ln =>
    cases r with
    | nan _ _ _ => rfl
    | inf rn => cases ln <;> cases rn <;> rfl
    | zero _ => rfl
    | finite _ _ _ => rfl
  | zero ln =>
    cases r with
    | nan _ _ _ => rfl
    | inf _ => rfl
    | zero rn => cases ln <;> cases rn <;> rfl
    | finite _ _ _ => rfl
  | finite ln lnum lden =>
    cases r with
    | nan _ _ _ => rfl
    | inf _ => rfl
    | zero _ => rfl
    | finite rn rnum rden =>
      dsimp only
      rw [Int.add_comm (signedNum ln lnum * Int.ofNat rden), Nat.mul_comm lden rden]

theorem evalFloatArithBaseProto_add_comm (f : IeeeFormat) (a b : Nat) :
    evalFloatArithBaseProto .add f a b = evalFloatArithBaseProto .add f b a :=
  exactSumProto_comm f (decodeBits f a) (decodeBits f b)

theorem evalFloatArithBaseProto_mul_comm (f : IeeeFormat) (a b : Nat) :
    evalFloatArithBaseProto .mul f a b = evalFloatArithBaseProto .mul f b a := by
  unfold evalFloatArithBaseProto
  cases decodeBits f a with
  | nan _ _ _ => cases decodeBits f b <;> rfl
  | inf ln =>
    cases decodeBits f b with
    | nan _ _ _ => rfl
    | zero _ => rfl
    | inf rn => cases ln <;> cases rn <;> rfl
    | finite rn _ _ => cases ln <;> cases rn <;> rfl
  | zero ln =>
    cases decodeBits f b with
    | nan _ _ _ => rfl
    | inf _ => rfl
    | zero rn => cases ln <;> cases rn <;> rfl
    | finite rn _ _ => cases ln <;> cases rn <;> rfl
  | finite ln lnum lden =>
    cases decodeBits f b with
    | nan _ _ _ => rfl
    | inf rn => cases ln <;> cases rn <;> rfl
    | zero rn => cases ln <;> cases rn <;> rfl
    | finite rn rnum rden =>
      dsimp only
      have hxor : xor ln rn = xor rn ln := by cases ln <;> cases rn <;> rfl
      rw [hxor, Nat.mul_comm lnum rnum, Nat.mul_comm lden rden]

theorem evalFloatArithBaseProto_add_negZero_negZero (f : IeeeFormat) :
    evalFloatArithBaseProto .add f (zeroBits f true) (zeroBits f true) = zeroBits f true := by
  unfold evalFloatArithBaseProto exactSumProto
  rw [decodeBits_zeroBits]
  rfl

theorem evalFloatArithBaseProto_add_posZero_negZero (f : IeeeFormat) :
    evalFloatArithBaseProto .add f (zeroBits f false) (zeroBits f true) = zeroBits f false := by
  unfold evalFloatArithBaseProto exactSumProto
  rw [decodeBits_zeroBits, decodeBits_zeroBits]
  rfl

theorem evalFloatArithBaseProto_sub_negZero_posZero (f : IeeeFormat) :
    evalFloatArithBaseProto .sub f (zeroBits f true) (zeroBits f false) = zeroBits f true := by
  rw [evalFloatArithBaseProto_sub_eq_add_neg, evalFloatNegProto_zeroBits]
  exact evalFloatArithBaseProto_add_negZero_negZero f

/-- IEEE-754 `roundTiesToEven` additive identity: adding `-0.0` preserves every
non-NaN bit pattern canonically (including `+0.0`, `-0.0`, subnormals, normals,
and `±Inf`). -/
theorem evalFloatArithBaseProto_add_negZero_right (f : IeeeFormat) (x : Nat)
    (hx : isNaNBits f x = false) :
    evalFloatArithBaseProto .add f x (zeroBits f true) = x % 2 ^ f.width := by
  have hmod : x % 2 ^ f.width < 2 ^ f.width := Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold evalFloatArithBaseProto exactSumProto
  rw [decodeBits_zeroBits, ← decodeBits_mod_width f x]
  unfold isNaNBits at hx
  rw [← decodeBits_mod_width f x] at hx
  cases hd : decodeBits f (x % 2 ^ f.width) with
  | nan _ _ _ => rw [hd] at hx; cases hx
  | inf ln => exact (bits_eq_infBits_of_decodeBits_inf f _ ln hmod hd).symm
  | zero ln =>
    dsimp only
    rw [Bool.and_true]
    exact (bits_eq_zeroBits_of_decodeBits_zero f _ ln hmod hd).symm
  | finite ln lnum lden =>
    exact roundRatioTiesToEven_eq_bits_of_decodeBits_finite f _ ln lnum lden hmod hd

/-- Adding `+0.0` preserves every non-NaN bit pattern other than `-0.0`. -/
theorem evalFloatArithBaseProto_add_posZero_right (f : IeeeFormat) (x : Nat)
    (hx : isNaNBits f x = false) (hne : decodeBits f x ≠ .zero true) :
    evalFloatArithBaseProto .add f x (zeroBits f false) = x % 2 ^ f.width := by
  have hmod : x % 2 ^ f.width < 2 ^ f.width := Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold evalFloatArithBaseProto exactSumProto
  rw [decodeBits_zeroBits, ← decodeBits_mod_width f x]
  unfold isNaNBits at hx
  rw [← decodeBits_mod_width f x] at hx hne
  cases hd : decodeBits f (x % 2 ^ f.width) with
  | nan _ _ _ => rw [hd] at hx; cases hx
  | inf ln => exact (bits_eq_infBits_of_decodeBits_inf f _ ln hmod hd).symm
  | zero ln =>
    cases ln
    · exact (bits_eq_zeroBits_of_decodeBits_zero f _ false hmod hd).symm
    · exact absurd hd hne
  | finite ln lnum lden =>
    exact roundRatioTiesToEven_eq_bits_of_decodeBits_finite f _ ln lnum lden hmod hd

/-- Exact cancellation of a finite nonzero float with its negation yields `+0.0`
under `roundTiesToEven`. -/
theorem evalFloatArithBaseProto_add_neg_self_finite (f : IeeeFormat) (x : Nat)
    (neg : Bool) (n d : Nat) (h : decodeBits f x = .finite neg n d) :
    evalFloatArithBaseProto .add f x (evalFloatNegProto f x) = zeroBits f false := by
  have hd_pos := decodeBits_finite_den_pos f x neg n d h
  unfold evalFloatArithBaseProto exactSumProto
  rw [decodeBits_evalFloatNegProto, h]
  dsimp only [negateFloatKind]
  rw [signedNum_neg, Int.neg_mul, Int.add_right_neg]
  unfold roundRatioTiesToEven
  have hdd : d * d ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hd_pos hd_pos)
  rw [if_neg' hdd]
  rfl

/-- Multiplying signed zero by any finite (zero or nonzero) value yields signed
zero with XOR sign. -/
theorem evalFloatArithBaseProto_mul_zero_finite (f : IeeeFormat) (zneg : Bool) (x : Nat)
    (hfin : (∃ xn, decodeBits f x = .zero xn) ∨ (∃ xn n d, decodeBits f x = .finite xn n d)) :
    evalFloatArithBaseProto .mul f (zeroBits f zneg) x =
      zeroBits f (xor zneg (unpackBits f x).neg) := by
  unfold evalFloatArithBaseProto
  rw [decodeBits_zeroBits]
  rcases hfin with ⟨xn, hx⟩ | ⟨xn, n, d, hx⟩
  · rw [hx]
    have hneg : (unpackBits f x).neg = xn := by
      unfold decodeBits at hx
      dsimp only at hx
      split at hx
      · split at hx <;> cases hx
      · split at hx
        · split at hx
          · injection hx
          · cases hx
        · cases hx
    rw [hneg]
  · rw [hx]
    have hneg : (unpackBits f x).neg = xn := by
      unfold decodeBits at hx
      dsimp only at hx
      split at hx
      · split at hx <;> cases hx
      · split at hx
        · split at hx
          · cases hx
          · injection hx
        · injection hx
    rw [hneg]

theorem evalFloatArithBaseProto_rem_inf_right (f : IeeeFormat) (x : Nat) (ineg : Bool)
    (hfin : (∃ xn, decodeBits f x = .zero xn) ∨ (∃ xn n d, decodeBits f x = .finite xn n d)) :
    evalFloatArithBaseProto .rem f x (infBits f ineg) = x % 2 ^ f.width := by
  unfold evalFloatArithBaseProto
  rw [decodeBits_infBits]
  rcases hfin with ⟨xn, hx⟩ | ⟨xn, n, d, hx⟩ <;> rw [hx]

theorem evalFloatArithBaseProto_rem_zero_finite (f : IeeeFormat) (zneg : Bool) (y : Nat)
    (yn rn rd : Nat) (yneg : Bool) (hy : decodeBits f y = .finite yneg rn rd) :
    evalFloatArithBaseProto .rem f (zeroBits f zneg) y = zeroBits f zneg := by
  let _ := yn
  unfold evalFloatArithBaseProto
  rw [decodeBits_zeroBits, hy]

/-! ## §4. Mode-Parametric `miri#5643` NaN Choices & Relational Semantics -/

/-- Mode selecting deterministic preferred-NaN vs. `miri#5643` nondeterministic
NaN payload/sign choice semantics. -/
inductive FloatArithMode : Type where
  | deterministic : FloatArithMode
  | nondeterministic : FloatArithMode
deriving DecidableEq, Repr

/-- Collect quieted target-format NaN candidates from all NaN inputs (preserving
input list order, matching pinned `Miri.Interpreter.FloatBits.nanChoices`). -/
def quietedNaNCandidates (f : IeeeFormat) : List (IeeeFormat × Nat) → List Nat
  | .nil => .nil
  | entry :: rest =>
    let srcFmt := entry.1
    let inBits := entry.2
    let tail := quietedNaNCandidates f rest
    if isNaNBits srcFmt inBits then
      evalFloatToFloatRoundTiesToEven srcFmt f inBits :: tail
    else tail

/-- Collect signaling target-format NaN candidates from signaling NaN inputs
whose target-format payload retains nonzero low bits (matching pinned
`Miri.Interpreter.FloatBits.nanChoices`). -/
def signalingNaNCandidates (f : IeeeFormat) : List (IeeeFormat × Nat) → List Nat
  | .nil => .nil
  | entry :: rest =>
    let srcFmt := entry.1
    let inBits := entry.2
    let tail := signalingNaNCandidates f rest
    if isSignalingNaNBits srcFmt inBits then
      let q := evalFloatToFloatRoundTiesToEven srcFmt f inBits
      let cq := unpackBits f q
      let lower := cq.fraction % 2 ^ (f.fractionBits - 1)
      if lower != 0 then
        encodeBits f cq.neg (2 ^ f.exponentBits - 1) lower :: tail
      else tail
    else tail

/-- Duplicate each candidate `c` with both its original sign and its negated sign
`[c, evalFloatNegProto f c]`. -/
def expandNaNSigns (f : IeeeFormat) : List Nat → List Nat
  | .nil => .nil
  | c :: rest => c :: evalFloatNegProto f c :: expandNaNSigns f rest

/-- Mode-parametric NaN candidate generator transliterating pinned Miri
`FloatBits.nanChoices` (`lean-miri/vendor/Miri/Interpreter/Float.lean:132-151`). -/
def nanChoicesProto (f : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (mode : FloatArithMode) : List Nat :=
  match mode with
  | .deterministic => [preferredNaNBits f]
  | .nondeterministic =>
    let candidates :=
      preferredNaNBits f :: (quietedNaNCandidates f inputs ++ signalingNaNCandidates f inputs)
    expandNaNSigns f candidates

theorem isSignalingNaNBits_iff_payload_lt (f : IeeeFormat) (bits : Nat) :
    isSignalingNaNBits f bits = true ↔
      ∃ neg payload, decodeBits f bits = .nan neg false payload ∧
        payload ≠ 0 ∧ payload < 2 ^ (f.fractionBits - 1) := by
  constructor
  · intro hs
    unfold isSignalingNaNBits at hs
    cases hd : decodeBits f bits with
    | nan neg q payload =>
      cases q with
      | true => rw [hd] at hs; cases hs
      | false =>
        obtain ⟨_, hne, hlt, hq⟩ := decodeBits_nan_payload f bits neg false payload hd
        have hsp : 2 ^ f.fractionBits = 2 * 2 ^ (f.fractionBits - 1) :=
          (ieeeFormat_width_split f).2.2.1
        have hpos : 0 < 2 ^ (f.fractionBits - 1) := Nat.two_pow_pos _
        have hdiv2 : payload / 2 ^ (f.fractionBits - 1) < 2 :=
          nat_div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hsp]; exact hlt)
        have hdiv0 : payload / 2 ^ (f.fractionBits - 1) = 0 := by
          rcases h01 : payload / 2 ^ (f.fractionBits - 1) with _ | _ | k
          · rfl
          · rw [h01] at hq; cases hq
          · omega
        have hlt_half : payload < 2 ^ (f.fractionBits - 1) := by
          by_cases hge : 2 ^ (f.fractionBits - 1) ≤ payload
          · have : 1 ≤ payload / 2 ^ (f.fractionBits - 1) :=
              (Nat.le_div_iff_mul_le hpos).mpr (by rw [Nat.one_mul]; exact hge)
            omega
          · omega
        exact ⟨neg, payload, rfl, hne, hlt_half⟩
    | _ => rw [hd] at hs; cases hs
  · rintro ⟨neg, payload, hd, _, _⟩
    unfold isSignalingNaNBits
    rw [hd]

theorem isAdmissibleQuietNaN_preferredNaNBits (f : IeeeFormat) :
    isAdmissibleQuietNaN f (preferredNaNBits f) = true := by
  cases f <;> decide

theorem isAdmissibleQuietNaN_of_mem_quieted (f : IeeeFormat)
    (inputs : List (IeeeFormat × Nat)) (c : Nat)
    (hc : c ∈ quietedNaNCandidates f inputs) :
    isAdmissibleQuietNaN f c = true := by
  induction inputs with
  | nil => cases hc
  | cons entry rest ih =>
    unfold quietedNaNCandidates at hc
    dsimp only at hc
    by_cases hnan : isNaNBits entry.1 entry.2 = true
    · rw [if_pos' hnan] at hc
      cases hc with
      | head =>
        unfold isAdmissibleQuietNaN
        rw [decide_eq_true (evalFloatToFloatRoundTiesToEven_lt entry.1 f entry.2)]
        have hq : isQuietNaNBits f (evalFloatToFloatRoundTiesToEven entry.1 f entry.2) = true := by
          rw [← convertFloatBits_tiesToEven]
          exact (convertFloatBits_nan_quiet .tiesToEven entry.1 f entry.2 hnan).2
        rw [hq]; rfl
      | tail _ hmem => exact ih hmem
    · rw [if_neg' hnan] at hc
      exact ih hc

theorem isAdmissibleQuietNaN_of_mem_quieted_expanded (f : IeeeFormat)
    (inputs : List (IeeeFormat × Nat)) (c : Nat)
    (hc : c ∈ expandNaNSigns f (preferredNaNBits f :: quietedNaNCandidates f inputs)) :
    isAdmissibleQuietNaN f c = true := by
  have hmem_exp : ∀ (l : List Nat) (x : Nat),
      (∀ y ∈ l, isAdmissibleQuietNaN f y = true) →
      x ∈ expandNaNSigns f l → isAdmissibleQuietNaN f x = true := by
    intro l x hall hx
    induction l with
    | nil => cases hx
    | cons a tl ihl =>
      unfold expandNaNSigns at hx
      cases hx with
      | head => exact hall _ (List.Mem.head _)
      | tail _ hx' =>
        cases hx' with
        | head =>
          have ha := hall a (List.Mem.head _)
          unfold isAdmissibleQuietNaN at ha
          have haq : isQuietNaNBits f a = true := by
            cases h1 : decide (a < 2 ^ f.width) <;> cases h2 : isQuietNaNBits f a <;>
              rw [h1, h2] at ha <;> first | rfl | cases ha
          exact isAdmissibleQuietNaN_evalFloatNegProto f a haq
        | tail _ htl => exact ihl (fun y hy => hall y (List.Mem.tail _ hy)) htl
  apply hmem_exp _ c _ hc
  intro y hy
  cases hy with
  | head => exact isAdmissibleQuietNaN_preferredNaNBits f
  | tail _ hq => exact isAdmissibleQuietNaN_of_mem_quieted f inputs y hq

theorem isSignalingNaNBits_of_mem_signaling (f : IeeeFormat)
    (inputs : List (IeeeFormat × Nat)) (c : Nat)
    (hc : c ∈ signalingNaNCandidates f inputs) :
    c < 2 ^ f.width ∧ isSignalingNaNBits f c = true := by
  induction inputs with
  | nil => cases hc
  | cons entry rest ih =>
    unfold signalingNaNCandidates at hc
    dsimp only at hc
    by_cases hs : isSignalingNaNBits entry.1 entry.2 = true
    · rw [if_pos' hs] at hc
      let q := evalFloatToFloatRoundTiesToEven entry.1 f entry.2
      let cq := unpackBits f q
      let lower := cq.fraction % 2 ^ (f.fractionBits - 1)
      by_cases hnz : (lower != 0) = true
      · rw [if_pos' hnz] at hc
        cases hc with
        | head =>
          have hlower_ne : lower ≠ 0 := by
            intro h0; rw [h0] at hnz; cases hnz
          have hlower_lt_half : lower < 2 ^ (f.fractionBits - 1) :=
            Nat.mod_lt _ (Nat.two_pow_pos _)
          have hsp : 2 ^ f.fractionBits = 2 * 2 ^ (f.fractionBits - 1) :=
            (ieeeFormat_width_split f).2.2.1
          have hlower_lt : lower < 2 ^ f.fractionBits := by omega
          have hE : 2 ^ f.exponentBits - 1 < 2 ^ f.exponentBits :=
            Nat.sub_lt (Nat.two_pow_pos _) (by decide)
          refine ⟨encodeBits_lt f cq.neg _ lower hE hlower_lt, ?_⟩
          unfold isSignalingNaNBits
          rw [decodeBits_encodeBits f cq.neg _ lower hE hlower_lt,
              if_pos' rfl, if_neg' hlower_ne]
          have hdiv0 : lower / 2 ^ (f.fractionBits - 1) = 0 := Nat.div_eq_of_lt hlower_lt_half
          rw [hdiv0]
        | tail _ hmem => exact ih hmem
      · rw [if_neg' hnz] at hc
        exact ih hc
    · rw [if_neg' hs] at hc
      exact ih hc

/-- For same-format `srcFmt = f` signaling NaN inputs, the converted NaN's lower
payload bits are strictly nonzero and equal the original fraction payload; hence
the signaling candidate reproduces the canonical input bit pattern exactly. -/
theorem same_format_signaling_candidate_eq (f : IeeeFormat) (inBits : Nat)
    (hs : isSignalingNaNBits f inBits = true) :
    let q := evalFloatToFloatRoundTiesToEven f f inBits
    let cq := unpackBits f q
    let lower := cq.fraction % 2 ^ (f.fractionBits - 1)
    lower ≠ 0 ∧
      encodeBits f cq.neg (2 ^ f.exponentBits - 1) lower = inBits % 2 ^ f.width := by
  obtain ⟨neg, payload, hd, hne, hlt_half⟩ := (isSignalingNaNBits_iff_payload_lt f inBits).mp hs
  have hmod : inBits % 2 ^ f.width < 2 ^ f.width := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hd_mod : decodeBits f (inBits % 2 ^ f.width) = .nan neg false payload := by
    rw [decodeBits_mod_width]; exact hd
  have hq_eq : evalFloatToFloatRoundTiesToEven f f inBits =
      encodeBits f neg (2 ^ f.exponentBits - 1) (payload + 2 ^ (f.fractionBits - 1)) := by
    rw [evalFloatToFloatRoundTiesToEven_of_nan f f inBits neg false payload hd]
    have hsame :
        (if f.fractionBits ≤ f.fractionBits then
          Nat.lor payload (2 ^ (f.fractionBits - 1)) * 2 ^ (f.fractionBits - f.fractionBits)
        else Nat.lor payload (2 ^ (f.fractionBits - 1)) / 2 ^ (f.fractionBits - f.fractionBits)) =
          Nat.lor payload (2 ^ (f.fractionBits - 1)) := by
      rw [if_pos' (Nat.le_refl _), Nat.sub_self, Nat.pow_zero, Nat.mul_one]
    have hlor_idem : Nat.lor (Nat.lor payload (2 ^ (f.fractionBits - 1))) (2 ^ (f.fractionBits - 1)) =
        Nat.lor payload (2 ^ (f.fractionBits - 1)) := by
      change (payload ||| 2 ^ (f.fractionBits - 1)) ||| 2 ^ (f.fractionBits - 1) =
        payload ||| 2 ^ (f.fractionBits - 1)
      rw [Nat.or_assoc, Nat.or_self]
    have hlor_add : Nat.lor payload (2 ^ (f.fractionBits - 1)) = payload + 2 ^ (f.fractionBits - 1) := by
      have h1 := mul_two_pow_add_eq_lor 1 payload (f.fractionBits - 1) hlt_half
      rw [Nat.one_mul] at h1
      change payload ||| 2 ^ (f.fractionBits - 1) = payload + 2 ^ (f.fractionBits - 1)
      rw [Nat.add_comm, h1]
      exact Nat.or_comm payload (2 ^ (f.fractionBits - 1))
    rw [hsame, hlor_idem, hlor_add]
  have hsp := (ieeeFormat_width_split f).2.2.1
  have hE : 2 ^ f.exponentBits - 1 < 2 ^ f.exponentBits :=
    Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  have hF_lt : payload + 2 ^ (f.fractionBits - 1) < 2 ^ f.fractionBits := by omega
  have hunp : unpackBits f (evalFloatToFloatRoundTiesToEven f f inBits) =
      ⟨neg, 2 ^ f.exponentBits - 1, payload + 2 ^ (f.fractionBits - 1)⟩ := by
    rw [hq_eq]
    exact unpackBits_encodeBits f neg _ _ hE hF_lt
  dsimp only
  rw [hunp]
  have hlow : (payload + 2 ^ (f.fractionBits - 1)) % 2 ^ (f.fractionBits - 1) = payload := by
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt_half]
  rw [hlow]
  refine ⟨hne, ?_⟩
  have hrec := encodeBits_unpackBits f (inBits % 2 ^ f.width) hmod
  have hE_eq : (unpackBits f (inBits % 2 ^ f.width)).exponent = 2 ^ f.exponentBits - 1 := by
    unfold decodeBits at hd_mod
    dsimp only at hd_mod
    split at hd_mod
    · assumption
    · split at hd_mod
      · split at hd_mod <;> cases hd_mod
      · cases hd_mod
  have hneg_eq : (unpackBits f (inBits % 2 ^ f.width)).neg = neg := by
    unfold decodeBits at hd_mod
    dsimp only at hd_mod
    rw [if_pos' hE_eq] at hd_mod
    split at hd_mod
    · cases hd_mod
    · injection hd_mod
  have hfrac_eq : (unpackBits f (inBits % 2 ^ f.width)).fraction = payload := by
    obtain ⟨hp, _, _, _⟩ := decodeBits_nan_payload f (inBits % 2 ^ f.width) neg false payload hd_mod
    unfold unpackBits; exact hp.symm
  rw [← hneg_eq, ← hE_eq, ← hfrac_eq, hrec]

theorem expandNaNSigns_mem_iff (f : IeeeFormat) (l : List Nat) (x : Nat) :
    x ∈ expandNaNSigns f l ↔ ∃ c ∈ l, x = c ∨ x = evalFloatNegProto f c := by
  induction l with
  | nil =>
    constructor
    · intro h; cases h
    · rintro ⟨_, h, _⟩; cases h
  | cons a rest ih =>
    unfold expandNaNSigns
    constructor
    · intro h
      cases h with
      | head => exact ⟨_, List.Mem.head _, Or.inl rfl⟩
      | tail _ h' =>
        cases h' with
        | head => exact ⟨a, List.Mem.head _, Or.inr rfl⟩
        | tail _ htl =>
          obtain ⟨c, hc, hcx⟩ := ih.mp htl
          exact ⟨c, List.Mem.tail _ hc, hcx⟩
    · rintro ⟨c, hc, hcx⟩
      cases hc with
      | head =>
        rcases hcx with rfl | rfl
        · exact List.Mem.head _
        · exact List.Mem.tail _ (List.Mem.head _)
      | tail _ hmem =>
        exact List.Mem.tail _ (List.Mem.tail _ (ih.mpr ⟨c, hmem, hcx⟩))

theorem nanChoicesProto_mem_lt_and_nan (f : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (mode : FloatArithMode) (c : Nat) (hc : c ∈ nanChoicesProto f inputs mode) :
    c < 2 ^ f.width ∧ isNaNBits f c = true := by
  cases mode with
  | deterministic =>
    unfold nanChoicesProto at hc
    cases hc with
    | head =>
      refine ⟨preferredNaNBits_lt f, ?_⟩
      cases f <;> decide
    | tail _ h => cases h
  | nondeterministic =>
    unfold nanChoicesProto at hc
    obtain ⟨base, hbase, hcb⟩ := (expandNaNSigns_mem_iff f _ c).mp hc
    have hbase_ok : base < 2 ^ f.width ∧ isNaNBits f base = true := by
      cases hbase with
      | head =>
        refine ⟨preferredNaNBits_lt f, ?_⟩
        cases f <;> decide
      | tail _ hmem =>
        rcases List.mem_append.mp hmem with hq | hs
        · have hadm := isAdmissibleQuietNaN_of_mem_quieted f inputs base hq
          unfold isAdmissibleQuietNaN at hadm
          have hlt : base < 2 ^ f.width := by
            by_cases h1 : base < 2 ^ f.width
            · exact h1
            · rw [decide_eq_false h1] at hadm; cases hadm
          have hqn : isQuietNaNBits f base = true := by
            rw [decide_eq_true hlt] at hadm; exact hadm
          have hnan : isNaNBits f base = true := by
            unfold isQuietNaNBits at hqn; unfold isNaNBits
            cases hd : decodeBits f base with
            | nan _ _ _ => rfl
            | _ => rw [hd] at hqn; cases hqn
          exact ⟨hlt, hnan⟩
        · obtain ⟨hlt, hsig⟩ := isSignalingNaNBits_of_mem_signaling f inputs base hs
          have hnan : isNaNBits f base = true := by
            unfold isSignalingNaNBits at hsig; unfold isNaNBits
            cases hd : decodeBits f base with
            | nan _ _ _ => rfl
            | _ => rw [hd] at hsig; cases hsig
          exact ⟨hlt, hnan⟩
    rcases hcb with rfl | rfl
    · exact hbase_ok
    · exact ⟨evalFloatNegProto_lt f base, by rw [isNaNBits_evalFloatNegProto]; exact hbase_ok.2⟩

theorem preferredNaNBits_mem_nanChoicesProto (f : IeeeFormat)
    (inputs : List (IeeeFormat × Nat)) (mode : FloatArithMode) :
    preferredNaNBits f ∈ nanChoicesProto f inputs mode := by
  cases mode with
  | deterministic => exact List.Mem.head _
  | nondeterministic => exact List.Mem.head _

theorem nanChoicesProto_det_subset_nondet (f : IeeeFormat)
    (inputs : List (IeeeFormat × Nat)) (c : Nat)
    (hc : c ∈ nanChoicesProto f inputs .deterministic) :
    c ∈ nanChoicesProto f inputs .nondeterministic := by
  unfold nanChoicesProto at hc
  cases hc with
  | head => exact preferredNaNBits_mem_nanChoicesProto f inputs .nondeterministic
  | tail _ h => cases h

theorem nanChoicesProto_mem_swap_pair (f : IeeeFormat) (e₁ e₂ : IeeeFormat × Nat)
    (mode : FloatArithMode) (c : Nat) :
    c ∈ nanChoicesProto f [e₁, e₂] mode ↔ c ∈ nanChoicesProto f [e₂, e₁] mode := by
  cases mode with
  | deterministic => rfl
  | nondeterministic =>
    unfold nanChoicesProto
    rw [expandNaNSigns_mem_iff, expandNaNSigns_mem_iff]
    have hq_iff : ∀ b, b ∈ quietedNaNCandidates f [e₁, e₂] ↔ b ∈ quietedNaNCandidates f [e₂, e₁] := by
      intro b
      simp only [quietedNaNCandidates]
      by_cases h1 : isNaNBits e₁.1 e₁.2 = true <;> by_cases h2 : isNaNBits e₂.1 e₂.2 = true
      · rw [if_pos' h1, if_pos' h2, if_pos' h2, if_pos' h1]
        simp [or_comm]
      · rw [if_pos' h1, if_neg' h2, if_neg' h2, if_pos' h1]
      · rw [if_neg' h1, if_pos' h2, if_pos' h2, if_neg' h1]
      · rw [if_neg' h1, if_neg' h2, if_neg' h2, if_neg' h1]
    have hs_iff : ∀ b, b ∈ signalingNaNCandidates f [e₁, e₂] ↔ b ∈ signalingNaNCandidates f [e₂, e₁] := by
      intro b
      simp only [signalingNaNCandidates]
      by_cases h1 : isSignalingNaNBits e₁.1 e₁.2 = true <;>
        by_cases h2 : isSignalingNaNBits e₂.1 e₂.2 = true
      · rw [if_pos' h1, if_pos' h2, if_pos' h2, if_pos' h1]
        split <;> split <;> simp [or_comm]
      · rw [if_pos' h1, if_neg' h2, if_neg' h2, if_pos' h1]
      · rw [if_neg' h1, if_pos' h2, if_pos' h2, if_neg' h1]
      · rw [if_neg' h1, if_neg' h2, if_neg' h2, if_neg' h1]
    constructor <;> rintro ⟨b, hb, hbc⟩ <;> refine ⟨b, ?_, hbc⟩
    · cases hb with
      | head => exact List.Mem.head _
      | tail _ hmem =>
        apply List.Mem.tail
        rcases List.mem_append.mp hmem with hq | hs
        · exact List.mem_append.mpr (Or.inl ((hq_iff b).mp hq))
        · exact List.mem_append.mpr (Or.inr ((hs_iff b).mp hs))
    · cases hb with
      | head => exact List.Mem.head _
      | tail _ hmem =>
        apply List.Mem.tail
        rcases List.mem_append.mp hmem with hq | hs
        · exact List.mem_append.mpr (Or.inl ((hq_iff b).mpr hq))
        · exact List.mem_append.mpr (Or.inr ((hs_iff b).mpr hs))

/-- Helper: same-format float-to-float conversion commutes with sign negation on
NaN inputs. -/
private theorem evalFloatToFloat_same_neg_of_nan (f : IeeeFormat) (x : Nat)
    (hx : isNaNBits f x = true) :
    evalFloatToFloatRoundTiesToEven f f (evalFloatNegProto f x) =
      evalFloatNegProto f (evalFloatToFloatRoundTiesToEven f f x) := by
  have hdec : ∃ neg q payload, decodeBits f x = .nan neg q payload := by
    unfold isNaNBits at hx
    cases hd : decodeBits f x with
    | nan neg q payload => exact ⟨neg, q, payload, rfl⟩
    | _ => rw [hd] at hx; cases hx
  obtain ⟨neg, q, payload, hd⟩ := hdec
  obtain ⟨_, _, hp_lt, _⟩ := decodeBits_nan_payload f x neg q payload hd
  have hd_neg := decodeBits_evalFloatNegProto_nan f x neg q payload hd
  rw [evalFloatToFloatRoundTiesToEven_of_nan f f (evalFloatNegProto f x) (!neg) q payload hd_neg,
      evalFloatToFloatRoundTiesToEven_of_nan f f x neg q payload hd]
  have hE : 2 ^ f.exponentBits - 1 < 2 ^ f.exponentBits :=
    Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  exact (evalFloatNegProto_encodeBits f neg _ _ hE (convertNaNPayload_lt f f payload hp_lt)).symm

theorem nanChoicesProto_mem_neg_second (f : IeeeFormat) (a b : Nat)
    (mode : FloatArithMode) (c : Nat) :
    c ∈ nanChoicesProto f [(f, a), (f, evalFloatNegProto f b)] mode ↔
      c ∈ nanChoicesProto f [(f, a), (f, b)] mode := by
  cases mode with
  | deterministic => rfl
  | nondeterministic =>
    unfold nanChoicesProto
    rw [expandNaNSigns_mem_iff, expandNaNSigns_mem_iff]
    have hflip_pair : ∀ x : Nat, x < 2 ^ f.width →
        ((c = evalFloatNegProto f x ∨ c = evalFloatNegProto f (evalFloatNegProto f x)) ↔
          (c = x ∨ c = evalFloatNegProto f x)) := by
      intro x hx
      rw [evalFloatNegProto_involutive f x hx, or_comm]
    have hq_b : ∀ x,
        (x ∈ quietedNaNCandidates f [(f, evalFloatNegProto f b)] ∧ (c = x ∨ c = evalFloatNegProto f x)) →
        ∃ y, y ∈ quietedNaNCandidates f [(f, b)] ∧ (c = y ∨ c = evalFloatNegProto f y) := by
      intro x hx
      rcases hx with ⟨hmem, hcx⟩
      unfold quietedNaNCandidates at hmem ⊢
      dsimp only at hmem ⊢
      rw [isNaNBits_evalFloatNegProto] at hmem
      by_cases hnb : isNaNBits f b = true
      · rw [if_pos' hnb] at hmem ⊢
        cases hmem with
        | head =>
          rw [evalFloatToFloat_same_neg_of_nan f b hnb] at hcx
          have hlt := evalFloatToFloatRoundTiesToEven_lt f f b
          exact ⟨evalFloatToFloatRoundTiesToEven f f b, List.Mem.head _, (hflip_pair _ hlt).mp hcx⟩
        | tail _ h => cases h
      · rw [if_neg' hnb] at hmem; cases hmem
    have hq_b_rev : ∀ x,
        (x ∈ quietedNaNCandidates f [(f, b)] ∧ (c = x ∨ c = evalFloatNegProto f x)) →
        ∃ y, y ∈ quietedNaNCandidates f [(f, evalFloatNegProto f b)] ∧ (c = y ∨ c = evalFloatNegProto f y) := by
      intro x hx
      rcases hx with ⟨hmem, hcx⟩
      unfold quietedNaNCandidates at hmem ⊢
      dsimp only at hmem ⊢
      rw [isNaNBits_evalFloatNegProto]
      by_cases hnb : isNaNBits f b = true
      · rw [if_pos' hnb] at hmem ⊢
        cases hmem with
        | head =>
          have hlt := evalFloatToFloatRoundTiesToEven_lt f f b
          refine ⟨evalFloatToFloatRoundTiesToEven f f (evalFloatNegProto f b), List.Mem.head _, ?_⟩
          rw [evalFloatToFloat_same_neg_of_nan f b hnb]
          exact (hflip_pair _ hlt).mpr hcx
        | tail _ h => cases h
      · rw [if_neg' hnb] at hmem; cases hmem
    have hs_b_eq : ∀ s : Nat,
        isSignalingNaNBits f s = true →
        signalingNaNCandidates f [(f, s)] = [s % 2 ^ f.width] := by
      intro s hs
      simp only [signalingNaNCandidates]
      rw [if_pos' hs]
      obtain ⟨hne, heq⟩ := same_format_signaling_candidate_eq f s hs
      have hnz : (((unpackBits f (evalFloatToFloatRoundTiesToEven f f s)).fraction %
          2 ^ (f.fractionBits - 1)) != 0) = true := by
        cases h0 : ((unpackBits f (evalFloatToFloatRoundTiesToEven f f s)).fraction %
            2 ^ (f.fractionBits - 1)) with
        | zero => exact absurd h0 hne
        | succ _ => rfl
      rw [if_pos' hnz, heq]
    have hsplit_q : ∀ x, quietedNaNCandidates f [(f, a), (f, x)] =
        quietedNaNCandidates f [(f, a)] ++ quietedNaNCandidates f [(f, x)] := by
      intro x
      by_cases ha : isNaNBits f a = true
      · simp only [quietedNaNCandidates, ha, ↓reduceIte, List.cons_append, List.nil_append]
      · simp only [quietedNaNCandidates, ha, Bool.false_eq_true, ↓reduceIte, List.nil_append]
    have hsplit_s : ∀ x, signalingNaNCandidates f [(f, a), (f, x)] =
        signalingNaNCandidates f [(f, a)] ++ signalingNaNCandidates f [(f, x)] := by
      intro x
      by_cases ha : isSignalingNaNBits f a = true
      · simp only [signalingNaNCandidates, ha, ↓reduceIte]
        split <;> simp only [List.cons_append, List.nil_append]
      · simp only [signalingNaNCandidates, ha, Bool.false_eq_true, ↓reduceIte, List.nil_append]
    rw [hsplit_q, hsplit_q, hsplit_s, hsplit_s]
    constructor
    · rintro ⟨x, hx, hcx⟩
      cases hx with
      | head => exact ⟨_, List.Mem.head _, hcx⟩
      | tail _ hmem =>
        rcases List.mem_append.mp hmem with hq | hs
        · rcases List.mem_append.mp hq with hqa | hqb
          · exact ⟨x, List.Mem.tail _ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hqa)))), hcx⟩
          · obtain ⟨y, hy, hcy⟩ := hq_b x ⟨hqb, hcx⟩
            exact ⟨y, List.Mem.tail _ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hy)))), hcy⟩
        · rcases List.mem_append.mp hs with hsa | hsb
          · exact ⟨x, List.Mem.tail _ (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hsa)))), hcx⟩
          · by_cases hsb_sig : isSignalingNaNBits f b = true
            · have hsb_neg : isSignalingNaNBits f (evalFloatNegProto f b) = true := by
                rw [isSignalingNaNBits_evalFloatNegProto]; exact hsb_sig
              rw [hs_b_eq (evalFloatNegProto f b) hsb_neg] at hsb
              cases hsb with
              | head =>
                rw [Nat.mod_eq_of_lt (evalFloatNegProto_lt f b), ← evalFloatNegProto_mod f b] at hcx
                have hbm : b % 2 ^ f.width < 2 ^ f.width := Nat.mod_lt _ (Nat.two_pow_pos _)
                refine ⟨b % 2 ^ f.width, List.Mem.tail _ (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr ?_)))),
                  (hflip_pair _ hbm).mp hcx⟩
                rw [hs_b_eq b hsb_sig]; exact List.Mem.head _
              | tail _ h => cases h
            · unfold signalingNaNCandidates at hsb
              dsimp only at hsb
              rw [isSignalingNaNBits_evalFloatNegProto, if_neg' hsb_sig] at hsb
              cases hsb
    · rintro ⟨x, hx, hcx⟩
      cases hx with
      | head => exact ⟨_, List.Mem.head _, hcx⟩
      | tail _ hmem =>
        rcases List.mem_append.mp hmem with hq | hs
        · rcases List.mem_append.mp hq with hqa | hqb
          · exact ⟨x, List.Mem.tail _ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hqa)))), hcx⟩
          · obtain ⟨y, hy, hcy⟩ := hq_b_rev x ⟨hqb, hcx⟩
            exact ⟨y, List.Mem.tail _ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hy)))), hcy⟩
        · rcases List.mem_append.mp hs with hsa | hsb
          · exact ⟨x, List.Mem.tail _ (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hsa)))), hcx⟩
          · by_cases hsb_sig : isSignalingNaNBits f b = true
            · have hsb_neg : isSignalingNaNBits f (evalFloatNegProto f b) = true := by
                rw [isSignalingNaNBits_evalFloatNegProto]; exact hsb_sig
              rw [hs_b_eq b hsb_sig] at hsb
              cases hsb with
              | head =>
                have hbm : b % 2 ^ f.width < 2 ^ f.width := Nat.mod_lt _ (Nat.two_pow_pos _)
                refine ⟨evalFloatNegProto f b % 2 ^ f.width,
                  List.Mem.tail _ (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr ?_)))), ?_⟩
                · rw [hs_b_eq (evalFloatNegProto f b) hsb_neg]; exact List.Mem.head _
                · rw [Nat.mod_eq_of_lt (evalFloatNegProto_lt f b), ← evalFloatNegProto_mod f b]
                  exact (hflip_pair _ hbm).mpr hcx
              | tail _ h => cases h
            · unfold signalingNaNCandidates at hsb
              dsimp only at hsb
              rw [if_neg' hsb_sig] at hsb
              cases hsb

/-- Mode-parametric relational semantics for binary floating-point arithmetic:
- when `base := evalFloatArithBaseProto op f lhs rhs` is non-NaN, `out = base`;
- when `base` is NaN, `out ∈ nanChoicesProto f [(f, lhs), (f, rhs)] mode`. -/
def EvalFloatBinOpRel (mode : FloatArithMode) (op : BinOp) (f : IeeeFormat)
    (lhs rhs out : Nat) : Prop :=
  isFloatArithBinOp op = true ∧
    let base := evalFloatArithBaseProto op f lhs rhs
    if isNaNBits f base then
      out ∈ nanChoicesProto f [(f, lhs), (f, rhs)] mode
    else
      out = base

private theorem roundRatioTiesToEven_not_nan (f : IeeeFormat) (neg : Bool) (n d : Nat) (hd : 0 < d) :
    isNaNBits f (roundRatioTiesToEven f neg n d) = false := by
  have h := (roundRatioBits_valid_and_not_nan .tiesToEven f neg n d hd).2
  rw [roundRatioBits_tiesToEven] at h
  exact h

private theorem exactSumProto_eq_preferredNaN_of_isNaN (f : IeeeFormat) (l r : FloatKind)
    (hl : ∀ neg n d, l = .finite neg n d → 0 < d)
    (hr : ∀ neg n d, r = .finite neg n d → 0 < d)
    (hnan : isNaNBits f (exactSumProto f l r) = true) :
    exactSumProto f l r = preferredNaNBits f := by
  unfold exactSumProto at hnan ⊢
  cases l with
  | nan _ _ _ => rfl
  | inf ln =>
    cases r with
    | nan _ _ _ => rfl
    | inf rn =>
      cases ln <;> cases rn
      · simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hnan
        rw [isNaNBits, decodeBits_infBits] at hnan; cases hnan
      · rfl
      · rfl
      · simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hnan
        rw [isNaNBits, decodeBits_infBits] at hnan; cases hnan
    | zero _ => rw [isNaNBits, decodeBits_infBits] at hnan; cases hnan
    | finite _ _ _ => rw [isNaNBits, decodeBits_infBits] at hnan; cases hnan
  | zero ln =>
    cases r with
    | nan _ _ _ => rfl
    | inf rn => rw [isNaNBits, decodeBits_infBits] at hnan; cases hnan
    | zero rn => rw [isNaNBits, decodeBits_zeroBits] at hnan; cases hnan
    | finite rn rnum rden =>
      have hnot := roundRatioTiesToEven_not_nan f rn rnum rden (hr rn rnum rden rfl)
      rw [hnot] at hnan; cases hnan
  | finite ln lnum lden =>
    cases r with
    | nan _ _ _ => rfl
    | inf rn => rw [isNaNBits, decodeBits_infBits] at hnan; cases hnan
    | zero _ =>
      have hnot := roundRatioTiesToEven_not_nan f ln lnum lden (hl ln lnum lden rfl)
      rw [hnot] at hnan; cases hnan
    | finite rn rnum rden =>
      dsimp only at hnan ⊢
      let n : Int := signedNum ln lnum * Int.ofNat rden + signedNum rn rnum * Int.ofNat lden
      have hnot := roundRatioTiesToEven_not_nan f (decide (n < 0)) n.natAbs (lden * rden)
        (Nat.mul_pos (hl ln lnum lden rfl) (hr rn rnum rden rfl))
      rw [hnot] at hnan; cases hnan

theorem evalFloatArithBaseProto_eq_preferredNaN_of_isNaN (op : BinOp) (f : IeeeFormat)
    (lhs rhs : Nat) (hnan : isNaNBits f (evalFloatArithBaseProto op f lhs rhs) = true) :
    evalFloatArithBaseProto op f lhs rhs = preferredNaNBits f := by
  unfold evalFloatArithBaseProto at hnan ⊢
  cases op with
  | add =>
    exact exactSumProto_eq_preferredNaN_of_isNaN f _ _
      (fun neg n d h => decodeBits_finite_den_pos f lhs neg n d h)
      (fun neg n d h => decodeBits_finite_den_pos f rhs neg n d h)
      hnan
  | sub =>
    apply exactSumProto_eq_preferredNaN_of_isNaN f _ _
      (fun neg n d h => decodeBits_finite_den_pos f lhs neg n d h)
      _ hnan
    intro neg n d h
    cases hr : decodeBits f rhs with
    | finite rn rn' rd' =>
      rw [hr] at h; injection h with _ _ hd; subst hd
      exact decodeBits_finite_den_pos f rhs rn rn' rd' hr
    | _ => rw [hr] at h; cases h
  | mul =>
    cases hl : decodeBits f lhs with
    | nan _ _ _ => rfl
    | inf ln =>
      cases hr : decodeBits f rhs with
      | nan _ _ _ => rfl
      | zero _ => rfl
      | inf rn => rw [hl, hr, isNaNBits, decodeBits_infBits] at hnan; cases hnan
      | finite rn _ _ => rw [hl, hr, isNaNBits, decodeBits_infBits] at hnan; cases hnan
    | zero ln =>
      cases hr : decodeBits f rhs with
      | nan _ _ _ => rfl
      | inf _ => rfl
      | zero rn => rw [hl, hr, isNaNBits, decodeBits_zeroBits] at hnan; cases hnan
      | finite rn _ _ => rw [hl, hr, isNaNBits, decodeBits_zeroBits] at hnan; cases hnan
    | finite ln lnum lden =>
      cases hr : decodeBits f rhs with
      | nan _ _ _ => rfl
      | inf rn => rw [hl, hr, isNaNBits, decodeBits_infBits] at hnan; cases hnan
      | zero rn => rw [hl, hr, isNaNBits, decodeBits_zeroBits] at hnan; cases hnan
      | finite rn rnum rden =>
        rw [hl, hr] at hnan
        have hnot := roundRatioTiesToEven_not_nan f (xor ln rn) (lnum * rnum) (lden * rden)
          (Nat.mul_pos (decodeBits_finite_den_pos f lhs ln lnum lden hl)
            (decodeBits_finite_den_pos f rhs rn rnum rden hr))
        rw [hnot] at hnan; cases hnan
  | div =>
    cases hl : decodeBits f lhs with
    | nan _ _ _ => rfl
    | inf ln =>
      cases hr : decodeBits f rhs with
      | nan _ _ _ => rfl
      | inf _ => rfl
      | zero rn => rw [hl, hr, isNaNBits, decodeBits_infBits] at hnan; cases hnan
      | finite rn _ _ => rw [hl, hr, isNaNBits, decodeBits_infBits] at hnan; cases hnan
    | zero ln =>
      cases hr : decodeBits f rhs with
      | nan _ _ _ => rfl
      | zero _ => rfl
      | inf rn => rw [hl, hr, isNaNBits, decodeBits_zeroBits] at hnan; cases hnan
      | finite rn _ _ => rw [hl, hr, isNaNBits, decodeBits_zeroBits] at hnan; cases hnan
    | finite ln lnum lden =>
      cases hr : decodeBits f rhs with
      | nan _ _ _ => rfl
      | zero rn => rw [hl, hr, isNaNBits, decodeBits_infBits] at hnan; cases hnan
      | inf rn => rw [hl, hr, isNaNBits, decodeBits_zeroBits] at hnan; cases hnan
      | finite rn rnum rden =>
        rw [hl, hr] at hnan
        have hnot := roundRatioTiesToEven_not_nan f (xor ln rn) (lnum * rden) (lden * rnum)
          (Nat.mul_pos (decodeBits_finite_den_pos f lhs ln lnum lden hl)
            (decodeBits_finite_num_pos f rhs rn rnum rden hr))
        rw [hnot] at hnan; cases hnan
  | rem =>
    cases hl : decodeBits f lhs with
    | nan _ _ _ => rfl
    | inf _ => cases decodeBits f rhs <;> rfl
    | zero ln =>
      cases hr : decodeBits f rhs with
      | nan _ _ _ => rfl
      | zero _ => rfl
      | inf _ => rw [hl, hr] at hnan; unfold isNaNBits at hnan; rw [decodeBits_mod_width, hl] at hnan; cases hnan
      | finite _ _ _ => rw [hl, hr, isNaNBits, decodeBits_zeroBits] at hnan; cases hnan
    | finite ln lnum lden =>
      cases hr : decodeBits f rhs with
      | nan _ _ _ => rfl
      | zero _ => rfl
      | inf _ => rw [hl, hr] at hnan; unfold isNaNBits at hnan; rw [decodeBits_mod_width, hl] at hnan; cases hnan
      | finite rn rnum rden =>
        rw [hl, hr] at hnan
        dsimp only at hnan
        have hnot := roundRatioTiesToEven_not_nan f ln
          (lnum * rden - lnum * rden / (lden * rnum) * (lden * rnum)) (lden * rden)
          (Nat.mul_pos (decodeBits_finite_den_pos f lhs ln lnum lden hl)
            (decodeBits_finite_den_pos f rhs rn rnum rden hr))
        rw [hnot] at hnan; cases hnan
  | _ => rfl

theorem EvalFloatBinOpRel.det_iff (op : BinOp) (f : IeeeFormat) (lhs rhs out : Nat) :
    EvalFloatBinOpRel .deterministic op f lhs rhs out ↔
      (isFloatArithBinOp op = true ∧ out = evalFloatArithBaseProto op f lhs rhs) := by
  unfold EvalFloatBinOpRel
  dsimp only
  constructor
  · rintro ⟨hop, hbody⟩
    refine ⟨hop, ?_⟩
    by_cases hnan : isNaNBits f (evalFloatArithBaseProto op f lhs rhs) = true
    · rw [if_pos' hnan] at hbody
      unfold nanChoicesProto at hbody
      cases hbody with
      | head => exact (evalFloatArithBaseProto_eq_preferredNaN_of_isNaN op f lhs rhs hnan).symm
      | tail _ h => cases h
    · rw [if_neg' hnan] at hbody; exact hbody
  · rintro ⟨hop, rfl⟩
    refine ⟨hop, ?_⟩
    by_cases hnan : isNaNBits f (evalFloatArithBaseProto op f lhs rhs) = true
    · rw [if_pos' hnan, evalFloatArithBaseProto_eq_preferredNaN_of_isNaN op f lhs rhs hnan]
      exact preferredNaNBits_mem_nanChoicesProto f _ .deterministic
    · rw [if_neg' hnan]

theorem EvalFloatBinOpRel.det_imp_nondet (op : BinOp) (f : IeeeFormat) (lhs rhs out : Nat)
    (h : EvalFloatBinOpRel .deterministic op f lhs rhs out) :
    EvalFloatBinOpRel .nondeterministic op f lhs rhs out := by
  unfold EvalFloatBinOpRel at h ⊢
  refine ⟨h.1, ?_⟩
  have hb := h.2
  dsimp only at hb ⊢
  by_cases hnan : isNaNBits f (evalFloatArithBaseProto op f lhs rhs) = true
  · rw [if_pos' hnan] at hb ⊢
    exact nanChoicesProto_det_subset_nondet f [(f, lhs), (f, rhs)] out hb
  · rw [if_neg' hnan] at hb ⊢
    exact hb

theorem EvalFloatBinOpRel.total (mode : FloatArithMode) (op : BinOp) (f : IeeeFormat)
    (lhs rhs : Nat) (hop : isFloatArithBinOp op = true) :
    ∃ out, EvalFloatBinOpRel mode op f lhs rhs out := by
  have hdet : EvalFloatBinOpRel .deterministic op f lhs rhs (evalFloatArithBaseProto op f lhs rhs) :=
    (EvalFloatBinOpRel.det_iff op f lhs rhs _).mpr ⟨hop, rfl⟩
  cases mode with
  | deterministic => exact ⟨_, hdet⟩
  | nondeterministic => exact ⟨_, EvalFloatBinOpRel.det_imp_nondet op f lhs rhs _ hdet⟩

theorem EvalFloatBinOpRel.out_lt (mode : FloatArithMode) (op : BinOp) (f : IeeeFormat)
    (lhs rhs out : Nat) (h : EvalFloatBinOpRel mode op f lhs rhs out) :
    out < 2 ^ f.width := by
  have hb := h.2
  dsimp only at hb
  by_cases hnan : isNaNBits f (evalFloatArithBaseProto op f lhs rhs) = true
  · rw [if_pos' hnan] at hb
    exact (nanChoicesProto_mem_lt_and_nan f _ mode out hb).1
  · rw [if_neg' hnan] at hb
    rw [hb]
    exact evalFloatArithBaseProto_lt op f lhs rhs

theorem EvalFloatBinOpRel.nan_iff (mode : FloatArithMode) (op : BinOp) (f : IeeeFormat)
    (lhs rhs out : Nat) (h : EvalFloatBinOpRel mode op f lhs rhs out) :
    isNaNBits f out = isNaNBits f (evalFloatArithBaseProto op f lhs rhs) := by
  have hb := h.2
  dsimp only at hb
  by_cases hnan : isNaNBits f (evalFloatArithBaseProto op f lhs rhs) = true
  · rw [if_pos' hnan] at hb
    rw [hnan]
    exact (nanChoicesProto_mem_lt_and_nan f _ mode out hb).2
  · rw [if_neg' hnan] at hb
    rw [hb]

theorem evalFloatArithBaseProto_nan_left (op : BinOp) (f : IeeeFormat) (lhs rhs : Nat)
    (hl : isNaNBits f lhs = true) :
    evalFloatArithBaseProto op f lhs rhs = preferredNaNBits f := by
  unfold isNaNBits at hl
  unfold evalFloatArithBaseProto
  cases hd : decodeBits f lhs with
  | nan _ _ _ =>
    cases op <;> rfl
  | _ => rw [hd] at hl; cases hl

theorem evalFloatArithBaseProto_nan_right (op : BinOp) (f : IeeeFormat) (lhs rhs : Nat)
    (hr : isNaNBits f rhs = true) :
    evalFloatArithBaseProto op f lhs rhs = preferredNaNBits f := by
  unfold isNaNBits at hr
  unfold evalFloatArithBaseProto
  cases hd : decodeBits f rhs with
  | nan _ _ _ =>
    cases op <;> try rfl
    · unfold exactSumProto; cases decodeBits f lhs <;> rfl
    · unfold exactSumProto; dsimp only [negateFloatKind]; cases decodeBits f lhs <;> rfl
    · cases decodeBits f lhs <;> rfl
    · cases decodeBits f lhs <;> rfl
    · cases decodeBits f lhs <;> rfl
  | _ => rw [hd] at hr; cases hr

theorem EvalFloatBinOpRel.quieted_lhs_mem (op : BinOp) (f : IeeeFormat) (lhs rhs : Nat)
    (hop : isFloatArithBinOp op = true) (hl : isNaNBits f lhs = true) :
    EvalFloatBinOpRel .nondeterministic op f lhs rhs (evalFloatToFloatRoundTiesToEven f f lhs) := by
  refine ⟨hop, ?_⟩
  dsimp only
  rw [evalFloatArithBaseProto_nan_left op f lhs rhs hl]
  have hpn : isNaNBits f (preferredNaNBits f) = true := by cases f <;> decide
  rw [if_pos' hpn]
  unfold nanChoicesProto
  rw [expandNaNSigns_mem_iff]
  refine ⟨evalFloatToFloatRoundTiesToEven f f lhs, List.Mem.tail _ (List.mem_append.mpr (Or.inl ?_)), Or.inl rfl⟩
  simp only [quietedNaNCandidates]
  rw [if_pos' hl]
  exact List.Mem.head _

theorem EvalFloatBinOpRel.quieted_rhs_mem (op : BinOp) (f : IeeeFormat) (lhs rhs : Nat)
    (hop : isFloatArithBinOp op = true) (hr : isNaNBits f rhs = true) :
    EvalFloatBinOpRel .nondeterministic op f lhs rhs (evalFloatToFloatRoundTiesToEven f f rhs) := by
  refine ⟨hop, ?_⟩
  dsimp only
  rw [evalFloatArithBaseProto_nan_right op f lhs rhs hr]
  have hpn : isNaNBits f (preferredNaNBits f) = true := by cases f <;> decide
  rw [if_pos' hpn]
  unfold nanChoicesProto
  rw [expandNaNSigns_mem_iff]
  refine ⟨evalFloatToFloatRoundTiesToEven f f rhs, List.Mem.tail _ (List.mem_append.mpr (Or.inl ?_)), Or.inl rfl⟩
  simp only [quietedNaNCandidates]
  by_cases hl : isNaNBits f lhs = true
  · rw [if_pos' hl, if_pos' hr]
    exact List.Mem.tail _ (List.Mem.head _)
  · rw [if_neg' hl, if_pos' hr]
    exact List.Mem.head _

theorem EvalFloatBinOpRel.signaling_lhs_mem (op : BinOp) (f : IeeeFormat) (lhs rhs : Nat)
    (hop : isFloatArithBinOp op = true) (hl : isSignalingNaNBits f lhs = true) :
    EvalFloatBinOpRel .nondeterministic op f lhs rhs (lhs % 2 ^ f.width) := by
  have hnan : isNaNBits f lhs = true := by
    unfold isSignalingNaNBits at hl; unfold isNaNBits
    cases hd : decodeBits f lhs with
    | nan _ _ _ => rfl
    | _ => rw [hd] at hl; cases hl
  refine ⟨hop, ?_⟩
  dsimp only
  rw [evalFloatArithBaseProto_nan_left op f lhs rhs hnan]
  have hpn : isNaNBits f (preferredNaNBits f) = true := by cases f <;> decide
  rw [if_pos' hpn]
  unfold nanChoicesProto
  rw [expandNaNSigns_mem_iff]
  refine ⟨lhs % 2 ^ f.width, List.Mem.tail _ (List.mem_append.mpr (Or.inr ?_)), Or.inl rfl⟩
  unfold signalingNaNCandidates
  dsimp only
  rw [if_pos' hl]
  obtain ⟨hne, heq⟩ := same_format_signaling_candidate_eq f lhs hl
  have hnz : (((unpackBits f (evalFloatToFloatRoundTiesToEven f f lhs)).fraction %
      2 ^ (f.fractionBits - 1)) != 0) = true := by
    cases h0 : ((unpackBits f (evalFloatToFloatRoundTiesToEven f f lhs)).fraction %
        2 ^ (f.fractionBits - 1)) with
    | zero => exact absurd h0 hne
    | succ _ => rfl
  rw [if_pos' hnz, heq]
  exact List.Mem.head _

theorem EvalFloatBinOpRel.add_comm (mode : FloatArithMode) (f : IeeeFormat) (a b out : Nat) :
    EvalFloatBinOpRel mode .add f a b out ↔ EvalFloatBinOpRel mode .add f b a out := by
  unfold EvalFloatBinOpRel
  dsimp only
  rw [evalFloatArithBaseProto_add_comm f a b]
  by_cases hnan : isNaNBits f (evalFloatArithBaseProto .add f b a) = true
  · rw [if_pos' hnan, if_pos' hnan, nanChoicesProto_mem_swap_pair]
  · rw [if_neg' hnan, if_neg' hnan]

theorem EvalFloatBinOpRel.mul_comm (mode : FloatArithMode) (f : IeeeFormat) (a b out : Nat) :
    EvalFloatBinOpRel mode .mul f a b out ↔ EvalFloatBinOpRel mode .mul f b a out := by
  unfold EvalFloatBinOpRel
  dsimp only
  rw [evalFloatArithBaseProto_mul_comm f a b]
  by_cases hnan : isNaNBits f (evalFloatArithBaseProto .mul f b a) = true
  · rw [if_pos' hnan, if_pos' hnan, nanChoicesProto_mem_swap_pair]
  · rw [if_neg' hnan, if_neg' hnan]

theorem EvalFloatBinOpRel.sub_eq_add_neg (mode : FloatArithMode) (f : IeeeFormat)
    (a b out : Nat) :
    EvalFloatBinOpRel mode .sub f a b out ↔
      EvalFloatBinOpRel mode .add f a (evalFloatNegProto f b) out := by
  unfold EvalFloatBinOpRel
  dsimp only
  rw [evalFloatArithBaseProto_sub_eq_add_neg f a b]
  by_cases hnan : isNaNBits f (evalFloatArithBaseProto .add f a (evalFloatNegProto f b)) = true
  · rw [if_pos' hnan, if_pos' hnan, nanChoicesProto_mem_neg_second]
    rfl
  · rw [if_neg' hnan, if_neg' hnan]
    rfl

/-! ## §5. Prototype MIR `Rvalue` Float Dispatcher & Existing TCB Float Misdispatch Witness -/

/-- Extract the `FloatTy` of an optional static MIR type. -/
def floatTyOf? : Option Ty → Option FloatTy
  | .some ty =>
    match ty.kind with
    | .float fk => .some fk
    | _ => .none
  | .none => .none

/-- Map modeled IEEE-754 formats (`f32`/`f64`) to `IeeeFormat`, failing closed
on `f16`/`f128`. -/
def ieeeFormatOfFloatTy? : FloatTy → Option IeeeFormat
  | .f32 => .some .binary32
  | .f64 => .some .binary64
  | .f16 | .f128 => .none

/-- Prototype MIR `Rvalue` evaluator extending `Trusted.MirSemantics.evalRvalue`
with IEEE-754 `f32`/`f64` `.unaryOp .neg` and `.binaryOp` (arithmetic and
comparisons), failing closed with `.unsupported` on `f16`/`f128` or operand
type/width mismatches, and delegating identically to `evalRvalue` whenever no
operand has `.float _` static type. -/
def evalRvalueFloatProto
    (locals : List LocalSlot)
    (rv : Rvalue)
    (mem : Memory := emptyMemory)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    RvalueEvalResult :=
  match rv with
  | .unaryOp .neg op =>
    match floatTyOf? (operandTy localDecls layouts op) with
    | .none => evalRvalue locals rv mem localDecls layouts
    | .some fk =>
      match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
      | .ub => .ub
      | .unsupported => .unsupported
      | .ok (.scalar sc) locals' =>
        match ieeeFormatOfFloatTy? fk with
        | .none => .unsupported
        | .some fmt =>
          match Nat.beq sc.sizeBytes fmt.byteWidth with
          | false => .unsupported
          | true => .ok (.scalar ⟨evalFloatNegProto fmt sc.bits, fmt.byteWidth⟩) locals' mem
      | .ok _ _ => .unsupported
  | .binaryOp op lhsOp rhsOp =>
    match floatTyOf? (operandTy localDecls layouts lhsOp),
          floatTyOf? (operandTy localDecls layouts rhsOp) with
    | .none, .none => evalRvalue locals rv mem localDecls layouts
    | .some lhsFk, .some rhsFk =>
      match evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
      | .ub => .ub
      | .unsupported => .unsupported
      | .ok lhsVal locals₁ =>
        match evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
        | .ub => .ub
        | .unsupported => .unsupported
        | .ok rhsVal locals₂ =>
          match lhsVal, rhsVal with
          | .scalar lhsSc, .scalar rhsSc =>
            match ieeeFormatOfFloatTy? lhsFk, ieeeFormatOfFloatTy? rhsFk with
            | .some fmtL, .some fmtR =>
              if fmtL == fmtR && Nat.beq lhsSc.sizeBytes fmtL.byteWidth &&
                  Nat.beq rhsSc.sizeBytes fmtL.byteWidth then
                match evalFloatArithBaseProto? op fmtL lhsSc.bits rhsSc.bits with
                | .some bits => .ok (.scalar ⟨bits, fmtL.byteWidth⟩) locals₂ mem
                | .none =>
                  match evalFloatCmpProto? op fmtL lhsSc.bits rhsSc.bits with
                  | .some b => .ok (.scalar (boolToScalar b)) locals₂ mem
                  | .none => .unsupported
              else .unsupported
            | _, _ => .unsupported
          | _, _ => .unsupported
    | _, _ => .unsupported
  | _ => evalRvalue locals rv mem localDecls layouts

/-- Relational MIR `Rvalue` float semantics parameterized by `FloatArithMode`:
on `f32`/`f64` binary arithmetic ops, permits any `out` satisfying
`EvalFloatBinOpRel mode op fmt lhsSc.bits rhsSc.bits out`; everywhere else
coincides with `evalRvalueFloatProto`. -/
def EvalRvalueFloatRelProto
    (mode : FloatArithMode)
    (locals : List LocalSlot)
    (rv : Rvalue)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (res : RvalueEvalResult) : Prop :=
  match rv with
  | .binaryOp op lhsOp rhsOp =>
    match floatTyOf? (operandTy localDecls layouts lhsOp),
          floatTyOf? (operandTy localDecls layouts rhsOp) with
    | .some lhsFk, .some rhsFk =>
      match evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
      | .ok (.scalar lhsSc) locals₁ =>
        match evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
        | .ok (.scalar rhsSc) locals₂ =>
          match ieeeFormatOfFloatTy? lhsFk, ieeeFormatOfFloatTy? rhsFk with
          | .some fmtL, .some fmtR =>
            if fmtL == fmtR && Nat.beq lhsSc.sizeBytes fmtL.byteWidth &&
                Nat.beq rhsSc.sizeBytes fmtL.byteWidth && isFloatArithBinOp op then
              ∃ out, EvalFloatBinOpRel mode op fmtL lhsSc.bits rhsSc.bits out ∧
                res = .ok (.scalar ⟨out, fmtL.byteWidth⟩) locals₂ mem
            else res = evalRvalueFloatProto locals rv mem localDecls layouts
          | _, _ => res = evalRvalueFloatProto locals rv mem localDecls layouts
        | _ => res = evalRvalueFloatProto locals rv mem localDecls layouts
      | _ => res = evalRvalueFloatProto locals rv mem localDecls layouts
    | _, _ => res = evalRvalueFloatProto locals rv mem localDecls layouts
  | _ => res = evalRvalueFloatProto locals rv mem localDecls layouts

/-- Conservative extension: whenever no operand of `.unaryOp .neg` or `.binaryOp`
has static `.float _` type, `evalRvalueFloatProto` is identical to `evalRvalue`. -/
theorem evalRvalueFloatProto_nonFloat_eq
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hNonFloat :
      (∀ op, rv = .unaryOp .neg op → floatTyOf? (operandTy localDecls layouts op) = .none) ∧
      (∀ op lhs rhs, rv = .binaryOp op lhs rhs →
        floatTyOf? (operandTy localDecls layouts lhs) = .none ∧
        floatTyOf? (operandTy localDecls layouts rhs) = .none)) :
    evalRvalueFloatProto locals rv mem localDecls layouts =
      evalRvalue locals rv mem localDecls layouts := by
  cases rv with
  | unaryOp uop op =>
    cases uop with
    | neg =>
      unfold evalRvalueFloatProto
      dsimp only
      rw [hNonFloat.1 op rfl]
    | not => rfl
    | ptrMetadata => rfl
  | binaryOp op lhs rhs =>
    unfold evalRvalueFloatProto
    dsimp only
    obtain ⟨hl, hr⟩ := hNonFloat.2 op lhs rhs rfl
    rw [hl, hr]
  | _ => rfl

theorem EvalRvalueFloatRelProto.det_iff
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (res : RvalueEvalResult) :
    EvalRvalueFloatRelProto .deterministic locals rv mem localDecls layouts res ↔
      res = evalRvalueFloatProto locals rv mem localDecls layouts := by
  unfold EvalRvalueFloatRelProto
  cases rv with
  | binaryOp op lhsOp rhsOp =>
    dsimp only
    cases hlTy : floatTyOf? (operandTy localDecls layouts lhsOp) with
    | none => exact Iff.rfl
    | some lhsFk =>
      cases hrTy : floatTyOf? (operandTy localDecls layouts rhsOp) with
      | none => exact Iff.rfl
      | some rhsFk =>
        cases hlEv : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
        | ub => exact Iff.rfl
        | unsupported => exact Iff.rfl
        | ok lv locals₁ =>
          cases lv with
          | scalar lhsSc =>
            dsimp only
            cases hrEv : evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
            | ub => exact Iff.rfl
            | unsupported => exact Iff.rfl
            | ok rvVal locals₂ =>
              cases rvVal with
              | scalar rhsSc =>
                dsimp only
                cases hfmtL : ieeeFormatOfFloatTy? lhsFk with
                | none => exact Iff.rfl
                | some fmtL =>
                  cases hfmtR : ieeeFormatOfFloatTy? rhsFk with
                  | none => exact Iff.rfl
                  | some fmtR =>
                    dsimp only
                    by_cases hcond : (fmtL == fmtR && Nat.beq lhsSc.sizeBytes fmtL.byteWidth &&
                        Nat.beq rhsSc.sizeBytes fmtL.byteWidth && isFloatArithBinOp op) = true
                    · rw [if_pos' hcond]
                      have hcond3 : (fmtL == fmtR && Nat.beq lhsSc.sizeBytes fmtL.byteWidth &&
                          Nat.beq rhsSc.sizeBytes fmtL.byteWidth) = true := by
                        cases h1 : (fmtL == fmtR && Nat.beq lhsSc.sizeBytes fmtL.byteWidth &&
                            Nat.beq rhsSc.sizeBytes fmtL.byteWidth) <;> rw [h1] at hcond <;> first | rfl | cases hcond
                      have hop : isFloatArithBinOp op = true := by
                        rw [hcond3] at hcond; exact hcond
                      have heval : evalRvalueFloatProto locals (.binaryOp op lhsOp rhsOp) mem localDecls layouts =
                          .ok (.scalar ⟨evalFloatArithBaseProto op fmtL lhsSc.bits rhsSc.bits, fmtL.byteWidth⟩) locals₂ mem := by
                        unfold evalRvalueFloatProto
                        dsimp only
                        rw [hlTy, hrTy]; dsimp only
                        rw [hlEv]; dsimp only
                        rw [hrEv]; dsimp only
                        rw [hfmtL, hfmtR]; dsimp only
                        rw [if_pos' hcond3]
                        unfold evalFloatArithBaseProto?
                        rw [if_pos' hop]
                      rw [heval]
                      constructor
                      · rintro ⟨out, hrel, rfl⟩
                        obtain ⟨_, rfl⟩ := (EvalFloatBinOpRel.det_iff op fmtL lhsSc.bits rhsSc.bits out).mp hrel
                        rfl
                      · intro hres
                        exact ⟨evalFloatArithBaseProto op fmtL lhsSc.bits rhsSc.bits,
                          (EvalFloatBinOpRel.det_iff op fmtL lhsSc.bits rhsSc.bits _).mpr ⟨hop, rfl⟩,
                          hres⟩
                    · rw [if_neg' hcond]
              | _ => exact Iff.rfl
          | _ => exact Iff.rfl
  | _ => exact Iff.rfl

theorem EvalRvalueFloatRelProto.det_imp_nondet
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (res : RvalueEvalResult)
    (h : EvalRvalueFloatRelProto .deterministic locals rv mem localDecls layouts res) :
    EvalRvalueFloatRelProto .nondeterministic locals rv mem localDecls layouts res := by
  unfold EvalRvalueFloatRelProto at h ⊢
  cases rv with
  | binaryOp op lhsOp rhsOp =>
    dsimp only at h ⊢
    cases hlTy : floatTyOf? (operandTy localDecls layouts lhsOp) with
    | none => rw [hlTy] at h; exact h
    | some lhsFk =>
      rw [hlTy] at h
      cases hrTy : floatTyOf? (operandTy localDecls layouts rhsOp) with
      | none => rw [hrTy] at h; exact h
      | some rhsFk =>
        rw [hrTy] at h
        cases hlEv : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
        | ok lv locals₁ =>
          rw [hlEv] at h
          cases lv with
          | scalar lhsSc =>
            dsimp only at h ⊢
            cases hrEv : evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
            | ok rvVal locals₂ =>
              rw [hrEv] at h
              cases rvVal with
              | scalar rhsSc =>
                dsimp only at h ⊢
                cases hfmtL : ieeeFormatOfFloatTy? lhsFk with
                | none => rw [hfmtL] at h; exact h
                | some fmtL =>
                  rw [hfmtL] at h
                  cases hfmtR : ieeeFormatOfFloatTy? rhsFk with
                  | none => rw [hfmtR] at h; exact h
                  | some fmtR =>
                    rw [hfmtR] at h; dsimp only at h ⊢
                    by_cases hcond : (fmtL == fmtR && Nat.beq lhsSc.sizeBytes fmtL.byteWidth &&
                        Nat.beq rhsSc.sizeBytes fmtL.byteWidth && isFloatArithBinOp op) = true
                    · rw [if_pos' hcond] at h ⊢
                      obtain ⟨out, hrel, hres⟩ := h
                      exact ⟨out, EvalFloatBinOpRel.det_imp_nondet op fmtL lhsSc.bits rhsSc.bits out hrel, hres⟩
                    · rw [if_neg' hcond] at h ⊢
                      exact h
              | _ => exact h
            | _ => rw [hrEv] at h; exact h
          | _ => exact h
        | _ => rw [hlEv] at h; exact h
  | _ => exact h

/-- Concrete fixture demonstrating the existing float misdispatch bug in
`Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue` vs. `evalRvalueFloatProto`:
- locals `0`, `1`: `f32` (`1.0 = 0x3F800000`, `1.0 = 0x3F800000`);
- locals `2`, `3`: `f32` (`-0.0 = 0x80000000`, `+0.0 = 0x00000000`);
- local `4`: `f32` (`qNaN = 0x7FC00000`);
- local `5`: `f16` (`1.0_f16 = 0x3C00`);
- local `6`: `f128` (`1.0_f128 = 0x3FFF0000000000000000000000000000`). -/
def floatMisdispatchDecls : List LocalDecl := [
  { mutability := .not, ty := { kind := .float .f32, layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .float .f32, layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .float .f32, layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .float .f32, layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .float .f32, layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .float .f16, layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .float .f128, layoutIdx := 0 }, debugName := none }
]

def floatMisdispatchLocals : List LocalSlot := [
  .init (.scalar ⟨0x3F800000, 4⟩),
  .init (.scalar ⟨0x3F800000, 4⟩),
  .init (.scalar ⟨0x80000000, 4⟩),
  .init (.scalar ⟨0x00000000, 4⟩),
  .init (.scalar ⟨0x7FC00000, 4⟩),
  .init (.scalar ⟨0x3C00, 2⟩),
  .init (.scalar ⟨0x3FFF0000000000000000000000000000, 16⟩)
]

/-- Constructive witness that current `Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue`
silently misdispatches `.float` `.unaryOp .neg` and `.binaryOp` to integer
two's-complement / unsigned operations, whereas `evalRvalueFloatProto` computes
exact IEEE-754 results on `f32`/`f64` and fails closed with `.unsupported` on
`f16`/`f128` and type mismatches. -/
theorem trusted_evalRvalue_float_misdispatch_witness :
    -- 1. -1.0_f32: Trusted.evalRvalue produces 0xC0800000 (-4.0_f32!), proto produces 0xBF800000 (-1.0_f32)
    evalRvalue floatMisdispatchLocals (.unaryOp .neg (.copy ⟨0, []⟩)) emptyMemory
        floatMisdispatchDecls emptyLayoutTable =
      .ok (.scalar ⟨0xC0800000, 4⟩) floatMisdispatchLocals emptyMemory ∧
    evalRvalueFloatProto floatMisdispatchLocals (.unaryOp .neg (.copy ⟨0, []⟩)) emptyMemory
        floatMisdispatchDecls emptyLayoutTable =
      .ok (.scalar ⟨0xBF800000, 4⟩) floatMisdispatchLocals emptyMemory ∧
    -- 2. 1.0_f32 + 1.0_f32: Trusted.evalRvalue produces 0x7F000000, proto produces 0x40000000 (2.0_f32)
    evalRvalue floatMisdispatchLocals (.binaryOp .add (.copy ⟨0, []⟩) (.copy ⟨1, []⟩)) emptyMemory
        floatMisdispatchDecls emptyLayoutTable =
      .ok (.scalar ⟨0x7F000000, 4⟩) floatMisdispatchLocals emptyMemory ∧
    evalRvalueFloatProto floatMisdispatchLocals (.binaryOp .add (.copy ⟨0, []⟩) (.copy ⟨1, []⟩)) emptyMemory
        floatMisdispatchDecls emptyLayoutTable =
      .ok (.scalar ⟨0x40000000, 4⟩) floatMisdispatchLocals emptyMemory ∧
    -- 3. -0.0_f32 == +0.0_f32: Trusted.evalRvalue produces false (0), proto produces true (1)
    evalRvalue floatMisdispatchLocals (.binaryOp .eq (.copy ⟨2, []⟩) (.copy ⟨3, []⟩)) emptyMemory
        floatMisdispatchDecls emptyLayoutTable =
      .ok (.scalar ⟨0, 1⟩) floatMisdispatchLocals emptyMemory ∧
    evalRvalueFloatProto floatMisdispatchLocals (.binaryOp .eq (.copy ⟨2, []⟩) (.copy ⟨3, []⟩)) emptyMemory
        floatMisdispatchDecls emptyLayoutTable =
      .ok (.scalar ⟨1, 1⟩) floatMisdispatchLocals emptyMemory ∧
    -- 4. NaN == NaN: Trusted.evalRvalue produces true (1!), proto produces false (0)
    evalRvalue floatMisdispatchLocals (.binaryOp .eq (.copy ⟨4, []⟩) (.copy ⟨4, []⟩)) emptyMemory
        floatMisdispatchDecls emptyLayoutTable =
      .ok (.scalar ⟨1, 1⟩) floatMisdispatchLocals emptyMemory ∧
    evalRvalueFloatProto floatMisdispatchLocals (.binaryOp .eq (.copy ⟨4, []⟩) (.copy ⟨4, []⟩)) emptyMemory
        floatMisdispatchDecls emptyLayoutTable =
      .ok (.scalar ⟨0, 1⟩) floatMisdispatchLocals emptyMemory ∧
    -- 5. f16 / f128 fail closed with .unsupported in evalRvalueFloatProto (while Trusted.evalRvalue misdispatches)
    evalRvalueFloatProto floatMisdispatchLocals (.unaryOp .neg (.copy ⟨5, []⟩)) emptyMemory
        floatMisdispatchDecls emptyLayoutTable = .unsupported ∧
    evalRvalueFloatProto floatMisdispatchLocals (.binaryOp .add (.copy ⟨5, []⟩) (.copy ⟨5, []⟩)) emptyMemory
        floatMisdispatchDecls emptyLayoutTable = .unsupported ∧
    evalRvalueFloatProto floatMisdispatchLocals (.unaryOp .neg (.copy ⟨6, []⟩)) emptyMemory
        floatMisdispatchDecls emptyLayoutTable = .unsupported ∧
    evalRvalueFloatProto floatMisdispatchLocals (.binaryOp .add (.copy ⟨6, []⟩) (.copy ⟨6, []⟩)) emptyMemory
        floatMisdispatchDecls emptyLayoutTable = .unsupported := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §6. Mode-Parametric `Ptr2IntTransmutePolicy` (`ucg#630` vs. `reference#1752`) -/

/-- Policy governing whether transmuting / byte-decoding initialized bytes that
carry pointer provenance into non-pointer scalar types (integers, floats, `bool`,
`char`, slice length metadata) strips provenance (`rust-lang/reference#1752`) or
triggers UB (`rust-lang/unsafe-code-guidelines#630`). -/
inductive Ptr2IntTransmutePolicy : Type where
  | stripProvenance : Ptr2IntTransmutePolicy
  | strictUcg630Ub : Ptr2IntTransmutePolicy
deriving DecidableEq, Repr

/-- `true` iff `policy` rejects `bytes` due to pointer provenance. -/
@[reducible]
def policyRejectsProv (policy : Ptr2IntTransmutePolicy) (bytes : List AbstractByte) : Bool :=
  match policy with
  | .stripProvenance => false
  | .strictUcg630Ub => abstractBytesHaveProv bytes

/-- Policy-parameterized pointer byte decoder (exact generalization of
`Trusted.Rustc.V2026_06_01.MirSemantics.decodePtrBytesNoForge`, using `.1`/`.2`
projections to satisfy projection discipline). -/
def decodePtrBytesNoForgeWithPolicy
    (policy : Ptr2IntTransmutePolicy)
    (isRef : Bool)
    (pointee : RigidTy)
    (ptrBytes : Nat)
    (bytes : List AbstractByte) :
    Option Value :=
  let dataOf (dataBytes : List AbstractByte) : Option Value :=
    match Nat.beq (length dataBytes) ptrBytes, decodeScalarBytes dataBytes false with
    | true, .some p =>
      let sv := p.1
      let prov := p.2
      match abstractBytesUniformProv dataBytes, prov with
      | true, .some ap =>
        .some (.ptr { allocId := ap.1, offsetBytes := sv.bits } ptrBytes)
      | _, _ =>
        match isRef with
        | true => .none
        | false => .some (.scalar ⟨sv.bits, ptrBytes⟩)
    | _, _ => .none
  let wideMetaIsDyn : Option Bool :=
    match pointee with
    | .slice _ => .some false
    | .str => .some false
    | .dynamic _ => .some true
    | _ => .none
  match wideMetaIsDyn with
  | .none => dataOf bytes
  | .some isDyn =>
    match Nat.beq (length bytes) (Nat.add ptrBytes ptrBytes) with
    | false => .none
    | true =>
      let metaBytes := dropAbstractBytes ptrBytes bytes
      let metaOpt : Option Value :=
        match decodeScalarBytes metaBytes false with
        | .none => .none
        | .some mp =>
          let metaSv := mp.1
          let metaProv := mp.2
          match isDyn, abstractBytesUniformProv metaBytes, metaProv with
          | true, true, .some vt =>
            .some (.ptr { allocId := vt.1, offsetBytes := metaSv.bits } ptrBytes)
          | true, _, _ => .some (.scalar ⟨metaSv.bits, ptrBytes⟩)
          | false, _, _ =>
            match policyRejectsProv policy metaBytes with
            | true => .none
            | false => .some (.scalar ⟨metaSv.bits, ptrBytes⟩)
      match dataOf (takeAbstractBytes ptrBytes bytes), metaOpt with
      | .some dataVal, .some metaVal => .some (.aggregate 0 (dataVal :: metaVal :: .nil))
      | _, _ => .none

/-- Policy-parameterized `ScalarLayout` byte decoder (exact generalization of
`Trusted.Rustc.V2026_06_01.MirSemantics.decodeScalarLayoutBytesNoForge`). -/
def decodeScalarLayoutBytesWithPolicy
    (policy : Ptr2IntTransmutePolicy)
    (sl : ScalarLayout)
    (bytes : List AbstractByte) :
    Option Value :=
  match scalarLayoutByteWidth sl with
  | .none => .none
  | .some sz =>
    match Nat.beq (length bytes) sz with
    | false => .none
    | true =>
      match sl with
      | .initialized (.pointer _) vr =>
        match decodeScalarBytes bytes false with
        | .none => .none
        | .some p =>
          let sv := p.1
          let prov := p.2
          match abstractBytesUniformProv bytes, prov with
          | true, .some ap =>
            .some (.ptr { allocId := ap.1, offsetBytes := sv.bits } sz)
          | _, _ =>
            match wrappingRangeContains vr sv.bits with
            | true => .some (.scalar sv)
            | false => .none
      | .initialized _ vr =>
        match policyRejectsProv policy bytes with
        | true => .none
        | false =>
          match decodeScalarBytes bytes false with
          | .none => .none
          | .some p =>
            let sv := p.1
            match wrappingRangeContains vr sv.bits with
            | false => .none
            | true =>
              match
                Bool.and
                  (Nat.beq sv.sizeBytes 4)
                  (Bool.and (Nat.beq vr.start 0) (Nat.beq vr.end_ 0x10FFFF))
              with
              | true =>
                match isValidCharCode sv.bits with
                | true => .some (.scalar sv)
                | false => .none
              | false => .some (.scalar sv)
      | .union (.pointer _) =>
        match decodeScalarBytes bytes false with
        | .none => .none
        | .some p =>
          let sv := p.1
          let prov := p.2
          match abstractBytesUniformProv bytes, prov with
          | true, .some ap =>
            .some (.ptr { allocId := ap.1, offsetBytes := sv.bits } sz)
          | _, _ => .some (.scalar sv)
      | .union _ =>
        match policyRejectsProv policy bytes with
        | true => .none
        | false =>
          match decodeScalarBytes bytes false with
          | .some p => .some (.scalar p.1)
          | .none => .none

/-- Policy-parameterized fuel-bounded layout- and type-aware byte decoder (exact
generalization of `Trusted.Rustc.V2026_06_01.MirSemantics.decodeTypedValueFromBytes`). -/
def decodeTypedValueFromBytesWithPolicy
    (policy : Ptr2IntTransmutePolicy) :
    Nat → LayoutTable → Ty → List AbstractByte → Option Value
  | .zero, _, _, _ => .none
  | .succ fuel', layouts, ty, bytes =>
    let rTy := normalizeCodecTy ty
    let decodeChild := fun (cTy : Ty) (bs : List AbstractByte) =>
      decodeTypedValueFromBytesWithPolicy policy fuel' layouts cTy bs
    match rTy.kind with
    | .array elemKind n =>
      match Nat.beq n 0 with
      | true =>
        match bytes with
        | .nil => .some (.aggregate 0 .nil)
        | _ :: _ => .none
      | false =>
        match LayoutTable.lookup layouts rTy.layoutIdx with
        | .some { fields := .array stride _, fieldLayouts := elemFlIdx :: _, .. } =>
          match Nat.beq (length bytes) (Nat.mul stride.bytes n) with
          | false => .none
          | true =>
            match
              decodeArrayChunksWith
                (decodeChild { kind := elemKind, layoutIdx := elemFlIdx })
                stride.bytes
                n
                bytes
            with
            | .some elems => .some (.aggregate 0 elems)
            | .none => .none
        | _ =>
          let elemSzOpt : Option Nat :=
            match rigidTyKindByteSize elemKind with
            | .some sz => .some sz
            | .none =>
              match LayoutTable.lookup layouts rTy.layoutIdx with
              | .some { fields := .array stride _, .. } => .some stride.bytes
              | _ =>
                match elemKind with
                | .tuple ks => tupleFieldsByteSize ks
                | _ => .none
          match elemSzOpt with
          | .none => .none
          | .some elemSz =>
            match Nat.beq (length bytes) (Nat.mul elemSz n) with
            | false => .none
            | true =>
              match
                decodeArrayChunksWith
                  (decodeChild { kind := elemKind, layoutIdx := 0 })
                  elemSz
                  n
                  bytes
              with
              | .some elems => .some (.aggregate 0 elems)
              | .none => .none
    | .tuple (kHead :: kTail) =>
      let ks := kHead :: kTail
      let decodeTypedKind := fun (k : RigidTy) (bs : List AbstractByte) =>
        decodeChild { kind := k, layoutIdx := 0 } bs
      let sizeOfKind := fun (k : RigidTy) =>
        rigidTyByteSize layouts { kind := k, layoutIdx := 0 }
      match LayoutTable.lookup layouts rTy.layoutIdx with
      | .some l =>
        match Nat.beq (length bytes) l.size.bytes, l.fields with
        | true, .arbitrary offsets _ =>
          match
            Bool.and
              (Nat.beq (length ks) (length offsets))
              (Nat.beq (length l.fieldLayouts) (length offsets))
          with
          | true =>
            match
              decodeTypedKindsAndLayoutsAtOffsets
                decodeChild
                layouts
                bytes
                offsets
                ks
                l.fieldLayouts
            with
            | .some vals => .some (.aggregate 0 vals)
            | .none => .none
          | false =>
            match
              decodeFieldsAtOffsetsWith
                decodeTypedKind
                sizeOfKind
                bytes
                offsets
                ks
            with
            | .some vals => .some (.aggregate 0 vals)
            | .none => .none
        | true, _ =>
          match decodeSeqFieldsWith decodeTypedKind sizeOfKind ks bytes with
          | .some vals => .some (.aggregate 0 vals)
          | .none => .none
        | false, _ => .none
      | .none =>
        match decodeSeqFieldsWith decodeTypedKind sizeOfKind ks bytes with
        | .some vals => .some (.aggregate 0 vals)
        | .none => .none
    | .adt _ _ =>
      match LayoutTable.lookup layouts rTy.layoutIdx with
      | .none => decodeValueFromBytes (.succ fuel') layouts rTy bytes
      | .some l =>
        match
          Bool.or
            l.isUninhabited
            (Bool.not (Nat.beq (length bytes) l.size.bytes))
        with
        | true => .none
        | false =>
          match l.variants with
          | .single variantIdx =>
            match l.fields with
            | .union count =>
              match variantIdx with
              | 0 => decodeUnionBytesWithCountOpt layouts rTy.layoutIdx count bytes
              | _ => decodeValueFromBytes (.succ fuel') layouts rTy bytes
            | .arbitrary .nil _ =>
              .some (.aggregate variantIdx .nil)
            | .arbitrary offsets _ =>
              match Nat.beq (length l.fieldLayouts) (length offsets) with
              | true =>
                match
                  decodeFieldsByLayoutIdxs
                    (fun fIdx fSlice =>
                      decodeChild { kind := .adt "" .nil, layoutIdx := fIdx } fSlice)
                    layouts
                    bytes
                    offsets
                    l.fieldLayouts
                with
                | .some vals => .some (.aggregate variantIdx vals)
                | .none => .none
              | false =>
                match offsets, l.backendRepr with
                | off0 :: .nil, .scalar s0 =>
                  match scalarLayoutByteWidth s0 with
                  | .none => .none
                  | .some sz0 =>
                    match sliceAbstractBytes bytes off0.bytes sz0 with
                    | .none => .none
                    | .some slice0 =>
                      match decodeScalarLayoutBytesWithPolicy policy s0 slice0 with
                      | .some v0 => .some (.aggregate variantIdx (v0 :: .nil))
                      | .none => .none
                | off0 :: off1 :: .nil, .scalarPair s0 s1 =>
                  match scalarLayoutByteWidth s0, scalarLayoutByteWidth s1 with
                  | .some sz0, .some sz1 =>
                    match
                      sliceAbstractBytes bytes off0.bytes sz0,
                      sliceAbstractBytes bytes off1.bytes sz1
                    with
                    | .some slice0, .some slice1 =>
                      match
                        decodeScalarLayoutBytesWithPolicy policy s0 slice0,
                        decodeScalarLayoutBytesWithPolicy policy s1 slice1
                      with
                      | .some v0, .some v1 =>
                        .some (.aggregate variantIdx (v0 :: v1 :: .nil))
                      | _, _ => .none
                    | _, _ => .none
                  | _, _ => .none
                | _, _ =>
                  match policyRejectsProv policy bytes with
                  | true => .none
                  | false =>
                    match decodeFieldsBySpan bytes l.size.bytes offsets with
                    | .some vals => .some (.aggregate variantIdx vals)
                    | .none => .none
            | .array stride count =>
              match Nat.beq count 0 with
              | true =>
                match bytes with
                | .nil => .some (.aggregate variantIdx .nil)
                | _ :: _ => .none
              | false =>
                match l.fieldLayouts with
                | elemFlIdx :: _ =>
                  match
                    decodeArrayChunksWith
                      (decodeChild { kind := .adt "" .nil, layoutIdx := elemFlIdx })
                      stride.bytes
                      count
                      bytes
                  with
                  | .some vals => .some (.aggregate variantIdx vals)
                  | .none => .none
                | .nil =>
                  match policyRejectsProv policy bytes with
                  | true => .none
                  | false => decodeValueFromBytes (.succ fuel') layouts rTy bytes
            | .primitive =>
              match Nat.beq l.size.bytes 0 with
              | true => .some .unit
              | false =>
                match l.backendRepr with
                | .scalar s0 => decodeScalarLayoutBytesWithPolicy policy s0 bytes
                | _ =>
                  match policyRejectsProv policy bytes with
                  | true => .none
                  | false =>
                    match decodeScalarBytes bytes false with
                    | .some p => .some (.scalar p.1)
                    | .none => .none
          | _ => decodeValueFromBytes (.succ fuel') layouts rTy bytes
    | .bool | .char | .int _ | .uint _ =>
      match policyRejectsProv policy bytes with
      | true => .none
      | false => decodeValueFromBytes (.succ fuel') layouts rTy bytes
    | .fnPtr _ _ _ _ =>
      decodePtrBytesNoForgeWithPolicy policy true (.tuple .nil) (layoutPointerBytes layouts) bytes
    | .rawPtr _ pointee =>
      decodePtrBytesNoForgeWithPolicy policy false pointee (layoutPointerBytes layouts) bytes
    | .ref _ pointee =>
      decodePtrBytesNoForgeWithPolicy policy true pointee (layoutPointerBytes layouts) bytes
    | _ => decodeValueFromBytes (.succ fuel') layouts rTy bytes

/-- Policy-parameterized MIR `CastKind.transmute` / `CastKind.subtype` evaluator
(exact generalization of `Trusted.Rustc.V2026_06_01.MirSemantics.evalByteCast`). -/
def evalByteCastWithPolicy
    (policy : Ptr2IntTransmutePolicy)
    (locals : List LocalSlot)
    (op : Operand)
    (targetTy : Ty)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    RvalueEvalResult :=
  match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
  | .ub => .ub
  | .unsupported => .unsupported
  | .ok v locals' =>
    let rTargetTy := resolveTyWithLocalDecls localDecls layouts targetTy
    match tyByteSize localDecls layouts rTargetTy with
    | .none => .unsupported
    | .some dstSize =>
      match operandTy localDecls layouts op with
      | .some srcTy =>
        let rSrcTy := resolveTyWithLocalDecls localDecls layouts srcTy
        match tyByteSize localDecls layouts rSrcTy with
        | .none => .unsupported
        | .some srcSize =>
          match Nat.beq srcSize dstSize with
          | false => .unsupported
          | true =>
            let encodedOpt : Option (List AbstractByte) :=
              encodeByteCastSourceBytes layouts rSrcTy v
            match encodedOpt with
            | .none => .ub
            | .some bs =>
              match Nat.beq (length bs) dstSize with
              | false => .ub
              | true =>
                match
                  decodeTypedValueFromBytesWithPolicy policy defaultCodecFuel layouts rTargetTy bs
                with
                | .some v' => .ok v' locals' mem
                | .none => .ub
      | .none =>
        match encodeUntypedValueToBytes defaultCodecFuel v with
        | .none => .unsupported
        | .some bs =>
          match Nat.beq (length bs) dstSize with
          | false => .unsupported
          | true =>
            match decodeTypedValueFromBytesWithPolicy policy defaultCodecFuel layouts rTargetTy bs with
            | .some v' => .ok v' locals' mem
            | .none => .ub

/-! ### §6.1 Exact TCB Correspondence at `.strictUcg630Ub` -/

theorem decodePtrBytesNoForgeWithPolicy_strict_eq
    (isRef : Bool) (pointee : RigidTy) (ptrBytes : Nat) (bytes : List AbstractByte) :
    decodePtrBytesNoForgeWithPolicy .strictUcg630Ub isRef pointee ptrBytes bytes =
      decodePtrBytesNoForge isRef pointee ptrBytes bytes := by
  unfold decodePtrBytesNoForgeWithPolicy decodePtrBytesNoForge policyRejectsProv
  dsimp only
  have hdata : ∀ bs,
      ((match Nat.beq (length bs) ptrBytes, decodeScalarBytes bs false with
       | true, .some p =>
         match abstractBytesUniformProv bs, p.2 with
         | true, .some ap => .some (.ptr { allocId := ap.1, offsetBytes := p.1.bits } ptrBytes)
         | _, _ => match isRef with | true => .none | false => .some (.scalar ⟨p.1.bits, ptrBytes⟩)
       | _, _ => .none) : Option Value) =
      (match Nat.beq (length bs) ptrBytes, decodeScalarBytes bs false with
       | true, .some (sv, prov) =>
         match abstractBytesUniformProv bs, prov with
         | true, .some (allocId, _) => .some (.ptr { allocId := allocId, offsetBytes := sv.bits } ptrBytes)
         | _, _ => match isRef with | true => .none | false => .some (.scalar ⟨sv.bits, ptrBytes⟩)
       | _, _ => .none) := by
    intro bs
    cases Nat.beq (length bs) ptrBytes with
    | false => rfl
    | true =>
      cases decodeScalarBytes bs false with
      | none => rfl
      | some p =>
        cases p with | mk sv prov =>
        dsimp only
        cases abstractBytesUniformProv bs with
        | false => rfl
        | true =>
          cases prov with
          | none => rfl
          | some ap => cases ap; rfl
  cases pointee with
  | slice _ | str =>
    dsimp only
    cases Nat.beq (length bytes) (Nat.add ptrBytes ptrBytes) with
    | false => rfl
    | true =>
      dsimp only
      rw [hdata (takeAbstractBytes ptrBytes bytes)]
      cases decodeScalarBytes (dropAbstractBytes ptrBytes bytes) false with
      | none => rfl
      | some mp =>
        cases mp with | mk msv mprov =>
        dsimp only
        cases abstractBytesHaveProv (dropAbstractBytes ptrBytes bytes) <;> rfl
  | dynamic _ =>
    dsimp only
    cases Nat.beq (length bytes) (Nat.add ptrBytes ptrBytes) with
    | false => rfl
    | true =>
      dsimp only
      rw [hdata (takeAbstractBytes ptrBytes bytes)]
      cases decodeScalarBytes (dropAbstractBytes ptrBytes bytes) false with
      | none => rfl
      | some mp =>
        cases mp with | mk msv mprov =>
        dsimp only
        cases abstractBytesUniformProv (dropAbstractBytes ptrBytes bytes) with
        | false => rfl
        | true =>
          cases mprov with
          | none => rfl
          | some vt => cases vt; rfl
  | _ => dsimp only; exact hdata bytes

theorem decodeScalarLayoutBytesWithPolicy_strict_eq
    (sl : ScalarLayout) (bytes : List AbstractByte) :
    decodeScalarLayoutBytesWithPolicy .strictUcg630Ub sl bytes =
      decodeScalarLayoutBytesNoForge sl bytes := by
  unfold decodeScalarLayoutBytesWithPolicy decodeScalarLayoutBytesNoForge policyRejectsProv
  dsimp only
  cases scalarLayoutByteWidth sl with
  | none => rfl
  | some sz =>
    dsimp only
    cases Nat.beq (length bytes) sz with
    | false => rfl
    | true =>
      dsimp only
      cases sl with
      | initialized pk vr =>
        cases pk with
        | pointer _ =>
          dsimp only
          cases decodeScalarBytes bytes false with
          | none => rfl
          | some p =>
            cases p with | mk sv prov =>
            dsimp only
            cases abstractBytesUniformProv bytes with
            | false => rfl
            | true =>
              cases prov with
              | none => rfl
              | some ap => cases ap; rfl
        | int _ _ | float _ =>
          dsimp only
          cases abstractBytesHaveProv bytes with
          | true => rfl
          | false =>
            dsimp only
            cases decodeScalarBytes bytes false with
            | none => rfl
            | some p => cases p; rfl
      | union pk =>
        cases pk with
        | pointer _ =>
          dsimp only
          cases decodeScalarBytes bytes false with
          | none => rfl
          | some p =>
            cases p with | mk sv prov =>
            dsimp only
            cases abstractBytesUniformProv bytes with
            | false => rfl
            | true =>
              cases prov with
              | none => rfl
              | some ap => cases ap; rfl
        | int _ _ | float _ =>
          dsimp only
          cases abstractBytesHaveProv bytes with
          | true => rfl
          | false =>
            dsimp only
            cases decodeScalarBytes bytes false with
            | none => rfl
            | some p => cases p; rfl

theorem decodeTypedValueFromBytesWithPolicy_strict_eq :
    ∀ (fuel : Nat) (layouts : LayoutTable) (ty : Ty) (bytes : List AbstractByte),
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel layouts ty bytes =
        decodeTypedValueFromBytes fuel layouts ty bytes
  | .zero, _, _, _ => rfl
  | .succ fuel', layouts, ty, bytes => by
    unfold decodeTypedValueFromBytesWithPolicy decodeTypedValueFromBytes
    dsimp only
    have hchild :
        decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel' layouts =
        decodeTypedValueFromBytes fuel' layouts :=
      funext fun cTy => funext fun bs =>
        decodeTypedValueFromBytesWithPolicy_strict_eq fuel' layouts cTy bs
    have hsl :
        decodeScalarLayoutBytesWithPolicy .strictUcg630Ub = decodeScalarLayoutBytesNoForge :=
      funext fun sl => funext fun bs => decodeScalarLayoutBytesWithPolicy_strict_eq sl bs
    have hptr :
        decodePtrBytesNoForgeWithPolicy .strictUcg630Ub = decodePtrBytesNoForge :=
      funext fun isRef => funext fun pointee => funext fun pb => funext fun bs =>
        decodePtrBytesNoForgeWithPolicy_strict_eq isRef pointee pb bs
    have hsc :
        ((match decodeScalarBytes bytes false with
         | .some p => .some (.scalar p.1)
         | .none => .none) : Option Value) =
        (match decodeScalarBytes bytes false with
         | .some (sv, _) => .some (.scalar sv)
         | .none => .none) := by
      cases decodeScalarBytes bytes false with
      | none => rfl
      | some p => cases p; rfl
    simp only [hchild, hsl, hptr, hsc, policyRejectsProv]
    cases (normalizeCodecTy ty).kind with
    | array _ n =>
      cases Nat.beq n 0 with
      | true => rfl
      | false =>
        cases LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
        | none => rfl
        | some l => cases l; rfl
    | tuple ks =>
      cases ks with
      | nil => rfl
      | cons _ _ =>
        cases LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
        | none => rfl
        | some l =>
          cases Nat.beq (length bytes) l.size.bytes with
          | false => rfl
          | true => cases l.fields <;> rfl
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
          | multiple _ _ _ => rfl
          | single variantIdx =>
            dsimp only
            cases variantIdx with
            | zero =>
              cases l.fields with
              | union _ => rfl
              | arbitrary offsets _ => cases offsets <;> rfl
              | array _ _ => rfl
              | primitive => rfl
            | succ _ =>
              cases l.fields with
              | union _ => rfl
              | arbitrary offsets _ => cases offsets <;> rfl
              | array _ _ => rfl
              | primitive => rfl
    | _ => rfl

theorem evalByteCastWithPolicy_strict_eq
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalByteCastWithPolicy .strictUcg630Ub locals op targetTy mem localDecls layouts =
      evalByteCast locals op targetTy mem localDecls layouts := by
  unfold evalByteCastWithPolicy evalByteCast
  have hdec : decodeTypedValueFromBytesWithPolicy .strictUcg630Ub defaultCodecFuel layouts =
      decodeTypedValueFromBytes defaultCodecFuel layouts :=
    funext fun ty => funext fun bs =>
      decodeTypedValueFromBytesWithPolicy_strict_eq defaultCodecFuel layouts ty bs
  simp only [hdec]
  cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
  | ub => rfl
  | unsupported => rfl
  | ok v locals' =>
    cases tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts targetTy) with
    | none => rfl
    | some dstSize =>
      cases operandTy localDecls layouts op with
      | none => rfl
      | some srcTy => rfl

/-! ### §6.2 Exact Policy Refinement / Monotonicity (`.strictUcg630Ub → .stripProvenance`) -/

theorem decodePtrBytesNoForgeWithPolicy_strict_refines_strip
    (isRef : Bool) (pointee : RigidTy) (ptrBytes : Nat) (bytes : List AbstractByte) (v : Value)
    (h : decodePtrBytesNoForgeWithPolicy .strictUcg630Ub isRef pointee ptrBytes bytes = .some v) :
    decodePtrBytesNoForgeWithPolicy .stripProvenance isRef pointee ptrBytes bytes = .some v := by
  unfold decodePtrBytesNoForgeWithPolicy policyRejectsProv at h ⊢
  dsimp only at h ⊢
  cases pointee with
  | slice _ | str =>
    dsimp only at h ⊢
    cases hlen : Nat.beq (length bytes) (Nat.add ptrBytes ptrBytes) with
    | false => rw [hlen] at h; cases h
    | true =>
      rw [hlen] at h; dsimp only at h ⊢
      have hnone : ∀ (x : Option Value),
          ((match x, (Option.none : Option Value) with
            | .some d, .some m => Option.some (Value.aggregate 0 [d, m])
            | _, _ => Option.none) : Option Value) = Option.none := by
        intro x; cases x <;> rfl
      cases hdec : decodeScalarBytes (dropAbstractBytes ptrBytes bytes) false with
      | none =>
        rw [hdec] at h; dsimp only at h
        rw [hnone] at h; cases h
      | some mp =>
        rw [hdec] at h; dsimp only at h ⊢
        cases hprov : abstractBytesHaveProv (dropAbstractBytes ptrBytes bytes) with
        | false => rw [hprov] at h; exact h
        | true =>
          rw [hprov] at h; dsimp only at h
          rw [hnone] at h; cases h
  | dynamic _ =>
    dsimp only at h ⊢
    cases hlen : Nat.beq (length bytes) (Nat.add ptrBytes ptrBytes) with
    | false => rw [hlen] at h; cases h
    | true =>
      rw [hlen] at h; dsimp only at h ⊢
      cases hdec : decodeScalarBytes (dropAbstractBytes ptrBytes bytes) false with
      | none => rw [hdec] at h; exact h
      | some mp =>
        rw [hdec] at h; dsimp only at h ⊢
        cases hu : abstractBytesUniformProv (dropAbstractBytes ptrBytes bytes) with
        | false => rw [hu] at h; exact h
        | true =>
          rw [hu] at h
          cases hm : mp.2 with
          | none => rw [hm] at h; exact h
          | some _ => rw [hm] at h; exact h
  | _ => exact h

theorem decodeScalarLayoutBytesWithPolicy_strict_refines_strip
    (sl : ScalarLayout) (bytes : List AbstractByte) (v : Value)
    (h : decodeScalarLayoutBytesWithPolicy .strictUcg630Ub sl bytes = .some v) :
    decodeScalarLayoutBytesWithPolicy .stripProvenance sl bytes = .some v := by
  unfold decodeScalarLayoutBytesWithPolicy policyRejectsProv at h ⊢
  dsimp only at h ⊢
  cases hw : scalarLayoutByteWidth sl with
  | none => rw [hw] at h; cases h
  | some sz =>
    rw [hw] at h; dsimp only at h ⊢
    cases hlen : Nat.beq (length bytes) sz with
    | false => rw [hlen] at h; cases h
    | true =>
      rw [hlen] at h; dsimp only at h ⊢
      cases sl with
      | initialized pk vr =>
        cases pk with
        | pointer _ => exact h
        | int _ _ | float _ =>
          dsimp only at h ⊢
          cases hp : abstractBytesHaveProv bytes with
          | false => rw [hp] at h; exact h
          | true => rw [hp] at h; cases h
      | union pk =>
        cases pk with
        | pointer _ => exact h
        | int _ _ | float _ =>
          dsimp only at h ⊢
          cases hp : abstractBytesHaveProv bytes with
          | false => rw [hp] at h; exact h
          | true => rw [hp] at h; cases h

private theorem decodeArrayChunksWith_mono
    (f₁ f₂ : List AbstractByte → Option Value) (elemSz : Nat)
    (hf : ∀ bs v, f₁ bs = .some v → f₂ bs = .some v) :
    ∀ n bs vs, decodeArrayChunksWith f₁ elemSz n bs = .some vs →
      decodeArrayChunksWith f₂ elemSz n bs = .some vs
  | .zero, .nil, _, h => h
  | .zero, _ :: _, _, h => by cases h
  | .succ k, bs, vs, h => by
    unfold decodeArrayChunksWith at h ⊢
    cases hle : Nat.ble elemSz (length bs) with
    | false => rw [hle] at h; cases h
    | true =>
      rw [hle] at h; dsimp only at h ⊢
      cases h1 : f₁ (takeAbstractBytes elemSz bs) with
      | none => rw [h1] at h; cases h
      | some v =>
        rw [h1] at h; dsimp only at h ⊢
        rw [hf _ v h1]; dsimp only
        cases h2 : decodeArrayChunksWith f₁ elemSz k (dropAbstractBytes elemSz bs) with
        | none => rw [h2] at h; cases h
        | some rest =>
          rw [h2] at h; dsimp only at h ⊢
          rw [decodeArrayChunksWith_mono f₁ f₂ elemSz hf k _ rest h2]
          exact h

private theorem decodeTypedKindsAndLayoutsAtOffsets_mono
    (f₁ f₂ : Ty → List AbstractByte → Option Value)
    (layouts : LayoutTable) (bytes : List AbstractByte)
    (hf : ∀ ty bs v, f₁ ty bs = .some v → f₂ ty bs = .some v) :
    ∀ offs ks fls vs,
      decodeTypedKindsAndLayoutsAtOffsets f₁ layouts bytes offs ks fls = .some vs →
      decodeTypedKindsAndLayoutsAtOffsets f₂ layouts bytes offs ks fls = .some vs
  | .nil, .nil, .nil, _, h => h
  | off :: offRest, k :: kRest, fIdx :: fRest, vs, h => by
    unfold decodeTypedKindsAndLayoutsAtOffsets at h ⊢
    cases hlk : LayoutTable.lookup layouts fIdx with
    | none => rw [hlk] at h; cases h
    | some fl =>
      rw [hlk] at h; dsimp only at h ⊢
      cases hsl : sliceAbstractBytes bytes off.bytes fl.size.bytes with
      | none => rw [hsl] at h; cases h
      | some fSlice =>
        rw [hsl] at h; dsimp only at h ⊢
        cases h1 : f₁ { kind := k, layoutIdx := fIdx } fSlice with
        | none => rw [h1] at h; cases h
        | some v =>
          rw [h1] at h; dsimp only at h ⊢
          rw [hf _ _ v h1]; dsimp only
          cases h2 : decodeTypedKindsAndLayoutsAtOffsets f₁ layouts bytes offRest kRest fRest with
          | none => rw [h2] at h; cases h
          | some rest =>
            rw [h2] at h; dsimp only at h ⊢
            rw [decodeTypedKindsAndLayoutsAtOffsets_mono f₁ f₂ layouts bytes hf offRest kRest fRest rest h2]
            exact h
  | .nil, _ :: _, _, _, h => by cases h
  | .nil, .nil, _ :: _, _, h => by cases h
  | _ :: _, .nil, _, _, h => by cases h
  | _ :: _, _ :: _, .nil, _, h => by cases h

private theorem decodeFieldsAtOffsetsWith_mono
    (f₁ f₂ : RigidTy → List AbstractByte → Option Value)
    (sizeOfKind : RigidTy → Option Nat) (bytes : List AbstractByte)
    (hf : ∀ k bs v, f₁ k bs = .some v → f₂ k bs = .some v) :
    ∀ offs ks vs,
      decodeFieldsAtOffsetsWith f₁ sizeOfKind bytes offs ks = .some vs →
      decodeFieldsAtOffsetsWith f₂ sizeOfKind bytes offs ks = .some vs
  | .nil, .nil, _, h => h
  | .nil, _ :: _, _, h => by cases h
  | _ :: _, .nil, _, h => by cases h
  | off :: offRest, k :: kRest, vs, h => by
    unfold decodeFieldsAtOffsetsWith at h ⊢
    cases hsz : sizeOfKind k with
    | none => rw [hsz] at h; cases h
    | some fSize =>
      rw [hsz] at h; dsimp only at h ⊢
      cases hsl : sliceAbstractBytes bytes off.bytes fSize with
      | none => rw [hsl] at h; cases h
      | some fSlice =>
        rw [hsl] at h; dsimp only at h ⊢
        cases h1 : f₁ k fSlice with
        | none => rw [h1] at h; cases h
        | some v =>
          rw [h1] at h; dsimp only at h ⊢
          rw [hf k fSlice v h1]; dsimp only
          cases h2 : decodeFieldsAtOffsetsWith f₁ sizeOfKind bytes offRest kRest with
          | none => rw [h2] at h; cases h
          | some rest =>
            rw [h2] at h; dsimp only at h ⊢
            rw [decodeFieldsAtOffsetsWith_mono f₁ f₂ sizeOfKind bytes hf offRest kRest rest h2]
            exact h

private theorem decodeSeqFieldsWith_mono
    (f₁ f₂ : RigidTy → List AbstractByte → Option Value)
    (sizeOfKind : RigidTy → Option Nat)
    (hf : ∀ k bs v, f₁ k bs = .some v → f₂ k bs = .some v) :
    ∀ ks bs vs,
      decodeSeqFieldsWith f₁ sizeOfKind ks bs = .some vs →
      decodeSeqFieldsWith f₂ sizeOfKind ks bs = .some vs
  | .nil, .nil, _, h => h
  | .nil, _ :: _, _, h => by cases h
  | k :: kRest, bs, vs, h => by
    unfold decodeSeqFieldsWith at h ⊢
    cases hsz : sizeOfKind k with
    | none => rw [hsz] at h; cases h
    | some fSize =>
      rw [hsz] at h; dsimp only at h ⊢
      cases hle : Nat.ble fSize (length bs) with
      | false => rw [hle] at h; cases h
      | true =>
        rw [hle] at h; dsimp only at h ⊢
        cases h1 : f₁ k (takeAbstractBytes fSize bs) with
        | none => rw [h1] at h; cases h
        | some v =>
          rw [h1] at h; dsimp only at h ⊢
          rw [hf k _ v h1]; dsimp only
          cases h2 : decodeSeqFieldsWith f₁ sizeOfKind kRest (dropAbstractBytes fSize bs) with
          | none => rw [h2] at h; cases h
          | some rest =>
            rw [h2] at h; dsimp only at h ⊢
            rw [decodeSeqFieldsWith_mono f₁ f₂ sizeOfKind hf kRest _ rest h2]
            exact h

private theorem decodeFieldsByLayoutIdxs_mono
    (f₁ f₂ : Nat → List AbstractByte → Option Value)
    (layouts : LayoutTable) (bytes : List AbstractByte)
    (hf : ∀ fIdx bs v, f₁ fIdx bs = .some v → f₂ fIdx bs = .some v) :
    ∀ offs fls vs,
      decodeFieldsByLayoutIdxs f₁ layouts bytes offs fls = .some vs →
      decodeFieldsByLayoutIdxs f₂ layouts bytes offs fls = .some vs
  | .nil, .nil, _, h => h
  | .nil, _ :: _, _, h => by cases h
  | _ :: _, .nil, _, h => by cases h
  | off :: offRest, fIdx :: fRest, vs, h => by
    unfold decodeFieldsByLayoutIdxs at h ⊢
    cases hlk : LayoutTable.lookup layouts fIdx with
    | none => rw [hlk] at h; cases h
    | some fl =>
      rw [hlk] at h; dsimp only at h ⊢
      cases hsl : sliceAbstractBytes bytes off.bytes fl.size.bytes with
      | none => rw [hsl] at h; cases h
      | some fSlice =>
        rw [hsl] at h; dsimp only at h ⊢
        cases h1 : f₁ fIdx fSlice with
        | none => rw [h1] at h; cases h
        | some v =>
          rw [h1] at h; dsimp only at h ⊢
          rw [hf fIdx fSlice v h1]; dsimp only
          cases h2 : decodeFieldsByLayoutIdxs f₁ layouts bytes offRest fRest with
          | none => rw [h2] at h; cases h
          | some rest =>
            rw [h2] at h; dsimp only at h ⊢
            rw [decodeFieldsByLayoutIdxs_mono f₁ f₂ layouts bytes hf offRest fRest rest h2]
            exact h

private theorem arrayFallbackElemSize_mono
    (f₁ f₂ : List AbstractByte → Option Value)
    (hf : ∀ bs v, f₁ bs = .some v → f₂ bs = .some v)
    (elemSzOpt : Option Nat) (n : Nat) (bytes : List AbstractByte) (v : Value) :
    ((match elemSzOpt with
      | .none => .none
      | .some elemSz =>
        match Nat.beq (length bytes) (Nat.mul elemSz n) with
        | false => .none
        | true =>
          match decodeArrayChunksWith f₁ elemSz n bytes with
          | .some elems => .some (.aggregate 0 elems)
          | .none => .none) : Option Value) = .some v →
    ((match elemSzOpt with
      | .none => .none
      | .some elemSz =>
        match Nat.beq (length bytes) (Nat.mul elemSz n) with
        | false => .none
        | true =>
          match decodeArrayChunksWith f₂ elemSz n bytes with
          | .some elems => .some (.aggregate 0 elems)
          | .none => .none) : Option Value) = .some v := by
  intro h
  cases elemSzOpt with
  | none => cases h
  | some elemSz =>
    dsimp only at h ⊢
    cases hlen : Nat.beq (length bytes) (Nat.mul elemSz n) with
    | false => rw [hlen] at h; cases h
    | true =>
      rw [hlen] at h; dsimp only at h ⊢
      cases hch : decodeArrayChunksWith f₁ elemSz n bytes with
      | none => rw [hch] at h; cases h
      | some elems =>
        rw [hch] at h
        rw [decodeArrayChunksWith_mono f₁ f₂ elemSz hf n bytes elems hch]
        exact h

/-- Structural policy refinement: every successful decode under `.strictUcg630Ub`
succeeds with the exact same `Value` under `.stripProvenance`. -/
theorem decodeTypedValueFromBytesWithPolicy_strict_refines_strip :
    ∀ (fuel : Nat) (layouts : LayoutTable) (ty : Ty) (bytes : List AbstractByte) (v : Value),
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel layouts ty bytes = .some v →
      decodeTypedValueFromBytesWithPolicy .stripProvenance fuel layouts ty bytes = .some v
  | .zero, _, _, _, _, h => by cases h
  | .succ fuel', layouts, ty, bytes, v, h => by
    unfold decodeTypedValueFromBytesWithPolicy at h ⊢
    dsimp only at h ⊢
    have ih : ∀ cTy bs cv,
        decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel' layouts cTy bs = .some cv →
        decodeTypedValueFromBytesWithPolicy .stripProvenance fuel' layouts cTy bs = .some cv :=
      fun cTy bs cv hcv =>
        decodeTypedValueFromBytesWithPolicy_strict_refines_strip fuel' layouts cTy bs cv hcv
    cases hk : (normalizeCodecTy ty).kind with
    | array elemKind n =>
      rw [hk] at h; dsimp only at h ⊢
      cases h0 : Nat.beq n 0 with
      | true => rw [h0] at h; exact h
      | false =>
        rw [h0] at h; dsimp only at h ⊢
        cases hlk : LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
        | none =>
          rw [hlk] at h; dsimp only at h ⊢
          exact arrayFallbackElemSize_mono _ _ (fun bs cv hc => ih _ bs cv hc) _ n bytes v h
        | some l =>
          cases l with
          | mk lsz lal lbr lfld lvar lunin lfls =>
            rw [hlk] at h
            cases lfld with
            | array stride cnt =>
              cases lfls with
              | cons elemFlIdx flRest =>
                dsimp only at h ⊢
                cases hlen : Nat.beq (length bytes) (Nat.mul stride.bytes n) with
                | false => rw [hlen] at h; cases h
                | true =>
                  rw [hlen] at h; dsimp only at h ⊢
                  cases hch : decodeArrayChunksWith
                      (fun bs => decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel' layouts
                        { kind := elemKind, layoutIdx := elemFlIdx } bs) stride.bytes n bytes with
                  | none => rw [hch] at h; cases h
                  | some elems =>
                    rw [hch] at h
                    rw [decodeArrayChunksWith_mono _ _ _ (fun bs cv hc => ih _ bs cv hc) _ _ elems hch]
                    exact h
              | nil =>
                dsimp only at h ⊢
                exact arrayFallbackElemSize_mono _ _ (fun bs cv hc => ih _ bs cv hc) _ n bytes v h
            | _ =>
              dsimp only at h ⊢
              exact arrayFallbackElemSize_mono _ _ (fun bs cv hc => ih _ bs cv hc) _ n bytes v h
    | tuple ks =>
      rw [hk] at h
      cases ks with
      | nil => exact h
      | cons kHead kTail =>
        dsimp only at h ⊢
        cases hlk : LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
        | none =>
          rw [hlk] at h; dsimp only at h ⊢
          cases hseq : decodeSeqFieldsWith
              (fun k bs => decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel' layouts
                { kind := k, layoutIdx := 0 } bs)
              (fun k => rigidTyByteSize layouts { kind := k, layoutIdx := 0 })
              (kHead :: kTail) bytes with
          | none => rw [hseq] at h; cases h
          | some vals =>
            rw [hseq] at h
            rw [decodeSeqFieldsWith_mono _ _ _ (fun k bs cv hc => ih _ bs cv hc) _ _ vals hseq]
            exact h
        | some l =>
          rw [hlk] at h; dsimp only at h ⊢
          cases hlen : Nat.beq (length bytes) l.size.bytes with
          | false => rw [hlen] at h; cases h
          | true =>
            rw [hlen] at h
            cases hlf : l.fields with
            | arbitrary offsets _ =>
              rw [hlf] at h; dsimp only at h ⊢
              cases hboth : Bool.and (Nat.beq (length (kHead :: kTail)) (length offsets))
                  (Nat.beq (length l.fieldLayouts) (length offsets)) with
              | false =>
                rw [hboth] at h; dsimp only at h ⊢
                cases hdec : decodeFieldsAtOffsetsWith
                    (fun k bs => decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel' layouts
                      { kind := k, layoutIdx := 0 } bs)
                    (fun k => rigidTyByteSize layouts { kind := k, layoutIdx := 0 })
                    bytes offsets (kHead :: kTail) with
                | none => rw [hdec] at h; cases h
                | some vals =>
                  rw [hdec] at h
                  rw [decodeFieldsAtOffsetsWith_mono _ _ _ _ (fun k bs cv hc => ih _ bs cv hc) _ _ vals hdec]
                  exact h
              | true =>
                rw [hboth] at h; dsimp only at h ⊢
                cases hdec : decodeTypedKindsAndLayoutsAtOffsets
                    (fun cTy bs => decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel' layouts cTy bs)
                    layouts bytes offsets (kHead :: kTail) l.fieldLayouts with
                | none => rw [hdec] at h; cases h
                | some vals =>
                  rw [hdec] at h
                  rw [decodeTypedKindsAndLayoutsAtOffsets_mono _ _ _ _ ih _ _ _ vals hdec]
                  exact h
            | _ =>
              rw [hlf] at h; dsimp only at h ⊢
              cases hseq : decodeSeqFieldsWith
                  (fun k bs => decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel' layouts
                    { kind := k, layoutIdx := 0 } bs)
                  (fun k => rigidTyByteSize layouts { kind := k, layoutIdx := 0 })
                  (kHead :: kTail) bytes with
              | none => rw [hseq] at h; cases h
              | some vals =>
                rw [hseq] at h
                rw [decodeSeqFieldsWith_mono _ _ _ (fun k bs cv hc => ih _ bs cv hc) _ _ vals hseq]
                exact h
    | adt defPath args =>
      rw [hk] at h; dsimp only at h ⊢
      cases hlk : LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
      | none => rw [hlk] at h; exact h
      | some l =>
        rw [hlk] at h; dsimp only at h ⊢
        cases hbad : Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
        | true => rw [hbad] at h; cases h
        | false =>
          rw [hbad] at h; dsimp only at h ⊢
          cases hvar : l.variants with
          | empty => rw [hvar] at h; exact h
          | multiple _ _ _ => rw [hvar] at h; exact h
          | single variantIdx =>
            rw [hvar] at h; dsimp only at h ⊢
            cases hlf : l.fields with
            | union count => rw [hlf] at h; cases variantIdx <;> exact h
            | arbitrary offsets _ =>
              rw [hlf] at h
              cases offsets with
              | nil => exact h
              | cons off0 offRest =>
                dsimp only at h ⊢
                cases hfls : Nat.beq (length l.fieldLayouts) (length (off0 :: offRest)) with
                | true =>
                  rw [hfls] at h; dsimp only at h ⊢
                  cases hdec : decodeFieldsByLayoutIdxs
                      (fun fIdx fSlice => decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel' layouts
                        { kind := .adt "" .nil, layoutIdx := fIdx } fSlice)
                      layouts bytes (off0 :: offRest) l.fieldLayouts with
                  | none => rw [hdec] at h; cases h
                  | some vals =>
                    rw [hdec] at h
                    rw [decodeFieldsByLayoutIdxs_mono _ _ _ _ (fun fIdx bs cv hc => ih _ bs cv hc) _ _ vals hdec]
                    exact h
                | false =>
                  rw [hfls] at h; dsimp only at h ⊢
                  cases offRest with
                  | nil =>
                    cases hbr : l.backendRepr with
                    | scalar s0 =>
                      rw [hbr] at h; dsimp only at h ⊢
                      cases hsw : scalarLayoutByteWidth s0 with
                      | none => rw [hsw] at h; cases h
                      | some sz0 =>
                        rw [hsw] at h; dsimp only at h ⊢
                        cases hsl : sliceAbstractBytes bytes off0.bytes sz0 with
                        | none => rw [hsl] at h; cases h
                        | some slice0 =>
                          rw [hsl] at h; dsimp only at h ⊢
                          cases hds : decodeScalarLayoutBytesWithPolicy .strictUcg630Ub s0 slice0 with
                          | none => rw [hds] at h; cases h
                          | some v0 =>
                            rw [hds] at h
                            rw [decodeScalarLayoutBytesWithPolicy_strict_refines_strip s0 slice0 v0 hds]
                            exact h
                    | _ =>
                      rw [hbr] at h; dsimp only [policyRejectsProv] at h ⊢
                      cases hp : abstractBytesHaveProv bytes with
                      | false => rw [hp] at h; exact h
                      | true => rw [hp] at h; cases h
                  | cons off1 offRest2 =>
                    cases offRest2 with
                    | nil =>
                      cases hbr : l.backendRepr with
                      | scalarPair s0 s1 =>
                        rw [hbr] at h; dsimp only at h ⊢
                        cases hsw0 : scalarLayoutByteWidth s0 with
                        | none => rw [hsw0] at h; cases h
                        | some sz0 =>
                          rw [hsw0] at h
                          cases hsw1 : scalarLayoutByteWidth s1 with
                          | none => rw [hsw1] at h; cases h
                          | some sz1 =>
                            rw [hsw1] at h; dsimp only at h ⊢
                            cases hsl0 : sliceAbstractBytes bytes off0.bytes sz0 with
                            | none => rw [hsl0] at h; cases h
                            | some slice0 =>
                              rw [hsl0] at h
                              cases hsl1 : sliceAbstractBytes bytes off1.bytes sz1 with
                              | none => rw [hsl1] at h; cases h
                              | some slice1 =>
                                rw [hsl1] at h; dsimp only at h ⊢
                                cases hds0 : decodeScalarLayoutBytesWithPolicy .strictUcg630Ub s0 slice0 with
                                | none => rw [hds0] at h; cases h
                                | some v0 =>
                                  rw [hds0] at h
                                  cases hds1 : decodeScalarLayoutBytesWithPolicy .strictUcg630Ub s1 slice1 with
                                  | none => rw [hds1] at h; cases h
                                  | some v1 =>
                                    rw [hds1] at h
                                    rw [decodeScalarLayoutBytesWithPolicy_strict_refines_strip s0 slice0 v0 hds0,
                                        decodeScalarLayoutBytesWithPolicy_strict_refines_strip s1 slice1 v1 hds1]
                                    exact h
                      | _ =>
                        rw [hbr] at h; dsimp only [policyRejectsProv] at h ⊢
                        cases hp : abstractBytesHaveProv bytes with
                        | false => rw [hp] at h; exact h
                        | true => rw [hp] at h; cases h
                    | cons _ _ =>
                      dsimp only [policyRejectsProv] at h ⊢
                      cases hp : abstractBytesHaveProv bytes with
                      | false => rw [hp] at h; exact h
                      | true => rw [hp] at h; cases h
            | array stride count =>
              rw [hlf] at h; dsimp only at h ⊢
              cases hc0 : Nat.beq count 0 with
              | true => rw [hc0] at h; exact h
              | false =>
                rw [hc0] at h; dsimp only at h ⊢
                cases hfl : l.fieldLayouts with
                | cons elemFlIdx _ =>
                  rw [hfl] at h; dsimp only at h ⊢
                  cases hch : decodeArrayChunksWith
                      (fun bs => decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel' layouts
                        { kind := .adt "" .nil, layoutIdx := elemFlIdx } bs) stride.bytes count bytes with
                  | none => rw [hch] at h; cases h
                  | some vals =>
                    rw [hch] at h
                    rw [decodeArrayChunksWith_mono _ _ _ (fun bs cv hc => ih _ bs cv hc) _ _ vals hch]
                    exact h
                | nil =>
                  rw [hfl] at h; dsimp only [policyRejectsProv] at h ⊢
                  cases hp : abstractBytesHaveProv bytes with
                  | false => rw [hp] at h; exact h
                  | true => rw [hp] at h; cases h
            | primitive =>
              rw [hlf] at h; dsimp only at h ⊢
              cases hs0 : Nat.beq l.size.bytes 0 with
              | true => rw [hs0] at h; exact h
              | false =>
                rw [hs0] at h; dsimp only at h ⊢
                cases hbr : l.backendRepr with
                | scalar s0 =>
                  rw [hbr] at h
                  exact decodeScalarLayoutBytesWithPolicy_strict_refines_strip s0 bytes v h
                | _ =>
                  rw [hbr] at h; dsimp only [policyRejectsProv] at h ⊢
                  cases hp : abstractBytesHaveProv bytes with
                  | false => rw [hp] at h; exact h
                  | true => rw [hp] at h; cases h
    | bool | char | int _ | uint _ =>
      rw [hk] at h; dsimp only [policyRejectsProv] at h ⊢
      cases hp : abstractBytesHaveProv bytes with
      | false => rw [hp] at h; exact h
      | true => rw [hp] at h; cases h
    | fnPtr _ _ _ _ =>
      rw [hk] at h
      exact decodePtrBytesNoForgeWithPolicy_strict_refines_strip true (.tuple .nil) _ bytes v h
    | rawPtr _ pointee =>
      rw [hk] at h
      exact decodePtrBytesNoForgeWithPolicy_strict_refines_strip false pointee _ bytes v h
    | ref _ pointee =>
      rw [hk] at h
      exact decodePtrBytesNoForgeWithPolicy_strict_refines_strip true pointee _ bytes v h
    | _ => rw [hk] at h; exact h

/-- Top-level `evalByteCastWithPolicy` refinement: every `.ok` result under
`.strictUcg630Ub` succeeds identically under `.stripProvenance`. -/
theorem evalByteCastWithPolicy_strict_refines_strip
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (v : Value) (locals' : List LocalSlot)
    (h : evalByteCastWithPolicy .strictUcg630Ub locals op targetTy mem localDecls layouts =
      .ok v locals' mem) :
    evalByteCastWithPolicy .stripProvenance locals op targetTy mem localDecls layouts =
      .ok v locals' mem := by
  unfold evalByteCastWithPolicy at h ⊢
  cases hev : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
  | ub => rw [hev] at h; cases h
  | unsupported => rw [hev] at h; cases h
  | ok srcVal loc1 =>
    rw [hev] at h; dsimp only at h ⊢
    cases hdsz : tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts targetTy) with
    | none => rw [hdsz] at h; cases h
    | some dstSize =>
      rw [hdsz] at h; dsimp only at h ⊢
      cases hsty : operandTy localDecls layouts op with
      | some srcTy =>
        rw [hsty] at h; dsimp only at h ⊢
        cases hssz : tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts srcTy) with
        | none => rw [hssz] at h; cases h
        | some srcSize =>
          rw [hssz] at h; dsimp only at h ⊢
          cases hbeq : Nat.beq srcSize dstSize with
          | false => rw [hbeq] at h; cases h
          | true =>
            rw [hbeq] at h; dsimp only at h ⊢
            cases henc : encodeByteCastSourceBytes layouts (resolveTyWithLocalDecls localDecls layouts srcTy) srcVal with
            | none => rw [henc] at h; cases h
            | some bs =>
              rw [henc] at h; dsimp only at h ⊢
              cases hblen : Nat.beq (length bs) dstSize with
              | false => rw [hblen] at h; cases h
              | true =>
                rw [hblen] at h; dsimp only at h ⊢
                cases hdec : decodeTypedValueFromBytesWithPolicy .strictUcg630Ub defaultCodecFuel layouts
                    (resolveTyWithLocalDecls localDecls layouts targetTy) bs with
                | none => rw [hdec] at h; cases h
                | some v' =>
                  rw [hdec] at h
                  rw [decodeTypedValueFromBytesWithPolicy_strict_refines_strip _ _ _ _ v' hdec]
                  exact h
      | none =>
        rw [hsty] at h; dsimp only at h ⊢
        cases henc : encodeUntypedValueToBytes defaultCodecFuel srcVal with
        | none => rw [henc] at h; cases h
        | some bs =>
          rw [henc] at h; dsimp only at h ⊢
          cases hblen : Nat.beq (length bs) dstSize with
          | false => rw [hblen] at h; cases h
          | true =>
            rw [hblen] at h; dsimp only at h ⊢
            cases hdec : decodeTypedValueFromBytesWithPolicy .strictUcg630Ub defaultCodecFuel layouts
                (resolveTyWithLocalDecls localDecls layouts targetTy) bs with
            | none => rw [hdec] at h; cases h
            | some v' =>
              rw [hdec] at h
              rw [decodeTypedValueFromBytesWithPolicy_strict_refines_strip _ _ _ _ v' hdec]
              exact h

/-! ### §6.3 Provenance-Free Equivalence (`stripProvenance_eq_strict_of_no_prov`) -/

theorem abstractBytesHaveProv_take :
    ∀ (n : Nat) (bs : List AbstractByte),
      abstractBytesHaveProv bs = false → abstractBytesHaveProv (takeAbstractBytes n bs) = false
  | .zero, _, _ => rfl
  | .succ _, .nil, _ => rfl
  | .succ k, .uninit :: rest, h => abstractBytesHaveProv_take k rest h
  | .succ k, .init _ .none :: rest, h => abstractBytesHaveProv_take k rest h
  | .succ _, .init _ (.some _) :: _, h => by cases h

theorem abstractBytesHaveProv_drop :
    ∀ (n : Nat) (bs : List AbstractByte),
      abstractBytesHaveProv bs = false → abstractBytesHaveProv (dropAbstractBytes n bs) = false
  | .zero, _, h => h
  | .succ _, .nil, _ => rfl
  | .succ k, .uninit :: rest, h => abstractBytesHaveProv_drop k rest h
  | .succ k, .init _ .none :: rest, h => abstractBytesHaveProv_drop k rest h
  | .succ _, .init _ (.some _) :: _, h => by cases h

theorem abstractBytesHaveProv_slice (bs s : List AbstractByte) (off len : Nat)
    (hnp : abstractBytesHaveProv bs = false)
    (hsl : sliceAbstractBytes bs off len = .some s) :
    abstractBytesHaveProv s = false := by
  unfold sliceAbstractBytes at hsl
  cases hle : Nat.ble (Nat.add off len) (length bs) with
  | false => rw [hle] at hsl; cases hsl
  | true =>
    rw [hle] at hsl; dsimp only at hsl
    injection hsl with hs
    rw [← hs]
    exact abstractBytesHaveProv_take len _ (abstractBytesHaveProv_drop off bs hnp)

theorem decodePtrBytesNoForgeWithPolicy_strip_eq_strict_of_no_prov
    (isRef : Bool) (pointee : RigidTy) (ptrBytes : Nat) (bytes : List AbstractByte)
    (hnp : abstractBytesHaveProv bytes = false) :
    decodePtrBytesNoForgeWithPolicy .stripProvenance isRef pointee ptrBytes bytes =
      decodePtrBytesNoForgeWithPolicy .strictUcg630Ub isRef pointee ptrBytes bytes := by
  unfold decodePtrBytesNoForgeWithPolicy policyRejectsProv
  dsimp only
  cases pointee with
  | slice _ | str | dynamic _ =>
    dsimp only
    cases Nat.beq (length bytes) (Nat.add ptrBytes ptrBytes) with
    | false => rfl
    | true =>
      dsimp only
      have hdrop := abstractBytesHaveProv_drop ptrBytes bytes hnp
      simp only [hdrop]
  | _ => rfl

theorem decodeScalarLayoutBytesWithPolicy_strip_eq_strict_of_no_prov
    (sl : ScalarLayout) (bytes : List AbstractByte)
    (hnp : abstractBytesHaveProv bytes = false) :
    decodeScalarLayoutBytesWithPolicy .stripProvenance sl bytes =
      decodeScalarLayoutBytesWithPolicy .strictUcg630Ub sl bytes := by
  unfold decodeScalarLayoutBytesWithPolicy policyRejectsProv
  simp only [hnp]

private theorem decodeArrayChunksWith_congr_no_prov
    (f₁ f₂ : List AbstractByte → Option Value) (elemSz : Nat)
    (hf : ∀ bs, abstractBytesHaveProv bs = false → f₁ bs = f₂ bs) :
    ∀ n bs, abstractBytesHaveProv bs = false →
      decodeArrayChunksWith f₁ elemSz n bs = decodeArrayChunksWith f₂ elemSz n bs
  | .zero, .nil, _ => rfl
  | .zero, _ :: _, _ => rfl
  | .succ k, bs, hnp => by
    unfold decodeArrayChunksWith
    cases Nat.ble elemSz (length bs) with
    | false => rfl
    | true =>
      dsimp only
      rw [hf _ (abstractBytesHaveProv_take elemSz bs hnp)]
      cases f₂ (takeAbstractBytes elemSz bs) with
      | none => rfl
      | some v =>
        dsimp only
        rw [decodeArrayChunksWith_congr_no_prov f₁ f₂ elemSz hf k _
          (abstractBytesHaveProv_drop elemSz bs hnp)]

private theorem decodeTypedKindsAndLayoutsAtOffsets_congr_no_prov
    (f₁ f₂ : Ty → List AbstractByte → Option Value) (layouts : LayoutTable)
    (bytes : List AbstractByte) (hnp : abstractBytesHaveProv bytes = false)
    (hf : ∀ ty bs, abstractBytesHaveProv bs = false → f₁ ty bs = f₂ ty bs) :
    ∀ offs ks fls,
      decodeTypedKindsAndLayoutsAtOffsets f₁ layouts bytes offs ks fls =
        decodeTypedKindsAndLayoutsAtOffsets f₂ layouts bytes offs ks fls
  | .nil, .nil, .nil => rfl
  | off :: offRest, k :: kRest, fIdx :: fRest => by
    unfold decodeTypedKindsAndLayoutsAtOffsets
    cases LayoutTable.lookup layouts fIdx with
    | none => rfl
    | some fl =>
      dsimp only
      cases hsl : sliceAbstractBytes bytes off.bytes fl.size.bytes with
      | none => rfl
      | some fSlice =>
        dsimp only
        rw [hf _ fSlice (abstractBytesHaveProv_slice bytes fSlice off.bytes fl.size.bytes hnp hsl)]
        cases f₂ { kind := k, layoutIdx := fIdx } fSlice with
        | none => rfl
        | some v =>
          dsimp only
          rw [decodeTypedKindsAndLayoutsAtOffsets_congr_no_prov f₁ f₂ layouts bytes hnp hf offRest kRest fRest]
  | .nil, _ :: _, _ => rfl
  | .nil, .nil, _ :: _ => rfl
  | _ :: _, .nil, _ => rfl
  | _ :: _, _ :: _, .nil => rfl

private theorem decodeFieldsAtOffsetsWith_congr_no_prov
    (f₁ f₂ : RigidTy → List AbstractByte → Option Value)
    (sizeOfKind : RigidTy → Option Nat) (bytes : List AbstractByte)
    (hnp : abstractBytesHaveProv bytes = false)
    (hf : ∀ k bs, abstractBytesHaveProv bs = false → f₁ k bs = f₂ k bs) :
    ∀ offs ks,
      decodeFieldsAtOffsetsWith f₁ sizeOfKind bytes offs ks =
        decodeFieldsAtOffsetsWith f₂ sizeOfKind bytes offs ks
  | .nil, .nil => rfl
  | .nil, _ :: _ => rfl
  | _ :: _, .nil => rfl
  | off :: offRest, k :: kRest => by
    unfold decodeFieldsAtOffsetsWith
    cases sizeOfKind k with
    | none => rfl
    | some fSize =>
      dsimp only
      cases hsl : sliceAbstractBytes bytes off.bytes fSize with
      | none => rfl
      | some fSlice =>
        dsimp only
        rw [hf k fSlice (abstractBytesHaveProv_slice bytes fSlice off.bytes fSize hnp hsl)]
        cases f₂ k fSlice with
        | none => rfl
        | some v =>
          dsimp only
          rw [decodeFieldsAtOffsetsWith_congr_no_prov f₁ f₂ sizeOfKind bytes hnp hf offRest kRest]

private theorem decodeSeqFieldsWith_congr_no_prov
    (f₁ f₂ : RigidTy → List AbstractByte → Option Value)
    (sizeOfKind : RigidTy → Option Nat)
    (hf : ∀ k bs, abstractBytesHaveProv bs = false → f₁ k bs = f₂ k bs) :
    ∀ ks bs, abstractBytesHaveProv bs = false →
      decodeSeqFieldsWith f₁ sizeOfKind ks bs = decodeSeqFieldsWith f₂ sizeOfKind ks bs
  | .nil, .nil, _ => rfl
  | .nil, _ :: _, _ => rfl
  | k :: kRest, bs, hnp => by
    unfold decodeSeqFieldsWith
    cases sizeOfKind k with
    | none => rfl
    | some fSize =>
      dsimp only
      cases Nat.ble fSize (length bs) with
      | false => rfl
      | true =>
        dsimp only
        rw [hf k _ (abstractBytesHaveProv_take fSize bs hnp)]
        cases f₂ k (takeAbstractBytes fSize bs) with
        | none => rfl
        | some v =>
          dsimp only
          rw [decodeSeqFieldsWith_congr_no_prov f₁ f₂ sizeOfKind hf kRest _
            (abstractBytesHaveProv_drop fSize bs hnp)]

private theorem decodeFieldsByLayoutIdxs_congr_no_prov
    (f₁ f₂ : Nat → List AbstractByte → Option Value)
    (layouts : LayoutTable) (bytes : List AbstractByte)
    (hnp : abstractBytesHaveProv bytes = false)
    (hf : ∀ fIdx bs, abstractBytesHaveProv bs = false → f₁ fIdx bs = f₂ fIdx bs) :
    ∀ offs fls,
      decodeFieldsByLayoutIdxs f₁ layouts bytes offs fls =
        decodeFieldsByLayoutIdxs f₂ layouts bytes offs fls
  | .nil, .nil => rfl
  | .nil, _ :: _ => rfl
  | _ :: _, .nil => rfl
  | off :: offRest, fIdx :: fRest => by
    unfold decodeFieldsByLayoutIdxs
    cases LayoutTable.lookup layouts fIdx with
    | none => rfl
    | some fl =>
      dsimp only
      cases hsl : sliceAbstractBytes bytes off.bytes fl.size.bytes with
      | none => rfl
      | some fSlice =>
        dsimp only
        rw [hf fIdx fSlice (abstractBytesHaveProv_slice bytes fSlice off.bytes fl.size.bytes hnp hsl)]
        cases f₂ fIdx fSlice with
        | none => rfl
        | some v =>
          dsimp only
          rw [decodeFieldsByLayoutIdxs_congr_no_prov f₁ f₂ layouts bytes hnp hf offRest fRest]

private theorem arrayFallbackElemSize_congr_no_prov
    (f₁ f₂ : List AbstractByte → Option Value)
    (hf : ∀ bs, abstractBytesHaveProv bs = false → f₁ bs = f₂ bs)
    (elemSzOpt : Option Nat) (n : Nat) (bytes : List AbstractByte)
    (hnp : abstractBytesHaveProv bytes = false) :
    ((match elemSzOpt with
      | .none => .none
      | .some elemSz =>
        match Nat.beq (length bytes) (Nat.mul elemSz n) with
        | false => .none
        | true =>
          match decodeArrayChunksWith f₁ elemSz n bytes with
          | .some elems => .some (.aggregate 0 elems)
          | .none => .none) : Option Value) =
    (match elemSzOpt with
      | .none => .none
      | .some elemSz =>
        match Nat.beq (length bytes) (Nat.mul elemSz n) with
        | false => .none
        | true =>
          match decodeArrayChunksWith f₂ elemSz n bytes with
          | .some elems => .some (.aggregate 0 elems)
          | .none => .none) := by
  cases elemSzOpt with
  | none => rfl
  | some elemSz =>
    dsimp only
    cases Nat.beq (length bytes) (Nat.mul elemSz n) with
    | false => rfl
    | true =>
      dsimp only
      rw [decodeArrayChunksWith_congr_no_prov f₁ f₂ elemSz hf n bytes hnp]

/-- Provenance-free equivalence: whenever `bytes` carries no pointer provenance,
`.stripProvenance` and `.strictUcg630Ub` return the identical `Option Value`. -/
theorem decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov :
    ∀ (fuel : Nat) (layouts : LayoutTable) (ty : Ty) (bytes : List AbstractByte),
      abstractBytesHaveProv bytes = false →
      decodeTypedValueFromBytesWithPolicy .stripProvenance fuel layouts ty bytes =
        decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel layouts ty bytes
  | .zero, _, _, _, _ => rfl
  | .succ fuel', layouts, ty, bytes, hnp => by
    unfold decodeTypedValueFromBytesWithPolicy
    dsimp only
    have ih : ∀ cTy bs, abstractBytesHaveProv bs = false →
        decodeTypedValueFromBytesWithPolicy .stripProvenance fuel' layouts cTy bs =
          decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel' layouts cTy bs :=
      fun cTy bs hbs =>
        decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov fuel' layouts cTy bs hbs
    cases hk : (normalizeCodecTy ty).kind with
    | array elemKind n =>
      dsimp only
      cases Nat.beq n 0 with
      | true => rfl
      | false =>
        dsimp only
        cases LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
        | none =>
          dsimp only
          exact arrayFallbackElemSize_congr_no_prov _ _ (fun bs hbs => ih _ bs hbs) _ n bytes hnp
        | some l =>
          cases l with
          | mk lsz lal lbr lfld lvar lunin lfls =>
            cases lfld with
            | array stride cnt =>
              cases lfls with
              | cons elemFlIdx flRest =>
                dsimp only
                cases Nat.beq (length bytes) (Nat.mul stride.bytes n) with
                | false => rfl
                | true =>
                  dsimp only
                  rw [decodeArrayChunksWith_congr_no_prov _ _ _ (fun bs hbs => ih _ bs hbs) _ bytes hnp]
              | nil =>
                dsimp only
                exact arrayFallbackElemSize_congr_no_prov _ _ (fun bs hbs => ih _ bs hbs) _ n bytes hnp
            | _ =>
              dsimp only
              exact arrayFallbackElemSize_congr_no_prov _ _ (fun bs hbs => ih _ bs hbs) _ n bytes hnp
    | tuple ks =>
      cases ks with
      | nil => rfl
      | cons kHead kTail =>
        dsimp only
        cases LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
        | none =>
          dsimp only
          rw [decodeSeqFieldsWith_congr_no_prov _ _ _ (fun k bs hbs => ih _ bs hbs) _ bytes hnp]
        | some l =>
          dsimp only
          cases Nat.beq (length bytes) l.size.bytes with
          | false => rfl
          | true =>
            cases l.fields with
            | arbitrary offsets _ =>
              dsimp only
              cases Bool.and (Nat.beq (length (kHead :: kTail)) (length offsets))
                  (Nat.beq (length l.fieldLayouts) (length offsets)) with
              | false =>
                dsimp only
                rw [decodeFieldsAtOffsetsWith_congr_no_prov _ _ _ bytes hnp (fun k bs hbs => ih _ bs hbs)]
              | true =>
                dsimp only
                rw [decodeTypedKindsAndLayoutsAtOffsets_congr_no_prov _ _ _ bytes hnp ih]
            | _ =>
              dsimp only
              rw [decodeSeqFieldsWith_congr_no_prov _ _ _ (fun k bs hbs => ih _ bs hbs) _ bytes hnp]
    | adt defPath args =>
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
          | multiple _ _ _ => rfl
          | single variantIdx =>
            dsimp only
            cases l.fields with
            | union count => cases variantIdx <;> rfl
            | arbitrary offsets _ =>
              cases offsets with
              | nil => rfl
              | cons off0 offRest =>
                dsimp only
                cases Nat.beq (length l.fieldLayouts) (length (off0 :: offRest)) with
                | true =>
                  dsimp only
                  rw [decodeFieldsByLayoutIdxs_congr_no_prov _ _ _ bytes hnp (fun fIdx bs hbs => ih _ bs hbs)]
                | false =>
                  dsimp only
                  cases offRest with
                  | nil =>
                    cases l.backendRepr with
                    | scalar s0 =>
                      dsimp only
                      cases scalarLayoutByteWidth s0 with
                      | none => rfl
                      | some sz0 =>
                        dsimp only
                        cases hsl : sliceAbstractBytes bytes off0.bytes sz0 with
                        | none => rfl
                        | some slice0 =>
                          dsimp only
                          rw [decodeScalarLayoutBytesWithPolicy_strip_eq_strict_of_no_prov s0 slice0
                            (abstractBytesHaveProv_slice bytes slice0 off0.bytes sz0 hnp hsl)]
                    | _ => unfold policyRejectsProv; rw [hnp]
                  | cons off1 offRest2 =>
                    cases offRest2 with
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
                                rw [decodeScalarLayoutBytesWithPolicy_strip_eq_strict_of_no_prov s0 slice0
                                      (abstractBytesHaveProv_slice bytes slice0 off0.bytes sz0 hnp hsl0),
                                    decodeScalarLayoutBytesWithPolicy_strip_eq_strict_of_no_prov s1 slice1
                                      (abstractBytesHaveProv_slice bytes slice1 off1.bytes sz1 hnp hsl1)]
                      | _ => unfold policyRejectsProv; rw [hnp]
                    | cons _ _ => unfold policyRejectsProv; rw [hnp]
            | array stride count =>
              dsimp only
              cases Nat.beq count 0 with
              | true => rfl
              | false =>
                dsimp only
                cases l.fieldLayouts with
                | nil => unfold policyRejectsProv; rw [hnp]
                | cons elemFlIdx _ =>
                  dsimp only
                  rw [decodeArrayChunksWith_congr_no_prov _ _ _ (fun bs hbs => ih _ bs hbs) _ bytes hnp]
            | primitive =>
              dsimp only
              cases Nat.beq l.size.bytes 0 with
              | true => rfl
              | false =>
                dsimp only
                cases l.backendRepr with
                | scalar s0 => exact decodeScalarLayoutBytesWithPolicy_strip_eq_strict_of_no_prov s0 bytes hnp
                | _ => unfold policyRejectsProv; rw [hnp]
    | bool | char | int _ | uint _ => unfold policyRejectsProv; rw [hnp]
    | fnPtr _ _ _ _ => exact decodePtrBytesNoForgeWithPolicy_strip_eq_strict_of_no_prov true (.tuple .nil) _ bytes hnp
    | rawPtr _ pointee => exact decodePtrBytesNoForgeWithPolicy_strip_eq_strict_of_no_prov false pointee _ bytes hnp
    | ref _ pointee => exact decodePtrBytesNoForgeWithPolicy_strip_eq_strict_of_no_prov true pointee _ bytes hnp
    | _ => rfl

/-! ### §6.4 `MaybeUninit<u8>`, Raw-Pointer Policy Independence & No-Provenance-Forgery -/

/-- Union layouts (`FieldsShape.union`, e.g. `MaybeUninit<u8>`) decode identically
under `.stripProvenance` and `.strictUcg630Ub`, preserving raw `AbstractByte`
provenance overlays. -/
theorem decodeTypedValueFromBytesWithPolicy_union_policy_indep
    (fuel : Nat) (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy)
    (layoutIdx : LayoutIdx) (l : TypeLayout) (count : Nat) (bytes : List AbstractByte)
    (hlk : LayoutTable.lookup layouts layoutIdx = .some l)
    (hvar : l.variants = .single 0) (hfld : l.fields = .union count) :
    decodeTypedValueFromBytesWithPolicy .stripProvenance (.succ fuel) layouts
        { kind := .adt defPath args, layoutIdx := layoutIdx } bytes =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub (.succ fuel) layouts
        { kind := .adt defPath args, layoutIdx := layoutIdx } bytes := by
  unfold decodeTypedValueFromBytesWithPolicy
  dsimp only [normalizeCodecTy]
  rw [hlk]
  dsimp only
  cases Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => rfl
  | false =>
    dsimp only
    rw [hvar, hfld]

/-- Thin raw pointers (`*const T` / `*mut T` for non-unsized `pointee`) decode
identically under `.stripProvenance` and `.strictUcg630Ub`. -/
theorem decodeTypedValueFromBytesWithPolicy_thinRawPtr_policy_indep
    (fuel : Nat) (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (layoutIdx : LayoutIdx) (bytes : List AbstractByte)
    (hthin : isThinPtrKind (.rawPtr m pointee) = true) :
    decodeTypedValueFromBytesWithPolicy .stripProvenance (.succ fuel) layouts
        { kind := .rawPtr m pointee, layoutIdx := layoutIdx } bytes =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub (.succ fuel) layouts
        { kind := .rawPtr m pointee, layoutIdx := layoutIdx } bytes := by
  unfold decodeTypedValueFromBytesWithPolicy decodePtrBytesNoForgeWithPolicy
  dsimp only [normalizeCodecTy]
  cases pointee with
  | slice _ | str | dynamic _ => cases hthin
  | _ => rfl

/-- Thin references (`&T` / `&mut T`) decode identically under both policies. -/
theorem decodeTypedValueFromBytesWithPolicy_thinRef_policy_indep
    (fuel : Nat) (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (layoutIdx : LayoutIdx) (bytes : List AbstractByte)
    (hthin : isThinPtrKind (.ref m pointee) = true) :
    decodeTypedValueFromBytesWithPolicy .stripProvenance (.succ fuel) layouts
        { kind := .ref m pointee, layoutIdx := layoutIdx } bytes =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub (.succ fuel) layouts
        { kind := .ref m pointee, layoutIdx := layoutIdx } bytes := by
  unfold decodeTypedValueFromBytesWithPolicy decodePtrBytesNoForgeWithPolicy
  dsimp only [normalizeCodecTy]
  cases pointee with
  | slice _ | str | dynamic _ => cases hthin
  | _ => rfl

/-- Function pointers decode identically under both policies. -/
theorem decodeTypedValueFromBytesWithPolicy_fnPtr_policy_indep
    (fuel : Nat) (layouts : LayoutTable) (inputs : List RigidTy) (output : RigidTy)
    (safety : Safety) (abi : CallConv) (layoutIdx : LayoutIdx) (bytes : List AbstractByte) :
    decodeTypedValueFromBytesWithPolicy .stripProvenance (.succ fuel) layouts
        { kind := .fnPtr inputs output safety abi, layoutIdx := layoutIdx } bytes =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub (.succ fuel) layouts
        { kind := .fnPtr inputs output safety abi, layoutIdx := layoutIdx } bytes :=
  rfl

/-- `dyn` wide raw pointers and references decode identically under both policies. -/
theorem decodeTypedValueFromBytesWithPolicy_wideDynPtr_policy_indep
    (fuel : Nat) (layouts : LayoutTable) (m : Mutability) (traitPath : DefPath)
    (layoutIdx : LayoutIdx) (bytes : List AbstractByte) :
    decodeTypedValueFromBytesWithPolicy .stripProvenance (.succ fuel) layouts
        { kind := .rawPtr m (.dynamic traitPath), layoutIdx := layoutIdx } bytes =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub (.succ fuel) layouts
        { kind := .rawPtr m (.dynamic traitPath), layoutIdx := layoutIdx } bytes := by
  unfold decodeTypedValueFromBytesWithPolicy decodePtrBytesNoForgeWithPolicy
  dsimp only [normalizeCodecTy]
  cases Nat.beq (length bytes) (Nat.add (layoutPointerBytes layouts) (layoutPointerBytes layouts)) with
  | false => rfl
  | true =>
    dsimp only
    cases decodeScalarBytes (dropAbstractBytes (layoutPointerBytes layouts) bytes) false with
    | none => rfl
    | some mp =>
      dsimp only
      cases abstractBytesUniformProv (dropAbstractBytes (layoutPointerBytes layouts) bytes) <;>
        cases mp.2 <;> rfl

theorem abstractBytesUniformProv_false_of_no_prov (bytes : List AbstractByte)
    (hnp : abstractBytesHaveProv bytes = false) :
    abstractBytesUniformProv bytes = false := by
  cases bytes with
  | nil => rfl
  | cons b rest =>
    cases b with
    | uninit => rfl
    | init _ prov =>
      cases prov with
      | none => rfl
      | some _ => cases hnp

/-- No provenance forgery under either policy: provenance-free bytes decoded at
a thin raw pointer yield `Value.scalar` (never `Value.ptr`). -/
theorem decodeTypedValueFromBytesWithPolicy_no_forge_thinRawPtr
    (policy : Ptr2IntTransmutePolicy) (fuel : Nat) (layouts : LayoutTable)
    (m : Mutability) (pointee : RigidTy) (layoutIdx : LayoutIdx)
    (bytes : List AbstractByte) (v : Value)
    (hthin : isThinPtrKind (.rawPtr m pointee) = true)
    (hnp : abstractBytesHaveProv bytes = false)
    (hdec : decodeTypedValueFromBytesWithPolicy policy (.succ fuel) layouts
      { kind := .rawPtr m pointee, layoutIdx := layoutIdx } bytes = .some v) :
    ∃ sv, v = .scalar sv := by
  have hunif := abstractBytesUniformProv_false_of_no_prov bytes hnp
  unfold decodeTypedValueFromBytesWithPolicy decodePtrBytesNoForgeWithPolicy at hdec
  dsimp only [normalizeCodecTy] at hdec
  cases pointee with
  | slice _ | str | dynamic _ => cases hthin
  | _ =>
    dsimp only at hdec
    cases hlen : Nat.beq (length bytes) (layoutPointerBytes layouts)
    · rw [hlen] at hdec; cases hdec
    · rw [hlen] at hdec
      cases hsc : decodeScalarBytes bytes false with
      | none => rw [hsc] at hdec; cases hdec
      | some p =>
        rw [hsc, hunif] at hdec
        injection hdec with hv
        exact ⟨⟨p.1.bits, layoutPointerBytes layouts⟩, hv.symm⟩

/-- No provenance forgery under either policy: provenance-free bytes decoded at
a thin reference `&T` / `&mut T` fail with `.none` (`.ub`). -/
theorem decodeTypedValueFromBytesWithPolicy_no_forge_thinRef
    (policy : Ptr2IntTransmutePolicy) (fuel : Nat) (layouts : LayoutTable)
    (m : Mutability) (pointee : RigidTy) (layoutIdx : LayoutIdx)
    (bytes : List AbstractByte)
    (hthin : isThinPtrKind (.ref m pointee) = true)
    (hnp : abstractBytesHaveProv bytes = false) :
    decodeTypedValueFromBytesWithPolicy policy (.succ fuel) layouts
        { kind := .ref m pointee, layoutIdx := layoutIdx } bytes = .none := by
  have hunif := abstractBytesUniformProv_false_of_no_prov bytes hnp
  unfold decodeTypedValueFromBytesWithPolicy decodePtrBytesNoForgeWithPolicy
  dsimp only [normalizeCodecTy]
  cases pointee with
  | slice _ | str | dynamic _ => cases hthin
  | _ =>
    dsimp only
    cases Nat.beq (length bytes) (layoutPointerBytes layouts)
    · rfl
    · cases decodeScalarBytes bytes false with
      | none => rfl
      | some p => rw [hunif]

/-- No provenance forgery under either policy: provenance-free bytes decoded at
a function pointer `fn(...)` fail with `.none` (`.ub`). -/
theorem decodeTypedValueFromBytesWithPolicy_no_forge_fnPtr
    (policy : Ptr2IntTransmutePolicy) (fuel : Nat) (layouts : LayoutTable)
    (inputs : List RigidTy) (output : RigidTy) (safety : Safety) (abi : CallConv)
    (layoutIdx : LayoutIdx) (bytes : List AbstractByte)
    (hnp : abstractBytesHaveProv bytes = false) :
    decodeTypedValueFromBytesWithPolicy policy (.succ fuel) layouts
        { kind := .fnPtr inputs output safety abi, layoutIdx := layoutIdx } bytes = .none := by
  have hunif := abstractBytesUniformProv_false_of_no_prov bytes hnp
  unfold decodeTypedValueFromBytesWithPolicy decodePtrBytesNoForgeWithPolicy
  dsimp only [normalizeCodecTy]
  cases Nat.beq (length bytes) (layoutPointerBytes layouts)
  · rfl
  · cases decodeScalarBytes bytes false with
    | none => rfl
    | some p => rw [hunif]

/-! ### §6.5 Concrete Flip-Direction Separation & Round-Trip Witnesses (`by rfl`) -/

/-- ZST placeholder layout at index `0` (`unresolvedLayoutIdx`), so concrete ADT
and array layouts sit at indices `≥ 1`. -/
def protoUnitLayout : TypeLayout := {
  size := { bytes := 0 }
  align := { bytes := 1 }
  backendRepr := .memory
  fields := .arbitrary [] []
  variants := .single 0
  isUninhabited := false
}

/-- `core::mem::MaybeUninit<u8>` union layout at index `1`. -/
def protoMaybeUninitU8Layout : TypeLayout := {
  size := { bytes := 1 }
  align := { bytes := 1 }
  backendRepr := .scalar (.union (.int 8 false))
  fields := .union 2
  variants := .single 0
  isUninhabited := false
  fieldLayouts := []
}

/-- `[core::mem::MaybeUninit<u8>; 8]` array layout at index `2` (`fieldLayouts = [1]`). -/
def protoMaybeUninitU8Arr8Layout : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 1 }
  backendRepr := .memory
  fields := .array { bytes := 1 } 8
  variants := .single 0
  isUninhabited := false
  fieldLayouts := [1]
}

/-- `f64` primitive layout at index `3` (needed because `Bytes.rigidTyKindByteSize`
currently lacks a `.float` branch and relies on `LayoutTable.lookup` for `tyByteSize`). -/
def protoF64Layout : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 8 }
  backendRepr := .scalar (.initialized (.float 64) ⟨0, scalarModulus 8 - 1⟩)
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

def protoTransmuteLayouts : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries := [protoUnitLayout, protoMaybeUninitU8Layout, protoMaybeUninitU8Arr8Layout, protoF64Layout]
}

/-- Concrete pointer with nonzero allocation ID and `3.0_f64` bit pattern as
offset (`0x4008000000000000`), exercising integer, byte-array, and `f64` targets. -/
def protoSamplePtr : ProvenancePtr := { allocId := 7, offsetBytes := 0x4008000000000000 }

def protoConstU8PtrTy : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 0 }
def protoMutU8PtrTy : Ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }
def protoUsizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
def protoU8Arr8Ty : Ty := { kind := .array (.uint .u8) 8, layoutIdx := 0 }
def protoF64Ty : Ty := { kind := .float .f64, layoutIdx := 3 }
def protoMaybeUninitU8Kind : RigidTy := .adt "core::mem::maybe_uninit::MaybeUninit" [.uint .u8]
def protoMaybeUninitU8Arr8Ty : Ty := { kind := .array protoMaybeUninitU8Kind 8, layoutIdx := 2 }
def protoWideSlicePtrTy : Ty := { kind := .rawPtr .not (.slice (.uint .u8)), layoutIdx := 0 }
def protoPtrPairTy : Ty := { kind := .array (.rawPtr .not (.uint .u8)) 2, layoutIdx := 0 }

def protoTransmuteDecls : List LocalDecl := [
  { mutability := .not, ty := protoConstU8PtrTy, debugName := none },
  { mutability := .not, ty := protoUsizeTy, debugName := none },
  { mutability := .not, ty := protoMaybeUninitU8Arr8Ty, debugName := none },
  { mutability := .not, ty := protoPtrPairTy, debugName := none }
]

def protoTransmuteLocals : List LocalSlot := [
  .init (.ptr protoSamplePtr 8),
  .init (.scalar ⟨protoSamplePtr.offsetBytes, 8⟩),
  .uninit,
  .init (.aggregate 0 [.ptr protoSamplePtr 8, .ptr protoSamplePtr 8])
]

/-- Flip-direction separation witnesses (`by rfl`):
1. `transmute::<*const u8, usize>(p)`: `.ok (.scalar ⟨p.offsetBytes, 8⟩)` under
   `.stripProvenance` vs. `.ub` under `.strictUcg630Ub`;
2. `transmute::<*const u8, [u8; 8]>(p)`: `.ok` of the 8 little-endian bytes under
   `.stripProvenance` vs. `.ub` under `.strictUcg630Ub`;
3. `transmute::<*const u8, f64>(p)`: `.ok (.scalar ⟨p.offsetBytes, 8⟩)` under
   `.stripProvenance` vs. `.ub` under `.strictUcg630Ub`;
4. `transmute::<[*const u8; 2], *const [u8]>(pair)` (provenance in slice length
   metadata): `.ok` under `.stripProvenance` vs. `.ub` under `.strictUcg630Ub`. -/
theorem ptr2int_flip_direction_separation_witnesses :
    -- 1. ptr -> usize
    evalByteCastWithPolicy .stripProvenance protoTransmuteLocals (.copy ⟨0, []⟩) protoUsizeTy
        emptyMemory protoTransmuteDecls protoTransmuteLayouts =
      .ok (.scalar ⟨protoSamplePtr.offsetBytes, 8⟩) protoTransmuteLocals emptyMemory ∧
    evalByteCastWithPolicy .strictUcg630Ub protoTransmuteLocals (.copy ⟨0, []⟩) protoUsizeTy
        emptyMemory protoTransmuteDecls protoTransmuteLayouts = .ub ∧
    -- 2. ptr -> [u8; 8]
    evalByteCastWithPolicy .stripProvenance protoTransmuteLocals (.copy ⟨0, []⟩) protoU8Arr8Ty
        emptyMemory protoTransmuteDecls protoTransmuteLayouts =
      .ok (.aggregate 0 [.scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩,
                         .scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩, .scalar ⟨0x08, 1⟩, .scalar ⟨0x40, 1⟩])
        protoTransmuteLocals emptyMemory ∧
    evalByteCastWithPolicy .strictUcg630Ub protoTransmuteLocals (.copy ⟨0, []⟩) protoU8Arr8Ty
        emptyMemory protoTransmuteDecls protoTransmuteLayouts = .ub ∧
    -- 3. ptr -> f64
    evalByteCastWithPolicy .stripProvenance protoTransmuteLocals (.copy ⟨0, []⟩) protoF64Ty
        emptyMemory protoTransmuteDecls protoTransmuteLayouts =
      .ok (.scalar ⟨protoSamplePtr.offsetBytes, 8⟩) protoTransmuteLocals emptyMemory ∧
    evalByteCastWithPolicy .strictUcg630Ub protoTransmuteLocals (.copy ⟨0, []⟩) protoF64Ty
        emptyMemory protoTransmuteDecls protoTransmuteLayouts = .ub ∧
    -- 4. [*const u8; 2] -> *const [u8] (slice length metadata carries provenance)
    evalByteCastWithPolicy .stripProvenance protoTransmuteLocals (.copy ⟨3, []⟩) protoWideSlicePtrTy
        emptyMemory protoTransmuteDecls protoTransmuteLayouts =
      .ok (.aggregate 0 [.ptr protoSamplePtr 8, .scalar ⟨protoSamplePtr.offsetBytes, 8⟩])
        protoTransmuteLocals emptyMemory ∧
    evalByteCastWithPolicy .strictUcg630Ub protoTransmuteLocals (.copy ⟨3, []⟩) protoWideSlicePtrTy
        emptyMemory protoTransmuteDecls protoTransmuteLayouts = .ub := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Two-step round-trip contrast (`by rfl`):
- `ptr -> usize -> *const u8` under `.stripProvenance` strips provenance,
  yielding `Value.scalar ⟨p.offsetBytes, 8⟩` (never `Value.ptr`);
- `ptr -> [MaybeUninit<u8>; 8] -> *const u8` preserves `Value.ptr p 8` under
  **both** `.stripProvenance` and `.strictUcg630Ub`;
- `ptr -> *mut u8` preserves `Value.ptr p 8` under **both** policies. -/
theorem ptr_roundtrip_contrast_witnesses :
    -- 1. ptr -> usize (strip) -> *const u8 yields provenance-less Value.scalar
    (match evalByteCastWithPolicy .stripProvenance protoTransmuteLocals (.copy ⟨0, []⟩) protoUsizeTy
        emptyMemory protoTransmuteDecls protoTransmuteLayouts with
      | .ok uVal _ _ =>
        let locals2 : List LocalSlot :=
          [.init (.ptr protoSamplePtr 8), .init uVal, .uninit,
           .init (.aggregate 0 [.ptr protoSamplePtr 8, .ptr protoSamplePtr 8])]
        evalByteCastWithPolicy .stripProvenance locals2 (.copy ⟨1, []⟩) protoConstU8PtrTy
          emptyMemory protoTransmuteDecls protoTransmuteLayouts =
            .ok (.scalar ⟨protoSamplePtr.offsetBytes, 8⟩) locals2 emptyMemory
      | _ => False) ∧
    -- 2. ptr -> [MaybeUninit<u8>; 8] -> *const u8 preserves Value.ptr under .stripProvenance
    (match evalByteCastWithPolicy .stripProvenance protoTransmuteLocals (.copy ⟨0, []⟩)
        protoMaybeUninitU8Arr8Ty emptyMemory protoTransmuteDecls protoTransmuteLayouts with
      | .ok arrVal _ _ =>
        let locals2 : List LocalSlot :=
          [.init (.ptr protoSamplePtr 8), .init (.scalar ⟨protoSamplePtr.offsetBytes, 8⟩),
           .init arrVal, .init (.aggregate 0 [.ptr protoSamplePtr 8, .ptr protoSamplePtr 8])]
        evalByteCastWithPolicy .stripProvenance locals2 (.copy ⟨2, []⟩) protoConstU8PtrTy
          emptyMemory protoTransmuteDecls protoTransmuteLayouts =
            .ok (.ptr protoSamplePtr 8) locals2 emptyMemory
      | _ => False) ∧
    -- 3. ptr -> [MaybeUninit<u8>; 8] -> *const u8 preserves Value.ptr under .strictUcg630Ub
    (match evalByteCastWithPolicy .strictUcg630Ub protoTransmuteLocals (.copy ⟨0, []⟩)
        protoMaybeUninitU8Arr8Ty emptyMemory protoTransmuteDecls protoTransmuteLayouts with
      | .ok arrVal _ _ =>
        let locals2 : List LocalSlot :=
          [.init (.ptr protoSamplePtr 8), .init (.scalar ⟨protoSamplePtr.offsetBytes, 8⟩),
           .init arrVal, .init (.aggregate 0 [.ptr protoSamplePtr 8, .ptr protoSamplePtr 8])]
        evalByteCastWithPolicy .strictUcg630Ub locals2 (.copy ⟨2, []⟩) protoConstU8PtrTy
          emptyMemory protoTransmuteDecls protoTransmuteLayouts =
            .ok (.ptr protoSamplePtr 8) locals2 emptyMemory
      | _ => False) ∧
    -- 4. ptr -> *mut u8 preserves Value.ptr under both policies
    evalByteCastWithPolicy .stripProvenance protoTransmuteLocals (.copy ⟨0, []⟩) protoMutU8PtrTy
        emptyMemory protoTransmuteDecls protoTransmuteLayouts =
      .ok (.ptr protoSamplePtr 8) protoTransmuteLocals emptyMemory ∧
    evalByteCastWithPolicy .strictUcg630Ub protoTransmuteLocals (.copy ⟨0, []⟩) protoMutU8PtrTy
        emptyMemory protoTransmuteDecls protoTransmuteLayouts =
      .ok (.ptr protoSamplePtr 8) protoTransmuteLocals emptyMemory := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Anneal.FloatArithAndUcg630Prototype
