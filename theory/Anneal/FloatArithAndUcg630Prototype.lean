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

3. **Strengthened specifications** (§7–§8):
   - IEEE-754 sign rules for `mul` / `div` / `rem`, out-of-width bit-pattern
     canonicalization, exact rational specifications of finite arithmetic
     (including the Euclidean `rem` decomposition), and correct rounding of
     finite products and quotients;
   - Exact characterization of the `miri#5643` candidate set and of the
     nondeterministic relation (Rust NaN rules: preferred / quieting
     propagation / unchanged propagation, nondeterministic sign);
   - General dispatcher fail-closed and result well-formedness theorems, plus
     the residual untyped-place interception gap witness;
   - Semantic characterization of `.stripProvenance` as `.strictUcg630Ub` on
     provenance-erased bytes (`stripAbstractBytesProv`) for non-pointer scalar
     targets, the exact shape of the policy split (`strip = strict ∨ strict = UB`),
     and general (non-witness) policy-independence / no-forgery theorems.

4. **Completeness results** (§9–§13):
   - Correct rounding of `add` / `sub`, exactness and magnitude bound of `rem`,
     gradual underflow, cross-format signaling-NaN survival, composite
     (array / tuple / wide-slice) erasure, and cast-level policy independence;
   - Sign symmetry of the rounding core (`roundRatioTiesToEven_not_neg`),
     sign-symmetric `mul` / `div` / `rem`, and the multiplicative identity `1.0`;
   - Multi-variant enum decoding: conservativity of the untyped policy-aware
     decoder with respect to the trusted decoder, the pointer-payload
     regression witness, and the typed per-variant decoder
     (`decodeMultiVariantEnumTypedWithPolicy`);
   - Outcome shape and failure preservation of the relational dispatcher.

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
    (rn rd : Nat) (yneg : Bool) (hy : decodeBits f y = .finite yneg rn rd) :
    evalFloatArithBaseProto .rem f (zeroBits f zneg) y = zeroBits f zneg := by
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

/-! ## §7. IEEE-754 Sign Rules, Width Canonicalization, Exact Rational Specs & Correct Rounding -/

/-- Sign field of a decoded `FloatKind`. -/
def floatKindNeg : FloatKind → Bool
  | .zero neg => neg
  | .finite neg _ _ => neg
  | .inf neg => neg
  | .nan neg _ _ => neg

theorem floatKindNeg_decodeBits (f : IeeeFormat) (bits : Nat) :
    floatKindNeg (decodeBits f bits) = (unpackBits f bits).neg := by
  unfold decodeBits
  dsimp only
  split
  · split <;> rfl
  · split
    · split <;> rfl
    · rfl

theorem isNaNBits_preferredNaNBits (f : IeeeFormat) :
    isNaNBits f (preferredNaNBits f) = true := by
  cases f <;> decide

/-- `roundRatioTiesToEven` never loses the requested sign: the result (zero,
subnormal, normal, or overflow infinity) always carries sign `neg`. -/
theorem floatKindNeg_roundRatioTiesToEven (f : IeeeFormat) (neg : Bool) (n d : Nat)
    (hd : 0 < d) :
    floatKindNeg (decodeBits f (roundRatioTiesToEven f neg n d)) = neg := by
  by_cases hn : n = 0
  · subst hn
    have h := (roundRatioBits_sign_and_underflow_zero_preserved.1 .tiesToEven f neg d hd).2
    rw [roundRatioBits_tiesToEven] at h
    rw [h]
    rfl
  · have h := (roundRatioTiesToEven_float_half_ulp f neg n d (Nat.pos_of_ne_zero hn) hd).2.2
    by_cases hinf : decodeBits f (roundRatioTiesToEven f neg n d) = .inf neg
    · rw [hinf]
      rfl
    · have hs := h hinf
      split at hs
      · cases hk : decodeBits f (roundRatioTiesToEven f neg n d) with
        | zero n₁ => rw [hk] at hs; exact hs
        | finite _ _ _ => rw [hk] at hs; exact False.elim hs
        | inf _ => rw [hk] at hs; exact False.elim hs
        | nan _ _ _ => rw [hk] at hs; exact False.elim hs
      · cases hk : decodeBits f (roundRatioTiesToEven f neg n d) with
        | zero _ => rw [hk] at hs; exact False.elim hs
        | finite s₁ _ _ => rw [hk] at hs; exact hs.1
        | inf _ => rw [hk] at hs; exact False.elim hs
        | nan _ _ _ => rw [hk] at hs; exact False.elim hs

/-- IEEE-754 §6.3 sign rule for products: every non-NaN `mul` result carries the
XOR of the operand signs (including exact zeros, underflow to zero, and
overflow to infinity). -/
theorem evalFloatArithBaseProto_mul_sign (f : IeeeFormat) (a b : Nat)
    (hnan : isNaNBits f (evalFloatArithBaseProto .mul f a b) = false) :
    (unpackBits f (evalFloatArithBaseProto .mul f a b)).neg =
      xor (unpackBits f a).neg (unpackBits f b).neg := by
  have hpn := isNaNBits_preferredNaNBits f
  rw [← floatKindNeg_decodeBits, ← floatKindNeg_decodeBits f a, ← floatKindNeg_decodeBits f b]
  unfold evalFloatArithBaseProto at hnan ⊢
  cases hl : decodeBits f a with
  | nan _ _ _ => rw [hl] at hnan; rw [hpn] at hnan; cases hnan
  | inf ln =>
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; rw [hpn] at hnan; cases hnan
    | zero _ => rw [hl, hr] at hnan; rw [hpn] at hnan; cases hnan
    | inf rn => dsimp only; rw [decodeBits_infBits]; rfl
    | finite rn _ _ => dsimp only; rw [decodeBits_infBits]; rfl
  | zero ln =>
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; rw [hpn] at hnan; cases hnan
    | inf _ => rw [hl, hr] at hnan; rw [hpn] at hnan; cases hnan
    | zero rn => dsimp only; rw [decodeBits_zeroBits]; rfl
    | finite rn _ _ => dsimp only; rw [decodeBits_zeroBits]; rfl
  | finite ln lnum lden =>
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; rw [hpn] at hnan; cases hnan
    | inf rn => dsimp only; rw [decodeBits_infBits]; rfl
    | zero rn => dsimp only; rw [decodeBits_zeroBits]; rfl
    | finite rn rnum rden =>
      dsimp only
      rw [floatKindNeg_roundRatioTiesToEven f _ _ _
        (Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden hl)
          (decodeBits_finite_den_pos f b rn rnum rden hr))]
      rfl

/-- IEEE-754 §6.3 sign rule for quotients: every non-NaN `div` result carries
the XOR of the operand signs (including `x / ±0 = ±Inf` and `x / ±Inf = ±0`). -/
theorem evalFloatArithBaseProto_div_sign (f : IeeeFormat) (a b : Nat)
    (hnan : isNaNBits f (evalFloatArithBaseProto .div f a b) = false) :
    (unpackBits f (evalFloatArithBaseProto .div f a b)).neg =
      xor (unpackBits f a).neg (unpackBits f b).neg := by
  have hpn := isNaNBits_preferredNaNBits f
  rw [← floatKindNeg_decodeBits, ← floatKindNeg_decodeBits f a, ← floatKindNeg_decodeBits f b]
  unfold evalFloatArithBaseProto at hnan ⊢
  cases hl : decodeBits f a with
  | nan _ _ _ => rw [hl] at hnan; rw [hpn] at hnan; cases hnan
  | inf ln =>
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; rw [hpn] at hnan; cases hnan
    | inf _ => rw [hl, hr] at hnan; rw [hpn] at hnan; cases hnan
    | zero rn => dsimp only; rw [decodeBits_infBits]; rfl
    | finite rn _ _ => dsimp only; rw [decodeBits_infBits]; rfl
  | zero ln =>
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; rw [hpn] at hnan; cases hnan
    | zero _ => rw [hl, hr] at hnan; rw [hpn] at hnan; cases hnan
    | inf rn => dsimp only; rw [decodeBits_zeroBits]; rfl
    | finite rn _ _ => dsimp only; rw [decodeBits_zeroBits]; rfl
  | finite ln lnum lden =>
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; rw [hpn] at hnan; cases hnan
    | zero rn => dsimp only; rw [decodeBits_infBits]; rfl
    | inf rn => dsimp only; rw [decodeBits_zeroBits]; rfl
    | finite rn rnum rden =>
      dsimp only
      rw [floatKindNeg_roundRatioTiesToEven f _ _ _
        (Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden hl)
          (decodeBits_finite_num_pos f b rn rnum rden hr))]
      rfl

/-- Rust `%` / C `fmod` sign rule: every non-NaN `rem` result carries the sign
of the dividend `a` (including exact zero remainders such as `(-4.0) % 2.0 =
-0.0`), independently of the divisor sign. -/
theorem evalFloatArithBaseProto_rem_sign (f : IeeeFormat) (a b : Nat)
    (hnan : isNaNBits f (evalFloatArithBaseProto .rem f a b) = false) :
    (unpackBits f (evalFloatArithBaseProto .rem f a b)).neg = (unpackBits f a).neg := by
  have hpn := isNaNBits_preferredNaNBits f
  rw [← floatKindNeg_decodeBits, ← floatKindNeg_decodeBits f a]
  unfold evalFloatArithBaseProto at hnan ⊢
  cases hl : decodeBits f a with
  | nan _ _ _ => rw [hl] at hnan; rw [hpn] at hnan; cases hnan
  | inf _ =>
    rw [hl] at hnan
    cases hr : decodeBits f b <;> rw [hr] at hnan <;> cases hpn.symm.trans hnan
  | zero ln =>
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; rw [hpn] at hnan; cases hnan
    | zero _ => rw [hl, hr] at hnan; rw [hpn] at hnan; cases hnan
    | inf _ => dsimp only; rw [decodeBits_mod_width, hl]
    | finite _ _ _ => dsimp only; rw [decodeBits_zeroBits]
  | finite ln lnum lden =>
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; rw [hpn] at hnan; cases hnan
    | zero _ => rw [hl, hr] at hnan; rw [hpn] at hnan; cases hnan
    | inf _ => dsimp only; rw [decodeBits_mod_width, hl]
    | finite rn rnum rden =>
      dsimp only
      rw [floatKindNeg_roundRatioTiesToEven f _ _ _
        (Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden hl)
          (decodeBits_finite_den_pos f b rn rnum rden hr))]
      rfl

/-! ### §7.1 Out-of-Width Bit-Pattern Canonicalization -/

theorem isNaNBits_mod_width (f : IeeeFormat) (bits : Nat) :
    isNaNBits f (bits % 2 ^ f.width) = isNaNBits f bits := by
  unfold isNaNBits
  rw [decodeBits_mod_width]

theorem isSignalingNaNBits_mod_width (f : IeeeFormat) (bits : Nat) :
    isSignalingNaNBits f (bits % 2 ^ f.width) = isSignalingNaNBits f bits := by
  unfold isSignalingNaNBits
  rw [decodeBits_mod_width]

theorem evalFloatToFloatRoundTiesToEven_mod_width (src dst : IeeeFormat) (bits : Nat) :
    evalFloatToFloatRoundTiesToEven src dst (bits % 2 ^ src.width) =
      evalFloatToFloatRoundTiesToEven src dst bits := by
  unfold evalFloatToFloatRoundTiesToEven
  rw [decodeBits_mod_width]

/-- Every base arithmetic op depends only on the canonical low `f.width` bits of
each operand: out-of-width scalar payloads cannot perturb the result. -/
theorem evalFloatArithBaseProto_mod_width (op : BinOp) (f : IeeeFormat) (a b : Nat) :
    evalFloatArithBaseProto op f (a % 2 ^ f.width) (b % 2 ^ f.width) =
      evalFloatArithBaseProto op f a b := by
  unfold evalFloatArithBaseProto
  rw [decodeBits_mod_width, decodeBits_mod_width, Nat.mod_mod]

theorem evalFloatPartialCompareProto_mod_width (f : IeeeFormat) (a b : Nat) :
    evalFloatPartialCompareProto f (a % 2 ^ f.width) (b % 2 ^ f.width) =
      evalFloatPartialCompareProto f a b := by
  unfold evalFloatPartialCompareProto
  rw [decodeBits_mod_width, decodeBits_mod_width]

theorem evalFloatCmpProto_mod_width (op : BinOp) (f : IeeeFormat) (a b : Nat) :
    evalFloatCmpProto op f (a % 2 ^ f.width) (b % 2 ^ f.width) = evalFloatCmpProto op f a b := by
  unfold evalFloatCmpProto
  rw [evalFloatPartialCompareProto_mod_width]

/-- Canonicalize every NaN-choice input to its source-format width. -/
def canonFloatInputs : List (IeeeFormat × Nat) → List (IeeeFormat × Nat)
  | .nil => .nil
  | entry :: rest => (entry.1, entry.2 % 2 ^ entry.1.width) :: canonFloatInputs rest

theorem quietedNaNCandidates_canon (f : IeeeFormat) (inputs : List (IeeeFormat × Nat)) :
    quietedNaNCandidates f (canonFloatInputs inputs) = quietedNaNCandidates f inputs := by
  induction inputs with
  | nil => rfl
  | cons entry rest ih =>
    unfold canonFloatInputs quietedNaNCandidates
    dsimp only
    rw [isNaNBits_mod_width, evalFloatToFloatRoundTiesToEven_mod_width, ih]

theorem signalingNaNCandidates_canon (f : IeeeFormat) (inputs : List (IeeeFormat × Nat)) :
    signalingNaNCandidates f (canonFloatInputs inputs) = signalingNaNCandidates f inputs := by
  induction inputs with
  | nil => rfl
  | cons entry rest ih =>
    unfold canonFloatInputs signalingNaNCandidates
    dsimp only
    rw [isSignalingNaNBits_mod_width, evalFloatToFloatRoundTiesToEven_mod_width, ih]

/-- The `miri#5643` candidate list is invariant under input canonicalization. -/
theorem nanChoicesProto_canon (f : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (mode : FloatArithMode) :
    nanChoicesProto f (canonFloatInputs inputs) mode = nanChoicesProto f inputs mode := by
  unfold nanChoicesProto
  rw [quietedNaNCandidates_canon, signalingNaNCandidates_canon]

/-- The relational semantics depends only on canonical operand bit patterns. -/
theorem EvalFloatBinOpRel.mod_width (mode : FloatArithMode) (op : BinOp) (f : IeeeFormat)
    (a b out : Nat) :
    EvalFloatBinOpRel mode op f (a % 2 ^ f.width) (b % 2 ^ f.width) out ↔
      EvalFloatBinOpRel mode op f a b out := by
  unfold EvalFloatBinOpRel
  dsimp only
  rw [evalFloatArithBaseProto_mod_width]
  have hc : nanChoicesProto f [(f, a % 2 ^ f.width), (f, b % 2 ^ f.width)] mode =
      nanChoicesProto f [(f, a), (f, b)] mode :=
    nanChoicesProto_canon f [(f, a), (f, b)] mode
  rw [hc]

/-! ### §7.2 Exact Rational Specifications of Finite Arithmetic & Correct Rounding -/

theorem evalFloatArithBaseProto_add_finite (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite ln lnum lden) (hr : decodeBits f b = .finite rn rnum rden) :
    evalFloatArithBaseProto .add f a b =
      roundRatioTiesToEven f
        (decide (signedNum ln lnum * Int.ofNat rden + signedNum rn rnum * Int.ofNat lden < 0))
        (signedNum ln lnum * Int.ofNat rden + signedNum rn rnum * Int.ofNat lden).natAbs
        (lden * rden) := by
  unfold evalFloatArithBaseProto exactSumProto
  rw [hl, hr]

theorem evalFloatArithBaseProto_sub_finite (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite ln lnum lden) (hr : decodeBits f b = .finite rn rnum rden) :
    evalFloatArithBaseProto .sub f a b =
      roundRatioTiesToEven f
        (decide (signedNum ln lnum * Int.ofNat rden - signedNum rn rnum * Int.ofNat lden < 0))
        (signedNum ln lnum * Int.ofNat rden - signedNum rn rnum * Int.ofNat lden).natAbs
        (lden * rden) := by
  unfold evalFloatArithBaseProto exactSumProto
  rw [hl, hr]
  dsimp only [negateFloatKind]
  rw [signedNum_neg, Int.neg_mul, ← Int.sub_eq_add_neg]

theorem evalFloatArithBaseProto_mul_finite (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite ln lnum lden) (hr : decodeBits f b = .finite rn rnum rden) :
    evalFloatArithBaseProto .mul f a b =
      roundRatioTiesToEven f (xor ln rn) (lnum * rnum) (lden * rden) := by
  unfold evalFloatArithBaseProto
  rw [hl, hr]

theorem evalFloatArithBaseProto_div_finite (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite ln lnum lden) (hr : decodeBits f b = .finite rn rnum rden) :
    evalFloatArithBaseProto .div f a b =
      roundRatioTiesToEven f (xor ln rn) (lnum * rden) (lden * rnum) := by
  unfold evalFloatArithBaseProto
  rw [hl, hr]

/-- Truncated-division remainder specification (Rust `%`, C `fmod`, LLVM
`frem`): for finite nonzero operands `|a| = lnum / lden` and `|b| = rnum / rden`
the result is the single rounding of the exact remainder
`((lnum * rden) % (lden * rnum)) / (lden * rden)`, which is strictly smaller in
magnitude than `|b|` (`rem < lden * rnum`) and satisfies the exact Euclidean
decomposition `|a| = q * |b| + rem` with `q = ⌊|a| / |b|⌋`. -/
theorem evalFloatArithBaseProto_rem_finite (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite ln lnum lden) (hr : decodeBits f b = .finite rn rnum rden) :
    evalFloatArithBaseProto .rem f a b =
        roundRatioTiesToEven f ln ((lnum * rden) % (lden * rnum)) (lden * rden) ∧
      (lnum * rden) % (lden * rnum) < lden * rnum ∧
      lnum * rden =
        (lnum * rden) / (lden * rnum) * (lden * rnum) + (lnum * rden) % (lden * rnum) := by
  have hden : 0 < lden * rnum :=
    Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden hl)
      (decodeBits_finite_num_pos f b rn rnum rden hr)
  have hdm := Nat.div_add_mod (lnum * rden) (lden * rnum)
  rw [Nat.mul_comm (lden * rnum) (lnum * rden / (lden * rnum))] at hdm
  refine ⟨?_, Nat.mod_lt _ hden, hdm.symm⟩
  unfold evalFloatArithBaseProto
  rw [hl, hr]
  dsimp only
  have hsub : lnum * rden - lnum * rden / (lden * rnum) * (lden * rnum) =
      lnum * rden % (lden * rnum) := by omega
  rw [hsub]

/-- Correct rounding of finite products: the result is the IEEE-754
`roundTiesToEven` rounding of the exact rational product
`(lnum * rnum) / (lden * rden)` (within half a unit in the last place of the
working binade, exact ties resolved to an even significand, and decoding to
exactly `(-1)^sign * sig * 2^(exponent - fractionBits)` unless it overflows). -/
theorem evalFloatArithBaseProto_mul_finite_correctly_rounded (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite ln lnum lden) (hr : decodeBits f b = .finite rn rnum rden) :
    let n := lnum * rnum
    let d := lden * rden
    let exponent := max (ratioExponent n d) f.minExponent
    let scaled := powScale n d ((f.fractionBits : Int) - exponent)
    let sig := roundQuotientTiesToEven scaled.1 scaled.2
    2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs ≤ scaled.2 ∧
      (2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs = scaled.2 →
        sig % 2 = 0) ∧
      (decodeBits f (evalFloatArithBaseProto .mul f a b) ≠ .inf (xor ln rn) →
        floatKindSameValue (decodeBits f (evalFloatArithBaseProto .mul f a b))
          (if sig = 0 then .zero (xor ln rn)
           else .finite (xor ln rn) (powScale sig 1 (exponent - f.fractionBits)).1
             (powScale sig 1 (exponent - f.fractionBits)).2)) := by
  rw [evalFloatArithBaseProto_mul_finite f a b ln rn lnum lden rnum rden hl hr]
  exact roundRatioTiesToEven_float_half_ulp f (xor ln rn) (lnum * rnum) (lden * rden)
    (Nat.mul_pos (decodeBits_finite_num_pos f a ln lnum lden hl)
      (decodeBits_finite_num_pos f b rn rnum rden hr))
    (Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden hl)
      (decodeBits_finite_den_pos f b rn rnum rden hr))

/-- Correct rounding of finite quotients (see
`evalFloatArithBaseProto_mul_finite_correctly_rounded`). -/
theorem evalFloatArithBaseProto_div_finite_correctly_rounded (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite ln lnum lden) (hr : decodeBits f b = .finite rn rnum rden) :
    let n := lnum * rden
    let d := lden * rnum
    let exponent := max (ratioExponent n d) f.minExponent
    let scaled := powScale n d ((f.fractionBits : Int) - exponent)
    let sig := roundQuotientTiesToEven scaled.1 scaled.2
    2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs ≤ scaled.2 ∧
      (2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs = scaled.2 →
        sig % 2 = 0) ∧
      (decodeBits f (evalFloatArithBaseProto .div f a b) ≠ .inf (xor ln rn) →
        floatKindSameValue (decodeBits f (evalFloatArithBaseProto .div f a b))
          (if sig = 0 then .zero (xor ln rn)
           else .finite (xor ln rn) (powScale sig 1 (exponent - f.fractionBits)).1
             (powScale sig 1 (exponent - f.fractionBits)).2)) := by
  rw [evalFloatArithBaseProto_div_finite f a b ln rn lnum lden rnum rden hl hr]
  exact roundRatioTiesToEven_float_half_ulp f (xor ln rn) (lnum * rden) (lden * rnum)
    (Nat.mul_pos (decodeBits_finite_num_pos f a ln lnum lden hl)
      (decodeBits_finite_den_pos f b rn rnum rden hr))
    (Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden hl)
      (decodeBits_finite_num_pos f b rn rnum rden hr))

/-! ### §7.3 Exact `miri#5643` NaN-Choice Characterization -/

/-- Lower (non-quiet-bit) payload of the target-format quieted conversion of
input `(srcFmt, inBits)`. -/
def signalingNaNLowerOf (f srcFmt : IeeeFormat) (inBits : Nat) : Nat :=
  (unpackBits f (evalFloatToFloatRoundTiesToEven srcFmt f inBits)).fraction %
    2 ^ (f.fractionBits - 1)

/-- The "unchanged propagation" candidate derived from input `(srcFmt, inBits)`:
its quieted target-format conversion with the quiet bit cleared again. -/
def signalingNaNCandidateOf (f srcFmt : IeeeFormat) (inBits : Nat) : Nat :=
  encodeBits f (unpackBits f (evalFloatToFloatRoundTiesToEven srcFmt f inBits)).neg
    (2 ^ f.exponentBits - 1) (signalingNaNLowerOf f srcFmt inBits)

private theorem nat_bne_zero_eq_true {x : Nat} (h : x ≠ 0) : (x != 0) = true := by
  cases x with
  | zero => exact absurd rfl h
  | succ _ => rfl

private theorem nat_bne_zero_eq_false {x : Nat} (h : x = 0) : (x != 0) = false := by
  subst h
  rfl

theorem isNaNBits_of_isSignalingNaNBits (f : IeeeFormat) (bits : Nat)
    (h : isSignalingNaNBits f bits = true) : isNaNBits f bits = true := by
  unfold isSignalingNaNBits at h
  unfold isNaNBits
  cases hd : decodeBits f bits with
  | nan _ _ _ => rfl
  | zero _ => rw [hd] at h; cases h
  | finite _ _ _ => rw [hd] at h; cases h
  | inf _ => rw [hd] at h; cases h

/-- Exact membership characterization of the quieted candidates: precisely the
target-format quieted conversions of the NaN inputs. -/
theorem mem_quietedNaNCandidates_iff (f : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (c : Nat) :
    c ∈ quietedNaNCandidates f inputs ↔
      ∃ e, e ∈ inputs ∧ isNaNBits e.1 e.2 = true ∧
        c = evalFloatToFloatRoundTiesToEven e.1 f e.2 := by
  induction inputs with
  | nil =>
    constructor
    · intro h; cases h
    · rintro ⟨_, h, _⟩; cases h
  | cons entry rest ih =>
    have hstep : quietedNaNCandidates f (entry :: rest) =
        if isNaNBits entry.1 entry.2 = true then
          evalFloatToFloatRoundTiesToEven entry.1 f entry.2 :: quietedNaNCandidates f rest
        else quietedNaNCandidates f rest := rfl
    rw [hstep]
    by_cases hnan : isNaNBits entry.1 entry.2 = true
    · rw [if_pos' hnan]
      constructor
      · intro h
        cases h with
        | head => exact ⟨entry, List.Mem.head _, hnan, rfl⟩
        | tail _ ht =>
          obtain ⟨e, he, hen, hc⟩ := ih.mp ht
          exact ⟨e, List.Mem.tail _ he, hen, hc⟩
      · rintro ⟨e, he, hen, hc⟩
        cases he with
        | head => rw [hc]; exact List.Mem.head _
        | tail _ ht => exact List.Mem.tail _ (ih.mpr ⟨e, ht, hen, hc⟩)
    · rw [if_neg' hnan]
      constructor
      · intro h
        obtain ⟨e, he, hen, hc⟩ := ih.mp h
        exact ⟨e, List.Mem.tail _ he, hen, hc⟩
      · rintro ⟨e, he, hen, hc⟩
        cases he with
        | head => exact absurd hen hnan
        | tail _ ht => exact ih.mpr ⟨e, ht, hen, hc⟩

/-- Exact membership characterization of the signaling candidates: precisely
the de-quieted conversions of the signaling NaN inputs whose target-format
lower payload survives (`signalingNaNLowerOf ≠ 0`). -/
theorem mem_signalingNaNCandidates_iff (f : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (c : Nat) :
    c ∈ signalingNaNCandidates f inputs ↔
      ∃ e, e ∈ inputs ∧ isSignalingNaNBits e.1 e.2 = true ∧
        signalingNaNLowerOf f e.1 e.2 ≠ 0 ∧ c = signalingNaNCandidateOf f e.1 e.2 := by
  induction inputs with
  | nil =>
    constructor
    · intro h; cases h
    · rintro ⟨_, h, _⟩; cases h
  | cons entry rest ih =>
    have hstep : signalingNaNCandidates f (entry :: rest) =
        if isSignalingNaNBits entry.1 entry.2 = true then
          if (signalingNaNLowerOf f entry.1 entry.2 != 0) = true then
            signalingNaNCandidateOf f entry.1 entry.2 :: signalingNaNCandidates f rest
          else signalingNaNCandidates f rest
        else signalingNaNCandidates f rest := rfl
    rw [hstep]
    by_cases hs : isSignalingNaNBits entry.1 entry.2 = true
    · rw [if_pos' hs]
      by_cases hl : signalingNaNLowerOf f entry.1 entry.2 = 0
      · rw [nat_bne_zero_eq_false hl, if_neg' (fun h => Bool.noConfusion h)]
        constructor
        · intro h
          obtain ⟨e, he, hes, hel, hc⟩ := ih.mp h
          exact ⟨e, List.Mem.tail _ he, hes, hel, hc⟩
        · rintro ⟨e, he, hes, hel, hc⟩
          cases he with
          | head => exact absurd hl hel
          | tail _ ht => exact ih.mpr ⟨e, ht, hes, hel, hc⟩
      · rw [nat_bne_zero_eq_true hl, if_pos' rfl]
        constructor
        · intro h
          cases h with
          | head => exact ⟨entry, List.Mem.head _, hs, hl, rfl⟩
          | tail _ ht =>
            obtain ⟨e, he, hes, hel, hc⟩ := ih.mp ht
            exact ⟨e, List.Mem.tail _ he, hes, hel, hc⟩
        · rintro ⟨e, he, hes, hel, hc⟩
          cases he with
          | head => rw [hc]; exact List.Mem.head _
          | tail _ ht => exact List.Mem.tail _ (ih.mpr ⟨e, ht, hes, hel, hc⟩)
    · rw [if_neg' hs]
      constructor
      · intro h
        obtain ⟨e, he, hes, hel, hc⟩ := ih.mp h
        exact ⟨e, List.Mem.tail _ he, hes, hel, hc⟩
      · rintro ⟨e, he, hes, hel, hc⟩
        cases he with
        | head => exact absurd hes hs
        | tail _ ht => exact ih.mpr ⟨e, ht, hes, hel, hc⟩

/-- Exact characterization of the nondeterministic `miri#5643` candidate set
for arbitrary (possibly cross-format) inputs: the preferred NaN, a quieted
input NaN, or a surviving de-quieted signaling input NaN, each with either
sign. -/
theorem nanChoicesProto_nondet_mem_iff (f : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (c : Nat) :
    c ∈ nanChoicesProto f inputs .nondeterministic ↔
      ∃ base,
        (base = preferredNaNBits f ∨
          (∃ e, e ∈ inputs ∧ isNaNBits e.1 e.2 = true ∧
            base = evalFloatToFloatRoundTiesToEven e.1 f e.2) ∨
          (∃ e, e ∈ inputs ∧ isSignalingNaNBits e.1 e.2 = true ∧
            signalingNaNLowerOf f e.1 e.2 ≠ 0 ∧ base = signalingNaNCandidateOf f e.1 e.2)) ∧
        (c = base ∨ c = evalFloatNegProto f base) := by
  have hexp : c ∈ nanChoicesProto f inputs .nondeterministic ↔
      ∃ base, base ∈ preferredNaNBits f ::
          (quietedNaNCandidates f inputs ++ signalingNaNCandidates f inputs) ∧
        (c = base ∨ c = evalFloatNegProto f base) :=
    expandNaNSigns_mem_iff f _ c
  rw [hexp]
  constructor
  · rintro ⟨base, hb, hc⟩
    refine ⟨base, ?_, hc⟩
    cases hb with
    | head => exact Or.inl rfl
    | tail _ hmem =>
      rcases List.mem_append.mp hmem with hq | hs
      · exact Or.inr (Or.inl ((mem_quietedNaNCandidates_iff f inputs base).mp hq))
      · exact Or.inr (Or.inr ((mem_signalingNaNCandidates_iff f inputs base).mp hs))
  · rintro ⟨base, hb, hc⟩
    refine ⟨base, ?_, hc⟩
    rcases hb with hp | hq | hs
    · rw [hp]; exact List.Mem.head _
    · exact List.Mem.tail _ (List.mem_append.mpr
        (Or.inl ((mem_quietedNaNCandidates_iff f inputs base).mpr hq)))
    · exact List.Mem.tail _ (List.mem_append.mpr
        (Or.inr ((mem_signalingNaNCandidates_iff f inputs base).mpr hs)))

/-- Sign nondeterminism is a closure property: the nondeterministic candidate
set is closed under bitwise negation. -/
theorem nanChoicesProto_nondet_neg_closed (f : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (c : Nat) (hc : c ∈ nanChoicesProto f inputs .nondeterministic) :
    evalFloatNegProto f c ∈ nanChoicesProto f inputs .nondeterministic := by
  have hexp : ∀ x, x ∈ nanChoicesProto f inputs .nondeterministic ↔
      ∃ base, base ∈ preferredNaNBits f ::
          (quietedNaNCandidates f inputs ++ signalingNaNCandidates f inputs) ∧
        (x = base ∨ x = evalFloatNegProto f base) :=
    fun x => expandNaNSigns_mem_iff f _ x
  obtain ⟨base, hb, hcb⟩ := (hexp c).mp hc
  have hlt : base < 2 ^ f.width :=
    (nanChoicesProto_mem_lt_and_nan f inputs .nondeterministic base
      ((hexp base).mpr ⟨base, hb, Or.inl rfl⟩)).1
  refine (hexp _).mpr ⟨base, hb, ?_⟩
  rcases hcb with hcb | hcb
  · rw [hcb]; exact Or.inr rfl
  · rw [hcb]; exact Or.inl (evalFloatNegProto_involutive f base hlt)

/-- Rust NaN rules for same-format binary arithmetic (`core` "NaN bit
patterns"): the admissible NaN results are exactly the preferred NaN, the
quieting propagation of either NaN operand, or the unchanged propagation of
either signaling NaN operand (canonical input bit pattern), each with a
nondeterministic sign. -/
theorem nanChoicesProto_binary_nondet_mem_iff (f : IeeeFormat) (a b c : Nat) :
    c ∈ nanChoicesProto f [(f, a), (f, b)] .nondeterministic ↔
      ∃ base,
        (base = preferredNaNBits f ∨
          (isNaNBits f a = true ∧ base = evalFloatToFloatRoundTiesToEven f f a) ∨
          (isNaNBits f b = true ∧ base = evalFloatToFloatRoundTiesToEven f f b) ∨
          (isSignalingNaNBits f a = true ∧ base = a % 2 ^ f.width) ∨
          (isSignalingNaNBits f b = true ∧ base = b % 2 ^ f.width)) ∧
        (c = base ∨ c = evalFloatNegProto f base) := by
  rw [nanChoicesProto_nondet_mem_iff]
  have hsame : ∀ x, isSignalingNaNBits f x = true →
      signalingNaNLowerOf f f x ≠ 0 ∧ signalingNaNCandidateOf f f x = x % 2 ^ f.width :=
    fun x hx => same_format_signaling_candidate_eq f x hx
  constructor
  · rintro ⟨base, hb, hc⟩
    refine ⟨base, ?_, hc⟩
    rcases hb with h | ⟨e, he, hen, hbe⟩ | ⟨e, he, hes, _, hbe⟩
    · exact Or.inl h
    · cases he with
      | head => exact Or.inr (Or.inl ⟨hen, hbe⟩)
      | tail _ he' =>
        cases he' with
        | head => exact Or.inr (Or.inr (Or.inl ⟨hen, hbe⟩))
        | tail _ h => cases h
    · cases he with
      | head => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hes, hbe.trans (hsame a hes).2⟩)))
      | tail _ he' =>
        cases he' with
        | head => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hes, hbe.trans (hsame b hes).2⟩)))
        | tail _ h => cases h
  · rintro ⟨base, hb, hc⟩
    refine ⟨base, ?_, hc⟩
    rcases hb with h | ⟨hn, hbe⟩ | ⟨hn, hbe⟩ | ⟨hs, hbe⟩ | ⟨hs, hbe⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨(f, a), List.Mem.head _, hn, hbe⟩)
    · exact Or.inr (Or.inl ⟨(f, b), List.Mem.tail _ (List.Mem.head _), hn, hbe⟩)
    · exact Or.inr (Or.inr ⟨(f, a), List.Mem.head _, hs, (hsame a hs).1,
        hbe.trans (hsame a hs).2.symm⟩)
    · exact Or.inr (Or.inr ⟨(f, b), List.Mem.tail _ (List.Mem.head _), hs, (hsame b hs).1,
        hbe.trans (hsame b hs).2.symm⟩)

/-- Unchanged propagation of a signaling NaN right operand is admissible
(the symmetric counterpart of `EvalFloatBinOpRel.signaling_lhs_mem`). -/
theorem EvalFloatBinOpRel.signaling_rhs_mem (op : BinOp) (f : IeeeFormat) (lhs rhs : Nat)
    (hop : isFloatArithBinOp op = true) (hr : isSignalingNaNBits f rhs = true) :
    EvalFloatBinOpRel .nondeterministic op f lhs rhs (rhs % 2 ^ f.width) := by
  refine ⟨hop, ?_⟩
  dsimp only
  rw [evalFloatArithBaseProto_nan_right op f lhs rhs (isNaNBits_of_isSignalingNaNBits f rhs hr),
    if_pos' (isNaNBits_preferredNaNBits f)]
  exact (nanChoicesProto_binary_nondet_mem_iff f lhs rhs _).mpr
    ⟨rhs % 2 ^ f.width, Or.inr (Or.inr (Or.inr (Or.inr ⟨hr, rfl⟩))), Or.inl rfl⟩

/-- Nondeterminism is confined to NaN results: any admissible non-NaN output is
the deterministic base result, under either mode. -/
theorem EvalFloatBinOpRel.eq_base_of_not_nan (mode : FloatArithMode) (op : BinOp)
    (f : IeeeFormat) (lhs rhs out : Nat) (h : EvalFloatBinOpRel mode op f lhs rhs out)
    (hout : isNaNBits f out = false) :
    out = evalFloatArithBaseProto op f lhs rhs := by
  have hiff := EvalFloatBinOpRel.nan_iff mode op f lhs rhs out h
  have hb := h.2
  dsimp only at hb
  by_cases hnan : isNaNBits f (evalFloatArithBaseProto op f lhs rhs) = true
  · rw [hnan, hout] at hiff
    cases hiff
  · rw [if_neg' hnan] at hb
    exact hb

/-- The sign of an admissible NaN result is unconstrained: negating any
admissible NaN output yields another admissible output. -/
theorem EvalFloatBinOpRel.nondet_neg_closed (op : BinOp) (f : IeeeFormat) (lhs rhs out : Nat)
    (hnan : isNaNBits f (evalFloatArithBaseProto op f lhs rhs) = true)
    (h : EvalFloatBinOpRel .nondeterministic op f lhs rhs out) :
    EvalFloatBinOpRel .nondeterministic op f lhs rhs (evalFloatNegProto f out) := by
  refine ⟨h.1, ?_⟩
  have hb := h.2
  dsimp only at hb ⊢
  rw [if_pos' hnan] at hb ⊢
  exact nanChoicesProto_nondet_neg_closed f _ out hb

/-- Complete characterization of the nondeterministic relation: a non-NaN base
result is the unique output, and a NaN base result admits exactly the Rust NaN
rule set (preferred / quieting propagation / unchanged propagation, with a
nondeterministic sign). -/
theorem EvalFloatBinOpRel.nondet_iff (op : BinOp) (f : IeeeFormat) (lhs rhs out : Nat) :
    EvalFloatBinOpRel .nondeterministic op f lhs rhs out ↔
      isFloatArithBinOp op = true ∧
        ((isNaNBits f (evalFloatArithBaseProto op f lhs rhs) = false ∧
            out = evalFloatArithBaseProto op f lhs rhs) ∨
          (isNaNBits f (evalFloatArithBaseProto op f lhs rhs) = true ∧
            ∃ base,
              (base = preferredNaNBits f ∨
                (isNaNBits f lhs = true ∧ base = evalFloatToFloatRoundTiesToEven f f lhs) ∨
                (isNaNBits f rhs = true ∧ base = evalFloatToFloatRoundTiesToEven f f rhs) ∨
                (isSignalingNaNBits f lhs = true ∧ base = lhs % 2 ^ f.width) ∨
                (isSignalingNaNBits f rhs = true ∧ base = rhs % 2 ^ f.width)) ∧
              (out = base ∨ out = evalFloatNegProto f base))) := by
  unfold EvalFloatBinOpRel
  dsimp only
  by_cases hnan : isNaNBits f (evalFloatArithBaseProto op f lhs rhs) = true
  · rw [if_pos' hnan, nanChoicesProto_binary_nondet_mem_iff]
    constructor
    · rintro ⟨hop, hb⟩
      exact ⟨hop, Or.inr ⟨hnan, hb⟩⟩
    · rintro ⟨hop, hcase⟩
      rcases hcase with ⟨hf, _⟩ | ⟨_, hb⟩
      · rw [hnan] at hf; cases hf
      · exact ⟨hop, hb⟩
  · rw [if_neg' hnan]
    have hfalse : isNaNBits f (evalFloatArithBaseProto op f lhs rhs) = false := by
      cases hx : isNaNBits f (evalFloatArithBaseProto op f lhs rhs) with
      | false => rfl
      | true => exact absurd hx hnan
    constructor
    · rintro ⟨hop, hb⟩
      exact ⟨hop, Or.inl ⟨hfalse, hb⟩⟩
    · rintro ⟨hop, hcase⟩
      rcases hcase with ⟨_, hb⟩ | ⟨ht, _⟩
      · exact ⟨hop, hb⟩
      · exact absurd ht hnan

/-! ### §7.4 Dispatcher Fail-Closed & Result Well-Formedness Theorems -/

private theorem bool_and_true_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a
  · cases h
  · rfl

private theorem bool_and_true_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a
  · cases h
  · exact h

private theorem ieeeFormat_eq_of_beq {a b : IeeeFormat} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

/-- General `f16`/`f128` fail-closed gate for float negation: whenever the
operand's static type is an unmodeled float kind, `evalRvalueFloatProto` never
returns `.ok`. -/
theorem evalRvalueFloatProto_neg_fail_closed_of_unmodeled
    (locals : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (fk : FloatTy)
    (hty : floatTyOf? (operandTy localDecls layouts op) = .some fk)
    (hfk : ieeeFormatOfFloatTy? fk = .none) :
    evalRvalueFloatProto locals (.unaryOp .neg op) mem localDecls layouts = .ub ∨
      evalRvalueFloatProto locals (.unaryOp .neg op) mem localDecls layouts = .unsupported := by
  unfold evalRvalueFloatProto
  dsimp only
  rw [hty]
  dsimp only
  cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack with
  | ub => exact Or.inl rfl
  | unsupported => exact Or.inr rfl
  | ok v l =>
    cases v with
    | scalar sc => dsimp only; rw [hfk]; exact Or.inr rfl
    | unit => exact Or.inr rfl
    | ptr _ _ => exact Or.inr rfl
    | aggregate _ _ => exact Or.inr rfl

/-- Well-formedness of successful float negation: the result is a canonical
in-width scalar of the operand's IEEE format and memory is unchanged. -/
theorem evalRvalueFloatProto_neg_float_ok_wf
    (locals : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (fk : FloatTy)
    (v : Value) (locals' : List LocalSlot) (mem' : Memory)
    (hty : floatTyOf? (operandTy localDecls layouts op) = .some fk)
    (hok : evalRvalueFloatProto locals (.unaryOp .neg op) mem localDecls layouts =
      .ok v locals' mem') :
    mem' = mem ∧
      ∃ fmt bits, ieeeFormatOfFloatTy? fk = .some fmt ∧
        v = .scalar ⟨bits, fmt.byteWidth⟩ ∧ bits < 2 ^ fmt.width := by
  unfold evalRvalueFloatProto at hok
  dsimp only at hok
  rw [hty] at hok
  dsimp only at hok
  cases hev : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack with
  | ub => rw [hev] at hok; cases hok
  | unsupported => rw [hev] at hok; cases hok
  | ok val l =>
    rw [hev] at hok
    cases val with
    | scalar sc =>
      dsimp only at hok
      cases hfmt : ieeeFormatOfFloatTy? fk with
      | none => rw [hfmt] at hok; cases hok
      | some fmt =>
        rw [hfmt] at hok
        dsimp only at hok
        cases hsz : Nat.beq sc.sizeBytes fmt.byteWidth with
        | false => rw [hsz] at hok; cases hok
        | true =>
          rw [hsz] at hok
          injection hok with hv _ hm
          exact ⟨hm.symm, fmt, evalFloatNegProto fmt sc.bits, rfl, hv.symm,
            evalFloatNegProto_lt fmt sc.bits⟩
    | unit => cases hok
    | ptr _ _ => cases hok
    | aggregate _ _ => cases hok

/-- Mixed float / non-float binary operands always fail closed with
`.unsupported` (never reaching the integer scalar path). -/
theorem evalRvalueFloatProto_binaryOp_float_nonFloat_unsupported
    (locals : List LocalSlot) (op : BinOp) (lhsOp rhsOp : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (fk : FloatTy)
    (h : (floatTyOf? (operandTy localDecls layouts lhsOp) = .some fk ∧
            floatTyOf? (operandTy localDecls layouts rhsOp) = .none) ∨
          (floatTyOf? (operandTy localDecls layouts lhsOp) = .none ∧
            floatTyOf? (operandTy localDecls layouts rhsOp) = .some fk)) :
    evalRvalueFloatProto locals (.binaryOp op lhsOp rhsOp) mem localDecls layouts =
      .unsupported := by
  unfold evalRvalueFloatProto
  dsimp only
  rcases h with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> rw [hl, hr]

/-- General fail-closed gate for float binary ops: whenever both operands are
float-typed but do not share one modeled IEEE format (`f16`/`f128` on either
side, or `f32` vs. `f64`), `evalRvalueFloatProto` never returns `.ok`. -/
theorem evalRvalueFloatProto_binaryOp_fail_closed_of_unmodeled_or_mismatch
    (locals : List LocalSlot) (op : BinOp) (lhsOp rhsOp : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (lhsFk rhsFk : FloatTy)
    (hl : floatTyOf? (operandTy localDecls layouts lhsOp) = .some lhsFk)
    (hr : floatTyOf? (operandTy localDecls layouts rhsOp) = .some rhsFk)
    (hmis : ∀ fmt, ¬ (ieeeFormatOfFloatTy? lhsFk = .some fmt ∧
      ieeeFormatOfFloatTy? rhsFk = .some fmt)) :
    evalRvalueFloatProto locals (.binaryOp op lhsOp rhsOp) mem localDecls layouts = .ub ∨
      evalRvalueFloatProto locals (.binaryOp op lhsOp rhsOp) mem localDecls layouts =
        .unsupported := by
  unfold evalRvalueFloatProto
  dsimp only
  rw [hl, hr]
  dsimp only
  cases evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack with
  | ub => exact Or.inl rfl
  | unsupported => exact Or.inr rfl
  | ok lv l₁ =>
    dsimp only
    cases evalOperand l₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls
        mem.callStack with
    | ub => exact Or.inl rfl
    | unsupported => exact Or.inr rfl
    | ok rv l₂ =>
      dsimp only
      cases lv with
      | scalar lsc =>
        cases rv with
        | scalar rsc =>
          dsimp only
          cases hfl : ieeeFormatOfFloatTy? lhsFk with
          | none => exact Or.inr rfl
          | some fmtL =>
            cases hfr : ieeeFormatOfFloatTy? rhsFk with
            | none => exact Or.inr rfl
            | some fmtR =>
              dsimp only
              by_cases hcond : (fmtL == fmtR && Nat.beq lsc.sizeBytes fmtL.byteWidth &&
                  Nat.beq rsc.sizeBytes fmtL.byteWidth) = true
              · have heq := ieeeFormat_eq_of_beq (bool_and_true_left (bool_and_true_left hcond))
                subst heq
                exact absurd ⟨hfl, hfr⟩ (hmis fmtL)
              · rw [if_neg' hcond]
                exact Or.inr rfl
        | unit => exact Or.inr rfl
        | ptr _ _ => exact Or.inr rfl
        | aggregate _ _ => exact Or.inr rfl
      | unit => exact Or.inr rfl
      | ptr _ _ => exact Or.inr rfl
      | aggregate _ _ => exact Or.inr rfl

/-- Well-formedness of successful float binary ops: both operands share one
modeled IEEE format, memory is unchanged, arithmetic results are canonical
in-width scalars of that format, and comparison results are canonical `bool`
scalars. -/
theorem evalRvalueFloatProto_binaryOp_float_ok_wf
    (locals : List LocalSlot) (op : BinOp) (lhsOp rhsOp : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (lhsFk rhsFk : FloatTy)
    (v : Value) (locals' : List LocalSlot) (mem' : Memory)
    (hl : floatTyOf? (operandTy localDecls layouts lhsOp) = .some lhsFk)
    (hr : floatTyOf? (operandTy localDecls layouts rhsOp) = .some rhsFk)
    (hok : evalRvalueFloatProto locals (.binaryOp op lhsOp rhsOp) mem localDecls layouts =
      .ok v locals' mem') :
    mem' = mem ∧
      ∃ fmt, ieeeFormatOfFloatTy? lhsFk = .some fmt ∧ ieeeFormatOfFloatTy? rhsFk = .some fmt ∧
        ((isFloatArithBinOp op = true ∧
            ∃ bits, v = .scalar ⟨bits, fmt.byteWidth⟩ ∧ bits < 2 ^ fmt.width) ∨
          (isFloatArithBinOp op = false ∧ isFloatCmpBinOp op = true ∧
            ∃ b, v = .scalar (boolToScalar b))) := by
  unfold evalRvalueFloatProto at hok
  dsimp only at hok
  rw [hl, hr] at hok
  dsimp only at hok
  cases hlev : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals
      localDecls mem.callStack with
  | ub => rw [hlev] at hok; cases hok
  | unsupported => rw [hlev] at hok; cases hok
  | ok lv l₁ =>
    rw [hlev] at hok
    dsimp only at hok
    cases hrev : evalOperand l₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals
        localDecls mem.callStack with
    | ub => rw [hrev] at hok; cases hok
    | unsupported => rw [hrev] at hok; cases hok
    | ok rv l₂ =>
      rw [hrev] at hok
      dsimp only at hok
      cases lv with
      | scalar lsc =>
        cases rv with
        | scalar rsc =>
          dsimp only at hok
          cases hfl : ieeeFormatOfFloatTy? lhsFk with
          | none => rw [hfl] at hok; cases hok
          | some fmtL =>
            cases hfr : ieeeFormatOfFloatTy? rhsFk with
            | none => rw [hfl, hfr] at hok; cases hok
            | some fmtR =>
              rw [hfl, hfr] at hok
              dsimp only at hok
              by_cases hcond : (fmtL == fmtR && Nat.beq lsc.sizeBytes fmtL.byteWidth &&
                  Nat.beq rsc.sizeBytes fmtL.byteWidth) = true
              · have heq := ieeeFormat_eq_of_beq (bool_and_true_left (bool_and_true_left hcond))
                subst heq
                rw [if_pos' hcond] at hok
                unfold evalFloatArithBaseProto? evalFloatCmpProto? at hok
                by_cases hop : isFloatArithBinOp op = true
                · rw [if_pos' hop] at hok
                  dsimp only at hok
                  injection hok with hv _ hm
                  exact ⟨hm.symm, fmtL, rfl, rfl, Or.inl ⟨hop,
                    evalFloatArithBaseProto op fmtL lsc.bits rsc.bits, hv.symm,
                    evalFloatArithBaseProto_lt op fmtL lsc.bits rsc.bits⟩⟩
                · rw [if_neg' hop] at hok
                  dsimp only at hok
                  have hopf : isFloatArithBinOp op = false := by
                    cases hx : isFloatArithBinOp op with
                    | false => rfl
                    | true => exact absurd hx hop
                  by_cases hcmp : isFloatCmpBinOp op = true
                  · rw [if_pos' hcmp] at hok
                    dsimp only at hok
                    injection hok with hv _ hm
                    exact ⟨hm.symm, fmtL, rfl, rfl, Or.inr ⟨hopf, hcmp,
                      evalFloatCmpProto op fmtL lsc.bits rsc.bits, hv.symm⟩⟩
                  · rw [if_neg' hcmp] at hok
                    cases hok
              · rw [if_neg' hcond] at hok
                cases hok
        | unit => cases hok
        | ptr _ _ => cases hok
        | aggregate _ _ => cases hok
      | unit => cases hok
      | ptr _ _ => cases hok
      | aggregate _ _ => cases hok

/-- `UnOp.not` on a float-typed operand is delegated to the trusted
`evalRvalue`, whose `evalUnaryNot` rejects float types: the dispatcher never
returns `.ok` (no bitwise-NOT misdispatch on IEEE-754 bit patterns). -/
theorem evalRvalueFloatProto_not_float_fail_closed
    (locals : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (fk : FloatTy)
    (hty : floatTyOf? (operandTy localDecls layouts op) = .some fk) :
    evalRvalueFloatProto locals (.unaryOp .not op) mem localDecls layouts = .ub ∨
      evalRvalueFloatProto locals (.unaryOp .not op) mem localDecls layouts = .unsupported := by
  have hproto : evalRvalueFloatProto locals (.unaryOp .not op) mem localDecls layouts =
      evalRvalue locals (.unaryOp .not op) mem localDecls layouts := rfl
  rw [hproto]
  unfold evalRvalue
  dsimp only
  cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack with
  | ub => exact Or.inl rfl
  | unsupported => exact Or.inr rfl
  | ok v l =>
    cases v with
    | scalar sc =>
      dsimp only
      unfold floatTyOf? at hty
      cases hot : operandTy localDecls layouts op with
      | none => rw [hot] at hty; cases hty
      | some ty =>
        rw [hot] at hty
        dsimp only at hty
        unfold evalUnaryNot
        dsimp only
        cases hk : ty.kind <;> rw [hk] at hty <;> first | exact Or.inr rfl | cases hty
    | unit => exact Or.inr rfl
    | ptr _ _ => exact Or.inr rfl
    | aggregate _ _ => exact Or.inr rfl

/-- The relational `Rvalue` float semantics is total under both modes (the
deterministic evaluator's result is always admissible). -/
theorem EvalRvalueFloatRelProto.total
    (mode : FloatArithMode) (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    ∃ res, EvalRvalueFloatRelProto mode locals rv mem localDecls layouts res := by
  have hdet : EvalRvalueFloatRelProto .deterministic locals rv mem localDecls layouts
      (evalRvalueFloatProto locals rv mem localDecls layouts) :=
    (EvalRvalueFloatRelProto.det_iff locals rv mem localDecls layouts _).mpr rfl
  cases mode with
  | deterministic => exact ⟨_, hdet⟩
  | nondeterministic =>
    exact ⟨_, EvalRvalueFloatRelProto.det_imp_nondet locals rv mem localDecls layouts _ hdet⟩

/-- A float constant operand (`Operand.constant`) with static type `f32`. -/
def f32ConstOperandProto (bits : Nat) : Operand :=
  .constant { ty := { kind := .float .f32, layoutIdx := 0 }, val := .scalar (.int ⟨bits, 4⟩) }

/-- Scope of the static-type-directed interception (`by rfl`):
1. float **constants** carry their own type (`ConstOperand.ty`), so they are
   intercepted even with empty `localDecls` (`1.5 + 2.25 = 3.75`, and negation
   of a signaling NaN constant preserves its payload);
2. **residual gap**: a float held in a *place* whose type cannot be resolved
   (`localDecls = []`, the default argument of the trusted `evalRvalue`) is
   invisible to `floatTyOf?`, so the wrapper delegates to the trusted evaluator
   and inherits its integer misdispatch (`-1.0_f32 ↦ 0xC0800000`). The TCB patch
   must therefore either guarantee that every `evalRvalue` call site threads
   `localDecls` (and `layouts`), or fail closed on untyped scalar `neg` /
   arithmetic operands. -/
theorem evalRvalueFloatProto_constant_interception_and_untyped_place_residual_witness :
    evalRvalueFloatProto [] (.binaryOp .add (f32ConstOperandProto 0x3FC00000)
        (f32ConstOperandProto 0x40100000)) emptyMemory [] emptyLayoutTable =
      .ok (.scalar ⟨0x40700000, 4⟩) [] emptyMemory ∧
    evalRvalueFloatProto [] (.unaryOp .neg (f32ConstOperandProto 0x7F800001)) emptyMemory []
        emptyLayoutTable =
      .ok (.scalar ⟨0xFF800001, 4⟩) [] emptyMemory ∧
    evalRvalueFloatProto floatMisdispatchLocals (.binaryOp .mul (f32ConstOperandProto 0x40000000)
        (.copy ⟨0, []⟩)) emptyMemory floatMisdispatchDecls emptyLayoutTable =
      .ok (.scalar ⟨0x40000000, 4⟩) floatMisdispatchLocals emptyMemory ∧
    evalRvalueFloatProto floatMisdispatchLocals (.unaryOp .neg (.copy ⟨0, []⟩)) emptyMemory []
        emptyLayoutTable =
      .ok (.scalar ⟨0xC0800000, 4⟩) floatMisdispatchLocals emptyMemory ∧
    evalRvalueFloatProto floatMisdispatchLocals (.binaryOp .mul (f32ConstOperandProto 0x40000000)
        (.copy ⟨0, []⟩)) emptyMemory [] emptyLayoutTable = .unsupported := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## §8. `.stripProvenance` Characterization & Strengthened `Ptr2IntTransmutePolicy` Theorems -/

/-- Erase pointer provenance from one abstract byte, keeping `.uninit` and the
underlying byte value. -/
def stripAbstractByteProv : AbstractByte → AbstractByte
  | .uninit => .uninit
  | .init b _ => .init b .none

/-- Erase pointer provenance from every byte (`rust-lang/reference#1752`
pointer-to-integer transmute: "the provenance is stripped"). -/
def stripAbstractBytesProv : List AbstractByte → List AbstractByte
  | .nil => .nil
  | b :: rest => stripAbstractByteProv b :: stripAbstractBytesProv rest

theorem abstractBytesHaveProv_stripAbstractBytesProv (bytes : List AbstractByte) :
    abstractBytesHaveProv (stripAbstractBytesProv bytes) = false := by
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | uninit => exact ih
    | init _ _ => exact ih

theorem length_stripAbstractBytesProv (bytes : List AbstractByte) :
    length (stripAbstractBytesProv bytes) = length bytes := by
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
    show (stripAbstractBytesProv rest).length + 1 = rest.length + 1
    exact congrArg Nat.succ ih

theorem stripAbstractBytesProv_idem (bytes : List AbstractByte) :
    stripAbstractBytesProv (stripAbstractBytesProv bytes) = stripAbstractBytesProv bytes := by
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | uninit => exact congrArg (List.cons AbstractByte.uninit) ih
    | init v _ => exact congrArg (List.cons (AbstractByte.init v .none)) ih

/-- Erasing provenance is the identity on provenance-free bytes. -/
theorem stripAbstractBytesProv_of_no_prov (bytes : List AbstractByte)
    (hnp : abstractBytesHaveProv bytes = false) : stripAbstractBytesProv bytes = bytes := by
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | uninit => exact congrArg (List.cons AbstractByte.uninit) (ih hnp)
    | init v prov =>
      cases prov with
      | none => exact congrArg (List.cons (AbstractByte.init v .none)) (ih hnp)
      | some _ => cases hnp

/-- Little-endian decoding of provenance-erased bytes yields the same bit
pattern with no provenance. -/
theorem decodeLittleEndianBytes_stripAbstractBytesProv (bytes : List AbstractByte) :
    decodeLittleEndianBytes (stripAbstractBytesProv bytes) =
      match decodeLittleEndianBytes bytes with
      | .some p => .some (p.1, .none)
      | .none => .none := by
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | uninit => rfl
    | init v prov =>
      simp only [stripAbstractBytesProv, stripAbstractByteProv, decodeLittleEndianBytes]
      rw [ih]
      cases decodeLittleEndianBytes rest with
      | none => rfl
      | some p => cases p; rfl

/-- Scalar decoding of provenance-erased bytes yields the same scalar with no
provenance (and fails on exactly the same `.uninit` / empty inputs). -/
theorem decodeScalarBytes_stripAbstractBytesProv (bytes : List AbstractByte) (signed : Bool) :
    decodeScalarBytes (stripAbstractBytesProv bytes) signed =
      match decodeScalarBytes bytes signed with
      | .some p => .some (p.1, .none)
      | .none => .none := by
  unfold decodeScalarBytes
  dsimp only
  rw [length_stripAbstractBytesProv, decodeLittleEndianBytes_stripAbstractBytesProv]
  cases Nat.beq (length bytes) 0 with
  | true => rfl
  | false =>
    cases decodeLittleEndianBytes bytes with
    | none => rfl
    | some p => cases p; rfl

/-- `true` iff `sl` is a pointer-register scalar layout (whose decoding
preserves intact provenance under both policies). -/
def scalarLayoutIsPointer : ScalarLayout → Bool
  | .initialized (.pointer _) _ => true
  | .union (.pointer _) => true
  | _ => false

/-- **`.stripProvenance` = `.strictUcg630Ub` ∘ provenance erasure** on every
non-pointer `ScalarLayout`: the lenient policy decodes exactly the underlying
byte values (still enforcing initialization, niche `WrappingRange`, and `char`
validity). -/
theorem decodeScalarLayoutBytesWithPolicy_strip_eq_strict_erased
    (sl : ScalarLayout) (bytes : List AbstractByte)
    (hnp : scalarLayoutIsPointer sl = false) :
    decodeScalarLayoutBytesWithPolicy .stripProvenance sl bytes =
      decodeScalarLayoutBytesWithPolicy .strictUcg630Ub sl (stripAbstractBytesProv bytes) := by
  unfold decodeScalarLayoutBytesWithPolicy
  cases scalarLayoutByteWidth sl with
  | none => rfl
  | some sz =>
    dsimp only
    rw [length_stripAbstractBytesProv]
    cases Nat.beq (length bytes) sz with
    | false => rfl
    | true =>
      dsimp only
      cases sl with
      | initialized pk vr =>
        cases pk with
        | pointer _ => cases hnp
        | int _ _ =>
          dsimp only [policyRejectsProv]
          rw [abstractBytesHaveProv_stripAbstractBytesProv,
            decodeScalarBytes_stripAbstractBytesProv]
          cases decodeScalarBytes bytes false with
          | none => rfl
          | some p => rfl
        | float _ =>
          dsimp only [policyRejectsProv]
          rw [abstractBytesHaveProv_stripAbstractBytesProv,
            decodeScalarBytes_stripAbstractBytesProv]
          cases decodeScalarBytes bytes false with
          | none => rfl
          | some p => rfl
      | union pk =>
        cases pk with
        | pointer _ => cases hnp
        | int _ _ =>
          dsimp only [policyRejectsProv]
          rw [abstractBytesHaveProv_stripAbstractBytesProv,
            decodeScalarBytes_stripAbstractBytesProv]
          cases decodeScalarBytes bytes false with
          | none => rfl
          | some p => rfl
        | float _ =>
          dsimp only [policyRejectsProv]
          rw [abstractBytesHaveProv_stripAbstractBytesProv,
            decodeScalarBytes_stripAbstractBytesProv]
          cases decodeScalarBytes bytes false with
          | none => rfl
          | some p => rfl

/-- `Bytes.decodeValueFromBytes` is provenance-oblivious on the non-pointer
scalar kinds `bool`, `char`, `iN`, and `uN`: it reads only byte values. -/
theorem decodeValueFromBytes_scalar_stripAbstractBytesProv
    (fuel : Nat) (layouts : LayoutTable) (kind : RigidTy) (layoutIdx : LayoutIdx)
    (bytes : List AbstractByte)
    (hk : kind = .bool ∨ kind = .char ∨ (∃ w, kind = .int w) ∨ (∃ w, kind = .uint w)) :
    decodeValueFromBytes (.succ fuel) layouts { kind := kind, layoutIdx := layoutIdx }
        (stripAbstractBytesProv bytes) =
      decodeValueFromBytes (.succ fuel) layouts { kind := kind, layoutIdx := layoutIdx }
        bytes := by
  rcases hk with hk | hk | ⟨w, hk⟩ | ⟨w, hk⟩
  · subst hk
    unfold decodeValueFromBytes
    dsimp only
    cases bytes with
    | nil => rfl
    | cons b rest =>
      cases rest with
      | nil => cases b <;> rfl
      | cons b2 rest2 => cases b <;> cases b2 <;> rfl
  · subst hk
    unfold decodeValueFromBytes
    dsimp only
    rw [length_stripAbstractBytesProv, decodeScalarBytes_stripAbstractBytesProv]
    cases Nat.beq (length bytes) 4 with
    | false => rfl
    | true =>
      dsimp only
      cases decodeScalarBytes bytes false with
      | none => rfl
      | some p => cases p; rfl
  · subst hk
    unfold decodeValueFromBytes
    dsimp only
    rw [length_stripAbstractBytesProv, decodeScalarBytes_stripAbstractBytesProv]
    cases intCastTargetBytes (.int w) with
    | none => rfl
    | some expected =>
      dsimp only
      cases Nat.beq (length bytes) expected with
      | false => rfl
      | true =>
        dsimp only
        cases decodeScalarBytes bytes true with
        | none => rfl
        | some p => cases p; rfl
  · subst hk
    unfold decodeValueFromBytes
    dsimp only
    rw [length_stripAbstractBytesProv, decodeScalarBytes_stripAbstractBytesProv]
    cases intCastTargetBytes (.uint w) with
    | none => rfl
    | some expected =>
      dsimp only
      cases Nat.beq (length bytes) expected with
      | false => rfl
      | true =>
        dsimp only
        cases decodeScalarBytes bytes false with
        | none => rfl
        | some p => cases p; rfl

/-- `true` iff `kind` is a non-pointer scalar kind (`bool`, `char`, integer, or
float): exactly the top-level targets whose decoding differs between the two
policies. -/
def isNonPtrScalarKind : RigidTy → Bool
  | .bool | .char | .int _ | .uint _ | .float _ => true
  | _ => false

/-- **Semantic characterization of `.stripProvenance`** on non-pointer scalar
targets (`bool`, `char`, `iN`, `uN`, `fN`): decoding under `.stripProvenance`
is exactly decoding the provenance-erased bytes under `.strictUcg630Ub` (the
current TCB semantics). In particular the lenient policy never invents bits:
it validates and returns the underlying byte values only. -/
theorem decodeTypedValueFromBytesWithPolicy_strip_scalar_eq_strict_erased
    (fuel : Nat) (layouts : LayoutTable) (ty : Ty) (bytes : List AbstractByte)
    (hk : isNonPtrScalarKind ty.kind = true) :
    decodeTypedValueFromBytesWithPolicy .stripProvenance fuel layouts ty bytes =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel layouts ty
        (stripAbstractBytesProv bytes) := by
  cases fuel with
  | zero => rfl
  | succ fuel' =>
    have hcore : ∀ (k : RigidTy) (l : LayoutIdx),
        (k = .bool ∨ k = .char ∨ (∃ w, k = .int w) ∨ (∃ w, k = .uint w)) →
        (match policyRejectsProv .stripProvenance bytes with
          | true => (none : Option Value)
          | false => decodeValueFromBytes (.succ fuel') layouts { kind := k, layoutIdx := l }
              bytes) =
        (match policyRejectsProv .strictUcg630Ub (stripAbstractBytesProv bytes) with
          | true => (none : Option Value)
          | false => decodeValueFromBytes (.succ fuel') layouts { kind := k, layoutIdx := l }
              (stripAbstractBytesProv bytes)) := by
      intro k l hkl
      dsimp only [policyRejectsProv]
      rw [abstractBytesHaveProv_stripAbstractBytesProv]
      exact (decodeValueFromBytes_scalar_stripAbstractBytesProv fuel' layouts k l bytes hkl).symm
    cases ty with
    | mk kind layoutIdx =>
      dsimp only at hk
      cases kind with
      | bool => exact hcore .bool layoutIdx (Or.inl rfl)
      | char => exact hcore .char layoutIdx (Or.inr (Or.inl rfl))
      | int w => exact hcore (.int w) layoutIdx (Or.inr (Or.inr (Or.inl ⟨w, rfl⟩)))
      | uint w => exact hcore (.uint w) layoutIdx (Or.inr (Or.inr (Or.inr ⟨w, rfl⟩)))
      | float fk =>
        cases fk with
        | f16 => exact hcore (.uint .u16) 0 (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))
        | f32 => exact hcore (.uint .u32) 0 (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))
        | f64 => exact hcore (.uint .u64) 0 (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))
        | f128 => exact hcore (.uint .u128) 0 (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))
      | _ => cases hk

/-- The two policies can only disagree on bytes that carry pointer provenance. -/
theorem decodeTypedValueFromBytesWithPolicy_policies_differ_imp_prov
    (fuel : Nat) (layouts : LayoutTable) (ty : Ty) (bytes : List AbstractByte)
    (hne : decodeTypedValueFromBytesWithPolicy .stripProvenance fuel layouts ty bytes ≠
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel layouts ty bytes) :
    abstractBytesHaveProv bytes = true := by
  cases hp : abstractBytesHaveProv bytes with
  | true => rfl
  | false =>
    exact absurd
      (decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov fuel layouts ty bytes hp)
      hne

/-- Exact shape of the policy split at the decoder: the two policies agree
unless the strict policy rejects (`.none`). -/
theorem decodeTypedValueFromBytesWithPolicy_strip_eq_strict_or_strict_none
    (fuel : Nat) (layouts : LayoutTable) (ty : Ty) (bytes : List AbstractByte) :
    decodeTypedValueFromBytesWithPolicy .stripProvenance fuel layouts ty bytes =
        decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel layouts ty bytes ∨
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel layouts ty bytes = .none := by
  cases hs : decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel layouts ty bytes with
  | none => exact Or.inr rfl
  | some v =>
    exact Or.inl
      (decodeTypedValueFromBytesWithPolicy_strict_refines_strip fuel layouts ty bytes v hs)

/-- Exact shape of the policy split at `transmute` / `subtype` casts: the two
policies return the identical `RvalueEvalResult` (including `.unsupported`)
unless the strict policy reports `.ub`. Hence flipping `.strictUcg630Ub` to
`.stripProvenance` can only turn UB into defined behavior, never the reverse. -/
theorem evalByteCastWithPolicy_strip_eq_strict_or_strict_ub
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalByteCastWithPolicy .stripProvenance locals op targetTy mem localDecls layouts =
        evalByteCastWithPolicy .strictUcg630Ub locals op targetTy mem localDecls layouts ∨
      evalByteCastWithPolicy .strictUcg630Ub locals op targetTy mem localDecls layouts = .ub := by
  unfold evalByteCastWithPolicy
  cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack with
  | ub => exact Or.inl rfl
  | unsupported => exact Or.inl rfl
  | ok v locals' =>
    dsimp only
    cases tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts targetTy) with
    | none => exact Or.inl rfl
    | some dstSize =>
      dsimp only
      cases operandTy localDecls layouts op with
      | none =>
        dsimp only
        cases encodeUntypedValueToBytes defaultCodecFuel v with
        | none => exact Or.inl rfl
        | some bs =>
          dsimp only
          cases Nat.beq (length bs) dstSize with
          | false => exact Or.inl rfl
          | true =>
            dsimp only
            rcases decodeTypedValueFromBytesWithPolicy_strip_eq_strict_or_strict_none
              defaultCodecFuel layouts (resolveTyWithLocalDecls localDecls layouts targetTy) bs
              with heq | hnone
            · rw [heq]; exact Or.inl rfl
            · rw [hnone]; exact Or.inr rfl
      | some srcTy =>
        dsimp only
        cases tyByteSize localDecls layouts
            (resolveTyWithLocalDecls localDecls layouts srcTy) with
        | none => exact Or.inl rfl
        | some srcSize =>
          dsimp only
          cases Nat.beq srcSize dstSize with
          | false => exact Or.inl rfl
          | true =>
            dsimp only
            cases encodeByteCastSourceBytes layouts
                (resolveTyWithLocalDecls localDecls layouts srcTy) v with
            | none => exact Or.inl rfl
            | some bs =>
              dsimp only
              cases Nat.beq (length bs) dstSize with
              | false => exact Or.inl rfl
              | true =>
                dsimp only
                rcases decodeTypedValueFromBytesWithPolicy_strip_eq_strict_or_strict_none
                  defaultCodecFuel layouts
                  (resolveTyWithLocalDecls localDecls layouts targetTy) bs with heq | hnone
                · rw [heq]; exact Or.inl rfl
                · rw [hnone]; exact Or.inr rfl

/-- Cast-level congruence: any target type on which the decoder is
policy-independent yields a policy-independent `transmute` / `subtype` cast. -/
theorem evalByteCastWithPolicy_policy_indep_of_decode_indep
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h : ∀ bs,
      decodeTypedValueFromBytesWithPolicy .stripProvenance defaultCodecFuel layouts
          (resolveTyWithLocalDecls localDecls layouts targetTy) bs =
        decodeTypedValueFromBytesWithPolicy .strictUcg630Ub defaultCodecFuel layouts
          (resolveTyWithLocalDecls localDecls layouts targetTy) bs) :
    evalByteCastWithPolicy .stripProvenance locals op targetTy mem localDecls layouts =
      evalByteCastWithPolicy .strictUcg630Ub locals op targetTy mem localDecls layouts := by
  have hf : decodeTypedValueFromBytesWithPolicy .stripProvenance defaultCodecFuel layouts
        (resolveTyWithLocalDecls localDecls layouts targetTy) =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub defaultCodecFuel layouts
        (resolveTyWithLocalDecls localDecls layouts targetTy) := funext h
  unfold evalByteCastWithPolicy
  simp only [hf]

/-- Pointer-to-pointer transmutes are policy-independent in full generality:
every `transmute` / `subtype` cast whose (resolved) target is a thin raw
pointer evaluates identically under both policies, for every operand, memory,
and layout table. -/
theorem evalByteCastWithPolicy_thinRawPtr_policy_indep
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (hk : (resolveTyWithLocalDecls localDecls layouts targetTy).kind = .rawPtr m pointee)
    (hthin : isThinPtrKind (.rawPtr m pointee) = true) :
    evalByteCastWithPolicy .stripProvenance locals op targetTy mem localDecls layouts =
      evalByteCastWithPolicy .strictUcg630Ub locals op targetTy mem localDecls layouts := by
  apply evalByteCastWithPolicy_policy_indep_of_decode_indep
  intro bs
  generalize resolveTyWithLocalDecls localDecls layouts targetTy = rT at hk
  cases rT with
  | mk k l =>
    dsimp only at hk
    subst hk
    exact decodeTypedValueFromBytesWithPolicy_thinRawPtr_policy_indep 15 layouts m pointee l bs
      hthin

/-- `dyn` wide references decode identically under both policies (reference
counterpart of `decodeTypedValueFromBytesWithPolicy_wideDynPtr_policy_indep`). -/
theorem decodeTypedValueFromBytesWithPolicy_wideDynRef_policy_indep
    (fuel : Nat) (layouts : LayoutTable) (m : Mutability) (traitPath : DefPath)
    (layoutIdx : LayoutIdx) (bytes : List AbstractByte) :
    decodeTypedValueFromBytesWithPolicy .stripProvenance (.succ fuel) layouts
        { kind := .ref m (.dynamic traitPath), layoutIdx := layoutIdx } bytes =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub (.succ fuel) layouts
        { kind := .ref m (.dynamic traitPath), layoutIdx := layoutIdx } bytes := by
  unfold decodeTypedValueFromBytesWithPolicy decodePtrBytesNoForgeWithPolicy
  dsimp only [normalizeCodecTy]
  cases Nat.beq (length bytes)
      (Nat.add (layoutPointerBytes layouts) (layoutPointerBytes layouts)) with
  | false => rfl
  | true =>
    dsimp only
    cases decodeScalarBytes (dropAbstractBytes (layoutPointerBytes layouts) bytes) false with
    | none => rfl
    | some mp =>
      dsimp only
      cases abstractBytesUniformProv (dropAbstractBytes (layoutPointerBytes layouts) bytes) <;>
        cases mp.2 <;> rfl

/-- Arrays of union elements (e.g. `[MaybeUninit<u8>; N]`) decode identically
under both policies for every byte image, preserving raw provenance overlays. -/
theorem decodeTypedValueFromBytesWithPolicy_unionArray_policy_indep
    (fuel : Nat) (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (n : Nat)
    (layoutIdx elemFlIdx : LayoutIdx) (arrL elemL : TypeLayout) (stride : Size)
    (cnt count : Nat) (restFl : List LayoutIdx) (bytes : List AbstractByte)
    (harr : LayoutTable.lookup layouts layoutIdx = .some arrL)
    (hfields : arrL.fields = .array stride cnt)
    (hfl : arrL.fieldLayouts = elemFlIdx :: restFl)
    (helem : LayoutTable.lookup layouts elemFlIdx = .some elemL)
    (hvar : elemL.variants = .single 0) (hfld : elemL.fields = .union count) :
    decodeTypedValueFromBytesWithPolicy .stripProvenance (.succ (.succ fuel)) layouts
        { kind := .array (.adt defPath args) n, layoutIdx := layoutIdx } bytes =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub (.succ (.succ fuel)) layouts
        { kind := .array (.adt defPath args) n, layoutIdx := layoutIdx } bytes := by
  have hf : decodeTypedValueFromBytesWithPolicy .stripProvenance (.succ fuel) layouts
        { kind := .adt defPath args, layoutIdx := elemFlIdx } =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub (.succ fuel) layouts
        { kind := .adt defPath args, layoutIdx := elemFlIdx } :=
    funext fun bs =>
      decodeTypedValueFromBytesWithPolicy_union_policy_indep fuel layouts defPath args elemFlIdx
        elemL count bs helem hvar hfld
  cases arrL with
  | mk size align backendRepr fields variants isUninhabited fieldLayouts =>
    dsimp only at hfields hfl
    subst hfields
    subst hfl
    unfold decodeTypedValueFromBytesWithPolicy
    dsimp only [normalizeCodecTy]
    rw [harr]
    dsimp only
    rw [hf]

/-- No provenance forgery for **every** reference target (thin `&T` as well as
wide `&[T]`, `&str`, and `&dyn Trait`) under both policies: provenance-free
bytes never decode to a reference. -/
theorem decodeTypedValueFromBytesWithPolicy_no_forge_ref
    (policy : Ptr2IntTransmutePolicy) (fuel : Nat) (layouts : LayoutTable)
    (m : Mutability) (pointee : RigidTy) (layoutIdx : LayoutIdx) (bytes : List AbstractByte)
    (hnp : abstractBytesHaveProv bytes = false) :
    decodeTypedValueFromBytesWithPolicy policy (.succ fuel) layouts
        { kind := .ref m pointee, layoutIdx := layoutIdx } bytes = .none := by
  unfold decodeTypedValueFromBytesWithPolicy decodePtrBytesNoForgeWithPolicy
  dsimp only [normalizeCodecTy]
  cases pointee with
  | slice _ | str | dynamic _ =>
    dsimp only
    cases Nat.beq (length bytes)
        (Nat.add (layoutPointerBytes layouts) (layoutPointerBytes layouts)) with
    | false => rfl
    | true =>
      dsimp only
      cases Nat.beq (length (takeAbstractBytes (layoutPointerBytes layouts) bytes))
          (layoutPointerBytes layouts) with
      | false => rfl
      | true =>
        cases decodeScalarBytes (takeAbstractBytes (layoutPointerBytes layouts) bytes) false with
        | none => rfl
        | some p =>
          dsimp only
          rw [abstractBytesUniformProv_false_of_no_prov _
            (abstractBytesHaveProv_take (layoutPointerBytes layouts) bytes hnp)]
  | _ =>
    dsimp only
    cases Nat.beq (length bytes) (layoutPointerBytes layouts) with
    | false => rfl
    | true =>
      cases decodeScalarBytes bytes false with
      | none => rfl
      | some p => rw [abstractBytesUniformProv_false_of_no_prov bytes hnp]

/-- Intrinsic no-forgery for thin raw pointers under both policies: a decoded
`Value.ptr` can only come from an intact (uniform-provenance) pointer image,
and its allocation and address are exactly the byte provenance and the decoded
little-endian bits. -/
theorem decodeTypedValueFromBytesWithPolicy_thinRawPtr_ptr_imp_uniformProv
    (policy : Ptr2IntTransmutePolicy) (fuel : Nat) (layouts : LayoutTable)
    (m : Mutability) (pointee : RigidTy) (layoutIdx : LayoutIdx) (bytes : List AbstractByte)
    (p : ProvenancePtr) (sz : Nat)
    (hthin : isThinPtrKind (.rawPtr m pointee) = true)
    (hdec : decodeTypedValueFromBytesWithPolicy policy (.succ fuel) layouts
      { kind := .rawPtr m pointee, layoutIdx := layoutIdx } bytes = .some (.ptr p sz)) :
    abstractBytesUniformProv bytes = true ∧
      ∃ q ap, decodeScalarBytes bytes false = .some q ∧ q.2 = .some ap ∧
        p = { allocId := ap.1, offsetBytes := q.1.bits } ∧ sz = layoutPointerBytes layouts := by
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
      | some q =>
        rw [hsc] at hdec
        dsimp only at hdec
        cases hu : abstractBytesUniformProv bytes with
        | false => rw [hu] at hdec; cases hdec
        | true =>
          rw [hu] at hdec
          cases hq2 : q.2 with
          | none => rw [hq2] at hdec; cases hdec
          | some ap =>
            rw [hq2] at hdec
            injection hdec with hv
            injection hv with hp hsz
            exact ⟨rfl, q, ap, rfl, hq2, hp.symm, hsz.symm⟩

/-! ### §8.1 Kernel-Checked TCB Finding: Multi-Variant Enums Leak `.stripProvenance` Semantics -/

/-- `enum E { A(u32), B(u32) }`: `u32` tag at offset `0`, `u32` payload at
offset `4` in both variants. -/
def protoTwoVariantEnumLayout : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 4 }
  backendRepr := .memory
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .multiple (.initialized (.int 32 false) ⟨0, 1⟩) 0
    [.arbitrary [{ bytes := 4 }] [0], .arbitrary [{ bytes := 4 }] [0]]
  isUninhabited := false
}

def protoEnumLayouts : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries := [protoUnitLayout, protoTwoVariantEnumLayout]
}

def protoTwoVariantEnumTy : Ty := { kind := .adt "E" [], layoutIdx := 1 }

/-- A pointer whose little-endian address bytes spell enum tag `1` (low four
bytes) and payload `42` (high four bytes). -/
def protoEnumShapedPtr : ProvenancePtr := { allocId := 7, offsetBytes := 0x0000002A00000001 }

def protoEnumDecls : List LocalDecl := [
  { mutability := .not, ty := protoConstU8PtrTy, debugName := none }
]

def protoEnumLocals : List LocalSlot := [.init (.ptr protoEnumShapedPtr 8)]

/-- **TCB finding (kernel-checked, `by rfl`)**: the current trusted byte
reinterpretation is *not* uniformly `ucg#630`-strict. For a multi-variant enum
target, `Places.decodeTypedValueFromBytes` falls back to the
provenance-oblivious `Bytes.decodeValueFromBytes` (tag via
`decodeScalarLayoutBytes`, payload via `decodeFieldsBySpan`), so
`transmute::<*const u8, E>(p)` succeeds — silently stripping pointer provenance
into the integer tag and payload — under the trusted `evalByteCast` and hence
under `.strictUcg630Ub` (which reproduces the TCB exactly), whereas the very
same provenance-carrying bytes are rejected at the plain integer aggregate
`(u32, u32)`. The TCB patch must thread `policyRejectsProv` through the
`.multiple`-variant tag and payload decoding. -/
theorem trusted_evalByteCast_multiVariant_enum_strict_leak_witness :
    abstractBytesHaveProv
        (encodeLittleEndianBytes protoEnumShapedPtr.offsetBytes 8 (.some (7, 7))) = true ∧
    decodeTypedValueFromBytes 4 protoEnumLayouts protoTwoVariantEnumTy
        (encodeLittleEndianBytes protoEnumShapedPtr.offsetBytes 8 (.some (7, 7))) =
      .some (.aggregate 1 [.scalar ⟨42, 4⟩]) ∧
    evalByteCast protoEnumLocals (.copy ⟨0, []⟩) protoTwoVariantEnumTy emptyMemory
        protoEnumDecls protoEnumLayouts =
      .ok (.aggregate 1 [.scalar ⟨42, 4⟩]) protoEnumLocals emptyMemory ∧
    evalByteCastWithPolicy .strictUcg630Ub protoEnumLocals (.copy ⟨0, []⟩)
        protoTwoVariantEnumTy emptyMemory protoEnumDecls protoEnumLayouts =
      .ok (.aggregate 1 [.scalar ⟨42, 4⟩]) protoEnumLocals emptyMemory ∧
    evalByteCastWithPolicy .stripProvenance protoEnumLocals (.copy ⟨0, []⟩)
        protoTwoVariantEnumTy emptyMemory protoEnumDecls protoEnumLayouts =
      .ok (.aggregate 1 [.scalar ⟨42, 4⟩]) protoEnumLocals emptyMemory ∧
    evalByteCast protoEnumLocals (.copy ⟨0, []⟩)
        { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 0 } emptyMemory
        protoEnumDecls protoEnumLayouts = .ub := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §9. Correct Rounding of `add`/`sub`, Gradual Underflow, Exact IEEE-754 `rem`, Cross-Format `miri#5643` NaN Rules & Relational Dispatcher Specs -/

/-- Bitwise IEEE-754 absolute value: clears the sign bit (`f.width - 1`) on
canonical `bits % 2 ^ f.width`. -/
def evalFloatAbsProto (f : IeeeFormat) (bits : Nat) : Nat :=
  let c := bits % 2 ^ f.width
  let signBit := 2 ^ (f.width - 1)
  if c < signBit then c else c - signBit

theorem evalFloatAbsProto_lt (f : IeeeFormat) (bits : Nat) :
    evalFloatAbsProto f bits < 2 ^ f.width := by
  unfold evalFloatAbsProto
  dsimp only
  have hsplit := (ieeeFormat_width_split f).1
  have hmod : bits % 2 ^ f.width < 2 ^ f.width := Nat.mod_lt _ (Nat.two_pow_pos _)
  split <;> omega

theorem decodeBits_evalFloatAbsProto (f : IeeeFormat) (bits : Nat) :
    decodeBits f (evalFloatAbsProto f bits) =
      match decodeBits f bits with
      | .zero _ => .zero false
      | .finite _ n d => .finite false n d
      | .inf _ => .inf false
      | .nan _ q p => .nan false q p := by
  have hmod := decodeBits_mod_width f bits
  rw [← hmod]
  have hc : bits % 2 ^ f.width < 2 ^ f.width := Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold evalFloatAbsProto
  dsimp only
  generalize bits % 2 ^ f.width = c at hc ⊢
  have hsplit := (ieeeFormat_width_split f).1
  by_cases hlt : c < 2 ^ (f.width - 1)
  · rw [if_pos' hlt]
    have hneg_false : (unpackBits f c).neg = false := by
      unfold unpackBits
      dsimp only
      have hdiv0 : c / 2 ^ (f.width - 1) = 0 := Nat.div_eq_of_lt hlt
      rw [hdiv0]
      rfl
    unfold decodeBits
    dsimp only
    rw [hneg_false]
    split
    · split <;> rfl
    · split
      · split <;> rfl
      · rfl
  · rw [if_neg' hlt]
    have hneg_eq : c - 2 ^ (f.width - 1) = evalFloatNegProto f c := by
      unfold evalFloatNegProto
      dsimp only
      rw [Nat.mod_eq_of_lt hc, if_neg' hlt]
    have hneg_true : (unpackBits f c).neg = true := by
      unfold unpackBits
      dsimp only
      have hge : 2 ^ (f.width - 1) ≤ c := Nat.le_of_not_lt hlt
      have hsub_lt : c - 2 ^ (f.width - 1) < 2 ^ (f.width - 1) := by omega
      have hdiv1 : c / 2 ^ (f.width - 1) = 1 := by
        have heq : c = (c - 2 ^ (f.width - 1)) + 2 ^ (f.width - 1) := by omega
        conv => lhs; rw [heq]
        rw [Nat.add_div_right _ (ieeeFormat_width_split f).2.2.2.1, Nat.div_eq_of_lt hsub_lt]
      rw [hdiv1]
      rfl
    rw [hneg_eq, decodeBits_evalFloatNegProto]
    have hneg_dec : floatKindNeg (decodeBits f c) = true := by
      rw [floatKindNeg_decodeBits, hneg_true]
    cases hd : decodeBits f c with
    | zero s => rw [hd] at hneg_dec; dsimp only [floatKindNeg] at hneg_dec; subst hneg_dec; rfl
    | finite s _ _ => rw [hd] at hneg_dec; dsimp only [floatKindNeg] at hneg_dec; subst hneg_dec; rfl
    | inf s => rw [hd] at hneg_dec; dsimp only [floatKindNeg] at hneg_dec; subst hneg_dec; rfl
    | nan s _ _ => rw [hd] at hneg_dec; dsimp only [floatKindNeg] at hneg_dec; subst hneg_dec; rfl

/-! ### §9.1 Correct Rounding of Finite `add` and `sub` -/

/-- Correct rounding of finite sums with nonzero exact rational value:
within half a unit in the last place of the working binade, exact ties
resolved to an even significand, and decoding to the exact rounded value
unless it overflows to `±Inf`. -/
theorem evalFloatArithBaseProto_add_finite_correctly_rounded (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite ln lnum lden) (hr : decodeBits f b = .finite rn rnum rden)
    (hnz : signedNum ln lnum * Int.ofNat rden + signedNum rn rnum * Int.ofNat lden ≠ 0) :
    let sumInt := signedNum ln lnum * Int.ofNat rden + signedNum rn rnum * Int.ofNat lden
    let sign := decide (sumInt < 0)
    let n := sumInt.natAbs
    let d := lden * rden
    let exponent := max (ratioExponent n d) f.minExponent
    let scaled := powScale n d ((f.fractionBits : Int) - exponent)
    let sig := roundQuotientTiesToEven scaled.1 scaled.2
    2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs ≤ scaled.2 ∧
      (2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs = scaled.2 →
        sig % 2 = 0) ∧
      (decodeBits f (evalFloatArithBaseProto .add f a b) ≠ .inf sign →
        floatKindSameValue (decodeBits f (evalFloatArithBaseProto .add f a b))
          (if sig = 0 then .zero sign
           else .finite sign (powScale sig 1 (exponent - f.fractionBits)).1
             (powScale sig 1 (exponent - f.fractionBits)).2)) := by
  rw [evalFloatArithBaseProto_add_finite f a b ln rn lnum lden rnum rden hl hr]
  exact roundRatioTiesToEven_float_half_ulp f _ _ _
    (Int.natAbs_pos.mpr hnz)
    (Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden hl)
      (decodeBits_finite_den_pos f b rn rnum rden hr))

/-- Correct rounding of finite differences with nonzero exact rational value. -/
theorem evalFloatArithBaseProto_sub_finite_correctly_rounded (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite ln lnum lden) (hr : decodeBits f b = .finite rn rnum rden)
    (hnz : signedNum ln lnum * Int.ofNat rden - signedNum rn rnum * Int.ofNat lden ≠ 0) :
    let diffInt := signedNum ln lnum * Int.ofNat rden - signedNum rn rnum * Int.ofNat lden
    let sign := decide (diffInt < 0)
    let n := diffInt.natAbs
    let d := lden * rden
    let exponent := max (ratioExponent n d) f.minExponent
    let scaled := powScale n d ((f.fractionBits : Int) - exponent)
    let sig := roundQuotientTiesToEven scaled.1 scaled.2
    2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs ≤ scaled.2 ∧
      (2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs = scaled.2 →
        sig % 2 = 0) ∧
      (decodeBits f (evalFloatArithBaseProto .sub f a b) ≠ .inf sign →
        floatKindSameValue (decodeBits f (evalFloatArithBaseProto .sub f a b))
          (if sig = 0 then .zero sign
           else .finite sign (powScale sig 1 (exponent - f.fractionBits)).1
             (powScale sig 1 (exponent - f.fractionBits)).2)) := by
  rw [evalFloatArithBaseProto_sub_finite f a b ln rn lnum lden rnum rden hl hr]
  exact roundRatioTiesToEven_float_half_ulp f _ _ _
    (Int.natAbs_pos.mpr hnz)
    (Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden hl)
      (decodeBits_finite_den_pos f b rn rnum rden hr))

/-! ### §9.2 Dyadic Representation, Exact IEEE-754 `rem` & Gradual Underflow -/

/-- Every finite decoded IEEE-754 value is a dyadic rational `m * 2^t` with
`0 < m < 2^(fb+1)`, `minExponent - fb ≤ t ≤ maxExponent - fb`, and either
subnormal (`t = minExponent - fb`) or normal (`2^fb ≤ m`). -/
theorem decodeBits_finite_dyadic (f : IeeeFormat) (bits : Nat) (neg : Bool) (n d : Nat)
    (h : decodeBits f bits = .finite neg n d) :
    ∃ (m : Nat) (t : Int),
      0 < m ∧ m < 2 ^ (f.fractionBits + 1) ∧
      f.minExponent - (f.fractionBits : Int) ≤ t ∧
      t ≤ f.maxExponent - (f.fractionBits : Int) ∧
      (t = f.minExponent - (f.fractionBits : Int) ∨ 2 ^ f.fractionBits ≤ m) ∧
      n = (powScale m 1 t).1 ∧ d = (powScale m 1 t).2 := by
  have hE_lt := unpackBits_exponent_lt f bits
  have hF_lt := unpackBits_fraction_lt f bits
  have htwo : 2 ^ (f.fractionBits + 1) = 2 * 2 ^ f.fractionBits := by
    rw [Nat.pow_succ]; omega
  have hbias := IeeeFormat.two_bias_lt f
  unfold decodeBits at h
  dsimp only at h
  by_cases hEmax : (unpackBits f bits).exponent = 2 ^ f.exponentBits - 1
  · rw [if_pos' hEmax] at h
    split at h <;> cases h
  · rw [if_neg' hEmax] at h
    by_cases hE0 : (unpackBits f bits).exponent = 0
    · rw [if_pos' hE0] at h
      by_cases hF0 : (unpackBits f bits).fraction = 0
      · rw [if_pos' hF0] at h; cases h
      · rw [if_neg' hF0] at h
        injection h with _ hn hd
        refine ⟨(unpackBits f bits).fraction, f.minExponent - (f.fractionBits : Int),
          Nat.pos_of_ne_zero hF0, by omega, Int.le_refl _, ?_, Or.inl rfl, hn.symm, hd.symm⟩
        cases f <;> decide
    · rw [if_neg' hE0] at h
      injection h with _ hn hd
      have hmin_le : f.minExponent - (f.fractionBits : Int) ≤
          ((unpackBits f bits).exponent : Int) - f.bias - f.fractionBits := by
        simp only [IeeeFormat.minExponent]; omega
      have hmax_le : ((unpackBits f bits).exponent : Int) - f.bias - f.fractionBits ≤
          f.maxExponent - (f.fractionBits : Int) := by
        simp only [IeeeFormat.maxExponent]
        have hEmax_eq : 2 ^ f.exponentBits - 1 = 2 * f.bias + 1 := by cases f <;> decide
        omega
      refine ⟨2 ^ f.fractionBits + (unpackBits f bits).fraction,
        ((unpackBits f bits).exponent : Int) - f.bias - f.fractionBits,
        Nat.add_pos_left (Nat.two_pow_pos _) _, by omega, hmin_le, hmax_le,
        Or.inr (Nat.le_add_right _ _), hn.symm, hd.symm⟩

/-- Every representable positive dyadic rational `m * 2^t` (`0 < m < 2^(fb+1)`,
`minExponent - fb ≤ t ≤ maxExponent - fb`) is encoded **exactly** (zero
rounding error, never overflowing to `±Inf`) by `roundRatioTiesToEven`. -/
theorem roundRatioTiesToEven_exact_dyadic (f : IeeeFormat) (neg : Bool) (m : Nat) (t : Int)
    (hm0 : 0 < m) (hm_lt : m < 2 ^ (f.fractionBits + 1))
    (ht_lo : f.minExponent - (f.fractionBits : Int) ≤ t)
    (ht_hi : t ≤ f.maxExponent - (f.fractionBits : Int)) :
    ∃ rN rD,
      decodeBits f (roundRatioTiesToEven f neg (powScale m 1 t).1 (powScale m 1 t).2) =
        .finite neg rN rD ∧
      rN * (powScale m 1 t).2 = (powScale m 1 t).1 * rD ∧
      0 < rD := by
  have hL1 := Nat.log2_self_le (Nat.pos_iff_ne_zero.mp hm0)
  have hL2 := Nat.lt_log2_self (n := m)
  generalize hLv : Nat.log2 m = L at hL1 hL2
  have hLfb : L ≤ f.fractionBits := by
    have := (Nat.log2_lt (Nat.pos_iff_ne_zero.mp hm0)).mpr hm_lt
    omega
  rw [← roundRatioBits_tiesToEven]
  by_cases hnorm : f.minExponent ≤ t + (L : Int)
  · -- Normal case: shift significand left by `j = fb - L` so `2^fb ≤ m * 2^j < 2^(fb+1)`
    let j := f.fractionBits - L
    have hS1 : 2 ^ f.fractionBits ≤ m * 2 ^ j := by
      have hmul := Nat.mul_le_mul_right (2 ^ j) hL1
      rw [← Nat.pow_add, Nat.add_sub_cancel' hLfb] at hmul
      exact hmul
    have hS2 : m * 2 ^ j < 2 ^ (f.fractionBits + 1) := by
      have hmul := Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos j)
      rw [← Nat.pow_add, show L + 1 + j = f.fractionBits + 1 by omega] at hmul
      exact hmul
    have hcross := powScale_shift_cross m j t
    have hcong : roundRatioBits .tiesToEven f neg (powScale m 1 t).1 (powScale m 1 t).2 =
        roundRatioBits .tiesToEven f neg (powScale (m * 2 ^ j) 1 (t - (j : Int))).1
          (powScale (m * 2 ^ j) 1 (t - (j : Int))).2 :=
      roundRatioBits_congr .tiesToEven f neg _ _ _ _ (powScale_snd_pos m t)
        (powScale_snd_pos _ _) hcross.symm
    have hE1 : f.minExponent ≤ (t - (j : Int)) + f.fractionBits := by omega
    have hE2 : (t - (j : Int)) + f.fractionBits ≤ f.maxExponent := by omega
    rw [hcong, decodeBits_roundRatio_normal .tiesToEven f neg (m * 2 ^ j) (t - (j : Int))
      hS1 hS2 hE1 hE2]
    exact ⟨_, _, rfl, hcross, powScale_snd_pos _ _⟩
  · -- Subnormal case: shift significand left by `k = (t - (minExp - fb)).toNat` so `0 < m * 2^k < 2^fb`
    let k := (t - (f.minExponent - (f.fractionBits : Int))).toNat
    have hk_eq : (k : Int) = t - (f.minExponent - (f.fractionBits : Int)) :=
      Int.toNat_of_nonneg (by omega)
    have ht_sub : t - (k : Int) = f.minExponent - (f.fractionBits : Int) := by omega
    have hS0 : 0 < m * 2 ^ k := Nat.mul_pos hm0 (Nat.two_pow_pos k)
    have hS_lt : m * 2 ^ k < 2 ^ f.fractionBits := by
      have hLk : L + 1 + k ≤ f.fractionBits := by omega
      have hmul := Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos k)
      rw [← Nat.pow_add] at hmul
      have hpow_le : 2 ^ (L + 1 + k) ≤ 2 ^ f.fractionBits := Nat.pow_le_pow_right (by decide) hLk
      omega
    have hcross := powScale_shift_cross m k t
    rw [ht_sub] at hcross
    have hcong : roundRatioBits .tiesToEven f neg (powScale m 1 t).1 (powScale m 1 t).2 =
        roundRatioBits .tiesToEven f neg
          (powScale (m * 2 ^ k) 1 (f.minExponent - f.fractionBits)).1
          (powScale (m * 2 ^ k) 1 (f.minExponent - f.fractionBits)).2 :=
      roundRatioBits_congr .tiesToEven f neg _ _ _ _ (powScale_snd_pos m t)
        (powScale_snd_pos _ _) hcross.symm
    rw [hcong, decodeBits_roundRatio_subnormal .tiesToEven f neg (m * 2 ^ k) hS0 hS_lt]
    exact ⟨_, _, rfl, hcross, powScale_snd_pos _ _⟩

/-- Helper: `(a * 2^k) * 2^t` equals `a * 2^(t + k)` in cross-multiplication form. -/
private theorem powScale_add_nat_cross (m k : Nat) (t : Int) :
    (powScale (m * 2 ^ k) 1 t).1 * (powScale m 1 (t + (k : Int))).2 =
      (powScale m 1 (t + (k : Int))).1 * (powScale (m * 2 ^ k) 1 t).2 := by
  have h := powScale_shift_cross m k (t + (k : Int))
  have hsub : t + (k : Int) - (k : Int) = t := by omega
  rw [hsub] at h
  exact h

/-- Constructive cancellation for `a * c < b * c → a < b` (avoids stdlib
`Nat.lt_of_mul_lt_mul_right` which pulls in `Classical.choice`). -/
private theorem nat_lt_of_mul_lt_mul_right {a b c : Nat} (h : a * c < b * c) : a < b :=
  match Nat.lt_or_ge a b with
  | .inl hlt => hlt
  | .inr hge => absurd (Nat.mul_le_mul_right c hge) (Nat.not_le_of_lt h)

/-- **Exactness of IEEE-754 truncated remainder (`rem` / `%` / C `fmod`)**:
for every pair of finite nonzero `f32`/`f64` operands `a` and `b`,
`evalFloatArithBaseProto .rem f a b` **never overflows and incurs zero rounding
error**:
- if `(lnum * rden) % (lden * rnum) = 0`, it equals `zeroBits f ln`;
- otherwise it decodes to `.finite ln remN remD` whose exact rational value
  equals `((lnum * rden) % (lden * rnum)) / (lden * rden)`! -/
theorem evalFloatArithBaseProto_rem_finite_exact (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite ln lnum lden) (hr : decodeBits f b = .finite rn rnum rden) :
    let remNum := (lnum * rden) % (lden * rnum)
    (remNum = 0 → evalFloatArithBaseProto .rem f a b = zeroBits f ln) ∧
    (0 < remNum →
      ∃ remN remD,
        decodeBits f (evalFloatArithBaseProto .rem f a b) = .finite ln remN remD ∧
        remN * (lden * rden) = remNum * remD ∧
        0 < remD) := by
  have hrem := (evalFloatArithBaseProto_rem_finite f a b ln rn lnum lden rnum rden hl hr).1
  have hlden_pos := decodeBits_finite_den_pos f a ln lnum lden hl
  have hrden_pos := decodeBits_finite_den_pos f b rn rnum rden hr
  have hlnum_pos := decodeBits_finite_num_pos f a ln lnum lden hl
  have hrnum_pos := decodeBits_finite_num_pos f b rn rnum rden hr
  have hden_pos : 0 < lden * rden := Nat.mul_pos hlden_pos hrden_pos
  dsimp only
  constructor
  · intro h0
    rw [hrem, h0]
    unfold roundRatioTiesToEven
    have hne : ¬ (lden * rden = 0) := Nat.ne_of_gt hden_pos
    rw [if_neg' hne, if_pos' rfl]
  · intro hpos
    rw [hrem]
    obtain ⟨ma, ta, hma0, hma_lt, hta_lo, hta_hi, _, hl1, hl2⟩ :=
      decodeBits_finite_dyadic f a ln lnum lden hl
    obtain ⟨mb, tb, hmb0, hmb_lt, htb_lo, htb_hi, htb_norm, hr1, hr2⟩ :=
      decodeBits_finite_dyadic f b rn rnum rden hr
    by_cases hlt_ab : lnum * rden < lden * rnum
    · -- `|a| < |b|`, so remainder is `|a|` itself
      have hmod_eq : (lnum * rden) % (lden * rnum) = lnum * rden := Nat.mod_eq_of_lt hlt_ab
      rw [hmod_eq]
      have hcong : roundRatioTiesToEven f ln (lnum * rden) (lden * rden) =
          roundRatioTiesToEven f ln (powScale ma 1 ta).1 (powScale ma 1 ta).2 := by
        rw [← roundRatioBits_tiesToEven, ← roundRatioBits_tiesToEven]
        apply roundRatioBits_congr .tiesToEven f ln _ _ _ _ hden_pos (powScale_snd_pos ma ta)
        rw [← hl1, ← hl2, Nat.mul_right_comm, Nat.mul_assoc]
      rw [hcong]
      obtain ⟨remN, remD, hdec, hcross, hDpos⟩ :=
        roundRatioTiesToEven_exact_dyadic f ln ma ta hma0 hma_lt hta_lo hta_hi
      refine ⟨remN, remD, hdec, ?_, hDpos⟩
      rw [← hl1, ← hl2] at hcross
      have hmul := congrArg (· * rden) hcross
      rw [Nat.mul_assoc, Nat.mul_right_comm lnum remD rden] at hmul
      exact hmul
    · -- `|b| ≤ |a|`, so `tb ≤ ta`
      have hge_ab : lden * rnum ≤ lnum * rden := Nat.le_of_not_lt hlt_ab
      have htb_le_ta : tb ≤ ta := by
        rcases htb_norm with rfl | hmb_ge
        · exact hta_lo
        · by_cases hle : tb ≤ ta
          · exact hle
          · exfalso
            have hta_lt_tb : ta < tb := by omega
            let j := (tb - ta).toNat
            have hj_pos : 1 ≤ j := by omega
            have htb_eq : tb = ta + (j : Int) := by omega
            have hcross_b := powScale_add_nat_cross mb j ta
            rw [← htb_eq, ← hr1, ← hr2] at hcross_b
            have hcmp_cross : lnum * rden * (powScale (mb * 2 ^ j) 1 ta).2 <
                lden * rnum * (powScale (mb * 2 ^ j) 1 ta).2 := by
              have h1 : ma < mb * 2 ^ j := by
                have h2j : 2 ≤ 2 ^ j := by
                  have := Nat.pow_le_pow_right (show 0 < 2 by decide) hj_pos
                  simpa using this
                have htwo : 2 ^ (f.fractionBits + 1) = 2 ^ f.fractionBits * 2 := by
                  rw [Nat.pow_succ]
                have hmb2 : 2 ^ f.fractionBits * 2 ≤ mb * 2 ^ j :=
                  Nat.mul_le_mul hmb_ge h2j
                omega
              rw [hl1, hl2]
              have hr_mul : (powScale ma 1 ta).2 * rnum * (powScale (mb * 2 ^ j) 1 ta).2 =
                  (powScale ma 1 ta).2 * (powScale (mb * 2 ^ j) 1 ta).1 * rden := by
                rw [Nat.mul_assoc, ← hcross_b, ← Nat.mul_assoc]
              rw [hr_mul]
              have hmul_a : (powScale ma 1 ta).1 * rden * (powScale (mb * 2 ^ j) 1 ta).2 =
                  (powScale ma 1 ta).1 * (powScale (mb * 2 ^ j) 1 ta).2 * rden := by
                rw [Nat.mul_right_comm]
              rw [hmul_a]
              have hstrict : (powScale ma 1 ta).1 * (powScale (mb * 2 ^ j) 1 ta).2 <
                  (powScale ma 1 ta).2 * (powScale (mb * 2 ^ j) 1 ta).1 := by
                cases ta with
                | ofNat e =>
                  simp only [powScale, Nat.mul_one, Nat.one_mul]
                  exact Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos e)
                | negSucc e =>
                  simp only [powScale, Nat.one_mul]
                  rw [Nat.mul_comm (2 ^ (e + 1))]
                  exact Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos (e + 1))
              exact Nat.mul_lt_mul_of_pos_right hstrict hrden_pos
            have := nat_lt_of_mul_lt_mul_right hcmp_cross
            omega
      -- Now `tb ≤ ta`, so let `k = (ta - tb).toNat` and express both at scale `2^tb`!
      let k := (ta - tb).toNat
      have hta_eq : ta = tb + (k : Int) := by omega
      have hcross_a := powScale_add_nat_cross ma k tb
      rw [← hta_eq, ← hl1, ← hl2] at hcross_a
      -- `lnum / lden = (ma * 2^k) * 2^tb` and `rnum / rden = mb * 2^tb`.
      -- Let `rInt := (ma * 2^k) % mb`. Then `(lnum * rden) % (lden * rnum) / (lden * rden) = rInt * 2^tb`!
      let rInt := (ma * 2 ^ k) % mb
      have hr_cross : ((lnum * rden) % (lden * rnum)) * (powScale rInt 1 tb).2 =
          (powScale rInt 1 tb).1 * (lden * rden) := by
        cases htb_case : tb with
        | ofNat e =>
          rw [htb_case] at hcross_a hr1 hr2
          simp only [powScale, Nat.mul_one] at hcross_a hr1 hr2 ⊢
          have hl_eq : lnum = ma * 2 ^ k * 2 ^ e * lden := hcross_a.symm
          have hmul_mod : (lnum * rden) % (lden * rnum) =
              ((ma * 2 ^ k) % mb) * (2 ^ e * lden) := by
            rw [hl_eq, hr1, hr2, Nat.mul_one]
            have h1 : ma * 2 ^ k * 2 ^ e * lden = (ma * 2 ^ k) * (2 ^ e * lden) := by
              rw [Nat.mul_assoc (ma * 2 ^ k)]
            have h2 : lden * (mb * 2 ^ e) = mb * (2 ^ e * lden) := by
              rw [Nat.mul_comm lden, Nat.mul_assoc, Nat.mul_comm (2 ^ e) lden, ← Nat.mul_assoc,
                Nat.mul_assoc mb]
            rw [h1, h2, Nat.mul_mod_mul_right]
          rw [hmul_mod, hr2, Nat.mul_one]
          show ((ma * 2 ^ k) % mb) * (2 ^ e * lden) = ((ma * 2 ^ k) % mb) * 2 ^ e * lden
          rw [Nat.mul_assoc]
        | negSucc e =>
          rw [htb_case] at hcross_a hr1 hr2
          simp only [powScale, Nat.one_mul] at hcross_a hr1 hr2 ⊢
          have h1 : lnum * rden = (ma * 2 ^ k) * lden := by
            rw [hr2]; exact hcross_a.symm
          have h2 : lden * rnum = mb * lden := by
            rw [hr1, Nat.mul_comm]
          rw [h1, h2, Nat.mul_mod_mul_right]
          show ((ma * 2 ^ k) % mb) * lden * 2 ^ (e + 1) =
            ((ma * 2 ^ k) % mb) * (lden * rden)
          rw [hr2, Nat.mul_assoc]
      have hrInt_pos : 0 < rInt := by
        by_cases h0 : rInt = 0
        · exfalso
          rw [h0, powScale_zero_fst, Nat.zero_mul] at hr_cross
          have hpos_lhs := Nat.mul_pos hpos (powScale_snd_pos 0 tb)
          omega
        · exact Nat.pos_of_ne_zero h0
      have hrInt_lt : rInt < 2 ^ (f.fractionBits + 1) :=
        Nat.lt_trans (Nat.mod_lt _ hmb0) hmb_lt
      have hcong : roundRatioTiesToEven f ln ((lnum * rden) % (lden * rnum)) (lden * rden) =
          roundRatioTiesToEven f ln (powScale rInt 1 tb).1 (powScale rInt 1 tb).2 := by
        rw [← roundRatioBits_tiesToEven, ← roundRatioBits_tiesToEven]
        exact roundRatioBits_congr .tiesToEven f ln _ _ _ _ hden_pos (powScale_snd_pos rInt tb)
          hr_cross
      rw [hcong]
      obtain ⟨remN, remD, hdec, hcross_r, hDpos⟩ :=
        roundRatioTiesToEven_exact_dyadic f ln rInt tb hrInt_pos hrInt_lt htb_lo htb_hi
      refine ⟨remN, remD, hdec, ?_, hDpos⟩
      have hmul1 : remN * (lden * rden) * (powScale rInt 1 tb).2 =
          remN * (powScale rInt 1 tb).2 * (lden * rden) := Nat.mul_right_comm _ _ _
      have hmul2 : ((lnum * rden) % (lden * rnum)) * remD * (powScale rInt 1 tb).2 =
          ((lnum * rden) % (lden * rnum)) * (powScale rInt 1 tb).2 * remD :=
        Nat.mul_right_comm _ _ _
      apply Nat.eq_of_mul_eq_mul_right (powScale_snd_pos rInt tb)
      rw [hmul1, hcross_r, hmul2, hr_cross, Nat.mul_right_comm]

/-- Magnitude bound for IEEE-754 `rem`: for every pair of finite nonzero
operands `a` and `b`, `|a % b| < |b|`. -/
theorem evalFloatArithBaseProto_rem_finite_lt_abs_rhs (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite ln lnum lden) (hr : decodeBits f b = .finite rn rnum rden) :
    evalFloatCmpProto .lt f (evalFloatAbsProto f (evalFloatArithBaseProto .rem f a b))
      (evalFloatAbsProto f b) = true := by
  obtain ⟨h0, hpos⟩ := evalFloatArithBaseProto_rem_finite_exact f a b ln rn lnum lden rnum rden hl hr
  have hlt_rem := (evalFloatArithBaseProto_rem_finite f a b ln rn lnum lden rnum rden hl hr).2.1
  have hrden_pos := decodeBits_finite_den_pos f b rn rnum rden hr
  have hlden_pos := decodeBits_finite_den_pos f a ln lnum lden hl
  unfold evalFloatCmpProto evalFloatPartialCompareProto
  rw [decodeBits_evalFloatAbsProto, decodeBits_evalFloatAbsProto, hr]
  by_cases hrem0 : (lnum * rden) % (lden * rnum) = 0
  · rw [h0 hrem0, decodeBits_zeroBits]
    rfl
  · obtain ⟨remN, remD, hdec, hcross, hDpos⟩ := hpos (Nat.pos_of_ne_zero hrem0)
    rw [hdec]
    dsimp only [signedNum]
    have hlt_nat : remN * rden < rnum * remD := by
      apply nat_lt_of_mul_lt_mul_right (c := lden)
      have hlhs : remN * rden * lden = remN * (lden * rden) := by
        rw [Nat.mul_assoc, Nat.mul_comm rden lden]
      have hrhs : rnum * remD * lden = lden * rnum * remD := by
        rw [Nat.mul_right_comm, Nat.mul_comm rnum lden]
      rw [hlhs, hcross, hrhs]
      exact Nat.mul_lt_mul_of_pos_right hlt_rem hDpos
    have hlt_int : Int.ofNat remN * Int.ofNat rden < Int.ofNat rnum * Int.ofNat remD :=
      Int.ofNat_lt.mpr hlt_nat
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [(int_compare_eq_lt_iff _ _).mpr hlt_int]
    rfl

/-- Helper: every finite rational `|a| = n / d` decoded from `f` is an integer
multiple of `min_subnormal = 2^(f.minExponent - f.fractionBits)`. -/
private theorem decodeBits_finite_subnormal_quantum (f : IeeeFormat) (bits : Nat)
    (neg : Bool) (n d : Nat) (h : decodeBits f bits = .finite neg n d) :
    ∃ M : Nat, 0 < M ∧
      n * (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).2 =
        M * d * (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).1 := by
  obtain ⟨m, t, hm0, _, ht_lo, _, _, h1, h2⟩ := decodeBits_finite_dyadic f bits neg n d h
  let k := (t - (f.minExponent - (f.fractionBits : Int))).toNat
  have ht_eq : t = (f.minExponent - (f.fractionBits : Int)) + (k : Int) := by omega
  have hcross := powScale_add_nat_cross m k (f.minExponent - (f.fractionBits : Int))
  rw [← ht_eq, ← h1, ← h2] at hcross
  have he : f.minExponent - (f.fractionBits : Int) < 0 := by cases f <;> decide
  have hneg : ∃ p : Nat, f.minExponent - (f.fractionBits : Int) = Int.negSucc p := by
    cases hval : f.minExponent - (f.fractionBits : Int) with
    | ofNat a => rw [hval] at he; exact absurd he (Int.not_lt.mpr (Int.natCast_nonneg a))
    | negSucc p => exact ⟨p, rfl⟩
  obtain ⟨p, hp⟩ := hneg
  rw [hp] at hcross ⊢
  simp only [powScale, Nat.one_mul] at hcross ⊢
  refine ⟨m * 2 ^ k, Nat.mul_pos hm0 (Nat.two_pow_pos k), ?_⟩
  rw [Nat.mul_one]
  exact hcross.symm

/-- Any positive rational `n / d ≥ min_subnormal = 2^(f.minExponent - fb)` never
underflows to `±0.0` under `roundRatioTiesToEven`. -/
theorem roundRatioTiesToEven_ne_zero_of_ge_minSubnormal (f : IeeeFormat) (neg : Bool)
    (n d : Nat) (hn : 0 < n) (hd : 0 < d)
    (hge : d * (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).1 ≤
      n * (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).2) :
    ∀ zneg, decodeBits f (roundRatioTiesToEven f neg n d) ≠ .zero zneg := by
  intro zneg hz
  have hcr := roundRatioTiesToEven_correctly_rounded f neg n d hn hd
  dsimp only at hcr
  have hne_inf : decodeBits f (roundRatioTiesToEven f neg n d) ≠ .inf neg := by
    rw [hz]; intro h; cases h
  have hsame := hcr.2.2.2.2.2 hne_inf
  rw [hz] at hsame
  -- Show `sig ≥ 1`, contradicting `floatKindSameValue (.zero zneg) (if sig = 0 ...)`!
  have hsig_ge1 : 1 ≤ roundQuotientTiesToEven
      (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).1
      (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).2 := by
    have hsc_le : (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).2 ≤
        (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).1 := by
      by_cases hnorm : f.minExponent ≤ ratioExponent n d
      · have hfb := hcr.2.2.1 hnorm
        have hpos_pow : 1 ≤ 2 ^ f.fractionBits := Nat.two_pow_pos _
        have hmul := Nat.mul_le_mul_right
          (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).2 hpos_pow
        rw [Nat.one_mul] at hmul
        exact Nat.le_trans hmul hfb
      · have hmax : max (ratioExponent n d) f.minExponent = f.minExponent := by omega
        rw [hmax]
        have hpos_s : 0 < (f.fractionBits : Int) - f.minExponent := by cases f <;> decide
        have hsub : ∃ p : Nat, (f.fractionBits : Int) - f.minExponent = Int.ofNat (p + 1) ∧
            f.minExponent - (f.fractionBits : Int) = Int.negSucc p := by
          cases f
          · exact ⟨148, by decide, by decide⟩
          · exact ⟨1073, by decide, by decide⟩
        obtain ⟨p, hp1, hp2⟩ := hsub
        rw [hp1]
        rw [hp2] at hge
        simp only [powScale, Nat.one_mul, Nat.mul_one] at hge ⊢
        exact hge
    have hds := powScale_snd_pos_gen n d hd ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)
    have hge_rq := roundQuotient_ge_of_mul_le .tiesToEven _ _ 1 hds (by rw [Nat.one_mul]; exact hsc_le)
    rw [roundQuotient_tiesToEven] at hge_rq
    exact hge_rq
  have hsig_ne0 : roundQuotientTiesToEven
      (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).1
      (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).2 ≠ 0 := by
    omega
  rw [if_neg' hsig_ne0] at hsame
  exact hsame

/-- **IEEE-754 gradual-underflow theorem (`x - y == 0 ↔ x == y`)**: for all
finite (zero or nonzero) `f32`/`f64` operands `a` and `b`, `a - b` decodes to
`±0.0` **if and only if** `evalFloatCmpProto .eq f a b = true`. In particular,
distinct finite IEEE-754 floats never catastrophically flush to zero on
subtraction. -/
theorem evalFloatArithBaseProto_sub_finite_eq_zero_iff (f : IeeeFormat) (a b : Nat)
    (ha : (∃ an, decodeBits f a = .zero an) ∨ (∃ an n d, decodeBits f a = .finite an n d))
    (hb : (∃ bn, decodeBits f b = .zero bn) ∨ (∃ bn n d, decodeBits f b = .finite bn n d)) :
    (∃ zneg, decodeBits f (evalFloatArithBaseProto .sub f a b) = .zero zneg) ↔
      evalFloatCmpProto .eq f a b = true := by
  rcases ha with ⟨an, ha⟩ | ⟨an, lnum, lden, ha⟩ <;>
    rcases hb with ⟨bn, hb⟩ | ⟨bn, rnum, rden, hb⟩
  · -- zero - zero
    unfold evalFloatArithBaseProto exactSumProto evalFloatCmpProto evalFloatPartialCompareProto
    rw [ha, hb]
    dsimp only [negateFloatKind]
    rw [decodeBits_zeroBits]
    exact ⟨fun _ => rfl, fun _ => ⟨_, rfl⟩⟩
  · -- zero - finite: never zero and never eq
    have hsub : evalFloatArithBaseProto .sub f a b =
        roundRatioTiesToEven f (!bn) rnum rden := by
      unfold evalFloatArithBaseProto exactSumProto; rw [ha, hb]; rfl
    have heq_f : evalFloatCmpProto .eq f a b = false := by
      unfold evalFloatCmpProto evalFloatPartialCompareProto
      rw [ha, hb]; cases bn <;> rfl
    rw [hsub, heq_f]
    constructor
    · rintro ⟨zneg, hz⟩
      obtain ⟨M, hM0, hq⟩ := decodeBits_finite_subnormal_quantum f b bn rnum rden hb
      have hge : rden * (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).1 ≤
          rnum * (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).2 := by
        rw [hq]
        have hmul := Nat.mul_le_mul_right
          (rden * (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).1) hM0
        rw [Nat.one_mul, ← Nat.mul_assoc] at hmul
        exact hmul
      exact absurd hz (roundRatioTiesToEven_ne_zero_of_ge_minSubnormal f (!bn) rnum rden
        (decodeBits_finite_num_pos f b bn rnum rden hb)
        (decodeBits_finite_den_pos f b bn rnum rden hb) hge zneg)
    · intro h; cases h
  · -- finite - zero: never zero and never eq
    have hsub : evalFloatArithBaseProto .sub f a b =
        roundRatioTiesToEven f an lnum lden := by
      unfold evalFloatArithBaseProto exactSumProto; rw [ha, hb]; rfl
    have heq_f : evalFloatCmpProto .eq f a b = false := by
      unfold evalFloatCmpProto evalFloatPartialCompareProto
      rw [ha, hb]; cases an <;> rfl
    rw [hsub, heq_f]
    constructor
    · rintro ⟨zneg, hz⟩
      obtain ⟨M, hM0, hq⟩ := decodeBits_finite_subnormal_quantum f a an lnum lden ha
      have hge : lden * (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).1 ≤
          lnum * (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).2 := by
        rw [hq]
        have hmul := Nat.mul_le_mul_right
          (lden * (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).1) hM0
        rw [Nat.one_mul, ← Nat.mul_assoc] at hmul
        exact hmul
      exact absurd hz (roundRatioTiesToEven_ne_zero_of_ge_minSubnormal f an lnum lden
        (decodeBits_finite_num_pos f a an lnum lden ha)
        (decodeBits_finite_den_pos f a an lnum lden ha) hge zneg)
    · intro h; cases h
  · -- finite - finite
    rw [evalFloatArithBaseProto_sub_finite f a b an bn lnum lden rnum rden ha hb]
    have hlden_pos := decodeBits_finite_den_pos f a an lnum lden ha
    have hrden_pos := decodeBits_finite_den_pos f b bn rnum rden hb
    let diffInt := signedNum an lnum * Int.ofNat rden - signedNum bn rnum * Int.ofNat lden
    have heq_iff : evalFloatCmpProto .eq f a b = true ↔ diffInt = 0 := by
      unfold evalFloatCmpProto evalFloatPartialCompareProto
      rw [ha, hb]
      dsimp only [diffInt]
      constructor
      · intro h
        have hcmp : compare (signedNum an lnum * Int.ofNat rden) (signedNum bn rnum * Int.ofNat lden) = .eq := by
          cases hc : compare (signedNum an lnum * Int.ofNat rden) (signedNum bn rnum * Int.ofNat lden) <;>
            rw [hc] at h <;> first | rfl | cases h
        have hcross := (int_compare_eq_eq_iff _ _).mp hcmp
        omega
      · intro h0
        have hcross : signedNum an lnum * Int.ofNat rden = signedNum bn rnum * Int.ofNat lden := by omega
        rw [(int_compare_eq_eq_iff _ _).mpr hcross]
        rfl
    rw [heq_iff]
    constructor
    · rintro ⟨zneg, hz⟩
      by_cases h0 : diffInt = 0
      · exact h0
      · exfalso
        obtain ⟨Ma, _, hqa⟩ := decodeBits_finite_subnormal_quantum f a an lnum lden ha
        obtain ⟨Mb, _, hqb⟩ := decodeBits_finite_subnormal_quantum f b bn rnum rden hb
        have hq_pos : 0 < (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).2 :=
          powScale_snd_pos 1 _
        have hq1_eq : (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).1 = 1 := by
          cases f <;> decide
        -- Show `diffInt * Q2 = (signedNum an Ma - signedNum bn Mb) * (lden * rden)`!
        have hsigned_q : ∀ (sg : Bool) (num den M : Nat),
            num * (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).2 = M * den * 1 →
            signedNum sg num * Int.ofNat (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).2 =
              signedNum sg M * Int.ofNat den := by
          intro sg num den M hq
          rw [Nat.mul_one] at hq
          unfold signedNum
          cases sg
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact congrArg Int.ofNat hq
          · simp only [↓reduceIte, Int.neg_mul]
            exact congrArg Neg.neg (congrArg Int.ofNat hq)
        rw [hq1_eq] at hqa hqb
        have hsa := hsigned_q an lnum lden Ma hqa
        have hsb := hsigned_q bn rnum rden Mb hqb
        have hmul_diff : diffInt * Int.ofNat (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).2 =
            (signedNum an Ma - signedNum bn Mb) * Int.ofNat (lden * rden) := by
          dsimp only [diffInt]
          rw [Int.sub_mul]
          have hL : signedNum an lnum * Int.ofNat rden *
              Int.ofNat (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).2 =
              signedNum an Ma * Int.ofNat (lden * rden) := by
            rw [Int.mul_right_comm, hsa, Int.mul_assoc]
            rfl
          have hR : signedNum bn rnum * Int.ofNat lden *
              Int.ofNat (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).2 =
              signedNum bn Mb * Int.ofNat (lden * rden) := by
            rw [Int.mul_right_comm, hsb, Int.mul_assoc]
            rw [Nat.mul_comm lden rden]
            rfl
          rw [hL, hR, Int.sub_mul]
        have hM_ne : signedNum an Ma - signedNum bn Mb ≠ 0 := by
          intro hM0
          rw [hM0, Int.zero_mul] at hmul_diff
          have hq_int : Int.ofNat (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).2 ≠ 0 :=
            fun h => Nat.ne_of_gt hq_pos (Int.ofNat.inj h)
          rcases Int.mul_eq_zero.mp hmul_diff with h1 | h2
          · exact h0 h1
          · exact hq_int h2
        have hnat_eq : diffInt.natAbs * (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).2 =
            (signedNum an Ma - signedNum bn Mb).natAbs * (lden * rden) := by
          have h := congrArg Int.natAbs hmul_diff
          rw [Int.natAbs_mul, Int.natAbs_mul] at h
          exact h
        have hge : lden * rden * (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).1 ≤
            diffInt.natAbs * (powScale 1 1 (f.minExponent - (f.fractionBits : Int))).2 := by
          rw [hq1_eq, Nat.mul_one, hnat_eq]
          have h1 : 1 ≤ (signedNum an Ma - signedNum bn Mb).natAbs := Int.natAbs_pos.mpr hM_ne
          have hmul := Nat.mul_le_mul_right (lden * rden) h1
          rw [Nat.one_mul] at hmul
          exact hmul
        exact roundRatioTiesToEven_ne_zero_of_ge_minSubnormal f (decide (diffInt < 0))
          diffInt.natAbs (lden * rden) (Int.natAbs_pos.mpr h0)
          (Nat.mul_pos hlden_pos hrden_pos) hge zneg hz
    · intro h0
      have habs : diffInt.natAbs = 0 := by rw [h0]; rfl
      show ∃ zneg, decodeBits f (roundRatioTiesToEven f (decide (diffInt < 0)) diffInt.natAbs (lden * rden)) = .zero zneg
      rw [habs]
      unfold roundRatioTiesToEven
      rw [if_neg' (Nat.ne_of_gt (Nat.mul_pos hlden_pos hrden_pos)), if_pos' rfl, decodeBits_zeroBits]
      exact ⟨_, rfl⟩

/-! ### §9.3 Cross-Format `miri#5643` Signaling-NaN Survival & Length Theorems -/

/-- Exact length of `expandNaNSigns`: always `2 * l.length`. -/
theorem length_expandNaNSigns (f : IeeeFormat) (l : List Nat) :
    (expandNaNSigns f l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons _ rest ih =>
    unfold expandNaNSigns
    show (expandNaNSigns f rest).length + 2 = 2 * (rest.length + 1)
    omega

/-- Exact length of `nanChoicesProto` under `.nondeterministic`, guaranteeing
`≥ 2` entries and matching Miri's `candidates[index]?` indexing bounds. -/
theorem length_nanChoicesProto_nondet (f : IeeeFormat) (inputs : List (IeeeFormat × Nat)) :
    (nanChoicesProto f inputs .nondeterministic).length =
      2 * (1 + (quietedNaNCandidates f inputs).length + (signalingNaNCandidates f inputs).length) := by
  unfold nanChoicesProto
  rw [length_expandNaNSigns]
  show 2 * ((quietedNaNCandidates f inputs ++ signalingNaNCandidates f inputs).length + 1) = _
  rw [List.length_append]
  omega

/-- Helper: exact `signalingNaNLowerOf` formula for any signaling NaN input. -/
private theorem signalingNaNLowerOf_eq_of_snan (src dst : IeeeFormat) (inBits : Nat)
    (neg : Bool) (payload : Nat) (hd : decodeBits src inBits = .nan neg false payload) :
    signalingNaNLowerOf dst src inBits =
      (if src.fractionBits ≤ dst.fractionBits then
        payload * 2 ^ (dst.fractionBits - src.fractionBits)
      else
        payload / 2 ^ (src.fractionBits - dst.fractionBits)) := by
  obtain ⟨_, hne, hp_lt, _⟩ := decodeBits_nan_payload src inBits neg false payload hd
  have hlt_half : payload < 2 ^ (src.fractionBits - 1) := by
    have hsp := (ieeeFormat_width_split src).2.2.1
    have hs : isSignalingNaNBits src inBits = true := by unfold isSignalingNaNBits; rw [hd]
    obtain ⟨n', p', hd', _, hlt'⟩ := (isSignalingNaNBits_iff_payload_lt src inBits).mp hs
    rw [hd] at hd'; injection hd' with _ _ hp_eq; subst hp_eq; exact hlt'
  have hlor_src : Nat.lor payload (2 ^ (src.fractionBits - 1)) =
      payload + 2 ^ (src.fractionBits - 1) := by
    have h1 := mul_two_pow_add_eq_lor 1 payload (src.fractionBits - 1) hlt_half
    rw [Nat.one_mul] at h1
    change payload ||| 2 ^ (src.fractionBits - 1) = _
    rw [Nat.add_comm, h1]
    exact Nat.or_comm _ _
  have hE : 2 ^ dst.exponentBits - 1 < 2 ^ dst.exponentBits :=
    Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  have hconv_lt := convertNaNPayload_lt src dst payload hp_lt
  unfold signalingNaNLowerOf
  rw [evalFloatToFloatRoundTiesToEven_of_nan src dst inBits neg false payload hd,
      unpackBits_encodeBits dst neg _ _ hE hconv_lt]
  dsimp only
  by_cases hle : src.fractionBits ≤ dst.fractionBits
  · rw [if_pos' hle, if_pos' hle, hlor_src]
    have hshift : (payload + 2 ^ (src.fractionBits - 1)) * 2 ^ (dst.fractionBits - src.fractionBits) =
        payload * 2 ^ (dst.fractionBits - src.fractionBits) + 2 ^ (dst.fractionBits - 1) := by
      rw [Nat.add_mul, ← Nat.pow_add]
      have hexp : src.fractionBits - 1 + (dst.fractionBits - src.fractionBits) = dst.fractionBits - 1 := by
        cases src <;> cases dst <;> simp_all [IeeeFormat.fractionBits]
      rw [hexp]
    have hlow_lt : payload * 2 ^ (dst.fractionBits - src.fractionBits) < 2 ^ (dst.fractionBits - 1) := by
      have hmul := Nat.mul_lt_mul_of_pos_right hlt_half (Nat.two_pow_pos (dst.fractionBits - src.fractionBits))
      rw [← Nat.pow_add] at hmul
      have hexp : src.fractionBits - 1 + (dst.fractionBits - src.fractionBits) = dst.fractionBits - 1 := by
        cases src <;> cases dst <;> simp_all [IeeeFormat.fractionBits]
      rw [hexp] at hmul
      exact hmul
    rw [hshift]
    have hlor_dst : Nat.lor (payload * 2 ^ (dst.fractionBits - src.fractionBits) + 2 ^ (dst.fractionBits - 1))
        (2 ^ (dst.fractionBits - 1)) =
        payload * 2 ^ (dst.fractionBits - src.fractionBits) + 2 ^ (dst.fractionBits - 1) := by
      have h1 := mul_two_pow_add_eq_lor 1 (payload * 2 ^ (dst.fractionBits - src.fractionBits))
        (dst.fractionBits - 1) hlow_lt
      rw [Nat.one_mul] at h1
      change _ = (2 ^ (dst.fractionBits - 1)) ||| (payload * 2 ^ (dst.fractionBits - src.fractionBits)) at h1
      change (payload * 2 ^ (dst.fractionBits - src.fractionBits) + 2 ^ (dst.fractionBits - 1)) |||
        2 ^ (dst.fractionBits - 1) = _
      rw [Nat.add_comm _ (2 ^ (dst.fractionBits - 1)), h1, Nat.or_assoc, Nat.or_comm _ (2 ^ (dst.fractionBits - 1)),
        ← Nat.or_assoc, Nat.or_self]
    rw [hlor_dst, Nat.add_mod_right, Nat.mod_eq_of_lt hlow_lt]
  · rw [if_neg' hle, if_neg' hle, hlor_src]
    have hdiff_exp : 2 ^ (src.fractionBits - 1) =
        2 ^ (dst.fractionBits - 1) * 2 ^ (src.fractionBits - dst.fractionBits) := by
      cases src <;> cases dst <;> first | decide | (exfalso; exact hle (by decide))
    have hdiv_pos : 0 < 2 ^ (src.fractionBits - dst.fractionBits) := Nat.two_pow_pos _
    have hshift : (payload + 2 ^ (src.fractionBits - 1)) / 2 ^ (src.fractionBits - dst.fractionBits) =
        payload / 2 ^ (src.fractionBits - dst.fractionBits) + 2 ^ (dst.fractionBits - 1) := by
      rw [hdiff_exp, Nat.add_mul_div_right _ _ hdiv_pos]
    have hlow_lt : payload / 2 ^ (src.fractionBits - dst.fractionBits) < 2 ^ (dst.fractionBits - 1) := by
      apply nat_div_lt_of_lt_mul
      rw [Nat.mul_comm, ← hdiff_exp]
      exact hlt_half
    rw [hshift]
    have hlor_dst : Nat.lor (payload / 2 ^ (src.fractionBits - dst.fractionBits) + 2 ^ (dst.fractionBits - 1))
        (2 ^ (dst.fractionBits - 1)) =
        payload / 2 ^ (src.fractionBits - dst.fractionBits) + 2 ^ (dst.fractionBits - 1) := by
      have h1 := mul_two_pow_add_eq_lor 1 (payload / 2 ^ (src.fractionBits - dst.fractionBits))
        (dst.fractionBits - 1) hlow_lt
      rw [Nat.one_mul] at h1
      change _ = (2 ^ (dst.fractionBits - 1)) ||| (payload / 2 ^ (src.fractionBits - dst.fractionBits)) at h1
      change (payload / 2 ^ (src.fractionBits - dst.fractionBits) + 2 ^ (dst.fractionBits - 1)) |||
        2 ^ (dst.fractionBits - 1) = _
      rw [Nat.add_comm _ (2 ^ (dst.fractionBits - 1)), h1, Nat.or_assoc, Nat.or_comm _ (2 ^ (dst.fractionBits - 1)),
        ← Nat.or_assoc, Nat.or_self]
    rw [hlor_dst, Nat.add_mod_right, Nat.mod_eq_of_lt hlow_lt]

/-- **Widening signaling-NaN survival (`miri#5643`)**: whenever
`src.fractionBits ≤ dst.fractionBits` (including same-format and `f32 → f64`),
every signaling NaN input in `src` has a nonzero lower payload in `dst`, so its
unchanged-propagation signaling candidate **always** survives in
`signalingNaNCandidates`. -/
theorem widening_signaling_candidate_survives (src dst : IeeeFormat) (inBits : Nat)
    (hle : src.fractionBits ≤ dst.fractionBits)
    (hs : isSignalingNaNBits src inBits = true) :
    signalingNaNLowerOf dst src inBits ≠ 0 ∧
      signalingNaNCandidateOf dst src inBits ∈ signalingNaNCandidates dst [(src, inBits)] := by
  obtain ⟨neg, payload, hd, hne, _⟩ := (isSignalingNaNBits_iff_payload_lt src inBits).mp hs
  have hlow := signalingNaNLowerOf_eq_of_snan src dst inBits neg payload hd
  rw [if_pos' hle] at hlow
  have hnz : signalingNaNLowerOf dst src inBits ≠ 0 := by
    rw [hlow]
    exact Nat.ne_of_gt (Nat.mul_pos (Nat.pos_of_ne_zero hne) (Nat.two_pow_pos _))
  refine ⟨hnz, (mem_signalingNaNCandidates_iff dst [(src, inBits)] _).mpr ?_⟩
  exact ⟨(src, inBits), List.Mem.head _, hs, hnz, rfl⟩

/-- **Narrowing signaling-NaN survival characterization (`miri#5643`)**: whenever
`dst.fractionBits < src.fractionBits` (i.e. `f64 → f32`), a signaling NaN input
with decoded payload `payload` produces a signaling candidate in `dst` **if and
only if** its surviving upper payload bits `payload / 2^(src.fractionBits - dst.fractionBits)`
are nonzero (preventing a zero lower payload from being encoded as `±Inf`). -/
theorem narrowing_signaling_candidate_iff (src dst : IeeeFormat) (inBits : Nat)
    (neg : Bool) (payload : Nat)
    (hlt : dst.fractionBits < src.fractionBits)
    (hd : decodeBits src inBits = .nan neg false payload) :
    (signalingNaNLowerOf dst src inBits ≠ 0 ↔
      payload / 2 ^ (src.fractionBits - dst.fractionBits) ≠ 0) ∧
    (signalingNaNCandidateOf dst src inBits ∈ signalingNaNCandidates dst [(src, inBits)] ↔
      payload / 2 ^ (src.fractionBits - dst.fractionBits) ≠ 0) := by
  have hnot_le : ¬ src.fractionBits ≤ dst.fractionBits := Nat.not_le.mpr hlt
  have hlow := signalingNaNLowerOf_eq_of_snan src dst inBits neg payload hd
  rw [if_neg' hnot_le] at hlow
  have hs : isSignalingNaNBits src inBits = true := by unfold isSignalingNaNBits; rw [hd]
  refine ⟨by rw [hlow], ?_⟩
  rw [mem_signalingNaNCandidates_iff]
  constructor
  · rintro ⟨e, he, _, hnz, _⟩
    cases he with
    | head => rw [hlow] at hnz; exact hnz
    | tail _ h => cases h
  · intro hnz
    exact ⟨(src, inBits), List.Mem.head _, hs, by rw [hlow]; exact hnz, rfl⟩

/-! ### §9.4 Relational MIR `Rvalue` Dispatcher Strengthening -/

/-- Exact conservative extension of `EvalRvalueFloatRelProto`: on any non-float
`Rvalue`, the relational semantics collapses to exact equality with the trusted
`evalRvalue` under both modes. -/
theorem EvalRvalueFloatRelProto.nonFloat_iff (mode : FloatArithMode)
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (res : RvalueEvalResult)
    (hNonFloat :
      (∀ op, rv = .unaryOp .neg op → floatTyOf? (operandTy localDecls layouts op) = .none) ∧
      (∀ op lhs rhs, rv = .binaryOp op lhs rhs →
        floatTyOf? (operandTy localDecls layouts lhs) = .none ∧
        floatTyOf? (operandTy localDecls layouts rhs) = .none)) :
    EvalRvalueFloatRelProto mode locals rv mem localDecls layouts res ↔
      res = evalRvalue locals rv mem localDecls layouts := by
  have hbase := evalRvalueFloatProto_nonFloat_eq locals rv mem localDecls layouts hNonFloat
  unfold EvalRvalueFloatRelProto
  cases rv with
  | binaryOp op lhs rhs =>
    dsimp only
    obtain ⟨hl, hr⟩ := hNonFloat.2 op lhs rhs rfl
    rw [hl, hr, hbase]
  | _ => rw [hbase]

/-- Well-formedness of `EvalRvalueFloatRelProto` on float binary ops under
**both** `.deterministic` and `.nondeterministic` modes: memory is unchanged,
both operands share one modeled IEEE format, arithmetic results are canonical
in-width scalars of that format, and comparison results are canonical `bool`s. -/
theorem EvalRvalueFloatRelProto.binaryOp_float_ok_wf (mode : FloatArithMode)
    (locals : List LocalSlot) (op : BinOp) (lhsOp rhsOp : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (lhsFk rhsFk : FloatTy)
    (v : Value) (locals' : List LocalSlot) (mem' : Memory)
    (hl : floatTyOf? (operandTy localDecls layouts lhsOp) = .some lhsFk)
    (hr : floatTyOf? (operandTy localDecls layouts rhsOp) = .some rhsFk)
    (hrel : EvalRvalueFloatRelProto mode locals (.binaryOp op lhsOp rhsOp) mem localDecls layouts
      (.ok v locals' mem')) :
    mem' = mem ∧
      ∃ fmt, ieeeFormatOfFloatTy? lhsFk = .some fmt ∧ ieeeFormatOfFloatTy? rhsFk = .some fmt ∧
        ((isFloatArithBinOp op = true ∧
            ∃ bits, v = .scalar ⟨bits, fmt.byteWidth⟩ ∧ bits < 2 ^ fmt.width) ∨
          (isFloatArithBinOp op = false ∧ isFloatCmpBinOp op = true ∧
            ∃ b, v = .scalar (boolToScalar b))) := by
  unfold EvalRvalueFloatRelProto at hrel
  dsimp only at hrel
  rw [hl, hr] at hrel
  dsimp only at hrel
  cases hlev : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals
      localDecls mem.callStack with
  | ub =>
    rw [hlev] at hrel
    exact evalRvalueFloatProto_binaryOp_float_ok_wf locals op lhsOp rhsOp mem localDecls layouts
      lhsFk rhsFk v locals' mem' hl hr hrel.symm
  | unsupported =>
    rw [hlev] at hrel
    exact evalRvalueFloatProto_binaryOp_float_ok_wf locals op lhsOp rhsOp mem localDecls layouts
      lhsFk rhsFk v locals' mem' hl hr hrel.symm
  | ok lv l₁ =>
    rw [hlev] at hrel
    cases lv with
    | scalar lsc =>
      dsimp only at hrel
      cases hrev : evalOperand l₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals
          localDecls mem.callStack with
      | ub =>
        rw [hrev] at hrel
        exact evalRvalueFloatProto_binaryOp_float_ok_wf locals op lhsOp rhsOp mem localDecls layouts
          lhsFk rhsFk v locals' mem' hl hr hrel.symm
      | unsupported =>
        rw [hrev] at hrel
        exact evalRvalueFloatProto_binaryOp_float_ok_wf locals op lhsOp rhsOp mem localDecls layouts
          lhsFk rhsFk v locals' mem' hl hr hrel.symm
      | ok rvVal l₂ =>
        rw [hrev] at hrel
        cases rvVal with
        | scalar rsc =>
          dsimp only at hrel
          cases hfl : ieeeFormatOfFloatTy? lhsFk with
          | none =>
            rw [hfl] at hrel
            rw [← hfl]
            exact evalRvalueFloatProto_binaryOp_float_ok_wf locals op lhsOp rhsOp mem localDecls
              layouts lhsFk rhsFk v locals' mem' hl hr hrel.symm
          | some fmtL =>
            cases hfr : ieeeFormatOfFloatTy? rhsFk with
            | none =>
              rw [hfl, hfr] at hrel
              rw [← hfl, ← hfr]
              exact evalRvalueFloatProto_binaryOp_float_ok_wf locals op lhsOp rhsOp mem localDecls
                layouts lhsFk rhsFk v locals' mem' hl hr hrel.symm
            | some fmtR =>
              rw [hfl, hfr] at hrel
              dsimp only at hrel
              by_cases hcond : (fmtL == fmtR && Nat.beq lsc.sizeBytes fmtL.byteWidth &&
                  Nat.beq rsc.sizeBytes fmtL.byteWidth && isFloatArithBinOp op) = true
              · rw [if_pos' hcond] at hrel
                obtain ⟨out, hout, hres⟩ := hrel
                have hcond3 := bool_and_true_left hcond
                have heq := ieeeFormat_eq_of_beq (bool_and_true_left (bool_and_true_left hcond3))
                subst heq
                injection hres with hv _ hm
                exact ⟨hm, fmtL, rfl, rfl, Or.inl ⟨hout.1, out, hv,
                  EvalFloatBinOpRel.out_lt mode op fmtL lsc.bits rsc.bits out hout⟩⟩
              · rw [if_neg' hcond] at hrel
                rw [← hfl, ← hfr]
                exact evalRvalueFloatProto_binaryOp_float_ok_wf locals op lhsOp rhsOp mem localDecls
                  layouts lhsFk rhsFk v locals' mem' hl hr hrel.symm
        | unit =>
          exact evalRvalueFloatProto_binaryOp_float_ok_wf locals op lhsOp rhsOp mem localDecls
            layouts lhsFk rhsFk v locals' mem' hl hr hrel.symm
        | ptr _ _ =>
          exact evalRvalueFloatProto_binaryOp_float_ok_wf locals op lhsOp rhsOp mem localDecls
            layouts lhsFk rhsFk v locals' mem' hl hr hrel.symm
        | aggregate _ _ =>
          exact evalRvalueFloatProto_binaryOp_float_ok_wf locals op lhsOp rhsOp mem localDecls
            layouts lhsFk rhsFk v locals' mem' hl hr hrel.symm
    | unit =>
      exact evalRvalueFloatProto_binaryOp_float_ok_wf locals op lhsOp rhsOp mem localDecls layouts
        lhsFk rhsFk v locals' mem' hl hr hrel.symm
    | ptr _ _ =>
      exact evalRvalueFloatProto_binaryOp_float_ok_wf locals op lhsOp rhsOp mem localDecls layouts
        lhsFk rhsFk v locals' mem' hl hr hrel.symm
    | aggregate _ _ =>
      exact evalRvalueFloatProto_binaryOp_float_ok_wf locals op lhsOp rhsOp mem localDecls layouts
        lhsFk rhsFk v locals' mem' hl hr hrel.symm

/-! ## §10. Composite Erasure Characterization (Arrays, Tuples, Wide Slice Metadata), Cast-Level Policy Independence & Multi-Variant Enum Fix Prototype -/

theorem takeAbstractBytes_stripAbstractBytesProv (n : Nat) (bytes : List AbstractByte) :
    takeAbstractBytes n (stripAbstractBytesProv bytes) =
      stripAbstractBytesProv (takeAbstractBytes n bytes) := by
  induction n generalizing bytes with
  | zero => rfl
  | succ k ih =>
    cases bytes with
    | nil => rfl
    | cons b rest =>
      show stripAbstractByteProv b :: takeAbstractBytes k (stripAbstractBytesProv rest) =
        stripAbstractByteProv b :: stripAbstractBytesProv (takeAbstractBytes k rest)
      exact congrArg (List.cons _) (ih rest)

theorem dropAbstractBytes_stripAbstractBytesProv (n : Nat) (bytes : List AbstractByte) :
    dropAbstractBytes n (stripAbstractBytesProv bytes) =
      stripAbstractBytesProv (dropAbstractBytes n bytes) := by
  induction n generalizing bytes with
  | zero => rfl
  | succ k ih =>
    cases bytes with
    | nil => rfl
    | cons _ rest => exact ih rest

theorem sliceAbstractBytes_stripAbstractBytesProv (bytes : List AbstractByte) (off len : Nat) :
    sliceAbstractBytes (stripAbstractBytesProv bytes) off len =
      match sliceAbstractBytes bytes off len with
      | .some s => .some (stripAbstractBytesProv s)
      | .none => .none := by
  unfold sliceAbstractBytes
  rw [length_stripAbstractBytesProv]
  cases Nat.ble (Nat.add off len) (length bytes) with
  | false => rfl
  | true =>
    dsimp only
    rw [dropAbstractBytes_stripAbstractBytesProv, takeAbstractBytes_stripAbstractBytesProv]

private theorem takeAbstractBytes_append_left (n : Nat) (xs ys : List AbstractByte)
    (hlen : length xs = n) :
    takeAbstractBytes n (appendAbstractBytes xs ys) = xs := by
  induction n generalizing xs with
  | zero =>
    cases xs with
    | nil => rfl
    | cons _ _ => cases hlen
  | succ k ih =>
    cases xs with
    | nil => cases hlen
    | cons b rest =>
      have hrest : length rest = k := Nat.succ.inj hlen
      show b :: takeAbstractBytes k (appendAbstractBytes rest ys) = b :: rest
      exact congrArg (List.cons b) (ih rest hrest)

private theorem dropAbstractBytes_append_left (n : Nat) (xs ys : List AbstractByte)
    (hlen : length xs = n) :
    dropAbstractBytes n (appendAbstractBytes xs ys) = ys := by
  induction n generalizing xs with
  | zero =>
    cases xs with
    | nil => rfl
    | cons _ _ => cases hlen
  | succ k ih =>
    cases xs with
    | nil => cases hlen
    | cons _ rest =>
      exact ih rest (Nat.succ.inj hlen)

private theorem length_takeAbstractBytes_of_le (n : Nat) (bytes : List AbstractByte)
    (hle : n ≤ length bytes) :
    length (takeAbstractBytes n bytes) = n := by
  induction n generalizing bytes with
  | zero => rfl
  | succ k ih =>
    cases bytes with
    | nil => cases hle
    | cons _ rest =>
      show (takeAbstractBytes k rest).length + 1 = k + 1
      exact congrArg Nat.succ (ih rest (Nat.le_of_succ_le_succ hle))

private theorem length_dropAbstractBytes (n : Nat) (bytes : List AbstractByte) :
    length (dropAbstractBytes n bytes) = length bytes - n := by
  induction n generalizing bytes with
  | zero => rfl
  | succ k ih =>
    cases bytes with
    | nil => exact (Nat.zero_sub (k + 1)).symm
    | cons _ rest =>
      show (dropAbstractBytes k rest).length = (rest.length + 1) - (k + 1)
      rw [Nat.succ_sub_succ]
      exact ih rest

private theorem length_appendAbstractBytes (xs ys : List AbstractByte) :
    length (appendAbstractBytes xs ys) = length xs + length ys := by
  induction xs with
  | nil =>
    show length ys = 0 + length ys
    rw [Nat.zero_add]
  | cons _ rest ih =>
    show length (appendAbstractBytes rest ys) + 1 = length rest + 1 + length ys
    rw [ih]
    omega

/-- `decodeFieldsBySpan` depends only on byte values (provenance-oblivious). -/
theorem decodeFieldsBySpan_stripAbstractBytesProv (bytes : List AbstractByte) (totalSize : Nat) :
    ∀ (offsets : List Size),
      decodeFieldsBySpan (stripAbstractBytesProv bytes) totalSize offsets =
        decodeFieldsBySpan bytes totalSize offsets
  | .nil => rfl
  | off :: rest => by
    have ih := decodeFieldsBySpan_stripAbstractBytesProv bytes totalSize rest
    unfold decodeFieldsBySpan
    cases rest with
    | nil =>
      dsimp only
      cases Nat.ble off.bytes totalSize with
      | false => rfl
      | true =>
        dsimp only
        rw [sliceAbstractBytes_stripAbstractBytesProv]
        cases sliceAbstractBytes bytes off.bytes (Nat.sub totalSize off.bytes) with
        | none => rfl
        | some fSlice =>
          dsimp only
          cases Nat.beq (Nat.sub totalSize off.bytes) 0 with
          | true => rfl
          | false =>
            dsimp only
            rw [decodeScalarBytes_stripAbstractBytesProv]
            cases decodeScalarBytes fSlice false with
            | none => rfl
            | some p => cases p; rfl
    | cons next tail =>
      dsimp only
      cases Nat.ble off.bytes next.bytes with
      | false => rfl
      | true =>
        dsimp only
        rw [sliceAbstractBytes_stripAbstractBytesProv]
        cases sliceAbstractBytes bytes off.bytes (Nat.sub next.bytes off.bytes) with
        | none => rfl
        | some fSlice =>
          dsimp only
          cases Nat.beq (Nat.sub next.bytes off.bytes) 0 with
          | true =>
            dsimp only
            rw [ih]
          | false =>
            dsimp only
            rw [decodeScalarBytes_stripAbstractBytesProv]
            cases decodeScalarBytes fSlice false with
            | none => rfl
            | some p =>
              cases p; dsimp only
              rw [ih]

private theorem decodeArrayChunksWith_strip_eq_strict_erased
    (f₁ f₂ : List AbstractByte → Option Value) (elemSz : Nat)
    (hf : ∀ bs, f₁ bs = f₂ (stripAbstractBytesProv bs)) :
    ∀ (n : Nat) (bytes : List AbstractByte),
      decodeArrayChunksWith f₁ elemSz n bytes =
        decodeArrayChunksWith f₂ elemSz n (stripAbstractBytesProv bytes)
  | .zero, .nil => rfl
  | .zero, _ :: _ => rfl
  | .succ k, bytes => by
    unfold decodeArrayChunksWith
    rw [length_stripAbstractBytesProv]
    cases Nat.ble elemSz (length bytes) with
    | false => rfl
    | true =>
      dsimp only
      rw [takeAbstractBytes_stripAbstractBytesProv, dropAbstractBytes_stripAbstractBytesProv, hf]
      cases f₂ (stripAbstractBytesProv (takeAbstractBytes elemSz bytes)) with
      | none => rfl
      | some v =>
        dsimp only
        rw [decodeArrayChunksWith_strip_eq_strict_erased f₁ f₂ elemSz hf k
          (dropAbstractBytes elemSz bytes)]

private theorem decodeSeqFieldsWith_strip_eq_strict_erased
    (f₁ f₂ : RigidTy → List AbstractByte → Option Value) (sz : RigidTy → Option Nat)
    (P : RigidTy → Bool)
    (hf : ∀ k bs, P k = true → f₁ k bs = f₂ k (stripAbstractBytesProv bs)) :
    ∀ (ks : List RigidTy) (bytes : List AbstractByte),
      ks.all P = true →
      decodeSeqFieldsWith f₁ sz ks bytes =
        decodeSeqFieldsWith f₂ sz ks (stripAbstractBytesProv bytes)
  | .nil, .nil, _ => rfl
  | .nil, _ :: _, _ => rfl
  | k :: rest, bytes, hall => by
    have hP : P k = true := bool_and_true_left hall
    have hrest : rest.all P = true := bool_and_true_right hall
    unfold decodeSeqFieldsWith
    rw [length_stripAbstractBytesProv]
    cases sz k with
    | none => rfl
    | some fSize =>
      dsimp only
      cases Nat.ble fSize (length bytes) with
      | false => rfl
      | true =>
        dsimp only
        rw [takeAbstractBytes_stripAbstractBytesProv, dropAbstractBytes_stripAbstractBytesProv,
          hf k _ hP]
        cases f₂ k (stripAbstractBytesProv (takeAbstractBytes fSize bytes)) with
        | none => rfl
        | some v =>
          dsimp only
          rw [decodeSeqFieldsWith_strip_eq_strict_erased f₁ f₂ sz P hf rest
            (dropAbstractBytes fSize bytes) hrest]

private theorem decodeFieldsAtOffsetsWith_strip_eq_strict_erased
    (f₁ f₂ : RigidTy → List AbstractByte → Option Value) (sz : RigidTy → Option Nat)
    (bytes : List AbstractByte) (P : RigidTy → Bool)
    (hf : ∀ k bs, P k = true → f₁ k bs = f₂ k (stripAbstractBytesProv bs)) :
    ∀ (offs : List Size) (ks : List RigidTy),
      ks.all P = true →
      decodeFieldsAtOffsetsWith f₁ sz bytes offs ks =
        decodeFieldsAtOffsetsWith f₂ sz (stripAbstractBytesProv bytes) offs ks
  | .nil, .nil, _ => rfl
  | .nil, _ :: _, _ => rfl
  | _ :: _, .nil, _ => rfl
  | off :: offRest, k :: kRest, hall => by
    have hP : P k = true := bool_and_true_left hall
    have hrest : kRest.all P = true := bool_and_true_right hall
    unfold decodeFieldsAtOffsetsWith
    cases sz k with
    | none => rfl
    | some fSize =>
      dsimp only
      rw [sliceAbstractBytes_stripAbstractBytesProv]
      cases sliceAbstractBytes bytes off.bytes fSize with
      | none => rfl
      | some fSlice =>
        dsimp only
        rw [hf k fSlice hP]
        cases f₂ k (stripAbstractBytesProv fSlice) with
        | none => rfl
        | some v =>
          dsimp only
          rw [decodeFieldsAtOffsetsWith_strip_eq_strict_erased f₁ f₂ sz bytes P hf offRest
            kRest hrest]

private theorem decodeTypedKindsAndLayoutsAtOffsets_strip_eq_strict_erased
    (f₁ f₂ : Ty → List AbstractByte → Option Value) (layouts : LayoutTable)
    (bytes : List AbstractByte) (P : RigidTy → Bool)
    (hf : ∀ k lIdx bs, P k = true →
      f₁ { kind := k, layoutIdx := lIdx } bs =
        f₂ { kind := k, layoutIdx := lIdx } (stripAbstractBytesProv bs)) :
    ∀ (offs : List Size) (ks : List RigidTy) (fIdxs : List Nat),
      ks.all P = true →
      decodeTypedKindsAndLayoutsAtOffsets f₁ layouts bytes offs ks fIdxs =
        decodeTypedKindsAndLayoutsAtOffsets f₂ layouts (stripAbstractBytesProv bytes) offs ks fIdxs
  | .nil, .nil, .nil, _ => rfl
  | off :: offRest, k :: kRest, fIdx :: fRest, hall => by
    have hP : P k = true := bool_and_true_left hall
    have hrest : kRest.all P = true := bool_and_true_right hall
    unfold decodeTypedKindsAndLayoutsAtOffsets
    cases LayoutTable.lookup layouts fIdx with
    | none => rfl
    | some fl =>
      dsimp only
      rw [sliceAbstractBytes_stripAbstractBytesProv]
      cases sliceAbstractBytes bytes off.bytes fl.size.bytes with
      | none => rfl
      | some fSlice =>
        dsimp only
        rw [hf k fIdx fSlice hP]
        cases f₂ { kind := k, layoutIdx := fIdx } (stripAbstractBytesProv fSlice) with
        | none => rfl
        | some v =>
          dsimp only
          rw [decodeTypedKindsAndLayoutsAtOffsets_strip_eq_strict_erased f₁ f₂ layouts bytes P hf
            offRest kRest fRest hrest]
  | .nil, _ :: _, _, _ => rfl
  | .nil, .nil, _ :: _, _ => rfl
  | _ :: _, .nil, _, _ => rfl
  | _ :: _, _ :: _, .nil, _ => rfl

/-- **Composite erasure characterization (arrays of non-pointer scalars)**:
for every `[T; n]` where `T` is a non-pointer scalar (`bool`, `char`, `iN`,
`uN`, `fN`, e.g. `[u8; 8]`, `[u16; 4]`, `[usize; 2]`, `[f32; 2]`, `[bool; 8]`),
`.stripProvenance` decoding is identical to `.strictUcg630Ub` decoding of the
provenance-erased bytes (whether layout-backed or unindexed). -/
theorem decodeTypedValueFromBytesWithPolicy_strip_array_scalar_eq_strict_erased
    (fuel : Nat) (layouts : LayoutTable) (elemKind : RigidTy) (n : Nat)
    (layoutIdx : LayoutIdx) (bytes : List AbstractByte)
    (helem : isNonPtrScalarKind elemKind = true) :
    decodeTypedValueFromBytesWithPolicy .stripProvenance (.succ (.succ fuel)) layouts
        { kind := .array elemKind n, layoutIdx := layoutIdx } bytes =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub (.succ (.succ fuel)) layouts
        { kind := .array elemKind n, layoutIdx := layoutIdx } (stripAbstractBytesProv bytes) := by
  have hcore : ∀ (ek : RigidTy), isNonPtrScalarKind ek = true →
      ∀ (lIdx : LayoutIdx),
        decodeTypedValueFromBytesWithPolicy .stripProvenance (.succ (.succ fuel)) layouts
            { kind := .array ek n, layoutIdx := lIdx } bytes =
          decodeTypedValueFromBytesWithPolicy .strictUcg630Ub (.succ (.succ fuel)) layouts
            { kind := .array ek n, layoutIdx := lIdx } (stripAbstractBytesProv bytes) := by
    intro ek hek lIdx
    have hnorm_is_arr : ∃ ek',
        normalizeCodecTy { kind := .array ek n, layoutIdx := lIdx } =
          { kind := .array ek' n, layoutIdx := lIdx } ∧ isNonPtrScalarKind ek' = true := by
      cases ek with
      | float fk =>
        cases fk with
        | f16 => exact ⟨.uint .u16, rfl, rfl⟩
        | f32 => exact ⟨.uint .u32, rfl, rfl⟩
        | f64 => exact ⟨.uint .u64, rfl, rfl⟩
        | f128 => exact ⟨.uint .u128, rfl, rfl⟩
      | bool => exact ⟨.bool, rfl, rfl⟩
      | char => exact ⟨.char, rfl, rfl⟩
      | int w => exact ⟨.int w, rfl, rfl⟩
      | uint w => exact ⟨.uint w, rfl, rfl⟩
      | _ => cases hek
    obtain ⟨ek', hnorm, hek'⟩ := hnorm_is_arr
    unfold decodeTypedValueFromBytesWithPolicy
    rw [hnorm]
    dsimp only
    rw [length_stripAbstractBytesProv]
    cases Nat.beq n 0 with
    | true =>
      cases bytes <;> rfl
    | false =>
      dsimp only
      have hel : ∀ (fi : LayoutIdx) (bs : List AbstractByte),
          decodeTypedValueFromBytesWithPolicy .stripProvenance (.succ fuel) layouts
              { kind := ek', layoutIdx := fi } bs =
            decodeTypedValueFromBytesWithPolicy .strictUcg630Ub (.succ fuel) layouts
              { kind := ek', layoutIdx := fi } (stripAbstractBytesProv bs) :=
        fun fi bs =>
          decodeTypedValueFromBytesWithPolicy_strip_scalar_eq_strict_erased (.succ fuel) layouts
            { kind := ek', layoutIdx := fi } bs hek'
      have hfb : ∀ (elemSzOpt : Option Nat),
          ((match elemSzOpt with
            | .none => .none
            | .some elemSz =>
              match Nat.beq (length bytes) (Nat.mul elemSz n) with
              | false => .none
              | true =>
                match decodeArrayChunksWith
                    (fun bs => decodeTypedValueFromBytesWithPolicy .stripProvenance (.succ fuel)
                      layouts { kind := ek', layoutIdx := 0 } bs) elemSz n bytes with
                | .some elems => .some (.aggregate 0 elems)
                | .none => .none) : Option Value) =
          (match elemSzOpt with
            | .none => .none
            | .some elemSz =>
              match Nat.beq (length bytes) (Nat.mul elemSz n) with
              | false => .none
              | true =>
                match decodeArrayChunksWith
                    (fun bs => decodeTypedValueFromBytesWithPolicy .strictUcg630Ub (.succ fuel)
                      layouts { kind := ek', layoutIdx := 0 } bs) elemSz n
                    (stripAbstractBytesProv bytes) with
                | .some elems => .some (.aggregate 0 elems)
                | .none => .none) := by
        intro elemSzOpt
        cases elemSzOpt with
        | none => rfl
        | some elemSz =>
          dsimp only
          cases Nat.beq (length bytes) (Nat.mul elemSz n) with
          | false => rfl
          | true =>
            dsimp only
            rw [decodeArrayChunksWith_strip_eq_strict_erased _ _ elemSz (hel 0) n bytes]
      cases LayoutTable.lookup layouts lIdx with
      | none => exact hfb _
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
                rw [decodeArrayChunksWith_strip_eq_strict_erased _ _ stride.bytes (hel elemFlIdx) n
                  bytes]
            | nil => exact hfb _
          | _ => exact hfb _
  exact hcore elemKind helem layoutIdx

private theorem isNonPtrScalarKind_byteCodecScalarKind (k : RigidTy)
    (hk : isNonPtrScalarKind k = true) :
    isNonPtrScalarKind (byteCodecScalarKind k) = true := by
  cases k with
  | float fk => cases fk <;> rfl
  | bool | char | int _ | uint _ => exact hk
  | _ => cases hk

private theorem all_isNonPtrScalarKind_mapByteCodecScalarKinds (ks : List RigidTy)
    (hks : ks.all isNonPtrScalarKind = true) :
    (mapByteCodecScalarKinds ks).all isNonPtrScalarKind = true := by
  induction ks with
  | nil => rfl
  | cons k rest ih =>
    have hk : isNonPtrScalarKind k = true := bool_and_true_left hks
    have hrest : rest.all isNonPtrScalarKind = true := bool_and_true_right hks
    show (isNonPtrScalarKind (byteCodecScalarKind k) &&
        (mapByteCodecScalarKinds rest).all isNonPtrScalarKind) = true
    rw [isNonPtrScalarKind_byteCodecScalarKind k hk, ih hrest]
    rfl

/-- **Composite erasure characterization (tuples of non-pointer scalars)**:
for every tuple `(T_0, ..., T_{k-1})` where every `T_i` is a non-pointer scalar
(e.g. `(u32, u32)`, `(u8, bool, u16)`), `.stripProvenance` decoding equals
`.strictUcg630Ub` decoding of the provenance-erased bytes (under sequential,
offset-only, or field-layout-backed tuple decoding). -/
theorem decodeTypedValueFromBytesWithPolicy_strip_tuple_scalar_eq_strict_erased
    (fuel : Nat) (layouts : LayoutTable) (ks : List RigidTy)
    (layoutIdx : LayoutIdx) (bytes : List AbstractByte)
    (hks : ks.all isNonPtrScalarKind = true) :
    decodeTypedValueFromBytesWithPolicy .stripProvenance (.succ (.succ fuel)) layouts
        { kind := .tuple ks, layoutIdx := layoutIdx } bytes =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub (.succ (.succ fuel)) layouts
        { kind := .tuple ks, layoutIdx := layoutIdx } (stripAbstractBytesProv bytes) := by
  cases ks with
  | nil =>
    unfold decodeTypedValueFromBytesWithPolicy
    dsimp only [normalizeCodecTy]
    cases bytes <;> rfl
  | cons kHead kTail =>
    have hks' : (byteCodecScalarKind kHead :: mapByteCodecScalarKinds kTail).all isNonPtrScalarKind = true :=
      all_isNonPtrScalarKind_mapByteCodecScalarKinds (kHead :: kTail) hks
    unfold decodeTypedValueFromBytesWithPolicy
    dsimp only [normalizeCodecTy, mapByteCodecScalarKinds]
    rw [length_stripAbstractBytesProv]
    have hel : ∀ k lIdx bs, isNonPtrScalarKind k = true →
        decodeTypedValueFromBytesWithPolicy .stripProvenance (.succ fuel) layouts
            { kind := k, layoutIdx := lIdx } bs =
          decodeTypedValueFromBytesWithPolicy .strictUcg630Ub (.succ fuel) layouts
            { kind := k, layoutIdx := lIdx } (stripAbstractBytesProv bs) :=
      fun k lIdx bs hk =>
        decodeTypedValueFromBytesWithPolicy_strip_scalar_eq_strict_erased (.succ fuel) layouts
          { kind := k, layoutIdx := lIdx } bs hk
    cases LayoutTable.lookup layouts layoutIdx with
    | none =>
      dsimp only
      rw [decodeSeqFieldsWith_strip_eq_strict_erased _ _ _ isNonPtrScalarKind
        (fun k bs hk => hel k 0 bs hk) _ bytes hks']
    | some l =>
      dsimp only
      cases Nat.beq (length bytes) l.size.bytes with
      | false => rfl
      | true =>
        cases l.fields with
        | arbitrary offsets _ =>
          dsimp only
          cases Bool.and (Nat.beq (length (byteCodecScalarKind kHead :: mapByteCodecScalarKinds kTail)) (length offsets))
              (Nat.beq (length l.fieldLayouts) (length offsets)) with
          | true =>
            rw [decodeTypedKindsAndLayoutsAtOffsets_strip_eq_strict_erased _ _ layouts bytes
              isNonPtrScalarKind hel offsets _ l.fieldLayouts hks']
          | false =>
            rw [decodeFieldsAtOffsetsWith_strip_eq_strict_erased _ _ _ bytes isNonPtrScalarKind
              (fun k bs hk => hel k 0 bs hk) offsets _ hks']
        | _ =>
          dsimp only
          rw [decodeSeqFieldsWith_strip_eq_strict_erased _ _ _ isNonPtrScalarKind
            (fun k bs hk => hel k 0 bs hk) _ bytes hks']

/-- **Hybrid erasure characterization for wide slice / `str` pointers**:
decoding a wide slice or `str` pointer (`*const [T]`, `&[T]`, `*const str`,
`&str`) under `.stripProvenance` preserves the data-pointer half's provenance
intact and equals `.strictUcg630Ub` decoding on the byte list whose length
metadata half alone has its provenance erased! -/
theorem decodePtrBytesNoForgeWithPolicy_strip_wideSlice_eq_strict_meta_erased
    (isRef : Bool) (pointee : RigidTy) (ptrBytes : Nat) (bytes : List AbstractByte)
    (hslice : (∃ elem, pointee = .slice elem) ∨ pointee = .str)
    (hlen : length bytes = Nat.add ptrBytes ptrBytes) :
    decodePtrBytesNoForgeWithPolicy .stripProvenance isRef pointee ptrBytes bytes =
      decodePtrBytesNoForgeWithPolicy .strictUcg630Ub isRef pointee ptrBytes
        (appendAbstractBytes (takeAbstractBytes ptrBytes bytes)
          (stripAbstractBytesProv (dropAbstractBytes ptrBytes bytes))) := by
  let dataBs := takeAbstractBytes ptrBytes bytes
  let metaBs := dropAbstractBytes ptrBytes bytes
  have hle : ptrBytes ≤ length bytes := by rw [hlen]; exact Nat.le_add_right ptrBytes ptrBytes
  have hdata_len : length dataBs = ptrBytes := length_takeAbstractBytes_of_le ptrBytes bytes hle
  have hmeta_len : length metaBs = ptrBytes := by
    dsimp only [metaBs]; rw [length_dropAbstractBytes, hlen]; exact Nat.add_sub_cancel_left ptrBytes ptrBytes
  have happ_len : length (appendAbstractBytes dataBs (stripAbstractBytesProv metaBs)) =
      Nat.add ptrBytes ptrBytes := by
    rw [length_appendAbstractBytes, hdata_len, length_stripAbstractBytesProv, hmeta_len]
    rfl
  have htake : takeAbstractBytes ptrBytes
      (appendAbstractBytes dataBs (stripAbstractBytesProv metaBs)) = dataBs :=
    takeAbstractBytes_append_left ptrBytes dataBs (stripAbstractBytesProv metaBs) hdata_len
  have hdrop : dropAbstractBytes ptrBytes
      (appendAbstractBytes dataBs (stripAbstractBytesProv metaBs)) = stripAbstractBytesProv metaBs :=
    dropAbstractBytes_append_left ptrBytes dataBs (stripAbstractBytesProv metaBs) hdata_len
  rcases hslice with ⟨elem, rfl⟩ | rfl
  all_goals
    unfold decodePtrBytesNoForgeWithPolicy
    dsimp only [policyRejectsProv]
    rw [hlen, happ_len, htake, hdrop, abstractBytesHaveProv_stripAbstractBytesProv,
      decodeScalarBytes_stripAbstractBytesProv]
    cases Nat.beq (Nat.add ptrBytes ptrBytes) (Nat.add ptrBytes ptrBytes) with
    | false => rfl
    | true =>
      dsimp only
      cases decodeScalarBytes metaBs false with
      | none => rfl
      | some mp => rfl

/-! ### §10.1 Full Cast-Level Policy Independence (Refs, `fnPtr`, `dyn`, Unions, `[MaybeUninit<T>; N]`) -/

theorem evalByteCastWithPolicy_thinRef_policy_indep
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (m : Mutability) (pointee : RigidTy)
    (hk : (resolveTyWithLocalDecls localDecls layouts targetTy).kind = .ref m pointee)
    (hthin : isThinPtrKind (.ref m pointee) = true) :
    evalByteCastWithPolicy .stripProvenance locals op targetTy mem localDecls layouts =
      evalByteCastWithPolicy .strictUcg630Ub locals op targetTy mem localDecls layouts := by
  apply evalByteCastWithPolicy_policy_indep_of_decode_indep
  intro bs
  generalize resolveTyWithLocalDecls localDecls layouts targetTy = rT at hk
  cases rT with
  | mk k l =>
    dsimp only at hk; subst hk
    exact decodeTypedValueFromBytesWithPolicy_thinRef_policy_indep 15 layouts m pointee l bs hthin

theorem evalByteCastWithPolicy_fnPtr_policy_indep
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (inputs : List RigidTy) (output : RigidTy) (safety : Safety) (abi : CallConv)
    (hk : (resolveTyWithLocalDecls localDecls layouts targetTy).kind =
      .fnPtr inputs output safety abi) :
    evalByteCastWithPolicy .stripProvenance locals op targetTy mem localDecls layouts =
      evalByteCastWithPolicy .strictUcg630Ub locals op targetTy mem localDecls layouts := by
  apply evalByteCastWithPolicy_policy_indep_of_decode_indep
  intro bs
  generalize resolveTyWithLocalDecls localDecls layouts targetTy = rT at hk
  cases rT with
  | mk k l =>
    dsimp only at hk; subst hk
    exact decodeTypedValueFromBytesWithPolicy_fnPtr_policy_indep 15 layouts inputs output safety
      abi l bs

theorem evalByteCastWithPolicy_wideDynPtr_policy_indep
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (m : Mutability) (traitPath : DefPath)
    (hk : (resolveTyWithLocalDecls localDecls layouts targetTy).kind = .rawPtr m (.dynamic traitPath)) :
    evalByteCastWithPolicy .stripProvenance locals op targetTy mem localDecls layouts =
      evalByteCastWithPolicy .strictUcg630Ub locals op targetTy mem localDecls layouts := by
  apply evalByteCastWithPolicy_policy_indep_of_decode_indep
  intro bs
  generalize resolveTyWithLocalDecls localDecls layouts targetTy = rT at hk
  cases rT with
  | mk k l =>
    dsimp only at hk; subst hk
    exact decodeTypedValueFromBytesWithPolicy_wideDynPtr_policy_indep 15 layouts m traitPath l bs

theorem evalByteCastWithPolicy_wideDynRef_policy_indep
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (m : Mutability) (traitPath : DefPath)
    (hk : (resolveTyWithLocalDecls localDecls layouts targetTy).kind = .ref m (.dynamic traitPath)) :
    evalByteCastWithPolicy .stripProvenance locals op targetTy mem localDecls layouts =
      evalByteCastWithPolicy .strictUcg630Ub locals op targetTy mem localDecls layouts := by
  apply evalByteCastWithPolicy_policy_indep_of_decode_indep
  intro bs
  generalize resolveTyWithLocalDecls localDecls layouts targetTy = rT at hk
  cases rT with
  | mk k l =>
    dsimp only at hk; subst hk
    exact decodeTypedValueFromBytesWithPolicy_wideDynRef_policy_indep 15 layouts m traitPath l bs

theorem evalByteCastWithPolicy_union_policy_indep
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (defPath : DefPath) (args : List RigidTy) (l : TypeLayout) (count : Nat)
    (hk : (resolveTyWithLocalDecls localDecls layouts targetTy).kind = .adt defPath args)
    (hlk : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts targetTy).layoutIdx =
      .some l)
    (hvar : l.variants = .single 0) (hfld : l.fields = .union count) :
    evalByteCastWithPolicy .stripProvenance locals op targetTy mem localDecls layouts =
      evalByteCastWithPolicy .strictUcg630Ub locals op targetTy mem localDecls layouts := by
  apply evalByteCastWithPolicy_policy_indep_of_decode_indep
  intro bs
  generalize resolveTyWithLocalDecls localDecls layouts targetTy = rT at hk hlk
  cases rT with
  | mk k lIdx =>
    dsimp only at hk hlk; subst hk
    exact decodeTypedValueFromBytesWithPolicy_union_policy_indep 15 layouts defPath args lIdx l
      count bs hlk hvar hfld

/-- Full cast-level policy independence for `[MaybeUninit<T>; N]` (or any array
of union elements): `transmute::<S, [MaybeUninit<u8>; N]>` evaluates identically
under both policies for every source operand, memory, and layout table. -/
theorem evalByteCastWithPolicy_unionArray_policy_indep
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (defPath : DefPath) (args : List RigidTy) (n : Nat)
    (elemFlIdx : LayoutIdx) (arrL elemL : TypeLayout) (stride : Size)
    (cnt count : Nat) (restFl : List LayoutIdx)
    (hk : (resolveTyWithLocalDecls localDecls layouts targetTy).kind =
      .array (.adt defPath args) n)
    (harr : LayoutTable.lookup layouts
      (resolveTyWithLocalDecls localDecls layouts targetTy).layoutIdx = .some arrL)
    (hfields : arrL.fields = .array stride cnt)
    (hfl : arrL.fieldLayouts = elemFlIdx :: restFl)
    (helem : LayoutTable.lookup layouts elemFlIdx = .some elemL)
    (hvar : elemL.variants = .single 0) (hfld : elemL.fields = .union count) :
    evalByteCastWithPolicy .stripProvenance locals op targetTy mem localDecls layouts =
      evalByteCastWithPolicy .strictUcg630Ub locals op targetTy mem localDecls layouts := by
  apply evalByteCastWithPolicy_policy_indep_of_decode_indep
  intro bs
  generalize resolveTyWithLocalDecls localDecls layouts targetTy = rT at hk harr
  cases rT with
  | mk k lIdx =>
    dsimp only at hk harr; subst hk
    exact decodeTypedValueFromBytesWithPolicy_unionArray_policy_indep 14 layouts defPath args n
      lIdx elemFlIdx arrL elemL stride cnt count restFl bs harr hfields hfl helem hvar hfld

/-! ### §10.2 Prototyped TCB Fix for Finding #3 (Policy-Aware Multi-Variant Enum Decoding) -/

/-- Proposed TCB replacement for the `Places.lean:8055` `.multiple`-variant enum
fallback (Finding #3): decodes the discriminant tag via
`decodeScalarLayoutBytesWithPolicy policy` and gates span-based payload
decoding with `policyRejectsProv policy bytes`. -/
def decodeMultiVariantEnumWithPolicy
    (policy : Ptr2IntTransmutePolicy)
    (l : TypeLayout)
    (tagLayout : ScalarLayout)
    (tagField : Nat)
    (variantShapes : List FieldsShape)
    (bytes : List AbstractByte) :
    Option Value :=
  match Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => .none
  | false =>
    match l.fields, scalarLayoutByteWidth tagLayout with
    | .arbitrary outerOffsets _, .some tagSz =>
      match get? outerOffsets tagField with
      | .none => .none
      | .some tagOff =>
        match sliceAbstractBytes bytes tagOff.bytes tagSz with
        | .none => .none
        | .some tagSlice =>
          match decodeScalarLayoutBytesWithPolicy policy tagLayout tagSlice with
          | .some (.scalar tagSc) =>
            let varIdx := tagSc.bits
            match get? variantShapes varIdx with
            | .some (.arbitrary varOffsets _) =>
              match policyRejectsProv policy bytes with
              | true => .none
              | false =>
                match decodeFieldsBySpan bytes l.size.bytes varOffsets with
                | .some vals => .some (.aggregate varIdx vals)
                | .none => .none
            | _ => .none
          | _ => .none
    | _, _ => .none

theorem decodeMultiVariantEnumWithPolicy_strict_refines_strip
    (l : TypeLayout) (tagLayout : ScalarLayout) (tagField : Nat)
    (variantShapes : List FieldsShape) (bytes : List AbstractByte) (v : Value)
    (h : decodeMultiVariantEnumWithPolicy .strictUcg630Ub l tagLayout tagField variantShapes bytes =
      .some v) :
    decodeMultiVariantEnumWithPolicy .stripProvenance l tagLayout tagField variantShapes bytes =
      .some v := by
  unfold decodeMultiVariantEnumWithPolicy at h ⊢
  cases hbad : Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => rw [hbad] at h; cases h
  | false =>
    rw [hbad] at h; dsimp only at h ⊢
    cases hf : l.fields with
    | arbitrary outerOffsets _ =>
      rw [hf] at h
      cases htw : scalarLayoutByteWidth tagLayout with
      | none => rw [htw] at h; cases h
      | some tagSz =>
        rw [htw] at h; dsimp only at h ⊢
        cases hg : get? outerOffsets tagField with
        | none => rw [hg] at h; cases h
        | some tagOff =>
          rw [hg] at h; dsimp only at h ⊢
          cases hsl : sliceAbstractBytes bytes tagOff.bytes tagSz with
          | none => rw [hsl] at h; cases h
          | some tagSlice =>
            rw [hsl] at h; dsimp only at h ⊢
            cases htd : decodeScalarLayoutBytesWithPolicy .strictUcg630Ub tagLayout tagSlice with
            | none => rw [htd] at h; cases h
            | some tv =>
              rw [htd] at h
              rw [decodeScalarLayoutBytesWithPolicy_strict_refines_strip tagLayout tagSlice tv htd]
              cases tv with
              | scalar tagSc =>
                dsimp only at h ⊢
                cases hvs : get? variantShapes tagSc.bits with
                | none => rw [hvs] at h; cases h
                | some vs =>
                  rw [hvs] at h
                  cases vs with
                  | arbitrary varOffsets _ =>
                    dsimp only [policyRejectsProv] at h ⊢
                    cases hp : abstractBytesHaveProv bytes with
                    | true => rw [hp] at h; cases h
                    | false => rw [hp] at h; exact h
                  | _ => cases h
              | _ => cases h
    | _ => rw [hf] at h; cases h

theorem decodeMultiVariantEnumWithPolicy_strip_eq_strict_erased
    (l : TypeLayout) (tagLayout : ScalarLayout) (tagField : Nat)
    (variantShapes : List FieldsShape) (bytes : List AbstractByte)
    (htag_np : scalarLayoutIsPointer tagLayout = false) :
    decodeMultiVariantEnumWithPolicy .stripProvenance l tagLayout tagField variantShapes bytes =
      decodeMultiVariantEnumWithPolicy .strictUcg630Ub l tagLayout tagField variantShapes
        (stripAbstractBytesProv bytes) := by
  unfold decodeMultiVariantEnumWithPolicy
  rw [length_stripAbstractBytesProv]
  cases Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => rfl
  | false =>
    dsimp only
    cases l.fields with
    | arbitrary outerOffsets _ =>
      cases scalarLayoutByteWidth tagLayout with
      | none => rfl
      | some tagSz =>
        dsimp only
        cases get? outerOffsets tagField with
        | none => rfl
        | some tagOff =>
          dsimp only
          rw [sliceAbstractBytes_stripAbstractBytesProv]
          cases sliceAbstractBytes bytes tagOff.bytes tagSz with
          | none => rfl
          | some tagSlice =>
            dsimp only
            rw [decodeScalarLayoutBytesWithPolicy_strip_eq_strict_erased tagLayout tagSlice htag_np]
            cases decodeScalarLayoutBytesWithPolicy .strictUcg630Ub tagLayout
                (stripAbstractBytesProv tagSlice) with
            | none => rfl
            | some tv =>
              cases tv with
              | scalar tagSc =>
                dsimp only
                cases get? variantShapes tagSc.bits with
                | none => rfl
                | some vs =>
                  cases vs with
                  | arbitrary varOffsets _ =>
                    dsimp only [policyRejectsProv]
                    rw [abstractBytesHaveProv_stripAbstractBytesProv,
                      decodeFieldsBySpan_stripAbstractBytesProv]
                  | _ => rfl
              | _ => rfl
    | _ => rfl

/-- Witness (`by rfl`) that `decodeMultiVariantEnumWithPolicy` closes Finding #3:
on `enum E { A(u32), B(u32) }` and provenance-carrying pointer bytes, the strict
policy now rejects with `.none` (matching `(u32, u32)`) while `.stripProvenance`
decodes `.some (.aggregate 1 [.scalar ⟨42, 4⟩])` and provenance-free bytes
decode identically under both policies. -/
theorem multiVariant_enum_fix_separation_witness :
    decodeMultiVariantEnumWithPolicy .strictUcg630Ub protoTwoVariantEnumLayout
        (.initialized (.int 32 false) ⟨0, 1⟩) 0
        [.arbitrary [{ bytes := 4 }] [0], .arbitrary [{ bytes := 4 }] [0]]
        (encodeLittleEndianBytes protoEnumShapedPtr.offsetBytes 8 (.some (7, 7))) = .none ∧
    decodeMultiVariantEnumWithPolicy .stripProvenance protoTwoVariantEnumLayout
        (.initialized (.int 32 false) ⟨0, 1⟩) 0
        [.arbitrary [{ bytes := 4 }] [0], .arbitrary [{ bytes := 4 }] [0]]
        (encodeLittleEndianBytes protoEnumShapedPtr.offsetBytes 8 (.some (7, 7))) =
      .some (.aggregate 1 [.scalar ⟨42, 4⟩]) ∧
    decodeMultiVariantEnumWithPolicy .strictUcg630Ub protoTwoVariantEnumLayout
        (.initialized (.int 32 false) ⟨0, 1⟩) 0
        [.arbitrary [{ bytes := 4 }] [0], .arbitrary [{ bytes := 4 }] [0]]
        (encodeLittleEndianBytes protoEnumShapedPtr.offsetBytes 8 .none) =
      .some (.aggregate 1 [.scalar ⟨42, 4⟩]) := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## §11. Sign Symmetry of Rounding, Sign-Symmetric Arithmetic & Multiplicative Identities -/

private def rrExponent (f : IeeeFormat) (n d : Nat) : Int :=
  max (ratioExponent n d) f.minExponent

private def rrSignificand (f : IeeeFormat) (n d : Nat) : Nat :=
  roundQuotientTiesToEven
    (powScale n d ((f.fractionBits : Int) - rrExponent f n d)).1
    (powScale n d ((f.fractionBits : Int) - rrExponent f n d)).2

private def rrCarry (f : IeeeFormat) (n d : Nat) : Bool :=
  decide (2 ^ (f.fractionBits + 1) ≤ rrSignificand f n d)

private def rrSignificand' (f : IeeeFormat) (n d : Nat) : Nat :=
  if rrCarry f n d then rrSignificand f n d / 2 else rrSignificand f n d

private def rrExponent' (f : IeeeFormat) (n d : Nat) : Int :=
  if rrCarry f n d then rrExponent f n d + 1 else rrExponent f n d

/-- The trusted rounding core as a sign-independent decision tree: `neg` only
selects the sign of the emitted zero / infinity / encoded bit pattern. -/
private theorem roundRatioTiesToEven_eq_shape (f : IeeeFormat) (neg : Bool) (n d : Nat) :
    roundRatioTiesToEven f neg n d =
      if d = 0 then preferredNaNBits f
      else if n = 0 then zeroBits f neg
      else if rrExponent f n d > f.maxExponent then infBits f neg
      else if rrExponent' f n d > f.maxExponent then infBits f neg
      else if rrSignificand' f n d < 2 ^ f.fractionBits then
        (if rrExponent' f n d = f.minExponent then encodeBits f neg 0 (rrSignificand' f n d)
         else preferredNaNBits f)
      else if 2 ^ (f.fractionBits + 1) ≤ rrSignificand' f n d then preferredNaNBits f
      else encodeBits f neg (rrExponent' f n d + (f.bias : Int)).toNat
        (rrSignificand' f n d - 2 ^ f.fractionBits) := rfl

/-- **Sign symmetry of `roundTiesToEven`**: rounding the exact rational with the
opposite sign yields exactly the bitwise negation (round-to-nearest-even is an
odd function, including underflow to `±0`, subnormals, and overflow to `±Inf`). -/
theorem roundRatioTiesToEven_not_neg (f : IeeeFormat) (neg : Bool) (n d : Nat) (hd : 0 < d) :
    roundRatioTiesToEven f (!neg) n d =
      evalFloatNegProto f (roundRatioTiesToEven f neg n d) := by
  have hnn := roundRatioTiesToEven_not_nan f neg n d hd
  have hpn := isNaNBits_preferredNaNBits f
  rw [roundRatioTiesToEven_eq_shape] at hnn
  rw [roundRatioTiesToEven_eq_shape f (!neg), roundRatioTiesToEven_eq_shape f neg]
  have hd0 : ¬ d = 0 := by omega
  rw [if_neg' hd0] at hnn
  rw [if_neg' hd0, if_neg' hd0]
  by_cases hn0 : n = 0
  · rw [if_pos' hn0, if_pos' hn0]
    exact (evalFloatNegProto_zeroBits f neg).symm
  · rw [if_neg' hn0] at hnn
    rw [if_neg' hn0, if_neg' hn0]
    by_cases he : rrExponent f n d > f.maxExponent
    · rw [if_pos' he, if_pos' he]
      exact (evalFloatNegProto_infBits f neg).symm
    · rw [if_neg' he] at hnn
      rw [if_neg' he, if_neg' he]
      by_cases he' : rrExponent' f n d > f.maxExponent
      · rw [if_pos' he', if_pos' he']
        exact (evalFloatNegProto_infBits f neg).symm
      · rw [if_neg' he'] at hnn
        rw [if_neg' he', if_neg' he']
        by_cases hs : rrSignificand' f n d < 2 ^ f.fractionBits
        · rw [if_pos' hs] at hnn
          rw [if_pos' hs, if_pos' hs]
          by_cases hm : rrExponent' f n d = f.minExponent
          · rw [if_pos' hm, if_pos' hm]
            exact (evalFloatNegProto_encodeBits f neg 0 _ (Nat.two_pow_pos _) hs).symm
          · rw [if_neg' hm, hpn] at hnn
            cases hnn
        · rw [if_neg' hs] at hnn
          rw [if_neg' hs, if_neg' hs]
          by_cases hbig : 2 ^ (f.fractionBits + 1) ≤ rrSignificand' f n d
          · rw [if_pos' hbig, hpn] at hnn
            cases hnn
          · rw [if_neg' hbig, if_neg' hbig]
            have hbias := IeeeFormat.two_bias_lt f
            have htwo : 2 ^ (f.fractionBits + 1) = 2 * 2 ^ f.fractionBits := by
              rw [Nat.pow_succ]; omega
            have hE : (rrExponent' f n d + (f.bias : Int)).toNat < 2 ^ f.exponentBits := by
              unfold IeeeFormat.maxExponent at he'
              omega
            have hF : rrSignificand' f n d - 2 ^ f.fractionBits < 2 ^ f.fractionBits := by omega
            exact (evalFloatNegProto_encodeBits f neg _ _ hE hF).symm

private theorem bool_xor_not_left (p q : Bool) : xor (!p) q = !(xor p q) := by
  cases p <;> cases q <;> rfl

private theorem bool_xor_not_right (p q : Bool) : xor p (!q) = !(xor p q) := by
  cases p <;> cases q <;> rfl

/-- `(-a) * b = -(a * b)` bit-for-bit whenever the product is not NaN. -/
theorem evalFloatArithBaseProto_mul_neg_left (f : IeeeFormat) (a b : Nat)
    (hnan : isNaNBits f (evalFloatArithBaseProto .mul f a b) = false) :
    evalFloatArithBaseProto .mul f (evalFloatNegProto f a) b =
      evalFloatNegProto f (evalFloatArithBaseProto .mul f a b) := by
  have hpn := isNaNBits_preferredNaNBits f
  unfold evalFloatArithBaseProto at hnan ⊢
  rw [decodeBits_evalFloatNegProto]
  cases hl : decodeBits f a with
  | nan _ _ _ => rw [hl] at hnan; cases hpn.symm.trans hnan
  | inf ln =>
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | zero _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | inf rn =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_left, evalFloatNegProto_infBits]
    | finite rn _ _ =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_left, evalFloatNegProto_infBits]
  | zero ln =>
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | inf _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | zero rn =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_left, evalFloatNegProto_zeroBits]
    | finite rn _ _ =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_left, evalFloatNegProto_zeroBits]
  | finite ln lnum lden =>
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | inf rn =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_left, evalFloatNegProto_infBits]
    | zero rn =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_left, evalFloatNegProto_zeroBits]
    | finite rn rnum rden =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_left]
      exact roundRatioTiesToEven_not_neg f _ _ _
        (Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden hl)
          (decodeBits_finite_den_pos f b rn rnum rden hr))

/-- `a * (-b) = -(a * b)` bit-for-bit whenever the product is not NaN. -/
theorem evalFloatArithBaseProto_mul_neg_right (f : IeeeFormat) (a b : Nat)
    (hnan : isNaNBits f (evalFloatArithBaseProto .mul f a b) = false) :
    evalFloatArithBaseProto .mul f a (evalFloatNegProto f b) =
      evalFloatNegProto f (evalFloatArithBaseProto .mul f a b) := by
  rw [evalFloatArithBaseProto_mul_comm f a (evalFloatNegProto f b),
    evalFloatArithBaseProto_mul_comm f a b]
  rw [evalFloatArithBaseProto_mul_comm f a b] at hnan
  exact evalFloatArithBaseProto_mul_neg_left f b a hnan

/-- `(-a) / b = -(a / b)` bit-for-bit whenever the quotient is not NaN. -/
theorem evalFloatArithBaseProto_div_neg_left (f : IeeeFormat) (a b : Nat)
    (hnan : isNaNBits f (evalFloatArithBaseProto .div f a b) = false) :
    evalFloatArithBaseProto .div f (evalFloatNegProto f a) b =
      evalFloatNegProto f (evalFloatArithBaseProto .div f a b) := by
  have hpn := isNaNBits_preferredNaNBits f
  unfold evalFloatArithBaseProto at hnan ⊢
  rw [decodeBits_evalFloatNegProto]
  cases hl : decodeBits f a with
  | nan _ _ _ => rw [hl] at hnan; cases hpn.symm.trans hnan
  | inf ln =>
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | inf _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | zero rn =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_left, evalFloatNegProto_infBits]
    | finite rn _ _ =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_left, evalFloatNegProto_infBits]
  | zero ln =>
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | zero _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | inf rn =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_left, evalFloatNegProto_zeroBits]
    | finite rn _ _ =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_left, evalFloatNegProto_zeroBits]
  | finite ln lnum lden =>
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | zero rn =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_left, evalFloatNegProto_infBits]
    | inf rn =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_left, evalFloatNegProto_zeroBits]
    | finite rn rnum rden =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_left]
      exact roundRatioTiesToEven_not_neg f _ _ _
        (Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden hl)
          (decodeBits_finite_num_pos f b rn rnum rden hr))

/-- `a / (-b) = -(a / b)` bit-for-bit whenever the quotient is not NaN. -/
theorem evalFloatArithBaseProto_div_neg_right (f : IeeeFormat) (a b : Nat)
    (hnan : isNaNBits f (evalFloatArithBaseProto .div f a b) = false) :
    evalFloatArithBaseProto .div f a (evalFloatNegProto f b) =
      evalFloatNegProto f (evalFloatArithBaseProto .div f a b) := by
  have hpn := isNaNBits_preferredNaNBits f
  unfold evalFloatArithBaseProto at hnan ⊢
  rw [decodeBits_evalFloatNegProto]
  cases hl : decodeBits f a with
  | nan _ _ _ => rw [hl] at hnan; cases hpn.symm.trans hnan
  | inf ln =>
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | inf _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | zero rn =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_right, evalFloatNegProto_infBits]
    | finite rn _ _ =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_right, evalFloatNegProto_infBits]
  | zero ln =>
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | zero _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | inf rn =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_right, evalFloatNegProto_zeroBits]
    | finite rn _ _ =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_right, evalFloatNegProto_zeroBits]
  | finite ln lnum lden =>
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | zero rn =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_right, evalFloatNegProto_infBits]
    | inf rn =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_right, evalFloatNegProto_zeroBits]
    | finite rn rnum rden =>
      dsimp only [negateFloatKind]
      rw [bool_xor_not_right]
      exact roundRatioTiesToEven_not_neg f _ _ _
        (Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden hl)
          (decodeBits_finite_num_pos f b rn rnum rden hr))

/-- `(-a) % b = -(a % b)` bit-for-bit whenever the remainder is not NaN (the
remainder is an odd function of the dividend). -/
theorem evalFloatArithBaseProto_rem_neg_left (f : IeeeFormat) (a b : Nat)
    (hnan : isNaNBits f (evalFloatArithBaseProto .rem f a b) = false) :
    evalFloatArithBaseProto .rem f (evalFloatNegProto f a) b =
      evalFloatNegProto f (evalFloatArithBaseProto .rem f a b) := by
  have hpn := isNaNBits_preferredNaNBits f
  have hmodneg : evalFloatNegProto f a % 2 ^ f.width = evalFloatNegProto f (a % 2 ^ f.width) := by
    rw [Nat.mod_eq_of_lt (evalFloatNegProto_lt f a), evalFloatNegProto_mod]
  unfold evalFloatArithBaseProto at hnan ⊢
  rw [decodeBits_evalFloatNegProto]
  cases hl : decodeBits f a with
  | nan _ _ _ => rw [hl] at hnan; cases hpn.symm.trans hnan
  | inf _ =>
    rw [hl] at hnan
    cases hr : decodeBits f b <;> rw [hr] at hnan <;> cases hpn.symm.trans hnan
  | zero ln =>
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | zero _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | inf _ => dsimp only [negateFloatKind]; exact hmodneg
    | finite _ _ _ => dsimp only [negateFloatKind]; rw [evalFloatNegProto_zeroBits]
  | finite ln lnum lden =>
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | zero _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | inf _ => dsimp only [negateFloatKind]; exact hmodneg
    | finite rn rnum rden =>
      dsimp only [negateFloatKind]
      exact roundRatioTiesToEven_not_neg f _ _ _
        (Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden hl)
          (decodeBits_finite_den_pos f b rn rnum rden hr))

/-- `a % (-b) = a % b` unconditionally, for all bit patterns: the truncated
remainder ignores the divisor's sign (also on NaN results, which are always the
preferred NaN). -/
theorem evalFloatArithBaseProto_rem_neg_right (f : IeeeFormat) (a b : Nat) :
    evalFloatArithBaseProto .rem f a (evalFloatNegProto f b) =
      evalFloatArithBaseProto .rem f a b := by
  unfold evalFloatArithBaseProto
  rw [decodeBits_evalFloatNegProto]
  cases decodeBits f a <;> cases decodeBits f b <;> rfl

/-- Bit pattern of `1.0` in format `f`. -/
def oneBitsProto (f : IeeeFormat) : Nat := encodeBits f false f.bias 0

theorem decodeBits_oneBitsProto (f : IeeeFormat) :
    decodeBits f (oneBitsProto f) = .finite false (2 ^ f.fractionBits) (2 ^ f.fractionBits) := by
  cases f <;> rfl

private theorem bool_xor_false_right (p : Bool) : xor p false = p := by
  cases p <;> rfl

/-- `x * 1.0 = x` and `x / 1.0 = x` exactly (canonical bit pattern) for every
non-NaN `x`: signed zeros, subnormals, normals, and infinities are fixed points
(no spurious rounding or sign change). -/
theorem evalFloatArithBaseProto_mul_div_one_right (f : IeeeFormat) (x : Nat)
    (hx : isNaNBits f x = false) :
    evalFloatArithBaseProto .mul f x (oneBitsProto f) = x % 2 ^ f.width ∧
      evalFloatArithBaseProto .div f x (oneBitsProto f) = x % 2 ^ f.width := by
  have hmod : x % 2 ^ f.width < 2 ^ f.width := Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold evalFloatArithBaseProto
  rw [decodeBits_oneBitsProto, ← decodeBits_mod_width f x]
  unfold isNaNBits at hx
  rw [← decodeBits_mod_width f x] at hx
  cases hd : decodeBits f (x % 2 ^ f.width) with
  | nan _ _ _ => rw [hd] at hx; cases hx
  | inf ln =>
    dsimp only
    rw [bool_xor_false_right]
    exact ⟨(bits_eq_infBits_of_decodeBits_inf f _ ln hmod hd).symm,
      (bits_eq_infBits_of_decodeBits_inf f _ ln hmod hd).symm⟩
  | zero ln =>
    dsimp only
    rw [bool_xor_false_right]
    exact ⟨(bits_eq_zeroBits_of_decodeBits_zero f _ ln hmod hd).symm,
      (bits_eq_zeroBits_of_decodeBits_zero f _ ln hmod hd).symm⟩
  | finite ln lnum lden =>
    dsimp only
    rw [bool_xor_false_right]
    have hden := decodeBits_finite_den_pos f _ ln lnum lden hd
    have hpow : 0 < 2 ^ f.fractionBits := Nat.two_pow_pos _
    have hcongr : roundRatioTiesToEven f ln (lnum * 2 ^ f.fractionBits)
        (lden * 2 ^ f.fractionBits) = roundRatioTiesToEven f ln lnum lden := by
      rw [← roundRatioBits_tiesToEven, ← roundRatioBits_tiesToEven]
      exact roundRatioBits_congr .tiesToEven f ln _ _ _ _ (Nat.mul_pos hden hpow) hden
        (by rw [Nat.mul_right_comm, Nat.mul_assoc])
    rw [hcongr]
    exact ⟨roundRatioTiesToEven_eq_bits_of_decodeBits_finite f _ ln lnum lden hmod hd,
      roundRatioTiesToEven_eq_bits_of_decodeBits_finite f _ ln lnum lden hmod hd⟩

/-! ## §12. Multi-Variant Enum Fix: TCB Conservativity, Pointer-Payload Regression & Typed Per-Variant Decoding -/

/-- A decoded scalar always carries the byte length of its image. -/
theorem decodeScalarBytes_sizeBytes (bytes : List AbstractByte) (signed : Bool)
    (p : ScalarVal × Option (Nat × Nat)) (h : decodeScalarBytes bytes signed = .some p) :
    p.1.sizeBytes = length bytes := by
  unfold decodeScalarBytes at h
  dsimp only at h
  cases hz : Nat.beq (length bytes) 0 with
  | true => rw [hz] at h; cases h
  | false =>
    rw [hz] at h
    cases hd : decodeLittleEndianBytes bytes with
    | none => rw [hd] at h; cases h
    | some q =>
      rw [hd] at h
      cases q with
      | mk bits prov =>
        injection h with hp
        rw [← hp]

/-- On integer scalar layouts other than the 4-byte `char` range
(`0..=0x10FFFF`), `.stripProvenance` decoding coincides with the trusted
provenance-oblivious `Bytes.decodeScalarLayoutBytes` (the decoder used by the
TCB for multi-variant enum tags). On the 4-byte `char` range the policy decoder
is additionally stricter (it rejects surrogates). -/
theorem decodeScalarLayoutBytesWithPolicy_strip_eq_trusted_int
    (bits : Nat) (signed : Bool) (vr : WrappingRange) (bytes : List AbstractByte)
    (hnotchar : Bool.and (Nat.beq (Nat.div bits 8) 4)
      (Bool.and (Nat.beq vr.start 0) (Nat.beq vr.end_ 0x10FFFF)) = false) :
    decodeScalarLayoutBytesWithPolicy .stripProvenance (.initialized (.int bits signed) vr) bytes =
      decodeScalarLayoutBytes (.initialized (.int bits signed) vr) bytes := by
  unfold decodeScalarLayoutBytesWithPolicy decodeScalarLayoutBytes
  dsimp only [scalarLayoutByteWidth, primitiveKindByteWidth]
  cases Nat.beq bits 0 with
  | true => rfl
  | false =>
    dsimp only
    cases hlen : Nat.beq (length bytes) (Nat.div bits 8) with
    | false => rfl
    | true =>
      dsimp only [policyRejectsProv]
      cases hsc : decodeScalarBytes bytes false with
      | none => rfl
      | some p =>
        have hsz : p.1.sizeBytes = Nat.div bits 8 :=
          (decodeScalarBytes_sizeBytes bytes false p hsc).trans (Nat.eq_of_beq_eq_true hlen)
        cases p with
        | mk sv prov =>
          dsimp only at hsz ⊢
          cases wrappingRangeContains vr sv.bits with
          | false => rfl
          | true =>
            dsimp only
            rw [hsz, hnotchar]

/-- **Conservativity of the proposed enum fix at `.stripProvenance`**: on every
multi-variant enum layout whose tag decodes identically under the policy
decoder and the trusted tag decoder (e.g. every integer tag outside the 4-byte
`char` range, `decodeScalarLayoutBytesWithPolicy_strip_eq_trusted_int`),
`decodeMultiVariantEnumWithPolicy .stripProvenance` **is** today's trusted
`decodeTypedValueFromBytes` — for all byte images, with or without provenance.
Hence adopting the fix changes TCB behavior only under `.strictUcg630Ub`, and
there only by rejecting (`decodeMultiVariantEnumWithPolicy_strict_refines_strip`). -/
theorem decodeMultiVariantEnumWithPolicy_strip_eq_trusted
    (fuel : Nat) (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy)
    (layoutIdx : LayoutIdx) (l : TypeLayout) (tagLayout : ScalarLayout) (tagField : Nat)
    (variantShapes : List FieldsShape) (bytes : List AbstractByte)
    (hlk : LayoutTable.lookup layouts layoutIdx = .some l)
    (hvar : l.variants = .multiple tagLayout tagField variantShapes)
    (htag : ∀ bs, decodeScalarLayoutBytesWithPolicy .stripProvenance tagLayout bs =
      decodeScalarLayoutBytes tagLayout bs) :
    decodeTypedValueFromBytes (.succ fuel) layouts
        { kind := .adt defPath args, layoutIdx := layoutIdx } bytes =
      decodeMultiVariantEnumWithPolicy .stripProvenance l tagLayout tagField variantShapes
        bytes := by
  unfold decodeTypedValueFromBytes decodeMultiVariantEnumWithPolicy
  dsimp only [normalizeCodecTy]
  rw [hlk]
  dsimp only
  cases hu : Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => rfl
  | false =>
    dsimp only
    rw [hvar]
    dsimp only
    unfold decodeValueFromBytes
    dsimp only
    rw [hlk]
    dsimp only
    rw [hu]
    dsimp only
    rw [hvar]
    dsimp only
    cases l.fields with
    | arbitrary outerOffsets _ =>
      cases scalarLayoutByteWidth tagLayout with
      | none => rfl
      | some tagSz =>
        dsimp only
        cases get? outerOffsets tagField with
        | none => rfl
        | some tagOff =>
          dsimp only
          cases sliceAbstractBytes bytes tagOff.bytes tagSz with
          | none => rfl
          | some tagSlice =>
            dsimp only
            rw [htag]
            cases decodeScalarLayoutBytes tagLayout tagSlice with
            | none => rfl
            | some tv => cases tv <;> rfl
    | primitive => rfl
    | union _ => rfl
    | array _ _ => rfl

/-- `enum P { A(*const u8), B(*const u8) }`: `u64` tag at offset `0`, thin
pointer payload at offset `8` in both variants (layout index `1`), with the
payload field layout (a pointer scalar) at index `2`. -/
def protoPtrPayloadEnumLayout : TypeLayout := {
  size := { bytes := 16 }
  align := { bytes := 8 }
  backendRepr := .memory
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .multiple (.initialized (.int 64 false) ⟨0, 1⟩) 0
    [.arbitrary [{ bytes := 8 }] [0], .arbitrary [{ bytes := 8 }] [0]]
  isUninhabited := false
}

def protoPtrFieldLayout : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 8 }
  backendRepr := .scalar (.initialized (.pointer 0) ⟨0, scalarModulus 8 - 1⟩)
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

def protoU32FieldLayout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 4 }
  backendRepr := .scalar (.initialized (.int 32 false) ⟨0, scalarModulus 4 - 1⟩)
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

def protoTypedEnumLayouts : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries := [protoUnitLayout, protoPtrPayloadEnumLayout, protoPtrFieldLayout,
    protoTwoVariantEnumLayout, protoU32FieldLayout]
}

def protoPtrPayloadEnumTy : Ty := { kind := .adt "P" [], layoutIdx := 1 }

/-- Byte image of the genuine value `P::B(p)` with `p = (alloc 7, addr 0x1000)`:
a provenance-free tag `1` followed by an intact pointer image. No
pointer-to-integer reinterpretation is involved. -/
def protoPtrPayloadEnumBytes : List AbstractByte :=
  appendAbstractBytes (encodeLittleEndianBytes 1 8 .none)
    (encodeLittleEndianBytes 0x1000 8 (.some (7, 7)))

/-- Policy-aware multi-variant enum decoding with **typed per-variant payload
fields**: `variantFieldLayouts[varIdx]` lists the `LayoutTable` indices of the
selected variant's fields (information the TCB layout capture must add, since
`TypeLayout.fieldLayouts` exists only for single-variant aggregates). Each
payload field is decoded by the policy-aware typed decoder `decodeChild` on its
own byte slice, so pointer fields keep intact provenance under both policies
and integer fields obey the policy field by field. When no per-variant field
layouts are available it falls back to the untyped, whole-image-gated span
decoding of `decodeMultiVariantEnumWithPolicy`. -/
def decodeMultiVariantEnumTypedWithPolicy
    (policy : Ptr2IntTransmutePolicy)
    (decodeChild : Ty → List AbstractByte → Option Value)
    (layouts : LayoutTable)
    (l : TypeLayout)
    (tagLayout : ScalarLayout)
    (tagField : Nat)
    (variantShapes : List FieldsShape)
    (variantFieldLayouts : List (List Nat))
    (bytes : List AbstractByte) :
    Option Value :=
  let spanFallback (varIdx : Nat) (varOffsets : List Size) : Option Value :=
    match policyRejectsProv policy bytes with
    | true => .none
    | false =>
      match decodeFieldsBySpan bytes l.size.bytes varOffsets with
      | .some vals => .some (.aggregate varIdx vals)
      | .none => .none
  match Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => .none
  | false =>
    match l.fields, scalarLayoutByteWidth tagLayout with
    | .arbitrary outerOffsets _, .some tagSz =>
      match get? outerOffsets tagField with
      | .none => .none
      | .some tagOff =>
        match sliceAbstractBytes bytes tagOff.bytes tagSz with
        | .none => .none
        | .some tagSlice =>
          match decodeScalarLayoutBytesWithPolicy policy tagLayout tagSlice with
          | .some (.scalar tagSc) =>
            match get? variantShapes tagSc.bits with
            | .some (.arbitrary varOffsets _) =>
              match get? variantFieldLayouts tagSc.bits with
              | .some fls =>
                match Nat.beq (length fls) (length varOffsets) with
                | true =>
                  match
                    decodeFieldsByLayoutIdxs
                      (fun fIdx fSlice =>
                        decodeChild { kind := .adt "" .nil, layoutIdx := fIdx } fSlice)
                      layouts bytes varOffsets fls
                  with
                  | .some vals => .some (.aggregate tagSc.bits vals)
                  | .none => .none
                | false => spanFallback tagSc.bits varOffsets
              | .none => spanFallback tagSc.bits varOffsets
            | _ => .none
          | _ => .none
    | _, _ => .none

/-- Without per-variant field layouts the typed decoder is exactly the untyped
proposal `decodeMultiVariantEnumWithPolicy` (conservative extension). -/
theorem decodeMultiVariantEnumTypedWithPolicy_nil_eq
    (policy : Ptr2IntTransmutePolicy) (decodeChild : Ty → List AbstractByte → Option Value)
    (layouts : LayoutTable) (l : TypeLayout) (tagLayout : ScalarLayout) (tagField : Nat)
    (variantShapes : List FieldsShape) (bytes : List AbstractByte) :
    decodeMultiVariantEnumTypedWithPolicy policy decodeChild layouts l tagLayout tagField
        variantShapes .nil bytes =
      decodeMultiVariantEnumWithPolicy policy l tagLayout tagField variantShapes bytes := by
  unfold decodeMultiVariantEnumTypedWithPolicy decodeMultiVariantEnumWithPolicy
  dsimp only
  cases Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => rfl
  | false =>
    dsimp only
    cases l.fields with
    | arbitrary outerOffsets _ =>
      cases scalarLayoutByteWidth tagLayout with
      | none => rfl
      | some tagSz =>
        dsimp only
        cases get? outerOffsets tagField with
        | none => rfl
        | some tagOff =>
          dsimp only
          cases sliceAbstractBytes bytes tagOff.bytes tagSz with
          | none => rfl
          | some tagSlice =>
            dsimp only
            cases decodeScalarLayoutBytesWithPolicy policy tagLayout tagSlice with
            | none => rfl
            | some tv =>
              cases tv with
              | scalar tagSc =>
                dsimp only
                cases get? variantShapes tagSc.bits with
                | none => rfl
                | some vs => cases vs <;> rfl
              | unit => rfl
              | ptr _ _ => rfl
              | aggregate _ _ => rfl
    | primitive => rfl
    | union _ => rfl
    | array _ _ => rfl

/-- Policy refinement of the typed enum decoder: every `.strictUcg630Ub`
success is the identical `.stripProvenance` success, provided the payload
decoders refine (as `decodeTypedValueFromBytesWithPolicy` does). -/
theorem decodeMultiVariantEnumTypedWithPolicy_strict_refines_strip
    (childStrict childStrip : Ty → List AbstractByte → Option Value)
    (layouts : LayoutTable) (l : TypeLayout) (tagLayout : ScalarLayout) (tagField : Nat)
    (variantShapes : List FieldsShape) (variantFieldLayouts : List (List Nat))
    (bytes : List AbstractByte) (v : Value)
    (hchild : ∀ ty bs cv, childStrict ty bs = .some cv → childStrip ty bs = .some cv)
    (h : decodeMultiVariantEnumTypedWithPolicy .strictUcg630Ub childStrict layouts l tagLayout
      tagField variantShapes variantFieldLayouts bytes = .some v) :
    decodeMultiVariantEnumTypedWithPolicy .stripProvenance childStrip layouts l tagLayout
      tagField variantShapes variantFieldLayouts bytes = .some v := by
  unfold decodeMultiVariantEnumTypedWithPolicy at h ⊢
  dsimp only at h ⊢
  cases hu : Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => rw [hu] at h; cases h
  | false =>
    rw [hu] at h
    dsimp only at h ⊢
    cases hf : l.fields with
    | arbitrary outerOffsets _ =>
      rw [hf] at h
      cases htw : scalarLayoutByteWidth tagLayout with
      | none => rw [htw] at h; cases h
      | some tagSz =>
        rw [htw] at h
        dsimp only at h ⊢
        cases hg : get? outerOffsets tagField with
        | none => rw [hg] at h; cases h
        | some tagOff =>
          rw [hg] at h
          dsimp only at h ⊢
          cases hsl : sliceAbstractBytes bytes tagOff.bytes tagSz with
          | none => rw [hsl] at h; cases h
          | some tagSlice =>
            rw [hsl] at h
            dsimp only at h ⊢
            cases htd : decodeScalarLayoutBytesWithPolicy .strictUcg630Ub tagLayout tagSlice with
            | none => rw [htd] at h; cases h
            | some tv =>
              rw [htd] at h
              rw [decodeScalarLayoutBytesWithPolicy_strict_refines_strip tagLayout tagSlice tv htd]
              cases tv with
              | scalar tagSc =>
                dsimp only at h ⊢
                cases hvs : get? variantShapes tagSc.bits with
                | none => rw [hvs] at h; cases h
                | some vs =>
                  rw [hvs] at h
                  cases vs with
                  | arbitrary varOffsets _ =>
                    dsimp only at h ⊢
                    have hspan :
                        (match policyRejectsProv .strictUcg630Ub bytes with
                          | true => (none : Option Value)
                          | false =>
                            match decodeFieldsBySpan bytes l.size.bytes varOffsets with
                            | .some vals => .some (.aggregate tagSc.bits vals)
                            | .none => .none) = .some v →
                        (match policyRejectsProv .stripProvenance bytes with
                          | true => (none : Option Value)
                          | false =>
                            match decodeFieldsBySpan bytes l.size.bytes varOffsets with
                            | .some vals => .some (.aggregate tagSc.bits vals)
                            | .none => .none) = .some v := by
                      intro hs
                      dsimp only [policyRejectsProv] at hs ⊢
                      cases hp : abstractBytesHaveProv bytes with
                      | true => rw [hp] at hs; cases hs
                      | false => rw [hp] at hs; exact hs
                    cases hfl : get? variantFieldLayouts tagSc.bits with
                    | none => rw [hfl] at h; exact hspan h
                    | some fls =>
                      rw [hfl] at h
                      dsimp only at h ⊢
                      cases hlen : Nat.beq (length fls) (length varOffsets) with
                      | false => rw [hlen] at h; exact hspan h
                      | true =>
                        rw [hlen] at h
                        dsimp only at h ⊢
                        cases hdf : decodeFieldsByLayoutIdxs
                            (fun fIdx fSlice =>
                              childStrict { kind := .adt "" .nil, layoutIdx := fIdx } fSlice)
                            layouts bytes varOffsets fls with
                        | none => rw [hdf] at h; cases h
                        | some vals =>
                          rw [hdf] at h
                          rw [decodeFieldsByLayoutIdxs_mono
                            (fun fIdx fSlice =>
                              childStrict { kind := .adt "" .nil, layoutIdx := fIdx } fSlice)
                            (fun fIdx fSlice =>
                              childStrip { kind := .adt "" .nil, layoutIdx := fIdx } fSlice)
                            layouts bytes (fun fIdx bs cv hc => hchild _ bs cv hc)
                            varOffsets fls vals hdf]
                          exact h
                  | primitive => cases h
                  | union _ => cases h
                  | array _ _ => cases h
              | unit => cases h
              | ptr _ _ => cases h
              | aggregate _ _ => cases h
    | primitive => rw [hf] at h; cases h
    | union _ => rw [hf] at h; cases h
    | array _ _ => rw [hf] at h; cases h

/-- **Kernel-checked critique of the untyped enum fix and its typed repair
(`by rfl`)** on the genuine value `P::B(p)` (no pointer-to-integer
reinterpretation anywhere):
1. *TCB finding*: today's trusted decoder returns the pointer payload as a
   provenance-less integer (`Value.scalar`) — pointer provenance is silently
   dropped when a pointer-carrying multi-variant enum is decoded from bytes;
2. *Regression of the untyped fix*: `decodeMultiVariantEnumWithPolicy
   .strictUcg630Ub` rejects this image outright (its whole-image
   `policyRejectsProv` gate cannot tell a pointer payload from a transmuted
   integer), so adopting it at the `.multiple` fallback would turn every typed
   copy of a pointer-carrying enum into UB under the default policy; under
   `.stripProvenance` it still drops the provenance;
3. *Typed repair*: with per-variant field layouts,
   `decodeMultiVariantEnumTypedWithPolicy` returns `Value.ptr` with intact
   provenance under **both** policies, while the integer-payload enum
   `E { A(u32), B(u32) }` still flips (`.none` strict vs. `.some` strip) on
   provenance-carrying pointer bytes. -/
theorem multiVariant_enum_pointer_payload_regression_and_typed_fix_witness :
    decodeTypedValueFromBytes 4 protoTypedEnumLayouts protoPtrPayloadEnumTy
        protoPtrPayloadEnumBytes =
      .some (.aggregate 1 [.scalar ⟨0x1000, 8⟩]) ∧
    decodeMultiVariantEnumWithPolicy .strictUcg630Ub protoPtrPayloadEnumLayout
        (.initialized (.int 64 false) ⟨0, 1⟩) 0
        [.arbitrary [{ bytes := 8 }] [0], .arbitrary [{ bytes := 8 }] [0]]
        protoPtrPayloadEnumBytes = .none ∧
    decodeMultiVariantEnumWithPolicy .stripProvenance protoPtrPayloadEnumLayout
        (.initialized (.int 64 false) ⟨0, 1⟩) 0
        [.arbitrary [{ bytes := 8 }] [0], .arbitrary [{ bytes := 8 }] [0]]
        protoPtrPayloadEnumBytes =
      .some (.aggregate 1 [.scalar ⟨0x1000, 8⟩]) ∧
    decodeMultiVariantEnumTypedWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoTypedEnumLayouts)
        protoTypedEnumLayouts protoPtrPayloadEnumLayout
        (.initialized (.int 64 false) ⟨0, 1⟩) 0
        [.arbitrary [{ bytes := 8 }] [0], .arbitrary [{ bytes := 8 }] [0]] [[2], [2]]
        protoPtrPayloadEnumBytes =
      .some (.aggregate 1 [.ptr { allocId := 7, offsetBytes := 0x1000 } 8]) ∧
    decodeMultiVariantEnumTypedWithPolicy .stripProvenance
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoTypedEnumLayouts)
        protoTypedEnumLayouts protoPtrPayloadEnumLayout
        (.initialized (.int 64 false) ⟨0, 1⟩) 0
        [.arbitrary [{ bytes := 8 }] [0], .arbitrary [{ bytes := 8 }] [0]] [[2], [2]]
        protoPtrPayloadEnumBytes =
      .some (.aggregate 1 [.ptr { allocId := 7, offsetBytes := 0x1000 } 8]) ∧
    decodeMultiVariantEnumTypedWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoTypedEnumLayouts)
        protoTypedEnumLayouts protoTwoVariantEnumLayout
        (.initialized (.int 32 false) ⟨0, 1⟩) 0
        [.arbitrary [{ bytes := 4 }] [0], .arbitrary [{ bytes := 4 }] [0]] [[4], [4]]
        (encodeLittleEndianBytes protoEnumShapedPtr.offsetBytes 8 (.some (7, 7))) = .none ∧
    decodeMultiVariantEnumTypedWithPolicy .stripProvenance
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoTypedEnumLayouts)
        protoTypedEnumLayouts protoTwoVariantEnumLayout
        (.initialized (.int 32 false) ⟨0, 1⟩) 0
        [.arbitrary [{ bytes := 4 }] [0], .arbitrary [{ bytes := 4 }] [0]] [[4], [4]]
        (encodeLittleEndianBytes protoEnumShapedPtr.offsetBytes 8 (.some (7, 7))) =
      .some (.aggregate 1 [.scalar ⟨42, 4⟩]) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §13. Relational Dispatcher: Outcome Shape & Failure Preservation -/

/-- **Outcome shape of the relational dispatcher** (both modes): every related
result is either exactly the deterministic evaluator's result, or both are
successful scalar results of the same byte width over the same post-state
(`locals'`, `mem`) differing only in the scalar bits (the NaN choice). -/
theorem EvalRvalueFloatRelProto.eq_fun_or_scalar_variant
    (mode : FloatArithMode) (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (res : RvalueEvalResult)
    (h : EvalRvalueFloatRelProto mode locals rv mem localDecls layouts res) :
    res = evalRvalueFloatProto locals rv mem localDecls layouts ∨
      ∃ out base w locals',
        evalRvalueFloatProto locals rv mem localDecls layouts =
          .ok (.scalar ⟨base, w⟩) locals' mem ∧
        res = .ok (.scalar ⟨out, w⟩) locals' mem := by
  unfold EvalRvalueFloatRelProto at h
  cases rv with
  | binaryOp op lhsOp rhsOp =>
    dsimp only at h
    cases hlTy : floatTyOf? (operandTy localDecls layouts lhsOp) with
    | none => rw [hlTy] at h; exact Or.inl h
    | some lhsFk =>
      rw [hlTy] at h
      cases hrTy : floatTyOf? (operandTy localDecls layouts rhsOp) with
      | none => rw [hrTy] at h; exact Or.inl h
      | some rhsFk =>
        rw [hrTy] at h
        cases hlEv : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals
            localDecls mem.callStack with
        | ub => rw [hlEv] at h; exact Or.inl h
        | unsupported => rw [hlEv] at h; exact Or.inl h
        | ok lv locals₁ =>
          rw [hlEv] at h
          cases lv with
          | scalar lhsSc =>
            dsimp only at h
            cases hrEv : evalOperand locals₁ rhsOp mem.borrows mem.globals layouts
                mem.callerLocals localDecls mem.callStack with
            | ub => rw [hrEv] at h; exact Or.inl h
            | unsupported => rw [hrEv] at h; exact Or.inl h
            | ok rvVal locals₂ =>
              rw [hrEv] at h
              cases rvVal with
              | scalar rhsSc =>
                dsimp only at h
                cases hfmtL : ieeeFormatOfFloatTy? lhsFk with
                | none => rw [hfmtL] at h; exact Or.inl h
                | some fmtL =>
                  rw [hfmtL] at h
                  cases hfmtR : ieeeFormatOfFloatTy? rhsFk with
                  | none => rw [hfmtR] at h; exact Or.inl h
                  | some fmtR =>
                    rw [hfmtR] at h
                    dsimp only at h
                    by_cases hcond : (fmtL == fmtR && Nat.beq lhsSc.sizeBytes fmtL.byteWidth &&
                        Nat.beq rhsSc.sizeBytes fmtL.byteWidth && isFloatArithBinOp op) = true
                    · rw [if_pos' hcond] at h
                      have hcond3 : (fmtL == fmtR && Nat.beq lhsSc.sizeBytes fmtL.byteWidth &&
                          Nat.beq rhsSc.sizeBytes fmtL.byteWidth) = true :=
                        bool_and_true_left hcond
                      have hop : isFloatArithBinOp op = true := bool_and_true_right hcond
                      have heval : evalRvalueFloatProto locals (.binaryOp op lhsOp rhsOp) mem
                          localDecls layouts =
                          .ok (.scalar ⟨evalFloatArithBaseProto op fmtL lhsSc.bits rhsSc.bits,
                            fmtL.byteWidth⟩) locals₂ mem := by
                        unfold evalRvalueFloatProto
                        dsimp only
                        rw [hlTy, hrTy]; dsimp only
                        rw [hlEv]; dsimp only
                        rw [hrEv]; dsimp only
                        rw [hfmtL, hfmtR]; dsimp only
                        rw [if_pos' hcond3]
                        unfold evalFloatArithBaseProto?
                        rw [if_pos' hop]
                      obtain ⟨out, _, hres⟩ := h
                      exact Or.inr ⟨out, _, fmtL.byteWidth, locals₂, heval, hres⟩
                    · rw [if_neg' hcond] at h
                      exact Or.inl h
              | unit => exact Or.inl h
              | ptr _ _ => exact Or.inl h
              | aggregate _ _ => exact Or.inl h
          | unit => exact Or.inl h
          | ptr _ _ => exact Or.inl h
          | aggregate _ _ => exact Or.inl h
  | _ => exact Or.inl h

/-- **Failure preservation of the relational dispatcher** (both modes): a
related result is `.ub` / `.unsupported` exactly when the deterministic
evaluator's is, and a related `.ok` implies a deterministic `.ok` over the same
post-state. Hence every functional fail-closed theorem (`f16` / `f128`, format
mismatches, mixed float / non-float operands, `UnOp.not`) transfers verbatim to
`EvalRvalueFloatRelProto`: nondeterministic NaN choice can never turn a failure
into a success or vice versa. -/
theorem EvalRvalueFloatRelProto.failure_preserved
    (mode : FloatArithMode) (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (res : RvalueEvalResult)
    (h : EvalRvalueFloatRelProto mode locals rv mem localDecls layouts res) :
    (res = .ub ↔ evalRvalueFloatProto locals rv mem localDecls layouts = .ub) ∧
    (res = .unsupported ↔
      evalRvalueFloatProto locals rv mem localDecls layouts = .unsupported) ∧
    (∀ v locals' mem', res = .ok v locals' mem' →
      ∃ v', evalRvalueFloatProto locals rv mem localDecls layouts = .ok v' locals' mem') := by
  rcases EvalRvalueFloatRelProto.eq_fun_or_scalar_variant mode locals rv mem localDecls layouts
    res h with heq | ⟨out, base, w, locals₂, hfun, hres⟩
  · rw [heq]
    exact ⟨Iff.rfl, Iff.rfl, fun v locals' mem' hv => ⟨v, hv⟩⟩
  · rw [hfun, hres]
    refine ⟨⟨fun hc => (by cases hc), fun hc => (by cases hc)⟩,
      ⟨fun hc => (by cases hc), fun hc => (by cases hc)⟩, ?_⟩
    intro v locals' mem' hv
    injection hv with _ hl hm
    rw [← hl, ← hm]
    exact ⟨_, rfl⟩

/-! ## §14. Additive Sign Symmetry, Exact Rational Overflow/Underflow Thresholds & Relational Dispatcher Commutativity -/

/-- Counterexample refuting the naive caveat "except exact cancellation of
nonzero operands" for `(-a) + (-b) = -(a + b)`: even when **both** operands are
zeros (`+0.0` and `-0.0`), `(-(+0.0)) + (-(-0.0)) = +0.0 ≠ -0.0 = -((+0.0) + (-0.0))`. -/
theorem evalFloatArithBaseProto_add_neg_both_counterexample_zero :
    evalFloatArithBaseProto .add .binary32
        (evalFloatNegProto .binary32 0x00000000) (evalFloatNegProto .binary32 0x80000000) ≠
      evalFloatNegProto .binary32
        (evalFloatArithBaseProto .add .binary32 0x00000000 0x80000000) ∧
    evalFloatArithBaseProto .add .binary64
        (evalFloatNegProto .binary64 0x0000000000000000)
        (evalFloatNegProto .binary64 0x8000000000000000) ≠
      evalFloatNegProto .binary64
        (evalFloatArithBaseProto .add .binary64 0x0000000000000000 0x8000000000000000) := by
  exact ⟨by decide, by decide⟩

private theorem zeroBits_false_ne_true (f : IeeeFormat) :
    zeroBits f false ≠ zeroBits f true := by
  intro h
  have hd := congrArg (decodeBits f) h
  rw [decodeBits_zeroBits, decodeBits_zeroBits] at hd
  cases hd

private theorem infBits_ne_zeroBits (f : IeeeFormat) (ineg zneg : Bool) :
    infBits f ineg ≠ zeroBits f zneg := by
  intro h
  have hd := congrArg (decodeBits f) h
  rw [decodeBits_infBits, decodeBits_zeroBits] at hd
  cases hd

private theorem signedNum_not_neg_sum (ln rn : Bool) (lnum lden rnum rden : Nat) :
    signedNum (!ln) lnum * Int.ofNat rden + signedNum (!rn) rnum * Int.ofNat lden =
      -(signedNum ln lnum * Int.ofNat rden + signedNum rn rnum * Int.ofNat lden) := by
  rw [signedNum_neg, signedNum_neg, Int.neg_mul, Int.neg_mul, Int.neg_add]

private theorem decodeBits_evalFloatNegProto_involutive (f : IeeeFormat) (bits : Nat) :
    decodeBits f (evalFloatNegProto f (evalFloatNegProto f bits)) = decodeBits f bits := by
  rw [decodeBits_evalFloatNegProto, decodeBits_evalFloatNegProto]
  cases decodeBits f bits <;> simp [negateFloatKind]

private theorem decide_neg_lt_zero (z : Int) (hz : z ≠ 0) :
    decide (-z < 0) = !decide (z < 0) := by
  by_cases hlt : z < 0
  · have hpos : ¬ (-z < 0) := by omega
    rw [decide_eq_true hlt, decide_eq_false hpos]
    rfl
  · have hneg : -z < 0 := by omega
    rw [decide_eq_false hlt, decide_eq_true hneg]
    rfl

/-- **Exact additive sign-symmetry characterization**: for every pair of bit
patterns `a, b` whose IEEE-754 sum is not NaN,
`(-a) + (-b) = -(a + b)` holds bit-for-bit **if and only if** `a + b` is NOT an
opposite-sign cancellation to `+0.0` (which occurs both on `(+0.0) + (-0.0)` and
on finite nonzero `x + (-x)`). -/
theorem evalFloatArithBaseProto_add_neg_both_iff (f : IeeeFormat) (a b : Nat)
    (hnan : isNaNBits f (evalFloatArithBaseProto .add f a b) = false) :
    evalFloatArithBaseProto .add f (evalFloatNegProto f a) (evalFloatNegProto f b) =
        evalFloatNegProto f (evalFloatArithBaseProto .add f a b) ↔
      ¬ (evalFloatArithBaseProto .add f a b = zeroBits f false ∧
        (unpackBits f a).neg ≠ (unpackBits f b).neg) := by
  have hpn := isNaNBits_preferredNaNBits f
  have hna := floatKindNeg_decodeBits f a
  have hnb := floatKindNeg_decodeBits f b
  unfold evalFloatArithBaseProto at hnan ⊢
  rw [decodeBits_evalFloatNegProto, decodeBits_evalFloatNegProto]
  cases hl : decodeBits f a with
  | nan _ _ _ => rw [hl] at hnan; cases hpn.symm.trans hnan
  | inf ln =>
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | inf rn =>
      cases ln <;> cases rn
      · simp only [exactSumProto, negateFloatKind, Bool.not_false, bne_self_eq_false,
          Bool.false_eq_true, ↓reduceIte]
        rw [evalFloatNegProto_infBits]
        exact ⟨fun _ h => infBits_ne_zeroBits f false false h.1, fun _ => rfl⟩
      · rw [hl, hr] at hnan; dsimp only [exactSumProto] at hnan; cases hpn.symm.trans hnan
      · rw [hl, hr] at hnan; dsimp only [exactSumProto] at hnan; cases hpn.symm.trans hnan
      · simp only [exactSumProto, negateFloatKind, Bool.not_true, bne_self_eq_false,
          Bool.false_eq_true, ↓reduceIte]
        rw [evalFloatNegProto_infBits]
        exact ⟨fun _ h => infBits_ne_zeroBits f true false h.1, fun _ => rfl⟩
    | zero _ =>
      dsimp only [exactSumProto, negateFloatKind]
      rw [evalFloatNegProto_infBits]
      exact ⟨fun _ h => infBits_ne_zeroBits f ln false h.1, fun _ => rfl⟩
    | finite _ _ _ =>
      dsimp only [exactSumProto, negateFloatKind]
      rw [evalFloatNegProto_infBits]
      exact ⟨fun _ h => infBits_ne_zeroBits f ln false h.1, fun _ => rfl⟩
  | zero ln =>
    rw [hl] at hna; dsimp only [floatKindNeg] at hna
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | inf rn =>
      dsimp only [exactSumProto, negateFloatKind]
      rw [evalFloatNegProto_infBits]
      exact ⟨fun _ h => infBits_ne_zeroBits f rn false h.1, fun _ => rfl⟩
    | zero rn =>
      rw [hr] at hnb; dsimp only [floatKindNeg] at hnb
      rw [← hna, ← hnb]
      cases ln <;> cases rn
      · dsimp only [exactSumProto, negateFloatKind]
        rw [evalFloatNegProto_zeroBits]
        exact ⟨fun _ h => h.2 rfl, fun _ => rfl⟩
      · dsimp only [exactSumProto, negateFloatKind]
        rw [evalFloatNegProto_zeroBits]
        exact ⟨fun heq => absurd heq (zeroBits_false_ne_true f),
          fun h => absurd ⟨rfl, by decide⟩ h⟩
      · dsimp only [exactSumProto, negateFloatKind]
        rw [evalFloatNegProto_zeroBits]
        exact ⟨fun heq => absurd heq (zeroBits_false_ne_true f),
          fun h => absurd ⟨rfl, by decide⟩ h⟩
      · dsimp only [exactSumProto, negateFloatKind]
        rw [evalFloatNegProto_zeroBits]
        exact ⟨fun _ h => h.2 rfl, fun _ => rfl⟩
    | finite rn rnum rden =>
      dsimp only [exactSumProto, negateFloatKind]
      have hden := decodeBits_finite_den_pos f b rn rnum rden hr
      have hsym := roundRatioTiesToEven_not_neg f rn rnum rden hden
      have hne : roundRatioTiesToEven f rn rnum rden ≠ zeroBits f false := by
        have hrb : roundRatioTiesToEven f rn rnum rden = b % 2 ^ f.width := by
          have hb_mod := decodeBits_mod_width f b
          rw [hr] at hb_mod
          exact roundRatioTiesToEven_eq_bits_of_decodeBits_finite f (b % 2 ^ f.width) rn rnum
            rden (Nat.mod_lt _ (Nat.two_pow_pos _)) hb_mod
        intro hz
        have hd := congrArg (decodeBits f) (hrb.symm.trans hz)
        rw [decodeBits_mod_width, hr, decodeBits_zeroBits] at hd
        cases hd
      exact ⟨fun _ h => hne h.1, fun _ => hsym⟩
  | finite ln lnum lden =>
    rw [hl] at hna; dsimp only [floatKindNeg] at hna
    cases hr : decodeBits f b with
    | nan _ _ _ => rw [hl, hr] at hnan; cases hpn.symm.trans hnan
    | inf rn =>
      dsimp only [exactSumProto, negateFloatKind]
      rw [evalFloatNegProto_infBits]
      exact ⟨fun _ h => infBits_ne_zeroBits f rn false h.1, fun _ => rfl⟩
    | zero _ =>
      dsimp only [exactSumProto, negateFloatKind]
      have hden := decodeBits_finite_den_pos f a ln lnum lden hl
      have hsym := roundRatioTiesToEven_not_neg f ln lnum lden hden
      have hne : roundRatioTiesToEven f ln lnum lden ≠ zeroBits f false := by
        have hra : roundRatioTiesToEven f ln lnum lden = a % 2 ^ f.width := by
          have ha_mod := decodeBits_mod_width f a
          rw [hl] at ha_mod
          exact roundRatioTiesToEven_eq_bits_of_decodeBits_finite f (a % 2 ^ f.width) ln lnum
            lden (Nat.mod_lt _ (Nat.two_pow_pos _)) ha_mod
        intro hz
        have hd := congrArg (decodeBits f) (hra.symm.trans hz)
        rw [decodeBits_mod_width, hl, decodeBits_zeroBits] at hd
        cases hd
      exact ⟨fun _ h => hne h.1, fun _ => hsym⟩
    | finite rn rnum rden =>
      rw [hr] at hnb; dsimp only [floatKindNeg] at hnb
      rw [← hna, ← hnb]
      dsimp only [exactSumProto, negateFloatKind]
      rw [signedNum_not_neg_sum]
      let s : Int := signedNum ln lnum * Int.ofNat rden + signedNum rn rnum * Int.ofNat lden
      change roundRatioTiesToEven f (decide (-s < 0)) (-s).natAbs (lden * rden) =
          evalFloatNegProto f (roundRatioTiesToEven f (decide (s < 0)) s.natAbs (lden * rden)) ↔
        ¬ (roundRatioTiesToEven f (decide (s < 0)) s.natAbs (lden * rden) = zeroBits f false ∧
          ln ≠ rn)
      have hlden := decodeBits_finite_den_pos f a ln lnum lden hl
      have hrden := decodeBits_finite_den_pos f b rn rnum rden hr
      have hlnum := decodeBits_finite_num_pos f a ln lnum lden hl
      have hrnum := decodeBits_finite_num_pos f b rn rnum rden hr
      have hden_ne : ¬ (lden * rden = 0) := Nat.ne_of_gt (Nat.mul_pos hlden hrden)
      by_cases hs0 : s = 0
      · rw [hs0, Int.neg_zero]
        simp only [Int.natAbs_zero, show decide ((0 : Int) < 0) = false by decide]
        rw [roundRatioTiesToEven_eq_shape, if_neg' hden_ne, if_pos' rfl, evalFloatNegProto_zeroBits]
        have hsign_ne : ln ≠ rn := by
          intro heq
          subst heq
          have hp1 : 0 < lnum * rden := Nat.mul_pos hlnum hrden
          have hp2 : 0 < rnum * lden := Nat.mul_pos hrnum hlden
          cases ln
          · simp only [s, signedNum, Bool.false_eq_true, ↓reduceIte] at hs0
            have h1 : Int.ofNat lnum * Int.ofNat rden = Int.ofNat (lnum * rden) := rfl
            have h2 : Int.ofNat rnum * Int.ofNat lden = Int.ofNat (rnum * lden) := rfl
            rw [h1, h2] at hs0
            have h3 : Int.ofNat (lnum * rden + rnum * lden) = Int.ofNat 0 := hs0
            have h4 : lnum * rden + rnum * lden = 0 := Int.ofNat.inj h3
            omega
          · simp only [s, signedNum, ↓reduceIte] at hs0
            have h1 : Int.ofNat lnum * Int.ofNat rden = Int.ofNat (lnum * rden) := rfl
            have h2 : Int.ofNat rnum * Int.ofNat lden = Int.ofNat (rnum * lden) := rfl
            rw [Int.neg_mul, Int.neg_mul, h1, h2] at hs0
            have hneg : -(Int.ofNat (lnum * rden) + Int.ofNat (rnum * lden)) = 0 := by
              rw [Int.neg_add]; exact hs0
            have hpos_eq : Int.ofNat (lnum * rden) + Int.ofNat (rnum * lden) = 0 := by
              have := congrArg Neg.neg hneg
              simpa using this
            have h4 : lnum * rden + rnum * lden = 0 := Int.ofNat.inj hpos_eq
            omega
        exact ⟨fun heq => absurd heq (zeroBits_false_ne_true f),
          fun h => absurd ⟨rfl, hsign_ne⟩ h⟩
      · rw [Int.natAbs_neg, decide_neg_lt_zero s hs0]
        have hsym := roundRatioTiesToEven_not_neg f (decide (s < 0)) s.natAbs (lden * rden)
          (Nat.mul_pos hlden hrden)
        have hne_z : roundRatioTiesToEven f (decide (s < 0)) s.natAbs (lden * rden) ≠
            zeroBits f false := by
          intro hz
          have hsub_eq : evalFloatArithBaseProto .sub f a (evalFloatNegProto f b) =
              roundRatioTiesToEven f (decide (s < 0)) s.natAbs (lden * rden) := by
            rw [evalFloatArithBaseProto_sub_eq_add_neg]
            unfold evalFloatArithBaseProto
            rw [decodeBits_evalFloatNegProto_involutive, hl, hr]
            rfl
          have hdec_z : decodeBits f (evalFloatArithBaseProto .sub f a (evalFloatNegProto f b)) =
              .zero false := by
            rw [hsub_eq, hz, decodeBits_zeroBits]
          have heq_cmp := (evalFloatArithBaseProto_sub_finite_eq_zero_iff f a (evalFloatNegProto f b)
            (Or.inr ⟨ln, lnum, lden, hl⟩)
            (Or.inr ⟨!rn, rnum, rden, by rw [decodeBits_evalFloatNegProto, hr]; rfl⟩)).mp
            ⟨false, hdec_z⟩
          unfold evalFloatCmpProto evalFloatPartialCompareProto at heq_cmp
          rw [hl, decodeBits_evalFloatNegProto, hr] at heq_cmp
          dsimp only [negateFloatKind] at heq_cmp
          rw [signedNum_neg] at heq_cmp
          cases hcmp : compare (signedNum ln lnum * Int.ofNat rden)
              (-(signedNum rn rnum) * Int.ofNat lden) with
          | lt => rw [hcmp] at heq_cmp; cases heq_cmp
          | gt => rw [hcmp] at heq_cmp; cases heq_cmp
          | eq =>
            have hcmp_eq : signedNum ln lnum * Int.ofNat rden =
                -(signedNum rn rnum) * Int.ofNat lden := by
              have hle1 : ¬ (signedNum ln lnum * Int.ofNat rden <
                  -(signedNum rn rnum) * Int.ofNat lden) := by
                intro hlt
                have := (int_compare_eq_lt_iff _ _).mpr hlt
                rw [hcmp] at this; cases this
              have hle2 : ¬ (-(signedNum rn rnum) * Int.ofNat lden <
                  signedNum ln lnum * Int.ofNat rden) := by
                intro hlt
                have := (int_compare_eq_gt_iff _ _).mpr hlt
                rw [hcmp] at this; cases this
              omega
            have : s = 0 := by
              dsimp only [s]
              rw [Int.neg_mul] at hcmp_eq
              omega
            exact hs0 this
        exact ⟨fun _ h => hne_z h.1, fun _ => hsym⟩

/-- **Exact subtractive sign-symmetry characterization**: for every pair of bit
patterns `a, b` whose IEEE-754 difference is not NaN,
`(-a) - (-b) = -(a - b)` holds bit-for-bit **if and only if** `a - b` is NOT a
same-sign cancellation to `+0.0` (e.g., `(+0.0) - (+0.0)`, `(-0.0) - (-0.0)`, or
finite nonzero `x - x`). -/
theorem evalFloatArithBaseProto_sub_neg_both_iff (f : IeeeFormat) (a b : Nat)
    (hnan : isNaNBits f (evalFloatArithBaseProto .sub f a b) = false) :
    evalFloatArithBaseProto .sub f (evalFloatNegProto f a) (evalFloatNegProto f b) =
        evalFloatNegProto f (evalFloatArithBaseProto .sub f a b) ↔
      ¬ (evalFloatArithBaseProto .sub f a b = zeroBits f false ∧
        (unpackBits f a).neg = (unpackBits f b).neg) := by
  rw [evalFloatArithBaseProto_sub_eq_add_neg f a b] at hnan ⊢
  rw [evalFloatArithBaseProto_sub_eq_add_neg f (evalFloatNegProto f a) (evalFloatNegProto f b)]
  have hiff := evalFloatArithBaseProto_add_neg_both_iff f a (evalFloatNegProto f b) hnan
  rw [unpackBits_evalFloatNegProto] at hiff
  dsimp only at hiff
  have hneg_neq : ((unpackBits f a).neg ≠ !(unpackBits f b).neg) ↔
      ((unpackBits f a).neg = (unpackBits f b).neg) := by
    cases (unpackBits f a).neg <;> cases (unpackBits f b).neg <;> decide
  rw [hneg_neq] at hiff
  exact hiff

/-- Positive subnormal exponent shift `fractionBits - minExponent` (`149` for
`binary32`, `1074` for `binary64`), so `min_subnormal = 2^-(underflowShiftProto f)`. -/
def underflowShiftProto (f : IeeeFormat) : Nat :=
  ((f.fractionBits : Int) - f.minExponent).toNat

/-- Shift for the overflow half-ulp boundary (`103` for `binary32`, `970` for
`binary64`). -/
def overflowShiftProto (f : IeeeFormat) : Nat :=
  (f.maxExponent - (f.fractionBits : Int) - 1).toNat

/-- Exact integer threshold for round-to-nearest-even overflow to `±Inf`:
`(2^(fractionBits + 2) - 1) * 2^(maxExponent - fractionBits - 1)` =
`MAX + 0.5 * ulp(MAX)`. -/
def overflowThresholdNumProto (f : IeeeFormat) : Nat :=
  (2 ^ (f.fractionBits + 2) - 1) * 2 ^ overflowShiftProto f

private theorem underflowShiftProto_int (f : IeeeFormat) :
    (f.fractionBits : Int) - f.minExponent = (underflowShiftProto f : Int) := by
  cases f <;> decide

private theorem overflowShiftProto_int (f : IeeeFormat) :
    (f.fractionBits : Int) - f.maxExponent = -((overflowShiftProto f + 1 : Nat) : Int) := by
  cases f <;> decide

private theorem maxExponent_eq_pos (f : IeeeFormat) :
    f.maxExponent = ((f.fractionBits + 1 + overflowShiftProto f : Nat) : Int) := by
  cases f <;> decide

private theorem roundQuotientTiesToEven_eq_zero_iff (a b : Nat) (hb : 0 < b) :
    roundQuotientTiesToEven a b = 0 ↔ 2 * a ≤ b := by
  unfold roundQuotientTiesToEven
  dsimp only
  by_cases hlt : a < b
  · have hq : a / b = 0 := Nat.div_eq_of_lt hlt
    have hr : a % b = a := Nat.mod_eq_of_lt hlt
    rw [hq, hr]
    by_cases hcond : a * 2 > b ∨ a * 2 = b ∧ 0 % 2 = 1
    · rw [if_pos' hcond]
      rcases hcond with h1 | ⟨_, h2⟩
      · exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
      · exact absurd h2 (by decide)
    · rw [if_neg' hcond]
      have h1 : ¬(a * 2 > b) := fun x => hcond (Or.inl x)
      exact ⟨fun _ => by omega, fun _ => rfl⟩
  · have hge : b ≤ a := Nat.le_of_not_lt hlt
    have hq_pos : 1 ≤ a / b := (Nat.le_div_iff_mul_le hb).mpr (by simpa using hge)
    by_cases hcond : a % b * 2 > b ∨ a % b * 2 = b ∧ a / b % 2 = 1
    · rw [if_pos' hcond]
      exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    · rw [if_neg' hcond]
      exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

private theorem roundQuotientTiesToEven_eq_even_of_lt (a b M : Nat) (hb : 0 < b)
    (hM_pos : 2 ≤ M) (hM_even : M % 2 = 0) (hlt : a < M * b) :
    roundQuotientTiesToEven a b = M ↔ (2 * M - 1) * b ≤ 2 * a := by
  unfold roundQuotientTiesToEven
  dsimp only
  have hdiv := Nat.div_add_mod a b
  have hq_lt : a / b < M := (Nat.div_lt_iff_lt_mul hb).mpr hlt
  have hrem_lt : a % b < b := Nat.mod_lt a hb
  by_cases hq_eq : a / b = M - 1
  · have hodd : (M - 1) % 2 = 1 := by omega
    rw [hq_eq, hodd]
    have ha_eq : a = (M - 1) * b + a % b := by
      have := hdiv.symm
      rw [hq_eq, Nat.mul_comm] at this
      exact this
    have h2M : (2 * M - 1) * b = 2 * ((M - 1) * b) + b := by
      have : 2 * M - 1 = 2 * (M - 1) + 1 := by omega
      rw [this, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    by_cases hcond : a % b * 2 > b ∨ a % b * 2 = b ∧ (1 : Nat) = 1
    · rw [if_pos' hcond]
      rcases hcond with h1 | ⟨h1, _⟩
      · exact ⟨fun _ => by omega, fun _ => by omega⟩
      · exact ⟨fun _ => by omega, fun _ => by omega⟩
    · rw [if_neg' hcond]
      have h1 : ¬(a % b * 2 > b) := fun x => hcond (Or.inl x)
      have h2 : ¬(a % b * 2 = b) := fun x => hcond (Or.inr ⟨x, rfl⟩)
      exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  · have hq_le : a / b + 1 < M := by omega
    have h2a_lt : 2 * a < (2 * M - 1) * b := by
      have h1 : a ≤ (M - 2) * b + (b - 1) := by
        have hq2 : a / b ≤ M - 2 := by omega
        have hm := Nat.mul_le_mul_right b hq2
        rw [Nat.mul_comm b (a / b)] at hdiv
        omega
      have h2 : 2 * ((M - 2) * b + (b - 1)) < (2 * M - 1) * b := by
        have : 2 * M - 1 = 2 * (M - 2) + 3 := by omega
        rw [this, Nat.add_mul, Nat.mul_assoc]
        omega
      omega
    by_cases hcond : a % b * 2 > b ∨ a % b * 2 = b ∧ a / b % 2 = 1
    · rw [if_pos' hcond]
      exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    · rw [if_neg' hcond]
      exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

private theorem powScale_nonneg_eq (n d k : Nat) :
    powScale n d (k : Int) = (n * 2 ^ k, d) := by
  cases k <;> rfl

private theorem powScale_neg_succ_eq (n d k : Nat) :
    powScale n d (-((k + 1 : Nat) : Int)) = (n, d * 2 ^ (k + 1)) := by
  show powScale n d (Int.negSucc k) = (n, d * 2 ^ (k + 1))
  rfl

/-- **Exact rational underflow threshold for `roundRatioTiesToEven`**:
for every positive denominator `d`, `roundRatioTiesToEven f neg n d = zeroBits f neg`
if and only if `n / d ≤ 1/2 * min_subnormal = 2^(minExponent - fractionBits - 1)`,
expressed purely in `Nat` arithmetic as `2 * n * 2^(underflowShiftProto f) ≤ d`. -/
theorem roundRatioTiesToEven_eq_zeroBits_iff (f : IeeeFormat) (neg : Bool) (n d : Nat)
    (hd : 0 < d) :
    roundRatioTiesToEven f neg n d = zeroBits f neg ↔
      2 * n * 2 ^ underflowShiftProto f ≤ d := by
  have hd0 : ¬ (d = 0) := Nat.ne_of_gt hd
  by_cases hn0 : n = 0
  · subst hn0
    rw [roundRatioTiesToEven_eq_shape, if_neg' hd0, if_pos' rfl]
    simp
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hshift := underflowShiftProto_int f
    have hmin_le_max : f.minExponent ≤ f.maxExponent := by cases f <;> decide
    constructor
    · intro hzero
      have hdec : decodeBits f (roundRatioTiesToEven f neg n d) = .zero neg := by
        rw [hzero, decodeBits_zeroBits]
      have hcr := roundRatioTiesToEven_float_half_ulp f neg n d hn hd
      dsimp only at hcr
      have hne_inf : decodeBits f (roundRatioTiesToEven f neg n d) ≠ .inf neg := by
        rw [hdec]; intro hc; cases hc
      have hsame := hcr.2.2 hne_inf
      rw [hdec] at hsame
      let exponent := max (ratioExponent n d) f.minExponent
      let scaled := powScale n d ((f.fractionBits : Int) - exponent)
      let sig := roundQuotientTiesToEven scaled.1 scaled.2
      have hsig0 : sig = 0 := by
        by_cases hs : sig = 0
        · exact hs
        · change floatKindSameValue (.zero neg)
            (if sig = 0 then .zero neg
             else .finite neg (powScale sig 1 (exponent - f.fractionBits)).1
               (powScale sig 1 (exponent - f.fractionBits)).2) at hsame
          rw [if_neg' hs] at hsame
          cases hsame
      have hexp_eq : exponent = f.minExponent := by
        by_cases hgt : f.minExponent < ratioExponent n d
        · exfalso
          obtain ⟨_, hlo_ge, _⟩ := powScale_roundRatio_scaled_bounds f n d hn hd
          have hge_min : f.minExponent ≤ ratioExponent n d := by omega
          have hlo : 2 ^ f.fractionBits * scaled.2 ≤ scaled.1 := hlo_ge hge_min
          have hds := powScale_snd_pos_gen n d hd ((f.fractionBits : Int) - exponent)
          have hsig_ge : 2 ^ f.fractionBits ≤ sig := by
            have := roundQuotient_ge_of_mul_le .tiesToEven scaled.1 scaled.2 (2 ^ f.fractionBits)
              hds hlo
            simpa [roundQuotient, sig] using this
          have hpow_pos : 0 < 2 ^ f.fractionBits := Nat.two_pow_pos _
          omega
        · dsimp only [exponent]; omega
      have hscaled_eq : scaled = (n * 2 ^ underflowShiftProto f, d) := by
        dsimp only [scaled]
        rw [hexp_eq, hshift, powScale_nonneg_eq]
      have hsig_eq : roundQuotientTiesToEven (n * 2 ^ underflowShiftProto f) d = 0 := by
        simpa [sig, hscaled_eq] using hsig0
      have hle := (roundQuotientTiesToEven_eq_zero_iff (n * 2 ^ underflowShiftProto f) d hd).mp
        hsig_eq
      rwa [← Nat.mul_assoc] at hle
    · intro hle
      have hle' : 2 * (n * 2 ^ underflowShiftProto f) ≤ d := by rwa [← Nat.mul_assoc]
      have hlt_min : ratioExponent n d < f.minExponent := by
        by_cases hge : f.minExponent ≤ ratioExponent n d
        · exfalso
          have hre := powScale_neg_ratioExponent_bounds n d hn hd
          have hcross := powScale_diff_cross n d (-ratioExponent n d) (-f.minExponent) (by omega)
          have h1 : (powScale n d (-f.minExponent)).2 ≤ (powScale n d (-f.minExponent)).1 := by
            have hle_r := hre.1
            have hmul : (powScale n d (-ratioExponent n d)).2 *
                (powScale n d (-f.minExponent)).2 ≤
                (powScale n d (-ratioExponent n d)).1 *
                (powScale n d (-f.minExponent)).2 :=
              Nat.mul_le_mul_right _ hle_r
            have hstep : (powScale n d (-ratioExponent n d)).1 *
                (powScale n d (-f.minExponent)).2 ≤
                (powScale n d (-ratioExponent n d)).2 *
                (powScale n d (-f.minExponent)).1 := by
              rw [Nat.mul_comm (powScale n d (-ratioExponent n d)).2, ← hcross]
              exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
            have hcomb : (powScale n d (-ratioExponent n d)).2 *
                (powScale n d (-f.minExponent)).2 ≤
                (powScale n d (-ratioExponent n d)).2 *
                (powScale n d (-f.minExponent)).1 := Nat.le_trans hmul hstep
            exact Nat.le_of_mul_le_mul_left hcomb (powScale_snd_pos_gen n d hd _)
          have hneg_min : -f.minExponent = ((-f.minExponent).toNat : Int) := by
            cases f <;> decide
          have hps : powScale n d (-f.minExponent) = (n * 2 ^ (-f.minExponent).toNat, d) := by
            rw [hneg_min, powScale_nonneg_eq]
            rfl
          rw [hps] at h1
          dsimp only at h1
          have hexp_le : (-f.minExponent).toNat ≤ underflowShiftProto f := by
            cases f <;> decide
          have hpow_le : 2 ^ (-f.minExponent).toNat < 2 * 2 ^ underflowShiftProto f := by
            have h1p : 2 ^ (-f.minExponent).toNat ≤ 2 ^ underflowShiftProto f :=
              Nat.pow_le_pow_right (by decide) hexp_le
            have hpos := Nat.two_pow_pos (underflowShiftProto f)
            omega
          have hmul_lt := Nat.mul_lt_mul_of_pos_left hpow_le hn
          rw [Nat.mul_left_comm] at hmul_lt
          omega
        · omega
      have hexp : rrExponent f n d = f.minExponent := by
        unfold rrExponent; omega
      have hsc : powScale n d ((f.fractionBits : Int) - rrExponent f n d) =
          (n * 2 ^ underflowShiftProto f, d) := by
        rw [hexp, hshift, powScale_nonneg_eq]
      have hsig0 : rrSignificand f n d = 0 := by
        unfold rrSignificand
        rw [hsc]
        exact (roundQuotientTiesToEven_eq_zero_iff _ d hd).mpr hle'
      have hcarry : rrCarry f n d = false := by
        unfold rrCarry
        rw [hsig0]
        exact decide_eq_false (Nat.not_le_of_lt (Nat.two_pow_pos _))
      have hsig' : rrSignificand' f n d = 0 := by
        unfold rrSignificand'; rw [hcarry]; exact hsig0
      have hexp' : rrExponent' f n d = f.minExponent := by
        unfold rrExponent'; rw [hcarry]; exact hexp
      rw [roundRatioTiesToEven_eq_shape, if_neg' hd0, if_neg' hn0, hexp, hexp', hsig']
      have hnot_gt : ¬ (f.minExponent > f.maxExponent) := by omega
      rw [if_neg' hnot_gt, if_neg' hnot_gt, if_pos' (Nat.two_pow_pos _), if_pos' rfl]
      exact (zeroBits_eq_encodeBits f neg).symm

/-- **Exact rational overflow threshold for `roundRatioTiesToEven`**:
for every positive denominator `d`, `roundRatioTiesToEven f neg n d = infBits f neg`
if and only if `n / d ≥ MAX + 0.5 * ulp(MAX) = (2^(fractionBits + 2) - 1) * 2^(maxExponent - fractionBits - 1)`,
expressed purely in `Nat` arithmetic as `d * overflowThresholdNumProto f ≤ n`. -/
theorem roundRatioTiesToEven_eq_infBits_iff (f : IeeeFormat) (neg : Bool) (n d : Nat)
    (hd : 0 < d) :
    roundRatioTiesToEven f neg n d = infBits f neg ↔
      d * overflowThresholdNumProto f ≤ n := by
  have hthresh_pos : 0 < overflowThresholdNumProto f := by
    unfold overflowThresholdNumProto
    have hgt1 : 1 < 2 ^ (f.fractionBits + 2) := by
      have h2 : 2 ^ 1 ≤ 2 ^ (f.fractionBits + 2) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ f.fractionBits + 2)
      omega
    exact Nat.mul_pos (Nat.sub_pos_of_lt hgt1) (Nat.two_pow_pos _)
  by_cases hn0 : n = 0
  · subst hn0
    have hd0 : ¬ (d = 0) := Nat.ne_of_gt hd
    rw [roundRatioTiesToEven_eq_shape, if_neg' hd0, if_pos' rfl]
    have hpos := Nat.mul_pos hd hthresh_pos
    exact ⟨fun h => absurd h.symm (infBits_ne_zeroBits f neg neg), fun h => by omega⟩
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hov := (roundRatioTiesToEven_overflow_iff f neg n d hn hd).1
    rw [hov]
    have hmin_lt_max : f.minExponent < f.maxExponent := by cases f <;> decide
    have hmax_pos := maxExponent_eq_pos f
    let E := f.fractionBits + 1 + overflowShiftProto f
    have hE_eq : f.maxExponent = (E : Int) := hmax_pos
    have htwo_E1 : 2 ^ (E + 1) = 2 ^ (f.fractionBits + 2) * 2 ^ overflowShiftProto f := by
      have hidx : E + 1 = (f.fractionBits + 2) + overflowShiftProto f := by dsimp only [E]; omega
      rw [hidx, Nat.pow_add]
    have htwo_E : 2 ^ E = 2 ^ (f.fractionBits + 1) * 2 ^ overflowShiftProto f :=
      Nat.pow_add 2 (f.fractionBits + 1) (overflowShiftProto f)
    have hthresh_lt_E1 : overflowThresholdNumProto f < 2 ^ (E + 1) := by
      unfold overflowThresholdNumProto
      rw [htwo_E1]
      exact Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (Nat.two_pow_pos _) (by decide))
        (Nat.two_pow_pos _)
    have hE_lt_thresh : 2 ^ E < overflowThresholdNumProto f := by
      unfold overflowThresholdNumProto
      rw [htwo_E]
      have h1 : 2 ^ (f.fractionBits + 1) < 2 ^ (f.fractionBits + 2) - 1 := by
        cases f <;> decide
      exact Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
    -- Relate `ratioExponent n d` to `E` using `powScale_neg_ratioExponent_bounds`:
    have hre_gt_iff : f.maxExponent < ratioExponent n d ↔ d * 2 ^ (E + 1) ≤ n := by
      have hre := powScale_neg_ratioExponent_bounds n d hn hd
      constructor
      · intro hgt
        have hcross := powScale_diff_cross n d (-ratioExponent n d) (-((E + 1 : Nat) : Int))
          (by rw [hE_eq] at hgt; omega)
        have h1 : (powScale n d (-((E + 1 : Nat) : Int))).2 ≤
            (powScale n d (-((E + 1 : Nat) : Int))).1 := by
          have hmul := Nat.mul_le_mul_right (powScale n d (-((E + 1 : Nat) : Int))).2 hre.1
          have hstep : (powScale n d (-ratioExponent n d)).1 *
              (powScale n d (-((E + 1 : Nat) : Int))).2 ≤
              (powScale n d (-ratioExponent n d)).2 *
              (powScale n d (-((E + 1 : Nat) : Int))).1 := by
            rw [Nat.mul_comm (powScale n d (-ratioExponent n d)).2, ← hcross]
            exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
          exact Nat.le_of_mul_le_mul_left (Nat.le_trans hmul hstep) (powScale_snd_pos_gen n d hd _)
        rw [powScale_neg_succ_eq] at h1
        exact h1
      · intro hge
        by_cases hle : ratioExponent n d ≤ f.maxExponent
        · exfalso
          have hcross := powScale_diff_cross n d (-((E : Nat) : Int)) (-ratioExponent n d)
            (by rw [hE_eq] at hle; omega)
          have hre2 := hre.2
          have hpow_E : powScale n d (-((E : Nat) : Int)) = (n, d * 2 ^ E) := by
            have hE_pos : ∃ k, E = k + 1 := ⟨f.fractionBits + overflowShiftProto f, by
              dsimp only [E]; omega⟩
            obtain ⟨k, hk⟩ := hE_pos
            rw [hk, powScale_neg_succ_eq]
          rw [hpow_E] at hcross
          dsimp only at hcross
          have hlt2 : n * (powScale n d (-ratioExponent n d)).2 <
              2 * (d * 2 ^ E) * (powScale n d (-ratioExponent n d)).2 := by
            have hle_diff : n * (powScale n d (-ratioExponent n d)).2 ≤
                n * (powScale n d (-ratioExponent n d)).2 *
                  2 ^ ((-ratioExponent n d - -((E : Nat) : Int)).toNat) :=
              Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
            rw [hcross, Nat.mul_comm (powScale n d (-ratioExponent n d)).1] at hle_diff
            have hlt_step : d * 2 ^ E * (powScale n d (-ratioExponent n d)).1 <
                d * 2 ^ E * (2 * (powScale n d (-ratioExponent n d)).2) :=
              Nat.mul_lt_mul_of_pos_left hre2 (Nat.mul_pos hd (Nat.two_pow_pos _))
            have heq_r : d * 2 ^ E * (2 * (powScale n d (-ratioExponent n d)).2) =
                2 * (d * 2 ^ E) * (powScale n d (-ratioExponent n d)).2 := by
              rw [Nat.mul_left_comm (d * 2 ^ E) 2, ← Nat.mul_assoc]
            rw [heq_r] at hlt_step
            exact Nat.lt_of_le_of_lt hle_diff hlt_step
          have hn_lt : n < 2 * (d * 2 ^ E) := nat_lt_of_mul_lt_mul_right hlt2
          have h2E : 2 * (d * 2 ^ E) = d * 2 ^ (E + 1) := by
            rw [Nat.pow_succ, Nat.mul_comm (2 ^ E) 2, Nat.mul_left_comm]
          omega
        · omega
    have hre_eq_iff : ratioExponent n d = f.maxExponent ↔
        d * 2 ^ E ≤ n ∧ n < d * 2 ^ (E + 1) := by
      have hiff := ratioExponent_eq_iff_powScale_bounds n d f.maxExponent hn hd
      rw [hE_eq] at hiff ⊢
      have hE_pos : ∃ k, E = k + 1 := ⟨f.fractionBits + overflowShiftProto f, by
        dsimp only [E]; omega⟩
      obtain ⟨k, hk⟩ := hE_pos
      have hpow_E : powScale n d (-((E : Nat) : Int)) = (n, d * 2 ^ E) := by
        rw [hk, powScale_neg_succ_eq]
      rw [hpow_E] at hiff
      dsimp only at hiff
      have h2E : 2 * (d * 2 ^ E) = d * 2 ^ (E + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ E) 2, Nat.mul_left_comm]
      rw [h2E] at hiff
      exact hiff
    -- Now combine the three regimes of `ratioExponent n d` relative to `f.maxExponent`:
    by_cases hgt : f.maxExponent < ratioExponent n d
    · have hge_E1 : d * 2 ^ (E + 1) ≤ n := hre_gt_iff.mp hgt
      have hge_th : d * overflowThresholdNumProto f ≤ n :=
        Nat.le_trans (Nat.mul_le_mul_left d (Nat.le_of_lt hthresh_lt_E1)) hge_E1
      have hmax_gt : f.maxExponent < max (ratioExponent n d) f.minExponent := by omega
      exact ⟨fun _ => hge_th, fun _ => Or.inl hmax_gt⟩
    · by_cases heq : ratioExponent n d = f.maxExponent
      · obtain ⟨_, hn_lt_E1⟩ := hre_eq_iff.mp heq
        have hexp : max (ratioExponent n d) f.minExponent = f.maxExponent := by omega
        have hnot_gt : ¬ (f.maxExponent < max (ratioExponent n d) f.minExponent) := by omega
        have hsc : powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent) =
            (n, d * 2 ^ (overflowShiftProto f + 1)) := by
          rw [hexp, overflowShiftProto_int, powScale_neg_succ_eq]
        rw [hsc]
        dsimp only
        have hM_even : (2 ^ (f.fractionBits + 1)) % 2 = 0 := by
          rw [Nat.pow_succ]; omega
        have hM_ge2 : 2 ≤ 2 ^ (f.fractionBits + 1) := by cases f <;> decide
        have hMb : 2 ^ (f.fractionBits + 1) * (d * 2 ^ (overflowShiftProto f + 1)) =
            d * 2 ^ (E + 1) := by
          have hidx : E + 1 = (f.fractionBits + 1) + (overflowShiftProto f + 1) := by
            dsimp only [E]; omega
          rw [hidx, Nat.pow_add 2 (f.fractionBits + 1) (overflowShiftProto f + 1),
            Nat.mul_left_comm]
        have hn_lt_Mb : n < 2 ^ (f.fractionBits + 1) * (d * 2 ^ (overflowShiftProto f + 1)) := by
          rw [hMb]; exact hn_lt_E1
        have hrq := roundQuotientTiesToEven_eq_even_of_lt n (d * 2 ^ (overflowShiftProto f + 1))
          (2 ^ (f.fractionBits + 1)) (Nat.mul_pos hd (Nat.two_pow_pos _)) hM_ge2 hM_even hn_lt_Mb
        have h2th : (2 * 2 ^ (f.fractionBits + 1) - 1) * (d * 2 ^ (overflowShiftProto f + 1)) =
            2 * (d * overflowThresholdNumProto f) := by
          unfold overflowThresholdNumProto
          have h2p : 2 * 2 ^ (f.fractionBits + 1) = 2 ^ (f.fractionBits + 2) := by
            rw [Nat.pow_succ 2 (f.fractionBits + 1), Nat.mul_comm]
          have hpow_s : 2 ^ (overflowShiftProto f + 1) = 2 ^ overflowShiftProto f * 2 :=
            Nat.pow_succ 2 (overflowShiftProto f)
          rw [h2p, hpow_s]
          have h1 : d * (2 ^ overflowShiftProto f * 2) = 2 * (d * 2 ^ overflowShiftProto f) := by
            rw [Nat.mul_comm (2 ^ overflowShiftProto f) 2, Nat.mul_left_comm]
          rw [h1, Nat.mul_left_comm, Nat.mul_left_comm (2 ^ (f.fractionBits + 2) - 1) d]
        rw [h2th] at hrq
        constructor
        · intro hdisj
          rcases hdisj with hbad | ⟨_, hsig_eq⟩
          · exact absurd hbad hnot_gt
          · have h2le := hrq.mp hsig_eq
            omega
        · intro hge_th
          exact Or.inr ⟨hexp, hrq.mpr (by omega)⟩
      · -- `ratioExponent n d < f.maxExponent`
        have hlt_max : ratioExponent n d < f.maxExponent := by omega
        have hexp_lt : max (ratioExponent n d) f.minExponent < f.maxExponent := by omega
        have hn_lt_E : n < d * 2 ^ E := by
          by_cases hge_E : d * 2 ^ E ≤ n
          · exfalso
            by_cases hge_E1 : d * 2 ^ (E + 1) ≤ n
            · exact hgt (hre_gt_iff.mpr hge_E1)
            · exact heq (hre_eq_iff.mpr ⟨hge_E, Nat.lt_of_not_le hge_E1⟩)
          · exact Nat.lt_of_not_le hge_E
        have hn_lt_th : n < d * overflowThresholdNumProto f :=
          Nat.lt_of_lt_of_le hn_lt_E (Nat.mul_le_mul_left d (Nat.le_of_lt hE_lt_thresh))
        constructor
        · intro hdisj
          rcases hdisj with h1 | ⟨h2, _⟩ <;> omega
        · intro hge
          omega

/-- Exact rational underflow criterion for finite `mul`: `a * b = ±0` iff
`|a * b| ≤ 0.5 * min_subnormal`. -/
theorem evalFloatArithBaseProto_mul_finite_underflow_iff (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite ln lnum lden) (hr : decodeBits f b = .finite rn rnum rden) :
    evalFloatArithBaseProto .mul f a b = zeroBits f (xor ln rn) ↔
      2 * (lnum * rnum) * 2 ^ underflowShiftProto f ≤ lden * rden := by
  rw [evalFloatArithBaseProto_mul_finite f a b ln rn lnum lden rnum rden hl hr]
  exact roundRatioTiesToEven_eq_zeroBits_iff f (xor ln rn) (lnum * rnum) (lden * rden)
    (Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden hl)
      (decodeBits_finite_den_pos f b rn rnum rden hr))

/-- Exact rational overflow criterion for finite `mul`: `a * b = ±Inf` iff
`|a * b| ≥ MAX + 0.5 * ulp(MAX)`. -/
theorem evalFloatArithBaseProto_mul_finite_overflow_iff (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite ln lnum lden) (hr : decodeBits f b = .finite rn rnum rden) :
    evalFloatArithBaseProto .mul f a b = infBits f (xor ln rn) ↔
      (lden * rden) * overflowThresholdNumProto f ≤ lnum * rnum := by
  rw [evalFloatArithBaseProto_mul_finite f a b ln rn lnum lden rnum rden hl hr]
  exact roundRatioTiesToEven_eq_infBits_iff f (xor ln rn) (lnum * rnum) (lden * rden)
    (Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden hl)
      (decodeBits_finite_den_pos f b rn rnum rden hr))

/-- Exact rational underflow criterion for finite `div`: `a / b = ±0` iff
`|a / b| ≤ 0.5 * min_subnormal`. -/
theorem evalFloatArithBaseProto_div_finite_underflow_iff (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite ln lnum lden) (hr : decodeBits f b = .finite rn rnum rden) :
    evalFloatArithBaseProto .div f a b = zeroBits f (xor ln rn) ↔
      2 * (lnum * rden) * 2 ^ underflowShiftProto f ≤ lden * rnum := by
  rw [evalFloatArithBaseProto_div_finite f a b ln rn lnum lden rnum rden hl hr]
  exact roundRatioTiesToEven_eq_zeroBits_iff f (xor ln rn) (lnum * rden) (lden * rnum)
    (Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden hl)
      (decodeBits_finite_num_pos f b rn rnum rden hr))

/-- Exact rational overflow criterion for finite `div`: `a / b = ±Inf` iff
`|a / b| ≥ MAX + 0.5 * ulp(MAX)`. -/
theorem evalFloatArithBaseProto_div_finite_overflow_iff (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite ln lnum lden) (hr : decodeBits f b = .finite rn rnum rden) :
    evalFloatArithBaseProto .div f a b = infBits f (xor ln rn) ↔
      (lden * rnum) * overflowThresholdNumProto f ≤ lnum * rden := by
  rw [evalFloatArithBaseProto_div_finite f a b ln rn lnum lden rnum rden hl hr]
  exact roundRatioTiesToEven_eq_infBits_iff f (xor ln rn) (lnum * rden) (lden * rnum)
    (Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden hl)
      (decodeBits_finite_num_pos f b rn rnum rden hr))

/-- Evaluating a constant operand or a plain (unprojected) `.copy` local never
mutates `locals`. -/
theorem evalOperand_const_or_plain_copy_preserves_locals
    (locals : List LocalSlot) (op : Operand) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame) (v : Value) (locals' : List LocalSlot)
    (hform : (∃ c, op = .constant c) ∨ (∃ idx, op = .copy ⟨idx, []⟩))
    (hev : evalOperand locals op borrows globals layouts callerLocals localDecls callStack =
      .ok v locals') :
    locals' = locals := by
  rcases hform with ⟨c, rfl⟩ | ⟨idx, rfl⟩
  · unfold evalOperand at hev
    dsimp only at hev
    cases hc : c.val with
    | indirect allocId offset =>
      rw [hc] at hev
      dsimp only at hev
      cases hlk : lookupGlobalAlloc globals allocId with
      | none => rw [hlk] at hev; cases hev
      | some _ =>
        rw [hlk] at hev
        dsimp only at hev
        cases hec : evalConstValue (.indirect allocId offset) c.ty globals layouts with
        | none => rw [hec] at hev; cases hev
        | some _ => rw [hec] at hev; injection hev with _ hl; exact hl.symm
    | unevaluated _ => rw [hc] at hev; cases hev
    | zeroSized | scalar _ | slice _ =>
      rw [hc] at hev
      dsimp only at hev
      cases hec : evalConstValue _ c.ty globals layouts with
      | none => rw [hec] at hev; cases hev
      | some _ => rw [hec] at hev; injection hev with _ hl; exact hl.symm
  · unfold evalOperand at hev
    dsimp only at hev
    cases hg : get? locals idx with
    | none => rw [hg] at hev; cases hev
    | some slot =>
      rw [hg] at hev
      cases slot with
      | uninit | dead => cases hev
      | init rootVal =>
        dsimp only at hev
        cases hrp : readProjectedValue locals rootVal .nil with
        | ub => rw [hrp] at hev; cases hev
        | unsupported => rw [hrp] at hev; cases hev
        | ok _ => rw [hrp] at hev; injection hev with _ hl; exact hl.symm

private def floatBinOpRelSpec (mode : FloatArithMode) (op : BinOp)
    (locals : List LocalSlot) (mem : Memory) (lhsFk rhsFk : FloatTy)
    (lv rvVal : Value) (res : RvalueEvalResult) : Prop :=
  match lv, rvVal, ieeeFormatOfFloatTy? lhsFk, ieeeFormatOfFloatTy? rhsFk with
  | .scalar lhsSc, .scalar rhsSc, .some fmtL, .some fmtR =>
    if (fmtL == fmtR && Nat.beq lhsSc.sizeBytes fmtL.byteWidth &&
        Nat.beq rhsSc.sizeBytes fmtL.byteWidth) = true then
      ∃ out, EvalFloatBinOpRel mode op fmtL lhsSc.bits rhsSc.bits out ∧
        res = .ok (.scalar ⟨out, fmtL.byteWidth⟩) locals mem
    else
      res = .unsupported
  | _, _, _, _ => res = .unsupported

private theorem evalRvalueFloatRelProto_binaryOp_float_char
    (mode : FloatArithMode) (op : BinOp) (locals : List LocalSlot) (lhsOp rhsOp : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (lhsFk rhsFk : FloatTy) (lv rvVal : Value) (res : RvalueEvalResult)
    (hop : isFloatArithBinOp op = true)
    (hlTy : floatTyOf? (operandTy localDecls layouts lhsOp) = .some lhsFk)
    (hrTy : floatTyOf? (operandTy localDecls layouts rhsOp) = .some rhsFk)
    (hl : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals
      localDecls mem.callStack = .ok lv locals)
    (hr : evalOperand locals rhsOp mem.borrows mem.globals layouts mem.callerLocals
      localDecls mem.callStack = .ok rvVal locals) :
    EvalRvalueFloatRelProto mode locals (.binaryOp op lhsOp rhsOp) mem localDecls layouts res ↔
      floatBinOpRelSpec mode op locals mem lhsFk rhsFk lv rvVal res := by
  have hfun_unsup :
      (match lv, rvVal, ieeeFormatOfFloatTy? lhsFk, ieeeFormatOfFloatTy? rhsFk with
       | .scalar lhsSc, .scalar rhsSc, .some fmtL, .some fmtR =>
         (fmtL == fmtR && Nat.beq lhsSc.sizeBytes fmtL.byteWidth &&
           Nat.beq rhsSc.sizeBytes fmtL.byteWidth) = false
       | _, _, _, _ => True) →
      evalRvalueFloatProto locals (.binaryOp op lhsOp rhsOp) mem localDecls layouts = .unsupported := by
    intro hbad
    unfold evalRvalueFloatProto
    dsimp only
    rw [hlTy, hrTy]; dsimp only
    rw [hl]; dsimp only
    rw [hr]; dsimp only
    cases lv with
    | unit | ptr _ _ | aggregate _ _ => rfl
    | scalar lhsSc =>
      cases rvVal with
      | unit | ptr _ _ | aggregate _ _ => rfl
      | scalar rhsSc =>
        dsimp only at hbad ⊢
        cases hfmtL : ieeeFormatOfFloatTy? lhsFk with
        | none => rfl
        | some fmtL =>
          cases hfmtR : ieeeFormatOfFloatTy? rhsFk with
          | none => rfl
          | some fmtR =>
            rw [hfmtL, hfmtR] at hbad
            dsimp only at hbad ⊢
            rw [hbad]
            rfl
  unfold EvalRvalueFloatRelProto floatBinOpRelSpec
  dsimp only
  rw [hlTy, hrTy]; dsimp only
  rw [hl]
  cases lv with
  | unit | ptr _ _ | aggregate _ _ =>
    rw [hfun_unsup (by trivial)]
  | scalar lhsSc =>
    dsimp only
    rw [hr]
    cases rvVal with
    | unit | ptr _ _ | aggregate _ _ =>
      rw [hfun_unsup (by trivial)]
    | scalar rhsSc =>
      dsimp only
      cases hfmtL : ieeeFormatOfFloatTy? lhsFk with
      | none =>
        rw [hfun_unsup (by rw [hfmtL]; trivial)]
      | some fmtL =>
        cases hfmtR : ieeeFormatOfFloatTy? rhsFk with
        | none =>
          rw [hfun_unsup (by rw [hfmtL, hfmtR]; trivial)]
        | some fmtR =>
          dsimp only
          by_cases hc : (fmtL == fmtR && Nat.beq lhsSc.sizeBytes fmtL.byteWidth &&
              Nat.beq rhsSc.sizeBytes fmtL.byteWidth) = true
          · have hc4 : (fmtL == fmtR && Nat.beq lhsSc.sizeBytes fmtL.byteWidth &&
                Nat.beq rhsSc.sizeBytes fmtL.byteWidth && isFloatArithBinOp op) = true := by
              rw [hc, hop]; rfl
            rw [if_pos' hc4, if_pos' hc]
          · have hcf : (fmtL == fmtR && Nat.beq lhsSc.sizeBytes fmtL.byteWidth &&
                Nat.beq rhsSc.sizeBytes fmtL.byteWidth) = false := Bool.eq_false_iff.mpr hc
            have hc4f : ¬ ((fmtL == fmtR && Nat.beq lhsSc.sizeBytes fmtL.byteWidth &&
                Nat.beq rhsSc.sizeBytes fmtL.byteWidth && isFloatArithBinOp op) = true) := by
              rw [hcf]; exact Bool.false_ne_true
            rw [if_neg' hc4f, if_neg' hc, hfun_unsup (by rw [hfmtL, hfmtR]; exact hcf)]

/-- **Relational MIR dispatcher commutativity for `.add` and `.mul`**: under
either `FloatArithMode`, whenever at least one operand has a static `.float _`
type and both operands evaluate cleanly without mutating `locals` (as guaranteed
for constants and plain `.copy` locals by
`evalOperand_const_or_plain_copy_preserves_locals`), swapping `lhsOp` and
`rhsOp` preserves the set of related `RvalueEvalResult`s identically (covering
`.ok` with full nondeterministic NaN choices as well as `.unsupported` on
mismatches / unmodeled `f16` / `f128`). -/
theorem EvalRvalueFloatRelProto.add_mul_comm_float_of_ok
    (mode : FloatArithMode) (op : BinOp) (locals : List LocalSlot) (lhsOp rhsOp : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (lv rvVal : Value) (res : RvalueEvalResult)
    (hop : op = .add ∨ op = .mul)
    (hfl : (∃ fk, floatTyOf? (operandTy localDecls layouts lhsOp) = .some fk) ∨
      (∃ fk, floatTyOf? (operandTy localDecls layouts rhsOp) = .some fk))
    (hl : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals
      localDecls mem.callStack = .ok lv locals)
    (hr : evalOperand locals rhsOp mem.borrows mem.globals layouts mem.callerLocals
      localDecls mem.callStack = .ok rvVal locals) :
    EvalRvalueFloatRelProto mode locals (.binaryOp op lhsOp rhsOp) mem localDecls layouts res ↔
      EvalRvalueFloatRelProto mode locals (.binaryOp op rhsOp lhsOp) mem localDecls layouts res := by
  have hop_arith : isFloatArithBinOp op = true := by rcases hop with rfl | rfl <;> rfl
  have hrel_comm : ∀ fmt a b out,
      EvalFloatBinOpRel mode op fmt a b out ↔ EvalFloatBinOpRel mode op fmt b a out := by
    intro fmt a b out
    rcases hop with rfl | rfl
    · exact EvalFloatBinOpRel.add_comm mode fmt a b out
    · exact EvalFloatBinOpRel.mul_comm mode fmt a b out
  cases hlTy : floatTyOf? (operandTy localDecls layouts lhsOp) with
  | none =>
    cases hrTy : floatTyOf? (operandTy localDecls layouts rhsOp) with
    | none =>
      rcases hfl with ⟨fk, hfk⟩ | ⟨fk, hfk⟩
      · rw [hlTy] at hfk; cases hfk
      · rw [hrTy] at hfk; cases hfk
    | some _ =>
      unfold EvalRvalueFloatRelProto evalRvalueFloatProto
      dsimp only; rw [hlTy, hrTy]
  | some lhsFk =>
    cases hrTy : floatTyOf? (operandTy localDecls layouts rhsOp) with
    | none =>
      unfold EvalRvalueFloatRelProto evalRvalueFloatProto
      dsimp only; rw [hlTy, hrTy]
    | some rhsFk =>
      rw [evalRvalueFloatRelProto_binaryOp_float_char mode op locals lhsOp rhsOp mem localDecls
            layouts lhsFk rhsFk lv rvVal res hop_arith hlTy hrTy hl hr,
          evalRvalueFloatRelProto_binaryOp_float_char mode op locals rhsOp lhsOp mem localDecls
            layouts rhsFk lhsFk rvVal lv res hop_arith hrTy hlTy hr hl]
      unfold floatBinOpRelSpec
      cases lv with
      | unit | ptr _ _ | aggregate _ _ =>
        cases rvVal <;> cases ieeeFormatOfFloatTy? lhsFk <;> cases ieeeFormatOfFloatTy? rhsFk <;>
          exact Iff.rfl
      | scalar lhsSc =>
        cases rvVal with
        | unit | ptr _ _ | aggregate _ _ =>
          cases ieeeFormatOfFloatTy? lhsFk <;> cases ieeeFormatOfFloatTy? rhsFk <;> exact Iff.rfl
        | scalar rhsSc =>
          cases ieeeFormatOfFloatTy? lhsFk with
          | none => cases ieeeFormatOfFloatTy? rhsFk <;> exact Iff.rfl
          | some fmtL =>
            cases ieeeFormatOfFloatTy? rhsFk with
            | none => exact Iff.rfl
            | some fmtR =>
              cases fmtL <;> cases fmtR
              · by_cases hwL : Nat.beq lhsSc.sizeBytes IeeeFormat.binary32.byteWidth = true
                · by_cases hwR : Nat.beq rhsSc.sizeBytes IeeeFormat.binary32.byteWidth = true
                  · simp only [beq_self_eq_true, hwL, hwR, Bool.and_self, ↓reduceIte]
                    constructor <;> rintro ⟨out, hrel, hres⟩
                    · exact ⟨out, (hrel_comm .binary32 _ _ _).mp hrel, hres⟩
                    · exact ⟨out, (hrel_comm .binary32 _ _ _).mpr hrel, hres⟩
                  · have hwRf : Nat.beq rhsSc.sizeBytes IeeeFormat.binary32.byteWidth = false :=
                      Bool.eq_false_iff.mpr hwR
                    simp [hwL, hwRf]
                · have hwLf : Nat.beq lhsSc.sizeBytes IeeeFormat.binary32.byteWidth = false :=
                    Bool.eq_false_iff.mpr hwL
                  simp [hwLf]
              · simp
              · simp
              · by_cases hwL : Nat.beq lhsSc.sizeBytes IeeeFormat.binary64.byteWidth = true
                · by_cases hwR : Nat.beq rhsSc.sizeBytes IeeeFormat.binary64.byteWidth = true
                  · simp only [beq_self_eq_true, hwL, hwR, Bool.and_self, ↓reduceIte]
                    constructor <;> rintro ⟨out, hrel, hres⟩
                    · exact ⟨out, (hrel_comm .binary64 _ _ _).mp hrel, hres⟩
                    · exact ⟨out, (hrel_comm .binary64 _ _ _).mpr hrel, hres⟩
                  · have hwRf : Nat.beq rhsSc.sizeBytes IeeeFormat.binary64.byteWidth = false :=
                      Bool.eq_false_iff.mpr hwR
                    simp [hwL, hwRf]
                · have hwLf : Nat.beq lhsSc.sizeBytes IeeeFormat.binary64.byteWidth = false :=
                    Bool.eq_false_iff.mpr hwL
                  simp [hwLf]

/-- Witness explaining why the non-mutating-read hypothesis in
`EvalRvalueFloatRelProto.add_mul_comm_float_of_ok` is necessary: `Operand.move`
invalidates a local slot after reading it, so `move _0 + move _0` fails with
`.ub` on the second operand, whereas `copy _0 + copy _0` succeeds; moreover,
swapping an uninitialized local (`ub`) with a valid `f16` local (`unsupported`
only after both reads) preserves left-to-right MIR evaluation order. -/
theorem evalRvalueFloatProto_move_order_witness :
    evalRvalueFloatProto floatMisdispatchLocals
        (.binaryOp .add (.move ⟨0, []⟩) (.move ⟨0, []⟩))
        emptyMemory floatMisdispatchDecls emptyLayoutTable = .ub ∧
    evalRvalueFloatProto floatMisdispatchLocals
        (.binaryOp .add (.copy ⟨0, []⟩) (.copy ⟨0, []⟩))
        emptyMemory floatMisdispatchDecls emptyLayoutTable =
      .ok (.scalar ⟨0x40000000, 4⟩) floatMisdispatchLocals emptyMemory ∧
    evalRvalueFloatProto [.uninit, .init (.scalar ⟨0x3F800000, 4⟩)]
        (.binaryOp .add (.copy ⟨0, []⟩) (.copy ⟨1, []⟩))
        emptyMemory floatMisdispatchDecls emptyLayoutTable = .ub := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## §15. Struct Composite Erasure, Cast-Level Provenance-Free Equivalence, TCB Finding 5 & Rich/Niche Enum Decoding -/

/-! ### §15.1 Struct / Single-Variant ADT Composite Erasure Characterization -/

/-- True iff `l` is an inhabited primitive single-variant layout whose
`backendRepr` is a non-pointer `ScalarLayout` with nonzero size. -/
def isNonPtrScalarLayout (l : TypeLayout) : Bool :=
  match l.isUninhabited, l.variants, l.fields, Nat.beq l.size.bytes 0, l.backendRepr with
  | false, .single _, .primitive, false, .scalar sl => !scalarLayoutIsPointer sl
  | _, _, _, _, _ => false

/-- On any ADT layout satisfying `isNonPtrScalarLayout`, `.stripProvenance`
equals `.strictUcg630Ub` applied to provenance-erased bytes. -/
theorem decodeTypedValueFromBytesWithPolicy_strip_adt_scalarLayout_eq_strict_erased
    (fuel : Nat) (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy)
    (layoutIdx : LayoutIdx) (l : TypeLayout) (bytes : List AbstractByte)
    (hlk : LayoutTable.lookup layouts layoutIdx = .some l)
    (hnp : isNonPtrScalarLayout l = true) :
    decodeTypedValueFromBytesWithPolicy .stripProvenance (.succ fuel) layouts
        { kind := .adt defPath args, layoutIdx := layoutIdx } bytes =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub (.succ fuel) layouts
        { kind := .adt defPath args, layoutIdx := layoutIdx } (stripAbstractBytesProv bytes) := by
  unfold isNonPtrScalarLayout at hnp
  cases hu : l.isUninhabited with
  | true => rw [hu] at hnp; cases hnp
  | false =>
    rw [hu] at hnp
    cases hv : l.variants with
    | empty => rw [hv] at hnp; cases hnp
    | multiple _ _ _ => rw [hv] at hnp; cases hnp
    | single vIdx =>
      rw [hv] at hnp
      cases hf : l.fields with
      | arbitrary _ _ => rw [hf] at hnp; cases hnp
      | union _ => rw [hf] at hnp; cases hnp
      | array _ _ => rw [hf] at hnp; cases hnp
      | primitive =>
        rw [hf] at hnp
        cases hsz : Nat.beq l.size.bytes 0 with
        | true => rw [hsz] at hnp; cases hnp
        | false =>
          rw [hsz] at hnp
          cases hbr : l.backendRepr with
          | memory => rw [hbr] at hnp; cases hnp
          | scalarPair _ _ => rw [hbr] at hnp; cases hnp
          | scalar sl =>
            rw [hbr] at hnp
            dsimp only at hnp
            have hnotptr : scalarLayoutIsPointer sl = false := by
              cases hsp : scalarLayoutIsPointer sl with
              | false => rfl
              | true => rw [hsp] at hnp; cases hnp
            unfold decodeTypedValueFromBytesWithPolicy
            dsimp only [normalizeCodecTy]
            rw [hlk]
            dsimp only
            rw [hu, length_stripAbstractBytesProv]
            cases hlen : Nat.beq (length bytes) l.size.bytes with
            | false => rfl
            | true =>
              rw [hv, hf, hsz, hbr]
              dsimp only
              exact decodeScalarLayoutBytesWithPolicy_strip_eq_strict_erased sl bytes hnotptr

/-- Commuting `decodeFieldsByLayoutIdxs` with `stripAbstractBytesProv` whenever
each field index decoder commutes with provenance erasure. -/
theorem decodeFieldsByLayoutIdxs_stripAbstractBytesProv
    (fStrip fStrict : Nat → List AbstractByte → Option Value)
    (layouts : LayoutTable) (bytes : List AbstractByte)
    (offsets : List Size) (fls : List Nat)
    (hf : ∀ idx bs, idx ∈ fls → fStrip idx bs = fStrict idx (stripAbstractBytesProv bs)) :
    decodeFieldsByLayoutIdxs fStrip layouts bytes offsets fls =
      decodeFieldsByLayoutIdxs fStrict layouts (stripAbstractBytesProv bytes) offsets fls := by
  induction offsets generalizing fls with
  | nil =>
    cases fls with
    | nil => rfl
    | cons _ _ => rfl
  | cons off rest ih =>
    cases fls with
    | nil => rfl
    | cons fIdx flRest =>
      unfold decodeFieldsByLayoutIdxs
      cases hlk : LayoutTable.lookup layouts fIdx with
      | none => rfl
      | some fl =>
        dsimp only
        rw [sliceAbstractBytes_stripAbstractBytesProv]
        cases hsl : sliceAbstractBytes bytes off.bytes fl.size.bytes with
        | none => rfl
        | some fSlice =>
          dsimp only
          rw [hf fIdx fSlice (List.Mem.head _)]
          cases fStrict fIdx (stripAbstractBytesProv fSlice) with
          | none => rfl
          | some fv =>
            dsimp only
            rw [ih flRest (fun idx bs hm => hf idx bs (List.Mem.tail _ hm))]

/-- **Composite erasure characterization for single-variant structs / ADTs**:
for every single-variant ADT (`#[repr(C)] struct Pair { a: u32, b: f32 }`,
`struct NonZeroPair(NonZeroU32, u32)`, etc.) whose `FieldsShape.arbitrary`
fields all resolve via `fieldLayouts` to non-pointer `ScalarLayout`s,
`.stripProvenance` decoding is **identical** to `.strictUcg630Ub` decoding on
provenance-erased bytes (including arbitrary padding bytes). -/
theorem decodeTypedValueFromBytesWithPolicy_strip_struct_scalar_eq_strict_erased
    (fuel : Nat) (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy)
    (layoutIdx : LayoutIdx) (l : TypeLayout) (variantIdx : Nat)
    (offsets : List Size) (memOrder : List Nat) (bytes : List AbstractByte)
    (hlk : LayoutTable.lookup layouts layoutIdx = .some l)
    (hvar : l.variants = .single variantIdx)
    (hfld : l.fields = .arbitrary offsets memOrder)
    (hlen : Nat.beq (length l.fieldLayouts) (length offsets) = true)
    (hfields : ∀ idx, idx ∈ l.fieldLayouts →
      ∃ fl, LayoutTable.lookup layouts idx = .some fl ∧ isNonPtrScalarLayout fl = true) :
    decodeTypedValueFromBytesWithPolicy .stripProvenance (.succ (.succ fuel)) layouts
        { kind := .adt defPath args, layoutIdx := layoutIdx } bytes =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub (.succ (.succ fuel)) layouts
        { kind := .adt defPath args, layoutIdx := layoutIdx } (stripAbstractBytesProv bytes) := by
  unfold decodeTypedValueFromBytesWithPolicy
  dsimp only [normalizeCodecTy]
  rw [hlk]
  dsimp only
  rw [length_stripAbstractBytesProv]
  cases hu : Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => rfl
  | false =>
    dsimp only
    rw [hvar, hfld]
    cases offsets with
    | nil => rfl
    | cons off0 offRest =>
      dsimp only
      rw [hlen]
      dsimp only
      rw [decodeFieldsByLayoutIdxs_stripAbstractBytesProv
        (fun fIdx fSlice =>
          decodeTypedValueFromBytesWithPolicy .stripProvenance (.succ fuel) layouts
            { kind := .adt "" .nil, layoutIdx := fIdx } fSlice)
        (fun fIdx fSlice =>
          decodeTypedValueFromBytesWithPolicy .strictUcg630Ub (.succ fuel) layouts
            { kind := .adt "" .nil, layoutIdx := fIdx } fSlice)
        layouts bytes (off0 :: offRest) l.fieldLayouts
        (fun idx bs hm => by
          obtain ⟨fl, hflk, hnp⟩ := hfields idx hm
          exact decodeTypedValueFromBytesWithPolicy_strip_adt_scalarLayout_eq_strict_erased
            fuel layouts "" .nil idx fl bs hflk hnp)]

/-! ### §15.2 Cast-Level Provenance-Free Equivalence -/

mutual
  /-- True iff a runtime `Value` contains any `Value.ptr` leaf anywhere inside it. -/
  def valueHasProv : Value → Bool
    | .unit => false
    | .scalar _ => false
    | .ptr _ _ => true
    | .aggregate _ fields => valueListHasProv fields

  /-- True iff any `Value` in a list contains a `Value.ptr` leaf. -/
  def valueListHasProv : List Value → Bool
    | .nil => false
    | v :: vs => Bool.or (valueHasProv v) (valueListHasProv vs)
end

private theorem abstractBytesHaveProv_appendAbstractBytes (a b : List AbstractByte) :
    abstractBytesHaveProv (appendAbstractBytes a b) =
      Bool.or (abstractBytesHaveProv a) (abstractBytesHaveProv b) := by
  induction a with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | uninit =>
      show abstractBytesHaveProv (appendAbstractBytes tl b) =
        Bool.or (abstractBytesHaveProv tl) (abstractBytesHaveProv b)
      exact ih
    | init byte prov =>
      cases prov with
      | none =>
        show abstractBytesHaveProv (appendAbstractBytes tl b) =
          Bool.or (abstractBytesHaveProv tl) (abstractBytesHaveProv b)
        exact ih
      | some p =>
        rfl

private theorem abstractBytesHaveProv_encodeLittleEndianBytes_none (bits sz : Nat) :
    abstractBytesHaveProv (encodeLittleEndianBytes bits sz .none) = false := by
  induction sz generalizing bits with
  | zero => rfl
  | succ k ih =>
    unfold encodeLittleEndianBytes abstractBytesHaveProv
    exact ih (Nat.div bits 256)

private theorem abstractBytesHaveProv_encodeScalarBytes_none (sv : ScalarVal)
    (bs : List AbstractByte) (h : encodeScalarBytes sv .none = .some bs) :
    abstractBytesHaveProv bs = false := by
  unfold encodeScalarBytes at h
  cases hz : Nat.beq sv.sizeBytes 0 with
  | true => rw [hz] at h; cases h
  | false =>
    rw [hz] at h
    injection h with hbs
    rw [← hbs]
    exact abstractBytesHaveProv_encodeLittleEndianBytes_none sv.bits sv.sizeBytes

private theorem abstractBytesHaveProv_replicateUninitBytes (n : Nat) :
    abstractBytesHaveProv (replicateUninitBytes n) = false := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold replicateUninitBytes abstractBytesHaveProv
    exact ih

private theorem abstractBytesHaveProv_writeAbstractBytesAt
    (buf patch out : List AbstractByte) (off : Nat)
    (hbuf : abstractBytesHaveProv buf = false)
    (hpatch : abstractBytesHaveProv patch = false)
    (hw : writeAbstractBytesAt buf off patch = .some out) :
    abstractBytesHaveProv out = false := by
  induction buf generalizing off patch out with
  | nil =>
    cases patch with
    | nil => injection hw with ho; rw [← ho]
    | cons _ _ => cases hw
  | cons b bufRest ih =>
    cases patch with
    | nil => injection hw with ho; rw [← ho]; exact hbuf
    | cons w wRest =>
      have hb : abstractBytesHaveProv [b] = false ∧ abstractBytesHaveProv bufRest = false := by
        cases b with
        | uninit => exact ⟨rfl, hbuf⟩
        | init _ prov =>
          cases prov with
          | none => exact ⟨rfl, hbuf⟩
          | some _ => cases hbuf
      have hw0 : abstractBytesHaveProv [w] = false ∧ abstractBytesHaveProv wRest = false := by
        cases w with
        | uninit => exact ⟨rfl, hpatch⟩
        | init _ prov =>
          cases prov with
          | none => exact ⟨rfl, hpatch⟩
          | some _ => cases hpatch
      cases off with
      | zero =>
        unfold writeAbstractBytesAt at hw
        cases hrec : writeAbstractBytesAt bufRest 0 wRest with
        | none => rw [hrec] at hw; cases hw
        | some tail' =>
          rw [hrec] at hw
          injection hw with ho
          rw [← ho]
          have htail := ih wRest tail' 0 hb.2 hw0.2 hrec
          cases w with
          | uninit => exact htail
          | init _ prov =>
            cases prov with
            | none => exact htail
            | some _ => cases hw0.1
      | succ off' =>
        unfold writeAbstractBytesAt at hw
        cases hrec : writeAbstractBytesAt bufRest off' (w :: wRest) with
        | none => rw [hrec] at hw; cases hw
        | some tail' =>
          rw [hrec] at hw
          injection hw with ho
          rw [← ho]
          have htail := ih (w :: wRest) tail' off' hb.2 hpatch hrec
          cases b with
          | uninit => exact htail
          | init _ prov =>
            cases prov with
            | none => exact htail
            | some _ => cases hb.1

/-- Encoding any provenance-free `Value` (`valueHasProv v = false`) via
`encodeUntypedValueToBytes` yields provenance-free bytes. -/
theorem abstractBytesHaveProv_encodeUntypedValueToBytes_of_no_prov
    (fuel : Nat) (v : Value) (bs : List AbstractByte)
    (hnp : valueHasProv v = false)
    (he : encodeUntypedValueToBytes fuel v = .some bs) :
    abstractBytesHaveProv bs = false := by
  induction fuel generalizing v bs with
  | zero => unfold encodeUntypedValueToBytes at he; cases he
  | succ fuel' ih =>
    cases v with
    | unit => injection he with hbs; rw [← hbs]
    | scalar sv => exact abstractBytesHaveProv_encodeScalarBytes_none sv bs he
    | ptr _ _ => cases hnp
    | aggregate _ fields =>
      unfold encodeUntypedValueToBytes at he
      dsimp only [valueHasProv] at hnp
      have hgo : ∀ (fs : List Value) (out : List AbstractByte),
          valueListHasProv fs = false →
          encodeUntypedValueToBytes.encodeFields fuel' fs = .some out →
          abstractBytesHaveProv out = false := by
        intro fs
        induction fs with
        | nil =>
          intro out _ hgo
          injection hgo with ho; rw [← ho]
        | cons f rest ihf =>
          intro out hfs hgo
          unfold valueListHasProv at hfs
          have hf0 : valueHasProv f = false := by
            cases hf : valueHasProv f with
            | false => rfl
            | true => rw [hf] at hfs; cases hfs
          have hr0 : valueListHasProv rest = false := by
            rw [hf0] at hfs; exact hfs
          unfold encodeUntypedValueToBytes.encodeFields at hgo
          cases he1 : encodeUntypedValueToBytes fuel' f with
          | none => rw [he1] at hgo; cases hgo
          | some b1 =>
            rw [he1] at hgo
            cases he2 : encodeUntypedValueToBytes.encodeFields fuel' rest with
            | none => rw [he2] at hgo; cases hgo
            | some b2 =>
              rw [he2] at hgo
              injection hgo with ho
              rw [← ho, abstractBytesHaveProv_appendAbstractBytes,
                ih f b1 hf0 he1, ihf b2 hr0 he2]
              rfl
      exact hgo fields bs hnp he

private theorem abstractBytesHaveProv_encodeListWith
    (enc : Value → Option (List AbstractByte)) (sz : Nat) (elems : List Value)
    (out : List AbstractByte)
    (henc : ∀ v bs, valueHasProv v = false → enc v = .some bs → abstractBytesHaveProv bs = false)
    (hnp : valueListHasProv elems = false)
    (he : encodeListWith enc sz elems = .some out) :
    abstractBytesHaveProv out = false := by
  induction elems generalizing out with
  | nil => injection he with ho; rw [← ho]
  | cons v rest ih =>
    unfold valueListHasProv at hnp
    have hv0 : valueHasProv v = false := by
      cases hv : valueHasProv v with
      | false => rfl
      | true => rw [hv] at hnp; cases hnp
    have hr0 : valueListHasProv rest = false := by rw [hv0] at hnp; exact hnp
    unfold encodeListWith at he
    cases he1 : enc v with
    | none => rw [he1] at he; cases he
    | some b1 =>
      rw [he1] at he; dsimp only at he
      cases hsz : Nat.beq (length b1) sz with
      | false => rw [hsz] at he; cases he
      | true =>
        rw [hsz] at he; dsimp only at he
        cases he2 : encodeListWith enc sz rest with
        | none => rw [he2] at he; cases he
        | some b2 =>
          rw [he2] at he
          injection he with ho
          rw [← ho, abstractBytesHaveProv_appendAbstractBytes,
            henc v b1 hv0 he1, ih b2 hr0 he2]
          rfl

private theorem abstractBytesHaveProv_encodeSeqFieldsWith
    (enc : RigidTy → Value → Option (List AbstractByte))
    (ks : List RigidTy) (vs : List Value) (out : List AbstractByte)
    (henc : ∀ k v bs, valueHasProv v = false → enc k v = .some bs →
      abstractBytesHaveProv bs = false)
    (hnp : valueListHasProv vs = false)
    (he : encodeSeqFieldsWith enc ks vs = .some out) :
    abstractBytesHaveProv out = false := by
  induction ks generalizing vs out with
  | nil =>
    cases vs with
    | nil => injection he with ho; rw [← ho]
    | cons _ _ => cases he
  | cons k kRest ih =>
    cases vs with
    | nil => cases he
    | cons v vRest =>
      unfold valueListHasProv at hnp
      have hv0 : valueHasProv v = false := by
        cases hv : valueHasProv v with
        | false => rfl
        | true => rw [hv] at hnp; cases hnp
      have hr0 : valueListHasProv vRest = false := by rw [hv0] at hnp; exact hnp
      unfold encodeSeqFieldsWith at he
      cases he1 : enc k v with
      | none => rw [he1] at he; cases he
      | some b1 =>
        rw [he1] at he
        cases he2 : encodeSeqFieldsWith enc kRest vRest with
        | none => rw [he2] at he; cases he
        | some b2 =>
          rw [he2] at he
          injection he with ho
          rw [← ho, abstractBytesHaveProv_appendAbstractBytes,
            henc k v b1 hv0 he1, ih vRest b2 hr0 he2]
          rfl

private theorem abstractBytesHaveProv_encodeFieldsAtOffsetsWith
    (encT : RigidTy → Value → Option (List AbstractByte))
    (encF : Value → Option (List AbstractByte))
    (offsets : List Size) (ks : List RigidTy) (vs : List Value)
    (buf out : List AbstractByte)
    (hT : ∀ k v bs, valueHasProv v = false → encT k v = .some bs →
      abstractBytesHaveProv bs = false)
    (hF : ∀ v bs, valueHasProv v = false → encF v = .some bs →
      abstractBytesHaveProv bs = false)
    (hbuf : abstractBytesHaveProv buf = false)
    (hnp : valueListHasProv vs = false)
    (he : encodeFieldsAtOffsetsWith encT encF offsets ks vs buf = .some out) :
    abstractBytesHaveProv out = false := by
  induction offsets generalizing ks vs buf out with
  | nil =>
    cases vs with
    | nil => injection he with ho; rw [← ho]; exact hbuf
    | cons _ _ => cases he
  | cons off offRest ih =>
    cases vs with
    | nil => cases he
    | cons v vRest =>
      unfold valueListHasProv at hnp
      have hv0 : valueHasProv v = false := by
        cases hv : valueHasProv v with
        | false => rfl
        | true => rw [hv] at hnp; cases hnp
      have hr0 : valueListHasProv vRest = false := by rw [hv0] at hnp; exact hnp
      unfold encodeFieldsAtOffsetsWith at he
      dsimp only at he
      cases ks with
      | nil =>
        dsimp only at he
        cases hfb : encF v with
        | none => rw [hfb] at he; cases he
        | some fb =>
          rw [hfb] at he; dsimp only at he
          cases hw : writeAbstractBytesAt buf off.bytes fb with
          | none => rw [hw] at he; cases he
          | some buf' =>
            rw [hw] at he; dsimp only at he
            have hbuf' := abstractBytesHaveProv_writeAbstractBytesAt buf fb buf' off.bytes
              hbuf (hF v fb hv0 hfb) hw
            exact ih .nil vRest buf' out hbuf' hr0 he
      | cons k kRest =>
        dsimp only at he
        cases ht : encT k v with
        | some fb =>
          rw [ht] at he; dsimp only at he
          cases hw : writeAbstractBytesAt buf off.bytes fb with
          | none => rw [hw] at he; cases he
          | some buf' =>
            rw [hw] at he; dsimp only at he
            have hbuf' := abstractBytesHaveProv_writeAbstractBytesAt buf fb buf' off.bytes
              hbuf (hT k v fb hv0 ht) hw
            exact ih kRest vRest buf' out hbuf' hr0 he
        | none =>
          rw [ht] at he; dsimp only at he
          cases hkb : rigidTyKindByteSize k with
          | some _ => rw [hkb] at he; cases he
          | none =>
            rw [hkb] at he; dsimp only at he
            cases hfb : encF v with
            | none => rw [hfb] at he; cases he
            | some fb =>
              rw [hfb] at he; dsimp only at he
              cases hw : writeAbstractBytesAt buf off.bytes fb with
              | none => rw [hw] at he; cases he
              | some buf' =>
                rw [hw] at he; dsimp only at he
                have hbuf' := abstractBytesHaveProv_writeAbstractBytesAt buf fb buf' off.bytes
                  hbuf (hF v fb hv0 hfb) hw
                exact ih kRest vRest buf' out hbuf' hr0 he

private theorem abstractBytesHaveProv_encodeUnionFieldsWith
    (encF : Value → Option (List AbstractByte)) (totalSize : Nat)
    (fieldVals : List Value) (out : List AbstractByte)
    (hF : ∀ v bs, valueHasProv v = false → encF v = .some bs →
      abstractBytesHaveProv bs = false)
    (hnp : valueListHasProv fieldVals = false)
    (he : encodeUnionFieldsWith encF totalSize fieldVals = .some out) :
    abstractBytesHaveProv out = false := by
  have hfind : ∀ fs bs, valueListHasProv fs = false →
      encodeUnionFieldsWith.findFullSize encF totalSize fs = .some bs →
      abstractBytesHaveProv bs = false := by
    intro fs
    induction fs with
    | nil => intro bs _ h; cases h
    | cons fv rest ih =>
      intro bs hfs h
      unfold valueListHasProv at hfs
      have hfv0 : valueHasProv fv = false := by
        cases hf : valueHasProv fv with
        | false => rfl
        | true => rw [hf] at hfs; cases hfs
      have hr0 : valueListHasProv rest = false := by rw [hfv0] at hfs; exact hfs
      unfold encodeUnionFieldsWith.findFullSize at h
      cases hf : encF fv with
      | none => rw [hf] at h; exact ih bs hr0 h
      | some fBytes =>
        rw [hf] at h; dsimp only at h
        cases hsz : Nat.beq (length fBytes) totalSize with
        | false => rw [hsz] at h; exact ih bs hr0 h
        | true =>
          rw [hsz] at h
          exact abstractBytesHaveProv_writeAbstractBytesAt
            (replicateUninitBytes totalSize) fBytes bs 0
            (abstractBytesHaveProv_replicateUninitBytes totalSize) (hF fv fBytes hfv0 hf) h
  unfold encodeUnionFieldsWith at he
  cases fieldVals with
  | nil => cases he
  | cons firstField rest =>
    dsimp only at he
    unfold valueListHasProv at hnp
    have hff0 : valueHasProv firstField = false := by
      cases hf : valueHasProv firstField with
      | false => rfl
      | true => rw [hf] at hnp; cases hnp
    have hr0 : valueListHasProv rest = false := by rw [hff0] at hnp; exact hnp
    cases h1 : encF firstField with
    | none => rw [h1] at he; exact hfind rest out hr0 he
    | some firstBytes =>
      rw [h1] at he; dsimp only at he
      have hfb0 := hF firstField firstBytes hff0 h1
      cases hsz : Nat.beq (length firstBytes) totalSize with
      | true =>
        rw [hsz] at he; dsimp only at he
        cases hff : encodeUnionFieldsWith.findFullSize encF totalSize (firstField :: rest) with
        | some bs =>
          rw [hff] at he; injection he with ho; rw [← ho]
          exact hfind (firstField :: rest) bs (by unfold valueListHasProv; rw [hff0, hr0]; rfl) hff
        | none =>
          rw [hff] at he
          exact abstractBytesHaveProv_writeAbstractBytesAt
            (replicateUninitBytes totalSize) firstBytes out 0
            (abstractBytesHaveProv_replicateUninitBytes totalSize) hfb0 he
      | false =>
        rw [hsz] at he; dsimp only at he
        cases hz : Nat.beq (length firstBytes) 0 with
        | true =>
          rw [hz] at he; dsimp only at he
          cases hff : encodeUnionFieldsWith.findFullSize encF totalSize rest with
          | some bs =>
            rw [hff] at he; injection he with ho; rw [← ho]; exact hfind rest bs hr0 hff
          | none =>
            rw [hff] at he
            exact abstractBytesHaveProv_writeAbstractBytesAt
              (replicateUninitBytes totalSize) firstBytes out 0
              (abstractBytesHaveProv_replicateUninitBytes totalSize) hfb0 he
        | false =>
          rw [hz] at he; dsimp only at he
          cases hff : encodeUnionFieldsWith.findFullSize encF totalSize rest with
          | some bs =>
            rw [hff] at he
            exact abstractBytesHaveProv_writeAbstractBytesAt bs firstBytes out 0
              (hfind rest bs hr0 hff) hfb0 he
          | none =>
            rw [hff] at he
            exact abstractBytesHaveProv_writeAbstractBytesAt
              (replicateUninitBytes totalSize) firstBytes out 0
              (abstractBytesHaveProv_replicateUninitBytes totalSize) hfb0 he

/-- Encoding any provenance-free `Value` (`valueHasProv v = false`) via
`encodeValueToBytes` yields provenance-free bytes (covering scalars, unit,
arrays, tuples, structs, unions without overlays, and multi-variant enums). -/
theorem abstractBytesHaveProv_encodeValueToBytes_of_no_prov
    (fuel : Nat) (layouts : LayoutTable) (ty : Ty) (v : Value) (bs : List AbstractByte)
    (hnp : valueHasProv v = false)
    (he : encodeValueToBytes fuel layouts ty v = .some bs) :
    abstractBytesHaveProv bs = false := by
  induction fuel generalizing ty v bs with
  | zero => cases he
  | succ fuel' ih =>
    unfold encodeValueToBytes at he
    cases hk : ty.kind with
    | bool =>
      rw [hk] at he; dsimp only at he
      cases v with
      | scalar sv =>
        dsimp only at he
        cases hsz : Nat.beq sv.sizeBytes 1 with
        | false => rw [hsz] at he; cases he
        | true =>
          rw [hsz] at he; dsimp only at he
          cases h0 : Nat.beq sv.bits 0 with
          | true => rw [h0] at he; injection he with hbs; rw [← hbs]
          | false =>
            rw [h0] at he; dsimp only at he
            cases h1 : Nat.beq sv.bits 1 with
            | true => rw [h1] at he; injection he with hbs; rw [← hbs]
            | false => rw [h1] at he; cases he
      | unit | ptr _ _ | aggregate _ _ => cases he
    | char =>
      rw [hk] at he; dsimp only at he
      cases v with
      | scalar sv =>
        dsimp only at he
        cases hc : Bool.and (Nat.beq sv.sizeBytes 4) (isValidCharCode sv.bits) with
        | false => rw [hc] at he; cases he
        | true => rw [hc] at he; exact abstractBytesHaveProv_encodeScalarBytes_none sv bs he
      | unit | ptr _ _ | aggregate _ _ => cases he
    | uint w =>
      rw [hk] at he; dsimp only at he
      cases hi : intCastTargetBytes (.uint w) with
      | none => rw [hi] at he; cases he
      | some exp =>
        rw [hi] at he
        cases v with
        | scalar sv =>
          dsimp only at he
          cases hsz : Nat.beq sv.sizeBytes exp with
          | false => rw [hsz] at he; cases he
          | true => rw [hsz] at he; exact abstractBytesHaveProv_encodeScalarBytes_none sv bs he
        | unit | ptr _ _ | aggregate _ _ => cases he
    | int w =>
      rw [hk] at he; dsimp only at he
      cases hi : intCastTargetBytes (.int w) with
      | none => rw [hi] at he; cases he
      | some exp =>
        rw [hi] at he
        cases v with
        | scalar sv =>
          dsimp only at he
          cases hsz : Nat.beq sv.sizeBytes exp with
          | false => rw [hsz] at he; cases he
          | true => rw [hsz] at he; exact abstractBytesHaveProv_encodeScalarBytes_none sv bs he
        | unit | ptr _ _ | aggregate _ _ => cases he
    | fnDef _ _ =>
      rw [hk] at he; dsimp only at he
      cases v with
      | unit => injection he with hbs; rw [← hbs]
      | aggregate varIdx fs =>
        cases varIdx with
        | zero =>
          cases fs with
          | nil => injection he with hbs; rw [← hbs]
          | cons _ _ => cases he
        | succ _ => cases he
      | scalar _ | ptr _ _ => cases he
    | fnPtr _ _ _ _ =>
      rw [hk] at he; dsimp only at he
      cases v with
      | ptr _ _ => cases hnp
      | scalar sv =>
        dsimp only at he
        cases hsz : Nat.beq sv.sizeBytes 8 with
        | false => rw [hsz] at he; cases he
        | true => rw [hsz] at he; exact abstractBytesHaveProv_encodeScalarBytes_none sv bs he
      | unit | aggregate _ _ => cases he
    | rawPtr _ pointee =>
      rw [hk] at he; dsimp only at he
      cases v with
      | ptr _ _ => cases hnp
      | unit => cases pointee <;> cases he
      | scalar sv =>
        have hsc : (match Nat.beq sv.sizeBytes 8 with
            | true => encodeScalarBytes sv
            | false => none) = some bs → abstractBytesHaveProv bs = false := by
          intro h1
          cases hsz : Nat.beq sv.sizeBytes 8 with
          | false => rw [hsz] at h1; cases h1
          | true => rw [hsz] at h1; exact abstractBytesHaveProv_encodeScalarBytes_none sv bs h1
        cases pointee <;> first | cases he | exact hsc he
      | aggregate varIdx fs =>
        cases varIdx with
        | succ _ => cases pointee <;> cases he
        | zero =>
          cases fs with
          | nil => cases pointee <;> cases he
          | cons f0 _ =>
            cases f0 with
            | ptr _ _ => cases hnp
            | unit | scalar _ | aggregate _ _ => cases pointee <;> cases he
    | ref _ pointee =>
      rw [hk] at he; dsimp only at he
      cases v with
      | ptr _ _ => cases hnp
      | unit => cases pointee <;> cases he
      | scalar sv =>
        have hsc : (match Nat.beq sv.sizeBytes 8 with
            | true => encodeScalarBytes sv
            | false => none) = some bs → abstractBytesHaveProv bs = false := by
          intro h1
          cases hsz : Nat.beq sv.sizeBytes 8 with
          | false => rw [hsz] at h1; cases h1
          | true => rw [hsz] at h1; exact abstractBytesHaveProv_encodeScalarBytes_none sv bs h1
        cases pointee <;> first | cases he | exact hsc he
      | aggregate varIdx fs =>
        cases varIdx with
        | succ _ => cases pointee <;> cases he
        | zero =>
          cases fs with
          | nil => cases pointee <;> cases he
          | cons f0 _ =>
            cases f0 with
            | ptr _ _ => cases hnp
            | unit | scalar _ | aggregate _ _ => cases pointee <;> cases he
    | array elemKind n =>
      rw [hk] at he; dsimp only at he
      cases hn0 : Nat.beq n 0 with
      | true =>
        rw [hn0] at he; dsimp only at he
        cases v with
        | unit => injection he with hbs; rw [← hbs]
        | aggregate varIdx fs =>
          cases varIdx with
          | zero =>
            cases fs with
            | nil => injection he with hbs; rw [← hbs]
            | cons _ _ => cases he
          | succ _ => cases he
        | scalar _ | ptr _ _ => cases he
      | false =>
        rw [hn0] at he; dsimp only at he
        cases v with
        | aggregate varIdx elems =>
          cases varIdx with
          | succ _ => cases he
          | zero =>
            change (match Nat.beq (length elems) n with
              | false => none
              | true =>
                match (match rigidTyKindByteSize elemKind with
                  | .some sz => Option.some sz
                  | .none =>
                    match LayoutTable.lookup layouts ty.layoutIdx with
                    | .some l =>
                      match l.fields with
                      | .array stride _ => Option.some stride.bytes
                      | _ => none
                    | .none =>
                      match (generalizing := false) elemKind with
                      | .tuple ks => tupleFieldsByteSize ks
                      | _ => none) with
                | .none => none
                | .some elemSz =>
                  encodeListWith
                    (fun e => encodeValueToBytes fuel' layouts { kind := elemKind, layoutIdx := 0 } e)
                    elemSz elems) = .some bs at he
            cases hlen : Nat.beq (length elems) n with
            | false => rw [hlen] at he; cases he
            | true =>
              rw [hlen] at he; dsimp only at he
              have hgen : ∀ o : Option Nat,
                  (match o with
                   | none => none
                   | some elemSz =>
                     encodeListWith
                       (fun e => encodeValueToBytes fuel' layouts { kind := elemKind, layoutIdx := 0 } e)
                       elemSz elems) = .some bs →
                  abstractBytesHaveProv bs = false := by
                intro o ho
                cases o with
                | none => cases ho
                | some elemSz =>
                  exact abstractBytesHaveProv_encodeListWith
                    (fun e => encodeValueToBytes fuel' layouts { kind := elemKind, layoutIdx := 0 } e)
                    elemSz elems bs
                    (fun e ebs henp hee => ih { kind := elemKind, layoutIdx := 0 } e ebs henp hee)
                    hnp ho
              exact hgen _ he
        | unit | scalar _ | ptr _ _ => cases he
    | tuple ks =>
      rw [hk] at he; dsimp only at he
      cases ks with
      | nil =>
        cases v with
        | unit => injection he with hbs; rw [← hbs]
        | aggregate varIdx fs =>
          cases varIdx with
          | zero =>
            cases fs with
            | nil => injection he with hbs; rw [← hbs]
            | cons _ _ => cases he
          | succ _ => cases he
        | scalar _ | ptr _ _ => cases he
      | cons kHead kTail =>
        dsimp only at he
        cases v with
        | aggregate varIdx fieldVals =>
          cases varIdx with
          | succ _ => cases he
          | zero =>
            change (match Nat.beq (length fieldVals) (length (kHead :: kTail)) with
              | false => none
              | true =>
                match LayoutTable.lookup layouts ty.layoutIdx with
                | .some l =>
                  match l.fields with
                  | .arbitrary offsets _ =>
                    match Nat.beq (length offsets) (length fieldVals) with
                    | true =>
                      encodeFieldsAtOffsetsWith
                        (fun k fv => encodeValueToBytes fuel' layouts { kind := k, layoutIdx := 0 } fv)
                        (fun fv => encodeUntypedValueToBytes fuel' fv) offsets (kHead :: kTail) fieldVals
                        (replicateUninitBytes l.size.bytes)
                    | false =>
                      encodeSeqFieldsWith
                        (fun k fv => encodeValueToBytes fuel' layouts { kind := k, layoutIdx := 0 } fv)
                        (kHead :: kTail) fieldVals
                  | _ =>
                    encodeSeqFieldsWith
                      (fun k fv => encodeValueToBytes fuel' layouts { kind := k, layoutIdx := 0 } fv)
                      (kHead :: kTail) fieldVals
                | .none =>
                  encodeSeqFieldsWith
                    (fun k fv => encodeValueToBytes fuel' layouts { kind := k, layoutIdx := 0 } fv)
                    (kHead :: kTail) fieldVals) = .some bs at he
            cases hlen : Nat.beq (length fieldVals) (length (kHead :: kTail)) with
            | false => rw [hlen] at he; cases he
            | true =>
              rw [hlen] at he; dsimp only at he
              cases hlk : LayoutTable.lookup layouts ty.layoutIdx with
              | none =>
                rw [hlk] at he
                exact abstractBytesHaveProv_encodeSeqFieldsWith _ (kHead :: kTail) fieldVals bs
                  (fun k fv fbs hfnp hfe => ih { kind := k, layoutIdx := 0 } fv fbs hfnp hfe)
                  hnp he
              | some l =>
                rw [hlk] at he; dsimp only at he
                cases hlf : l.fields with
                | arbitrary offsets _ =>
                  rw [hlf] at he; dsimp only at he
                  cases hlo : Nat.beq (length offsets) (length fieldVals) with
                  | true =>
                    rw [hlo] at he
                    exact abstractBytesHaveProv_encodeFieldsAtOffsetsWith _ _ offsets
                      (kHead :: kTail) fieldVals (replicateUninitBytes l.size.bytes) bs
                      (fun k fv fbs hfnp hfe => ih { kind := k, layoutIdx := 0 } fv fbs hfnp hfe)
                      (fun fv fbs hfnp hfe =>
                        abstractBytesHaveProv_encodeUntypedValueToBytes_of_no_prov fuel' fv fbs hfnp hfe)
                      (abstractBytesHaveProv_replicateUninitBytes l.size.bytes) hnp he
                  | false =>
                    rw [hlo] at he
                    exact abstractBytesHaveProv_encodeSeqFieldsWith _ (kHead :: kTail) fieldVals bs
                      (fun k fv fbs hfnp hfe => ih { kind := k, layoutIdx := 0 } fv fbs hfnp hfe)
                      hnp he
                | primitive | union _ | array _ _ =>
                  rw [hlf] at he
                  exact abstractBytesHaveProv_encodeSeqFieldsWith _ (kHead :: kTail) fieldVals bs
                    (fun k fv fbs hfnp hfe => ih { kind := k, layoutIdx := 0 } fv fbs hfnp hfe)
                    hnp he
        | unit | scalar _ | ptr _ _ => cases he
    | adt _ args =>
      rw [hk] at he; dsimp only at he
      cases hlk : LayoutTable.lookup layouts ty.layoutIdx with
      | none =>
        rw [hlk] at he; dsimp only at he
        cases v with
        | unit => injection he with hbs; rw [← hbs]
        | aggregate varIdx fs =>
          cases varIdx with
          | zero =>
            cases fs with
            | nil => injection he with hbs; rw [← hbs]
            | cons _ _ =>
              exact abstractBytesHaveProv_encodeUntypedValueToBytes_of_no_prov fuel' _ bs hnp he
          | succ _ =>
            exact abstractBytesHaveProv_encodeUntypedValueToBytes_of_no_prov fuel' _ bs hnp he
        | scalar _ | ptr _ _ =>
          exact abstractBytesHaveProv_encodeUntypedValueToBytes_of_no_prov fuel' _ bs hnp he
      | some l =>
        rw [hlk] at he; dsimp only at he
        cases hu : l.isUninhabited with
        | true => rw [hu] at he; cases he
        | false =>
          rw [hu] at he; dsimp only at he
          cases hv : l.variants with
          | empty => rw [hv] at he; cases he
          | single expectedVar =>
            rw [hv] at he; dsimp only at he
            cases hlf : l.fields with
            | arbitrary offsets _ =>
              rw [hlf] at he
              cases v with
              | aggregate varIdx fieldVals =>
                dsimp only at he
                cases hok : Bool.and (Nat.beq varIdx expectedVar)
                    (Nat.beq (length offsets) (length fieldVals)) with
                | false => rw [hok] at he; cases he
                | true =>
                  rw [hok] at he; dsimp only at he
                  exact abstractBytesHaveProv_encodeFieldsAtOffsetsWith _ _ offsets _ fieldVals
                    (replicateUninitBytes l.size.bytes) bs
                    (fun k fv fbs hfnp hfe => ih { kind := k, layoutIdx := 0 } fv fbs hfnp hfe)
                    (fun fv fbs hfnp hfe =>
                      abstractBytesHaveProv_encodeUntypedValueToBytes_of_no_prov fuel' fv fbs hfnp hfe)
                    (abstractBytesHaveProv_replicateUninitBytes l.size.bytes) hnp he
              | unit =>
                cases offsets with
                | nil =>
                  injection he with hbs; rw [← hbs]
                  exact abstractBytesHaveProv_replicateUninitBytes l.size.bytes
                | cons _ _ => cases he
              | scalar _ | ptr _ _ => cases he
            | primitive =>
              rw [hlf] at he
              cases v with
              | scalar sv =>
                dsimp only at he
                cases hsz : Nat.beq sv.sizeBytes l.size.bytes with
                | false => rw [hsz] at he; cases he
                | true => rw [hsz] at he; exact abstractBytesHaveProv_encodeScalarBytes_none sv bs he
              | unit | ptr _ _ | aggregate _ _ => cases he
            | union _ =>
              rw [hlf] at he
              cases v with
              | aggregate _ fieldVals =>
                exact abstractBytesHaveProv_encodeUnionFieldsWith _ l.size.bytes fieldVals bs
                  (fun fv fbs hfnp hfe =>
                    abstractBytesHaveProv_encodeUntypedValueToBytes_of_no_prov fuel' fv fbs hfnp hfe)
                  hnp he
              | unit | scalar _ | ptr _ _ => cases he
            | array _ _ => rw [hlf] at he; cases he
          | multiple tagLayout tagField variantShapes =>
            rw [hv] at he; dsimp only at he
            cases v with
            | aggregate varIdx fieldVals =>
              dsimp only at he
              cases hlf : l.fields with
              | arbitrary outerOffsets _ =>
                rw [hlf] at he
                cases htw : scalarLayoutByteWidth tagLayout with
                | none => rw [htw] at he; cases he
                | some tagSz =>
                  rw [htw] at he
                  cases hvs : get? variantShapes varIdx with
                  | none => rw [hvs] at he; cases he
                  | some vs =>
                    rw [hvs] at he
                    cases vs with
                    | arbitrary varOffsets _ =>
                      dsimp only at he
                      cases hgo : get? outerOffsets tagField with
                      | none => rw [hgo] at he; cases he
                      | some tagOff =>
                        rw [hgo] at he; dsimp only at he
                        cases htb : encodeScalarBytes ⟨varIdx, tagSz⟩ .none with
                        | none => rw [htb] at he; cases he
                        | some tagBytes =>
                          rw [htb] at he; dsimp only at he
                          cases hwb : writeAbstractBytesAt (replicateUninitBytes l.size.bytes)
                              tagOff.bytes tagBytes with
                          | none => rw [hwb] at he; cases he
                          | some bufWithTag =>
                            rw [hwb] at he; dsimp only at he
                            have hbufTag := abstractBytesHaveProv_writeAbstractBytesAt
                              (replicateUninitBytes l.size.bytes) tagBytes bufWithTag tagOff.bytes
                              (abstractBytesHaveProv_replicateUninitBytes l.size.bytes)
                              (abstractBytesHaveProv_encodeScalarBytes_none _ tagBytes htb) hwb
                            exact abstractBytesHaveProv_encodeFieldsAtOffsetsWith _ _ varOffsets
                              .nil fieldVals bufWithTag bs
                              (fun k fv fbs hfnp hfe =>
                                ih { kind := k, layoutIdx := 0 } fv fbs hfnp hfe)
                              (fun fv fbs hfnp hfe =>
                                abstractBytesHaveProv_encodeUntypedValueToBytes_of_no_prov
                                  fuel' fv fbs hfnp hfe)
                              hbufTag hnp he
                    | primitive | union _ | array _ _ => cases he
              | primitive | union _ | array _ _ => rw [hlf] at he; cases he
            | unit | scalar _ | ptr _ _ => cases he
    | float _ | str | slice _ | never | dynamic _ | foreign _ | closure _ _ | param _ | alias _ | other _ =>
      rw [hk] at he; cases he

private theorem abstractBytesHaveProv_encodeByLayoutIdxAux_scalar
    (fuel : Nat) (layouts : LayoutTable) (idx : Nat) (sv : ScalarVal) (bs : List AbstractByte)
    (he : encodeByLayoutIdxAux fuel layouts idx (.scalar sv) = .some bs) :
    abstractBytesHaveProv bs = false := by
  cases fuel with
  | zero => unfold encodeByLayoutIdxAux at he; cases he
  | succ _ =>
    unfold encodeByLayoutIdxAux at he
    dsimp only at he
    have hgen : ∀ b : Bool,
        (match b with | true => encodeScalarBytes sv | false => .none) = .some bs →
        abstractBytesHaveProv bs = false := by
      intro b hb
      cases b with
      | false => cases hb
      | true => exact abstractBytesHaveProv_encodeScalarBytes_none sv bs hb
    exact hgen _ he

/-- **Cast-level provenance-free equivalence for scalar sources**: whenever the
source operand of `evalByteCastWithPolicy` evaluates to a plain `Value.scalar`
(covering `u64 → f64`, `usize → *const u8`, `usize → &u8`, `i32 → f32`,
`u8 → bool`, `u32 → char`, etc.), `.stripProvenance` and `.strictUcg630Ub`
return the **exact identical** `RvalueEvalResult` for **every** target type
`targetTy`, memory, and layout table. -/
theorem evalByteCastWithPolicy_strip_eq_strict_of_scalar_src
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (sv : ScalarVal) (locals' : List LocalSlot)
    (hev : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals
      localDecls mem.callStack = .ok (.scalar sv) locals') :
    evalByteCastWithPolicy .stripProvenance locals op targetTy mem localDecls layouts =
      evalByteCastWithPolicy .strictUcg630Ub locals op targetTy mem localDecls layouts := by
  have hno_prov_src : ∀ srcTy bs,
      encodeByteCastSourceBytes layouts srcTy (.scalar sv) = .some bs →
      abstractBytesHaveProv bs = false := by
    intro srcTy bs hbs
    unfold encodeByteCastSourceBytes at hbs
    cases het : encodeTypedValueToBytes layouts srcTy (.scalar sv) with
    | some bs' =>
      rw [het] at hbs
      injection hbs with heq; rw [← heq]
      unfold encodeTypedValueToBytes at het
      dsimp only at het
      cases hu : isUnionLayout layouts (normalizeCodecTy srcTy) with
      | true =>
        rw [hu] at het
        exact abstractBytesHaveProv_encodeByLayoutIdxAux_scalar 8 layouts _ sv bs' het
      | false =>
        rw [hu] at het
        cases hev' : encodeValueToBytes defaultCodecFuel layouts (normalizeCodecTy srcTy) (.scalar sv) with
        | some bs'' =>
          rw [hev'] at het; injection het with heq2; rw [← heq2]
          exact abstractBytesHaveProv_encodeValueToBytes_of_no_prov
            defaultCodecFuel layouts _ (.scalar sv) bs'' rfl hev'
        | none =>
          rw [hev'] at het; dsimp only at het
          cases hk : (normalizeCodecTy srcTy).kind with
          | adt _ _ | array _ _ =>
            rw [hk] at het; dsimp only at het
            cases hlk : LayoutTable.lookup layouts (normalizeCodecTy srcTy).layoutIdx with
            | none => rw [hlk] at het; cases het
            | some _ =>
              rw [hlk] at het
              exact abstractBytesHaveProv_encodeByLayoutIdxAux_scalar 8 layouts _ sv bs' het
          | tuple ks =>
            rw [hk] at het
            cases ks with
            | nil => cases het
            | cons _ _ =>
              dsimp only at het
              cases hlk : LayoutTable.lookup layouts (normalizeCodecTy srcTy).layoutIdx with
              | none => rw [hlk] at het; cases het
              | some _ =>
                rw [hlk] at het
                exact abstractBytesHaveProv_encodeByLayoutIdxAux_scalar 8 layouts _ sv bs' het
          | bool | char | int _ | uint _ | float _ | never | str | slice _ | ref _ _ | rawPtr _ _
          | fnDef _ _ | fnPtr _ _ _ _ | closure _ _ | dynamic _ | foreign _ | param _ | alias _
          | other _ =>
            rw [hk] at het; cases het
    | none =>
      rw [het] at hbs
      cases hu : isUnionLayout layouts (normalizeCodecTy srcTy) with
      | true => rw [hu] at hbs; cases hbs
      | false =>
        rw [hu] at hbs
        exact abstractBytesHaveProv_encodeUntypedValueToBytes_of_no_prov
          defaultCodecFuel (.scalar sv) bs rfl hbs
  unfold evalByteCastWithPolicy
  rw [hev]
  dsimp only
  cases tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts targetTy) with
  | none => rfl
  | some dstSize =>
    dsimp only
    cases operandTy localDecls layouts op with
    | some srcTy =>
      dsimp only
      cases tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts srcTy) with
      | none => rfl
      | some srcSize =>
        dsimp only
        cases Nat.beq srcSize dstSize with
        | false => rfl
        | true =>
          dsimp only
          cases hbs : encodeByteCastSourceBytes layouts
              (resolveTyWithLocalDecls localDecls layouts srcTy) (.scalar sv) with
          | none => rfl
          | some bs =>
            dsimp only
            cases Nat.beq (length bs) dstSize with
            | false => rfl
            | true =>
              dsimp only
              rw [decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
                defaultCodecFuel layouts _ bs (hno_prov_src _ bs hbs)]
    | none =>
      dsimp only
      cases hbs : encodeUntypedValueToBytes defaultCodecFuel (.scalar sv) with
      | none => rfl
      | some bs =>
        dsimp only
        cases Nat.beq (length bs) dstSize with
        | false => rfl
        | true =>
          dsimp only
          rw [decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
            defaultCodecFuel layouts _ bs
            (abstractBytesHaveProv_encodeUntypedValueToBytes_of_no_prov
              defaultCodecFuel (.scalar sv) bs rfl hbs)]

/-- **Cast-level provenance-free equivalence for non-union aggregate sources**:
whenever the source operand evaluates to any provenance-free `Value`
(`valueHasProv v = false`, e.g., `[u8; 8]`, `(u32, u32)`, `struct Pair`) whose
source type is not a union layout and whose `encodeValueToBytes` succeeds (or
when untyped), `.stripProvenance` and `.strictUcg630Ub` return the **exact
identical** `RvalueEvalResult` for **every** target type `targetTy`. -/
theorem evalByteCastWithPolicy_strip_eq_strict_of_nonUnion_no_prov_src
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (v : Value) (locals' : List LocalSlot)
    (hev : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals
      localDecls mem.callStack = .ok v locals')
    (hnp : valueHasProv v = false)
    (hsrc : ∀ srcTy, operandTy localDecls layouts op = .some srcTy →
      let rSrc := normalizeCodecTy (resolveTyWithLocalDecls localDecls layouts srcTy)
      isUnionLayout layouts rSrc = false ∧
        (∃ bs, encodeValueToBytes defaultCodecFuel layouts rSrc v = .some bs)) :
    evalByteCastWithPolicy .stripProvenance locals op targetTy mem localDecls layouts =
      evalByteCastWithPolicy .strictUcg630Ub locals op targetTy mem localDecls layouts := by
  unfold evalByteCastWithPolicy
  rw [hev]
  dsimp only
  cases tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts targetTy) with
  | none => rfl
  | some dstSize =>
    dsimp only
    cases hop : operandTy localDecls layouts op with
    | some srcTy =>
      dsimp only
      obtain ⟨hnonU, bs0, henc0⟩ := hsrc srcTy hop
      cases tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts srcTy) with
      | none => rfl
      | some srcSize =>
        dsimp only
        cases Nat.beq srcSize dstSize with
        | false => rfl
        | true =>
          dsimp only
          have hbs_eq : encodeByteCastSourceBytes layouts
              (resolveTyWithLocalDecls localDecls layouts srcTy) v = .some bs0 := by
            unfold encodeByteCastSourceBytes encodeTypedValueToBytes
            dsimp only
            rw [hnonU]; dsimp only
            rw [henc0]
          rw [hbs_eq]
          dsimp only
          cases Nat.beq (length bs0) dstSize with
          | false => rfl
          | true =>
            dsimp only
            rw [decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
              defaultCodecFuel layouts _ bs0
              (abstractBytesHaveProv_encodeValueToBytes_of_no_prov
                defaultCodecFuel layouts _ v bs0 hnp henc0)]
    | none =>
      dsimp only
      cases hbs : encodeUntypedValueToBytes defaultCodecFuel v with
      | none => rfl
      | some bs =>
        dsimp only
        cases Nat.beq (length bs) dstSize with
        | false => rfl
        | true =>
          dsimp only
          rw [decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
            defaultCodecFuel layouts _ bs
            (abstractBytesHaveProv_encodeUntypedValueToBytes_of_no_prov
              defaultCodecFuel v bs hnp hbs)]

/-! ### §15.3 TCB Finding 5, B2 Typed-Enum Critique & Complete `Ty`-Preserving / Niche-Capable Enum Decoding -/

/-- Non-null pointer field layout (the layout rustc emits for `&u8`, `NonNull<u8>`,
and `fn()`): `backendRepr = .scalar (.initialized (.pointer 0) ⟨1, 2^64-1⟩)`. -/
def protoNonNullPtrFieldLayout : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 8 }
  backendRepr := .scalar (.initialized (.pointer 0) ⟨1, scalarModulus 8 - 1⟩)
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

/-- `#[repr(transparent)] struct Wrap<'a>(&'a u8)` with `fieldLayouts := [1]`. -/
def protoWrapRefLayout : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 8 }
  backendRepr := .scalar (.initialized (.pointer 0) ⟨1, scalarModulus 8 - 1⟩)
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .single 0
  fieldLayouts := [1]
  isUninhabited := false
}

/-- `enum R<'a> { A(&'a u8), B(&'a u8) }`: `u64` tag at offset `0`, `&u8` field
at offset `8` (layout index `1` = `protoNonNullPtrFieldLayout`). -/
def protoRefPayloadEnumLayout : TypeLayout := {
  size := { bytes := 16 }
  align := { bytes := 8 }
  backendRepr := .memory
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .multiple (.initialized (.int 64 false) ⟨0, 1⟩) 0
    [.arbitrary [{ bytes := 8 }] [0], .arbitrary [{ bytes := 8 }] [0]]
  isUninhabited := false
}

/-- Niche-encoded `Option<&u8>`: `8`-byte pointer-valued tag at offset `0`
(`0` = `None`, nonzero pointer = `Some(&u8)`). -/
def protoNicheOptionRefLayout : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 8 }
  backendRepr := .scalar (.initialized (.pointer 0) ⟨0, scalarModulus 8 - 1⟩)
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .multiple (.initialized (.pointer 0) ⟨0, scalarModulus 8 - 1⟩) 0
    [.arbitrary [] [], .arbitrary [{ bytes := 0 }] [0]]
  isUninhabited := false
}

/-- `enum W<'a> { A(&'a [u8]), B(&'a [u8]) }`: `u64` tag at offset `0`, 16-byte
wide slice reference payload at offset `8` (`size := 24`). -/
def protoWideSliceEnumLayout : TypeLayout := {
  size := { bytes := 24 }
  align := { bytes := 8 }
  backendRepr := .memory
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .multiple (.initialized (.int 64 false) ⟨0, 1⟩) 0
    [.arbitrary [{ bytes := 8 }] [0], .arbitrary [{ bytes := 8 }] [0]]
  isUninhabited := false
}

/-- 16-byte wide slice reference layout (`&[u8]`): `scalarPair` of non-null
pointer and `usize` length. -/
def protoWideSliceRefLayout : TypeLayout := {
  size := { bytes := 16 }
  align := { bytes := 8 }
  backendRepr := .scalarPair
    (.initialized (.pointer 0) ⟨1, scalarModulus 8 - 1⟩)
    (.initialized (.int 64 false) ⟨0, scalarModulus 8 - 1⟩)
  fields := .arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1]
  variants := .single 0
  isUninhabited := false
}

/-- `#[repr(C)] struct Pair { a: u32, b: u32 }` (`size := 8`, `fieldLayouts := [7, 7]`). -/
def protoU32PairStructLayout : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 4 }
  backendRepr := .scalarPair
    (.initialized (.int 32 false) ⟨0, scalarModulus 4 - 1⟩)
    (.initialized (.int 32 false) ⟨0, scalarModulus 4 - 1⟩)
  fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }] [0, 1]
  variants := .single 0
  fieldLayouts := [7, 7]
  isUninhabited := false
}

def protoRichEnumLayouts : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries := [
    protoUnitLayout,            -- 0
    protoNonNullPtrFieldLayout, -- 1
    protoWrapRefLayout,         -- 2
    protoRefPayloadEnumLayout,  -- 3
    protoNicheOptionRefLayout,  -- 4
    protoWideSliceEnumLayout,   -- 5
    protoWideSliceRefLayout,    -- 6
    protoU32FieldLayout,        -- 7
    protoU32PairStructLayout    -- 8
  ]
}

def protoWrapRefTy : Ty := { kind := .adt "Wrap" [], layoutIdx := 2 }
def protoTupleRefTy : Ty := { kind := .tuple [.ref .not (.uint .u8)], layoutIdx := 2 }
def protoRefTy : Ty := { kind := .ref .not (.uint .u8), layoutIdx := 1 }
def protoWideSliceRefTy : Ty := { kind := .ref .not (.slice (.uint .u8)), layoutIdx := 6 }
def protoU32PairStructTy : Ty := { kind := .adt "Pair" [], layoutIdx := 8 }

def protoWrapRefDecls : List LocalDecl := [
  { mutability := .not, ty := { kind := .uint .usize, layoutIdx := 0 }, debugName := none }
]

def protoWrapRefLocals : List LocalSlot := [
  .init (.scalar ⟨0x1000, 8⟩)
]

/-- **Kernel-checked witness (`by rfl`) of TCB Finding 5 and two soundness /
completeness bugs in B2's `decodeMultiVariantEnumTypedWithPolicy`**:
1. **TCB Finding 5 (`RigidTy` erasure in `Places.lean:7976`)**: on provenance-free
   `usize = 0x1000`, `evalByteCast` rejects `transmute::<usize, (&u8,)>(0x1000)`
   with `.ub` (because `.tuple` retains `RigidTy.ref`), YET accepts
   `transmute::<usize, struct Wrap(&u8)>(0x1000)` with
   `.ok (.aggregate 0 [.scalar ⟨0x1000, 8⟩])` because `decodeFieldsByLayoutIdxs`
   erases the field type to `{ kind := .adt "" .nil, layoutIdx := fIdx }`,
   bypassing `no_forge_ref`!
2. **B2 Bug A (ref forgery leak)**: B2's `decodeMultiVariantEnumTypedWithPolicy`
   replicates this exact `RigidTy` erasure — on provenance-free `(1, 0x1000)` for
   `enum R { A(&u8), B(&u8) }` it returns `.some (.aggregate 1 [.scalar ⟨0x1000, 8⟩])`
   under **both** `.strictUcg630Ub` and `.stripProvenance`!
3. **B2 Bug C (niche pointer tag rejection)**: on niche-encoded `Option<&u8>`
   (`tagLayout = .initialized (.pointer 0) ⟨0, 2^64-1⟩`) with genuine
   `Option::Some(&x)` bytes carrying provenance `(7, 7)`, B2's
   `decodeMultiVariantEnumTypedWithPolicy` returns **`.none`** under **both**
   policies because it matches only `.some (.scalar tagSc)` and rejects
   `.some (.ptr p 8)`! -/
theorem trusted_struct_and_B2_enum_ref_forgery_and_niche_witness :
    -- 1. TCB Finding 5: tuple `(&u8,)` rejects `0x1000`, struct `Wrap(&u8)` accepts it!
    evalByteCast protoWrapRefLocals (.copy ⟨0, []⟩) protoTupleRefTy emptyMemory
        protoWrapRefDecls protoRichEnumLayouts = .ub ∧
    evalByteCast protoWrapRefLocals (.copy ⟨0, []⟩) protoWrapRefTy emptyMemory
        protoWrapRefDecls protoRichEnumLayouts =
      .ok (.aggregate 0 [.scalar ⟨0x1000, 8⟩]) protoWrapRefLocals emptyMemory ∧
    -- 2. B2 Bug A: `decodeMultiVariantEnumTypedWithPolicy` forges `R::B(&u8)` from plain ints
    decodeMultiVariantEnumTypedWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichEnumLayouts)
        protoRichEnumLayouts protoRefPayloadEnumLayout (.initialized (.int 64 false) ⟨0, 1⟩) 0
        [.arbitrary [{ bytes := 8 }] [0], .arbitrary [{ bytes := 8 }] [0]] [[1], [1]]
        (appendAbstractBytes (encodeLittleEndianBytes 1 8 .none)
          (encodeLittleEndianBytes 0x1000 8 .none)) =
      .some (.aggregate 1 [.scalar ⟨0x1000, 8⟩]) ∧
    decodeMultiVariantEnumTypedWithPolicy .stripProvenance
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoRichEnumLayouts)
        protoRichEnumLayouts protoRefPayloadEnumLayout (.initialized (.int 64 false) ⟨0, 1⟩) 0
        [.arbitrary [{ bytes := 8 }] [0], .arbitrary [{ bytes := 8 }] [0]] [[1], [1]]
        (appendAbstractBytes (encodeLittleEndianBytes 1 8 .none)
          (encodeLittleEndianBytes 0x1000 8 .none)) =
      .some (.aggregate 1 [.scalar ⟨0x1000, 8⟩]) ∧
    -- 3. B2 Bug C: `decodeMultiVariantEnumTypedWithPolicy` rejects genuine `Option::Some(&x)`
    decodeMultiVariantEnumTypedWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichEnumLayouts)
        protoRichEnumLayouts protoNicheOptionRefLayout
        (.initialized (.pointer 0) ⟨0, scalarModulus 8 - 1⟩) 0
        [.arbitrary [] [], .arbitrary [{ bytes := 0 }] [0]] [[], [1]]
        (encodeLittleEndianBytes 0x1000 8 (.some (7, 7))) = .none ∧
    decodeMultiVariantEnumTypedWithPolicy .stripProvenance
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoRichEnumLayouts)
        protoRichEnumLayouts protoNicheOptionRefLayout
        (.initialized (.pointer 0) ⟨0, scalarModulus 8 - 1⟩) 0
        [.arbitrary [] [], .arbitrary [{ bytes := 0 }] [0]] [[], [1]]
        (encodeLittleEndianBytes 0x1000 8 (.some (7, 7))) = .none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Specification of how a multi-variant enum's discriminant and typed fields are
decoded — distinguishing explicitly tagged enums (carrying full `Ty` per variant
field, NOT just `LayoutIdx`) from niche-encoded pointer enums (`Option<&T>`,
`Option<NonNull<T>>`, `Option<fn()>`). -/
inductive EnumDecodeSpec where
  | tagged (tagLayout : ScalarLayout) (tagField : Nat)
      (variantShapes : List FieldsShape) (variantFieldTys : List (List Ty))
  | nichePointer (nicheVariant dataVariant : Nat) (dataFieldTy : Ty)

/-- Primitive / pointer / float structural byte size extending
`Trusted.Bytes.rigidTyKindByteSize` with the four IEEE float kinds (`f16`, `f32`,
`f64`, `f128`) and float arrays (`[f32; n]`, `[f64; n]`). Returns `.none` for
`.adt` and non-empty `.tuple` so aggregate padding still comes from `LayoutTable`. -/
def protoRigidTyKindByteSize : RigidTy → Option Nat
  | .float .f16 => .some 2
  | .float .f32 => .some 4
  | .float .f64 => .some 8
  | .float .f128 => .some 16
  | .array elemKind n =>
    match protoRigidTyKindByteSize elemKind with
    | .some elemSz => .some (Nat.mul elemSz n)
    | .none => .none
  | k => rigidTyKindByteSize k

/-- Field byte-size lookup checking `protoRigidTyKindByteSize fTy.kind` **before**
`LayoutTable.lookup layouts fTy.layoutIdx`. Prevents placeholder `layoutIdx := 0`
on primitive MIR fields (`{ kind := .uint .u64, layoutIdx := 0 }`,
`{ kind := .float .f64, layoutIdx := 0 }`, etc.) from colliding with a 0-byte
ZST (`()`) at `LayoutTable` slot `0`, while still consulting `LayoutTable` first
for `.adt` and non-empty `.tuple` fields. -/
def protoFieldByteSize (layouts : LayoutTable) (fTy : Ty) : Option Nat :=
  match protoRigidTyKindByteSize fTy.kind with
  | .some sz => .some sz
  | .none =>
    match LayoutTable.lookup layouts fTy.layoutIdx with
    | .some fl => .some fl.size.bytes
    | .none => rigidTyByteSize layouts fTy

/-- Decode aggregate fields at `offsets` using each field's **full `Ty`**
(`RigidTy` + `LayoutIdx`), slicing each field via `protoFieldByteSize` (checking
primitive/float/pointer widths before `LayoutTable.lookup` so placeholder
`layoutIdx := 0` never collides with a ZST at slot `0`). Preserves `RigidTy.ref`,
`RigidTy.fnPtr`, and wide-pointer kinds (`&[T]`, `*const dyn Trait`) that
`decodeFieldsByLayoutIdxs` erases. -/
def decodeFieldsByTysWithPolicy
    (decodeChild : Ty → List AbstractByte → Option Value)
    (layouts : LayoutTable)
    (bytes : List AbstractByte) :
    List Size → List Ty → Option (List Value)
  | .nil, .nil => .some .nil
  | off :: offRest, fTy :: tyRest =>
    match protoFieldByteSize layouts fTy with
    | .none => .none
    | .some fSz =>
      match sliceAbstractBytes bytes off.bytes fSz with
      | .none => .none
      | .some fSlice =>
        match decodeChild fTy fSlice with
        | .none => .none
        | .some fv =>
          match decodeFieldsByTysWithPolicy decodeChild layouts bytes offRest tyRest with
          | .some restVals => .some (fv :: restVals)
          | .none => .none
  | _, _ => .none

/-- **Complete `Ty`-preserving and niche-capable policy-aware multi-variant enum
decoder**:
- On `.tagged`: decodes the integer discriminant via
  `decodeScalarLayoutBytesWithPolicy` and each payload field via
  `decodeFieldsByTysWithPolicy` with its **full `Ty`** (`RigidTy` + `LayoutIdx`),
  closing Findings 3, 4, and 5 (including `&T`, `fn()`, and wide `&[T]`/`&dyn`
  payloads!).
- On `.nichePointer`: handles Rust's `Option<&T>` / `Option<NonNull<T>>` /
  `Option<fn()>` niche layout:
  - null address (`0`) decodes to `nicheVariant` (`None`), gated by
    `policyRejectsProv` (so a zero-address pointer with provenance flips between
    `.none` under `.strictUcg630Ub` and `.some (.aggregate nicheVariant [])`
    under `.stripProvenance`, while provenance-free `0` is `None` under both);
  - nonzero bytes delegate directly to `decodeChild dataFieldTy bytes`,
    preserving `Value.ptr` provenance on genuine `Some(&x)` under both policies
    and rejecting provenance-free forged integers via `no_forge_ref` under both! -/
def decodeMultiVariantEnumRichWithPolicy
    (policy : Ptr2IntTransmutePolicy)
    (decodeChild : Ty → List AbstractByte → Option Value)
    (layouts : LayoutTable)
    (l : TypeLayout)
    (spec : EnumDecodeSpec)
    (bytes : List AbstractByte) :
    Option Value :=
  match Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => .none
  | false =>
    match spec with
    | .tagged tagLayout tagField variantShapes variantFieldTys =>
      match l.fields, scalarLayoutByteWidth tagLayout with
      | .arbitrary outerOffsets _, .some tagSz =>
        match get? outerOffsets tagField with
        | .none => .none
        | .some tagOff =>
          match sliceAbstractBytes bytes tagOff.bytes tagSz with
          | .none => .none
          | .some tagSlice =>
            match decodeScalarLayoutBytesWithPolicy policy tagLayout tagSlice with
            | .some (.scalar tagSc) =>
              match get? variantShapes tagSc.bits, get? variantFieldTys tagSc.bits with
              | .some (.arbitrary varOffsets _), .some fTys =>
                match decodeFieldsByTysWithPolicy decodeChild layouts bytes varOffsets fTys with
                | .some vals => .some (.aggregate tagSc.bits vals)
                | .none => .none
              | _, _ => .none
            | _ => .none
      | _, _ => .none
    | .nichePointer nicheVariant dataVariant dataFieldTy =>
      match decodeScalarBytes bytes false with
      | .none => .none
      | .some p =>
        match Nat.beq p.1.bits 0 with
        | true =>
          match policyRejectsProv policy bytes with
          | true => .none
          | false => .some (.aggregate nicheVariant .nil)
        | false =>
          match decodeChild dataFieldTy bytes with
          | .some dv => .some (.aggregate dataVariant (dv :: .nil))
          | .none => .none

private theorem decodeFieldsByTysWithPolicy_mono
    (c1 c2 : Ty → List AbstractByte → Option Value)
    (layouts : LayoutTable) (bytes : List AbstractByte)
    (offsets : List Size) (fTys : List Ty) (vals : List Value)
    (hc : ∀ ty bs v, c1 ty bs = .some v → c2 ty bs = .some v)
    (h : decodeFieldsByTysWithPolicy c1 layouts bytes offsets fTys = .some vals) :
    decodeFieldsByTysWithPolicy c2 layouts bytes offsets fTys = .some vals := by
  induction offsets generalizing fTys vals with
  | nil =>
    cases fTys with
    | nil => exact h
    | cons _ _ => cases h
  | cons off offRest ih =>
    cases fTys with
    | nil => cases h
    | cons fTy tyRest =>
      unfold decodeFieldsByTysWithPolicy at h ⊢
      cases hsz : protoFieldByteSize layouts fTy with
      | none => rw [hsz] at h; cases h
      | some fSz =>
        rw [hsz] at h; dsimp only at h ⊢
        cases hsl : sliceAbstractBytes bytes off.bytes fSz with
        | none => rw [hsl] at h; cases h
        | some fSlice =>
          rw [hsl] at h; dsimp only at h ⊢
          cases hd : c1 fTy fSlice with
          | none => rw [hd] at h; cases h
          | some fv =>
            rw [hd] at h; dsimp only at h ⊢
            rw [hc fTy fSlice fv hd]
            cases hr : decodeFieldsByTysWithPolicy c1 layouts bytes offRest tyRest with
            | none => rw [hr] at h; cases h
            | some restVals =>
              rw [hr] at h
              rw [ih tyRest restVals hr]
              exact h

private theorem decodeFieldsByTysWithPolicy_eq_of_no_prov
    (c1 c2 : Ty → List AbstractByte → Option Value)
    (layouts : LayoutTable) (bytes : List AbstractByte)
    (offsets : List Size) (fTys : List Ty)
    (hnp : abstractBytesHaveProv bytes = false)
    (hc : ∀ ty bs, abstractBytesHaveProv bs = false → c1 ty bs = c2 ty bs) :
    decodeFieldsByTysWithPolicy c1 layouts bytes offsets fTys =
      decodeFieldsByTysWithPolicy c2 layouts bytes offsets fTys := by
  induction offsets generalizing fTys with
  | nil =>
    cases fTys <;> rfl
  | cons off offRest ih =>
    cases fTys with
    | nil => rfl
    | cons fTy tyRest =>
      unfold decodeFieldsByTysWithPolicy
      cases hsz : protoFieldByteSize layouts fTy with
      | none => rfl
      | some fSz =>
        dsimp only
        cases hsl : sliceAbstractBytes bytes off.bytes fSz with
        | none => rfl
        | some fSlice =>
          dsimp only
          rw [hc fTy fSlice (abstractBytesHaveProv_slice bytes fSlice off.bytes fSz hnp hsl)]
          cases c2 fTy fSlice with
          | none => rfl
          | some _ => rw [ih tyRest]

/-- Policy monotonicity of `decodeMultiVariantEnumRichWithPolicy`: every
`.strictUcg630Ub` success is the identical `.stripProvenance` success (covering
both explicitly tagged and niche-pointer enums). -/
theorem decodeMultiVariantEnumRichWithPolicy_strict_refines_strip
    (childStrict childStrip : Ty → List AbstractByte → Option Value)
    (layouts : LayoutTable) (l : TypeLayout) (spec : EnumDecodeSpec)
    (bytes : List AbstractByte) (v : Value)
    (hchild : ∀ ty bs cv, childStrict ty bs = .some cv → childStrip ty bs = .some cv)
    (h : decodeMultiVariantEnumRichWithPolicy .strictUcg630Ub childStrict layouts l spec bytes =
      .some v) :
    decodeMultiVariantEnumRichWithPolicy .stripProvenance childStrip layouts l spec bytes =
      .some v := by
  unfold decodeMultiVariantEnumRichWithPolicy at h ⊢
  cases hu : Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => rw [hu] at h; cases h
  | false =>
    rw [hu] at h; dsimp only at h ⊢
    cases spec with
    | tagged tagLayout tagField variantShapes variantFieldTys =>
      dsimp only at h ⊢
      cases hf : l.fields with
      | arbitrary outerOffsets _ =>
        rw [hf] at h
        cases htw : scalarLayoutByteWidth tagLayout with
        | none => rw [htw] at h; cases h
        | some tagSz =>
          rw [htw] at h; dsimp only at h ⊢
          cases hg : get? outerOffsets tagField with
          | none => rw [hg] at h; cases h
          | some tagOff =>
            rw [hg] at h; dsimp only at h ⊢
            cases hsl : sliceAbstractBytes bytes tagOff.bytes tagSz with
            | none => rw [hsl] at h; cases h
            | some tagSlice =>
              rw [hsl] at h; dsimp only at h ⊢
              cases htd : decodeScalarLayoutBytesWithPolicy .strictUcg630Ub tagLayout tagSlice with
              | none => rw [htd] at h; cases h
              | some tv =>
                rw [htd] at h
                rw [decodeScalarLayoutBytesWithPolicy_strict_refines_strip tagLayout tagSlice tv htd]
                cases tv with
                | scalar tagSc =>
                  dsimp only at h ⊢
                  cases hvs : get? variantShapes tagSc.bits with
                  | none => rw [hvs] at h; cases h
                  | some vs =>
                    rw [hvs] at h
                    cases vs with
                    | arbitrary varOffsets _ =>
                      cases hft : get? variantFieldTys tagSc.bits with
                      | none => rw [hft] at h; cases h
                      | some fTys =>
                        rw [hft] at h; dsimp only at h ⊢
                        cases hdf : decodeFieldsByTysWithPolicy childStrict layouts bytes
                            varOffsets fTys with
                        | none => rw [hdf] at h; cases h
                        | some vals =>
                          rw [hdf] at h
                          rw [decodeFieldsByTysWithPolicy_mono childStrict childStrip layouts bytes
                            varOffsets fTys vals hchild hdf]
                          exact h
                    | primitive | union _ | array _ _ => cases h
                | unit | ptr _ _ | aggregate _ _ => cases h
      | primitive | union _ | array _ _ => rw [hf] at h; cases h
    | nichePointer nicheVariant dataVariant dataFieldTy =>
      dsimp only at h ⊢
      cases hsc : decodeScalarBytes bytes false with
      | none => rw [hsc] at h; cases h
      | some p =>
        rw [hsc] at h; dsimp only at h ⊢
        cases hz : Nat.beq p.1.bits 0 with
        | true =>
          rw [hz] at h; dsimp only [policyRejectsProv] at h ⊢
          cases hp : abstractBytesHaveProv bytes with
          | true => rw [hp] at h; cases h
          | false => rw [hp] at h; exact h
        | false =>
          rw [hz] at h; dsimp only at h ⊢
          cases hd : childStrict dataFieldTy bytes with
          | none => rw [hd] at h; cases h
          | some dv =>
            rw [hd] at h
            rw [hchild dataFieldTy bytes dv hd]
            exact h

/-- Provenance-free equivalence of `decodeMultiVariantEnumRichWithPolicy`: when
`abstractBytesHaveProv bytes = false`, `.stripProvenance` and `.strictUcg630Ub`
return the identical `Option Value` on both tagged and niche-pointer enums. -/
theorem decodeMultiVariantEnumRichWithPolicy_strip_eq_strict_of_no_prov
    (childStrip childStrict : Ty → List AbstractByte → Option Value)
    (layouts : LayoutTable) (l : TypeLayout) (spec : EnumDecodeSpec)
    (bytes : List AbstractByte)
    (hnp : abstractBytesHaveProv bytes = false)
    (hchild : ∀ ty bs, abstractBytesHaveProv bs = false → childStrip ty bs = childStrict ty bs) :
    decodeMultiVariantEnumRichWithPolicy .stripProvenance childStrip layouts l spec bytes =
      decodeMultiVariantEnumRichWithPolicy .strictUcg630Ub childStrict layouts l spec bytes := by
  unfold decodeMultiVariantEnumRichWithPolicy
  cases Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => rfl
  | false =>
    dsimp only
    cases spec with
    | tagged tagLayout tagField variantShapes variantFieldTys =>
      dsimp only
      cases l.fields with
      | arbitrary outerOffsets _ =>
        cases scalarLayoutByteWidth tagLayout with
        | none => rfl
        | some tagSz =>
          dsimp only
          cases get? outerOffsets tagField with
          | none => rfl
          | some tagOff =>
            dsimp only
            cases hsl : sliceAbstractBytes bytes tagOff.bytes tagSz with
            | none => rfl
            | some tagSlice =>
              dsimp only
              rw [decodeScalarLayoutBytesWithPolicy_strip_eq_strict_of_no_prov tagLayout tagSlice
                (abstractBytesHaveProv_slice bytes tagSlice tagOff.bytes tagSz hnp hsl)]
              cases decodeScalarLayoutBytesWithPolicy .strictUcg630Ub tagLayout tagSlice with
              | none => rfl
              | some tv =>
                cases tv with
                | scalar tagSc =>
                  dsimp only
                  cases get? variantShapes tagSc.bits with
                  | none => rfl
                  | some vs =>
                    cases vs with
                    | arbitrary varOffsets _ =>
                      cases get? variantFieldTys tagSc.bits with
                      | none => rfl
                      | some fTys =>
                        dsimp only
                        rw [decodeFieldsByTysWithPolicy_eq_of_no_prov childStrip childStrict
                          layouts bytes varOffsets fTys hnp hchild]
                    | primitive | union _ | array _ _ => rfl
                | unit | ptr _ _ | aggregate _ _ => rfl
      | primitive | union _ | array _ _ => rfl
    | nichePointer nicheVariant dataVariant dataFieldTy =>
      dsimp only
      cases decodeScalarBytes bytes false with
      | none => rfl
      | some p =>
        dsimp only
        cases Nat.beq p.1.bits 0 with
        | true => dsimp only [policyRejectsProv]; rw [hnp]
        | false => dsimp only; rw [hchild dataFieldTy bytes hnp]

/-- **No-forgery theorem for niche-encoded `Option<&T>`**: under **both**
policies, provenance-free bytes NEVER decode to `Option::Some(&T)` (they either
decode to `None` when zero, or fail with `.none` when nonzero — never forging a
reference!). -/
theorem decodeMultiVariantEnumRichWithPolicy_niche_ref_no_forge
    (policy : Ptr2IntTransmutePolicy) (fuel : Nat) (layouts : LayoutTable)
    (l : TypeLayout) (nicheVariant dataVariant : Nat)
    (m : Mutability) (pointee : RigidTy) (layoutIdx : LayoutIdx)
    (bytes : List AbstractByte) (dv : Value)
    (hnp : abstractBytesHaveProv bytes = false)
    (hne : dataVariant ≠ nicheVariant) :
    decodeMultiVariantEnumRichWithPolicy policy
        (decodeTypedValueFromBytesWithPolicy policy (.succ fuel) layouts)
        layouts l (.nichePointer nicheVariant dataVariant
          { kind := .ref m pointee, layoutIdx := layoutIdx }) bytes ≠
      .some (.aggregate dataVariant (dv :: .nil)) := by
  intro h
  unfold decodeMultiVariantEnumRichWithPolicy at h
  cases hu : Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => rw [hu] at h; cases h
  | false =>
    rw [hu] at h; dsimp only at h
    cases hsc : decodeScalarBytes bytes false with
    | none => rw [hsc] at h; cases h
    | some p =>
      rw [hsc] at h; dsimp only at h
      cases hz : Nat.beq p.1.bits 0 with
      | true =>
        rw [hz] at h; dsimp only at h
        cases hp : policyRejectsProv policy bytes with
        | true => rw [hp] at h; cases h
        | false =>
          rw [hp] at h
          injection h with hval
          injection hval with hv _
          exact hne hv.symm
      | false =>
        rw [hz] at h; dsimp only at h
        rw [decodeTypedValueFromBytesWithPolicy_no_forge_ref policy fuel layouts m pointee
          layoutIdx bytes hnp] at h
        cases h

/-- **Kernel-checked witnesses (`by rfl`) of `decodeMultiVariantEnumRichWithPolicy`**
across tagged reference enums (`enum R { A(&u8), B(&u8) }`), tagged wide-slice
enums (`enum W { A(&[u8]), B(&[u8]) }`), and niche-encoded `Option<&u8>`:
1. `enum R` rejects provenance-free `(1, 0x1000)` under BOTH policies (closing
   B2 Bug A) and preserves genuine `R::B(&x)` (`Value.ptr`) under BOTH policies;
2. `enum W` preserves genuine `W::B(&[u8])` (`[ptr, scalar len]`) under BOTH
   policies, rejects a provenance-free data pointer under BOTH policies, and
   flips provenance-carrying length metadata (`strict = .none` vs `strip = .some`);
3. `Option<&u8>` decodes `None` (`0`, no prov) under BOTH policies, decodes
   genuine `Some(&x)` (`Value.ptr`) under BOTH policies (closing B2 Bug C),
   rejects forged `0x1000` (no prov) under BOTH policies, and flips a
   zero-address provenance-carrying pointer `ptr(alloc 7, 0)` across policies! -/
theorem multiVariant_enum_rich_fix_witnesses :
    -- 1a. `enum R`: provenance-free `(1, 0x1000)` rejected under BOTH policies
    decodeMultiVariantEnumRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichEnumLayouts)
        protoRichEnumLayouts protoRefPayloadEnumLayout
        (.tagged (.initialized (.int 64 false) ⟨0, 1⟩) 0
          [.arbitrary [{ bytes := 8 }] [0], .arbitrary [{ bytes := 8 }] [0]]
          [[protoRefTy], [protoRefTy]])
        (appendAbstractBytes (encodeLittleEndianBytes 1 8 .none)
          (encodeLittleEndianBytes 0x1000 8 .none)) = .none ∧
    decodeMultiVariantEnumRichWithPolicy .stripProvenance
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoRichEnumLayouts)
        protoRichEnumLayouts protoRefPayloadEnumLayout
        (.tagged (.initialized (.int 64 false) ⟨0, 1⟩) 0
          [.arbitrary [{ bytes := 8 }] [0], .arbitrary [{ bytes := 8 }] [0]]
          [[protoRefTy], [protoRefTy]])
        (appendAbstractBytes (encodeLittleEndianBytes 1 8 .none)
          (encodeLittleEndianBytes 0x1000 8 .none)) = .none ∧
    -- 1b. `enum R`: genuine `R::B(&x)` preserves `Value.ptr` under BOTH policies
    decodeMultiVariantEnumRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichEnumLayouts)
        protoRichEnumLayouts protoRefPayloadEnumLayout
        (.tagged (.initialized (.int 64 false) ⟨0, 1⟩) 0
          [.arbitrary [{ bytes := 8 }] [0], .arbitrary [{ bytes := 8 }] [0]]
          [[protoRefTy], [protoRefTy]])
        (appendAbstractBytes (encodeLittleEndianBytes 1 8 .none)
          (encodeLittleEndianBytes 0x1000 8 (.some (7, 7)))) =
      .some (.aggregate 1 [.ptr { allocId := 7, offsetBytes := 0x1000 } 8]) ∧
    -- 2a. `enum W`: genuine `W::B(&[u8])` preserves data ptr + len under BOTH policies
    decodeMultiVariantEnumRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichEnumLayouts)
        protoRichEnumLayouts protoWideSliceEnumLayout
        (.tagged (.initialized (.int 64 false) ⟨0, 1⟩) 0
          [.arbitrary [{ bytes := 8 }] [0], .arbitrary [{ bytes := 8 }] [0]]
          [[protoWideSliceRefTy], [protoWideSliceRefTy]])
        (appendAbstractBytes (encodeLittleEndianBytes 1 8 .none)
          (appendAbstractBytes (encodeLittleEndianBytes 0x1000 8 (.some (7, 7)))
            (encodeLittleEndianBytes 16 8 .none))) =
      .some (.aggregate 1 [.aggregate 0 [.ptr { allocId := 7, offsetBytes := 0x1000 } 8,
        .scalar ⟨16, 8⟩]]) ∧
    -- 2b. `enum W`: provenance in slice length metadata flips strict `.none` vs strip `.some`
    decodeMultiVariantEnumRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichEnumLayouts)
        protoRichEnumLayouts protoWideSliceEnumLayout
        (.tagged (.initialized (.int 64 false) ⟨0, 1⟩) 0
          [.arbitrary [{ bytes := 8 }] [0], .arbitrary [{ bytes := 8 }] [0]]
          [[protoWideSliceRefTy], [protoWideSliceRefTy]])
        (appendAbstractBytes (encodeLittleEndianBytes 1 8 .none)
          (appendAbstractBytes (encodeLittleEndianBytes 0x1000 8 (.some (7, 7)))
            (encodeLittleEndianBytes 16 8 (.some (9, 9))))) = .none ∧
    decodeMultiVariantEnumRichWithPolicy .stripProvenance
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoRichEnumLayouts)
        protoRichEnumLayouts protoWideSliceEnumLayout
        (.tagged (.initialized (.int 64 false) ⟨0, 1⟩) 0
          [.arbitrary [{ bytes := 8 }] [0], .arbitrary [{ bytes := 8 }] [0]]
          [[protoWideSliceRefTy], [protoWideSliceRefTy]])
        (appendAbstractBytes (encodeLittleEndianBytes 1 8 .none)
          (appendAbstractBytes (encodeLittleEndianBytes 0x1000 8 (.some (7, 7)))
            (encodeLittleEndianBytes 16 8 (.some (9, 9))))) =
      .some (.aggregate 1 [.aggregate 0 [.ptr { allocId := 7, offsetBytes := 0x1000 } 8,
        .scalar ⟨16, 8⟩]]) ∧
    -- 3a. `Option<&u8>`: genuine `None` (`0`, no prov) under BOTH policies
    decodeMultiVariantEnumRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichEnumLayouts)
        protoRichEnumLayouts protoNicheOptionRefLayout
        (.nichePointer 0 1 protoRefTy)
        (encodeLittleEndianBytes 0 8 .none) = .some (.aggregate 0 []) ∧
    -- 3b. `Option<&u8>`: genuine `Some(&x)` preserves `Value.ptr` under BOTH policies
    decodeMultiVariantEnumRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichEnumLayouts)
        protoRichEnumLayouts protoNicheOptionRefLayout
        (.nichePointer 0 1 protoRefTy)
        (encodeLittleEndianBytes 0x1000 8 (.some (7, 7))) =
      .some (.aggregate 1 [.ptr { allocId := 7, offsetBytes := 0x1000 } 8]) ∧
    decodeMultiVariantEnumRichWithPolicy .stripProvenance
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoRichEnumLayouts)
        protoRichEnumLayouts protoNicheOptionRefLayout
        (.nichePointer 0 1 protoRefTy)
        (encodeLittleEndianBytes 0x1000 8 (.some (7, 7))) =
      .some (.aggregate 1 [.ptr { allocId := 7, offsetBytes := 0x1000 } 8]) ∧
    -- 3c. `Option<&u8>`: forged integer `0x1000` (no prov) rejected under BOTH policies
    decodeMultiVariantEnumRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichEnumLayouts)
        protoRichEnumLayouts protoNicheOptionRefLayout
        (.nichePointer 0 1 protoRefTy)
        (encodeLittleEndianBytes 0x1000 8 .none) = .none ∧
    decodeMultiVariantEnumRichWithPolicy .stripProvenance
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoRichEnumLayouts)
        protoRichEnumLayouts protoNicheOptionRefLayout
        (.nichePointer 0 1 protoRefTy)
        (encodeLittleEndianBytes 0x1000 8 .none) = .none ∧
    -- 3d. `Option<&u8>`: zero-address provenance pointer flips strict `.none` vs strip `None`
    decodeMultiVariantEnumRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichEnumLayouts)
        protoRichEnumLayouts protoNicheOptionRefLayout
        (.nichePointer 0 1 protoRefTy)
        (encodeLittleEndianBytes 0 8 (.some (7, 7))) = .none ∧
    decodeMultiVariantEnumRichWithPolicy .stripProvenance
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoRichEnumLayouts)
        protoRichEnumLayouts protoNicheOptionRefLayout
        (.nichePointer 0 1 protoRefTy)
        (encodeLittleEndianBytes 0 8 (.some (7, 7))) = .some (.aggregate 0 []) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §16. Provenance-Aware Niche Decoding: Offset-Zero References Are Not Null -/

/-- Byte image of a fresh reference `&x`. In the trusted model `Rvalue.ref`
evaluates to `Value.ptr { allocId := tag, offsetBytes := 0 } 8`: a pointer
stores its *offset within the allocation* next to its provenance, so the image
of the most common reference is eight zero bytes **carrying provenance**. -/
def protoOffsetZeroRefBytes : List AbstractByte :=
  encodeLittleEndianBytes 0 8 (.some (7, 7))

/-- Provenance-aware niche-pointer enum decoder (`Option<&T>`,
`Option<NonNull<T>>`, `Option<fn()>`): an image is the null niche **only when
it is provenance-free and zero**; any image carrying provenance denotes the
dataful variant and is decoded by the policy-aware typed payload decoder
`decodeChild` (which preserves intact provenance and never forges it). The
niche test itself never consults the policy: reading `None` out of
provenance-free zero bytes is not a pointer-to-integer reinterpretation. -/
def decodeNichePointerEnumProvAware
    (decodeChild : Ty → List AbstractByte → Option Value)
    (l : TypeLayout)
    (nicheVariant dataVariant : Nat)
    (dataFieldTy : Ty)
    (bytes : List AbstractByte) :
    Option Value :=
  match Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => .none
  | false =>
    match abstractBytesHaveProv bytes with
    | true =>
      match decodeChild dataFieldTy bytes with
      | .some dv => .some (.aggregate dataVariant (dv :: .nil))
      | .none => .none
    | false =>
      match decodeScalarBytes bytes false with
      | .none => .none
      | .some p =>
        match Nat.beq p.1.bits 0 with
        | true => .some (.aggregate nicheVariant .nil)
        | false =>
          match decodeChild dataFieldTy bytes with
          | .some dv => .some (.aggregate dataVariant (dv :: .nil))
          | .none => .none

/-- **Kernel-checked bug in the `.nichePointer` arm of
`decodeMultiVariantEnumRichWithPolicy` and its repair (`by rfl`)**: that arm
tests `bits = 0` on the raw address bits, but a pointer with provenance is never
null in this model. On the image of the genuine value `Some(&x)` with a fresh
(offset-zero) reference it therefore returns `None` under `.stripProvenance`
(silently replacing `Some(&x)` by `None`) and rejects under `.strictUcg630Ub`,
whereas `decodeNichePointerEnumProvAware` returns `Some(ptr)` with intact
provenance under both policies, still decodes provenance-free zero bytes to
`None`, still refuses to forge a reference from a provenance-free nonzero
integer, and agrees with the rich decoder on a nonzero-offset reference. -/
theorem niche_offset_zero_ref_misclassified_and_provAware_fix_witness :
    decodeMultiVariantEnumRichWithPolicy .stripProvenance
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoRichEnumLayouts)
        protoRichEnumLayouts protoNicheOptionRefLayout (.nichePointer 0 1 protoRefTy)
        protoOffsetZeroRefBytes = .some (.aggregate 0 []) ∧
    decodeMultiVariantEnumRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichEnumLayouts)
        protoRichEnumLayouts protoNicheOptionRefLayout (.nichePointer 0 1 protoRefTy)
        protoOffsetZeroRefBytes = .none ∧
    decodeNichePointerEnumProvAware
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoRichEnumLayouts)
        protoNicheOptionRefLayout 0 1 protoRefTy protoOffsetZeroRefBytes =
      .some (.aggregate 1 [.ptr { allocId := 7, offsetBytes := 0 } 8]) ∧
    decodeNichePointerEnumProvAware
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichEnumLayouts)
        protoNicheOptionRefLayout 0 1 protoRefTy protoOffsetZeroRefBytes =
      .some (.aggregate 1 [.ptr { allocId := 7, offsetBytes := 0 } 8]) ∧
    decodeNichePointerEnumProvAware
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichEnumLayouts)
        protoNicheOptionRefLayout 0 1 protoRefTy (encodeLittleEndianBytes 0 8 .none) =
      .some (.aggregate 0 []) ∧
    decodeNichePointerEnumProvAware
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoRichEnumLayouts)
        protoNicheOptionRefLayout 0 1 protoRefTy (encodeLittleEndianBytes 0x1000 8 .none) =
      .none ∧
    decodeNichePointerEnumProvAware
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichEnumLayouts)
        protoNicheOptionRefLayout 0 1 protoRefTy
        (encodeLittleEndianBytes 0x1000 8 (.some (7, 7))) =
      decodeMultiVariantEnumRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichEnumLayouts)
        protoRichEnumLayouts protoNicheOptionRefLayout (.nichePointer 0 1 protoRefTy)
        (encodeLittleEndianBytes 0x1000 8 (.some (7, 7))) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A pointer image with provenance is never the null niche: the
provenance-aware decoder can only return the dataful variant on it. -/
theorem decodeNichePointerEnumProvAware_prov_imp_dataful
    (decodeChild : Ty → List AbstractByte → Option Value) (l : TypeLayout)
    (nicheVariant dataVariant : Nat) (dataFieldTy : Ty) (bytes : List AbstractByte) (v : Value)
    (hprov : abstractBytesHaveProv bytes = true)
    (h : decodeNichePointerEnumProvAware decodeChild l nicheVariant dataVariant dataFieldTy
      bytes = .some v) :
    ∃ dv, decodeChild dataFieldTy bytes = .some dv ∧ v = .aggregate dataVariant (dv :: .nil) := by
  unfold decodeNichePointerEnumProvAware at h
  cases hu : Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => rw [hu] at h; cases h
  | false =>
    rw [hu] at h
    dsimp only at h
    rw [hprov] at h
    dsimp only at h
    cases hc : decodeChild dataFieldTy bytes with
    | none => rw [hc] at h; cases h
    | some dv =>
      rw [hc] at h
      injection h with hv
      exact ⟨dv, rfl, hv.symm⟩

/-- Policy refinement of the provenance-aware niche decoder: it inherits
refinement from the payload decoders (and is policy-independent whenever they
are, e.g. on pointer payload types). -/
theorem decodeNichePointerEnumProvAware_mono
    (childStrict childStrip : Ty → List AbstractByte → Option Value) (l : TypeLayout)
    (nicheVariant dataVariant : Nat) (dataFieldTy : Ty) (bytes : List AbstractByte) (v : Value)
    (hchild : ∀ bs cv, childStrict dataFieldTy bs = .some cv → childStrip dataFieldTy bs = .some cv)
    (h : decodeNichePointerEnumProvAware childStrict l nicheVariant dataVariant dataFieldTy
      bytes = .some v) :
    decodeNichePointerEnumProvAware childStrip l nicheVariant dataVariant dataFieldTy bytes =
      .some v := by
  unfold decodeNichePointerEnumProvAware at h ⊢
  cases hu : Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => rw [hu] at h; cases h
  | false =>
    rw [hu] at h
    dsimp only at h ⊢
    cases hc : childStrict dataFieldTy bytes with
    | none =>
      rw [hc] at h
      cases hp : abstractBytesHaveProv bytes with
      | true => rw [hp] at h; cases h
      | false =>
        rw [hp] at h
        dsimp only at h ⊢
        cases hsc : decodeScalarBytes bytes false with
        | none => rw [hsc] at h; cases h
        | some p =>
          rw [hsc] at h
          dsimp only at h ⊢
          cases hz : Nat.beq p.1.bits 0 with
          | true => rw [hz] at h; exact h
          | false => rw [hz] at h; cases h
    | some cv =>
      rw [hc] at h
      rw [hchild bytes cv hc]
      exact h

/-- No forgery through the niche: provenance-free bytes never decode to the
dataful variant of a reference-payload niche enum (under either policy). -/
theorem decodeNichePointerEnumProvAware_ref_no_forge
    (policy : Ptr2IntTransmutePolicy) (fuel : Nat) (layouts : LayoutTable) (l : TypeLayout)
    (nicheVariant dataVariant : Nat) (m : Mutability) (pointee : RigidTy)
    (layoutIdx : LayoutIdx) (bytes : List AbstractByte) (dv : Value)
    (hnp : abstractBytesHaveProv bytes = false) (hne : dataVariant ≠ nicheVariant) :
    decodeNichePointerEnumProvAware
        (decodeTypedValueFromBytesWithPolicy policy (.succ fuel) layouts) l nicheVariant
        dataVariant { kind := .ref m pointee, layoutIdx := layoutIdx } bytes ≠
      .some (.aggregate dataVariant (dv :: .nil)) := by
  intro h
  unfold decodeNichePointerEnumProvAware at h
  cases hu : Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => rw [hu] at h; cases h
  | false =>
    rw [hu] at h
    dsimp only at h
    rw [hnp, decodeTypedValueFromBytesWithPolicy_no_forge_ref policy fuel layouts m pointee
      layoutIdx bytes hnp] at h
    dsimp only at h
    cases hsc : decodeScalarBytes bytes false with
    | none => rw [hsc] at h; cases h
    | some p =>
      rw [hsc] at h
      dsimp only at h
      cases hz : Nat.beq p.1.bits 0 with
      | true =>
        rw [hz] at h
        injection h with hv
        injection hv with hidx _
        exact hne hidx.symm
      | false => rw [hz] at h; cases h

/-- Away from the bug the two niche decoders coincide: on provenance-free
images the provenance-aware decoder equals the `.nichePointer` arm of
`decodeMultiVariantEnumRichWithPolicy` under both policies. -/
theorem decodeNichePointerEnumProvAware_eq_rich_of_no_prov
    (policy : Ptr2IntTransmutePolicy) (decodeChild : Ty → List AbstractByte → Option Value)
    (layouts : LayoutTable) (l : TypeLayout) (nicheVariant dataVariant : Nat)
    (dataFieldTy : Ty) (bytes : List AbstractByte)
    (hnp : abstractBytesHaveProv bytes = false) :
    decodeNichePointerEnumProvAware decodeChild l nicheVariant dataVariant dataFieldTy bytes =
      decodeMultiVariantEnumRichWithPolicy policy decodeChild layouts l
        (.nichePointer nicheVariant dataVariant dataFieldTy) bytes := by
  unfold decodeNichePointerEnumProvAware decodeMultiVariantEnumRichWithPolicy
  cases Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => rfl
  | false =>
    dsimp only
    rw [hnp]
    dsimp only
    cases decodeScalarBytes bytes false with
    | none => rfl
    | some p =>
      dsimp only
      cases Nat.beq p.1.bits 0 with
      | true => cases policy <;> dsimp only [policyRejectsProv] <;> (try rw [hnp])
      | false => rfl

/-! ### §16.1 Offset-Sliced Multi-Field Niche Enums & Fuel-Indexed Rich ADT Integration -/

/-- Unified rich ADT layout metadata closing TCB Findings 3, 4, and 5 as well as
both niche-enum bugs in `EnumDecodeSpec.nichePointer`:
- `.structFields`: single-variant struct/ADT carrying full `fieldTys : List Ty`
  (closing Finding 5's `RigidTy` erasure on `struct Wrap(&u8)`);
- `.taggedEnum`: explicitly tagged multi-variant enum carrying full
  `List (List Ty)` per variant (closing Findings 3 & 4);
- `.nichePointerEnum`: offset-sliced, multi-field, uniform-provenance-aware
  niche pointer enum (`Option<&T>`, `Option<&[T]>`, `Option<(&T, u64)>`,
  `Result<(&T, u64), ()>`), slicing **only** `[nicheOffset .. nicheOffset + nicheBytes)`
  so inactive `.uninit` or leftover nonzero metadata/payload bytes in `None` are
  never read, and treating intact pointer provenance (`abstractBytesUniformProv`,
  including `offsetBytes = 0` for fresh `&x` / `&STATIC`) as non-null! -/
inductive RichAdtSpec where
  | structFields (variantIdx : Nat) (offsets : List Size) (fieldTys : List Ty)
  | taggedEnum
      (tagLayout : ScalarLayout)
      (tagField : Nat)
      (variantShapes : List FieldsShape)
      (variantFieldTys : List (List Ty))
  | nichePointerEnum
      (nicheOffset : Size)
      (nicheBytes : Nat)
      (nicheVariant dataVariant : Nat)
      (dataOffsets : List Size)
      (dataFieldTys : List Ty)
  | nicheScalarEnum
      (nicheOffset : Size)
      (nicheBytes : Nat)
      (nicheValue : Nat)
      (nicheVariant dataVariant : Nat)
      (dataOffsets : List Size)
      (dataFieldTys : List Ty)

/-- Projection-disciplined lookup (`entry.1` / `entry.2`, avoiding `Prod.casesOn`)
in an auxiliary `LayoutIdx ↦ RichAdtSpec` side table. -/
def lookupRichAdtSpec : List (LayoutIdx × RichAdtSpec) → LayoutIdx → Option RichAdtSpec
  | .nil, _ => .none
  | entry :: rest, idx =>
    match Nat.beq entry.1 idx with
    | true => .some entry.2
    | false => lookupRichAdtSpec rest idx

/-- Decode a single-variant struct, tagged enum, or offset-sliced multi-field
niche-pointer enum using `RichAdtSpec` and `Ptr2IntTransmutePolicy`. -/
def decodeAdtRichWithPolicy
    (policy : Ptr2IntTransmutePolicy)
    (decodeChild : Ty → List AbstractByte → Option Value)
    (layouts : LayoutTable)
    (l : TypeLayout)
    (spec : RichAdtSpec)
    (bytes : List AbstractByte) :
    Option Value :=
  match Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => .none
  | false =>
    match spec with
    | .structFields variantIdx offsets fieldTys =>
      match decodeFieldsByTysWithPolicy decodeChild layouts bytes offsets fieldTys with
      | .some vals => .some (.aggregate variantIdx vals)
      | .none => .none
    | .taggedEnum tagLayout tagField variantShapes variantFieldTys =>
      decodeMultiVariantEnumRichWithPolicy policy decodeChild layouts l
        (.tagged tagLayout tagField variantShapes variantFieldTys) bytes
    | .nichePointerEnum nicheOffset nicheBytes nicheVariant dataVariant dataOffsets dataFieldTys =>
      match sliceAbstractBytes bytes nicheOffset.bytes nicheBytes with
      | .none => .none
      | .some nicheSlice =>
        match decodeScalarBytes nicheSlice false with
        | .none => .none
        | .some p =>
          match abstractBytesUniformProv nicheSlice with
          | true =>
            match decodeFieldsByTysWithPolicy decodeChild layouts bytes dataOffsets dataFieldTys with
            | .some vals => .some (.aggregate dataVariant vals)
            | .none => .none
          | false =>
            match Nat.beq p.1.bits 0 with
            | true =>
              match policyRejectsProv policy nicheSlice with
              | true => .none
              | false => .some (.aggregate nicheVariant .nil)
            | false =>
              match decodeFieldsByTysWithPolicy decodeChild layouts bytes dataOffsets dataFieldTys with
              | .some vals => .some (.aggregate dataVariant vals)
              | .none => .none
    | .nicheScalarEnum nicheOffset nicheBytes nicheValue nicheVariant dataVariant dataOffsets dataFieldTys =>
      match sliceAbstractBytes bytes nicheOffset.bytes nicheBytes with
      | .none => .none
      | .some nicheSlice =>
        match decodeScalarBytes nicheSlice false with
        | .none => .none
        | .some p =>
          match Nat.beq p.1.bits nicheValue with
          | true =>
            match policyRejectsProv policy nicheSlice with
            | true => .none
            | false => .some (.aggregate nicheVariant .nil)
          | false =>
            match decodeFieldsByTysWithPolicy decodeChild layouts bytes dataOffsets dataFieldTys with
            | .some vals => .some (.aggregate dataVariant vals)
            | .none => .none

/-- Policy refinement for `decodeAdtRichWithPolicy` across single-variant
structs, tagged enums, and offset-sliced multi-field niche-pointer enums. -/
theorem decodeAdtRichWithPolicy_strict_refines_strip
    (childStrict childStrip : Ty → List AbstractByte → Option Value)
    (layouts : LayoutTable) (l : TypeLayout) (spec : RichAdtSpec)
    (bytes : List AbstractByte) (v : Value)
    (hchild : ∀ ty bs cv, childStrict ty bs = .some cv → childStrip ty bs = .some cv)
    (h : decodeAdtRichWithPolicy .strictUcg630Ub childStrict layouts l spec bytes = .some v) :
    decodeAdtRichWithPolicy .stripProvenance childStrip layouts l spec bytes = .some v := by
  cases spec with
  | structFields variantIdx offsets fieldTys =>
    unfold decodeAdtRichWithPolicy at h ⊢
    cases hu : Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
    | true => rw [hu] at h; cases h
    | false =>
      rw [hu] at h; dsimp only at h ⊢
      cases hdf : decodeFieldsByTysWithPolicy childStrict layouts bytes offsets fieldTys with
      | none => rw [hdf] at h; cases h
      | some vals =>
        rw [hdf] at h
        rw [decodeFieldsByTysWithPolicy_mono childStrict childStrip layouts bytes
          offsets fieldTys vals hchild hdf]
        exact h
  | taggedEnum tagLayout tagField variantShapes variantFieldTys =>
    unfold decodeAdtRichWithPolicy at h ⊢
    cases hu : Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
    | true => rw [hu] at h; cases h
    | false =>
      rw [hu] at h; dsimp only at h ⊢
      exact decodeMultiVariantEnumRichWithPolicy_strict_refines_strip childStrict childStrip
        layouts l (.tagged tagLayout tagField variantShapes variantFieldTys) bytes v hchild h
  | nichePointerEnum nicheOffset nicheBytes nicheVariant dataVariant dataOffsets dataFieldTys =>
    unfold decodeAdtRichWithPolicy at h ⊢
    cases hu : Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
    | true => rw [hu] at h; cases h
    | false =>
      rw [hu] at h; dsimp only at h ⊢
      cases hsl : sliceAbstractBytes bytes nicheOffset.bytes nicheBytes with
      | none => rw [hsl] at h; cases h
      | some nicheSlice =>
        rw [hsl] at h; dsimp only at h ⊢
        cases hsc : decodeScalarBytes nicheSlice false with
        | none => rw [hsc] at h; cases h
        | some p =>
          rw [hsc] at h; dsimp only at h ⊢
          cases hup : abstractBytesUniformProv nicheSlice with
          | true =>
            rw [hup] at h; dsimp only at h ⊢
            cases hdf : decodeFieldsByTysWithPolicy childStrict layouts bytes
                dataOffsets dataFieldTys with
            | none => rw [hdf] at h; cases h
            | some vals =>
              rw [hdf] at h
              rw [decodeFieldsByTysWithPolicy_mono childStrict childStrip layouts bytes
                dataOffsets dataFieldTys vals hchild hdf]
              exact h
          | false =>
            rw [hup] at h; dsimp only at h ⊢
            cases hz : Nat.beq p.1.bits 0 with
            | true =>
              rw [hz] at h; dsimp only [policyRejectsProv] at h ⊢
              cases hp : abstractBytesHaveProv nicheSlice with
              | true => rw [hp] at h; cases h
              | false => rw [hp] at h; exact h
            | false =>
              rw [hz] at h; dsimp only at h ⊢
              cases hdf : decodeFieldsByTysWithPolicy childStrict layouts bytes
                  dataOffsets dataFieldTys with
              | none => rw [hdf] at h; cases h
              | some vals =>
                rw [hdf] at h
                rw [decodeFieldsByTysWithPolicy_mono childStrict childStrip layouts bytes
                  dataOffsets dataFieldTys vals hchild hdf]
                exact h
  | nicheScalarEnum nicheOffset nicheBytes nicheValue nicheVariant dataVariant dataOffsets dataFieldTys =>
    unfold decodeAdtRichWithPolicy at h ⊢
    cases hu : Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
    | true => rw [hu] at h; cases h
    | false =>
      rw [hu] at h; dsimp only at h ⊢
      cases hsl : sliceAbstractBytes bytes nicheOffset.bytes nicheBytes with
      | none => rw [hsl] at h; cases h
      | some nicheSlice =>
        rw [hsl] at h; dsimp only at h ⊢
        cases hsc : decodeScalarBytes nicheSlice false with
        | none => rw [hsc] at h; cases h
        | some p =>
          rw [hsc] at h; dsimp only at h ⊢
          cases hz : Nat.beq p.1.bits nicheValue with
          | true =>
            rw [hz] at h; dsimp only [policyRejectsProv] at h ⊢
            cases hp : abstractBytesHaveProv nicheSlice with
            | true => rw [hp] at h; cases h
            | false => rw [hp] at h; exact h
          | false =>
            rw [hz] at h; dsimp only at h ⊢
            cases hdf : decodeFieldsByTysWithPolicy childStrict layouts bytes
                dataOffsets dataFieldTys with
            | none => rw [hdf] at h; cases h
            | some vals =>
              rw [hdf] at h
              rw [decodeFieldsByTysWithPolicy_mono childStrict childStrip layouts bytes
                dataOffsets dataFieldTys vals hchild hdf]
              exact h

/-- Provenance-free equivalence of `decodeAdtRichWithPolicy`: whenever
`abstractBytesHaveProv bytes = false`, `.stripProvenance` and `.strictUcg630Ub`
return the identical `Option Value`. -/
theorem decodeAdtRichWithPolicy_strip_eq_strict_of_no_prov
    (childStrip childStrict : Ty → List AbstractByte → Option Value)
    (layouts : LayoutTable) (l : TypeLayout) (spec : RichAdtSpec)
    (bytes : List AbstractByte)
    (hnp : abstractBytesHaveProv bytes = false)
    (hchild : ∀ ty bs, abstractBytesHaveProv bs = false → childStrip ty bs = childStrict ty bs) :
    decodeAdtRichWithPolicy .stripProvenance childStrip layouts l spec bytes =
      decodeAdtRichWithPolicy .strictUcg630Ub childStrict layouts l spec bytes := by
  cases spec with
  | structFields variantIdx offsets fieldTys =>
    unfold decodeAdtRichWithPolicy
    cases Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
    | true => rfl
    | false =>
      dsimp only
      rw [decodeFieldsByTysWithPolicy_eq_of_no_prov childStrip childStrict
        layouts bytes offsets fieldTys hnp hchild]
  | taggedEnum tagLayout tagField variantShapes variantFieldTys =>
    unfold decodeAdtRichWithPolicy
    cases Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
    | true => rfl
    | false =>
      dsimp only
      exact decodeMultiVariantEnumRichWithPolicy_strip_eq_strict_of_no_prov childStrip childStrict
        layouts l (.tagged tagLayout tagField variantShapes variantFieldTys) bytes hnp hchild
  | nichePointerEnum nicheOffset nicheBytes nicheVariant dataVariant dataOffsets dataFieldTys =>
    unfold decodeAdtRichWithPolicy
    cases Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
    | true => rfl
    | false =>
      dsimp only
      cases hsl : sliceAbstractBytes bytes nicheOffset.bytes nicheBytes with
      | none => rfl
      | some nicheSlice =>
        dsimp only
        have hnpSlice := abstractBytesHaveProv_slice bytes nicheSlice
          nicheOffset.bytes nicheBytes hnp hsl
        cases decodeScalarBytes nicheSlice false with
        | none => rfl
        | some p =>
          dsimp only
          cases abstractBytesUniformProv nicheSlice with
          | true =>
            dsimp only
            rw [decodeFieldsByTysWithPolicy_eq_of_no_prov childStrip childStrict
              layouts bytes dataOffsets dataFieldTys hnp hchild]
          | false =>
            dsimp only
            cases Nat.beq p.1.bits 0 with
            | true => dsimp only [policyRejectsProv]; rw [hnpSlice]
            | false =>
              dsimp only
              rw [decodeFieldsByTysWithPolicy_eq_of_no_prov childStrip childStrict
                layouts bytes dataOffsets dataFieldTys hnp hchild]
  | nicheScalarEnum nicheOffset nicheBytes nicheValue nicheVariant dataVariant dataOffsets dataFieldTys =>
    unfold decodeAdtRichWithPolicy
    cases Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
    | true => rfl
    | false =>
      dsimp only
      cases hsl : sliceAbstractBytes bytes nicheOffset.bytes nicheBytes with
      | none => rfl
      | some nicheSlice =>
        dsimp only
        have hnpSlice := abstractBytesHaveProv_slice bytes nicheSlice
          nicheOffset.bytes nicheBytes hnp hsl
        cases decodeScalarBytes nicheSlice false with
        | none => rfl
        | some p =>
          dsimp only
          cases Nat.beq p.1.bits nicheValue with
          | true => dsimp only [policyRejectsProv]; rw [hnpSlice]
          | false =>
            dsimp only
            rw [decodeFieldsByTysWithPolicy_eq_of_no_prov childStrip childStrict
              layouts bytes dataOffsets dataFieldTys hnp hchild]

/-- Layout fixture for 16-byte niche-encoded `Option<&[u8]>` / `Option<(&u8, u64)>`
(null niche in `[0..8)`, inactive or sibling payload in `[8..16)`). -/
def protoNicheWide16Layout : TypeLayout := {
  size := { bytes := 16 }
  align := { bytes := 8 }
  backendRepr := .scalarPair
    (.initialized (.pointer 0) ⟨0, scalarModulus 8 - 1⟩)
    (.union (.int 64 false))
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .multiple (.initialized (.pointer 0) ⟨0, scalarModulus 8 - 1⟩) 0
    [.arbitrary [] [], .arbitrary [{ bytes := 0 }] [0]]
  isUninhabited := false
}

/-- Layout fixture for `[Option<&u8>; 2]` (`stride = 8`, `count = 2`,
`fieldLayouts = [4]` pointing to `protoNicheOptionRefLayout` in
`protoRichEnumLayouts`). -/
def protoOptionRefArray2Layout : TypeLayout := {
  size := { bytes := 16 }
  align := { bytes := 8 }
  backendRepr := .memory
  fields := .array { bytes := 8 } 2
  variants := .single 0
  fieldLayouts := [4]
  isUninhabited := false
}

def protoRichExtLayouts : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries := [
    protoUnitLayout,            -- 0
    protoNonNullPtrFieldLayout, -- 1
    protoWrapRefLayout,         -- 2
    protoRefPayloadEnumLayout,  -- 3
    protoNicheOptionRefLayout,  -- 4
    protoWideSliceEnumLayout,   -- 5
    protoWideSliceRefLayout,    -- 6
    protoU32FieldLayout,        -- 7
    protoU32PairStructLayout,   -- 8
    protoNicheWide16Layout,     -- 9
    protoOptionRefArray2Layout  -- 10
  ]
}

/-- **Second bug in `EnumDecodeSpec.nichePointer` (`by rfl`) and its repair via
`RichAdtSpec.nichePointerEnum`**:
`decodeMultiVariantEnumRichWithPolicy`'s `.nichePointer` arm runs
`decodeScalarBytes bytes false` across the **entire** enum byte slice instead of
slicing only `[nicheOffset .. nicheOffset + nicheBytes)`:
1. On genuine `Option::<&[u8]>::None` (`0` at `0..8` + `.uninit` inactive
   metadata padding at `8..16`), A2's `.nichePointer` returns **`.none` (`UB`)**
   under both policies;
2. Even when `8..16` holds initialized leftover metadata `5` (`0` at `0..8`, `5`
   at `8..16`), A2's `.nichePointer` sees `bits = 5 * 2^64 ≠ 0`, misclassifies
   `None` as `Some(&[u8])`, and returns **`.none` (`UB`)** under both policies;
3. `decodeAdtRichWithPolicy` with `.nichePointerEnum ⟨0⟩ 8 0 1 …` decodes BOTH
   `Option::<&[u8]>::None` images to `.some (.aggregate 0 [])` under both
   policies, decodes offset-zero `Option::Some(&slice)` (`allocId = 7, offset = 0,
   len = 5`) to `Some([ptr(7, 0), scalar 5])` under both policies, and on
   multi-field `Option<(&u8, u64)>` (`[⟨0⟩, ⟨8⟩]`, `[&u8, u64]`) decodes `None`
   (`0` + `.uninit` padding), preserves `Some((&x, 42))`, rejects forged
   `Some((0x1000, 42))`, and flips provenance-carrying sibling `u64` (`strict =
   .none` vs `strip = .some`)! -/
theorem niche_wide_and_multifield_bug_and_complete_fix_witness :
    -- 1. A2 `.nichePointer` rejects valid `Option::<&[u8]>::None` with `.uninit` metadata padding
    decodeMultiVariantEnumRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichExtLayouts)
        protoRichExtLayouts protoNicheWide16Layout (.nichePointer 0 1 protoWideSliceRefTy)
        (appendAbstractBytes (encodeLittleEndianBytes 0 8 .none) (replicateUninitBytes 8)) =
      .none ∧
    decodeMultiVariantEnumRichWithPolicy .stripProvenance
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoRichExtLayouts)
        protoRichExtLayouts protoNicheWide16Layout (.nichePointer 0 1 protoWideSliceRefTy)
        (appendAbstractBytes (encodeLittleEndianBytes 0 8 .none) (replicateUninitBytes 8)) =
      .none ∧
    -- 2. A2 `.nichePointer` ALSO rejects `Option::<&[u8]>::None` with leftover nonzero metadata!
    decodeMultiVariantEnumRichWithPolicy .stripProvenance
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoRichExtLayouts)
        protoRichExtLayouts protoNicheWide16Layout (.nichePointer 0 1 protoWideSliceRefTy)
        (appendAbstractBytes (encodeLittleEndianBytes 0 8 .none)
          (encodeLittleEndianBytes 5 8 .none)) = .none ∧
    -- 3. `decodeAdtRichWithPolicy` decodes BOTH `Option::<&[u8]>::None` images under both policies
    decodeAdtRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichExtLayouts)
        protoRichExtLayouts protoNicheWide16Layout
        (.nichePointerEnum { bytes := 0 } 8 0 1 [{ bytes := 0 }] [protoWideSliceRefTy])
        (appendAbstractBytes (encodeLittleEndianBytes 0 8 .none) (replicateUninitBytes 8)) =
      .some (.aggregate 0 []) ∧
    decodeAdtRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichExtLayouts)
        protoRichExtLayouts protoNicheWide16Layout
        (.nichePointerEnum { bytes := 0 } 8 0 1 [{ bytes := 0 }] [protoWideSliceRefTy])
        (appendAbstractBytes (encodeLittleEndianBytes 0 8 .none)
          (encodeLittleEndianBytes 5 8 .none)) =
      .some (.aggregate 0 []) ∧
    -- 4. Offset-zero `Option::Some(&slice)` preserves `Value.ptr` + `len = 5` under both policies
    decodeAdtRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichExtLayouts)
        protoRichExtLayouts protoNicheWide16Layout
        (.nichePointerEnum { bytes := 0 } 8 0 1 [{ bytes := 0 }] [protoWideSliceRefTy])
        (appendAbstractBytes protoOffsetZeroRefBytes (encodeLittleEndianBytes 5 8 .none)) =
      .some (.aggregate 1 [.aggregate 0 [.ptr { allocId := 7, offsetBytes := 0 } 8,
        .scalar ⟨5, 8⟩]]) ∧
    -- 5. Multi-field `Option<(&u8, u64)>`: `Some((&x_at_0, 42))` preserved, forged `0x1000` rejected,
    --    and provenance in sibling `u64` flips `.strictUcg630Ub = .none` vs `.stripProvenance = .some`!
    decodeAdtRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichExtLayouts)
        protoRichExtLayouts protoNicheWide16Layout
        (.nichePointerEnum { bytes := 0 } 8 0 1
          [{ bytes := 0 }, { bytes := 8 }] [protoRefTy, { kind := .uint .u64, layoutIdx := 99 }])
        (appendAbstractBytes protoOffsetZeroRefBytes (encodeLittleEndianBytes 42 8 .none)) =
      .some (.aggregate 1 [.ptr { allocId := 7, offsetBytes := 0 } 8, .scalar ⟨42, 8⟩]) ∧
    decodeAdtRichWithPolicy .stripProvenance
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoRichExtLayouts)
        protoRichExtLayouts protoNicheWide16Layout
        (.nichePointerEnum { bytes := 0 } 8 0 1
          [{ bytes := 0 }, { bytes := 8 }] [protoRefTy, { kind := .uint .u64, layoutIdx := 99 }])
        (appendAbstractBytes (encodeLittleEndianBytes 0x1000 8 .none)
          (encodeLittleEndianBytes 42 8 .none)) = .none ∧
    decodeAdtRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichExtLayouts)
        protoRichExtLayouts protoNicheWide16Layout
        (.nichePointerEnum { bytes := 0 } 8 0 1
          [{ bytes := 0 }, { bytes := 8 }] [protoRefTy, { kind := .uint .u64, layoutIdx := 99 }])
        (appendAbstractBytes protoOffsetZeroRefBytes
          (encodeLittleEndianBytes 42 8 (.some (9, 9)))) = .none ∧
    decodeAdtRichWithPolicy .stripProvenance
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoRichExtLayouts)
        protoRichExtLayouts protoNicheWide16Layout
        (.nichePointerEnum { bytes := 0 } 8 0 1
          [{ bytes := 0 }, { bytes := 8 }] [protoRefTy, { kind := .uint .u64, layoutIdx := 99 }])
        (appendAbstractBytes protoOffsetZeroRefBytes
          (encodeLittleEndianBytes 42 8 (.some (9, 9)))) =
      .some (.aggregate 1 [.ptr { allocId := 7, offsetBytes := 0 } 8, .scalar ⟨42, 8⟩]) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Fuel-indexed rich typed decoder** integrating `RichAdtSpec` across nested
ADTs, arrays (`[Option<&u8>; N]`, `[Wrap(&u8); N]`), and tuples
(`(Option<&u8>, Wrap(&u8))`), while collapsing definitionally to
`decodeTypedValueFromBytesWithPolicy` when `richSpecs = []`. -/
def decodeTypedValueRichWithPolicy
    (policy : Ptr2IntTransmutePolicy) :
    Nat → LayoutTable → List (LayoutIdx × RichAdtSpec) → Ty → List AbstractByte → Option Value
  | .zero, _, _, _, _ => .none
  | .succ fuel', layouts, richSpecs, ty, bytes =>
    match richSpecs with
    | .nil => decodeTypedValueFromBytesWithPolicy policy (.succ fuel') layouts ty bytes
    | _ :: _ =>
      let rTy := normalizeCodecTy ty
      let decodeChild := fun (cTy : Ty) (bs : List AbstractByte) =>
        decodeTypedValueRichWithPolicy policy fuel' layouts richSpecs cTy bs
      match rTy.kind with
      | .adt _ _ =>
        match LayoutTable.lookup layouts rTy.layoutIdx, lookupRichAdtSpec richSpecs rTy.layoutIdx with
        | .some l, .some spec =>
          decodeAdtRichWithPolicy policy decodeChild layouts l spec bytes
        | .some l, .none =>
          match Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
          | true => .none
          | false =>
            match l.variants with
            | .single variantIdx =>
              match l.fields with
              | .arbitrary (off0 :: offRest) _ =>
                match Nat.beq (length l.fieldLayouts) (length (off0 :: offRest)) with
                | true =>
                  match decodeFieldsByLayoutIdxs
                      (fun fIdx fSlice => decodeChild { kind := .adt "" .nil, layoutIdx := fIdx } fSlice)
                      layouts bytes (off0 :: offRest) l.fieldLayouts with
                  | .some vals => .some (.aggregate variantIdx vals)
                  | .none => .none
                | false =>
                  decodeTypedValueFromBytesWithPolicy policy (.succ fuel') layouts ty bytes
              | _ =>
                decodeTypedValueFromBytesWithPolicy policy (.succ fuel') layouts ty bytes
            | _ =>
              decodeTypedValueFromBytesWithPolicy policy (.succ fuel') layouts ty bytes
        | .none, _ =>
          decodeTypedValueFromBytesWithPolicy policy (.succ fuel') layouts ty bytes
      | .array elemKind n =>
        match Nat.beq n 0 with
        | true =>
          match bytes with
          | .nil => .some (.aggregate 0 .nil)
          | _ :: _ => .none
        | false =>
          match LayoutTable.lookup layouts rTy.layoutIdx with
          | .some l =>
            match l.fields, l.fieldLayouts with
            | .array stride _, elemFlIdx :: _ =>
              match Nat.beq (length bytes) (Nat.mul stride.bytes n) with
              | false => .none
              | true =>
                match decodeArrayChunksWith
                    (decodeChild { kind := elemKind, layoutIdx := elemFlIdx })
                    stride.bytes n bytes with
                | .some elems => .some (.aggregate 0 elems)
                | .none => .none
            | _, _ =>
              decodeTypedValueFromBytesWithPolicy policy (.succ fuel') layouts ty bytes
          | .none =>
            decodeTypedValueFromBytesWithPolicy policy (.succ fuel') layouts ty bytes
      | .tuple (kHead :: kTail) =>
        let ks := kHead :: kTail
        match LayoutTable.lookup layouts rTy.layoutIdx with
        | .some l =>
          match Nat.beq (length bytes) l.size.bytes, l.fields with
          | true, .arbitrary offsets _ =>
            match Bool.and (Nat.beq (length ks) (length offsets))
                (Nat.beq (length l.fieldLayouts) (length offsets)) with
            | true =>
              match decodeTypedKindsAndLayoutsAtOffsets decodeChild layouts bytes
                  offsets ks l.fieldLayouts with
              | .some vals => .some (.aggregate 0 vals)
              | .none => .none
            | false =>
              decodeTypedValueFromBytesWithPolicy policy (.succ fuel') layouts ty bytes
          | _, _ =>
            decodeTypedValueFromBytesWithPolicy policy (.succ fuel') layouts ty bytes
        | .none =>
          decodeTypedValueFromBytesWithPolicy policy (.succ fuel') layouts ty bytes
      | _ =>
        decodeTypedValueFromBytesWithPolicy policy (.succ fuel') layouts ty bytes

/-- With an empty `richSpecs` table, `decodeTypedValueRichWithPolicy` is
identically `decodeTypedValueFromBytesWithPolicy`. -/
theorem decodeTypedValueRichWithPolicy_empty_eq
    (policy : Ptr2IntTransmutePolicy) (fuel : Nat) (layouts : LayoutTable)
    (ty : Ty) (bytes : List AbstractByte) :
    decodeTypedValueRichWithPolicy policy fuel layouts .nil ty bytes =
      decodeTypedValueFromBytesWithPolicy policy fuel layouts ty bytes := by
  cases fuel <;> rfl

/-- **Structural policy refinement for `decodeTypedValueRichWithPolicy`**: for
every `fuel`, `layouts`, `richSpecs`, `ty`, and `bytes`, every `.strictUcg630Ub`
success is the identical `.stripProvenance` success. -/
theorem decodeTypedValueRichWithPolicy_strict_refines_strip
    (fuel : Nat) (layouts : LayoutTable) (richSpecs : List (LayoutIdx × RichAdtSpec))
    (ty : Ty) (bytes : List AbstractByte) (v : Value)
    (h : decodeTypedValueRichWithPolicy .strictUcg630Ub fuel layouts richSpecs ty bytes = .some v) :
    decodeTypedValueRichWithPolicy .stripProvenance fuel layouts richSpecs ty bytes = .some v := by
  induction fuel generalizing ty bytes v with
  | zero => cases h
  | succ fuel' ih =>
    cases richSpecs with
    | nil =>
      exact decodeTypedValueFromBytesWithPolicy_strict_refines_strip
        (.succ fuel') layouts ty bytes v h
    | cons specHd specTl =>
      unfold decodeTypedValueRichWithPolicy at h ⊢
      dsimp only at h ⊢
      cases hk : (normalizeCodecTy ty).kind with
      | adt defPath args =>
        rw [hk] at h; dsimp only at h ⊢
        cases hlk : LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
        | none =>
          rw [hlk] at h
          exact decodeTypedValueFromBytesWithPolicy_strict_refines_strip
            (.succ fuel') layouts ty bytes v h
        | some l =>
          rw [hlk] at h
          cases hsp : lookupRichAdtSpec (specHd :: specTl) (normalizeCodecTy ty).layoutIdx with
          | none =>
            rw [hsp] at h; dsimp only at h ⊢
            cases hu : Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
            | true => rw [hu] at h; cases h
            | false =>
              rw [hu] at h; dsimp only at h ⊢
              cases hv : l.variants with
              | empty | multiple _ _ _ =>
                rw [hv] at h
                exact decodeTypedValueFromBytesWithPolicy_strict_refines_strip
                  (.succ fuel') layouts ty bytes v h
              | single variantIdx =>
                rw [hv] at h; dsimp only at h ⊢
                cases hf : l.fields with
                | primitive | union _ | array _ _ =>
                  rw [hf] at h
                  exact decodeTypedValueFromBytesWithPolicy_strict_refines_strip
                    (.succ fuel') layouts ty bytes v h
                | arbitrary offsets _ =>
                  rw [hf] at h
                  cases offsets with
                  | nil =>
                    exact decodeTypedValueFromBytesWithPolicy_strict_refines_strip
                      (.succ fuel') layouts ty bytes v h
                  | cons off0 offRest =>
                    dsimp only at h ⊢
                    cases hlen : Nat.beq (length l.fieldLayouts) (length (off0 :: offRest)) with
                    | false =>
                      rw [hlen] at h
                      exact decodeTypedValueFromBytesWithPolicy_strict_refines_strip
                        (.succ fuel') layouts ty bytes v h
                    | true =>
                      rw [hlen] at h; dsimp only at h ⊢
                      cases hdec : decodeFieldsByLayoutIdxs
                          (fun fIdx fSlice => decodeTypedValueRichWithPolicy .strictUcg630Ub fuel'
                            layouts (specHd :: specTl) { kind := .adt "" .nil, layoutIdx := fIdx } fSlice)
                          layouts bytes (off0 :: offRest) l.fieldLayouts with
                      | none => rw [hdec] at h; cases h
                      | some vals =>
                        rw [hdec] at h
                        rw [decodeFieldsByLayoutIdxs_mono _ _ layouts bytes
                          (fun fIdx bs cv hc => ih _ bs cv hc)
                          (off0 :: offRest) l.fieldLayouts vals hdec]
                        exact h
          | some spec =>
            rw [hsp] at h
            exact decodeAdtRichWithPolicy_strict_refines_strip _ _ layouts l spec bytes v
              (fun cTy bs cv hc => ih cTy bs cv hc) h
      | array elemKind n =>
        rw [hk] at h; dsimp only at h ⊢
        cases hn : Nat.beq n 0 with
        | true => rw [hn] at h; exact h
        | false =>
          rw [hn] at h; dsimp only at h ⊢
          cases hlk : LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
          | none =>
            rw [hlk] at h
            exact decodeTypedValueFromBytesWithPolicy_strict_refines_strip
              (.succ fuel') layouts ty bytes v h
          | some l =>
            rw [hlk] at h; dsimp only at h ⊢
            cases hf : l.fields with
            | array stride count =>
              rw [hf] at h
              cases hfl : l.fieldLayouts with
              | nil =>
                rw [hfl] at h
                exact decodeTypedValueFromBytesWithPolicy_strict_refines_strip
                  (.succ fuel') layouts ty bytes v h
              | cons elemFlIdx flRest =>
                rw [hfl] at h; dsimp only at h ⊢
                cases hlen : Nat.beq (length bytes) (Nat.mul stride.bytes n) with
                | false => rw [hlen] at h; cases h
                | true =>
                  rw [hlen] at h; dsimp only at h ⊢
                  cases hch : decodeArrayChunksWith
                      (decodeTypedValueRichWithPolicy .strictUcg630Ub fuel' layouts
                        (specHd :: specTl) { kind := elemKind, layoutIdx := elemFlIdx })
                      stride.bytes n bytes with
                  | none => rw [hch] at h; cases h
                  | some elems =>
                    rw [hch] at h
                    rw [decodeArrayChunksWith_mono _ _ stride.bytes
                      (fun bs cv hc => ih _ bs cv hc) n bytes elems hch]
                    exact h
            | primitive | union _ | arbitrary _ _ =>
              rw [hf] at h
              exact decodeTypedValueFromBytesWithPolicy_strict_refines_strip
                (.succ fuel') layouts ty bytes v h
      | tuple ks =>
        rw [hk] at h
        cases ks with
        | nil =>
          exact decodeTypedValueFromBytesWithPolicy_strict_refines_strip
            (.succ fuel') layouts ty bytes v h
        | cons kHead kTail =>
          dsimp only at h ⊢
          cases hlk : LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
          | none =>
            rw [hlk] at h
            exact decodeTypedValueFromBytesWithPolicy_strict_refines_strip
              (.succ fuel') layouts ty bytes v h
          | some l =>
            rw [hlk] at h; dsimp only at h ⊢
            cases hsz : Nat.beq (length bytes) l.size.bytes with
            | false =>
              rw [hsz] at h
              exact decodeTypedValueFromBytesWithPolicy_strict_refines_strip
                (.succ fuel') layouts ty bytes v h
            | true =>
              rw [hsz] at h
              cases hf : l.fields with
              | arbitrary offsets memOrder =>
                rw [hf] at h; dsimp only at h ⊢
                cases hmatch : Bool.and
                    (Nat.beq (length (kHead :: kTail)) (length offsets))
                    (Nat.beq (length l.fieldLayouts) (length offsets)) with
                | false =>
                  rw [hmatch] at h
                  exact decodeTypedValueFromBytesWithPolicy_strict_refines_strip
                    (.succ fuel') layouts ty bytes v h
                | true =>
                  rw [hmatch] at h; dsimp only at h ⊢
                  cases hdec : decodeTypedKindsAndLayoutsAtOffsets
                      (decodeTypedValueRichWithPolicy .strictUcg630Ub fuel' layouts (specHd :: specTl))
                      layouts bytes offsets (kHead :: kTail) l.fieldLayouts with
                  | none => rw [hdec] at h; cases h
                  | some vals =>
                    rw [hdec] at h
                    rw [decodeTypedKindsAndLayoutsAtOffsets_mono _ _ layouts bytes
                      (fun cTy bs cv hc => ih cTy bs cv hc)
                      offsets (kHead :: kTail) l.fieldLayouts vals hdec]
                    exact h
              | primitive | union _ | array _ _ =>
                rw [hf] at h
                exact decodeTypedValueFromBytesWithPolicy_strict_refines_strip
                  (.succ fuel') layouts ty bytes v h
      | _ =>
        rw [hk] at h
        exact decodeTypedValueFromBytesWithPolicy_strict_refines_strip
          (.succ fuel') layouts ty bytes v h

/-- **Provenance-free equivalence for `decodeTypedValueRichWithPolicy`**:
whenever `abstractBytesHaveProv bytes = false`, `.stripProvenance` and
`.strictUcg630Ub` return the identical `Option Value` across arbitrary nested
`richSpecs`. -/
theorem decodeTypedValueRichWithPolicy_strip_eq_strict_of_no_prov
    (fuel : Nat) (layouts : LayoutTable) (richSpecs : List (LayoutIdx × RichAdtSpec))
    (ty : Ty) (bytes : List AbstractByte)
    (hnp : abstractBytesHaveProv bytes = false) :
    decodeTypedValueRichWithPolicy .stripProvenance fuel layouts richSpecs ty bytes =
      decodeTypedValueRichWithPolicy .strictUcg630Ub fuel layouts richSpecs ty bytes := by
  induction fuel generalizing ty bytes with
  | zero => rfl
  | succ fuel' ih =>
    cases richSpecs with
    | nil =>
      exact decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
        (.succ fuel') layouts ty bytes hnp
    | cons specHd specTl =>
      unfold decodeTypedValueRichWithPolicy
      dsimp only
      cases hk : (normalizeCodecTy ty).kind with
      | adt defPath args =>
        dsimp only
        cases LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
        | none =>
          exact decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
            (.succ fuel') layouts ty bytes hnp
        | some l =>
          cases lookupRichAdtSpec (specHd :: specTl) (normalizeCodecTy ty).layoutIdx with
          | none =>
            dsimp only
            cases Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
            | true => rfl
            | false =>
              dsimp only
              cases l.variants with
              | empty | multiple _ _ _ =>
                exact decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
                  (.succ fuel') layouts ty bytes hnp
              | single variantIdx =>
                dsimp only
                cases l.fields with
                | primitive | union _ | array _ _ =>
                  exact decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
                    (.succ fuel') layouts ty bytes hnp
                | arbitrary offsets _ =>
                  cases offsets with
                  | nil =>
                    exact decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
                      (.succ fuel') layouts ty bytes hnp
                  | cons off0 offRest =>
                    dsimp only
                    cases Nat.beq (length l.fieldLayouts) (length (off0 :: offRest)) with
                    | false =>
                      exact decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
                        (.succ fuel') layouts ty bytes hnp
                    | true =>
                      dsimp only
                      rw [decodeFieldsByLayoutIdxs_congr_no_prov _ _ layouts bytes hnp
                        (fun fIdx bs hbs => ih _ bs hbs) (off0 :: offRest) l.fieldLayouts]
          | some spec =>
            exact decodeAdtRichWithPolicy_strip_eq_strict_of_no_prov _ _ layouts l spec bytes hnp
              (fun cTy bs hbs => ih cTy bs hbs)
      | array elemKind n =>
        dsimp only
        cases Nat.beq n 0 with
        | true => rfl
        | false =>
          dsimp only
          cases LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
          | none =>
            exact decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
              (.succ fuel') layouts ty bytes hnp
          | some l =>
            dsimp only
            cases l.fields with
            | array stride count =>
              cases l.fieldLayouts with
              | nil =>
                exact decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
                  (.succ fuel') layouts ty bytes hnp
              | cons elemFlIdx flRest =>
                dsimp only
                cases Nat.beq (length bytes) (Nat.mul stride.bytes n) with
                | false => rfl
                | true =>
                  dsimp only
                  rw [decodeArrayChunksWith_congr_no_prov _ _ stride.bytes
                    (fun bs hbs => ih _ bs hbs) n bytes hnp]
            | primitive | union _ | arbitrary _ _ =>
              exact decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
                (.succ fuel') layouts ty bytes hnp
      | tuple ks =>
        cases ks with
        | nil =>
          exact decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
            (.succ fuel') layouts ty bytes hnp
        | cons kHead kTail =>
          dsimp only
          cases LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
          | none =>
            exact decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
              (.succ fuel') layouts ty bytes hnp
          | some l =>
            dsimp only
            cases Nat.beq (length bytes) l.size.bytes with
            | false =>
              exact decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
                (.succ fuel') layouts ty bytes hnp
            | true =>
              cases l.fields with
              | arbitrary offsets memOrder =>
                dsimp only
                cases Bool.and
                    (Nat.beq (length (kHead :: kTail)) (length offsets))
                    (Nat.beq (length l.fieldLayouts) (length offsets)) with
                | false =>
                  exact decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
                    (.succ fuel') layouts ty bytes hnp
                | true =>
                  dsimp only
                  rw [decodeTypedKindsAndLayoutsAtOffsets_congr_no_prov _ _ layouts bytes hnp
                    (fun cTy bs hbs => ih cTy bs hbs) offsets (kHead :: kTail) l.fieldLayouts]
              | primitive | union _ | array _ _ =>
                exact decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
                  (.succ fuel') layouts ty bytes hnp
      | _ =>
        exact decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
          (.succ fuel') layouts ty bytes hnp

/-- Cast-level byte reinterpretation (`CastKind.transmute` / `CastKind.subtype`)
backed by `decodeTypedValueRichWithPolicy`. -/
def evalByteCastRichWithPolicy
    (policy : Ptr2IntTransmutePolicy)
    (richSpecs : List (LayoutIdx × RichAdtSpec))
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
            match encodeByteCastSourceBytes layouts rSrcTy v with
            | .none => .ub
            | .some bs =>
              match Nat.beq (length bs) dstSize with
              | false => .ub
              | true =>
                match decodeTypedValueRichWithPolicy policy defaultCodecFuel
                    layouts richSpecs rTargetTy bs with
                | .some v' => .ok v' locals' mem
                | .none => .ub
      | .none =>
        match encodeUntypedValueToBytes defaultCodecFuel v with
        | .none => .unsupported
        | .some bs =>
          match Nat.beq (length bs) dstSize with
          | false => .unsupported
          | true =>
            match decodeTypedValueRichWithPolicy policy defaultCodecFuel
                layouts richSpecs rTargetTy bs with
            | .some v' => .ok v' locals' mem
            | .none => .ub

/-- Cast-level policy refinement of `evalByteCastRichWithPolicy`: every
`.strictUcg630Ub` `.ok` evaluation is the identical `.stripProvenance` `.ok`
evaluation across arbitrary `richSpecs`. -/
theorem evalByteCastRichWithPolicy_strict_refines_strip
    (richSpecs : List (LayoutIdx × RichAdtSpec))
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (v' : Value) (locals' : List LocalSlot) (mem' : Memory)
    (h : evalByteCastRichWithPolicy .strictUcg630Ub richSpecs locals op targetTy
      mem localDecls layouts = .ok v' locals' mem') :
    evalByteCastRichWithPolicy .stripProvenance richSpecs locals op targetTy
      mem localDecls layouts = .ok v' locals' mem' := by
  unfold evalByteCastRichWithPolicy at h ⊢
  cases hev : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals
      localDecls mem.callStack with
  | ub => rw [hev] at h; cases h
  | unsupported => rw [hev] at h; cases h
  | ok v loc1 =>
    rw [hev] at h; dsimp only at h ⊢
    cases hdst : tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts targetTy) with
    | none => rw [hdst] at h; cases h
    | some dstSize =>
      rw [hdst] at h; dsimp only at h ⊢
      cases hopTy : operandTy localDecls layouts op with
      | some srcTy =>
        rw [hopTy] at h; dsimp only at h ⊢
        cases hsrc : tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts srcTy) with
        | none => rw [hsrc] at h; cases h
        | some srcSize =>
          rw [hsrc] at h; dsimp only at h ⊢
          cases hsz : Nat.beq srcSize dstSize with
          | false => rw [hsz] at h; cases h
          | true =>
            rw [hsz] at h; dsimp only at h ⊢
            cases henc : encodeByteCastSourceBytes layouts
                (resolveTyWithLocalDecls localDecls layouts srcTy) v with
            | none => rw [henc] at h; cases h
            | some bs =>
              rw [henc] at h; dsimp only at h ⊢
              cases hlen : Nat.beq (length bs) dstSize with
              | false => rw [hlen] at h; cases h
              | true =>
                rw [hlen] at h; dsimp only at h ⊢
                cases hdec : decodeTypedValueRichWithPolicy .strictUcg630Ub defaultCodecFuel
                    layouts richSpecs (resolveTyWithLocalDecls localDecls layouts targetTy) bs with
                | none => rw [hdec] at h; cases h
                | some dv =>
                  rw [hdec] at h
                  rw [decodeTypedValueRichWithPolicy_strict_refines_strip defaultCodecFuel
                    layouts richSpecs _ bs dv hdec]
                  exact h
      | none =>
        rw [hopTy] at h; dsimp only at h ⊢
        cases henc : encodeUntypedValueToBytes defaultCodecFuel v with
        | none => rw [henc] at h; cases h
        | some bs =>
          rw [henc] at h; dsimp only at h ⊢
          cases hlen : Nat.beq (length bs) dstSize with
          | false => rw [hlen] at h; cases h
          | true =>
            rw [hlen] at h; dsimp only at h ⊢
            cases hdec : decodeTypedValueRichWithPolicy .strictUcg630Ub defaultCodecFuel
                layouts richSpecs (resolveTyWithLocalDecls localDecls layouts targetTy) bs with
            | none => rw [hdec] at h; cases h
            | some dv =>
              rw [hdec] at h
              rw [decodeTypedValueRichWithPolicy_strict_refines_strip defaultCodecFuel
                layouts richSpecs _ bs dv hdec]
              exact h

/-- Rich spec table for `protoRichExtLayouts`:
- `2`: `struct Wrap(&u8)` (`.structFields 0 [⟨0⟩] [protoRefTy]`);
- `3`: `enum R { A(&u8), B(&u8) }` (`.taggedEnum …`);
- `4`: `Option<&u8>` (`.nichePointerEnum ⟨0⟩ 8 0 1 [⟨0⟩] [protoRefTy]`). -/
def protoRichExtSpecs : List (LayoutIdx × RichAdtSpec) := [
  (2, .structFields 0 [{ bytes := 0 }] [protoRefTy]),
  (3, .taggedEnum (.initialized (.int 64 false) ⟨0, 1⟩) 0
    [.arbitrary [{ bytes := 8 }] [0], .arbitrary [{ bytes := 8 }] [0]]
    [[protoRefTy], [protoRefTy]]),
  (4, .nichePointerEnum { bytes := 0 } 8 0 1 [{ bytes := 0 }] [protoRefTy])
]

/-- **Cast-level end-to-end closure (`by rfl`) of TCB Findings 3, 4, and 5 plus
nested `[Option<&u8>; 2]`**:
1. **Finding 5 closed at cast layer**: `transmute::<usize, struct Wrap(&u8)>(0x1000)`
   returns **`.ub` under both policies** (whereas trusted `evalByteCast` returned
   `.ok`), while genuine offset-zero `&u8 -> Wrap(&u8)` preserves `Value.ptr`;
2. **Finding 3 closed at cast layer**: `transmute::<*const u8, enum E>(p)` flips
   between **`.ub` under `.strictUcg630Ub`** and **`.ok (.aggregate 1 [scalar 42])`
   under `.stripProvenance`**;
3. **Nested `[Option<&u8>; 2]`**: `[None, Some(&x_at_offset_0)]` decodes cleanly
   under **both** policies (exercising array -> niche-enum recursion with
   offset-zero provenance), whereas `[None, forged_0x1000]` is rejected under
   **both** policies! -/
theorem evalByteCastRichWithPolicy_closing_findings_3_4_5_witness :
    -- 1a. Finding 5 closed: `usize(0x1000) -> struct Wrap(&u8)` is `.ub` under BOTH policies
    evalByteCastRichWithPolicy .strictUcg630Ub protoRichExtSpecs
        protoWrapRefLocals (.copy ⟨0, []⟩) protoWrapRefTy emptyMemory
        protoWrapRefDecls protoRichExtLayouts = .ub ∧
    evalByteCastRichWithPolicy .stripProvenance protoRichExtSpecs
        protoWrapRefLocals (.copy ⟨0, []⟩) protoWrapRefTy emptyMemory
        protoWrapRefDecls protoRichExtLayouts = .ub ∧
    -- 1b. Genuine offset-zero `&u8 -> struct Wrap(&u8)` preserves `Value.ptr` under BOTH policies
    evalByteCastRichWithPolicy .strictUcg630Ub protoRichExtSpecs
        [.init (.ptr { allocId := 7, offsetBytes := 0 } 8)] (.copy ⟨0, []⟩) protoWrapRefTy
        emptyMemory [{ mutability := .not, ty := protoRefTy, debugName := none }]
        protoRichExtLayouts =
      .ok (.aggregate 0 [.ptr { allocId := 7, offsetBytes := 0 } 8])
        [.init (.ptr { allocId := 7, offsetBytes := 0 } 8)] emptyMemory ∧
    -- 2. Finding 3 closed: `*const u8 -> enum E { A(u32), B(u32) }` flips strict `.ub` vs strip `.ok`
    evalByteCastRichWithPolicy .strictUcg630Ub
        [(1, .taggedEnum (.initialized (.int 32 false) ⟨0, 1⟩) 0
          [.arbitrary [{ bytes := 4 }] [0], .arbitrary [{ bytes := 4 }] [0]]
          [[{ kind := .uint .u32, layoutIdx := 99 }], [{ kind := .uint .u32, layoutIdx := 99 }]])]
        protoEnumLocals (.copy ⟨0, []⟩) protoTwoVariantEnumTy emptyMemory
        protoEnumDecls protoEnumLayouts = .ub ∧
    evalByteCastRichWithPolicy .stripProvenance
        [(1, .taggedEnum (.initialized (.int 32 false) ⟨0, 1⟩) 0
          [.arbitrary [{ bytes := 4 }] [0], .arbitrary [{ bytes := 4 }] [0]]
          [[{ kind := .uint .u32, layoutIdx := 99 }], [{ kind := .uint .u32, layoutIdx := 99 }]])]
        protoEnumLocals (.copy ⟨0, []⟩) protoTwoVariantEnumTy emptyMemory
        protoEnumDecls protoEnumLayouts =
      .ok (.aggregate 1 [.scalar ⟨42, 4⟩]) protoEnumLocals emptyMemory ∧
    -- 3. Nested `[Option<&u8>; 2]`: `[None, Some(&x_at_offset_0)]` succeeds under BOTH policies,
    --    while `[None, forged_0x1000]` fails under BOTH policies!
    decodeTypedValueRichWithPolicy .strictUcg630Ub 4 protoRichExtLayouts protoRichExtSpecs
        { kind := .array (.adt "Option" [.ref .not (.uint .u8)]) 2, layoutIdx := 10 }
        (appendAbstractBytes (encodeLittleEndianBytes 0 8 .none) protoOffsetZeroRefBytes) =
      .some (.aggregate 0 [.aggregate 0 [],
        .aggregate 1 [.ptr { allocId := 7, offsetBytes := 0 } 8]]) ∧
    decodeTypedValueRichWithPolicy .stripProvenance 4 protoRichExtLayouts protoRichExtSpecs
        { kind := .array (.adt "Option" [.ref .not (.uint .u8)]) 2, layoutIdx := 10 }
        (appendAbstractBytes (encodeLittleEndianBytes 0 8 .none) protoOffsetZeroRefBytes) =
      .some (.aggregate 0 [.aggregate 0 [],
        .aggregate 1 [.ptr { allocId := 7, offsetBytes := 0 } 8]]) ∧
    decodeTypedValueRichWithPolicy .stripProvenance 4 protoRichExtLayouts protoRichExtSpecs
        { kind := .array (.adt "Option" [.ref .not (.uint .u8)]) 2, layoutIdx := 10 }
        (appendAbstractBytes (encodeLittleEndianBytes 0 8 .none)
          (encodeLittleEndianBytes 0x1000 8 .none)) = .none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §17. Additive Rational Thresholds, Sterbenz's Exact-Subtraction Theorem & Relational Dispatcher Determinism -/

/-- Exact rational underflow criterion for finite `add`:
`a + b = zeroBits f (decide (sumInt < 0))` iff `|a + b| ≤ 0.5 * min_subnormal`
(covering exact zero cancellation `sumInt = 0` as well as nonzero subnormal
underflow). -/
theorem evalFloatArithBaseProto_add_finite_underflow_iff (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite ln lnum lden) (hr : decodeBits f b = .finite rn rnum rden) :
    let sumInt := signedNum ln lnum * Int.ofNat rden + signedNum rn rnum * Int.ofNat lden
    evalFloatArithBaseProto .add f a b = zeroBits f (decide (sumInt < 0)) ↔
      2 * sumInt.natAbs * 2 ^ underflowShiftProto f ≤ lden * rden := by
  rw [evalFloatArithBaseProto_add_finite f a b ln rn lnum lden rnum rden hl hr]
  exact roundRatioTiesToEven_eq_zeroBits_iff f _ _ (lden * rden)
    (Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden hl)
      (decodeBits_finite_den_pos f b rn rnum rden hr))

/-- Exact rational overflow criterion for finite `add`:
`a + b = ±Inf` iff `|a + b| ≥ MAX + 0.5 * ulp(MAX)`. -/
theorem evalFloatArithBaseProto_add_finite_overflow_iff (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite ln lnum lden) (hr : decodeBits f b = .finite rn rnum rden) :
    let sumInt := signedNum ln lnum * Int.ofNat rden + signedNum rn rnum * Int.ofNat lden
    evalFloatArithBaseProto .add f a b = infBits f (decide (sumInt < 0)) ↔
      (lden * rden) * overflowThresholdNumProto f ≤ sumInt.natAbs := by
  rw [evalFloatArithBaseProto_add_finite f a b ln rn lnum lden rnum rden hl hr]
  exact roundRatioTiesToEven_eq_infBits_iff f _ _ (lden * rden)
    (Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden hl)
      (decodeBits_finite_den_pos f b rn rnum rden hr))

/-- Exact rational underflow criterion for finite `sub`:
`a - b = zeroBits f (decide (diffInt < 0))` iff `|a - b| ≤ 0.5 * min_subnormal`
(combining with gradual underflow `evalFloatArithBaseProto_sub_finite_eq_zero_iff`
confirms that for finite floats this occurs exclusively when `diffInt = 0`, i.e.,
`a == b`). -/
theorem evalFloatArithBaseProto_sub_finite_underflow_iff (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite ln lnum lden) (hr : decodeBits f b = .finite rn rnum rden) :
    let diffInt := signedNum ln lnum * Int.ofNat rden - signedNum rn rnum * Int.ofNat lden
    evalFloatArithBaseProto .sub f a b = zeroBits f (decide (diffInt < 0)) ↔
      2 * diffInt.natAbs * 2 ^ underflowShiftProto f ≤ lden * rden := by
  rw [evalFloatArithBaseProto_sub_finite f a b ln rn lnum lden rnum rden hl hr]
  exact roundRatioTiesToEven_eq_zeroBits_iff f _ _ (lden * rden)
    (Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden hl)
      (decodeBits_finite_den_pos f b rn rnum rden hr))

/-- Exact rational overflow criterion for finite `sub`:
`a - b = ±Inf` iff `|a - b| ≥ MAX + 0.5 * ulp(MAX)`. -/
theorem evalFloatArithBaseProto_sub_finite_overflow_iff (f : IeeeFormat) (a b : Nat)
    (ln rn : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite ln lnum lden) (hr : decodeBits f b = .finite rn rnum rden) :
    let diffInt := signedNum ln lnum * Int.ofNat rden - signedNum rn rnum * Int.ofNat lden
    evalFloatArithBaseProto .sub f a b = infBits f (decide (diffInt < 0)) ↔
      (lden * rden) * overflowThresholdNumProto f ≤ diffInt.natAbs := by
  rw [evalFloatArithBaseProto_sub_finite f a b ln rn lnum lden rnum rden hl hr]
  exact roundRatioTiesToEven_eq_infBits_iff f _ _ (lden * rden)
    (Nat.mul_pos (decodeBits_finite_den_pos f a ln lnum lden hl)
      (decodeBits_finite_den_pos f b rn rnum rden hr))

/-- Constructive cancellation `a * c ≤ b * c → a ≤ b` for `0 < c` (avoiding
stdlib classical wrappers). -/
private theorem nat_le_of_mul_le_mul_right {a b c : Nat} (hc : 0 < c) (h : a * c ≤ b * c) :
    a ≤ b :=
  match Nat.lt_or_ge b a with
  | .inl hgt => absurd h (Nat.not_le_of_gt (Nat.mul_lt_mul_of_pos_right hgt hc))
  | .inr hle => hle

/-- Core ordered-magnitude lemma for Sterbenz's theorem: when finite `big` and
`small` satisfy `|small| < |big| ≤ 2 * |small|`, their positive rational
difference `(bigN * smallD - bigD * smallN) / (bigD * smallD)` is a dyadic
rational `mDiff * 2^tb` with `0 < mDiff < 2^(fb+1)` and `minExp - fb ≤ tb ≤
maxExp - fb`, hence rounded **with zero error and zero overflow** by
`roundRatioTiesToEven`. -/
private theorem sterbenz_ordered_magnitude (f : IeeeFormat) (neg outSign : Bool)
    (big small bigN bigD smallN smallD : Nat)
    (hbig : decodeBits f big = .finite neg bigN bigD)
    (hsmall : decodeBits f small = .finite neg smallN smallD)
    (hlt : bigD * smallN < bigN * smallD)
    (hle2 : bigN * smallD ≤ 2 * (bigD * smallN)) :
    ∃ diffN diffD,
      decodeBits f (roundRatioTiesToEven f outSign
          (bigN * smallD - bigD * smallN) (bigD * smallD)) =
        .finite outSign diffN diffD ∧
      diffN * (bigD * smallD) = (bigN * smallD - bigD * smallN) * diffD ∧
      0 < diffD := by
  have hbigD_pos := decodeBits_finite_den_pos f big neg bigN bigD hbig
  have hsmallD_pos := decodeBits_finite_den_pos f small neg smallN smallD hsmall
  have hden_pos : 0 < bigD * smallD := Nat.mul_pos hbigD_pos hsmallD_pos
  obtain ⟨ma, ta, _, hma_lt, hta_lo, _, _, hb1, hb2⟩ :=
    decodeBits_finite_dyadic f big neg bigN bigD hbig
  obtain ⟨mb, tb, _, hmb_lt, htb_lo, htb_hi, htb_norm, hs1, hs2⟩ :=
    decodeBits_finite_dyadic f small neg smallN smallD hsmall
  have htb_le_ta : tb ≤ ta := by
    rcases htb_norm with rfl | hmb_ge
    · exact hta_lo
    · by_cases hle : tb ≤ ta
      · exact hle
      · exfalso
        let j := (tb - ta).toNat
        have hj_pos : 1 ≤ j := by omega
        have htb_eq : tb = ta + (j : Int) := by omega
        have hcross_b := powScale_add_nat_cross mb j ta
        rw [← htb_eq, ← hs1, ← hs2] at hcross_b
        have hcmp_cross : bigN * smallD * (powScale (mb * 2 ^ j) 1 ta).2 <
            bigD * smallN * (powScale (mb * 2 ^ j) 1 ta).2 := by
          have h1 : ma < mb * 2 ^ j := by
            have h2j : 2 ≤ 2 ^ j := by
              have := Nat.pow_le_pow_right (show 0 < 2 by decide) hj_pos
              simpa using this
            have htwo : 2 ^ (f.fractionBits + 1) = 2 ^ f.fractionBits * 2 := Nat.pow_succ _ _
            have hmb2 : 2 ^ f.fractionBits * 2 ≤ mb * 2 ^ j := Nat.mul_le_mul hmb_ge h2j
            omega
          rw [hb1, hb2]
          have hr_mul : (powScale ma 1 ta).2 * smallN * (powScale (mb * 2 ^ j) 1 ta).2 =
              (powScale ma 1 ta).2 * (powScale (mb * 2 ^ j) 1 ta).1 * smallD := by
            rw [Nat.mul_assoc, ← hcross_b, ← Nat.mul_assoc]
          have hmul_a : (powScale ma 1 ta).1 * smallD * (powScale (mb * 2 ^ j) 1 ta).2 =
              (powScale ma 1 ta).1 * (powScale (mb * 2 ^ j) 1 ta).2 * smallD := by
            rw [Nat.mul_right_comm]
          rw [hr_mul, hmul_a]
          have hstrict : (powScale ma 1 ta).1 * (powScale (mb * 2 ^ j) 1 ta).2 <
              (powScale ma 1 ta).2 * (powScale (mb * 2 ^ j) 1 ta).1 := by
            cases ta with
            | ofNat e =>
              simp only [powScale, Nat.mul_one, Nat.one_mul]
              exact Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos e)
            | negSucc e =>
              simp only [powScale, Nat.one_mul]
              rw [Nat.mul_comm (2 ^ (e + 1))]
              exact Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos (e + 1))
          exact Nat.mul_lt_mul_of_pos_right hstrict hsmallD_pos
        exact Nat.not_lt_of_le (Nat.le_of_lt hlt) (nat_lt_of_mul_lt_mul_right hcmp_cross)
  let k := (ta - tb).toNat
  have hta_eq : ta = tb + (k : Int) := by omega
  have hcross_a := powScale_add_nat_cross ma k tb
  rw [← hta_eq, ← hb1, ← hb2] at hcross_a
  let mDiff := ma * 2 ^ k - mb
  have hscale_factor : ∃ c : Nat, 0 < c ∧
      bigN * smallD = (ma * 2 ^ k) * c ∧
      bigD * smallN = mb * c ∧
      (bigN * smallD - bigD * smallN) * (powScale mDiff 1 tb).2 =
        (powScale mDiff 1 tb).1 * (bigD * smallD) := by
    cases htb_case : tb with
    | ofNat e =>
      rw [htb_case] at hcross_a hs1 hs2
      simp only [powScale, Nat.mul_one] at hcross_a hs1 hs2 ⊢
      refine ⟨2 ^ e * bigD, Nat.mul_pos (Nat.two_pow_pos e) hbigD_pos, ?_, ?_, ?_⟩
      · rw [hs2, Nat.mul_one, ← hcross_a, Nat.mul_assoc]
      · rw [hs1, Nat.mul_left_comm, Nat.mul_comm bigD (2 ^ e)]
      · have he1 : bigN * smallD = (ma * 2 ^ k) * (2 ^ e * bigD) := by
          rw [hs2, Nat.mul_one, ← hcross_a, Nat.mul_assoc]
        have he2 : bigD * smallN = mb * (2 ^ e * bigD) := by
          rw [hs1, Nat.mul_left_comm, Nat.mul_comm bigD (2 ^ e)]
        rw [he1, he2, ← Nat.sub_mul, hs2, Nat.mul_one]
        show mDiff * (2 ^ e * bigD) = mDiff * 2 ^ e * bigD
        rw [Nat.mul_assoc]
    | negSucc e =>
      rw [htb_case] at hcross_a hs1 hs2
      simp only [powScale, Nat.one_mul] at hcross_a hs1 hs2 ⊢
      refine ⟨bigD, hbigD_pos, ?_, ?_, ?_⟩
      · rw [hs2]; exact hcross_a.symm
      · rw [hs1, Nat.mul_comm]
      · have he1 : bigN * smallD = (ma * 2 ^ k) * bigD := by rw [hs2]; exact hcross_a.symm
        have he2 : bigD * smallN = mb * bigD := by rw [hs1, Nat.mul_comm]
        rw [he1, he2, ← Nat.sub_mul, hs2]
        show mDiff * bigD * 2 ^ (e + 1) = mDiff * (bigD * 2 ^ (e + 1))
        rw [Nat.mul_assoc]
  obtain ⟨c, hc_pos, h_big_c, h_small_c, hdiff_cross⟩ := hscale_factor
  have hmb_lt_mak : mb < ma * 2 ^ k := by
    apply nat_lt_of_mul_lt_mul_right (c := c)
    rw [← h_small_c, ← h_big_c]
    exact hlt
  have hmak_le_2mb : ma * 2 ^ k ≤ 2 * mb := by
    apply nat_le_of_mul_le_mul_right hc_pos
    rw [← h_big_c, Nat.mul_assoc, ← h_small_c]
    exact hle2
  have hmDiff_pos : 0 < mDiff := by dsimp only [mDiff]; omega
  have hmDiff_lt : mDiff < 2 ^ (f.fractionBits + 1) := by dsimp only [mDiff]; omega
  have hcong : roundRatioTiesToEven f outSign
      (bigN * smallD - bigD * smallN) (bigD * smallD) =
      roundRatioTiesToEven f outSign (powScale mDiff 1 tb).1 (powScale mDiff 1 tb).2 := by
    rw [← roundRatioBits_tiesToEven, ← roundRatioBits_tiesToEven]
    exact roundRatioBits_congr .tiesToEven f outSign _ _ _ _
      hden_pos (powScale_snd_pos mDiff tb) hdiff_cross
  rw [hcong]
  obtain ⟨diffN, diffD, hdec, hcross, hDpos⟩ :=
    roundRatioTiesToEven_exact_dyadic f outSign mDiff tb hmDiff_pos hmDiff_lt htb_lo htb_hi
  refine ⟨diffN, diffD, hdec, ?_, hDpos⟩
  have hmul := congrArg (· * (bigD * smallD)) hcross
  have hrhs : (powScale mDiff 1 tb).1 * diffD * (bigD * smallD) =
      (bigN * smallD - bigD * smallN) * diffD * (powScale mDiff 1 tb).2 := by
    rw [Nat.mul_right_comm, ← hdiff_cross, Nat.mul_right_comm]
  have hlhs : diffN * (powScale mDiff 1 tb).2 * (bigD * smallD) =
      diffN * (bigD * smallD) * (powScale mDiff 1 tb).2 := by
    rw [Nat.mul_right_comm]
  rw [hlhs, hrhs] at hmul
  have hle1 := nat_le_of_mul_le_mul_right (powScale_snd_pos mDiff tb) (Nat.le_of_eq hmul)
  have hle2' := nat_le_of_mul_le_mul_right (powScale_snd_pos mDiff tb) (Nat.le_of_eq hmul.symm)
  exact Nat.le_antisymm hle1 hle2'

/-- **Sterbenz's Exact-Subtraction Theorem (`evalFloatArithBaseProto_sub_sterbenz_exact`)**:
for any two finite `f32`/`f64` floats `a` and `b` of the **same sign** (normal or
subnormal, positive or negative) within a factor of `2` (`|b| / 2 ≤ |a| ≤ 2 * |b|`,
expressed in exact rational cross-multiplied form `lden * rnum ≤ 2 * (lnum * rden)`
and `lnum * rden ≤ 2 * (lden * rnum)`), IEEE-754 subtraction `a - b` is **100%
exact** (incurs **zero rounding error** and **never overflows**):
- if `diffInt = 0` (`|a| = |b|`), `a - b = zeroBits f false` (`+0.0`);
- if `diffInt ≠ 0`, `a - b` decodes to `.finite (decide (diffInt < 0)) diffN diffD`
  whose exact rational value `diffN / diffD` equals `|a - b|`! -/
theorem evalFloatArithBaseProto_sub_sterbenz_exact (f : IeeeFormat) (a b : Nat)
    (sign : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite sign lnum lden)
    (hr : decodeBits f b = .finite sign rnum rden)
    (hlo : lden * rnum ≤ 2 * (lnum * rden))
    (hhi : lnum * rden ≤ 2 * (lden * rnum)) :
    let diffInt := signedNum sign lnum * Int.ofNat rden - signedNum sign rnum * Int.ofNat lden
    (diffInt = 0 → evalFloatArithBaseProto .sub f a b = zeroBits f false) ∧
    (diffInt ≠ 0 →
      ∃ diffN diffD,
        decodeBits f (evalFloatArithBaseProto .sub f a b) =
          .finite (decide (diffInt < 0)) diffN diffD ∧
        diffN * (lden * rden) = diffInt.natAbs * diffD ∧
        0 < diffD) := by
  have hsub := evalFloatArithBaseProto_sub_finite f a b sign sign lnum lden rnum rden hl hr
  have hden_pos : 0 < lden * rden :=
    Nat.mul_pos (decodeBits_finite_den_pos f a sign lnum lden hl)
      (decodeBits_finite_den_pos f b sign rnum rden hr)
  dsimp only at hsub ⊢
  constructor
  · intro h0
    rw [hsub, h0]
    unfold roundRatioTiesToEven
    rw [if_neg' (Nat.ne_of_gt hden_pos)]
    rfl
  · intro hnz
    rw [hsub]
    let diffInt := signedNum sign lnum * Int.ofNat rden - signedNum sign rnum * Int.ofNat lden
    let X : Nat := lnum * rden
    let Y : Nat := lden * rnum
    have hdiff_eq : diffInt =
        if sign then (Y : Int) - (X : Int) else (X : Int) - (Y : Int) := by
      dsimp only [diffInt, signedNum, X, Y]
      have hcomm : Int.ofNat rnum * Int.ofNat lden = ((lden * rnum : Nat) : Int) := by
        rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast, ← Int.natCast_mul, Nat.mul_comm]
      have hlprod : Int.ofNat lnum * Int.ofNat rden = ((lnum * rden : Nat) : Int) := by
        rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast, ← Int.natCast_mul]
      cases sign
      · simp only [Bool.false_eq_true, ↓reduceIte, hlprod, hcomm]
      · simp only [↓reduceIte, Int.neg_mul, hlprod, hcomm]
        generalize (lnum * rden : Nat) = x, (lden * rnum : Nat) = y
        omega
    by_cases hgt : lden * rnum < lnum * rden
    · have hgtXY : Y < X := hgt
      have hnatAbs : diffInt.natAbs = X - Y := by
        rw [hdiff_eq]
        generalize (X : Nat) = x, (Y : Nat) = y at hgtXY ⊢
        cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
      rw [hnatAbs]
      exact sterbenz_ordered_magnitude f sign (decide (diffInt < 0))
        a b lnum lden rnum rden hl hr hgt hhi
    · have hleXY : X ≤ Y := Nat.le_of_not_lt hgt
      have hlt : lnum * rden < lden * rnum := by
        change diffInt ≠ 0 at hnz
        rw [hdiff_eq] at hnz
        show X < Y
        generalize (X : Nat) = x, (Y : Nat) = y at hleXY hnz ⊢
        cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte] at hnz <;> omega
      have hltXY : X < Y := hlt
      have hnatAbs : diffInt.natAbs = rnum * lden - rden * lnum := by
        rw [Nat.mul_comm rnum lden, Nat.mul_comm rden lnum, hdiff_eq]
        show (if sign then (Y : Int) - (X : Int) else (X : Int) - (Y : Int)).natAbs = Y - X
        generalize (X : Nat) = x, (Y : Nat) = y at hltXY ⊢
        cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
      have hlt_swap : rden * lnum < rnum * lden := by
        rw [Nat.mul_comm rden lnum, Nat.mul_comm rnum lden]; exact hlt
      have hle2_swap : rnum * lden ≤ 2 * (rden * lnum) := by
        rw [Nat.mul_comm rnum lden, Nat.mul_comm rden lnum]; exact hlo
      rw [hnatAbs, Nat.mul_comm lden rden]
      obtain ⟨diffN, diffD, hdec, hcross, hDpos⟩ :=
        sterbenz_ordered_magnitude f sign (decide (diffInt < 0))
          b a rnum rden lnum lden hr hl hlt_swap hle2_swap
      exact ⟨diffN, diffD, hdec, hcross, hDpos⟩

/-- **Strict determinism of `EvalRvalueFloatRelProto` on all unary operations**:
for every `UnOp` (including float `.neg` on signaling/quiet NaNs) and both
`FloatArithMode`s, `EvalRvalueFloatRelProto` coincides identically with
`res = evalRvalueFloatProto …`. -/
theorem EvalRvalueFloatRelProto.unaryOp_iff
    (mode : FloatArithMode) (u : UnOp) (op : Operand)
    (locals : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (res : RvalueEvalResult) :
    EvalRvalueFloatRelProto mode locals (.unaryOp u op) mem localDecls layouts res ↔
      res = evalRvalueFloatProto locals (.unaryOp u op) mem localDecls layouts :=
  Iff.rfl

/-- **Strict determinism of `EvalRvalueFloatRelProto` on all non-arithmetic
binary operations (including all 6 IEEE-754 comparisons `eq`, `ne`, `lt`, `le`,
`gt`, `ge`)**: whenever `isFloatArithBinOp op = false`, `EvalRvalueFloatRelProto`
is completely independent of `FloatArithMode` — even on signaling or quiet NaN
operands — and coincides identically with `res = evalRvalueFloatProto …`. -/
theorem EvalRvalueFloatRelProto.nonArith_binOp_iff
    (mode : FloatArithMode) (op : BinOp) (lhsOp rhsOp : Operand)
    (locals : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (res : RvalueEvalResult)
    (hnarith : isFloatArithBinOp op = false) :
    EvalRvalueFloatRelProto mode locals (.binaryOp op lhsOp rhsOp) mem localDecls layouts res ↔
      res = evalRvalueFloatProto locals (.binaryOp op lhsOp rhsOp) mem localDecls layouts := by
  unfold EvalRvalueFloatRelProto
  dsimp only
  cases floatTyOf? (operandTy localDecls layouts lhsOp) with
  | none => exact Iff.rfl
  | some lhsFk =>
    cases floatTyOf? (operandTy localDecls layouts rhsOp) with
    | none => exact Iff.rfl
    | some rhsFk =>
      dsimp only
      cases evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals
          localDecls mem.callStack with
      | ub | unsupported => exact Iff.rfl
      | ok lv locals₁ =>
        cases lv with
        | unit | ptr _ _ | aggregate _ _ => exact Iff.rfl
        | scalar lhsSc =>
          dsimp only
          cases evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals
              localDecls mem.callStack with
          | ub | unsupported => exact Iff.rfl
          | ok rvVal locals₂ =>
            cases rvVal with
            | unit | ptr _ _ | aggregate _ _ => exact Iff.rfl
            | scalar rhsSc =>
              dsimp only
              cases ieeeFormatOfFloatTy? lhsFk with
              | none => exact Iff.rfl
              | some fmtL =>
                cases ieeeFormatOfFloatTy? rhsFk with
                | none => exact Iff.rfl
                | some fmtR =>
                  dsimp only
                  have hfalse : ¬ ((fmtL == fmtR && Nat.beq lhsSc.sizeBytes fmtL.byteWidth &&
                      Nat.beq rhsSc.sizeBytes fmtL.byteWidth && isFloatArithBinOp op) = true) := by
                    rw [hnarith, Bool.and_false]
                    exact Bool.false_ne_true
                  rw [if_neg' hfalse]

/-- **Relational MIR dispatcher comparison laws (`gt = swap lt`, `ge = swap le`,
`ne = !eq`)**: under **both** `FloatArithMode`s (including `.nondeterministic`
and signaling/quiet NaN operands!), for well-typed `f32`/`f64` scalar operands
whose reads do not mutate `locals`, `EvalRvalueFloatRelProto` satisfies exact
relational `gt`/`lt` swap, `ge`/`le` swap, and `ne`/`!eq` duality! -/
theorem EvalRvalueFloatRelProto.cmp_laws_float
    (mode : FloatArithMode) (locals : List LocalSlot) (lhsOp rhsOp : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (fk : FloatTy) (fmt : IeeeFormat) (lhsSc rhsSc : ScalarVal)
    (res : RvalueEvalResult)
    (hlTy : floatTyOf? (operandTy localDecls layouts lhsOp) = .some fk)
    (hrTy : floatTyOf? (operandTy localDecls layouts rhsOp) = .some fk)
    (hfmt : ieeeFormatOfFloatTy? fk = .some fmt)
    (hwL : Nat.beq lhsSc.sizeBytes fmt.byteWidth = true)
    (hwR : Nat.beq rhsSc.sizeBytes fmt.byteWidth = true)
    (hl : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals
      localDecls mem.callStack = .ok (.scalar lhsSc) locals)
    (hr : evalOperand locals rhsOp mem.borrows mem.globals layouts mem.callerLocals
      localDecls mem.callStack = .ok (.scalar rhsSc) locals) :
    (EvalRvalueFloatRelProto mode locals (.binaryOp .gt lhsOp rhsOp) mem localDecls layouts res ↔
      EvalRvalueFloatRelProto mode locals (.binaryOp .lt rhsOp lhsOp) mem localDecls layouts res) ∧
    (EvalRvalueFloatRelProto mode locals (.binaryOp .ge lhsOp rhsOp) mem localDecls layouts res ↔
      EvalRvalueFloatRelProto mode locals (.binaryOp .le rhsOp lhsOp) mem localDecls layouts res) ∧
    (EvalRvalueFloatRelProto mode locals (.binaryOp .ne lhsOp rhsOp) mem localDecls layouts
      (.ok (.scalar (boolToScalar (!evalFloatCmpProto .eq fmt lhsSc.bits rhsSc.bits))) locals mem)) := by
  have heval_cmp : ∀ (op : BinOp) (b : Bool),
      isFloatArithBinOp op = false →
      ∀ o1 o2 sc1 sc2,
        floatTyOf? (operandTy localDecls layouts o1) = .some fk →
        floatTyOf? (operandTy localDecls layouts o2) = .some fk →
        Nat.beq sc1.sizeBytes fmt.byteWidth = true →
        Nat.beq sc2.sizeBytes fmt.byteWidth = true →
        evalOperand locals o1 mem.borrows mem.globals layouts mem.callerLocals
          localDecls mem.callStack = .ok (.scalar sc1) locals →
        evalOperand locals o2 mem.borrows mem.globals layouts mem.callerLocals
          localDecls mem.callStack = .ok (.scalar sc2) locals →
        evalFloatCmpProto? op fmt sc1.bits sc2.bits = .some b →
        evalRvalueFloatProto locals (.binaryOp op o1 o2) mem localDecls layouts =
          .ok (.scalar (boolToScalar b)) locals mem := by
    intro op b hna o1 o2 sc1 sc2 ho1 ho2 hsc1 hsc2 he1 he2 hcmp
    unfold evalRvalueFloatProto
    dsimp only
    rw [ho1, ho2]; dsimp only
    rw [he1]; dsimp only
    rw [he2]; dsimp only
    rw [hfmt]; dsimp only
    have hcond : (fmt == fmt && Nat.beq sc1.sizeBytes fmt.byteWidth &&
        Nat.beq sc2.sizeBytes fmt.byteWidth) = true := by
      cases fmt <;> simp [hsc1, hsc2]
    rw [if_pos' hcond]
    have hnone : evalFloatArithBaseProto? op fmt sc1.bits sc2.bits = .none := by
      unfold evalFloatArithBaseProto?; rw [if_neg' (by rw [hna]; exact Bool.false_ne_true)]
    rw [hnone]; dsimp only
    rw [hcmp]
  refine ⟨?_, ?_, ?_⟩
  · rw [EvalRvalueFloatRelProto.nonArith_binOp_iff mode .gt lhsOp rhsOp locals mem localDecls layouts res rfl,
        EvalRvalueFloatRelProto.nonArith_binOp_iff mode .lt rhsOp lhsOp locals mem localDecls layouts res rfl,
        heval_cmp .gt (evalFloatCmpProto .gt fmt lhsSc.bits rhsSc.bits) rfl
          lhsOp rhsOp lhsSc rhsSc hlTy hrTy hwL hwR hl hr rfl,
        heval_cmp .lt (evalFloatCmpProto .lt fmt rhsSc.bits lhsSc.bits) rfl
          rhsOp lhsOp rhsSc lhsSc hrTy hlTy hwR hwL hr hl rfl,
        evalFloatCmpProto_gt_eq_lt_swap fmt lhsSc.bits rhsSc.bits]
  · rw [EvalRvalueFloatRelProto.nonArith_binOp_iff mode .ge lhsOp rhsOp locals mem localDecls layouts res rfl,
        EvalRvalueFloatRelProto.nonArith_binOp_iff mode .le rhsOp lhsOp locals mem localDecls layouts res rfl,
        heval_cmp .ge (evalFloatCmpProto .ge fmt lhsSc.bits rhsSc.bits) rfl
          lhsOp rhsOp lhsSc rhsSc hlTy hrTy hwL hwR hl hr rfl,
        heval_cmp .le (evalFloatCmpProto .le fmt rhsSc.bits lhsSc.bits) rfl
          rhsOp lhsOp rhsSc lhsSc hrTy hlTy hwR hwL hr hl rfl,
        evalFloatCmpProto_ge_eq_le_swap fmt lhsSc.bits rhsSc.bits]
  · rw [EvalRvalueFloatRelProto.nonArith_binOp_iff mode .ne lhsOp rhsOp locals mem localDecls layouts _ rfl,
        heval_cmp .ne (evalFloatCmpProto .ne fmt lhsSc.bits rhsSc.bits) rfl
          lhsOp rhsOp lhsSc rhsSc hlTy hrTy hwL hwR hl hr rfl,
        evalFloatCmpProto_ne_eq_not_eq fmt lhsSc.bits rhsSc.bits]

/-! ## §18. Field-Size Precedence & Float Size Fix, Non-Pointer Niche Enums, Multi-Field No-Forgery, Nested Struct Propagation, Conservativity & Unconditional Cast-Level No-Prov Equivalence -/

/-- Whenever a field's `LayoutTable` entry `fl` agrees with
`protoRigidTyKindByteSize fTy.kind` (or the kind has no fixed primitive width,
e.g. `.adt` / non-empty `.tuple`), `protoFieldByteSize` returns `fl.size.bytes`. -/
theorem protoFieldByteSize_eq_layout_of_agree
    (layouts : LayoutTable) (fTy : Ty) (fl : TypeLayout)
    (hlk : LayoutTable.lookup layouts fTy.layoutIdx = .some fl)
    (hagree : ∀ sz, protoRigidTyKindByteSize fTy.kind = .some sz → sz = fl.size.bytes) :
    protoFieldByteSize layouts fTy = .some fl.size.bytes := by
  unfold protoFieldByteSize
  cases hk : protoRigidTyKindByteSize fTy.kind with
  | some sz => rw [hagree sz hk]
  | none => rw [hlk]

/-- **Kernel-checked witness (`by rfl`) of B3's unfixed `layoutIdx := 0` field-size
bug, the missing `.float` arm in `Trusted.Bytes.rigidTyKindByteSize`, and their
repair via `protoFieldByteSize`**:
1. Naive `LayoutTable.lookup` first returns `0` (from `protoUnitLayout` at slot
   `0`) for realistic MIR fields `{ kind := .uint .u64, layoutIdx := 0 }` and
   `{ kind := .float .f64, layoutIdx := 0 }`;
2. `Trusted.Bytes.rigidTyKindByteSize` returns `.none` for `.float .f64` and
   `.array (.float .f32) 4`;
3. `protoFieldByteSize` returns `some 8`, `some 8`, and `some 16` respectively,
   and `decodeAdtRichWithPolicy` / `evalByteCastRichWithPolicy` decode
   `Option<(&u8, u64)>`, `Option<(&u8, f64)>`, and `enum E { A(u32), B(u32) }`
   at **realistic `layoutIdx := 0`** without any out-of-bounds `layoutIdx := 99`
   hack! -/
theorem field_size_lookup_precedence_and_float_witness :
    -- 1. Naive lookup-first collides with `protoUnitLayout` (`size = 0`) at `layoutIdx := 0`
    (match LayoutTable.lookup protoRichExtLayouts 0 with
     | .some fl => Option.some fl.size.bytes
     | .none => .none) = .some 0 ∧
    -- 2. Trusted `rigidTyKindByteSize` lacks `.float` and `[f32; 4]`
    rigidTyKindByteSize (.float .f64) = .none ∧
    rigidTyKindByteSize (.array (.float .f32) 4) = .none ∧
    -- 3. `protoFieldByteSize` resolves `u64`, `f64`, and `[f32; 4]` at `layoutIdx := 0`
    protoFieldByteSize protoRichExtLayouts { kind := .uint .u64, layoutIdx := 0 } = .some 8 ∧
    protoFieldByteSize protoRichExtLayouts { kind := .float .f64, layoutIdx := 0 } = .some 8 ∧
    protoFieldByteSize protoRichExtLayouts { kind := .array (.float .f32) 4, layoutIdx := 0 } =
      .some 16 ∧
    -- 4. Realistic `layoutIdx := 0` works end-to-end on `Option<(&u8, u64)>`, `Option<(&u8, f64)>`,
    --    and cast-level `enum E { A(u32), B(u32) }`!
    decodeAdtRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichExtLayouts)
        protoRichExtLayouts protoNicheWide16Layout
        (.nichePointerEnum { bytes := 0 } 8 0 1
          [{ bytes := 0 }, { bytes := 8 }] [protoRefTy, { kind := .uint .u64, layoutIdx := 0 }])
        (appendAbstractBytes protoOffsetZeroRefBytes (encodeLittleEndianBytes 42 8 .none)) =
      .some (.aggregate 1 [.ptr { allocId := 7, offsetBytes := 0 } 8, .scalar ⟨42, 8⟩]) ∧
    decodeAdtRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichExtLayouts)
        protoRichExtLayouts protoNicheWide16Layout
        (.nichePointerEnum { bytes := 0 } 8 0 1
          [{ bytes := 0 }, { bytes := 8 }] [protoRefTy, { kind := .float .f64, layoutIdx := 0 }])
        (appendAbstractBytes protoOffsetZeroRefBytes
          (encodeLittleEndianBytes 0x3FF0000000000000 8 .none)) =
      .some (.aggregate 1 [.ptr { allocId := 7, offsetBytes := 0 } 8,
        .scalar ⟨0x3FF0000000000000, 8⟩]) ∧
    evalByteCastRichWithPolicy .stripProvenance
        [(1, .taggedEnum (.initialized (.int 32 false) ⟨0, 1⟩) 0
          [.arbitrary [{ bytes := 4 }] [0], .arbitrary [{ bytes := 4 }] [0]]
          [[{ kind := .uint .u32, layoutIdx := 0 }], [{ kind := .uint .u32, layoutIdx := 0 }]])]
        protoEnumLocals (.copy ⟨0, []⟩) protoTwoVariantEnumTy emptyMemory
        protoEnumDecls protoEnumLayouts =
      .ok (.aggregate 1 [.scalar ⟨42, 4⟩]) protoEnumLocals emptyMemory := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 8-byte spliced partial-provenance zero image (byte `0` carries provenance
`(7, 7)`, bytes `1..7` carry `.none`): `abstractBytesHaveProv = true`,
`abstractBytesUniformProv = false`, `bits = 0`. -/
def protoSplicedZeroBytes : List AbstractByte :=
  AbstractByte.init (UInt8.ofNat 0) (.some (7, 7)) :: encodeLittleEndianBytes 0 7 .none

/-- `Option<NonZeroU64>` 8-byte scalar niche layout (`nicheValue = 0`). -/
def protoOptionNonZeroU64Layout : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 8 }
  backendRepr := .scalar (.initialized (.int 64 false) ⟨0, scalarModulus 8 - 1⟩)
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .multiple (.initialized (.int 64 false) ⟨0, scalarModulus 8 - 1⟩) 0
    [.arbitrary [] [], .arbitrary [{ bytes := 0 }] [0]]
  isUninhabited := false
}

/-- `NonZeroU64` 8-byte scalar layout (`WrappingRange ⟨1, 2^64 - 1⟩`). -/
def protoNonZeroU64Layout : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 8 }
  backendRepr := .scalar (.initialized (.int 64 false) ⟨1, scalarModulus 8 - 1⟩)
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

/-- `Option<bool>` 1-byte scalar niche layout (`0 ↦ Some(false)`, `1 ↦ Some(true)`,
`2 ↦ None`, `≥ 3 ↦ UB`). -/
def protoOptionBoolLayout : TypeLayout := {
  size := { bytes := 1 }
  align := { bytes := 1 }
  backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 2⟩)
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .multiple (.initialized (.int 8 false) ⟨0, 2⟩) 0
    [.arbitrary [] [], .arbitrary [{ bytes := 0 }] [0]]
  isUninhabited := false
}

/-- Unregistered outer struct `struct Outer { opt: Option<&u8> }` whose
`fieldLayouts := [4]` points to `Option<&u8>` (`protoNicheOptionRefLayout`). -/
def protoOuterStructOptRefLayout : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 8 }
  backendRepr := .scalar (.initialized (.pointer 0) ⟨0, scalarModulus 8 - 1⟩)
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .single 0
  fieldLayouts := [4]
  isUninhabited := false
}

def protoRichExt2Layouts : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries := [
    protoUnitLayout,              -- 0
    protoNonNullPtrFieldLayout,   -- 1
    protoWrapRefLayout,           -- 2
    protoRefPayloadEnumLayout,    -- 3
    protoNicheOptionRefLayout,    -- 4
    protoWideSliceEnumLayout,     -- 5
    protoWideSliceRefLayout,      -- 6
    protoU32FieldLayout,          -- 7
    protoU32PairStructLayout,     -- 8
    protoNicheWide16Layout,       -- 9
    protoOptionRefArray2Layout,   -- 10
    protoNonZeroU64Layout,        -- 11
    protoOptionNonZeroU64Layout,  -- 12
    protoOptionBoolLayout,        -- 13
    protoOuterStructOptRefLayout  -- 14
  ]
}

def protoNonZeroU64Ty : Ty := { kind := .adt "core::num::NonZeroU64" [], layoutIdx := 11 }
def protoOuterStructOptRefTy : Ty := { kind := .adt "OuterOptRef" [], layoutIdx := 14 }

/-- **Kernel-checked witness (`by rfl`) of B3's niche-decoder contradiction and
missing non-pointer niche enums (`Option<NonZeroU64>`, `Option<bool>`)**:
1. On `protoSplicedZeroBytes` under `.stripProvenance`, B3's two niche decoders
   **disagree**: `decodeNichePointerEnumProvAware` returns `.none` while
   `decodeAdtRichWithPolicy .nichePointerEnum` returns `.some (.aggregate 0 [])`
   (`Option::None`);
2. On `Option<NonZeroU64>` with `protoOffsetZeroRefBytes`, `.nichePointerEnum`
   returns `.none` even under `.stripProvenance` (wrongly forcing the dataful
   `NonZeroU64` branch on `0`!), whereas `.nicheScalarEnum` (`nicheValue := 0`)
   flips cleanly between **`.none` under `.strictUcg630Ub`** and
   **`.some (.aggregate 0 [])` (`None`) under `.stripProvenance`**, and decodes
   `42` with provenance `(7, 7)` as `.none` (strict) vs `Some(42)` (strip);
3. On `Option<bool>` via `.nicheScalarEnum` (`nicheValue := 2`): `0 ↦ Some(false)`,
   `1 ↦ Some(true)`, `2 ↦ None`, `3 ↦ .none`, and provenance-carrying `2` flips
   between `.none` (strict) and `None` (strip)! -/
theorem b3_niche_contradiction_and_nonptr_niche_witness :
    -- 1. Contradiction between B3's own two niche decoders on spliced zero bytes under `.stripProvenance`
    decodeNichePointerEnumProvAware
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoRichExt2Layouts)
        protoNicheOptionRefLayout 0 1 protoRefTy protoSplicedZeroBytes = .none ∧
    decodeAdtRichWithPolicy .stripProvenance
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoRichExt2Layouts)
        protoRichExt2Layouts protoNicheOptionRefLayout
        (.nichePointerEnum { bytes := 0 } 8 0 1 [{ bytes := 0 }] [protoRefTy])
        protoSplicedZeroBytes = .some (.aggregate 0 []) ∧
    -- 2. `.nichePointerEnum` mishandles `Option<NonZeroU64>` on `protoOffsetZeroRefBytes` under strip,
    --    whereas `.nicheScalarEnum` flips strict `.none` vs strip `None` (and flips `42` with prov)!
    decodeAdtRichWithPolicy .stripProvenance
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoRichExt2Layouts)
        protoRichExt2Layouts protoOptionNonZeroU64Layout
        (.nichePointerEnum { bytes := 0 } 8 0 1 [{ bytes := 0 }] [protoNonZeroU64Ty])
        protoOffsetZeroRefBytes = .none ∧
    decodeAdtRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichExt2Layouts)
        protoRichExt2Layouts protoOptionNonZeroU64Layout
        (.nicheScalarEnum { bytes := 0 } 8 0 0 1 [{ bytes := 0 }] [protoNonZeroU64Ty])
        protoOffsetZeroRefBytes = .none ∧
    decodeAdtRichWithPolicy .stripProvenance
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoRichExt2Layouts)
        protoRichExt2Layouts protoOptionNonZeroU64Layout
        (.nicheScalarEnum { bytes := 0 } 8 0 0 1 [{ bytes := 0 }] [protoNonZeroU64Ty])
        protoOffsetZeroRefBytes = .some (.aggregate 0 []) ∧
    decodeAdtRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichExt2Layouts)
        protoRichExt2Layouts protoOptionNonZeroU64Layout
        (.nicheScalarEnum { bytes := 0 } 8 0 0 1 [{ bytes := 0 }] [protoNonZeroU64Ty])
        (encodeLittleEndianBytes 42 8 (.some (7, 7))) = .none ∧
    decodeAdtRichWithPolicy .stripProvenance
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoRichExt2Layouts)
        protoRichExt2Layouts protoOptionNonZeroU64Layout
        (.nicheScalarEnum { bytes := 0 } 8 0 0 1 [{ bytes := 0 }] [protoNonZeroU64Ty])
        (encodeLittleEndianBytes 42 8 (.some (7, 7))) =
      .some (.aggregate 1 [.scalar ⟨42, 8⟩]) ∧
    -- 3. `Option<bool>` (`nicheValue := 2`): `0 ↦ Some(false)`, `1 ↦ Some(true)`, `2 ↦ None`,
    --    `3 ↦ .none`, and provenance-carrying `2` flips strict `.none` vs strip `None`!
    decodeAdtRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichExt2Layouts)
        protoRichExt2Layouts protoOptionBoolLayout
        (.nicheScalarEnum { bytes := 0 } 1 2 0 1 [{ bytes := 0 }] [{ kind := .bool, layoutIdx := 0 }])
        (encodeLittleEndianBytes 0 1 .none) = .some (.aggregate 1 [.scalar ⟨0, 1⟩]) ∧
    decodeAdtRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichExt2Layouts)
        protoRichExt2Layouts protoOptionBoolLayout
        (.nicheScalarEnum { bytes := 0 } 1 2 0 1 [{ bytes := 0 }] [{ kind := .bool, layoutIdx := 0 }])
        (encodeLittleEndianBytes 1 1 .none) = .some (.aggregate 1 [.scalar ⟨1, 1⟩]) ∧
    decodeAdtRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichExt2Layouts)
        protoRichExt2Layouts protoOptionBoolLayout
        (.nicheScalarEnum { bytes := 0 } 1 2 0 1 [{ bytes := 0 }] [{ kind := .bool, layoutIdx := 0 }])
        (encodeLittleEndianBytes 2 1 .none) = .some (.aggregate 0 []) ∧
    decodeAdtRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichExt2Layouts)
        protoRichExt2Layouts protoOptionBoolLayout
        (.nicheScalarEnum { bytes := 0 } 1 2 0 1 [{ bytes := 0 }] [{ kind := .bool, layoutIdx := 0 }])
        (encodeLittleEndianBytes 3 1 .none) = .none ∧
    decodeAdtRichWithPolicy .strictUcg630Ub
        (decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoRichExt2Layouts)
        protoRichExt2Layouts protoOptionBoolLayout
        (.nicheScalarEnum { bytes := 0 } 1 2 0 1 [{ bytes := 0 }] [{ kind := .bool, layoutIdx := 0 }])
        (encodeLittleEndianBytes 2 1 (.some (7, 7))) = .none ∧
    decodeAdtRichWithPolicy .stripProvenance
        (decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoRichExt2Layouts)
        protoRichExt2Layouts protoOptionBoolLayout
        (.nicheScalarEnum { bytes := 0 } 1 2 0 1 [{ bytes := 0 }] [{ kind := .bool, layoutIdx := 0 }])
        (encodeLittleEndianBytes 2 1 (.some (7, 7))) = .some (.aggregate 0 []) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem decodeFieldsByTysWithPolicy_none_of_ref_member_no_prov
    (decodeChild : Ty → List AbstractByte → Option Value)
    (layouts : LayoutTable) (bytes : List AbstractByte)
    (offsets : List Size) (fTys : List Ty)
    (hnp : abstractBytesHaveProv bytes = false)
    (hRefNone : ∀ (m : Mutability) (pointee : RigidTy) (lIdx : LayoutIdx) (bs : List AbstractByte),
      abstractBytesHaveProv bs = false →
      decodeChild { kind := .ref m pointee, layoutIdx := lIdx } bs = .none)
    (hmem : ∃ m pointee lIdx, { kind := .ref m pointee, layoutIdx := lIdx } ∈ fTys) :
    decodeFieldsByTysWithPolicy decodeChild layouts bytes offsets fTys = .none := by
  induction offsets generalizing fTys with
  | nil =>
    cases fTys with
    | nil => obtain ⟨_, _, _, hm⟩ := hmem; cases hm
    | cons _ _ => rfl
  | cons off offRest ih =>
    cases fTys with
    | nil => rfl
    | cons fTy tyRest =>
      unfold decodeFieldsByTysWithPolicy
      cases hsz : protoFieldByteSize layouts fTy with
      | none => rfl
      | some fSz =>
        dsimp only
        cases hsl : sliceAbstractBytes bytes off.bytes fSz with
        | none => rfl
        | some fSlice =>
          dsimp only
          obtain ⟨m, pointee, lIdx, hm⟩ := hmem
          cases hm with
          | head =>
            rw [hRefNone m pointee lIdx fSlice
              (abstractBytesHaveProv_slice bytes fSlice off.bytes fSz hnp hsl)]
          | tail _ htail =>
            cases decodeChild fTy fSlice with
            | none => rfl
            | some _ =>
              rw [ih tyRest ⟨m, pointee, lIdx, htail⟩]

/-- **Multi-field no-forgery theorem for `decodeAdtRichWithPolicy .nichePointerEnum`**:
for **every** `Option<&T>`, `Option<&[T]>`, or multi-field `Option<(&T, U, ...)>`
whose `dataFieldTys` contains at least one `.ref m pointee` field, provenance-free
bytes NEVER decode to the dataful variant `.aggregate dataVariant vals` under
**either** policy (closing the gap where B3 proved no-forgery only for single-field
`decodeNichePointerEnumProvAware`)! -/
theorem decodeAdtRichWithPolicy_nichePointer_ref_no_forge
    (policy : Ptr2IntTransmutePolicy) (fuel : Nat) (layouts : LayoutTable)
    (l : TypeLayout) (nicheOffset : Size) (nicheBytes nicheVariant dataVariant : Nat)
    (dataOffsets : List Size) (dataFieldTys : List Ty)
    (bytes : List AbstractByte) (vals : List Value)
    (hnp : abstractBytesHaveProv bytes = false)
    (hne : dataVariant ≠ nicheVariant)
    (hmem : ∃ m pointee lIdx, { kind := .ref m pointee, layoutIdx := lIdx } ∈ dataFieldTys) :
    decodeAdtRichWithPolicy policy
        (decodeTypedValueFromBytesWithPolicy policy (.succ fuel) layouts)
        layouts l
        (.nichePointerEnum nicheOffset nicheBytes nicheVariant dataVariant dataOffsets dataFieldTys)
        bytes ≠
      .some (.aggregate dataVariant vals) := by
  intro h
  have hfieldsNone :
      decodeFieldsByTysWithPolicy
          (decodeTypedValueFromBytesWithPolicy policy (.succ fuel) layouts)
          layouts bytes dataOffsets dataFieldTys = .none :=
    decodeFieldsByTysWithPolicy_none_of_ref_member_no_prov _ layouts bytes dataOffsets dataFieldTys
      hnp (fun m pointee lIdx bs hbs =>
        decodeTypedValueFromBytesWithPolicy_no_forge_ref policy fuel layouts m pointee lIdx bs hbs)
      hmem
  unfold decodeAdtRichWithPolicy at h
  cases hu : Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => rw [hu] at h; cases h
  | false =>
    rw [hu] at h; dsimp only at h
    cases hsl : sliceAbstractBytes bytes nicheOffset.bytes nicheBytes with
    | none => rw [hsl] at h; cases h
    | some nicheSlice =>
      rw [hsl] at h; dsimp only at h
      cases hsc : decodeScalarBytes nicheSlice false with
      | none => rw [hsc] at h; cases h
      | some p =>
        rw [hsc] at h; dsimp only at h
        cases hup : abstractBytesUniformProv nicheSlice with
        | true =>
          rw [hup, hfieldsNone] at h; cases h
        | false =>
          rw [hup] at h; dsimp only at h
          cases hz : Nat.beq p.1.bits 0 with
          | true =>
            rw [hz] at h; dsimp only at h
            cases hp : policyRejectsProv policy nicheSlice with
            | true => rw [hp] at h; cases h
            | false =>
              rw [hp] at h
              injection h with hval
              injection hval with hv _
              exact hne hv.symm
          | false =>
            rw [hz, hfieldsNone] at h; cases h

/-- **Nested unregistered-struct `richSpecs` propagation witness (`by rfl`)**:
`struct OuterOptRef { opt: Option<&u8> }` is NOT registered in `protoRichExtSpecs`
(only its inner field `Option<&u8>` at `layoutIdx := 4` is). With the A3 fix to
`decodeTypedValueRichWithPolicy`, `OuterOptRef` preserves `richSpecs` into `opt`:
- `OuterOptRef { opt: Some(&x_at_offset_0) }` decodes with intact `Value.ptr`
  under **both** policies (whereas trusted `decodeTypedValueFromBytes` degrades
  it to `.scalar`);
- `OuterOptRef { opt: None }` decodes cleanly under **both** policies;
- `OuterOptRef { opt: forged_0x1000 }` is rejected (`.none`) under **both** policies! -/
theorem decodeTypedValueRichWithPolicy_nested_unregistered_struct_witness :
    decodeTypedValueRichWithPolicy .strictUcg630Ub 4 protoRichExt2Layouts protoRichExtSpecs
        protoOuterStructOptRefTy protoOffsetZeroRefBytes =
      .some (.aggregate 0 [.aggregate 1 [.ptr { allocId := 7, offsetBytes := 0 } 8]]) ∧
    decodeTypedValueRichWithPolicy .stripProvenance 4 protoRichExt2Layouts protoRichExtSpecs
        protoOuterStructOptRefTy protoOffsetZeroRefBytes =
      .some (.aggregate 0 [.aggregate 1 [.ptr { allocId := 7, offsetBytes := 0 } 8]]) ∧
    decodeTypedValueRichWithPolicy .strictUcg630Ub 4 protoRichExt2Layouts protoRichExtSpecs
        protoOuterStructOptRefTy (encodeLittleEndianBytes 0 8 .none) =
      .some (.aggregate 0 [.aggregate 0 []]) ∧
    decodeTypedValueRichWithPolicy .strictUcg630Ub 4 protoRichExt2Layouts protoRichExtSpecs
        protoOuterStructOptRefTy (encodeLittleEndianBytes 0x1000 8 .none) = .none ∧
    decodeTypedValueRichWithPolicy .stripProvenance 4 protoRichExt2Layouts protoRichExtSpecs
        protoOuterStructOptRefTy (encodeLittleEndianBytes 0x1000 8 .none) = .none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem decodeFieldsByTysWithPolicy_eq_decodeFieldsByLayoutIdxs
    (cTy : Ty → List AbstractByte → Option Value)
    (cIdx : Nat → List AbstractByte → Option Value)
    (layouts : LayoutTable) (bytes : List AbstractByte)
    (offsets : List Size) (fTys : List Ty) (fls : List Nat)
    (hlen : length fTys = length fls)
    (hmatch : ∀ (i : Nat) (fTy : Ty) (fIdx : Nat),
      get? fTys i = .some fTy → get? fls i = .some fIdx →
      (∃ fl, LayoutTable.lookup layouts fIdx = .some fl ∧
        protoFieldByteSize layouts fTy = .some fl.size.bytes) ∧
      (∀ bs, cTy fTy bs = cIdx fIdx bs)) :
    decodeFieldsByTysWithPolicy cTy layouts bytes offsets fTys =
      decodeFieldsByLayoutIdxs cIdx layouts bytes offsets fls := by
  induction offsets generalizing fTys fls with
  | nil =>
    cases fTys with
    | nil =>
      cases fls with
      | nil => rfl
      | cons _ _ => cases hlen
    | cons _ _ =>
      cases fls with
      | nil => cases hlen
      | cons _ _ => rfl
  | cons off offRest ih =>
    cases fTys with
    | nil =>
      cases fls with
      | nil => rfl
      | cons _ _ => cases hlen
    | cons fTy tyRest =>
      cases fls with
      | nil => cases hlen
      | cons fIdx flRest =>
        unfold decodeFieldsByTysWithPolicy decodeFieldsByLayoutIdxs
        obtain ⟨⟨fl, hlk, hsz⟩, hdec⟩ := hmatch 0 fTy fIdx rfl rfl
        rw [hsz, hlk]
        dsimp only
        cases hsl : sliceAbstractBytes bytes off.bytes fl.size.bytes with
        | none => rfl
        | some fSlice =>
          dsimp only
          rw [hdec fSlice]
          cases cIdx fIdx fSlice with
          | none => rfl
          | some fv =>
            dsimp only
            have hlen' : length tyRest = length flRest := Nat.succ.inj hlen
            rw [ih tyRest flRest hlen' (fun i t idx ht hi => hmatch (.succ i) t idx ht hi)]
            cases decodeFieldsByLayoutIdxs cIdx layouts bytes offRest flRest <;> rfl

/-- **Conservativity of `decodeTypedValueRichWithPolicy` vs
`decodeTypedValueFromBytesWithPolicy` on single-variant scalar structs**:
whenever `richSpecs` registers a single-variant struct layout `l` as
`.structFields variantIdx offsets fieldTys` matching `l.variants`, `l.fields`,
and `l.fieldLayouts` (non-empty) such that every field's `protoFieldByteSize`
and child decoding match the legacy `LayoutIdx` decoder (e.g. non-pointer scalar
fields `u32`, `i64`, `f32`, `NonZeroU32`), `decodeTypedValueRichWithPolicy`
returns the **exact identical** `Option Value` as `decodeTypedValueFromBytesWithPolicy`
(and hence trusted `decodeTypedValueFromBytes` at `.strictUcg630Ub`) on **every**
byte image `bytes`! -/
theorem decodeTypedValueRichWithPolicy_scalarStruct_eq_trusted
    (policy : Ptr2IntTransmutePolicy) (fuel : Nat) (layouts : LayoutTable)
    (specHd : LayoutIdx × RichAdtSpec) (specTl : List (LayoutIdx × RichAdtSpec))
    (defPath : DefPath) (args : List RigidTy) (layoutIdx : LayoutIdx)
    (l : TypeLayout) (variantIdx : Nat) (off0 : Size) (offRest : List Size)
    (memOrder : List Nat) (fieldTys : List Ty) (bytes : List AbstractByte)
    (hlk : LayoutTable.lookup layouts layoutIdx = .some l)
    (hsp : lookupRichAdtSpec (specHd :: specTl) layoutIdx =
      .some (.structFields variantIdx (off0 :: offRest) fieldTys))
    (hvar : l.variants = .single variantIdx)
    (hfld : l.fields = .arbitrary (off0 :: offRest) memOrder)
    (hlenFl : Nat.beq (length l.fieldLayouts) (length (off0 :: offRest)) = true)
    (hlenTy : length fieldTys = length l.fieldLayouts)
    (hfields : ∀ (i : Nat) (fTy : Ty) (fIdx : Nat),
      get? fieldTys i = .some fTy → get? l.fieldLayouts i = .some fIdx →
      (∃ fl, LayoutTable.lookup layouts fIdx = .some fl ∧
        protoFieldByteSize layouts fTy = .some fl.size.bytes) ∧
      (∀ bs,
        decodeTypedValueRichWithPolicy policy fuel layouts (specHd :: specTl) fTy bs =
          decodeTypedValueFromBytesWithPolicy policy fuel layouts
            { kind := .adt "" .nil, layoutIdx := fIdx } bs)) :
    decodeTypedValueRichWithPolicy policy (.succ fuel) layouts (specHd :: specTl)
        { kind := .adt defPath args, layoutIdx := layoutIdx } bytes =
      decodeTypedValueFromBytesWithPolicy policy (.succ fuel) layouts
        { kind := .adt defPath args, layoutIdx := layoutIdx } bytes := by
  unfold decodeTypedValueRichWithPolicy decodeTypedValueFromBytesWithPolicy
  dsimp only [normalizeCodecTy]
  rw [hlk, hsp]
  dsimp only
  unfold decodeAdtRichWithPolicy
  cases hu : Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
  | true => rfl
  | false =>
    dsimp only
    rw [hvar, hfld]
    dsimp only
    rw [hlenFl]
    dsimp only
    rw [decodeFieldsByTysWithPolicy_eq_decodeFieldsByLayoutIdxs _ _ layouts bytes
      (off0 :: offRest) fieldTys l.fieldLayouts hlenTy hfields]

/-- With an empty `richSpecs` table, `evalByteCastRichWithPolicy` is identically
`evalByteCastWithPolicy` (and hence at `.strictUcg630Ub` equals trusted
`evalByteCast`). -/
theorem evalByteCastRichWithPolicy_empty_eq
    (policy : Ptr2IntTransmutePolicy) (locals : List LocalSlot) (op : Operand)
    (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalByteCastRichWithPolicy policy .nil locals op targetTy mem localDecls layouts =
      evalByteCastWithPolicy policy locals op targetTy mem localDecls layouts := by
  unfold evalByteCastRichWithPolicy evalByteCastWithPolicy
  cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
  | ub | unsupported => rfl
  | ok v locals' =>
    dsimp only
    cases tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts targetTy) with
    | none => rfl
    | some dstSize =>
      dsimp only
      cases operandTy localDecls layouts op with
      | some srcTy =>
        dsimp only
        cases tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts srcTy) with
        | none => rfl
        | some srcSize =>
          dsimp only
          cases Nat.beq srcSize dstSize with
          | false => rfl
          | true =>
            dsimp only
            cases encodeByteCastSourceBytes layouts (resolveTyWithLocalDecls localDecls layouts srcTy) v with
            | none => rfl
            | some bs =>
              dsimp only
              cases Nat.beq (length bs) dstSize with
              | false => rfl
              | true =>
                dsimp only
                rw [decodeTypedValueRichWithPolicy_empty_eq]
      | none =>
        dsimp only
        cases encodeUntypedValueToBytes defaultCodecFuel v with
        | none => rfl
        | some bs =>
          dsimp only
          cases Nat.beq (length bs) dstSize with
          | false => rfl
          | true =>
            dsimp only
            rw [decodeTypedValueRichWithPolicy_empty_eq]

/-- **Exact cast-level split for `evalByteCastRichWithPolicy`**: for every
`richSpecs`, operand, target type, and machine state, `.stripProvenance` and
`.strictUcg630Ub` return the **exact same `RvalueEvalResult`** (including
`.unsupported`) unless `.strictUcg630Ub` is `.ub`! -/
theorem evalByteCastRichWithPolicy_strip_eq_strict_or_strict_ub
    (richSpecs : List (LayoutIdx × RichAdtSpec))
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalByteCastRichWithPolicy .stripProvenance richSpecs locals op targetTy mem localDecls layouts =
      evalByteCastRichWithPolicy .strictUcg630Ub richSpecs locals op targetTy mem localDecls layouts ∨
    evalByteCastRichWithPolicy .strictUcg630Ub richSpecs locals op targetTy mem localDecls layouts =
      .ub := by
  cases h : evalByteCastRichWithPolicy .strictUcg630Ub richSpecs locals op targetTy mem localDecls layouts with
  | ub => exact Or.inr rfl
  | ok v' locals' mem' =>
    exact Or.inl (evalByteCastRichWithPolicy_strict_refines_strip richSpecs locals op targetTy mem
      localDecls layouts v' locals' mem' h)
  | unsupported =>
    left
    unfold evalByteCastRichWithPolicy at h ⊢
    cases hev : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals
        localDecls mem.callStack with
    | ub => rw [hev] at h; cases h
    | unsupported => rfl
    | ok v loc1 =>
      rw [hev] at h; dsimp only at h ⊢
      cases hdst : tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts targetTy) with
      | none => rfl
      | some dstSize =>
        rw [hdst] at h; dsimp only at h ⊢
        cases hopTy : operandTy localDecls layouts op with
        | some srcTy =>
          rw [hopTy] at h; dsimp only at h ⊢
          cases hsrc : tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts srcTy) with
          | none => rfl
          | some srcSize =>
            rw [hsrc] at h; dsimp only at h ⊢
            cases hsz : Nat.beq srcSize dstSize with
            | false => rfl
            | true =>
              rw [hsz] at h; dsimp only at h ⊢
              cases henc : encodeByteCastSourceBytes layouts
                  (resolveTyWithLocalDecls localDecls layouts srcTy) v with
              | none => rw [henc] at h; cases h
              | some bs =>
                rw [henc] at h; dsimp only at h ⊢
                cases hlen : Nat.beq (length bs) dstSize with
                | false => rw [hlen] at h; cases h
                | true =>
                  rw [hlen] at h; dsimp only at h ⊢
                  cases hdec : decodeTypedValueRichWithPolicy .strictUcg630Ub defaultCodecFuel
                      layouts richSpecs (resolveTyWithLocalDecls localDecls layouts targetTy) bs with
                  | none => rw [hdec] at h; cases h
                  | some _ => rw [hdec] at h; cases h
        | none =>
          rw [hopTy] at h; dsimp only at h ⊢
          cases henc : encodeUntypedValueToBytes defaultCodecFuel v with
          | none => rfl
          | some bs =>
            rw [henc] at h; dsimp only at h ⊢
            cases hlen : Nat.beq (length bs) dstSize with
            | false => rfl
            | true =>
              rw [hlen] at h; dsimp only at h ⊢
              cases hdec : decodeTypedValueRichWithPolicy .strictUcg630Ub defaultCodecFuel
                  layouts richSpecs (resolveTyWithLocalDecls localDecls layouts targetTy) bs with
              | none => rw [hdec] at h; cases h
              | some _ => rw [hdec] at h; cases h

/-! ### §18.1 Unconditional Cast-Level Provenance-Free Equivalence (Covering `encodeByLayoutIdxAux` & Provenance-Free Unions) -/

private theorem abstractBytesHaveProv_mergeMaskedAbstractBytes
    (a b : List AbstractByte) (am bm : List Bool) (res : List AbstractByte × List Bool)
    (ha : abstractBytesHaveProv a = false) (hb : abstractBytesHaveProv b = false)
    (hm : mergeMaskedAbstractBytes a am b bm = .some res) :
    abstractBytesHaveProv res.1 = false := by
  induction a generalizing b am bm res with
  | nil =>
    cases b with
    | nil => unfold mergeMaskedAbstractBytes at hm; injection hm with hr; rw [← hr]
    | cons _ _ => unfold mergeMaskedAbstractBytes at hm; cases hm
  | cons a0 aRest ih =>
    cases b with
    | nil =>
      unfold mergeMaskedAbstractBytes at hm
      injection hm with hr; rw [← hr]; exact ha
    | cons b0 bRest =>
      cases am with
      | nil => unfold mergeMaskedAbstractBytes at hm; cases hm
      | cons am0 amRest =>
        have ha0 : abstractBytesHaveProv [a0] = false ∧ abstractBytesHaveProv aRest = false := by
          cases a0 with
          | uninit => exact ⟨rfl, ha⟩
          | init _ prov =>
            cases prov with
            | none => exact ⟨rfl, ha⟩
            | some _ => cases ha
        have hb0 : abstractBytesHaveProv [b0] = false ∧ abstractBytesHaveProv bRest = false := by
          cases b0 with
          | uninit => exact ⟨rfl, hb⟩
          | init _ prov =>
            cases prov with
            | none => exact ⟨rfl, hb⟩
            | some _ => cases hb
        unfold mergeMaskedAbstractBytes at hm
        dsimp only at hm
        have hstep : ∀ (mRest : List Bool) (effBm : Bool),
            (match mergeMaskedAbstractBytes aRest amRest bRest mRest with
             | none => none
             | some (tailB, tailM) =>
               match (generalizing := false) effBm with
               | false => Option.some (a0 :: tailB, am0 :: tailM)
               | true =>
                 match (generalizing := false) am0 with
                 | false => Option.some (b0 :: tailB, true :: tailM)
                 | true =>
                   match (generalizing := false) abstractByteEq a0 b0 with
                   | true => Option.some (a0 :: tailB, true :: tailM)
                   | false => none) = .some res →
            abstractBytesHaveProv res.1 = false := by
          intro mRest effBm he
          cases hrec : mergeMaskedAbstractBytes aRest amRest bRest mRest with
          | none => rw [hrec] at he; cases he
          | some tail =>
            rw [hrec] at he; dsimp only at he
            have htail := ih bRest amRest mRest tail ha0.2 hb0.2 hrec
            have hconsA : abstractBytesHaveProv (a0 :: tail.1) = false := by
              cases a0 with
              | uninit => exact htail
              | init _ prov =>
                cases prov with
                | none => exact htail
                | some _ => cases ha0.1
            have hconsB : abstractBytesHaveProv (b0 :: tail.1) = false := by
              cases b0 with
              | uninit => exact htail
              | init _ prov =>
                cases prov with
                | none => exact htail
                | some _ => cases hb0.1
            cases effBm with
            | false => injection he with hr; rw [← hr]; exact hconsA
            | true =>
              dsimp only at he
              cases am0 with
              | false => injection he with hr; rw [← hr]; exact hconsB
              | true =>
                dsimp only at he
                cases hab : abstractByteEq a0 b0 with
                | false => rw [hab] at he; cases he
                | true => rw [hab] at he; injection he with hr; rw [← hr]; exact hconsA
        cases bm with
        | nil => dsimp only at hm; exact hstep .nil _ hm
        | cons _ mRest => dsimp only at hm; exact hstep mRest _ hm

private theorem valueListHasProv_splitUnionTypedAndOverlay
    (count : Nat) (fieldVals : List Value) (res : List Value × Option (List Value))
    (hnp : valueListHasProv fieldVals = false)
    (hs : splitUnionTypedAndOverlay count fieldVals = .some res) :
    valueListHasProv res.1 = false ∧
    (∀ rawVals, res.2 = .some rawVals → valueListHasProv rawVals = false) := by
  induction count generalizing fieldVals res with
  | zero =>
    cases fieldVals with
    | nil =>
      injection hs with hr; rw [← hr]
      exact ⟨rfl, fun _ h => by cases h⟩
    | cons v rest =>
      cases rest with
      | cons v2 r2 =>
        have hnone : splitUnionTypedAndOverlay 0 (v :: v2 :: r2) = none := by
          cases v with
          | unit | scalar _ | ptr _ _ => rfl
          | aggregate varIdx _ => cases varIdx <;> rfl
        rw [hnone] at hs; cases hs
      | nil =>
        cases v with
        | unit | scalar _ | ptr _ _ => cases hs
        | aggregate varIdx rawVals =>
          cases varIdx with
          | succ _ => change none = .some res at hs; cases hs
          | zero =>
            change Option.some (List.nil, Option.some rawVals) = .some res at hs
            injection hs with hr; rw [← hr]
            unfold valueListHasProv valueHasProv at hnp
            have hr0 : valueListHasProv rawVals = false := by
              cases hr' : valueListHasProv rawVals with
              | false => rfl
              | true => rw [hr'] at hnp; cases hnp
            exact ⟨rfl, fun rv hrv => by injection hrv with he; rw [← he]; exact hr0⟩
  | succ k ih =>
    cases fieldVals with
    | nil =>
      injection hs with hr; rw [← hr]
      exact ⟨rfl, fun _ h => by cases h⟩
    | cons v rest =>
      unfold valueListHasProv at hnp
      have hv0 : valueHasProv v = false := by
        cases hv : valueHasProv v with
        | false => rfl
        | true => rw [hv] at hnp; cases hnp
      have hr0 : valueListHasProv rest = false := by rw [hv0] at hnp; exact hnp
      unfold splitUnionTypedAndOverlay at hs
      cases hrec : splitUnionTypedAndOverlay k rest with
      | none => rw [hrec] at hs; cases hs
      | some sub =>
        rw [hrec] at hs; dsimp only at hs
        injection hs with hr; rw [← hr]
        obtain ⟨h1, h2⟩ := ih rest sub hr0 hrec
        refine ⟨?_, h2⟩
        unfold valueListHasProv; rw [hv0, h1]; rfl

private theorem abstractBytesHaveProv_overlayRawAbstractByteVals
    (rawVals : List Value) (buf out : List AbstractByte)
    (hnp : valueListHasProv rawVals = false)
    (hbuf : abstractBytesHaveProv buf = false)
    (ho : overlayRawAbstractByteVals rawVals buf = .some out) :
    abstractBytesHaveProv out = false := by
  induction rawVals generalizing buf out with
  | nil => injection ho with h; rw [← h]; exact hbuf
  | cons v vRest ih =>
    unfold valueListHasProv at hnp
    have hv0 : valueHasProv v = false := by
      cases hv : valueHasProv v with
      | false => rfl
      | true => rw [hv] at hnp; cases hnp
    have hr0 : valueListHasProv vRest = false := by rw [hv0] at hnp; exact hnp
    cases buf with
    | nil => cases ho
    | cons b bRest =>
      have hbRest : abstractBytesHaveProv bRest = false := by
        cases b with
        | uninit => exact hbuf
        | init _ prov =>
          cases prov with
          | none => exact hbuf
          | some _ => cases hbuf
      cases v with
      | unit | aggregate _ _ => cases ho
      | ptr _ _ => cases hv0
      | scalar sv =>
        cases sv with
        | mk bits sizeBytes =>
          cases sizeBytes with
          | zero =>
            cases bits with
            | succ _ => change none = .some out at ho; cases ho
            | zero =>
              change (match overlayRawAbstractByteVals vRest bRest with
                | some tail => Option.some (AbstractByte.uninit :: tail)
                | none => none) = .some out at ho
              cases hrec : overlayRawAbstractByteVals vRest bRest with
              | none => rw [hrec] at ho; cases ho
              | some tail =>
                rw [hrec] at ho; injection ho with h; rw [← h]
                exact ih bRest tail hr0 hbRest hrec
          | succ s =>
            cases s with
            | zero =>
              have h1 : overlayRawAbstractByteVals (.scalar ⟨bits, 0 + 1⟩ :: vRest) (b :: bRest) =
                  match overlayRawAbstractByteVals vRest bRest with
                  | some tail => Option.some (AbstractByte.init (UInt8.ofNat bits) none :: tail)
                  | none => none := by
                cases bits <;> rfl
              rw [h1] at ho
              cases hrec : overlayRawAbstractByteVals vRest bRest with
              | none => rw [hrec] at ho; cases ho
              | some tail =>
                rw [hrec] at ho; injection ho with h; rw [← h]
                exact ih bRest tail hr0 hbRest hrec
            | succ k =>
              have h2 : overlayRawAbstractByteVals (.scalar ⟨bits, k + 1 + 1⟩ :: vRest) (b :: bRest) =
                  none := by
                cases bits <;> rfl
              rw [h2] at ho
              cases ho

private theorem abstractBytesHaveProv_mergeUnionTypedSlotsAux
    (layouts : LayoutTable) (encodeSlot : Nat → Value → Option (List AbstractByte))
    (fallbackLayoutIdx : Nat) (hasOverlay : Bool) (unionSize : Nat)
    (flIdxs : List Nat) (fieldVals : List Value)
    (buf out : List AbstractByte) (bufMask : List Bool)
    (henc : ∀ idx v bs, valueHasProv v = false → encodeSlot idx v = .some bs →
      abstractBytesHaveProv bs = false)
    (hnp : valueListHasProv fieldVals = false)
    (hbuf : abstractBytesHaveProv buf = false)
    (hm : mergeUnionTypedSlotsAux layouts encodeSlot fallbackLayoutIdx hasOverlay unionSize
      flIdxs fieldVals buf bufMask = .some out) :
    abstractBytesHaveProv out = false := by
  induction fieldVals generalizing flIdxs buf bufMask out with
  | nil => injection hm with h; rw [← h]; exact hbuf
  | cons fv vRest ih =>
    unfold valueListHasProv at hnp
    have hfv0 : valueHasProv fv = false := by
      cases hf : valueHasProv fv with
      | false => rfl
      | true => rw [hf] at hnp; cases hnp
    have hr0 : valueListHasProv vRest = false := by rw [hfv0] at hnp; exact hnp
    unfold mergeUnionTypedSlotsAux at hm
    dsimp only at hm
    cases fv with
    | unit =>
      exact ih _ buf out bufMask hr0 hbuf hm
    | ptr _ _ => cases hfv0
    | scalar sv =>
      dsimp only at hm
      cases flIdxs with
      | cons flIdx nextIdxs =>
        dsimp only at hm
        cases he : encodeSlot flIdx (.scalar sv) with
        | none => rw [he] at hm; cases hm
        | some fBytes =>
          rw [he] at hm; dsimp only at hm
          cases hmg : mergeMaskedAbstractBytes buf bufMask fBytes (layoutValueMaskAux 8 layouts flIdx) with
          | none => rw [hmg] at hm; cases hm
          | some merged =>
            rw [hmg] at hm; dsimp only at hm
            exact ih nextIdxs merged.1 out merged.2 hr0
              (abstractBytesHaveProv_mergeMaskedAbstractBytes buf fBytes bufMask _ merged
                hbuf (henc flIdx _ fBytes hfv0 he) hmg) hm
      | nil =>
        dsimp only at hm
        cases he : encodeSlot fallbackLayoutIdx (.scalar sv) with
        | none => rw [he] at hm; cases hm
        | some fBytes =>
          rw [he] at hm
          cases fBytes with
          | nil =>
            dsimp only at hm
            cases hcu : valueContainsUnit (.scalar sv) with
            | false => rw [hcu] at hm; exact ih .nil buf out bufMask hr0 hbuf hm
            | true =>
              rw [hcu] at hm; dsimp only at hm
              cases hmg : mergeMaskedAbstractBytes buf bufMask (replicateUninitBytes unionSize)
                  (replicateBool unionSize true) with
              | none => rw [hmg] at hm; cases hm
              | some merged =>
                rw [hmg] at hm; dsimp only at hm
                exact ih .nil merged.1 out merged.2 hr0
                  (abstractBytesHaveProv_mergeMaskedAbstractBytes buf _ bufMask _ merged
                    hbuf (abstractBytesHaveProv_replicateUninitBytes unionSize) hmg) hm
          | cons b0 bRest =>
            dsimp only at hm
            cases hmg : mergeMaskedAbstractBytes buf bufMask (b0 :: bRest)
                (replicateBool (length (b0 :: bRest)) true) with
            | none => rw [hmg] at hm; cases hm
            | some merged =>
              rw [hmg] at hm; dsimp only at hm
              exact ih .nil merged.1 out merged.2 hr0
                (abstractBytesHaveProv_mergeMaskedAbstractBytes buf (b0 :: bRest) bufMask _ merged
                  hbuf (henc fallbackLayoutIdx _ (b0 :: bRest) hfv0 he) hmg) hm
    | aggregate varIdx aggFs =>
      dsimp only at hm
      cases flIdxs with
      | cons flIdx nextIdxs =>
        dsimp only at hm
        cases he : encodeSlot flIdx (.aggregate varIdx aggFs) with
        | none => rw [he] at hm; cases hm
        | some fBytes =>
          rw [he] at hm; dsimp only at hm
          cases hmg : mergeMaskedAbstractBytes buf bufMask fBytes (layoutValueMaskAux 8 layouts flIdx) with
          | none => rw [hmg] at hm; cases hm
          | some merged =>
            rw [hmg] at hm; dsimp only at hm
            exact ih nextIdxs merged.1 out merged.2 hr0
              (abstractBytesHaveProv_mergeMaskedAbstractBytes buf fBytes bufMask _ merged
                hbuf (henc flIdx _ fBytes hfv0 he) hmg) hm
      | nil =>
        dsimp only at hm
        cases hasOverlay with
        | true =>
          cases aggFs with
          | nil =>
            dsimp only at hm
            have hgen : ∀ b : Bool,
                (match b with
                 | false => mergeUnionTypedSlotsAux layouts encodeSlot fallbackLayoutIdx true
                     unionSize .nil vRest buf bufMask
                 | true => none) = .some out →
                abstractBytesHaveProv out = false := by
              intro b hb
              cases b with
              | true => cases hb
              | false => exact ih .nil buf out bufMask hr0 hbuf hb
            exact hgen _ hm
          | cons f0 fTail =>
            dsimp only at hm
            cases heu : encodeUntypedValueToBytes defaultCodecFuel (.aggregate varIdx (f0 :: fTail)) with
            | none => rw [heu] at hm; cases hm
            | some fBytes =>
              rw [heu] at hm
              cases fBytes with
              | nil =>
                dsimp only at hm
                cases hcu : valueContainsUnit (.aggregate varIdx (f0 :: fTail)) with
                | false => rw [hcu] at hm; exact ih .nil buf out bufMask hr0 hbuf hm
                | true =>
                  rw [hcu] at hm; dsimp only at hm
                  cases hmg : mergeMaskedAbstractBytes buf bufMask (replicateUninitBytes unionSize)
                      (replicateBool unionSize true) with
                  | none => rw [hmg] at hm; cases hm
                  | some merged =>
                    rw [hmg] at hm; dsimp only at hm
                    exact ih .nil merged.1 out merged.2 hr0
                      (abstractBytesHaveProv_mergeMaskedAbstractBytes buf _ bufMask _ merged
                        hbuf (abstractBytesHaveProv_replicateUninitBytes unionSize) hmg) hm
              | cons b0 bRest =>
                dsimp only at hm
                cases hsub : abstractByteSubseq (b0 :: bRest) buf with
                | false => rw [hsub] at hm; cases hm
                | true => rw [hsub] at hm; exact ih .nil buf out bufMask hr0 hbuf hm
        | false =>
          have hfallback :
              (match encodeSlot fallbackLayoutIdx (.aggregate varIdx aggFs) with
               | none => none
               | some .nil =>
                 match valueContainsUnit (.aggregate varIdx aggFs) with
                 | false => mergeUnionTypedSlotsAux layouts encodeSlot fallbackLayoutIdx false
                     unionSize .nil vRest buf bufMask
                 | true =>
                   match mergeMaskedAbstractBytes buf bufMask (replicateUninitBytes unionSize)
                       (replicateBool unionSize true) with
                   | none => none
                   | some (buf', bufMask') =>
                     mergeUnionTypedSlotsAux layouts encodeSlot fallbackLayoutIdx false
                       unionSize .nil vRest buf' bufMask'
               | some (b0 :: bRest) =>
                 match mergeMaskedAbstractBytes buf bufMask (b0 :: bRest)
                     (replicateBool (length (b0 :: bRest)) true) with
                 | none => none
                 | some (buf', bufMask') =>
                   mergeUnionTypedSlotsAux layouts encodeSlot fallbackLayoutIdx false
                     unionSize .nil vRest buf' bufMask') = .some out →
              abstractBytesHaveProv out = false := by
            intro hm'
            cases he : encodeSlot fallbackLayoutIdx (.aggregate varIdx aggFs) with
            | none => rw [he] at hm'; cases hm'
            | some fBytes =>
              rw [he] at hm'
              cases fBytes with
              | nil =>
                dsimp only at hm'
                cases hcu : valueContainsUnit (.aggregate varIdx aggFs) with
                | false => rw [hcu] at hm'; exact ih .nil buf out bufMask hr0 hbuf hm'
                | true =>
                  rw [hcu] at hm'; dsimp only at hm'
                  cases hmg : mergeMaskedAbstractBytes buf bufMask (replicateUninitBytes unionSize)
                      (replicateBool unionSize true) with
                  | none => rw [hmg] at hm'; cases hm'
                  | some merged =>
                    rw [hmg] at hm'; dsimp only at hm'
                    exact ih .nil merged.1 out merged.2 hr0
                      (abstractBytesHaveProv_mergeMaskedAbstractBytes buf _ bufMask _ merged
                        hbuf (abstractBytesHaveProv_replicateUninitBytes unionSize) hmg) hm'
              | cons b0 bRest =>
                dsimp only at hm'
                cases hmg : mergeMaskedAbstractBytes buf bufMask (b0 :: bRest)
                    (replicateBool (length (b0 :: bRest)) true) with
                | none => rw [hmg] at hm'; cases hm'
                | some merged =>
                  rw [hmg] at hm'; dsimp only at hm'
                  exact ih .nil merged.1 out merged.2 hr0
                    (abstractBytesHaveProv_mergeMaskedAbstractBytes buf (b0 :: bRest) bufMask _ merged
                      hbuf (henc fallbackLayoutIdx _ (b0 :: bRest) hfv0 he) hmg) hm'
          cases aggFs <;> exact hfallback hm

private theorem abstractBytesHaveProv_encodeArbitrarySlotsIntoBufAux
    (encodeSlot : Nat → Value → Option (List AbstractByte)) (fallbackLayoutIdx : Nat)
    (offsets : List Size) (flIdxs : List Nat) (fieldVals : List Value)
    (buf out : List AbstractByte)
    (henc : ∀ idx v bs, valueHasProv v = false → encodeSlot idx v = .some bs →
      abstractBytesHaveProv bs = false)
    (hnp : valueListHasProv fieldVals = false)
    (hbuf : abstractBytesHaveProv buf = false)
    (he : encodeArbitrarySlotsIntoBufAux encodeSlot fallbackLayoutIdx offsets flIdxs fieldVals buf =
      .some out) :
    abstractBytesHaveProv out = false := by
  induction offsets generalizing flIdxs fieldVals buf out with
  | nil =>
    cases fieldVals with
    | nil => injection he with h; rw [← h]; exact hbuf
    | cons _ _ => cases he
  | cons off offRest ih =>
    cases fieldVals with
    | nil => cases he
    | cons fv vRest =>
      unfold valueListHasProv at hnp
      have hfv0 : valueHasProv fv = false := by
        cases hf : valueHasProv fv with
        | false => rfl
        | true => rw [hf] at hnp; cases hnp
      have hr0 : valueListHasProv vRest = false := by rw [hfv0] at hnp; exact hnp
      unfold encodeArbitrarySlotsIntoBufAux at he
      dsimp only at he
      cases flIdxs with
      | nil =>
        dsimp only at he
        cases hes : encodeSlot fallbackLayoutIdx fv with
        | none => rw [hes] at he; cases he
        | some fBytes =>
          rw [hes] at he; dsimp only at he
          cases hw : writeAbstractBytesAt buf off.bytes fBytes with
          | none => rw [hw] at he; cases he
          | some buf' =>
            rw [hw] at he; dsimp only at he
            exact ih .nil vRest buf' out hr0
              (abstractBytesHaveProv_writeAbstractBytesAt buf fBytes buf' off.bytes
                hbuf (henc fallbackLayoutIdx fv fBytes hfv0 hes) hw) he
      | cons flIdx fRest =>
        dsimp only at he
        cases hes : encodeSlot flIdx fv with
        | none => rw [hes] at he; cases he
        | some fBytes =>
          rw [hes] at he; dsimp only at he
          cases hw : writeAbstractBytesAt buf off.bytes fBytes with
          | none => rw [hw] at he; cases he
          | some buf' =>
            rw [hw] at he; dsimp only at he
            exact ih fRest vRest buf' out hr0
              (abstractBytesHaveProv_writeAbstractBytesAt buf fBytes buf' off.bytes
                hbuf (henc flIdx fv fBytes hfv0 hes) hw) he

private theorem abstractBytesHaveProv_encodeArraySlotsIntoBufAux
    (encodeSlot : Nat → Value → Option (List AbstractByte))
    (elemFlIdx strideBytes runningOff : Nat) (elems : List Value)
    (buf out : List AbstractByte)
    (henc : ∀ idx v bs, valueHasProv v = false → encodeSlot idx v = .some bs →
      abstractBytesHaveProv bs = false)
    (hnp : valueListHasProv elems = false)
    (hbuf : abstractBytesHaveProv buf = false)
    (he : encodeArraySlotsIntoBufAux encodeSlot elemFlIdx strideBytes runningOff elems buf =
      .some out) :
    abstractBytesHaveProv out = false := by
  induction elems generalizing runningOff buf out with
  | nil => injection he with h; rw [← h]; exact hbuf
  | cons ev eRest ih =>
    unfold valueListHasProv at hnp
    have hev0 : valueHasProv ev = false := by
      cases hf : valueHasProv ev with
      | false => rfl
      | true => rw [hf] at hnp; cases hnp
    have hr0 : valueListHasProv eRest = false := by rw [hev0] at hnp; exact hnp
    unfold encodeArraySlotsIntoBufAux at he
    cases hes : encodeSlot elemFlIdx ev with
    | none => rw [hes] at he; cases he
    | some eBytes =>
      rw [hes] at he; dsimp only at he
      cases hw : writeAbstractBytesAt buf runningOff eBytes with
      | none => rw [hw] at he; cases he
      | some buf' =>
        rw [hw] at he; dsimp only at he
        exact ih (Nat.add runningOff strideBytes) buf' out hr0
          (abstractBytesHaveProv_writeAbstractBytesAt buf eBytes buf' runningOff
            hbuf (henc elemFlIdx ev eBytes hev0 hes) hw) he

/-- **Unconditional no-provenance preservation for `encodeByLayoutIdxAux`**:
encoding **any** provenance-free `Value` (`valueHasProv v = false` — including
scalars, structs, arrays, tuples, enums, AND `MaybeUninit`/union values with
raw-byte overlays!) via `encodeByLayoutIdxAux` yields provenance-free bytes. -/
theorem abstractBytesHaveProv_encodeByLayoutIdxAux_of_no_prov
    (fuel : Nat) (layouts : LayoutTable) (idx : Nat) (v : Value) (bs : List AbstractByte)
    (hnp : valueHasProv v = false)
    (he : encodeByLayoutIdxAux fuel layouts idx v = .some bs) :
    abstractBytesHaveProv bs = false := by
  induction fuel generalizing idx v bs with
  | zero => cases he
  | succ fuel' ih =>
    cases v with
    | unit => injection he with h; rw [← h]
    | ptr _ _ => cases hnp
    | scalar sv =>
      exact abstractBytesHaveProv_encodeByLayoutIdxAux_scalar (.succ fuel') layouts idx sv bs he
    | aggregate varIdx fieldVals =>
      dsimp only [valueHasProv] at hnp
      unfold encodeByLayoutIdxAux at he
      dsimp only at he
      cases hlk : LayoutTable.lookup layouts idx with
      | none =>
        rw [hlk] at he
        exact abstractBytesHaveProv_encodeUntypedValueToBytes_of_no_prov
          defaultCodecFuel (.aggregate varIdx fieldVals) bs hnp he
      | some l =>
        rw [hlk] at he; dsimp only at he
        cases hu : l.isUninhabited with
        | true => rw [hu] at he; cases he
        | false =>
          rw [hu] at he; dsimp only at he
          cases hf : l.fields with
          | union count =>
            rw [hf] at he; dsimp only at he
            cases hv0 : Nat.beq varIdx 0 with
            | false => rw [hv0] at he; cases he
            | true =>
              rw [hv0] at he; dsimp only at he
              unfold encodeUnionSlotsIntoBufAux at he
              cases hsp : splitUnionTypedAndOverlay count fieldVals with
              | none => rw [hsp] at he; cases he
              | some pair =>
                rw [hsp] at he; dsimp only at he
                obtain ⟨ht0, ho0⟩ := valueListHasProv_splitUnionTypedAndOverlay count fieldVals
                  pair hnp hsp
                have hgen : ∀ amb : Bool,
                    (match amb, pair.2 with
                     | true, _ => none
                     | false, .none =>
                       mergeUnionTypedSlotsAux layouts (encodeByLayoutIdxAux fuel' layouts)
                         (unresolvedLayoutIdx layouts) false l.size.bytes l.fieldLayouts pair.1
                         (replicateUninitBytes l.size.bytes) (replicateBool l.size.bytes false)
                     | false, .some rawVals =>
                       match Nat.ble (unionNonUnitNonZstTypedSlotCount layouts count l.fieldLayouts pair.1) 1 with
                       | false => none
                       | true =>
                         match overlayRawAbstractByteVals rawVals (replicateUninitBytes l.size.bytes) with
                         | .none => none
                         | .some rawImage =>
                           mergeUnionTypedSlotsAux layouts (encodeByLayoutIdxAux fuel' layouts)
                             (unresolvedLayoutIdx layouts) true l.size.bytes l.fieldLayouts pair.1
                             rawImage (replicateBool l.size.bytes true)) = .some bs →
                    abstractBytesHaveProv bs = false := by
                  intro amb hamb
                  cases amb with
                  | true => cases hamb
                  | false =>
                    cases hov : pair.2 with
                    | none =>
                      rw [hov] at hamb
                      exact abstractBytesHaveProv_mergeUnionTypedSlotsAux layouts _ _ false
                        l.size.bytes l.fieldLayouts pair.1 (replicateUninitBytes l.size.bytes) bs
                        (replicateBool l.size.bytes false)
                        (fun cIdx cv cbs hcv hce => ih cIdx cv cbs hcv hce) ht0
                        (abstractBytesHaveProv_replicateUninitBytes l.size.bytes) hamb
                    | some rawVals =>
                      rw [hov] at hamb; dsimp only at hamb
                      cases hcnt : Nat.ble (unionNonUnitNonZstTypedSlotCount layouts count l.fieldLayouts pair.1) 1 with
                      | false => rw [hcnt] at hamb; cases hamb
                      | true =>
                        rw [hcnt] at hamb; dsimp only at hamb
                        cases hraw : overlayRawAbstractByteVals rawVals (replicateUninitBytes l.size.bytes) with
                        | none => rw [hraw] at hamb; cases hamb
                        | some rawImage =>
                          rw [hraw] at hamb; dsimp only at hamb
                          have hraw0 := abstractBytesHaveProv_overlayRawAbstractByteVals rawVals
                            (replicateUninitBytes l.size.bytes) rawImage (ho0 rawVals hov)
                            (abstractBytesHaveProv_replicateUninitBytes l.size.bytes) hraw
                          exact abstractBytesHaveProv_mergeUnionTypedSlotsAux layouts _ _ true
                            l.size.bytes l.fieldLayouts pair.1 rawImage bs
                            (replicateBool l.size.bytes true)
                            (fun cIdx cv cbs hcv hce => ih cIdx cv cbs hcv hce) ht0 hraw0 hamb
                exact hgen _ he
          | arbitrary offsets _ =>
            rw [hf] at he; dsimp only at he
            cases hv : l.variants with
            | single expectedVar =>
              rw [hv] at he; dsimp only at he
              cases hok : Bool.and (Nat.beq varIdx expectedVar)
                  (Nat.beq (length offsets) (length fieldVals)) with
              | false => rw [hok] at he; cases he
              | true =>
                rw [hok] at he
                exact abstractBytesHaveProv_encodeArbitrarySlotsIntoBufAux _ _ offsets
                  l.fieldLayouts fieldVals (replicateUninitBytes l.size.bytes) bs
                  (fun cIdx cv cbs hcv hce => ih cIdx cv cbs hcv hce) hnp
                  (abstractBytesHaveProv_replicateUninitBytes l.size.bytes) he
            | empty | multiple _ _ _ =>
              rw [hv] at he
              exact abstractBytesHaveProv_encodeValueToBytes_of_no_prov defaultCodecFuel layouts
                { kind := .adt "" .nil, layoutIdx := idx } (.aggregate varIdx fieldVals) bs hnp he
          | array stride count =>
            rw [hf] at he; dsimp only at he
            cases hok : Bool.and (Nat.beq varIdx 0) (Nat.beq (length fieldVals) count) with
            | false => rw [hok] at he; cases he
            | true =>
              rw [hok] at he
              exact abstractBytesHaveProv_encodeArraySlotsIntoBufAux _ _ stride.bytes 0 fieldVals
                (replicateUninitBytes l.size.bytes) bs
                (fun cIdx cv cbs hcv hce => ih cIdx cv cbs hcv hce) hnp
                (abstractBytesHaveProv_replicateUninitBytes l.size.bytes) he
          | primitive =>
            rw [hf] at he; dsimp only at he
            cases heu : encodeUntypedValueToBytes defaultCodecFuel (.aggregate varIdx fieldVals) with
            | none => rw [heu] at he; cases he
            | some ubs =>
              rw [heu] at he; dsimp only at he
              cases hlen : Nat.beq (length ubs) l.size.bytes with
              | false => rw [hlen] at he; cases he
              | true =>
                rw [hlen] at he; injection he with h; rw [← h]
                exact abstractBytesHaveProv_encodeUntypedValueToBytes_of_no_prov
                  defaultCodecFuel (.aggregate varIdx fieldVals) ubs hnp heu

/-- Unconditional no-provenance preservation for `encodeTypedValueToBytes`. -/
theorem abstractBytesHaveProv_encodeTypedValueToBytes_of_no_prov
    (layouts : LayoutTable) (ty : Ty) (v : Value) (bs : List AbstractByte)
    (hnp : valueHasProv v = false)
    (he : encodeTypedValueToBytes layouts ty v = .some bs) :
    abstractBytesHaveProv bs = false := by
  unfold encodeTypedValueToBytes at he
  dsimp only at he
  cases hu : isUnionLayout layouts (normalizeCodecTy ty) with
  | true =>
    rw [hu] at he
    exact abstractBytesHaveProv_encodeByLayoutIdxAux_of_no_prov 8 layouts _ v bs hnp he
  | false =>
    rw [hu] at he; dsimp only at he
    cases hev : encodeValueToBytes defaultCodecFuel layouts (normalizeCodecTy ty) v with
    | some bs' =>
      rw [hev] at he; injection he with h; rw [← h]
      exact abstractBytesHaveProv_encodeValueToBytes_of_no_prov
        defaultCodecFuel layouts _ v bs' hnp hev
    | none =>
      rw [hev] at he; dsimp only at he
      cases hk : (normalizeCodecTy ty).kind with
      | adt _ _ | array _ _ =>
        rw [hk] at he; dsimp only at he
        cases hlk : LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
        | none => rw [hlk] at he; cases he
        | some _ =>
          rw [hlk] at he
          exact abstractBytesHaveProv_encodeByLayoutIdxAux_of_no_prov 8 layouts _ v bs hnp he
      | tuple ks =>
        rw [hk] at he
        cases ks with
        | nil => cases he
        | cons _ _ =>
          dsimp only at he
          cases hlk : LayoutTable.lookup layouts (normalizeCodecTy ty).layoutIdx with
          | none => rw [hlk] at he; cases he
          | some _ =>
            rw [hlk] at he
            exact abstractBytesHaveProv_encodeByLayoutIdxAux_of_no_prov 8 layouts _ v bs hnp he
      | bool | char | int _ | uint _ | float _ | never | str | slice _ | ref _ _ | rawPtr _ _
      | fnDef _ _ | fnPtr _ _ _ _ | closure _ _ | dynamic _ | foreign _ | param _ | alias _
      | other _ =>
        rw [hk] at he; cases he

/-- Unconditional no-provenance preservation for `encodeByteCastSourceBytes`. -/
theorem abstractBytesHaveProv_encodeByteCastSourceBytes_of_no_prov
    (layouts : LayoutTable) (srcTy : Ty) (v : Value) (bs : List AbstractByte)
    (hnp : valueHasProv v = false)
    (he : encodeByteCastSourceBytes layouts srcTy v = .some bs) :
    abstractBytesHaveProv bs = false := by
  unfold encodeByteCastSourceBytes at he
  cases het : encodeTypedValueToBytes layouts srcTy v with
  | some bs' =>
    rw [het] at he; injection he with h; rw [← h]
    exact abstractBytesHaveProv_encodeTypedValueToBytes_of_no_prov layouts srcTy v bs' hnp het
  | none =>
    rw [het] at he; dsimp only at he
    cases hu : isUnionLayout layouts (normalizeCodecTy srcTy) with
    | true => rw [hu] at he; cases he
    | false =>
      rw [hu] at he
      exact abstractBytesHaveProv_encodeUntypedValueToBytes_of_no_prov
        defaultCodecFuel v bs hnp he

/-- **Unconditional cast-level provenance-free equivalence for `evalByteCastWithPolicy`**:
whenever the source operand evaluates to **any** provenance-free `Value`
(`valueHasProv v = false` — scalars, structs, tuples, arrays, enums, AND
provenance-free `MaybeUninit`/union values, with ZERO `isUnionLayout` or
`encodeValueToBytes` side conditions!), `.stripProvenance` and `.strictUcg630Ub`
return the **exact identical** `RvalueEvalResult` for **every** target type! -/
theorem evalByteCastWithPolicy_strip_eq_strict_of_no_prov_src
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (v : Value) (locals' : List LocalSlot)
    (hev : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals
      localDecls mem.callStack = .ok v locals')
    (hnp : valueHasProv v = false) :
    evalByteCastWithPolicy .stripProvenance locals op targetTy mem localDecls layouts =
      evalByteCastWithPolicy .strictUcg630Ub locals op targetTy mem localDecls layouts := by
  unfold evalByteCastWithPolicy
  rw [hev]; dsimp only
  cases tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts targetTy) with
  | none => rfl
  | some dstSize =>
    dsimp only
    cases operandTy localDecls layouts op with
    | some srcTy =>
      dsimp only
      cases tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts srcTy) with
      | none => rfl
      | some srcSize =>
        dsimp only
        cases Nat.beq srcSize dstSize with
        | false => rfl
        | true =>
          dsimp only
          cases hbs : encodeByteCastSourceBytes layouts
              (resolveTyWithLocalDecls localDecls layouts srcTy) v with
          | none => rfl
          | some bs =>
            dsimp only
            cases Nat.beq (length bs) dstSize with
            | false => rfl
            | true =>
              dsimp only
              rw [decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
                defaultCodecFuel layouts _ bs
                (abstractBytesHaveProv_encodeByteCastSourceBytes_of_no_prov layouts _ v bs hnp hbs)]
    | none =>
      dsimp only
      cases hbs : encodeUntypedValueToBytes defaultCodecFuel v with
      | none => rfl
      | some bs =>
        dsimp only
        cases Nat.beq (length bs) dstSize with
        | false => rfl
        | true =>
          dsimp only
          rw [decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
            defaultCodecFuel layouts _ bs
            (abstractBytesHaveProv_encodeUntypedValueToBytes_of_no_prov
              defaultCodecFuel v bs hnp hbs)]

/-- **Unconditional cast-level provenance-free equivalence for
`evalByteCastRichWithPolicy`**: whenever `valueHasProv v = false`,
`.stripProvenance` and `.strictUcg630Ub` return the **exact identical**
`RvalueEvalResult` across arbitrary `richSpecs` and target types! -/
theorem evalByteCastRichWithPolicy_strip_eq_strict_of_no_prov_src
    (richSpecs : List (LayoutIdx × RichAdtSpec))
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (v : Value) (locals' : List LocalSlot)
    (hev : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals
      localDecls mem.callStack = .ok v locals')
    (hnp : valueHasProv v = false) :
    evalByteCastRichWithPolicy .stripProvenance richSpecs locals op targetTy mem localDecls layouts =
      evalByteCastRichWithPolicy .strictUcg630Ub richSpecs locals op targetTy mem localDecls layouts := by
  unfold evalByteCastRichWithPolicy
  rw [hev]; dsimp only
  cases tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts targetTy) with
  | none => rfl
  | some dstSize =>
    dsimp only
    cases operandTy localDecls layouts op with
    | some srcTy =>
      dsimp only
      cases tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts srcTy) with
      | none => rfl
      | some srcSize =>
        dsimp only
        cases Nat.beq srcSize dstSize with
        | false => rfl
        | true =>
          dsimp only
          cases hbs : encodeByteCastSourceBytes layouts
              (resolveTyWithLocalDecls localDecls layouts srcTy) v with
          | none => rfl
          | some bs =>
            dsimp only
            cases Nat.beq (length bs) dstSize with
            | false => rfl
            | true =>
              dsimp only
              rw [decodeTypedValueRichWithPolicy_strip_eq_strict_of_no_prov
                defaultCodecFuel layouts richSpecs _ bs
                (abstractBytesHaveProv_encodeByteCastSourceBytes_of_no_prov layouts _ v bs hnp hbs)]
    | none =>
      dsimp only
      cases hbs : encodeUntypedValueToBytes defaultCodecFuel v with
      | none => rfl
      | some bs =>
        dsimp only
        cases Nat.beq (length bs) dstSize with
        | false => rfl
        | true =>
          dsimp only
          rw [decodeTypedValueRichWithPolicy_strip_eq_strict_of_no_prov
            defaultCodecFuel layouts richSpecs _ bs
            (abstractBytesHaveProv_encodeUntypedValueToBytes_of_no_prov
              defaultCodecFuel v bs hnp hbs)]

/-! ## §19. Sterbenz Exact Addition, `sub` vs `add ∘ neg` NaN List-Order Witness & Relational Dispatcher `sub`/`ne` Laws -/

/-- **Sterbenz's Exact-Addition Theorem (`evalFloatArithBaseProto_add_sterbenz_exact`)**:
for any two finite `f32`/`f64` floats `a` and `b` of **opposite signs** within a
factor of `2` (`|b| / 2 ≤ |a| ≤ 2 * |b|`), IEEE-754 addition `a + b` incurs
**zero rounding error** and **never overflows** (clean corollary of
`evalFloatArithBaseProto_sub_sterbenz_exact` via `a + b = a - (-b)`). -/
theorem evalFloatArithBaseProto_add_sterbenz_exact (f : IeeeFormat) (a b : Nat)
    (sign : Bool) (lnum lden rnum rden : Nat)
    (hl : decodeBits f a = .finite sign lnum lden)
    (hr : decodeBits f b = .finite (!sign) rnum rden)
    (hlo : lden * rnum ≤ 2 * (lnum * rden))
    (hhi : lnum * rden ≤ 2 * (lden * rnum)) :
    let sumInt := signedNum sign lnum * Int.ofNat rden + signedNum (!sign) rnum * Int.ofNat lden
    (sumInt = 0 → evalFloatArithBaseProto .add f a b = zeroBits f false) ∧
    (sumInt ≠ 0 →
      ∃ sumN sumD,
        decodeBits f (evalFloatArithBaseProto .add f a b) =
          .finite (decide (sumInt < 0)) sumN sumD ∧
        sumN * (lden * rden) = sumInt.natAbs * sumD ∧
        0 < sumD) := by
  have hr_neg : decodeBits f (evalFloatNegProto f b) = .finite sign rnum rden := by
    rw [decodeBits_evalFloatNegProto, hr]
    cases sign <;> rfl
  have hadd_eq : evalFloatArithBaseProto .add f a b =
      evalFloatArithBaseProto .sub f a (evalFloatNegProto f b) := by
    have hmod_neg : evalFloatNegProto f b = evalFloatNegProto f (b % 2 ^ f.width) := by
      unfold evalFloatNegProto
      rw [Nat.mod_mod]
    rw [evalFloatArithBaseProto_sub_eq_add_neg, hmod_neg,
      evalFloatNegProto_involutive f (b % 2 ^ f.width) (Nat.mod_lt _ (Nat.two_pow_pos _)),
      ← evalFloatArithBaseProto_mod_width .add f a b,
      ← evalFloatArithBaseProto_mod_width .add f a (b % 2 ^ f.width), Nat.mod_mod]
  have hsum_eq :
      signedNum sign lnum * Int.ofNat rden + signedNum (!sign) rnum * Int.ofNat lden =
        signedNum sign lnum * Int.ofNat rden - signedNum sign rnum * Int.ofNat lden := by
    dsimp only [signedNum]
    cases sign <;> simp [Int.neg_mul, Int.sub_eq_add_neg]
  dsimp only
  rw [hadd_eq, hsum_eq]
  exact evalFloatArithBaseProto_sub_sterbenz_exact f a (evalFloatNegProto f b)
    sign lnum lden rnum rden hl hr_neg hlo hhi

/-- **Kernel-checked witness (`by rfl`) of `nanChoicesProto` ordered-list swap
between `sub` and `add ∘ neg`**: while `EvalFloatBinOpRel.sub_eq_add_neg` holds
as a *set* equality, negating `rhs` reverses `[q, neg q]` to `[neg q, q]` (and
reverses signaling candidates `[s, neg s]` to `[neg s, s]`) in the ordered
candidate list of `nanChoicesProto` — proving why `LeanMiriSpec/FloatArithLM.lean`
must map `.Sub` directly to `FloatBits.arithmetic .Sub` rather than rewriting
through `negate` before `adjustNaN`! -/
theorem nanChoicesProto_sub_vs_add_neg_order_witness :
    -- 1. `f32` quiet NaN `rhs = 0x7FC01234`: `sub` puts `0x7FC01234` before `0xFFC01234`,
    --    while `add ∘ neg` puts `0xFFC01234` before `0x7FC01234`!
    nanChoicesProto .binary32 [(.binary32, 0x3F800000), (.binary32, 0x7FC01234)]
        .nondeterministic =
      [0x7FC00000, 0xFFC00000, 0x7FC01234, 0xFFC01234] ∧
    nanChoicesProto .binary32
        [(.binary32, 0x3F800000), (.binary32, evalFloatNegProto .binary32 0x7FC01234)]
        .nondeterministic =
      [0x7FC00000, 0xFFC00000, 0xFFC01234, 0x7FC01234] ∧
    -- 2. `f32` signaling NaN `rhs = 0x7F800001`: both quieted and signaling pairs swap order!
    nanChoicesProto .binary32 [(.binary32, 0x3F800000), (.binary32, 0x7F800001)]
        .nondeterministic =
      [0x7FC00000, 0xFFC00000, 0x7FC00001, 0xFFC00001, 0x7F800001, 0xFF800001] ∧
    nanChoicesProto .binary32
        [(.binary32, 0x3F800000), (.binary32, evalFloatNegProto .binary32 0x7F800001)]
        .nondeterministic =
      [0x7FC00000, 0xFFC00000, 0xFFC00001, 0x7FC00001, 0xFF800001, 0x7F800001] ∧
    -- 3. `f64` quiet NaN `rhs = 0x7FF8000000000005`: same ordered swap!
    nanChoicesProto .binary64
        [(.binary64, 0x3FF0000000000000), (.binary64, 0x7FF8000000000005)]
        .nondeterministic =
      [0x7FF8000000000000, 0xFFF8000000000000, 0x7FF8000000000005, 0xFFF8000000000005] ∧
    nanChoicesProto .binary64
        [(.binary64, 0x3FF0000000000000),
         (.binary64, evalFloatNegProto .binary64 0x7FF8000000000005)]
        .nondeterministic =
      [0x7FF8000000000000, 0xFFF8000000000000, 0xFFF8000000000005, 0x7FF8000000000005] := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **Relational MIR dispatcher equivalence of `sub` and `add ∘ neg`**:
under **both** `.deterministic` and `.nondeterministic` modes, whenever `lhsOp`,
`rhsOp`, and `rhsNegOp` read well-typed `f32`/`f64` scalars without mutating
`locals` and `rhsNegOp`'s bit pattern equals `evalFloatNegProto fmt rhsSc.bits`,
`EvalRvalueFloatRelProto` admits the **exact same outcomes** for
`.binaryOp .sub lhsOp rhsOp` and `.binaryOp .add lhsOp rhsNegOp` (lifting
`EvalFloatBinOpRel.sub_eq_add_neg` to the MIR `Rvalue` dispatcher!). -/
theorem EvalRvalueFloatRelProto.sub_eq_add_neg_float_of_ok
    (mode : FloatArithMode) (locals : List LocalSlot) (lhsOp rhsOp rhsNegOp : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (fk : FloatTy) (fmt : IeeeFormat) (lhsSc rhsSc rhsNegSc : ScalarVal)
    (res : RvalueEvalResult)
    (hlTy : floatTyOf? (operandTy localDecls layouts lhsOp) = .some fk)
    (hrTy : floatTyOf? (operandTy localDecls layouts rhsOp) = .some fk)
    (hrnTy : floatTyOf? (operandTy localDecls layouts rhsNegOp) = .some fk)
    (hfmt : ieeeFormatOfFloatTy? fk = .some fmt)
    (hwL : Nat.beq lhsSc.sizeBytes fmt.byteWidth = true)
    (hwR : Nat.beq rhsSc.sizeBytes fmt.byteWidth = true)
    (hwRN : Nat.beq rhsNegSc.sizeBytes fmt.byteWidth = true)
    (hneg : rhsNegSc.bits = evalFloatNegProto fmt rhsSc.bits)
    (hl : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals
      localDecls mem.callStack = .ok (.scalar lhsSc) locals)
    (hr : evalOperand locals rhsOp mem.borrows mem.globals layouts mem.callerLocals
      localDecls mem.callStack = .ok (.scalar rhsSc) locals)
    (hrn : evalOperand locals rhsNegOp mem.borrows mem.globals layouts mem.callerLocals
      localDecls mem.callStack = .ok (.scalar rhsNegSc) locals) :
    EvalRvalueFloatRelProto mode locals (.binaryOp .sub lhsOp rhsOp) mem localDecls layouts res ↔
      EvalRvalueFloatRelProto mode locals (.binaryOp .add lhsOp rhsNegOp) mem localDecls layouts res := by
  have hchar : ∀ (op : BinOp) (rOp : Operand) (rSc : ScalarVal),
      isFloatArithBinOp op = true →
      floatTyOf? (operandTy localDecls layouts rOp) = .some fk →
      Nat.beq rSc.sizeBytes fmt.byteWidth = true →
      evalOperand locals rOp mem.borrows mem.globals layouts mem.callerLocals
        localDecls mem.callStack = .ok (.scalar rSc) locals →
      (EvalRvalueFloatRelProto mode locals (.binaryOp op lhsOp rOp) mem localDecls layouts res ↔
        ∃ out, EvalFloatBinOpRel mode op fmt lhsSc.bits rSc.bits out ∧
          res = .ok (.scalar ⟨out, fmt.byteWidth⟩) locals mem) := by
    intro op rOp rSc harith hrT hwR' hrEv
    unfold EvalRvalueFloatRelProto
    dsimp only
    rw [hlTy, hrT]; dsimp only
    rw [hl]; dsimp only
    rw [hrEv]; dsimp only
    rw [hfmt]; dsimp only
    have hc : (fmt == fmt && Nat.beq lhsSc.sizeBytes fmt.byteWidth &&
        Nat.beq rSc.sizeBytes fmt.byteWidth && isFloatArithBinOp op) = true := by
      cases fmt <;> simp [hwL, hwR', harith]
    rw [if_pos' hc]
  rw [hchar .sub rhsOp rhsSc rfl hrTy hwR hr,
      hchar .add rhsNegOp rhsNegSc rfl hrnTy hwRN hrn, hneg]
  constructor
  · intro ⟨out, hrel, hres⟩
    exact ⟨out, (EvalFloatBinOpRel.sub_eq_add_neg mode fmt lhsSc.bits rhsSc.bits out).mp hrel, hres⟩
  · intro ⟨out, hrel, hres⟩
    exact ⟨out, (EvalFloatBinOpRel.sub_eq_add_neg mode fmt lhsSc.bits rhsSc.bits out).mpr hrel, hres⟩

/-- **Full biconditional relational `.ne` / `.eq` duality** (strengthening the
one-way `.ne` conjunct in `cmp_laws_float`): under both `FloatArithMode`s,
`.binaryOp .ne` relates to `res` iff `res` is the negated `.eq` boolean scalar,
and relates to `boolToScalar b` iff `.binaryOp .eq` relates to `boolToScalar (!b)`. -/
theorem EvalRvalueFloatRelProto.ne_eq_duality_float
    (mode : FloatArithMode) (locals : List LocalSlot) (lhsOp rhsOp : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (fk : FloatTy) (fmt : IeeeFormat) (lhsSc rhsSc : ScalarVal)
    (res : RvalueEvalResult) (b : Bool)
    (hlTy : floatTyOf? (operandTy localDecls layouts lhsOp) = .some fk)
    (hrTy : floatTyOf? (operandTy localDecls layouts rhsOp) = .some fk)
    (hfmt : ieeeFormatOfFloatTy? fk = .some fmt)
    (hwL : Nat.beq lhsSc.sizeBytes fmt.byteWidth = true)
    (hwR : Nat.beq rhsSc.sizeBytes fmt.byteWidth = true)
    (hl : evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals
      localDecls mem.callStack = .ok (.scalar lhsSc) locals)
    (hr : evalOperand locals rhsOp mem.borrows mem.globals layouts mem.callerLocals
      localDecls mem.callStack = .ok (.scalar rhsSc) locals) :
    (EvalRvalueFloatRelProto mode locals (.binaryOp .ne lhsOp rhsOp) mem localDecls layouts res ↔
      res = .ok (.scalar (boolToScalar (!evalFloatCmpProto .eq fmt lhsSc.bits rhsSc.bits)))
        locals mem) ∧
    (EvalRvalueFloatRelProto mode locals (.binaryOp .ne lhsOp rhsOp) mem localDecls layouts
        (.ok (.scalar (boolToScalar b)) locals mem) ↔
      EvalRvalueFloatRelProto mode locals (.binaryOp .eq lhsOp rhsOp) mem localDecls layouts
        (.ok (.scalar (boolToScalar (!b))) locals mem)) := by
  have heval_eq : evalRvalueFloatProto locals (.binaryOp .eq lhsOp rhsOp) mem localDecls layouts =
      .ok (.scalar (boolToScalar (evalFloatCmpProto .eq fmt lhsSc.bits rhsSc.bits))) locals mem := by
    unfold evalRvalueFloatProto
    dsimp only
    rw [hlTy, hrTy]; dsimp only
    rw [hl]; dsimp only
    rw [hr]; dsimp only
    rw [hfmt]; dsimp only
    have hc : (fmt == fmt && Nat.beq lhsSc.sizeBytes fmt.byteWidth &&
        Nat.beq rhsSc.sizeBytes fmt.byteWidth) = true := by
      cases fmt <;> simp [hwL, hwR]
    rw [if_pos' hc]
    rfl
  have heval_ne : evalRvalueFloatProto locals (.binaryOp .ne lhsOp rhsOp) mem localDecls layouts =
      .ok (.scalar (boolToScalar (!evalFloatCmpProto .eq fmt lhsSc.bits rhsSc.bits))) locals mem := by
    unfold evalRvalueFloatProto
    dsimp only
    rw [hlTy, hrTy]; dsimp only
    rw [hl]; dsimp only
    rw [hr]; dsimp only
    rw [hfmt]; dsimp only
    have hc : (fmt == fmt && Nat.beq lhsSc.sizeBytes fmt.byteWidth &&
        Nat.beq rhsSc.sizeBytes fmt.byteWidth) = true := by
      cases fmt <;> simp [hwL, hwR]
    rw [if_pos' hc]
    show RvalueEvalResult.ok (.scalar (boolToScalar (evalFloatCmpProto .ne fmt lhsSc.bits rhsSc.bits)))
      locals mem = _
    rw [evalFloatCmpProto_ne_eq_not_eq]
  have hne_iff := EvalRvalueFloatRelProto.nonArith_binOp_iff mode .ne lhsOp rhsOp locals mem
    localDecls layouts res rfl
  rw [heval_ne] at hne_iff
  refine ⟨hne_iff, ?_⟩
  rw [EvalRvalueFloatRelProto.nonArith_binOp_iff mode .ne lhsOp rhsOp locals mem localDecls layouts _ rfl,
      EvalRvalueFloatRelProto.nonArith_binOp_iff mode .eq lhsOp rhsOp locals mem localDecls layouts _ rfl,
      heval_ne, heval_eq]
  cases b <;> cases evalFloatCmpProto .eq fmt lhsSc.bits rhsSc.bits <;>
    exact ⟨fun h => by cases h <;> rfl, fun h => by cases h <;> rfl⟩

/-- **Unconditional mode-independence of `EvalRvalueFloatRelProto` on all
non-arithmetic binary operations** (including all 6 float comparisons `eq`, `ne`,
`lt`, `le`, `gt`, `ge`, even on `f16`/`f128`, NaNs, or `.ub` / `.unsupported`
states). -/
theorem EvalRvalueFloatRelProto.cmp_mode_indep
    (op : BinOp) (lhsOp rhsOp : Operand) (locals : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (res : RvalueEvalResult)
    (hnarith : isFloatArithBinOp op = false) :
    EvalRvalueFloatRelProto .deterministic locals (.binaryOp op lhsOp rhsOp) mem localDecls layouts res ↔
      EvalRvalueFloatRelProto .nondeterministic locals (.binaryOp op lhsOp rhsOp) mem localDecls layouts res := by
  rw [EvalRvalueFloatRelProto.nonArith_binOp_iff .deterministic op lhsOp rhsOp locals mem localDecls layouts res hnarith,
      EvalRvalueFloatRelProto.nonArith_binOp_iff .nondeterministic op lhsOp rhsOp locals mem localDecls layouts res hnarith]

end Anneal.FloatArithAndUcg630Prototype
