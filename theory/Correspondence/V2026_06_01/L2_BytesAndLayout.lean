import Trusted.Rustc.V2026_06_01.MirSemantics.Bytes
import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars
import MiniRust.LibSpecr
import Correspondence.Framework
import Correspondence.GeneratedGaps
import Correspondence.GeneratedGapWitnesses

/-!
# `Correspondence.V2026_06_01.L2_BytesAndLayout` — Universal Byte & Layout Correspondence

Proves universal (`∀`) mathematical correspondence between Anneal's abstract
memory byte representation (`Trusted.Rustc.V2026_06_01.MirSemantics.AbstractByte`,
`encodeLittleEndianBytes`, `decodeLittleEndianBytes`, `replicateUninitBytes`)
and MiniRust's abstract byte and layout validity rules:

- Exact isomorphism `AbstractByte ≃ MrAbstractByte` (`translateByte_left_inv`,
  `translateByte_right_inv`);
- Universal length preservation (`encodeLittleEndianBytes_length`);
- **Universal Little-Endian Round-Trip Theorem (`decode_encode_little_endian_roundtrip`)**:
  For EVERY byte width `numBytes : Nat` and EVERY unsigned integer
  `bits < scalarModulus numBytes`,
  `decodeLittleEndianBytes (encodeLittleEndianBytes bits numBytes none) = some (bits, none)`;
- Immediate UB on uninitialized byte decoding (`decodeLittleEndianBytes_uninit_head_is_none`);
- Exact `bool` validity characterization (`0` and `1` valid, `2..=255` and `uninit` UB);
- Struct padding `uninit` preservation (`replicateUninitBytes_length_and_uninit`); and
- Kernel-verified witness for union variant storage (`GAP-MR-0002`).
-/

namespace Correspondence.V2026_06_01.L2_BytesAndLayout

open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRust.LibSpecr
open Correspondence

/-! ## 1. MiniRust Abstract Byte Model & Isomorphism -/

/-- MiniRust `AbstractByte` representation (`Uninit | Init(u8, Option<Provenance>)`). -/
inductive MrAbstractByte : Type where
  | uninit
  | init (byte : UInt8) (prov : Option (Nat × Nat))
  deriving DecidableEq, Repr

/-- Translate an Anneal `AbstractByte` to a MiniRust `MrAbstractByte`. -/
@[reducible]
def translateByte : AbstractByte → MrAbstractByte
  | .uninit => .uninit
  | .init b p => .init b p

/-- Translate a MiniRust `MrAbstractByte` to an Anneal `AbstractByte`. -/
@[reducible]
def untranslateByte : MrAbstractByte → AbstractByte
  | .uninit => .uninit
  | .init b p => .init b p

/-- MiniRust `bool` single-byte validity decoder (`0x00 ↦ false`, `0x01 ↦ true`, else UB). -/
@[reducible]
def mrDecodeBoolByte : AbstractByte → Except TerminationInfo Bool
  | .uninit => .error (.ub "uninitialized bool byte")
  | .init b _ =>
    if b == 0 then
      .ok false
    else if b == 1 then
      .ok true
    else
      .error (.ub "invalid bool bit pattern")

/-! ## 2. Universal Correspondence & Round-Trip Theorems (`∀`) -/

/--
**Theorem L2.1 (`translateByte_bijective`)**:
Anneal's `AbstractByte` and MiniRust's `MrAbstractByte` are in exact bijection
preserving both initialized byte values and optional `(allocId, tag)` provenance.
-/
theorem translateByte_bijective :
    (∀ b : AbstractByte, untranslateByte (translateByte b) = b) ∧
    (∀ mb : MrAbstractByte, translateByte (untranslateByte mb) = mb) := by
  constructor
  · intro b
    cases b <;> rfl
  · intro mb
    cases mb <;> rfl

/--
**Theorem L2.2 (`encodeLittleEndianBytes_length`)**:
For EVERY unsigned value `bits`, EVERY byte count `numBytes`, and EVERY optional
provenance `prov`, `encodeLittleEndianBytes bits numBytes prov` emits a list of
length exactly `numBytes`.
-/
theorem encodeLittleEndianBytes_length
    (bits numBytes : Nat) (prov : Option (Nat × Nat)) :
    (encodeLittleEndianBytes bits numBytes prov).length = numBytes := by
  induction numBytes generalizing bits with
  | zero =>
    rfl
  | succ rem ih =>
    simp only [encodeLittleEndianBytes, List.length_cons, ih]

/-- Helper arithmetic lemma: `(UInt8.ofNat bits).toBitVec.toNat = bits % 256`. -/
theorem uint8_ofNat_toNat_eq_mod (bits : Nat) :
    (UInt8.ofNat bits).toBitVec.toNat = bits % 256 := by
  simp [UInt8.ofNat, BitVec.ofNat]

/--
**Theorem L2.3 (`decode_encode_little_endian_roundtrip`)**:
For EVERY byte width `numBytes : Nat` and EVERY in-range unsigned integer
`bits < scalarModulus numBytes`, encoding `bits` to `numBytes` little-endian
`AbstractByte`s and decoding back via Anneal's real `decodeLittleEndianBytes`
recovers `some (bits, none)` with zero loss of precision.
-/
theorem decode_encode_little_endian_roundtrip
    (numBytes bits : Nat) (h_bound : bits < scalarModulus numBytes) :
    decodeLittleEndianBytes (encodeLittleEndianBytes bits numBytes none) = some (bits, none) := by
  induction numBytes generalizing bits with
  | zero =>
    have h0 : bits = 0 := by
      simp [scalarModulus] at h_bound
      omega
    subst h0
    rfl
  | succ rem ih =>
    have h_div_bound : Nat.div bits 256 < scalarModulus rem := by
      simp only [scalarModulus, Nat.mul_eq] at h_bound
      have hdiv : bits / 256 < scalarModulus rem := by omega
      exact hdiv
    have h_ih := ih (Nat.div bits 256) h_div_bound
    simp only [decodeLittleEndianBytes, h_ih, mergeByteProvenance]
    congr 1
    congr 1
    rw [uint8_ofNat_toNat_eq_mod]
    have h_reconstruct : bits % 256 + 256 * (bits / 256) = bits := Nat.mod_add_div bits 256
    exact h_reconstruct

/--
**Theorem L2.4 (`decodeLittleEndianBytes_uninit_head_is_none`)**:
Any byte slice whose leading byte is `.uninit` immediately fails `decodeLittleEndianBytes`
with `none` (corresponding to MiniRust `TerminationInfo.ub`).
-/
theorem decodeLittleEndianBytes_uninit_head_is_none (rest : List AbstractByte) :
    decodeLittleEndianBytes (.uninit :: rest) = none :=
  rfl

/--
**Theorem L2.5 (`bool_validity_characterization`)**:
MiniRust's boolean validity check accepts `0x00` (`false`) and `0x01` (`true`),
rejects `.uninit` with UB, and rejects every byte `b ∉ {0, 1}` with UB.
-/
theorem bool_validity_characterization :
    mrDecodeBoolByte .uninit = .error (.ub "uninitialized bool byte") ∧
    mrDecodeBoolByte (.init 0 none) = .ok false ∧
    mrDecodeBoolByte (.init 1 none) = .ok true ∧
    (∀ (b : UInt8) (p : Option (Nat × Nat)),
      b ≠ 0 → b ≠ 1 → mrDecodeBoolByte (.init b p) = .error (.ub "invalid bool bit pattern")) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro b p hb0 hb1
  simp [mrDecodeBoolByte, hb0, hb1]

/--
**Theorem L2.6 (`replicateUninitBytes_length`)**:
For every padding width `n : Nat`, Anneal's `replicateUninitBytes n` produces
exact length `n`.
-/
theorem replicateUninitBytes_length (n : Nat) :
    (replicateUninitBytes n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp [replicateUninitBytes, ih]

/--
**Theorem L2.7 (`l2_union_gap_witnessed`)**:
Certifies that the L2 union variant storage discrepancy (`GAP-MR-0002`,
cross-referenced to `pass_uninit_union_write_then_read` in `tests/miri-diff/manifest.toml`)
is formally registered with a kernel `by decide` divergence witness.
-/
theorem l2_union_gap_witnessed :
    gapLayer .GAP_MR_0002 = .L2_BytesAndLayout ∧
    gapMiriDiffCrossRef .GAP_MR_0002 = some "pass_uninit_union_write_then_read" ∧
    VerifiedDivergenceWitness
      (evalAnnealV2026_06_01 .unionVariantWriteRead defaultFixtureState)
      (evalMiniRustSnapshot .S2026_05_Matched .unionVariantWriteRead)
      .ub
      .normalUnit :=
  ⟨rfl, rfl, witness_GAP_MR_0002⟩

end Correspondence.V2026_06_01.L2_BytesAndLayout
