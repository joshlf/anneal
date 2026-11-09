import Trusted
import Anneal.Scalars

namespace Anneal.BitValidity

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-!
Byte-level bit-validity predicates, `zerocopy` trait models (`TryFromBytes`,
`FromZeros`, `FromBytes`, `IntoBytes`, `Unaligned`), and decidable layout
certificate checkers over `MirSemantics.AbstractByte` and `LayoutTable` (`#88`,
`#100`, `#102`, `#103`).

This module connects the operational byte codec in
`Trusted.Rustc.V2026_06_01.MirSemantics.Bytes` (`encodeValueToBytes` and
`decodeValueFromBytes`) to the type-level invariants relied on by safe byte
transmutation:
- `ValidityMode` and `ByteSeqValid` classify when an `AbstractByte` sequence
  satisfies uninitialized, initialized, or bit-valid layout constraints.
- `IsTryFromBytes`, `IsFromZeros`, `IsFromBytes`, `IsIntoBytes`, and
  `IsUnaligned` formalize the semantic obligations of `zerocopy`'s core marker
  traits, unified under `ZerocopyTrait` / `ValidForTrait`.
- `transmute_sound_of_into_from_bytes` proves that encoding any valid value of
  an `IsIntoBytes` source type and decoding at a same-sized `IsFromBytes`
  destination type always succeeds without undefined behavior.
- `checkUnaligned`, `checkFromZeros`, `checkFromBytes`, and `checkIntoBytes`
  provide decidable (`rfl`-checkable) layout certificate checkers for scalars,
  unit, homogeneous integer arrays, and contiguous multi-field structs.
  `checkIntoBytes` additionally accepts `bool`, `char`, `[bool; n]`,
  `[char; n]`, and contiguous structs with such fields, while `checkFromBytes`
  keeps rejecting them (`checkFromBytes_implies_checkIntoBytes`,
  `checkIntoBytes_strictly_extends_checkFromBytes`).
- Section 6 relates `rustc`'s scalar layout descriptors
  (`ScalarLayout.initialized pk validRange`, `wrappingRangeContains`, and
  `decodeScalarLayoutBytes`) to `IsFromBytes`, `IsFromZeros`, and exact
  `IsTryFromBytes` decodability for `.primitive` ADTs such as fieldless enum
  tags and `NonZero*` niches.
-/

/-! ## 1. Byte-Sequence Validity Modes and Initialized-Byte Helpers -/

/-- Byte-sequence validity modes for raw memory reads, casts, and conversions. -/
inductive ValidityMode : Type where
  /-- Arbitrary byte sequence of the type's byte size (`.uninit` permitted). -/
  | Uninit
  /-- Byte sequence that is bit-valid whenever all of its bytes are `.init`. -/
  | AsInitialized
  /-- Byte sequence of the type's byte size with no `.uninit` bytes. -/
  | Initialized
  /-- Byte sequence that decodes via `decodeValueFromBytes` to a valid `Value`. -/
  | BitValid
  /-- Byte sequence that decodes to a valid `Value` satisfying all invariants. -/
  | Valid
  deriving DecidableEq, Repr

namespace ValidityMode

abbrev uninit : ValidityMode := .Uninit
abbrev asInitialized : ValidityMode := .AsInitialized
abbrev initialized : ValidityMode := .Initialized
abbrev bitValid : ValidityMode := .BitValid
abbrev valid : ValidityMode := .Valid

end ValidityMode

/-- Whether every byte in `bs` is initialized (`AbstractByte.init`). -/
@[reducible]
def allBytesInitialized : List AbstractByte → Bool
  | [] => true
  | .uninit :: _ => false
  | .init _ _ :: rest => allBytesInitialized rest

@[simp]
theorem allBytesInitialized_nil : allBytesInitialized [] = true := rfl

@[simp]
theorem allBytesInitialized_uninit (rest : List AbstractByte) :
    allBytesInitialized (.uninit :: rest) = false := rfl

@[simp]
theorem allBytesInitialized_init
    (b : UInt8) (prov : Option (Nat × Nat)) (rest : List AbstractByte) :
    allBytesInitialized (.init b prov :: rest) = allBytesInitialized rest := rfl

/-- Construct `n` zero-initialized bytes (`0x00` with no provenance). -/
@[reducible]
def zeroInitBytes : Nat → List AbstractByte
  | 0 => []
  | k + 1 => .init (UInt8.ofNat 0) none :: zeroInitBytes k

@[simp]
theorem length_zeroInitBytes : ∀ n : Nat, length (zeroInitBytes n) = n
  | 0 => rfl
  | k + 1 => congrArg Nat.succ (length_zeroInitBytes k)

@[simp]
theorem allBytesInitialized_zeroInitBytes :
    ∀ n : Nat, allBytesInitialized (zeroInitBytes n) = true
  | 0 => rfl
  | k + 1 => allBytesInitialized_zeroInitBytes k

@[simp]
theorem takeAbstractBytes_eq_take :
    ∀ (n : Nat) (bs : List AbstractByte), takeAbstractBytes n bs = bs.take n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, b :: bs => congrArg (b :: ·) (takeAbstractBytes_eq_take k bs)

@[simp]
theorem dropAbstractBytes_eq_drop :
    ∀ (n : Nat) (bs : List AbstractByte), dropAbstractBytes n bs = bs.drop n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, _ :: bs => dropAbstractBytes_eq_drop k bs

@[simp]
theorem appendAbstractBytes_eq_append :
    ∀ xs ys : List AbstractByte, appendAbstractBytes xs ys = xs ++ ys
  | [], _ => rfl
  | x :: xs, ys => congrArg (x :: ·) (appendAbstractBytes_eq_append xs ys)

@[simp]
theorem replicateUninitBytes_eq_replicate :
    ∀ n : Nat, replicateUninitBytes n = List.replicate n .uninit
  | 0 => rfl
  | k + 1 => congrArg (.uninit :: ·) (replicateUninitBytes_eq_replicate k)

theorem allBytesInitialized_append
    {xs ys : List AbstractByte}
    (hxs : allBytesInitialized xs = true)
    (hys : allBytesInitialized ys = true) :
    allBytesInitialized (xs ++ ys) = true := by
  induction xs with
  | nil => exact hys
  | cons x rest ih =>
    cases x with
    | uninit => nomatch hxs
    | init _ _ => exact ih hxs

theorem allBytesInitialized_take
    (n : Nat) {bs : List AbstractByte}
    (h : allBytesInitialized bs = true) :
    allBytesInitialized (bs.take n) = true := by
  induction n generalizing bs with
  | zero => rfl
  | succ k ih =>
    cases bs with
    | nil => rfl
    | cons x rest =>
      cases x with
      | uninit => nomatch h
      | init _ _ => exact ih h

theorem allBytesInitialized_drop
    (n : Nat) {bs : List AbstractByte}
    (h : allBytesInitialized bs = true) :
    allBytesInitialized (bs.drop n) = true := by
  induction n generalizing bs with
  | zero => exact h
  | succ k ih =>
    cases bs with
    | nil => rfl
    | cons x rest =>
      cases x with
      | uninit => nomatch h
      | init _ _ => exact ih h

/--
Required ABI alignment in bytes of `ty` in `layouts`, falling back to primitive
architectural alignments when `layouts` does not index `ty.layoutIdx`.
-/
@[reducible]
def tyAlignmentBytes (layouts : LayoutTable) (ty : Ty) : Option Nat :=
  match LayoutTable.lookup layouts ty.layoutIdx with
  | some l => some l.align.bytes
  | none =>
    match ty.kind with
    | .tuple [] | .bool | .uint .u8 | .int .i8
    | .array (.uint .u8) _ | .array (.int .i8) _ | .array .bool _ => some 1
    | .uint .u16 | .int .i16 => some 2
    | .uint .u32 | .int .i32 | .char => some 4
    | .uint .u64 | .int .i64 | .uint .usize | .int .isize => some 8
    | .uint .u128 | .int .i128 => some 16
    | _ => none

/-- Whether byte sequence `bs` satisfies `mode` for `ty` under `layouts`. -/
def ByteSeqValid
    (layouts : LayoutTable) (ty : Ty) (mode : ValidityMode)
    (bs : List AbstractByte) : Prop :=
  match mode with
  | .Uninit =>
    ∃ sz, rigidTyByteSize layouts ty = some sz ∧ length bs = sz
  | .AsInitialized =>
    ∃ sz,
      rigidTyByteSize layouts ty = some sz ∧
      length bs = sz ∧
      (allBytesInitialized bs = true →
        ∃ v, decodeValueFromBytes defaultCodecFuel layouts ty bs = some v)
  | .Initialized =>
    ∃ sz,
      rigidTyByteSize layouts ty = some sz ∧
      length bs = sz ∧
      allBytesInitialized bs = true
  | .BitValid | .Valid =>
    ∃ sz v,
      rigidTyByteSize layouts ty = some sz ∧
      length bs = sz ∧
      decodeValueFromBytes defaultCodecFuel layouts ty bs = some v

theorem byteSeqValid_bitValid_implies_uninit
    (layouts : LayoutTable) (ty : Ty) (bs : List AbstractByte)
    (h : ByteSeqValid layouts ty .BitValid bs) :
    ByteSeqValid layouts ty .Uninit bs := by
  rcases h with ⟨sz, _, hsz, hlen, _⟩
  exact ⟨sz, hsz, hlen⟩

theorem byteSeqValid_bitValid_implies_asInitialized
    (layouts : LayoutTable) (ty : Ty) (bs : List AbstractByte)
    (h : ByteSeqValid layouts ty .BitValid bs) :
    ByteSeqValid layouts ty .AsInitialized bs := by
  rcases h with ⟨sz, v, hsz, hlen, hdec⟩
  exact ⟨sz, hsz, hlen, fun _ => ⟨v, hdec⟩⟩

/-! ## 2. Semantic Models of `zerocopy` Marker Traits and Transmutation -/

/-- Semantic model of `zerocopy::TryFromBytes`. -/
def IsTryFromBytes
    (layouts : LayoutTable) (ty : Ty)
    (validPred : Value → Prop := fun _ => True) : Prop :=
  ∃ sz,
    rigidTyByteSize layouts ty = some sz ∧
    ∀ bs v,
      decodeValueFromBytes defaultCodecFuel layouts ty bs = some v →
      validPred v

/-- Semantic model of `zerocopy::FromZeros`. -/
def IsFromZeros (layouts : LayoutTable) (ty : Ty) : Prop :=
  ∃ sz v,
    rigidTyByteSize layouts ty = some sz ∧
    decodeValueFromBytes defaultCodecFuel layouts ty (zeroInitBytes sz) = some v

/-- Semantic model of `zerocopy::FromBytes`. -/
def IsFromBytes (layouts : LayoutTable) (ty : Ty) : Prop :=
  ∃ sz,
    rigidTyByteSize layouts ty = some sz ∧
    ∀ bs,
      length bs = sz →
      allBytesInitialized bs = true →
      ∃ v, decodeValueFromBytes defaultCodecFuel layouts ty bs = some v

/-- Semantic model of `zerocopy::IntoBytes`. -/
def IsIntoBytes (layouts : LayoutTable) (ty : Ty) : Prop :=
  ∃ sz,
    rigidTyByteSize layouts ty = some sz ∧
    ∀ v bs,
      encodeValueToBytes defaultCodecFuel layouts ty v = some bs →
      length bs = sz ∧ allBytesInitialized bs = true

/-- Semantic model of `zerocopy::Unaligned` (1-byte ABI alignment). -/
def IsUnaligned (layouts : LayoutTable) (ty : Ty) : Prop :=
  tyAlignmentBytes layouts ty = some 1

/-- Enumeration of core `zerocopy` marker traits. -/
inductive ZerocopyTrait : Type where
  | tryFromBytes
  | fromZeros
  | fromBytes
  | intoBytes
  | unaligned
  deriving DecidableEq, Repr

/-- Unified trait-validity predicate dispatching on `ZerocopyTrait`. -/
@[reducible]
def ValidForTrait (tr : ZerocopyTrait) (layouts : LayoutTable) (ty : Ty) : Prop :=
  match tr with
  | .tryFromBytes => IsTryFromBytes layouts ty
  | .fromZeros => IsFromZeros layouts ty
  | .fromBytes => IsFromBytes layouts ty
  | .intoBytes => IsIntoBytes layouts ty
  | .unaligned => IsUnaligned layouts ty

theorem isFromBytes_implies_isFromZeros
    (layouts : LayoutTable) (ty : Ty) (h : IsFromBytes layouts ty) :
    IsFromZeros layouts ty := by
  rcases h with ⟨sz, hsz, hdec⟩
  rcases hdec (zeroInitBytes sz) (length_zeroInitBytes sz)
    (allBytesInitialized_zeroInitBytes sz) with ⟨v, hv⟩
  exact ⟨sz, v, hsz, hv⟩

theorem isFromBytes_implies_isTryFromBytes
    (layouts : LayoutTable) (ty : Ty) (h : IsFromBytes layouts ty) :
    IsTryFromBytes layouts ty := by
  rcases h with ⟨sz, hsz, _⟩
  exact ⟨sz, hsz, fun _ _ _ => trivial⟩

/--
Soundness of safe byte transmutation (`zerocopy::transmute!`): encoding any
valid value of an `IsIntoBytes` source type produces a byte sequence that
decodes without UB at any same-sized `IsFromBytes` destination type.
-/
theorem transmute_sound_of_into_from_bytes
    (layouts : LayoutTable) (srcTy dstTy : Ty)
    (hInto : IsIntoBytes layouts srcTy)
    (hFrom : IsFromBytes layouts dstTy)
    (hSizeEq : rigidTyByteSize layouts srcTy = rigidTyByteSize layouts dstTy)
    (v : Value) (bs : List AbstractByte)
    (hEnc : encodeValueToBytes defaultCodecFuel layouts srcTy v = some bs) :
    ∃ v', decodeValueFromBytes defaultCodecFuel layouts dstTy bs = some v' := by
  rcases hInto with ⟨szSrc, hSzSrc, hEncProps⟩
  rcases hFrom with ⟨szDst, hSzDst, hDecProps⟩
  have hEq : szSrc = szDst := by
    rw [hSzSrc, hSzDst] at hSizeEq
    exact Option.some.inj hSizeEq
  have ⟨hLen, hInit⟩ := hEncProps v bs hEnc
  exact hDecProps bs (hEq ▸ hLen) hInit

/-! ## 3. Little-Endian Scalar Codec and Primitive Trait Theorems -/

@[simp]
theorem length_encodeLittleEndianBytes (prov : Option (Nat × Nat)) :
    ∀ n bits : Nat, length (encodeLittleEndianBytes bits n prov) = n
  | 0, _ => rfl
  | k + 1, bits =>
    congrArg Nat.succ (length_encodeLittleEndianBytes prov k (bits / 256))

@[simp]
theorem allBytesInitialized_encodeLittleEndianBytes (prov : Option (Nat × Nat)) :
    ∀ n bits : Nat,
      allBytesInitialized (encodeLittleEndianBytes bits n prov) = true
  | 0, _ => rfl
  | k + 1, bits =>
    allBytesInitialized_encodeLittleEndianBytes prov k (bits / 256)

theorem encodeScalarBytes_length_and_init
    (sv : ScalarVal) (prov : Option (Nat × Nat)) (bs : List AbstractByte)
    (h : encodeScalarBytes sv prov = some bs) :
    length bs = sv.sizeBytes ∧ allBytesInitialized bs = true := by
  unfold encodeScalarBytes at h
  cases hZero : Nat.beq sv.sizeBytes 0 <;> rw [hZero] at h
  · injection h with hBs
    subst hBs
    exact ⟨length_encodeLittleEndianBytes prov sv.sizeBytes sv.bits,
           allBytesInitialized_encodeLittleEndianBytes prov sv.sizeBytes sv.bits⟩
  · nomatch h

theorem decodeLittleEndianBytes_of_allBytesInitialized :
    ∀ bs : List AbstractByte,
      allBytesInitialized bs = true →
      ∃ bits prov, decodeLittleEndianBytes bs = some (bits, prov)
  | [], _ => ⟨0, none, rfl⟩
  | .uninit :: _, h => nomatch h
  | .init b prov :: rest, h => by
    rcases decodeLittleEndianBytes_of_allBytesInitialized rest h with
      ⟨highBits, restProv, hRest⟩
    refine ⟨b.toBitVec.toNat + 256 * highBits,
            mergeByteProvenance prov restProv, ?_⟩
    simp [decodeLittleEndianBytes, hRest]

theorem decodeScalarBytes_of_allBytesInitialized
    (bs : List AbstractByte) (signed : Bool)
    (hNonEmpty : Nat.beq (length bs) 0 = false)
    (hInit : allBytesInitialized bs = true) :
    ∃ sv prov, decodeScalarBytes bs signed = some (sv, prov) := by
  rcases decodeLittleEndianBytes_of_allBytesInitialized bs hInit with
    ⟨bits, prov, hDec⟩
  refine ⟨⟨bits, length bs⟩, prov, ?_⟩
  unfold decodeScalarBytes
  simp [hNonEmpty, hDec]

private theorem uintWidth_targetBytes (w : UintTy) :
    ∃ sz, intCastTargetBytes (.uint w) = some sz ∧ Nat.beq sz 0 = false := by
  cases w <;> exact ⟨_, rfl, rfl⟩

private theorem intWidth_targetBytes (w : IntTy) :
    ∃ sz, intCastTargetBytes (.int w) = some sz ∧ Nat.beq sz 0 = false := by
  cases w <;> exact ⟨_, rfl, rfl⟩

private theorem uint_decode_anyFuel
    (fuel : Nat) (layouts : LayoutTable) (w : UintTy) (idx : LayoutIdx)
    (sz : Nat) (hSz : intCastTargetBytes (.uint w) = some sz)
    (hNz : Nat.beq sz 0 = false) (bs : List AbstractByte)
    (hLen : length bs = sz) (hInit : allBytesInitialized bs = true) :
    ∃ v,
      decodeValueFromBytes (fuel + 1) layouts { kind := .uint w, layoutIdx := idx }
        bs = some v := by
  rcases decodeScalarBytes_of_allBytesInitialized bs false (hLen ▸ hNz) hInit
    with ⟨sv, prov, hDec⟩
  refine ⟨.scalar sv, ?_⟩
  have hBeq : Nat.beq (length bs) sz = true := by simp [hLen]
  unfold decodeValueFromBytes
  simp [hSz, hBeq, hDec]

private theorem int_decode_anyFuel
    (fuel : Nat) (layouts : LayoutTable) (w : IntTy) (idx : LayoutIdx)
    (sz : Nat) (hSz : intCastTargetBytes (.int w) = some sz)
    (hNz : Nat.beq sz 0 = false) (bs : List AbstractByte)
    (hLen : length bs = sz) (hInit : allBytesInitialized bs = true) :
    ∃ v,
      decodeValueFromBytes (fuel + 1) layouts { kind := .int w, layoutIdx := idx }
        bs = some v := by
  rcases decodeScalarBytes_of_allBytesInitialized bs true (hLen ▸ hNz) hInit
    with ⟨sv, prov, hDec⟩
  refine ⟨.scalar sv, ?_⟩
  have hBeq : Nat.beq (length bs) sz = true := by simp [hLen]
  unfold decodeValueFromBytes
  simp [hSz, hBeq, hDec]

private theorem uint_encode_anyFuel
    (fuel : Nat) (layouts : LayoutTable) (w : UintTy) (idx : LayoutIdx)
    (sz : Nat) (hSz : intCastTargetBytes (.uint w) = some sz)
    (v : Value) (bs : List AbstractByte)
    (hEnc :
      encodeValueToBytes (fuel + 1) layouts { kind := .uint w, layoutIdx := idx }
        v = some bs) :
    length bs = sz ∧ allBytesInitialized bs = true := by
  unfold encodeValueToBytes at hEnc
  cases v <;> simp [hSz] at hEnc
  case scalar sv =>
    cases hEq : Nat.beq sv.sizeBytes sz <;> rw [hEq] at hEnc
    · nomatch hEnc
    · have hSvSz : sv.sizeBytes = sz := Nat.eq_of_beq_eq_true hEq
      have ⟨hLen, hInit⟩ := encodeScalarBytes_length_and_init sv none bs hEnc
      exact ⟨hSvSz ▸ hLen, hInit⟩

private theorem int_encode_anyFuel
    (fuel : Nat) (layouts : LayoutTable) (w : IntTy) (idx : LayoutIdx)
    (sz : Nat) (hSz : intCastTargetBytes (.int w) = some sz)
    (v : Value) (bs : List AbstractByte)
    (hEnc :
      encodeValueToBytes (fuel + 1) layouts { kind := .int w, layoutIdx := idx }
        v = some bs) :
    length bs = sz ∧ allBytesInitialized bs = true := by
  unfold encodeValueToBytes at hEnc
  cases v <;> simp [hSz] at hEnc
  case scalar sv =>
    cases hEq : Nat.beq sv.sizeBytes sz <;> rw [hEq] at hEnc
    · nomatch hEnc
    · have hSvSz : sv.sizeBytes = sz := Nat.eq_of_beq_eq_true hEq
      have ⟨hLen, hInit⟩ := encodeScalarBytes_length_and_init sv none bs hEnc
      exact ⟨hSvSz ▸ hLen, hInit⟩

/-- Every unsigned integer type `uN` satisfies `IsFromBytes`. -/
theorem uint_isFromBytes
    (layouts : LayoutTable) (w : UintTy) (idx : LayoutIdx) :
    IsFromBytes layouts { kind := .uint w, layoutIdx := idx } := by
  rcases uintWidth_targetBytes w with ⟨sz, hSz, hNz⟩
  refine ⟨sz, by simp [rigidTyByteSize, rigidTyKindByteSize, hSz], ?_⟩
  intro bs hLen hInit
  exact uint_decode_anyFuel 15 layouts w idx sz hSz hNz bs hLen hInit

/-- Every unsigned integer type `uN` satisfies `IsIntoBytes`. -/
theorem uint_isIntoBytes
    (layouts : LayoutTable) (w : UintTy) (idx : LayoutIdx) :
    IsIntoBytes layouts { kind := .uint w, layoutIdx := idx } := by
  rcases uintWidth_targetBytes w with ⟨sz, hSz, _⟩
  refine ⟨sz, by simp [rigidTyByteSize, rigidTyKindByteSize, hSz], ?_⟩
  intro v bs hEnc
  exact uint_encode_anyFuel 15 layouts w idx sz hSz v bs hEnc

/-- Every signed integer type `iN` satisfies `IsFromBytes`. -/
theorem int_isFromBytes
    (layouts : LayoutTable) (w : IntTy) (idx : LayoutIdx) :
    IsFromBytes layouts { kind := .int w, layoutIdx := idx } := by
  rcases intWidth_targetBytes w with ⟨sz, hSz, hNz⟩
  refine ⟨sz, by simp [rigidTyByteSize, rigidTyKindByteSize, hSz], ?_⟩
  intro bs hLen hInit
  exact int_decode_anyFuel 15 layouts w idx sz hSz hNz bs hLen hInit

/-- Every signed integer type `iN` satisfies `IsIntoBytes`. -/
theorem int_isIntoBytes
    (layouts : LayoutTable) (w : IntTy) (idx : LayoutIdx) :
    IsIntoBytes layouts { kind := .int w, layoutIdx := idx } := by
  rcases intWidth_targetBytes w with ⟨sz, hSz, _⟩
  refine ⟨sz, by simp [rigidTyByteSize, rigidTyKindByteSize, hSz], ?_⟩
  intro v bs hEnc
  exact int_encode_anyFuel 15 layouts w idx sz hSz v bs hEnc

theorem u8_isFromBytes (layouts : LayoutTable) (idx : LayoutIdx) :
    IsFromBytes layouts { kind := .uint .u8, layoutIdx := idx } :=
  uint_isFromBytes layouts .u8 idx

theorem u8_isIntoBytes (layouts : LayoutTable) (idx : LayoutIdx) :
    IsIntoBytes layouts { kind := .uint .u8, layoutIdx := idx } :=
  uint_isIntoBytes layouts .u8 idx

theorem u16_isFromBytes (layouts : LayoutTable) (idx : LayoutIdx) :
    IsFromBytes layouts { kind := .uint .u16, layoutIdx := idx } :=
  uint_isFromBytes layouts .u16 idx

theorem u16_isIntoBytes (layouts : LayoutTable) (idx : LayoutIdx) :
    IsIntoBytes layouts { kind := .uint .u16, layoutIdx := idx } :=
  uint_isIntoBytes layouts .u16 idx

theorem u32_isFromBytes (layouts : LayoutTable) (idx : LayoutIdx) :
    IsFromBytes layouts { kind := .uint .u32, layoutIdx := idx } :=
  uint_isFromBytes layouts .u32 idx

theorem u32_isIntoBytes (layouts : LayoutTable) (idx : LayoutIdx) :
    IsIntoBytes layouts { kind := .uint .u32, layoutIdx := idx } :=
  uint_isIntoBytes layouts .u32 idx

theorem u64_isFromBytes (layouts : LayoutTable) (idx : LayoutIdx) :
    IsFromBytes layouts { kind := .uint .u64, layoutIdx := idx } :=
  uint_isFromBytes layouts .u64 idx

theorem u64_isIntoBytes (layouts : LayoutTable) (idx : LayoutIdx) :
    IsIntoBytes layouts { kind := .uint .u64, layoutIdx := idx } :=
  uint_isIntoBytes layouts .u64 idx

/-- `()` (`.tuple []`) satisfies `IsFromBytes`. -/
theorem unit_isFromBytes (layouts : LayoutTable) (idx : LayoutIdx) :
    IsFromBytes layouts { kind := .tuple [], layoutIdx := idx } := by
  refine ⟨0, rfl, ?_⟩
  intro bs hLen _
  cases bs with
  | nil => exact ⟨.unit, rfl⟩
  | cons _ _ => nomatch hLen

/-- `()` (`.tuple []`) satisfies `IsIntoBytes`. -/
theorem unit_isIntoBytes (layouts : LayoutTable) (idx : LayoutIdx) :
    IsIntoBytes layouts { kind := .tuple [], layoutIdx := idx } := by
  refine ⟨0, rfl, ?_⟩
  intro v bs hEnc
  unfold defaultCodecFuel encodeValueToBytes at hEnc
  cases v with
  | unit =>
    injection hEnc with hBs
    subst hBs
    exact ⟨rfl, rfl⟩
  | aggregate varIdx fs =>
    match varIdx, fs with
    | 0, [] =>
      injection hEnc with hBs
      subst hBs
      exact ⟨rfl, rfl⟩
    | _ + 1, _ | 0, _ :: _ => nomatch hEnc
  | _ => nomatch hEnc

/-- `bool` satisfies `IsIntoBytes` and `IsFromZeros`, but NOT `IsFromBytes`. -/
private theorem bool_encode_anyFuel
    (fuel : Nat) (layouts : LayoutTable) (idx : LayoutIdx)
    (v : Value) (bs : List AbstractByte)
    (hEnc :
      encodeValueToBytes (fuel + 1) layouts { kind := .bool, layoutIdx := idx }
        v = some bs) :
    length bs = 1 ∧ allBytesInitialized bs = true := by
  unfold encodeValueToBytes at hEnc
  cases v with
  | scalar sv =>
    dsimp only at hEnc
    cases h1 : Nat.beq sv.sizeBytes 1 <;> rw [h1] at hEnc
    · nomatch hEnc
    · dsimp only at hEnc
      cases h0 : Nat.beq sv.bits 0 <;> rw [h0] at hEnc
      · dsimp only at hEnc
        cases hb1 : Nat.beq sv.bits 1 <;> rw [hb1] at hEnc
        · nomatch hEnc
        · injection hEnc with hBs; subst hBs; exact ⟨rfl, rfl⟩
      · injection hEnc with hBs; subst hBs; exact ⟨rfl, rfl⟩
  | _ => nomatch hEnc

theorem bool_isIntoBytes (layouts : LayoutTable) (idx : LayoutIdx) :
    IsIntoBytes layouts { kind := .bool, layoutIdx := idx } := by
  refine ⟨1, rfl, ?_⟩
  intro v bs hEnc
  exact bool_encode_anyFuel 15 layouts idx v bs hEnc

theorem bool_isFromZeros (layouts : LayoutTable) (idx : LayoutIdx) :
    IsFromZeros layouts { kind := .bool, layoutIdx := idx } :=
  ⟨1, .scalar ⟨0, 1⟩, rfl, rfl⟩

theorem bool_not_isFromBytes (layouts : LayoutTable) (idx : LayoutIdx) :
    ¬ IsFromBytes layouts { kind := .bool, layoutIdx := idx } := by
  rintro ⟨sz, hSz, hDec⟩
  injection hSz with hSz1
  subst hSz1
  rcases hDec [.init (UInt8.ofNat 2) none] rfl rfl with ⟨v, hv⟩
  nomatch hv

/-- `bool` satisfies `IsTryFromBytes` with validity predicate `bits ≤ 1`. -/
theorem bool_isTryFromBytes (layouts : LayoutTable) (idx : LayoutIdx) :
    IsTryFromBytes layouts { kind := .bool, layoutIdx := idx }
      (fun v => ∃ bits, bits ≤ 1 ∧ v = .scalar ⟨bits, 1⟩) := by
  refine ⟨1, rfl, ?_⟩
  intro bs v hDec
  unfold defaultCodecFuel decodeValueFromBytes at hDec
  cases bs with
  | nil => nomatch hDec
  | cons b0 rest =>
    cases b0 with
    | uninit => nomatch hDec
    | init b prov =>
      cases rest with
      | cons _ _ => nomatch hDec
      | nil =>
        dsimp only at hDec
        cases h0 : Nat.beq b.toBitVec.toNat 0 <;> rw [h0] at hDec
        · dsimp only at hDec
          cases h1 : Nat.beq b.toBitVec.toNat 1 <;> rw [h1] at hDec
          · nomatch hDec
          · injection hDec with hV
            exact ⟨1, Nat.le_refl 1, hV.symm⟩
        · injection hDec with hV
          exact ⟨0, Nat.zero_le 1, hV.symm⟩

private theorem char_encode_anyFuel
    (fuel : Nat) (layouts : LayoutTable) (idx : LayoutIdx)
    (v : Value) (bs : List AbstractByte)
    (hEnc :
      encodeValueToBytes (fuel + 1) layouts { kind := .char, layoutIdx := idx }
        v = some bs) :
    length bs = 4 ∧ allBytesInitialized bs = true := by
  unfold encodeValueToBytes at hEnc
  cases v with
  | scalar sv =>
    dsimp only at hEnc
    cases hCond : Bool.and (Nat.beq sv.sizeBytes 4) (isValidCharCode sv.bits) <;>
      rw [hCond] at hEnc
    · nomatch hEnc
    · simp only [Bool.and_eq_true] at hCond
      have hSz : sv.sizeBytes = 4 := Nat.eq_of_beq_eq_true hCond.1
      have ⟨hLen, hInit⟩ := encodeScalarBytes_length_and_init sv none bs hEnc
      exact ⟨hSz ▸ hLen, hInit⟩
  | _ => nomatch hEnc

/-- `char` satisfies `IsIntoBytes` and `IsFromZeros`, but NOT `IsFromBytes`. -/
theorem char_isIntoBytes (layouts : LayoutTable) (idx : LayoutIdx) :
    IsIntoBytes layouts { kind := .char, layoutIdx := idx } := by
  refine ⟨4, rfl, ?_⟩
  intro v bs hEnc
  exact char_encode_anyFuel 15 layouts idx v bs hEnc

theorem char_isFromZeros (layouts : LayoutTable) (idx : LayoutIdx) :
    IsFromZeros layouts { kind := .char, layoutIdx := idx } :=
  ⟨4, .scalar ⟨0, 4⟩, rfl, rfl⟩

theorem char_not_isFromBytes (layouts : LayoutTable) (idx : LayoutIdx) :
    ¬ IsFromBytes layouts { kind := .char, layoutIdx := idx } := by
  rintro ⟨sz, hSz, hDec⟩
  injection hSz with hSz4
  subst hSz4
  rcases hDec
    [.init (UInt8.ofNat 0) none,
     .init (UInt8.ofNat 216) none,
     .init (UInt8.ofNat 0) none,
     .init (UInt8.ofNat 0) none]
    rfl rfl with ⟨v, hv⟩
  nomatch hv

/-- `char` satisfies `IsTryFromBytes` with validity predicate `isValidCharCode bits = true`. -/
theorem char_isTryFromBytes (layouts : LayoutTable) (idx : LayoutIdx) :
    IsTryFromBytes layouts { kind := .char, layoutIdx := idx }
      (fun v => ∃ bits, isValidCharCode bits = true ∧ v = .scalar ⟨bits, 4⟩) := by
  refine ⟨4, rfl, ?_⟩
  intro bs v hDec
  unfold defaultCodecFuel decodeValueFromBytes at hDec
  dsimp only at hDec
  cases hLen : Nat.beq (length bs) 4 <;> rw [hLen] at hDec
  · nomatch hDec
  · dsimp only at hDec
    cases hSc : decodeScalarBytes bs false <;> rw [hSc] at hDec
    · nomatch hDec
    case some pair =>
      rcases pair with ⟨sv, prov⟩
      dsimp only at hDec
      cases hValid : isValidCharCode sv.bits <;> rw [hValid] at hDec
      · nomatch hDec
      · injection hDec with hV
        unfold decodeScalarBytes at hSc
        dsimp only at hSc
        cases hEmpty : Nat.beq (length bs) 0 <;> rw [hEmpty] at hSc
        · cases hLE : decodeLittleEndianBytes bs <;> rw [hLE] at hSc
          · nomatch hSc
          case some bp =>
            rcases bp with ⟨bits, p⟩
            injection hSc with hPair
            injection hPair with hSv _
            have hBsLen : length bs = 4 := Nat.eq_of_beq_eq_true hLen
            subst hSv
            refine ⟨bits, hValid, ?_⟩
            rw [← hV, hBsLen]
        · nomatch hSc

/-! ## 4. Homogeneous Array Combinators (`[T; n]`) -/

theorem decodeArrayChunksWith_of_allBytesInitialized
    (decodeElem : List AbstractByte → Option Value) (elemSz : Nat)
    (hElem :
      ∀ chunk,
        length chunk = elemSz →
        allBytesInitialized chunk = true →
        ∃ v, decodeElem chunk = some v) :
    ∀ (n : Nat) (bs : List AbstractByte),
      length bs = elemSz * n →
      allBytesInitialized bs = true →
      ∃ elems, decodeArrayChunksWith decodeElem elemSz n bs = some elems
  | 0, [], _, _ => ⟨[], rfl⟩
  | 0, _ :: _, hLen, _ => by simp [length] at hLen
  | k + 1, bs, hLen, hInit => by
    have hMul : elemSz * (k + 1) = elemSz * k + elemSz := Nat.mul_succ elemSz k
    have hLe : elemSz ≤ bs.length := by
      simp [length] at hLen; omega
    have hBle : Nat.ble elemSz (length bs) = true := Nat.ble_eq_true_of_le hLe
    have hChunkLen : length (bs.take elemSz) = elemSz := by
      simp [length, List.length_take]; omega
    have hRestLen : length (bs.drop elemSz) = elemSz * k := by
      simp [length, List.length_drop] at hLen ⊢
      omega
    rcases hElem (bs.take elemSz) hChunkLen (allBytesInitialized_take elemSz hInit)
      with ⟨v, hV⟩
    rcases decodeArrayChunksWith_of_allBytesInitialized decodeElem elemSz hElem
      k (bs.drop elemSz) hRestLen (allBytesInitialized_drop elemSz hInit)
      with ⟨vs, hVs⟩
    refine ⟨v :: vs, ?_⟩
    unfold decodeArrayChunksWith
    simp [hBle, hV, hVs]

theorem encodeListWith_length_and_init
    (encodeElem : Value → Option (List AbstractByte)) (elemSz : Nat)
    (hElem : ∀ e eBs, encodeElem e = some eBs → allBytesInitialized eBs = true) :
    ∀ (elems : List Value) (bs : List AbstractByte),
      encodeListWith encodeElem elemSz elems = some bs →
      length bs = elemSz * length elems ∧ allBytesInitialized bs = true
  | [], bs, hEnc => by
    injection hEnc with hBs; subst hBs; simp [length]
  | v :: rest, bs, hEnc => by
    unfold encodeListWith at hEnc
    cases hEv : encodeElem v <;> rw [hEv] at hEnc
    · nomatch hEnc
    case some eBs =>
      dsimp only at hEnc
      cases hEq : Nat.beq (length eBs) elemSz <;> rw [hEq] at hEnc
      · nomatch hEnc
      · dsimp only at hEnc
        cases hRest : encodeListWith encodeElem elemSz rest <;> rw [hRest] at hEnc
        · nomatch hEnc
        case some restBs =>
          injection hEnc with hBs; subst hBs
          rw [appendAbstractBytes_eq_append]
          have hEBsLen : eBs.length = elemSz := Nat.eq_of_beq_eq_true hEq
          have ⟨hRLen, hRInit⟩ :=
            encodeListWith_length_and_init encodeElem elemSz hElem rest restBs hRest
          refine ⟨?_, allBytesInitialized_append (hElem v eBs hEv) hRInit⟩
          simp [length, hEBsLen] at hRLen ⊢
          have : elemSz * (rest.length + 1) = elemSz * rest.length + elemSz :=
            Nat.mul_succ elemSz rest.length
          omega

private theorem array_uint_decode_anyFuel
    (fuel : Nat) (layouts : LayoutTable) (w : UintTy) (n : Nat)
    (idx : LayoutIdx) (sz : Nat) (hSz : intCastTargetBytes (.uint w) = some sz)
    (hNz : Nat.beq sz 0 = false) (bs : List AbstractByte)
    (hLen : length bs = sz * n) (hInit : allBytesInitialized bs = true) :
    ∃ v,
      decodeValueFromBytes (fuel + 2) layouts
        { kind := .array (.uint w) n, layoutIdx := idx } bs = some v := by
  cases n with
  | zero =>
    cases bs with
    | nil => exact ⟨.aggregate 0 [], rfl⟩
    | cons _ _ => simp [length] at hLen
  | succ k =>
    rcases decodeArrayChunksWith_of_allBytesInitialized
      (fun chunk =>
        decodeValueFromBytes (fuel + 1) layouts { kind := .uint w, layoutIdx := 0 }
          chunk)
      sz
      (fun chunk hCL hCI => uint_decode_anyFuel fuel layouts w 0 sz hSz hNz chunk hCL hCI)
      (k + 1) bs hLen hInit with ⟨elems, hElems⟩
    refine ⟨.aggregate 0 elems, ?_⟩
    have hK : Nat.beq (k + 1) 0 = false := rfl
    have hBeq : Nat.beq (length bs) (sz * (k + 1)) = true := by simp [hLen]
    unfold decodeValueFromBytes
    simp [rigidTyKindByteSize, hK, hSz, hBeq, hElems]

private theorem array_uint_encode_anyFuel
    (fuel : Nat) (layouts : LayoutTable) (w : UintTy) (n : Nat)
    (idx : LayoutIdx) (sz : Nat) (hSz : intCastTargetBytes (.uint w) = some sz)
    (v : Value) (bs : List AbstractByte)
    (hEnc :
      encodeValueToBytes (fuel + 2) layouts
        { kind := .array (.uint w) n, layoutIdx := idx } v = some bs) :
    length bs = sz * n ∧ allBytesInitialized bs = true := by
  cases n with
  | zero =>
    unfold encodeValueToBytes at hEnc
    cases v with
    | unit => injection hEnc with hBs; subst hBs; simp [length]
    | aggregate varIdx fs =>
      match varIdx, fs with
      | 0, [] => injection hEnc with hBs; subst hBs; simp [length]
      | _ + 1, _ | 0, _ :: _ => nomatch hEnc
    | _ => nomatch hEnc
  | succ k =>
    unfold encodeValueToBytes at hEnc
    have hK : Nat.beq (k + 1) 0 = false := rfl
    cases v with
    | aggregate varIdx elems =>
      cases varIdx with
      | succ _ => nomatch hEnc
      | zero =>
        simp only [rigidTyKindByteSize, hK, hSz] at hEnc
        cases hLenEq : Nat.beq (length elems) (k + 1) <;> rw [hLenEq] at hEnc
        · nomatch hEnc
        · dsimp only at hEnc
          have ⟨hBLen, hBInit⟩ :=
            encodeListWith_length_and_init
              (fun e =>
                encodeValueToBytes (fuel + 1) layouts
                  { kind := .uint w, layoutIdx := 0 } e)
              sz
              (fun e eBs hE => (uint_encode_anyFuel fuel layouts w 0 sz hSz e eBs hE).2)
              elems bs hEnc
          have hELen : length elems = k + 1 := Nat.eq_of_beq_eq_true hLenEq
          exact ⟨hELen ▸ hBLen, hBInit⟩
    | _ => nomatch hEnc

private theorem array_int_decode_anyFuel
    (fuel : Nat) (layouts : LayoutTable) (w : IntTy) (n : Nat)
    (idx : LayoutIdx) (sz : Nat) (hSz : intCastTargetBytes (.int w) = some sz)
    (hNz : Nat.beq sz 0 = false) (bs : List AbstractByte)
    (hLen : length bs = sz * n) (hInit : allBytesInitialized bs = true) :
    ∃ v,
      decodeValueFromBytes (fuel + 2) layouts
        { kind := .array (.int w) n, layoutIdx := idx } bs = some v := by
  cases n with
  | zero =>
    cases bs with
    | nil => exact ⟨.aggregate 0 [], rfl⟩
    | cons _ _ => simp [length] at hLen
  | succ k =>
    rcases decodeArrayChunksWith_of_allBytesInitialized
      (fun chunk =>
        decodeValueFromBytes (fuel + 1) layouts { kind := .int w, layoutIdx := 0 }
          chunk)
      sz
      (fun chunk hCL hCI => int_decode_anyFuel fuel layouts w 0 sz hSz hNz chunk hCL hCI)
      (k + 1) bs hLen hInit with ⟨elems, hElems⟩
    refine ⟨.aggregate 0 elems, ?_⟩
    have hK : Nat.beq (k + 1) 0 = false := rfl
    have hBeq : Nat.beq (length bs) (sz * (k + 1)) = true := by simp [hLen]
    unfold decodeValueFromBytes
    simp [rigidTyKindByteSize, hK, hSz, hBeq, hElems]

private theorem array_int_encode_anyFuel
    (fuel : Nat) (layouts : LayoutTable) (w : IntTy) (n : Nat)
    (idx : LayoutIdx) (sz : Nat) (hSz : intCastTargetBytes (.int w) = some sz)
    (v : Value) (bs : List AbstractByte)
    (hEnc :
      encodeValueToBytes (fuel + 2) layouts
        { kind := .array (.int w) n, layoutIdx := idx } v = some bs) :
    length bs = sz * n ∧ allBytesInitialized bs = true := by
  cases n with
  | zero =>
    unfold encodeValueToBytes at hEnc
    cases v with
    | unit => injection hEnc with hBs; subst hBs; simp [length]
    | aggregate varIdx fs =>
      match varIdx, fs with
      | 0, [] => injection hEnc with hBs; subst hBs; simp [length]
      | _ + 1, _ | 0, _ :: _ => nomatch hEnc
    | _ => nomatch hEnc
  | succ k =>
    unfold encodeValueToBytes at hEnc
    have hK : Nat.beq (k + 1) 0 = false := rfl
    cases v with
    | aggregate varIdx elems =>
      cases varIdx with
      | succ _ => nomatch hEnc
      | zero =>
        simp only [rigidTyKindByteSize, hK, hSz] at hEnc
        cases hLenEq : Nat.beq (length elems) (k + 1) <;> rw [hLenEq] at hEnc
        · nomatch hEnc
        · dsimp only at hEnc
          have ⟨hBLen, hBInit⟩ :=
            encodeListWith_length_and_init
              (fun e =>
                encodeValueToBytes (fuel + 1) layouts
                  { kind := .int w, layoutIdx := 0 } e)
              sz
              (fun e eBs hE => (int_encode_anyFuel fuel layouts w 0 sz hSz e eBs hE).2)
              elems bs hEnc
          have hELen : length elems = k + 1 := Nat.eq_of_beq_eq_true hLenEq
          exact ⟨hELen ▸ hBLen, hBInit⟩
    | _ => nomatch hEnc

theorem array_uint_isFromBytes
    (layouts : LayoutTable) (w : UintTy) (n : Nat) (idx : LayoutIdx) :
    IsFromBytes layouts { kind := .array (.uint w) n, layoutIdx := idx } := by
  rcases uintWidth_targetBytes w with ⟨sz, hSz, hNz⟩
  refine ⟨sz * n, by simp [rigidTyByteSize, rigidTyKindByteSize, hSz], ?_⟩
  exact array_uint_decode_anyFuel 14 layouts w n idx sz hSz hNz

theorem array_uint_isIntoBytes
    (layouts : LayoutTable) (w : UintTy) (n : Nat) (idx : LayoutIdx) :
    IsIntoBytes layouts { kind := .array (.uint w) n, layoutIdx := idx } := by
  rcases uintWidth_targetBytes w with ⟨sz, hSz, _⟩
  refine ⟨sz * n, by simp [rigidTyByteSize, rigidTyKindByteSize, hSz], ?_⟩
  exact array_uint_encode_anyFuel 14 layouts w n idx sz hSz

theorem array_int_isFromBytes
    (layouts : LayoutTable) (w : IntTy) (n : Nat) (idx : LayoutIdx) :
    IsFromBytes layouts { kind := .array (.int w) n, layoutIdx := idx } := by
  rcases intWidth_targetBytes w with ⟨sz, hSz, hNz⟩
  refine ⟨sz * n, by simp [rigidTyByteSize, rigidTyKindByteSize, hSz], ?_⟩
  exact array_int_decode_anyFuel 14 layouts w n idx sz hSz hNz

theorem array_int_isIntoBytes
    (layouts : LayoutTable) (w : IntTy) (n : Nat) (idx : LayoutIdx) :
    IsIntoBytes layouts { kind := .array (.int w) n, layoutIdx := idx } := by
  rcases intWidth_targetBytes w with ⟨sz, hSz, _⟩
  refine ⟨sz * n, by simp [rigidTyByteSize, rigidTyKindByteSize, hSz], ?_⟩
  exact array_int_encode_anyFuel 14 layouts w n idx sz hSz

theorem array_u8_n_isFromBytes
    (layouts : LayoutTable) (n : Nat) (idx : LayoutIdx) :
    IsFromBytes layouts { kind := .array (.uint .u8) n, layoutIdx := idx } :=
  array_uint_isFromBytes layouts .u8 n idx

theorem array_u8_n_isIntoBytes
    (layouts : LayoutTable) (n : Nat) (idx : LayoutIdx) :
    IsIntoBytes layouts { kind := .array (.uint .u8) n, layoutIdx := idx } :=
  array_uint_isIntoBytes layouts .u8 n idx

theorem array_u8_n_isFromZeros
    (layouts : LayoutTable) (n : Nat) (idx : LayoutIdx) :
    IsFromZeros layouts { kind := .array (.uint .u8) n, layoutIdx := idx } :=
  isFromBytes_implies_isFromZeros _ _ (array_u8_n_isFromBytes layouts n idx)

private theorem array_bool_encode_anyFuel
    (fuel : Nat) (layouts : LayoutTable) (n : Nat)
    (idx : LayoutIdx) (v : Value) (bs : List AbstractByte)
    (hEnc :
      encodeValueToBytes (fuel + 2) layouts
        { kind := .array .bool n, layoutIdx := idx } v = some bs) :
    length bs = 1 * n ∧ allBytesInitialized bs = true := by
  cases n with
  | zero =>
    unfold encodeValueToBytes at hEnc
    cases v with
    | unit => injection hEnc with hBs; subst hBs; simp [length]
    | aggregate varIdx fs =>
      match varIdx, fs with
      | 0, [] => injection hEnc with hBs; subst hBs; simp [length]
      | _ + 1, _ | 0, _ :: _ => nomatch hEnc
    | _ => nomatch hEnc
  | succ k =>
    unfold encodeValueToBytes at hEnc
    have hK : Nat.beq (k + 1) 0 = false := rfl
    cases v with
    | aggregate varIdx elems =>
      cases varIdx with
      | succ _ => nomatch hEnc
      | zero =>
        simp only [hK] at hEnc
        cases hLenEq : Nat.beq (length elems) (k + 1) <;> rw [hLenEq] at hEnc
        · nomatch hEnc
        · dsimp only at hEnc
          have ⟨hBLen, hBInit⟩ :=
            encodeListWith_length_and_init
              (fun e =>
                encodeValueToBytes (fuel + 1) layouts
                  { kind := .bool, layoutIdx := 0 } e)
              1
              (fun e eBs hE => (bool_encode_anyFuel fuel layouts 0 e eBs hE).2)
              elems bs hEnc
          have hELen : length elems = k + 1 := Nat.eq_of_beq_eq_true hLenEq
          exact ⟨hELen ▸ hBLen, hBInit⟩
    | _ => nomatch hEnc

private theorem array_char_encode_anyFuel
    (fuel : Nat) (layouts : LayoutTable) (n : Nat)
    (idx : LayoutIdx) (v : Value) (bs : List AbstractByte)
    (hEnc :
      encodeValueToBytes (fuel + 2) layouts
        { kind := .array .char n, layoutIdx := idx } v = some bs) :
    length bs = 4 * n ∧ allBytesInitialized bs = true := by
  cases n with
  | zero =>
    unfold encodeValueToBytes at hEnc
    cases v with
    | unit => injection hEnc with hBs; subst hBs; simp [length]
    | aggregate varIdx fs =>
      match varIdx, fs with
      | 0, [] => injection hEnc with hBs; subst hBs; simp [length]
      | _ + 1, _ | 0, _ :: _ => nomatch hEnc
    | _ => nomatch hEnc
  | succ k =>
    unfold encodeValueToBytes at hEnc
    have hK : Nat.beq (k + 1) 0 = false := rfl
    cases v with
    | aggregate varIdx elems =>
      cases varIdx with
      | succ _ => nomatch hEnc
      | zero =>
        simp only [hK] at hEnc
        cases hLenEq : Nat.beq (length elems) (k + 1) <;> rw [hLenEq] at hEnc
        · nomatch hEnc
        · dsimp only at hEnc
          have ⟨hBLen, hBInit⟩ :=
            encodeListWith_length_and_init
              (fun e =>
                encodeValueToBytes (fuel + 1) layouts
                  { kind := .char, layoutIdx := 0 } e)
              4
              (fun e eBs hE => (char_encode_anyFuel fuel layouts 0 e eBs hE).2)
              elems bs hEnc
          have hELen : length elems = k + 1 := Nat.eq_of_beq_eq_true hLenEq
          exact ⟨hELen ▸ hBLen, hBInit⟩
    | _ => nomatch hEnc

/-- Homogeneous boolean arrays `[bool; n]` satisfy `IsIntoBytes`. -/
theorem array_bool_isIntoBytes
    (layouts : LayoutTable) (n : Nat) (idx : LayoutIdx) :
    IsIntoBytes layouts { kind := .array .bool n, layoutIdx := idx } := by
  refine ⟨1 * n, by simp [rigidTyByteSize], ?_⟩
  exact array_bool_encode_anyFuel 14 layouts n idx

/-- Homogeneous character arrays `[char; n]` satisfy `IsIntoBytes`. -/
theorem array_char_isIntoBytes
    (layouts : LayoutTable) (n : Nat) (idx : LayoutIdx) :
    IsIntoBytes layouts { kind := .array .char n, layoutIdx := idx } := by
  refine ⟨4 * n, by simp [rigidTyByteSize], ?_⟩
  exact array_char_encode_anyFuel 14 layouts n idx

/-! ## 5. Decidable Layout Certificate Checkers -/

/-- Decidable certificate checker for `IsUnaligned`. -/
@[reducible]
def checkUnaligned (layouts : LayoutTable) (ty : Ty) : Bool :=
  match tyAlignmentBytes layouts ty with
  | some a => a == 1
  | none => false

theorem checkUnaligned_sound
    (layouts : LayoutTable) (ty : Ty)
    (h : checkUnaligned layouts ty = true) :
    IsUnaligned layouts ty := by
  unfold checkUnaligned IsUnaligned at *
  cases hA : tyAlignmentBytes layouts ty <;> rw [hA] at h
  · nomatch h
  case some a =>
    simp at h
    exact congrArg some h

theorem checkValidForTrait_unaligned_sound
    (layouts : LayoutTable) (ty : Ty)
    (h : checkUnaligned layouts ty = true) :
    ValidForTrait .unaligned layouts ty :=
  checkUnaligned_sound layouts ty h

/-- Decidable certificate checker for `IsFromZeros`. -/
@[reducible]
def checkFromZeros (layouts : LayoutTable) (ty : Ty) : Bool :=
  match rigidTyByteSize layouts ty with
  | none => false
  | some sz =>
    (decodeValueFromBytes defaultCodecFuel layouts ty (zeroInitBytes sz)).isSome

theorem checkFromZeros_sound
    (layouts : LayoutTable) (ty : Ty)
    (h : checkFromZeros layouts ty = true) :
    IsFromZeros layouts ty := by
  unfold checkFromZeros IsFromZeros at *
  cases hSz : rigidTyByteSize layouts ty <;> rw [hSz] at h
  · nomatch h
  case some sz =>
    dsimp only [Option.isSome] at h
    cases hDec :
        decodeValueFromBytes defaultCodecFuel layouts ty (zeroInitBytes sz) <;>
      rw [hDec] at h
    · nomatch h
    case some v =>
      exact ⟨sz, v, rfl, hDec⟩

theorem checkValidForTrait_fromZeros_sound
    (layouts : LayoutTable) (ty : Ty)
    (h : checkFromZeros layouts ty = true) :
    ValidForTrait .fromZeros layouts ty :=
  checkFromZeros_sound layouts ty h

/-- Base `RigidTy` kinds that satisfy both `FromBytes` and `IntoBytes`. -/
def checkBaseFromBytesKind : RigidTy → Bool
  | .uint _ | .int _ | .tuple []
  | .array (.uint _) _ | .array (.int _) _ => true
  | _ => false

private theorem checkBaseFromBytesKind_decode_anyFuel
    (fuel : Nat) (layouts : LayoutTable) (k : RigidTy) (idx : LayoutIdx)
    (fSz : Nat) (hBase : checkBaseFromBytesKind k = true)
    (hFSz : rigidTyKindByteSize k = some fSz)
    (bs : List AbstractByte) (hLen : length bs = fSz)
    (hInit : allBytesInitialized bs = true) :
    ∃ v,
      decodeValueFromBytes (fuel + 2) layouts { kind := k, layoutIdx := idx } bs =
        some v := by
  cases k with
  | uint w =>
    rcases uintWidth_targetBytes w with ⟨sz, hSz, hNz⟩
    simp [rigidTyKindByteSize, hSz] at hFSz
    subst hFSz
    exact uint_decode_anyFuel (fuel + 1) layouts w idx sz hSz hNz bs hLen hInit
  | int w =>
    rcases intWidth_targetBytes w with ⟨sz, hSz, hNz⟩
    simp [rigidTyKindByteSize, hSz] at hFSz
    subst hFSz
    exact int_decode_anyFuel (fuel + 1) layouts w idx sz hSz hNz bs hLen hInit
  | tuple ks =>
    cases ks with
    | nil =>
      simp [rigidTyKindByteSize] at hFSz
      subst hFSz
      cases bs with
      | nil => exact ⟨.unit, rfl⟩
      | cons _ _ => nomatch hLen
    | cons _ _ => nomatch hBase
  | array elem n =>
    cases elem with
    | uint w =>
      rcases uintWidth_targetBytes w with ⟨sz, hSz, hNz⟩
      simp [rigidTyKindByteSize, hSz] at hFSz
      subst hFSz
      exact array_uint_decode_anyFuel fuel layouts w n idx sz hSz hNz bs hLen hInit
    | int w =>
      rcases intWidth_targetBytes w with ⟨sz, hSz, hNz⟩
      simp [rigidTyKindByteSize, hSz] at hFSz
      subst hFSz
      exact array_int_decode_anyFuel fuel layouts w n idx sz hSz hNz bs hLen hInit
    | _ => nomatch hBase
  | _ => nomatch hBase

private theorem checkBaseFromBytesKind_encode_anyFuel
    (fuel : Nat) (layouts : LayoutTable) (k : RigidTy) (idx : LayoutIdx)
    (fSz : Nat) (hBase : checkBaseFromBytesKind k = true)
    (hFSz : rigidTyKindByteSize k = some fSz)
    (v : Value) (bs : List AbstractByte)
    (hEnc :
      encodeValueToBytes (fuel + 2) layouts { kind := k, layoutIdx := idx } v =
        some bs) :
    length bs = fSz ∧ allBytesInitialized bs = true := by
  cases k with
  | uint w =>
    rcases uintWidth_targetBytes w with ⟨sz, hSz, _⟩
    simp [rigidTyKindByteSize, hSz] at hFSz
    subst hFSz
    exact uint_encode_anyFuel (fuel + 1) layouts w idx sz hSz v bs hEnc
  | int w =>
    rcases intWidth_targetBytes w with ⟨sz, hSz, _⟩
    simp [rigidTyKindByteSize, hSz] at hFSz
    subst hFSz
    exact int_encode_anyFuel (fuel + 1) layouts w idx sz hSz v bs hEnc
  | tuple ks =>
    cases ks with
    | nil =>
      simp [rigidTyKindByteSize] at hFSz
      subst hFSz
      unfold encodeValueToBytes at hEnc
      cases v with
      | unit => injection hEnc with hBs; subst hBs; exact ⟨rfl, rfl⟩
      | aggregate varIdx fs =>
        match varIdx, fs with
        | 0, [] => injection hEnc with hBs; subst hBs; exact ⟨rfl, rfl⟩
        | _ + 1, _ | 0, _ :: _ => nomatch hEnc
      | _ => nomatch hEnc
    | cons _ _ => nomatch hBase
  | array elem n =>
    cases elem with
    | uint w =>
      rcases uintWidth_targetBytes w with ⟨sz, hSz, _⟩
      simp [rigidTyKindByteSize, hSz] at hFSz
      subst hFSz
      exact array_uint_encode_anyFuel fuel layouts w n idx sz hSz v bs hEnc
    | int w =>
      rcases intWidth_targetBytes w with ⟨sz, hSz, _⟩
      simp [rigidTyKindByteSize, hSz] at hFSz
      subst hFSz
      exact array_int_encode_anyFuel fuel layouts w n idx sz hSz v bs hEnc
    | _ => nomatch hBase
  | _ => nomatch hBase

private theorem checkBaseFromBytesKind_hasByteSize
    {k : RigidTy} (hBase : checkBaseFromBytesKind k = true) :
    ∃ sz, rigidTyKindByteSize k = some sz := by
  cases k with
  | uint w =>
    rcases uintWidth_targetBytes w with ⟨sz, hSz, _⟩
    exact ⟨sz, hSz⟩
  | int w =>
    rcases intWidth_targetBytes w with ⟨sz, hSz, _⟩
    exact ⟨sz, hSz⟩
  | tuple ks =>
    cases ks with
    | nil => exact ⟨0, rfl⟩
    | cons _ _ => nomatch hBase
  | array elem n =>
    cases elem with
    | uint w =>
      rcases uintWidth_targetBytes w with ⟨sz, hSz, _⟩
      exact ⟨sz * n, by simp [rigidTyKindByteSize, hSz]⟩
    | int w =>
      rcases intWidth_targetBytes w with ⟨sz, hSz, _⟩
      exact ⟨sz * n, by simp [rigidTyKindByteSize, hSz]⟩
    | _ => nomatch hBase
  | _ => nomatch hBase

theorem checkBaseFromBytesKind_isFromBytes
    (layouts : LayoutTable) (k : RigidTy) (idx : LayoutIdx)
    (hBase : checkBaseFromBytesKind k = true) :
    IsFromBytes layouts { kind := k, layoutIdx := idx } := by
  rcases checkBaseFromBytesKind_hasByteSize hBase with ⟨sz, hSz⟩
  refine ⟨sz, by simp [rigidTyByteSize, hSz], ?_⟩
  exact checkBaseFromBytesKind_decode_anyFuel 14 layouts k idx sz hBase hSz

theorem checkBaseFromBytesKind_isIntoBytes
    (layouts : LayoutTable) (k : RigidTy) (idx : LayoutIdx)
    (hBase : checkBaseFromBytesKind k = true) :
    IsIntoBytes layouts { kind := k, layoutIdx := idx } := by
  rcases checkBaseFromBytesKind_hasByteSize hBase with ⟨sz, hSz⟩
  refine ⟨sz, by simp [rigidTyByteSize, hSz], ?_⟩
  exact checkBaseFromBytesKind_encode_anyFuel 14 layouts k idx sz hBase hSz

/--
Checks that `offs` and `fks` are base `FromBytes`/`IntoBytes` fields placed
contiguously starting at `curOff`, returning the final cumulative offset.
-/
def checkAdtFieldsContiguous
    (curOff : Nat) : List Size → List RigidTy → Option Nat
  | [], [] => some curOff
  | off :: offs, fk :: fks =>
    if checkBaseFromBytesKind fk && (off.bytes == curOff) then
      match rigidTyKindByteSize fk with
      | none => none
      | some fSz => checkAdtFieldsContiguous (curOff + fSz) offs fks
    else
      none
  | _, _ => none

private theorem checkAdtFieldsContiguous_props :
    ∀ (offs : List Size) (fks : List RigidTy) (curOff totalOff : Nat),
      checkAdtFieldsContiguous curOff offs fks = some totalOff →
      fks.length = offs.length ∧ curOff ≤ totalOff
  | [], [], _, _, h => by
    injection h with hEq; subst hEq; exact ⟨rfl, Nat.le_refl _⟩
  | [], _ :: _, _, _, h => nomatch h
  | _ :: _, [], _, _, h => nomatch h
  | off :: offs, fk :: fks, curOff, totalOff, h => by
    unfold checkAdtFieldsContiguous at h
    split at h
    · cases hSz : rigidTyKindByteSize fk <;> rw [hSz] at h
      · nomatch h
      case some fSz =>
        have ⟨hLen, hLe⟩ :=
          checkAdtFieldsContiguous_props offs fks (curOff + fSz) totalOff h
        exact ⟨congrArg Nat.succ hLen, by omega⟩
    · nomatch h

@[simp]
private theorem writeAbstractBytesAt_nil
    (buf : List AbstractByte) (off : Nat) :
    writeAbstractBytesAt buf off [] = some buf := by
  cases buf <;> rfl

private theorem writeAbstractBytesAt_append_replicate :
    ∀ (pre patch : List AbstractByte) (rem : Nat),
      writeAbstractBytesAt
        (pre ++ List.replicate (patch.length + rem) .uninit)
        pre.length
        patch =
        some (pre ++ patch ++ List.replicate rem .uninit)
  | [], [], _ => by simp
  | [], w :: ws, rem => by
    have ih := writeAbstractBytesAt_append_replicate [] ws rem
    simp only [List.nil_append, List.length_nil, List.length_cons] at ih ⊢
    have hAdd : ws.length + 1 + rem = (ws.length + rem) + 1 := by omega
    rw [hAdd, List.replicate_succ]
    dsimp only [writeAbstractBytesAt]
    rw [ih]
    rfl
  | _ :: _, [], _ => by simp
  | b :: bs, w :: ws, rem => by
    have ih := writeAbstractBytesAt_append_replicate bs (w :: ws) rem
    dsimp only [List.cons_append, List.length_cons] at ih ⊢
    dsimp only [writeAbstractBytesAt]
    rw [ih]

private theorem checkAdtFieldsContiguous_decode
    (layouts : LayoutTable) (bs : List AbstractByte)
    (hInit : allBytesInitialized bs = true) :
    ∀ (offs : List Size) (fks : List RigidTy) (curOff totalOff : Nat),
      checkAdtFieldsContiguous curOff offs fks = some totalOff →
      totalOff ≤ bs.length →
      ∃ vals,
        decodeFieldsAtOffsetsWith
          (fun k s =>
            decodeValueFromBytes 15 layouts { kind := k, layoutIdx := 0 } s)
          (fun k => rigidTyByteSize layouts { kind := k, layoutIdx := 0 })
          bs offs fks = some vals
  | [], [], _, _, _, _ => ⟨[], rfl⟩
  | [], _ :: _, _, _, h, _ => nomatch h
  | _ :: _, [], _, _, h, _ => nomatch h
  | off :: offs, fk :: fks, curOff, totalOff, hContig, hLe => by
    unfold checkAdtFieldsContiguous at hContig
    split at hContig
    case isTrue hCond =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hCond
      rcases hCond with ⟨hBase, hOff⟩
      cases hFSz : rigidTyKindByteSize fk <;> rw [hFSz] at hContig
      · nomatch hContig
      case some fSz =>
        have ⟨_, hNextLe⟩ :=
          checkAdtFieldsContiguous_props offs fks (curOff + fSz) totalOff hContig
        have hInBounds : off.bytes + fSz ≤ bs.length := by omega
        have hBle : Nat.ble (off.bytes + fSz) (length bs) = true :=
          Nat.ble_eq_true_of_le hInBounds
        let fSlice := (bs.drop off.bytes).take fSz
        have hSliceLen : length fSlice = fSz := by
          simp [fSlice, length, List.length_take, List.length_drop]; omega
        have hSliceInit : allBytesInitialized fSlice = true :=
          allBytesInitialized_take fSz (allBytesInitialized_drop off.bytes hInit)
        rcases checkBaseFromBytesKind_decode_anyFuel 13 layouts fk 0 fSz hBase
          hFSz fSlice hSliceLen hSliceInit with ⟨v, hV⟩
        rcases checkAdtFieldsContiguous_decode layouts bs hInit offs fks
          (curOff + fSz) totalOff hContig hLe with ⟨vs, hVs⟩
        refine ⟨v :: vs, ?_⟩
        unfold decodeFieldsAtOffsetsWith sliceAbstractBytes
        simp [rigidTyByteSize, hFSz, hBle, fSlice, hV, hVs]
    case isFalse => nomatch hContig

private theorem checkAdtFieldsContiguous_encode
    (layouts : LayoutTable) :
    ∀ (offs : List Size) (fks : List RigidTy) (vals : List Value)
      (pre : List AbstractByte) (curOff totalOff : Nat)
      (outBs : List AbstractByte),
      checkAdtFieldsContiguous curOff offs fks = some totalOff →
      pre.length = curOff →
      allBytesInitialized pre = true →
      encodeFieldsAtOffsetsWith
        (fun k fv =>
          encodeValueToBytes 15 layouts { kind := k, layoutIdx := 0 } fv)
        (fun fv => encodeUntypedValueToBytes 15 fv)
        offs fks vals
        (pre ++ List.replicate (totalOff - curOff) .uninit) = some outBs →
      length outBs = totalOff ∧ allBytesInitialized outBs = true
  | [], [], [], pre, curOff, totalOff, outBs, hContig, hPreLen, hPreInit, hEnc => by
    injection hContig with hEq; subst hEq
    simp [encodeFieldsAtOffsetsWith] at hEnc
    subst hEnc
    exact ⟨hPreLen, hPreInit⟩
  | [], [], _ :: _, _, _, _, _, _, _, _, hEnc => nomatch hEnc
  | [], _ :: _, _, _, _, _, _, hContig, _, _, _ => nomatch hContig
  | _ :: _, [], _, _, _, _, _, hContig, _, _, _ => nomatch hContig
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, hEnc => nomatch hEnc
  | off :: offs, fk :: fks, v :: vs, pre, curOff, totalOff, outBs,
      hContig, hPreLen, hPreInit, hEnc => by
    unfold checkAdtFieldsContiguous at hContig
    split at hContig
    case isTrue hCond =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hCond
      rcases hCond with ⟨hBase, hOff⟩
      cases hFSz : rigidTyKindByteSize fk <;> rw [hFSz] at hContig
      · nomatch hContig
      case some fSz =>
        have ⟨_, hNextLe⟩ :=
          checkAdtFieldsContiguous_props offs fks (curOff + fSz) totalOff hContig
        unfold encodeFieldsAtOffsetsWith at hEnc
        dsimp only at hEnc
        cases hEv :
            encodeValueToBytes 15 layouts { kind := fk, layoutIdx := 0 } v <;>
          rw [hEv] at hEnc
        · simp [hFSz] at hEnc
        case some fBytes =>
          dsimp only at hEnc
          have ⟨hFLen, hFInit⟩ :=
            checkBaseFromBytesKind_encode_anyFuel 13 layouts fk 0 fSz hBase hFSz
              v fBytes hEv
          have hSub : totalOff - curOff = fBytes.length + (totalOff - (curOff + fSz)) := by
            simp [length] at hFLen; omega
          have hOffPre : off.bytes = pre.length := by omega
          rw [hSub, hOffPre,
              writeAbstractBytesAt_append_replicate pre fBytes
                (totalOff - (curOff + fSz))] at hEnc
          dsimp only at hEnc
          exact checkAdtFieldsContiguous_encode layouts offs fks vs
            (pre ++ fBytes) (curOff + fSz) totalOff outBs hContig
            (by simp [length] at hFLen; simp [hPreLen, hFLen])
            (allBytesInitialized_append hPreInit hFInit)
            hEnc
    case isFalse => nomatch hContig

/--
Checks whether `ty` has a single-variant struct layout whose field offsets
match `fieldKinds` contiguously from byte offset `0` up to `l.size.bytes`.
-/
def checkAdtContiguousLayout
    (layouts : LayoutTable) (ty : Ty) (fieldKinds : List RigidTy) : Bool :=
  match LayoutTable.lookup layouts ty.layoutIdx with
  | none => false
  | some l =>
    match l.isUninhabited, l.variants, l.fields with
    | false, .single _, .arbitrary offs _ =>
      match checkAdtFieldsContiguous 0 offs fieldKinds with
      | none => false
      | some totalOff => l.size.bytes == totalOff
    | _, _, _ => false

theorem checkAdtContiguousLayout_isFromBytes
    (layouts : LayoutTable) (defPath : DefPath) (fk : RigidTy)
    (fks : List RigidTy) (layoutIdx : LayoutIdx)
    (hLayout :
      checkAdtContiguousLayout layouts
        { kind := .adt defPath (fk :: fks), layoutIdx := layoutIdx }
        (fk :: fks) = true) :
    IsFromBytes layouts
      { kind := .adt defPath (fk :: fks), layoutIdx := layoutIdx } := by
  unfold checkAdtContiguousLayout at hLayout
  cases hLookup : LayoutTable.lookup layouts layoutIdx <;>
    simp [hLookup] at hLayout
  case some l =>
    rcases l with ⟨⟨sb⟩, lAlign, lRepr, lFields, lVariants, lUninhabited⟩
    cases lUninhabited <;> cases lVariants <;> cases lFields <;>
      try simp at hLayout
    case false.single.arbitrary variantIdx offs fieldOrder =>
      cases offs with
      | nil => simp [checkAdtFieldsContiguous] at hLayout
      | cons off0 restOffs =>
        cases hContig :
            checkAdtFieldsContiguous 0 (off0 :: restOffs) (fk :: fks) <;>
          simp [hContig] at hLayout
        case some totalOff =>
          subst hLayout
          have ⟨hArgsLen, _⟩ :=
            checkAdtFieldsContiguous_props (off0 :: restOffs) (fk :: fks)
              0 sb hContig
          refine ⟨sb, by simp [rigidTyByteSize, hLookup], ?_⟩
          intro bs hLen hInit
          rcases checkAdtFieldsContiguous_decode layouts bs hInit
            (off0 :: restOffs) (fk :: fks) 0 sb hContig
            (by simp [length] at hLen; omega) with ⟨vals, hVals⟩
          refine ⟨.aggregate variantIdx vals, ?_⟩
          have hBeqBs : Nat.beq (length bs) sb = true := by simp [hLen]
          have hBeqArgs :
              Nat.beq (length (fk :: fks)) (length (off0 :: restOffs)) = true := by
            simp [length, hArgsLen]
          unfold defaultCodecFuel decodeValueFromBytes
          simp [hLookup, hBeqBs, hBeqArgs, hVals]

theorem checkAdtContiguousLayout_isIntoBytes
    (layouts : LayoutTable) (defPath : DefPath) (fk : RigidTy)
    (fks : List RigidTy) (layoutIdx : LayoutIdx)
    (hLayout :
      checkAdtContiguousLayout layouts
        { kind := .adt defPath (fk :: fks), layoutIdx := layoutIdx }
        (fk :: fks) = true) :
    IsIntoBytes layouts
      { kind := .adt defPath (fk :: fks), layoutIdx := layoutIdx } := by
  unfold checkAdtContiguousLayout at hLayout
  cases hLookup : LayoutTable.lookup layouts layoutIdx <;>
    simp [hLookup] at hLayout
  case some l =>
    rcases l with ⟨⟨sb⟩, lAlign, lRepr, lFields, lVariants, lUninhabited⟩
    cases lUninhabited <;> cases lVariants <;> cases lFields <;>
      try simp at hLayout
    case false.single.arbitrary variantIdx offs fieldOrder =>
      cases offs with
      | nil => simp [checkAdtFieldsContiguous] at hLayout
      | cons off0 restOffs =>
        cases hContig :
            checkAdtFieldsContiguous 0 (off0 :: restOffs) (fk :: fks) <;>
          simp [hContig] at hLayout
        case some totalOff =>
          subst hLayout
          have ⟨hArgsLen, _⟩ :=
            checkAdtFieldsContiguous_props (off0 :: restOffs) (fk :: fks)
              0 sb hContig
          refine ⟨sb, by simp [rigidTyByteSize, hLookup], ?_⟩
          intro v bs hEnc
          unfold defaultCodecFuel encodeValueToBytes at hEnc
          simp only [hLookup] at hEnc
          cases v with
          | aggregate varIdx fieldVals =>
            dsimp only at hEnc
            cases hCond :
                Bool.and (Nat.beq varIdx variantIdx)
                  (Nat.beq (length (off0 :: restOffs)) (length fieldVals)) <;>
              rw [hCond] at hEnc
            · nomatch hEnc
            · have hBeqArgs :
                  Nat.beq (length (fk :: fks)) (length (off0 :: restOffs)) = true := by
                simp [length, hArgsLen]
              simp only [hBeqArgs, replicateUninitBytes_eq_replicate] at hEnc
              exact checkAdtFieldsContiguous_encode layouts
                (off0 :: restOffs) (fk :: fks) fieldVals [] 0 sb bs
                hContig rfl rfl (by simpa using hEnc)
          | _ => nomatch hEnc

/--
Decidable certificate checker for `IsFromBytes` accepting all primitive integer
types, `()`, homogeneous integer arrays `[uN; M]` / `[iN; M]`, and contiguous
padding-free single-variant structs `.adt defPath (fk :: fks)`.
-/
def checkFromBytes (layouts : LayoutTable) (ty : Ty) : Bool :=
  if checkBaseFromBytesKind ty.kind then
    true
  else
    match ty.kind with
    | .adt _ (fk :: fks) => checkAdtContiguousLayout layouts ty (fk :: fks)
    | _ => false

abbrev checkPrimitiveFromBytes : LayoutTable → Ty → Bool := checkFromBytes

theorem checkFromBytes_sound
    (layouts : LayoutTable) (ty : Ty)
    (h : checkFromBytes layouts ty = true) :
    IsFromBytes layouts ty := by
  rcases ty with ⟨kind, layoutIdx⟩
  unfold checkFromBytes at h
  split at h
  case isTrue hBase =>
    exact checkBaseFromBytesKind_isFromBytes layouts kind layoutIdx hBase
  case isFalse =>
    cases kind with
    | adt defPath fks =>
      cases fks with
      | nil => nomatch h
      | cons fk rest =>
        exact checkAdtContiguousLayout_isFromBytes
          layouts defPath fk rest layoutIdx h
    | _ => nomatch h

theorem checkPrimitiveFromBytes_sound :
    ∀ layouts ty, checkPrimitiveFromBytes layouts ty = true →
      IsFromBytes layouts ty :=
  checkFromBytes_sound

theorem checkValidForTrait_fromBytes_sound
    (layouts : LayoutTable) (ty : Ty)
    (h : checkFromBytes layouts ty = true) :
    ValidForTrait .fromBytes layouts ty :=
  checkFromBytes_sound layouts ty h

/--
Base `RigidTy` kinds that satisfy `IntoBytes`: every `checkBaseFromBytesKind`
kind plus `bool`, `char`, `[bool; M]`, and `[char; M]`, whose encodings are
always fully initialized even though not every byte pattern is a valid value.
-/
def checkBaseIntoBytesKind : RigidTy → Bool
  | .uint _ | .int _ | .bool | .char | .tuple []
  | .array (.uint _) _ | .array (.int _) _
  | .array .bool _ | .array .char _ => true
  | _ => false

theorem checkBaseFromBytesKind_implies_checkBaseIntoBytesKind
    {k : RigidTy} (h : checkBaseFromBytesKind k = true) :
    checkBaseIntoBytesKind k = true := by
  cases k with
  | uint _ | int _ => rfl
  | tuple ks =>
    cases ks with
    | nil => rfl
    | cons _ _ => nomatch h
  | array elem _ =>
    cases elem with
    | uint _ | int _ => rfl
    | _ => nomatch h
  | _ => nomatch h

private theorem checkBaseIntoBytesKind_encode_anyFuel
    (fuel : Nat) (layouts : LayoutTable) (k : RigidTy) (idx : LayoutIdx)
    (fSz : Nat) (hBase : checkBaseIntoBytesKind k = true)
    (hFSz : rigidTyKindByteSize k = some fSz)
    (v : Value) (bs : List AbstractByte)
    (hEnc :
      encodeValueToBytes (fuel + 2) layouts { kind := k, layoutIdx := idx } v =
        some bs) :
    length bs = fSz ∧ allBytesInitialized bs = true := by
  cases k with
  | uint w =>
    rcases uintWidth_targetBytes w with ⟨sz, hSz, _⟩
    simp [rigidTyKindByteSize, hSz] at hFSz
    subst hFSz
    exact uint_encode_anyFuel (fuel + 1) layouts w idx sz hSz v bs hEnc
  | int w =>
    rcases intWidth_targetBytes w with ⟨sz, hSz, _⟩
    simp [rigidTyKindByteSize, hSz] at hFSz
    subst hFSz
    exact int_encode_anyFuel (fuel + 1) layouts w idx sz hSz v bs hEnc
  | bool =>
    simp [rigidTyKindByteSize] at hFSz
    subst hFSz
    exact bool_encode_anyFuel (fuel + 1) layouts idx v bs hEnc
  | char =>
    simp [rigidTyKindByteSize] at hFSz
    subst hFSz
    exact char_encode_anyFuel (fuel + 1) layouts idx v bs hEnc
  | tuple ks =>
    cases ks with
    | nil =>
      simp [rigidTyKindByteSize] at hFSz
      subst hFSz
      unfold encodeValueToBytes at hEnc
      cases v with
      | unit => injection hEnc with hBs; subst hBs; exact ⟨rfl, rfl⟩
      | aggregate varIdx fs =>
        match varIdx, fs with
        | 0, [] => injection hEnc with hBs; subst hBs; exact ⟨rfl, rfl⟩
        | _ + 1, _ | 0, _ :: _ => nomatch hEnc
      | _ => nomatch hEnc
    | cons _ _ => nomatch hBase
  | array elem n =>
    cases elem with
    | uint w =>
      rcases uintWidth_targetBytes w with ⟨sz, hSz, _⟩
      simp [rigidTyKindByteSize, hSz] at hFSz
      subst hFSz
      exact array_uint_encode_anyFuel fuel layouts w n idx sz hSz v bs hEnc
    | int w =>
      rcases intWidth_targetBytes w with ⟨sz, hSz, _⟩
      simp [rigidTyKindByteSize, hSz] at hFSz
      subst hFSz
      exact array_int_encode_anyFuel fuel layouts w n idx sz hSz v bs hEnc
    | bool =>
      simp [rigidTyKindByteSize] at hFSz
      subst hFSz
      have ⟨hL, hI⟩ := array_bool_encode_anyFuel fuel layouts n idx v bs hEnc
      rw [Nat.one_mul] at hL
      exact ⟨hL, hI⟩
    | char =>
      simp [rigidTyKindByteSize] at hFSz
      subst hFSz
      exact array_char_encode_anyFuel fuel layouts n idx v bs hEnc
    | _ => nomatch hBase
  | _ => nomatch hBase

private theorem checkBaseIntoBytesKind_hasByteSize
    {k : RigidTy} (hBase : checkBaseIntoBytesKind k = true) :
    ∃ sz, rigidTyKindByteSize k = some sz := by
  cases k with
  | uint w =>
    rcases uintWidth_targetBytes w with ⟨sz, hSz, _⟩
    exact ⟨sz, hSz⟩
  | int w =>
    rcases intWidth_targetBytes w with ⟨sz, hSz, _⟩
    exact ⟨sz, hSz⟩
  | bool => exact ⟨1, rfl⟩
  | char => exact ⟨4, rfl⟩
  | tuple ks =>
    cases ks with
    | nil => exact ⟨0, rfl⟩
    | cons _ _ => nomatch hBase
  | array elem n =>
    cases elem with
    | uint w =>
      rcases uintWidth_targetBytes w with ⟨sz, hSz, _⟩
      exact ⟨sz * n, by simp [rigidTyKindByteSize, hSz]⟩
    | int w =>
      rcases intWidth_targetBytes w with ⟨sz, hSz, _⟩
      exact ⟨sz * n, by simp [rigidTyKindByteSize, hSz]⟩
    | bool => exact ⟨1 * n, rfl⟩
    | char => exact ⟨4 * n, rfl⟩
    | _ => nomatch hBase
  | _ => nomatch hBase

theorem checkBaseIntoBytesKind_isIntoBytes
    (layouts : LayoutTable) (k : RigidTy) (idx : LayoutIdx)
    (hBase : checkBaseIntoBytesKind k = true) :
    IsIntoBytes layouts { kind := k, layoutIdx := idx } := by
  rcases checkBaseIntoBytesKind_hasByteSize hBase with ⟨sz, hSz⟩
  refine ⟨sz, by simp [rigidTyByteSize, hSz], ?_⟩
  exact checkBaseIntoBytesKind_encode_anyFuel 14 layouts k idx sz hBase hSz

/--
Checks that `offs` and `fks` are base `IntoBytes` fields placed contiguously
starting at `curOff`, returning the final cumulative offset.
-/
def checkAdtFieldsContiguousIntoBytes
    (curOff : Nat) : List Size → List RigidTy → Option Nat
  | [], [] => some curOff
  | off :: offs, fk :: fks =>
    if checkBaseIntoBytesKind fk && (off.bytes == curOff) then
      match rigidTyKindByteSize fk with
      | none => none
      | some fSz => checkAdtFieldsContiguousIntoBytes (curOff + fSz) offs fks
    else
      none
  | _, _ => none

private theorem checkAdtFieldsContiguousIntoBytes_props :
    ∀ (offs : List Size) (fks : List RigidTy) (curOff totalOff : Nat),
      checkAdtFieldsContiguousIntoBytes curOff offs fks = some totalOff →
      fks.length = offs.length ∧ curOff ≤ totalOff
  | [], [], _, _, h => by
    injection h with hEq; subst hEq; exact ⟨rfl, Nat.le_refl _⟩
  | [], _ :: _, _, _, h => nomatch h
  | _ :: _, [], _, _, h => nomatch h
  | off :: offs, fk :: fks, curOff, totalOff, h => by
    unfold checkAdtFieldsContiguousIntoBytes at h
    split at h
    · cases hSz : rigidTyKindByteSize fk <;> rw [hSz] at h
      · nomatch h
      case some fSz =>
        have ⟨hLen, hLe⟩ :=
          checkAdtFieldsContiguousIntoBytes_props offs fks (curOff + fSz) totalOff h
        exact ⟨congrArg Nat.succ hLen, by omega⟩
    · nomatch h

theorem checkAdtFieldsContiguous_implies_intoBytes :
    ∀ (offs : List Size) (fks : List RigidTy) (curOff totalOff : Nat),
      checkAdtFieldsContiguous curOff offs fks = some totalOff →
      checkAdtFieldsContiguousIntoBytes curOff offs fks = some totalOff
  | [], [], _, _, h => h
  | [], _ :: _, _, _, h => nomatch h
  | _ :: _, [], _, _, h => nomatch h
  | off :: offs, fk :: fks, curOff, totalOff, h => by
    unfold checkAdtFieldsContiguous at h
    split at h
    case isTrue hCond =>
      simp only [Bool.and_eq_true] at hCond
      rcases hCond with ⟨hBase, hOff⟩
      have hInto : checkBaseIntoBytesKind fk = true :=
        checkBaseFromBytesKind_implies_checkBaseIntoBytesKind hBase
      unfold checkAdtFieldsContiguousIntoBytes
      simp only [hInto, hOff, Bool.and_self, ↓reduceIte]
      cases hSz : rigidTyKindByteSize fk <;> rw [hSz] at h
      · nomatch h
      case some fSz =>
        exact checkAdtFieldsContiguous_implies_intoBytes offs fks (curOff + fSz) totalOff h
    case isFalse => nomatch h

private theorem checkAdtFieldsContiguousIntoBytes_encode
    (layouts : LayoutTable) :
    ∀ (offs : List Size) (fks : List RigidTy) (vals : List Value)
      (pre : List AbstractByte) (curOff totalOff : Nat)
      (outBs : List AbstractByte),
      checkAdtFieldsContiguousIntoBytes curOff offs fks = some totalOff →
      pre.length = curOff →
      allBytesInitialized pre = true →
      encodeFieldsAtOffsetsWith
        (fun k fv =>
          encodeValueToBytes 15 layouts { kind := k, layoutIdx := 0 } fv)
        (fun fv => encodeUntypedValueToBytes 15 fv)
        offs fks vals
        (pre ++ List.replicate (totalOff - curOff) .uninit) = some outBs →
      length outBs = totalOff ∧ allBytesInitialized outBs = true
  | [], [], [], pre, curOff, totalOff, outBs, hContig, hPreLen, hPreInit, hEnc => by
    injection hContig with hEq; subst hEq
    simp [encodeFieldsAtOffsetsWith] at hEnc
    subst hEnc
    exact ⟨hPreLen, hPreInit⟩
  | [], [], _ :: _, _, _, _, _, _, _, _, hEnc => nomatch hEnc
  | [], _ :: _, _, _, _, _, _, hContig, _, _, _ => nomatch hContig
  | _ :: _, [], _, _, _, _, _, hContig, _, _, _ => nomatch hContig
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, hEnc => nomatch hEnc
  | off :: offs, fk :: fks, v :: vs, pre, curOff, totalOff, outBs,
      hContig, hPreLen, hPreInit, hEnc => by
    unfold checkAdtFieldsContiguousIntoBytes at hContig
    split at hContig
    case isTrue hCond =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hCond
      rcases hCond with ⟨hBase, hOff⟩
      cases hFSz : rigidTyKindByteSize fk <;> rw [hFSz] at hContig
      · nomatch hContig
      case some fSz =>
        have ⟨_, hNextLe⟩ :=
          checkAdtFieldsContiguousIntoBytes_props offs fks (curOff + fSz) totalOff hContig
        unfold encodeFieldsAtOffsetsWith at hEnc
        dsimp only at hEnc
        cases hEv :
            encodeValueToBytes 15 layouts { kind := fk, layoutIdx := 0 } v <;>
          rw [hEv] at hEnc
        · simp [hFSz] at hEnc
        case some fBytes =>
          dsimp only at hEnc
          have ⟨hFLen, hFInit⟩ :=
            checkBaseIntoBytesKind_encode_anyFuel 13 layouts fk 0 fSz hBase hFSz
              v fBytes hEv
          have hSub : totalOff - curOff = fBytes.length + (totalOff - (curOff + fSz)) := by
            simp [length] at hFLen; omega
          have hOffPre : off.bytes = pre.length := by omega
          rw [hSub, hOffPre,
              writeAbstractBytesAt_append_replicate pre fBytes
                (totalOff - (curOff + fSz))] at hEnc
          dsimp only at hEnc
          exact checkAdtFieldsContiguousIntoBytes_encode layouts offs fks vs
            (pre ++ fBytes) (curOff + fSz) totalOff outBs hContig
            (by simp [length] at hFLen; simp [hPreLen, hFLen])
            (allBytesInitialized_append hPreInit hFInit)
            hEnc
    case isFalse => nomatch hContig

/--
Checks whether `ty` has a single-variant struct layout whose field offsets
match `fieldKinds` contiguously from byte offset `0` up to `l.size.bytes` and
whose fields all satisfy `checkBaseIntoBytesKind`.
-/
def checkAdtContiguousIntoBytesLayout
    (layouts : LayoutTable) (ty : Ty) (fieldKinds : List RigidTy) : Bool :=
  match LayoutTable.lookup layouts ty.layoutIdx with
  | none => false
  | some l =>
    match l.isUninhabited, l.variants, l.fields with
    | false, .single _, .arbitrary offs _ =>
      match checkAdtFieldsContiguousIntoBytes 0 offs fieldKinds with
      | none => false
      | some totalOff => l.size.bytes == totalOff
    | _, _, _ => false

theorem checkAdtContiguousLayout_implies_intoBytes
    (layouts : LayoutTable) (ty : Ty) (fieldKinds : List RigidTy)
    (h : checkAdtContiguousLayout layouts ty fieldKinds = true) :
    checkAdtContiguousIntoBytesLayout layouts ty fieldKinds = true := by
  unfold checkAdtContiguousLayout at h
  unfold checkAdtContiguousIntoBytesLayout
  cases hLookup : LayoutTable.lookup layouts ty.layoutIdx <;>
    simp [hLookup] at h ⊢
  case some l =>
    rcases l with ⟨⟨sb⟩, lAlign, lRepr, lFields, lVariants, lUninhabited⟩
    cases lUninhabited <;> cases lVariants <;> cases lFields <;>
      try simp at h
    case false.single.arbitrary variantIdx offs fieldOrder =>
      dsimp only at h ⊢
      cases hContig : checkAdtFieldsContiguous 0 offs fieldKinds <;>
        rw [hContig] at h
      · nomatch h
      case some totalOff =>
        rw [checkAdtFieldsContiguous_implies_intoBytes offs fieldKinds 0 totalOff hContig]
        exact h

theorem checkAdtContiguousIntoBytesLayout_isIntoBytes
    (layouts : LayoutTable) (defPath : DefPath) (fk : RigidTy)
    (fks : List RigidTy) (layoutIdx : LayoutIdx)
    (hLayout :
      checkAdtContiguousIntoBytesLayout layouts
        { kind := .adt defPath (fk :: fks), layoutIdx := layoutIdx }
        (fk :: fks) = true) :
    IsIntoBytes layouts
      { kind := .adt defPath (fk :: fks), layoutIdx := layoutIdx } := by
  unfold checkAdtContiguousIntoBytesLayout at hLayout
  cases hLookup : LayoutTable.lookup layouts layoutIdx <;>
    simp [hLookup] at hLayout
  case some l =>
    rcases l with ⟨⟨sb⟩, lAlign, lRepr, lFields, lVariants, lUninhabited⟩
    cases lUninhabited <;> cases lVariants <;> cases lFields <;>
      try simp at hLayout
    case false.single.arbitrary variantIdx offs fieldOrder =>
      cases offs with
      | nil => simp [checkAdtFieldsContiguousIntoBytes] at hLayout
      | cons off0 restOffs =>
        cases hContig :
            checkAdtFieldsContiguousIntoBytes 0 (off0 :: restOffs) (fk :: fks) <;>
          simp [hContig] at hLayout
        case some totalOff =>
          subst hLayout
          have ⟨hArgsLen, _⟩ :=
            checkAdtFieldsContiguousIntoBytes_props (off0 :: restOffs) (fk :: fks)
              0 sb hContig
          refine ⟨sb, by simp [rigidTyByteSize, hLookup], ?_⟩
          intro v bs hEnc
          unfold defaultCodecFuel encodeValueToBytes at hEnc
          simp only [hLookup] at hEnc
          cases v with
          | aggregate varIdx fieldVals =>
            dsimp only at hEnc
            cases hCond :
                Bool.and (Nat.beq varIdx variantIdx)
                  (Nat.beq (length (off0 :: restOffs)) (length fieldVals)) <;>
              rw [hCond] at hEnc
            · nomatch hEnc
            · have hBeqArgs :
                  Nat.beq (length (fk :: fks)) (length (off0 :: restOffs)) = true := by
                simp [length, hArgsLen]
              simp only [hBeqArgs, replicateUninitBytes_eq_replicate] at hEnc
              exact checkAdtFieldsContiguousIntoBytes_encode layouts
                (off0 :: restOffs) (fk :: fks) fieldVals [] 0 sb bs
                hContig rfl rfl (by simpa using hEnc)
          | _ => nomatch hEnc

/--
Decidable certificate checker for `IsIntoBytes` accepting all primitive integer
types, `bool`, `char`, `()`, homogeneous arrays `[uN; M]` / `[iN; M]` /
`[bool; M]` / `[char; M]`, and contiguous padding-free single-variant structs
`.adt defPath (fk :: fks)` whose fields satisfy `checkBaseIntoBytesKind`. It
accepts every type accepted by `checkFromBytes`
(`checkFromBytes_implies_checkIntoBytes`), and strictly more
(`checkIntoBytes_strictly_extends_checkFromBytes`).
-/
def checkIntoBytes (layouts : LayoutTable) (ty : Ty) : Bool :=
  if checkBaseIntoBytesKind ty.kind then
    true
  else
    match ty.kind with
    | .adt _ (fk :: fks) => checkAdtContiguousIntoBytesLayout layouts ty (fk :: fks)
    | _ => false

abbrev checkPrimitiveIntoBytes : LayoutTable → Ty → Bool := checkIntoBytes

theorem checkIntoBytes_sound
    (layouts : LayoutTable) (ty : Ty)
    (h : checkIntoBytes layouts ty = true) :
    IsIntoBytes layouts ty := by
  rcases ty with ⟨kind, layoutIdx⟩
  unfold checkIntoBytes at h
  split at h
  case isTrue hBase =>
    exact checkBaseIntoBytesKind_isIntoBytes layouts kind layoutIdx hBase
  case isFalse =>
    cases kind with
    | adt defPath fks =>
      cases fks with
      | nil => nomatch h
      | cons fk rest =>
        exact checkAdtContiguousIntoBytesLayout_isIntoBytes
          layouts defPath fk rest layoutIdx h
    | _ => nomatch h

theorem checkPrimitiveIntoBytes_sound :
    ∀ layouts ty, checkPrimitiveIntoBytes layouts ty = true →
      IsIntoBytes layouts ty :=
  checkIntoBytes_sound

theorem checkValidForTrait_intoBytes_sound
    (layouts : LayoutTable) (ty : Ty)
    (h : checkIntoBytes layouts ty = true) :
    ValidForTrait .intoBytes layouts ty :=
  checkIntoBytes_sound layouts ty h

theorem checkFromBytes_implies_checkIntoBytes
    (layouts : LayoutTable) (ty : Ty)
    (h : checkFromBytes layouts ty = true) :
    checkIntoBytes layouts ty = true := by
  rcases ty with ⟨kind, layoutIdx⟩
  unfold checkFromBytes at h
  unfold checkIntoBytes
  split at h
  case isTrue hBase =>
    have hInto := checkBaseFromBytesKind_implies_checkBaseIntoBytesKind hBase
    simp [hInto]
  case isFalse =>
    split
    case isTrue => rfl
    case isFalse =>
      cases kind with
      | adt defPath fks =>
        cases fks with
        | nil => nomatch h
        | cons fk rest =>
          exact checkAdtContiguousLayout_implies_intoBytes
            layouts { kind := .adt defPath (fk :: rest), layoutIdx := layoutIdx }
            (fk :: rest) h
      | _ => nomatch h

theorem checkFromBytes_implies_isIntoBytes
    (layouts : LayoutTable) (ty : Ty)
    (h : checkFromBytes layouts ty = true) :
    IsIntoBytes layouts ty :=
  checkIntoBytes_sound layouts ty (checkFromBytes_implies_checkIntoBytes layouts ty h)

/--
The strengthened `checkIntoBytes` strictly extends `checkFromBytes`: it accepts
`bool`, `char`, `[bool; n]`, and `[char; n]`, which `checkFromBytes` still
rejects (matching `bool_not_isFromBytes` and `char_not_isFromBytes`).
-/
theorem checkIntoBytes_strictly_extends_checkFromBytes
    (layouts : LayoutTable) (idx : LayoutIdx) (n : Nat) :
    (checkIntoBytes layouts { kind := .bool, layoutIdx := idx } = true ∧
      checkFromBytes layouts { kind := .bool, layoutIdx := idx } = false) ∧
    (checkIntoBytes layouts { kind := .char, layoutIdx := idx } = true ∧
      checkFromBytes layouts { kind := .char, layoutIdx := idx } = false) ∧
    (checkIntoBytes layouts { kind := .array .bool n, layoutIdx := idx } = true ∧
      checkFromBytes layouts { kind := .array .bool n, layoutIdx := idx } = false) ∧
    (checkIntoBytes layouts { kind := .array .char n, layoutIdx := idx } = true ∧
      checkFromBytes layouts { kind := .array .char n, layoutIdx := idx } = false) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-! ## 6. `ScalarLayout.validRange` & `wrappingRangeContains` Bridges -/

/-- Every little-endian byte sequence decodes to a bit pattern strictly below `scalarModulus (length bs)`. -/
theorem decodeLittleEndianBytes_lt_scalarModulus :
    ∀ (bs : List AbstractByte) (bits : Nat) (prov : Option (Nat × Nat)),
      decodeLittleEndianBytes bs = some (bits, prov) →
      bits < scalarModulus (length bs)
  | [], bits, _, h => by
    injection h with hPair
    injection hPair with hBits _
    subst hBits
    exact Nat.zero_lt_one
  | .uninit :: _, _, _, h => nomatch h
  | .init b _ :: rest, bits, _, h => by
    unfold decodeLittleEndianBytes at h
    cases hRest : decodeLittleEndianBytes rest <;> rw [hRest] at h
    · nomatch h
    case some bp =>
      rcases bp with ⟨highBits, restProv⟩
      injection h with hPair
      injection hPair with hBits _
      have hHigh := decodeLittleEndianBytes_lt_scalarModulus rest highBits restProv hRest
      have hLow : b.toBitVec.toNat < 256 := b.toBitVec.isLt
      subst hBits
      change b.toBitVec.toNat + 256 * highBits < 256 * scalarModulus (length rest)
      omega

/-- Any `ScalarVal` decoded via `decodeScalarBytes` has `sv.sizeBytes = length bs` and `sv.bits < scalarModulus (length bs)`. -/
theorem decodeScalarBytes_bits_lt
    (bs : List AbstractByte) (signed : Bool)
    (sv : ScalarVal) (prov : Option (Nat × Nat))
    (h : decodeScalarBytes bs signed = some (sv, prov)) :
    sv.sizeBytes = length bs ∧ sv.bits < scalarModulus (length bs) := by
  unfold decodeScalarBytes at h
  dsimp only at h
  cases hZero : Nat.beq (length bs) 0 <;> rw [hZero] at h
  · cases hLE : decodeLittleEndianBytes bs <;> rw [hLE] at h
    · nomatch h
    case some bp =>
      rcases bp with ⟨bits, p⟩
      injection h with hPair
      injection hPair with hSv _
      subst hSv
      exact ⟨rfl, decodeLittleEndianBytes_lt_scalarModulus bs bits p hLE⟩
  · nomatch h

@[simp]
theorem decodeLittleEndianBytes_zeroInitBytes :
    ∀ n : Nat, decodeLittleEndianBytes (zeroInitBytes n) = some (0, none)
  | 0 => rfl
  | k + 1 => by
    unfold zeroInitBytes decodeLittleEndianBytes
    rw [decodeLittleEndianBytes_zeroInitBytes k]
    rfl

theorem decodeScalarBytes_zeroInitBytes
    (sz : Nat) (signed : Bool) (hNz : Nat.beq sz 0 = false) :
    decodeScalarBytes (zeroInitBytes sz) signed = some (⟨0, sz⟩, none) := by
  unfold decodeScalarBytes
  dsimp only
  rw [length_zeroInitBytes sz, hNz, decodeLittleEndianBytes_zeroInitBytes sz]

/-- Little-endian round trip: decoding `encodeLittleEndianBytes bits (n + 1) prov`
recovers `bits` and `prov` whenever `bits < scalarModulus (n + 1)`. -/
theorem decodeLittleEndianBytes_encodeLittleEndianBytes_of_lt
    (prov : Option (Nat × Nat)) :
    ∀ (n bits : Nat), bits < scalarModulus (n + 1) →
      decodeLittleEndianBytes (encodeLittleEndianBytes bits (n + 1) prov) = some (bits, prov)
  | 0, bits, h => by
    have h256 : bits < 256 := h
    have hLow : (UInt8.ofNat bits).toBitVec.toNat = bits := by
      simp [UInt8.ofNat, BitVec.ofNat, Nat.mod_eq_of_lt h256]
    show
      (match decodeLittleEndianBytes ([] : List AbstractByte) with
       | some (highBits, restProv) =>
         some (Nat.add (UInt8.ofNat bits).toBitVec.toNat (Nat.mul 256 highBits),
           mergeByteProvenance prov restProv)
       | none => none) = some (bits, prov)
    show some (Nat.add (UInt8.ofNat bits).toBitVec.toNat (Nat.mul 256 0),
      mergeByteProvenance prov none) = some (bits, prov)
    rw [hLow]
    cases prov <;> rfl
  | n + 1, bits, h => by
    have hDiv : bits / 256 < scalarModulus (n + 1) := by
      change bits < 256 * scalarModulus (n + 1) at h
      omega
    have hRest := decodeLittleEndianBytes_encodeLittleEndianBytes_of_lt prov n (bits / 256) hDiv
    have hLow : (UInt8.ofNat bits).toBitVec.toNat = bits % 256 := by
      simp [UInt8.ofNat, BitVec.ofNat]
    show
      (match decodeLittleEndianBytes (encodeLittleEndianBytes (Nat.div bits 256) (n + 1) prov) with
       | some (highBits, restProv) =>
         some (Nat.add (UInt8.ofNat bits).toBitVec.toNat (Nat.mul 256 highBits),
           mergeByteProvenance prov restProv)
       | none => none) = some (bits, prov)
    rw [show Nat.div bits 256 = bits / 256 from rfl, hRest]
    show some (Nat.add (UInt8.ofNat bits).toBitVec.toNat (Nat.mul 256 (bits / 256)),
      mergeByteProvenance prov prov) = some (bits, prov)
    rw [hLow]
    have hMerge : mergeByteProvenance prov prov = prov := by cases prov <;> rfl
    rw [hMerge]
    congr 2
    exact Nat.mod_add_div bits 256

/-- Scalar round trip: `decodeScalarBytes` on `encodeLittleEndianBytes bits sz prov`
returns `⟨bits, sz⟩` with provenance `prov` whenever `0 < sz` and
`bits < scalarModulus sz`. -/
theorem decodeScalarBytes_encodeLittleEndianBytes_of_lt
    (sz bits : Nat) (prov : Option (Nat × Nat)) (signed : Bool)
    (hSz : 0 < sz) (hBits : bits < scalarModulus sz) :
    decodeScalarBytes (encodeLittleEndianBytes bits sz prov) signed =
      some (⟨bits, sz⟩, prov) := by
  obtain ⟨n, rfl⟩ : ∃ n, sz = n + 1 := ⟨sz - 1, by omega⟩
  unfold decodeScalarBytes
  rw [length_encodeLittleEndianBytes prov (n + 1) bits,
    decodeLittleEndianBytes_encodeLittleEndianBytes_of_lt prov n bits hBits]
  rfl

/-- Non-wrapping `WrappingRange` characterization (`lo ≤ hi`). -/
theorem wrappingRangeContains_nonwrapping_iff
    {lo hi v : Nat} (hLe : lo ≤ hi) :
    wrappingRangeContains ⟨lo, hi⟩ v = true ↔ (lo ≤ v ∧ v ≤ hi) := by
  unfold wrappingRangeContains
  have hBle : Nat.ble lo hi = true := Nat.ble_eq_true_of_le hLe
  rw [hBle]
  simp only [Bool.and_eq_true, Nat.ble_eq]

/-- Non-wrapping `WrappingRange` rejection characterization (`lo ≤ hi`). -/
theorem wrappingRangeContains_nonwrapping_eq_false_iff
    {lo hi v : Nat} (hLe : lo ≤ hi) :
    wrappingRangeContains ⟨lo, hi⟩ v = false ↔ (v < lo ∨ hi < v) := by
  rw [← Bool.not_eq_true, wrappingRangeContains_nonwrapping_iff hLe]
  omega

/-- Contiguous `0..=maxTag` enum discriminant range characterization. -/
theorem wrappingRangeContains_zero_max_iff (maxTag v : Nat) :
    wrappingRangeContains ⟨0, maxTag⟩ v = true ↔ v ≤ maxTag := by
  rw [wrappingRangeContains_nonwrapping_iff (Nat.zero_le maxTag)]
  omega

/-- Full scalar range `0..=scalarModulus sz - 1` characterization. -/
theorem wrappingRangeContains_fullRange_iff (sz v : Nat) :
    wrappingRangeContains ⟨0, scalarModulus sz - 1⟩ v = true ↔
      v < scalarModulus sz := by
  have hPos : 0 < scalarModulus sz := Anneal.Scalars.scalarModulus_pos sz
  rw [wrappingRangeContains_zero_max_iff]
  omega

theorem wrappingRangeContains_fullRange_of_lt
    {sz v : Nat} (hLt : v < scalarModulus sz) :
    wrappingRangeContains ⟨0, scalarModulus sz - 1⟩ v = true :=
  (wrappingRangeContains_fullRange_iff sz v).mpr hLt

/-- `NonZero*` niche range `1..=scalarModulus sz - 1` characterization (`1 ≤ sz`). -/
theorem wrappingRangeContains_nonZeroRange_iff
    {sz : Nat} (hSz : 0 < sz) (v : Nat) :
    wrappingRangeContains ⟨1, scalarModulus sz - 1⟩ v = true ↔
      (0 < v ∧ v < scalarModulus sz) := by
  have hMod : 256 ≤ scalarModulus sz := by
    cases sz with
    | zero => omega
    | succ k =>
      have hk : 0 < scalarModulus k := Anneal.Scalars.scalarModulus_pos k
      change 256 ≤ 256 * scalarModulus k
      omega
  rw [wrappingRangeContains_nonwrapping_iff (by omega)]
  omega

/-- `NonZero*` niche range rejects `0` for every positive byte width `0 < sz`. -/
theorem wrappingRangeContains_nonZeroRange_zero
    {sz : Nat} (hSz : 0 < sz) :
    wrappingRangeContains ⟨1, scalarModulus sz - 1⟩ 0 = false := by
  apply Bool.eq_false_iff.mpr
  intro hTrue
  have ⟨hPos, _⟩ := (wrappingRangeContains_nonZeroRange_iff hSz 0).mp hTrue
  omega

/-- Closed-form reduction of `decodeScalarLayoutBytes` for an initialized integer scalar layout. -/
theorem decodeScalarLayoutBytes_initialized_int_eq
    (bitsWidth : Nat) (signed : Bool) (validRange : WrappingRange)
    (sz : Nat) (bs : List AbstractByte)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some sz) :
    decodeScalarLayoutBytes (.initialized (.int bitsWidth signed) validRange) bs =
      match Nat.beq (length bs) sz with
      | false => none
      | true =>
        match decodeScalarBytes bs false with
        | none => none
        | some (sv, _) =>
          match wrappingRangeContains validRange sv.bits with
          | false => none
          | true => some (.scalar sv) := by
  unfold decodeScalarLayoutBytes scalarLayoutByteWidth
  dsimp only
  rw [hWidth]
  rfl

/-- Exact characterization of when `decodeScalarLayoutBytes (.initialized pk validRange) bs` succeeds. -/
theorem decodeScalarLayoutBytes_initialized_some_iff
    (pk : PrimitiveKind) (validRange : WrappingRange)
    (sz : Nat) (bs : List AbstractByte)
    (hWidth : primitiveKindByteWidth pk = some sz) :
    (∃ v, decodeScalarLayoutBytes (.initialized pk validRange) bs = some v) ↔
      (length bs = sz ∧
       ∃ sv prov,
         decodeScalarBytes bs false = some (sv, prov) ∧
         wrappingRangeContains validRange sv.bits = true) := by
  unfold decodeScalarLayoutBytes scalarLayoutByteWidth
  dsimp only
  rw [hWidth]
  dsimp only
  cases hLen : Nat.beq (length bs) sz
  · simp only [reduceCtorEq, exists_false, false_iff]
    rintro ⟨hEq, _⟩
    have : Nat.beq (length bs) sz = true := Nat.beq_eq.mpr hEq
    rw [hLen] at this
    nomatch this
  · have hLenEq : length bs = sz := Nat.eq_of_beq_eq_true hLen
    simp only [hLenEq, true_and]
    cases hSc : decodeScalarBytes bs false
    · simp
    case some pair =>
      rcases pair with ⟨sv, prov⟩
      dsimp only
      cases hRange : wrappingRangeContains validRange sv.bits
      · constructor
        · rintro ⟨v, hv⟩; nomatch hv
        · rintro ⟨sv', prov', hEq, hR⟩
          injection hEq with hPair
          injection hPair with hSv _
          subst hSv
          rw [hRange] at hR
          nomatch hR
      · constructor
        · intro _
          exact ⟨sv, prov, rfl, hRange⟩
        · intro _
          cases pk with
          | pointer _ =>
            cases prov <;> exact ⟨_, rfl⟩
          | int _ _ => exact ⟨_, rfl⟩
          | float _ => exact ⟨_, rfl⟩

/-- Any initialized scalar layout whose `validRange` contains `[0, scalarModulus sz)` decodes all initialized `sz`-byte sequences. -/
theorem decodeScalarLayoutBytes_initialized_fullRange_of_allBytesInitialized
    (pk : PrimitiveKind) (validRange : WrappingRange) (sz : Nat)
    (hWidth : primitiveKindByteWidth pk = some sz)
    (hNz : Nat.beq sz 0 = false)
    (hFull : ∀ b, b < scalarModulus sz → wrappingRangeContains validRange b = true)
    (bs : List AbstractByte)
    (hLen : length bs = sz)
    (hInit : allBytesInitialized bs = true) :
    ∃ v, decodeScalarLayoutBytes (.initialized pk validRange) bs = some v := by
  rcases decodeScalarBytes_of_allBytesInitialized bs false (hLen ▸ hNz) hInit
    with ⟨sv, prov, hSc⟩
  have ⟨_, hLt⟩ := decodeScalarBytes_bits_lt bs false sv prov hSc
  rw [hLen] at hLt
  exact (decodeScalarLayoutBytes_initialized_some_iff pk validRange sz bs hWidth).mpr
    ⟨hLen, sv, prov, hSc, hFull sv.bits hLt⟩

/-- Zero-byte decoding characterization for `ScalarLayout.initialized`. -/
theorem decodeScalarLayoutBytes_initialized_zeroInitBytes_iff
    (pk : PrimitiveKind) (validRange : WrappingRange) (sz : Nat)
    (hWidth : primitiveKindByteWidth pk = some sz)
    (hNz : Nat.beq sz 0 = false) :
    (∃ v, decodeScalarLayoutBytes (.initialized pk validRange) (zeroInitBytes sz) = some v) ↔
      wrappingRangeContains validRange 0 = true := by
  rw [decodeScalarLayoutBytes_initialized_some_iff pk validRange sz (zeroInitBytes sz) hWidth]
  rw [length_zeroInitBytes sz, decodeScalarBytes_zeroInitBytes sz false hNz]
  constructor
  · rintro ⟨_, sv, prov, hEq, hRange⟩
    injection hEq with hPair
    injection hPair with hSv _
    subst hSv
    exact hRange
  · intro hRange
    exact ⟨rfl, ⟨0, sz⟩, none, rfl, hRange⟩

/--
Candidate-validation characterization of `decodeScalarLayoutBytes
(.initialized pk validRange)` for any `PrimitiveKind` of byte width `sz`: the
encoding of a bit pattern `bits < scalarModulus sz` (carrying any byte
provenance `prov`) is accepted exactly when
`wrappingRangeContains validRange bits = true`.
-/
theorem decodeScalarLayoutBytes_initialized_encode_some_iff
    (pk : PrimitiveKind) (validRange : WrappingRange) (sz bits : Nat)
    (prov : Option (Nat × Nat))
    (hWidth : primitiveKindByteWidth pk = some sz)
    (hNz : Nat.beq sz 0 = false)
    (hBits : bits < scalarModulus sz) :
    (∃ v, decodeScalarLayoutBytes (.initialized pk validRange)
        (encodeLittleEndianBytes bits sz prov) = some v) ↔
      wrappingRangeContains validRange bits = true := by
  have hPos : 0 < sz := by
    cases sz with
    | zero => nomatch hNz
    | succ k => exact Nat.succ_pos k
  rw [decodeScalarLayoutBytes_initialized_some_iff pk validRange sz _ hWidth,
    length_encodeLittleEndianBytes prov sz bits,
    decodeScalarBytes_encodeLittleEndianBytes_of_lt sz bits prov false hPos hBits]
  constructor
  · rintro ⟨_, sv, p, hEq, hRange⟩
    injection hEq with hPair
    injection hPair with hSv _
    subst hSv
    exact hRange
  · intro hRange
    exact ⟨rfl, ⟨bits, sz⟩, prov, rfl, hRange⟩

/--
Exact decoding equation for an initialized integer scalar layout on an encoded
candidate bit pattern `bits < scalarModulus sz`: the result is
`.scalar ⟨bits, sz⟩` when `wrappingRangeContains validRange bits = true` and
`none` otherwise.
-/
theorem decodeScalarLayoutBytes_initialized_int_encode_eq
    (bitsWidth : Nat) (signed : Bool) (validRange : WrappingRange) (sz bits : Nat)
    (prov : Option (Nat × Nat))
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some sz)
    (hNz : Nat.beq sz 0 = false)
    (hBits : bits < scalarModulus sz) :
    decodeScalarLayoutBytes (.initialized (.int bitsWidth signed) validRange)
        (encodeLittleEndianBytes bits sz prov) =
      match wrappingRangeContains validRange bits with
      | true => some (.scalar ⟨bits, sz⟩)
      | false => none := by
  have hPos : 0 < sz := by
    cases sz with
    | zero => nomatch hNz
    | succ k => exact Nat.succ_pos k
  have hBeq : Nat.beq (length (encodeLittleEndianBytes bits sz prov)) sz = true := by
    rw [length_encodeLittleEndianBytes prov sz bits]
    exact Nat.beq_refl sz
  rw [decodeScalarLayoutBytes_initialized_int_eq bitsWidth signed validRange sz _ hWidth, hBeq]
  dsimp only
  rw [decodeScalarBytes_encodeLittleEndianBytes_of_lt sz bits prov false hPos hBits]
  dsimp only
  cases wrappingRangeContains validRange bits <;> rfl

/--
For any inhabited, non-zero-sized single-variant `.primitive` ADT whose backend
representation is `.scalar s0`, `decodeValueFromBytes` reduces directly to
`decodeScalarLayoutBytes s0` whenever `scalarLayoutByteWidth s0 = some l.size.bytes`.
-/
theorem decodeValueFromBytes_adt_primitive_scalarLayout
    (fuel : Nat) (layouts : LayoutTable) (defPath : DefPath)
    (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx : Nat) (s0 : ScalarLayout)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hRepr : l.backendRepr = .scalar s0)
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : scalarLayoutByteWidth s0 = some l.size.bytes)
    (bs : List AbstractByte) :
    decodeValueFromBytes (fuel + 1) layouts { kind := .adt defPath args, layoutIdx := idx } bs =
      decodeScalarLayoutBytes s0 bs := by
  unfold decodeValueFromBytes
  simp only [hLookup, hInhab, Bool.false_or, hVar, hFields, hNz, hRepr]
  unfold decodeScalarLayoutBytes
  rw [hWidth]
  cases hBeq : Nat.beq (length bs) l.size.bytes <;> simp [hBeq]

/--
Exact decodability characterization (`try_transmute` completeness) for an
inhabited single-variant `.primitive` ADT with `ScalarLayout.initialized pk
validRange`: `decodeValueFromBytes` accepts `bs` if and only if `bs` has the
layout size, all of its bytes are initialized (so `decodeScalarBytes`
succeeds), and the decoded bit pattern lies in `validRange`.
-/
theorem adt_primitive_scalarLayout_decode_some_iff
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx : Nat) (pk : PrimitiveKind) (validRange : WrappingRange)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hRepr : l.backendRepr = .scalar (.initialized pk validRange))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth pk = some l.size.bytes)
    (bs : List AbstractByte) :
    (∃ v, decodeValueFromBytes defaultCodecFuel layouts
        { kind := .adt defPath args, layoutIdx := idx } bs = some v) ↔
      (length bs = l.size.bytes ∧
       ∃ sv prov,
         decodeScalarBytes bs false = some (sv, prov) ∧
         wrappingRangeContains validRange sv.bits = true) := by
  rw [show defaultCodecFuel = 15 + 1 from rfl,
    decodeValueFromBytes_adt_primitive_scalarLayout 15 layouts defPath args idx l variantIdx
      (.initialized pk validRange) hLookup hInhab hVar hFields hRepr hNz hWidth bs]
  exact decodeScalarLayoutBytes_initialized_some_iff pk validRange l.size.bytes bs hWidth

/--
Candidate-validation form of `adt_primitive_scalarLayout_decode_some_iff` for an
integer scalar layout: the encoding of any bit pattern
`bits < scalarModulus l.size.bytes` (carrying any byte provenance `prov`)
decodes to `.scalar ⟨bits, l.size.bytes⟩` when
`wrappingRangeContains validRange bits = true`, and is rejected otherwise.
-/
theorem adt_primitive_scalarLayout_decode_encode_eq
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx bitsWidth : Nat) (signed : Bool) (validRange : WrappingRange)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hRepr : l.backendRepr = .scalar (.initialized (.int bitsWidth signed) validRange))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes)
    (bits : Nat) (prov : Option (Nat × Nat))
    (hBits : bits < scalarModulus l.size.bytes) :
    decodeValueFromBytes defaultCodecFuel layouts
        { kind := .adt defPath args, layoutIdx := idx }
        (encodeLittleEndianBytes bits l.size.bytes prov) =
      match wrappingRangeContains validRange bits with
      | true => some (.scalar ⟨bits, l.size.bytes⟩)
      | false => none := by
  rw [show defaultCodecFuel = 15 + 1 from rfl,
    decodeValueFromBytes_adt_primitive_scalarLayout 15 layouts defPath args idx l variantIdx
      (.initialized (.int bitsWidth signed) validRange) hLookup hInhab hVar hFields hRepr hNz
      hWidth _]
  exact decodeScalarLayoutBytes_initialized_int_encode_eq bitsWidth signed validRange
    l.size.bytes bits prov hWidth hNz hBits

/--
A single-variant `.primitive` ADT with `ScalarLayout.initialized pk validRange`
satisfies `IsFromBytes` whenever `validRange` covers all bit patterns `< scalarModulus l.size.bytes`.
-/
theorem adt_primitive_scalarLayout_isFromBytes_of_fullRange
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx : Nat) (pk : PrimitiveKind) (validRange : WrappingRange)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hRepr : l.backendRepr = .scalar (.initialized pk validRange))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth pk = some l.size.bytes)
    (hFull : ∀ b, b < scalarModulus l.size.bytes → wrappingRangeContains validRange b = true) :
    IsFromBytes layouts { kind := .adt defPath args, layoutIdx := idx } := by
  refine ⟨l.size.bytes, by simp [rigidTyByteSize, hLookup], ?_⟩
  intro bs hLen hInit
  rw [show defaultCodecFuel = 15 + 1 from rfl,
      decodeValueFromBytes_adt_primitive_scalarLayout 15 layouts defPath args idx l variantIdx
        (.initialized pk validRange) hLookup hInhab hVar hFields hRepr hNz hWidth bs]
  exact decodeScalarLayoutBytes_initialized_fullRange_of_allBytesInitialized
    pk validRange l.size.bytes hWidth hNz hFull bs hLen hInit

/--
A single-variant `.primitive` ADT with full-range `validRange = ⟨0, scalarModulus l.size.bytes - 1⟩`
satisfies `IsFromBytes`.
-/
theorem adt_primitive_scalarLayout_isFromBytes
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx : Nat) (pk : PrimitiveKind)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hRepr : l.backendRepr = .scalar (.initialized pk ⟨0, scalarModulus l.size.bytes - 1⟩))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth pk = some l.size.bytes) :
    IsFromBytes layouts { kind := .adt defPath args, layoutIdx := idx } :=
  adt_primitive_scalarLayout_isFromBytes_of_fullRange
    layouts defPath args idx l variantIdx pk ⟨0, scalarModulus l.size.bytes - 1⟩
    hLookup hInhab hVar hFields hRepr hNz hWidth
    (fun _ hLt => wrappingRangeContains_fullRange_of_lt hLt)

/--
Exact `IsFromBytes` characterization for a single-variant `.primitive` ADT with
`ScalarLayout.initialized pk validRange`: it satisfies `IsFromBytes` if and only
if `validRange` contains every bit pattern below `scalarModulus l.size.bytes`.
-/
theorem adt_primitive_scalarLayout_isFromBytes_iff
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx : Nat) (pk : PrimitiveKind) (validRange : WrappingRange)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hRepr : l.backendRepr = .scalar (.initialized pk validRange))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth pk = some l.size.bytes) :
    IsFromBytes layouts { kind := .adt defPath args, layoutIdx := idx } ↔
      ∀ b, b < scalarModulus l.size.bytes → wrappingRangeContains validRange b = true := by
  constructor
  · rintro ⟨sz, hSz, hDec⟩ b hB
    have hSzEq : sz = l.size.bytes := by
      have h : rigidTyByteSize layouts { kind := .adt defPath args, layoutIdx := idx } =
          some l.size.bytes := by
        simp [rigidTyByteSize, hLookup]
      rw [h] at hSz
      exact (Option.some.inj hSz).symm
    rw [hSzEq] at hDec
    rcases hDec (encodeLittleEndianBytes b l.size.bytes none)
      (length_encodeLittleEndianBytes none l.size.bytes b)
      (allBytesInitialized_encodeLittleEndianBytes none l.size.bytes b) with ⟨v, hv⟩
    have hDecIff := (adt_primitive_scalarLayout_decode_some_iff layouts defPath args idx l
      variantIdx pk validRange hLookup hInhab hVar hFields hRepr hNz hWidth
      (encodeLittleEndianBytes b l.size.bytes none)).mp ⟨v, hv⟩
    rcases hDecIff with ⟨_, sv, prov, hSc, hRange⟩
    have hPos : 0 < l.size.bytes := by
      cases h : l.size.bytes with
      | zero => rw [h] at hNz; nomatch hNz
      | succ k => exact Nat.succ_pos k
    rw [decodeScalarBytes_encodeLittleEndianBytes_of_lt l.size.bytes b none false hPos hB] at hSc
    injection hSc with hPair
    injection hPair with hSv _
    subst hSv
    exact hRange
  · intro hFull
    exact adt_primitive_scalarLayout_isFromBytes_of_fullRange layouts defPath args idx l
      variantIdx pk validRange hLookup hInhab hVar hFields hRepr hNz hWidth hFull

/--
Exact `IsFromZeros` characterization for a single-variant `.primitive` ADT with
`ScalarLayout.initialized pk validRange`: it satisfies `IsFromZeros` iff
`wrappingRangeContains validRange 0 = true`.
-/
theorem adt_primitive_scalarLayout_isFromZeros_iff
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx : Nat) (pk : PrimitiveKind) (validRange : WrappingRange)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hRepr : l.backendRepr = .scalar (.initialized pk validRange))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth pk = some l.size.bytes) :
    IsFromZeros layouts { kind := .adt defPath args, layoutIdx := idx } ↔
      wrappingRangeContains validRange 0 = true := by
  have hSz : rigidTyByteSize layouts { kind := .adt defPath args, layoutIdx := idx } =
      some l.size.bytes := by
    simp [rigidTyByteSize, hLookup]
  have hRed := decodeValueFromBytes_adt_primitive_scalarLayout 15 layouts defPath args idx
    l variantIdx (.initialized pk validRange) hLookup hInhab hVar hFields hRepr hNz hWidth
    (zeroInitBytes l.size.bytes)
  rw [← decodeScalarLayoutBytes_initialized_zeroInitBytes_iff pk validRange l.size.bytes hWidth hNz]
  constructor
  · rintro ⟨sz, v, hSzEq, hDec⟩
    rw [hSz] at hSzEq
    injection hSzEq with hEq
    subst hEq
    rw [show defaultCodecFuel = 15 + 1 from rfl, hRed] at hDec
    exact ⟨v, hDec⟩
  · rintro ⟨v, hDec⟩
    refine ⟨l.size.bytes, v, hSz, ?_⟩
    rw [show defaultCodecFuel = 15 + 1 from rfl, hRed]
    exact hDec

theorem adt_primitive_scalarLayout_isFromZeros
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx : Nat) (pk : PrimitiveKind) (validRange : WrappingRange)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hRepr : l.backendRepr = .scalar (.initialized pk validRange))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth pk = some l.size.bytes)
    (hZero : wrappingRangeContains validRange 0 = true) :
    IsFromZeros layouts { kind := .adt defPath args, layoutIdx := idx } :=
  (adt_primitive_scalarLayout_isFromZeros_iff layouts defPath args idx l variantIdx pk validRange
    hLookup hInhab hVar hFields hRepr hNz hWidth).mpr hZero

theorem adt_primitive_scalarLayout_not_isFromZeros
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx : Nat) (pk : PrimitiveKind) (validRange : WrappingRange)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hRepr : l.backendRepr = .scalar (.initialized pk validRange))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth pk = some l.size.bytes)
    (hNoZero : wrappingRangeContains validRange 0 = false) :
    ¬ IsFromZeros layouts { kind := .adt defPath args, layoutIdx := idx } := by
  intro hFZ
  have hTrue := (adt_primitive_scalarLayout_isFromZeros_iff layouts defPath args idx l variantIdx
    pk validRange hLookup hInhab hVar hFields hRepr hNz hWidth).mp hFZ
  rw [hNoZero] at hTrue
  nomatch hTrue

/--
`IsTryFromBytes` bridge for a single-variant `.primitive` ADT with
`ScalarLayout.initialized (.int bitsWidth signed) validRange`: every decoded value is
a `.scalar sv` of width `l.size.bytes` whose bit pattern satisfies
`wrappingRangeContains validRange sv.bits = true`.
-/
theorem adt_primitive_scalarLayout_isTryFromBytes
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx bitsWidth : Nat) (signed : Bool) (validRange : WrappingRange)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hRepr : l.backendRepr = .scalar (.initialized (.int bitsWidth signed) validRange))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes) :
    IsTryFromBytes layouts { kind := .adt defPath args, layoutIdx := idx }
      (fun v =>
        ∃ sv : ScalarVal,
          v = .scalar sv ∧
          sv.sizeBytes = l.size.bytes ∧
          sv.bits < scalarModulus l.size.bytes ∧
          wrappingRangeContains validRange sv.bits = true) := by
  refine ⟨l.size.bytes, by simp [rigidTyByteSize, hLookup], ?_⟩
  intro bs v hDec
  rw [show defaultCodecFuel = 15 + 1 from rfl,
      decodeValueFromBytes_adt_primitive_scalarLayout 15 layouts defPath args idx l variantIdx
        (.initialized (.int bitsWidth signed) validRange) hLookup hInhab hVar hFields hRepr hNz hWidth bs,
      decodeScalarLayoutBytes_initialized_int_eq bitsWidth signed validRange l.size.bytes bs hWidth] at hDec
  cases hLen : Nat.beq (length bs) l.size.bytes <;> rw [hLen] at hDec
  · nomatch hDec
  · dsimp only at hDec
    cases hSc : decodeScalarBytes bs false <;> rw [hSc] at hDec
    · nomatch hDec
    case some pair =>
      rcases pair with ⟨sv, prov⟩
      dsimp only at hDec
      cases hRange : wrappingRangeContains validRange sv.bits <;> rw [hRange] at hDec
      · nomatch hDec
      · injection hDec with hV
        have hBsLen : length bs = l.size.bytes := Nat.eq_of_beq_eq_true hLen
        have ⟨hSvSz, hSvLt⟩ := decodeScalarBytes_bits_lt bs false sv prov hSc
        rw [hBsLen] at hSvSz hSvLt
        exact ⟨sv, hV.symm, hSvSz, hSvLt, hRange⟩

/--
Concrete `IsTryFromBytes` helper for a contiguous `#[repr(Int)]` enum or bounded
scalar ADT with `validRange = ⟨lo, hi⟩` (`lo ≤ hi`).
-/
theorem adt_primitive_range_isTryFromBytes
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx bitsWidth lo hi : Nat) (signed : Bool)
    (hLe : lo ≤ hi)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hRepr : l.backendRepr = .scalar (.initialized (.int bitsWidth signed) ⟨lo, hi⟩))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes) :
    IsTryFromBytes layouts { kind := .adt defPath args, layoutIdx := idx }
      (fun v =>
        ∃ sv : ScalarVal,
          v = .scalar sv ∧
          sv.sizeBytes = l.size.bytes ∧
          lo ≤ sv.bits ∧ sv.bits ≤ hi) := by
  rcases adt_primitive_scalarLayout_isTryFromBytes layouts defPath args idx l variantIdx
    bitsWidth signed ⟨lo, hi⟩ hLookup hInhab hVar hFields hRepr hNz hWidth with ⟨sz, hSz, hTry⟩
  refine ⟨sz, hSz, fun bs v hDec => ?_⟩
  rcases hTry bs v hDec with ⟨sv, rfl, hSvSz, _, hRange⟩
  have ⟨hLo, hHi⟩ := (wrappingRangeContains_nonwrapping_iff hLe).mp hRange
  exact ⟨sv, rfl, hSvSz, hLo, hHi⟩

/--
Concrete `IsTryFromBytes` helper for a `#[repr(u8)]` / contiguous `0..=maxTag`
enum tag layout.
-/
theorem adt_primitive_enumTag_isTryFromBytes
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx bitsWidth maxTag : Nat) (signed : Bool)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hRepr : l.backendRepr = .scalar (.initialized (.int bitsWidth signed) ⟨0, maxTag⟩))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes) :
    IsTryFromBytes layouts { kind := .adt defPath args, layoutIdx := idx }
      (fun v =>
        ∃ sv : ScalarVal,
          v = .scalar sv ∧
          sv.sizeBytes = l.size.bytes ∧
          sv.bits ≤ maxTag) := by
  rcases adt_primitive_range_isTryFromBytes layouts defPath args idx l variantIdx
    bitsWidth 0 maxTag signed (Nat.zero_le maxTag) hLookup hInhab hVar hFields hRepr hNz hWidth
    with ⟨sz, hSz, hTry⟩
  refine ⟨sz, hSz, fun bs v hDec => ?_⟩
  rcases hTry bs v hDec with ⟨sv, rfl, hSvSz, _, hHi⟩
  exact ⟨sv, rfl, hSvSz, hHi⟩

/--
Every contiguous `0..=maxTag` enum tag layout satisfies `IsFromZeros` (`0` is a
valid discriminant).
-/
theorem adt_primitive_enumTag_isFromZeros
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx : Nat) (pk : PrimitiveKind) (maxTag : Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hRepr : l.backendRepr = .scalar (.initialized pk ⟨0, maxTag⟩))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth pk = some l.size.bytes) :
    IsFromZeros layouts { kind := .adt defPath args, layoutIdx := idx } :=
  adt_primitive_scalarLayout_isFromZeros layouts defPath args idx l variantIdx pk ⟨0, maxTag⟩
    hLookup hInhab hVar hFields hRepr hNz hWidth
    ((wrappingRangeContains_zero_max_iff maxTag 0).mpr (Nat.zero_le maxTag))

/--
Concrete `IsTryFromBytes` helper for `NonZero*` scalar niche layouts
(`validRange = ⟨1, scalarModulus l.size.bytes - 1⟩`): every decoded value is a
non-zero scalar (`0 < sv.bits < scalarModulus l.size.bytes`).
-/
theorem adt_primitive_nonZero_isTryFromBytes
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx bitsWidth : Nat) (signed : Bool)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hRepr :
      l.backendRepr =
        .scalar (.initialized (.int bitsWidth signed) ⟨1, scalarModulus l.size.bytes - 1⟩))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes) :
    IsTryFromBytes layouts { kind := .adt defPath args, layoutIdx := idx }
      (fun v =>
        ∃ sv : ScalarVal,
          v = .scalar sv ∧
          sv.sizeBytes = l.size.bytes ∧
          0 < sv.bits ∧
          sv.bits < scalarModulus l.size.bytes) := by
  have hPos : 0 < l.size.bytes := by
    cases h : l.size.bytes with
    | zero => rw [h] at hNz; nomatch hNz
    | succ k => exact Nat.succ_pos k
  rcases adt_primitive_scalarLayout_isTryFromBytes layouts defPath args idx l variantIdx
    bitsWidth signed ⟨1, scalarModulus l.size.bytes - 1⟩
    hLookup hInhab hVar hFields hRepr hNz hWidth with ⟨sz, hSz, hTry⟩
  refine ⟨sz, hSz, fun bs v hDec => ?_⟩
  rcases hTry bs v hDec with ⟨sv, rfl, hSvSz, _, hRange⟩
  have ⟨hGt, hLt⟩ := (wrappingRangeContains_nonZeroRange_iff hPos sv.bits).mp hRange
  exact ⟨sv, rfl, hSvSz, hGt, hLt⟩

/--
Every `NonZero*` scalar niche layout (`validRange = ⟨1, scalarModulus l.size.bytes - 1⟩`)
rejects all-zero bytes (`¬ IsFromZeros`).
-/
theorem adt_primitive_nonZero_not_isFromZeros
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx : Nat) (pk : PrimitiveKind)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive)
    (hRepr :
      l.backendRepr =
        .scalar (.initialized pk ⟨1, scalarModulus l.size.bytes - 1⟩))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth pk = some l.size.bytes) :
    ¬ IsFromZeros layouts { kind := .adt defPath args, layoutIdx := idx } := by
  have hPos : 0 < l.size.bytes := by
    cases h : l.size.bytes with
    | zero => rw [h] at hNz; nomatch hNz
    | succ k => exact Nat.succ_pos k
  exact adt_primitive_scalarLayout_not_isFromZeros layouts defPath args idx l variantIdx
    pk ⟨1, scalarModulus l.size.bytes - 1⟩ hLookup hInhab hVar hFields hRepr hNz hWidth
    (wrappingRangeContains_nonZeroRange_zero hPos)

/-! ### 6.4 Single-Field Scalar-Wrapper Newtype ADTs (`FieldsShape.arbitrary [⟨0⟩]`) & Multi-Variant Fieldless Enums (`VariantsShape.multiple`)

Which decoding path applies. For a single-variant `.adt defPath args` with
`FieldsShape.arbitrary offsets`, `decodeValueFromBytes` first decodes the fields
at the type arguments `args` when `args` has the same length as `offsets`, then
at the recorded per-field layouts `l.fieldLayouts` when those have the same
length, and only otherwise falls back to the backend scalar representation
`l.backendRepr`. Only that last path enforces a scalar niche recorded in
`l.backendRepr`. The `adt_newtype_*` theorems below assume it (`args = []` and
`l.fieldLayouts = []`). A monomorphized generic wrapper such as `NonZero<u32>`
(`args = [u32]`) takes the type-argument path, where the niche is **not**
enforced (`adt_generic_nonZero_typeArg_path_niche_unenforced`). The
field-layout path does not read the wrapper's `l.backendRepr` either: it decodes
each field at its own recorded layout. So it enforces exactly the niches recorded
on those field layouts (`adt_fieldLayout_path_inner_primitive_scalarLayout_decode_encode_eq`)
and ignores a niche recorded only on the wrapper
(`adt_fieldLayout_path_outer_niche_unenforced`).

The `.multiple` decoder uses the tag value itself as the variant index
(`get? variantShapes tag`), and the encoder writes the variant index as the tag.
This matches `rustc` only for direct tags whose discriminants are the variant
indices `0..n-1`; explicit discriminants diverge
(`adt_multiple_enum_explicit_discriminant_divergence`).
-/

@[simp]
theorem sliceAbstractBytes_zero_full
    (bs : List AbstractByte) (sz : Nat)
    (hLen : length bs = sz) :
    sliceAbstractBytes bs 0 sz = some bs := by
  unfold sliceAbstractBytes
  have hBle : Nat.ble (Nat.add 0 sz) (length bs) = true := by
    change Nat.ble (0 + sz) (length bs) = true
    rw [Nat.zero_add, hLen]
    exact Nat.ble_eq_true_of_le (Nat.le_refl sz)
  rw [hBle]
  dsimp only
  rw [dropAbstractBytes_eq_drop, List.drop_zero, takeAbstractBytes_eq_take]
  have hBsLen : bs.length = sz := hLen
  rw [← hBsLen, List.take_length]

/--
Unfolding lemma for `decodeValueFromBytes` on an inhabited single-variant
single-field scalar-wrapper newtype `.adt defPath []` (`l.fields = .arbitrary [⟨0⟩] memoryOrder`,
`l.fieldLayouts = []`, `l.backendRepr = .scalar sl`, `scalarLayoutByteWidth sl = some l.size.bytes`):
with no type arguments and no recorded field layouts, decoding reaches the
backend scalar path and enforces `sl`. This is the shape of a scalar-niche
wrapper such as `core::num::NonZero*` when its layout entry records no per-field
layouts; see the section note for the type-argument path, which does not
enforce the niche.
-/
theorem decodeValueFromBytes_adt_newtype_scalarLayout
    (fuel : Nat) (layouts : LayoutTable) (defPath : DefPath) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx : Nat) (memoryOrder : List Nat) (sl : ScalarLayout)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hNoFieldLayouts : l.fieldLayouts = [])
    (hRepr : l.backendRepr = .scalar sl)
    (hWidth : scalarLayoutByteWidth sl = some l.size.bytes)
    (bs : List AbstractByte) :
    decodeValueFromBytes (fuel + 1) layouts { kind := .adt defPath [], layoutIdx := idx } bs =
      match Nat.beq (length bs) l.size.bytes with
      | false => none
      | true =>
        match decodeScalarLayoutBytes sl bs with
        | some v0 => some (.aggregate variantIdx [v0])
        | none => none := by
  unfold decodeValueFromBytes
  dsimp only
  rw [hLookup]
  dsimp only
  rw [hInhab]
  cases hLen : Nat.beq (length bs) l.size.bytes
  · rfl
  · dsimp only [Bool.not, Bool.or]
    rw [hVar, hFields, hNoFieldLayouts, hRepr]
    dsimp only
    have hBeqNil : Nat.beq (length ([] : List RigidTy)) (length ([{ bytes := 0 }] : List Size)) = false := rfl
    have hBeqFl : Nat.beq (length ([] : List Nat)) (length ([{ bytes := 0 }] : List Size)) = false := rfl
    rw [hBeqNil, hBeqFl]
    dsimp only
    rw [hWidth]
    dsimp only
    have hBsLen : length bs = l.size.bytes := Nat.eq_of_beq_eq_true hLen
    rw [sliceAbstractBytes_zero_full bs l.size.bytes hBsLen]
    rfl

/--
Exact evaluation of `decodeValueFromBytes` on `encodeLittleEndianBytes bits l.size.bytes prov`
for a single-field scalar-wrapper newtype `.adt defPath []` with
`ScalarLayout.initialized (.int bitsWidth signed) validRange`.
-/
theorem adt_newtype_scalarLayout_decode_encode_eq
    (layouts : LayoutTable) (defPath : DefPath) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx bitsWidth : Nat) (memoryOrder : List Nat)
    (signed : Bool) (validRange : WrappingRange)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hNoFieldLayouts : l.fieldLayouts = [])
    (hRepr : l.backendRepr = .scalar (.initialized (.int bitsWidth signed) validRange))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes)
    (bits : Nat) (prov : Option (Nat × Nat))
    (hBits : bits < scalarModulus l.size.bytes) :
    decodeValueFromBytes defaultCodecFuel layouts
        { kind := .adt defPath [], layoutIdx := idx }
        (encodeLittleEndianBytes bits l.size.bytes prov) =
      match wrappingRangeContains validRange bits with
      | true => some (.aggregate variantIdx [.scalar ⟨bits, l.size.bytes⟩])
      | false => none := by
  have hPos : 0 < l.size.bytes := by
    cases h : l.size.bytes with
    | zero => rw [h] at hNz; nomatch hNz
    | succ k => exact Nat.succ_pos k
  have hBeqLen :
      Nat.beq (length (encodeLittleEndianBytes bits l.size.bytes prov)) l.size.bytes = true := by
    rw [length_encodeLittleEndianBytes]
    exact Nat.beq_refl _
  rw [show defaultCodecFuel = 15 + 1 from rfl,
      decodeValueFromBytes_adt_newtype_scalarLayout 15 layouts defPath idx l variantIdx
        memoryOrder (.initialized (.int bitsWidth signed) validRange)
        hLookup hInhab hVar hFields hNoFieldLayouts hRepr hWidth,
      hBeqLen]
  dsimp only
  rw [decodeScalarLayoutBytes_initialized_int_eq bitsWidth signed validRange l.size.bytes _ hWidth,
      hBeqLen]
  dsimp only
  rw [decodeScalarBytes_encodeLittleEndianBytes_of_lt l.size.bytes bits prov false hPos hBits]
  dsimp only
  cases wrappingRangeContains validRange bits <;> rfl

/--
A single-field scalar-wrapper newtype `.adt defPath []` with
`ScalarLayout.initialized (.int bitsWidth signed) validRange` satisfies `IsFromBytes`
whenever `validRange` covers all bit patterns `< scalarModulus l.size.bytes`.
-/
theorem adt_newtype_scalarLayout_isFromBytes_of_fullRange
    (layouts : LayoutTable) (defPath : DefPath) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx bitsWidth : Nat) (memoryOrder : List Nat)
    (signed : Bool) (validRange : WrappingRange)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hNoFieldLayouts : l.fieldLayouts = [])
    (hRepr : l.backendRepr = .scalar (.initialized (.int bitsWidth signed) validRange))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes)
    (hAllValid : ∀ bits < scalarModulus l.size.bytes, wrappingRangeContains validRange bits = true) :
    IsFromBytes layouts { kind := .adt defPath [], layoutIdx := idx } := by
  refine ⟨l.size.bytes, by simp [rigidTyByteSize, hLookup], ?_⟩
  intro bs hLen hInit
  have hBeqLen : Nat.beq (length bs) l.size.bytes = true := by
    rw [hLen]; exact Nat.beq_refl _
  rcases decodeScalarBytes_of_allBytesInitialized bs false (hLen ▸ hNz) hInit with
    ⟨sv, prov, hDec⟩
  have ⟨_, hBitsLt⟩ := decodeScalarBytes_bits_lt bs false sv prov hDec
  rw [hLen] at hBitsLt
  have hValid : wrappingRangeContains validRange sv.bits = true :=
    hAllValid sv.bits hBitsLt
  refine ⟨.aggregate variantIdx [.scalar sv], ?_⟩
  rw [show defaultCodecFuel = 15 + 1 from rfl,
      decodeValueFromBytes_adt_newtype_scalarLayout 15 layouts defPath idx l variantIdx
        memoryOrder (.initialized (.int bitsWidth signed) validRange)
        hLookup hInhab hVar hFields hNoFieldLayouts hRepr hWidth,
      hBeqLen]
  dsimp only
  rw [decodeScalarLayoutBytes_initialized_int_eq bitsWidth signed validRange l.size.bytes bs hWidth]
  simp [hBeqLen, hDec, hValid]

/--
Conversely, if any bit pattern `bits < scalarModulus l.size.bytes` falls outside
`validRange`, then a single-field scalar-wrapper newtype `.adt defPath []` does NOT
satisfy `IsFromBytes`.
-/
theorem adt_newtype_scalarLayout_not_isFromBytes_of_invalidBit
    (layouts : LayoutTable) (defPath : DefPath) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx bitsWidth : Nat) (memoryOrder : List Nat)
    (signed : Bool) (validRange : WrappingRange) (bits : Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hNoFieldLayouts : l.fieldLayouts = [])
    (hRepr : l.backendRepr = .scalar (.initialized (.int bitsWidth signed) validRange))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes)
    (hBits : bits < scalarModulus l.size.bytes)
    (hInvalid : wrappingRangeContains validRange bits = false) :
    ¬ IsFromBytes layouts { kind := .adt defPath [], layoutIdx := idx } := by
  rintro ⟨sz, hSz, hDecAll⟩
  simp [rigidTyByteSize, hLookup] at hSz
  subst hSz
  let bs := encodeLittleEndianBytes bits l.size.bytes none
  rcases hDecAll bs (length_encodeLittleEndianBytes none l.size.bytes bits)
    (allBytesInitialized_encodeLittleEndianBytes none l.size.bytes bits) with ⟨v, hDec⟩
  rw [adt_newtype_scalarLayout_decode_encode_eq layouts defPath idx l variantIdx
      bitsWidth memoryOrder signed validRange hLookup hInhab hVar hFields hNoFieldLayouts
      hRepr hNz hWidth bits none hBits, hInvalid] at hDec
  nomatch hDec

/--
Exact bidirectional characterization of `IsFromBytes` for single-field scalar-wrapper
newtype ADTs (`FieldsShape.arbitrary [⟨0⟩]`): `IsFromBytes` holds if and only if
`wrappingRangeContains validRange bits = true` for every `bits < scalarModulus l.size.bytes`.
-/
theorem adt_newtype_scalarLayout_isFromBytes_iff_allInRange
    (layouts : LayoutTable) (defPath : DefPath) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx bitsWidth : Nat) (memoryOrder : List Nat)
    (signed : Bool) (validRange : WrappingRange)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hNoFieldLayouts : l.fieldLayouts = [])
    (hRepr : l.backendRepr = .scalar (.initialized (.int bitsWidth signed) validRange))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes) :
    IsFromBytes layouts { kind := .adt defPath [], layoutIdx := idx } ↔
      (∀ bits < scalarModulus l.size.bytes, wrappingRangeContains validRange bits = true) := by
  constructor
  · intro hFrom bits hBits
    cases hValid : wrappingRangeContains validRange bits
    · exfalso
      exact adt_newtype_scalarLayout_not_isFromBytes_of_invalidBit
        layouts defPath idx l variantIdx bitsWidth memoryOrder signed validRange bits
        hLookup hInhab hVar hFields hNoFieldLayouts hRepr hNz hWidth hBits hValid hFrom
    · rfl
  · exact adt_newtype_scalarLayout_isFromBytes_of_fullRange
      layouts defPath idx l variantIdx bitsWidth memoryOrder signed validRange
      hLookup hInhab hVar hFields hNoFieldLayouts hRepr hNz hWidth

/--
A single-field scalar-wrapper newtype `.adt defPath []` with
`ScalarLayout.initialized (.int bitsWidth signed) validRange` satisfies `IsFromZeros`
whenever `0` lies in `validRange`.
-/
theorem adt_newtype_scalarLayout_isFromZeros_of_zeroInRange
    (layouts : LayoutTable) (defPath : DefPath) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx bitsWidth : Nat) (memoryOrder : List Nat)
    (signed : Bool) (validRange : WrappingRange)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hNoFieldLayouts : l.fieldLayouts = [])
    (hRepr : l.backendRepr = .scalar (.initialized (.int bitsWidth signed) validRange))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes)
    (hZeroValid : wrappingRangeContains validRange 0 = true) :
    IsFromZeros layouts { kind := .adt defPath [], layoutIdx := idx } := by
  refine ⟨l.size.bytes, .aggregate variantIdx [.scalar ⟨0, l.size.bytes⟩],
    by simp [rigidTyByteSize, hLookup], ?_⟩
  have hBeqLen : Nat.beq (length (zeroInitBytes l.size.bytes)) l.size.bytes = true := by
    rw [length_zeroInitBytes]; exact Nat.beq_refl _
  rw [show defaultCodecFuel = 15 + 1 from rfl,
      decodeValueFromBytes_adt_newtype_scalarLayout 15 layouts defPath idx l variantIdx
        memoryOrder (.initialized (.int bitsWidth signed) validRange)
        hLookup hInhab hVar hFields hNoFieldLayouts hRepr hWidth,
      hBeqLen]
  dsimp only
  rw [decodeScalarLayoutBytes_initialized_int_eq bitsWidth signed validRange l.size.bytes
        (zeroInitBytes l.size.bytes) hWidth,
      hBeqLen]
  dsimp only
  rw [decodeScalarBytes_zeroInitBytes l.size.bytes false hNz]
  dsimp only
  rw [hZeroValid]

/--
A single-field scalar-wrapper newtype `.adt defPath []` with
`ScalarLayout.initialized pk validRange` does NOT satisfy `IsFromZeros` whenever
`wrappingRangeContains validRange 0 = false`.
-/
theorem adt_newtype_scalarLayout_not_isFromZeros
    (layouts : LayoutTable) (defPath : DefPath) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx : Nat) (memoryOrder : List Nat)
    (pk : PrimitiveKind) (validRange : WrappingRange)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hNoFieldLayouts : l.fieldLayouts = [])
    (hRepr : l.backendRepr = .scalar (.initialized pk validRange))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth pk = some l.size.bytes)
    (hZeroInvalid : wrappingRangeContains validRange 0 = false) :
    ¬ IsFromZeros layouts { kind := .adt defPath [], layoutIdx := idx } := by
  rintro ⟨sz, v, hSz, hDec⟩
  simp [rigidTyByteSize, hLookup] at hSz
  subst hSz
  have hBeqLen : Nat.beq (length (zeroInitBytes l.size.bytes)) l.size.bytes = true := by
    rw [length_zeroInitBytes]; exact Nat.beq_refl _
  rw [show defaultCodecFuel = 15 + 1 from rfl,
      decodeValueFromBytes_adt_newtype_scalarLayout 15 layouts defPath idx l variantIdx
        memoryOrder (.initialized pk validRange)
        hLookup hInhab hVar hFields hNoFieldLayouts hRepr hWidth,
      hBeqLen] at hDec
  dsimp only at hDec
  unfold decodeScalarLayoutBytes scalarLayoutByteWidth at hDec
  dsimp only at hDec
  rw [hWidth] at hDec
  dsimp only at hDec
  rw [hBeqLen] at hDec
  dsimp only at hDec
  rw [decodeScalarBytes_zeroInitBytes l.size.bytes false hNz] at hDec
  dsimp only at hDec
  rw [hZeroInvalid] at hDec
  nomatch hDec

/--
Exact bidirectional characterization of `IsFromZeros` for single-field scalar-wrapper
newtype ADTs (`FieldsShape.arbitrary [⟨0⟩]`): `IsFromZeros` holds iff `0` lies in `validRange`.
-/
theorem adt_newtype_scalarLayout_isFromZeros_iff
    (layouts : LayoutTable) (defPath : DefPath) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx bitsWidth : Nat) (memoryOrder : List Nat)
    (signed : Bool) (validRange : WrappingRange)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hNoFieldLayouts : l.fieldLayouts = [])
    (hRepr : l.backendRepr = .scalar (.initialized (.int bitsWidth signed) validRange))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes) :
    IsFromZeros layouts { kind := .adt defPath [], layoutIdx := idx } ↔
      wrappingRangeContains validRange 0 = true := by
  constructor
  · intro hFz
    cases hZ : wrappingRangeContains validRange 0
    · exfalso
      exact adt_newtype_scalarLayout_not_isFromZeros layouts defPath idx l variantIdx
        memoryOrder (.int bitsWidth signed) validRange
        hLookup hInhab hVar hFields hNoFieldLayouts hRepr hNz hWidth hZ hFz
    · rfl
  · exact adt_newtype_scalarLayout_isFromZeros_of_zeroInRange
      layouts defPath idx l variantIdx bitsWidth memoryOrder signed validRange
      hLookup hInhab hVar hFields hNoFieldLayouts hRepr hNz hWidth

/--
`IsTryFromBytes` characterization for single-field scalar-wrapper newtype ADTs
(`FieldsShape.arbitrary [⟨0⟩]`): every decoded value has the form
`.aggregate variantIdx [.scalar sv]` with `sv.sizeBytes = l.size.bytes`,
`sv.bits < scalarModulus l.size.bytes`, and `wrappingRangeContains validRange sv.bits = true`.
-/
theorem adt_newtype_scalarLayout_isTryFromBytes
    (layouts : LayoutTable) (defPath : DefPath) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx bitsWidth : Nat) (memoryOrder : List Nat)
    (signed : Bool) (validRange : WrappingRange)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hNoFieldLayouts : l.fieldLayouts = [])
    (hRepr : l.backendRepr = .scalar (.initialized (.int bitsWidth signed) validRange))
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes) :
    IsTryFromBytes layouts { kind := .adt defPath [], layoutIdx := idx }
      (fun v =>
        ∃ sv : ScalarVal,
          v = .aggregate variantIdx [.scalar sv] ∧
          sv.sizeBytes = l.size.bytes ∧
          sv.bits < scalarModulus l.size.bytes ∧
          wrappingRangeContains validRange sv.bits = true) := by
  refine ⟨l.size.bytes, by simp [rigidTyByteSize, hLookup], ?_⟩
  intro bs v hDec
  rw [show defaultCodecFuel = 15 + 1 from rfl,
      decodeValueFromBytes_adt_newtype_scalarLayout 15 layouts defPath idx l variantIdx
        memoryOrder (.initialized (.int bitsWidth signed) validRange)
        hLookup hInhab hVar hFields hNoFieldLayouts hRepr hWidth] at hDec
  cases hLen : Nat.beq (length bs) l.size.bytes <;> rw [hLen] at hDec
  · nomatch hDec
  · dsimp only at hDec
    rw [decodeScalarLayoutBytes_initialized_int_eq bitsWidth signed validRange l.size.bytes bs hWidth,
        hLen] at hDec
    dsimp only at hDec
    cases hSc : decodeScalarBytes bs false <;> rw [hSc] at hDec
    · nomatch hDec
    case some pair =>
      rcases pair with ⟨sv, prov⟩
      dsimp only at hDec
      cases hRange : wrappingRangeContains validRange sv.bits <;> rw [hRange] at hDec
      · nomatch hDec
      · injection hDec with hV
        have hBsLen : length bs = l.size.bytes := Nat.eq_of_beq_eq_true hLen
        have ⟨hSvSz, hSvLt⟩ := decodeScalarBytes_bits_lt bs false sv prov hSc
        rw [hBsLen] at hSvSz hSvLt
        exact ⟨sv, hV.symm, hSvSz, hSvLt, hRange⟩

/--
Concrete `IsTryFromBytes` theorem for `NonZero*`-style single-field newtype layouts
(`FieldsShape.arbitrary [⟨0⟩] memoryOrder`, `validRange = ⟨1, scalarModulus l.size.bytes - 1⟩`)
decoded on the backend scalar path (`.adt defPath []`, `l.fieldLayouts = []`):
every decoded value is `.aggregate variantIdx [.scalar sv]` with `0 < sv.bits < scalarModulus l.size.bytes`.
-/
theorem adt_newtype_nonZero_isTryFromBytes
    (layouts : LayoutTable) (defPath : DefPath) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx bitsWidth : Nat) (memoryOrder : List Nat) (signed : Bool)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hNoFieldLayouts : l.fieldLayouts = [])
    (hRepr :
      l.backendRepr =
        .scalar (.initialized (.int bitsWidth signed) ⟨1, scalarModulus l.size.bytes - 1⟩))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes) :
    IsTryFromBytes layouts { kind := .adt defPath [], layoutIdx := idx }
      (fun v =>
        ∃ sv : ScalarVal,
          v = .aggregate variantIdx [.scalar sv] ∧
          sv.sizeBytes = l.size.bytes ∧
          0 < sv.bits ∧
          sv.bits < scalarModulus l.size.bytes) := by
  have hPos : 0 < l.size.bytes := by
    cases h : l.size.bytes with
    | zero => rw [h] at hNz; nomatch hNz
    | succ k => exact Nat.succ_pos k
  rcases adt_newtype_scalarLayout_isTryFromBytes layouts defPath idx l variantIdx
    bitsWidth memoryOrder signed ⟨1, scalarModulus l.size.bytes - 1⟩
    hLookup hInhab hVar hFields hNoFieldLayouts hRepr hWidth with ⟨sz, hSz, hTry⟩
  refine ⟨sz, hSz, fun bs v hDec => ?_⟩
  rcases hTry bs v hDec with ⟨sv, rfl, hSvSz, _, hRange⟩
  have ⟨hGt, hLt⟩ := (wrappingRangeContains_nonZeroRange_iff hPos sv.bits).mp hRange
  exact ⟨sv, rfl, hSvSz, hGt, hLt⟩

/--
Every `NonZero*` single-field newtype layout (`FieldsShape.arbitrary [⟨0⟩] memoryOrder`,
`validRange = ⟨1, scalarModulus l.size.bytes - 1⟩`) rejects all-zero bytes (`¬ IsFromZeros`).
-/
theorem adt_newtype_nonZero_not_isFromZeros
    (layouts : LayoutTable) (defPath : DefPath) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx : Nat) (memoryOrder : List Nat) (pk : PrimitiveKind)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hNoFieldLayouts : l.fieldLayouts = [])
    (hRepr :
      l.backendRepr =
        .scalar (.initialized pk ⟨1, scalarModulus l.size.bytes - 1⟩))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth pk = some l.size.bytes) :
    ¬ IsFromZeros layouts { kind := .adt defPath [], layoutIdx := idx } := by
  have hPos : 0 < l.size.bytes := by
    cases h : l.size.bytes with
    | zero => rw [h] at hNz; nomatch hNz
    | succ k => exact Nat.succ_pos k
  exact adt_newtype_scalarLayout_not_isFromZeros layouts defPath idx l variantIdx
    memoryOrder pk ⟨1, scalarModulus l.size.bytes - 1⟩
    hLookup hInhab hVar hFields hNoFieldLayouts hRepr hNz hWidth
    (wrappingRangeContains_nonZeroRange_zero hPos)

/--
Unfolding lemma for `decodeValueFromBytes` on an inhabited multi-variant enum
`.adt defPath args` (`l.variants = .multiple tagLayout 0 variantShapes`,
`l.fields = .arbitrary [⟨0⟩] memoryOrder`, `scalarLayoutByteWidth tagLayout = some l.size.bytes`),
the layout shape of a fieldless multi-variant `#[repr(u8)]` / `#[repr(Int)]` enum
whose tag fills the whole value. The decoded tag value is used directly as the
variant index, which matches `rustc` only when the discriminants are the variant
indices (`adt_multiple_enum_explicit_discriminant_divergence`).
-/
theorem decodeValueFromBytes_adt_multiple_enum_scalarLayout
    (fuel : Nat) (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (tagLayout : ScalarLayout) (variantShapes : List FieldsShape)
    (memoryOrder : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .multiple tagLayout 0 variantShapes)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hWidth : scalarLayoutByteWidth tagLayout = some l.size.bytes)
    (bs : List AbstractByte) :
    decodeValueFromBytes (fuel + 1) layouts { kind := .adt defPath args, layoutIdx := idx } bs =
      match Nat.beq (length bs) l.size.bytes with
      | false => none
      | true =>
        match decodeScalarLayoutBytes tagLayout bs with
        | some (.scalar tagSc) =>
          match get? variantShapes tagSc.bits with
          | some (.arbitrary varOffsets _) =>
            match decodeFieldsBySpan bs l.size.bytes varOffsets with
            | some vals => some (.aggregate tagSc.bits vals)
            | none => none
          | _ => none
        | _ => none := by
  unfold decodeValueFromBytes
  dsimp only
  rw [hLookup]
  dsimp only
  rw [hInhab]
  cases hLen : Nat.beq (length bs) l.size.bytes
  · rfl
  · dsimp only [Bool.not, Bool.or]
    rw [hVar]
    dsimp only
    rw [hFields, hWidth]
    dsimp only
    have hGet0 : get? ([{ bytes := 0 }] : List Size) 0 = some { bytes := 0 } := rfl
    rw [hGet0]
    dsimp only
    have hBsLen : length bs = l.size.bytes := Nat.eq_of_beq_eq_true hLen
    rw [sliceAbstractBytes_zero_full bs l.size.bytes hBsLen]
    rfl

/--
Exact evaluation of `decodeValueFromBytes` on `encodeLittleEndianBytes bits l.size.bytes prov`
for a fieldless multi-variant `#[repr(Int)]` / `#[repr(u8)]` enum
(`l.variants = .multiple (.initialized (.int bitsWidth signed) validRange) 0 variantShapes`,
`l.fields = .arbitrary [⟨0⟩] memoryOrder`) where every valid tag in `validRange` maps to a
fieldless variant `.arbitrary [] _` in `variantShapes`.
-/
theorem adt_multiple_enum_scalarLayout_decode_encode_eq
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (bitsWidth : Nat) (signed : Bool) (validRange : WrappingRange)
    (variantShapes : List FieldsShape) (memoryOrder : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .multiple (.initialized (.int bitsWidth signed) validRange) 0 variantShapes)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes)
    (hFieldless :
      ∀ tag < scalarModulus l.size.bytes,
        wrappingRangeContains validRange tag = true →
        ∃ varMemOrder, get? variantShapes tag = some (.arbitrary [] varMemOrder))
    (bits : Nat) (prov : Option (Nat × Nat))
    (hBits : bits < scalarModulus l.size.bytes) :
    decodeValueFromBytes defaultCodecFuel layouts
        { kind := .adt defPath args, layoutIdx := idx }
        (encodeLittleEndianBytes bits l.size.bytes prov) =
      match wrappingRangeContains validRange bits with
      | true => some (.aggregate bits [])
      | false => none := by
  have hPos : 0 < l.size.bytes := by
    cases h : l.size.bytes with
    | zero => rw [h] at hNz; nomatch hNz
    | succ k => exact Nat.succ_pos k
  have hBeqLen :
      Nat.beq (length (encodeLittleEndianBytes bits l.size.bytes prov)) l.size.bytes = true := by
    rw [length_encodeLittleEndianBytes]
    exact Nat.beq_refl _
  rw [show defaultCodecFuel = 15 + 1 from rfl,
      decodeValueFromBytes_adt_multiple_enum_scalarLayout 15 layouts defPath args idx l
        (.initialized (.int bitsWidth signed) validRange) variantShapes memoryOrder
        hLookup hInhab hVar hFields hWidth,
      hBeqLen]
  dsimp only
  rw [decodeScalarLayoutBytes_initialized_int_eq bitsWidth signed validRange l.size.bytes _ hWidth,
      hBeqLen]
  dsimp only
  rw [decodeScalarBytes_encodeLittleEndianBytes_of_lt l.size.bytes bits prov false hPos hBits]
  dsimp only
  cases hW : wrappingRangeContains validRange bits
  · rfl
  · dsimp only
    rcases hFieldless bits hBits hW with ⟨varMemOrder, hGet⟩
    rw [hGet]

/--
A fieldless multi-variant `#[repr(Int)]` / `#[repr(u8)]` enum satisfies `IsFromZeros`
whenever `0` lies in `validRange` and variant `0` is fieldless (`.arbitrary [] _`).
-/
theorem adt_multiple_enum_scalarLayout_isFromZeros_of_zeroInRange
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (bitsWidth : Nat) (signed : Bool) (validRange : WrappingRange)
    (variantShapes : List FieldsShape) (memoryOrder varMemOrder0 : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .multiple (.initialized (.int bitsWidth signed) validRange) 0 variantShapes)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes)
    (hZeroValid : wrappingRangeContains validRange 0 = true)
    (hVar0 : get? variantShapes 0 = some (.arbitrary [] varMemOrder0)) :
    IsFromZeros layouts { kind := .adt defPath args, layoutIdx := idx } := by
  refine ⟨l.size.bytes, .aggregate 0 [], by simp [rigidTyByteSize, hLookup], ?_⟩
  have hBeqLen : Nat.beq (length (zeroInitBytes l.size.bytes)) l.size.bytes = true := by
    rw [length_zeroInitBytes]; exact Nat.beq_refl _
  rw [show defaultCodecFuel = 15 + 1 from rfl,
      decodeValueFromBytes_adt_multiple_enum_scalarLayout 15 layouts defPath args idx l
        (.initialized (.int bitsWidth signed) validRange) variantShapes memoryOrder
        hLookup hInhab hVar hFields hWidth,
      hBeqLen]
  dsimp only
  rw [decodeScalarLayoutBytes_initialized_int_eq bitsWidth signed validRange l.size.bytes
        (zeroInitBytes l.size.bytes) hWidth,
      hBeqLen]
  dsimp only
  rw [decodeScalarBytes_zeroInitBytes l.size.bytes false hNz]
  dsimp only
  rw [hZeroValid]
  dsimp only
  rw [hVar0]

/--
A multi-variant `#[repr(Int)]` / `#[repr(u8)]` enum does NOT satisfy `IsFromZeros`
whenever `wrappingRangeContains validRange 0 = false` (e.g., when discriminant `0` is uninhabited).
-/
theorem adt_multiple_enum_scalarLayout_not_isFromZeros
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (pk : PrimitiveKind) (validRange : WrappingRange)
    (variantShapes : List FieldsShape) (memoryOrder : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .multiple (.initialized pk validRange) 0 variantShapes)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth pk = some l.size.bytes)
    (hZeroInvalid : wrappingRangeContains validRange 0 = false) :
    ¬ IsFromZeros layouts { kind := .adt defPath args, layoutIdx := idx } := by
  rintro ⟨sz, v, hSz, hDec⟩
  simp [rigidTyByteSize, hLookup] at hSz
  subst hSz
  have hBeqLen : Nat.beq (length (zeroInitBytes l.size.bytes)) l.size.bytes = true := by
    rw [length_zeroInitBytes]; exact Nat.beq_refl _
  rw [show defaultCodecFuel = 15 + 1 from rfl,
      decodeValueFromBytes_adt_multiple_enum_scalarLayout 15 layouts defPath args idx l
        (.initialized pk validRange) variantShapes memoryOrder
        hLookup hInhab hVar hFields hWidth,
      hBeqLen] at hDec
  dsimp only at hDec
  unfold decodeScalarLayoutBytes scalarLayoutByteWidth at hDec
  dsimp only at hDec
  rw [hWidth] at hDec
  dsimp only at hDec
  rw [hBeqLen] at hDec
  dsimp only at hDec
  rw [decodeScalarBytes_zeroInitBytes l.size.bytes false hNz] at hDec
  dsimp only at hDec
  rw [hZeroInvalid] at hDec
  nomatch hDec

/--
`IsTryFromBytes` characterization for multi-variant `#[repr(Int)]` / `#[repr(u8)]` enums
(`l.variants = .multiple (.initialized (.int bitsWidth signed) validRange) 0 variantShapes`,
`l.fields = .arbitrary [⟨0⟩] memoryOrder`): every decoded value has the form
`.aggregate tag vals` where `tag < scalarModulus l.size.bytes` and
`wrappingRangeContains validRange tag = true` (and `vals = []` when all variants in `variantShapes`
are fieldless).
-/
theorem adt_multiple_enum_scalarLayout_isTryFromBytes
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (bitsWidth : Nat) (signed : Bool) (validRange : WrappingRange)
    (variantShapes : List FieldsShape) (memoryOrder : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .multiple (.initialized (.int bitsWidth signed) validRange) 0 variantShapes)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes) :
    IsTryFromBytes layouts { kind := .adt defPath args, layoutIdx := idx }
      (fun v =>
        ∃ (tag : Nat) (vals : List Value) (varOffsets : List Size) (varMemOrder : List Nat),
          v = .aggregate tag vals ∧
          tag < scalarModulus l.size.bytes ∧
          wrappingRangeContains validRange tag = true ∧
          get? variantShapes tag = some (.arbitrary varOffsets varMemOrder)) := by
  refine ⟨l.size.bytes, by simp [rigidTyByteSize, hLookup], ?_⟩
  intro bs v hDec
  rw [show defaultCodecFuel = 15 + 1 from rfl,
      decodeValueFromBytes_adt_multiple_enum_scalarLayout 15 layouts defPath args idx l
        (.initialized (.int bitsWidth signed) validRange) variantShapes memoryOrder
        hLookup hInhab hVar hFields hWidth] at hDec
  cases hLen : Nat.beq (length bs) l.size.bytes <;> rw [hLen] at hDec
  · nomatch hDec
  · dsimp only at hDec
    rw [decodeScalarLayoutBytes_initialized_int_eq bitsWidth signed validRange l.size.bytes bs hWidth,
        hLen] at hDec
    dsimp only at hDec
    cases hSc : decodeScalarBytes bs false <;> rw [hSc] at hDec
    · nomatch hDec
    case some pair =>
      rcases pair with ⟨sv, prov⟩
      dsimp only at hDec
      cases hRange : wrappingRangeContains validRange sv.bits <;> rw [hRange] at hDec
      · nomatch hDec
      · dsimp only at hDec
        cases hGet : get? variantShapes sv.bits <;> rw [hGet] at hDec
        · nomatch hDec
        case some varShape =>
          cases varShape with
          | arbitrary varOffsets varMemOrder =>
            dsimp only at hDec
            cases hSpan : decodeFieldsBySpan bs l.size.bytes varOffsets <;> rw [hSpan] at hDec
            · nomatch hDec
            case some vals =>
              injection hDec with hV
              have hBsLen : length bs = l.size.bytes := Nat.eq_of_beq_eq_true hLen
              have ⟨_, hSvLt⟩ := decodeScalarBytes_bits_lt bs false sv prov hSc
              rw [hBsLen] at hSvLt
              exact ⟨sv.bits, vals, varOffsets, varMemOrder, hV.symm, hSvLt, hRange, hGet⟩
          | _ => nomatch hDec

/--
A multi-variant fieldless enum (`VariantsShape.multiple tagLayout 0 variantShapes`,
`l.fields = .arbitrary [⟨0⟩] memoryOrder`, `scalarLayoutByteWidth tagLayout = some l.size.bytes`,
where every variant in `variantShapes` has empty field offsets `.arbitrary [] _`)
satisfies `IsIntoBytes`: every valid variant encoding writes its `l.size.bytes`-byte
discriminant tag at offset `0` with no uninitialized padding bytes.
-/
theorem adt_multiple_enum_fieldless_isIntoBytes
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (tagLayout : ScalarLayout)
    (variantShapes : List FieldsShape) (memoryOrder : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .multiple tagLayout 0 variantShapes)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hWidth : scalarLayoutByteWidth tagLayout = some l.size.bytes)
    (hFieldless :
      ∀ (varIdx : Nat) (varOffsets : List Size) (varMemOrder : List Nat),
        get? variantShapes varIdx = some (.arbitrary varOffsets varMemOrder) →
        varOffsets = []) :
    IsIntoBytes layouts { kind := .adt defPath args, layoutIdx := idx } := by
  refine ⟨l.size.bytes, by simp [rigidTyByteSize, hLookup], ?_⟩
  intro v bs hEnc
  unfold defaultCodecFuel encodeValueToBytes at hEnc
  dsimp only at hEnc
  rw [hLookup] at hEnc
  dsimp only at hEnc
  rw [hInhab, hVar] at hEnc
  dsimp only at hEnc
  cases v with
  | aggregate varIdx fieldVals =>
    dsimp only at hEnc
    rw [hFields, hWidth] at hEnc
    cases hGet : get? variantShapes varIdx <;> rw [hGet] at hEnc
    · nomatch hEnc
    case some varShape =>
      cases varShape with
      | arbitrary varOffsets varMemOrder =>
        have hNil := hFieldless varIdx varOffsets varMemOrder hGet
        subst hNil
        dsimp only at hEnc
        have hGet0 : get? ([{ bytes := 0 }] : List Size) 0 = some { bytes := 0 } := rfl
        rw [hGet0] at hEnc
        dsimp only at hEnc
        cases hTagEnc : encodeScalarBytes ⟨varIdx, l.size.bytes⟩ none <;> rw [hTagEnc] at hEnc
        · nomatch hEnc
        case some tagBytes =>
          dsimp only at hEnc
          have ⟨hTagLen, hTagInit⟩ :=
            encodeScalarBytes_length_and_init ⟨varIdx, l.size.bytes⟩ none tagBytes hTagEnc
          dsimp only at hTagLen
          have hWrite :
              writeAbstractBytesAt (replicateUninitBytes l.size.bytes) 0 tagBytes =
                some tagBytes := by
            rw [replicateUninitBytes_eq_replicate]
            have hRep :
                List.replicate l.size.bytes AbstractByte.uninit =
                  ([] : List AbstractByte) ++ List.replicate (tagBytes.length + 0) .uninit := by
              change List.replicate l.size.bytes AbstractByte.uninit =
                List.replicate (length tagBytes) AbstractByte.uninit
              rw [hTagLen]
            rw [hRep]
            simpa using writeAbstractBytesAt_append_replicate [] tagBytes 0
          rw [hWrite] at hEnc
          dsimp only at hEnc
          cases fieldVals with
          | nil =>
            injection hEnc with hBs
            subst hBs
            exact ⟨hTagLen, hTagInit⟩
          | cons _ _ => nomatch hEnc
      | _ => nomatch hEnc
  | _ => nomatch hEnc

/--
**Divergence (generic `NonZero<T>` niche on the type-argument decoding path).**
For a single-variant `.adt defPath args` whose `FieldsShape.arbitrary` offsets
have the same length as `args`, `decodeValueFromBytes` decodes each field at the
corresponding *type argument* and never reads `l.backendRepr`. Take a
`NonZero<u32>`-shaped layout: one field at offset `0`, `4` bytes, and backend
representation `ScalarLayout.initialized (.int 32 false) ⟨1, 2^32 - 1⟩`. Carried
by the monomorphized type `.adt defPath [.uint .u32]`, it accepts the all-zero
candidate even though the recorded niche excludes `0`. So `Trusted` does not
enforce the `NonZero*` niche on this path, and the type satisfies `IsFromZeros`,
whereas in Rust all-zero bytes are not a valid `NonZero<u32>`. The
niche-enforcing `.primitive` and `adt_newtype_*` theorems apply only when
decoding reaches the backend scalar path.
-/
theorem adt_generic_nonZero_typeArg_path_niche_unenforced
    (layouts : LayoutTable) (defPath : DefPath) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx : Nat) (memoryOrder : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hSz : l.size.bytes = 4)
    (_hRepr : l.backendRepr = .scalar (.initialized (.int 32 false) ⟨1, scalarModulus 4 - 1⟩)) :
    wrappingRangeContains ⟨1, scalarModulus 4 - 1⟩ 0 = false ∧
    decodeValueFromBytes defaultCodecFuel layouts
        { kind := .adt defPath [.uint .u32], layoutIdx := idx } (zeroInitBytes 4) =
      some (.aggregate variantIdx [.scalar ⟨0, 4⟩]) ∧
    IsFromZeros layouts { kind := .adt defPath [.uint .u32], layoutIdx := idx } := by
  have hDec : decodeValueFromBytes defaultCodecFuel layouts
      { kind := .adt defPath [.uint .u32], layoutIdx := idx } (zeroInitBytes 4) =
      some (.aggregate variantIdx [.scalar ⟨0, 4⟩]) := by
    rcases l with ⟨⟨sb⟩, lAlign, lRepr, lFields, lVariants, lUninhabited, lFieldLayouts⟩
    dsimp only at hInhab hVar hFields hSz
    subst hInhab hVar hFields hSz
    rw [show defaultCodecFuel = 15 + 1 from rfl]
    unfold decodeValueFromBytes
    dsimp only
    rw [hLookup]
    rfl
  have hSize : rigidTyByteSize layouts { kind := .adt defPath [.uint .u32], layoutIdx := idx } =
      some 4 := by
    simp [rigidTyByteSize, hLookup, hSz]
  exact ⟨rfl, hDec, ⟨4, _, hSize, hDec⟩⟩

/--
**Divergence (explicit enum discriminants).** The `.multiple` codec identifies
the tag value with the variant index: `decodeValueFromBytes` looks up
`get? variantShapes tag`, and `encodeValueToBytes` writes the variant index as
the tag. For a fieldless `#[repr(u8)] enum E { A = 1, B = 2 }`-shaped layout
(`validRange = ⟨1, 2⟩`, two fieldless variants):
1. the valid discriminant `2` is inside `validRange` but is rejected;
2. the discriminant `1` (which is `E::A` in Rust) decodes to variant index `1`
   (`E::B`);
3. encoding `E::A` (`.aggregate 0 []`) writes the byte `0`, which lies outside
   `validRange`, and the same layout rejects it when decoding.
Theorems over `.multiple` enum layouts are therefore faithful to `rustc` only
when the discriminants are the variant indices `0..n-1`.
-/
theorem adt_multiple_enum_explicit_discriminant_divergence
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (memoryOrder vm0 vm1 : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants =
      .multiple (.initialized (.int 8 false) ⟨1, 2⟩) 0 [.arbitrary [] vm0, .arbitrary [] vm1])
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hSz : l.size.bytes = 1) :
    let enumTy : Ty := { kind := .adt defPath args, layoutIdx := idx }
    wrappingRangeContains ⟨1, 2⟩ 2 = true ∧
    decodeValueFromBytes defaultCodecFuel layouts enumTy (encodeLittleEndianBytes 2 1 none) = none ∧
    decodeValueFromBytes defaultCodecFuel layouts enumTy (encodeLittleEndianBytes 1 1 none) =
      some (.aggregate 1 []) ∧
    encodeValueToBytes defaultCodecFuel layouts enumTy (.aggregate 0 []) =
      some (encodeLittleEndianBytes 0 1 none) ∧
    decodeValueFromBytes defaultCodecFuel layouts enumTy (encodeLittleEndianBytes 0 1 none) =
      none := by
  intro enumTy
  rcases l with ⟨⟨sb⟩, lAlign, lRepr, lFields, lVariants, lUninhabited, lFieldLayouts⟩
  dsimp only at hInhab hVar hFields hSz
  subst hInhab hVar hFields hSz
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · rw [show defaultCodecFuel = 15 + 1 from rfl]
    unfold decodeValueFromBytes
    dsimp only [enumTy]
    rw [hLookup]
    rfl
  · rw [show defaultCodecFuel = 15 + 1 from rfl]
    unfold decodeValueFromBytes
    dsimp only [enumTy]
    rw [hLookup]
    rfl
  · rw [show defaultCodecFuel = 15 + 1 from rfl]
    unfold encodeValueToBytes
    dsimp only [enumTy]
    rw [hLookup]
    rfl
  · rw [show defaultCodecFuel = 15 + 1 from rfl]
    unfold decodeValueFromBytes
    dsimp only [enumTy]
    rw [hLookup]
    rfl

/--
**Positive round-trip theorem for `0..n-1` multi-variant fieldless `#[repr(Int)]` / `#[repr(u8)]` enums.**
When variant index `varIdx < scalarModulus l.size.bytes` lies in `validRange` and maps to a fieldless
variant `.arbitrary [] varMemOrder` in `variantShapes`:
1. `encodeValueToBytes` on `.aggregate varIdx []` produces `some (encodeLittleEndianBytes varIdx l.size.bytes none)`.
2. `decodeValueFromBytes` on those encoded bytes recovers `some (.aggregate varIdx [])`.
-/
theorem adt_multiple_enum_encode_decode_roundtrip
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (bitsWidth varIdx : Nat) (signed : Bool) (validRange : WrappingRange)
    (variantShapes : List FieldsShape) (memoryOrder varMemOrder : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .multiple (.initialized (.int bitsWidth signed) validRange) 0 variantShapes)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes)
    (hVarLt : varIdx < scalarModulus l.size.bytes)
    (hInRange : wrappingRangeContains validRange varIdx = true)
    (hGetVar : get? variantShapes varIdx = some (.arbitrary [] varMemOrder)) :
    let enumTy : Ty := { kind := .adt defPath args, layoutIdx := idx }
    let tagBytes := encodeLittleEndianBytes varIdx l.size.bytes none
    encodeValueToBytes defaultCodecFuel layouts enumTy (.aggregate varIdx []) = some tagBytes ∧
    decodeValueFromBytes defaultCodecFuel layouts enumTy tagBytes =
      some (.aggregate varIdx []) := by
  intro enumTy tagBytes
  have hPos : 0 < l.size.bytes := by
    cases h : l.size.bytes with
    | zero => rw [h] at hNz; nomatch hNz
    | succ k => exact Nat.succ_pos k
  have hEnc :
      encodeValueToBytes defaultCodecFuel layouts enumTy (.aggregate varIdx []) = some tagBytes := by
    unfold defaultCodecFuel encodeValueToBytes
    dsimp only [enumTy]
    rw [hLookup]
    dsimp only
    rw [hInhab, hVar]
    dsimp only
    rw [hFields, show scalarLayoutByteWidth (.initialized (.int bitsWidth signed) validRange) =
      some l.size.bytes from hWidth, hGetVar]
    dsimp only
    have hGet0 : get? ([{ bytes := 0 }] : List Size) 0 = some { bytes := 0 } := rfl
    rw [hGet0]
    dsimp only
    unfold encodeScalarBytes
    dsimp only
    rw [hNz]
    dsimp only
    have hWrite :
        writeAbstractBytesAt (replicateUninitBytes l.size.bytes) 0 tagBytes = some tagBytes := by
      rw [replicateUninitBytes_eq_replicate]
      have hTagLen : length tagBytes = l.size.bytes :=
        length_encodeLittleEndianBytes none l.size.bytes varIdx
      have hRep :
          List.replicate l.size.bytes AbstractByte.uninit =
            ([] : List AbstractByte) ++ List.replicate (tagBytes.length + 0) .uninit := by
        change List.replicate l.size.bytes AbstractByte.uninit =
          List.replicate (length tagBytes) AbstractByte.uninit
        rw [hTagLen]
      rw [hRep]
      simpa using writeAbstractBytesAt_append_replicate [] tagBytes 0
    rw [hWrite]
  have hDec :
      decodeValueFromBytes defaultCodecFuel layouts enumTy tagBytes =
        some (.aggregate varIdx []) := by
    have hBeqLen : Nat.beq (length tagBytes) l.size.bytes = true := by
      unfold tagBytes
      rw [length_encodeLittleEndianBytes]
      exact Nat.beq_refl _
    rw [show defaultCodecFuel = 15 + 1 from rfl,
        decodeValueFromBytes_adt_multiple_enum_scalarLayout 15 layouts defPath args idx l
          (.initialized (.int bitsWidth signed) validRange) variantShapes memoryOrder
          hLookup hInhab hVar hFields hWidth,
        hBeqLen]
    dsimp only
    rw [decodeScalarLayoutBytes_initialized_int_eq bitsWidth signed validRange l.size.bytes _ hWidth,
        hBeqLen]
    dsimp only
    unfold tagBytes
    rw [decodeScalarBytes_encodeLittleEndianBytes_of_lt l.size.bytes varIdx none false hPos hVarLt]
    dsimp only
    rw [hInRange]
    dsimp only
    rw [hGetVar]
  exact ⟨hEnc, hDec⟩

/--
**Positive `l.fieldLayouts` niche-enforcement theorem.**
Conversely, because `decodeFieldsByLayoutIdxs` invokes `decodeValueFromBytes` at `{ kind := .adt "" [], layoutIdx := fIdx }`
with **empty** type arguments `[]`, whenever a single-field `.adt defPath args` (with `args.length ≠ 1`,
in particular `args = []`) has `l.fields = .arbitrary [⟨0⟩] memoryOrder` and `l.fieldLayouts = [fIdx]`
where the field layout `fl` at `fIdx` enforces a `ScalarLayout.initialized (.int bitsWidth signed) validRange`
niche on the `.primitive` path (`fl.fields = .primitive`), `decodeValueFromBytes` on the outer ADT
enforces `validRange` on `encodeLittleEndianBytes bits l.size.bytes prov`.
-/
theorem adt_fieldLayout_path_inner_primitive_scalarLayout_decode_encode_eq
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx fIdx : LayoutIdx)
    (l fl : TypeLayout) (variantIdx innerVarIdx bitsWidth : Nat) (memoryOrder : List Nat)
    (signed : Bool) (validRange : WrappingRange)
    (hArgsNe1 : Nat.beq (length args) 1 = false)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hFieldLayouts : l.fieldLayouts = [fIdx])
    (hFLookup : LayoutTable.lookup layouts fIdx = some fl)
    (hFInhab : fl.isUninhabited = false)
    (hFVar : fl.variants = .single innerVarIdx)
    (hFFields : fl.fields = .primitive)
    (hFSz : fl.size.bytes = l.size.bytes)
    (hFRepr : fl.backendRepr = .scalar (.initialized (.int bitsWidth signed) validRange))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes)
    (bits : Nat) (prov : Option (Nat × Nat))
    (hBits : bits < scalarModulus l.size.bytes) :
    decodeValueFromBytes defaultCodecFuel layouts
        { kind := .adt defPath args, layoutIdx := idx }
        (encodeLittleEndianBytes bits l.size.bytes prov) =
      match wrappingRangeContains validRange bits with
      | true => some (.aggregate variantIdx [.scalar ⟨bits, l.size.bytes⟩])
      | false => none := by
  have hPos : 0 < l.size.bytes := by
    cases h : l.size.bytes with
    | zero => rw [h] at hNz; nomatch hNz
    | succ k => exact Nat.succ_pos k
  let bs := encodeLittleEndianBytes bits l.size.bytes prov
  have hBsLen : length bs = l.size.bytes :=
    length_encodeLittleEndianBytes prov l.size.bytes bits
  have hBeqLen : Nat.beq (length bs) l.size.bytes = true := by
    rw [hBsLen]; exact Nat.beq_refl _
  have hFNz : Nat.beq fl.size.bytes 0 = false := hFSz.symm ▸ hNz
  have hFWidth : primitiveKindByteWidth (.int bitsWidth signed) = some fl.size.bytes :=
    hFSz.symm ▸ hWidth
  have hInnerDec :
      decodeValueFromBytes 15 layouts { kind := .adt "" [], layoutIdx := fIdx } bs =
        match wrappingRangeContains validRange bits with
        | true => some (.scalar ⟨bits, l.size.bytes⟩)
        | false => none := by
    rw [decodeValueFromBytes_adt_primitive_scalarLayout 14 layouts "" [] fIdx fl innerVarIdx
          (.initialized (.int bitsWidth signed) validRange)
          hFLookup hFInhab hFVar hFFields hFRepr hFNz hFWidth,
        decodeScalarLayoutBytes_initialized_int_eq bitsWidth signed validRange fl.size.bytes bs hFWidth,
        hFSz, hBeqLen]
    dsimp only
    rw [decodeScalarBytes_encodeLittleEndianBytes_of_lt l.size.bytes bits prov false hPos hBits]
    dsimp only
    cases wrappingRangeContains validRange bits <;> rfl
  rw [show defaultCodecFuel = 15 + 1 from rfl]
  unfold decodeValueFromBytes
  dsimp only
  rw [hLookup]
  dsimp only
  rw [hInhab, hBeqLen]
  dsimp only [Bool.not, Bool.or]
  rw [hVar, hFields, hFieldLayouts]
  dsimp only
  have hArgsBeq : Nat.beq (length args) (length ([{ bytes := 0 }] : List Size)) = false := hArgsNe1
  have hFlBeq : Nat.beq (length ([fIdx] : List Nat)) (length ([{ bytes := 0 }] : List Size)) = true := rfl
  rw [hArgsBeq, hFlBeq]
  dsimp only [decodeFieldsByLayoutIdxs]
  rw [hFLookup]
  dsimp only
  rw [hFSz, sliceAbstractBytes_zero_full bs l.size.bytes hBsLen]
  dsimp only
  rw [hInnerDec]
  cases wrappingRangeContains validRange bits <;> rfl

/--
**Divergence (`l.fieldLayouts` decoding path vs. outer `l.backendRepr` scalar niche).**
When a single-variant single-field `.adt defPath []` has `l.fields = .arbitrary [⟨0⟩] memoryOrder`
and `l.fieldLayouts = [fIdx]`, `decodeValueFromBytes` takes the `hasFieldLayouts` branch
(`decodeFieldsByLayoutIdxs`) and never inspects the outer layout's `l.backendRepr`. Consequently,
if the outer layout `l` records a `NonZero` niche `⟨1, scalarModulus 4 - 1⟩` in `l.backendRepr`
(as `#[rustc_layout_scalar_valid_range_start(1)]` does on the wrapper struct) while the inner
field layout `fl` at `fIdx` is an unconstrained 4-byte scalar layout `⟨0, scalarModulus 4 - 1⟩`,
`decodeValueFromBytes` accepts `zeroInitBytes 4` and the outer ADT satisfies `IsFromZeros` even
when `args = []`.
-/
theorem adt_fieldLayout_path_outer_niche_unenforced
    (layouts : LayoutTable) (defPath : DefPath) (idx fIdx : LayoutIdx)
    (l fl : TypeLayout) (variantIdx innerVarIdx : Nat) (memoryOrder : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hFieldLayouts : l.fieldLayouts = [fIdx])
    (hSz : l.size.bytes = 4)
    (_hOuterRepr :
      l.backendRepr = .scalar (.initialized (.int 32 false) ⟨1, scalarModulus 4 - 1⟩))
    (hFLookup : LayoutTable.lookup layouts fIdx = some fl)
    (hFInhab : fl.isUninhabited = false)
    (hFVar : fl.variants = .single innerVarIdx)
    (hFFields : fl.fields = .primitive)
    (hFSz : fl.size.bytes = 4)
    (hFRepr :
      fl.backendRepr = .scalar (.initialized (.int 32 false) ⟨0, scalarModulus 4 - 1⟩)) :
    wrappingRangeContains ⟨1, scalarModulus 4 - 1⟩ 0 = false ∧
    decodeValueFromBytes defaultCodecFuel layouts
        { kind := .adt defPath [], layoutIdx := idx } (zeroInitBytes 4) =
      some (.aggregate variantIdx [.scalar ⟨0, 4⟩]) ∧
    IsFromZeros layouts { kind := .adt defPath [], layoutIdx := idx } := by
  have hDec :
      decodeValueFromBytes defaultCodecFuel layouts
          { kind := .adt defPath [], layoutIdx := idx } (zeroInitBytes 4) =
        some (.aggregate variantIdx [.scalar ⟨0, 4⟩]) := by
    have hEq := adt_fieldLayout_path_inner_primitive_scalarLayout_decode_encode_eq
      layouts defPath [] idx fIdx l fl variantIdx innerVarIdx 32 memoryOrder false
      ⟨0, scalarModulus 4 - 1⟩ rfl hLookup hInhab hVar hFields hFieldLayouts
      hFLookup hFInhab hFVar hFFields (by omega) hFRepr (by rw [hSz]; rfl) (by rw [hSz])
      0 none (by rw [hSz]; decide)
    rw [hSz] at hEq
    exact hEq
  have hSize : rigidTyByteSize layouts { kind := .adt defPath [], layoutIdx := idx } = some 4 := by
    simp [rigidTyByteSize, hLookup, hSz]
  exact ⟨rfl, hDec, ⟨4, _, hSize, hDec⟩⟩

/--
Every inhabited single-variant `.primitive` ADT (`l.variants = .single variantIdx`,
`l.fields = .primitive`) satisfies `IsIntoBytes`: its encoder only accepts `.scalar sv`
with `sv.sizeBytes = l.size.bytes` and emits `l.size.bytes` initialized bytes via
`encodeScalarBytes`. In particular, `.primitive` `NonZero*` and `#[repr(Int)]` enum
layouts satisfy `IsIntoBytes` and can serve as the source of safe `IntoBytes -> FromBytes`
transmutes (e.g., `NonZeroU32 -> u32`, `#[repr(u8)] Enum -> u8`).
-/
theorem adt_primitive_isIntoBytes
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (variantIdx : Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .primitive) :
    IsIntoBytes layouts { kind := .adt defPath args, layoutIdx := idx } := by
  refine ⟨l.size.bytes, by simp [rigidTyByteSize, hLookup], ?_⟩
  intro v bs hEnc
  unfold defaultCodecFuel encodeValueToBytes at hEnc
  dsimp only at hEnc
  rw [hLookup] at hEnc
  dsimp only at hEnc
  rw [hInhab, hVar] at hEnc
  dsimp only at hEnc
  cases v with
  | scalar sv =>
    rw [hFields] at hEnc
    dsimp only at hEnc
    cases hEq : Nat.beq sv.sizeBytes l.size.bytes <;> rw [hEq] at hEnc
    · nomatch hEnc
    · have hSvSz : sv.sizeBytes = l.size.bytes := Nat.eq_of_beq_eq_true hEq
      have ⟨hLen, hInit⟩ := encodeScalarBytes_length_and_init sv none bs hEnc
      exact ⟨hSvSz ▸ hLen, hInit⟩
  | unit | ptr _ _ | aggregate _ _ =>
    rw [hFields] at hEnc
    nomatch hEnc

/--
`IsTryFromBytes` on the `l.fieldLayouts = [fIdx]` wrapper path when the inner field layout
`fl` at `fIdx` is a `.primitive` scalar-niche layout (`ScalarLayout.initialized (.int bitsWidth signed) validRange`):
every decoded value has the form `.aggregate variantIdx [.scalar sv]` with
`sv.sizeBytes = l.size.bytes`, `sv.bits < scalarModulus l.size.bytes`, and
`wrappingRangeContains validRange sv.bits = true`.
-/
theorem adt_fieldLayout_path_inner_primitive_isTryFromBytes
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx fIdx : LayoutIdx)
    (l fl : TypeLayout) (variantIdx innerVarIdx bitsWidth : Nat) (memoryOrder : List Nat)
    (signed : Bool) (validRange : WrappingRange)
    (hArgsNe1 : Nat.beq (length args) 1 = false)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hFieldLayouts : l.fieldLayouts = [fIdx])
    (hFLookup : LayoutTable.lookup layouts fIdx = some fl)
    (hFInhab : fl.isUninhabited = false)
    (hFVar : fl.variants = .single innerVarIdx)
    (hFFields : fl.fields = .primitive)
    (hFSz : fl.size.bytes = l.size.bytes)
    (hFRepr : fl.backendRepr = .scalar (.initialized (.int bitsWidth signed) validRange))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes) :
    IsTryFromBytes layouts { kind := .adt defPath args, layoutIdx := idx }
      (fun v =>
        ∃ sv : ScalarVal,
          v = .aggregate variantIdx [.scalar sv] ∧
          sv.sizeBytes = l.size.bytes ∧
          sv.bits < scalarModulus l.size.bytes ∧
          wrappingRangeContains validRange sv.bits = true) := by
  refine ⟨l.size.bytes, by simp [rigidTyByteSize, hLookup], ?_⟩
  intro bs v hDec
  rw [show defaultCodecFuel = 15 + 1 from rfl] at hDec
  unfold decodeValueFromBytes at hDec
  dsimp only at hDec
  rw [hLookup] at hDec
  dsimp only at hDec
  rw [hInhab] at hDec
  cases hLen : Nat.beq (length bs) l.size.bytes <;> rw [hLen] at hDec
  · nomatch hDec
  · dsimp only [Bool.not, Bool.or] at hDec
    rw [hVar, hFields, hFieldLayouts] at hDec
    dsimp only at hDec
    have hArgsBeq : Nat.beq (length args) (length ([{ bytes := 0 }] : List Size)) = false := hArgsNe1
    have hFlBeq : Nat.beq (length ([fIdx] : List Nat)) (length ([{ bytes := 0 }] : List Size)) = true := rfl
    rw [hArgsBeq, hFlBeq] at hDec
    dsimp only [decodeFieldsByLayoutIdxs] at hDec
    rw [hFLookup] at hDec
    dsimp only at hDec
    have hBsLen : length bs = l.size.bytes := Nat.eq_of_beq_eq_true hLen
    rw [hFSz, sliceAbstractBytes_zero_full bs l.size.bytes hBsLen] at hDec
    dsimp only at hDec
    have hFNz : Nat.beq fl.size.bytes 0 = false := hFSz.symm ▸ hNz
    have hFWidth : primitiveKindByteWidth (.int bitsWidth signed) = some fl.size.bytes :=
      hFSz.symm ▸ hWidth
    rw [decodeValueFromBytes_adt_primitive_scalarLayout 14 layouts "" [] fIdx fl innerVarIdx
          (.initialized (.int bitsWidth signed) validRange)
          hFLookup hFInhab hFVar hFFields hFRepr hFNz hFWidth,
        decodeScalarLayoutBytes_initialized_int_eq bitsWidth signed validRange fl.size.bytes bs hFWidth,
        hFSz, hLen] at hDec
    dsimp only at hDec
    cases hSc : decodeScalarBytes bs false <;> rw [hSc] at hDec
    · nomatch hDec
    case some pair =>
      rcases pair with ⟨sv, prov⟩
      dsimp only at hDec
      cases hRange : wrappingRangeContains validRange sv.bits <;> rw [hRange] at hDec
      · nomatch hDec
      · dsimp only at hDec
        injection hDec with hV
        have ⟨hSvSz, hSvLt⟩ := decodeScalarBytes_bits_lt bs false sv prov hSc
        rw [hBsLen] at hSvSz hSvLt
        exact ⟨sv, hV.symm, hSvSz, hSvLt, hRange⟩

/--
On the `l.fieldLayouts = [fIdx]` wrapper path, if the inner `.primitive` field layout `fl`
excludes `0` from `validRange` (`wrappingRangeContains validRange 0 = false`, e.g. `NonZero*`),
then the outer ADT rejects all-zero bytes (`¬ IsFromZeros`).
-/
theorem adt_fieldLayout_path_inner_primitive_not_isFromZeros
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx fIdx : LayoutIdx)
    (l fl : TypeLayout) (variantIdx innerVarIdx bitsWidth : Nat) (memoryOrder : List Nat)
    (signed : Bool) (validRange : WrappingRange)
    (hArgsNe1 : Nat.beq (length args) 1 = false)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single variantIdx)
    (hFields : l.fields = .arbitrary [⟨0⟩] memoryOrder)
    (hFieldLayouts : l.fieldLayouts = [fIdx])
    (hFLookup : LayoutTable.lookup layouts fIdx = some fl)
    (hFInhab : fl.isUninhabited = false)
    (hFVar : fl.variants = .single innerVarIdx)
    (hFFields : fl.fields = .primitive)
    (hFSz : fl.size.bytes = l.size.bytes)
    (hFRepr : fl.backendRepr = .scalar (.initialized (.int bitsWidth signed) validRange))
    (hNz : Nat.beq l.size.bytes 0 = false)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some l.size.bytes)
    (hZeroInvalid : wrappingRangeContains validRange 0 = false) :
    ¬ IsFromZeros layouts { kind := .adt defPath args, layoutIdx := idx } := by
  rintro ⟨sz, v, hSz, hDec⟩
  simp [rigidTyByteSize, hLookup] at hSz
  subst hSz
  have hTry := adt_fieldLayout_path_inner_primitive_isTryFromBytes
    layouts defPath args idx fIdx l fl variantIdx innerVarIdx bitsWidth memoryOrder signed
    validRange hArgsNe1 hLookup hInhab hVar hFields hFieldLayouts hFLookup hFInhab hFVar
    hFFields hFSz hFRepr hNz hWidth
  rcases hTry with ⟨_, _, hPred⟩
  rcases hPred (zeroInitBytes l.size.bytes) v hDec with ⟨sv, _, _, _, hRange⟩
  rw [show defaultCodecFuel = 15 + 1 from rfl] at hDec
  unfold decodeValueFromBytes at hDec
  dsimp only at hDec
  rw [hLookup] at hDec
  dsimp only at hDec
  have hBeqLen : Nat.beq (length (zeroInitBytes l.size.bytes)) l.size.bytes = true := by
    rw [length_zeroInitBytes]; exact Nat.beq_refl _
  rw [hInhab, hBeqLen] at hDec
  dsimp only [Bool.not, Bool.or] at hDec
  rw [hVar, hFields, hFieldLayouts] at hDec
  dsimp only at hDec
  have hArgsBeq : Nat.beq (length args) (length ([{ bytes := 0 }] : List Size)) = false := hArgsNe1
  have hFlBeq : Nat.beq (length ([fIdx] : List Nat)) (length ([{ bytes := 0 }] : List Size)) = true := rfl
  rw [hArgsBeq, hFlBeq] at hDec
  dsimp only [decodeFieldsByLayoutIdxs] at hDec
  rw [hFLookup] at hDec
  dsimp only at hDec
  rw [hFSz, sliceAbstractBytes_zero_full (zeroInitBytes l.size.bytes) l.size.bytes
        (length_zeroInitBytes l.size.bytes)] at hDec
  dsimp only at hDec
  have hFNz : Nat.beq fl.size.bytes 0 = false := hFSz.symm ▸ hNz
  have hFWidth : primitiveKindByteWidth (.int bitsWidth signed) = some fl.size.bytes :=
    hFSz.symm ▸ hWidth
  rw [decodeValueFromBytes_adt_primitive_scalarLayout 14 layouts "" [] fIdx fl innerVarIdx
        (.initialized (.int bitsWidth signed) validRange)
        hFLookup hFInhab hFVar hFFields hFRepr hFNz hFWidth,
      decodeScalarLayoutBytes_initialized_int_eq bitsWidth signed validRange fl.size.bytes
        (zeroInitBytes l.size.bytes) hFWidth,
      hFSz, hBeqLen] at hDec
  dsimp only at hDec
  rw [decodeScalarBytes_zeroInitBytes l.size.bytes false hNz] at hDec
  dsimp only at hDec
  rw [hZeroInvalid] at hDec
  nomatch hDec

end Anneal.BitValidity
