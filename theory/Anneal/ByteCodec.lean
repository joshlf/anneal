-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted
import Anneal.Scalars
import Anneal.BitValidity

namespace Anneal.ByteCodec

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.BitValidity

/-!
Composable prefix-free fixed-width `AbstractByte` codecs (`FixedByteCodec`),
bridges to `Anneal.BitValidity` marker traits (`IsTryFromBytes`, `IsFromZeros`,
`IsFromBytes`, `IsIntoBytes`, `ByteSeqValid`, `transmute_sound`), structural
`sizeOf` descent lemmas for fuel-free recursion over `RigidTy` and `Value`, and
kernel-reducing pattern-matched `RigidTy` classification predicates.

Key design invariants:
1. Every `c : FixedByteCodec α n` encodes values to an exact `n`-byte list and
   satisfies the prefix-free round-trip law `decode ((encode x ++ rest).take n) = some x`,
   so contiguous products, padded structs, and homogeneous arrays compose in O(1)
   via `take`/`drop` and `sliceAbstractBytes`.
2. Built-in combinators enforce exact byte width (`IsExactWidth`), rejecting both
   truncated buffers and trailing bytes (even for zero-sized codecs `n = 0`).
3. Padding combinators (`padUninit`, `padLeft`, `padRight`) emit `.uninit` bytes on
   `encode` while accepting arbitrary `padBytes`-length slices on `decode`,
   faithfully capturing why padded Rust structs can satisfy `FromZeros`/`FromBytes`
   while failing `IntoBytes` when `0 < padBytes`.
-/

/-! ## 1. Core Prefix-Free Fixed-Width Byte Codec (`FixedByteCodec`) -/

/--
A prefix-free fixed-width codec between values of type `α` and `n`-byte
`AbstractByte` sequences.
-/
structure FixedByteCodec (α : Type) (n : Nat) : Type where
  /-- Serialize `x` into an `n`-byte sequence. -/
  encode : α → List AbstractByte
  /-- Attempt to deserialize an `α` from `bs`. -/
  decode : List AbstractByte → Option α
  /-- Every encoded value has exact byte length `n`. -/
  encode_length : ∀ x : α, (encode x).length = n
  /-- Exact round-trip on `encode x`. -/
  decode_encode : ∀ x : α, decode (encode x) = some x
  /-- Prefix-free round-trip: trailing bytes after the `n`-byte prefix are ignored by `take n`. -/
  decode_take_append :
    ∀ (x : α) (rest : List AbstractByte), decode ((encode x ++ rest).take n) = some x

namespace FixedByteCodec

/--
Construct a `FixedByteCodec α n` from `encode`, `decode`, `encode_length`, and
`decode_encode`, automatically deriving `decode_take_append` via `List.take_left'`.
-/
def ofRoundTrip {α : Type} {n : Nat}
    (encode : α → List AbstractByte)
    (decode : List AbstractByte → Option α)
    (encode_length : ∀ x : α, (encode x).length = n)
    (decode_encode : ∀ x : α, decode (encode x) = some x) :
    FixedByteCodec α n where
  encode := encode
  decode := decode
  encode_length := encode_length
  decode_encode := decode_encode
  decode_take_append := fun x rest => by
    rw [List.take_left' (encode_length x)]
    exact decode_encode x

/-- Encoding is injective for every `FixedByteCodec`. -/
theorem encode_injective {α : Type} {n : Nat} (c : FixedByteCodec α n)
    {x y : α} (h : c.encode x = c.encode y) : x = y := by
  have hx := c.decode_encode x
  rw [h, c.decode_encode y] at hx
  exact Option.some.inj hx.symm

/-- Slicing at offset `pre.length` for width `n` recovers `c.encode x` verbatim. -/
theorem take_drop_append_encode {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (pre post : List AbstractByte) (x : α) :
    ((pre ++ c.encode x ++ post).drop pre.length).take n = c.encode x := by
  rw [List.append_assoc, List.drop_left' rfl, List.take_left' (c.encode_length x)]

/-- Decoding the `n`-byte window starting at `pre.length` in `pre ++ c.encode x ++ post` returns `some x`. -/
theorem decode_slice_at_append {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (pre post : List AbstractByte) (x : α) :
    c.decode (((pre ++ c.encode x ++ post).drop pre.length).take n) = some x := by
  rw [c.take_drop_append_encode pre post x]
  exact c.decode_encode x

/-- `sliceAbstractBytes` extracts `some (c.encode x)` from `pre ++ c.encode x ++ post` at `pre.length`. -/
theorem sliceAbstractBytes_append_encode {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (pre post : List AbstractByte) (x : α) :
    sliceAbstractBytes (pre ++ c.encode x ++ post) pre.length n = some (c.encode x) := by
  unfold sliceAbstractBytes
  have hLen : pre.length + n ≤ (pre ++ c.encode x ++ post).length := by
    have hEnc := c.encode_length x
    simp only [List.length_append, hEnc]
    omega
  have hBle : Nat.ble (Nat.add pre.length n) (Trusted.Sequence.length (pre ++ c.encode x ++ post)) = true :=
    Nat.ble_eq_true_of_le hLen
  rw [hBle]
  dsimp only
  rw [takeAbstractBytes_eq_take, dropAbstractBytes_eq_drop]
  exact congrArg some (c.take_drop_append_encode pre post x)

/-- Chaining `sliceAbstractBytes` with `c.decode` recovers `some x` in O(1) without unfolding `c`. -/
theorem decode_sliceAbstractBytes_append {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (pre post : List AbstractByte) (x : α) :
    (sliceAbstractBytes (pre ++ c.encode x ++ post) pre.length n).bind c.decode = some x := by
  rw [c.sliceAbstractBytes_append_encode pre post x]
  exact c.decode_encode x

/-- Decoder rejects any byte sequence whose length differs from `n`. -/
def IsExactWidth {α : Type} {n : Nat} (c : FixedByteCodec α n) : Prop :=
  ∀ ⦃bs : List AbstractByte⦄ ⦃x : α⦄, c.decode bs = some x → bs.length = n

/-- Every encoded byte sequence consists solely of initialized bytes (`IntoBytes` side-condition). -/
def IsInitCodec {α : Type} {n : Nat} (c : FixedByteCodec α n) : Prop :=
  ∀ x : α, allBytesInitialized (c.encode x) = true

/-- Every `n`-byte fully-initialized sequence decodes to some `x : α` (`FromBytes` side-condition). -/
def IsSurjectiveInitDecoder {α : Type} {n : Nat} (c : FixedByteCodec α n) : Prop :=
  ∀ bs : List AbstractByte, bs.length = n → allBytesInitialized bs = true → ∃ x : α, c.decode bs = some x

/-- The `n`-byte zero-initialized sequence decodes to some `x : α` (`FromZeros` side-condition). -/
def HasZeroValid {α : Type} {n : Nat} (c : FixedByteCodec α n) : Prop :=
  ∃ x : α, c.decode (zeroInitBytes n) = some x

/-- Any `IsSurjectiveInitDecoder` codec automatically satisfies `HasZeroValid`. -/
theorem IsSurjectiveInitDecoder.hasZeroValid {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (h : c.IsSurjectiveInitDecoder) : c.HasZeroValid :=
  h (zeroInitBytes n) (length_zeroInitBytes n) (allBytesInitialized_zeroInitBytes n)

/-- If `c` is `IsExactWidth`, decoding `bs` with `bs.length ≠ n` returns `none`. -/
theorem IsExactWidth.decode_eq_none_of_length_ne {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hExact : c.IsExactWidth)
    {bs : List AbstractByte} (hNe : bs.length ≠ n) :
    c.decode bs = none := by
  cases hDec : c.decode bs with
  | none => rfl
  | some x => exact False.elim (hNe (hExact hDec))

end FixedByteCodec

/-! ## 2. Helper Lemmas on `Nat.beq`, `zeroInitBytes`, `replicateUninitBytes`, and LE Bytes -/

theorem nat_beq_self (n : Nat) : Nat.beq n n = true :=
  Nat.beq_eq.mpr rfl

theorem nat_beq_eq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact False.elim (h (Nat.eq_of_beq_eq_true hb))

/-- `zeroInitBytes (m + n)` splits as `zeroInitBytes m ++ zeroInitBytes n`. -/
theorem zeroInitBytes_add :
    ∀ m n : Nat, zeroInitBytes (m + n) = zeroInitBytes m ++ zeroInitBytes n
  | 0, n => by simp [zeroInitBytes]
  | k + 1, n => by
    have hEq : k + 1 + n = (k + n) + 1 := by omega
    rw [hEq]
    exact congrArg (.init (UInt8.ofNat 0) none :: ·) (zeroInitBytes_add k n)

/-- Encoding `0` as `sz` little-endian bytes with `none` provenance yields `zeroInitBytes sz`. -/
theorem encodeLittleEndianBytes_zero_eq_zeroInitBytes :
    ∀ sz : Nat, encodeLittleEndianBytes 0 sz none = zeroInitBytes sz
  | 0 => rfl
  | k + 1 => by
    unfold encodeLittleEndianBytes zeroInitBytes
    have hDiv : Nat.div 0 256 = 0 := rfl
    rw [hDiv, encodeLittleEndianBytes_zero_eq_zeroInitBytes k]

/-- Length of `replicateUninitBytes n` is `n`. -/
@[simp]
theorem length_replicateUninitBytes :
    ∀ n : Nat, (replicateUninitBytes n).length = n
  | 0 => rfl
  | k + 1 => congrArg Nat.succ (length_replicateUninitBytes k)

/-- For any positive count `0 < padBytes`, `replicateUninitBytes padBytes` is not initialized. -/
theorem allBytesInitialized_replicateUninitBytes_eq_false
    {padBytes : Nat} (hPos : 0 < padBytes) :
    allBytesInitialized (replicateUninitBytes padBytes) = false := by
  cases padBytes with
  | zero => omega
  | succ _ => rfl

/-- Appending an uninitialized byte list on the right makes `allBytesInitialized` `false`. -/
theorem allBytesInitialized_append_eq_false_right
    (xs : List AbstractByte) {ys : List AbstractByte}
    (hys : allBytesInitialized ys = false) :
    allBytesInitialized (xs ++ ys) = false := by
  induction xs with
  | nil => exact hys
  | cons x rest ih =>
    cases x with
    | uninit => rfl
    | init _ _ => exact ih

/-- Appending an uninitialized byte list on the left makes `allBytesInitialized` `false`. -/
theorem allBytesInitialized_append_eq_false_left
    {xs : List AbstractByte} (ys : List AbstractByte)
    (hxs : allBytesInitialized xs = false) :
    allBytesInitialized (xs ++ ys) = false := by
  induction xs with
  | nil => nomatch hxs
  | cons x rest ih =>
    cases x with
    | uninit => rfl
    | init _ _ => exact ih hxs

/-- `encodeLittleEndianBytes` depends only on `bits % 2 ^ (8 * sz)`. -/
theorem encodeLittleEndianBytes_mod_two_pow (prov : Option (Nat × Nat)) :
    ∀ (sz bits : Nat),
      encodeLittleEndianBytes (bits % 2 ^ (8 * sz)) sz prov =
        encodeLittleEndianBytes bits sz prov
  | 0, _ => rfl
  | k + 1, bits => by
    let M := 2 ^ (8 * k)
    have hPow : 2 ^ (8 * (k + 1)) = 256 * M := by
      have hMul : 8 * (k + 1) = 8 + 8 * k := by omega
      rw [hMul, Nat.pow_add]
    have hLow : UInt8.ofNat (bits % 2 ^ (8 * (k + 1))) = UInt8.ofNat bits := by
      rw [hPow]
      apply UInt8.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      simp only [UInt8.ofNat, BitVec.ofNat]
      change (bits % (256 * M)) % 256 = bits % 256
      have hDvd : 256 ∣ 256 * M := ⟨M, rfl⟩
      exact Nat.mod_mod_of_dvd bits hDvd
    have hHigh : (bits % 2 ^ (8 * (k + 1))) / 256 = (bits / 256) % M := by
      rw [hPow]
      have hMPos : 0 < M := Nat.two_pow_pos (8 * k)
      have hRemLt : (bits % (256 * M)) / 256 < M := by
        have hLt : bits % (256 * M) < 256 * M := Nat.mod_lt bits (by omega)
        have hDiv := Nat.div_add_mod (bits % (256 * M)) 256
        omega
      have hBitsEq : bits = bits % (256 * M) + 256 * (M * (bits / (256 * M))) := by
        have h1 := (Nat.mod_add_div bits (256 * M)).symm
        rw [Nat.mul_assoc 256 M] at h1
        exact h1
      have hDiv256 : bits / 256 = (bits % (256 * M)) / 256 + M * (bits / (256 * M)) := by
        conv => lhs; arg 1; rw [hBitsEq]
        exact Nat.add_mul_div_left (bits % (256 * M)) (M * (bits / (256 * M))) (by decide)
      rw [hDiv256, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hRemLt]
    unfold encodeLittleEndianBytes
    change
      AbstractByte.init (UInt8.ofNat (bits % 2 ^ (8 * (k + 1)))) prov ::
          encodeLittleEndianBytes ((bits % 2 ^ (8 * (k + 1))) / 256) k prov =
        AbstractByte.init (UInt8.ofNat bits) prov ::
          encodeLittleEndianBytes (bits / 256) k prov
    rw [hLow, hHigh, encodeLittleEndianBytes_mod_two_pow prov k (bits / 256)]

/-! ## 3. Composable `FixedByteCodec` Combinators -/

namespace FixedByteCodec

/-- Zero-byte codec for `Unit` (`()`). -/
def unit : FixedByteCodec Unit 0 :=
  ofRoundTrip
    (fun _ => [])
    (fun bs => match bs with | [] => some () | _ :: _ => none)
    (fun _ => rfl)
    (fun _ => rfl)

theorem unit_isExactWidth : unit.IsExactWidth := by
  intro bs _ hDec
  cases bs with
  | nil => rfl
  | cons _ _ => nomatch hDec

theorem unit_isInitCodec : unit.IsInitCodec := fun _ => rfl

theorem unit_isSurjectiveInitDecoder : unit.IsSurjectiveInitDecoder := by
  intro bs hLen _
  cases bs with
  | nil => exact ⟨(), rfl⟩
  | cons _ _ => nomatch hLen

theorem unit_hasZeroValid : unit.HasZeroValid :=
  unit_isSurjectiveInitDecoder.hasZeroValid

/-- Single-byte codec for `UInt8` (`u8`). -/
def u8 : FixedByteCodec UInt8 1 :=
  ofRoundTrip
    (fun b => [.init b none])
    (fun bs => match bs with | [.init b _] => some b | _ => none)
    (fun _ => rfl)
    (fun _ => rfl)

theorem u8_isExactWidth : u8.IsExactWidth := by
  intro bs _ hDec
  cases bs with
  | nil => nomatch hDec
  | cons b0 rest =>
    cases b0 with
    | uninit => nomatch hDec
    | init _ _ =>
      cases rest with
      | nil => rfl
      | cons _ _ => nomatch hDec

theorem u8_isInitCodec : u8.IsInitCodec := fun _ => rfl

theorem u8_isSurjectiveInitDecoder : u8.IsSurjectiveInitDecoder := by
  intro bs hLen hInit
  cases bs with
  | nil => nomatch hLen
  | cons b0 rest =>
    cases rest with
    | cons _ _ => nomatch hLen
    | nil =>
      cases b0 with
      | uninit => nomatch hInit
      | init b _ => exact ⟨b, rfl⟩

theorem u8_hasZeroValid : u8.HasZeroValid :=
  u8_isSurjectiveInitDecoder.hasZeroValid

@[simp]
theorem u8_decode_uninit : u8.decode [.uninit] = none := rfl

/-- Single-byte Rust `bool` codec (`false ↦ 0x00`, `true ↦ 0x01`, rejecting `≥ 2` and `.uninit`). -/
def boolByte : FixedByteCodec Bool 1 :=
  ofRoundTrip
    (fun b =>
      match b with
      | false => [.init (UInt8.ofNat 0) none]
      | true => [.init (UInt8.ofNat 1) none])
    (fun bs =>
      match bs with
      | [.init b _] =>
        match Nat.beq b.toBitVec.toNat 0 with
        | true => some false
        | false =>
          match Nat.beq b.toBitVec.toNat 1 with
          | true => some true
          | false => none
      | _ => none)
    (fun b => by cases b <;> rfl)
    (fun b => by cases b <;> rfl)

theorem boolByte_isExactWidth : boolByte.IsExactWidth := by
  intro bs _ hDec
  cases bs with
  | nil => nomatch hDec
  | cons b0 rest =>
    cases b0 with
    | uninit => nomatch hDec
    | init _ _ =>
      cases rest with
      | nil => rfl
      | cons _ _ => nomatch hDec

theorem boolByte_isInitCodec : boolByte.IsInitCodec := by
  intro b
  cases b <;> rfl

theorem boolByte_hasZeroValid : boolByte.HasZeroValid :=
  ⟨false, rfl⟩

@[simp]
theorem boolByte_decode_uninit : boolByte.decode [.uninit] = none := rfl

/-- `boolByte` rejects every initialized byte with unsigned value `b ≥ 2`. -/
theorem boolByte_decode_invalid_of_ge_two
    (b : UInt8) (prov : Option (Nat × Nat)) (hGe : 2 ≤ b.toBitVec.toNat) :
    boolByte.decode [.init b prov] = none := by
  have hNe0 : Nat.beq b.toBitVec.toNat 0 = false :=
    nat_beq_eq_false_of_ne (by omega)
  have hNe1 : Nat.beq b.toBitVec.toNat 1 = false :=
    nat_beq_eq_false_of_ne (by omega)
  change
    (match Nat.beq b.toBitVec.toNat 0 with
     | true => some false
     | false =>
       match Nat.beq b.toBitVec.toNat 1 with
       | true => some true
       | false => none) = none
  rw [hNe0, hNe1]

/-- `boolByte` is NOT `IsSurjectiveInitDecoder` (`0x02` is initialized of length `1`, yet invalid). -/
theorem boolByte_not_isSurjectiveInitDecoder :
    ¬ boolByte.IsSurjectiveInitDecoder := by
  intro hSurj
  rcases hSurj [.init (UInt8.ofNat 2) none] rfl rfl with ⟨b, hb⟩
  nomatch hb

/--
Fixed-width little-endian unsigned bit-pattern codec of positive byte width `sz`,
decoding into `{ bits : Nat // bits < 2 ^ (8 * sz) }`.
-/
def uintBitsLE (sz : Nat) (hNz : 0 < sz) :
    FixedByteCodec { bits : Nat // bits < 2 ^ (8 * sz) } sz :=
  ofRoundTrip
    (fun x => encodeLittleEndianBytes x.val sz none)
    (fun bs =>
      match Nat.beq bs.length sz with
      | false => none
      | true =>
        match decodeLittleEndianBytes bs with
        | none => none
        | some (bits, _) =>
          if hLt : bits < 2 ^ (8 * sz) then some ⟨bits, hLt⟩ else none)
    (fun x => length_encodeLittleEndianBytes none sz x.val)
    (fun ⟨bits, hProp⟩ => by
      obtain ⟨k, rfl⟩ : ∃ k, sz = k + 1 := ⟨sz - 1, by omega⟩
      have hLenEq : (encodeLittleEndianBytes bits (k + 1) none).length = k + 1 :=
        length_encodeLittleEndianBytes none (k + 1) bits
      have hLen : Nat.beq (encodeLittleEndianBytes bits (k + 1) none).length (k + 1) = true :=
        Nat.beq_eq.mpr hLenEq
      have hModLt : bits < scalarModulus (k + 1) := by
        rw [Anneal.Scalars.scalarModulus_eq_two_pow]
        exact hProp
      have hDec := decodeLittleEndianBytes_encodeLittleEndianBytes_of_lt none k bits hModLt
      dsimp only
      rw [hLen]
      dsimp only
      rw [hDec]
      simp only [hProp, ↓reduceDIte])

theorem uintBitsLE_isExactWidth (sz : Nat) (hNz : 0 < sz) :
    (uintBitsLE sz hNz).IsExactWidth := by
  intro bs _ hDec
  unfold uintBitsLE ofRoundTrip at hDec
  dsimp only at hDec
  cases hBeq : Nat.beq bs.length sz <;> rw [hBeq] at hDec
  · nomatch hDec
  · exact Nat.eq_of_beq_eq_true hBeq

theorem uintBitsLE_isInitCodec (sz : Nat) (hNz : 0 < sz) :
    (uintBitsLE sz hNz).IsInitCodec :=
  fun x => allBytesInitialized_encodeLittleEndianBytes none sz x.val

theorem uintBitsLE_isSurjectiveInitDecoder (sz : Nat) (hNz : 0 < sz) :
    (uintBitsLE sz hNz).IsSurjectiveInitDecoder := by
  intro bs hLen hInit
  rcases decodeLittleEndianBytes_of_allBytesInitialized bs hInit with ⟨bits, prov, hDec⟩
  have hModLt : bits < scalarModulus bs.length :=
    decodeLittleEndianBytes_lt_scalarModulus bs bits prov hDec
  have hLt : bits < 2 ^ (8 * sz) := by
    rw [hLen, Anneal.Scalars.scalarModulus_eq_two_pow] at hModLt
    exact hModLt
  refine ⟨⟨bits, hLt⟩, ?_⟩
  unfold uintBitsLE ofRoundTrip
  have hBeq : Nat.beq bs.length sz = true := Nat.beq_eq.mpr hLen
  dsimp only
  rw [hBeq]
  dsimp only
  rw [hDec]
  simp only [hLt, ↓reduceDIte]

theorem uintBitsLE_hasZeroValid (sz : Nat) (hNz : 0 < sz) :
    (uintBitsLE sz hNz).HasZeroValid :=
  (uintBitsLE_isSurjectiveInitDecoder sz hNz).hasZeroValid

/-- Decoding `zeroInitBytes sz` with `uintBitsLE sz hNz` yields `0`. -/
theorem uintBitsLE_decode_zeroInitBytes (sz : Nat) (hNz : 0 < sz) :
    (uintBitsLE sz hNz).decode (zeroInitBytes sz) =
      some ⟨0, Nat.two_pow_pos (8 * sz)⟩ := by
  have hEnc : (uintBitsLE sz hNz).encode ⟨0, Nat.two_pow_pos (8 * sz)⟩ = zeroInitBytes sz :=
    encodeLittleEndianBytes_zero_eq_zeroInitBytes sz
  rw [← hEnc]
  exact (uintBitsLE sz hNz).decode_encode ⟨0, Nat.two_pow_pos (8 * sz)⟩

/-- Map a `FixedByteCodec α n` across a type equivalence `(toβ, ofβ)`. -/
def mapEquiv {α β : Type} {n : Nat}
    (c : FixedByteCodec α n)
    (toβ : α → β)
    (ofβ : β → α)
    (_left_inv : ∀ a : α, ofβ (toβ a) = a)
    (right_inv : ∀ b : β, toβ (ofβ b) = b) :
    FixedByteCodec β n :=
  ofRoundTrip
    (fun b => c.encode (ofβ b))
    (fun bs => (c.decode bs).map toβ)
    (fun b => c.encode_length (ofβ b))
    (fun b => by
      simp only [c.decode_encode (ofβ b), Option.map_some, right_inv b])

theorem mapEquiv_encode_to {α β : Type} {n : Nat}
    (c : FixedByteCodec α n) (toβ : α → β) (ofβ : β → α)
    (hL : ∀ a, ofβ (toβ a) = a) (hR : ∀ b, toβ (ofβ b) = b) (a : α) :
    (c.mapEquiv toβ ofβ hL hR).encode (toβ a) = c.encode a :=
  congrArg c.encode (hL a)

theorem mapEquiv_isExactWidth {α β : Type} {n : Nat}
    (c : FixedByteCodec α n) (toβ : α → β) (ofβ : β → α)
    (hL : ∀ a, ofβ (toβ a) = a) (hR : ∀ b, toβ (ofβ b) = b)
    (hExact : c.IsExactWidth) :
    (c.mapEquiv toβ ofβ hL hR).IsExactWidth := by
  intro bs _ hDec
  unfold mapEquiv ofRoundTrip at hDec
  dsimp only at hDec
  cases hCDec : c.decode bs <;> rw [hCDec] at hDec
  · nomatch hDec
  · exact hExact hCDec

theorem mapEquiv_isInitCodec {α β : Type} {n : Nat}
    (c : FixedByteCodec α n) (toβ : α → β) (ofβ : β → α)
    (hL : ∀ a, ofβ (toβ a) = a) (hR : ∀ b, toβ (ofβ b) = b)
    (hInit : c.IsInitCodec) :
    (c.mapEquiv toβ ofβ hL hR).IsInitCodec :=
  fun b => hInit (ofβ b)

theorem mapEquiv_isSurjectiveInitDecoder {α β : Type} {n : Nat}
    (c : FixedByteCodec α n) (toβ : α → β) (ofβ : β → α)
    (hL : ∀ a, ofβ (toβ a) = a) (hR : ∀ b, toβ (ofβ b) = b)
    (hSurj : c.IsSurjectiveInitDecoder) :
    (c.mapEquiv toβ ofβ hL hR).IsSurjectiveInitDecoder := by
  intro bs hLen hInit
  rcases hSurj bs hLen hInit with ⟨a, ha⟩
  exact ⟨toβ a, by simp [mapEquiv, ofRoundTrip, ha]⟩

theorem mapEquiv_hasZeroValid {α β : Type} {n : Nat}
    (c : FixedByteCodec α n) (toβ : α → β) (ofβ : β → α)
    (hL : ∀ a, ofβ (toβ a) = a) (hR : ∀ b, toβ (ofβ b) = b)
    (hZero : c.HasZeroValid) :
    (c.mapEquiv toβ ofβ hL hR).HasZeroValid := by
  rcases hZero with ⟨a, ha⟩
  exact ⟨toβ a, by simp [mapEquiv, ofRoundTrip, ha]⟩

/--
Fixed-width little-endian `ScalarInt` codec of positive byte width `sz`,
decoding into `{ sv : ScalarInt // sv.sizeBytes = sz ∧ sv.bits < 2 ^ (8 * sz) }`.
-/
def scalarLE (sz : Nat) (hNz : 0 < sz) :
    FixedByteCodec { sv : ScalarInt // sv.sizeBytes = sz ∧ sv.bits < 2 ^ (8 * sz) } sz :=
  (uintBitsLE sz hNz).mapEquiv
    (fun b => ⟨{ bits := b.val, sizeBytes := sz }, rfl, b.property⟩)
    (fun s => ⟨s.val.bits, s.property.2⟩)
    (fun _ => rfl)
    (fun ⟨⟨bits, sizeBytes⟩, hSz, hLt⟩ => by
      subst hSz
      rfl)

theorem scalarLE_isExactWidth (sz : Nat) (hNz : 0 < sz) :
    (scalarLE sz hNz).IsExactWidth :=
  mapEquiv_isExactWidth _ _ _ _ _ (uintBitsLE_isExactWidth sz hNz)

theorem scalarLE_isInitCodec (sz : Nat) (hNz : 0 < sz) :
    (scalarLE sz hNz).IsInitCodec :=
  mapEquiv_isInitCodec _ _ _ _ _ (uintBitsLE_isInitCodec sz hNz)

theorem scalarLE_isSurjectiveInitDecoder (sz : Nat) (hNz : 0 < sz) :
    (scalarLE sz hNz).IsSurjectiveInitDecoder :=
  mapEquiv_isSurjectiveInitDecoder _ _ _ _ _ (uintBitsLE_isSurjectiveInitDecoder sz hNz)

theorem scalarLE_hasZeroValid (sz : Nat) (hNz : 0 < sz) :
    (scalarLE sz hNz).HasZeroValid :=
  mapEquiv_hasZeroValid _ _ _ _ _ (uintBitsLE_hasZeroValid sz hNz)

/-- Bridge connecting `scalarLE.encode` to `Trusted`'s `encodeScalarBytes`. -/
theorem encodeScalarBytes_eq_scalarLE_encode (sz : Nat) (hNz : 0 < sz)
    (x : { sv : ScalarInt // sv.sizeBytes = sz ∧ sv.bits < 2 ^ (8 * sz) }) :
    encodeScalarBytes x.val none = some ((scalarLE sz hNz).encode x) := by
  rcases x with ⟨⟨bits, svSz⟩, hSz, _hLt⟩
  dsimp only at hSz
  subst hSz
  unfold encodeScalarBytes
  dsimp only
  have hBeq : Nat.beq svSz 0 = false := nat_beq_eq_false_of_ne (by omega)
  rw [hBeq]
  rfl

/-- Contiguous product combinator concatenating `n₁`-byte and `n₂`-byte codecs. -/
def prod {α β : Type} {n₁ n₂ : Nat}
    (c₁ : FixedByteCodec α n₁) (c₂ : FixedByteCodec β n₂) :
    FixedByteCodec (α × β) (n₁ + n₂) :=
  ofRoundTrip
    (fun p => c₁.encode p.1 ++ c₂.encode p.2)
    (fun bs =>
      match Nat.beq bs.length (n₁ + n₂) with
      | false => none
      | true =>
        match c₁.decode (bs.take n₁), c₂.decode (bs.drop n₁) with
        | some a, some b => some (a, b)
        | _, _ => none)
    (fun p => by
      rw [List.length_append, c₁.encode_length p.1, c₂.encode_length p.2])
    (fun ⟨a, b⟩ => by
      have hLen : (c₁.encode a ++ c₂.encode b).length = n₁ + n₂ := by
        rw [List.length_append, c₁.encode_length a, c₂.encode_length b]
      have hBeq : Nat.beq (c₁.encode a ++ c₂.encode b).length (n₁ + n₂) = true :=
        Nat.beq_eq.mpr hLen
      dsimp only
      rw [hBeq]
      dsimp only
      rw [List.take_left' (c₁.encode_length a), List.drop_left' (c₁.encode_length a),
          c₁.decode_encode a, c₂.decode_encode b])

theorem prod_isExactWidth {α β : Type} {n₁ n₂ : Nat}
    (c₁ : FixedByteCodec α n₁) (c₂ : FixedByteCodec β n₂) :
    (prod c₁ c₂).IsExactWidth := by
  intro bs _ hDec
  unfold prod ofRoundTrip at hDec
  dsimp only at hDec
  cases hBeq : Nat.beq bs.length (n₁ + n₂) <;> rw [hBeq] at hDec
  · nomatch hDec
  · exact Nat.eq_of_beq_eq_true hBeq

theorem prod_isInitCodec {α β : Type} {n₁ n₂ : Nat}
    {c₁ : FixedByteCodec α n₁} {c₂ : FixedByteCodec β n₂}
    (h₁ : c₁.IsInitCodec) (h₂ : c₂.IsInitCodec) :
    (prod c₁ c₂).IsInitCodec :=
  fun ⟨a, b⟩ => allBytesInitialized_append (h₁ a) (h₂ b)

theorem prod_isSurjectiveInitDecoder {α β : Type} {n₁ n₂ : Nat}
    {c₁ : FixedByteCodec α n₁} {c₂ : FixedByteCodec β n₂}
    (h₁ : c₁.IsSurjectiveInitDecoder) (h₂ : c₂.IsSurjectiveInitDecoder) :
    (prod c₁ c₂).IsSurjectiveInitDecoder := by
  intro bs hLen hInit
  have hTakeLen : (bs.take n₁).length = n₁ := by
    rw [List.length_take]; omega
  have hDropLen : (bs.drop n₁).length = n₂ := by
    rw [List.length_drop]; omega
  rcases h₁ (bs.take n₁) hTakeLen (allBytesInitialized_take n₁ hInit) with ⟨a, ha⟩
  rcases h₂ (bs.drop n₁) hDropLen (allBytesInitialized_drop n₁ hInit) with ⟨b, hb⟩
  refine ⟨(a, b), ?_⟩
  unfold prod ofRoundTrip
  have hBeq : Nat.beq bs.length (n₁ + n₂) = true := Nat.beq_eq.mpr hLen
  dsimp only
  rw [hBeq]
  dsimp only
  rw [ha, hb]

theorem prod_hasZeroValid {α β : Type} {n₁ n₂ : Nat}
    {c₁ : FixedByteCodec α n₁} {c₂ : FixedByteCodec β n₂}
    (h₁ : c₁.HasZeroValid) (h₂ : c₂.HasZeroValid) :
    (prod c₁ c₂).HasZeroValid := by
  rcases h₁ with ⟨a, ha⟩
  rcases h₂ with ⟨b, hb⟩
  refine ⟨(a, b), ?_⟩
  unfold prod ofRoundTrip
  have hBeq : Nat.beq (zeroInitBytes (n₁ + n₂)).length (n₁ + n₂) = true :=
    Nat.beq_eq.mpr (length_zeroInitBytes (n₁ + n₂))
  dsimp only
  rw [hBeq]
  dsimp only
  rw [zeroInitBytes_add n₁ n₂,
      List.take_left' (length_zeroInitBytes n₁),
      List.drop_left' (length_zeroInitBytes n₁),
      ha, hb]

/-- Negative propagation: if the first component `c₁` rejects `bs.take n₁`, `prod c₁ c₂` rejects `bs`. -/
theorem prod_decode_eq_none_of_fst_none {α β : Type} {n₁ n₂ : Nat}
    (c₁ : FixedByteCodec α n₁) (c₂ : FixedByteCodec β n₂)
    {bs : List AbstractByte} (hFst : c₁.decode (bs.take n₁) = none) :
    (prod c₁ c₂).decode bs = none := by
  unfold prod ofRoundTrip
  dsimp only
  cases Nat.beq bs.length (n₁ + n₂)
  · rfl
  · dsimp only
    rw [hFst]

/-- Negative propagation: if the second component `c₂` rejects `bs.drop n₁`, `prod c₁ c₂` rejects `bs`. -/
theorem prod_decode_eq_none_of_snd_none {α β : Type} {n₁ n₂ : Nat}
    (c₁ : FixedByteCodec α n₁) (c₂ : FixedByteCodec β n₂)
    {bs : List AbstractByte} (hSnd : c₂.decode (bs.drop n₁) = none) :
    (prod c₁ c₂).decode bs = none := by
  unfold prod ofRoundTrip
  dsimp only
  cases Nat.beq bs.length (n₁ + n₂)
  · rfl
  · dsimp only
    cases c₁.decode (bs.take n₁) <;> rw [hSnd]

/--
Uninitialized padding codec of width `padBytes`: encodes `()` to
`replicateUninitBytes padBytes` and accepts any `padBytes`-length slice on `decode`.
-/
def padUninit (padBytes : Nat) : FixedByteCodec Unit padBytes :=
  ofRoundTrip
    (fun _ => replicateUninitBytes padBytes)
    (fun bs => if Nat.beq bs.length padBytes then some () else none)
    (fun _ => length_replicateUninitBytes padBytes)
    (fun _ => by simp)

theorem padUninit_encode_eq_replicate (padBytes : Nat) :
    (padUninit padBytes).encode () = List.replicate padBytes .uninit :=
  replicateUninitBytes_eq_replicate padBytes

theorem padUninit_isExactWidth (padBytes : Nat) :
    (padUninit padBytes).IsExactWidth := by
  intro bs _ hDec
  unfold padUninit ofRoundTrip at hDec
  dsimp only at hDec
  cases hBeq : Nat.beq bs.length padBytes <;> rw [hBeq] at hDec
  · nomatch hDec
  · exact Nat.eq_of_beq_eq_true hBeq

theorem padUninit_isSurjectiveInitDecoder (padBytes : Nat) :
    (padUninit padBytes).IsSurjectiveInitDecoder := by
  intro bs hLen _
  exact ⟨(), by simp [padUninit, ofRoundTrip, hLen]⟩

theorem padUninit_hasZeroValid (padBytes : Nat) :
    (padUninit padBytes).HasZeroValid :=
  (padUninit_isSurjectiveInitDecoder padBytes).hasZeroValid

theorem padUninit_encode_uninit_of_pos {padBytes : Nat} (hPos : 0 < padBytes) :
    allBytesInitialized ((padUninit padBytes).encode ()) = false :=
  allBytesInitialized_replicateUninitBytes_eq_false hPos

theorem padUninit_not_isInitCodec {padBytes : Nat} (hPos : 0 < padBytes) :
    ¬ (padUninit padBytes).IsInitCodec := by
  intro hInit
  have hTrue := hInit ()
  rw [padUninit_encode_uninit_of_pos hPos] at hTrue
  nomatch hTrue

/-- Prepend `padBytes` uninitialized padding bytes before `c`. -/
def padLeft {α : Type} {n : Nat} (padBytes : Nat) (c : FixedByteCodec α n) :
    FixedByteCodec α (padBytes + n) :=
  (prod (padUninit padBytes) c).mapEquiv
    (fun p => p.2)
    (fun x => ((), x))
    (fun ⟨_, _⟩ => rfl)
    (fun _ => rfl)

/-- Append `padBytes` uninitialized padding bytes after `c`. -/
def padRight {α : Type} {n : Nat} (c : FixedByteCodec α n) (padBytes : Nat) :
    FixedByteCodec α (n + padBytes) :=
  (prod c (padUninit padBytes)).mapEquiv
    (fun p => p.1)
    (fun x => (x, ()))
    (fun ⟨_, _⟩ => rfl)
    (fun _ => rfl)

theorem padLeft_encode_eq {α : Type} {n : Nat}
    (padBytes : Nat) (c : FixedByteCodec α n) (x : α) :
    (padLeft padBytes c).encode x = replicateUninitBytes padBytes ++ c.encode x := rfl

theorem padRight_encode_eq {α : Type} {n : Nat}
    (c : FixedByteCodec α n) (padBytes : Nat) (x : α) :
    (padRight c padBytes).encode x = c.encode x ++ replicateUninitBytes padBytes := rfl

theorem padLeft_isExactWidth {α : Type} {n : Nat}
    (padBytes : Nat) (c : FixedByteCodec α n) :
    (padLeft padBytes c).IsExactWidth :=
  mapEquiv_isExactWidth _ _ _ _ _ (prod_isExactWidth (padUninit padBytes) c)

theorem padRight_isExactWidth {α : Type} {n : Nat}
    (c : FixedByteCodec α n) (padBytes : Nat) :
    (padRight c padBytes).IsExactWidth :=
  mapEquiv_isExactWidth _ _ _ _ _ (prod_isExactWidth c (padUninit padBytes))

theorem padLeft_isSurjectiveInitDecoder {α : Type} {n : Nat}
    (padBytes : Nat) {c : FixedByteCodec α n} (hc : c.IsSurjectiveInitDecoder) :
    (padLeft padBytes c).IsSurjectiveInitDecoder :=
  mapEquiv_isSurjectiveInitDecoder _ _ _ _ _
    (prod_isSurjectiveInitDecoder (padUninit_isSurjectiveInitDecoder padBytes) hc)

theorem padRight_isSurjectiveInitDecoder {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (padBytes : Nat) (hc : c.IsSurjectiveInitDecoder) :
    (padRight c padBytes).IsSurjectiveInitDecoder :=
  mapEquiv_isSurjectiveInitDecoder _ _ _ _ _
    (prod_isSurjectiveInitDecoder hc (padUninit_isSurjectiveInitDecoder padBytes))

theorem padLeft_hasZeroValid {α : Type} {n : Nat}
    (padBytes : Nat) {c : FixedByteCodec α n} (hc : c.HasZeroValid) :
    (padLeft padBytes c).HasZeroValid :=
  mapEquiv_hasZeroValid _ _ _ _ _
    (prod_hasZeroValid (padUninit_hasZeroValid padBytes) hc)

theorem padRight_hasZeroValid {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (padBytes : Nat) (hc : c.HasZeroValid) :
    (padRight c padBytes).HasZeroValid :=
  mapEquiv_hasZeroValid _ _ _ _ _
    (prod_hasZeroValid hc (padUninit_hasZeroValid padBytes))

/-- Negative theorem: when `0 < padBytes`, `padLeft` always emits uninitialized bytes. -/
theorem allBytesInitialized_padLeft_encode_eq_false {α : Type} {n : Nat}
    {padBytes : Nat} (hPos : 0 < padBytes) (c : FixedByteCodec α n) (x : α) :
    allBytesInitialized ((padLeft padBytes c).encode x) = false :=
  allBytesInitialized_append_eq_false_left (c.encode x)
    (allBytesInitialized_replicateUninitBytes_eq_false hPos)

/-- Negative theorem: when `0 < padBytes`, `padRight` always emits uninitialized bytes. -/
theorem allBytesInitialized_padRight_encode_eq_false {α : Type} {n : Nat}
    (c : FixedByteCodec α n) {padBytes : Nat} (hPos : 0 < padBytes) (x : α) :
    allBytesInitialized ((padRight c padBytes).encode x) = false :=
  allBytesInitialized_append_eq_false_right (c.encode x)
    (allBytesInitialized_replicateUninitBytes_eq_false hPos)

/-- Any inhabited codec padded with `0 < padBytes` left-padding bytes violates `IsInitCodec`. -/
theorem padLeft_not_isInitCodec {α : Type} {n padBytes : Nat}
    (hPos : 0 < padBytes) (c : FixedByteCodec α n) (x₀ : α) :
    ¬ (padLeft padBytes c).IsInitCodec := by
  intro hInit
  have hTrue := hInit x₀
  rw [allBytesInitialized_padLeft_encode_eq_false hPos c x₀] at hTrue
  nomatch hTrue

/-- Any inhabited codec padded with `0 < padBytes` right-padding bytes violates `IsInitCodec`. -/
theorem padRight_not_isInitCodec {α : Type} {n padBytes : Nat}
    (c : FixedByteCodec α n) (hPos : 0 < padBytes) (x₀ : α) :
    ¬ (padRight c padBytes).IsInitCodec := by
  intro hInit
  have hTrue := hInit x₀
  rw [allBytesInitialized_padRight_encode_eq_false c hPos x₀] at hTrue
  nomatch hTrue

/-- Zero-width padding (`padUninit 0`) emits `[]` and therefore satisfies `IsInitCodec`. -/
theorem padUninit_zero_isInitCodec : (padUninit 0).IsInitCodec :=
  fun _ => rfl

/-- Zero left-padding (`padLeft 0 c`) preserves `IsInitCodec`. -/
theorem padLeft_zero_isInitCodec {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hc : c.IsInitCodec) :
    (padLeft 0 c).IsInitCodec :=
  fun x => hc x

/-- Left-padding preserves `IsInitCodec` whenever `padBytes = 0`. -/
theorem padLeft_isInitCodec_of_eq_zero {α : Type} {n padBytes : Nat}
    {c : FixedByteCodec α n} (hZero : padBytes = 0) (hc : c.IsInitCodec) :
    (padLeft padBytes c).IsInitCodec := by
  subst hZero
  exact padLeft_zero_isInitCodec hc

/-- Zero right-padding (`padRight c 0`) preserves `IsInitCodec`. -/
theorem padRight_zero_isInitCodec {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hc : c.IsInitCodec) :
    (padRight c 0).IsInitCodec := by
  intro x
  rw [padRight_encode_eq]
  exact allBytesInitialized_append (hc x) rfl

/-- Right-padding preserves `IsInitCodec` whenever `padBytes = 0`. -/
theorem padRight_isInitCodec_of_eq_zero {α : Type} {n padBytes : Nat}
    {c : FixedByteCodec α n} (hZero : padBytes = 0) (hc : c.IsInitCodec) :
    (padRight c padBytes).IsInitCodec := by
  subst hZero
  exact padRight_zero_isInitCodec hc

/-- Exact `IsInitCodec` characterization for `padLeft` over any inhabited type `α`. -/
theorem padLeft_isInitCodec_iff {α : Type} {n padBytes : Nat}
    (c : FixedByteCodec α n) (x₀ : α) :
    (padLeft padBytes c).IsInitCodec ↔ padBytes = 0 ∧ c.IsInitCodec := by
  cases padBytes with
  | zero =>
    simp only [true_and]
    exact ⟨fun h x => h x, padLeft_zero_isInitCodec⟩
  | succ k =>
    constructor
    · intro hInit
      exact False.elim (padLeft_not_isInitCodec (Nat.succ_pos k) c x₀ hInit)
    · rintro ⟨hEq, _⟩
      nomatch hEq

/-- Exact `IsInitCodec` characterization for `padRight` over any inhabited type `α`. -/
theorem padRight_isInitCodec_iff {α : Type} {n padBytes : Nat}
    (c : FixedByteCodec α n) (x₀ : α) :
    (padRight c padBytes).IsInitCodec ↔ padBytes = 0 ∧ c.IsInitCodec := by
  cases padBytes with
  | zero =>
    simp only [true_and]
    constructor
    · intro hInit x
      have hx := hInit x
      rw [padRight_encode_eq, show replicateUninitBytes 0 = [] from rfl, List.append_nil] at hx
      exact hx
    · exact padRight_zero_isInitCodec
  | succ k =>
    constructor
    · intro hInit
      exact False.elim (padRight_not_isInitCodec c (Nat.succ_pos k) x₀ hInit)
    · rintro ⟨hEq, _⟩
      nomatch hEq

/-- On an exact-width `(n + padBytes)`-byte chunk, `(padRight c padBytes).decode` reduces to `c.decode (chunk.take n)`. -/
theorem padRight_decode_of_length_eq {α : Type} {n padBytes : Nat}
    (c : FixedByteCodec α n) {chunk : List AbstractByte}
    (hLen : chunk.length = n + padBytes) :
    (padRight c padBytes).decode chunk = c.decode (chunk.take n) := by
  unfold padRight mapEquiv prod padUninit ofRoundTrip
  dsimp only
  rw [Nat.beq_eq.mpr hLen]
  dsimp only
  have hDropLen : Nat.beq (chunk.drop n).length padBytes = true := by
    apply Nat.beq_eq.mpr
    rw [List.length_drop]
    omega
  simp only [hDropLen, ↓reduceIte]
  cases c.decode (chunk.take n) <;> rfl

/-! ### Homogeneous Fixed-Length Lists (`listFixed`) and Arrays (`array`) -/

/-- Encode a list of elements sequentially by concatenating `c.encode` on each element. -/
@[reducible]
def encodeElems {α : Type} {n : Nat} (c : FixedByteCodec α n) : List α → List AbstractByte
  | [] => []
  | x :: xs => c.encode x ++ encodeElems c xs

/-- Decode `k` consecutive `n`-byte chunks into a length-indexed list `{ xs : List α // xs.length = k }`. -/
@[reducible]
def decodeChunks {α : Type} {n : Nat} (c : FixedByteCodec α n) :
    (k : Nat) → List AbstractByte → Option { xs : List α // xs.length = k }
  | 0, [] => some ⟨[], rfl⟩
  | 0, _ :: _ => none
  | k + 1, bs =>
    match Nat.ble n bs.length with
    | false => none
    | true =>
      match c.decode (bs.take n), decodeChunks c k (bs.drop n) with
      | some x, some ⟨xs, hxs⟩ => some ⟨x :: xs, congrArg Nat.succ hxs⟩
      | _, _ => none

theorem length_encodeElems {α : Type} {n : Nat} (c : FixedByteCodec α n) :
    ∀ xs : List α, (encodeElems c xs).length = xs.length * n
  | [] => by simp [encodeElems]
  | x :: xs => by
    simp only [encodeElems, List.length_append, c.encode_length x,
               length_encodeElems c xs, List.length_cons]
    have : (xs.length + 1) * n = n + xs.length * n := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    exact this.symm

theorem allBytesInitialized_encodeElems {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hInit : c.IsInitCodec) :
    ∀ xs : List α, allBytesInitialized (encodeElems c xs) = true
  | [] => rfl
  | x :: xs =>
    allBytesInitialized_append (hInit x) (allBytesInitialized_encodeElems hInit xs)

theorem decodeChunks_encodeElems {α : Type} {n : Nat} (c : FixedByteCodec α n) :
    ∀ (k : Nat) (xs : List α) (hLen : xs.length = k),
      decodeChunks c k (encodeElems c xs) = some ⟨xs, hLen⟩
  | 0, [], rfl => rfl
  | k + 1, x :: xs, hLen => by
    have hTail : xs.length = k := Nat.succ.inj hLen
    subst hTail
    unfold encodeElems decodeChunks
    have hGe : n ≤ (c.encode x ++ encodeElems c xs).length := by
      rw [List.length_append, c.encode_length x]
      omega
    have hBle : Nat.ble n (c.encode x ++ encodeElems c xs).length = true :=
      Nat.ble_eq_true_of_le hGe
    rw [hBle]
    dsimp only
    rw [List.take_left' (c.encode_length x), List.drop_left' (c.encode_length x),
        c.decode_encode x, decodeChunks_encodeElems c xs.length xs rfl]

theorem decodeChunks_length_eq {α : Type} {n : Nat} (c : FixedByteCodec α n) :
    ∀ {k : Nat} {bs : List AbstractByte} {res : { xs : List α // xs.length = k }},
      decodeChunks c k bs = some res → bs.length = k * n
  | 0, [], _, _ => by simp
  | 0, _ :: _, _, hDec => nomatch hDec
  | k + 1, bs, _, hDec => by
    unfold decodeChunks at hDec
    cases hBle : Nat.ble n bs.length <;> rw [hBle] at hDec
    · nomatch hDec
    · dsimp only at hDec
      cases hHead : c.decode (bs.take n) <;> rw [hHead] at hDec
      · nomatch hDec
      · cases hTail : decodeChunks c k (bs.drop n) <;> rw [hTail] at hDec
        · nomatch hDec
        case some tailSub =>
          have hLe : n ≤ bs.length := Nat.le_of_ble_eq_true hBle
          have hDropLen := decodeChunks_length_eq c hTail
          rw [List.length_drop] at hDropLen
          have hMul : (k + 1) * n = n + k * n := by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
          omega

/-- Homogeneous fixed-length list combinator of `k` elements (`k * n` bytes). -/
def listFixed {α : Type} {n : Nat} (k : Nat) (c : FixedByteCodec α n) :
    FixedByteCodec { xs : List α // xs.length = k } (k * n) :=
  ofRoundTrip
    (fun xs => encodeElems c xs.val)
    (fun bs => decodeChunks c k bs)
    (fun xs => by
      rw [length_encodeElems c xs.val, xs.property])
    (fun ⟨xs, hLen⟩ => decodeChunks_encodeElems c k xs hLen)

theorem listFixed_isExactWidth {α : Type} {n : Nat} (k : Nat) (c : FixedByteCodec α n) :
    (listFixed k c).IsExactWidth :=
  fun _ _ hDec => decodeChunks_length_eq c hDec

theorem listFixed_isInitCodec {α : Type} {n : Nat} (k : Nat)
    {c : FixedByteCodec α n} (hc : c.IsInitCodec) :
    (listFixed k c).IsInitCodec :=
  fun xs => allBytesInitialized_encodeElems hc xs.val

theorem listFixed_isSurjectiveInitDecoder {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hc : c.IsSurjectiveInitDecoder) (k : Nat) :
    (listFixed k c).IsSurjectiveInitDecoder := by
  induction k with
  | zero =>
    intro bs hLen _
    cases bs with
    | nil => exact ⟨⟨[], rfl⟩, rfl⟩
    | cons _ _ => simp at hLen
  | succ k ih =>
    intro bs hLen hInit
    have hMul : (k + 1) * n = n + k * n := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    have hLe : n ≤ bs.length := by omega
    have hBle : Nat.ble n bs.length = true := Nat.ble_eq_true_of_le hLe
    have hTakeLen : (bs.take n).length = n := by rw [List.length_take]; omega
    have hDropLen : (bs.drop n).length = k * n := by rw [List.length_drop]; omega
    rcases hc (bs.take n) hTakeLen (allBytesInitialized_take n hInit) with ⟨x, hx⟩
    rcases ih (bs.drop n) hDropLen (allBytesInitialized_drop n hInit) with ⟨⟨xs, hxs⟩, hRest⟩
    have hRestChunks : decodeChunks c k (bs.drop n) = some ⟨xs, hxs⟩ := hRest
    refine ⟨⟨x :: xs, congrArg Nat.succ hxs⟩, ?_⟩
    show decodeChunks c (k + 1) bs = some ⟨x :: xs, congrArg Nat.succ hxs⟩
    unfold decodeChunks
    rw [hBle]
    dsimp only
    rw [hx, hRestChunks]

theorem listFixed_hasZeroValid {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hc : c.HasZeroValid) (k : Nat) :
    (listFixed k c).HasZeroValid := by
  induction k with
  | zero =>
    have h0 : 0 * n = 0 := Nat.zero_mul n
    refine ⟨⟨[], rfl⟩, ?_⟩
    show decodeChunks c 0 (zeroInitBytes (0 * n)) = some ⟨[], rfl⟩
    rw [h0]
  | succ k ih =>
    rcases hc with ⟨x, hx⟩
    rcases ih with ⟨⟨xs, hxs⟩, hRest⟩
    have hRestChunks : decodeChunks c k (zeroInitBytes (k * n)) = some ⟨xs, hxs⟩ := hRest
    have hMul : (k + 1) * n = n + k * n := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    refine ⟨⟨x :: xs, congrArg Nat.succ hxs⟩, ?_⟩
    show decodeChunks c (k + 1) (zeroInitBytes ((k + 1) * n)) =
      some ⟨x :: xs, congrArg Nat.succ hxs⟩
    rw [hMul, zeroInitBytes_add n (k * n)]
    unfold decodeChunks
    have hZLen : (zeroInitBytes n).length = n := length_zeroInitBytes n
    have hGe : n ≤ (zeroInitBytes n ++ zeroInitBytes (k * n)).length := by
      rw [List.length_append, hZLen]
      omega
    have hBle : Nat.ble n (zeroInitBytes n ++ zeroInitBytes (k * n)).length = true :=
      Nat.ble_eq_true_of_le hGe
    rw [hBle]
    dsimp only
    rw [List.take_left' hZLen, List.drop_left' hZLen, hx, hRestChunks]

/-- Bridge from `encodeListWith` in `Trusted` to `encodeElems` / `listFixed`. -/
theorem encodeListWith_map_eq_encodeElems {α : Type} {n : Nat}
    (c : FixedByteCodec α n)
    (toVal : α → Value)
    (encVal : Value → Option (List AbstractByte))
    (hEnc : ∀ x : α, encVal (toVal x) = some (c.encode x)) :
    ∀ xs : List α,
      encodeListWith encVal n (xs.map toVal) = some (encodeElems c xs)
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, encodeListWith, hEnc x]
    have hBeq : Nat.beq (Trusted.Sequence.length (c.encode x)) n = true :=
      Nat.beq_eq.mpr (c.encode_length x)
    rw [hBeq]
    dsimp only
    rw [encodeListWith_map_eq_encodeElems c toVal encVal hEnc xs]
    dsimp only
    rw [appendAbstractBytes_eq_append]

/-- Bridge from `decodeArrayChunksWith` in `Trusted` to `decodeChunks` / `listFixed`. -/
theorem decodeArrayChunksWith_eq_listFixed_map {α : Type} {n : Nat}
    (c : FixedByteCodec α n)
    (toVal : α → Value)
    (decVal : List AbstractByte → Option Value)
    (hDec : ∀ chunk : List AbstractByte, decVal chunk = (c.decode chunk).map toVal) :
    ∀ (k : Nat) (bs : List AbstractByte),
      decodeArrayChunksWith decVal n k bs =
        ((listFixed k c).decode bs).map (fun xs => xs.val.map toVal)
  | 0, [] => rfl
  | 0, _ :: _ => rfl
  | k + 1, bs => by
    show
      decodeArrayChunksWith decVal n (k + 1) bs =
        (decodeChunks c (k + 1) bs).map (fun xs => xs.val.map toVal)
    unfold decodeArrayChunksWith decodeChunks
    have hLenDef : Trusted.Sequence.length bs = bs.length := rfl
    rw [hLenDef]
    cases hBle : Nat.ble n bs.length
    · rfl
    · dsimp only
      rw [takeAbstractBytes_eq_take, dropAbstractBytes_eq_drop, hDec (bs.take n)]
      have ih := decodeArrayChunksWith_eq_listFixed_map c toVal decVal hDec k (bs.drop n)
      have hSubEq : decodeChunks c k (bs.drop n) = (listFixed k c).decode (bs.drop n) := rfl
      rw [hSubEq, ih]
      cases c.decode (bs.take n) <;> cases (listFixed k c).decode (bs.drop n) <;> rfl

/-- Homogeneous fixed-length `Vector α k` combinator (`[T; k]`, `k * n` bytes). -/
def array {α : Type} {n : Nat} (k : Nat) (c : FixedByteCodec α n) :
    FixedByteCodec (Vector α k) (k * n) :=
  (listFixed k c).mapEquiv
    (fun xs => Vector.mk xs.val.toArray (by rw [List.size_toArray, xs.property]))
    (fun v => ⟨v.toList, v.length_toList⟩)
    (fun ⟨xs, hxs⟩ => Subtype.ext (by simp [Vector.toList]))
    (fun v => by
      cases v with
      | mk arr hSize =>
        simp [Vector.toList])

theorem array_isExactWidth {α : Type} {n : Nat} (k : Nat) (c : FixedByteCodec α n) :
    (array k c).IsExactWidth :=
  mapEquiv_isExactWidth _ _ _ _ _ (listFixed_isExactWidth k c)

theorem array_isInitCodec {α : Type} {n : Nat} (k : Nat)
    {c : FixedByteCodec α n} (hc : c.IsInitCodec) :
    (array k c).IsInitCodec :=
  mapEquiv_isInitCodec _ _ _ _ _ (listFixed_isInitCodec k hc)

theorem array_isSurjectiveInitDecoder {α : Type} {n : Nat} (k : Nat)
    {c : FixedByteCodec α n} (hc : c.IsSurjectiveInitDecoder) :
    (array k c).IsSurjectiveInitDecoder :=
  mapEquiv_isSurjectiveInitDecoder _ _ _ _ _ (listFixed_isSurjectiveInitDecoder hc k)

theorem array_hasZeroValid {α : Type} {n : Nat} (k : Nat)
    {c : FixedByteCodec α n} (hc : c.HasZeroValid) :
    (array k c).HasZeroValid :=
  mapEquiv_hasZeroValid _ _ _ _ _ (listFixed_hasZeroValid hc k)

/-- Negative propagation: if the head chunk `bs.take n` fails `c.decode`, `listFixed (k + 1) c` returns `none`. -/
theorem listFixed_decode_eq_none_of_head_none {α : Type} {n : Nat}
    (k : Nat) (c : FixedByteCodec α n) {bs : List AbstractByte}
    (hHead : c.decode (bs.take n) = none) :
    (listFixed (k + 1) c).decode bs = none := by
  show decodeChunks c (k + 1) bs = none
  unfold decodeChunks
  cases Nat.ble n bs.length
  · rfl
  · dsimp only
    rw [hHead]

/-- Negative propagation: if any tail suffix `bs.drop n` fails `listFixed k c`, `listFixed (k + 1) c` returns `none`. -/
theorem listFixed_decode_eq_none_of_tail_none {α : Type} {n : Nat}
    (k : Nat) (c : FixedByteCodec α n) {bs : List AbstractByte}
    (hTail : (listFixed k c).decode (bs.drop n) = none) :
    (listFixed (k + 1) c).decode bs = none := by
  show decodeChunks c (k + 1) bs = none
  have hTailChunks : decodeChunks c k (bs.drop n) = none := hTail
  unfold decodeChunks
  cases Nat.ble n bs.length
  · rfl
  · dsimp only
    cases c.decode (bs.take n) <;> rw [hTailChunks]

/-- Negative propagation from `listFixed k c` to `array k c`. -/
theorem array_decode_eq_none_of_listFixed_none {α : Type} {n : Nat}
    (k : Nat) (c : FixedByteCodec α n) {bs : List AbstractByte}
    (hNone : (listFixed k c).decode bs = none) :
    (array k c).decode bs = none := by
  unfold array mapEquiv ofRoundTrip
  dsimp only
  rw [hNone]
  rfl

/-! ### Niche Refinement (`refineNiche`), `scalarValidRange`, and `enumRepr` -/

/--
Refine a `FixedByteCodec α n` by a decidable `Bool` bit-validity invariant `P`,
decoding into `{ x : α // P x = true }` and rejecting values with `P x = false`.
-/
def refineNiche {α : Type} {n : Nat} (c : FixedByteCodec α n) (P : α → Bool) :
    FixedByteCodec { x : α // P x = true } n :=
  ofRoundTrip
    (fun sub => c.encode sub.val)
    (fun bs =>
      match c.decode bs with
      | none => none
      | some x => if h : P x = true then some ⟨x, h⟩ else none)
    (fun sub => c.encode_length sub.val)
    (fun ⟨x, hx⟩ => by
      dsimp only
      rw [c.decode_encode x]
      simp only [hx, ↓reduceDIte])

theorem refineNiche_isExactWidth {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (P : α → Bool) (hExact : c.IsExactWidth) :
    (c.refineNiche P).IsExactWidth := by
  intro bs _ hDec
  unfold refineNiche ofRoundTrip at hDec
  dsimp only at hDec
  cases hCDec : c.decode bs <;> rw [hCDec] at hDec
  · nomatch hDec
  · exact hExact hCDec

theorem refineNiche_isInitCodec {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (P : α → Bool) (hInit : c.IsInitCodec) :
    (c.refineNiche P).IsInitCodec :=
  fun sub => hInit sub.val

/-- Negative rejection law: if `c.decode bs = some x` and `P x = false`, `refineNiche` returns `none`. -/
theorem refineNiche_decode_rejects_false {α : Type} {n : Nat}
    (c : FixedByteCodec α n) (P : α → Bool)
    {bs : List AbstractByte} {x : α}
    (hDec : c.decode bs = some x) (hFalse : P x = false) :
    (c.refineNiche P).decode bs = none := by
  unfold refineNiche ofRoundTrip
  dsimp only
  rw [hDec]
  simp only [hFalse, Bool.false_eq_true, ↓reduceDIte]

/-- Negative rejection law: if `c.decode bs = none`, `refineNiche` also returns `none`. -/
theorem refineNiche_decode_none_of_decode_none {α : Type} {n : Nat}
    (c : FixedByteCodec α n) (P : α → Bool)
    {bs : List AbstractByte} (hNone : c.decode bs = none) :
    (c.refineNiche P).decode bs = none := by
  unfold refineNiche ofRoundTrip
  dsimp only
  rw [hNone]

/-- Exact characterization of when `(c.refineNiche P).decode bs = none`. -/
theorem refineNiche_decode_eq_none_iff {α : Type} {n : Nat}
    (c : FixedByteCodec α n) (P : α → Bool) (bs : List AbstractByte) :
    (c.refineNiche P).decode bs = none ↔
      (c.decode bs = none ∨ ∃ x : α, c.decode bs = some x ∧ P x = false) := by
  unfold refineNiche ofRoundTrip
  dsimp only
  cases hDec : c.decode bs with
  | none => simp
  | some x =>
    cases hP : P x with
    | false =>
      simp [hP]
    | true =>
      simp [hP]

/-- Any `IsInitCodec` refined by a predicate that rejects at least one `bad : α` is NOT `IsSurjectiveInitDecoder`. -/
theorem refineNiche_not_isSurjectiveInitDecoder {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (P : α → Bool)
    (hInit : c.IsInitCodec) {bad : α} (hBad : P bad = false) :
    ¬ (c.refineNiche P).IsSurjectiveInitDecoder := by
  intro hSurj
  rcases hSurj (c.encode bad) (c.encode_length bad) (hInit bad) with ⟨y, hy⟩
  rw [refineNiche_decode_rejects_false c P (c.decode_encode bad) hBad] at hy
  nomatch hy

theorem refineNiche_hasZeroValid_of {α : Type} {n : Nat}
    (c : FixedByteCodec α n) (P : α → Bool)
    {x₀ : α} (hZero : c.decode (zeroInitBytes n) = some x₀) (hP : P x₀ = true) :
    (c.refineNiche P).HasZeroValid := by
  refine ⟨⟨x₀, hP⟩, ?_⟩
  unfold refineNiche ofRoundTrip
  dsimp only
  rw [hZero]
  simp only [hP, ↓reduceDIte]

/--
Compiler scalar niche codec enforcing `WrappingRange` validity (`NonZero*`,
bounded enum tags, `char`-like scalar subranges) on `sz`-byte little-endian integers.
-/
def scalarValidRange (sz : Nat) (hNz : 0 < sz) (range : WrappingRange) :
    FixedByteCodec
      { bits : Nat // bits < 2 ^ (8 * sz) ∧ wrappingRangeContains range bits = true }
      sz :=
  ((uintBitsLE sz hNz).refineNiche (fun x => wrappingRangeContains range x.val)).mapEquiv
    (fun sub => ⟨sub.val.val, sub.val.property, sub.property⟩)
    (fun sub => ⟨⟨sub.val, sub.property.1⟩, sub.property.2⟩)
    (fun ⟨⟨_, _⟩, _⟩ => rfl)
    (fun ⟨_, _, _⟩ => rfl)

theorem scalarValidRange_isExactWidth (sz : Nat) (hNz : 0 < sz) (range : WrappingRange) :
    (scalarValidRange sz hNz range).IsExactWidth :=
  mapEquiv_isExactWidth _ _ _ _ _
    (refineNiche_isExactWidth _ (uintBitsLE_isExactWidth sz hNz))

theorem scalarValidRange_isInitCodec (sz : Nat) (hNz : 0 < sz) (range : WrappingRange) :
    (scalarValidRange sz hNz range).IsInitCodec :=
  mapEquiv_isInitCodec _ _ _ _ _
    (refineNiche_isInitCodec _ (uintBitsLE_isInitCodec sz hNz))

/-- `scalarValidRange` rejects any `sz`-byte integer whose bit pattern lies outside `range`. -/
theorem scalarValidRange_decode_rejects_out_of_range
    (sz : Nat) (hNz : 0 < sz) (range : WrappingRange)
    {bits : Nat} (hLt : bits < 2 ^ (8 * sz))
    (hOut : wrappingRangeContains range bits = false) :
    (scalarValidRange sz hNz range).decode (encodeLittleEndianBytes bits sz none) = none := by
  unfold scalarValidRange mapEquiv ofRoundTrip
  dsimp only
  have hBase : (uintBitsLE sz hNz).decode (encodeLittleEndianBytes bits sz none) =
      some ⟨bits, hLt⟩ :=
    (uintBitsLE sz hNz).decode_encode ⟨bits, hLt⟩
  rw [refineNiche_decode_rejects_false (uintBitsLE sz hNz)
      (fun x => wrappingRangeContains range x.val) hBase hOut]
  rfl

/-- Kernel-reducing predicate classifying non-pointer `PrimitiveKind`s (`.int` and `.float`)
that decode to `Value.scalar` in `decodeScalarLayoutBytes`.

Note: `.pointer _` is intentionally excluded here because `decodeScalarLayoutBytes`
decodes pointer layouts to `Value.ptr` (incorporating byte-level provenance `(allocId, tag)`),
rather than `Value.scalar`. -/
@[reducible]
def isNonPointerPrimitiveKind : PrimitiveKind → Bool
  | .int _ _ | .float _ => true
  | .pointer _ => false

/--
Exact pointwise bridge between `scalarValidRange` and `Trusted`'s
`decodeScalarLayoutBytes (.initialized pk range)` for any non-pointer
`PrimitiveKind` (`.int bitsWidth signed` or `.float bitsWidth`).

Pointer `PrimitiveKind`s (`.pointer _`) decode to `Value.ptr` using byte
provenance rather than `Value.scalar` and are therefore out of scope of
scalar bit-pattern codecs.
-/
theorem decodeScalarLayoutBytes_initialized_nonPtr_eq_scalarValidRange_map
    (pk : PrimitiveKind) (range : WrappingRange)
    (sz : Nat) (hNz : 0 < sz)
    (hNonPtr : isNonPointerPrimitiveKind pk = true)
    (hWidth : primitiveKindByteWidth pk = some sz)
    (bs : List AbstractByte) :
    decodeScalarLayoutBytes (.initialized pk range) bs =
      ((scalarValidRange sz hNz range).decode bs).map
        (fun x => Value.scalar ⟨x.val, sz⟩) := by
  unfold decodeScalarLayoutBytes scalarLayoutByteWidth
  dsimp only
  rw [hWidth]
  dsimp only
  unfold scalarValidRange mapEquiv refineNiche uintBitsLE ofRoundTrip
  dsimp only
  have hLenDef : Trusted.Sequence.length bs = bs.length := rfl
  rw [hLenDef]
  cases hLen : Nat.beq bs.length sz
  · rfl
  · have hLenEq : bs.length = sz := Nat.eq_of_beq_eq_true hLen
    have hNonEmpty : Nat.beq (Trusted.Sequence.length bs) 0 = false := by
      rw [hLenDef, hLenEq]
      exact nat_beq_eq_false_of_ne (by omega)
    dsimp only
    unfold decodeScalarBytes
    dsimp only
    rw [hNonEmpty]
    dsimp only
    cases hLE : decodeLittleEndianBytes bs with
    | none => rfl
    | some bp =>
      rcases bp with ⟨bits, prov⟩
      have hModLt := decodeLittleEndianBytes_lt_scalarModulus bs bits prov hLE
      have hLt : bits < 2 ^ (8 * sz) := by
        rw [hLenDef, hLenEq, Anneal.Scalars.scalarModulus_eq_two_pow] at hModLt
        exact hModLt
      dsimp only
      simp only [hLt, ↓reduceDIte]
      rw [hLenDef, hLenEq]
      by_cases hRange : wrappingRangeContains range bits = true
      · simp only [hRange, ↓reduceDIte, Option.map_some]
        cases pk with
        | int _ _ => rfl
        | float _ => rfl
        | pointer _ => nomatch hNonPtr
      · have hFalse : wrappingRangeContains range bits = false :=
          Bool.eq_false_iff.mpr hRange
        simp [hFalse]

/--
Specialization of `decodeScalarLayoutBytes_initialized_nonPtr_eq_scalarValidRange_map`
to integer `PrimitiveKind.int bitsWidth signed`.
-/
theorem decodeScalarLayoutBytes_initialized_int_eq_scalarValidRange_map
    (bitsWidth : Nat) (signed : Bool) (range : WrappingRange)
    (sz : Nat) (hNz : 0 < sz)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some sz)
    (bs : List AbstractByte) :
    decodeScalarLayoutBytes (.initialized (.int bitsWidth signed) range) bs =
      ((scalarValidRange sz hNz range).decode bs).map
        (fun x => Value.scalar ⟨x.val, sz⟩) :=
  decodeScalarLayoutBytes_initialized_nonPtr_eq_scalarValidRange_map
    (.int bitsWidth signed) range sz hNz rfl hWidth bs

/--
Codec for a fieldless `#[repr(u8/u16/u32/u64)]` enum `ε` with discriminant map
`toTag : ε → Nat` and partial inverse `ofTag : Nat → Option ε`.

Decoding enforces canonical discriminant round-tripping (`Nat.beq (toTag e) x.val`),
so even if `ofTag` maps an unused/non-canonical tag `t` to some variant `e` with
`toTag e ≠ t`, `decode` still rejects `t` with `none`.
-/
def enumRepr (sz : Nat) (hNz : 0 < sz) {ε : Type}
    (toTag : ε → Nat)
    (ofTag : Nat → Option ε)
    (hRound : ∀ e : ε, ofTag (toTag e) = some e)
    (hBounds : ∀ e : ε, toTag e < 2 ^ (8 * sz)) :
    FixedByteCodec ε sz :=
  ofRoundTrip
    (fun e => (uintBitsLE sz hNz).encode ⟨toTag e, hBounds e⟩)
    (fun bs =>
      ((uintBitsLE sz hNz).decode bs).bind (fun x =>
        match ofTag x.val with
        | some e => if Nat.beq (toTag e) x.val then some e else none
        | none => none))
    (fun e => (uintBitsLE sz hNz).encode_length ⟨toTag e, hBounds e⟩)
    (fun e => by
      change
        (((uintBitsLE sz hNz).decode ((uintBitsLE sz hNz).encode ⟨toTag e, hBounds e⟩)).bind _) =
          some e
      rw [(uintBitsLE sz hNz).decode_encode ⟨toTag e, hBounds e⟩]
      unfold Option.bind
      dsimp only
      rw [hRound e]
      dsimp only
      rw [nat_beq_self (toTag e)]
      rfl)

theorem enumRepr_isExactWidth (sz : Nat) (hNz : 0 < sz) {ε : Type}
    (toTag : ε → Nat) (ofTag : Nat → Option ε)
    (hRound : ∀ e, ofTag (toTag e) = some e)
    (hBounds : ∀ e, toTag e < 2 ^ (8 * sz)) :
    (enumRepr sz hNz toTag ofTag hRound hBounds).IsExactWidth := by
  intro bs _ hDec
  unfold enumRepr ofRoundTrip at hDec
  dsimp only at hDec
  cases hBase : (uintBitsLE sz hNz).decode bs <;> rw [hBase] at hDec
  · nomatch hDec
  · exact uintBitsLE_isExactWidth sz hNz hBase

theorem enumRepr_isInitCodec (sz : Nat) (hNz : 0 < sz) {ε : Type}
    (toTag : ε → Nat) (ofTag : Nat → Option ε)
    (hRound : ∀ e, ofTag (toTag e) = some e)
    (hBounds : ∀ e, toTag e < 2 ^ (8 * sz)) :
    (enumRepr sz hNz toTag ofTag hRound hBounds).IsInitCodec :=
  fun e => uintBitsLE_isInitCodec sz hNz ⟨toTag e, hBounds e⟩

/-- Exact canonical characterization of `enumRepr.decode`: `bs` decodes to `some e`
if and only if `uintBitsLE` decodes `bs` to the canonical discriminant `toTag e`. -/
theorem enumRepr_decode_eq_some_iff (sz : Nat) (hNz : 0 < sz) {ε : Type}
    (toTag : ε → Nat) (ofTag : Nat → Option ε)
    (hRound : ∀ e, ofTag (toTag e) = some e)
    (hBounds : ∀ e, toTag e < 2 ^ (8 * sz))
    (bs : List AbstractByte) (e : ε) :
    (enumRepr sz hNz toTag ofTag hRound hBounds).decode bs = some e ↔
      (uintBitsLE sz hNz).decode bs = some ⟨toTag e, hBounds e⟩ := by
  unfold enumRepr ofRoundTrip
  dsimp only
  constructor
  · intro hDec
    cases hBase : (uintBitsLE sz hNz).decode bs <;> rw [hBase] at hDec
    · nomatch hDec
    case some x =>
      dsimp only [Option.bind] at hDec
      cases hOf : ofTag x.val <;> rw [hOf] at hDec
      · nomatch hDec
      case some e' =>
        dsimp only at hDec
        cases hEqTag : Nat.beq (toTag e') x.val <;> rw [hEqTag] at hDec
        · nomatch hDec
        · simp only [↓reduceIte, Option.some.injEq] at hDec
          subst hDec
          have hValEq : x.val = toTag e' := (Nat.eq_of_beq_eq_true hEqTag).symm
          exact congrArg some (Subtype.ext hValEq)
  · intro hBase
    rw [hBase]
    dsimp only [Option.bind]
    rw [hRound e]
    dsimp only
    rw [nat_beq_self (toTag e)]
    rfl

/-- `enumRepr` rejects any byte sequence whose decoded discriminant `bits` has `ofTag bits = none`. -/
theorem enumRepr_decode_rejects_invalid_tag (sz : Nat) (hNz : 0 < sz) {ε : Type}
    (toTag : ε → Nat) (ofTag : Nat → Option ε)
    (hRound : ∀ e, ofTag (toTag e) = some e)
    (hBounds : ∀ e, toTag e < 2 ^ (8 * sz))
    {bits : Nat} (hLt : bits < 2 ^ (8 * sz)) (hInvalid : ofTag bits = none) :
    (enumRepr sz hNz toTag ofTag hRound hBounds).decode
        (encodeLittleEndianBytes bits sz none) = none := by
  unfold enumRepr ofRoundTrip
  dsimp only
  have hBase := (uintBitsLE sz hNz).decode_encode ⟨bits, hLt⟩
  change (((uintBitsLE sz hNz).decode ((uintBitsLE sz hNz).encode ⟨bits, hLt⟩)).bind _) = none
  rw [hBase]
  dsimp only [Option.bind]
  rw [hInvalid]

/-- `enumRepr` rejects any non-canonical discriminant `bits` (`∀ e, toTag e ≠ bits`),
even if `ofTag bits` leniently returns `some e`. -/
theorem enumRepr_decode_rejects_non_canonical_tag (sz : Nat) (hNz : 0 < sz) {ε : Type}
    (toTag : ε → Nat) (ofTag : Nat → Option ε)
    (hRound : ∀ e, ofTag (toTag e) = some e)
    (hBounds : ∀ e, toTag e < 2 ^ (8 * sz))
    {bits : Nat} (hLt : bits < 2 ^ (8 * sz))
    (hNonCanon : ∀ e : ε, toTag e ≠ bits) :
    (enumRepr sz hNz toTag ofTag hRound hBounds).decode
        (encodeLittleEndianBytes bits sz none) = none := by
  cases hDec : (enumRepr sz hNz toTag ofTag hRound hBounds).decode
      (encodeLittleEndianBytes bits sz none) with
  | none => rfl
  | some e =>
    have hSome := (enumRepr_decode_eq_some_iff sz hNz toTag ofTag hRound hBounds
      (encodeLittleEndianBytes bits sz none) e).mp hDec
    have hBase : (uintBitsLE sz hNz).decode (encodeLittleEndianBytes bits sz none) =
        some ⟨bits, hLt⟩ :=
      (uintBitsLE sz hNz).decode_encode ⟨bits, hLt⟩
    rw [hBase] at hSome
    injection hSome with hSub
    have hTagEq : bits = toTag e := congrArg Subtype.val hSub
    exact False.elim (hNonCanon e hTagEq.symm)

/-- A fieldless `enumRepr` codec satisfies `HasZeroValid` (`FromZeros`) if and only if `0` is a discriminant. -/
theorem enumRepr_hasZeroValid_iff (sz : Nat) (hNz : 0 < sz) {ε : Type}
    (toTag : ε → Nat) (ofTag : Nat → Option ε)
    (hRound : ∀ e, ofTag (toTag e) = some e)
    (hBounds : ∀ e, toTag e < 2 ^ (8 * sz)) :
    (enumRepr sz hNz toTag ofTag hRound hBounds).HasZeroValid ↔ ∃ e₀ : ε, toTag e₀ = 0 := by
  unfold HasZeroValid
  constructor
  · rintro ⟨e₀, hDec⟩
    have hSome := (enumRepr_decode_eq_some_iff sz hNz toTag ofTag hRound hBounds
      (zeroInitBytes sz) e₀).mp hDec
    rw [uintBitsLE_decode_zeroInitBytes sz hNz] at hSome
    injection hSome with hSub
    exact ⟨e₀, (congrArg Subtype.val hSub).symm⟩
  · rintro ⟨e₀, hTag0⟩
    refine ⟨e₀, (enumRepr_decode_eq_some_iff sz hNz toTag ofTag hRound hBounds
      (zeroInitBytes sz) e₀).mpr ?_⟩
    rw [uintBitsLE_decode_zeroInitBytes sz hNz]
    exact congrArg some (Subtype.ext hTag0.symm)

/-- Convenient constructor for `enumRepr` `HasZeroValid` from a zero-discriminant variant `e₀`. -/
theorem enumRepr_hasZeroValid_of (sz : Nat) (hNz : 0 < sz) {ε : Type}
    (toTag : ε → Nat) (ofTag : Nat → Option ε)
    (hRound : ∀ e, ofTag (toTag e) = some e)
    (hBounds : ∀ e, toTag e < 2 ^ (8 * sz))
    (e₀ : ε) (hTag0 : toTag e₀ = 0) :
    (enumRepr sz hNz toTag ofTag hRound hBounds).HasZeroValid :=
  (enumRepr_hasZeroValid_iff sz hNz toTag ofTag hRound hBounds).mpr ⟨e₀, hTag0⟩

/-- If some `sz`-byte bit pattern `bits < 2 ^ (8 * sz)` has no corresponding enum variant,
`enumRepr` is NOT `IsSurjectiveInitDecoder` (hence not `FromBytes`). -/
theorem enumRepr_not_isSurjectiveInitDecoder (sz : Nat) (hNz : 0 < sz) {ε : Type}
    (toTag : ε → Nat) (ofTag : Nat → Option ε)
    (hRound : ∀ e, ofTag (toTag e) = some e)
    (hBounds : ∀ e, toTag e < 2 ^ (8 * sz))
    {bits : Nat} (hLt : bits < 2 ^ (8 * sz))
    (hMissing : ∀ e : ε, toTag e ≠ bits) :
    ¬ (enumRepr sz hNz toTag ofTag hRound hBounds).IsSurjectiveInitDecoder := by
  intro hSurj
  let bs := encodeLittleEndianBytes bits sz none
  rcases hSurj bs
      (length_encodeLittleEndianBytes none sz bits)
      (allBytesInitialized_encodeLittleEndianBytes none sz bits) with ⟨e, hDec⟩
  rw [enumRepr_decode_rejects_non_canonical_tag sz hNz toTag ofTag hRound hBounds hLt hMissing]
    at hDec
  nomatch hDec

/-- Conversely, if every `bits < 2 ^ (8 * sz)` is realized by some variant (e.g., a 256-variant
`#[repr(u8)]` enum), `enumRepr` IS `IsSurjectiveInitDecoder` (`FromBytes`). -/
theorem enumRepr_isSurjectiveInitDecoder (sz : Nat) (hNz : 0 < sz) {ε : Type}
    (toTag : ε → Nat) (ofTag : Nat → Option ε)
    (hRound : ∀ e, ofTag (toTag e) = some e)
    (hBounds : ∀ e, toTag e < 2 ^ (8 * sz))
    (hCover : ∀ bits : Nat, bits < 2 ^ (8 * sz) → ∃ e : ε, toTag e = bits) :
    (enumRepr sz hNz toTag ofTag hRound hBounds).IsSurjectiveInitDecoder := by
  intro bs hLen hInit
  rcases uintBitsLE_isSurjectiveInitDecoder sz hNz bs hLen hInit with ⟨⟨bits, hLt⟩, hBase⟩
  rcases hCover bits hLt with ⟨e, hTagEq⟩
  refine ⟨e, (enumRepr_decode_eq_some_iff sz hNz toTag ofTag hRound hBounds bs e).mpr ?_⟩
  rw [hBase]
  exact congrArg some (Subtype.ext hTagEq.symm)

end FixedByteCodec

/-! ## 4. `MirValueCodec` and `Anneal.BitValidity` Marker-Trait / `transmute_sound` Bridges -/

/--
Typed bridge connecting a `FixedByteCodec α sz` to Anneal's MIR operational
byte codec (`encodeValueToBytes defaultCodecFuel layouts ty` and
`decodeValueFromBytes defaultCodecFuel layouts ty`).
-/
structure MirValueCodec (layouts : LayoutTable) (ty : Ty) (α : Type) (sz : Nat) : Type where
  /-- Underlying prefix-free `sz`-byte codec. -/
  codec : FixedByteCodec α sz
  /-- Embed typed value `α` into runtime `Value`. -/
  toValue : α → Value
  /-- Partial projection from runtime `Value` back to `α`. -/
  ofValue : Value → Option α
  /-- `ofValue` is a left inverse to `toValue`. -/
  ofValue_toValue : ∀ x : α, ofValue (toValue x) = some x
  /-- `ty` has byte size `sz` in `layouts`. -/
  tySize_eq : rigidTyByteSize layouts ty = some sz
  /-- Encoding `toValue x` at `ty` produces `codec.encode x`. -/
  encode_toValue :
    ∀ x : α,
      encodeValueToBytes defaultCodecFuel layouts ty (toValue x) = some (codec.encode x)
  /-- Whether `encodeValueToBytes` at `ty` checks exact field widths on arbitrary untyped `Value`s
      (true for scalars, arrays, laid-out tuples, `.primitive` ADTs, and `.multiple` fieldless enums;
      false on unparameterized `.adt defPath []` newtypes with `FieldsShape.arbitrary` where
      `encodeValueToBytes` delegates untyped field values to `encodeUntypedValueToBytes`). -/
  enforcesUntypedFieldWidths : Bool := true
  /-- Whenever `enforcesUntypedFieldWidths = true` and `codec` is `IsInitCodec`,
      every `Value` encoded at `ty` produces `sz` initialized bytes. -/
  encode_length_and_init_of_isInit :
    enforcesUntypedFieldWidths = true →
    codec.IsInitCodec →
    ∀ (v : Value) (bs : List AbstractByte),
      encodeValueToBytes defaultCodecFuel layouts ty v = some bs →
      bs.length = sz ∧ allBytesInitialized bs = true
  /-- Decoding at `ty` agrees pointwise with `(codec.decode bs).map toValue`. -/
  decode_eq_map :
    ∀ bs : List AbstractByte,
      decodeValueFromBytes defaultCodecFuel layouts ty bs = (codec.decode bs).map toValue

namespace MirValueCodec

/--
Smart constructor for `MirValueCodec` when every successful `encodeValueToBytes`
at `ty` emits `codec.encode x` for some `x : α`.
-/
def ofCanonicalEncode {layouts : LayoutTable} {ty : Ty} {α : Type} {sz : Nat}
    (codec : FixedByteCodec α sz)
    (toValue : α → Value)
    (ofValue : Value → Option α)
    (ofValue_toValue : ∀ x : α, ofValue (toValue x) = some x)
    (tySize_eq : rigidTyByteSize layouts ty = some sz)
    (encode_toValue :
      ∀ x : α,
        encodeValueToBytes defaultCodecFuel layouts ty (toValue x) = some (codec.encode x))
    (encode_witness :
      ∀ (v : Value) (bs : List AbstractByte),
        encodeValueToBytes defaultCodecFuel layouts ty v = some bs →
        ∃ x : α, bs = codec.encode x)
    (decode_eq_map :
      ∀ bs : List AbstractByte,
        decodeValueFromBytes defaultCodecFuel layouts ty bs = (codec.decode bs).map toValue) :
    MirValueCodec layouts ty α sz where
  codec := codec
  toValue := toValue
  ofValue := ofValue
  ofValue_toValue := ofValue_toValue
  tySize_eq := tySize_eq
  encode_toValue := encode_toValue
  enforcesUntypedFieldWidths := true
  encode_length_and_init_of_isInit := fun _ hInit v bs hEnc => by
    rcases encode_witness v bs hEnc with ⟨x, rfl⟩
    exact ⟨codec.encode_length x, hInit x⟩
  decode_eq_map := decode_eq_map

/-- Exact `decodeValueFromBytes` characterization via `codec.decode`. -/
theorem decodeValue_eq_some_iff {layouts : LayoutTable} {ty : Ty} {α : Type} {sz : Nat}
    (m : MirValueCodec layouts ty α sz)
    (hInj : ∀ ⦃x y : α⦄, m.toValue x = m.toValue y → x = y)
    (bs : List AbstractByte) (x : α) :
    decodeValueFromBytes defaultCodecFuel layouts ty bs = some (m.toValue x) ↔
      m.codec.decode bs = some x := by
  rw [m.decode_eq_map bs]
  cases hDec : m.codec.decode bs with
  | none => simp
  | some y =>
    simp only [Option.map_some, Option.some.injEq]
    exact ⟨fun hEq => congrArg some (hInj hEq) |> Option.some.inj,
           fun hEq => congrArg m.toValue hEq⟩

/-- Every `MirValueCodec` witnesses `IsTryFromBytes` with validity predicate `∃ x, m.toValue x = v`. -/
theorem isTryFromBytes {layouts : LayoutTable} {ty : Ty} {α : Type} {sz : Nat}
    (m : MirValueCodec layouts ty α sz) :
    IsTryFromBytes layouts ty (fun v => ∃ x : α, m.toValue x = v ∧ m.ofValue v = some x) := by
  refine ⟨sz, m.tySize_eq, ?_⟩
  intro bs v hDec
  rw [m.decode_eq_map bs] at hDec
  cases hC : m.codec.decode bs <;> rw [hC] at hDec
  · nomatch hDec
  case some x =>
    injection hDec with hV
    subst hV
    exact ⟨x, rfl, m.ofValue_toValue x⟩

/-- Lift any typed invariant `valid : Value → Prop` holding on `m.toValue` to `IsTryFromBytes`. -/
theorem isTryFromBytes_of {layouts : LayoutTable} {ty : Ty} {α : Type} {sz : Nat}
    (m : MirValueCodec layouts ty α sz) {valid : Value → Prop}
    (hValid : ∀ x : α, valid (m.toValue x)) :
    IsTryFromBytes layouts ty valid := by
  rcases m.isTryFromBytes with ⟨sz', hSz', hDec⟩
  refine ⟨sz', hSz', fun bs v hD => ?_⟩
  rcases hDec bs v hD with ⟨x, rfl, _⟩
  exact hValid x

/-- Unconditional `IsTryFromBytes layouts ty` (default `True` predicate). -/
theorem isTryFromBytes_trivial {layouts : LayoutTable} {ty : Ty} {α : Type} {sz : Nat}
    (m : MirValueCodec layouts ty α sz) :
    IsTryFromBytes layouts ty :=
  ⟨sz, m.tySize_eq, fun _ _ _ => trivial⟩

/-- `HasZeroValid` on `m.codec` lifts to `IsFromZeros layouts ty`. -/
theorem isFromZeros {layouts : LayoutTable} {ty : Ty} {α : Type} {sz : Nat}
    (m : MirValueCodec layouts ty α sz) (hZero : m.codec.HasZeroValid) :
    IsFromZeros layouts ty := by
  rcases hZero with ⟨x, hx⟩
  refine ⟨sz, m.toValue x, m.tySize_eq, ?_⟩
  rw [m.decode_eq_map (zeroInitBytes sz), hx]
  rfl

/-- `IsSurjectiveInitDecoder` on `m.codec` lifts to `IsFromBytes layouts ty`. -/
theorem isFromBytes {layouts : LayoutTable} {ty : Ty} {α : Type} {sz : Nat}
    (m : MirValueCodec layouts ty α sz) (hSurj : m.codec.IsSurjectiveInitDecoder) :
    IsFromBytes layouts ty := by
  refine ⟨sz, m.tySize_eq, ?_⟩
  intro bs hLen hInit
  rcases hSurj bs hLen hInit with ⟨x, hx⟩
  refine ⟨m.toValue x, ?_⟩
  rw [m.decode_eq_map bs, hx]
  rfl

/-- `IsInitCodec` on `m.codec` lifts to `IsIntoBytes layouts ty` whenever `m` enforces untyped field widths. -/
theorem isIntoBytes {layouts : LayoutTable} {ty : Ty} {α : Type} {sz : Nat}
    (m : MirValueCodec layouts ty α sz) (hInit : m.codec.IsInitCodec)
    (hWidths : m.enforcesUntypedFieldWidths = true := by rfl) :
    IsIntoBytes layouts ty :=
  ⟨sz, m.tySize_eq, m.encode_length_and_init_of_isInit hWidths hInit⟩

/-- Negative bridge: if `zeroInitBytes sz` fails `m.codec.decode`, `ty` is NOT `IsFromZeros`. -/
theorem not_isFromZeros_of_zero_none {layouts : LayoutTable} {ty : Ty} {α : Type} {sz : Nat}
    (m : MirValueCodec layouts ty α sz)
    (hNone : m.codec.decode (zeroInitBytes sz) = none) :
    ¬ IsFromZeros layouts ty := by
  rintro ⟨sz', v, hSz', hDec⟩
  rw [m.tySize_eq] at hSz'
  injection hSz' with hEq
  subst hEq
  rw [m.decode_eq_map (zeroInitBytes sz), hNone] at hDec
  nomatch hDec

/-- Negative bridge: if an initialized `sz`-byte sequence fails `m.codec.decode`, `ty` is NOT `IsFromBytes`. -/
theorem not_isFromBytes_of_rejected_init {layouts : LayoutTable} {ty : Ty} {α : Type} {sz : Nat}
    (m : MirValueCodec layouts ty α sz)
    {bs : List AbstractByte} (hLen : bs.length = sz)
    (hInit : allBytesInitialized bs = true) (hNone : m.codec.decode bs = none) :
    ¬ IsFromBytes layouts ty := by
  rintro ⟨sz', hSz', hDec⟩
  rw [m.tySize_eq] at hSz'
  injection hSz' with hEq
  subst hEq
  rcases hDec bs hLen hInit with ⟨v, hv⟩
  rw [m.decode_eq_map bs, hNone] at hv
  nomatch hv

/-- Negative bridge: if some `x : α` encodes with an `.uninit` byte, `ty` is NOT `IsIntoBytes`. -/
theorem not_isIntoBytes_of_uninit_encode {layouts : LayoutTable} {ty : Ty} {α : Type} {sz : Nat}
    (m : MirValueCodec layouts ty α sz)
    (x : α) (hUninit : allBytesInitialized (m.codec.encode x) = false) :
    ¬ IsIntoBytes layouts ty := by
  rintro ⟨_, _, hEncProps⟩
  have ⟨_, hInit⟩ := hEncProps (m.toValue x) (m.codec.encode x) (m.encode_toValue x)
  rw [hUninit] at hInit
  nomatch hInit

/-- Every `m.codec.encode x` is `ByteSeqValid layouts ty .BitValid`. -/
theorem byteSeqValid_of_encode {layouts : LayoutTable} {ty : Ty} {α : Type} {sz : Nat}
    (m : MirValueCodec layouts ty α sz) (x : α) :
    ByteSeqValid layouts ty .BitValid (m.codec.encode x) := by
  refine ⟨sz, m.toValue x, m.tySize_eq, m.codec.encode_length x, ?_⟩
  rw [m.decode_eq_map (m.codec.encode x), m.codec.decode_encode x]
  rfl

/--
Safe byte transmutation across `MirValueCodec`s via `BitValidity.transmute_sound_of_into_from_bytes`.
-/
theorem transmute_sound {layouts : LayoutTable} {srcTy dstTy : Ty} {α β : Type} {sz : Nat}
    (mSrc : MirValueCodec layouts srcTy α sz)
    (mDst : MirValueCodec layouts dstTy β sz)
    (hInto : mSrc.codec.IsInitCodec)
    (hFrom : mDst.codec.IsSurjectiveInitDecoder)
    (v : Value) (bs : List AbstractByte)
    (hEnc : encodeValueToBytes defaultCodecFuel layouts srcTy v = some bs)
    (hWidths : mSrc.enforcesUntypedFieldWidths = true := by rfl) :
    ∃ v', decodeValueFromBytes defaultCodecFuel layouts dstTy bs = some v' :=
  transmute_sound_of_into_from_bytes layouts srcTy dstTy
    (mSrc.isIntoBytes hInto hWidths)
    (mDst.isFromBytes hFrom)
    (by rw [mSrc.tySize_eq, mDst.tySize_eq])
    v bs hEnc

/--
Safe byte transmutation for any decoded/well-typed inhabitant `v` of `srcTy`
(`decodeValueFromBytes defaultCodecFuel layouts srcTy bs₀ = some v`), applicable to
every `MirValueCodec` including `scalarNicheNewtype` without requiring `enforcesUntypedFieldWidths`.
-/
theorem transmute_sound_of_decoded {layouts : LayoutTable} {srcTy dstTy : Ty} {α β : Type} {sz : Nat}
    (mSrc : MirValueCodec layouts srcTy α sz)
    (mDst : MirValueCodec layouts dstTy β sz)
    (hInto : mSrc.codec.IsInitCodec)
    (hFrom : mDst.codec.IsSurjectiveInitDecoder)
    {bs₀ : List AbstractByte} {v : Value} {bs : List AbstractByte}
    (hValidSrc : decodeValueFromBytes defaultCodecFuel layouts srcTy bs₀ = some v)
    (hEnc : encodeValueToBytes defaultCodecFuel layouts srcTy v = some bs) :
    ∃ v', decodeValueFromBytes defaultCodecFuel layouts dstTy bs = some v' := by
  rw [mSrc.decode_eq_map bs₀] at hValidSrc
  cases hC : mSrc.codec.decode bs₀ <;> rw [hC] at hValidSrc
  · nomatch hValidSrc
  case some x =>
    injection hValidSrc with hV
    subst hV
    rw [mSrc.encode_toValue x] at hEnc
    injection hEnc with hBs
    subst hBs
    rcases mDst.isFromBytes hFrom with ⟨sz', hSz', hDecDst⟩
    rw [mDst.tySize_eq] at hSz'
    injection hSz' with hEq
    subst hEq
    exact hDecDst (mSrc.codec.encode x) (mSrc.codec.encode_length x) (hInto x)

/-- Typed transmutation: `mSrc.codec.encode x` decodes to a typed `y : β` in `mDst`. -/
theorem transmute_typed {layouts : LayoutTable} {srcTy dstTy : Ty} {α β : Type} {sz : Nat}
    (mSrc : MirValueCodec layouts srcTy α sz)
    (mDst : MirValueCodec layouts dstTy β sz)
    (hInto : mSrc.codec.IsInitCodec)
    (hFrom : mDst.codec.IsSurjectiveInitDecoder)
    (x : α) :
    ∃ y : β,
      mDst.codec.decode (mSrc.codec.encode x) = some y ∧
      decodeValueFromBytes defaultCodecFuel layouts dstTy (mSrc.codec.encode x) =
        some (mDst.toValue y) := by
  rcases hFrom (mSrc.codec.encode x) (mSrc.codec.encode_length x) (hInto x) with ⟨y, hy⟩
  refine ⟨y, hy, ?_⟩
  rw [mDst.decode_eq_map, hy]
  rfl

/-! ### Ready-to-Use `MirValueCodec` Constructors -/

/-- `MirValueCodec` for `()` (`{ kind := .tuple [], layoutIdx := idx }`). -/
def unit (layouts : LayoutTable) (idx : LayoutIdx) :
    MirValueCodec layouts { kind := .tuple [], layoutIdx := idx } Unit 0 :=
  ofCanonicalEncode
    FixedByteCodec.unit
    (fun _ => .unit)
    (fun v => match v with | .unit => some () | _ => none)
    (fun _ => rfl)
    rfl
    (fun _ => rfl)
    (fun v bs hEnc => by
      unfold defaultCodecFuel encodeValueToBytes at hEnc
      cases v with
      | unit =>
        injection hEnc with hBs
        exact ⟨(), hBs.symm⟩
      | aggregate varIdx fs =>
        match varIdx, fs with
        | 0, [] =>
          injection hEnc with hBs
          exact ⟨(), hBs.symm⟩
        | _ + 1, _ | 0, _ :: _ => nomatch hEnc
      | _ => nomatch hEnc)
    (fun bs => by
      cases bs <;> rfl)

/-- `MirValueCodec` for Rust `bool` (`{ kind := .bool, layoutIdx := idx }`). -/
def bool (layouts : LayoutTable) (idx : LayoutIdx) :
    MirValueCodec layouts { kind := .bool, layoutIdx := idx } Bool 1 :=
  ofCanonicalEncode
    FixedByteCodec.boolByte
    (fun b => .scalar ⟨if b then 1 else 0, 1⟩)
    (fun v =>
      match v with
      | .scalar sv =>
        if sv.sizeBytes == 1 then
          if sv.bits == 0 then some false
          else if sv.bits == 1 then some true
          else none
        else none
      | _ => none)
    (fun b => by cases b <;> rfl)
    rfl
    (fun b => by cases b <;> rfl)
    (fun v bs hEnc => by
      unfold defaultCodecFuel encodeValueToBytes at hEnc
      cases v with
      | scalar sv =>
        dsimp only at hEnc
        cases h1 : Nat.beq sv.sizeBytes 1 <;> rw [h1] at hEnc
        · nomatch hEnc
        · dsimp only at hEnc
          cases hb0 : Nat.beq sv.bits 0 <;> rw [hb0] at hEnc
          · dsimp only at hEnc
            cases hb1 : Nat.beq sv.bits 1 <;> rw [hb1] at hEnc
            · nomatch hEnc
            · injection hEnc with hBs
              exact ⟨true, hBs.symm⟩
          · injection hEnc with hBs
            exact ⟨false, hBs.symm⟩
      | _ => nomatch hEnc)
    (fun bs => by
      unfold defaultCodecFuel decodeValueFromBytes FixedByteCodec.boolByte FixedByteCodec.ofRoundTrip
      cases bs with
      | nil => rfl
      | cons b0 rest =>
        cases b0 with
        | uninit => rfl
        | init b prov =>
          cases rest with
          | cons _ _ => rfl
          | nil =>
            dsimp only
            cases Nat.beq b.toBitVec.toNat 0 <;> cases Nat.beq b.toBitVec.toNat 1 <;> rfl)

/-- Byte width of `UintTy` on 64-bit targets (`1, 2, 4, 8, 16`), matching `intCastTargetBytes`. -/
@[reducible]
def uintByteSize : UintTy → Nat
  | .u8 => 1
  | .u16 => 2
  | .u32 => 4
  | .u64 => 8
  | .u128 => 16
  | .usize => 8

theorem uintByteSize_pos (w : UintTy) : 0 < uintByteSize w := by
  cases w <;> decide

theorem intCastTargetBytes_uint_eq (w : UintTy) :
    intCastTargetBytes (.uint w) = some (uintByteSize w) := by
  cases w <;> rfl

/-- `MirValueCodec` for every unsigned integer type `u8`, `u16`, `u32`, `u64`, `u128`, `usize`. -/
def uint (layouts : LayoutTable) (w : UintTy) (idx : LayoutIdx) :
    MirValueCodec layouts { kind := .uint w, layoutIdx := idx }
      { bits : Nat // bits < 2 ^ (8 * uintByteSize w) } (uintByteSize w) :=
  let sz := uintByteSize w
  let hNz := uintByteSize_pos w
  ofCanonicalEncode
    (FixedByteCodec.uintBitsLE sz hNz)
    (fun x => .scalar ⟨x.val, sz⟩)
    (fun v =>
      match v with
      | .scalar sv =>
        if sv.sizeBytes == sz then
          if hLt : sv.bits < 2 ^ (8 * sz) then some ⟨sv.bits, hLt⟩ else none
        else none
      | _ => none)
    (fun ⟨bits, hLt⟩ => by
      simp [sz, hLt])
    (by
      unfold rigidTyByteSize rigidTyKindByteSize
      rw [intCastTargetBytes_uint_eq w])
    (fun ⟨bits, _hLt⟩ => by
      unfold defaultCodecFuel encodeValueToBytes
      dsimp only
      rw [intCastTargetBytes_uint_eq w]
      dsimp only
      have hSzEq : Nat.beq sz sz = true := nat_beq_self sz
      rw [hSzEq]
      dsimp only
      unfold encodeScalarBytes
      have hBeq0 : Nat.beq sz 0 = false := nat_beq_eq_false_of_ne (by omega)
      rw [hBeq0]
      rfl)
    (fun v bs hEnc => by
      unfold defaultCodecFuel encodeValueToBytes at hEnc
      dsimp only at hEnc
      rw [intCastTargetBytes_uint_eq w] at hEnc
      cases v <;> dsimp only at hEnc
      case unit => nomatch hEnc
      case ptr => nomatch hEnc
      case aggregate => nomatch hEnc
      case scalar sv =>
        cases hEq : Nat.beq sv.sizeBytes sz <;> rw [hEq] at hEnc
        · nomatch hEnc
        · have hSvSz : sv.sizeBytes = sz := Nat.eq_of_beq_eq_true hEq
          unfold encodeScalarBytes at hEnc
          rw [hSvSz] at hEnc
          have hBeq0 : Nat.beq sz 0 = false := nat_beq_eq_false_of_ne (by omega)
          rw [hBeq0] at hEnc
          injection hEnc with hBs
          refine ⟨⟨sv.bits % 2 ^ (8 * sz), Nat.mod_lt _ (Nat.two_pow_pos _)⟩, ?_⟩
          rw [← hBs]
          exact (encodeLittleEndianBytes_mod_two_pow none sz sv.bits).symm)
    (fun bs => by
      unfold defaultCodecFuel decodeValueFromBytes FixedByteCodec.uintBitsLE FixedByteCodec.ofRoundTrip
      dsimp only
      rw [intCastTargetBytes_uint_eq w]
      dsimp only
      have hLenDef : Trusted.Sequence.length bs = bs.length := rfl
      rw [hLenDef]
      cases hLen : Nat.beq bs.length sz
      · rfl
      · have hLenEq : bs.length = sz := Nat.eq_of_beq_eq_true hLen
        have hNonEmpty : Nat.beq (Trusted.Sequence.length bs) 0 = false := by
          rw [hLenDef, hLenEq]
          exact nat_beq_eq_false_of_ne (by omega)
        dsimp only
        unfold decodeScalarBytes
        dsimp only
        rw [hNonEmpty]
        dsimp only
        cases hLE : decodeLittleEndianBytes bs with
        | none => rfl
        | some bp =>
          rcases bp with ⟨bits, prov⟩
          have hModLt := decodeLittleEndianBytes_lt_scalarModulus bs bits prov hLE
          have hLt : bits < 2 ^ (8 * sz) := by
            rw [hLenDef, hLenEq, Anneal.Scalars.scalarModulus_eq_two_pow] at hModLt
            exact hModLt
          dsimp only
          simp only [hLt, ↓reduceDIte]
          rw [hLenDef, hLenEq]
          rfl)

/--
`MirValueCodec` for a `.primitive`-fields scalar-niche ADT (`l.fields = .primitive`,
`l.variants = .single varIdx`) backed by `ScalarLayout.initialized pk range` for any
non-pointer `PrimitiveKind` `pk` (`.int bitsWidth signed` or `.float bitsWidth`).

This covers `.primitive`-fields ADT layouts (such as inner scalar field layouts
referenced through `TypeLayout.fieldLayouts`). For single-field newtype wrappers
with `l.fields = .arbitrary [⟨0⟩] _` (such as `rustc`'s newtype `NonZero*` shape),
use `scalarNicheNewtype` / `scalarNicheNewtypeNonPtr`; for multi-variant fieldless
enums (`l.variants = .multiple ...`), use `fieldlessEnum`.
-/
def primitiveNicheAdtNonPtr
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (sz : Nat) (pk : PrimitiveKind) (varIdx : VariantIdx)
    (range : WrappingRange)
    (hNz : 0 < sz)
    (hNonPtr : FixedByteCodec.isNonPointerPrimitiveKind pk = true)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hSize : l.size.bytes = sz)
    (hFields : l.fields = .primitive)
    (hVar : l.variants = .single varIdx)
    (hRepr : l.backendRepr = .scalar (.initialized pk range))
    (hWidth : primitiveKindByteWidth pk = some sz) :
    MirValueCodec layouts { kind := .adt defPath args, layoutIdx := idx }
      { bits : Nat // bits < 2 ^ (8 * sz) ∧ wrappingRangeContains range bits = true } sz where
  codec := FixedByteCodec.scalarValidRange sz hNz range
  toValue := fun x => .scalar ⟨x.val, sz⟩
  ofValue := fun v =>
    match v with
    | .scalar sv =>
      if sv.sizeBytes == sz then
        if h : sv.bits < 2 ^ (8 * sz) ∧ wrappingRangeContains range sv.bits = true then
          some ⟨sv.bits, h⟩
        else none
      else none
    | _ => none
  ofValue_toValue := fun ⟨bits, hProp⟩ => by
    simp [hProp]
  tySize_eq := by
    unfold rigidTyByteSize rigidTyKindByteSize
    rw [hLookup]
    exact congrArg some hSize
  encode_toValue := fun ⟨bits, _hProp⟩ => by
    unfold defaultCodecFuel encodeValueToBytes
    dsimp only
    rw [hLookup]
    dsimp only
    rw [hInhab]
    dsimp only
    rw [hVar]
    dsimp only
    rw [hFields, hSize]
    dsimp only
    rw [nat_beq_self sz]
    dsimp only
    unfold encodeScalarBytes
    have hBeq0 : Nat.beq sz 0 = false := nat_beq_eq_false_of_ne (by omega)
    rw [hBeq0]
    rfl
  enforcesUntypedFieldWidths := true
  encode_length_and_init_of_isInit := fun _ _ v bs hEnc => by
    unfold defaultCodecFuel encodeValueToBytes at hEnc
    dsimp only at hEnc
    rw [hLookup] at hEnc
    dsimp only at hEnc
    rw [hInhab] at hEnc
    dsimp only at hEnc
    rw [hVar, hFields] at hEnc
    cases v <;> dsimp only at hEnc
    case unit => nomatch hEnc
    case ptr => nomatch hEnc
    case aggregate => nomatch hEnc
    case scalar sv =>
      cases hEq : Nat.beq sv.sizeBytes l.size.bytes <;> rw [hEq] at hEnc
      · nomatch hEnc
      · have hSvSz : sv.sizeBytes = sz := (Nat.eq_of_beq_eq_true hEq).trans hSize
        have ⟨hLen, hInit⟩ := encodeScalarBytes_length_and_init sv none bs hEnc
        exact ⟨hSvSz ▸ hLen, hInit⟩
  decode_eq_map := fun bs => by
    unfold defaultCodecFuel decodeValueFromBytes
    dsimp only
    rw [hLookup]
    dsimp only
    have hLenDef : Trusted.Sequence.length bs = bs.length := rfl
    rw [hLenDef, hInhab, hSize, Bool.false_or]
    cases hLen : Nat.beq bs.length sz
    · have hNe : bs.length ≠ sz := fun hEq => by
        rw [Nat.beq_eq.mpr hEq] at hLen; nomatch hLen
      rw [(FixedByteCodec.scalarValidRange_isExactWidth sz hNz range).decode_eq_none_of_length_ne hNe]
      rfl
    · rw [Bool.not_true, hVar, hFields]
      have hSzBeq0 : Nat.beq sz 0 = false := nat_beq_eq_false_of_ne (by omega)
      rw [hSzBeq0, hRepr]
      exact FixedByteCodec.decodeScalarLayoutBytes_initialized_nonPtr_eq_scalarValidRange_map
        pk range sz hNz hNonPtr hWidth bs

/--
`MirValueCodec` for a `.primitive`-fields integer scalar-niche ADT (`l.fields = .primitive`,
`l.variants = .single varIdx`) backed by `ScalarLayout.initialized (.int bitsWidth signed) range`.
See `scalarNicheNewtype` for single-field newtype wrappers (`l.fields = .arbitrary [⟨0⟩] _`)
and `fieldlessEnum` for multi-variant fieldless enums (`l.variants = .multiple ...`).
-/
def primitiveNicheAdt
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (sz bitsWidth : Nat) (signed : Bool) (varIdx : VariantIdx)
    (range : WrappingRange)
    (hNz : 0 < sz)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hSize : l.size.bytes = sz)
    (hFields : l.fields = .primitive)
    (hVar : l.variants = .single varIdx)
    (hRepr : l.backendRepr = .scalar (.initialized (.int bitsWidth signed) range))
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some sz) :
    MirValueCodec layouts { kind := .adt defPath args, layoutIdx := idx }
      { bits : Nat // bits < 2 ^ (8 * sz) ∧ wrappingRangeContains range bits = true } sz :=
  primitiveNicheAdtNonPtr layouts defPath args idx l sz (.int bitsWidth signed) varIdx range
    hNz rfl hLookup hInhab hSize hFields hVar hRepr hWidth

/-- Helper decoder extracting `ScalarInt` elements of byte width `sz` from a `List Value`. -/
def uintArrayDecodeVals (sz : Nat) :
    List Value → Option (List { bits : Nat // bits < 2 ^ (8 * sz) })
  | [] => some []
  | .scalar sv :: rest =>
    if sv.sizeBytes == sz then
      if hLt : sv.bits < 2 ^ (8 * sz) then
        (uintArrayDecodeVals sz rest).map (⟨sv.bits, hLt⟩ :: ·)
      else none
    else none
  | _ :: _ => none

theorem uintArrayDecodeVals_map_scalar (sz : Nat) :
    ∀ ys : List { bits : Nat // bits < 2 ^ (8 * sz) },
      uintArrayDecodeVals sz (ys.map (fun x => Value.scalar ⟨x.val, sz⟩)) = some ys
  | [] => rfl
  | ⟨bits, hLt⟩ :: rest => by
    dsimp only [List.map, uintArrayDecodeVals]
    have hBeq : (sz == sz) = true := by simp
    rw [hBeq]
    simp only [↓reduceIte, hLt, ↓reduceDIte]
    rw [uintArrayDecodeVals_map_scalar sz rest]
    rfl

/--
`MirValueCodec` for homogeneous unsigned integer arrays `[uN; k]` (`k > 0`) using
`FixedByteCodec.listFixed`.
-/
def uintArray (layouts : LayoutTable) (w : UintTy) (k : Nat) (hk : 0 < k) (idx : LayoutIdx) :
    MirValueCodec layouts { kind := .array (.uint w) k, layoutIdx := idx }
      { xs : List { bits : Nat // bits < 2 ^ (8 * uintByteSize w) } // xs.length = k }
      (k * uintByteSize w) :=
  let sz := uintByteSize w
  let hNz := uintByteSize_pos w
  let elemCodec := FixedByteCodec.uintBitsLE sz hNz
  let toElemVal := fun (x : { bits : Nat // bits < 2 ^ (8 * sz) }) => Value.scalar ⟨x.val, sz⟩
  have hKBeq0 : Nat.beq k 0 = false := nat_beq_eq_false_of_ne (by omega)
  have hMulComm : Nat.mul sz k = k * sz := Nat.mul_comm sz k
  ofCanonicalEncode
    (FixedByteCodec.listFixed k elemCodec)
    (fun xs => .aggregate 0 (xs.val.map toElemVal))
    (fun v =>
      match v with
      | .aggregate 0 vs =>
        match uintArrayDecodeVals sz vs with
        | some xs => if hLen : xs.length = k then some ⟨xs, hLen⟩ else none
        | none => none
      | _ => none)
    (fun ⟨xs, hLen⟩ => by
      simp only []
      rw [uintArrayDecodeVals_map_scalar sz xs]
      simp only [hLen, ↓reduceDIte])
    (by
      unfold rigidTyByteSize
      dsimp only [rigidTyKindByteSize]
      rw [intCastTargetBytes_uint_eq w]
      exact congrArg some hMulComm)
    (fun ⟨xs, hLen⟩ => by
      unfold defaultCodecFuel encodeValueToBytes
      dsimp only
      rw [hKBeq0]
      simp only []
      have hMapLen : Nat.beq (Trusted.Sequence.length (xs.map toElemVal)) k = true := by
        have hEq : Trusted.Sequence.length (xs.map toElemVal) = k := by
          change (xs.map toElemVal).length = k
          rw [List.length_map, hLen]
        exact Nat.beq_eq.mpr hEq
      rw [hMapLen]
      dsimp only [rigidTyKindByteSize]
      rw [intCastTargetBytes_uint_eq w]
      dsimp only
      apply FixedByteCodec.encodeListWith_map_eq_encodeElems elemCodec toElemVal
      intro ⟨bits, _hLt⟩
      unfold encodeValueToBytes
      dsimp only [toElemVal, sz]
      rw [intCastTargetBytes_uint_eq w]
      dsimp only
      rw [nat_beq_self (uintByteSize w)]
      dsimp only
      unfold encodeScalarBytes
      have hSz0 : Nat.beq (uintByteSize w) 0 = false := nat_beq_eq_false_of_ne (by omega)
      rw [hSz0]
      rfl)
    (fun v bs hEnc => by
      unfold defaultCodecFuel encodeValueToBytes at hEnc
      dsimp only at hEnc
      rw [hKBeq0] at hEnc
      cases v <;> dsimp only at hEnc
      case unit => nomatch hEnc
      case scalar => nomatch hEnc
      case ptr => nomatch hEnc
      case aggregate varIdx elems =>
        cases varIdx with
        | succ _ => nomatch hEnc
        | zero =>
          change
            (match Nat.beq (Trusted.Sequence.length elems) k with
             | false => none
             | true =>
               match
                 match rigidTyKindByteSize (.uint w) with
                 | some sz0 => some sz0
                 | none => _ with
               | none => none
               | some elemSz =>
                 encodeListWith
                   (fun e => encodeValueToBytes 15 layouts { kind := .uint w, layoutIdx := 0 } e)
                   elemSz elems) = some bs at hEnc
          cases hELen : Nat.beq (Trusted.Sequence.length elems) k <;> rw [hELen] at hEnc
          · nomatch hEnc
          · dsimp only [rigidTyKindByteSize] at hEnc
            rw [intCastTargetBytes_uint_eq w] at hEnc
            dsimp only at hEnc
            have hListWitness :
                ∀ (es : List Value) (outBs : List AbstractByte),
                  encodeListWith
                    (fun e => encodeValueToBytes 15 layouts { kind := .uint w, layoutIdx := 0 } e)
                    sz es = some outBs →
                  ∃ ys : List { bits : Nat // bits < 2 ^ (8 * sz) },
                    ys.length = es.length ∧ outBs = FixedByteCodec.encodeElems elemCodec ys := by
              intro es
              induction es with
              | nil =>
                intro outBs hE
                injection hE with hOut
                exact ⟨[], rfl, hOut.symm⟩
              | cons e rest ih =>
                intro outBs hE
                unfold encodeListWith at hE
                cases hHead : encodeValueToBytes 15 layouts { kind := .uint w, layoutIdx := 0 } e <;>
                  rw [hHead] at hE
                · nomatch hE
                case some headBs =>
                  dsimp only at hE
                  cases hHeadLen : Nat.beq (Trusted.Sequence.length headBs) sz <;>
                    rw [hHeadLen] at hE
                  · nomatch hE
                  · dsimp only at hE
                    cases hTail :
                        encodeListWith
                          (fun e => encodeValueToBytes 15 layouts { kind := .uint w, layoutIdx := 0 } e)
                          sz rest <;> rw [hTail] at hE
                    · nomatch hE
                    case some tailBs =>
                      injection hE with hOut
                      rw [appendAbstractBytes_eq_append] at hOut
                      unfold encodeValueToBytes at hHead
                      dsimp only at hHead
                      rw [intCastTargetBytes_uint_eq w] at hHead
                      cases e <;> dsimp only at hHead
                      case unit => nomatch hHead
                      case ptr => nomatch hHead
                      case aggregate => nomatch hHead
                      case scalar sv =>
                        cases hSvEq : Nat.beq sv.sizeBytes sz <;> rw [hSvEq] at hHead
                        · nomatch hHead
                        · have hSvSz : sv.sizeBytes = sz := Nat.eq_of_beq_eq_true hSvEq
                          unfold encodeScalarBytes at hHead
                          rw [hSvSz] at hHead
                          have hSz0 : Nat.beq sz 0 = false := nat_beq_eq_false_of_ne (by omega)
                          rw [hSz0] at hHead
                          injection hHead with hHeadBs
                          rcases ih tailBs hTail with ⟨ys, hYsLen, hYsBs⟩
                          refine ⟨⟨sv.bits % 2 ^ (8 * sz), Nat.mod_lt _ (Nat.two_pow_pos _)⟩ :: ys,
                                  congrArg Nat.succ hYsLen, ?_⟩
                          rw [← hOut, hYsBs, ← hHeadBs]
                          dsimp only [FixedByteCodec.encodeElems, elemCodec,
                                      FixedByteCodec.uintBitsLE, FixedByteCodec.ofRoundTrip]
                          rw [encodeLittleEndianBytes_mod_two_pow none sz sv.bits]
            rcases hListWitness elems bs hEnc with ⟨ys, hYsLen, hYsBs⟩
            have hElemsLen : elems.length = k := Nat.eq_of_beq_eq_true hELen
            exact ⟨⟨ys, hYsLen.trans hElemsLen⟩, hYsBs⟩)
    (fun bs => by
      unfold defaultCodecFuel decodeValueFromBytes
      dsimp only
      rw [hKBeq0]
      dsimp only [rigidTyKindByteSize]
      rw [intCastTargetBytes_uint_eq w]
      dsimp only
      have hLenDef : Trusted.Sequence.length bs = bs.length := rfl
      rw [hLenDef]
      change
        (match Nat.beq bs.length (Nat.mul sz k) with
         | false => none
         | true =>
           match
             decodeArrayChunksWith
               (fun chunk => decodeValueFromBytes 15 layouts { kind := .uint w, layoutIdx := 0 } chunk)
               sz k bs with
           | some elems => some (Value.aggregate 0 elems)
           | none => none) =
          ((FixedByteCodec.listFixed k elemCodec).decode bs).map
            (fun xs => Value.aggregate 0 (xs.val.map toElemVal))
      rw [hMulComm]
      cases hLen : Nat.beq bs.length (k * sz)
      · dsimp only
        have hNe : bs.length ≠ k * sz := fun hEq => by
          rw [Nat.beq_eq.mpr hEq] at hLen; nomatch hLen
        rw [(FixedByteCodec.listFixed_isExactWidth k elemCodec).decode_eq_none_of_length_ne hNe]
        rfl
      · dsimp only
        have hBridge := FixedByteCodec.decodeArrayChunksWith_eq_listFixed_map elemCodec toElemVal
          (fun chunk => decodeValueFromBytes 15 layouts { kind := .uint w, layoutIdx := 0 } chunk)
          (fun chunk => (uint layouts w 0).decode_eq_map chunk)
          k bs
        rw [hBridge]
        cases (FixedByteCodec.listFixed k elemCodec).decode bs <;> rfl)

/--
`MirValueCodec` for unindexed 2-element primitive integer tuples `(uA, uB)`
(`LayoutTable.lookup layouts idx = none`), built directly on `FixedByteCodec.prod`.
-/
def uintPairTuple (layouts : LayoutTable) (w₁ w₂ : UintTy) (idx : LayoutIdx)
    (hNoLayout : LayoutTable.lookup layouts idx = none) :
    MirValueCodec layouts { kind := .tuple [.uint w₁, .uint w₂], layoutIdx := idx }
      ({ bits : Nat // bits < 2 ^ (8 * uintByteSize w₁) } ×
       { bits : Nat // bits < 2 ^ (8 * uintByteSize w₂) })
      (uintByteSize w₁ + uintByteSize w₂) :=
  let sz₁ := uintByteSize w₁
  let sz₂ := uintByteSize w₂
  let c₁ := FixedByteCodec.uintBitsLE sz₁ (uintByteSize_pos w₁)
  let c₂ := FixedByteCodec.uintBitsLE sz₂ (uintByteSize_pos w₂)
  let m₁ := uint layouts w₁ 0
  let m₂ := uint layouts w₂ 0
  ofCanonicalEncode
    (FixedByteCodec.prod c₁ c₂)
    (fun ⟨a, b⟩ => .aggregate 0 [m₁.toValue a, m₂.toValue b])
    (fun v =>
      match v with
      | .aggregate 0 [v₁, v₂] =>
        match m₁.ofValue v₁, m₂.ofValue v₂ with
        | some a, some b => some (a, b)
        | _, _ => none
      | _ => none)
    (fun ⟨a, b⟩ => by
      show
        (match m₁.ofValue (m₁.toValue a), m₂.ofValue (m₂.toValue b) with
         | some a', some b' => some (a', b')
         | _, _ => none) = some (a, b)
      rw [m₁.ofValue_toValue a, m₂.ofValue_toValue b])
    (by
      unfold rigidTyByteSize
      dsimp only [rigidTyKindByteSize, tupleFieldsByteSize]
      rw [hNoLayout, intCastTargetBytes_uint_eq w₁, intCastTargetBytes_uint_eq w₂]
      rfl)
    (fun ⟨a, b⟩ => by
      have ha : encodeValueToBytes 15 layouts { kind := .uint w₁, layoutIdx := 0 }
          (m₁.toValue a) = some (c₁.encode a) := m₁.encode_toValue a
      have hb : encodeValueToBytes 15 layouts { kind := .uint w₂, layoutIdx := 0 }
          (m₂.toValue b) = some (c₂.encode b) := m₂.encode_toValue b
      unfold defaultCodecFuel encodeValueToBytes
      simp only []
      have hLenEq : Nat.beq (Trusted.Sequence.length [m₁.toValue a, m₂.toValue b])
          (Trusted.Sequence.length [RigidTy.uint w₁, RigidTy.uint w₂]) = true := rfl
      rw [hLenEq]
      dsimp only
      rw [hNoLayout]
      dsimp only [encodeSeqFieldsWith]
      rw [ha, hb]
      dsimp only
      rw [appendAbstractBytes_eq_append, appendAbstractBytes_eq_append, List.append_nil]
      rfl)
    (fun v bs hEnc => by
      unfold defaultCodecFuel encodeValueToBytes at hEnc
      cases v <;> dsimp only at hEnc
      case unit => nomatch hEnc
      case scalar => nomatch hEnc
      case ptr => nomatch hEnc
      case aggregate varIdx fs =>
        cases varIdx with
        | succ _ => nomatch hEnc
        | zero =>
          cases fs with
          | nil => nomatch hEnc
          | cons v₁ rest₁ =>
            cases rest₁ with
            | nil => nomatch hEnc
            | cons v₂ rest₂ =>
              cases rest₂ with
              | cons _ _ => nomatch hEnc
              | nil =>
                have hLenEq : Nat.beq (Trusted.Sequence.length [v₁, v₂])
                    (Trusted.Sequence.length [RigidTy.uint w₁, RigidTy.uint w₂]) = true := rfl
                simp only [] at hEnc
                rw [hLenEq] at hEnc
                dsimp only at hEnc
                rw [hNoLayout] at hEnc
                dsimp only [encodeSeqFieldsWith] at hEnc
                cases hE₁ : encodeValueToBytes 15 layouts { kind := .uint w₁, layoutIdx := 0 } v₁ <;>
                  rw [hE₁] at hEnc
                · nomatch hEnc
                case some b₁ =>
                  cases hE₂ : encodeValueToBytes 15 layouts { kind := .uint w₂, layoutIdx := 0 } v₂ <;>
                    rw [hE₂] at hEnc
                  · nomatch hEnc
                  case some b₂ =>
                    dsimp only at hEnc
                    injection hEnc with hBs
                    rw [appendAbstractBytes_eq_append, appendAbstractBytes_eq_append, List.append_nil] at hBs
                    unfold encodeValueToBytes at hE₁ hE₂
                    dsimp only at hE₁ hE₂
                    rw [intCastTargetBytes_uint_eq w₁] at hE₁
                    rw [intCastTargetBytes_uint_eq w₂] at hE₂
                    cases v₁ <;> dsimp only at hE₁
                    case unit => nomatch hE₁
                    case ptr => nomatch hE₁
                    case aggregate => nomatch hE₁
                    case scalar sv₁ =>
                      cases hS₁ : Nat.beq sv₁.sizeBytes sz₁ <;> rw [hS₁] at hE₁
                      · nomatch hE₁
                      · cases v₂ <;> dsimp only at hE₂
                        case unit => nomatch hE₂
                        case ptr => nomatch hE₂
                        case aggregate => nomatch hE₂
                        case scalar sv₂ =>
                          cases hS₂ : Nat.beq sv₂.sizeBytes sz₂ <;> rw [hS₂] at hE₂
                          · nomatch hE₂
                          · have hSvSz₁ : sv₁.sizeBytes = sz₁ := Nat.eq_of_beq_eq_true hS₁
                            have hSvSz₂ : sv₂.sizeBytes = sz₂ := Nat.eq_of_beq_eq_true hS₂
                            unfold encodeScalarBytes at hE₁ hE₂
                            rw [hSvSz₁] at hE₁
                            rw [hSvSz₂] at hE₂
                            have hNz₁ : Nat.beq sz₁ 0 = false :=
                              nat_beq_eq_false_of_ne (by have := uintByteSize_pos w₁; omega)
                            have hNz₂ : Nat.beq sz₂ 0 = false :=
                              nat_beq_eq_false_of_ne (by have := uintByteSize_pos w₂; omega)
                            rw [hNz₁] at hE₁
                            rw [hNz₂] at hE₂
                            injection hE₁ with hB₁
                            injection hE₂ with hB₂
                            refine ⟨(⟨sv₁.bits % 2 ^ (8 * sz₁), Nat.mod_lt _ (Nat.two_pow_pos _)⟩,
                                     ⟨sv₂.bits % 2 ^ (8 * sz₂), Nat.mod_lt _ (Nat.two_pow_pos _)⟩), ?_⟩
                            rw [← hBs, ← hB₁, ← hB₂]
                            dsimp only [FixedByteCodec.prod, c₁, c₂,
                                        FixedByteCodec.uintBitsLE, FixedByteCodec.ofRoundTrip]
                            rw [encodeLittleEndianBytes_mod_two_pow none sz₁ sv₁.bits,
                                encodeLittleEndianBytes_mod_two_pow none sz₂ sv₂.bits])
    (fun bs => by
      unfold defaultCodecFuel decodeValueFromBytes
      dsimp only
      rw [hNoLayout]
      dsimp only
      unfold decodeSeqFieldsWith
      have hSz₁ : rigidTyByteSize layouts { kind := .uint w₁, layoutIdx := 0 } = some sz₁ :=
        m₁.tySize_eq
      have hSz₂ : rigidTyByteSize layouts { kind := .uint w₂, layoutIdx := 0 } = some sz₂ :=
        m₂.tySize_eq
      rw [hSz₁]
      dsimp only
      have hLenDef : Trusted.Sequence.length bs = bs.length := rfl
      rw [hLenDef]
      cases hBle₁ : Nat.ble sz₁ bs.length
      · dsimp only
        have hGt : bs.length < sz₁ := by
          cases Nat.lt_or_ge bs.length sz₁ with
          | inl h => exact h
          | inr h => rw [Nat.ble_eq_true_of_le h] at hBle₁; nomatch hBle₁
        have hNe : bs.length ≠ sz₁ + sz₂ := by omega
        rw [(FixedByteCodec.prod_isExactWidth c₁ c₂).decode_eq_none_of_length_ne hNe]
        rfl
      · dsimp only
        rw [takeAbstractBytes_eq_take, dropAbstractBytes_eq_drop]
        have hD₁ : decodeValueFromBytes 15 layouts { kind := .uint w₁, layoutIdx := 0 }
            (bs.take sz₁) = (c₁.decode (bs.take sz₁)).map m₁.toValue :=
          m₁.decode_eq_map (bs.take sz₁)
        rw [hD₁]
        cases hC₁ : c₁.decode (bs.take sz₁)
        · dsimp only [Option.map]
          unfold FixedByteCodec.prod FixedByteCodec.ofRoundTrip
          dsimp only [Option.map]
          cases Nat.beq bs.length (sz₁ + sz₂)
          · rfl
          · dsimp only [sz₁] at hC₁ ⊢
            rw [hC₁]
        case some a =>
          dsimp only [Option.map]
          unfold decodeSeqFieldsWith
          rw [hSz₂]
          dsimp only
          have hDropLenDef : Trusted.Sequence.length (bs.drop sz₁) = (bs.drop sz₁).length := rfl
          rw [hDropLenDef]
          have hLe₁ : sz₁ ≤ bs.length := Nat.le_of_ble_eq_true hBle₁
          cases hBle₂ : Nat.ble sz₂ (bs.drop sz₁).length
          · dsimp only
            have hDropLt : (bs.drop sz₁).length < sz₂ := by
              cases Nat.lt_or_ge (bs.drop sz₁).length sz₂ with
              | inl h => exact h
              | inr h => rw [Nat.ble_eq_true_of_le h] at hBle₂; nomatch hBle₂
            rw [List.length_drop] at hDropLt
            have hNe : bs.length ≠ sz₁ + sz₂ := by omega
            rw [(FixedByteCodec.prod_isExactWidth c₁ c₂).decode_eq_none_of_length_ne hNe]
          · dsimp only
            rw [takeAbstractBytes_eq_take, dropAbstractBytes_eq_drop]
            have hD₂ : decodeValueFromBytes 15 layouts { kind := .uint w₂, layoutIdx := 0 }
                ((bs.drop sz₁).take sz₂) =
                (c₂.decode ((bs.drop sz₁).take sz₂)).map m₂.toValue :=
              m₂.decode_eq_map ((bs.drop sz₁).take sz₂)
            rw [hD₂]
            cases hRest : (bs.drop sz₁).drop sz₂ with
            | cons _ _ =>
              have hDropGe : (bs.drop sz₁).length > sz₂ := by
                have hLenRest := congrArg List.length hRest
                dsimp only [sz₁, sz₂] at hLenRest ⊢
                simp only [List.length_drop, List.length_cons] at hLenRest
                simp only [List.length_drop]
                omega
              rw [List.length_drop] at hDropGe
              have hNe : bs.length ≠ sz₁ + sz₂ := by omega
              rw [(FixedByteCodec.prod_isExactWidth c₁ c₂).decode_eq_none_of_length_ne hNe]
              cases c₂.decode ((bs.drop sz₁).take sz₂) <;> rfl
            | nil =>
              have hDropLe : (bs.drop sz₁).length ≤ sz₂ := by
                have hLenRest := congrArg List.length hRest
                dsimp only [sz₁, sz₂] at hLenRest ⊢
                simp only [List.length_drop, List.length_nil] at hLenRest
                simp only [List.length_drop]
                omega
              have hDropGe : sz₂ ≤ (bs.drop sz₁).length := Nat.le_of_ble_eq_true hBle₂
              have hDropEq : (bs.drop sz₁).length = sz₂ := by omega
              have hBsEq : bs.length = sz₁ + sz₂ := by
                rw [List.length_drop] at hDropEq
                omega
              have hTakeAll : (bs.drop sz₁).take sz₂ = bs.drop sz₁ :=
                List.take_of_length_le hDropLe
              rw [hTakeAll]
              unfold FixedByteCodec.prod FixedByteCodec.ofRoundTrip
              dsimp only
              rw [Nat.beq_eq.mpr hBsEq]
              dsimp only
              rw [hC₁]
              cases c₂.decode (bs.drop sz₁) <;> rfl)

theorem replicateUninitBytes_add_eq (a b : Nat) :
    replicateUninitBytes (a + b) = replicateUninitBytes a ++ replicateUninitBytes b := by
  induction a with
  | zero =>
    have h0 : 0 + b = b := Nat.zero_add b
    rw [h0]
    rfl
  | succ a' ih =>
    have hSucc : (a' + 1) + b = (a' + b) + 1 := Nat.succ_add a' b
    rw [hSucc]
    dsimp only [replicateUninitBytes, List.cons_append]
    exact congrArg (List.cons .uninit) ih

theorem writeAbstractBytesAt_zero_replicateUninit {len : Nat}
    (patch rest : List AbstractByte) (hLen : patch.length = len) :
    writeAbstractBytesAt (replicateUninitBytes len ++ rest) 0 patch =
      some (patch ++ rest) := by
  subst hLen
  induction patch with
  | nil => cases rest <;> rfl
  | cons p ps ih =>
    dsimp only [List.length_cons, replicateUninitBytes, List.cons_append, writeAbstractBytesAt]
    rw [ih]

theorem writeAbstractBytesAt_offset_replicateUninit {off len : Nat}
    (pre patch post : List AbstractByte)
    (hPre : pre.length = off) (hPatch : patch.length = len) :
    writeAbstractBytesAt (pre ++ replicateUninitBytes len ++ post) off patch =
      some (pre ++ patch ++ post) := by
  subst hPre
  induction pre with
  | nil =>
    dsimp only [List.length_nil, List.nil_append]
    exact writeAbstractBytesAt_zero_replicateUninit patch post hPatch
  | cons b ps ih =>
    cases patch with
    | nil =>
      subst hPatch
      dsimp only [List.length_nil, replicateUninitBytes, List.nil_append,
                  List.cons_append, writeAbstractBytesAt]
    | cons w ws =>
      dsimp only [List.length_cons, List.cons_append, writeAbstractBytesAt]
      rw [ih]

/-- Single-element tuple `(UintTy,)` laid out with `padBytes` bytes of trailing
uninitialized alignment padding (`FieldsShape.arbitrary [{ bytes := 0 }] [0]`
and `l.size.bytes = uintByteSize w + padBytes`), bridged to
`FixedByteCodec.padRight (uintBitsLE sz hNz) padBytes`.

When `0 < padBytes`, this witnesses a concrete MIR aggregate type satisfying
`IsFromBytes`, `IsFromZeros`, and `IsTryFromBytes` while failing `IsIntoBytes`
(`not_isIntoBytes_of_uninit_encode`). -/
def paddedSingleElemTuple (layouts : LayoutTable) (w : UintTy) (padBytes : Nat)
    (idx : LayoutIdx) (l : TypeLayout)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size = { bytes := uintByteSize w + padBytes })
    (hFields : l.fields = .arbitrary [{ bytes := 0 }] [0]) :
    MirValueCodec layouts { kind := .tuple [.uint w], layoutIdx := idx }
      { bits : Nat // bits < 2 ^ (8 * uintByteSize w) }
      (uintByteSize w + padBytes) :=
  let c := FixedByteCodec.uintBitsLE (uintByteSize w) (uintByteSize_pos w)
  let m := uint layouts w 0
  ofCanonicalEncode
    (FixedByteCodec.padRight c padBytes)
    (fun a => .aggregate 0 [m.toValue a])
    (fun v =>
      match v with
      | .aggregate 0 [v₁] => m.ofValue v₁
      | _ => none)
    (fun a => by
      simp only []
      exact m.ofValue_toValue a)
    (by
      unfold rigidTyByteSize
      dsimp only [rigidTyKindByteSize]
      rw [hLookup]
      dsimp only
      rw [hSize])
    (fun a => by
      have ha : encodeValueToBytes 15 layouts { kind := .uint w, layoutIdx := 0 }
          (m.toValue a) = some (c.encode a) := m.encode_toValue a
      unfold defaultCodecFuel encodeValueToBytes
      simp only []
      have hLen1 : Nat.beq (Trusted.Sequence.length [m.toValue a])
          (Trusted.Sequence.length [RigidTy.uint w]) = true := rfl
      rw [hLen1]
      dsimp only
      rw [hLookup]
      dsimp only
      rw [hFields, hSize]
      dsimp only
      have hOffLen : Nat.beq (Trusted.Sequence.length ([{ bytes := 0 }] : List Size))
          (Trusted.Sequence.length [m.toValue a]) = true := rfl
      rw [hOffLen]
      dsimp only [encodeFieldsAtOffsetsWith]
      rw [ha]
      dsimp only
      rw [replicateUninitBytes_add_eq (uintByteSize w) padBytes,
          writeAbstractBytesAt_zero_replicateUninit (c.encode a) (replicateUninitBytes padBytes)
            (c.encode_length a)]
      rfl)
    (fun v bs hEnc => by
      unfold defaultCodecFuel encodeValueToBytes at hEnc
      cases v <;> dsimp only at hEnc
      case unit => nomatch hEnc
      case scalar => nomatch hEnc
      case ptr => nomatch hEnc
      case aggregate varIdx fs =>
        cases varIdx with
        | succ _ => nomatch hEnc
        | zero =>
          cases fs with
          | nil => nomatch hEnc
          | cons v₁ rest₁ =>
            cases rest₁ with
            | cons _ _ => nomatch hEnc
            | nil =>
              simp only [] at hEnc
              have hLen1 : Nat.beq (Trusted.Sequence.length [v₁])
                  (Trusted.Sequence.length [RigidTy.uint w]) = true := rfl
              rw [hLen1] at hEnc
              dsimp only at hEnc
              rw [hLookup] at hEnc
              dsimp only at hEnc
              rw [hFields, hSize] at hEnc
              dsimp only at hEnc
              have hOffLen : Nat.beq (Trusted.Sequence.length ([{ bytes := 0 }] : List Size))
                  (Trusted.Sequence.length [v₁]) = true := rfl
              rw [hOffLen] at hEnc
              dsimp only [encodeFieldsAtOffsetsWith] at hEnc
              cases hE₁ : encodeValueToBytes 15 layouts { kind := .uint w, layoutIdx := 0 } v₁ <;>
                rw [hE₁] at hEnc
              · dsimp only [rigidTyKindByteSize] at hEnc
                rw [intCastTargetBytes_uint_eq w] at hEnc
                nomatch hEnc
              case some b₁ =>
                dsimp only at hEnc
                unfold encodeValueToBytes at hE₁
                dsimp only at hE₁
                rw [intCastTargetBytes_uint_eq w] at hE₁
                cases v₁ <;> dsimp only at hE₁
                case unit => nomatch hE₁
                case ptr => nomatch hE₁
                case aggregate => nomatch hE₁
                case scalar sv₁ =>
                  cases hS₁ : Nat.beq sv₁.sizeBytes (uintByteSize w) <;> rw [hS₁] at hE₁
                  · nomatch hE₁
                  · have hSvSz₁ : sv₁.sizeBytes = uintByteSize w := Nat.eq_of_beq_eq_true hS₁
                    unfold encodeScalarBytes at hE₁
                    rw [hSvSz₁] at hE₁
                    have hNz₁ : Nat.beq (uintByteSize w) 0 = false :=
                      nat_beq_eq_false_of_ne (by have := uintByteSize_pos w; omega)
                    rw [hNz₁] at hE₁
                    injection hE₁ with hB₁
                    let xWitness : { bits : Nat // bits < 2 ^ (8 * uintByteSize w) } :=
                      ⟨sv₁.bits % 2 ^ (8 * uintByteSize w), Nat.mod_lt _ (Nat.two_pow_pos _)⟩
                    have hCEnc : b₁ = c.encode xWitness := by
                      rw [← hB₁]
                      exact (encodeLittleEndianBytes_mod_two_pow none (uintByteSize w) sv₁.bits).symm
                    have hB₁Len : b₁.length = uintByteSize w := by
                      rw [hCEnc]
                      exact c.encode_length xWitness
                    rw [replicateUninitBytes_add_eq (uintByteSize w) padBytes,
                        writeAbstractBytesAt_zero_replicateUninit b₁ (replicateUninitBytes padBytes)
                          hB₁Len] at hEnc
                    dsimp only [encodeFieldsAtOffsetsWith] at hEnc
                    injection hEnc with hBs
                    refine ⟨xWitness, ?_⟩
                    rw [← hBs, hCEnc, FixedByteCodec.padRight_encode_eq])
    (fun bs => by
      unfold defaultCodecFuel decodeValueFromBytes
      dsimp only
      rw [hLookup]
      dsimp only
      rw [hSize, hFields]
      dsimp only
      have hLenDef : Trusted.Sequence.length bs = bs.length := rfl
      rw [hLenDef]
      cases hBeq : Nat.beq bs.length (uintByteSize w + padBytes)
      · dsimp only
        have hNe : bs.length ≠ uintByteSize w + padBytes := by
          intro hEq
          rw [Nat.beq_eq.mpr hEq] at hBeq
          nomatch hBeq
        rw [(FixedByteCodec.padRight_isExactWidth c padBytes).decode_eq_none_of_length_ne hNe]
        rfl
      · dsimp only [decodeFieldsAtOffsetsWith]
        have hSz : rigidTyByteSize layouts { kind := .uint w, layoutIdx := 0 } =
            some (uintByteSize w) := m.tySize_eq
        rw [hSz]
        dsimp only [sliceAbstractBytes]
        rw [hLenDef]
        have hBsEq : bs.length = uintByteSize w + padBytes := Nat.eq_of_beq_eq_true hBeq
        have hBle : Nat.ble (Nat.add 0 (uintByteSize w)) bs.length = true :=
          Nat.ble_eq_true_of_le (by
            have h0 : Nat.add 0 (uintByteSize w) = uintByteSize w := Nat.zero_add _
            rw [h0]
            omega)
        rw [hBle]
        dsimp only [dropAbstractBytes]
        rw [takeAbstractBytes_eq_take]
        have hD₁ : decodeValueFromBytes 15 layouts { kind := .uint w, layoutIdx := 0 }
            (bs.take (uintByteSize w)) = (c.decode (bs.take (uintByteSize w))).map m.toValue :=
          m.decode_eq_map (bs.take (uintByteSize w))
        rw [hD₁]
        unfold FixedByteCodec.padRight FixedByteCodec.mapEquiv FixedByteCodec.prod
               FixedByteCodec.padUninit FixedByteCodec.ofRoundTrip
        dsimp only
        rw [hBeq]
        dsimp only
        have hDropLen : Nat.beq (bs.drop (uintByteSize w)).length padBytes = true := by
          apply Nat.beq_eq.mpr
          rw [List.length_drop]
          omega
        simp only [hDropLen, ↓reduceIte]
        cases c.decode (bs.take (uintByteSize w)) <;> rfl)

/--
Laid-out two-field integer tuple `(UintTy, UintTy)` backed by a concrete compiler
`TypeLayout` entry (`FieldsShape.arbitrary [{ bytes := 0 }, { bytes := uintByteSize w₁ + pad₁ }] memoryIndex`
and `l.size = { bytes := (uintByteSize w₁ + pad₁) + (uintByteSize w₂ + pad₂) }`),
bridged to `FixedByteCodec.prod (FixedByteCodec.padRight c₁ pad₁) (FixedByteCodec.padRight c₂ pad₂)`.

Models real `rustc` aggregate layouts with interior alignment padding (`0 < pad₁`,
such as `(u8, u32)` laid out at offsets `[0, 4]` with total size `8`) and/or
trailing alignment padding (`0 < pad₂`), proving pointwise equivalence against
`Trusted`'s `encodeFieldsAtOffsetsWith` and `decodeFieldsAtOffsetsWith`.
-/
def uintPairArbitraryTuple (layouts : LayoutTable) (w₁ w₂ : UintTy)
    (pad₁ pad₂ : Nat) (idx : LayoutIdx) (l : TypeLayout) (memoryIndex : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size = { bytes := (uintByteSize w₁ + pad₁) + (uintByteSize w₂ + pad₂) })
    (hFields : l.fields =
      .arbitrary [{ bytes := 0 }, { bytes := uintByteSize w₁ + pad₁ }] memoryIndex) :
    MirValueCodec layouts { kind := .tuple [.uint w₁, .uint w₂], layoutIdx := idx }
      ({ bits : Nat // bits < 2 ^ (8 * uintByteSize w₁) } ×
        { bits : Nat // bits < 2 ^ (8 * uintByteSize w₂) })
      ((uintByteSize w₁ + pad₁) + (uintByteSize w₂ + pad₂)) :=
  let c₁ := FixedByteCodec.uintBitsLE (uintByteSize w₁) (uintByteSize_pos w₁)
  let c₂ := FixedByteCodec.uintBitsLE (uintByteSize w₂) (uintByteSize_pos w₂)
  let p₁ := FixedByteCodec.padRight c₁ pad₁
  let p₂ := FixedByteCodec.padRight c₂ pad₂
  let m₁ := uint layouts w₁ 0
  let m₂ := uint layouts w₂ 0
  ofCanonicalEncode
    (FixedByteCodec.prod p₁ p₂)
    (fun ⟨a, b⟩ => .aggregate 0 [m₁.toValue a, m₂.toValue b])
    (fun v =>
      match v with
      | .aggregate 0 [v₁, v₂] =>
        match m₁.ofValue v₁, m₂.ofValue v₂ with
        | some a, some b => some (a, b)
        | _, _ => none
      | _ => none)
    (fun ⟨a, b⟩ => by
      simp only []
      rw [m₁.ofValue_toValue a, m₂.ofValue_toValue b])
    (by
      unfold rigidTyByteSize
      dsimp only [rigidTyKindByteSize]
      rw [hLookup]
      dsimp only
      rw [hSize])
    (fun ⟨a, b⟩ => by
      have ha : encodeValueToBytes 15 layouts { kind := .uint w₁, layoutIdx := 0 }
          (m₁.toValue a) = some (c₁.encode a) := m₁.encode_toValue a
      have hb : encodeValueToBytes 15 layouts { kind := .uint w₂, layoutIdx := 0 }
          (m₂.toValue b) = some (c₂.encode b) := m₂.encode_toValue b
      unfold defaultCodecFuel encodeValueToBytes
      simp only []
      have hLen2 : Nat.beq (Trusted.Sequence.length [m₁.toValue a, m₂.toValue b])
          (Trusted.Sequence.length [RigidTy.uint w₁, RigidTy.uint w₂]) = true := rfl
      rw [hLen2]
      dsimp only
      rw [hLookup]
      dsimp only
      rw [hFields, hSize]
      dsimp only
      have hOffLen : Nat.beq
          (Trusted.Sequence.length ([{ bytes := 0 }, { bytes := uintByteSize w₁ + pad₁ }] : List Size))
          (Trusted.Sequence.length [m₁.toValue a, m₂.toValue b]) = true := rfl
      rw [hOffLen]
      dsimp only [encodeFieldsAtOffsetsWith]
      rw [ha]
      dsimp only
      rw [replicateUninitBytes_add_eq (uintByteSize w₁ + pad₁) (uintByteSize w₂ + pad₂),
          replicateUninitBytes_add_eq (uintByteSize w₁) pad₁,
          replicateUninitBytes_add_eq (uintByteSize w₂) pad₂,
          List.append_assoc (replicateUninitBytes (uintByteSize w₁)) (replicateUninitBytes pad₁),
          writeAbstractBytesAt_zero_replicateUninit (c₁.encode a)
            (replicateUninitBytes pad₁ ++
              (replicateUninitBytes (uintByteSize w₂) ++ replicateUninitBytes pad₂))
            (c₁.encode_length a)]
      dsimp only [encodeFieldsAtOffsetsWith]
      rw [hb]
      dsimp only
      have hAssoc₁ :
          c₁.encode a ++
              (replicateUninitBytes pad₁ ++
                (replicateUninitBytes (uintByteSize w₂) ++ replicateUninitBytes pad₂)) =
            (c₁.encode a ++ replicateUninitBytes pad₁) ++
              replicateUninitBytes (uintByteSize w₂) ++ replicateUninitBytes pad₂ := by
        simp only [List.append_assoc]
      have hPreLen : (c₁.encode a ++ replicateUninitBytes pad₁).length = uintByteSize w₁ + pad₁ := by
        rw [List.length_append, c₁.encode_length a, length_replicateUninitBytes]
      rw [hAssoc₁,
          writeAbstractBytesAt_offset_replicateUninit
            (c₁.encode a ++ replicateUninitBytes pad₁) (c₂.encode b) (replicateUninitBytes pad₂)
            hPreLen (c₂.encode_length b)]
      dsimp only [encodeFieldsAtOffsetsWith]
      apply congrArg some
      dsimp only [FixedByteCodec.prod, p₁, p₂, FixedByteCodec.padRight,
                  FixedByteCodec.mapEquiv, FixedByteCodec.padUninit, FixedByteCodec.ofRoundTrip]
      simp only [List.append_assoc])
    (fun v bs hEnc => by
      unfold defaultCodecFuel encodeValueToBytes at hEnc
      cases v <;> dsimp only at hEnc
      case unit => nomatch hEnc
      case scalar => nomatch hEnc
      case ptr => nomatch hEnc
      case aggregate varIdx fs =>
        cases varIdx with
        | succ _ => nomatch hEnc
        | zero =>
          cases fs with
          | nil => nomatch hEnc
          | cons v₁ rest₁ =>
            cases rest₁ with
            | nil => nomatch hEnc
            | cons v₂ rest₂ =>
              cases rest₂ with
              | cons _ _ => nomatch hEnc
              | nil =>
                simp only [] at hEnc
                have hLen2 : Nat.beq (Trusted.Sequence.length [v₁, v₂])
                    (Trusted.Sequence.length [RigidTy.uint w₁, RigidTy.uint w₂]) = true := rfl
                rw [hLen2] at hEnc
                dsimp only at hEnc
                rw [hLookup] at hEnc
                dsimp only at hEnc
                rw [hFields, hSize] at hEnc
                dsimp only at hEnc
                have hOffLen : Nat.beq
                    (Trusted.Sequence.length ([{ bytes := 0 }, { bytes := uintByteSize w₁ + pad₁ }] : List Size))
                    (Trusted.Sequence.length [v₁, v₂]) = true := rfl
                rw [hOffLen] at hEnc
                dsimp only [encodeFieldsAtOffsetsWith] at hEnc
                cases hE₁ : encodeValueToBytes 15 layouts { kind := .uint w₁, layoutIdx := 0 } v₁ <;>
                  rw [hE₁] at hEnc
                · dsimp only [rigidTyKindByteSize] at hEnc
                  rw [intCastTargetBytes_uint_eq w₁] at hEnc
                  nomatch hEnc
                case some b₁ =>
                  dsimp only at hEnc
                  unfold encodeValueToBytes at hE₁
                  dsimp only at hE₁
                  rw [intCastTargetBytes_uint_eq w₁] at hE₁
                  cases v₁ <;> dsimp only at hE₁
                  case unit => nomatch hE₁
                  case ptr => nomatch hE₁
                  case aggregate => nomatch hE₁
                  case scalar sv₁ =>
                    cases hS₁ : Nat.beq sv₁.sizeBytes (uintByteSize w₁) <;> rw [hS₁] at hE₁
                    · nomatch hE₁
                    · have hSvSz₁ : sv₁.sizeBytes = uintByteSize w₁ := Nat.eq_of_beq_eq_true hS₁
                      unfold encodeScalarBytes at hE₁
                      rw [hSvSz₁] at hE₁
                      have hNz₁ : Nat.beq (uintByteSize w₁) 0 = false :=
                        nat_beq_eq_false_of_ne (by have := uintByteSize_pos w₁; omega)
                      rw [hNz₁] at hE₁
                      injection hE₁ with hB₁
                      let x₁ : { bits : Nat // bits < 2 ^ (8 * uintByteSize w₁) } :=
                        ⟨sv₁.bits % 2 ^ (8 * uintByteSize w₁), Nat.mod_lt _ (Nat.two_pow_pos _)⟩
                      have hCEnc₁ : b₁ = c₁.encode x₁ := by
                        rw [← hB₁]
                        exact (encodeLittleEndianBytes_mod_two_pow none (uintByteSize w₁) sv₁.bits).symm
                      have hB₁Len : b₁.length = uintByteSize w₁ := by
                        rw [hCEnc₁]
                        exact c₁.encode_length x₁
                      rw [replicateUninitBytes_add_eq (uintByteSize w₁ + pad₁) (uintByteSize w₂ + pad₂),
                          replicateUninitBytes_add_eq (uintByteSize w₁) pad₁,
                          replicateUninitBytes_add_eq (uintByteSize w₂) pad₂,
                          List.append_assoc (replicateUninitBytes (uintByteSize w₁)) (replicateUninitBytes pad₁),
                          writeAbstractBytesAt_zero_replicateUninit b₁
                            (replicateUninitBytes pad₁ ++
                              (replicateUninitBytes (uintByteSize w₂) ++ replicateUninitBytes pad₂))
                            hB₁Len] at hEnc
                      dsimp only [encodeFieldsAtOffsetsWith] at hEnc
                      cases hE₂ : encodeValueToBytes 15 layouts { kind := .uint w₂, layoutIdx := 0 } v₂ <;>
                        rw [hE₂] at hEnc
                      · dsimp only [rigidTyKindByteSize] at hEnc
                        rw [intCastTargetBytes_uint_eq w₂] at hEnc
                        nomatch hEnc
                      case some b₂ =>
                        dsimp only at hEnc
                        unfold encodeValueToBytes at hE₂
                        dsimp only at hE₂
                        rw [intCastTargetBytes_uint_eq w₂] at hE₂
                        cases v₂ <;> dsimp only at hE₂
                        case unit => nomatch hE₂
                        case ptr => nomatch hE₂
                        case aggregate => nomatch hE₂
                        case scalar sv₂ =>
                          cases hS₂ : Nat.beq sv₂.sizeBytes (uintByteSize w₂) <;> rw [hS₂] at hE₂
                          · nomatch hE₂
                          · have hSvSz₂ : sv₂.sizeBytes = uintByteSize w₂ := Nat.eq_of_beq_eq_true hS₂
                            unfold encodeScalarBytes at hE₂
                            rw [hSvSz₂] at hE₂
                            have hNz₂ : Nat.beq (uintByteSize w₂) 0 = false :=
                              nat_beq_eq_false_of_ne (by have := uintByteSize_pos w₂; omega)
                            rw [hNz₂] at hE₂
                            injection hE₂ with hB₂
                            let x₂ : { bits : Nat // bits < 2 ^ (8 * uintByteSize w₂) } :=
                              ⟨sv₂.bits % 2 ^ (8 * uintByteSize w₂), Nat.mod_lt _ (Nat.two_pow_pos _)⟩
                            have hCEnc₂ : b₂ = c₂.encode x₂ := by
                              rw [← hB₂]
                              exact (encodeLittleEndianBytes_mod_two_pow none (uintByteSize w₂) sv₂.bits).symm
                            have hB₂Len : b₂.length = uintByteSize w₂ := by
                              rw [hCEnc₂]
                              exact c₂.encode_length x₂
                            have hAssoc₁ :
                                b₁ ++
                                    (replicateUninitBytes pad₁ ++
                                      (replicateUninitBytes (uintByteSize w₂) ++ replicateUninitBytes pad₂)) =
                                  (b₁ ++ replicateUninitBytes pad₁) ++
                                    replicateUninitBytes (uintByteSize w₂) ++ replicateUninitBytes pad₂ := by
                              simp only [List.append_assoc]
                            have hPreLen : (b₁ ++ replicateUninitBytes pad₁).length =
                                uintByteSize w₁ + pad₁ := by
                              rw [List.length_append, hB₁Len, length_replicateUninitBytes]
                            rw [hAssoc₁,
                                writeAbstractBytesAt_offset_replicateUninit
                                  (b₁ ++ replicateUninitBytes pad₁) b₂ (replicateUninitBytes pad₂)
                                  hPreLen hB₂Len] at hEnc
                            dsimp only [encodeFieldsAtOffsetsWith] at hEnc
                            injection hEnc with hBs
                            refine ⟨(x₁, x₂), ?_⟩
                            rw [← hBs, hCEnc₁, hCEnc₂]
                            dsimp only [FixedByteCodec.prod, p₁, p₂, FixedByteCodec.padRight,
                                        FixedByteCodec.mapEquiv, FixedByteCodec.padUninit,
                                        FixedByteCodec.ofRoundTrip]
                            simp only [List.append_assoc])
    (fun bs => by
      unfold defaultCodecFuel decodeValueFromBytes
      dsimp only
      rw [hLookup]
      dsimp only
      rw [hSize, hFields]
      dsimp only
      have hLenDef : Trusted.Sequence.length bs = bs.length := rfl
      rw [hLenDef]
      let totalSz := (uintByteSize w₁ + pad₁) + (uintByteSize w₂ + pad₂)
      cases hBeq : Nat.beq bs.length totalSz
      · dsimp only
        have hNe : bs.length ≠ totalSz := by
          intro hEq
          rw [Nat.beq_eq.mpr hEq] at hBeq
          nomatch hBeq
        rw [(FixedByteCodec.prod_isExactWidth p₁ p₂).decode_eq_none_of_length_ne hNe]
        rfl
      · dsimp only [decodeFieldsAtOffsetsWith]
        have hSz₁ : rigidTyByteSize layouts { kind := .uint w₁, layoutIdx := 0 } =
            some (uintByteSize w₁) := m₁.tySize_eq
        have hSz₂ : rigidTyByteSize layouts { kind := .uint w₂, layoutIdx := 0 } =
            some (uintByteSize w₂) := m₂.tySize_eq
        rw [hSz₁]
        dsimp only [sliceAbstractBytes]
        rw [hLenDef]
        have hBsEq : bs.length = (uintByteSize w₁ + pad₁) + (uintByteSize w₂ + pad₂) :=
          Nat.eq_of_beq_eq_true hBeq
        have hBle₁ : Nat.ble (Nat.add 0 (uintByteSize w₁)) bs.length = true :=
          Nat.ble_eq_true_of_le (by
            have h0 : Nat.add 0 (uintByteSize w₁) = uintByteSize w₁ := Nat.zero_add _
            rw [h0]
            omega)
        rw [hBle₁]
        dsimp only [dropAbstractBytes]
        have hMC₁ : m₁.codec = c₁ := rfl
        have hMC₂ : m₂.codec = c₂ := rfl
        rw [takeAbstractBytes_eq_take, m₁.decode_eq_map (bs.take (uintByteSize w₁)), hMC₁]
        have hBle₂ : Nat.ble (Nat.add (uintByteSize w₁ + pad₁) (uintByteSize w₂)) bs.length = true :=
          Nat.ble_eq_true_of_le (by
            have hAdd : Nat.add (uintByteSize w₁ + pad₁) (uintByteSize w₂) =
                (uintByteSize w₁ + pad₁) + uintByteSize w₂ := rfl
            rw [hAdd]
            omega)
        have hTakeLen₁ : (bs.take (uintByteSize w₁ + pad₁)).length = uintByteSize w₁ + pad₁ := by
          rw [List.length_take]
          omega
        have hDropLen₂ : (bs.drop (uintByteSize w₁ + pad₁)).length = uintByteSize w₂ + pad₂ := by
          rw [List.length_drop]
          omega
        have hTakeTake :
            (bs.take (uintByteSize w₁ + pad₁)).take (uintByteSize w₁) =
              bs.take (uintByteSize w₁) := by
          rw [List.take_take]
          exact congrArg (fun k => bs.take k) (Nat.min_eq_left (by omega))
        unfold FixedByteCodec.prod FixedByteCodec.ofRoundTrip
        dsimp only
        rw [hBeq]
        dsimp only
        have hP₁ : p₁.decode (bs.take (uintByteSize w₁ + pad₁)) =
            c₁.decode (bs.take (uintByteSize w₁)) := by
          dsimp only [p₁]
          rw [FixedByteCodec.padRight_decode_of_length_eq c₁ hTakeLen₁, hTakeTake]
        have hP₂ : p₂.decode (bs.drop (uintByteSize w₁ + pad₁)) =
            c₂.decode ((bs.drop (uintByteSize w₁ + pad₁)).take (uintByteSize w₂)) := by
          dsimp only [p₂]
          exact FixedByteCodec.padRight_decode_of_length_eq c₂ hDropLen₂
        rw [hP₁, hP₂]
        cases c₁.decode (bs.take (uintByteSize w₁)) with
        | none => rfl
        | some a =>
          dsimp only [Option.map, decodeFieldsAtOffsetsWith]
          rw [hSz₂]
          dsimp only [sliceAbstractBytes]
          rw [hBle₂]
          dsimp only
          rw [dropAbstractBytes_eq_drop, takeAbstractBytes_eq_take,
              m₂.decode_eq_map ((bs.drop (uintByteSize w₁ + pad₁)).take (uintByteSize w₂)), hMC₂]
          cases c₂.decode ((bs.drop (uintByteSize w₁ + pad₁)).take (uintByteSize w₂)) <;> rfl)

/--
`MirValueCodec` for a single-field scalar-niche newtype wrapper `.adt defPath []`
(`l.fields = .arbitrary [{ bytes := 0 }] memoryOrder`, `l.fieldLayouts = []`,
`l.variants = .single varIdx`, `l.backendRepr = .scalar (.initialized pk range)`),
matching the newtype `NonZero*` shape analyzed in `Anneal.BitValidity` §6.4
(`decodeValueFromBytes_adt_newtype_scalarLayout`).

Values decode to and encode from `.aggregate varIdx [.scalar ⟨x.val, sz⟩]`.

**Divergence (monomorphized `NonZero<T>` type-argument niche & untyped `IsIntoBytes` on `.adt _ []` newtypes):**
1. **Divergence (`args = [T]` monomorphized niche):** On the monomorphized type
   `.adt "core::num::NonZero" [.uint .u32]`, `args.length == offsets.length`, so `Trusted`'s
   `decodeValueFromBytes` takes the `byArgs` type-argument path and decodes the field at
   `.uint .u32` without inspecting `l.backendRepr` (`adt_generic_nonZero_typeArg_path_niche_unenforced`).
   Consequently, `zeroInitBytes 4` is accepted (`IsFromZeros` holds) and **no zero-rejecting niche
   `MirValueCodec` can exist** for `.adt defPath [.uint .u32]` (`monomorphized_nonZero_u32_forces_hasZeroValid`).
2. **Divergence (`args = []` untyped-field encoder fallback vs. `zerocopy::IntoBytes`):** In Rust /
   `zerocopy`, `NonZeroU32` (and every `NonZero*`) *is* `IntoBytes` because it has no padding bytes.
   On `.adt defPath []` (`args = []`), `decodeValueFromBytes` enforces the `l.backendRepr` niche,
   and every well-typed/decoded value encodes to `sz` initialized bytes (`transmute_typed` and
   `transmute_sound_of_decoded` model sound `IntoBytes` transmutation from `NonZero*`). However,
   untyped `BitValidity.IsIntoBytes` fails (`enforcesUntypedFieldWidths = false`) solely because
   `Trusted`'s `encodeValueToBytes` falls back to `encodeUntypedValueToBytes` when `args = []`,
   allowing the ill-typed 0-byte field `.aggregate varIdx [.unit]` to encode to
   `replicateUninitBytes sz` (`scalarNicheNewtype_untyped_unit_field_divergence`).
-/
def scalarNicheNewtypeNonPtr
    (layouts : LayoutTable) (defPath : DefPath) (idx : LayoutIdx)
    (l : TypeLayout) (sz : Nat) (pk : PrimitiveKind) (varIdx : VariantIdx)
    (memoryOrder : List Nat) (range : WrappingRange)
    (hNz : 0 < sz)
    (hNonPtr : FixedByteCodec.isNonPointerPrimitiveKind pk = true)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hSize : l.size.bytes = sz)
    (hFields : l.fields = .arbitrary [{ bytes := 0 }] memoryOrder)
    (hNoFieldLayouts : l.fieldLayouts = [])
    (hVar : l.variants = .single varIdx)
    (hRepr : l.backendRepr = .scalar (.initialized pk range))
    (hWidth : primitiveKindByteWidth pk = some sz) :
    MirValueCodec layouts { kind := .adt defPath [], layoutIdx := idx }
      { bits : Nat // bits < 2 ^ (8 * sz) ∧ wrappingRangeContains range bits = true } sz where
  codec := FixedByteCodec.scalarValidRange sz hNz range
  toValue := fun x => .aggregate varIdx [.scalar ⟨x.val, sz⟩]
  ofValue := fun v =>
    match v with
    | .aggregate vIdx [.scalar sv] =>
      if vIdx == varIdx && sv.sizeBytes == sz then
        if h : sv.bits < 2 ^ (8 * sz) ∧ wrappingRangeContains range sv.bits = true then
          some ⟨sv.bits, h⟩
        else none
      else none
    | _ => none
  ofValue_toValue := fun ⟨bits, hProp⟩ => by
    simp [hProp]
  tySize_eq := by
    unfold rigidTyByteSize rigidTyKindByteSize
    rw [hLookup]
    exact congrArg some hSize
  encode_toValue := fun ⟨bits, hProp⟩ => by
    unfold defaultCodecFuel encodeValueToBytes
    dsimp only
    rw [hLookup]
    dsimp only
    rw [hInhab]
    dsimp only
    rw [hVar]
    dsimp only
    rw [hFields, hSize]
    dsimp only
    have hCond :
        Bool.and (Nat.beq varIdx varIdx)
          (Nat.beq (Trusted.Sequence.length ([{ bytes := 0 }] : List Size))
            (Trusted.Sequence.length [Value.scalar ⟨bits, sz⟩])) = true := by
      rw [nat_beq_self varIdx]
      rfl
    rw [hCond]
    dsimp only
    have hArgsNe : Nat.beq (Trusted.Sequence.length ([] : List RigidTy))
        (Trusted.Sequence.length ([{ bytes := 0 }] : List Size)) = false := rfl
    rw [hArgsNe]
    dsimp only [encodeFieldsAtOffsetsWith, encodeUntypedValueToBytes]
    unfold encodeScalarBytes
    have hBeq0 : Nat.beq sz 0 = false := nat_beq_eq_false_of_ne (by omega)
    dsimp only
    rw [hBeq0]
    dsimp only
    have hWrite :
        writeAbstractBytesAt (replicateUninitBytes sz) 0
          (encodeLittleEndianBytes bits sz none) =
        some (encodeLittleEndianBytes bits sz none) := by
      have hRep : replicateUninitBytes sz = replicateUninitBytes sz ++ [] :=
        (List.append_nil _).symm
      rw [hRep,
          writeAbstractBytesAt_zero_replicateUninit
            (encodeLittleEndianBytes bits sz none) []
            (length_encodeLittleEndianBytes none sz bits),
          List.append_nil]
    rw [hWrite]
    rfl
  enforcesUntypedFieldWidths := false
  encode_length_and_init_of_isInit := fun h => nomatch h
  decode_eq_map := fun bs => by
    have hScalarWidth : scalarLayoutByteWidth (.initialized pk range) = some l.size.bytes := by
      unfold scalarLayoutByteWidth
      dsimp only
      rw [hWidth, hSize]
    rw [show defaultCodecFuel = 15 + 1 from rfl,
        decodeValueFromBytes_adt_newtype_scalarLayout 15 layouts defPath idx l varIdx
          memoryOrder (.initialized pk range) hLookup hInhab hVar hFields hNoFieldLayouts
          hRepr hScalarWidth]
    have hLenDef : Trusted.Sequence.length bs = bs.length := rfl
    rw [hLenDef, hSize]
    cases hLen : Nat.beq bs.length sz
    · have hNe : bs.length ≠ sz := fun hEq => by
        rw [Nat.beq_eq.mpr hEq] at hLen; nomatch hLen
      rw [(FixedByteCodec.scalarValidRange_isExactWidth sz hNz range).decode_eq_none_of_length_ne hNe]
      rfl
    · dsimp only
      rw [FixedByteCodec.decodeScalarLayoutBytes_initialized_nonPtr_eq_scalarValidRange_map
            pk range sz hNz hNonPtr hWidth bs]
      cases (FixedByteCodec.scalarValidRange sz hNz range).decode bs <;> rfl

/--
Integer specialization of `scalarNicheNewtypeNonPtr` for single-field scalar-niche
newtype ADTs `.adt defPath []` (such as newtype `NonZeroU8` / `NonZeroU32` with
`l.fields = .arbitrary [{ bytes := 0 }] memoryOrder` and `l.fieldLayouts = []`).

See `scalarNicheNewtypeNonPtr` for the **Divergence** notes on monomorphized
`NonZero<T>` (`args = [T]`) and `Trusted`'s `args = []` untyped-field encoder
fallback versus `zerocopy::IntoBytes` (modeled for well-typed/decoded values via
`transmute_typed` and `transmute_sound_of_decoded`).
-/
def scalarNicheNewtype
    (layouts : LayoutTable) (defPath : DefPath) (idx : LayoutIdx)
    (l : TypeLayout) (sz bitsWidth : Nat) (signed : Bool) (varIdx : VariantIdx)
    (memoryOrder : List Nat) (range : WrappingRange)
    (hNz : 0 < sz)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hSize : l.size.bytes = sz)
    (hFields : l.fields = .arbitrary [{ bytes := 0 }] memoryOrder)
    (hNoFieldLayouts : l.fieldLayouts = [])
    (hVar : l.variants = .single varIdx)
    (hRepr : l.backendRepr = .scalar (.initialized (.int bitsWidth signed) range))
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some sz) :
    MirValueCodec layouts { kind := .adt defPath [], layoutIdx := idx }
      { bits : Nat // bits < 2 ^ (8 * sz) ∧ wrappingRangeContains range bits = true } sz :=
  scalarNicheNewtypeNonPtr layouts defPath idx l sz (.int bitsWidth signed) varIdx
    memoryOrder range hNz rfl hLookup hInhab hSize hFields hNoFieldLayouts hVar hRepr hWidth

/--
**Divergence (Trusted untyped-field encoder fallback vs. `zerocopy::IntoBytes`):**
In Rust / `zerocopy`, single-field scalar-niche newtypes such as `NonZeroU32` *are*
`IntoBytes` because they contain no padding bytes (modeled for well-typed/decoded
values via `transmute_typed` and `transmute_sound_of_decoded`). In `Trusted`, on
`.adt defPath []` with `l.fields = .arbitrary [{ bytes := 0 }] memoryOrder` and `0 < sz`,
`encodeValueToBytes` falls back to `encodeUntypedValueToBytes` when `args = []`, so
passing the ill-typed 0-byte field `.aggregate varIdx [.unit]` returns
`some (replicateUninitBytes sz)` and falsifies untyped `BitValidity.IsIntoBytes`.
-/
theorem scalarNicheNewtype_untyped_unit_field_divergence
    (layouts : LayoutTable) (defPath : DefPath) (idx : LayoutIdx)
    (l : TypeLayout) (sz : Nat) (varIdx : VariantIdx) (memoryOrder : List Nat)
    (hNz : 0 < sz)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hSize : l.size.bytes = sz)
    (hFields : l.fields = .arbitrary [{ bytes := 0 }] memoryOrder)
    (hVar : l.variants = .single varIdx) :
    encodeValueToBytes defaultCodecFuel layouts { kind := .adt defPath [], layoutIdx := idx }
        (.aggregate varIdx [.unit]) = some (replicateUninitBytes sz) ∧
    ¬ IsIntoBytes layouts { kind := .adt defPath [], layoutIdx := idx } := by
  have hEncUnit :
      encodeValueToBytes defaultCodecFuel layouts { kind := .adt defPath [], layoutIdx := idx }
        (.aggregate varIdx [.unit]) = some (replicateUninitBytes sz) := by
    unfold defaultCodecFuel encodeValueToBytes
    dsimp only
    rw [hLookup]
    dsimp only
    rw [hInhab]
    dsimp only
    rw [hVar]
    dsimp only
    rw [hFields, hSize]
    dsimp only
    have hCond :
        Bool.and (Nat.beq varIdx varIdx)
          (Nat.beq (Trusted.Sequence.length ([{ bytes := 0 }] : List Size))
            (Trusted.Sequence.length [Value.unit])) = true := by
      rw [nat_beq_self varIdx]
      rfl
    rw [hCond]
    dsimp only
    have hArgsNe : Nat.beq (Trusted.Sequence.length ([] : List RigidTy))
        (Trusted.Sequence.length ([{ bytes := 0 }] : List Size)) = false := rfl
    rw [hArgsNe]
    dsimp only [encodeFieldsAtOffsetsWith, encodeUntypedValueToBytes, writeAbstractBytesAt]
    cases sz with
    | zero => omega
    | succ _ => rfl
  refine ⟨hEncUnit, ?_⟩
  rintro ⟨_, _, hEncProps⟩
  have ⟨_, hInit⟩ := hEncProps (.aggregate varIdx [.unit]) (replicateUninitBytes sz) hEncUnit
  rw [allBytesInitialized_replicateUninitBytes_eq_false hNz] at hInit
  nomatch hInit

/--
Impossibility of a zero-rejecting niche `MirValueCodec` on monomorphized
`NonZero<u32>` (`.adt defPath [.uint .u32]`): because `args.length == offsets.length`,
`Trusted`'s `decodeValueFromBytes` decodes the field at `.uint .u32` and ignores
`l.backendRepr` (`adt_generic_nonZero_typeArg_path_niche_unenforced`), so `IsFromZeros`
holds and *every* `MirValueCodec` for `{ kind := .adt defPath [.uint .u32], layoutIdx := idx }`
must satisfy `m.codec.HasZeroValid`.
-/
theorem monomorphized_nonZero_u32_forces_hasZeroValid
    (layouts : LayoutTable) (defPath : DefPath) (idx : LayoutIdx)
    (l : TypeLayout) (varIdx : VariantIdx) (memoryOrder : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single varIdx)
    (hFields : l.fields = .arbitrary [{ bytes := 0 }] memoryOrder)
    (hSz : l.size.bytes = 4)
    (hRepr : l.backendRepr = .scalar (.initialized (.int 32 false) ⟨1, scalarModulus 4 - 1⟩)) :
    IsFromZeros layouts { kind := .adt defPath [.uint .u32], layoutIdx := idx } ∧
    ∀ {α : Type} (m : MirValueCodec layouts { kind := .adt defPath [.uint .u32], layoutIdx := idx } α 4),
      m.codec.HasZeroValid := by
  have ⟨_, hDec0, hFz⟩ :=
    adt_generic_nonZero_typeArg_path_niche_unenforced
      layouts defPath idx l varIdx memoryOrder hLookup hInhab hVar hFields hSz hRepr
  refine ⟨hFz, ?_⟩
  intro α m
  rw [m.decode_eq_map (zeroInitBytes 4)] at hDec0
  cases hC : m.codec.decode (zeroInitBytes 4) <;> rw [hC] at hDec0
  · nomatch hDec0
  case some x₀ =>
    exact ⟨x₀, hC⟩

/--
`MirValueCodec` for a real multi-variant fieldless `#[repr(uN)]` / `#[repr(Int)]` enum
`.adt defPath args` (`l.variants = .multiple (.initialized (.int bitsWidth signed) validRange) 0 variantShapes`,
`l.fields = .arbitrary [{ bytes := 0 }] memoryOrder`), bridged to
`FixedByteCodec.enumRepr sz hNz toTag ofTag hRound hBounds` with `toValue e = .aggregate (toTag e) []`
under `Trusted`'s direct variant-index discriminant discipline (`0 .. k - 1`).

Proves full `enforcesUntypedFieldWidths := true` (`IsIntoBytes` via
`BitValidity.adt_multiple_enum_fieldless_isIntoBytes`) and pointwise `decode_eq_map`
via `BitValidity.decodeValueFromBytes_adt_multiple_enum_scalarLayout`.
-/
def fieldlessEnum {ε : Type}
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (sz bitsWidth : Nat) (signed : Bool) (validRange : WrappingRange)
    (variantShapes : List FieldsShape) (memoryOrder : List Nat)
    (toTag : ε → Nat) (ofTag : Nat → Option ε)
    (hRound : ∀ e : ε, ofTag (toTag e) = some e)
    (hBounds : ∀ e : ε, toTag e < 2 ^ (8 * sz))
    (hNz : 0 < sz)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hSize : l.size.bytes = sz)
    (hVar : l.variants = .multiple (.initialized (.int bitsWidth signed) validRange) 0 variantShapes)
    (hFields : l.fields = .arbitrary [{ bytes := 0 }] memoryOrder)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some sz)
    (hAllFieldless :
      ∀ (varIdx : Nat) (varOffsets : List Size) (varMemOrder : List Nat),
        Trusted.Sequence.get? variantShapes varIdx = some (.arbitrary varOffsets varMemOrder) →
        varOffsets = [])
    (hTagValid :
      ∀ e : ε,
        wrappingRangeContains validRange (toTag e) = true ∧
        ∃ vm, Trusted.Sequence.get? variantShapes (toTag e) = some (.arbitrary [] vm))
    (hTagComplete :
      ∀ (t : Nat) (varShape : FieldsShape),
        t < 2 ^ (8 * sz) →
        wrappingRangeContains validRange t = true →
        Trusted.Sequence.get? variantShapes t = some varShape →
        ∃ e : ε, toTag e = t) :
    MirValueCodec layouts { kind := .adt defPath args, layoutIdx := idx } ε sz where
  codec := FixedByteCodec.enumRepr sz hNz toTag ofTag hRound hBounds
  toValue := fun e => .aggregate (toTag e) []
  ofValue := fun v =>
    match v with
    | .aggregate tag [] =>
      match ofTag tag with
      | some e => if Nat.beq (toTag e) tag then some e else none
      | none => none
    | _ => none
  ofValue_toValue := fun e => by
    simp only []
    rw [hRound e]
    dsimp only
    rw [nat_beq_self (toTag e)]
    rfl
  tySize_eq := by
    unfold rigidTyByteSize rigidTyKindByteSize
    rw [hLookup]
    exact congrArg some hSize
  encode_toValue := fun e => by
    rcases (hTagValid e).2 with ⟨vm, hGetVar⟩
    have hScalarWidth :
        scalarLayoutByteWidth (.initialized (.int bitsWidth signed) validRange) = some sz :=
      hWidth
    unfold defaultCodecFuel encodeValueToBytes
    dsimp only
    rw [hLookup]
    dsimp only
    rw [hInhab]
    dsimp only
    rw [hVar]
    dsimp only
    rw [hFields, hScalarWidth, hGetVar]
    dsimp only
    have hGet0 : Trusted.Sequence.get? ([{ bytes := 0 }] : List Size) 0 = some { bytes := 0 } := rfl
    rw [hGet0, hSize]
    dsimp only
    unfold encodeScalarBytes
    have hBeq0 : Nat.beq sz 0 = false := nat_beq_eq_false_of_ne (by omega)
    dsimp only
    rw [hBeq0]
    dsimp only
    have hWrite :
        writeAbstractBytesAt (replicateUninitBytes sz) 0
          (encodeLittleEndianBytes (toTag e) sz none) =
        some (encodeLittleEndianBytes (toTag e) sz none) := by
      have hRep : replicateUninitBytes sz = replicateUninitBytes sz ++ [] :=
        (List.append_nil _).symm
      rw [hRep,
          writeAbstractBytesAt_zero_replicateUninit
            (encodeLittleEndianBytes (toTag e) sz none) []
            (length_encodeLittleEndianBytes none sz (toTag e)),
          List.append_nil]
    rw [hWrite]
    rfl
  enforcesUntypedFieldWidths := true
  encode_length_and_init_of_isInit := fun _ _ v bs hEnc => by
    have hScalarWidth :
        scalarLayoutByteWidth (.initialized (.int bitsWidth signed) validRange) =
          some l.size.bytes := by
      unfold scalarLayoutByteWidth
      dsimp only
      rw [hWidth, hSize]
    rcases adt_multiple_enum_fieldless_isIntoBytes layouts defPath args idx l
        (.initialized (.int bitsWidth signed) validRange) variantShapes memoryOrder
        hLookup hInhab hVar hFields hScalarWidth hAllFieldless with ⟨sz', hSz', hInto⟩
    have hSzEq : sz' = sz := by
      unfold rigidTyByteSize rigidTyKindByteSize at hSz'
      rw [hLookup] at hSz'
      dsimp only at hSz'
      rw [hSize] at hSz'
      exact Option.some.inj hSz'.symm
    subst hSzEq
    exact hInto v bs hEnc
  decode_eq_map := fun bs => by
    have hScalarWidth :
        scalarLayoutByteWidth (.initialized (.int bitsWidth signed) validRange) =
          some l.size.bytes := by
      unfold scalarLayoutByteWidth
      dsimp only
      rw [hWidth, hSize]
    rw [show defaultCodecFuel = 15 + 1 from rfl,
        decodeValueFromBytes_adt_multiple_enum_scalarLayout 15 layouts defPath args idx l
          (.initialized (.int bitsWidth signed) validRange) variantShapes memoryOrder
          hLookup hInhab hVar hFields hScalarWidth]
    have hLenDef : Trusted.Sequence.length bs = bs.length := rfl
    rw [hLenDef, hSize]
    let enumC := FixedByteCodec.enumRepr sz hNz toTag ofTag hRound hBounds
    cases hLen : Nat.beq bs.length sz
    · have hNe : bs.length ≠ sz := fun hEq => by
        rw [Nat.beq_eq.mpr hEq] at hLen; nomatch hLen
      rw [(FixedByteCodec.enumRepr_isExactWidth sz hNz toTag ofTag hRound hBounds).decode_eq_none_of_length_ne hNe]
      rfl
    · dsimp only
      rw [FixedByteCodec.decodeScalarLayoutBytes_initialized_int_eq_scalarValidRange_map
            bitsWidth signed validRange sz hNz hWidth bs]
      unfold FixedByteCodec.scalarValidRange FixedByteCodec.mapEquiv
             FixedByteCodec.refineNiche FixedByteCodec.ofRoundTrip
      dsimp only
      cases hU : (FixedByteCodec.uintBitsLE sz hNz).decode bs with
      | none =>
        have hENone : enumC.decode bs = none := by
          unfold enumC FixedByteCodec.enumRepr FixedByteCodec.ofRoundTrip
          dsimp only
          rw [hU]
          rfl
        rw [hENone]
        rfl
      | some x =>
        rcases x with ⟨t, ht⟩
        dsimp only
        cases hEnumDec : enumC.decode bs with
        | some e =>
          have hSome := (FixedByteCodec.enumRepr_decode_eq_some_iff
            sz hNz toTag ofTag hRound hBounds bs e).mp hEnumDec
          rw [hU] at hSome
          injection hSome with hSub
          have hTEq : t = toTag e := congrArg Subtype.val hSub
          subst hTEq
          rcases hTagValid e with ⟨hRangeTrue, vm, hGetVar⟩
          simp only [hRangeTrue, ↓reduceDIte, Option.map_some]
          rw [hGetVar]
        | none =>
          dsimp only [Option.map]
          by_cases hRange : wrappingRangeContains validRange t = true
          · simp only [hRange, ↓reduceDIte]
            cases hGet : Trusted.Sequence.get? variantShapes t with
            | none => rfl
            | some varShape =>
              rcases hTagComplete t varShape ht hRange hGet with ⟨e, hTagEq⟩
              have hMustDecode : enumC.decode bs = some e := by
                apply (FixedByteCodec.enumRepr_decode_eq_some_iff
                  sz hNz toTag ofTag hRound hBounds bs e).mpr
                rw [hU]
                exact congrArg some (Subtype.ext hTagEq.symm)
              rw [hMustDecode] at hEnumDec
              nomatch hEnumDec
          · have hRangeFalse : wrappingRangeContains validRange t = false :=
              Bool.eq_false_iff.mpr hRange
            simp only [hRangeFalse, Bool.false_eq_true, ↓reduceDIte]

end MirValueCodec

/-! ## 5. Structural Termination Helpers (`sizeOf_lt_*`) & Fuel-Free Recursion -/

/-- Generic list-membership `sizeOf` bound (`sizeOf x < sizeOf xs` when `x ∈ xs`). -/
theorem sizeOf_lt_of_mem_list {α : Type} [SizeOf α] {x : α} {xs : List α}
    (h : x ∈ xs) : sizeOf x < sizeOf xs :=
  List.sizeOf_lt_of_mem h

theorem sizeOf_lt_of_mem_tuple_fields {f : RigidTy} {fields : List RigidTy}
    (h : f ∈ fields) : sizeOf f < sizeOf (RigidTy.tuple fields) := by
  have hMem := List.sizeOf_lt_of_mem h
  simp_all only [RigidTy.tuple.sizeOf_spec]
  omega

theorem sizeOf_lt_of_mem_adt_args (defPath : DefPath) {a : RigidTy} {args : List RigidTy}
    (h : a ∈ args) : sizeOf a < sizeOf (RigidTy.adt defPath args) := by
  have hMem := List.sizeOf_lt_of_mem h
  simp_all only [RigidTy.adt.sizeOf_spec]
  omega

theorem sizeOf_lt_of_mem_alias_args (defPath : DefPath) {a : RigidTy} {args : List RigidTy}
    (h : a ∈ args) : sizeOf a < sizeOf (RigidTy.alias defPath args) := by
  have hMem := List.sizeOf_lt_of_mem h
  simp_all only [RigidTy.alias.sizeOf_spec]
  omega

theorem sizeOf_lt_of_mem_fnDef_args (defPath : DefPath) {a : RigidTy} {args : List RigidTy}
    (h : a ∈ args) : sizeOf a < sizeOf (RigidTy.fnDef defPath args) := by
  have hMem := List.sizeOf_lt_of_mem h
  simp_all only [RigidTy.fnDef.sizeOf_spec]
  omega

theorem sizeOf_lt_of_mem_fnPtr_inputs
    {inp : RigidTy} {inputs : List RigidTy}
    (output : RigidTy) (safety : Safety) (abi : CallConv)
    (h : inp ∈ inputs) :
    sizeOf inp < sizeOf (RigidTy.fnPtr inputs output safety abi) := by
  have hMem := List.sizeOf_lt_of_mem h
  simp_all only [RigidTy.fnPtr.sizeOf_spec]
  omega

theorem sizeOf_lt_output_of_fnPtr
    (inputs : List RigidTy) (output : RigidTy) (safety : Safety) (abi : CallConv) :
    sizeOf output < sizeOf (RigidTy.fnPtr inputs output safety abi) := by
  simp only [RigidTy.fnPtr.sizeOf_spec]
  omega

theorem sizeOf_lt_of_mem_closure_upvars (defPath : DefPath) {u : RigidTy} {upvars : List RigidTy}
    (h : u ∈ upvars) : sizeOf u < sizeOf (RigidTy.closure defPath upvars) := by
  have hMem := List.sizeOf_lt_of_mem h
  simp_all only [RigidTy.closure.sizeOf_spec]
  omega

theorem sizeOf_lt_elem_of_array (elem : RigidTy) (len : Nat) :
    sizeOf elem < sizeOf (RigidTy.array elem len) := by
  simp only [RigidTy.array.sizeOf_spec]
  omega

theorem sizeOf_lt_elem_of_slice (elem : RigidTy) :
    sizeOf elem < sizeOf (RigidTy.slice elem) := by
  simp only [RigidTy.slice.sizeOf_spec]
  omega

theorem sizeOf_lt_pointee_of_ref (mutability : Mutability) (pointee : RigidTy) :
    sizeOf pointee < sizeOf (RigidTy.ref mutability pointee) := by
  simp only [RigidTy.ref.sizeOf_spec]
  omega

theorem sizeOf_lt_pointee_of_rawPtr (mutability : Mutability) (pointee : RigidTy) :
    sizeOf pointee < sizeOf (RigidTy.rawPtr mutability pointee) := by
  simp only [RigidTy.rawPtr.sizeOf_spec]
  omega

theorem sizeOf_lt_of_mem_aggregate_fields
    (variantIdx : VariantIdx) {v : Value} {fields : List Value}
    (h : v ∈ fields) : sizeOf v < sizeOf (Value.aggregate variantIdx fields) := by
  have hMem := List.sizeOf_lt_of_mem h
  simp_all only [Value.aggregate.sizeOf_spec]
  omega

/--
Fuel-free AST node counter over `RigidTy`, proved terminating structurally on
`sizeOf r` via the `sizeOf_lt_*` lemmas without any `Nat` fuel parameter.
-/
def rigidTyNodeCount : RigidTy → Nat
  | .param _ _ | .bool | .char | .int _ | .uint _ | .float _
  | .never | .str | .dynamic _ | .foreign _ | .other _ => 1
  | .array elem _ => 1 + rigidTyNodeCount elem
  | .slice elem => 1 + rigidTyNodeCount elem
  | .ref _ pointee => 1 + rigidTyNodeCount pointee
  | .rawPtr _ pointee => 1 + rigidTyNodeCount pointee
  | .tuple fields =>
    1 + fields.attach.foldl (fun acc ⟨f, _⟩ => acc + rigidTyNodeCount f) 0
  | .adt _ args =>
    1 + args.attach.foldl (fun acc ⟨a, _⟩ => acc + rigidTyNodeCount a) 0
  | .alias _ args =>
    1 + args.attach.foldl (fun acc ⟨a, _⟩ => acc + rigidTyNodeCount a) 0
  | .fnDef _ args =>
    1 + args.attach.foldl (fun acc ⟨a, _⟩ => acc + rigidTyNodeCount a) 0
  | .fnPtr inputs output _ _ =>
    1 + rigidTyNodeCount output +
      inputs.attach.foldl (fun acc ⟨inp, _⟩ => acc + rigidTyNodeCount inp) 0
  | .closure _ upvars =>
    1 + upvars.attach.foldl (fun acc ⟨u, _⟩ => acc + rigidTyNodeCount u) 0
termination_by r => sizeOf r
decreasing_by
  · exact sizeOf_lt_elem_of_array _ _
  · exact sizeOf_lt_elem_of_slice _
  · exact sizeOf_lt_pointee_of_ref _ _
  · exact sizeOf_lt_pointee_of_rawPtr _ _
  · exact sizeOf_lt_of_mem_tuple_fields ‹_›
  · exact sizeOf_lt_of_mem_adt_args _ ‹_›
  · exact sizeOf_lt_of_mem_alias_args _ ‹_›
  · exact sizeOf_lt_of_mem_fnDef_args _ ‹_›
  · exact sizeOf_lt_output_of_fnPtr _ _ _ _
  · exact sizeOf_lt_of_mem_fnPtr_inputs _ _ _ ‹_›
  · exact sizeOf_lt_of_mem_closure_upvars _ ‹_›

/-- Every `RigidTy` has positive node count (`1 ≤ rigidTyNodeCount r`). -/
theorem rigidTyNodeCount_pos (r : RigidTy) : 0 < rigidTyNodeCount r := by
  cases r <;> unfold rigidTyNodeCount <;> omega

/--
Fuel-free untyped byte encoder over `Value`, terminating structurally on
`sizeOf v` via `sizeOf_lt_of_mem_aggregate_fields` without `defaultCodecFuel = 16`.
-/
def encodeUntypedValueFuelFree : Value → Option (List AbstractByte)
  | .unit => some []
  | .scalar sv => encodeScalarBytes sv none
  | .ptr p sz => encodeScalarBytes ⟨p.offsetBytes, sz⟩ (some (p.allocId, p.tag))
  | .aggregate _ fields =>
    fields.attach.foldr
      (fun ⟨f, _⟩ accOpt =>
        match encodeUntypedValueFuelFree f, accOpt with
        | some b1, some b2 => some (b1 ++ b2)
        | _, _ => none)
      (some [])
termination_by v => sizeOf v
decreasing_by
  exact sizeOf_lt_of_mem_aggregate_fields _ ‹_›

/-- `List.foldr` over `xs.attach` equals `List.foldr` over `xs` when the step function ignores membership proofs. -/
theorem foldr_attach_eq_foldr {α β : Type} (xs : List α)
    (step : α → β → β) (init : β) :
    xs.attach.foldr (fun ⟨a, _⟩ acc => step a acc) init = xs.foldr step init := by
  have hMap : (xs.attach.map Subtype.val).foldr step init =
      xs.attach.foldr (fun x acc => step x.val acc) init := List.foldr_map
  have hUnattach : xs.attach.map Subtype.val = xs := List.unattach_attach
  rw [hUnattach] at hMap
  exact hMap.symm

/-- Unfold one cons step of `List.foldr` over `(x :: xs).attach` when the step function ignores membership proofs. -/
theorem foldr_attach_cons {α β : Type} (x : α) (xs : List α)
    (step : α → β → β) (init : β) :
    (x :: xs).attach.foldr (fun ⟨a, _⟩ acc => step a acc) init =
      step x (xs.attach.foldr (fun ⟨a, _⟩ acc => step a acc) init) := by
  rw [foldr_attach_eq_foldr, foldr_attach_eq_foldr, List.foldr_cons]

/--
Adequacy (soundness) of `encodeUntypedValueFuelFree` with respect to `Trusted`'s
fuel-bounded `encodeUntypedValueToBytes`: whenever `encodeUntypedValueToBytes fuel v`
succeeds with `some bs`, `encodeUntypedValueFuelFree v` produces the exact same `some bs`.
-/
theorem encodeUntypedValueToBytes_eq_some_imp_fuelFree
    (fuel : Nat) :
    ∀ (v : Value) (bs : List AbstractByte),
      encodeUntypedValueToBytes fuel v = some bs →
      encodeUntypedValueFuelFree v = some bs := by
  induction fuel with
  | zero =>
    intro _ _ hEnc
    unfold encodeUntypedValueToBytes at hEnc
    nomatch hEnc
  | succ fuel' ihFuel =>
    intro v bs hEnc
    cases v with
    | unit =>
      rw [encodeUntypedValueFuelFree]
      exact hEnc
    | scalar sv =>
      rw [encodeUntypedValueFuelFree]
      exact hEnc
    | ptr p sz =>
      rw [encodeUntypedValueFuelFree]
      exact hEnc
    | aggregate varIdx fields =>
      rw [encodeUntypedValueFuelFree]
      unfold encodeUntypedValueToBytes at hEnc
      revert bs
      induction fields with
      | nil =>
        intro bs hNil
        exact hNil
      | cons f fs ih =>
        intro bs hCons
        unfold encodeUntypedValueToBytes.encodeFields at hCons
        cases hF : encodeUntypedValueToBytes fuel' f <;> rw [hF] at hCons
        · nomatch hCons
        case some b1 =>
          cases hFs : encodeUntypedValueToBytes.encodeFields fuel' fs <;> rw [hFs] at hCons
          · nomatch hCons
          case some b2 =>
            dsimp only at hCons
            injection hCons with hBs
            rw [appendAbstractBytes_eq_append] at hBs
            rw [foldr_attach_cons f fs
                (fun a accOpt =>
                  match encodeUntypedValueFuelFree a, accOpt with
                  | some x1, some x2 => some (x1 ++ x2)
                  | _, _ => none)
                (some []),
                ihFuel f b1 hF,
                ih b2 hFs]
            dsimp only
            rw [hBs]

/-- Fuel-free aggregate nesting depth of a `Value` (`0` on leaves, `1 + max field depth` on `.aggregate`). -/
def valueAggregateDepth : Value → Nat
  | .unit | .scalar _ | .ptr _ _ => 0
  | .aggregate _ fields =>
    1 + fields.attach.foldr (fun ⟨f, _⟩ acc => Nat.max (valueAggregateDepth f) acc) 0
termination_by v => sizeOf v
decreasing_by
  exact sizeOf_lt_of_mem_aggregate_fields _ ‹_›

theorem mem_le_foldr_max_depth :
    ∀ {fields : List Value} {f : Value},
      f ∈ fields →
      valueAggregateDepth f ≤
        fields.attach.foldr (fun ⟨g, _⟩ acc => Nat.max (valueAggregateDepth g) acc) 0
  | [], _, hMem => nomatch hMem
  | x :: xs, f, hMem => by
    rw [foldr_attach_cons x xs (fun g acc => Nat.max (valueAggregateDepth g) acc) 0]
    cases List.mem_cons.mp hMem with
    | inl hEq =>
      subst hEq
      exact Nat.le_max_left _ _
    | inr hTail =>
      exact Nat.le_trans (mem_le_foldr_max_depth hTail) (Nat.le_max_right _ _)

/--
Completeness / fuel-stabilization of `encodeUntypedValueFuelFree`: for every
`fuel > valueAggregateDepth v`, `Trusted`'s `encodeUntypedValueToBytes fuel v`
equals `encodeUntypedValueFuelFree v`.
-/
theorem encodeUntypedValueToBytes_eq_fuelFree_of_depth_lt
    (fuel : Nat) :
    ∀ (v : Value),
      valueAggregateDepth v < fuel →
      encodeUntypedValueToBytes fuel v = encodeUntypedValueFuelFree v := by
  induction fuel with
  | zero =>
    intro _ hLt
    nomatch hLt
  | succ fuel' ihFuel =>
    intro v hLt
    cases v with
    | unit => rw [encodeUntypedValueFuelFree]
    | scalar _ => rw [encodeUntypedValueFuelFree]
    | ptr _ _ => rw [encodeUntypedValueFuelFree]
    | aggregate varIdx fields =>
      rw [valueAggregateDepth] at hLt
      have hMaxLt :
          fields.attach.foldr (fun ⟨g, _⟩ acc => Nat.max (valueAggregateDepth g) acc) 0 < fuel' := by
        omega
      rw [encodeUntypedValueFuelFree]
      unfold encodeUntypedValueToBytes
      have hFields :
          ∀ (fs : List Value),
            (∀ f ∈ fs, valueAggregateDepth f < fuel') →
            encodeUntypedValueToBytes.encodeFields fuel' fs =
              fs.attach.foldr
                (fun ⟨f, _⟩ accOpt =>
                  match encodeUntypedValueFuelFree f, accOpt with
                  | some b1, some b2 => some (b1 ++ b2)
                  | _, _ => none)
                (some []) := by
        intro fs
        induction fs with
        | nil =>
          intro _
          rfl
        | cons f rest ih =>
          intro hBound
          unfold encodeUntypedValueToBytes.encodeFields
          rw [foldr_attach_cons f rest
                (fun a accOpt =>
                  match encodeUntypedValueFuelFree a, accOpt with
                  | some b1, some b2 => some (b1 ++ b2)
                  | _, _ => none)
                (some []),
              ihFuel f (hBound f (List.mem_cons_self ..)),
              ih (fun g hg => hBound g (List.mem_cons_of_mem f hg))]
          cases encodeUntypedValueFuelFree f <;>
            cases rest.attach.foldr
              (fun ⟨a, _⟩ accOpt =>
                match encodeUntypedValueFuelFree a, accOpt with
                | some b1, some b2 => some (b1 ++ b2)
                | _, _ => none)
              (some []) <;>
            simp [appendAbstractBytes_eq_append]
      exact hFields fields (fun f hf => Nat.lt_of_le_of_lt (mem_le_foldr_max_depth hf) hMaxLt)

/-- Fuel-free node count on `Value` using `sizeOf_lt_of_mem_aggregate_fields`. -/
def valueNodeCount : Value → Nat
  | .unit | .scalar _ | .ptr _ _ => 1
  | .aggregate _ fields =>
    1 + fields.attach.foldl (fun acc ⟨f, _⟩ => acc + valueNodeCount f) 0
termination_by v => sizeOf v
decreasing_by
  exact sizeOf_lt_of_mem_aggregate_fields _ ‹_›

/-! ## 6. Kernel-Reducing Pattern-Matched `RigidTy` Predicates -/

/-- Kernel-reducing test for `RigidTy.bool`. -/
@[reducible]
def isBoolRigidTy : RigidTy → Bool
  | .bool => true
  | _ => false

/-- Kernel-reducing test for `RigidTy.char`. -/
@[reducible]
def isCharRigidTy : RigidTy → Bool
  | .char => true
  | _ => false

/-- Kernel-reducing test for the unit tuple `RigidTy.tuple []`. -/
@[reducible]
def isUnitTupleRigidTy : RigidTy → Bool
  | .tuple .nil => true
  | _ => false

/--
Kernel-reducing test for dynamically-sized pointees (`[T]`, `str`, `dyn Trait`)
whose references and raw pointers are 16-byte wide pointers, matching `rigidTyKindByteSize`.
-/
@[reducible]
def isWidePointeeRigidTy : RigidTy → Bool
  | .slice _ | .str | .dynamic _ => true
  | _ => false

/-- Kernel-reducing test for 16-byte wide references and raw pointers. -/
@[reducible]
def isWidePtrRigidTy : RigidTy → Bool
  | .ref _ p | .rawPtr _ p => isWidePointeeRigidTy p
  | _ => false

/-- Kernel-reducing test for 8-byte thin pointers (thin `&T`/`&mut T`/`*const T`/`*mut T` and `fn(...)`). -/
@[reducible]
def isThinPtrRigidTy : RigidTy → Bool
  | .ref _ p | .rawPtr _ p => !isWidePointeeRigidTy p
  | .fnPtr _ _ _ _ => true
  | _ => false

@[simp]
theorem isBoolRigidTy_eq_true_iff (r : RigidTy) :
    isBoolRigidTy r = true ↔ r = .bool := by
  cases r <;> simp [isBoolRigidTy]

@[simp]
theorem isCharRigidTy_eq_true_iff (r : RigidTy) :
    isCharRigidTy r = true ↔ r = .char := by
  cases r <;> simp [isCharRigidTy]

@[simp]
theorem isUnitTupleRigidTy_eq_true_iff (r : RigidTy) :
    isUnitTupleRigidTy r = true ↔ r = .tuple [] := by
  cases r with
  | tuple fs =>
    cases fs <;> simp [isUnitTupleRigidTy]
  | _ => simp [isUnitTupleRigidTy]

theorem isWidePointeeRigidTy_eq_true_iff (r : RigidTy) :
    isWidePointeeRigidTy r = true ↔
      ((∃ elem, r = .slice elem) ∨ r = .str ∨ (∃ traitPath, r = .dynamic traitPath)) := by
  cases r <;> simp [isWidePointeeRigidTy]

theorem isWidePtrRigidTy_eq_true_iff (r : RigidTy) :
    isWidePtrRigidTy r = true ↔
      ∃ m p, (r = .ref m p ∨ r = .rawPtr m p) ∧ isWidePointeeRigidTy p = true := by
  cases r with
  | ref m p =>
    constructor
    · intro h
      exact ⟨m, p, Or.inl rfl, h⟩
    · rintro ⟨m', p', hEq, hWide⟩
      cases hEq with
      | inl hRef =>
        injection hRef with _ hP
        subst hP
        exact hWide
      | inr hRaw => nomatch hRaw
  | rawPtr m p =>
    constructor
    · intro h
      exact ⟨m, p, Or.inr rfl, h⟩
    · rintro ⟨m', p', hEq, hWide⟩
      cases hEq with
      | inl hRef => nomatch hRef
      | inr hRaw =>
        injection hRaw with _ hP
        subst hP
        exact hWide
  | _ =>
    simp [isWidePtrRigidTy]

theorem isThinPtrRigidTy_eq_true_iff (r : RigidTy) :
    isThinPtrRigidTy r = true ↔
      ((∃ m p, (r = .ref m p ∨ r = .rawPtr m p) ∧ isWidePointeeRigidTy p = false) ∨
       ∃ inputs output safety abi, r = .fnPtr inputs output safety abi) := by
  cases r with
  | ref m p =>
    cases hW : isWidePointeeRigidTy p
    · simp only [isThinPtrRigidTy, hW, Bool.not_false, true_iff]
      exact Or.inl ⟨m, p, Or.inl rfl, hW⟩
    · simp only [isThinPtrRigidTy, hW, Bool.not_true, Bool.false_eq_true, false_iff]
      rintro (⟨_, p', hEq, hFalse⟩ | ⟨_, _, _, _, hFn⟩)
      · cases hEq with
        | inl hRef => injection hRef with _ hP; subst hP; rw [hW] at hFalse; nomatch hFalse
        | inr hRaw => nomatch hRaw
      · nomatch hFn
  | rawPtr m p =>
    cases hW : isWidePointeeRigidTy p
    · simp only [isThinPtrRigidTy, hW, Bool.not_false, true_iff]
      exact Or.inl ⟨m, p, Or.inr rfl, hW⟩
    · simp only [isThinPtrRigidTy, hW, Bool.not_true, Bool.false_eq_true, false_iff]
      rintro (⟨_, p', hEq, hFalse⟩ | ⟨_, _, _, _, hFn⟩)
      · cases hEq with
        | inl hRef => nomatch hRef
        | inr hRaw => injection hRaw with _ hP; subst hP; rw [hW] at hFalse; nomatch hFalse
      · nomatch hFn
  | fnPtr inputs output safety abi =>
    simp only [isThinPtrRigidTy, true_iff]
    exact Or.inr ⟨inputs, output, safety, abi, rfl⟩
  | _ =>
    simp [isThinPtrRigidTy]

/-- Thin and wide pointer classifications are disjoint. -/
theorem isWidePtrRigidTy_eq_false_of_isThinPtrRigidTy {r : RigidTy}
    (h : isThinPtrRigidTy r = true) :
    isWidePtrRigidTy r = false := by
  cases r with
  | ref _ p | rawPtr _ p =>
    cases hW : isWidePointeeRigidTy p <;> simp [isThinPtrRigidTy, isWidePtrRigidTy, hW] at h ⊢
  | _ => rfl

/-- Wide and thin pointer classifications are disjoint. -/
theorem isThinPtrRigidTy_eq_false_of_isWidePtrRigidTy {r : RigidTy}
    (h : isWidePtrRigidTy r = true) :
    isThinPtrRigidTy r = false := by
  cases r with
  | ref _ p | rawPtr _ p =>
    cases hW : isWidePointeeRigidTy p <;> simp [isThinPtrRigidTy, isWidePtrRigidTy, hW] at h ⊢
  | _ => nomatch h

/-- `rigidTyKindByteSize` on `.ref m p` equals `16` iff `isWidePointeeRigidTy p`, else `8`. -/
theorem rigidTyKindByteSize_ref_eq (m : Mutability) (p : RigidTy) :
    rigidTyKindByteSize (.ref m p) = some (if isWidePointeeRigidTy p then 16 else 8) := by
  cases p <;> rfl

/-- `rigidTyKindByteSize` on `.rawPtr m p` equals `16` iff `isWidePointeeRigidTy p`, else `8`. -/
theorem rigidTyKindByteSize_rawPtr_eq (m : Mutability) (p : RigidTy) :
    rigidTyKindByteSize (.rawPtr m p) = some (if isWidePointeeRigidTy p then 16 else 8) := by
  cases p <;> rfl

/-- Every thin pointer `RigidTy` has structural byte size `8` on 64-bit targets. -/
theorem rigidTyKindByteSize_eq_eight_of_isThinPtrRigidTy {r : RigidTy}
    (h : isThinPtrRigidTy r = true) :
    rigidTyKindByteSize r = some 8 := by
  rcases (isThinPtrRigidTy_eq_true_iff r).mp h with
    (⟨m, p, hRefOrRaw, hNotWide⟩ | ⟨inputs, output, safety, abi, hEqFn⟩)
  · cases hRefOrRaw with
    | inl hEq =>
      subst hEq
      rw [rigidTyKindByteSize_ref_eq m p, hNotWide]
      rfl
    | inr hEq =>
      subst hEq
      rw [rigidTyKindByteSize_rawPtr_eq m p, hNotWide]
      rfl
  · subst hEqFn
    rfl

/-- Every wide pointer `RigidTy` has structural byte size `16` on 64-bit targets. -/
theorem rigidTyKindByteSize_eq_sixteen_of_isWidePtrRigidTy {r : RigidTy}
    (h : isWidePtrRigidTy r = true) :
    rigidTyKindByteSize r = some 16 := by
  rcases (isWidePtrRigidTy_eq_true_iff r).mp h with ⟨m, p, hRefOrRaw, hWide⟩
  cases hRefOrRaw with
  | inl hEq =>
    subst hEq
    rw [rigidTyKindByteSize_ref_eq m p, hWide]
    rfl
  | inr hEq =>
    subst hEq
    rw [rigidTyKindByteSize_rawPtr_eq m p, hWide]
    rfl

theorem rigidTyKindByteSize_eq_one_of_isBoolRigidTy {r : RigidTy}
    (h : isBoolRigidTy r = true) :
    rigidTyKindByteSize r = some 1 := by
  rw [(isBoolRigidTy_eq_true_iff r).mp h]

theorem rigidTyKindByteSize_eq_four_of_isCharRigidTy {r : RigidTy}
    (h : isCharRigidTy r = true) :
    rigidTyKindByteSize r = some 4 := by
  rw [(isCharRigidTy_eq_true_iff r).mp h]

theorem rigidTyKindByteSize_eq_zero_of_isUnitTupleRigidTy {r : RigidTy}
    (h : isUnitTupleRigidTy r = true) :
    rigidTyKindByteSize r = some 0 := by
  rw [(isUnitTupleRigidTy_eq_true_iff r).mp h]

end Anneal.ByteCodec
