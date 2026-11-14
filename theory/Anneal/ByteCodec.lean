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

/--
A surjective `scalarValidRange` decoder carries only a trivial niche: if every fully-initialized
`sz`-byte window decodes, then `range` contains every `sz`-byte bit pattern. Contrapositively, any
genuine niche (such as `NonZeroU8` `⟨1, 255⟩` excluding `0`) makes `scalarValidRange` non-surjective.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem scalarValidRange_contains_of_isSurjectiveInitDecoder
    {sz : Nat} {hNz : 0 < sz} {range : WrappingRange}
    (hSurj : (scalarValidRange sz hNz range).IsSurjectiveInitDecoder)
    (bits : Nat) (hLt : bits < 2 ^ (8 * sz)) :
    wrappingRangeContains range bits = true := by
  cases hIn : wrappingRangeContains range bits with
  | true => rfl
  | false =>
    obtain ⟨x, hx⟩ := hSurj (encodeLittleEndianBytes bits sz none)
      (length_encodeLittleEndianBytes none sz bits)
      (allBytesInitialized_encodeLittleEndianBytes none sz bits)
    rw [scalarValidRange_decode_rejects_out_of_range sz hNz range hLt hIn] at hx
    nomatch hx

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
      have hBeq : (sz == sz) = true := decide_eq_true rfl
      dsimp only
      rw [hBeq]
      exact dite_eq_left_of_eq_true (eq_true hLt))
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

/-- Byte width of `IntTy` on 64-bit targets (`1, 2, 4, 8, 16`), matching `intCastTargetBytes`. -/
@[reducible]
def intByteSize : IntTy → Nat
  | .i8 => 1
  | .i16 => 2
  | .i32 => 4
  | .i64 => 8
  | .i128 => 16
  | .isize => 8

/-- Every `IntTy` has strictly positive byte width. -/
theorem intByteSize_pos (w : IntTy) : 0 < intByteSize w := by
  cases w <;> decide

/-- `intCastTargetBytes (.int w)` equals `some (intByteSize w)`. -/
theorem intCastTargetBytes_int_eq (w : IntTy) :
    intCastTargetBytes (.int w) = some (intByteSize w) := by
  cases w <;> rfl

/-- `MirValueCodec` for every signed integer type `i8`, `i16`, `i32`, `i64`, `i128`, `isize`
(storing canonical two's-complement unsigned bit patterns in `[0, 2^(8 * intByteSize w))`). -/
def int (layouts : LayoutTable) (w : IntTy) (idx : LayoutIdx) :
    MirValueCodec layouts { kind := .int w, layoutIdx := idx }
      { bits : Nat // bits < 2 ^ (8 * intByteSize w) } (intByteSize w) :=
  let sz := intByteSize w
  let hNz := intByteSize_pos w
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
      have hBeq : (sz == sz) = true := decide_eq_true rfl
      dsimp only
      rw [hBeq]
      exact dite_eq_left_of_eq_true (eq_true hLt))
    (by
      unfold rigidTyByteSize rigidTyKindByteSize
      rw [intCastTargetBytes_int_eq w])
    (fun ⟨bits, _hLt⟩ => by
      unfold defaultCodecFuel encodeValueToBytes
      dsimp only
      rw [intCastTargetBytes_int_eq w]
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
      rw [intCastTargetBytes_int_eq w] at hEnc
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
      rw [intCastTargetBytes_int_eq w]
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
    have hBeq : (sz == sz) = true := decide_eq_true rfl
    dsimp only
    rw [hBeq]
    exact dite_eq_left_of_eq_true (eq_true hProp)
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
    have hBeq : (sz == sz) = true := decide_eq_true rfl
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
    have hBeq1 : (varIdx == varIdx) = true := decide_eq_true rfl
    have hBeq2 : (sz == sz) = true := decide_eq_true rfl
    dsimp only
    rw [hBeq1, hBeq2, Bool.and_self]
    exact dite_eq_left_of_eq_true (eq_true hProp)
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

/-! ## 7. Symbolic Pair & Multi-Field Struct Padding (`SymbolicPairPad`, `SymbolicStructSpine`, `FieldPerm`, `PlacedCodecSpine`) -/

/--
Exact size and ABI alignment of a field type (`TyLayout` in `crates/anneal-mir/src/ir.rs`), shared
between `Anneal.ByteCodec` and `Anneal.Mir.AdtAndControl` (which re-exports it).
-/
structure FieldLayout : Type where
  /-- Size in bytes. -/
  size : Nat
  /-- ABI alignment in bytes. -/
  align : Nat
  deriving DecidableEq, Repr

/-- A 1-ZST (size `0`, alignment `1`), which `#[repr(transparent)]` ignores. -/
def FieldLayout.isOneZst (f : FieldLayout) : Bool := f.size == 0 && f.align == 1

/-- Sum of the fields' sizes (in declaration or memory order). -/
def sumSizes : List FieldLayout → Nat
  | [] => 0
  | f :: fs => f.size + sumSizes fs

/--
Symbolic padding and memory-order descriptor for a 2-field struct:
- `pad0`: leading padding bytes before the first placed field in memory;
- `padMid`: inter-field padding bytes between the first and second placed fields;
- `padTail`: trailing padding bytes after the second placed field;
- `swapOrder`: when `false`, field `0` sits before field `1` in memory (`[0, 1]`);
  when `true`, `rustc` places field `1` before field `0` in memory (`[1, 0]`).
-/
structure SymbolicPairPad : Type where
  pad0 : Nat := 0
  padMid : Nat := 0
  padTail : Nat := 0
  swapOrder : Bool := false
  deriving DecidableEq, Repr

namespace SymbolicPairPad

/-- Alias for `pad0` (leading padding). -/
@[reducible]
def lead (w : SymbolicPairPad) : Nat := w.pad0

/-- Alias for `padMid` (inter-field padding). -/
@[reducible]
def mid (w : SymbolicPairPad) : Nat := w.padMid

/-- Alias for `padTail` (trailing padding). -/
@[reducible]
def trail (w : SymbolicPairPad) : Nat := w.padTail

/-- Canonical zero-padded declaration-order descriptor (`pad0 = 0`, `padMid = 0`, `padTail = 0`, `swapOrder = false`). -/
def canonical : SymbolicPairPad := ⟨0, 0, 0, false⟩

/-- Total padding bytes injected by `w`. -/
@[reducible]
def totalPad (w : SymbolicPairPad) : Nat :=
  w.pad0 + w.padMid + w.padTail

/-- Width of the first field placed in memory under `w`. -/
@[reducible]
def firstMemWidth (w : SymbolicPairPad) (n₁ n₂ : Nat) : Nat :=
  match w.swapOrder with
  | false => n₁
  | true => n₂

/-- Width of the second field placed in memory under `w`. -/
@[reducible]
def secondMemWidth (w : SymbolicPairPad) (n₁ n₂ : Nat) : Nat :=
  match w.swapOrder with
  | false => n₂
  | true => n₁

/-- Total byte size of a 2-field struct with field widths `n₁`, `n₂` under `w`. -/
@[reducible]
def totalByteSize (w : SymbolicPairPad) (n₁ n₂ : Nat) : Nat :=
  (w.pad0 + (w.firstMemWidth n₁ n₂ + w.padMid)) + (w.secondMemWidth n₁ n₂ + w.padTail)

/-- Byte offset of logical declaration field `0` in memory under `w`. -/
@[reducible]
def offsetField0 (w : SymbolicPairPad) (_n₁ n₂ : Nat) : Nat :=
  match w.swapOrder with
  | false => w.pad0
  | true => w.pad0 + n₂ + w.padMid

/-- Byte offset of logical declaration field `1` in memory under `w`. -/
@[reducible]
def offsetField1 (w : SymbolicPairPad) (n₁ _n₂ : Nat) : Nat :=
  match w.swapOrder with
  | false => w.pad0 + n₁ + w.padMid
  | true => w.pad0

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem totalByteSize_eq_sum_plus_totalPad (w : SymbolicPairPad) (n₁ n₂ : Nat) :
    w.totalByteSize n₁ n₂ = (n₁ + n₂) + w.totalPad := by
  unfold totalByteSize firstMemWidth secondMemWidth totalPad
  cases w.swapOrder <;> dsimp only <;> omega

end SymbolicPairPad

/--
Declaration-order two-field laid-out pair combinator with inter-field padding `padMid`
and trailing padding `padTail`, built from `FixedByteCodec.prod` and `FixedByteCodec.padRight`.
-/
def laidOutPair {α β : Type} {n₁ n₂ : Nat}
    (c₁ : FixedByteCodec α n₁) (padMid : Nat)
    (c₂ : FixedByteCodec β n₂) (padTail : Nat) :
    FixedByteCodec (α × β) ((n₁ + padMid) + (n₂ + padTail)) :=
  FixedByteCodec.prod (FixedByteCodec.padRight c₁ padMid) (FixedByteCodec.padRight c₂ padTail)

/-- Alias for `laidOutPair` in `FixedByteCodec`. -/
abbrev FixedByteCodec.laidOutPair {α β : Type} {n₁ n₂ : Nat}
    (c₁ : FixedByteCodec α n₁) (padMid : Nat)
    (c₂ : FixedByteCodec β n₂) (padTail : Nat) :
    FixedByteCodec (α × β) ((n₁ + padMid) + (n₂ + padTail)) :=
  Anneal.ByteCodec.laidOutPair c₁ padMid c₂ padTail

/--
Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutPair
-/
theorem laidOutPair_isExactWidth {α β : Type} {n₁ n₂ : Nat}
    (c₁ : FixedByteCodec α n₁) (padMid : Nat)
    (c₂ : FixedByteCodec β n₂) (padTail : Nat) :
    (laidOutPair c₁ padMid c₂ padTail).IsExactWidth :=
  FixedByteCodec.prod_isExactWidth
    (FixedByteCodec.padRight c₁ padMid)
    (FixedByteCodec.padRight c₂ padTail)

/--
Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutPair
-/
theorem laidOutPair_isSurjectiveInitDecoder {α β : Type} {n₁ n₂ : Nat}
    {c₁ : FixedByteCodec α n₁} {c₂ : FixedByteCodec β n₂}
    (padMid padTail : Nat)
    (h₁ : c₁.IsSurjectiveInitDecoder) (h₂ : c₂.IsSurjectiveInitDecoder) :
    (laidOutPair c₁ padMid c₂ padTail).IsSurjectiveInitDecoder :=
  FixedByteCodec.prod_isSurjectiveInitDecoder
    (FixedByteCodec.padRight_isSurjectiveInitDecoder padMid h₁)
    (FixedByteCodec.padRight_isSurjectiveInitDecoder padTail h₂)

/--
Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutPair
-/
theorem laidOutPair_hasZeroValid {α β : Type} {n₁ n₂ : Nat}
    {c₁ : FixedByteCodec α n₁} {c₂ : FixedByteCodec β n₂}
    (padMid padTail : Nat)
    (h₁ : c₁.HasZeroValid) (h₂ : c₂.HasZeroValid) :
    (laidOutPair c₁ padMid c₂ padTail).HasZeroValid :=
  FixedByteCodec.prod_hasZeroValid
    (FixedByteCodec.padRight_hasZeroValid padMid h₁)
    (FixedByteCodec.padRight_hasZeroValid padTail h₂)

/--
Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutPair
-/
theorem laidOutPair_isInitCodec_iff {α β : Type} {n₁ n₂ padMid padTail : Nat}
    (c₁ : FixedByteCodec α n₁) (c₂ : FixedByteCodec β n₂) (a₀ : α) (b₀ : β) :
    (laidOutPair c₁ padMid c₂ padTail).IsInitCodec ↔
      padMid = 0 ∧ padTail = 0 ∧ c₁.IsInitCodec ∧ c₂.IsInitCodec := by
  constructor
  · intro hInit
    have hP1 : (FixedByteCodec.padRight c₁ padMid).IsInitCodec := by
      intro a
      have hBoth := hInit (a, b₀)
      dsimp only [laidOutPair, FixedByteCodec.prod, FixedByteCodec.ofRoundTrip] at hBoth
      cases hA : allBytesInitialized ((FixedByteCodec.padRight c₁ padMid).encode a) with
      | true => rfl
      | false =>
        rw [allBytesInitialized_append_eq_false_left ((FixedByteCodec.padRight c₂ padTail).encode b₀) hA] at hBoth
        nomatch hBoth
    have hP2 : (FixedByteCodec.padRight c₂ padTail).IsInitCodec := by
      intro b
      have hBoth := hInit (a₀, b)
      dsimp only [laidOutPair, FixedByteCodec.prod, FixedByteCodec.ofRoundTrip] at hBoth
      cases hB : allBytesInitialized ((FixedByteCodec.padRight c₂ padTail).encode b) with
      | true => rfl
      | false =>
        rw [allBytesInitialized_append_eq_false_right ((FixedByteCodec.padRight c₁ padMid).encode a₀) hB] at hBoth
        nomatch hBoth
    obtain ⟨hMid0, hC1⟩ := (FixedByteCodec.padRight_isInitCodec_iff c₁ a₀).mp hP1
    obtain ⟨hTail0, hC2⟩ := (FixedByteCodec.padRight_isInitCodec_iff c₂ b₀).mp hP2
    exact ⟨hMid0, hTail0, hC1, hC2⟩
  · rintro ⟨rfl, rfl, hC1, hC2⟩
    exact FixedByteCodec.prod_isInitCodec
      (FixedByteCodec.padRight_zero_isInitCodec hC1)
      (FixedByteCodec.padRight_zero_isInitCodec hC2)

/--
Symbolic-padding two-field struct codec parameterized by `w : SymbolicPairPad`:
supports leading padding `w.pad0`, inter-field padding `w.padMid`, trailing padding
`w.padTail`, AND field memory-order permutation (`w.swapOrder = false` vs `true`).
-/
def laidOutPairSymbolicPad {α β : Type} {n₁ n₂ : Nat}
    (w : SymbolicPairPad)
    (c₁ : FixedByteCodec α n₁) (c₂ : FixedByteCodec β n₂) :
    FixedByteCodec (α × β) (w.totalByteSize n₁ n₂) :=
  match w with
  | ⟨pad0, padMid, padTail, false⟩ =>
    FixedByteCodec.prod
      (FixedByteCodec.padLeft pad0 (FixedByteCodec.padRight c₁ padMid))
      (FixedByteCodec.padRight c₂ padTail)
  | ⟨pad0, padMid, padTail, true⟩ =>
    (FixedByteCodec.prod
      (FixedByteCodec.padLeft pad0 (FixedByteCodec.padRight c₂ padMid))
      (FixedByteCodec.padRight c₁ padTail)).mapEquiv
      (fun p => (p.2, p.1))
      (fun p => (p.2, p.1))
      (fun ⟨_, _⟩ => rfl)
      (fun ⟨_, _⟩ => rfl)

/-- Alias for `laidOutPairSymbolicPad` in `FixedByteCodec`. -/
abbrev FixedByteCodec.laidOutPairSymbolicPad {α β : Type} {n₁ n₂ : Nat}
    (w : SymbolicPairPad)
    (c₁ : FixedByteCodec α n₁) (c₂ : FixedByteCodec β n₂) :
    FixedByteCodec (α × β) (w.totalByteSize n₁ n₂) :=
  Anneal.ByteCodec.laidOutPairSymbolicPad w c₁ c₂

/-- On an exact-width `n`-byte chunk, `(padLeft 0 c).decode` reduces to `c.decode chunk`. -/
theorem FixedByteCodec.padLeft_zero_decode_of_length_eq {α : Type} {n : Nat}
    (c : FixedByteCodec α n) {chunk : List AbstractByte}
    (hLen : chunk.length = n) :
    (FixedByteCodec.padLeft 0 c).decode chunk = c.decode chunk := by
  unfold FixedByteCodec.padLeft FixedByteCodec.mapEquiv FixedByteCodec.prod
         FixedByteCodec.padUninit FixedByteCodec.ofRoundTrip
  dsimp only [List.take, List.drop, List.length]
  rw [Nat.zero_add n, Nat.beq_eq.mpr hLen]
  dsimp only [Option.map, Nat.beq]
  cases c.decode chunk <;> rfl

/--
Zero-padding declaration-order `laidOutPairSymbolicPad` agrees byte-for-byte on `encode` and
`decode` with `FixedByteCodec.prod c₁ c₂`.

Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutPairSymbolicPad
-/
theorem laidOutPairSymbolicPad_zero_eq_prod {α β : Type} {n₁ n₂ : Nat}
    (c₁ : FixedByteCodec α n₁) (c₂ : FixedByteCodec β n₂) :
    (∀ x : α × β,
      (laidOutPairSymbolicPad SymbolicPairPad.canonical c₁ c₂).encode x =
        (FixedByteCodec.prod c₁ c₂).encode x) ∧
    (∀ bs : List AbstractByte,
      (laidOutPairSymbolicPad SymbolicPairPad.canonical c₁ c₂).decode bs =
        (FixedByteCodec.prod c₁ c₂).decode bs) := by
  refine ⟨fun ⟨a, b⟩ => ?_, fun bs => ?_⟩
  · show (replicateUninitBytes 0 ++ (c₁.encode a ++ replicateUninitBytes 0)) ++
        (c₂.encode b ++ replicateUninitBytes 0) =
      c₁.encode a ++ c₂.encode b
    simp only [show replicateUninitBytes 0 = [] from rfl, List.nil_append, List.append_nil]
  · change (FixedByteCodec.prod
        (FixedByteCodec.padLeft 0 (FixedByteCodec.padRight c₁ 0))
        (FixedByteCodec.padRight c₂ 0)).decode bs =
      (FixedByteCodec.prod c₁ c₂).decode bs
    unfold FixedByteCodec.prod FixedByteCodec.ofRoundTrip
    dsimp only
    have hSz : (0 + (n₁ + 0)) + (n₂ + 0) = n₁ + n₂ := by omega
    have hSz1 : 0 + (n₁ + 0) = n₁ := by omega
    rw [hSz]
    cases hBeq : Nat.beq bs.length (n₁ + n₂)
    · rfl
    · dsimp only
      have hLen : bs.length = n₁ + n₂ := Nat.eq_of_beq_eq_true hBeq
      have hTakeLen : (bs.take (0 + (n₁ + 0))).length = n₁ + 0 := by rw [List.length_take]; omega
      have hDropLen : (bs.drop (0 + (n₁ + 0))).length = n₂ + 0 := by rw [List.length_drop]; omega
      rw [FixedByteCodec.padLeft_zero_decode_of_length_eq (FixedByteCodec.padRight c₁ 0) hTakeLen,
          FixedByteCodec.padRight_decode_of_length_eq c₁ hTakeLen,
          FixedByteCodec.padRight_decode_of_length_eq c₂ hDropLen,
          hSz1]
      have hTakeTake : (bs.take n₁).take n₁ = bs.take n₁ :=
        List.take_of_length_le (by rw [List.length_take]; omega)
      have hDropTake : (bs.drop n₁).take n₂ = bs.drop n₁ :=
        List.take_of_length_le (by rw [List.length_drop]; omega)
      rw [hTakeTake, hDropTake]

/--
Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutPairSymbolicPad
-/
theorem laidOutPairSymbolicPad_isExactWidth {α β : Type} {n₁ n₂ : Nat}
    (w : SymbolicPairPad) (c₁ : FixedByteCodec α n₁) (c₂ : FixedByteCodec β n₂) :
    (laidOutPairSymbolicPad w c₁ c₂).IsExactWidth := by
  rcases w with ⟨pad0, padMid, padTail, swap⟩
  cases swap
  · exact FixedByteCodec.prod_isExactWidth
      (FixedByteCodec.padLeft pad0 (FixedByteCodec.padRight c₁ padMid))
      (FixedByteCodec.padRight c₂ padTail)
  · exact FixedByteCodec.mapEquiv_isExactWidth _
      (fun p => (p.2, p.1)) (fun p => (p.2, p.1))
      (fun ⟨_, _⟩ => rfl) (fun ⟨_, _⟩ => rfl)
      (FixedByteCodec.prod_isExactWidth
        (FixedByteCodec.padLeft pad0 (FixedByteCodec.padRight c₂ padMid))
        (FixedByteCodec.padRight c₁ padTail))

/--
Universal `FromBytes` (`IsSurjectiveInitDecoder`) preservation across all `w : SymbolicPairPad`,
including arbitrary non-negative padding `(pad0, padMid, padTail)` and field permutation `swapOrder`.

Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutPairSymbolicPad
-/
theorem laidOutPairSymbolicPad_isSurjectiveInitDecoder {α β : Type} {n₁ n₂ : Nat}
    (w : SymbolicPairPad) {c₁ : FixedByteCodec α n₁} {c₂ : FixedByteCodec β n₂}
    (h₁ : c₁.IsSurjectiveInitDecoder) (h₂ : c₂.IsSurjectiveInitDecoder) :
    (laidOutPairSymbolicPad w c₁ c₂).IsSurjectiveInitDecoder := by
  rcases w with ⟨pad0, padMid, padTail, swap⟩
  cases swap
  · exact FixedByteCodec.prod_isSurjectiveInitDecoder
      (FixedByteCodec.padLeft_isSurjectiveInitDecoder pad0
        (FixedByteCodec.padRight_isSurjectiveInitDecoder padMid h₁))
      (FixedByteCodec.padRight_isSurjectiveInitDecoder padTail h₂)
  · exact FixedByteCodec.mapEquiv_isSurjectiveInitDecoder _
      (fun p => (p.2, p.1)) (fun p => (p.2, p.1))
      (fun ⟨_, _⟩ => rfl) (fun ⟨_, _⟩ => rfl)
      (FixedByteCodec.prod_isSurjectiveInitDecoder
        (FixedByteCodec.padLeft_isSurjectiveInitDecoder pad0
          (FixedByteCodec.padRight_isSurjectiveInitDecoder padMid h₂))
        (FixedByteCodec.padRight_isSurjectiveInitDecoder padTail h₁))

/--
Universal `FromZeros` (`HasZeroValid`) preservation across all `w : SymbolicPairPad`.

Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutPairSymbolicPad
-/
theorem laidOutPairSymbolicPad_hasZeroValid {α β : Type} {n₁ n₂ : Nat}
    (w : SymbolicPairPad) {c₁ : FixedByteCodec α n₁} {c₂ : FixedByteCodec β n₂}
    (h₁ : c₁.HasZeroValid) (h₂ : c₂.HasZeroValid) :
    (laidOutPairSymbolicPad w c₁ c₂).HasZeroValid := by
  rcases w with ⟨pad0, padMid, padTail, swap⟩
  cases swap
  · exact FixedByteCodec.prod_hasZeroValid
      (FixedByteCodec.padLeft_hasZeroValid pad0
        (FixedByteCodec.padRight_hasZeroValid padMid h₁))
      (FixedByteCodec.padRight_hasZeroValid padTail h₂)
  · exact FixedByteCodec.mapEquiv_hasZeroValid _
      (fun p => (p.2, p.1)) (fun p => (p.2, p.1))
      (fun ⟨_, _⟩ => rfl) (fun ⟨_, _⟩ => rfl)
      (FixedByteCodec.prod_hasZeroValid
        (FixedByteCodec.padLeft_hasZeroValid pad0
          (FixedByteCodec.padRight_hasZeroValid padMid h₂))
        (FixedByteCodec.padRight_hasZeroValid padTail h₁))

/--
Exact `IsInitCodec` characterization for `laidOutPairSymbolicPad`: over any inhabited
field types `α` and `β`, the codec emits only initialized bytes iff `pad0 = 0`,
`padMid = 0`, `padTail = 0`, and both field codecs are `IsInitCodec` (independent of
field permutation `swapOrder`).

Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutPairSymbolicPad
-/
theorem laidOutPairSymbolicPad_isInitCodec_iff {α β : Type} {n₁ n₂ : Nat}
    (w : SymbolicPairPad) (c₁ : FixedByteCodec α n₁) (c₂ : FixedByteCodec β n₂)
    (a₀ : α) (b₀ : β) :
    (laidOutPairSymbolicPad w c₁ c₂).IsInitCodec ↔
      w.pad0 = 0 ∧ w.padMid = 0 ∧ w.padTail = 0 ∧ c₁.IsInitCodec ∧ c₂.IsInitCodec := by
  rcases w with ⟨pad0, padMid, padTail, swap⟩
  cases swap
  · dsimp only [laidOutPairSymbolicPad]
    constructor
    · intro hInit
      have hLeft : (FixedByteCodec.padLeft pad0 (FixedByteCodec.padRight c₁ padMid)).IsInitCodec := by
        intro a
        have hBoth := hInit (a, b₀)
        dsimp only [FixedByteCodec.prod, FixedByteCodec.ofRoundTrip] at hBoth
        cases hA : allBytesInitialized ((FixedByteCodec.padLeft pad0 (FixedByteCodec.padRight c₁ padMid)).encode a) with
        | true => rfl
        | false =>
          rw [allBytesInitialized_append_eq_false_left ((FixedByteCodec.padRight c₂ padTail).encode b₀) hA] at hBoth
          nomatch hBoth
      have hRight : (FixedByteCodec.padRight c₂ padTail).IsInitCodec := by
        intro b
        have hBoth := hInit (a₀, b)
        dsimp only [FixedByteCodec.prod, FixedByteCodec.ofRoundTrip] at hBoth
        cases hB : allBytesInitialized ((FixedByteCodec.padRight c₂ padTail).encode b) with
        | true => rfl
        | false =>
          rw [allBytesInitialized_append_eq_false_right ((FixedByteCodec.padLeft pad0 (FixedByteCodec.padRight c₁ padMid)).encode a₀) hB] at hBoth
          nomatch hBoth
      obtain ⟨hPad0, hMidCodec⟩ := (FixedByteCodec.padLeft_isInitCodec_iff (FixedByteCodec.padRight c₁ padMid) a₀).mp hLeft
      obtain ⟨hMid0, hC1⟩ := (FixedByteCodec.padRight_isInitCodec_iff c₁ a₀).mp hMidCodec
      obtain ⟨hTail0, hC2⟩ := (FixedByteCodec.padRight_isInitCodec_iff c₂ b₀).mp hRight
      exact ⟨hPad0, hMid0, hTail0, hC1, hC2⟩
    · rintro ⟨rfl, rfl, rfl, hC1, hC2⟩
      exact FixedByteCodec.prod_isInitCodec
        (FixedByteCodec.padLeft_zero_isInitCodec (FixedByteCodec.padRight_zero_isInitCodec hC1))
        (FixedByteCodec.padRight_zero_isInitCodec hC2)
  · dsimp only [laidOutPairSymbolicPad]
    constructor
    · intro hInit
      have hLeft : (FixedByteCodec.padLeft pad0 (FixedByteCodec.padRight c₂ padMid)).IsInitCodec := by
        intro b
        have hBoth := hInit (a₀, b)
        dsimp only [FixedByteCodec.mapEquiv, FixedByteCodec.prod, FixedByteCodec.ofRoundTrip] at hBoth
        cases hB : allBytesInitialized ((FixedByteCodec.padLeft pad0 (FixedByteCodec.padRight c₂ padMid)).encode b) with
        | true => rfl
        | false =>
          rw [allBytesInitialized_append_eq_false_left ((FixedByteCodec.padRight c₁ padTail).encode a₀) hB] at hBoth
          nomatch hBoth
      have hRight : (FixedByteCodec.padRight c₁ padTail).IsInitCodec := by
        intro a
        have hBoth := hInit (a, b₀)
        dsimp only [FixedByteCodec.mapEquiv, FixedByteCodec.prod, FixedByteCodec.ofRoundTrip] at hBoth
        cases hA : allBytesInitialized ((FixedByteCodec.padRight c₁ padTail).encode a) with
        | true => rfl
        | false =>
          rw [allBytesInitialized_append_eq_false_right ((FixedByteCodec.padLeft pad0 (FixedByteCodec.padRight c₂ padMid)).encode b₀) hA] at hBoth
          nomatch hBoth
      obtain ⟨hPad0, hMidCodec⟩ := (FixedByteCodec.padLeft_isInitCodec_iff (FixedByteCodec.padRight c₂ padMid) b₀).mp hLeft
      obtain ⟨hMid0, hC2⟩ := (FixedByteCodec.padRight_isInitCodec_iff c₂ b₀).mp hMidCodec
      obtain ⟨hTail0, hC1⟩ := (FixedByteCodec.padRight_isInitCodec_iff c₁ a₀).mp hRight
      exact ⟨hPad0, hMid0, hTail0, hC1, hC2⟩
    · rintro ⟨rfl, rfl, rfl, hC1, hC2⟩
      exact FixedByteCodec.mapEquiv_isInitCodec _
        (fun p => (p.2, p.1)) (fun p => (p.2, p.1))
        (fun ⟨_, _⟩ => rfl) (fun ⟨_, _⟩ => rfl)
        (FixedByteCodec.prod_isInitCodec
          (FixedByteCodec.padLeft_zero_isInitCodec (FixedByteCodec.padRight_zero_isInitCodec hC2))
          (FixedByteCodec.padRight_zero_isInitCodec hC1))

/--
Negative theorem: any positive padding (`0 < w.totalPad`) forces
`laidOutPairSymbolicPad` to emit `.uninit` bytes on every value `(a, b)`, violating
`IsInitCodec`.

Kind: codec
Witness: negative
Assumes: S0
Subject: laidOutPairSymbolicPad
-/
theorem laidOutPairSymbolicPad_not_isInitCodec_of_totalPad_pos {α β : Type} {n₁ n₂ : Nat}
    {w : SymbolicPairPad} (hPos : 0 < w.totalPad)
    (c₁ : FixedByteCodec α n₁) (c₂ : FixedByteCodec β n₂) (a₀ : α) (b₀ : β) :
    ¬ (laidOutPairSymbolicPad w c₁ c₂).IsInitCodec := by
  intro hInit
  have ⟨h0, hM, hT, _, _⟩ :=
    (laidOutPairSymbolicPad_isInitCodec_iff w c₁ c₂ a₀ b₀).mp hInit
  unfold SymbolicPairPad.totalPad at hPos
  omega

/--
Zero padding suffices for `IsInitCodec` (no inhabitants needed): if `pad0 = padMid = padTail = 0`
and both field codecs are `IsInitCodec`, so is `laidOutPairSymbolicPad w c₁ c₂` in either memory
order.

Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutPairSymbolicPad
-/
theorem laidOutPairSymbolicPad_isInitCodec_of_zero_pad {α β : Type} {n₁ n₂ : Nat}
    {w : SymbolicPairPad} (hPad : w.totalPad = 0)
    {c₁ : FixedByteCodec α n₁} {c₂ : FixedByteCodec β n₂}
    (h₁ : c₁.IsInitCodec) (h₂ : c₂.IsInitCodec) :
    (laidOutPairSymbolicPad w c₁ c₂).IsInitCodec := by
  rcases w with ⟨pad0, padMid, padTail, swap⟩
  unfold SymbolicPairPad.totalPad at hPad
  dsimp only at hPad
  have hp0 : pad0 = 0 := by omega
  have hpM : padMid = 0 := by omega
  have hpT : padTail = 0 := by omega
  subst hp0 hpM hpT
  cases swap
  · exact FixedByteCodec.prod_isInitCodec
      (FixedByteCodec.padLeft_zero_isInitCodec (FixedByteCodec.padRight_zero_isInitCodec h₁))
      (FixedByteCodec.padRight_zero_isInitCodec h₂)
  · exact FixedByteCodec.mapEquiv_isInitCodec _
      (fun p => (p.2, p.1)) (fun p => (p.2, p.1))
      (fun ⟨_, _⟩ => rfl) (fun ⟨_, _⟩ => rfl)
      (FixedByteCodec.prod_isInitCodec
        (FixedByteCodec.padLeft_zero_isInitCodec (FixedByteCodec.padRight_zero_isInitCodec h₂))
        (FixedByteCodec.padRight_zero_isInitCodec h₁))

/--
When `c₁` and `c₂` are `IsInitCodec` over inhabited field types, `laidOutPairSymbolicPad w c₁ c₂`
is `IsInitCodec` iff `w.totalPad = 0`.

Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutPairSymbolicPad
-/
theorem laidOutPairSymbolicPad_isInitCodec_iff_totalPad_eq_zero {α β : Type} {n₁ n₂ : Nat}
    (w : SymbolicPairPad) {c₁ : FixedByteCodec α n₁} {c₂ : FixedByteCodec β n₂}
    (h₁ : c₁.IsInitCodec) (h₂ : c₂.IsInitCodec) (a₀ : α) (b₀ : β) :
    (laidOutPairSymbolicPad w c₁ c₂).IsInitCodec ↔ w.totalPad = 0 := by
  constructor
  · intro hInit
    obtain ⟨h0, hM, hT, _, _⟩ :=
      (laidOutPairSymbolicPad_isInitCodec_iff w c₁ c₂ a₀ b₀).mp hInit
    unfold SymbolicPairPad.totalPad
    omega
  · intro hPad
    exact laidOutPairSymbolicPad_isInitCodec_of_zero_pad hPad h₁ h₂

/--
Pointwise uninitialized emission: whenever `0 < w.totalPad`, **every** value `(a, b)` encodes
with at least one `.uninit` byte (stronger than `¬ IsInitCodec`, which only exhibits one value).

Kind: codec
Witness: negative
Assumes: S0
Subject: laidOutPairSymbolicPad
-/
theorem laidOutPairSymbolicPad_encode_uninit_of_totalPad_pos {α β : Type} {n₁ n₂ : Nat}
    {w : SymbolicPairPad} (hPos : 0 < w.totalPad)
    (c₁ : FixedByteCodec α n₁) (c₂ : FixedByteCodec β n₂) (a : α) (b : β) :
    allBytesInitialized ((laidOutPairSymbolicPad w c₁ c₂).encode (a, b)) = false := by
  rcases w with ⟨pad0, padMid, padTail, swap⟩
  unfold SymbolicPairPad.totalPad at hPos
  dsimp only at hPos
  have hCases : 0 < pad0 ∨ 0 < padMid ∨ 0 < padTail := by omega
  cases swap
  · show allBytesInitialized
        ((replicateUninitBytes pad0 ++ (c₁.encode a ++ replicateUninitBytes padMid)) ++
          (c₂.encode b ++ replicateUninitBytes padTail)) = false
    rcases hCases with h | h | h
    · exact allBytesInitialized_append_eq_false_left _
        (allBytesInitialized_append_eq_false_left _ (allBytesInitialized_replicateUninitBytes_eq_false h))
    · exact allBytesInitialized_append_eq_false_left _
        (allBytesInitialized_append_eq_false_right _
          (allBytesInitialized_append_eq_false_right _ (allBytesInitialized_replicateUninitBytes_eq_false h)))
    · exact allBytesInitialized_append_eq_false_right _
        (allBytesInitialized_append_eq_false_right _ (allBytesInitialized_replicateUninitBytes_eq_false h))
  · show allBytesInitialized
        ((replicateUninitBytes pad0 ++ (c₂.encode b ++ replicateUninitBytes padMid)) ++
          (c₁.encode a ++ replicateUninitBytes padTail)) = false
    rcases hCases with h | h | h
    · exact allBytesInitialized_append_eq_false_left _
        (allBytesInitialized_append_eq_false_left _ (allBytesInitialized_replicateUninitBytes_eq_false h))
    · exact allBytesInitialized_append_eq_false_left _
        (allBytesInitialized_append_eq_false_right _
          (allBytesInitialized_append_eq_false_right _ (allBytesInitialized_replicateUninitBytes_eq_false h)))
    · exact allBytesInitialized_append_eq_false_right _
        (allBytesInitialized_append_eq_false_right _ (allBytesInitialized_replicateUninitBytes_eq_false h))

/-- Constructive membership witness: `allBytesInitialized bs = false` iff `.uninit ∈ bs`. -/
theorem allBytesInitialized_eq_false_iff_mem_uninit :
    ∀ bs : List AbstractByte, allBytesInitialized bs = false ↔ AbstractByte.uninit ∈ bs
  | [] => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | .uninit :: _ => ⟨fun _ => List.mem_cons_self .., fun _ => rfl⟩
  | .init _ _ :: rest => by
    show allBytesInitialized rest = false ↔ AbstractByte.uninit ∈ _ :: rest
    rw [allBytesInitialized_eq_false_iff_mem_uninit rest]
    exact ⟨fun h => List.mem_cons_of_mem _ h,
           fun h => by
             rcases List.mem_cons.mp h with hEq | hTail
             · nomatch hEq
             · exact hTail⟩

/--
Whenever `0 < w.totalPad`, `(laidOutPairSymbolicPad w c₁ c₂).encode (a, b)` contains `.uninit`
and has `allBytesInitialized = false`.

Kind: codec
Witness: negative
Assumes: S0
Subject: laidOutPairSymbolicPad
-/
theorem laidOutPairSymbolicPad_encode_contains_uninit_of_totalPad_pos {α β : Type} {n₁ n₂ : Nat}
    {w : SymbolicPairPad} (hPos : 0 < w.totalPad)
    (c₁ : FixedByteCodec α n₁) (c₂ : FixedByteCodec β n₂) (a : α) (b : β) :
    AbstractByte.uninit ∈ (laidOutPairSymbolicPad w c₁ c₂).encode (a, b) ∧
    allBytesInitialized ((laidOutPairSymbolicPad w c₁ c₂).encode (a, b)) = false := by
  have hFalse := laidOutPairSymbolicPad_encode_uninit_of_totalPad_pos hPos c₁ c₂ a b
  exact ⟨(allBytesInitialized_eq_false_iff_mem_uninit _).mp hFalse, hFalse⟩

/--
**Byte-Placement Realization**: in every symbolic pair world `w` (any padding, either memory
order), `laidOutPairSymbolicPad w c₁ c₂` places field `0`'s encoding exactly at the byte window
`[w.offsetField0, w.offsetField0 + n₁)` and field `1`'s encoding exactly at
`[w.offsetField1, w.offsetField1 + n₂)`.

Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutPairSymbolicPad
-/
theorem laidOutPairSymbolicPad_field_windows {α β : Type} {n₁ n₂ : Nat}
    (w : SymbolicPairPad) (c₁ : FixedByteCodec α n₁) (c₂ : FixedByteCodec β n₂) (a : α) (b : β) :
    (((laidOutPairSymbolicPad w c₁ c₂).encode (a, b)).drop (w.offsetField0 n₁ n₂)).take n₁ =
        c₁.encode a ∧
    (((laidOutPairSymbolicPad w c₁ c₂).encode (a, b)).drop (w.offsetField1 n₁ n₂)).take n₂ =
        c₂.encode b := by
  rcases w with ⟨pad0, padMid, padTail, swap⟩
  have hL0 : (replicateUninitBytes pad0).length = pad0 := length_replicateUninitBytes pad0
  cases swap
  · have hEnc : (laidOutPairSymbolicPad ⟨pad0, padMid, padTail, false⟩ c₁ c₂).encode (a, b) =
        replicateUninitBytes pad0 ++ (c₁.encode a ++ (replicateUninitBytes padMid ++
          (c₂.encode b ++ replicateUninitBytes padTail))) := by
      show (replicateUninitBytes pad0 ++ (c₁.encode a ++ replicateUninitBytes padMid)) ++
          (c₂.encode b ++ replicateUninitBytes padTail) = _
      simp only [List.append_assoc]
    have hL1 : (replicateUninitBytes pad0 ++ (c₁.encode a ++ replicateUninitBytes padMid)).length =
        pad0 + n₁ + padMid := by
      simp only [List.length_append, length_replicateUninitBytes, c₁.encode_length]
      omega
    have hEnc' : (laidOutPairSymbolicPad ⟨pad0, padMid, padTail, false⟩ c₁ c₂).encode (a, b) =
        (replicateUninitBytes pad0 ++ (c₁.encode a ++ replicateUninitBytes padMid)) ++
          (c₂.encode b ++ replicateUninitBytes padTail) := rfl
    refine ⟨?_, ?_⟩
    · dsimp only [SymbolicPairPad.offsetField0]
      rw [hEnc, List.drop_left' hL0, List.take_left' (c₁.encode_length a)]
    · dsimp only [SymbolicPairPad.offsetField1]
      rw [hEnc', List.drop_left' hL1, List.take_left' (c₂.encode_length b)]
  · have hEnc : (laidOutPairSymbolicPad ⟨pad0, padMid, padTail, true⟩ c₁ c₂).encode (a, b) =
        replicateUninitBytes pad0 ++ (c₂.encode b ++ (replicateUninitBytes padMid ++
          (c₁.encode a ++ replicateUninitBytes padTail))) := by
      show (replicateUninitBytes pad0 ++ (c₂.encode b ++ replicateUninitBytes padMid)) ++
          (c₁.encode a ++ replicateUninitBytes padTail) = _
      simp only [List.append_assoc]
    have hL1 : (replicateUninitBytes pad0 ++ (c₂.encode b ++ replicateUninitBytes padMid)).length =
        pad0 + n₂ + padMid := by
      simp only [List.length_append, length_replicateUninitBytes, c₂.encode_length]
      omega
    have hEnc' : (laidOutPairSymbolicPad ⟨pad0, padMid, padTail, true⟩ c₁ c₂).encode (a, b) =
        (replicateUninitBytes pad0 ++ (c₂.encode b ++ replicateUninitBytes padMid)) ++
          (c₁.encode a ++ replicateUninitBytes padTail) := rfl
    refine ⟨?_, ?_⟩
    · dsimp only [SymbolicPairPad.offsetField0]
      rw [hEnc', List.drop_left' hL1, List.take_left' (c₁.encode_length a)]
    · dsimp only [SymbolicPairPad.offsetField1]
      rw [hEnc, List.drop_left' hL0, List.take_left' (c₂.encode_length b)]

/-! ### General $k$-Field Heterogeneous Struct Codec Spine (`laidOutStructSymbolicPad`) -/

/-- Right-nested heterogeneous tuple of field types `[α₀, α₁, ..., α_{k-1}]`. -/
@[reducible]
def FieldTuple : List Type → Type
  | [] => Unit
  | α :: αs => α × FieldTuple αs

/-- Heterogeneous spine of `FixedByteCodec`s paired with symbolic post-field padding widths. -/
inductive SymbolicStructSpine : List Type → Nat → Type 1 where
  /-- Empty struct with `leadPad` bytes of padding (`0` for ZST structs). -/
  | nil (leadPad : Nat) : SymbolicStructSpine [] leadPad
  /-- Prepend a field with codec `c : FixedByteCodec α n` and `postPad` trailing/inter-field padding bytes. -/
  | cons {α : Type} {αs : List Type} {n restWidth : Nat}
      (c : FixedByteCodec α n) (postPad : Nat)
      (tail : SymbolicStructSpine αs restWidth) :
      SymbolicStructSpine (α :: αs) ((n + postPad) + restWidth)

namespace SymbolicStructSpine

/-- Sum of all padding slots inside a `SymbolicStructSpine`. -/
def totalPadBytes : {αs : List Type} → {w : Nat} → SymbolicStructSpine αs w → Nat
  | _, _, .nil leadPad => leadPad
  | _, _, .cons _ postPad tail => postPad + tail.totalPadBytes

/-- Sum of all raw field byte sizes inside a `SymbolicStructSpine`. -/
def sumFieldWidths : {αs : List Type} → {w : Nat} → SymbolicStructSpine αs w → Nat
  | _, _, .nil _ => 0
  | _, _, @SymbolicStructSpine.cons _ _ n _ _ _ tail => n + tail.sumFieldWidths

/-- Whether every field codec in the spine satisfies `IsSurjectiveInitDecoder`. -/
@[reducible]
def AllFieldsSurjective : {αs : List Type} → {w : Nat} → SymbolicStructSpine αs w → Prop
  | _, _, .nil _ => True
  | _, _, .cons c _ tail => c.IsSurjectiveInitDecoder ∧ tail.AllFieldsSurjective

/-- Whether every field codec in the spine satisfies `HasZeroValid`. -/
@[reducible]
def AllFieldsZeroValid : {αs : List Type} → {w : Nat} → SymbolicStructSpine αs w → Prop
  | _, _, .nil _ => True
  | _, _, .cons c _ tail => c.HasZeroValid ∧ tail.AllFieldsZeroValid

/-- Whether every field codec in the spine satisfies `IsInitCodec`. -/
@[reducible]
def AllFieldsInit : {αs : List Type} → {w : Nat} → SymbolicStructSpine αs w → Prop
  | _, _, .nil _ => True
  | _, _, .cons c _ tail => c.IsInitCodec ∧ tail.AllFieldsInit

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem width_eq_sumFieldWidths_add_totalPadBytes :
    ∀ {αs : List Type} {w : Nat} (s : SymbolicStructSpine αs w),
      w = s.sumFieldWidths + s.totalPadBytes
  | _, _, .nil leadPad => by simp [sumFieldWidths, totalPadBytes]
  | _, _, @SymbolicStructSpine.cons _ _ n restW _ postPad tail => by
    have ih := width_eq_sumFieldWidths_add_totalPadBytes tail
    dsimp only [sumFieldWidths, totalPadBytes]
    omega

/-- Byte offsets of each field in a `SymbolicStructSpine` starting at byte offset `base`. -/
def fieldOffsets : {αs : List Type} → {w : Nat} → SymbolicStructSpine αs w → Nat → List Nat
  | _, _, .nil _, _ => []
  | _, _, @SymbolicStructSpine.cons _ _ n _ _ postPad tail, base =>
    base :: tail.fieldOffsets (base + (n + postPad))

/-- `FieldLayout` list induced by a `SymbolicStructSpine` paired with per-field alignments `aligns`. -/
def toFieldLayouts :
    {αs : List Type} → {w : Nat} → SymbolicStructSpine αs w → List Nat → List FieldLayout
  | _, _, .nil _, _ => []
  | _, _, @SymbolicStructSpine.cons _ _ n _ _ _ tail, aligns =>
    { size := n, align := aligns.head?.getD 1 } :: tail.toFieldLayouts aligns.tail

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem fieldOffsets_length :
    ∀ {αs : List Type} {w : Nat} (s : SymbolicStructSpine αs w) (base : Nat),
      (s.fieldOffsets base).length = αs.length
  | _, _, .nil _, _ => rfl
  | _, _, .cons _ postPad tail, base => by
    dsimp only [fieldOffsets, List.length]
    rw [fieldOffsets_length tail]

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem toFieldLayouts_length :
    ∀ {αs : List Type} {w : Nat} (s : SymbolicStructSpine αs w) (aligns : List Nat),
      (s.toFieldLayouts aligns).length = αs.length
  | _, _, .nil _, _ => rfl
  | _, _, .cons _ _ tail, aligns => by
    dsimp only [toFieldLayouts, List.length]
    rw [toFieldLayouts_length tail]

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem sumSizes_toFieldLayouts :
    ∀ {αs : List Type} {w : Nat} (s : SymbolicStructSpine αs w) (aligns : List Nat),
      sumSizes (s.toFieldLayouts aligns) = s.sumFieldWidths
  | _, _, .nil _, _ => rfl
  | _, _, .cons _ _ tail, aligns => by
    dsimp only [toFieldLayouts, sumSizes, sumFieldWidths]
    rw [sumSizes_toFieldLayouts tail]

/--
Every offset in `s.fieldOffsets base` is at least `base`.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem fieldOffsets_ge_base :
    ∀ {αs : List Type} {w : Nat} (s : SymbolicStructSpine αs w) (base i o : Nat),
      (s.fieldOffsets base)[i]? = some o → base ≤ o
  | _, _, .nil _, _, _, _, h => nomatch h
  | _, _, @SymbolicStructSpine.cons _ _ n _ _ postPad tail, base, 0, o, h => by
    dsimp only [fieldOffsets] at h
    cases h
    exact Nat.le_refl base
  | _, _, @SymbolicStructSpine.cons _ _ n _ _ postPad tail, base, k + 1, o, h => by
    dsimp only [fieldOffsets] at h
    have ih := fieldOffsets_ge_base tail (base + (n + postPad)) k o h
    omega

/--
**$k$-Field Spine In-Bounds Theorem**: every field in `s.toFieldLayouts aligns` placed at
`s.fieldOffsets base` fits within `base + w`.

Kind: safety
Witness: universal
Assumes: S0
Subject: SymbolicStructSpine.fieldOffsets
-/
theorem fieldOffsets_inBounds :
    ∀ {αs : List Type} {w : Nat} (s : SymbolicStructSpine αs w)
      (base : Nat) (aligns : List Nat) (i o : Nat) (fl : FieldLayout),
      (s.fieldOffsets base)[i]? = some o →
      (s.toFieldLayouts aligns)[i]? = some fl →
      o + fl.size ≤ base + w
  | _, _, .nil _, _, _, _, _, _, hO, _ => nomatch hO
  | _, _, @SymbolicStructSpine.cons _ _ n restW _ postPad tail, base, aligns, 0, o, fl, hO, hF => by
    dsimp only [fieldOffsets, toFieldLayouts] at hO hF
    cases hO
    cases hF
    dsimp only
    omega
  | _, _, @SymbolicStructSpine.cons _ _ n restW _ postPad tail, base, aligns, k + 1, o, fl, hO, hF => by
    dsimp only [fieldOffsets, toFieldLayouts] at hO hF
    have ih := fieldOffsets_inBounds tail (base + (n + postPad)) aligns.tail k o fl hO hF
    omega

/--
**$k$-Field Spine Disjointness Theorem**: any two distinct fields `i ≠ j` in a
`SymbolicStructSpine` occupy pairwise disjoint byte intervals.

Kind: safety
Witness: universal
Assumes: S0
Subject: SymbolicStructSpine.fieldOffsets
-/
theorem fieldOffsets_disjoint :
    ∀ {αs : List Type} {w : Nat} (s : SymbolicStructSpine αs w)
      (base : Nat) (aligns : List Nat) (i j oi oj : Nat) (fi fj : FieldLayout),
      i ≠ j →
      (s.fieldOffsets base)[i]? = some oi →
      (s.fieldOffsets base)[j]? = some oj →
      (s.toFieldLayouts aligns)[i]? = some fi →
      (s.toFieldLayouts aligns)[j]? = some fj →
      oi + fi.size ≤ oj ∨ oj + fj.size ≤ oi
  | _, _, .nil _, _, _, _, _, _, _, _, _, _, hOi, _, _, _ => nomatch hOi
  | _, _, .cons _ _ _, _, _, 0, 0, _, _, _, _, hNe, _, _, _, _ =>
    False.elim (hNe rfl)
  | _, _, @SymbolicStructSpine.cons _ _ n _ _ postPad tail, base, aligns, 0, j + 1, oi, oj, fi, _, _, hOi, hOj, hFi, _ => by
    dsimp only [fieldOffsets, toFieldLayouts] at hOi hOj hFi
    cases hOi
    cases hFi
    have hGe := fieldOffsets_ge_base tail (base + (n + postPad)) j oj hOj
    dsimp only
    exact Or.inl (by omega)
  | _, _, @SymbolicStructSpine.cons _ _ n _ _ postPad tail, base, aligns, i + 1, 0, oi, oj, _, fj, _, hOi, hOj, _, hFj => by
    dsimp only [fieldOffsets, toFieldLayouts] at hOi hOj hFj
    cases hOj
    cases hFj
    have hGe := fieldOffsets_ge_base tail (base + (n + postPad)) i oi hOi
    dsimp only
    exact Or.inr (by omega)
  | _, _, @SymbolicStructSpine.cons _ _ n _ _ postPad tail, base, aligns, i + 1, j + 1, oi, oj, fi, fj, hNe, hOi, hOj, hFi, hFj => by
    dsimp only [fieldOffsets, toFieldLayouts] at hOi hOj hFi hFj
    have hNe' : i ≠ j := fun h => hNe (congrArg Nat.succ h)
    exact fieldOffsets_disjoint tail (base + (n + postPad)) aligns.tail i j oi oj fi fj hNe' hOi hOj hFi hFj

end SymbolicStructSpine

/--
Sequential $k$-field offset placement invariant starting at `base` within `total`:
field `0` sits at `o₀ ≥ base`, each subsequent field `i + 1` sits at `o_{i+1} ≥ o_i + f_i.size`,
and the final field fits within `total`.
-/
inductive SequentialFieldPlacement : Nat → List FieldLayout → List Nat → Nat → Prop where
  | nil {base total : Nat} (hLe : base ≤ total) : SequentialFieldPlacement base [] [] total
  | cons {base o total : Nat} {f : FieldLayout} {fs : List FieldLayout} {offs : List Nat}
      (hBase : base ≤ o)
      (hTail : SequentialFieldPlacement (o + f.size) fs offs total) :
      SequentialFieldPlacement base (f :: fs) (o :: offs) total

/-- Reconstruct field offsets from a base offset, field layouts, and inter-field padding gaps. -/
def reconstructSequentialOffsets : Nat → List FieldLayout → List Nat → List Nat
  | _, [], _ => []
  | base, f :: fs, pad :: pads =>
    (base + pad) :: reconstructSequentialOffsets (base + pad + f.size) fs pads
  | base, f :: fs, [] =>
    base :: reconstructSequentialOffsets (base + f.size) fs []

/--
**$k$-Field Sequential Gap Reconstruction**: every sequential $k$-field placement
`SequentialFieldPlacement base fs offs total` is realized by explicit non-negative inter-field
padding gaps `pads : List Nat` and trailing padding `tailPad : Nat` that reconstruct `offs` and
`total` (`base + sumSizes fs + pads.sum + tailPad = total`).

Kind: refinement
Witness: exists-sat
Assumes: S0
Subject: reconstructSequentialOffsets
-/
theorem exists_pads_of_sequentialFieldPlacement :
    ∀ {base total : Nat} {fs : List FieldLayout} {offs : List Nat},
      SequentialFieldPlacement base fs offs total →
      ∃ (pads : List Nat) (tailPad : Nat),
        pads.length = fs.length ∧
        reconstructSequentialOffsets base fs pads = offs ∧
        base + sumSizes fs + pads.sum + tailPad = total
  | base, total, [], [], .nil hLe =>
    ⟨[], total - base, rfl, rfl, by simp [sumSizes]; omega⟩
  | base, total, f :: fs, o :: offs, .cons hBase hTail => by
    obtain ⟨pads, tailPad, hLen, hRec, hTot⟩ := exists_pads_of_sequentialFieldPlacement hTail
    refine ⟨(o - base) :: pads, tailPad, congrArg Nat.succ hLen, ?_, ?_⟩
    · dsimp only [reconstructSequentialOffsets]
      have hBaseEq : base + (o - base) = o := by omega
      rw [hBaseEq, hRec]
    · dsimp only [sumSizes, List.sum_cons]
      omega

/--
General $k$-field heterogeneous struct `FixedByteCodec` built recursively from a
`SymbolicStructSpine`.
-/
def laidOutStructSymbolicPad :
    {αs : List Type} → {w : Nat} → SymbolicStructSpine αs w →
      FixedByteCodec (FieldTuple αs) w
  | _, _, .nil leadPad => FixedByteCodec.padUninit leadPad
  | _, _, .cons c postPad tail =>
    FixedByteCodec.prod (FixedByteCodec.padRight c postPad) (laidOutStructSymbolicPad tail)

/-- Alias for `laidOutStructSymbolicPad` in `FixedByteCodec`. -/
abbrev FixedByteCodec.laidOutStructSymbolicPad :
    {αs : List Type} → {w : Nat} → SymbolicStructSpine αs w →
      FixedByteCodec (FieldTuple αs) w :=
  Anneal.ByteCodec.laidOutStructSymbolicPad

/--
Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutStructSymbolicPad
-/
theorem laidOutStructSymbolicPad_isExactWidth :
    ∀ {αs : List Type} {w : Nat} (s : SymbolicStructSpine αs w),
      (laidOutStructSymbolicPad s).IsExactWidth
  | _, _, .nil leadPad => FixedByteCodec.padUninit_isExactWidth leadPad
  | _, _, .cons c postPad tail =>
    FixedByteCodec.prod_isExactWidth
      (FixedByteCodec.padRight c postPad)
      (laidOutStructSymbolicPad tail)

/--
General $k$-field `IsSurjectiveInitDecoder` (`FromBytes`) preservation across arbitrary
symbolic inter-field and trailing padding.

Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutStructSymbolicPad
-/
theorem laidOutStructSymbolicPad_isSurjectiveInitDecoder :
    ∀ {αs : List Type} {w : Nat} (s : SymbolicStructSpine αs w),
      s.AllFieldsSurjective →
      (laidOutStructSymbolicPad s).IsSurjectiveInitDecoder
  | _, _, .nil leadPad, _ => FixedByteCodec.padUninit_isSurjectiveInitDecoder leadPad
  | _, _, .cons _ postPad tail, h =>
    FixedByteCodec.prod_isSurjectiveInitDecoder
      (FixedByteCodec.padRight_isSurjectiveInitDecoder postPad h.1)
      (laidOutStructSymbolicPad_isSurjectiveInitDecoder tail h.2)

/--
General $k$-field `HasZeroValid` (`FromZeros`) preservation across arbitrary symbolic
inter-field and trailing padding.

Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutStructSymbolicPad
-/
theorem laidOutStructSymbolicPad_hasZeroValid :
    ∀ {αs : List Type} {w : Nat} (s : SymbolicStructSpine αs w),
      s.AllFieldsZeroValid →
      (laidOutStructSymbolicPad s).HasZeroValid
  | _, _, .nil leadPad, _ => FixedByteCodec.padUninit_hasZeroValid leadPad
  | _, _, .cons _ postPad tail, h =>
    FixedByteCodec.prod_hasZeroValid
      (FixedByteCodec.padRight_hasZeroValid postPad h.1)
      (laidOutStructSymbolicPad_hasZeroValid tail h.2)

/--
General $k$-field `IsInitCodec` (`IntoBytes`) characterization: over any inhabited
`FieldTuple αs`, `laidOutStructSymbolicPad s` is `IsInitCodec` iff `s.totalPadBytes = 0`
and all field codecs are `IsInitCodec`.

Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutStructSymbolicPad
-/
theorem laidOutStructSymbolicPad_isInitCodec_iff :
    ∀ {αs : List Type} {w : Nat} (s : SymbolicStructSpine αs w) (_x₀ : FieldTuple αs),
      (laidOutStructSymbolicPad s).IsInitCodec ↔
        s.totalPadBytes = 0 ∧ s.AllFieldsInit
  | _, _, .nil leadPad, () => by
    dsimp only [laidOutStructSymbolicPad, SymbolicStructSpine.totalPadBytes,
                SymbolicStructSpine.AllFieldsInit]
    cases leadPad with
    | zero =>
      exact ⟨fun _ => ⟨rfl, trivial⟩, fun _ => FixedByteCodec.padUninit_zero_isInitCodec⟩
    | succ k =>
      constructor
      · intro hInit
        exact False.elim (FixedByteCodec.padUninit_not_isInitCodec (Nat.succ_pos k) hInit)
      · rintro ⟨hEq, _⟩
        nomatch hEq
  | _, _, .cons c postPad tail, (a₀, rest₀) => by
    dsimp only [laidOutStructSymbolicPad, SymbolicStructSpine.totalPadBytes,
                SymbolicStructSpine.AllFieldsInit]
    have ih := laidOutStructSymbolicPad_isInitCodec_iff tail rest₀
    constructor
    · intro hInit
      have hHead : (FixedByteCodec.padRight c postPad).IsInitCodec := by
        intro a
        have hBoth := hInit (a, rest₀)
        dsimp only [FixedByteCodec.prod, FixedByteCodec.ofRoundTrip] at hBoth
        cases hA : allBytesInitialized ((FixedByteCodec.padRight c postPad).encode a) with
        | true => rfl
        | false =>
          rw [allBytesInitialized_append_eq_false_left
              ((laidOutStructSymbolicPad tail).encode rest₀) hA] at hBoth
          nomatch hBoth
      have hTailCodec : (laidOutStructSymbolicPad tail).IsInitCodec := by
        intro r
        have hBoth := hInit (a₀, r)
        dsimp only [FixedByteCodec.prod, FixedByteCodec.ofRoundTrip] at hBoth
        cases hR : allBytesInitialized ((laidOutStructSymbolicPad tail).encode r) with
        | true => rfl
        | false =>
          rw [allBytesInitialized_append_eq_false_right
              ((FixedByteCodec.padRight c postPad).encode a₀) hR] at hBoth
          nomatch hBoth
      obtain ⟨hPost0, hCInit⟩ := (FixedByteCodec.padRight_isInitCodec_iff c a₀).mp hHead
      obtain ⟨hTail0, hTailInit⟩ := ih.mp hTailCodec
      exact ⟨by omega, hCInit, hTailInit⟩
    · rintro ⟨hSum0, hCInit, hTailInit⟩
      have hPost0 : postPad = 0 := by omega
      have hTail0 : tail.totalPadBytes = 0 := by omega
      subst hPost0
      exact FixedByteCodec.prod_isInitCodec
        (FixedByteCodec.padRight_zero_isInitCodec hCInit)
        (ih.mpr ⟨hTail0, hTailInit⟩)

/--
Zero spine padding suffices for `IsInitCodec` (no inhabitant of `FieldTuple αs` needed).

Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutStructSymbolicPad
-/
theorem laidOutStructSymbolicPad_isInitCodec_of_zero_pad :
    ∀ {αs : List Type} {w : Nat} (s : SymbolicStructSpine αs w),
      s.totalPadBytes = 0 → s.AllFieldsInit → (laidOutStructSymbolicPad s).IsInitCodec
  | _, _, .nil leadPad, hPad, _ => by
    dsimp only [SymbolicStructSpine.totalPadBytes] at hPad
    subst hPad
    exact FixedByteCodec.padUninit_zero_isInitCodec
  | _, _, .cons _ postPad tail, hPad, hAll => by
    dsimp only [SymbolicStructSpine.totalPadBytes] at hPad
    have hPost : postPad = 0 := by omega
    have hTail : tail.totalPadBytes = 0 := by omega
    subst hPost
    exact FixedByteCodec.prod_isInitCodec (FixedByteCodec.padRight_zero_isInitCodec hAll.1)
      (laidOutStructSymbolicPad_isInitCodec_of_zero_pad tail hTail hAll.2)

/--
Positive spine padding emits at least one `.uninit` byte on every value `y : FieldTuple αs`.

Kind: divergence
Witness: negative
Assumes: S0
Subject: laidOutStructSymbolicPad
-/
theorem laidOutStructSymbolicPad_encode_uninit_of_totalPadBytes_pos :
    ∀ {αs : List Type} {w : Nat} (s : SymbolicStructSpine αs w),
      0 < s.totalPadBytes →
      ∀ (y : FieldTuple αs), allBytesInitialized ((laidOutStructSymbolicPad s).encode y) = false
  | _, _, .nil (k + 1), _, () => rfl
  | _, _, .cons c (k + 1) tail, _, (a, rest) =>
    allBytesInitialized_append_eq_false_left
      ((laidOutStructSymbolicPad tail).encode rest)
      (allBytesInitialized_append_eq_false_right (c.encode a) rfl)
  | _, _, .cons c 0 tail, hPos, (a, rest) => by
    dsimp only [SymbolicStructSpine.totalPadBytes] at hPos
    have hTailPos : 0 < tail.totalPadBytes := by omega
    exact allBytesInitialized_append_eq_false_right
      ((FixedByteCodec.padRight c 0).encode a)
      (laidOutStructSymbolicPad_encode_uninit_of_totalPadBytes_pos tail hTailPos rest)

/--
**$k$-Field Spine Byte-Window Realization**: for any `.cons c postPad tail`, the head field's
encoding occupies `[0, n)` and the remaining spine's encoding occupies `[n + postPad, (n + postPad) + restW)`,
matching the recursive offsets of `SymbolicStructSpine.fieldOffsets`.

Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutStructSymbolicPad
-/
theorem laidOutStructSymbolicPad_cons_windows {α : Type} {αs : List Type} {n restW : Nat}
    (c : FixedByteCodec α n) (postPad : Nat) (tail : SymbolicStructSpine αs restW)
    (a : α) (rest : FieldTuple αs) :
    (((laidOutStructSymbolicPad (.cons c postPad tail)).encode (a, rest)).take n = c.encode a) ∧
    (((laidOutStructSymbolicPad (.cons c postPad tail)).encode (a, rest)).drop (n + postPad) =
      (laidOutStructSymbolicPad tail).encode rest) := by
  have hEnc : (laidOutStructSymbolicPad (.cons c postPad tail)).encode (a, rest) =
      (c.encode a ++ replicateUninitBytes postPad) ++ (laidOutStructSymbolicPad tail).encode rest :=
    rfl
  have hEncAssoc : (laidOutStructSymbolicPad (.cons c postPad tail)).encode (a, rest) =
      c.encode a ++ (replicateUninitBytes postPad ++ (laidOutStructSymbolicPad tail).encode rest) := by
    rw [hEnc, List.append_assoc]
  have hHeadLen : (c.encode a ++ replicateUninitBytes postPad).length = n + postPad := by
    simp only [List.length_append, c.encode_length, length_replicateUninitBytes]
  refine ⟨?_, ?_⟩
  · rw [hEncAssoc, List.take_left' (c.encode_length a)]
  · rw [hEnc, List.drop_left' hHeadLen]

/-! ### Heterogeneous Field Memory-Order Permutations (`FieldPerm`) & Leading Padding -/

/--
Heterogeneous permutation from declaration-order field types `αs` to memory-order field types
`βs`, generated by congruence (`cons`), adjacent transposition (`swap`), and composition (`trans`);
`FieldPerm.toListPerm` certifies that it is a genuine `List.Perm`, so every memory order `rustc`
(or `-Z randomize-layout`) may choose for `#[repr(Rust)]` is expressible.
-/
inductive FieldPerm : List Type → List Type → Type 1 where
  | nil : FieldPerm [] []
  | cons (α : Type) {αs βs : List Type} (p : FieldPerm αs βs) : FieldPerm (α :: αs) (α :: βs)
  | swap (α β : Type) (αs : List Type) : FieldPerm (α :: β :: αs) (β :: α :: αs)
  | trans {αs βs γs : List Type} (p : FieldPerm αs βs) (q : FieldPerm βs γs) : FieldPerm αs γs

namespace FieldPerm

/-- Identity permutation (declaration order is memory order). -/
def refl : (αs : List Type) → FieldPerm αs αs
  | [] => .nil
  | α :: αs => .cons α (refl αs)

/-- Inverse permutation reversing a memory-order reordering back to declaration order. -/
def symm : {αs βs : List Type} → FieldPerm αs βs → FieldPerm βs αs
  | _, _, .nil => .nil
  | _, _, .cons α p => .cons α p.symm
  | _, _, .swap α β αs => .swap β α αs
  | _, _, .trans p q => .trans q.symm p.symm

/-- Move a declaration-order field tuple into memory order. -/
def apply : {αs βs : List Type} → FieldPerm αs βs → FieldTuple αs → FieldTuple βs
  | _, _, .nil, x => x
  | _, _, .cons _ p, (a, rest) => (a, p.apply rest)
  | _, _, .swap _ _ _, (a, b, rest) => (b, a, rest)
  | _, _, .trans p q, x => q.apply (p.apply x)

/-- Move a memory-order field tuple back into declaration order. -/
def unapply : {αs βs : List Type} → FieldPerm αs βs → FieldTuple βs → FieldTuple αs
  | _, _, .nil, y => y
  | _, _, .cons _ p, (a, rest) => (a, p.unapply rest)
  | _, _, .swap _ _ _, (b, a, rest) => (a, b, rest)
  | _, _, .trans p q, y => p.unapply (q.unapply y)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem symm_apply_eq_unapply :
    ∀ {αs βs : List Type} (p : FieldPerm αs βs) (y : FieldTuple βs),
      p.symm.apply y = p.unapply y
  | _, _, .nil, _ => rfl
  | _, _, .cons _ p, (a, rest) => by
    show (a, p.symm.apply rest) = (a, p.unapply rest)
    rw [symm_apply_eq_unapply p rest]
  | _, _, .swap _ _ _, (_, _, _) => rfl
  | _, _, .trans p q, y => by
    show p.symm.apply (q.symm.apply y) = p.unapply (q.unapply y)
    rw [symm_apply_eq_unapply q, symm_apply_eq_unapply p]

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem symm_unapply_eq_apply :
    ∀ {αs βs : List Type} (p : FieldPerm αs βs) (x : FieldTuple αs),
      p.symm.unapply x = p.apply x
  | _, _, .nil, _ => rfl
  | _, _, .cons _ p, (a, rest) => by
    show (a, p.symm.unapply rest) = (a, p.apply rest)
    rw [symm_unapply_eq_apply p rest]
  | _, _, .swap _ _ _, (_, _, _) => rfl
  | _, _, .trans p q, x => by
    show q.symm.unapply (p.symm.unapply x) = q.apply (p.apply x)
    rw [symm_unapply_eq_apply p, symm_unapply_eq_apply q]

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem unapply_apply :
    ∀ {αs βs : List Type} (p : FieldPerm αs βs) (x : FieldTuple αs), p.unapply (p.apply x) = x
  | _, _, .nil, _ => rfl
  | _, _, .cons _ p, (a, rest) => by
    show (a, p.unapply (p.apply rest)) = (a, rest)
    rw [unapply_apply p rest]
  | _, _, .swap _ _ _, (_, _, _) => rfl
  | _, _, .trans p q, x => by
    show p.unapply (q.unapply (q.apply (p.apply x))) = x
    rw [unapply_apply q, unapply_apply p]

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem apply_unapply :
    ∀ {αs βs : List Type} (p : FieldPerm αs βs) (y : FieldTuple βs), p.apply (p.unapply y) = y
  | _, _, .nil, _ => rfl
  | _, _, .cons _ p, (a, rest) => by
    show (a, p.apply (p.unapply rest)) = (a, rest)
    rw [apply_unapply p rest]
  | _, _, .swap _ _ _, (_, _, _) => rfl
  | _, _, .trans p q, y => by
    show q.apply (p.apply (p.unapply (q.unapply y))) = y
    rw [apply_unapply p, apply_unapply q]

/--
Every `FieldPerm` is a genuine list permutation of the field types.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem toListPerm : ∀ {αs βs : List Type}, FieldPerm αs βs → List.Perm αs βs
  | _, _, .nil => List.Perm.nil
  | _, _, .cons α p => List.Perm.cons α (toListPerm p)
  | _, _, .swap α β αs => List.Perm.swap β α αs
  | _, _, .trans p q => List.Perm.trans (toListPerm p) (toListPerm q)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem refl_apply :
    ∀ (αs : List Type) (x : FieldTuple αs), (FieldPerm.refl αs).apply x = x
  | [], _ => rfl
  | _ :: αs, (a, rest) => by
    show (a, (FieldPerm.refl αs).apply rest) = (a, rest)
    rw [FieldPerm.refl_apply αs rest]

end FieldPerm

/--
General $k$-field heterogeneous struct codec with leading padding `lead` and an arbitrary
memory-order permutation `perm`: values are supplied in declaration order (`FieldTuple αs`) and
laid out in memory order (`FieldTuple βs`) by the spine `s` (symbolic inter-field and trailing
padding) after `lead` bytes of leading padding.
-/
def laidOutStructSymbolicPadPerm {αs βs : List Type} {w : Nat}
    (lead : Nat) (perm : FieldPerm αs βs) (s : SymbolicStructSpine βs w) :
    FixedByteCodec (FieldTuple αs) (lead + w) :=
  (FixedByteCodec.padLeft lead (laidOutStructSymbolicPad s)).mapEquiv
    perm.unapply perm.apply perm.apply_unapply perm.unapply_apply

/-- Alias for `laidOutStructSymbolicPadPerm` in `FixedByteCodec`. -/
abbrev FixedByteCodec.laidOutStructSymbolicPadPerm {αs βs : List Type} {w : Nat}
    (lead : Nat) (perm : FieldPerm αs βs) (s : SymbolicStructSpine βs w) :
    FixedByteCodec (FieldTuple αs) (lead + w) :=
  Anneal.ByteCodec.laidOutStructSymbolicPadPerm lead perm s

/--
Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutStructSymbolicPadPerm
-/
theorem laidOutStructSymbolicPadPerm_encode {αs βs : List Type} {w : Nat}
    (lead : Nat) (perm : FieldPerm αs βs) (s : SymbolicStructSpine βs w) (x : FieldTuple αs) :
    (laidOutStructSymbolicPadPerm lead perm s).encode x =
      replicateUninitBytes lead ++ (laidOutStructSymbolicPad s).encode (perm.apply x) :=
  rfl

/--
Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutStructSymbolicPadPerm
-/
theorem laidOutStructSymbolicPadPerm_isExactWidth {αs βs : List Type} {w : Nat}
    (lead : Nat) (perm : FieldPerm αs βs) (s : SymbolicStructSpine βs w) :
    (laidOutStructSymbolicPadPerm lead perm s).IsExactWidth :=
  FixedByteCodec.mapEquiv_isExactWidth _ _ _ _ _
    (FixedByteCodec.padLeft_isExactWidth lead (laidOutStructSymbolicPad s))

/--
Universal $k$-field `FromBytes` preservation across arbitrary leading/inter-field/trailing padding
AND arbitrary field memory-order permutations.

Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutStructSymbolicPadPerm
-/
theorem laidOutStructSymbolicPadPerm_isSurjectiveInitDecoder {αs βs : List Type} {w : Nat}
    (lead : Nat) (perm : FieldPerm αs βs) (s : SymbolicStructSpine βs w)
    (h : s.AllFieldsSurjective) :
    (laidOutStructSymbolicPadPerm lead perm s).IsSurjectiveInitDecoder :=
  FixedByteCodec.mapEquiv_isSurjectiveInitDecoder _ _ _ _ _
    (FixedByteCodec.padLeft_isSurjectiveInitDecoder lead
      (laidOutStructSymbolicPad_isSurjectiveInitDecoder s h))

/--
Universal $k$-field `FromZeros` preservation across arbitrary padding and permutations.

Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutStructSymbolicPadPerm
-/
theorem laidOutStructSymbolicPadPerm_hasZeroValid {αs βs : List Type} {w : Nat}
    (lead : Nat) (perm : FieldPerm αs βs) (s : SymbolicStructSpine βs w)
    (h : s.AllFieldsZeroValid) :
    (laidOutStructSymbolicPadPerm lead perm s).HasZeroValid :=
  FixedByteCodec.mapEquiv_hasZeroValid _ _ _ _ _
    (FixedByteCodec.padLeft_hasZeroValid lead (laidOutStructSymbolicPad_hasZeroValid s h))

/--
Exact $k$-field `IntoBytes` characterization across permutations: over any inhabited
`FieldTuple αs`, the permuted codec is `IsInitCodec` iff there is no leading padding, no spine
padding, and every field codec is `IsInitCodec` (independent of the memory order).

Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutStructSymbolicPadPerm
-/
theorem laidOutStructSymbolicPadPerm_isInitCodec_iff {αs βs : List Type} {w : Nat}
    (lead : Nat) (perm : FieldPerm αs βs) (s : SymbolicStructSpine βs w) (x₀ : FieldTuple αs) :
    (laidOutStructSymbolicPadPerm lead perm s).IsInitCodec ↔
      lead = 0 ∧ s.totalPadBytes = 0 ∧ s.AllFieldsInit := by
  constructor
  · intro hInit
    have hPL : (FixedByteCodec.padLeft lead (laidOutStructSymbolicPad s)).IsInitCodec := by
      intro y
      have h := hInit (perm.unapply y)
      change allBytesInitialized
        ((FixedByteCodec.padLeft lead (laidOutStructSymbolicPad s)).encode
          (perm.apply (perm.unapply y))) = true at h
      rwa [perm.apply_unapply] at h
    obtain ⟨hLead, hSpine⟩ :=
      (FixedByteCodec.padLeft_isInitCodec_iff (laidOutStructSymbolicPad s) (perm.apply x₀)).mp hPL
    obtain ⟨hPad, hAll⟩ := (laidOutStructSymbolicPad_isInitCodec_iff s (perm.apply x₀)).mp hSpine
    exact ⟨hLead, hPad, hAll⟩
  · rintro ⟨hLead, hPad, hAll⟩
    exact FixedByteCodec.mapEquiv_isInitCodec _ _ _ _ _
      (FixedByteCodec.padLeft_isInitCodec_of_eq_zero hLead
        (laidOutStructSymbolicPad_isInitCodec_of_zero_pad s hPad hAll))

/--
Positive leading or spine padding (`0 < lead + s.totalPadBytes`) emits at least one `.uninit` byte
on **every** declaration-order tuple `x : FieldTuple αs` across any memory-order permutation `perm`.

Kind: divergence
Witness: negative
Assumes: S0
Subject: laidOutStructSymbolicPadPerm
-/
theorem laidOutStructSymbolicPadPerm_encode_uninit_of_pad_pos
    {αs βs : List Type} {w : Nat}
    (lead : Nat) (perm : FieldPerm αs βs) (s : SymbolicStructSpine βs w)
    (hPos : 0 < lead + s.totalPadBytes) (x : FieldTuple αs) :
    allBytesInitialized ((laidOutStructSymbolicPadPerm lead perm s).encode x) = false := by
  rw [laidOutStructSymbolicPadPerm_encode]
  cases lead with
  | succ k =>
    exact allBytesInitialized_append_eq_false_left
      ((laidOutStructSymbolicPad s).encode (perm.apply x)) rfl
  | zero =>
    have hS : 0 < s.totalPadBytes := by omega
    exact allBytesInitialized_append_eq_false_right
      (replicateUninitBytes 0)
      (laidOutStructSymbolicPad_encode_uninit_of_totalPadBytes_pos s hS (perm.apply x))

/-- Demo 3-field permutation: declaration order `[α, β, γ]` laid out in memory as `[β, γ, α]`
(e.g. `struct S { a: u8, b: u32, c: u16 }` reordered by `rustc` to `b, c, a`). -/
def rotateLeft3 (α β γ : Type) : FieldPerm [α, β, γ] [β, γ, α] :=
  .trans (.swap α β [γ]) (.cons β (.swap α γ []))

/--
The rotated permutation places field `b` first, `c` second, `a` third in memory while the codec's
value interface stays in declaration order `(a, b, c)`.

Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutStructSymbolicPadPerm
-/
theorem rotateLeft3_encode_memory_order {α β γ : Type} {n₁ n₂ n₃ : Nat}
    (c₁ : FixedByteCodec α n₁) (c₂ : FixedByteCodec β n₂) (c₃ : FixedByteCodec γ n₃)
    (a : α) (b : β) (c : γ) :
    (laidOutStructSymbolicPadPerm 0 (rotateLeft3 α β γ)
        (.cons c₂ 0 (.cons c₃ 0 (.cons c₁ 0 (.nil 0))))).encode (a, b, c, ()) =
      c₂.encode b ++ (c₃.encode c ++ (c₁.encode a ++ [])) := by
  show replicateUninitBytes 0 ++
      ((c₂.encode b ++ replicateUninitBytes 0) ++
        ((c₃.encode c ++ replicateUninitBytes 0) ++
          ((c₁.encode a ++ replicateUninitBytes 0) ++ replicateUninitBytes 0))) = _
  simp only [show replicateUninitBytes 0 = [] from rfl, List.nil_append, List.append_nil]

/-! ### Constructive Memory-Order Sorting (`memKey`, `memSort`) & `PlacedCodecSpine` -/

/-- `0` for a zero-sized field, `1` otherwise. -/
def nzBit : Nat → Nat
  | 0 => 0
  | _ + 1 => 1

/-- Memory-order sort key of a placed field `(offset, layout)`: by offset, with a zero-sized field
before a sized field at the same offset (a ZST may sit exactly where a sized field starts). -/
def memKey (p : Nat × FieldLayout) : Nat := 2 * p.1 + nzBit p.2.size

/-- Byte-window disjointness of two placed fields. -/
def PlacedDisjoint (p q : Nat × FieldLayout) : Prop :=
  p.1 + p.2.size ≤ q.1 ∨ q.1 + q.2.size ≤ p.1

/-- Insert a placed field into a `memKey`-sorted list. -/
def memInsert (p : Nat × FieldLayout) : List (Nat × FieldLayout) → List (Nat × FieldLayout)
  | [] => [p]
  | q :: qs => if memKey p ≤ memKey q then p :: q :: qs else q :: memInsert p qs

/-- Constructive insertion sort of placed fields into memory order (`memKey`). -/
def memSort : List (Nat × FieldLayout) → List (Nat × FieldLayout)
  | [] => []
  | p :: ps => memInsert p (memSort ps)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem memInsert_perm (p : Nat × FieldLayout) :
    ∀ (l : List (Nat × FieldLayout)), (memInsert p l).Perm (p :: l)
  | [] => List.Perm.refl _
  | q :: qs => by
    unfold memInsert
    split
    · exact List.Perm.refl _
    · exact ((memInsert_perm p qs).cons q).trans (List.Perm.swap p q qs)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem memSort_perm : ∀ (l : List (Nat × FieldLayout)), (memSort l).Perm l
  | [] => List.Perm.refl _
  | p :: ps => (memInsert_perm p (memSort ps)).trans ((memSort_perm ps).cons p)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem memInsert_pairwise (p : Nat × FieldLayout) :
    ∀ (l : List (Nat × FieldLayout)), l.Pairwise (fun a b => memKey a ≤ memKey b) →
      (memInsert p l).Pairwise (fun a b => memKey a ≤ memKey b)
  | [], _ => List.pairwise_singleton _ _
  | q :: qs, hl => by
    rw [List.pairwise_cons] at hl
    unfold memInsert
    split
    · next hpq =>
      refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr hl⟩
      intro r hr
      rcases List.mem_cons.mp hr with hEq | hr'
      · rw [hEq]
        exact hpq
      · exact Nat.le_trans hpq (hl.1 r hr')
    · next hpq =>
      refine List.pairwise_cons.mpr ⟨?_, memInsert_pairwise p qs hl.2⟩
      intro r hr
      rcases List.mem_cons.mp ((memInsert_perm p qs).mem_iff.mp hr) with hEq | hr'
      · rw [hEq]
        exact Nat.le_of_lt (Nat.lt_of_not_le hpq)
      · exact hl.1 r hr'

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem memSort_pairwise :
    ∀ (l : List (Nat × FieldLayout)), (memSort l).Pairwise (fun a b => memKey a ≤ memKey b)
  | [] => List.Pairwise.nil
  | p :: ps => memInsert_pairwise p (memSort ps) (memSort_pairwise ps)

/--
Demo: `struct S { a: u8, b: u32, c: () }` laid out by `rustc` as `b @ 0, a @ 4, c @ 5` (size 8):
`memSort` recovers the memory order `[b, a, c]` from the declaration-order placement, and a ZST
sharing an offset with a sized field sorts first (kernel-checked by `rfl`).

Kind: helper
Witness: universal
Assumes: S0
-/
theorem memSort_reordered_and_shared_offset_demo :
    memSort [(4, ⟨1, 1⟩), (0, ⟨4, 4⟩), (5, ⟨0, 1⟩)] = [(0, ⟨4, 4⟩), (4, ⟨1, 1⟩), (5, ⟨0, 1⟩)] ∧
    memSort [(4, ⟨4, 4⟩), (4, ⟨0, 1⟩)] = [(4, ⟨0, 1⟩), (4, ⟨4, 4⟩)] :=
  ⟨rfl, rfl⟩

/--
Two disjoint placed fields in `memKey` order are sequential: the first ends before the second
starts (a ZST sharing an offset with a sized field sorts first, two sized fields never share one).

Kind: helper
Witness: universal
Assumes: S0
-/
theorem placed_end_le_of_memKey_le {p q : Nat × FieldLayout}
    (hKey : memKey p ≤ memKey q) (hDisj : PlacedDisjoint p q) : p.1 + p.2.size ≤ q.1 := by
  rcases hDisj with h | h
  · exact h
  · unfold memKey at hKey
    obtain ⟨po, ⟨ps, pa⟩⟩ := p
    obtain ⟨qo, ⟨qs, qa⟩⟩ := q
    dsimp only at hKey h ⊢
    cases ps <;> cases qs <;> simp only [nzBit] at hKey <;> omega

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem sequentialFieldPlacement_of_sorted_disjoint :
    ∀ (l : List (Nat × FieldLayout)) (base total : Nat),
      l.Pairwise (fun a b => memKey a ≤ memKey b) →
      l.Pairwise PlacedDisjoint →
      (∀ p ∈ l, base ≤ p.1) →
      (∀ p ∈ l, p.1 + p.2.size ≤ total) →
      base ≤ total →
      SequentialFieldPlacement base (l.map Prod.snd) (l.map Prod.fst) total
  | [], _, _, _, _, _, _, hLe => .nil hLe
  | p :: ps, _, total, hSort, hDisj, hBase, hIn, _ => by
    rw [List.pairwise_cons] at hSort hDisj
    have hHead : p ∈ p :: ps := List.mem_cons.mpr (Or.inl rfl)
    exact .cons (hBase p hHead)
      (sequentialFieldPlacement_of_sorted_disjoint ps (p.1 + p.2.size) total hSort.2 hDisj.2
        (fun q hq => placed_end_le_of_memKey_le (hSort.1 q hq) (hDisj.1 q hq))
        (fun q hq => hIn q (List.mem_cons_of_mem p hq))
        (hIn p hHead))

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem SequentialFieldPlacement.base_le_headD {base total : Nat} {fls : List FieldLayout}
    {offs : List Nat} (h : SequentialFieldPlacement base fls offs total) : base ≤ offs.headD base := by
  cases h with
  | nil _ => exact Nat.le_refl base
  | cons hBase _ => exact hBase

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem sumSizes_perm {l₁ l₂ : List FieldLayout} (h : l₁.Perm l₂) : sumSizes l₁ = sumSizes l₂ := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    simp only [sumSizes]
    omega
  | swap x y l =>
    simp only [sumSizes]
    omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

namespace SymbolicStructSpine

/-- Raw field byte widths of a spine, in memory order. -/
def widths : {αs : List Type} → {w : Nat} → SymbolicStructSpine αs w → List Nat
  | _, _, .nil _ => []
  | _, _, @SymbolicStructSpine.cons _ _ n _ _ _ tail => n :: tail.widths

/-- Total width of `s.repad pads trail`. -/
def repadWidth : {αs : List Type} → {w : Nat} → SymbolicStructSpine αs w → List Nat → Nat → Nat
  | _, _, .nil _, _, trail => trail
  | _, _, @SymbolicStructSpine.cons _ _ n _ _ _ tail, pads, trail =>
    (n + pads.headD 0) + tail.repadWidth pads.tail trail

/-- Keep every field codec of `s` (same memory order) but replace its post-field padding by `pads`
(missing entries are `0`) and its trailing `.nil` padding by `trail`. -/
def repad : {αs : List Type} → {w : Nat} → (s : SymbolicStructSpine αs w) → (pads : List Nat) →
    (trail : Nat) → SymbolicStructSpine αs (s.repadWidth pads trail)
  | _, _, .nil _, _, trail => .nil trail
  | _, _, .cons c _ tail, pads, trail => .cons c (pads.headD 0) (tail.repad pads.tail trail)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem allFieldsSurjective_repad :
    ∀ {αs : List Type} {w : Nat} (s : SymbolicStructSpine αs w) (pads : List Nat) (trail : Nat),
      s.AllFieldsSurjective → (s.repad pads trail).AllFieldsSurjective
  | _, _, .nil _, _, _, _ => trivial
  | _, _, .cons _ _ tail, pads, trail, h => ⟨h.1, allFieldsSurjective_repad tail pads.tail trail h.2⟩

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem allFieldsZeroValid_repad :
    ∀ {αs : List Type} {w : Nat} (s : SymbolicStructSpine αs w) (pads : List Nat) (trail : Nat),
      s.AllFieldsZeroValid → (s.repad pads trail).AllFieldsZeroValid
  | _, _, .nil _, _, _, _ => trivial
  | _, _, .cons _ _ tail, pads, trail, h => ⟨h.1, allFieldsZeroValid_repad tail pads.tail trail h.2⟩

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem allFieldsInit_repad_iff :
    ∀ {αs : List Type} {w : Nat} (s : SymbolicStructSpine αs w) (pads : List Nat) (trail : Nat),
      (s.repad pads trail).AllFieldsInit ↔ s.AllFieldsInit
  | _, _, .nil _, _, _ => Iff.rfl
  | _, _, .cons _ _ tail, pads, trail =>
    and_congr Iff.rfl (allFieldsInit_repad_iff tail pads.tail trail)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem sumFieldWidths_repad :
    ∀ {αs : List Type} {w : Nat} (s : SymbolicStructSpine αs w) (pads : List Nat) (trail : Nat),
      (s.repad pads trail).sumFieldWidths = s.sumFieldWidths
  | _, _, .nil _, _, _ => rfl
  | _, _, @SymbolicStructSpine.cons _ _ n _ _ _ tail, pads, trail => by
    show n + (tail.repad pads.tail trail).sumFieldWidths = n + tail.sumFieldWidths
    rw [sumFieldWidths_repad tail pads.tail trail]

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem sumFieldWidths_eq_sumSizes_of_widths :
    ∀ {αs : List Type} {w : Nat} (s : SymbolicStructSpine αs w) (fls : List FieldLayout),
      s.widths = fls.map FieldLayout.size → s.sumFieldWidths = sumSizes fls
  | _, _, .nil _, [], _ => rfl
  | _, _, .nil _, _ :: _, hW => nomatch hW
  | _, _, .cons _ _ _, [], hW => nomatch hW
  | _, _, @SymbolicStructSpine.cons _ _ n _ _ _ tail, f :: fls, hW => by
    injection hW with hN hTail
    show n + tail.sumFieldWidths = f.size + sumSizes fls
    rw [hN, sumFieldWidths_eq_sumSizes_of_widths tail fls hTail]

/--
**Sequential Placements Are Re-Padded Spines**: for any sequential placement of `fls` at `offs`
within `total` and any codec spine `s` whose memory-order field widths are `fls.map size`, some
post-field paddings `pads` and trailing padding `trail` make `s.repad pads trail` place every field
exactly at `offs` (starting at leading padding `offs.headD base`) with total width `total`.

Kind: refinement
Witness: exists-sat
Assumes: S0
Subject: SymbolicStructSpine.repad
-/
theorem exists_repad_of_sequentialFieldPlacement {base total : Nat} {fls : List FieldLayout}
    {offs : List Nat} (hSeq : SequentialFieldPlacement base fls offs total) :
    ∀ {αs : List Type} {w : Nat} (s : SymbolicStructSpine αs w),
      s.widths = fls.map FieldLayout.size →
      ∃ (pads : List Nat) (trail : Nat),
        (s.repad pads trail).fieldOffsets (offs.headD base) = offs ∧
        offs.headD base + s.repadWidth pads trail = total := by
  induction hSeq with
  | @nil base total hLe =>
    intro αs w s hW
    cases s with
    | nil _ =>
      refine ⟨[], total - base, rfl, ?_⟩
      show base + (total - base) = total
      omega
    | cons _ _ _ => nomatch hW
  | @cons base o total f fls offs hBase hTail ih =>
    intro αs w s hW
    cases s with
    | nil _ => nomatch hW
    | @cons α αs' n restW c p tail =>
      injection hW with hN hTailW
      subst hN
      obtain ⟨pads, trail, hOffs, hTot⟩ := ih tail hTailW
      have hLe := hTail.base_le_headD
      refine ⟨(offs.headD (o + f.size) - (o + f.size)) :: pads, trail, ?_, ?_⟩
      · show o :: (tail.repad pads trail).fieldOffsets
            (o + (f.size + (offs.headD (o + f.size) - (o + f.size)))) = o :: offs
        rw [show o + (f.size + (offs.headD (o + f.size) - (o + f.size))) = offs.headD (o + f.size) by
          omega, hOffs]
      · show o + ((f.size + (offs.headD (o + f.size) - (o + f.size))) + tail.repadWidth pads trail) =
            total
        omega

/-- Byte windows of a spine laid out from offset `base`: each field's offset and its encoding. -/
def windows :
    {βs : List Type} → {W : Nat} → SymbolicStructSpine βs W → FieldTuple βs → Nat →
      List (Nat × List AbstractByte)
  | _, _, .nil _, _, _ => []
  | _, _, @SymbolicStructSpine.cons _ _ n _ c postPad tail, (a, rest), base =>
    (base, c.encode a) :: tail.windows rest (base + (n + postPad))

/--
**Spine Byte-Window Placement**: after any prefix `pre`, each spine field's encoding sits exactly at
its window offset in `pre ++ (laidOutStructSymbolicPad s).encode y`.

Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutStructSymbolicPad
-/
theorem window_bytes :
    ∀ {βs : List Type} {W : Nat} (s : SymbolicStructSpine βs W) (y : FieldTuple βs)
      (pre : List AbstractByte) (o : Nat) (bs : List AbstractByte),
      (o, bs) ∈ s.windows y pre.length →
      ((pre ++ (laidOutStructSymbolicPad s).encode y).drop o).take bs.length = bs
  | _, _, .nil _, _, _, _, _, hMem => nomatch hMem
  | _, _, @SymbolicStructSpine.cons _ _ n _ c postPad tail, (a, rest), pre, o, bs, hMem => by
    have hEnc : (laidOutStructSymbolicPad (.cons c postPad tail)).encode (a, rest) =
        (c.encode a ++ replicateUninitBytes postPad) ++ (laidOutStructSymbolicPad tail).encode rest :=
      rfl
    rw [hEnc]
    rcases List.mem_cons.mp hMem with hHead | hTail
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hHead
      rw [List.drop_left, List.append_assoc, List.take_left]
    · have hLen : (pre ++ (c.encode a ++ replicateUninitBytes postPad)).length =
          pre.length + (n + postPad) := by
        simp only [List.length_append, c.encode_length, length_replicateUninitBytes]
      rw [← hLen] at hTail
      have ih := SymbolicStructSpine.window_bytes tail rest
        (pre ++ (c.encode a ++ replicateUninitBytes postPad)) o bs hTail
      rwa [List.append_assoc] at ih

end SymbolicStructSpine

/--
Declaration-order (or memory-order) list of placed fields `(offset, fl)` paired with a
`FixedByteCodec α fl.size` for each field type `α`. Unlike `SymbolicStructSpine`, a
`PlacedCodecSpine` carries no assumption that its fields are already in memory order:
`PlacedCodecSpine.memSort` constructively sorts it by `memKey`, producing the memory-order
type list `pc.memSortTypes`, the constructive permutation `pc.memSortPerm : FieldPerm αs pc.memSortTypes`,
and the memory-order `SymbolicStructSpine`.
-/
inductive PlacedCodecSpine : List Type → Type 1 where
  | nil : PlacedCodecSpine []
  | cons {α : Type} {αs : List Type} (p : Nat × FieldLayout)
      (c : FixedByteCodec α p.2.size) (tail : PlacedCodecSpine αs) :
      PlacedCodecSpine (α :: αs)

namespace PlacedCodecSpine

/-- Underlying placed `(offset, FieldLayout)` list of a `PlacedCodecSpine`. -/
def placed : {αs : List Type} → PlacedCodecSpine αs → List (Nat × FieldLayout)
  | _, .nil => []
  | _, .cons p _ tail => p :: tail.placed

/-- Unpadded spine byte width of a `PlacedCodecSpine` (`0` inter-field and trailing padding). -/
def rawWidth : {αs : List Type} → PlacedCodecSpine αs → Nat
  | _, .nil => 0
  | _, .cons p _ tail => (p.2.size + 0) + tail.rawWidth

/-- Every field codec in `pc` is a surjective initial-byte decoder (`FromBytes`). -/
def AllFieldsSurjective : {αs : List Type} → PlacedCodecSpine αs → Prop
  | _, .nil => True
  | _, .cons _ c tail => c.IsSurjectiveInitDecoder ∧ tail.AllFieldsSurjective

/-- Every field codec in `pc` decodes the all-zero buffer (`FromZeros`). -/
def AllFieldsZeroValid : {αs : List Type} → PlacedCodecSpine αs → Prop
  | _, .nil => True
  | _, .cons _ c tail => c.HasZeroValid ∧ tail.AllFieldsZeroValid

/-- Every field codec in `pc` emits only initialized bytes (`IntoBytes`). -/
def AllFieldsInit : {αs : List Type} → PlacedCodecSpine αs → Prop
  | _, .nil => True
  | _, .cons _ c tail => c.IsInitCodec ∧ tail.AllFieldsInit

/-- Convert a `PlacedCodecSpine` into an unpadded `SymbolicStructSpine` in the same field order. -/
def toSymbolicStructSpine :
    {αs : List Type} → (pc : PlacedCodecSpine αs) → SymbolicStructSpine αs pc.rawWidth
  | _, .nil => .nil 0
  | _, .cons _ c tail => .cons c 0 tail.toSymbolicStructSpine

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem widths_toSymbolicStructSpine :
    ∀ {αs : List Type} (pc : PlacedCodecSpine αs),
      pc.toSymbolicStructSpine.widths = pc.placed.map (fun p => p.2.size)
  | _, .nil => rfl
  | _, .cons p _ tail => by
    show p.2.size :: tail.toSymbolicStructSpine.widths = p.2.size :: tail.placed.map (fun q => q.2.size)
    rw [widths_toSymbolicStructSpine tail]

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem allFieldsSurjective_toSymbolicStructSpine :
    ∀ {αs : List Type} (pc : PlacedCodecSpine αs),
      pc.toSymbolicStructSpine.AllFieldsSurjective ↔ pc.AllFieldsSurjective
  | _, .nil => Iff.rfl
  | _, .cons _ _ tail =>
    and_congr Iff.rfl (allFieldsSurjective_toSymbolicStructSpine tail)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem allFieldsZeroValid_toSymbolicStructSpine :
    ∀ {αs : List Type} (pc : PlacedCodecSpine αs),
      pc.toSymbolicStructSpine.AllFieldsZeroValid ↔ pc.AllFieldsZeroValid
  | _, .nil => Iff.rfl
  | _, .cons _ _ tail =>
    and_congr Iff.rfl (allFieldsZeroValid_toSymbolicStructSpine tail)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem allFieldsInit_toSymbolicStructSpine :
    ∀ {αs : List Type} (pc : PlacedCodecSpine αs),
      pc.toSymbolicStructSpine.AllFieldsInit ↔ pc.AllFieldsInit
  | _, .nil => Iff.rfl
  | _, .cons _ _ tail =>
    and_congr Iff.rfl (allFieldsInit_toSymbolicStructSpine tail)

/-- Type list resulting from inserting `(α, p)` into `pc : PlacedCodecSpine βs` in `memKey` order. -/
def memInsertTypes (α : Type) (p : Nat × FieldLayout) :
    {βs : List Type} → PlacedCodecSpine βs → List Type
  | _, .nil => [α]
  | β :: βs, .cons q _ tail =>
    cond (decide (memKey p ≤ memKey q)) (α :: β :: βs) (β :: tail.memInsertTypes α p)

/-- Cast-free branch selector for `PlacedCodecSpine.memInsert`. -/
def memInsertAux {α β : Type} {βs : List Type}
    (p : Nat × FieldLayout) (c : FixedByteCodec α p.2.size)
    (q : Nat × FieldLayout) (c' : FixedByteCodec β q.2.size)
    (tail : PlacedCodecSpine βs)
    {recTypes : List Type} (recSpine : PlacedCodecSpine recTypes) :
    (b : Bool) → PlacedCodecSpine (cond b (α :: β :: βs) (β :: recTypes))
  | true => .cons p c (.cons q c' tail)
  | false => .cons q c' recSpine

/-- Constructively insert a placed field codec `c` into `pc : PlacedCodecSpine βs` in `memKey` order. -/
def memInsert {α : Type} (p : Nat × FieldLayout) (c : FixedByteCodec α p.2.size) :
    {βs : List Type} → (pc : PlacedCodecSpine βs) → PlacedCodecSpine (pc.memInsertTypes α p)
  | _, .nil => .cons p c .nil
  | _, .cons q c' tail =>
    memInsertAux p c q c' tail (tail.memInsert p c) (decide (memKey p ≤ memKey q))

/-- Cast-free branch selector for `PlacedCodecSpine.memInsertPerm`. -/
def memInsertPermAux (α β : Type) (βs : List Type)
    {recTypes : List Type} (recPerm : FieldPerm (α :: βs) recTypes) :
    (b : Bool) → FieldPerm (α :: β :: βs) (cond b (α :: β :: βs) (β :: recTypes))
  | true => .refl (α :: β :: βs)
  | false => .trans (.swap α β βs) (.cons β recPerm)

/-- Constructive `FieldPerm` witnessing the single-element insertion `pc.memInsertTypes α p`. -/
def memInsertPerm (α : Type) (p : Nat × FieldLayout) :
    {βs : List Type} → (pc : PlacedCodecSpine βs) → FieldPerm (α :: βs) (pc.memInsertTypes α p)
  | _, .nil => .refl [α]
  | β :: βs, .cons q _ tail =>
    memInsertPermAux α β βs (tail.memInsertPerm α p) (decide (memKey p ≤ memKey q))

/-- Memory-order type list and sorted `PlacedCodecSpine` bundled together for structural recursion. -/
def memSortWithTypes :
    {αs : List Type} → PlacedCodecSpine αs → Σ βs : List Type, PlacedCodecSpine βs
  | _, .nil => ⟨[], .nil⟩
  | α :: _, .cons p c tail =>
    let ⟨_, sTail⟩ := tail.memSortWithTypes
    ⟨sTail.memInsertTypes α p, sTail.memInsert p c⟩

/-- Memory-order type list produced by sorting `pc : PlacedCodecSpine αs` by `memKey`. -/
def memSortTypes {αs : List Type} (pc : PlacedCodecSpine αs) : List Type :=
  pc.memSortWithTypes.1

/-- Constructively sort a declaration-order `PlacedCodecSpine` into memory order (`memKey`). -/
def memSort {αs : List Type} (pc : PlacedCodecSpine αs) : PlacedCodecSpine pc.memSortTypes :=
  pc.memSortWithTypes.2

/-- Constructive `FieldPerm` from declaration-order types `αs` to memory-order types `pc.memSortTypes`. -/
def memSortPerm :
    {αs : List Type} → (pc : PlacedCodecSpine αs) → FieldPerm αs pc.memSortTypes
  | _, .nil => .nil
  | α :: _, .cons p _ tail =>
    .trans (.cons α tail.memSortPerm) (tail.memSort.memInsertPerm α p)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem placed_memInsertAux {α β : Type} {βs recTypes : List Type}
    (p : Nat × FieldLayout) (c : FixedByteCodec α p.2.size)
    (q : Nat × FieldLayout) (c' : FixedByteCodec β q.2.size)
    (tail : PlacedCodecSpine βs) (recSpine : PlacedCodecSpine recTypes) :
    ∀ (b : Bool),
      (memInsertAux p c q c' tail recSpine b).placed =
        cond b (p :: q :: tail.placed) (q :: recSpine.placed)
  | true => rfl
  | false => rfl

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem placed_memInsert {α : Type} (p : Nat × FieldLayout) (c : FixedByteCodec α p.2.size) :
    ∀ {βs : List Type} (pc : PlacedCodecSpine βs),
      (pc.memInsert p c).placed = Anneal.ByteCodec.memInsert p pc.placed
  | _, .nil => rfl
  | _, .cons q c' tail => by
    change (memInsertAux p c q c' tail (tail.memInsert p c) (decide (memKey p ≤ memKey q))).placed =
      if memKey p ≤ memKey q then p :: q :: tail.placed
      else q :: Anneal.ByteCodec.memInsert p tail.placed
    rw [placed_memInsertAux, placed_memInsert p c tail]
    by_cases h : memKey p ≤ memKey q <;> simp [h]

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem placed_memSort :
    ∀ {αs : List Type} (pc : PlacedCodecSpine αs),
      pc.memSort.placed = Anneal.ByteCodec.memSort pc.placed
  | _, .nil => rfl
  | _, .cons p c tail => by
    change (tail.memSort.memInsert p c).placed =
      Anneal.ByteCodec.memInsert p (Anneal.ByteCodec.memSort tail.placed)
    rw [placed_memInsert p c tail.memSort, placed_memSort tail]

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem allFieldsSurjective_memInsertAux {α β : Type} {βs recTypes : List Type}
    (p : Nat × FieldLayout) (c : FixedByteCodec α p.2.size)
    (q : Nat × FieldLayout) (c' : FixedByteCodec β q.2.size)
    (tail : PlacedCodecSpine βs) (recSpine : PlacedCodecSpine recTypes)
    (hRec : recSpine.AllFieldsSurjective ↔ c.IsSurjectiveInitDecoder ∧ tail.AllFieldsSurjective) :
    ∀ (b : Bool),
      (memInsertAux p c q c' tail recSpine b).AllFieldsSurjective ↔
        c.IsSurjectiveInitDecoder ∧ c'.IsSurjectiveInitDecoder ∧ tail.AllFieldsSurjective
  | true => Iff.rfl
  | false => by
    dsimp only [memInsertAux, AllFieldsSurjective]
    rw [hRec]
    exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₁, h₃⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₁, h₃⟩⟩

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem allFieldsSurjective_memInsert {α : Type} (p : Nat × FieldLayout)
    (c : FixedByteCodec α p.2.size) :
    ∀ {βs : List Type} (pc : PlacedCodecSpine βs),
      (pc.memInsert p c).AllFieldsSurjective ↔ c.IsSurjectiveInitDecoder ∧ pc.AllFieldsSurjective
  | _, .nil => Iff.rfl
  | _, .cons q c' tail =>
    allFieldsSurjective_memInsertAux p c q c' tail (tail.memInsert p c)
      (allFieldsSurjective_memInsert p c tail) (decide (memKey p ≤ memKey q))

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem allFieldsSurjective_memSort :
    ∀ {αs : List Type} (pc : PlacedCodecSpine αs),
      pc.memSort.AllFieldsSurjective ↔ pc.AllFieldsSurjective
  | _, .nil => Iff.rfl
  | _, .cons p c tail => by
    change (tail.memSort.memInsert p c).AllFieldsSurjective ↔
      c.IsSurjectiveInitDecoder ∧ tail.AllFieldsSurjective
    rw [allFieldsSurjective_memInsert p c tail.memSort, allFieldsSurjective_memSort tail]

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem allFieldsZeroValid_memInsertAux {α β : Type} {βs recTypes : List Type}
    (p : Nat × FieldLayout) (c : FixedByteCodec α p.2.size)
    (q : Nat × FieldLayout) (c' : FixedByteCodec β q.2.size)
    (tail : PlacedCodecSpine βs) (recSpine : PlacedCodecSpine recTypes)
    (hRec : recSpine.AllFieldsZeroValid ↔ c.HasZeroValid ∧ tail.AllFieldsZeroValid) :
    ∀ (b : Bool),
      (memInsertAux p c q c' tail recSpine b).AllFieldsZeroValid ↔
        c.HasZeroValid ∧ c'.HasZeroValid ∧ tail.AllFieldsZeroValid
  | true => Iff.rfl
  | false => by
    dsimp only [memInsertAux, AllFieldsZeroValid]
    rw [hRec]
    exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₁, h₃⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₁, h₃⟩⟩

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem allFieldsZeroValid_memInsert {α : Type} (p : Nat × FieldLayout)
    (c : FixedByteCodec α p.2.size) :
    ∀ {βs : List Type} (pc : PlacedCodecSpine βs),
      (pc.memInsert p c).AllFieldsZeroValid ↔ c.HasZeroValid ∧ pc.AllFieldsZeroValid
  | _, .nil => Iff.rfl
  | _, .cons q c' tail =>
    allFieldsZeroValid_memInsertAux p c q c' tail (tail.memInsert p c)
      (allFieldsZeroValid_memInsert p c tail) (decide (memKey p ≤ memKey q))

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem allFieldsZeroValid_memSort :
    ∀ {αs : List Type} (pc : PlacedCodecSpine αs),
      pc.memSort.AllFieldsZeroValid ↔ pc.AllFieldsZeroValid
  | _, .nil => Iff.rfl
  | _, .cons p c tail => by
    change (tail.memSort.memInsert p c).AllFieldsZeroValid ↔
      c.HasZeroValid ∧ tail.AllFieldsZeroValid
    rw [allFieldsZeroValid_memInsert p c tail.memSort, allFieldsZeroValid_memSort tail]

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem allFieldsInit_memInsertAux {α β : Type} {βs recTypes : List Type}
    (p : Nat × FieldLayout) (c : FixedByteCodec α p.2.size)
    (q : Nat × FieldLayout) (c' : FixedByteCodec β q.2.size)
    (tail : PlacedCodecSpine βs) (recSpine : PlacedCodecSpine recTypes)
    (hRec : recSpine.AllFieldsInit ↔ c.IsInitCodec ∧ tail.AllFieldsInit) :
    ∀ (b : Bool),
      (memInsertAux p c q c' tail recSpine b).AllFieldsInit ↔
        c.IsInitCodec ∧ c'.IsInitCodec ∧ tail.AllFieldsInit
  | true => Iff.rfl
  | false => by
    dsimp only [memInsertAux, AllFieldsInit]
    rw [hRec]
    exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₁, h₃⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₁, h₃⟩⟩

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem allFieldsInit_memInsert {α : Type} (p : Nat × FieldLayout)
    (c : FixedByteCodec α p.2.size) :
    ∀ {βs : List Type} (pc : PlacedCodecSpine βs),
      (pc.memInsert p c).AllFieldsInit ↔ c.IsInitCodec ∧ pc.AllFieldsInit
  | _, .nil => Iff.rfl
  | _, .cons q c' tail =>
    allFieldsInit_memInsertAux p c q c' tail (tail.memInsert p c)
      (allFieldsInit_memInsert p c tail) (decide (memKey p ≤ memKey q))

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem allFieldsInit_memSort :
    ∀ {αs : List Type} (pc : PlacedCodecSpine αs),
      pc.memSort.AllFieldsInit ↔ pc.AllFieldsInit
  | _, .nil => Iff.rfl
  | _, .cons p c tail => by
    change (tail.memSort.memInsert p c).AllFieldsInit ↔
      c.IsInitCodec ∧ tail.AllFieldsInit
    rw [allFieldsInit_memInsert p c tail.memSort, allFieldsInit_memSort tail]

/-- Declaration-order byte windows of a placed codec spine: each field's offset and its encoding. -/
def windows : {αs : List Type} → PlacedCodecSpine αs → FieldTuple αs → List (Nat × List AbstractByte)
  | _, .nil, _ => []
  | _, .cons p c tail, (a, rest) => (p.1, c.encode a) :: tail.windows rest

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem windows_memInsertAux {α β : Type} {βs recTypes : List Type}
    (p : Nat × FieldLayout) (c : FixedByteCodec α p.2.size)
    (q : Nat × FieldLayout) (c' : FixedByteCodec β q.2.size)
    (tail : PlacedCodecSpine βs) (recSpine : PlacedCodecSpine recTypes)
    (recPerm : FieldPerm (α :: βs) recTypes) (a : α) (b : β) (t : FieldTuple βs)
    (hRec : (recSpine.windows (recPerm.apply (a, t))).Perm ((p.1, c.encode a) :: tail.windows t)) :
    ∀ (bb : Bool),
      ((memInsertAux p c q c' tail recSpine bb).windows
          ((memInsertPermAux α β βs recPerm bb).apply (a, b, t))).Perm
        ((p.1, c.encode a) :: (q.1, c'.encode b) :: tail.windows t)
  | true => by
    show ((PlacedCodecSpine.cons p c (.cons q c' tail)).windows
        ((FieldPerm.refl (α :: β :: βs)).apply (a, b, t))).Perm _
    rw [FieldPerm.refl_apply]
    exact List.Perm.refl _
  | false => by
    show ((q.1, c'.encode b) :: recSpine.windows (recPerm.apply (a, t))).Perm _
    exact (List.Perm.cons (q.1, c'.encode b) hRec).trans (List.Perm.swap _ _ _)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem windows_memInsert {α : Type} (p : Nat × FieldLayout) (c : FixedByteCodec α p.2.size) :
    ∀ {βs : List Type} (pc : PlacedCodecSpine βs) (a : α) (y : FieldTuple βs),
      ((pc.memInsert p c).windows ((pc.memInsertPerm α p).apply (a, y))).Perm
        ((p.1, c.encode a) :: pc.windows y)
  | _, .nil, _, _ => List.Perm.refl _
  | _, .cons q c' tail, a, (b, t) =>
    windows_memInsertAux p c q c' tail (tail.memInsert p c) (tail.memInsertPerm _ p) a b t
      (windows_memInsert p c tail a t) (decide (memKey p ≤ memKey q))

/--
**`memSortPerm` Routes Every Field Value With Its Placement**: the memory-order spine's windows,
evaluated on the permuted value `pc.memSortPerm.apply x`, are a permutation of the declaration-order
windows of `x` (each field's encoding travels with its own offset).

Kind: codec
Witness: universal
Assumes: S0
Subject: PlacedCodecSpine.memSortPerm
-/
theorem windows_memSort :
    ∀ {αs : List Type} (pc : PlacedCodecSpine αs) (x : FieldTuple αs),
      (pc.memSort.windows (pc.memSortPerm.apply x)).Perm (pc.windows x)
  | _, .nil, _ => List.Perm.refl _
  | _, .cons p c tail, (a, rest) => by
    show ((tail.memSort.memInsert p c).windows
        ((tail.memSort.memInsertPerm _ p).apply (a, tail.memSortPerm.apply rest))).Perm
      ((p.1, c.encode a) :: tail.windows rest)
    exact (windows_memInsert p c tail.memSort a (tail.memSortPerm.apply rest)).trans
      ((windows_memSort tail rest).cons _)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem windows_toSymbolicStructSpine_repad :
    ∀ {βs : List Type} (pc : PlacedCodecSpine βs) (pads : List Nat) (trail : Nat)
      (y : FieldTuple βs) (base : Nat),
      (pc.toSymbolicStructSpine.repad pads trail).fieldOffsets base = pc.placed.map Prod.fst →
      (pc.toSymbolicStructSpine.repad pads trail).windows y base = pc.windows y
  | _, .nil, _, _, _, _, _ => rfl
  | _, .cons p c tail, pads, trail, (a, rest), base, hOffs => by
    have hCons : base :: (tail.toSymbolicStructSpine.repad pads.tail trail).fieldOffsets
        (base + (p.2.size + pads.headD 0)) = p.1 :: tail.placed.map Prod.fst := hOffs
    injection hCons with hBase hTailOffs
    subst hBase
    show (p.1, c.encode a) :: (tail.toSymbolicStructSpine.repad pads.tail trail).windows rest
        (p.1 + (p.2.size + pads.headD 0)) = (p.1, c.encode a) :: tail.windows rest
    rw [windows_toSymbolicStructSpine_repad tail pads.tail trail rest _ hTailOffs]

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem windows_map_fst :
    ∀ {αs : List Type} (pc : PlacedCodecSpine αs) (x : FieldTuple αs),
      (pc.windows x).map Prod.fst = pc.placed.map Prod.fst
  | _, .nil, _ => rfl
  | _, .cons p _ tail, (_, rest) => by
    show p.1 :: (tail.windows rest).map Prod.fst = p.1 :: tail.placed.map Prod.fst
    rw [windows_map_fst tail rest]

/-- Computable inter-field padding gaps for a sequential placed-field list `l`. -/
def sequentialPads : List (Nat × FieldLayout) → List Nat
  | [] => []
  | p :: ps => ((ps.map Prod.fst).headD (p.1 + p.2.size) - (p.1 + p.2.size)) :: sequentialPads ps

/-- Computable trailing padding after the last field of `l` (starting from `base`) up to `total`. -/
def sequentialTrail : Nat → List (Nat × FieldLayout) → Nat → Nat
  | base, [], total => total - base
  | _, p :: ps, total => sequentialTrail (p.1 + p.2.size) ps total

/--
**Computable Sequential Re-Padding**: for any placed-field list `l` whose layouts and offsets form a
`SequentialFieldPlacement base (l.map Prod.snd) (l.map Prod.fst) total` and any spine `s` with
matching widths, the computable `sequentialPads l` and `sequentialTrail base l total` make
`s.repad (sequentialPads l) (sequentialTrail base l total)` place every field at `l.map Prod.fst`
with total width `total` (no existential quantifier needed).

Kind: refinement
Witness: universal
Assumes: S0
Subject: SymbolicStructSpine.repad
-/
theorem repad_sequentialPads_spec :
    ∀ (l : List (Nat × FieldLayout)) (base total : Nat),
      SequentialFieldPlacement base (l.map Prod.snd) (l.map Prod.fst) total →
      ∀ {βs : List Type} {W : Nat} (s : SymbolicStructSpine βs W),
        s.widths = l.map (fun p => p.2.size) →
        (s.repad (sequentialPads l) (sequentialTrail base l total)).fieldOffsets
            ((l.map Prod.fst).headD base) = l.map Prod.fst ∧
        (l.map Prod.fst).headD base +
          s.repadWidth (sequentialPads l) (sequentialTrail base l total) = total
  | [], base, total, .nil hLe, _, _, .nil _, _ => by
    refine ⟨rfl, ?_⟩
    show base + (total - base) = total
    omega
  | [], _, _, .nil _, _, _, .cons _ _ _, hW => nomatch hW
  | p :: ps, base, total, .cons hBase hTail, _, _, .nil _, hW => nomatch hW
  | p :: ps, base, total, .cons hBase hTail, _, _,
      @SymbolicStructSpine.cons _ _ n _ c postPad tail, hW => by
    injection hW with hN hTailW
    subst hN
    obtain ⟨hOffs, hTot⟩ := repad_sequentialPads_spec ps (p.1 + p.2.size) total hTail tail hTailW
    have hLe := hTail.base_le_headD
    refine ⟨?_, ?_⟩
    · show p.1 :: (tail.repad (sequentialPads ps)
          (sequentialTrail (p.1 + p.2.size) ps total)).fieldOffsets
            (p.1 + (p.2.size + ((ps.map Prod.fst).headD (p.1 + p.2.size) - (p.1 + p.2.size)))) =
        p.1 :: ps.map Prod.fst
      rw [show p.1 + (p.2.size + ((ps.map Prod.fst).headD (p.1 + p.2.size) - (p.1 + p.2.size))) =
        (ps.map Prod.fst).headD (p.1 + p.2.size) by omega, hOffs]
    · show p.1 + ((p.2.size + ((ps.map Prod.fst).headD (p.1 + p.2.size) - (p.1 + p.2.size))) +
          tail.repadWidth (sequentialPads ps) (sequentialTrail (p.1 + p.2.size) ps total)) = total
      omega

/-- Computable leading padding of `pc.memSort`. -/
def realizedLead {αs : List Type} (pc : PlacedCodecSpine αs) : Nat :=
  (pc.memSort.placed.map Prod.fst).headD 0

/-- Computable inter-field padding list of `pc.memSort`. -/
def realizedPads {αs : List Type} (pc : PlacedCodecSpine αs) : List Nat :=
  sequentialPads pc.memSort.placed

/-- Computable trailing padding of `pc.memSort` within `totalSize`. -/
def realizedTrail {αs : List Type} (pc : PlacedCodecSpine αs) (totalSize : Nat) : Nat :=
  sequentialTrail 0 pc.memSort.placed totalSize

/-- Computable re-padded memory-order spine of `pc` within `totalSize`. -/
def realizedSpine {αs : List Type} (pc : PlacedCodecSpine αs) (totalSize : Nat) :
    SymbolicStructSpine pc.memSortTypes
      (pc.memSort.toSymbolicStructSpine.repadWidth pc.realizedPads (pc.realizedTrail totalSize)) :=
  pc.memSort.toSymbolicStructSpine.repad pc.realizedPads (pc.realizedTrail totalSize)

/-- Computable total byte width of `pc.realizedCodec totalSize`. -/
def realizedWidth {αs : List Type} (pc : PlacedCodecSpine αs) (totalSize : Nat) : Nat :=
  pc.realizedLead +
    pc.memSort.toSymbolicStructSpine.repadWidth pc.realizedPads (pc.realizedTrail totalSize)

/--
**Computable Realized $k$-Field Struct Codec**: given any declaration-order `pc : PlacedCodecSpine αs`
and `totalSize : Nat`, `pc.realizedCodec totalSize` constructively sorts `pc` into memory order,
computes the exact leading, inter-field, and trailing padding (`realizedLead`, `realizedPads`,
`realizedTrail`), and wraps the re-padded spine in `pc.memSortPerm` back to declaration order `FieldTuple αs`
with **no existential quantifiers**.
-/
def realizedCodec {αs : List Type} (pc : PlacedCodecSpine αs) (totalSize : Nat) :
    FixedByteCodec (FieldTuple αs) (pc.realizedWidth totalSize) :=
  laidOutStructSymbolicPadPerm pc.realizedLead pc.memSortPerm (pc.realizedSpine totalSize)

/--
Kind: codec
Witness: universal
Assumes: S0
Subject: PlacedCodecSpine.realizedCodec
-/
theorem realizedCodec_isExactWidth {αs : List Type} (pc : PlacedCodecSpine αs) (totalSize : Nat) :
    (pc.realizedCodec totalSize).IsExactWidth :=
  laidOutStructSymbolicPadPerm_isExactWidth pc.realizedLead pc.memSortPerm (pc.realizedSpine totalSize)

/--
Universal `IsSurjectiveInitDecoder` (`FromBytes`) for `pc.realizedCodec totalSize` across all
leading/inter-field/trailing padding configurations and memory-order permutations.

Kind: codec
Witness: universal
Assumes: S0
Subject: PlacedCodecSpine.realizedCodec
-/
theorem realizedCodec_isSurjectiveInitDecoder {αs : List Type}
    (pc : PlacedCodecSpine αs) (totalSize : Nat) (hSurj : pc.AllFieldsSurjective) :
    (pc.realizedCodec totalSize).IsSurjectiveInitDecoder := by
  have hSurjRaw : pc.memSort.toSymbolicStructSpine.AllFieldsSurjective :=
    (allFieldsSurjective_toSymbolicStructSpine pc.memSort).mpr
      ((allFieldsSurjective_memSort pc).mpr hSurj)
  exact laidOutStructSymbolicPadPerm_isSurjectiveInitDecoder
    pc.realizedLead pc.memSortPerm (pc.realizedSpine totalSize)
    (pc.memSort.toSymbolicStructSpine.allFieldsSurjective_repad
      pc.realizedPads (pc.realizedTrail totalSize) hSurjRaw)

/--
Universal `HasZeroValid` (`FromZeros`) for `pc.realizedCodec totalSize`.

Kind: codec
Witness: universal
Assumes: S0
Subject: PlacedCodecSpine.realizedCodec
-/
theorem realizedCodec_hasZeroValid {αs : List Type}
    (pc : PlacedCodecSpine αs) (totalSize : Nat) (hZero : pc.AllFieldsZeroValid) :
    (pc.realizedCodec totalSize).HasZeroValid := by
  have hZeroRaw : pc.memSort.toSymbolicStructSpine.AllFieldsZeroValid :=
    (allFieldsZeroValid_toSymbolicStructSpine pc.memSort).mpr
      ((allFieldsZeroValid_memSort pc).mpr hZero)
  exact laidOutStructSymbolicPadPerm_hasZeroValid
    pc.realizedLead pc.memSortPerm (pc.realizedSpine totalSize)
    (pc.memSort.toSymbolicStructSpine.allFieldsZeroValid_repad
      pc.realizedPads (pc.realizedTrail totalSize) hZeroRaw)

/--
Tight-world `IsInitCodec` (`IntoBytes`) for `pc.realizedCodec totalSize` when total padding is `0`.

Kind: codec
Witness: universal
Assumes: S0
Subject: PlacedCodecSpine.realizedCodec
-/
theorem realizedCodec_isInitCodec_of_zero_pad {αs : List Type}
    (pc : PlacedCodecSpine αs) (totalSize : Nat)
    (hPad0 : pc.realizedLead + (pc.realizedSpine totalSize).totalPadBytes = 0)
    (hInit : pc.AllFieldsInit) :
    (pc.realizedCodec totalSize).IsInitCodec := by
  have hLead0 : pc.realizedLead = 0 := by omega
  have hSpine0 : (pc.realizedSpine totalSize).totalPadBytes = 0 := by omega
  have hInitRaw : pc.memSort.toSymbolicStructSpine.AllFieldsInit :=
    (allFieldsInit_toSymbolicStructSpine pc.memSort).mpr
      ((allFieldsInit_memSort pc).mpr hInit)
  exact FixedByteCodec.mapEquiv_isInitCodec _
    pc.memSortPerm.unapply pc.memSortPerm.apply
    pc.memSortPerm.apply_unapply pc.memSortPerm.unapply_apply
    (FixedByteCodec.padLeft_isInitCodec_of_eq_zero hLead0
      (laidOutStructSymbolicPad_isInitCodec_of_zero_pad _ hSpine0
        ((pc.memSort.toSymbolicStructSpine.allFieldsInit_repad_iff
          pc.realizedPads (pc.realizedTrail totalSize)).mpr hInitRaw)))

/--
Padded-world `.uninit` emission for `pc.realizedCodec totalSize` when total padding is positive.

Kind: divergence
Witness: negative
Assumes: S0
Subject: PlacedCodecSpine.realizedCodec
-/
theorem realizedCodec_encode_uninit_of_pad_pos {αs : List Type}
    (pc : PlacedCodecSpine αs) (totalSize : Nat)
    (hPos : 0 < pc.realizedLead + (pc.realizedSpine totalSize).totalPadBytes)
    (x : FieldTuple αs) :
    allBytesInitialized ((pc.realizedCodec totalSize).encode x) = false :=
  laidOutStructSymbolicPadPerm_encode_uninit_of_pad_pos
    pc.realizedLead pc.memSortPerm (pc.realizedSpine totalSize) hPos x

/--
Exact `IsInitCodec` characterization for `pc.realizedCodec totalSize` over any inhabited `FieldTuple αs`.

Kind: codec
Witness: universal
Assumes: S0
Subject: PlacedCodecSpine.realizedCodec
-/
theorem realizedCodec_isInitCodec_iff {αs : List Type}
    (pc : PlacedCodecSpine αs) (totalSize : Nat) (x₀ : FieldTuple αs) :
    (pc.realizedCodec totalSize).IsInitCodec ↔
      pc.realizedLead = 0 ∧ (pc.realizedSpine totalSize).totalPadBytes = 0 ∧ pc.AllFieldsInit := by
  unfold realizedCodec realizedWidth
  rw [laidOutStructSymbolicPadPerm_isInitCodec_iff _ _ _ x₀,
      realizedSpine, SymbolicStructSpine.allFieldsInit_repad_iff,
      allFieldsInit_toSymbolicStructSpine, allFieldsInit_memSort]

/--
Negative `IsInitCodec` theorem for `pc.realizedCodec totalSize` when total padding is positive.

Kind: divergence
Witness: negative
Assumes: S0
Subject: PlacedCodecSpine.realizedCodec
-/
theorem realizedCodec_not_isInitCodec_of_pad_pos {αs : List Type}
    (pc : PlacedCodecSpine αs) (totalSize : Nat)
    (hPos : 0 < pc.realizedLead + (pc.realizedSpine totalSize).totalPadBytes)
    (x₀ : FieldTuple αs) :
    ¬ (pc.realizedCodec totalSize).IsInitCodec := by
  intro hInit
  have hTrue := hInit x₀
  rw [pc.realizedCodec_encode_uninit_of_pad_pos totalSize hPos x₀] at hTrue
  nomatch hTrue

end PlacedCodecSpine

/-- Declaration-order placed codecs of `struct S { a: u8, b: [u8; 4], c: () }` in a reordered
`#[repr(Rust)]` layout world (`b @ 0`, `a @ 4`, `c @ 5`, size 8). -/
def demoS3Placed : PlacedCodecSpine [UInt8, Vector UInt8 4, Unit] :=
  .cons (4, ⟨1, 1⟩) FixedByteCodec.u8
    (.cons (0, ⟨4, 4⟩) (FixedByteCodec.array 4 FixedByteCodec.u8)
      (.cons (5, ⟨0, 1⟩) FixedByteCodec.unit .nil))

/--
`PlacedCodecSpine.memSort` reorders the declaration-order types `[UInt8, Vector UInt8 4, Unit]` into
the world's memory order `[Vector UInt8 4, UInt8, Unit]` (kernel-checked by `rfl`).

Kind: helper
Witness: universal
Assumes: S0
-/
theorem demoS3Placed_memSortTypes :
    demoS3Placed.memSortTypes = [Vector UInt8 4, UInt8, Unit] ∧
    demoS3Placed.memSort.placed = [(0, ⟨4, 4⟩), (4, ⟨1, 1⟩), (5, ⟨0, 1⟩)] :=
  ⟨rfl, rfl⟩

/-! ## 8. Real `LayoutTable` (`FieldsShape.arbitrary`) Bridge (`MirValueCodec.ofPlacedCodecSpine` & Concrete 2/3-Field Instances)

`MirValueCodec.ofPlacedCodecSpine` derives Trusted's tuple semantics from the `LayoutTable` entry:
1. **Byte windows** (`writeWindows`, `WindowImage`): Trusted's `encodeFieldsAtOffsetsWith` writes each
   declaration field's encoding at its offset over `.uninit` bytes, and pairwise-disjoint in-bounds
   window writes commute (`writeWindows_eq_of_perm`), so the memory-order realized codec agrees with
   the declaration-order writes (`PlacedCodecSpine.writeWindows_realizedCodec_encode`).
2. **Window decodes** (`PlacedCodecSpine.decodeAt`): both Trusted's `decodeFieldsAtOffsetsWith` and the
   realized codec decode each field from its own window and ignore padding bytes
   (`PlacedCodecSpine.realizedCodec_decode_eq_decodeAt`).
3. **Per-field bridges** (`TupleFieldCodec`) at `tupleFieldFuel`, the fuel at which Trusted recurses into
   tuple fields, with ready-made instances for `uN` and `()` fields.
-/

namespace FixedByteCodec

/--
Cast the byte-width index of a `FixedByteCodec α m` along a propositional equality `h : m = n`.
Preserves `encode` and `decode` definitionally (`rfl`).
-/
def castWidth {α : Type} {m n : Nat} (c : FixedByteCodec α m) (h : m = n) : FixedByteCodec α n :=
  ofRoundTrip c.encode c.decode (fun x => h ▸ c.encode_length x) c.decode_encode

@[simp]
theorem castWidth_encode {α : Type} {m n : Nat} (c : FixedByteCodec α m) (h : m = n) (x : α) :
    (c.castWidth h).encode x = c.encode x := rfl

@[simp]
theorem castWidth_decode {α : Type} {m n : Nat} (c : FixedByteCodec α m) (h : m = n)
    (bs : List AbstractByte) :
    (c.castWidth h).decode bs = c.decode bs := rfl

theorem castWidth_isExactWidth {α : Type} {m n : Nat} (c : FixedByteCodec α m) (h : m = n)
    (hEx : c.IsExactWidth) : (c.castWidth h).IsExactWidth := by
  subst h
  exact hEx

theorem castWidth_isInitCodec {α : Type} {m n : Nat} (c : FixedByteCodec α m) (h : m = n)
    (hInit : c.IsInitCodec) : (c.castWidth h).IsInitCodec :=
  hInit

theorem castWidth_isSurjectiveInitDecoder {α : Type} {m n : Nat} (c : FixedByteCodec α m) (h : m = n)
    (hSurj : c.IsSurjectiveInitDecoder) : (c.castWidth h).IsSurjectiveInitDecoder := by
  subst h
  exact hSurj

theorem castWidth_hasZeroValid {α : Type} {m n : Nat} (c : FixedByteCodec α m) (h : m = n)
    (hZero : c.HasZeroValid) : (c.castWidth h).HasZeroValid := by
  subst h
  exact hZero

end FixedByteCodec

/-! ### Byte-Window Images (`InWindow`, `WindowImage`, `writeWindows`) -/

/-- Byte index `j` lies inside the byte window `w = (offset, bytes)`. -/
def InWindow (j : Nat) (w : Nat × List AbstractByte) : Prop :=
  w.1 ≤ j ∧ j < w.1 + w.2.length

instance (j : Nat) (w : Nat × List AbstractByte) : Decidable (InWindow j w) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Two byte windows occupy disjoint byte ranges. -/
def WindowsDisjoint (w₁ w₂ : Nat × List AbstractByte) : Prop :=
  w₁.1 + w₁.2.length ≤ w₂.1 ∨ w₂.1 + w₂.2.length ≤ w₁.1

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem WindowsDisjoint.symm {w₁ w₂ : Nat × List AbstractByte} (h : WindowsDisjoint w₁ w₂) :
    WindowsDisjoint w₂ w₁ :=
  h.elim Or.inr Or.inl

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem WindowsDisjoint.not_inWindow {w₁ w₂ : Nat × List AbstractByte} (h : WindowsDisjoint w₁ w₂)
    {j : Nat} (h₁ : InWindow j w₁) : ¬ InWindow j w₂ := by
  intro h₂
  unfold WindowsDisjoint at h
  unfold InWindow at h₁ h₂
  omega

/--
`out` is the background buffer `buf` with every byte window of `ws` written over it: bytes inside a
window are that window's bytes, bytes outside every window are `buf`'s bytes, and the length is
unchanged.
-/
structure WindowImage (buf : List AbstractByte) (ws : List (Nat × List AbstractByte))
    (out : List AbstractByte) : Prop where
  length_eq : out.length = buf.length
  inside : ∀ w ∈ ws, ∀ j, InWindow j w → out[j]? = w.2[j - w.1]?
  outside : ∀ j, (∀ w ∈ ws, ¬ InWindow j w) → out[j]? = buf[j]?

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem WindowImage.perm {buf out : List AbstractByte} {ws ws' : List (Nat × List AbstractByte)}
    (h : WindowImage buf ws out) (hp : ws.Perm ws') : WindowImage buf ws' out where
  length_eq := h.length_eq
  inside := fun w hw => h.inside w (hp.mem_iff.mpr hw)
  outside := fun j hj => h.outside j (fun w hw => hj w (hp.mem_iff.mp hw))

/--
A window image is unique: two buffers that both realize the same background and window list are
equal (every byte is either inside some window or outside all of them).

Kind: helper
Witness: universal
Assumes: S0
-/
theorem WindowImage.unique {buf out₁ out₂ : List AbstractByte} {ws : List (Nat × List AbstractByte)}
    (h₁ : WindowImage buf ws out₁) (h₂ : WindowImage buf ws out₂) : out₁ = out₂ := by
  apply List.ext_getElem?
  intro j
  by_cases hIn : ∃ w ∈ ws, InWindow j w
  · obtain ⟨w, hw, hj⟩ := hIn
    rw [h₁.inside w hw j hj, h₂.inside w hw j hj]
  · have hOut : ∀ w ∈ ws, ¬ InWindow j w := fun w hw hj => hIn ⟨w, hw, hj⟩
    rw [h₁.outside j hOut, h₂.outside j hOut]

/--
Closed form of Trusted's `writeAbstractBytesAt` on an in-bounds window.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem writeAbstractBytesAt_eq_take_append_drop :
    ∀ (buf : List AbstractByte) (o : Nat) (p : List AbstractByte),
      o + p.length ≤ buf.length →
      writeAbstractBytesAt buf o p = some (buf.take o ++ p ++ buf.drop (o + p.length))
  | buf, o, [], _ => by
    have hNil : writeAbstractBytesAt buf o [] = some buf := by
      cases buf <;> cases o <;> rfl
    rw [hNil, List.length_nil, List.append_nil, Nat.add_zero, List.take_append_drop]
  | [], o, w :: ws, h => by
    exact absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | b :: bufRest, 0, w :: ws, h => by
    have hRest : 0 + ws.length ≤ bufRest.length := by
      simp only [List.length_cons] at h
      omega
    have ih := writeAbstractBytesAt_eq_take_append_drop bufRest 0 ws hRest
    show (match writeAbstractBytesAt bufRest 0 ws with
      | some tail' => some (w :: tail')
      | none => none) = _
    rw [ih]
    show some (w :: (bufRest.take 0 ++ ws ++ bufRest.drop (0 + ws.length))) =
      some ((b :: bufRest).take 0 ++ (w :: ws) ++ (b :: bufRest).drop (0 + (ws.length + 1)))
    rw [Nat.zero_add, Nat.zero_add]
    rfl
  | b :: bufRest, o + 1, w :: ws, h => by
    have hRest : o + (w :: ws).length ≤ bufRest.length := by
      simp only [List.length_cons] at h ⊢
      omega
    have ih := writeAbstractBytesAt_eq_take_append_drop bufRest o (w :: ws) hRest
    show (match writeAbstractBytesAt bufRest o (w :: ws) with
      | some tail' => some (b :: tail')
      | none => none) = _
    rw [ih]
    have hIdx : o + 1 + (w :: ws).length = (o + (w :: ws).length) + 1 := by omega
    rw [hIdx]
    rfl

/--
Pointwise characterization of an in-bounds `writeAbstractBytesAt`.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem writeAbstractBytesAt_windowImage (buf : List AbstractByte) (o : Nat) (p : List AbstractByte)
    (h : o + p.length ≤ buf.length) :
    ∃ out, writeAbstractBytesAt buf o p = some out ∧ WindowImage buf [(o, p)] out := by
  refine ⟨_, writeAbstractBytesAt_eq_take_append_drop buf o p h, ?_, ?_, ?_⟩
  · rw [List.length_append, List.length_append, List.length_take, List.length_drop]
    rw [Nat.min_eq_left (by omega)]
    omega
  · intro w hw j hj
    have hwEq : w = (o, p) := List.mem_singleton.mp hw
    rw [hwEq] at hj ⊢
    obtain ⟨hj₁, hj₂⟩ := hj
    dsimp only at hj₁ hj₂ ⊢
    have hTakeLen : (buf.take o).length = o := by
      rw [List.length_take]
      exact Nat.min_eq_left (by omega)
    rw [List.append_assoc, List.getElem?_append_right (by omega), hTakeLen,
      List.getElem?_append_left (by omega)]
  · intro j hj
    have hNot : ¬ InWindow j (o, p) := hj (o, p) (List.mem_singleton_self _)
    have hTakeLen : (buf.take o).length = o := by
      rw [List.length_take]
      exact Nat.min_eq_left (by omega)
    by_cases hj₁ : j < o
    · clear hNot
      rw [List.append_assoc, List.getElem?_append_left (by omega), List.getElem?_take]
      exact ite_eq_left_iff.mpr (fun hNot' => absurd hj₁ hNot')
    · have hoj : o ≤ j := Nat.le_of_not_lt hj₁
      have hj₂ : o + p.length ≤ j := Nat.le_of_not_lt (fun hlt => hNot ⟨hoj, hlt⟩)
      clear hNot hj hj₁
      rw [List.getElem?_append_right (by rw [List.length_append, hTakeLen]; omega),
        List.length_append, hTakeLen, List.getElem?_drop]
      congr 1
      omega

/-- Write every byte window of `ws` into `buf`, left to right (Trusted's tuple-field writes). -/
def writeWindows : List AbstractByte → List (Nat × List AbstractByte) → Option (List AbstractByte)
  | buf, [] => some buf
  | buf, w :: ws =>
    match writeAbstractBytesAt buf w.1 w.2 with
    | some buf' => writeWindows buf' ws
    | none => none

/--
Writing pairwise-disjoint in-bounds windows succeeds and produces their window image.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem writeWindows_windowImage :
    ∀ (ws : List (Nat × List AbstractByte)) (buf : List AbstractByte),
      (∀ w ∈ ws, w.1 + w.2.length ≤ buf.length) → ws.Pairwise WindowsDisjoint →
      ∃ out, writeWindows buf ws = some out ∧ WindowImage buf ws out
  | [], buf, _, _ =>
    ⟨buf, rfl, rfl, (fun _ hw => nomatch hw), (fun _ _ => rfl)⟩
  | w :: ws, buf, hIn, hDisj => by
    obtain ⟨buf', hW, hImg'⟩ := writeAbstractBytesAt_windowImage buf w.1 w.2
      (hIn w (List.mem_cons_self ..))
    have hLen' := hImg'.length_eq
    have hDisj' := List.pairwise_cons.mp hDisj
    obtain ⟨out, hOut, hImg⟩ := writeWindows_windowImage ws buf'
      (fun v hv => by rw [hLen']; exact hIn v (List.mem_cons_of_mem _ hv)) hDisj'.2
    refine ⟨out, ?_, hImg.length_eq.trans hLen', ?_, ?_⟩
    · show (match writeAbstractBytesAt buf w.1 w.2 with
        | some b => writeWindows b ws
        | none => none) = some out
      rw [hW]
      exact hOut
    · intro v hv j hj
      rcases List.mem_cons.mp hv with hvw | hv
      · rw [hvw] at hj ⊢
        have hNot : ∀ u ∈ ws, ¬ InWindow j u :=
          fun u hu => (hDisj'.1 u hu).not_inWindow hj
        rw [hImg.outside j hNot, hImg'.inside (w.1, w.2) (List.mem_singleton_self _) j hj]
      · exact hImg.inside v hv j hj
    · intro j hj
      rw [hImg.outside j (fun u hu => hj u (List.mem_cons_of_mem _ hu)),
        hImg'.outside j (fun u hu => by
          have huw : u = (w.1, w.2) := List.mem_singleton.mp hu
          rw [huw]
          exact hj w (List.mem_cons_self ..))]

/--
`writeWindows` is independent of the order of pairwise-disjoint in-bounds windows.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem writeWindows_eq_of_perm {buf : List AbstractByte} {ws₁ ws₂ : List (Nat × List AbstractByte)}
    (hp : ws₁.Perm ws₂) (hIn : ∀ w ∈ ws₁, w.1 + w.2.length ≤ buf.length)
    (hDisj : ws₁.Pairwise WindowsDisjoint) :
    writeWindows buf ws₁ = writeWindows buf ws₂ := by
  obtain ⟨o₁, h₁, i₁⟩ := writeWindows_windowImage ws₁ buf hIn hDisj
  obtain ⟨o₂, h₂, i₂⟩ := writeWindows_windowImage ws₂ buf (fun w hw => hIn w (hp.mem_iff.mpr hw))
    ((hp.pairwise_iff (fun h => WindowsDisjoint.symm h)).mp hDisj)
  rw [h₁, h₂, (i₁.perm hp).unique i₂]

/--
A spine's encoding is obtained by writing its field windows over uninitialized bytes.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem SymbolicStructSpine.writeWindows_encode :
    ∀ {βs : List Type} {W : Nat} (s : SymbolicStructSpine βs W) (y : FieldTuple βs)
      (pre post : List AbstractByte),
      writeWindows (pre ++ replicateUninitBytes W ++ post) (s.windows y pre.length) =
        some (pre ++ (laidOutStructSymbolicPad s).encode y ++ post)
  | _, _, .nil _, _, _, _ => rfl
  | _, _, @SymbolicStructSpine.cons _ _ n restW c postPad tail, (a, rest), pre, post => by
    have hSplit : pre ++ replicateUninitBytes ((n + postPad) + restW) ++ post =
        pre ++ replicateUninitBytes n ++
          (replicateUninitBytes postPad ++ replicateUninitBytes restW ++ post) := by
      rw [MirValueCodec.replicateUninitBytes_add_eq, MirValueCodec.replicateUninitBytes_add_eq]
      simp only [List.append_assoc]
    have hWrite := MirValueCodec.writeAbstractBytesAt_offset_replicateUninit pre (c.encode a)
      (replicateUninitBytes postPad ++ replicateUninitBytes restW ++ post) rfl (c.encode_length a)
    have hPre : (pre ++ c.encode a ++ replicateUninitBytes postPad).length =
        pre.length + (n + postPad) := by
      rw [List.length_append, List.length_append, c.encode_length, length_replicateUninitBytes]
      omega
    have ih := SymbolicStructSpine.writeWindows_encode tail rest
      (pre ++ c.encode a ++ replicateUninitBytes postPad) post
    rw [hPre] at ih
    show (match writeAbstractBytesAt (pre ++ replicateUninitBytes ((n + postPad) + restW) ++ post)
        pre.length (c.encode a) with
      | some b => writeWindows b (tail.windows rest (pre.length + (n + postPad)))
      | none => none) = _
    rw [hSplit, hWrite]
    dsimp only
    have hBuf : pre ++ c.encode a ++
        (replicateUninitBytes postPad ++ replicateUninitBytes restW ++ post) =
        pre ++ c.encode a ++ replicateUninitBytes postPad ++ replicateUninitBytes restW ++ post := by
      simp only [List.append_assoc]
    rw [hBuf, ih]
    show some (pre ++ c.encode a ++ replicateUninitBytes postPad ++
        (laidOutStructSymbolicPad tail).encode rest ++ post) =
      some (pre ++ ((c.encode a ++ replicateUninitBytes postPad) ++
        (laidOutStructSymbolicPad tail).encode rest) ++ post)
    simp only [List.append_assoc]

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem SequentialFieldPlacement.base_le_total {base total : Nat} {fls : List FieldLayout}
    {offs : List Nat} (h : SequentialFieldPlacement base fls offs total) : base ≤ total := by
  induction h with
  | nil hLe => exact hLe
  | cons hBase _ ih => omega

namespace PlacedCodecSpine

/--
The byte windows of a sequentially placed spine are pairwise disjoint and lie within
`[base, total)`.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem windows_disjoint_of_sequential :
    ∀ {βs : List Type} (q : PlacedCodecSpine βs) (base total : Nat) (y : FieldTuple βs),
      SequentialFieldPlacement base (q.placed.map Prod.snd) (q.placed.map Prod.fst) total →
      (q.windows y).Pairwise WindowsDisjoint ∧
        ∀ w ∈ q.windows y, base ≤ w.1 ∧ w.1 + w.2.length ≤ total
  | _, .nil, _, _, _, _ => ⟨List.Pairwise.nil, fun _ hw => nomatch hw⟩
  | _, .cons p c tail, base, total, (a, rest), hSeq => by
    have hSeq' : SequentialFieldPlacement base (p.2 :: tail.placed.map Prod.snd)
        (p.1 :: tail.placed.map Prod.fst) total := hSeq
    cases hSeq' with
    | cons hBase hTail =>
      obtain ⟨hPw, hBd⟩ := windows_disjoint_of_sequential tail (p.1 + p.2.size) total rest hTail
      have hTot := hTail.base_le_total
      refine ⟨List.pairwise_cons.mpr ⟨fun w hw => ?_, hPw⟩, fun w hw => ?_⟩
      · left
        show p.1 + (c.encode a).length ≤ w.1
        rw [c.encode_length]
        exact (hBd w hw).1
      · rcases List.mem_cons.mp hw with hw | hw
        · rw [hw]
          show base ≤ p.1 ∧ p.1 + (c.encode a).length ≤ total
          rw [c.encode_length]
          exact ⟨hBase, hTot⟩
        · have hW := hBd w hw
          exact ⟨Nat.le_trans (Nat.le_trans hBase (Nat.le_add_right _ _)) hW.1, hW.2⟩

/--
Every placed field of a sequentially placed spine lies within `[base, total)`.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem placed_in_bounds_of_sequential :
    ∀ (l : List (Nat × FieldLayout)) (base total : Nat),
      SequentialFieldPlacement base (l.map Prod.snd) (l.map Prod.fst) total →
      ∀ p ∈ l, base ≤ p.1 ∧ p.1 + p.2.size ≤ total
  | [], _, _, _, _, hp => nomatch hp
  | q :: qs, base, total, hSeq, p, hp => by
    have hSeq' : SequentialFieldPlacement base (q.2 :: qs.map Prod.snd) (q.1 :: qs.map Prod.fst)
        total := hSeq
    cases hSeq' with
    | cons hBase hTail =>
      rcases List.mem_cons.mp hp with hp | hp
      · rw [hp]
        exact ⟨hBase, hTail.base_le_total⟩
      · have h := placed_in_bounds_of_sequential qs (q.1 + q.2.size) total hTail p hp
        exact ⟨Nat.le_trans (Nat.le_trans hBase (Nat.le_add_right _ _)) h.1, h.2⟩

/-- Map every declaration field `(placement, codec, value)` of a placed codec spine to a `β`. -/
def fieldMap {β : Type}
    (F : {α : Type} → (p : Nat × FieldLayout) → FixedByteCodec α p.2.size → α → β) :
    {αs : List Type} → PlacedCodecSpine αs → FieldTuple αs → List β
  | _, .nil, _ => []
  | _, .cons p c tail, (a, rest) => F p c a :: fieldMap F tail rest

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem fieldMap_memInsertAux {β : Type}
    (F : {α : Type} → (p : Nat × FieldLayout) → FixedByteCodec α p.2.size → α → β)
    {α γ : Type} {γs recTypes : List Type}
    (p : Nat × FieldLayout) (c : FixedByteCodec α p.2.size)
    (q : Nat × FieldLayout) (c' : FixedByteCodec γ q.2.size)
    (tail : PlacedCodecSpine γs) (recSpine : PlacedCodecSpine recTypes)
    (recPerm : FieldPerm (α :: γs) recTypes) (a : α) (b : γ) (t : FieldTuple γs)
    (hRec : (recSpine.fieldMap F (recPerm.apply (a, t))).Perm (F p c a :: tail.fieldMap F t)) :
    ∀ (bb : Bool),
      ((memInsertAux p c q c' tail recSpine bb).fieldMap F
          ((memInsertPermAux α γ γs recPerm bb).apply (a, b, t))).Perm
        (F p c a :: F q c' b :: tail.fieldMap F t)
  | true => by
    show ((PlacedCodecSpine.cons p c (.cons q c' tail)).fieldMap F
        ((FieldPerm.refl (α :: γ :: γs)).apply (a, b, t))).Perm _
    rw [FieldPerm.refl_apply]
    exact List.Perm.refl _
  | false => by
    show (F q c' b :: recSpine.fieldMap F (recPerm.apply (a, t))).Perm _
    exact (List.Perm.cons _ hRec).trans (List.Perm.swap _ _ _)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem fieldMap_memInsert {β : Type}
    (F : {α : Type} → (p : Nat × FieldLayout) → FixedByteCodec α p.2.size → α → β)
    {α : Type} (p : Nat × FieldLayout) (c : FixedByteCodec α p.2.size) :
    ∀ {γs : List Type} (pc : PlacedCodecSpine γs) (a : α) (y : FieldTuple γs),
      ((pc.memInsert p c).fieldMap F ((pc.memInsertPerm α p).apply (a, y))).Perm
        (F p c a :: pc.fieldMap F y)
  | _, .nil, _, _ => List.Perm.refl _
  | _, .cons q c' tail, a, (b, t) =>
    fieldMap_memInsertAux F p c q c' tail (tail.memInsert p c) (tail.memInsertPerm _ p) a b t
      (fieldMap_memInsert F p c tail a t) (decide (memKey p ≤ memKey q))

/--
**`memSortPerm` Routes Every Per-Field Fact With Its Placement**: for any per-field functional `F`,
the memory-order spine's `fieldMap` on `pc.memSortPerm.apply x` is a permutation of the
declaration-order `fieldMap` on `x` (generalizing `windows_memSort`).

Kind: codec
Witness: universal
Assumes: S0
Subject: PlacedCodecSpine.memSortPerm
-/
theorem fieldMap_memSort {β : Type}
    (F : {α : Type} → (p : Nat × FieldLayout) → FixedByteCodec α p.2.size → α → β) :
    ∀ {αs : List Type} (pc : PlacedCodecSpine αs) (x : FieldTuple αs),
      (pc.memSort.fieldMap F (pc.memSortPerm.apply x)).Perm (pc.fieldMap F x)
  | _, .nil, _ => List.Perm.refl _
  | _, .cons p c tail, (a, rest) => by
    show ((tail.memSort.memInsert p c).fieldMap F
        ((tail.memSort.memInsertPerm _ p).apply (a, tail.memSortPerm.apply rest))).Perm
      (F p c a :: tail.fieldMap F rest)
    exact (fieldMap_memInsert F p c tail.memSort a (tail.memSortPerm.apply rest)).trans
      ((fieldMap_memSort F tail rest).cons _)

/-- Declaration-order decode of every field window `[p.1, p.1 + p.2.size)` of `bs`. -/
def decodeAt : {αs : List Type} → PlacedCodecSpine αs → List AbstractByte → Option (FieldTuple αs)
  | _, .nil, _ => some ()
  | _, .cons p c tail, bs =>
    match c.decode ((bs.drop p.1).take p.2.size), tail.decodeAt bs with
    | some a, some rest => some (a, rest)
    | _, _ => none

/-- Per-field decode obligations `c.decode (field window of bs) = some a` of a value tuple. -/
def decodeChecks {αs : List Type} (pc : PlacedCodecSpine αs) (bs : List AbstractByte)
    (x : FieldTuple αs) : List Prop :=
  pc.fieldMap (fun p c a => c.decode ((bs.drop p.1).take p.2.size) = some a) x

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem decodeAt_eq_some_iff :
    ∀ {αs : List Type} (pc : PlacedCodecSpine αs) (bs : List AbstractByte) (x : FieldTuple αs),
      pc.decodeAt bs = some x ↔ ∀ P ∈ pc.decodeChecks bs x, P
  | _, .nil, _, () => ⟨(fun _ _ hP => nomatch hP), (fun _ => rfl)⟩
  | _, .cons p c tail, bs, (a, rest) => by
    have ih := decodeAt_eq_some_iff tail bs rest
    show (match c.decode ((bs.drop p.1).take p.2.size), tail.decodeAt bs with
      | some a', some r => some (a', r)
      | _, _ => none) = some (a, rest) ↔
      ∀ P ∈ (c.decode ((bs.drop p.1).take p.2.size) = some a) :: tail.decodeChecks bs rest, P
    cases hC : c.decode ((bs.drop p.1).take p.2.size) with
    | none =>
      refine ⟨(fun h => nomatch h), fun h => ?_⟩
      have h0 := h _ (List.mem_cons_self ..)
      nomatch h0
    | some a' =>
      cases hT : tail.decodeAt bs with
      | none =>
        refine ⟨(fun h => nomatch h), fun h => ?_⟩
        have hT' := ih.mpr (fun P hP => h P (List.mem_cons_of_mem _ hP))
        rw [hT] at hT'
        nomatch hT'
      | some r =>
        constructor
        · intro h P hP
          injection h with h
          injection h with ha hr
          rcases List.mem_cons.mp hP with hP | hP
          · rw [hP, ha]
          · rw [hr] at hT
            exact ih.mp hT P hP
        · intro h
          have ha : some a' = some a := h _ (List.mem_cons_self ..)
          have hT' := ih.mpr (fun P hP => h P (List.mem_cons_of_mem _ hP))
          rw [hT] at hT'
          injection ha with ha
          injection hT' with hr
          rw [ha, hr]

end PlacedCodecSpine

namespace FixedByteCodec

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem prod_decode_eq_some_iff {α β : Type} {n₁ n₂ : Nat}
    (c₁ : FixedByteCodec α n₁) (c₂ : FixedByteCodec β n₂) (bs : List AbstractByte) (a : α) (b : β) :
    (prod c₁ c₂).decode bs = some (a, b) ↔
      bs.length = n₁ + n₂ ∧ c₁.decode (bs.take n₁) = some a ∧ c₂.decode (bs.drop n₁) = some b := by
  unfold prod ofRoundTrip
  dsimp only
  cases hL : Nat.beq bs.length (n₁ + n₂) with
  | false =>
    refine ⟨(fun h => nomatch h), fun ⟨hLen, _, _⟩ => ?_⟩
    rw [Nat.beq_eq.mpr hLen] at hL
    nomatch hL
  | true =>
    have hLen := Nat.eq_of_beq_eq_true hL
    dsimp only
    cases h₁ : c₁.decode (bs.take n₁) with
    | none => exact ⟨(fun h => nomatch h), fun ⟨_, h, _⟩ => nomatch h⟩
    | some a' =>
      cases h₂ : c₂.decode (bs.drop n₁) with
      | none => exact ⟨(fun h => nomatch h), fun ⟨_, _, h⟩ => nomatch h⟩
      | some b' =>
        constructor
        · intro h
          injection h with h
          injection h with ha hb
          rw [ha, hb]
          exact ⟨hLen, rfl, rfl⟩
        · rintro ⟨_, ha, hb⟩
          injection ha with ha
          injection hb with hb
          rw [ha, hb]

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem padLeft_decode_eq_some_iff {α : Type} {n : Nat} (k : Nat) (c : FixedByteCodec α n)
    (bs : List AbstractByte) (x : α) :
    (padLeft k c).decode bs = some x ↔ bs.length = k + n ∧ c.decode (bs.drop k) = some x := by
  have hDec : (padLeft k c).decode bs = ((prod (padUninit k) c).decode bs).map (fun p => p.2) := rfl
  rw [hDec]
  constructor
  · intro h
    cases hP : (prod (padUninit k) c).decode bs with
    | none =>
      rw [hP] at h
      nomatch h
    | some uy =>
      rw [hP] at h
      injection h with hx
      obtain ⟨u, y⟩ := uy
      have hP' := (prod_decode_eq_some_iff (padUninit k) c bs u y).mp hP
      dsimp only at hx
      rw [← hx]
      exact ⟨hP'.1, hP'.2.2⟩
  · rintro ⟨hLen, hC⟩
    have hU : (padUninit k).decode (bs.take k) = some () := by
      have hTakeLen : (bs.take k).length = k := by
        rw [List.length_take]
        exact Nat.min_eq_left (by omega)
      unfold padUninit ofRoundTrip
      dsimp only
      rw [Nat.beq_eq.mpr hTakeLen]
      rfl
    rw [(prod_decode_eq_some_iff (padUninit k) c bs () x).mpr ⟨hLen, hU, hC⟩]
    rfl

end FixedByteCodec

namespace PlacedCodecSpine

/--
Sequential decode of a re-padded memory-order spine: `bs` decodes to `y` iff it has the spine width
and every field window (at its absolute placement inside `pre ++ bs`) decodes to the matching
component of `y`.

Kind: codec
Witness: universal
Assumes: S0
Subject: laidOutStructSymbolicPad
-/
theorem decode_toSymbolicStructSpine_repad_eq_some_iff :
    ∀ {βs : List Type} (q : PlacedCodecSpine βs) (pads : List Nat) (trail : Nat)
      (pre bs : List AbstractByte) (y : FieldTuple βs),
      (q.toSymbolicStructSpine.repad pads trail).fieldOffsets pre.length = q.placed.map Prod.fst →
      ((laidOutStructSymbolicPad (q.toSymbolicStructSpine.repad pads trail)).decode bs = some y ↔
        bs.length = q.toSymbolicStructSpine.repadWidth pads trail ∧
          ∀ P ∈ q.decodeChecks (pre ++ bs) y, P)
  | _, .nil, _, trail, _, bs, (), _ => by
    show (FixedByteCodec.padUninit trail).decode bs = some () ↔
      bs.length = trail ∧ ∀ P ∈ ([] : List Prop), P
    unfold FixedByteCodec.padUninit FixedByteCodec.ofRoundTrip
    dsimp only
    cases hL : Nat.beq bs.length trail with
    | false =>
      refine ⟨(fun h => nomatch h), fun ⟨hLen, _⟩ => ?_⟩
      rw [Nat.beq_eq.mpr hLen] at hL
      nomatch hL
    | true =>
      exact ⟨fun _ => ⟨Nat.eq_of_beq_eq_true hL, fun _ hP => nomatch hP⟩, fun _ => rfl⟩
  | _, .cons p c tail, pads, trail, pre, bs, (a, rest), hOffs => by
    have hCons : pre.length :: (tail.toSymbolicStructSpine.repad pads.tail trail).fieldOffsets
        (pre.length + (p.2.size + pads.headD 0)) = p.1 :: tail.placed.map Prod.fst := hOffs
    injection hCons with hP1 hTailOffs
    show (FixedByteCodec.prod (FixedByteCodec.padRight c (pads.headD 0))
        (laidOutStructSymbolicPad (tail.toSymbolicStructSpine.repad pads.tail trail))).decode bs =
          some (a, rest) ↔
      bs.length = (p.2.size + pads.headD 0) + tail.toSymbolicStructSpine.repadWidth pads.tail trail ∧
        ∀ P ∈ (c.decode (((pre ++ bs).drop p.1).take p.2.size) = some a) ::
          tail.decodeChecks (pre ++ bs) rest, P
    rw [FixedByteCodec.prod_decode_eq_some_iff]
    have hDropPre : (pre ++ bs).drop p.1 = bs := by
      rw [← hP1]
      exact List.drop_left' rfl
    rw [hDropPre]
    constructor
    · rintro ⟨hLen, hHead, hTailDec⟩
      have hTakeLen : (bs.take (p.2.size + pads.headD 0)).length = p.2.size + pads.headD 0 := by
        rw [List.length_take]
        exact Nat.min_eq_left (by omega)
      rw [FixedByteCodec.padRight_decode_of_length_eq c hTakeLen, List.take_take,
        Nat.min_eq_left (Nat.le_add_right _ _)] at hHead
      have hPre' : (pre ++ bs.take (p.2.size + pads.headD 0)).length =
          pre.length + (p.2.size + pads.headD 0) := by
        rw [List.length_append, hTakeLen]
      have ih := decode_toSymbolicStructSpine_repad_eq_some_iff tail pads.tail trail
        (pre ++ bs.take (p.2.size + pads.headD 0)) (bs.drop (p.2.size + pads.headD 0)) rest
        (by rw [hPre']; exact hTailOffs)
      rw [List.append_assoc, List.take_append_drop] at ih
      obtain ⟨_, hChecks⟩ := ih.mp hTailDec
      refine ⟨hLen, fun P hP => ?_⟩
      rcases List.mem_cons.mp hP with hP | hP
      · rw [hP]
        exact hHead
      · exact hChecks P hP
    · rintro ⟨hLen, hChecks⟩
      have hTakeLen : (bs.take (p.2.size + pads.headD 0)).length = p.2.size + pads.headD 0 := by
        rw [List.length_take]
        exact Nat.min_eq_left (by omega)
      have hHead : c.decode (bs.take p.2.size) = some a := hChecks _ (List.mem_cons_self ..)
      have hPre' : (pre ++ bs.take (p.2.size + pads.headD 0)).length =
          pre.length + (p.2.size + pads.headD 0) := by
        rw [List.length_append, hTakeLen]
      have ih := decode_toSymbolicStructSpine_repad_eq_some_iff tail pads.tail trail
        (pre ++ bs.take (p.2.size + pads.headD 0)) (bs.drop (p.2.size + pads.headD 0)) rest
        (by rw [hPre']; exact hTailOffs)
      rw [List.append_assoc, List.take_append_drop] at ih
      refine ⟨hLen, ?_, ih.mpr ⟨by rw [List.length_drop]; omega,
        fun P hP => hChecks P (List.mem_cons_of_mem _ hP)⟩⟩
      rw [FixedByteCodec.padRight_decode_of_length_eq c hTakeLen, List.take_take,
        Nat.min_eq_left (Nat.le_add_right _ _)]
      exact hHead

/--
Computable realization of any sequential memory-order placement: `realizedWidth` is `totalSize`, and
the realized spine places every memory-order field at its offset.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem realized_offsets_and_width_of_sequential {αs : List Type} (pc : PlacedCodecSpine αs)
    (totalSize : Nat)
    (hSeq : SequentialFieldPlacement 0 (pc.memSort.placed.map Prod.snd)
      (pc.memSort.placed.map Prod.fst) totalSize) :
    (pc.realizedSpine totalSize).fieldOffsets pc.realizedLead = pc.memSort.placed.map Prod.fst ∧
      pc.realizedWidth totalSize = totalSize :=
  repad_sequentialPads_spec pc.memSort.placed 0 totalSize hSeq pc.memSort.toSymbolicStructSpine
    (widths_toSymbolicStructSpine pc.memSort)

/--
**Byte-Window Encoding of the Realized Codec**: in a sequential placement, `pc.realizedCodec`
encodes `x` exactly as writing the declaration-order windows `pc.windows x` over `totalSize`
uninitialized bytes (Trusted's `encodeFieldsAtOffsetsWith` strategy).

Kind: codec
Witness: universal
Assumes: S0
Subject: PlacedCodecSpine.realizedCodec
-/
theorem writeWindows_realizedCodec_encode {αs : List Type} (pc : PlacedCodecSpine αs)
    (totalSize : Nat)
    (hSeq : SequentialFieldPlacement 0 (pc.memSort.placed.map Prod.snd)
      (pc.memSort.placed.map Prod.fst) totalSize)
    (x : FieldTuple αs) :
    writeWindows (replicateUninitBytes totalSize) (pc.windows x) =
      some ((pc.realizedCodec totalSize).encode x) := by
  obtain ⟨hOffs, hWidth⟩ := pc.realized_offsets_and_width_of_sequential totalSize hSeq
  have hSpineWin : (pc.realizedSpine totalSize).windows (pc.memSortPerm.apply x) pc.realizedLead =
      pc.memSort.windows (pc.memSortPerm.apply x) :=
    windows_toSymbolicStructSpine_repad pc.memSort pc.realizedPads (pc.realizedTrail totalSize)
      (pc.memSortPerm.apply x) pc.realizedLead hOffs
  have hEnc := SymbolicStructSpine.writeWindows_encode (pc.realizedSpine totalSize)
    (pc.memSortPerm.apply x) (replicateUninitBytes pc.realizedLead) []
  rw [length_replicateUninitBytes, hSpineWin, List.append_nil, List.append_nil,
    ← MirValueCodec.replicateUninitBytes_add_eq] at hEnc
  have hW : pc.realizedLead + pc.memSort.toSymbolicStructSpine.repadWidth pc.realizedPads
      (pc.realizedTrail totalSize) = totalSize := hWidth
  rw [hW] at hEnc
  obtain ⟨hPw, hBd⟩ := windows_disjoint_of_sequential pc.memSort 0 totalSize
    (pc.memSortPerm.apply x) hSeq
  rw [← writeWindows_eq_of_perm (windows_memSort pc x)
    (fun w hw => by rw [length_replicateUninitBytes]; exact (hBd w hw).2) hPw]
  exact hEnc

/--
**Byte-Window Decoding of the Realized Codec**: in a sequential placement, `pc.realizedCodec`
decodes every `totalSize`-byte buffer exactly as decoding each declaration field from its own
window (`pc.decodeAt`), ignoring all padding bytes (Trusted's `decodeFieldsAtOffsetsWith` strategy).

Kind: codec
Witness: universal
Assumes: S0
Subject: PlacedCodecSpine.realizedCodec
-/
theorem realizedCodec_decode_eq_decodeAt {αs : List Type} (pc : PlacedCodecSpine αs)
    (totalSize : Nat)
    (hSeq : SequentialFieldPlacement 0 (pc.memSort.placed.map Prod.snd)
      (pc.memSort.placed.map Prod.fst) totalSize)
    (bs : List AbstractByte) (hLen : bs.length = totalSize) :
    (pc.realizedCodec totalSize).decode bs = pc.decodeAt bs := by
  obtain ⟨hOffs, hWidth⟩ := pc.realized_offsets_and_width_of_sequential totalSize hSeq
  have hW : pc.realizedLead + pc.memSort.toSymbolicStructSpine.repadWidth pc.realizedPads
      (pc.realizedTrail totalSize) = totalSize := hWidth
  apply Option.ext
  intro x
  have hDec : (pc.realizedCodec totalSize).decode bs =
      ((FixedByteCodec.padLeft pc.realizedLead
        (laidOutStructSymbolicPad (pc.realizedSpine totalSize))).decode bs).map
          pc.memSortPerm.unapply := rfl
  rw [hDec, decodeAt_eq_some_iff]
  have hTakeLen : (bs.take pc.realizedLead).length = pc.realizedLead := by
    rw [List.length_take]
    exact Nat.min_eq_left (by omega)
  have hSpine := decode_toSymbolicStructSpine_repad_eq_some_iff pc.memSort pc.realizedPads
    (pc.realizedTrail totalSize) (bs.take pc.realizedLead) (bs.drop pc.realizedLead)
    (pc.memSortPerm.apply x) (by rw [hTakeLen]; exact hOffs)
  rw [List.take_append_drop] at hSpine
  have hPerm := fieldMap_memSort
    (fun p c a => c.decode ((bs.drop p.1).take p.2.size) = some a) pc x
  constructor
  · intro h
    cases hP : (FixedByteCodec.padLeft pc.realizedLead
        (laidOutStructSymbolicPad (pc.realizedSpine totalSize))).decode bs with
    | none =>
      rw [hP] at h
      nomatch h
    | some y =>
      rw [hP] at h
      injection h with hx
      have hy : y = pc.memSortPerm.apply x := by
        rw [← hx, FieldPerm.apply_unapply]
      rw [hy] at hP
      have hSp := (FixedByteCodec.padLeft_decode_eq_some_iff _ _ bs _).mp hP
      have hChecks := (hSpine.mp hSp.2).2
      intro P hP
      exact hChecks P (hPerm.mem_iff.mpr hP)
  · intro hChecks
    have hSp : (laidOutStructSymbolicPad (pc.realizedSpine totalSize)).decode
        (bs.drop pc.realizedLead) = some (pc.memSortPerm.apply x) :=
      hSpine.mpr ⟨by rw [List.length_drop]; omega,
        fun P hP => hChecks P (hPerm.mem_iff.mp hP)⟩
    rw [(FixedByteCodec.padLeft_decode_eq_some_iff _ _ bs _).mpr ⟨by rw [hLen]; exact hW.symm, hSp⟩]
    show some (pc.memSortPerm.unapply (pc.memSortPerm.apply x)) = some x
    rw [FieldPerm.unapply_apply]

end PlacedCodecSpine

/-- Byte `j` of `bs` exists and is initialized. -/
def InitAt (bs : List AbstractByte) (j : Nat) : Prop :=
  ∃ (b : UInt8) (p : Option (Nat × Nat)), bs[j]? = some (.init b p)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem initAt_of_allBytesInitialized :
    ∀ (l : List AbstractByte), allBytesInitialized l = true → ∀ k, k < l.length → InitAt l k
  | [], _, k, hk => absurd hk (Nat.not_lt_zero k)
  | .uninit :: _, h, _, _ => nomatch h
  | .init b p :: rest, h, k, hk => by
    cases k with
    | zero => exact ⟨b, p, rfl⟩
    | succ k =>
      have hRest : allBytesInitialized rest = true := h
      exact initAt_of_allBytesInitialized rest hRest k (Nat.lt_of_succ_lt_succ hk)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem allBytesInitialized_of_initAt :
    ∀ (l : List AbstractByte), (∀ k, k < l.length → InitAt l k) → allBytesInitialized l = true
  | [], _ => rfl
  | x :: rest, h => by
    obtain ⟨b, p, hx⟩ := h 0 (Nat.zero_lt_succ _)
    have hx' : x = .init b p := Option.some.inj hx
    subst hx'
    exact allBytesInitialized_of_initAt rest (fun k hk => h (k + 1) (Nat.succ_lt_succ hk))

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem decodeLittleEndianBytes_some_allBytesInitialized :
    ∀ (l : List AbstractByte) (r : Nat × Option (Nat × Nat)),
      decodeLittleEndianBytes l = some r → allBytesInitialized l = true
  | [], _, _ => rfl
  | .uninit :: _, _, h => nomatch h
  | .init b prov :: rest, r, h => by
    have hUnfold : decodeLittleEndianBytes (.init b prov :: rest) =
        (match decodeLittleEndianBytes rest with
          | .some (highBits, restProv) =>
            .some (Nat.add b.toBitVec.toNat (Nat.mul 256 highBits), mergeByteProvenance prov restProv)
          | .none => .none) := rfl
    rw [hUnfold] at h
    cases hR : decodeLittleEndianBytes rest with
    | none =>
      rw [hR] at h
      nomatch h
    | some r' =>
      exact decodeLittleEndianBytes_some_allBytesInitialized rest r' hR

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem decodeScalarBytes_some_allBytesInitialized (bytes : List AbstractByte) (signed : Bool)
    (r : ScalarInt × Option (Nat × Nat))
    (h : decodeScalarBytes bytes signed = some r) :
    allBytesInitialized bytes = true := by
  unfold decodeScalarBytes at h
  dsimp only at h
  cases h0 : Nat.beq (Trusted.Sequence.length bytes) 0 with
  | true =>
    rw [h0] at h
    nomatch h
  | false =>
    rw [h0] at h
    dsimp only at h
    cases hLE : decodeLittleEndianBytes bytes with
    | none =>
      rw [hLE] at h
      nomatch h
    | some r' =>
      exact decodeLittleEndianBytes_some_allBytesInitialized bytes r' hLE

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem decodeScalarLayoutBytes_some_allBytesInitialized (sl : ScalarLayout)
    (bytes : List AbstractByte) (v : Value)
    (h : decodeScalarLayoutBytes sl bytes = some v) :
    allBytesInitialized bytes = true := by
  unfold decodeScalarLayoutBytes at h
  cases hW : scalarLayoutByteWidth sl with
  | none =>
    rw [hW] at h
    nomatch h
  | some sz =>
    rw [hW] at h
    dsimp only at h
    cases hLen : Nat.beq (Trusted.Sequence.length bytes) sz with
    | false =>
      rw [hLen] at h
      nomatch h
    | true =>
      rw [hLen] at h
      dsimp only at h
      cases sl <;>
        (cases hSc : decodeScalarBytes bytes false with
         | none =>
           rw [hSc] at h
           nomatch h
         | some r =>
           exact decodeScalarBytes_some_allBytesInitialized bytes false r hSc)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem sliceAbstractBytes_some_eq_drop_take_and_len
    {bs : List AbstractByte} {off sz : Nat} {fSlice : List AbstractByte}
    (h : sliceAbstractBytes bs off sz = some fSlice) :
    fSlice = (bs.drop off).take sz ∧ fSlice.length = sz := by
  unfold sliceAbstractBytes at h
  cases hBle : Nat.ble (Nat.add off sz) (Trusted.Sequence.length bs) with
  | false =>
    rw [hBle] at h
    nomatch h
  | true =>
    rw [hBle] at h
    injection h with hEq
    rw [takeAbstractBytes_eq_take, dropAbstractBytes_eq_drop] at hEq
    have hIn : off + sz ≤ bs.length := Nat.le_of_ble_eq_true hBle
    refine ⟨hEq.symm, ?_⟩
    rw [← hEq, List.length_take, List.length_drop]
    exact Nat.min_eq_left (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hIn))

/--
One-step unfolding of Trusted's `decodeFieldsBySpan` with the next offset as `headD`.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem decodeFieldsBySpan_cons (bs : List AbstractByte) (T : Nat) (off : Size) (rest : List Size) :
    decodeFieldsBySpan bs T (off :: rest) =
      (match Nat.ble off.bytes ((rest.map Size.bytes).headD T) with
      | false => none
      | true =>
        match sliceAbstractBytes bs off.bytes
            (Nat.sub ((rest.map Size.bytes).headD T) off.bytes) with
        | none => none
        | some fSlice =>
          match (match Nat.beq (Nat.sub ((rest.map Size.bytes).headD T) off.bytes) 0 with
            | true => some Value.unit
            | false =>
              match decodeScalarBytes fSlice false with
              | some (sv, _) => some (Value.scalar sv)
              | none => none) with
          | none => none
          | some v =>
            match decodeFieldsBySpan bs T rest with
            | some vs => some (v :: vs)
            | none => none) := by
  cases rest <;> rfl

/--
A successful `decodeFieldsBySpan` run certifies that its offsets are bounded below by the first one
and that every byte from the first offset up to `totalSize` is initialized.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem decodeFieldsBySpan_some_initAt (bs : List AbstractByte) (T : Nat) :
    ∀ (offs : List Size) (vs : List Value), decodeFieldsBySpan bs T offs = some vs →
      (∀ off ∈ offs, (offs.map Size.bytes).headD T ≤ off.bytes) ∧
      (∀ j, (offs.map Size.bytes).headD T ≤ j → j < T → InitAt bs j)
  | [], _, _ => ⟨(fun _ h => nomatch h),
      (fun j h₁ h₂ => absurd (Nat.lt_of_le_of_lt h₁ h₂) (Nat.lt_irrefl _))⟩
  | off :: rest, vs, h => by
    rw [decodeFieldsBySpan_cons] at h
    generalize hN : (rest.map Size.bytes).headD T = nextOff at h
    cases hBle : Nat.ble off.bytes nextOff with
    | false =>
      rw [hBle] at h
      nomatch h
    | true =>
      rw [hBle] at h
      dsimp only at h
      have hOffLe : off.bytes ≤ nextOff := Nat.le_of_ble_eq_true hBle
      cases hSl : sliceAbstractBytes bs off.bytes (Nat.sub nextOff off.bytes) with
      | none =>
        rw [hSl] at h
        nomatch h
      | some fSlice =>
        rw [hSl] at h
        dsimp only at h
        have hSlice := hSl
        unfold sliceAbstractBytes at hSlice
        cases hBle2 : Nat.ble (Nat.add off.bytes (Nat.sub nextOff off.bytes))
            (Trusted.Sequence.length bs) with
        | false =>
          rw [hBle2] at hSlice
          nomatch hSlice
        | true =>
          rw [hBle2] at hSlice
          injection hSlice with hFs0
          rw [takeAbstractBytes_eq_take, dropAbstractBytes_eq_drop] at hFs0
          have hFs : (bs.drop off.bytes).take (nextOff - off.bytes) = fSlice := hFs0
          have hInBs : off.bytes + (nextOff - off.bytes) ≤ bs.length := Nat.le_of_ble_eq_true hBle2
          have hFsLen : fSlice.length = nextOff - off.bytes := by
            rw [← hFs, List.length_take, List.length_drop]
            exact Nat.min_eq_left (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hInBs))
          have hFsAt : ∀ k, k < nextOff - off.bytes → fSlice[k]? = bs[off.bytes + k]? := by
            intro k hk
            rw [← hFs, List.getElem?_take, List.getElem?_drop]
            exact ite_eq_left_iff.mpr (fun hNot => absurd hk hNot)
          have hFieldInit : nextOff - off.bytes ≠ 0 → allBytesInitialized fSlice = true := by
            intro hNz
            have hBeq0 : Nat.beq (Nat.sub nextOff off.bytes) 0 = false :=
              nat_beq_eq_false_of_ne hNz
            rw [hBeq0] at h
            dsimp only at h
            cases hDec : decodeScalarBytes fSlice false with
            | none =>
              rw [hDec] at h
              nomatch h
            | some svp =>
              unfold decodeScalarBytes at hDec
              dsimp only at hDec
              cases hZ : Nat.beq (Trusted.Sequence.length fSlice) 0 with
              | true =>
                rw [hZ] at hDec
                nomatch hDec
              | false =>
                rw [hZ] at hDec
                dsimp only at hDec
                cases hLE : decodeLittleEndianBytes fSlice with
                | none =>
                  rw [hLE] at hDec
                  nomatch hDec
                | some r =>
                  exact decodeLittleEndianBytes_some_allBytesInitialized fSlice r hLE
          have hRestSome : ∃ vs', decodeFieldsBySpan bs T rest = some vs' := by
            cases hR : decodeFieldsBySpan bs T rest with
            | some vs' => exact ⟨vs', rfl⟩
            | none =>
              exfalso
              cases hB0 : Nat.beq (Nat.sub nextOff off.bytes) 0 with
              | true =>
                rw [hB0] at h
                dsimp only at h
                rw [hR] at h
                nomatch h
              | false =>
                rw [hB0] at h
                dsimp only at h
                cases hDec : decodeScalarBytes fSlice false with
                | none =>
                  rw [hDec] at h
                  nomatch h
                | some svp =>
                  rw [hDec] at h
                  dsimp only at h
                  rw [hR] at h
                  nomatch h
          obtain ⟨vs', hRest⟩ := hRestSome
          obtain ⟨ihLe, ihInit⟩ := decodeFieldsBySpan_some_initAt bs T rest vs' hRest
          rw [hN] at ihLe ihInit
          refine ⟨fun off' hOff' => ?_, fun j hj₁ hj₂ => ?_⟩
          · show off.bytes ≤ off'.bytes
            rcases List.mem_cons.mp hOff' with hEq | hMem
            · rw [hEq]
              exact Nat.le_refl _
            · exact Nat.le_trans hOffLe (ihLe off' hMem)
          · have hj₁' : off.bytes ≤ j := hj₁
            by_cases hjN : j < nextOff
            · have hk : j - off.bytes < nextOff - off.bytes := Nat.sub_lt_sub_right hj₁' hjN
              have hNz : nextOff - off.bytes ≠ 0 :=
                Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt (Nat.lt_of_le_of_lt hj₁' hjN))
              obtain ⟨b, p, hb⟩ := initAt_of_allBytesInitialized fSlice (hFieldInit hNz)
                (j - off.bytes) (by rw [hFsLen]; exact hk)
              rw [hFsAt (j - off.bytes) hk, Nat.add_sub_cancel' hj₁'] at hb
              exact ⟨b, p, hb⟩
            · exact ihInit j (Nat.le_of_not_lt hjN) hj₂

namespace PlacedCodecSpine

/--
If every field codec is a surjective initialized-byte decoder and every byte of every in-bounds field
window is initialized, the declaration-order window decode succeeds.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem decodeAt_isSome_of_initAt :
    ∀ {αs : List Type} (pc : PlacedCodecSpine αs) (bs : List AbstractByte),
      pc.AllFieldsSurjective →
      (∀ p ∈ pc.placed, p.1 + p.2.size ≤ bs.length) →
      (∀ p ∈ pc.placed, ∀ j, p.1 ≤ j → j < p.1 + p.2.size → InitAt bs j) →
      ∃ x, pc.decodeAt bs = some x
  | _, .nil, _, _, _, _ => ⟨(), rfl⟩
  | _, .cons p c tail, bs, hSurj, hIn, hInit => by
    obtain ⟨hC, hTail⟩ := hSurj
    have hP := hIn p (List.mem_cons_self ..)
    have hSliceLen : ((bs.drop p.1).take p.2.size).length = p.2.size := by
      rw [List.length_take, List.length_drop]
      omega
    have hSliceInit : allBytesInitialized ((bs.drop p.1).take p.2.size) = true := by
      apply allBytesInitialized_of_initAt
      intro k hk
      rw [hSliceLen] at hk
      obtain ⟨b, q, hb⟩ := hInit p (List.mem_cons_self ..) (p.1 + k) (Nat.le_add_right _ _)
        (Nat.add_lt_add_left hk _)
      refine ⟨b, q, ?_⟩
      rw [List.getElem?_take, List.getElem?_drop]
      rw [ite_eq_left_iff.mpr (fun hNot => absurd hk hNot)]
      exact hb
    obtain ⟨a, ha⟩ := hC _ hSliceLen hSliceInit
    obtain ⟨r, hr⟩ := decodeAt_isSome_of_initAt tail bs hTail
      (fun q hq => hIn q (List.mem_cons_of_mem _ hq))
      (fun q hq => hInit q (List.mem_cons_of_mem _ hq))
    refine ⟨(a, r), ?_⟩
    show (match c.decode ((bs.drop p.1).take p.2.size), tail.decodeAt bs with
      | some a', some r' => some (a', r')
      | _, _ => none) = some (a, r)
    rw [ha, hr]

end PlacedCodecSpine

/-! ### Trusted Tuple-Field Bridges (`TupleFieldCodec`, `TupleFieldCodecs`)

A `TupleFieldCodec layouts k c` exists only for field kinds with a structural byte size
(`rigidTyKindByteSize k = some n`: integers, `bool`, `char`, `()`, pointers, arrays), never for ADT
kinds (`TupleFieldCodec.not_adt`). The windows it accepts are fixed by `k`
(`TupleFieldCodec.decode_isSome_of_sameKind`): integer-kind fields are niche-blind
(`TupleFieldCodec.uint_isSurjectiveInitDecoder`, `TupleFieldCodec.int_isSurjectiveInitDecoder`), so
`NonZero*` niche codecs cannot be tuple fields
(`TupleFieldCodec.uint_not_scalarValidRange_of_out_of_range`), whereas `.bool` enforces its niche.
-/

/--
Fuel at which Trusted's `encodeValueToBytes` / `decodeValueFromBytes` recurse into the fields of a
tuple encoded at `defaultCodecFuel` (`defaultCodecFuel = tupleFieldFuel + 1`).
-/
abbrev tupleFieldFuel : Nat := 15

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem defaultCodecFuel_eq_tupleFieldFuel_succ : defaultCodecFuel = tupleFieldFuel + 1 := rfl

/--
Trusted-level bridge for one tuple field of rigid kind `k` (field type `{ kind := k, layoutIdx := 0 }`)
whose bytes are the `FixedByteCodec` `c`, stated at `tupleFieldFuel` — the fuel at which Trusted
encodes and decodes tuple fields. `kindSize_eq` pins the field's structural byte size, which also
rules out Trusted's untyped `encodeFallback` for this field.
-/
structure TupleFieldCodec (layouts : LayoutTable) (k : RigidTy) {α : Type} {n : Nat}
    (c : FixedByteCodec α n) : Type where
  /-- Embed a field value into a runtime `Value`. -/
  toValue : α → Value
  /-- Partial projection from a runtime `Value` back to a field value. -/
  ofValue : Value → Option α
  /-- `ofValue` is a left inverse to `toValue`. -/
  ofValue_toValue : ∀ x : α, ofValue (toValue x) = some x
  /-- The field kind has structural byte size `n`. -/
  kindSize_eq : rigidTyKindByteSize k = some n
  /-- Trusted encodes `toValue x` to `c.encode x`. -/
  encode_toValue : ∀ x : α,
    encodeValueToBytes tupleFieldFuel layouts { kind := k, layoutIdx := 0 } (toValue x) =
      some (c.encode x)
  /-- Every successful Trusted field encoding is `c.encode x` for some `x`. -/
  encode_witness : ∀ (v : Value) (bs : List AbstractByte),
    encodeValueToBytes tupleFieldFuel layouts { kind := k, layoutIdx := 0 } v = some bs →
      ∃ x : α, bs = c.encode x
  /-- Trusted decodes every field window exactly as `c.decode`. -/
  decode_eq_map : ∀ bs : List AbstractByte,
    decodeValueFromBytes tupleFieldFuel layouts { kind := k, layoutIdx := 0 } bs =
      (c.decode bs).map toValue

/--
Declaration-order `TupleFieldCodec` for every field of a `PlacedCodecSpine` (field kinds `ks`).
-/
inductive TupleFieldCodecs (layouts : LayoutTable) :
    List RigidTy → {αs : List Type} → PlacedCodecSpine αs → Type 1 where
  | nil : TupleFieldCodecs layouts [] .nil
  | cons {k : RigidTy} {ks : List RigidTy} {α : Type} {αs : List Type} {p : Nat × FieldLayout}
      {c : FixedByteCodec α p.2.size} {tail : PlacedCodecSpine αs}
      (f : TupleFieldCodec layouts k c) (rest : TupleFieldCodecs layouts ks tail) :
      TupleFieldCodecs layouts (k :: ks) (.cons p c tail)

namespace TupleFieldCodecs

variable {layouts : LayoutTable}

/-- Runtime field `Value`s of a declaration-order value tuple. -/
def toValues : {ks : List RigidTy} → {αs : List Type} → {pc : PlacedCodecSpine αs} →
    TupleFieldCodecs layouts ks pc → FieldTuple αs → List Value
  | _, _, _, .nil, _ => []
  | _, _, _, .cons f rest, (a, r) => f.toValue a :: rest.toValues r

/-- Partial projection from runtime field `Value`s back to a declaration-order value tuple. -/
def ofValues : {ks : List RigidTy} → {αs : List Type} → {pc : PlacedCodecSpine αs} →
    TupleFieldCodecs layouts ks pc → List Value → Option (FieldTuple αs)
  | _, _, _, .nil, [] => some ()
  | _, _, _, .nil, _ :: _ => none
  | _, _, _, .cons _ _, [] => none
  | _, _, _, .cons f rest, v :: vs =>
    match f.ofValue v, rest.ofValues vs with
    | some a, some r => some (a, r)
    | _, _ => none

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem ofValues_toValues :
    ∀ {ks : List RigidTy} {αs : List Type} {pc : PlacedCodecSpine αs}
      (fcs : TupleFieldCodecs layouts ks pc) (x : FieldTuple αs),
      fcs.ofValues (fcs.toValues x) = some x
  | _, _, _, .nil, () => rfl
  | _, _, _, .cons f rest, (a, r) => by
    show (match f.ofValue (f.toValue a), rest.ofValues (rest.toValues r) with
      | some a', some r' => some (a', r')
      | _, _ => none) = some (a, r)
    rw [f.ofValue_toValue a, ofValues_toValues rest r]

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem length_toValues :
    ∀ {ks : List RigidTy} {αs : List Type} {pc : PlacedCodecSpine αs}
      (fcs : TupleFieldCodecs layouts ks pc) (x : FieldTuple αs),
      (fcs.toValues x).length = ks.length
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons _ rest, (_, r) => congrArg Nat.succ (length_toValues rest r)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem length_placed :
    ∀ {ks : List RigidTy} {αs : List Type} {pc : PlacedCodecSpine αs}
      (_ : TupleFieldCodecs layouts ks pc), pc.placed.length = ks.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ rest => congrArg Nat.succ (length_placed rest)

/--
**Trusted Tuple-Field Writes Are Window Writes**: Trusted's `encodeFieldsAtOffsetsWith` over the
placed offsets of `pc` writes exactly the declaration-order windows `pc.windows x`.

Kind: refinement
Witness: universal
Assumes: S0
Subject: encodeFieldsAtOffsetsWith
-/
theorem encodeFieldsAtOffsetsWith_eq_writeWindows
    (encodeFallback : Value → Option (List AbstractByte)) :
    ∀ {ks : List RigidTy} {αs : List Type} {pc : PlacedCodecSpine αs}
      (fcs : TupleFieldCodecs layouts ks pc) (x : FieldTuple αs) (buf : List AbstractByte),
      encodeFieldsAtOffsetsWith
          (fun k fv => encodeValueToBytes tupleFieldFuel layouts { kind := k, layoutIdx := 0 } fv)
          encodeFallback (pc.placed.map fun p => ({ bytes := p.1 } : Size)) ks (fcs.toValues x) buf =
        writeWindows buf (pc.windows x)
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, @TupleFieldCodecs.cons _ k ks _ _ p c tail f rest, (a, r), buf => by
    have ih := encodeFieldsAtOffsetsWith_eq_writeWindows encodeFallback rest r
    show (match (match encodeValueToBytes tupleFieldFuel layouts { kind := k, layoutIdx := 0 }
              (f.toValue a) with
            | some bs => some bs
            | none =>
              match rigidTyKindByteSize k with
              | some _ => none
              | none => encodeFallback (f.toValue a)) with
        | none => none
        | some fBytes =>
          match writeAbstractBytesAt buf p.1 fBytes with
          | none => none
          | some buf' =>
            encodeFieldsAtOffsetsWith
              (fun k fv => encodeValueToBytes tupleFieldFuel layouts { kind := k, layoutIdx := 0 } fv)
              encodeFallback (tail.placed.map fun p => ({ bytes := p.1 } : Size)) ks
              (rest.toValues r) buf') =
      (match writeAbstractBytesAt buf p.1 (c.encode a) with
        | some buf' => writeWindows buf' (tail.windows r)
        | none => none)
    rw [f.encode_toValue a]
    dsimp only
    cases writeAbstractBytesAt buf p.1 (c.encode a) with
    | none => rfl
    | some buf' => exact ih buf'

/--
**Trusted Tuple-Field Write Witness**: every successful `encodeFieldsAtOffsetsWith` run over the
placed offsets of `pc` writes the windows `pc.windows x` of some value tuple `x`.

Kind: refinement
Witness: universal
Assumes: S0
Subject: encodeFieldsAtOffsetsWith
-/
theorem encodeFieldsAtOffsetsWith_witness
    (encodeFallback : Value → Option (List AbstractByte)) :
    ∀ {ks : List RigidTy} {αs : List Type} {pc : PlacedCodecSpine αs}
      (_fcs : TupleFieldCodecs layouts ks pc) (vals : List Value) (buf out : List AbstractByte),
      encodeFieldsAtOffsetsWith
          (fun k fv => encodeValueToBytes tupleFieldFuel layouts { kind := k, layoutIdx := 0 } fv)
          encodeFallback (pc.placed.map fun p => ({ bytes := p.1 } : Size)) ks vals buf = some out →
        ∃ x : FieldTuple αs, writeWindows buf (pc.windows x) = some out
  | _, _, _, .nil, [], buf, out, h => ⟨(), h⟩
  | _, _, _, .nil, _ :: _, _, _, h => nomatch h
  | _, _, _, .cons _ _, [], _, _, h => nomatch h
  | _, _, _, @TupleFieldCodecs.cons _ k ks _ _ p c tail f rest, v :: vs, buf, out, h => by
    change (match (match encodeValueToBytes tupleFieldFuel layouts { kind := k, layoutIdx := 0 } v with
            | some bs => some bs
            | none =>
              match rigidTyKindByteSize k with
              | some _ => none
              | none => encodeFallback v) with
        | none => none
        | some fBytes =>
          match writeAbstractBytesAt buf p.1 fBytes with
          | none => none
          | some buf' =>
            encodeFieldsAtOffsetsWith
              (fun k fv => encodeValueToBytes tupleFieldFuel layouts { kind := k, layoutIdx := 0 } fv)
              encodeFallback (tail.placed.map fun p => ({ bytes := p.1 } : Size)) ks vs buf') =
      some out at h
    cases hE : encodeValueToBytes tupleFieldFuel layouts { kind := k, layoutIdx := 0 } v with
    | none =>
      rw [hE, f.kindSize_eq] at h
      nomatch h
    | some bs =>
      rw [hE] at h
      obtain ⟨a, rfl⟩ := f.encode_witness v bs hE
      dsimp only at h
      cases hW : writeAbstractBytesAt buf p.1 (c.encode a) with
      | none =>
        rw [hW] at h
        nomatch h
      | some buf' =>
        rw [hW] at h
        obtain ⟨r, hr⟩ := encodeFieldsAtOffsetsWith_witness encodeFallback rest vs buf' out h
        refine ⟨(a, r), ?_⟩
        show (match writeAbstractBytesAt buf p.1 (c.encode a) with
          | some b => writeWindows b (tail.windows r)
          | none => none) = some out
        rw [hW]
        exact hr

/--
**Trusted Tuple-Field Reads Are Window Decodes**: Trusted's `decodeFieldsAtOffsetsWith` over the
placed offsets of `pc` decodes each declaration field from its own window (`pc.decodeAt`).

Kind: refinement
Witness: universal
Assumes: S0
Subject: decodeFieldsAtOffsetsWith
-/
theorem decodeFieldsAtOffsetsWith_eq_decodeAt :
    ∀ {ks : List RigidTy} {αs : List Type} {pc : PlacedCodecSpine αs}
      (fcs : TupleFieldCodecs layouts ks pc) (bs : List AbstractByte),
      (∀ p ∈ pc.placed, p.1 + p.2.size ≤ bs.length) →
      decodeFieldsAtOffsetsWith
          (fun k b => decodeValueFromBytes tupleFieldFuel layouts { kind := k, layoutIdx := 0 } b)
          (fun k => rigidTyByteSize layouts { kind := k, layoutIdx := 0 }) bs
          (pc.placed.map fun p => ({ bytes := p.1 } : Size)) ks =
        (pc.decodeAt bs).map fcs.toValues
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, @TupleFieldCodecs.cons _ k ks _ _ p c tail f rest, bs, hIn => by
    have ih := decodeFieldsAtOffsetsWith_eq_decodeAt rest bs
      (fun q hq => hIn q (List.mem_cons_of_mem _ hq))
    have hSz : rigidTyByteSize layouts { kind := k, layoutIdx := 0 } = some p.2.size := by
      unfold rigidTyByteSize
      dsimp only
      rw [f.kindSize_eq]
    have hP := hIn p (List.mem_cons_self ..)
    have hSlice : sliceAbstractBytes bs p.1 p.2.size = some ((bs.drop p.1).take p.2.size) := by
      unfold sliceAbstractBytes
      rw [Nat.ble_eq_true_of_le (show Nat.add p.1 p.2.size ≤ Trusted.Sequence.length bs from hP)]
      dsimp only
      rw [takeAbstractBytes_eq_take, dropAbstractBytes_eq_drop]
    show (match rigidTyByteSize layouts { kind := k, layoutIdx := 0 } with
        | none => none
        | some fSize =>
          match sliceAbstractBytes bs p.1 fSize with
          | none => none
          | some fSlice =>
            match decodeValueFromBytes tupleFieldFuel layouts { kind := k, layoutIdx := 0 } fSlice with
            | none => none
            | some v =>
              match decodeFieldsAtOffsetsWith
                  (fun k b => decodeValueFromBytes tupleFieldFuel layouts { kind := k, layoutIdx := 0 } b)
                  (fun k => rigidTyByteSize layouts { kind := k, layoutIdx := 0 }) bs
                  (tail.placed.map fun p => ({ bytes := p.1 } : Size)) ks with
              | some vs => some (v :: vs)
              | none => none) =
      (match c.decode ((bs.drop p.1).take p.2.size), tail.decodeAt bs with
        | some a, some r => some (a, r)
        | _, _ => none).map (fun x => (TupleFieldCodecs.cons f rest).toValues x)
    rw [hSz]
    dsimp only
    rw [hSlice]
    dsimp only
    rw [f.decode_eq_map, ih]
    cases c.decode ((bs.drop p.1).take p.2.size) with
    | none => rfl
    | some a =>
      cases tail.decodeAt bs with
      | none => rfl
      | some r => rfl

end TupleFieldCodecs

/--
Every placed field of a sequential memory-order placement lies within `totalSize` (declaration order).

Kind: helper
Witness: universal
Assumes: S0
-/
theorem PlacedCodecSpine.placed_in_bounds_of_memSort_sequential {αs : List Type}
    (pc : PlacedCodecSpine αs) (totalSize : Nat)
    (hSeq : SequentialFieldPlacement 0 (pc.memSort.placed.map Prod.snd)
      (pc.memSort.placed.map Prod.fst) totalSize) :
    ∀ p ∈ pc.placed, p.1 + p.2.size ≤ totalSize := by
  intro p hp
  have hMem : p ∈ pc.memSort.placed := by
    rw [placed_memSort]
    exact (memSort_perm pc.placed).mem_iff.mpr hp
  exact (PlacedCodecSpine.placed_in_bounds_of_sequential pc.memSort.placed 0 totalSize hSeq p hMem).2

namespace TupleFieldCodec

/-- `TupleFieldCodec` for an unsigned integer field `uN` (`FixedByteCodec.uintBitsLE`). -/
def uint (layouts : LayoutTable) (w : UintTy) :
    TupleFieldCodec layouts (.uint w)
      (FixedByteCodec.uintBitsLE (MirValueCodec.uintByteSize w) (MirValueCodec.uintByteSize_pos w)) where
  toValue := (MirValueCodec.uint layouts w 0).toValue
  ofValue := (MirValueCodec.uint layouts w 0).ofValue
  ofValue_toValue := (MirValueCodec.uint layouts w 0).ofValue_toValue
  kindSize_eq := MirValueCodec.intCastTargetBytes_uint_eq w
  encode_toValue := (MirValueCodec.uint layouts w 0).encode_toValue
  encode_witness := fun v bs hEnc => by
    unfold tupleFieldFuel encodeValueToBytes at hEnc
    dsimp only at hEnc
    rw [MirValueCodec.intCastTargetBytes_uint_eq w] at hEnc
    cases v <;> dsimp only at hEnc
    case unit => nomatch hEnc
    case ptr => nomatch hEnc
    case aggregate => nomatch hEnc
    case scalar sv =>
      cases hEq : Nat.beq sv.sizeBytes (MirValueCodec.uintByteSize w) <;> rw [hEq] at hEnc
      · nomatch hEnc
      · have hSvSz : sv.sizeBytes = MirValueCodec.uintByteSize w := Nat.eq_of_beq_eq_true hEq
        unfold encodeScalarBytes at hEnc
        rw [hSvSz] at hEnc
        have hBeq0 : Nat.beq (MirValueCodec.uintByteSize w) 0 = false :=
          nat_beq_eq_false_of_ne (by have := MirValueCodec.uintByteSize_pos w; omega)
        rw [hBeq0] at hEnc
        injection hEnc with hBs
        refine ⟨⟨sv.bits % 2 ^ (8 * MirValueCodec.uintByteSize w), Nat.mod_lt _ (Nat.two_pow_pos _)⟩, ?_⟩
        rw [← hBs]
        exact (encodeLittleEndianBytes_mod_two_pow none _ sv.bits).symm
  decode_eq_map := (MirValueCodec.uint layouts w 0).decode_eq_map

/-- `TupleFieldCodec` for a signed integer field `iN` (`FixedByteCodec.uintBitsLE` of two's-complement bits). -/
def int (layouts : LayoutTable) (w : IntTy) :
    TupleFieldCodec layouts (.int w)
      (FixedByteCodec.uintBitsLE (MirValueCodec.intByteSize w) (MirValueCodec.intByteSize_pos w)) where
  toValue := (MirValueCodec.int layouts w 0).toValue
  ofValue := (MirValueCodec.int layouts w 0).ofValue
  ofValue_toValue := (MirValueCodec.int layouts w 0).ofValue_toValue
  kindSize_eq := MirValueCodec.intCastTargetBytes_int_eq w
  encode_toValue := (MirValueCodec.int layouts w 0).encode_toValue
  encode_witness := fun v bs hEnc => by
    unfold tupleFieldFuel encodeValueToBytes at hEnc
    dsimp only at hEnc
    rw [MirValueCodec.intCastTargetBytes_int_eq w] at hEnc
    cases v <;> dsimp only at hEnc
    case unit => nomatch hEnc
    case ptr => nomatch hEnc
    case aggregate => nomatch hEnc
    case scalar sv =>
      cases hEq : Nat.beq sv.sizeBytes (MirValueCodec.intByteSize w) <;> rw [hEq] at hEnc
      · nomatch hEnc
      · have hSvSz : sv.sizeBytes = MirValueCodec.intByteSize w := Nat.eq_of_beq_eq_true hEq
        unfold encodeScalarBytes at hEnc
        rw [hSvSz] at hEnc
        have hBeq0 : Nat.beq (MirValueCodec.intByteSize w) 0 = false :=
          nat_beq_eq_false_of_ne (by have := MirValueCodec.intByteSize_pos w; omega)
        rw [hBeq0] at hEnc
        injection hEnc with hBs
        refine ⟨⟨sv.bits % 2 ^ (8 * MirValueCodec.intByteSize w), Nat.mod_lt _ (Nat.two_pow_pos _)⟩, ?_⟩
        rw [← hBs]
        exact (encodeLittleEndianBytes_mod_two_pow none _ sv.bits).symm
  decode_eq_map := (MirValueCodec.int layouts w 0).decode_eq_map

/--
**Acceptance is fixed by the field kind**: two `TupleFieldCodec`s at the same kind `k` bridge the
same Trusted field decode (`decodeValueFromBytes tupleFieldFuel layouts { kind := k, layoutIdx := 0 }`),
so every window accepted by `c₀` is accepted by `c` (and symmetrically). Choosing a different byte
codec for a tuple field can never add or remove a niche.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem decode_isSome_of_sameKind {layouts : LayoutTable} {k : RigidTy} {α β : Type} {n m : Nat}
    {c₀ : FixedByteCodec α n} {c : FixedByteCodec β m}
    (fc₀ : TupleFieldCodec layouts k c₀) (fc : TupleFieldCodec layouts k c)
    (bs : List AbstractByte) (h₀ : ∃ x, c₀.decode bs = some x) :
    ∃ y, c.decode bs = some y := by
  obtain ⟨x, hx⟩ := h₀
  have hEq := (fc₀.decode_eq_map bs).symm.trans (fc.decode_eq_map bs)
  rw [hx] at hEq
  cases hC : c.decode bs with
  | none =>
    rw [hC] at hEq
    nomatch hEq
  | some y => exact ⟨y, rfl⟩

/--
A `TupleFieldCodec` at a kind that also carries a surjective reference `TupleFieldCodec` is itself
surjective on fully-initialized windows (byte widths agree through `kindSize_eq`).

Kind: helper
Witness: universal
Assumes: S0
-/
theorem isSurjectiveInitDecoder_of_sameKind {layouts : LayoutTable} {k : RigidTy} {α β : Type}
    {n m : Nat} {c₀ : FixedByteCodec α n} {c : FixedByteCodec β m}
    (fc₀ : TupleFieldCodec layouts k c₀) (hSurj₀ : c₀.IsSurjectiveInitDecoder)
    (fc : TupleFieldCodec layouts k c) :
    c.IsSurjectiveInitDecoder := by
  intro bs hLen hInit
  have hNm : m = n := Option.some.inj (fc.kindSize_eq.symm.trans fc₀.kindSize_eq)
  exact decode_isSome_of_sameKind fc₀ fc bs (hSurj₀ bs (hLen.trans hNm) hInit)

/--
Every unsigned-integer tuple field codec is surjective on fully-initialized windows: Trusted's typed
`.uint w` field decode enforces no niche (`TupleFieldCodec.uint` bridges it to `uintBitsLE`).

Kind: helper
Witness: universal
Assumes: S0
-/
theorem uint_isSurjectiveInitDecoder {layouts : LayoutTable} {w : UintTy} {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (fc : TupleFieldCodec layouts (.uint w) c) :
    c.IsSurjectiveInitDecoder :=
  isSurjectiveInitDecoder_of_sameKind (uint layouts w)
    (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder _ (MirValueCodec.uintByteSize_pos w)) fc

/--
Every signed-integer tuple field codec is surjective on fully-initialized windows: Trusted's typed
`.int w` field decode enforces no niche (`TupleFieldCodec.int` bridges it to `uintBitsLE`).

Kind: helper
Witness: universal
Assumes: S0
-/
theorem int_isSurjectiveInitDecoder {layouts : LayoutTable} {w : IntTy} {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (fc : TupleFieldCodec layouts (.int w) c) :
    c.IsSurjectiveInitDecoder :=
  isSurjectiveInitDecoder_of_sameKind (int layouts w)
    (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder _ (MirValueCodec.intByteSize_pos w)) fc

/--
**No niche-enforcing unsigned-integer tuple field**: a `FixedByteCodec.scalarValidRange n hNz range`
whose `range` excludes some `n`-byte bit pattern (e.g. `NonZeroU8` `⟨1, 255⟩`, which excludes `0`)
admits no `TupleFieldCodec` at `.uint w`. Consequently a `scalarValidRange` niche field can never
reach `MirValueCodec.ofPlacedCodecSpine` / `adtOfPlacedCodecSpine` through an integer field kind,
whatever `AdtDecodeFallbackSound` / `FieldLayoutsDecodeSound` proof is available for it. Scalar-niche
newtypes are modeled by `MirValueCodec.scalarNicheNewtypeNonPtr` at `.adt defPath []` instead; the
type-argument path `.adt defPath [.uint w]` is niche-blind as well
(`MirValueCodec.monomorphized_nonZero_u32_forces_hasZeroValid`).

Kind: helper
Witness: negative
Assumes: S0
-/
theorem uint_not_scalarValidRange_of_out_of_range (layouts : LayoutTable) (w : UintTy)
    {n : Nat} (hNz : 0 < n) (range : WrappingRange) {bits : Nat}
    (hLt : bits < 2 ^ (8 * n)) (hOut : wrappingRangeContains range bits = false) :
    ¬ Nonempty (TupleFieldCodec layouts (.uint w) (FixedByteCodec.scalarValidRange n hNz range)) :=
  fun ⟨fc⟩ => nomatch hOut.symm.trans
    (FixedByteCodec.scalarValidRange_contains_of_isSurjectiveInitDecoder
      (uint_isSurjectiveInitDecoder fc) bits hLt)

/--
**No niche-enforcing signed-integer tuple field**: the `.int w` analogue of
`uint_not_scalarValidRange_of_out_of_range` (e.g. `NonZeroI32` excluding `0`).

Kind: helper
Witness: negative
Assumes: S0
-/
theorem int_not_scalarValidRange_of_out_of_range (layouts : LayoutTable) (w : IntTy)
    {n : Nat} (hNz : 0 < n) (range : WrappingRange) {bits : Nat}
    (hLt : bits < 2 ^ (8 * n)) (hOut : wrappingRangeContains range bits = false) :
    ¬ Nonempty (TupleFieldCodec layouts (.int w) (FixedByteCodec.scalarValidRange n hNz range)) :=
  fun ⟨fc⟩ => nomatch hOut.symm.trans
    (FixedByteCodec.scalarValidRange_contains_of_isSurjectiveInitDecoder
      (int_isSurjectiveInitDecoder fc) bits hLt)

/--
No tuple field exists at a kind without a structural byte size (`rigidTyKindByteSize k = none`):
`kindSize_eq` would force `none = some n`.

Kind: helper
Witness: negative
Assumes: S0
-/
theorem not_of_kindSize_none {layouts : LayoutTable} {k : RigidTy}
    (hk : rigidTyKindByteSize k = none) {α : Type} {n : Nat} (c : FixedByteCodec α n) :
    ¬ Nonempty (TupleFieldCodec layouts k c) :=
  fun ⟨fc⟩ => nomatch hk.symm.trans fc.kindSize_eq

/--
**ADT-kind fields have no `TupleFieldCodec`** (`rigidTyKindByteSize (.adt defPath args) = none`), so
`MirValueCodec.ofPlacedCodecSpine` / `adtOfPlacedCodecSpine` cover structs whose fields have
primitive, array, or unit kinds only; nested ADT fields (user structs, `Option<T>`, `NonZero*`) need a
dedicated constructor.

Kind: helper
Witness: negative
Assumes: S0
-/
theorem not_adt (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy)
    {α : Type} {n : Nat} (c : FixedByteCodec α n) :
    ¬ Nonempty (TupleFieldCodec layouts (.adt defPath args) c) :=
  not_of_kindSize_none rfl c

/-- `TupleFieldCodec` for a unit field `()` (`FixedByteCodec.unit`, a 1-ZST). -/
def unit (layouts : LayoutTable) : TupleFieldCodec layouts (.tuple []) FixedByteCodec.unit where
  toValue := fun _ => .unit
  ofValue := fun v =>
    match v with
    | .unit => some ()
    | _ => none
  ofValue_toValue := fun _ => rfl
  kindSize_eq := rfl
  encode_toValue := fun _ => rfl
  encode_witness := fun v bs hEnc => by
    refine ⟨(), ?_⟩
    unfold tupleFieldFuel encodeValueToBytes at hEnc
    cases v <;> dsimp only at hEnc
    case unit =>
      injection hEnc with hBs
      exact hBs.symm
    case scalar => nomatch hEnc
    case ptr => nomatch hEnc
    case aggregate varIdx fs =>
      match varIdx, fs, hEnc with
      | 0, [], hEnc =>
        injection hEnc with hBs
        exact hBs.symm
  decode_eq_map := fun bs => by
    cases bs <;> rfl

/--
Transport a `TupleFieldCodec layouts k c` across a constructive bijection `(toB, ofB)` onto
`FixedByteCodec.mapEquiv c toB ofB hLeft hRight`.
-/
def mapEquiv {layouts : LayoutTable} {k : RigidTy} {α β : Type} {n : Nat}
    {c : FixedByteCodec α n}
    (fc : TupleFieldCodec layouts k c)
    (toB : α → β) (ofB : β → α)
    (hLeft : ∀ a, ofB (toB a) = a)
    (hRight : ∀ b, toB (ofB b) = b) :
    TupleFieldCodec layouts k (FixedByteCodec.mapEquiv c toB ofB hLeft hRight) where
  toValue := fun b => fc.toValue (ofB b)
  ofValue := fun v => (fc.ofValue v).map toB
  ofValue_toValue := fun b => by
    show (fc.ofValue (fc.toValue (ofB b))).map toB = some b
    rw [fc.ofValue_toValue (ofB b)]
    dsimp only [Option.map]
    exact congrArg some (hRight b)
  kindSize_eq := fc.kindSize_eq
  encode_toValue := fun b => fc.encode_toValue (ofB b)
  encode_witness := fun v bs hEnc => by
    obtain ⟨a, ha⟩ := fc.encode_witness v bs hEnc
    refine ⟨toB a, ?_⟩
    show bs = c.encode (ofB (toB a))
    rw [hLeft a]
    exact ha
  decode_eq_map := fun bs => by
    rw [fc.decode_eq_map bs]
    change (c.decode bs).map fc.toValue =
      ((c.decode bs).map toB).map (fun b => fc.toValue (ofB b))
    cases c.decode bs with
    | none => rfl
    | some a =>
      dsimp only [Option.map]
      rw [hLeft a]

/-- `TupleFieldCodec` for a single-byte `u8` field typed directly as `UInt8` (`FixedByteCodec.u8`). -/
def u8 (layouts : LayoutTable) : TupleFieldCodec layouts (.uint .u8) FixedByteCodec.u8 where
  toValue := fun b => .scalar ⟨b.toNat, 1⟩
  ofValue := fun v =>
    match v with
    | .scalar sv =>
      if Nat.beq sv.sizeBytes 1 then some (UInt8.ofNat sv.bits) else none
    | _ => none
  ofValue_toValue := fun b => by
    dsimp only
    exact congrArg some UInt8.ofNat_toNat
  kindSize_eq := rfl
  encode_toValue := fun b => by
    unfold tupleFieldFuel encodeValueToBytes encodeScalarBytes encodeLittleEndianBytes
    dsimp only [intCastTargetBytes]
    rw [UInt8.ofNat_toNat]
    rfl
  encode_witness := fun v bs hEnc => by
    obtain ⟨⟨bits, hLt⟩, hBs⟩ := (uint layouts .u8).encode_witness v bs hEnc
    exact ⟨UInt8.ofNat bits, hBs⟩
  decode_eq_map := fun bs => by
    cases bs with
    | nil => rfl
    | cons b0 rest =>
      cases rest with
      | cons b1 rest' =>
        unfold tupleFieldFuel decodeValueFromBytes
        dsimp only [intCastTargetBytes]
        have hFalse : Nat.beq (Trusted.Sequence.length (b0 :: b1 :: rest')) 1 = false := rfl
        rw [hFalse]
        cases b0 <;> rfl
      | nil =>
        cases b0 with
        | uninit => rfl
        | init b prov => rfl

/-- `TupleFieldCodec` for a `bool` field (`FixedByteCodec.boolByte`, 1 byte, niche `{0, 1}`). -/
def bool (layouts : LayoutTable) : TupleFieldCodec layouts .bool FixedByteCodec.boolByte where
  toValue := (MirValueCodec.bool layouts 0).toValue
  ofValue := (MirValueCodec.bool layouts 0).ofValue
  ofValue_toValue := (MirValueCodec.bool layouts 0).ofValue_toValue
  kindSize_eq := rfl
  encode_toValue := (MirValueCodec.bool layouts 0).encode_toValue
  encode_witness := fun v bs hEnc => by
    unfold tupleFieldFuel encodeValueToBytes at hEnc
    cases v <;> dsimp only at hEnc
    case unit => nomatch hEnc
    case ptr => nomatch hEnc
    case aggregate => nomatch hEnc
    case scalar sv =>
      cases hSz : Nat.beq sv.sizeBytes 1 <;> rw [hSz] at hEnc
      · nomatch hEnc
      · dsimp only at hEnc
        cases h0 : Nat.beq sv.bits 0 <;> rw [h0] at hEnc
        · dsimp only at hEnc
          cases h1 : Nat.beq sv.bits 1 <;> rw [h1] at hEnc
          · nomatch hEnc
          · injection hEnc with hBs
            exact ⟨true, hBs.symm⟩
        · injection hEnc with hBs
          exact ⟨false, hBs.symm⟩
  decode_eq_map := (MirValueCodec.bool layouts 0).decode_eq_map

/-- Extract a fixed-length list of `UInt8` scalars from a list of runtime `Value`s. -/
def u8ArrayDecodeVals : Nat → List Value → Option (List UInt8)
  | 0, [] => some []
  | k + 1, .scalar sv :: vs =>
    if Nat.beq sv.sizeBytes 1 then
      (u8ArrayDecodeVals k vs).map (UInt8.ofNat sv.bits :: ·)
    else none
  | _, _ => none

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem u8ArrayDecodeVals_map_scalar :
    ∀ (k : Nat) (xs : List UInt8),
      xs.length = k →
      u8ArrayDecodeVals k (xs.map fun b : UInt8 => Value.scalar ⟨b.toNat, 1⟩) = some xs
  | 0, [], _ => rfl
  | k + 1, b :: xs, hLen => by
    have hTail : xs.length = k := Nat.succ.inj hLen
    dsimp only [List.map, u8ArrayDecodeVals]
    rw [u8ArrayDecodeVals_map_scalar k xs hTail, UInt8.ofNat_toNat]
    rfl

/--
`TupleFieldCodec` for a fixed-length byte array `[u8; k]` represented as `{ xs : List UInt8 // xs.length = k }`
(`FixedByteCodec.listFixed k FixedByteCodec.u8`), proved via `FixedByteCodec.encodeListWith_map_eq_encodeElems`
and `FixedByteCodec.decodeArrayChunksWith_eq_listFixed_map`.
-/
def u8ListFixed (layouts : LayoutTable) (k : Nat) :
    TupleFieldCodec layouts (.array (.uint .u8) k) (FixedByteCodec.listFixed k FixedByteCodec.u8) where
  toValue := fun xs => .aggregate 0 (xs.val.map fun b => .scalar ⟨b.toNat, 1⟩)
  ofValue := fun v =>
    match v with
    | .aggregate 0 vs =>
      match u8ArrayDecodeVals k vs with
      | some xs =>
        if h : xs.length = k then some ⟨xs, h⟩ else none
      | none => none
    | _ => none
  ofValue_toValue := fun ⟨xs, hLen⟩ => by
    simp only [u8ArrayDecodeVals_map_scalar k xs hLen, hLen, ↓reduceDIte]
  kindSize_eq := by
    show (match rigidTyKindByteSize (.uint .u8) with
      | some elemSz => some (Nat.mul elemSz k)
      | none => none) = some (k * 1)
    have hElem : rigidTyKindByteSize (.uint .u8) = some 1 := rfl
    rw [hElem]
    exact congrArg some (Nat.mul_comm 1 k)
  encode_toValue := fun ⟨xs, hLen⟩ => by
    cases k with
    | zero =>
      cases xs with
      | nil => rfl
      | cons _ _ => nomatch hLen
    | succ k' =>
      have hK0 : Nat.beq (k' + 1) 0 = false := rfl
      unfold tupleFieldFuel encodeValueToBytes
      dsimp only
      rw [hK0]
      simp only []
      have hMapLen : Nat.beq (Trusted.Sequence.length (xs.map fun b : UInt8 => Value.scalar ⟨b.toNat, 1⟩)) (k' + 1) = true := by
        apply Nat.beq_eq.mpr
        show (xs.map _).length = k' + 1
        rw [List.length_map, hLen]
      rw [hMapLen]
      dsimp only [rigidTyKindByteSize, intCastTargetBytes]
      apply FixedByteCodec.encodeListWith_map_eq_encodeElems FixedByteCodec.u8
        (fun b : UInt8 => Value.scalar ⟨b.toNat, 1⟩)
        (fun e => encodeValueToBytes 14 layouts { kind := .uint .u8, layoutIdx := 0 } e)
      intro b
      exact (u8 layouts).encode_toValue b
  encode_witness := fun v bs hEnc => by
    cases k with
    | zero =>
      unfold tupleFieldFuel encodeValueToBytes at hEnc
      cases v <;> dsimp only at hEnc
      case unit =>
        injection hEnc with hBs
        exact ⟨⟨[], rfl⟩, hBs.symm⟩
      case scalar => nomatch hEnc
      case ptr => nomatch hEnc
      case aggregate varIdx vals =>
        cases varIdx with
        | succ _ => nomatch hEnc
        | zero =>
          cases vals with
          | cons _ _ => nomatch hEnc
          | nil =>
            injection hEnc with hBs
            exact ⟨⟨[], rfl⟩, hBs.symm⟩
    | succ k' =>
      have hK0 : Nat.beq (k' + 1) 0 = false := rfl
      unfold tupleFieldFuel encodeValueToBytes at hEnc
      dsimp only at hEnc
      rw [hK0] at hEnc
      cases v <;> dsimp only at hEnc
      case unit => nomatch hEnc
      case scalar => nomatch hEnc
      case ptr => nomatch hEnc
      case aggregate varIdx elems =>
        cases varIdx with
        | succ _ => nomatch hEnc
        | zero =>
          change
            (match Nat.beq (Trusted.Sequence.length elems) (k' + 1) with
             | false => none
             | true =>
               encodeListWith
                 (fun e => encodeValueToBytes 14 layouts { kind := .uint .u8, layoutIdx := 0 } e)
                 1 elems) = some bs at hEnc
          cases hELen : Nat.beq (Trusted.Sequence.length elems) (k' + 1) <;> rw [hELen] at hEnc
          · nomatch hEnc
          · dsimp only at hEnc
            have hListWitness :
                ∀ (es : List Value) (outBs : List AbstractByte),
                  encodeListWith
                    (fun e => encodeValueToBytes 14 layouts { kind := .uint .u8, layoutIdx := 0 } e)
                    1 es = some outBs →
                  ∃ ys : List UInt8,
                    ys.length = es.length ∧ outBs = FixedByteCodec.encodeElems FixedByteCodec.u8 ys := by
              intro es
              induction es with
              | nil =>
                intro outBs hE
                injection hE with hOut
                exact ⟨[], rfl, hOut.symm⟩
              | cons e rest ih =>
                intro outBs hE
                unfold encodeListWith at hE
                cases hHead : encodeValueToBytes 14 layouts { kind := .uint .u8, layoutIdx := 0 } e <;>
                  rw [hHead] at hE
                · nomatch hE
                case some headBs =>
                  dsimp only at hE
                  cases hHeadLen : Nat.beq (Trusted.Sequence.length headBs) 1 <;>
                    rw [hHeadLen] at hE
                  · nomatch hE
                  · dsimp only at hE
                    cases hTail :
                        encodeListWith
                          (fun e => encodeValueToBytes 14 layouts { kind := .uint .u8, layoutIdx := 0 } e)
                          1 rest <;> rw [hTail] at hE
                    · nomatch hE
                    case some tailBs =>
                      injection hE with hOut
                      rw [appendAbstractBytes_eq_append] at hOut
                      obtain ⟨b0, hb0⟩ := (u8 layouts).encode_witness e headBs hHead
                      obtain ⟨ys, hYsLen, hYsBs⟩ := ih tailBs hTail
                      refine ⟨b0 :: ys, congrArg Nat.succ hYsLen, ?_⟩
                      rw [← hOut, hb0, hYsBs]
            obtain ⟨ys, hYsLen, hYsBs⟩ := hListWitness elems bs hEnc
            have hElemsLen : elems.length = k' + 1 := Nat.eq_of_beq_eq_true hELen
            exact ⟨⟨ys, hYsLen.trans hElemsLen⟩, hYsBs⟩
  decode_eq_map := fun bs => by
    cases k with
    | zero =>
      unfold tupleFieldFuel decodeValueFromBytes
      cases bs <;> rfl
    | succ k' =>
      have hK0 : Nat.beq (k' + 1) 0 = false := rfl
      unfold tupleFieldFuel decodeValueFromBytes
      dsimp only
      rw [hK0]
      dsimp only [rigidTyKindByteSize, intCastTargetBytes]
      have hLenDef : Trusted.Sequence.length bs = bs.length := rfl
      have hMul : Nat.mul 1 (k' + 1) = (k' + 1) * 1 := Nat.mul_comm 1 (k' + 1)
      rw [hLenDef, hMul]
      cases hLen : Nat.beq bs.length ((k' + 1) * 1)
      · dsimp only
        have hNe : bs.length ≠ (k' + 1) * 1 := fun hEq => by
          rw [Nat.beq_eq.mpr hEq] at hLen; nomatch hLen
        rw [(FixedByteCodec.listFixed_isExactWidth (k' + 1) FixedByteCodec.u8).decode_eq_none_of_length_ne hNe]
        rfl
      · dsimp only
        have hBridge := FixedByteCodec.decodeArrayChunksWith_eq_listFixed_map FixedByteCodec.u8
          (fun b : UInt8 => Value.scalar ⟨b.toNat, 1⟩)
          (fun chunk => decodeValueFromBytes 14 layouts { kind := .uint .u8, layoutIdx := 0 } chunk)
          (fun chunk => (u8 layouts).decode_eq_map chunk)
          (k' + 1) bs
        rw [hBridge]
        cases (FixedByteCodec.listFixed (k' + 1) FixedByteCodec.u8).decode bs <;> rfl

/--
`TupleFieldCodec` for a fixed-length byte array `[u8; k]` typed as `Vector UInt8 k`
(`FixedByteCodec.array k FixedByteCodec.u8`).
-/
def u8Array (layouts : LayoutTable) (k : Nat) :
    TupleFieldCodec layouts (.array (.uint .u8) k) (FixedByteCodec.array k FixedByteCodec.u8) :=
  mapEquiv (u8ListFixed layouts k)
    (fun xs => Vector.mk xs.val.toArray (by rw [List.size_toArray, xs.property]))
    (fun v => ⟨v.toList, v.length_toList⟩)
    (fun ⟨_, _⟩ => Subtype.ext (by simp [Vector.toList]))
    (fun v => by
      cases v with
      | mk arr hSize =>
        simp [Vector.toList])

/--
Declaration-order `TupleFieldCodecs` for `demoS3Placed` (`struct S { a: u8, b: [u8; 4], c: () }`
at `[.uint .u8, .array (.uint .u8) 4, .tuple []]`).
-/
def demoS3PlacedFieldCodecs (layouts : LayoutTable) :
    TupleFieldCodecs layouts [.uint .u8, .array (.uint .u8) 4, .tuple []] demoS3Placed :=
  .cons (u8 layouts) (.cons (u8Array layouts 4) (.cons (unit layouts) .nil))

end TupleFieldCodec

namespace MirValueCodec

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem tuple_cons_rigidTyByteSize {layouts : LayoutTable} {idx : LayoutIdx} {l : TypeLayout}
    {k : RigidTy} {ks : List RigidTy} {totalSize : Nat}
    (hLookup : LayoutTable.lookup layouts idx = some l) (hSize : l.size = { bytes := totalSize }) :
    rigidTyByteSize layouts { kind := .tuple (k :: ks), layoutIdx := idx } = some totalSize := by
  unfold rigidTyByteSize
  dsimp only [rigidTyKindByteSize]
  rw [hLookup]
  dsimp only
  rw [hSize]

/--
Trusted encodes the laid-out tuple value `.aggregate 0 (fcs.toValues x)` to the realized codec's
encoding of `x`.

Kind: refinement
Witness: universal
Assumes: S0
Subject: encodeValueToBytes
-/
theorem ofPlacedCodecSpine_encode_toValue
    {layouts : LayoutTable} {idx : LayoutIdx} {l : TypeLayout} {memoryIndex : List Nat}
    {k : RigidTy} {ks : List RigidTy} {αs : List Type} {pc : PlacedCodecSpine αs} {totalSize : Nat}
    (fcs : TupleFieldCodecs layouts (k :: ks) pc)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size = { bytes := totalSize })
    (hFields : l.fields = .arbitrary (pc.placed.map fun p => ({ bytes := p.1 } : Size)) memoryIndex)
    (hSeq : SequentialFieldPlacement 0 (pc.memSort.placed.map Prod.snd)
      (pc.memSort.placed.map Prod.fst) totalSize)
    (x : FieldTuple αs) :
    encodeValueToBytes defaultCodecFuel layouts { kind := .tuple (k :: ks), layoutIdx := idx }
        (.aggregate 0 (fcs.toValues x)) =
      some ((pc.realizedCodec totalSize).encode x) := by
  unfold defaultCodecFuel encodeValueToBytes
  simp only []
  have hLen1 : Nat.beq (Trusted.Sequence.length (fcs.toValues x))
      (Trusted.Sequence.length (k :: ks)) = true :=
    Nat.beq_eq.mpr (fcs.length_toValues x)
  rw [hLen1]
  dsimp only
  rw [hLookup]
  dsimp only
  rw [hFields]
  dsimp only
  have hLen2 : Nat.beq (Trusted.Sequence.length (pc.placed.map fun p => ({ bytes := p.1 } : Size)))
      (Trusted.Sequence.length (fcs.toValues x)) = true := by
    apply Nat.beq_eq.mpr
    show (pc.placed.map fun p => ({ bytes := p.1 } : Size)).length = (fcs.toValues x).length
    rw [List.length_map, fcs.length_placed, fcs.length_toValues]
  rw [hLen2]
  dsimp only
  rw [hSize]
  exact (fcs.encodeFieldsAtOffsetsWith_eq_writeWindows _ x _).trans
    (pc.writeWindows_realizedCodec_encode totalSize hSeq x)

/--
Every successful Trusted encoding of the laid-out tuple type is a realized-codec encoding.

Kind: refinement
Witness: universal
Assumes: S0
Subject: PlacedCodecSpine.realizedCodec
-/
theorem ofPlacedCodecSpine_encode_witness
    {layouts : LayoutTable} {idx : LayoutIdx} {l : TypeLayout} {memoryIndex : List Nat}
    {k : RigidTy} {ks : List RigidTy} {αs : List Type} {pc : PlacedCodecSpine αs} {totalSize : Nat}
    (fcs : TupleFieldCodecs layouts (k :: ks) pc)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size = { bytes := totalSize })
    (hFields : l.fields = .arbitrary (pc.placed.map fun p => ({ bytes := p.1 } : Size)) memoryIndex)
    (hSeq : SequentialFieldPlacement 0 (pc.memSort.placed.map Prod.snd)
      (pc.memSort.placed.map Prod.fst) totalSize)
    (v : Value) (bs : List AbstractByte)
    (hEnc : encodeValueToBytes defaultCodecFuel layouts
      { kind := .tuple (k :: ks), layoutIdx := idx } v = some bs) :
    ∃ x : FieldTuple αs, bs = (pc.realizedCodec totalSize).encode x := by
  unfold defaultCodecFuel encodeValueToBytes at hEnc
  cases v <;> dsimp only at hEnc
  case unit => nomatch hEnc
  case scalar => nomatch hEnc
  case ptr => nomatch hEnc
  case aggregate varIdx vals =>
    cases varIdx with
    | succ _ => nomatch hEnc
    | zero =>
      simp only [] at hEnc
      cases hL : Nat.beq (Trusted.Sequence.length vals) (Trusted.Sequence.length (k :: ks)) with
      | false =>
        rw [hL] at hEnc
        nomatch hEnc
      | true =>
        rw [hL] at hEnc
        dsimp only at hEnc
        rw [hLookup] at hEnc
        dsimp only at hEnc
        rw [hFields] at hEnc
        dsimp only at hEnc
        have hValsLen : vals.length = (k :: ks).length := Nat.eq_of_beq_eq_true hL
        have hLen2 : Nat.beq
            (Trusted.Sequence.length (pc.placed.map fun p => ({ bytes := p.1 } : Size)))
            (Trusted.Sequence.length vals) = true := by
          apply Nat.beq_eq.mpr
          show (pc.placed.map fun p => ({ bytes := p.1 } : Size)).length = vals.length
          rw [List.length_map, fcs.length_placed, hValsLen]
        rw [hLen2] at hEnc
        dsimp only at hEnc
        rw [hSize] at hEnc
        obtain ⟨x, hx⟩ := fcs.encodeFieldsAtOffsetsWith_witness _ vals _ bs hEnc
        rw [pc.writeWindows_realizedCodec_encode totalSize hSeq x] at hx
        injection hx with hx
        exact ⟨x, hx.symm⟩

/--
Trusted decodes the laid-out tuple type exactly as the realized codec (padding bytes ignored).

Kind: refinement
Witness: universal
Assumes: S0
Subject: decodeValueFromBytes
-/
theorem ofPlacedCodecSpine_decode_eq_map
    {layouts : LayoutTable} {idx : LayoutIdx} {l : TypeLayout} {memoryIndex : List Nat}
    {k : RigidTy} {ks : List RigidTy} {αs : List Type} {pc : PlacedCodecSpine αs} {totalSize : Nat}
    (fcs : TupleFieldCodecs layouts (k :: ks) pc)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size = { bytes := totalSize })
    (hFields : l.fields = .arbitrary (pc.placed.map fun p => ({ bytes := p.1 } : Size)) memoryIndex)
    (hSeq : SequentialFieldPlacement 0 (pc.memSort.placed.map Prod.snd)
      (pc.memSort.placed.map Prod.fst) totalSize)
    (bs : List AbstractByte) :
    decodeValueFromBytes defaultCodecFuel layouts { kind := .tuple (k :: ks), layoutIdx := idx } bs =
      ((pc.realizedCodec totalSize).decode bs).map (fun x => .aggregate 0 (fcs.toValues x)) := by
  have hWidth := (pc.realized_offsets_and_width_of_sequential totalSize hSeq).2
  unfold defaultCodecFuel decodeValueFromBytes
  dsimp only
  rw [hLookup]
  dsimp only
  rw [hSize]
  dsimp only
  cases hL : Nat.beq (Trusted.Sequence.length bs) totalSize with
  | false =>
    have hNe : bs.length ≠ pc.realizedWidth totalSize := by
      rw [hWidth]
      intro hEq
      rw [show Trusted.Sequence.length bs = bs.length from rfl, Nat.beq_eq.mpr hEq] at hL
      nomatch hL
    rw [(pc.realizedCodec_isExactWidth totalSize).decode_eq_none_of_length_ne hNe]
    rfl
  | true =>
    have hLen : bs.length = totalSize := Nat.eq_of_beq_eq_true hL
    dsimp only
    rw [hFields]
    dsimp only
    rw [fcs.decodeFieldsAtOffsetsWith_eq_decodeAt bs (by
        rw [hLen]
        exact pc.placed_in_bounds_of_memSort_sequential totalSize hSeq),
      pc.realizedCodec_decode_eq_decodeAt totalSize hSeq bs hLen]
    cases pc.decodeAt bs <;> rfl

/--
**General $k$-Field Laid-Out Tuple `MirValueCodec`** (generalizing `uintPairArbitraryTuple` to any
number of fields, any field memory order, zero-sized fields, and arbitrary leading/inter-field/
trailing padding): from a concrete `LayoutTable` entry `l` for the tuple type (`hLookup`, `hSize`,
and `hFields` giving the declaration-order `FieldsShape.arbitrary` offsets of `pc`), per-field
Trusted bridges `fcs`, and a sequential memory-order placement of those offsets within `l.size`
(`hSeq`, which every `ValidStructLayoutWorld` provides), this *derives* — rather than assumes —
the agreement of Trusted's `encodeValueToBytes` / `decodeValueFromBytes` with the computable
`pc.realizedCodec totalSize`.
-/
def ofPlacedCodecSpine
    (layouts : LayoutTable) (idx : LayoutIdx) (l : TypeLayout) (memoryIndex : List Nat)
    {k : RigidTy} {ks : List RigidTy} {αs : List Type} (pc : PlacedCodecSpine αs) (totalSize : Nat)
    (fcs : TupleFieldCodecs layouts (k :: ks) pc)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size = { bytes := totalSize })
    (hFields : l.fields = .arbitrary (pc.placed.map fun p => ({ bytes := p.1 } : Size)) memoryIndex)
    (hSeq : SequentialFieldPlacement 0 (pc.memSort.placed.map Prod.snd)
      (pc.memSort.placed.map Prod.fst) totalSize) :
    MirValueCodec layouts { kind := .tuple (k :: ks), layoutIdx := idx } (FieldTuple αs) totalSize :=
  ofCanonicalEncode
    ((pc.realizedCodec totalSize).castWidth
      (pc.realized_offsets_and_width_of_sequential totalSize hSeq).2)
    (fun x => .aggregate 0 (fcs.toValues x))
    (fun v =>
      match v with
      | .aggregate 0 vs => fcs.ofValues vs
      | _ => none)
    (fun x => fcs.ofValues_toValues x)
    (tuple_cons_rigidTyByteSize hLookup hSize)
    (fun x => ofPlacedCodecSpine_encode_toValue fcs hLookup hSize hFields hSeq x)
    (fun v bs hEnc => ofPlacedCodecSpine_encode_witness fcs hLookup hSize hFields hSeq v bs hEnc)
    (fun bs => ofPlacedCodecSpine_decode_eq_map fcs hLookup hSize hFields hSeq bs)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem adt_cons_rigidTyByteSize {layouts : LayoutTable} {defPath : DefPath} {idx : LayoutIdx}
    {l : TypeLayout} {k : RigidTy} {ks : List RigidTy} {totalSize : Nat}
    (hLookup : LayoutTable.lookup layouts idx = some l) (hSize : l.size = { bytes := totalSize }) :
    rigidTyByteSize layouts { kind := .adt defPath (k :: ks), layoutIdx := idx } = some totalSize := by
  unfold rigidTyByteSize
  dsimp only [rigidTyKindByteSize]
  rw [hLookup]
  dsimp only
  rw [hSize]

/--
Trusted's single-variant `.adt` fallback decoder on a `LayoutTable` entry `l` with field offsets
`offsets`: used by `decodeValueFromBytes` only if the primary `byArgs` field decode returns `none`.
-/
def adtDecodeFallback (layouts : LayoutTable) (l : TypeLayout) (varIdx : VariantIdx)
    (offsets : List Size) (bs : List AbstractByte) : Option Value :=
  match Nat.beq (Trusted.Sequence.length l.fieldLayouts) (Trusted.Sequence.length offsets) with
  | true =>
    let decodeByLayout := fun (fIdx : Nat) (fSlice : List AbstractByte) =>
      decodeValueFromBytes tupleFieldFuel layouts { kind := .adt "" .nil, layoutIdx := fIdx } fSlice
    match decodeFieldsByLayoutIdxs decodeByLayout layouts bs offsets l.fieldLayouts with
    | .some vals => .some (.aggregate varIdx vals)
    | .none => .none
  | false =>
    match offsets, l.backendRepr with
    | off0 :: .nil, .scalar s0 =>
      match scalarLayoutByteWidth s0 with
      | .none => .none
      | .some sz0 =>
        match sliceAbstractBytes bs off0.bytes sz0 with
        | .none => .none
        | .some slice0 =>
          match decodeScalarLayoutBytes s0 slice0 with
          | .some v0 => .some (.aggregate varIdx (v0 :: .nil))
          | .none => .none
    | off0 :: off1 :: .nil, .scalarPair s0 s1 =>
      match scalarLayoutByteWidth s0, scalarLayoutByteWidth s1 with
      | .some sz0, .some sz1 =>
        match sliceAbstractBytes bs off0.bytes sz0, sliceAbstractBytes bs off1.bytes sz1 with
        | .some slice0, .some slice1 =>
          match decodeScalarLayoutBytes s0 slice0, decodeScalarLayoutBytes s1 slice1 with
          | .some v0, .some v1 => .some (.aggregate varIdx (v0 :: v1 :: .nil))
          | _, _ => .none
        | _, _ => .none
      | _, _ => .none
    | _, _ =>
      match decodeFieldsBySpan bs l.size.bytes offsets with
      | .some vals => .some (.aggregate varIdx vals)
      | .none => .none

/--
Predicate stating that `adtDecodeFallback` returns `none` on every `totalSize`-byte buffer, so
Trusted's `decodeValueFromBytes` on `.adt defPath (k :: ks)` reduces purely to `byArgs`
(`decodeFieldsAtOffsetsWith` over `k :: ks`).
-/
def AdtDecodeFallbackNone (layouts : LayoutTable) (l : TypeLayout) (varIdx : VariantIdx)
    (offsets : List Size) (totalSize : Nat) : Prop :=
  ∀ bs : List AbstractByte, bs.length = totalSize →
    adtDecodeFallback layouts l varIdx offsets bs = none

/--
Sufficient condition 1 for `AdtDecodeFallbackNone`: `l.fieldLayouts` has length matching `offsets = off₀ :: offRest`
with an unmapped sentinel head layout index `LayoutTable.lookup layouts fIdx₀ = none`.
-/
theorem AdtDecodeFallbackNone.of_sentinel_fieldLayouts
    {layouts : LayoutTable} {l : TypeLayout} {varIdx : VariantIdx}
    {off₀ : Size} {offRest : List Size}
    {fIdx₀ : LayoutIdx} {fIdxRest : List LayoutIdx} {totalSize : Nat}
    (hFl : l.fieldLayouts = fIdx₀ :: fIdxRest)
    (hLen : (fIdx₀ :: fIdxRest).length = (off₀ :: offRest).length)
    (hLookup₀ : LayoutTable.lookup layouts fIdx₀ = none) :
    AdtDecodeFallbackNone layouts l varIdx (off₀ :: offRest) totalSize := by
  intro bs _
  unfold adtDecodeFallback
  have hBeq : Nat.beq (Trusted.Sequence.length l.fieldLayouts)
      (Trusted.Sequence.length (off₀ :: offRest)) = true := by
    rw [hFl]
    exact Nat.beq_eq.mpr hLen
  rw [hBeq]
  dsimp only
  rw [hFl]
  dsimp only [decodeFieldsByLayoutIdxs]
  rw [hLookup₀]

/--
Sufficient condition 2 for `AdtDecodeFallbackNone`: `l.fieldLayouts = []`, `l.backendRepr = .memory`,
and the first two declared fields are reordered in memory (`off₁.bytes < off₀.bytes`, so
`Nat.ble off₀.bytes off₁.bytes = false` and Trusted's span decoder rejects the offsets). This covers
reordered entries without `fieldLayouts`, such as `demoS3Placed`
(`struct S { a: u8 @ 4, b: [u8; 4] @ 0, c: () @ 5 }`) at `u8u32UnitPermutedLayout`; it never holds for
in-order structs (see `AdtDecodeFallbackSound.of_memory_surjective` for those).
-/
theorem AdtDecodeFallbackNone.of_reordered_head
    {layouts : LayoutTable} {l : TypeLayout} {varIdx : VariantIdx}
    {off₀ off₁ : Size} {offRest : List Size} {totalSize : Nat}
    (hFl : l.fieldLayouts = [])
    (hRepr : l.backendRepr = .memory)
    (hReord : off₁.bytes < off₀.bytes) :
    AdtDecodeFallbackNone layouts l varIdx (off₀ :: off₁ :: offRest) totalSize := by
  intro bs _
  unfold adtDecodeFallback
  rw [hFl, hRepr]
  have hBle : Nat.ble off₀.bytes off₁.bytes = false := by
    cases h : Nat.ble off₀.bytes off₁.bytes with
    | false => rfl
    | true =>
      have hLe : off₀.bytes ≤ off₁.bytes := Nat.le_of_ble_eq_true h
      omega
  cases offRest <;> dsimp only [decodeFieldsBySpan] <;> rw [hBle] <;> rfl

/--
Precise fallback condition for single-variant `.adt` decoding: on every `totalSize`-byte buffer whose
declaration-order field windows do **not** all decode (so Trusted's primary `byArgs` decoder fails),
Trusted's fallback decoder `adtDecodeFallback` fails too. Implied by `AdtDecodeFallbackNone`
(`AdtDecodeFallbackNone.toSound`) and, for `.memory` layouts without `fieldLayouts`, by surjective
field codecs (`AdtDecodeFallbackSound.of_memory_surjective`), which covers in-order structs.
-/
def AdtDecodeFallbackSound (layouts : LayoutTable) (l : TypeLayout) (varIdx : VariantIdx)
    {αs : List Type} (pc : PlacedCodecSpine αs) (totalSize : Nat) : Prop :=
  ∀ bs : List AbstractByte, bs.length = totalSize → pc.decodeAt bs = none →
    adtDecodeFallback layouts l varIdx (pc.placed.map fun p => ({ bytes := p.1 } : Size)) bs = none

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem AdtDecodeFallbackNone.toSound {layouts : LayoutTable} {l : TypeLayout} {varIdx : VariantIdx}
    {αs : List Type} {pc : PlacedCodecSpine αs} {totalSize : Nat}
    (h : AdtDecodeFallbackNone layouts l varIdx (pc.placed.map fun p => ({ bytes := p.1 } : Size))
      totalSize) :
    AdtDecodeFallbackSound layouts l varIdx pc totalSize :=
  fun bs hLen _ => h bs hLen

/--
For a `.memory` layout without `fieldLayouts`, Trusted's single-variant fallback decoder is the
padding-inclusive span decoder `decodeFieldsBySpan`.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem adtDecodeFallback_eq_span {layouts : LayoutTable} {l : TypeLayout} {varIdx : VariantIdx}
    {bs : List AbstractByte} (hFl : l.fieldLayouts = []) (hRepr : l.backendRepr = .memory) :
    ∀ (offsets : List Size), offsets ≠ [] →
      adtDecodeFallback layouts l varIdx offsets bs =
        (decodeFieldsBySpan bs l.size.bytes offsets).map (fun vals => .aggregate varIdx vals)
  | [], h => absurd rfl h
  | [o], _ => by
    unfold adtDecodeFallback
    rw [hFl, hRepr]
    cases decodeFieldsBySpan bs l.size.bytes [o] <;> rfl
  | [o₁, o₂], _ => by
    unfold adtDecodeFallback
    rw [hFl, hRepr]
    cases decodeFieldsBySpan bs l.size.bytes [o₁, o₂] <;> rfl
  | o₁ :: o₂ :: o₃ :: rest, _ => by
    unfold adtDecodeFallback
    rw [hFl, hRepr]
    cases decodeFieldsBySpan bs l.size.bytes (o₁ :: o₂ :: o₃ :: rest) <;> rfl

/--
Whether Trusted's single-variant fallback decoder (for an entry without `fieldLayouts`) uses the
padding-inclusive span decoder `decodeFieldsBySpan` on these field offsets and backend representation:
every shape except a 1-field `.scalar` struct and a 2-field `.scalarPair` struct, including `.scalar`
structs with zero-sized marker fields (`struct W(u32, PhantomData<T>)`) and `.memory` structs.
-/
def usesSpanFallback : List Size → BackendRepr → Bool
  | [_], .scalar _ => false
  | [_, _], .scalarPair _ _ => false
  | _, _ => true

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem usesSpanFallback_memory : ∀ (offsets : List Size), usesSpanFallback offsets .memory = true
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: _ => rfl

/--
For an entry without `fieldLayouts` whose shape uses the span fallback, Trusted's single-variant
fallback decoder is `decodeFieldsBySpan`.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem adtDecodeFallback_eq_span_of_usesSpanFallback {layouts : LayoutTable} {l : TypeLayout}
    {varIdx : VariantIdx} {bs : List AbstractByte} (hFl : l.fieldLayouts = []) :
    ∀ (offsets : List Size), offsets ≠ [] → usesSpanFallback offsets l.backendRepr = true →
      adtDecodeFallback layouts l varIdx offsets bs =
        (decodeFieldsBySpan bs l.size.bytes offsets).map (fun vals => .aggregate varIdx vals)
  | [], h, _ => absurd rfl h
  | [o], _, hSpan => by
    unfold adtDecodeFallback
    rw [hFl]
    cases hR : l.backendRepr with
    | scalar s0 =>
      rw [hR] at hSpan
      nomatch hSpan
    | scalarPair s0 s1 =>
      cases decodeFieldsBySpan bs l.size.bytes [o] <;> rfl
    | memory =>
      cases decodeFieldsBySpan bs l.size.bytes [o] <;> rfl
  | [o₁, o₂], _, hSpan => by
    unfold adtDecodeFallback
    rw [hFl]
    cases hR : l.backendRepr with
    | scalar s0 =>
      cases decodeFieldsBySpan bs l.size.bytes [o₁, o₂] <;> rfl
    | scalarPair s0 s1 =>
      rw [hR] at hSpan
      nomatch hSpan
    | memory =>
      cases decodeFieldsBySpan bs l.size.bytes [o₁, o₂] <;> rfl
  | o₁ :: o₂ :: o₃ :: rest, _, _ => by
    unfold adtDecodeFallback
    rw [hFl]
    cases l.backendRepr <;>
      cases decodeFieldsBySpan bs l.size.bytes (o₁ :: o₂ :: o₃ :: rest) <;> rfl

/--
**Fallback Soundness for Span-Fallback Structs With Surjective Field Codecs** (in-order *or*
reordered; `.memory` structs and `.scalar` / `.scalarPair` structs whose field count makes Trusted fall
back to the span decoder, such as `struct W(u32, PhantomData<T>)`): when `l.fieldLayouts = []`, the span
decoder succeeds only if every byte from the first offset to `totalSize` is initialized; then every
field window is initialized, so surjective field codecs make the primary window decode succeed.

Kind: refinement
Witness: universal
Assumes: S0
Subject: AdtDecodeFallbackSound
-/
theorem AdtDecodeFallbackSound.of_span_surjective
    {layouts : LayoutTable} {l : TypeLayout} {varIdx : VariantIdx}
    {α : Type} {αs : List Type} {p₀ : Nat × FieldLayout} {c₀ : FixedByteCodec α p₀.2.size}
    {tail : PlacedCodecSpine αs} {totalSize : Nat}
    (hFl : l.fieldLayouts = [])
    (hSpan : usesSpanFallback
      ((PlacedCodecSpine.cons p₀ c₀ tail).placed.map fun p => ({ bytes := p.1 } : Size))
      l.backendRepr = true)
    (hSize : l.size = { bytes := totalSize })
    (hSurj : (PlacedCodecSpine.cons p₀ c₀ tail).AllFieldsSurjective)
    (hIn : ∀ p ∈ (PlacedCodecSpine.cons p₀ c₀ tail).placed, p.1 + p.2.size ≤ totalSize) :
    AdtDecodeFallbackSound layouts l varIdx (PlacedCodecSpine.cons p₀ c₀ tail) totalSize := by
  intro bs hLen hNone
  show adtDecodeFallback layouts l varIdx
    (({ bytes := p₀.1 } : Size) :: tail.placed.map fun p => ({ bytes := p.1 } : Size)) bs = none
  rw [adtDecodeFallback_eq_span_of_usesSpanFallback hFl _ (List.cons_ne_nil _ _) hSpan, hSize]
  dsimp only
  cases hSpanDec : decodeFieldsBySpan bs totalSize
      (({ bytes := p₀.1 } : Size) :: tail.placed.map fun p => ({ bytes := p.1 } : Size)) with
  | none => rfl
  | some vs =>
    exfalso
    obtain ⟨hHeadLe, hInitAll⟩ := decodeFieldsBySpan_some_initAt bs totalSize _ vs hSpanDec
    obtain ⟨x, hx⟩ := (PlacedCodecSpine.cons p₀ c₀ tail).decodeAt_isSome_of_initAt bs hSurj
      (fun p hp => by rw [hLen]; exact hIn p hp)
      (fun p hp j hj₁ hj₂ => by
        have hMem : ({ bytes := p.1 } : Size) ∈
            (({ bytes := p₀.1 } : Size) :: tail.placed.map fun p => ({ bytes := p.1 } : Size)) :=
          List.mem_map_of_mem (f := fun p : Nat × FieldLayout => ({ bytes := p.1 } : Size)) hp
        exact hInitAll j (Nat.le_trans (hHeadLe _ hMem) hj₁)
          (Nat.lt_of_lt_of_le hj₂ (hIn p hp)))
    rw [hNone] at hx
    nomatch hx

/--
**Fallback Soundness for `.memory` Structs With Surjective Field Codecs** (in-order *or* reordered):
when `l.fieldLayouts = []` and `l.backendRepr = .memory`, Trusted's fallback is the span decoder,
which succeeds only if every byte from the first offset to `totalSize` is initialized; then every
field window is initialized, so surjective field codecs make the primary window decode succeed.
Hence the fallback can only run where it fails.

Kind: refinement
Witness: universal
Assumes: S0
Subject: AdtDecodeFallbackSound
-/
theorem AdtDecodeFallbackSound.of_memory_surjective
    {layouts : LayoutTable} {l : TypeLayout} {varIdx : VariantIdx}
    {α : Type} {αs : List Type} {p₀ : Nat × FieldLayout} {c₀ : FixedByteCodec α p₀.2.size}
    {tail : PlacedCodecSpine αs} {totalSize : Nat}
    (hFl : l.fieldLayouts = []) (hRepr : l.backendRepr = .memory)
    (hSize : l.size = { bytes := totalSize })
    (hSurj : (PlacedCodecSpine.cons p₀ c₀ tail).AllFieldsSurjective)
    (hIn : ∀ p ∈ (PlacedCodecSpine.cons p₀ c₀ tail).placed, p.1 + p.2.size ≤ totalSize) :
    AdtDecodeFallbackSound layouts l varIdx (PlacedCodecSpine.cons p₀ c₀ tail) totalSize :=
  AdtDecodeFallbackSound.of_span_surjective hFl (by rw [hRepr]; exact usesSpanFallback_memory _)
    hSize hSurj hIn

/--
**Fallback Soundness for 1-Field `.scalar` Structs** whose field codec accepts every slice that the
struct's scalar layout accepts (`hAccept0`): covers niche newtypes such as `struct B(bool)` whose
`.scalar` valid range is enforced by the fallback, not only surjective codecs.

Kind: refinement
Witness: universal
Assumes: S0
Subject: AdtDecodeFallbackSound
-/
theorem AdtDecodeFallbackSound.of_scalar
    {layouts : LayoutTable} {l : TypeLayout} {varIdx : VariantIdx}
    {α : Type} {p₀ : Nat × FieldLayout} {c₀ : FixedByteCodec α p₀.2.size}
    {s0 : ScalarLayout} {totalSize : Nat}
    (hFl : l.fieldLayouts = []) (hRepr : l.backendRepr = .scalar s0)
    (hWidth0 : scalarLayoutByteWidth s0 = some p₀.2.size)
    (hAccept0 : ∀ slice : List AbstractByte, slice.length = p₀.2.size →
      (∃ v, decodeScalarLayoutBytes s0 slice = some v) → ∃ a, c₀.decode slice = some a) :
    AdtDecodeFallbackSound layouts l varIdx (.cons p₀ c₀ .nil) totalSize := by
  intro bs _ hNone
  unfold adtDecodeFallback
  rw [hFl, hRepr]
  dsimp only [PlacedCodecSpine.placed, List.map]
  rw [hWidth0]
  dsimp only
  cases hSl : sliceAbstractBytes bs p₀.1 p₀.2.size with
  | none => rfl
  | some slice0 =>
    dsimp only
    cases hSc : decodeScalarLayoutBytes s0 slice0 with
    | none => rfl
    | some v0 =>
      exfalso
      obtain ⟨hEq, hLen⟩ := sliceAbstractBytes_some_eq_drop_take_and_len hSl
      obtain ⟨a₀, ha₀⟩ := hAccept0 slice0 hLen ⟨v0, hSc⟩
      rw [hEq] at ha₀
      unfold PlacedCodecSpine.decodeAt at hNone
      rw [ha₀] at hNone
      nomatch hNone

/--
**Fallback Soundness for 2-Field `.scalarPair` Structs** whose field codecs accept every slice that
the corresponding scalar layouts accept (in-order *or* reordered).

Kind: refinement
Witness: universal
Assumes: S0
Subject: AdtDecodeFallbackSound
-/
theorem AdtDecodeFallbackSound.of_scalarPair
    {layouts : LayoutTable} {l : TypeLayout} {varIdx : VariantIdx}
    {α₀ α₁ : Type} {p₀ p₁ : Nat × FieldLayout}
    {c₀ : FixedByteCodec α₀ p₀.2.size} {c₁ : FixedByteCodec α₁ p₁.2.size}
    {s0 s1 : ScalarLayout} {totalSize : Nat}
    (hFl : l.fieldLayouts = []) (hRepr : l.backendRepr = .scalarPair s0 s1)
    (hWidth0 : scalarLayoutByteWidth s0 = some p₀.2.size)
    (hWidth1 : scalarLayoutByteWidth s1 = some p₁.2.size)
    (hAccept0 : ∀ slice : List AbstractByte, slice.length = p₀.2.size →
      (∃ v, decodeScalarLayoutBytes s0 slice = some v) → ∃ a, c₀.decode slice = some a)
    (hAccept1 : ∀ slice : List AbstractByte, slice.length = p₁.2.size →
      (∃ v, decodeScalarLayoutBytes s1 slice = some v) → ∃ a, c₁.decode slice = some a) :
    AdtDecodeFallbackSound layouts l varIdx (.cons p₀ c₀ (.cons p₁ c₁ .nil)) totalSize := by
  intro bs _ hNone
  unfold adtDecodeFallback
  rw [hFl, hRepr]
  dsimp only [PlacedCodecSpine.placed, List.map]
  rw [hWidth0, hWidth1]
  dsimp only
  cases hSl0 : sliceAbstractBytes bs p₀.1 p₀.2.size with
  | none => rfl
  | some slice0 =>
    cases hSl1 : sliceAbstractBytes bs p₁.1 p₁.2.size with
    | none => rfl
    | some slice1 =>
      dsimp only
      cases hSc0 : decodeScalarLayoutBytes s0 slice0 with
      | none => rfl
      | some v0 =>
        cases hSc1 : decodeScalarLayoutBytes s1 slice1 with
        | none => rfl
        | some v1 =>
          exfalso
          obtain ⟨hEq0, hLen0⟩ := sliceAbstractBytes_some_eq_drop_take_and_len hSl0
          obtain ⟨hEq1, hLen1⟩ := sliceAbstractBytes_some_eq_drop_take_and_len hSl1
          obtain ⟨a₀, ha₀⟩ := hAccept0 slice0 hLen0 ⟨v0, hSc0⟩
          obtain ⟨a₁, ha₁⟩ := hAccept1 slice1 hLen1 ⟨v1, hSc1⟩
          rw [hEq0] at ha₀
          rw [hEq1] at ha₁
          unfold PlacedCodecSpine.decodeAt at hNone
          rw [ha₀] at hNone
          unfold PlacedCodecSpine.decodeAt at hNone
          rw [ha₁] at hNone
          nomatch hNone

/--
Every slice accepted by `bool`'s scalar niche layout (`u8` with valid range `0 ..= 1`) is accepted by
`FixedByteCodec.boolByte`.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem boolByte_decode_isSome_of_decodeScalarLayoutBytes (slice : List AbstractByte)
    (h : ∃ v, decodeScalarLayoutBytes (.initialized (.int 8 false) ⟨0, 1⟩) slice = some v) :
    ∃ b, FixedByteCodec.boolByte.decode slice = some b := by
  obtain ⟨v, hDec⟩ := h
  match slice, hDec with
  | [], hDec => nomatch hDec
  | [.uninit], hDec => nomatch hDec
  | .init b prov :: _ :: _, hDec => nomatch hDec
  | [.init b prov], hDec =>
    unfold decodeScalarLayoutBytes decodeScalarBytes decodeLittleEndianBytes
      wrappingRangeContains at hDec
    dsimp only [scalarLayoutByteWidth, primitiveKindByteWidth] at hDec
    cases h0 : Nat.beq b.toBitVec.toNat 0
    · cases h1 : Nat.beq b.toBitVec.toNat 1
      · have hNe0 : b.toBitVec.toNat ≠ 0 := fun h => by
          rw [Nat.beq_eq.mpr h] at h0; nomatch h0
        have hNe1 : b.toBitVec.toNat ≠ 1 := fun h => by
          rw [Nat.beq_eq.mpr h] at h1; nomatch h1
        have hBle1 : Nat.ble (b.toBitVec.toNat + 256 * 0) 1 = false := by
          cases hB : Nat.ble (b.toBitVec.toNat + 256 * 0) 1 with
          | false => rfl
          | true =>
            have hLe := Nat.le_of_ble_eq_true hB
            have hLe' : b.toBitVec.toNat ≤ 1 := by
              rw [Nat.mul_zero, Nat.add_zero] at hLe
              exact hLe
            rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hLe' with h' | h'
            · exact absurd h' hNe0
            · exact absurd h' hNe1
        change (match Bool.and (Nat.ble 0 (b.toBitVec.toNat + 256 * 0))
            (Nat.ble (b.toBitVec.toNat + 256 * 0) 1) with
          | false => none
          | true => some (Value.scalar ⟨b.toBitVec.toNat + 256 * 0, 1⟩)) = some v at hDec
        rw [hBle1, Bool.and_false] at hDec
        nomatch hDec
      · refine ⟨true, ?_⟩
        show (match Nat.beq b.toBitVec.toNat 0 with
          | true => some false
          | false =>
            match Nat.beq b.toBitVec.toNat 1 with
            | true => some true
            | false => none) = some true
        rw [h0, h1]
    · refine ⟨false, ?_⟩
      show (match Nat.beq b.toBitVec.toNat 0 with
        | true => some false
        | false =>
          match Nat.beq b.toBitVec.toNat 1 with
          | true => some true
          | false => none) = some false
      rw [h0]

/--
Every slice accepted by any non-pointer scalar layout `.initialized pk range`
(`pk = .int bitsWidth signed` or `.float bitsWidth`) of byte width `sz` is accepted by
`FixedByteCodec.scalarValidRange sz hNz range`. Generalizes
`boolByte_decode_isSome_of_decodeScalarLayoutBytes` from `bool` (`range = ⟨0, 1⟩`) to all integer
and float scalar niches (such as `NonZeroU8` `1 ..= 255` or `NonZeroU32` `1 ..= 2^32 - 1`),
discharging the `hAccept` obligation of `AdtDecodeFallbackSound.of_scalar`,
`AdtDecodeFallbackSound.of_scalarPair`, and `FieldLayoutsDecodeSound.cons_primitive_scalar`.

**Scope (fallback level only)**: this discharges fallback soundness for a spine whose field codec is
`scalarValidRange`, but an ADT codec built by `adtOfPlacedCodecSpine` also needs a `TupleFieldCodec`
for that field, and a genuine integer niche has none: `.uint w` / `.int w` fields are niche-blind
(`TupleFieldCodec.uint_not_scalarValidRange_of_out_of_range`,
`TupleFieldCodec.int_not_scalarValidRange_of_out_of_range`) and ADT kinds carry no structural size
(`TupleFieldCodec.not_adt`). End-to-end `NonZero*` codecs use `MirValueCodec.scalarNicheNewtypeNonPtr`.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem scalarValidRange_decode_isSome_of_decodeScalarLayoutBytes
    (pk : PrimitiveKind) (range : WrappingRange) (sz : Nat) (hNz : 0 < sz)
    (hNonPtr : FixedByteCodec.isNonPointerPrimitiveKind pk = true)
    (hWidth : primitiveKindByteWidth pk = some sz)
    (slice : List AbstractByte)
    (h : ∃ v, decodeScalarLayoutBytes (.initialized pk range) slice = some v) :
    ∃ x, (FixedByteCodec.scalarValidRange sz hNz range).decode slice = some x := by
  obtain ⟨v, hDec⟩ := h
  rw [FixedByteCodec.decodeScalarLayoutBytes_initialized_nonPtr_eq_scalarValidRange_map
      pk range sz hNz hNonPtr hWidth slice] at hDec
  cases hC : (FixedByteCodec.scalarValidRange sz hNz range).decode slice with
  | none =>
    rw [hC] at hDec
    nomatch hDec
  | some x =>
    exact ⟨x, rfl⟩

/--
**Fallback Soundness for 1-Field `.scalar` Structs With a Surjective Field Codec**:
when `l.fieldLayouts = []` and `l.backendRepr = .scalar s0` with `scalarLayoutByteWidth s0 = some p₀.2.size`,
Trusted's fallback slices `[p₀.1 .. p₀.1 + p₀.2.size)` and runs `decodeScalarLayoutBytes s0`, which
succeeds only if that window is initialized; then `c₀.IsSurjectiveInitDecoder` makes `pc.decodeAt bs`
succeed.

Kind: refinement
Witness: universal
Assumes: S0
Subject: AdtDecodeFallbackSound
-/
theorem AdtDecodeFallbackSound.of_scalar_surjective
    {layouts : LayoutTable} {l : TypeLayout} {varIdx : VariantIdx}
    {α : Type} {p₀ : Nat × FieldLayout} {c₀ : FixedByteCodec α p₀.2.size}
    {s0 : ScalarLayout} {totalSize : Nat}
    (hFl : l.fieldLayouts = []) (hRepr : l.backendRepr = .scalar s0)
    (hWidth0 : scalarLayoutByteWidth s0 = some p₀.2.size)
    (hSurj0 : c₀.IsSurjectiveInitDecoder) :
    AdtDecodeFallbackSound layouts l varIdx (.cons p₀ c₀ .nil) totalSize :=
  AdtDecodeFallbackSound.of_scalar hFl hRepr hWidth0 (fun slice hLen ⟨v, hSc⟩ =>
    hSurj0 slice hLen (decodeScalarLayoutBytes_some_allBytesInitialized _ slice v hSc))

/--
**Fallback Soundness for 2-Field `.scalarPair` Structs With Surjective Field Codecs**
(in-order *or* reordered, with any leading/inter-field/trailing padding):
when `l.fieldLayouts = []` and `l.backendRepr = .scalarPair s0 s1` with matching byte widths
`scalarLayoutByteWidth s0 = some p₀.2.size` and `scalarLayoutByteWidth s1 = some p₁.2.size`,
Trusted's fallback slices both field windows `[p₀.1 .. p₀.1 + p₀.2.size)` and
`[p₁.1 .. p₁.1 + p₁.2.size)` and runs `decodeScalarLayoutBytes` on each, which succeeds only if both
windows are initialized; then `c₀.IsSurjectiveInitDecoder` and `c₁.IsSurjectiveInitDecoder` make
`pc.decodeAt bs` succeed.

Kind: refinement
Witness: universal
Assumes: S0
Subject: AdtDecodeFallbackSound
-/
theorem AdtDecodeFallbackSound.of_scalarPair_surjective
    {layouts : LayoutTable} {l : TypeLayout} {varIdx : VariantIdx}
    {α₀ α₁ : Type} {p₀ p₁ : Nat × FieldLayout}
    {c₀ : FixedByteCodec α₀ p₀.2.size} {c₁ : FixedByteCodec α₁ p₁.2.size}
    {s0 s1 : ScalarLayout} {totalSize : Nat}
    (hFl : l.fieldLayouts = []) (hRepr : l.backendRepr = .scalarPair s0 s1)
    (hWidth0 : scalarLayoutByteWidth s0 = some p₀.2.size)
    (hWidth1 : scalarLayoutByteWidth s1 = some p₁.2.size)
    (hSurj0 : c₀.IsSurjectiveInitDecoder)
    (hSurj1 : c₁.IsSurjectiveInitDecoder) :
    AdtDecodeFallbackSound layouts l varIdx (.cons p₀ c₀ (.cons p₁ c₁ .nil)) totalSize :=
  AdtDecodeFallbackSound.of_scalarPair hFl hRepr hWidth0 hWidth1
    (fun slice hLen ⟨v, hSc⟩ =>
      hSurj0 slice hLen (decodeScalarLayoutBytes_some_allBytesInitialized _ slice v hSc))
    (fun slice hLen ⟨v, hSc⟩ =>
      hSurj1 slice hLen (decodeScalarLayoutBytes_some_allBytesInitialized _ slice v hSc))

/--
Per-field layout-table soundness for `TypeLayout.fieldLayouts`: each field `(p, c)` in `pc` is paired
with a layout index `fIdx` in `layouts` whose entry `fl` has size `p.2.size` and whose layout-based
decode (`decodeValueFromBytes tupleFieldFuel layouts { kind := .adt "" [], layoutIdx := fIdx }`)
succeeds only on byte slices that `c.decode` also accepts.

Unlike `l.fieldLayouts = []` (where Trusted falls back to `decodeFieldsBySpan`), a struct with
populated `l.fieldLayouts` satisfying `FieldLayoutsDecodeSound` enforces per-field niche invariants
(such as `bool` `0 ..= 1` or `NonZero*` `1 ..= MAX`) inside `adtDecodeFallback`, so
`AdtDecodeFallbackSound` holds for both in-order and reordered structs with niche fields!
(Only fallback soundness: combined with `adtOfPlacedCodecSpine`, every field also needs a
`TupleFieldCodec`, which exists for `bool` but not for integer niches such as `NonZero*`; see
`TupleFieldCodec.uint_not_scalarValidRange_of_out_of_range`.)
-/
inductive FieldLayoutsDecodeSound (layouts : LayoutTable) :
    {αs : List Type} → PlacedCodecSpine αs → List LayoutIdx → Prop where
  | nil : FieldLayoutsDecodeSound layouts .nil []
  | cons {α : Type} {αs : List Type} {p : Nat × FieldLayout}
      {c : FixedByteCodec α p.2.size} {tail : PlacedCodecSpine αs}
      {fIdx : LayoutIdx} {fRest : List LayoutIdx} {fl : TypeLayout}
      (hLookup : LayoutTable.lookup layouts fIdx = some fl)
      (hSize : fl.size.bytes = p.2.size)
      (hField : ∀ fSlice : List AbstractByte, fSlice.length = p.2.size →
        (∃ v, decodeValueFromBytes tupleFieldFuel layouts
          { kind := .adt "" [], layoutIdx := fIdx } fSlice = some v) →
        ∃ a, c.decode fSlice = some a)
      (rest : FieldLayoutsDecodeSound layouts tail fRest) :
      FieldLayoutsDecodeSound layouts (.cons p c tail) (fIdx :: fRest)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem FieldLayoutsDecodeSound.length_eq {layouts : LayoutTable} :
    ∀ {αs : List Type} {pc : PlacedCodecSpine αs} {fIdxs : List LayoutIdx},
      FieldLayoutsDecodeSound layouts pc fIdxs →
      fIdxs.length = pc.placed.length
  | _, .nil, _, .nil => rfl
  | _, .cons _ _ _, _, .cons _ _ _ rest =>
    congrArg Nat.succ (FieldLayoutsDecodeSound.length_eq rest)

/--
If `FieldLayoutsDecodeSound layouts pc fIdxs` holds, any successful `decodeFieldsByLayoutIdxs` run
implies that `pc.decodeAt bs` also succeeds.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem FieldLayoutsDecodeSound.decodeAt_isSome_of_decodeFieldsByLayoutIdxs
    {layouts : LayoutTable} (bs : List AbstractByte) :
    ∀ {αs : List Type} {pc : PlacedCodecSpine αs} {fIdxs : List LayoutIdx} {vals : List Value},
      FieldLayoutsDecodeSound layouts pc fIdxs →
      decodeFieldsByLayoutIdxs
        (fun fIdx fSlice =>
          decodeValueFromBytes tupleFieldFuel layouts { kind := .adt "" [], layoutIdx := fIdx } fSlice)
        layouts bs (pc.placed.map fun p => ({ bytes := p.1 } : Size)) fIdxs = some vals →
      ∃ x, pc.decodeAt bs = some x
  | _, .nil, _, _, .nil, _ => ⟨(), rfl⟩
  | _, .cons p c tail, _ :: fRest, vals, .cons hLookup hSize hField rest, hDec => by
    unfold decodeFieldsByLayoutIdxs at hDec
    dsimp only [PlacedCodecSpine.placed, List.map] at hDec
    rw [hLookup] at hDec
    dsimp only at hDec
    rw [hSize] at hDec
    cases hSl : sliceAbstractBytes bs p.1 p.2.size with
    | none =>
      rw [hSl] at hDec
      nomatch hDec
    | some fSlice =>
      rw [hSl] at hDec
      dsimp only at hDec
      cases hFV : decodeValueFromBytes tupleFieldFuel layouts
          { kind := .adt "" [], layoutIdx := _ } fSlice with
      | none =>
        rw [hFV] at hDec
        nomatch hDec
      | some v =>
        rw [hFV] at hDec
        dsimp only at hDec
        cases hRest : decodeFieldsByLayoutIdxs
            (fun fIdx fSlice =>
              decodeValueFromBytes tupleFieldFuel layouts
                { kind := .adt "" [], layoutIdx := fIdx } fSlice)
            layouts bs (tail.placed.map fun p => ({ bytes := p.1 } : Size)) fRest with
        | none =>
          rw [hRest] at hDec
          nomatch hDec
        | some vs =>
          obtain ⟨hEq, hLen⟩ := sliceAbstractBytes_some_eq_drop_take_and_len hSl
          obtain ⟨a, ha⟩ := hField fSlice hLen ⟨v, hFV⟩
          rw [hEq] at ha
          obtain ⟨r, hr⟩ :=
            FieldLayoutsDecodeSound.decodeAt_isSome_of_decodeFieldsByLayoutIdxs bs rest hRest
          refine ⟨(a, r), ?_⟩
          show (match c.decode ((bs.drop p.1).take p.2.size), tail.decodeAt bs with
            | some a', some r' => some (a', r')
            | _, _ => none) = some (a, r)
          rw [ha, hr]

/--
Ready-made `FieldLayoutsDecodeSound` step for any surjective field codec (`c.IsSurjectiveInitDecoder`)
paired with a `.primitive` field layout `fl` (`fl.size.bytes = p.2.size`, `0 < p.2.size`,
`fl.isUninhabited = false`, `fl.variants = .single varIdx`, `fl.fields = .primitive`).

Kind: helper
Witness: universal
Assumes: S0
-/
theorem FieldLayoutsDecodeSound.cons_primitive_surjective
    {layouts : LayoutTable} {α : Type} {αs : List Type}
    {p : Nat × FieldLayout} {c : FixedByteCodec α p.2.size} {tail : PlacedCodecSpine αs}
    {fIdx : LayoutIdx} {fRest : List LayoutIdx} {fl : TypeLayout} {varIdx : VariantIdx}
    (hLookup : LayoutTable.lookup layouts fIdx = some fl)
    (hInhab : fl.isUninhabited = false)
    (hVar : fl.variants = .single varIdx)
    (hFields : fl.fields = .primitive)
    (hSize : fl.size.bytes = p.2.size)
    (hNz : 0 < p.2.size)
    (hSurj : c.IsSurjectiveInitDecoder)
    (rest : FieldLayoutsDecodeSound layouts tail fRest) :
    FieldLayoutsDecodeSound layouts (.cons p c tail) (fIdx :: fRest) := by
  refine .cons hLookup hSize (fun fSlice hLen ⟨v, hDec⟩ => ?_) rest
  unfold tupleFieldFuel decodeValueFromBytes at hDec
  dsimp only at hDec
  rw [hLookup] at hDec
  dsimp only at hDec
  rw [hInhab, hSize] at hDec
  have hBeqLen : Nat.beq (Trusted.Sequence.length fSlice) p.2.size = true :=
    Nat.beq_eq.mpr hLen
  rw [hBeqLen] at hDec
  dsimp only [Bool.not, Bool.or] at hDec
  rw [hVar, hFields] at hDec
  dsimp only at hDec
  have hBeq0 : Nat.beq p.2.size 0 = false := nat_beq_eq_false_of_ne (by omega)
  rw [hBeq0] at hDec
  dsimp only at hDec
  have hInit : allBytesInitialized fSlice = true := by
    cases hRepr : fl.backendRepr with
    | scalar s0 =>
      rw [hRepr] at hDec
      exact decodeScalarLayoutBytes_some_allBytesInitialized s0 fSlice v hDec
    | scalarPair _ _ | memory =>
      rw [hRepr] at hDec
      dsimp only at hDec
      cases hSc : decodeScalarBytes fSlice false with
      | none =>
        rw [hSc] at hDec
        nomatch hDec
      | some r =>
        exact decodeScalarBytes_some_allBytesInitialized fSlice false r hSc
  exact hSurj fSlice hLen hInit

/--
Ready-made `FieldLayoutsDecodeSound` step for a 0-byte ZST unit/marker field (`FixedByteCodec.unit`)
paired with any 0-byte `TypeLayout` entry `fl` (`fl.size.bytes = 0`), such as `()` or `PhantomData<T>`.
Because `FixedByteCodec.unit.decode` succeeds on the empty slice `[]` regardless of how `fl` decodes,
no assumptions on `fl.fields`, `fl.variants`, or `fl.backendRepr` are needed.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem FieldLayoutsDecodeSound.cons_zst_unit
    {layouts : LayoutTable} {αs : List Type}
    {off : Nat} {align : Nat} {tail : PlacedCodecSpine αs}
    {fIdx : LayoutIdx} {fRest : List LayoutIdx} {fl : TypeLayout}
    (hLookup : LayoutTable.lookup layouts fIdx = some fl)
    (hSize : fl.size.bytes = 0)
    (rest : FieldLayoutsDecodeSound layouts tail fRest) :
    FieldLayoutsDecodeSound layouts (.cons (off, ⟨0, align⟩) FixedByteCodec.unit tail)
      (fIdx :: fRest) := by
  refine .cons hLookup hSize (fun fSlice hLen _ => ?_) rest
  cases fSlice with
  | nil => exact ⟨(), rfl⟩
  | cons _ _ => nomatch hLen

/--
Ready-made `FieldLayoutsDecodeSound` step for any field codec `c` paired with a `.primitive`
scalar-niche field layout `fl` (`fl.backendRepr = .scalar s0`, `0 < p.2.size`, `fl.size.bytes = p.2.size`,
`fl.isUninhabited = false`, `fl.variants = .single varIdx`, `fl.fields = .primitive`) whose scalar
layout decode `decodeScalarLayoutBytes s0` accepts only slices that `c.decode` also accepts.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem FieldLayoutsDecodeSound.cons_primitive_scalar
    {layouts : LayoutTable} {α : Type} {αs : List Type}
    {p : Nat × FieldLayout} {c : FixedByteCodec α p.2.size} {tail : PlacedCodecSpine αs}
    {fIdx : LayoutIdx} {fRest : List LayoutIdx} {fl : TypeLayout} {varIdx : VariantIdx}
    {s0 : ScalarLayout}
    (hLookup : LayoutTable.lookup layouts fIdx = some fl)
    (hInhab : fl.isUninhabited = false)
    (hVar : fl.variants = .single varIdx)
    (hFields : fl.fields = .primitive)
    (hSize : fl.size.bytes = p.2.size)
    (hNz : 0 < p.2.size)
    (hRepr : fl.backendRepr = .scalar s0)
    (hAccept : ∀ fSlice : List AbstractByte, fSlice.length = p.2.size →
      (∃ v, decodeScalarLayoutBytes s0 fSlice = some v) → ∃ a, c.decode fSlice = some a)
    (rest : FieldLayoutsDecodeSound layouts tail fRest) :
    FieldLayoutsDecodeSound layouts (.cons p c tail) (fIdx :: fRest) := by
  refine .cons hLookup hSize (fun fSlice hLen ⟨v, hDec⟩ => ?_) rest
  unfold tupleFieldFuel decodeValueFromBytes at hDec
  dsimp only at hDec
  rw [hLookup] at hDec
  dsimp only at hDec
  rw [hInhab, hSize] at hDec
  have hBeqLen : Nat.beq (Trusted.Sequence.length fSlice) p.2.size = true :=
    Nat.beq_eq.mpr hLen
  rw [hBeqLen] at hDec
  dsimp only [Bool.not, Bool.or] at hDec
  rw [hVar, hFields] at hDec
  dsimp only at hDec
  have hBeq0 : Nat.beq p.2.size 0 = false := nat_beq_eq_false_of_ne (by omega)
  rw [hBeq0] at hDec
  dsimp only at hDec
  rw [hRepr] at hDec
  exact hAccept fSlice hLen ⟨v, hDec⟩

/--
Ready-made `FieldLayoutsDecodeSound` step for `FixedByteCodec.scalarValidRange p.2.size hNz range`
paired with its `.primitive` non-pointer scalar-niche `TypeLayout`
(`fl.backendRepr = .scalar (.initialized pk range)`).

This is a fallback-level fact only: when `range` excludes some bit pattern (a genuine niche such as
`NonZero*`), the field has no `TupleFieldCodec` at `.uint w` / `.int w` / `.adt _ _`
(`TupleFieldCodec.uint_not_scalarValidRange_of_out_of_range`, `TupleFieldCodec.not_adt`), so the step
cannot complete an `adtOfPlacedCodecSpine` codec for such a field.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem FieldLayoutsDecodeSound.cons_primitive_scalarValidRange
    {layouts : LayoutTable} {αs : List Type}
    {p : Nat × FieldLayout} {hNz : 0 < p.2.size} {range : WrappingRange}
    {tail : PlacedCodecSpine αs}
    {fIdx : LayoutIdx} {fRest : List LayoutIdx} {fl : TypeLayout} {varIdx : VariantIdx}
    {pk : PrimitiveKind}
    (hLookup : LayoutTable.lookup layouts fIdx = some fl)
    (hInhab : fl.isUninhabited = false)
    (hVar : fl.variants = .single varIdx)
    (hFields : fl.fields = .primitive)
    (hSize : fl.size.bytes = p.2.size)
    (hRepr : fl.backendRepr = .scalar (.initialized pk range))
    (hNonPtr : FixedByteCodec.isNonPointerPrimitiveKind pk = true)
    (hWidth : primitiveKindByteWidth pk = some p.2.size)
    (rest : FieldLayoutsDecodeSound layouts tail fRest) :
    FieldLayoutsDecodeSound layouts
      (.cons p (FixedByteCodec.scalarValidRange p.2.size hNz range) tail)
      (fIdx :: fRest) :=
  FieldLayoutsDecodeSound.cons_primitive_scalar hLookup hInhab hVar hFields hSize hNz hRepr
    (fun fSlice _ h =>
      scalarValidRange_decode_isSome_of_decodeScalarLayoutBytes pk range p.2.size hNz hNonPtr
        hWidth fSlice h)
    rest

/--
Ready-made `FieldLayoutsDecodeSound` step for a `bool` field (`FixedByteCodec.boolByte`) paired with
its `.primitive` scalar-niche `TypeLayout` (`fl.size.bytes = 1`, `fl.isUninhabited = false`,
`fl.variants = .single varIdx`, `fl.fields = .primitive`,
`fl.backendRepr = .scalar (.initialized (.int 8 false) ⟨0, 1⟩)`).

Kind: helper
Witness: universal
Assumes: S0
-/
theorem FieldLayoutsDecodeSound.cons_primitive_bool
    {layouts : LayoutTable} {αs : List Type}
    {off : Nat} {align : Nat} {tail : PlacedCodecSpine αs}
    {fIdx : LayoutIdx} {fRest : List LayoutIdx} {fl : TypeLayout} {varIdx : VariantIdx}
    (hLookup : LayoutTable.lookup layouts fIdx = some fl)
    (hInhab : fl.isUninhabited = false)
    (hVar : fl.variants = .single varIdx)
    (hFields : fl.fields = .primitive)
    (hSize : fl.size.bytes = 1)
    (hRepr : fl.backendRepr = .scalar (.initialized (.int 8 false) ⟨0, 1⟩))
    (rest : FieldLayoutsDecodeSound layouts tail fRest) :
    FieldLayoutsDecodeSound layouts (.cons (off, ⟨1, align⟩) FixedByteCodec.boolByte tail)
      (fIdx :: fRest) :=
  FieldLayoutsDecodeSound.cons_primitive_scalar hLookup hInhab hVar hFields hSize Nat.zero_lt_one hRepr
    (fun fSlice _ h => boolByte_decode_isSome_of_decodeScalarLayoutBytes fSlice h)
    rest

/--
**Fallback Soundness for Structs With Populated `l.fieldLayouts`** (in-order *or* reordered, with
any `l.backendRepr` and niche fields such as `bool` or `NonZero*`):
whenever `FieldLayoutsDecodeSound layouts pc l.fieldLayouts` holds, Trusted's `adtDecodeFallback`
takes the `decodeFieldsByLayoutIdxs` branch and cannot succeed on any buffer rejected by
`pc.decodeAt`.

Kind: refinement
Witness: universal
Assumes: S0
Subject: AdtDecodeFallbackSound
-/
theorem AdtDecodeFallbackSound.of_fieldLayouts
    {layouts : LayoutTable} {l : TypeLayout} {varIdx : VariantIdx}
    {αs : List Type} {pc : PlacedCodecSpine αs} {totalSize : Nat}
    (hFl : FieldLayoutsDecodeSound layouts pc l.fieldLayouts) :
    AdtDecodeFallbackSound layouts l varIdx pc totalSize := by
  intro bs _ hNone
  unfold adtDecodeFallback
  have hBeq :
      Nat.beq (Trusted.Sequence.length l.fieldLayouts)
        (Trusted.Sequence.length (pc.placed.map fun p => ({ bytes := p.1 } : Size))) = true := by
    apply Nat.beq_eq.mpr
    show l.fieldLayouts.length = (pc.placed.map fun p => ({ bytes := p.1 } : Size)).length
    rw [List.length_map]
    exact hFl.length_eq
  rw [hBeq]
  dsimp only
  cases hIdx : decodeFieldsByLayoutIdxs
      (fun fIdx fSlice =>
        decodeValueFromBytes tupleFieldFuel layouts { kind := .adt "" [], layoutIdx := fIdx } fSlice)
      layouts bs (pc.placed.map fun p => ({ bytes := p.1 } : Size)) l.fieldLayouts with
  | none => rfl
  | some vals =>
    exfalso
    obtain ⟨x, hx⟩ := hFl.decodeAt_isSome_of_decodeFieldsByLayoutIdxs bs hIdx
    rw [hNone] at hx
    nomatch hx


/--
Trusted encodes the single-variant laid-out struct `.adt defPath (k :: ks)` value
`.aggregate varIdx (fcs.toValues x)` to the realized codec's encoding of `x`.

Kind: refinement
Witness: universal
Assumes: S0
Subject: encodeValueToBytes
-/
theorem adtOfPlacedCodecSpine_encode_toValue
    {layouts : LayoutTable} {defPath : DefPath} {idx : LayoutIdx} {l : TypeLayout}
    {varIdx : VariantIdx} {memoryIndex : List Nat}
    {k : RigidTy} {ks : List RigidTy} {αs : List Type} {pc : PlacedCodecSpine αs} {totalSize : Nat}
    (fcs : TupleFieldCodecs layouts (k :: ks) pc)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single varIdx)
    (hSize : l.size = { bytes := totalSize })
    (hFields : l.fields = .arbitrary (pc.placed.map fun p => ({ bytes := p.1 } : Size)) memoryIndex)
    (hSeq : SequentialFieldPlacement 0 (pc.memSort.placed.map Prod.snd)
      (pc.memSort.placed.map Prod.fst) totalSize)
    (x : FieldTuple αs) :
    encodeValueToBytes defaultCodecFuel layouts { kind := .adt defPath (k :: ks), layoutIdx := idx }
        (.aggregate varIdx (fcs.toValues x)) =
      some ((pc.realizedCodec totalSize).encode x) := by
  cases fcs with
  | @cons _ _ _ _ p₀ c₀ tail f₀ rest =>
    unfold defaultCodecFuel encodeValueToBytes
    simp only []
    rw [hLookup]
    dsimp only
    rw [hInhab]
    dsimp only
    rw [hVar]
    dsimp only
    rw [hFields]
    dsimp only
    have hCond1 :
        Bool.and (Nat.beq varIdx varIdx)
          (Nat.beq
            (Trusted.Sequence.length
              (((PlacedCodecSpine.cons p₀ c₀ tail).placed.map fun p => ({ bytes := p.1 } : Size))))
            (Trusted.Sequence.length ((TupleFieldCodecs.cons f₀ rest).toValues x))) = true := by
      rw [nat_beq_self varIdx, Bool.true_and]
      apply Nat.beq_eq.mpr
      show ((PlacedCodecSpine.cons p₀ c₀ tail).placed.map fun p => ({ bytes := p.1 } : Size)).length =
        ((TupleFieldCodecs.cons f₀ rest).toValues x).length
      rw [List.length_map, (TupleFieldCodecs.cons f₀ rest).length_placed,
          (TupleFieldCodecs.cons f₀ rest).length_toValues]
    rw [hCond1]
    dsimp only
    have hCond2 :
        Nat.beq (Trusted.Sequence.length (k :: ks))
          (Trusted.Sequence.length
            (((PlacedCodecSpine.cons p₀ c₀ tail).placed.map fun p => ({ bytes := p.1 } : Size)))) = true := by
      apply Nat.beq_eq.mpr
      show (k :: ks).length =
        ((PlacedCodecSpine.cons p₀ c₀ tail).placed.map fun p => ({ bytes := p.1 } : Size)).length
      rw [List.length_map, (TupleFieldCodecs.cons f₀ rest).length_placed]
    rw [hCond2]
    dsimp only
    rw [hSize]
    exact ((TupleFieldCodecs.cons f₀ rest).encodeFieldsAtOffsetsWith_eq_writeWindows _ x _).trans
      ((PlacedCodecSpine.cons p₀ c₀ tail).writeWindows_realizedCodec_encode totalSize hSeq x)

/--
Every successful Trusted encoding of the single-variant laid-out struct `.adt defPath (k :: ks)`
is a realized-codec encoding.

Kind: refinement
Witness: universal
Assumes: S0
Subject: PlacedCodecSpine.realizedCodec
-/
theorem adtOfPlacedCodecSpine_encode_witness
    {layouts : LayoutTable} {defPath : DefPath} {idx : LayoutIdx} {l : TypeLayout}
    {varIdx : VariantIdx} {memoryIndex : List Nat}
    {k : RigidTy} {ks : List RigidTy} {αs : List Type} {pc : PlacedCodecSpine αs} {totalSize : Nat}
    (fcs : TupleFieldCodecs layouts (k :: ks) pc)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single varIdx)
    (hSize : l.size = { bytes := totalSize })
    (hFields : l.fields = .arbitrary (pc.placed.map fun p => ({ bytes := p.1 } : Size)) memoryIndex)
    (hSeq : SequentialFieldPlacement 0 (pc.memSort.placed.map Prod.snd)
      (pc.memSort.placed.map Prod.fst) totalSize)
    (v : Value) (bs : List AbstractByte)
    (hEnc : encodeValueToBytes defaultCodecFuel layouts
      { kind := .adt defPath (k :: ks), layoutIdx := idx } v = some bs) :
    ∃ x : FieldTuple αs, bs = (pc.realizedCodec totalSize).encode x := by
  cases fcs with
  | @cons _ _ _ _ p₀ c₀ tail f₀ rest =>
    unfold defaultCodecFuel encodeValueToBytes at hEnc
    rw [hLookup] at hEnc
    dsimp only at hEnc
    rw [hInhab] at hEnc
    dsimp only at hEnc
    rw [hVar] at hEnc
    dsimp only at hEnc
    rw [hFields] at hEnc
    cases v <;> dsimp only [PlacedCodecSpine.placed, List.map] at hEnc
    case unit => nomatch hEnc
    case scalar => nomatch hEnc
    case ptr => nomatch hEnc
    case aggregate vIdx vals =>
      cases hCond1 : Bool.and (Nat.beq vIdx varIdx)
          (Nat.beq
            (Trusted.Sequence.length
              (({ bytes := p₀.1 } : Size) :: (tail.placed.map fun p => ({ bytes := p.1 } : Size))))
            (Trusted.Sequence.length vals)) with
      | false =>
        rw [hCond1] at hEnc
        nomatch hEnc
      | true =>
        rw [hCond1] at hEnc
        dsimp only at hEnc
        have hCond2 :
            Nat.beq (Trusted.Sequence.length (k :: ks))
              (Trusted.Sequence.length
                (({ bytes := p₀.1 } : Size) :: (tail.placed.map fun p => ({ bytes := p.1 } : Size)))) = true := by
          apply Nat.beq_eq.mpr
          show (k :: ks).length =
            ((PlacedCodecSpine.cons p₀ c₀ tail).placed.map fun p => ({ bytes := p.1 } : Size)).length
          rw [List.length_map, (TupleFieldCodecs.cons f₀ rest).length_placed]
        rw [hCond2] at hEnc
        dsimp only at hEnc
        rw [hSize] at hEnc
        obtain ⟨x, hx⟩ := (TupleFieldCodecs.cons f₀ rest).encodeFieldsAtOffsetsWith_witness _ vals _ bs hEnc
        rw [(PlacedCodecSpine.cons p₀ c₀ tail).writeWindows_realizedCodec_encode totalSize hSeq x] at hx
        injection hx with hx
        exact ⟨x, hx.symm⟩

/--
Trusted decodes the single-variant laid-out struct `.adt defPath (k :: ks)` exactly as the realized
codec whenever Trusted's fallback decoder cannot rescue a buffer that the field windows reject
(`AdtDecodeFallbackSound`).

Kind: refinement
Witness: universal
Assumes: S0
Subject: decodeValueFromBytes
-/
theorem adtOfPlacedCodecSpine_decode_eq_map
    {layouts : LayoutTable} {defPath : DefPath} {idx : LayoutIdx} {l : TypeLayout}
    {varIdx : VariantIdx} {memoryIndex : List Nat}
    {k : RigidTy} {ks : List RigidTy} {αs : List Type} {pc : PlacedCodecSpine αs} {totalSize : Nat}
    (fcs : TupleFieldCodecs layouts (k :: ks) pc)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single varIdx)
    (hSize : l.size = { bytes := totalSize })
    (hFields : l.fields = .arbitrary (pc.placed.map fun p => ({ bytes := p.1 } : Size)) memoryIndex)
    (hFallback : AdtDecodeFallbackSound layouts l varIdx pc totalSize)
    (hSeq : SequentialFieldPlacement 0 (pc.memSort.placed.map Prod.snd)
      (pc.memSort.placed.map Prod.fst) totalSize)
    (bs : List AbstractByte) :
    decodeValueFromBytes defaultCodecFuel layouts { kind := .adt defPath (k :: ks), layoutIdx := idx } bs =
      ((pc.realizedCodec totalSize).decode bs).map (fun x => .aggregate varIdx (fcs.toValues x)) := by
  cases fcs with
  | @cons _ _ _ _ p₀ c₀ tail f₀ rest =>
    have hWidth := ((PlacedCodecSpine.cons p₀ c₀ tail).realized_offsets_and_width_of_sequential totalSize hSeq).2
    unfold defaultCodecFuel decodeValueFromBytes
    dsimp only
    rw [hLookup]
    dsimp only
    rw [hInhab, hSize]
    dsimp only
    cases hL : Nat.beq (Trusted.Sequence.length bs) totalSize with
    | false =>
      have hNe : bs.length ≠ (PlacedCodecSpine.cons p₀ c₀ tail).realizedWidth totalSize := by
        rw [hWidth]
        intro hEq
        rw [show Trusted.Sequence.length bs = bs.length from rfl, Nat.beq_eq.mpr hEq] at hL
        nomatch hL
      rw [((PlacedCodecSpine.cons p₀ c₀ tail).realizedCodec_isExactWidth totalSize).decode_eq_none_of_length_ne hNe]
      rfl
    | true =>
      have hLen : bs.length = totalSize := Nat.eq_of_beq_eq_true hL
      rw [hVar, hFields]
      dsimp only [Bool.not, Bool.or, PlacedCodecSpine.placed, List.map]
      have hCond2 :
          Nat.beq (Trusted.Sequence.length (k :: ks))
            (Trusted.Sequence.length
              (({ bytes := p₀.1 } : Size) :: (tail.placed.map fun p => ({ bytes := p.1 } : Size)))) = true := by
        apply Nat.beq_eq.mpr
        show (k :: ks).length =
          ((PlacedCodecSpine.cons p₀ c₀ tail).placed.map fun p => ({ bytes := p.1 } : Size)).length
        rw [List.length_map, (TupleFieldCodecs.cons f₀ rest).length_placed]
      rw [hCond2]
      dsimp only
      have hDecodeAt :
          decodeFieldsAtOffsetsWith
              (fun k b => decodeValueFromBytes tupleFieldFuel layouts { kind := k, layoutIdx := 0 } b)
              (fun k => rigidTyByteSize layouts { kind := k, layoutIdx := 0 }) bs
              (({ bytes := p₀.1 } : Size) :: (tail.placed.map fun p => ({ bytes := p.1 } : Size)))
              (k :: ks) =
            ((PlacedCodecSpine.cons p₀ c₀ tail).decodeAt bs).map
              (TupleFieldCodecs.cons f₀ rest).toValues :=
        (TupleFieldCodecs.cons f₀ rest).decodeFieldsAtOffsetsWith_eq_decodeAt bs (by
          rw [hLen]
          exact (PlacedCodecSpine.cons p₀ c₀ tail).placed_in_bounds_of_memSort_sequential totalSize hSeq)
      rw [hDecodeAt,
        (PlacedCodecSpine.cons p₀ c₀ tail).realizedCodec_decode_eq_decodeAt totalSize hSeq bs hLen]
      cases hDA : (PlacedCodecSpine.cons p₀ c₀ tail).decodeAt bs with
      | some x => rfl
      | none =>
        have hFb :
            adtDecodeFallback layouts l varIdx
              (({ bytes := p₀.1 } : Size) :: (tail.placed.map fun p => ({ bytes := p.1 } : Size))) bs =
              none :=
          hFallback bs hLen hDA
        unfold adtDecodeFallback at hFb
        rw [hSize] at hFb
        exact hFb

/--
**General $k$-Field Laid-Out Struct (`TyKind.adt`) `MirValueCodec`**: bridges a single-variant
struct `{ kind := .adt defPath (k :: ks), layoutIdx := idx }` with `FieldsShape.arbitrary` field
offsets to `pc.realizedCodec totalSize`, provided Trusted's fallback decoder cannot accept a buffer
whose field windows are rejected (`AdtDecodeFallbackSound`). This side condition is necessary, not
technical: for an in-order `.memory` struct without `fieldLayouts`, Trusted's padding-inclusive span
fallback decodes a `bool` byte `2` as a raw scalar, so no codec with a `bool` field exists there. It
holds for every `.memory` struct without `fieldLayouts` whose field codecs are surjective
(`AdtDecodeFallbackSound.of_memory_surjective`, in-order or reordered) and whenever the fallback always
fails (`AdtDecodeFallbackNone.toSound`, e.g. `AdtDecodeFallbackNone.of_reordered_head`).
-/
def adtOfPlacedCodecSpine
    (layouts : LayoutTable) (defPath : DefPath) (idx : LayoutIdx) (l : TypeLayout)
    (varIdx : VariantIdx) (memoryIndex : List Nat)
    {k : RigidTy} {ks : List RigidTy} {αs : List Type} (pc : PlacedCodecSpine αs) (totalSize : Nat)
    (fcs : TupleFieldCodecs layouts (k :: ks) pc)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single varIdx)
    (hSize : l.size = { bytes := totalSize })
    (hFields : l.fields = .arbitrary (pc.placed.map fun p => ({ bytes := p.1 } : Size)) memoryIndex)
    (hFallback : AdtDecodeFallbackSound layouts l varIdx pc totalSize)
    (hSeq : SequentialFieldPlacement 0 (pc.memSort.placed.map Prod.snd)
      (pc.memSort.placed.map Prod.fst) totalSize) :
    MirValueCodec layouts { kind := .adt defPath (k :: ks), layoutIdx := idx } (FieldTuple αs) totalSize :=
  ofCanonicalEncode
    ((pc.realizedCodec totalSize).castWidth
      (pc.realized_offsets_and_width_of_sequential totalSize hSeq).2)
    (fun x => .aggregate varIdx (fcs.toValues x))
    (fun v =>
      match v with
      | .aggregate vIdx vs => if vIdx == varIdx then fcs.ofValues vs else none
      | _ => none)
    (fun x => by
      have hBeq : (varIdx == varIdx) = true := decide_eq_true rfl
      dsimp only
      rw [hBeq]
      exact fcs.ofValues_toValues x)
    (adt_cons_rigidTyByteSize hLookup hSize)
    (fun x => adtOfPlacedCodecSpine_encode_toValue fcs hLookup hInhab hVar hSize hFields hSeq x)
    (fun v bs hEnc => adtOfPlacedCodecSpine_encode_witness fcs hLookup hInhab hVar hSize hFields hSeq v bs hEnc)
    (fun bs => adtOfPlacedCodecSpine_decode_eq_map fcs hLookup hInhab hVar hSize hFields hFallback hSeq bs)


/--
Universal `IsFromBytes`, `IsFromZeros`, and `IsTryFromBytes` preservation for any
`MirValueCodec.ofPlacedCodecSpine` across all leading/inter-field/trailing padding configurations
and field memory-order permutations.

Kind: safety
Witness: universal
Assumes: S0
Subject: MirValueCodec.codec
-/
theorem ofPlacedCodecSpine_isFromBytes_all_pads
    {layouts : LayoutTable} {ty : Ty} {αs : List Type}
    (pc : PlacedCodecSpine αs) (totalSize : Nat)
    (hWidth : pc.realizedWidth totalSize = totalSize)
    (m : MirValueCodec layouts ty (FieldTuple αs) totalSize)
    (hCodec : m.codec = (pc.realizedCodec totalSize).castWidth hWidth := by rfl)
    (hSurj : pc.AllFieldsSurjective) :
    m.codec.IsSurjectiveInitDecoder ∧
    IsFromBytes layouts ty ∧
    IsFromZeros layouts ty ∧
    IsTryFromBytes layouts ty := by
  have hMSurj : m.codec.IsSurjectiveInitDecoder := by
    rw [hCodec]
    exact FixedByteCodec.castWidth_isSurjectiveInitDecoder (pc.realizedCodec totalSize) hWidth
      (pc.realizedCodec_isSurjectiveInitDecoder totalSize hSurj)
  have hFb := m.isFromBytes hMSurj
  exact ⟨hMSurj, hFb, isFromBytes_implies_isFromZeros _ _ hFb,
    isFromBytes_implies_isTryFromBytes _ _ hFb⟩

/--
Universal `IsFromZeros` and `IsTryFromBytes` preservation for any `MirValueCodec.ofPlacedCodecSpine`.

Kind: safety
Witness: universal
Assumes: S0
Subject: MirValueCodec.codec
-/
theorem ofPlacedCodecSpine_isFromZeros_all_pads
    {layouts : LayoutTable} {ty : Ty} {αs : List Type}
    (pc : PlacedCodecSpine αs) (totalSize : Nat)
    (hWidth : pc.realizedWidth totalSize = totalSize)
    (m : MirValueCodec layouts ty (FieldTuple αs) totalSize)
    (hCodec : m.codec = (pc.realizedCodec totalSize).castWidth hWidth := by rfl)
    (hZero : pc.AllFieldsZeroValid) :
    m.codec.HasZeroValid ∧
    IsFromZeros layouts ty ∧
    IsTryFromBytes layouts ty := by
  have hMZero : m.codec.HasZeroValid := by
    rw [hCodec]
    exact FixedByteCodec.castWidth_hasZeroValid (pc.realizedCodec totalSize) hWidth
      (pc.realizedCodec_hasZeroValid totalSize hZero)
  exact ⟨hMZero, m.isFromZeros hMZero, m.isTryFromBytes_trivial⟩

/--
Tight-world (`pc.realizedLead + (pc.realizedSpine totalSize).totalPadBytes = 0`) `IsInitCodec`,
`IsIntoBytes`, and `transmute_typed` soundness for `MirValueCodec.ofPlacedCodecSpine`.

Kind: safety
Witness: universal
Assumes: S0
Subject: MirValueCodec.codec
-/
theorem ofPlacedCodecSpine_zero_pad_isIntoBytes_and_transmute_typed
    {layouts : LayoutTable} {ty : Ty} {αs : List Type}
    (pc : PlacedCodecSpine αs) (totalSize : Nat)
    (hWidth : pc.realizedWidth totalSize = totalSize)
    (m : MirValueCodec layouts ty (FieldTuple αs) totalSize)
    (hCodec : m.codec = (pc.realizedCodec totalSize).castWidth hWidth := by rfl)
    (hWidths : m.enforcesUntypedFieldWidths = true := by rfl)
    (hPad0 : pc.realizedLead + (pc.realizedSpine totalSize).totalPadBytes = 0)
    (hInit : pc.AllFieldsInit) :
    m.codec.IsInitCodec ∧
    IsIntoBytes layouts ty ∧
    ∀ {dstTy : Ty} {β : Type} (mDst : MirValueCodec layouts dstTy β totalSize),
      mDst.codec.IsSurjectiveInitDecoder →
      ∀ x : FieldTuple αs, ∃ y : β,
        mDst.codec.decode (m.codec.encode x) = some y ∧
        decodeValueFromBytes defaultCodecFuel layouts dstTy (m.codec.encode x) =
          some (mDst.toValue y) := by
  have hMInit : m.codec.IsInitCodec := by
    rw [hCodec]
    exact FixedByteCodec.castWidth_isInitCodec (pc.realizedCodec totalSize) hWidth
      (pc.realizedCodec_isInitCodec_of_zero_pad totalSize hPad0 hInit)
  exact ⟨hMInit, m.isIntoBytes hMInit hWidths,
    fun mDst hFrom x => MirValueCodec.transmute_typed m mDst hMInit hFrom x⟩

/--
Padded-world (`0 < pc.realizedLead + (pc.realizedSpine totalSize).totalPadBytes`) `.uninit` emission,
`¬ IsInitCodec`, and `¬ IsIntoBytes` for `MirValueCodec.ofPlacedCodecSpine`.

Kind: divergence
Witness: negative
Assumes: S0
Subject: MirValueCodec.codec
-/
theorem ofPlacedCodecSpine_pad_pos_not_intoBytes
    {layouts : LayoutTable} {ty : Ty} {αs : List Type}
    (pc : PlacedCodecSpine αs) (totalSize : Nat)
    (hWidth : pc.realizedWidth totalSize = totalSize)
    (m : MirValueCodec layouts ty (FieldTuple αs) totalSize)
    (hCodec : m.codec = (pc.realizedCodec totalSize).castWidth hWidth := by rfl)
    (hPos : 0 < pc.realizedLead + (pc.realizedSpine totalSize).totalPadBytes)
    (x₀ : FieldTuple αs) :
    allBytesInitialized (m.codec.encode x₀) = false ∧
    ¬ m.codec.IsInitCodec ∧
    ¬ IsIntoBytes layouts ty := by
  have hUninit : allBytesInitialized (m.codec.encode x₀) = false := by
    rw [hCodec, FixedByteCodec.castWidth_encode]
    exact pc.realizedCodec_encode_uninit_of_pad_pos totalSize hPos x₀
  have hNotInit : ¬ m.codec.IsInitCodec := fun hInit => by
    have hTrue := hInit x₀
    rw [hUninit] at hTrue
    nomatch hTrue
  exact ⟨hUninit, hNotInit, m.not_isIntoBytes_of_uninit_encode x₀ hUninit⟩

/--
Declaration-order `PlacedCodecSpine` for the 3-field reordered tuple `(u8, u32, ())` where
field 0 (`u8`, 1 byte) sits at offset `4`, field 1 (`u32`, 4 bytes) sits at offset `0`, and
field 2 (`()`, 0-byte `1-ZST`) sits at offset `5`.
-/
def u8u32UnitPermutedPlaced :
    PlacedCodecSpine
      [{ bits : Nat // bits < 2 ^ (8 * uintByteSize .u8) },
       { bits : Nat // bits < 2 ^ (8 * uintByteSize .u32) },
       Unit] :=
  .cons (4, ⟨1, 1⟩) (FixedByteCodec.uintBitsLE 1 (by decide))
    (.cons (0, ⟨4, 4⟩) (FixedByteCodec.uintBitsLE 4 (by decide))
      (.cons (5, ⟨0, 1⟩) FixedByteCodec.unit .nil))

theorem u8u32UnitPermutedPlaced_realizedWidth (trail : Nat) :
    u8u32UnitPermutedPlaced.realizedWidth (5 + trail) = 5 + trail := by
  change 0 + ((4 + 0) + ((1 + 0) + ((0 + 0) + ((5 + trail) - 5)))) = 5 + trail
  omega

/-- Declaration-order `TupleFieldCodecs` of the `(u8, u32, ())` tuple fields. -/
def u8u32UnitPermutedFieldCodecs (layouts : LayoutTable) :
    TupleFieldCodecs layouts [.uint .u8, .uint .u32, .tuple []] u8u32UnitPermutedPlaced :=
  .cons (TupleFieldCodec.uint layouts .u8)
    (.cons (TupleFieldCodec.uint layouts .u32) (.cons (TupleFieldCodec.unit layouts) .nil))

/--
The reordered placement `u32 @ 0`, `u8 @ 4`, `() @ 5` is a sequential memory-order placement
within every total size `5 + trail`.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem u8u32UnitPermutedPlaced_sequential (trail : Nat) :
    SequentialFieldPlacement 0 (u8u32UnitPermutedPlaced.memSort.placed.map Prod.snd)
      (u8u32UnitPermutedPlaced.memSort.placed.map Prod.fst) (5 + trail) :=
  .cons (Nat.le_refl 0) (.cons (Nat.le_refl 4) (.cons (Nat.le_refl 5)
    (.nil (Nat.le_add_right 5 trail))))

/--
Concrete 3-field `MirValueCodec` for `(u8, u32, ())` laid out with reordered field offsets
`[{ bytes := 4 }, { bytes := 0 }, { bytes := 5 }]` and parametric trailing padding `trail : Nat`
(`l.size = { bytes := 5 + trail }`), obtained from the general `MirValueCodec.ofPlacedCodecSpine`:
no bespoke `encodeValueToBytes` / `decodeValueFromBytes` proof is needed.
-/
def u8u32UnitPermutedArbitraryTuple
    (layouts : LayoutTable) (trail : Nat) (idx : LayoutIdx) (l : TypeLayout)
    (memoryIndex : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size = { bytes := 5 + trail })
    (hFields : l.fields =
      .arbitrary [{ bytes := 4 }, { bytes := 0 }, { bytes := 5 }] memoryIndex) :
    MirValueCodec layouts { kind := .tuple [.uint .u8, .uint .u32, .tuple []], layoutIdx := idx }
      (FieldTuple
        [{ bits : Nat // bits < 2 ^ (8 * uintByteSize .u8) },
         { bits : Nat // bits < 2 ^ (8 * uintByteSize .u32) },
         Unit])
      (5 + trail) :=
  ofPlacedCodecSpine layouts idx l memoryIndex u8u32UnitPermutedPlaced (5 + trail)
    (u8u32UnitPermutedFieldCodecs layouts) hLookup hSize hFields
    (u8u32UnitPermutedPlaced_sequential trail)

/--
Universal `IsFromBytes`, `IsFromZeros`, and `IsTryFromBytes` for the 3-field permuted tuple
`(u8, u32, ())` across all trailing padding widths `trail : Nat`.

Kind: safety
Witness: universal
Assumes: S0
Subject: MirValueCodec.u8u32UnitPermutedArbitraryTuple
-/
theorem u8u32UnitPermutedArbitraryTuple_isFromBytes_all_trail
    (layouts : LayoutTable) (trail : Nat) (idx : LayoutIdx) (l : TypeLayout)
    (memoryIndex : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size = { bytes := 5 + trail })
    (hFields : l.fields =
      .arbitrary [{ bytes := 4 }, { bytes := 0 }, { bytes := 5 }] memoryIndex) :
    let m := u8u32UnitPermutedArbitraryTuple layouts trail idx l memoryIndex hLookup hSize hFields
    m.codec.IsSurjectiveInitDecoder ∧
    IsFromBytes layouts { kind := .tuple [.uint .u8, .uint .u32, .tuple []], layoutIdx := idx } ∧
    IsFromZeros layouts { kind := .tuple [.uint .u8, .uint .u32, .tuple []], layoutIdx := idx } ∧
    IsTryFromBytes layouts { kind := .tuple [.uint .u8, .uint .u32, .tuple []], layoutIdx := idx } := by
  intro m
  exact ofPlacedCodecSpine_isFromBytes_all_pads
    u8u32UnitPermutedPlaced (5 + trail) (u8u32UnitPermutedPlaced_realizedWidth trail) m rfl
    ⟨FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 1 (by decide),
     FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 4 (by decide),
     FixedByteCodec.unit_isSurjectiveInitDecoder,
     trivial⟩

/--
Tight-world (`trail = 0`, `totalSize = 5`) `IsInitCodec`, `IsIntoBytes`, and `transmute_typed`
for the 3-field permuted tuple `(u8, u32, ())`.

Kind: safety
Witness: universal
Assumes: S0
Subject: MirValueCodec.u8u32UnitPermutedArbitraryTuple
-/
theorem u8u32UnitPermutedArbitraryTuple_trail_zero_isIntoBytes_and_transmute
    (layouts : LayoutTable) (idx : LayoutIdx) (l : TypeLayout)
    (memoryIndex : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size = { bytes := 5 + 0 })
    (hFields : l.fields =
      .arbitrary [{ bytes := 4 }, { bytes := 0 }, { bytes := 5 }] memoryIndex) :
    let m := u8u32UnitPermutedArbitraryTuple layouts 0 idx l memoryIndex hLookup hSize hFields
    m.codec.IsInitCodec ∧
    IsIntoBytes layouts { kind := .tuple [.uint .u8, .uint .u32, .tuple []], layoutIdx := idx } ∧
    ∀ {dstTy : Ty} {β : Type} (mDst : MirValueCodec layouts dstTy β (5 + 0)),
      mDst.codec.IsSurjectiveInitDecoder →
      ∀ x, ∃ y : β,
        mDst.codec.decode (m.codec.encode x) = some y ∧
        decodeValueFromBytes defaultCodecFuel layouts dstTy (m.codec.encode x) =
          some (mDst.toValue y) := by
  intro m
  exact ofPlacedCodecSpine_zero_pad_isIntoBytes_and_transmute_typed
    u8u32UnitPermutedPlaced (5 + 0) (u8u32UnitPermutedPlaced_realizedWidth 0) m rfl rfl rfl
    ⟨FixedByteCodec.uintBitsLE_isInitCodec 1 (by decide),
     FixedByteCodec.uintBitsLE_isInitCodec 4 (by decide),
     FixedByteCodec.unit_isInitCodec,
     trivial⟩

/--
Padded-world (`0 < trail`) `.uninit` emission, `¬ IsInitCodec`, and `¬ IsIntoBytes` for the
3-field permuted tuple `(u8, u32, ())`.

Kind: divergence
Witness: negative
Assumes: S0
Subject: MirValueCodec.u8u32UnitPermutedArbitraryTuple
-/
theorem u8u32UnitPermutedArbitraryTuple_trail_pos_not_intoBytes
    (layouts : LayoutTable) (trail : Nat) (idx : LayoutIdx) (l : TypeLayout)
    (memoryIndex : List Nat)
    (hTrailPos : 0 < trail)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size = { bytes := 5 + trail })
    (hFields : l.fields =
      .arbitrary [{ bytes := 4 }, { bytes := 0 }, { bytes := 5 }] memoryIndex) :
    let m := u8u32UnitPermutedArbitraryTuple layouts trail idx l memoryIndex hLookup hSize hFields
    ¬ m.codec.IsInitCodec ∧
    ¬ IsIntoBytes layouts { kind := .tuple [.uint .u8, .uint .u32, .tuple []], layoutIdx := idx } := by
  intro m
  have hPadPos :
      0 < u8u32UnitPermutedPlaced.realizedLead +
        (u8u32UnitPermutedPlaced.realizedSpine (5 + trail)).totalPadBytes := by
    change 0 < 0 + (0 + (0 + (0 + ((5 + trail) - 5))))
    omega
  let x₀ : FieldTuple
      [{ bits : Nat // bits < 2 ^ (8 * uintByteSize .u8) },
       { bits : Nat // bits < 2 ^ (8 * uintByteSize .u32) },
       Unit] :=
    (⟨0, by decide⟩, ⟨0, by decide⟩, (), ())
  have ⟨_, hNotInit, hNotInto⟩ :=
    ofPlacedCodecSpine_pad_pos_not_intoBytes
      u8u32UnitPermutedPlaced (5 + trail) (u8u32UnitPermutedPlaced_realizedWidth trail)
      m rfl hPadPos x₀
  exact ⟨hNotInit, hNotInto⟩

/--
Declaration-order `PlacedCodecSpine` for the 2-field unsigned integer tuple `(u₁, u₂)` with
field 0 at byte offset `0` and field 1 at byte offset `uintByteSize w₁ + pad₁`.
-/
def uintPairPlaced (w₁ w₂ : UintTy) (pad₁ : Nat) :
    PlacedCodecSpine
      [{ bits : Nat // bits < 2 ^ (8 * uintByteSize w₁) },
       { bits : Nat // bits < 2 ^ (8 * uintByteSize w₂) }] :=
  .cons (0, ⟨uintByteSize w₁, uintByteSize w₁⟩)
    (FixedByteCodec.uintBitsLE (uintByteSize w₁) (uintByteSize_pos w₁))
    (.cons (uintByteSize w₁ + pad₁, ⟨uintByteSize w₂, uintByteSize w₂⟩)
      (FixedByteCodec.uintBitsLE (uintByteSize w₂) (uintByteSize_pos w₂))
      .nil)

/-- Declaration-order `TupleFieldCodecs` for `uintPairPlaced w₁ w₂ pad₁`. -/
def uintPairPlacedFieldCodecs (layouts : LayoutTable) (w₁ w₂ : UintTy) (pad₁ : Nat) :
    TupleFieldCodecs layouts [.uint w₁, .uint w₂] (uintPairPlaced w₁ w₂ pad₁) :=
  .cons (TupleFieldCodec.uint layouts w₁)
    (.cons (TupleFieldCodec.uint layouts w₂) .nil)

/--
Every 2-field integer placement `uintPairPlaced w₁ w₂ pad₁` is a sequential memory-order placement
within `(uintByteSize w₁ + pad₁) + (uintByteSize w₂ + pad₂)`.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem uintPairPlaced_sequential (w₁ w₂ : UintTy) (pad₁ pad₂ : Nat) :
    SequentialFieldPlacement 0
      ((uintPairPlaced w₁ w₂ pad₁).memSort.placed.map Prod.snd)
      ((uintPairPlaced w₁ w₂ pad₁).memSort.placed.map Prod.fst)
      ((uintByteSize w₁ + pad₁) + (uintByteSize w₂ + pad₂)) := by
  have hMemSort :
      (uintPairPlaced w₁ w₂ pad₁).memSort.placed =
        [(0, ⟨uintByteSize w₁, uintByteSize w₁⟩),
         (uintByteSize w₁ + pad₁, ⟨uintByteSize w₂, uintByteSize w₂⟩)] := by
    rw [PlacedCodecSpine.placed_memSort]
    dsimp only [uintPairPlaced, PlacedCodecSpine.placed, Anneal.ByteCodec.memSort,
      Anneal.ByteCodec.memInsert]
    have hKey :
        memKey (0, ⟨uintByteSize w₁, uintByteSize w₁⟩) ≤
          memKey (uintByteSize w₁ + pad₁, ⟨uintByteSize w₂, uintByteSize w₂⟩) := by
      cases w₁ <;> cases w₂ <;>
        dsimp only [memKey, nzBit, uintByteSize] <;> omega
    exact ite_eq_left_iff.mpr (fun hNot => absurd hKey hNot)
  rw [hMemSort]
  dsimp only [List.map]
  exact .cons (Nat.le_refl 0)
    (.cons (by dsimp only; omega) (.nil (by dsimp only; omega)))

/--
2-field unsigned integer tuple `MirValueCodec` instantiated directly from the general
$k$-field `MirValueCodec.ofPlacedCodecSpine` over `uintPairPlaced w₁ w₂ pad₁`.
-/
def uintPairArbitraryTupleOfPlacedCodecSpine
    (layouts : LayoutTable) (w₁ w₂ : UintTy) (pad₁ pad₂ : Nat)
    (idx : LayoutIdx) (l : TypeLayout) (memoryIndex : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size = { bytes := (uintByteSize w₁ + pad₁) + (uintByteSize w₂ + pad₂) })
    (hFields : l.fields =
      .arbitrary [{ bytes := 0 }, { bytes := uintByteSize w₁ + pad₁ }] memoryIndex) :
    MirValueCodec layouts { kind := .tuple [.uint w₁, .uint w₂], layoutIdx := idx }
      (FieldTuple
        [{ bits : Nat // bits < 2 ^ (8 * uintByteSize w₁) },
         { bits : Nat // bits < 2 ^ (8 * uintByteSize w₂) }])
      ((uintByteSize w₁ + pad₁) + (uintByteSize w₂ + pad₂)) :=
  ofPlacedCodecSpine layouts idx l memoryIndex (uintPairPlaced w₁ w₂ pad₁)
    ((uintByteSize w₁ + pad₁) + (uintByteSize w₂ + pad₂))
    (uintPairPlacedFieldCodecs layouts w₁ w₂ pad₁)
    hLookup hSize hFields (uintPairPlaced_sequential w₁ w₂ pad₁ pad₂)

/--
**Parametric Equivalence of `uintPairArbitraryTuple` and `ofPlacedCodecSpine`**: for all unsigned
integer widths `w₁, w₂` and all inter-field/trailing padding widths `pad₁, pad₂`, the 2-field
`MirValueCodec.uintPairArbitraryTuple` and the general $k$-field `MirValueCodec.ofPlacedCodecSpine`
instantiation `uintPairArbitraryTupleOfPlacedCodecSpine` have identical runtime `toValue` embeddings,
identical `encode` byte sequences, and identical `decode` results on every byte buffer `bs`.

Kind: refinement
Witness: universal
Assumes: S0
Subject: MirValueCodec.uintPairArbitraryTuple
-/
theorem uintPairArbitraryTuple_eq_ofPlacedCodecSpine
    (layouts : LayoutTable) (w₁ w₂ : UintTy) (pad₁ pad₂ : Nat)
    (idx : LayoutIdx) (l : TypeLayout) (memoryIndex : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size = { bytes := (uintByteSize w₁ + pad₁) + (uintByteSize w₂ + pad₂) })
    (hFields : l.fields =
      .arbitrary [{ bytes := 0 }, { bytes := uintByteSize w₁ + pad₁ }] memoryIndex) :
    let mPair := uintPairArbitraryTuple layouts w₁ w₂ pad₁ pad₂ idx l memoryIndex
      hLookup hSize hFields
    let mGen := uintPairArbitraryTupleOfPlacedCodecSpine layouts w₁ w₂ pad₁ pad₂ idx l memoryIndex
      hLookup hSize hFields
    (∀ x₁ x₂, mPair.toValue (x₁, x₂) = mGen.toValue (x₁, x₂, ())) ∧
    (∀ x₁ x₂, mPair.codec.encode (x₁, x₂) = mGen.codec.encode (x₁, x₂, ())) ∧
    (∀ bs, (mPair.codec.decode bs).map (fun p => (p.1, p.2, ())) = mGen.codec.decode bs) := by
  intro mPair mGen
  have hToVal : ∀ x₁ x₂, mPair.toValue (x₁, x₂) = mGen.toValue (x₁, x₂, ()) :=
    fun _ _ => rfl
  refine ⟨hToVal, fun x₁ x₂ => ?_, fun bs => ?_⟩
  · have hE1 := mPair.encode_toValue (x₁, x₂)
    have hE2 := mGen.encode_toValue (x₁, x₂, ())
    rw [hToVal x₁ x₂] at hE1
    exact Option.some.inj (hE1.symm.trans hE2)
  · have hD1 := mPair.decode_eq_map bs
    have hD2 := mGen.decode_eq_map bs
    have hMapEq : (mPair.codec.decode bs).map mPair.toValue =
        (mGen.codec.decode bs).map mGen.toValue :=
      hD1.symm.trans hD2
    have hBind := congrArg (fun o : Option Value => o.bind mGen.ofValue) hMapEq
    cases hP : mPair.codec.decode bs with
    | none =>
      rw [hP] at hBind
      cases hG : mGen.codec.decode bs with
      | none => rfl
      | some y =>
        rw [hG] at hBind
        dsimp only [Option.map, Option.bind] at hBind
        rw [mGen.ofValue_toValue y] at hBind
        nomatch hBind
    | some p =>
      rcases p with ⟨x₁, x₂⟩
      rw [hP] at hBind
      dsimp only [Option.map, Option.bind] at hBind ⊢
      rw [hToVal x₁ x₂, mGen.ofValue_toValue (x₁, x₂, ())] at hBind
      cases hG : mGen.codec.decode bs with
      | none =>
        rw [hG] at hBind
        nomatch hBind
      | some y =>
        rw [hG] at hBind
        dsimp only [Option.map, Option.bind] at hBind
        rw [mGen.ofValue_toValue y] at hBind
        exact hBind

end MirValueCodec

/-- Concrete `#[repr(Rust)]` 3-field reordered layout for `(u8, u32, ())` (`size = 8`, `align = 4`,
offsets `[4, 0, 5]`, `memoryIndex = [1, 0, 2]`, `trail = 3`). -/
def u8u32UnitPermutedLayout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨4⟩, backendRepr := .memory,
    fields := .arbitrary [⟨4⟩, ⟨0⟩, ⟨5⟩] [1, 0, 2], variants := .single 0, isUninhabited := false }

/-- Concrete single-entry `LayoutTable` holding `u8u32UnitPermutedLayout` at index `0`. -/
def u8u32UnitPermutedLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [u8u32UnitPermutedLayout] }

/--
Concrete 3-field permuted MIR witness: `(u8, u32, ())` at `u8u32UnitPermutedLayouts` is NOT
`BitValidity.IsIntoBytes`, while still `IsFromBytes`, `IsFromZeros`, and `IsTryFromBytes`.

Kind: divergence
Witness: negative
Assumes: S0
Subject: u8u32UnitPermutedLayouts
-/
theorem u8u32UnitPermutedLayouts_not_isIntoBytes_but_isFromBytes :
    ¬ IsIntoBytes u8u32UnitPermutedLayouts
        { kind := .tuple [.uint .u8, .uint .u32, .tuple []], layoutIdx := 0 } ∧
    IsFromBytes u8u32UnitPermutedLayouts
        { kind := .tuple [.uint .u8, .uint .u32, .tuple []], layoutIdx := 0 } :=
  ⟨(MirValueCodec.u8u32UnitPermutedArbitraryTuple_trail_pos_not_intoBytes
      u8u32UnitPermutedLayouts 3 0 u8u32UnitPermutedLayout [1, 0, 2] (by decide) rfl rfl rfl).2,
   (MirValueCodec.u8u32UnitPermutedArbitraryTuple_isFromBytes_all_trail
      u8u32UnitPermutedLayouts 3 0 u8u32UnitPermutedLayout [1, 0, 2] rfl rfl rfl).2.1⟩

/--
Universal `FromBytes`, `FromZeros`, and `TryFromBytes` preservation on
`MirValueCodec.uintPairArbitraryTuple`: for **every** inter-field padding `pad₁` and
trailing padding `pad₂`, the laid-out integer pair satisfies `IsFromBytes`,
`IsFromZeros`, and `IsTryFromBytes` in `Anneal.BitValidity`.

Kind: safety
Witness: universal
Assumes: S0
Subject: MirValueCodec.uintPairArbitraryTuple
-/
theorem uintPairArbitraryTuple_isFromBytes_all_pads
    (layouts : LayoutTable) (w₁ w₂ : UintTy) (pad₁ pad₂ : Nat)
    (idx : LayoutIdx) (l : TypeLayout) (memoryIndex : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size = { bytes := (MirValueCodec.uintByteSize w₁ + pad₁) + (MirValueCodec.uintByteSize w₂ + pad₂) })
    (hFields : l.fields =
      .arbitrary [{ bytes := 0 }, { bytes := MirValueCodec.uintByteSize w₁ + pad₁ }] memoryIndex) :
    let m := MirValueCodec.uintPairArbitraryTuple layouts w₁ w₂ pad₁ pad₂ idx l memoryIndex
      hLookup hSize hFields
    m.codec.IsSurjectiveInitDecoder ∧
    IsFromBytes layouts { kind := .tuple [.uint w₁, .uint w₂], layoutIdx := idx } ∧
    IsFromZeros layouts { kind := .tuple [.uint w₁, .uint w₂], layoutIdx := idx } ∧
    IsTryFromBytes layouts { kind := .tuple [.uint w₁, .uint w₂], layoutIdx := idx } := by
  intro m
  have hSurj : m.codec.IsSurjectiveInitDecoder :=
    laidOutPair_isSurjectiveInitDecoder pad₁ pad₂
      (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder
        (MirValueCodec.uintByteSize w₁) (MirValueCodec.uintByteSize_pos w₁))
      (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder
        (MirValueCodec.uintByteSize w₂) (MirValueCodec.uintByteSize_pos w₂))
  have hFb := m.isFromBytes hSurj
  exact ⟨hSurj, hFb, isFromBytes_implies_isFromZeros _ _ hFb, isFromBytes_implies_isTryFromBytes _ _ hFb⟩

/--
Concrete MIR-level instance of the padding rejection:
`MirValueCodec.uintPairArbitraryTuple` with positive padding fails `IsInitCodec` and
`BitValidity.IsIntoBytes`. The underlying codec is the declaration-order symbolic world
`⟨0, pad₁, pad₂, false⟩` (`uintPairArbitraryTuple_encode_eq_symbolicPad`).

Kind: divergence
Witness: negative
Assumes: S0
Subject: MirValueCodec.uintPairArbitraryTuple
-/
theorem uintPairArbitraryTuple_pad_pos_not_intoBytes
    (layouts : LayoutTable) (w₁ w₂ : UintTy) (pad₁ pad₂ : Nat)
    (idx : LayoutIdx) (l : TypeLayout) (memoryIndex : List Nat)
    (hPadPos : 0 < pad₁ + pad₂)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size = { bytes := (MirValueCodec.uintByteSize w₁ + pad₁) + (MirValueCodec.uintByteSize w₂ + pad₂) })
    (hFields : l.fields =
      .arbitrary [{ bytes := 0 }, { bytes := MirValueCodec.uintByteSize w₁ + pad₁ }] memoryIndex) :
    let m := MirValueCodec.uintPairArbitraryTuple layouts w₁ w₂ pad₁ pad₂ idx l memoryIndex
      hLookup hSize hFields
    ¬ m.codec.IsInitCodec ∧
    ¬ IsIntoBytes layouts { kind := .tuple [.uint w₁, .uint w₂], layoutIdx := idx } := by
  intro m
  let x₀ : { bits : Nat // bits < 2 ^ (8 * MirValueCodec.uintByteSize w₁) } :=
    ⟨0, Nat.two_pow_pos _⟩
  let y₀ : { bits : Nat // bits < 2 ^ (8 * MirValueCodec.uintByteSize w₂) } :=
    ⟨0, Nat.two_pow_pos _⟩
  have hNotInit : ¬ m.codec.IsInitCodec := by
    intro hInit
    have hIff := (laidOutPair_isInitCodec_iff
      (FixedByteCodec.uintBitsLE (MirValueCodec.uintByteSize w₁) (MirValueCodec.uintByteSize_pos w₁))
      (FixedByteCodec.uintBitsLE (MirValueCodec.uintByteSize w₂) (MirValueCodec.uintByteSize_pos w₂))
      x₀ y₀).mp hInit
    omega
  refine ⟨hNotInit, ?_⟩
  have hUninit : allBytesInitialized (m.codec.encode (x₀, y₀)) = false := by
    cases hB : allBytesInitialized (m.codec.encode (x₀, y₀)) with
    | false => rfl
    | true =>
      dsimp only [m, MirValueCodec.uintPairArbitraryTuple, MirValueCodec.ofCanonicalEncode,
                  FixedByteCodec.prod, FixedByteCodec.padRight, FixedByteCodec.mapEquiv,
                  FixedByteCodec.padUninit, FixedByteCodec.ofRoundTrip] at hB
      rcases Nat.eq_zero_or_pos pad₁ with rfl | hp1
      · have hp2 : 0 < pad₂ := by omega
        have hRightFalse :
            allBytesInitialized
              ((FixedByteCodec.uintBitsLE (MirValueCodec.uintByteSize w₂) (MirValueCodec.uintByteSize_pos w₂)).encode y₀ ++
                replicateUninitBytes pad₂) = false :=
          allBytesInitialized_append_eq_false_right _
            (allBytesInitialized_replicateUninitBytes_eq_false hp2)
        rw [allBytesInitialized_append_eq_false_right _ hRightFalse] at hB
        nomatch hB
      · have hLeftFalse :
            allBytesInitialized
              ((FixedByteCodec.uintBitsLE (MirValueCodec.uintByteSize w₁) (MirValueCodec.uintByteSize_pos w₁)).encode x₀ ++
                replicateUninitBytes pad₁) = false :=
          allBytesInitialized_append_eq_false_right _
            (allBytesInitialized_replicateUninitBytes_eq_false hp1)
        rw [allBytesInitialized_append_eq_false_left _ hLeftFalse] at hB
        nomatch hB
  exact m.not_isIntoBytes_of_uninit_encode (x₀, y₀) hUninit

/--
The `uintPairArbitraryTuple` codec is byte-for-byte the declaration-order symbolic pair world
`⟨0, pad₁, pad₂, false⟩`, connecting the concrete MIR codec to `SymbolicPairPad`.

Kind: refinement
Witness: universal
Assumes: S0
Subject: MirValueCodec.uintPairArbitraryTuple
-/
theorem uintPairArbitraryTuple_encode_eq_symbolicPad
    (layouts : LayoutTable) (w₁ w₂ : UintTy) (pad₁ pad₂ : Nat)
    (idx : LayoutIdx) (l : TypeLayout) (memoryIndex : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size = { bytes := (MirValueCodec.uintByteSize w₁ + pad₁) + (MirValueCodec.uintByteSize w₂ + pad₂) })
    (hFields : l.fields =
      .arbitrary [{ bytes := 0 }, { bytes := MirValueCodec.uintByteSize w₁ + pad₁ }] memoryIndex)
    (x : { bits : Nat // bits < 2 ^ (8 * MirValueCodec.uintByteSize w₁) } ×
      { bits : Nat // bits < 2 ^ (8 * MirValueCodec.uintByteSize w₂) }) :
    (MirValueCodec.uintPairArbitraryTuple layouts w₁ w₂ pad₁ pad₂ idx l memoryIndex
        hLookup hSize hFields).codec.encode x =
      (laidOutPairSymbolicPad ⟨0, pad₁, pad₂, false⟩
        (FixedByteCodec.uintBitsLE (MirValueCodec.uintByteSize w₁) (MirValueCodec.uintByteSize_pos w₁))
        (FixedByteCodec.uintBitsLE (MirValueCodec.uintByteSize w₂) (MirValueCodec.uintByteSize_pos w₂))).encode x :=
  rfl

/-- Concrete `#[repr(C)]`-shaped `(u8, u32)` layout (`size = 8`, `align = 4`, field offsets
`[0, 4]`): alignment *forces* 3 inter-field padding bytes in every valid world. -/
def u8u32PairLayout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨4⟩, backendRepr := .memory,
    fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1], variants := .single 0, isUninhabited := false }

/-- Concrete single-entry `LayoutTable` holding `u8u32PairLayout` at index `0`. -/
def u8u32PairLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [u8u32PairLayout] }

/--
Fully concrete, non-vacuous MIR-level rejection witness: the `(u8, u32)` tuple at
`u8u32PairLayouts` is NOT `BitValidity.IsIntoBytes`, while still `IsFromBytes`.

Kind: divergence
Witness: negative
Assumes: S0
Subject: u8u32PairLayouts
-/
theorem u8u32PairLayouts_not_isIntoBytes_but_isFromBytes :
    ¬ IsIntoBytes u8u32PairLayouts { kind := .tuple [.uint .u8, .uint .u32], layoutIdx := 0 } ∧
    IsFromBytes u8u32PairLayouts { kind := .tuple [.uint .u8, .uint .u32], layoutIdx := 0 } :=
  ⟨(uintPairArbitraryTuple_pad_pos_not_intoBytes u8u32PairLayouts .u8 .u32 3 0 0
      u8u32PairLayout [0, 1] (by decide) rfl rfl rfl).2,
   (uintPairArbitraryTuple_isFromBytes_all_pads u8u32PairLayouts .u8 .u32 3 0 0
      u8u32PairLayout [0, 1] rfl rfl rfl).2.1⟩

/--
Pinned `S3` (`pinned_compiler_coupled`) soundness certificate: when a `#[repr(Rust)]`
or `#[repr(C)]` pair layout has `pad₁ = 0` and `pad₂ = 0`, `uintPairArbitraryTuple`
satisfies `IsInitCodec`, `IsIntoBytes`, `IsFromBytes`, and `transmute_sound` to any
same-sized `IsFromBytes` target.

anneal:pinned_compiler_coupled Zero-padding canonical tuple layout pinned to rustc ABI
pin:sha256:344a55b195dc

Kind: safety
Witness: universal
Assumes: S3
Subject: MirValueCodec.uintPairArbitraryTuple
-/
theorem pinnedZeroPadPair_isIntoBytes_and_transmute_sound
    (layouts : LayoutTable) (w₁ w₂ : UintTy)
    (idx : LayoutIdx) (l : TypeLayout) (memoryIndex : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size = { bytes := (MirValueCodec.uintByteSize w₁ + 0) + (MirValueCodec.uintByteSize w₂ + 0) })
    (hFields : l.fields =
      .arbitrary [{ bytes := 0 }, { bytes := MirValueCodec.uintByteSize w₁ + 0 }] memoryIndex) :
    let m := MirValueCodec.uintPairArbitraryTuple layouts w₁ w₂ 0 0 idx l memoryIndex
      hLookup hSize hFields
    m.codec.IsInitCodec ∧
    IsIntoBytes layouts { kind := .tuple [.uint w₁, .uint w₂], layoutIdx := idx } ∧
    ∀ {dstTy : Ty} {β : Type}
      (mDst : MirValueCodec layouts dstTy β
        ((MirValueCodec.uintByteSize w₁ + 0) + (MirValueCodec.uintByteSize w₂ + 0))),
      mDst.codec.IsSurjectiveInitDecoder →
      ∀ x, ∃ y : β,
        mDst.codec.decode (m.codec.encode x) = some y ∧
        decodeValueFromBytes defaultCodecFuel layouts dstTy (m.codec.encode x) =
          some (mDst.toValue y) := by
  intro m
  have hInit : m.codec.IsInitCodec :=
    FixedByteCodec.prod_isInitCodec
      (FixedByteCodec.padRight_zero_isInitCodec
        (FixedByteCodec.uintBitsLE_isInitCodec
          (MirValueCodec.uintByteSize w₁) (MirValueCodec.uintByteSize_pos w₁)))
      (FixedByteCodec.padRight_zero_isInitCodec
        (FixedByteCodec.uintBitsLE_isInitCodec
          (MirValueCodec.uintByteSize w₂) (MirValueCodec.uintByteSize_pos w₂)))
  exact ⟨hInit, m.isIntoBytes hInit rfl,
    fun mDst hFrom x => MirValueCodec.transmute_typed m mDst hInit hFrom x⟩

/-! ## 9. Compact `UInt32` Enum Lookup & `FixedByteCodec` Isomorphism (`CompactEnumSpec` & `CompactEnumVal`) -/

/-- Extensionality on `UInt32` via `.toNat`. -/
theorem uint32_eq_of_toNat_eq {a b : UInt32} (h : a.toNat = b.toNat) : a = b :=
  UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

/-- Decidable check that a `List UInt32` is strictly increasing (`d₀ < d₁ < ...`). -/
@[reducible]
def isStrictlySortedList : List UInt32 → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => Nat.blt a.toNat b.toNat && isStrictlySortedList (b :: rest)

/-- Decidable check that an `Array UInt32` is strictly increasing. -/
@[reducible]
def isStrictlySortedArray (arr : Array UInt32) : Bool :=
  isStrictlySortedList arr.toList

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem isStrictlySortedList_iff_pairwise :
    ∀ xs : List UInt32, isStrictlySortedList xs = true ↔ List.Pairwise (· < ·) xs
  | [] => by simp [isStrictlySortedList]
  | [a] => by simp [isStrictlySortedList]
  | a :: b :: rest => by
    have ih := isStrictlySortedList_iff_pairwise (b :: rest)
    have hBlt : (Nat.blt a.toNat b.toNat = true) ↔ (a < b) := by
      rw [Nat.blt_eq]
      exact Iff.rfl
    simp only [isStrictlySortedList, Bool.and_eq_true, hBlt, ih, List.pairwise_cons]
    constructor
    · rintro ⟨hab, hbAll, hRest⟩
      refine ⟨fun x hx => ?_, hbAll, hRest⟩
      rcases List.mem_cons.mp hx with rfl | hMem
      · exact hab
      · exact UInt32.lt_trans hab (hbAll x hMem)
    · rintro ⟨hAll, hRest⟩
      exact ⟨hAll b (List.mem_cons_self ..), hRest⟩

/--
Compact `UInt32`-backed enum specification (`salikh` `cl/1018197791`):
replaces an $N$-constructor Lean `inductive` type with a single-constructor structure
indexed by a strictly sorted `Array UInt32` of valid discriminants and tag width
`tagByteWidth ∈ {1, 2, 4}`.
-/
structure CompactEnumSpec : Type where
  /-- Byte width of the integer discriminant tag (`1`, `2`, or `4`). -/
  tagByteWidth : Nat
  /-- Tag width is `u8` (`1`), `u16` (`2`), or `u32` (`4`). -/
  hTagWidth : tagByteWidth = 1 ∨ tagByteWidth = 2 ∨ tagByteWidth = 4
  /-- Strictly increasing table of valid `UInt32` discriminants. -/
  validDiscrs : Array UInt32
  /-- Kernel-checkable proof that `validDiscrs` is strictly sorted. -/
  hSorted : isStrictlySortedArray validDiscrs = true
  /-- Kernel-checkable proof that every discriminant fits in `8 * tagByteWidth` bits. -/
  hBounded : validDiscrs.toList.all (fun d => Nat.blt d.toNat (2 ^ (8 * tagByteWidth))) = true

namespace CompactEnumSpec

/-- Propositional well-formedness of a `CompactEnumSpec`. -/
def WF (spec : CompactEnumSpec) : Prop :=
  List.Pairwise (· < ·) spec.validDiscrs.toList ∧
  ∀ d ∈ spec.validDiscrs.toList, d.toNat < 2 ^ (8 * spec.tagByteWidth)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem wf (spec : CompactEnumSpec) : spec.WF := by
  refine ⟨(isStrictlySortedList_iff_pairwise spec.validDiscrs.toList).mp spec.hSorted, ?_⟩
  intro d hd
  have hAll := List.all_eq_true.mp spec.hBounded d hd
  exact Nat.blt_eq.mp hAll

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem tagByteWidth_pos (spec : CompactEnumSpec) : 0 < spec.tagByteWidth := by
  rcases spec.hTagWidth with h | h | h <;> omega

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem two_pow_tagBitWidth_le_u32_size (spec : CompactEnumSpec) :
    2 ^ (8 * spec.tagByteWidth) ≤ UInt32.size := by
  rcases spec.hTagWidth with h | h | h <;> rw [h] <;> decide

/--
Fuel-bounded binary search for `d` over the half-open index window `[lo, hi)` of a (strictly
sorted) discriminant table: `O(log n)` probes at runtime, and structural recursion on `fuel` so
that it also reduces in the kernel (no well-founded recursion).
-/
def bsearchDiscr (arr : Array UInt32) (d : UInt32) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, lo, hi =>
    if lo < hi then
      match arr[(lo + hi) / 2]? with
      | some v =>
        if d.toNat < v.toNat then bsearchDiscr arr d fuel lo ((lo + hi) / 2)
        else if v.toNat < d.toNat then bsearchDiscr arr d fuel ((lo + hi) / 2 + 1) hi
        else true
      | none => false
    else false

/--
**Binary Search Correctness**: on a strictly sorted table, `bsearchDiscr` over a window
`[lo, hi)` with enough fuel returns `true` exactly when `d` occurs in that window.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem bsearchDiscr_eq_true_iff (arr : Array UInt32) (d : UInt32)
    (hSorted : List.Pairwise (· < ·) arr.toList) :
    ∀ (fuel lo hi : Nat), hi ≤ arr.size → hi - lo ≤ fuel →
      (bsearchDiscr arr d fuel lo hi = true ↔
        ∃ i, lo ≤ i ∧ i < hi ∧ arr.toList[i]? = some d)
  | 0, lo, hi, _, hFuel => by
    constructor
    · intro h
      nomatch h
    · rintro ⟨i, h1, h2, _⟩
      omega
  | fuel + 1, lo, hi, hHi, hFuel => by
    have hLenEq : arr.toList.length = arr.size := Array.length_toList
    have hLt_iff : ∀ {i j : Nat} (hi : i < arr.toList.length) (hj : j < arr.toList.length),
        i < j → (arr.toList[i]).toNat < (arr.toList[j]).toNat :=
      fun hi hj hij => List.pairwise_iff_getElem.mp hSorted _ _ hi hj hij
    unfold bsearchDiscr
    by_cases hlt : lo < hi
    · simp only [hlt, ↓reduceIte]
      have hMidLo : lo ≤ (lo + hi) / 2 := by omega
      have hMidHi : (lo + hi) / 2 < hi := by omega
      have hMidLen : (lo + hi) / 2 < arr.toList.length := by omega
      have hGetArr : arr[(lo + hi) / 2]? = some (arr.toList[(lo + hi) / 2]) := by
        rw [← Array.getElem?_toList]
        exact List.getElem?_eq_getElem hMidLen
      rw [hGetArr]
      dsimp only
      by_cases hDlt : d.toNat < (arr.toList[(lo + hi) / 2]).toNat
      · simp only [hDlt, ↓reduceIte]
        rw [bsearchDiscr_eq_true_iff arr d hSorted fuel lo ((lo + hi) / 2) (by omega) (by omega)]
        constructor
        · rintro ⟨i, h1, h2, h3⟩
          exact ⟨i, h1, by omega, h3⟩
        · rintro ⟨i, h1, h2, h3⟩
          refine ⟨i, h1, ?_, h3⟩
          have hiLen : i < arr.toList.length := (List.getElem?_eq_some_iff.mp h3).1
          have hiEq : arr.toList[i] = d := (List.getElem?_eq_some_iff.mp h3).2
          rcases Nat.lt_or_ge i ((lo + hi) / 2) with hLt | hGe
          · exact hLt
          · rcases Nat.eq_or_lt_of_le hGe with hEq | hGt
            · subst hEq
              rw [hiEq] at hDlt
              omega
            · have := hLt_iff hMidLen hiLen hGt
              rw [hiEq] at this
              omega
      · simp only [hDlt, ↓reduceIte]
        by_cases hVlt : (arr.toList[(lo + hi) / 2]).toNat < d.toNat
        · simp only [hVlt, ↓reduceIte]
          rw [bsearchDiscr_eq_true_iff arr d hSorted fuel ((lo + hi) / 2 + 1) hi hHi (by omega)]
          constructor
          · rintro ⟨i, h1, h2, h3⟩
            exact ⟨i, by omega, h2, h3⟩
          · rintro ⟨i, h1, h2, h3⟩
            refine ⟨i, ?_, h2, h3⟩
            have hiLen : i < arr.toList.length := (List.getElem?_eq_some_iff.mp h3).1
            have hiEq : arr.toList[i] = d := (List.getElem?_eq_some_iff.mp h3).2
            rcases Nat.lt_or_ge ((lo + hi) / 2) i with hGt | hLe
            · omega
            · rcases Nat.eq_or_lt_of_le hLe with hEq | hLt
              · subst hEq
                rw [hiEq] at hVlt
                omega
              · have := hLt_iff hiLen hMidLen hLt
                rw [hiEq] at this
                omega
        · simp only [hVlt, ↓reduceIte]
          have hEqNat : d.toNat = (arr.toList[(lo + hi) / 2]).toNat := by omega
          have hEqD : arr.toList[(lo + hi) / 2] = d := uint32_eq_of_toNat_eq hEqNat.symm
          refine ⟨fun _ => ⟨(lo + hi) / 2, hMidLo, hMidHi, ?_⟩, fun _ => trivial⟩
          rw [List.getElem?_eq_getElem hMidLen, hEqD]
    · simp only [hlt, ↓reduceIte]
      constructor
      · intro h
        nomatch h
      · rintro ⟨i, h1, h2, _⟩
        omega

/--
`O(log n)` binary-search discriminant membership test over the strictly sorted table
`spec.validDiscrs` (proved equivalent to list membership by `isValidDiscr_eq_true_iff`).
-/
@[reducible]
def isValidDiscr (spec : CompactEnumSpec) (d : UInt32) : Bool :=
  bsearchDiscr spec.validDiscrs d spec.validDiscrs.size 0 spec.validDiscrs.size

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem isValidDiscr_eq_true_iff (spec : CompactEnumSpec) (d : UInt32) :
    spec.isValidDiscr d = true ↔ d ∈ spec.validDiscrs.toList := by
  unfold isValidDiscr
  rw [bsearchDiscr_eq_true_iff spec.validDiscrs d spec.wf.1 _ 0 _ (Nat.le_refl _) (by omega)]
  constructor
  · rintro ⟨i, _, _, hGet⟩
    exact List.mem_of_getElem? hGet
  · intro hMem
    obtain ⟨i, hGet⟩ := List.mem_iff_getElem?.mp hMem
    have hiLen : i < spec.validDiscrs.toList.length := (List.getElem?_eq_some_iff.mp hGet).1
    have hLenEq : spec.validDiscrs.toList.length = spec.validDiscrs.size := Array.length_toList
    exact ⟨i, Nat.zero_le _, by omega, hGet⟩

/--
Every `CompactEnumSpec` discriminant table is duplicate-free (strict sortedness implies `Nodup`).

Kind: helper
Witness: universal
Assumes: S0
-/
theorem nodup (spec : CompactEnumSpec) : spec.validDiscrs.toList.Nodup :=
  spec.wf.1.imp (fun h hEq => by subst hEq; exact Nat.lt_irrefl _ h)

/-- Every valid discriminant of `spec` fits in `2 ^ (8 * spec.tagByteWidth)`. -/
theorem toNat_lt_of_isValidDiscr (spec : CompactEnumSpec) {d : UInt32}
    (h : spec.isValidDiscr d = true) :
    d.toNat < 2 ^ (8 * spec.tagByteWidth) :=
  spec.wf.2 d ((spec.isValidDiscr_eq_true_iff d).mp h)

end CompactEnumSpec

/-- Alias for `CompactEnumSpec.bsearchDiscr`. -/
abbrev bsearchDiscr := CompactEnumSpec.bsearchDiscr

/-- Alias for `CompactEnumSpec.bsearchDiscr_eq_true_iff`. -/
abbrev bsearchDiscr_eq_true_iff := CompactEnumSpec.bsearchDiscr_eq_true_iff

/--
Single-constructor value of a `CompactEnumSpec` (`salikh` `cl/1018197791`):
avoids quadratic $N$-constructor Lean `inductive` eliminator generation while preserving
exact bit-pattern validity.
-/
structure CompactEnumVal (spec : CompactEnumSpec) : Type where
  /-- Underlying `UInt32` discriminant value. -/
  rawDiscr : UInt32
  /-- Membership certificate in `spec.validDiscrs`. -/
  valid : spec.isValidDiscr rawDiscr = true
  deriving DecidableEq

namespace CompactEnumVal

/-- Map a `CompactEnumVal spec` to its unsigned `Nat` tag. -/
@[reducible]
def toTag {spec : CompactEnumSpec} (v : CompactEnumVal spec) : Nat :=
  v.rawDiscr.toNat

/-- Attempt to construct a `CompactEnumVal spec` from a raw `Nat` tag. -/
@[reducible]
def ofTagNat (spec : CompactEnumSpec) (t : Nat) : Option (CompactEnumVal spec) :=
  if _hLt : t < 2 ^ (8 * spec.tagByteWidth) then
    let d := UInt32.ofNat t
    if hVal : spec.isValidDiscr d = true then
      some ⟨d, hVal⟩
    else
      none
  else
    none

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem toTag_lt (spec : CompactEnumSpec) (v : CompactEnumVal spec) :
    v.toTag < 2 ^ (8 * spec.tagByteWidth) :=
  spec.toNat_lt_of_isValidDiscr v.valid

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem uint32_ofNat_toNat_of_lt (spec : CompactEnumSpec) {t : Nat}
    (hLt : t < 2 ^ (8 * spec.tagByteWidth)) :
    (UInt32.ofNat t).toNat = t := by
  have hLe := spec.two_pow_tagBitWidth_le_u32_size
  have hLt32 : t < UInt32.size := Nat.lt_of_lt_of_le hLt hLe
  change t % UInt32.size = t
  exact Nat.mod_eq_of_lt hLt32

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem ofTagNat_toTag (spec : CompactEnumSpec) (v : CompactEnumVal spec) :
    ofTagNat spec v.toTag = some v := by
  rcases v with ⟨d, hVal⟩
  have hLt : d.toNat < 2 ^ (8 * spec.tagByteWidth) := spec.toNat_lt_of_isValidDiscr hVal
  have hOfNat : UInt32.ofNat d.toNat = d := UInt32.ofNat_toNat
  unfold ofTagNat toTag
  dsimp only
  simp only [hLt, ↓reduceDIte, hOfNat, hVal]

/--
Prefix-free fixed-width byte codec for `CompactEnumVal spec`, built directly via
`FixedByteCodec.enumRepr`.
-/
def byteCodec (spec : CompactEnumSpec) :
    FixedByteCodec (CompactEnumVal spec) spec.tagByteWidth :=
  FixedByteCodec.enumRepr
    spec.tagByteWidth
    spec.tagByteWidth_pos
    toTag
    (ofTagNat spec)
    (ofTagNat_toTag spec)
    (toTag_lt spec)

/--
Kind: codec
Witness: universal
Assumes: S0
Subject: CompactEnumVal.byteCodec
-/
theorem byteCodec_isExactWidth (spec : CompactEnumSpec) :
    (byteCodec spec).IsExactWidth :=
  FixedByteCodec.enumRepr_isExactWidth
    spec.tagByteWidth spec.tagByteWidth_pos toTag (ofTagNat spec)
    (ofTagNat_toTag spec) (toTag_lt spec)

/--
Kind: codec
Witness: universal
Assumes: S0
Subject: CompactEnumVal.byteCodec
-/
theorem byteCodec_isInitCodec (spec : CompactEnumSpec) :
    (byteCodec spec).IsInitCodec :=
  FixedByteCodec.enumRepr_isInitCodec
    spec.tagByteWidth spec.tagByteWidth_pos toTag (ofTagNat spec)
    (ofTagNat_toTag spec) (toTag_lt spec)

/--
`CompactEnumVal.byteCodec spec` satisfies `HasZeroValid` (`FromZeros`) iff `0` is a valid
discriminant in `spec.validDiscrs`.

Kind: codec
Witness: universal
Assumes: S0
Subject: CompactEnumVal.byteCodec
-/
theorem byteCodec_hasZeroValid_iff (spec : CompactEnumSpec) :
    (byteCodec spec).HasZeroValid ↔ spec.isValidDiscr 0 = true := by
  rw [byteCodec, FixedByteCodec.enumRepr_hasZeroValid_iff]
  constructor
  · rintro ⟨⟨d, hVal⟩, hToTag⟩
    unfold toTag at hToTag
    have hd0 : d = 0 := uint32_eq_of_toNat_eq hToTag
    subst hd0
    exact hVal
  · intro hVal0
    exact ⟨⟨0, hVal0⟩, rfl⟩

/--
If any tag `d : UInt32` within `2 ^ (8 * spec.tagByteWidth)` is absent from
`spec.validDiscrs`, `CompactEnumVal.byteCodec spec` has a niche and is NOT
`IsSurjectiveInitDecoder` (`¬ FromBytes`).

Kind: codec
Witness: negative
Assumes: S0
Subject: CompactEnumVal.byteCodec
-/
theorem byteCodec_not_isSurjectiveInitDecoder_of_missing (spec : CompactEnumSpec)
    {d : UInt32} (hLt : d.toNat < 2 ^ (8 * spec.tagByteWidth))
    (hMissing : spec.isValidDiscr d = false) :
    ¬ (byteCodec spec).IsSurjectiveInitDecoder := by
  apply FixedByteCodec.enumRepr_not_isSurjectiveInitDecoder
    spec.tagByteWidth spec.tagByteWidth_pos toTag (ofTagNat spec)
    (ofTagNat_toTag spec) (toTag_lt spec) hLt
  intro ⟨d', hVal'⟩ hEq
  unfold toTag at hEq
  have hdEq : d' = d := uint32_eq_of_toNat_eq hEq
  subst hdEq
  rw [hMissing] at hVal'
  nomatch hVal'

/--
Conversely, if every `bits < 2 ^ (8 * spec.tagByteWidth)` is a valid discriminant in
`spec.validDiscrs` (e.g., an exhaustive 256-variant `#[repr(u8)]` enum),
`CompactEnumVal.byteCodec spec` IS `IsSurjectiveInitDecoder` (`FromBytes`).

Kind: codec
Witness: universal
Assumes: S0
Subject: CompactEnumVal.byteCodec
-/
theorem byteCodec_isSurjectiveInitDecoder_of_all_valid (spec : CompactEnumSpec)
    (hCover : ∀ bits : Nat, bits < 2 ^ (8 * spec.tagByteWidth) →
      spec.isValidDiscr (UInt32.ofNat bits) = true) :
    (byteCodec spec).IsSurjectiveInitDecoder := by
  apply FixedByteCodec.enumRepr_isSurjectiveInitDecoder
    spec.tagByteWidth spec.tagByteWidth_pos toTag (ofTagNat spec)
    (ofTagNat_toTag spec) (toTag_lt spec)
  intro bits hLt
  refine ⟨⟨UInt32.ofNat bits, hCover bits hLt⟩, ?_⟩
  exact uint32_ofNat_toNat_of_lt spec hLt

/--
**Codec Isomorphism with `FixedByteCodec.enumRepr`**:
For any inductive/custom enum type `ε` equipped with `toTagΕ : ε → Nat` and
`ofTagΕ : Nat → Option ε` that has the same valid tag set as `spec`, `CompactEnumVal spec`
and `ε` have byte-for-byte identical encodings and decodings.

Kind: refinement
Witness: universal
Assumes: S0
Subject: CompactEnumVal.byteCodec
-/
theorem byteCodec_equiv_enumRepr (spec : CompactEnumSpec) {ε : Type}
    (toTagΕ : ε → Nat) (ofTagΕ : Nat → Option ε)
    (hRoundΕ : ∀ e : ε, ofTagΕ (toTagΕ e) = some e)
    (hBoundsΕ : ∀ e : ε, toTagΕ e < 2 ^ (8 * spec.tagByteWidth))
    (toCompact : ε → CompactEnumVal spec)
    (ofCompact : CompactEnumVal spec → ε)
    (hToTagPreserve : ∀ e : ε, (toCompact e).toTag = toTagΕ e)
    (_hLeftInv : ∀ e : ε, ofCompact (toCompact e) = e)
    (hRightInv : ∀ v : CompactEnumVal spec, toCompact (ofCompact v) = v) :
    (∀ e : ε,
      (byteCodec spec).encode (toCompact e) =
        (FixedByteCodec.enumRepr spec.tagByteWidth spec.tagByteWidth_pos
          toTagΕ ofTagΕ hRoundΕ hBoundsΕ).encode e) ∧
    (∀ bs : List AbstractByte,
      ((byteCodec spec).decode bs).map ofCompact =
        (FixedByteCodec.enumRepr spec.tagByteWidth spec.tagByteWidth_pos
          toTagΕ ofTagΕ hRoundΕ hBoundsΕ).decode bs) := by
  refine ⟨fun e => ?_, fun bs => ?_⟩
  · unfold byteCodec FixedByteCodec.enumRepr FixedByteCodec.uintBitsLE FixedByteCodec.ofRoundTrip
    dsimp only
    rw [hToTagPreserve e]
  · cases hDec : (byteCodec spec).decode bs with
    | none =>
      dsimp only [Option.map]
      cases hEDec : (FixedByteCodec.enumRepr spec.tagByteWidth spec.tagByteWidth_pos
          toTagΕ ofTagΕ hRoundΕ hBoundsΕ).decode bs with
      | none => rfl
      | some e =>
        have hBase := (FixedByteCodec.enumRepr_decode_eq_some_iff
          spec.tagByteWidth spec.tagByteWidth_pos toTagΕ ofTagΕ hRoundΕ hBoundsΕ bs e).mp hEDec
        have hMust : (byteCodec spec).decode bs = some (toCompact e) := by
          apply (FixedByteCodec.enumRepr_decode_eq_some_iff
            spec.tagByteWidth spec.tagByteWidth_pos toTag (ofTagNat spec)
            (ofTagNat_toTag spec) (toTag_lt spec) bs (toCompact e)).mpr
          rw [hBase]
          exact congrArg some (Subtype.ext (hToTagPreserve e).symm)
        rw [hMust] at hDec
        nomatch hDec
    | some v =>
      dsimp only [Option.map]
      have hBase := (FixedByteCodec.enumRepr_decode_eq_some_iff
        spec.tagByteWidth spec.tagByteWidth_pos toTag (ofTagNat spec)
        (ofTagNat_toTag spec) (toTag_lt spec) bs v).mp hDec
      symm
      apply (FixedByteCodec.enumRepr_decode_eq_some_iff
        spec.tagByteWidth spec.tagByteWidth_pos toTagΕ ofTagΕ hRoundΕ hBoundsΕ bs (ofCompact v)).mpr
      rw [hBase]
      apply congrArg some
      apply Subtype.ext
      have hTagEq := hToTagPreserve (ofCompact v)
      rw [hRightInv v] at hTagEq
      exact hTagEq

/--
Bridge from `CompactEnumVal spec` directly to `Anneal.ByteCodec.MirValueCodec.fieldlessEnum`
for any multi-variant fieldless enum in `LayoutTable`.
-/
def mirValueCodec (spec : CompactEnumSpec)
    (layouts : LayoutTable) (defPath : DefPath) (args : List RigidTy) (idx : LayoutIdx)
    (l : TypeLayout) (bitsWidth : Nat) (signed : Bool) (validRange : WrappingRange)
    (variantShapes : List FieldsShape) (memoryOrder : List Nat)
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hInhab : l.isUninhabited = false)
    (hSize : l.size.bytes = spec.tagByteWidth)
    (hVar : l.variants = .multiple (.initialized (.int bitsWidth signed) validRange) 0 variantShapes)
    (hFields : l.fields = .arbitrary [{ bytes := 0 }] memoryOrder)
    (hWidth : primitiveKindByteWidth (.int bitsWidth signed) = some spec.tagByteWidth)
    (hAllFieldless :
      ∀ (varIdx : Nat) (varOffsets : List Size) (varMemOrder : List Nat),
        Trusted.Sequence.get? variantShapes varIdx = some (.arbitrary varOffsets varMemOrder) →
        varOffsets = [])
    (hTagValid :
      ∀ v : CompactEnumVal spec,
        wrappingRangeContains validRange v.toTag = true ∧
        ∃ vm, Trusted.Sequence.get? variantShapes v.toTag = some (.arbitrary [] vm))
    (hTagComplete :
      ∀ (t : Nat) (varShape : FieldsShape),
        t < 2 ^ (8 * spec.tagByteWidth) →
        wrappingRangeContains validRange t = true →
        Trusted.Sequence.get? variantShapes t = some varShape →
        ∃ v : CompactEnumVal spec, v.toTag = t) :
    MirValueCodec layouts { kind := .adt defPath args, layoutIdx := idx }
      (CompactEnumVal spec) spec.tagByteWidth :=
  MirValueCodec.fieldlessEnum
    layouts defPath args idx l spec.tagByteWidth bitsWidth signed validRange
    variantShapes memoryOrder toTag (ofTagNat spec)
    (ofTagNat_toTag spec) (toTag_lt spec) spec.tagByteWidth_pos
    hLookup hInhab hSize hVar hFields hWidth hAllFieldless hTagValid hTagComplete

end CompactEnumVal

/-- Concrete sparse `#[repr(u16)]` enum with discriminants `#[0, 10, 1000, 65535]`. -/
def sparseU16EnumSpec : CompactEnumSpec where
  tagByteWidth := 2
  hTagWidth := Or.inr (Or.inl rfl)
  validDiscrs := #[0, 10, 1000, 65535]
  hSorted := rfl
  hBounded := rfl

#guard sparseU16EnumSpec.isValidDiscr 0 == true
#guard sparseU16EnumSpec.isValidDiscr 1000 == true
#guard sparseU16EnumSpec.isValidDiscr 65535 == true
#guard sparseU16EnumSpec.isValidDiscr 1 == false
#guard (CompactEnumVal.byteCodec sparseU16EnumSpec).decode [.init 232 none, .init 3 none] == some ⟨1000, rfl⟩
#guard (CompactEnumVal.byteCodec sparseU16EnumSpec).decode [.init 1 none, .init 0 none] == none
#guard (CompactEnumVal.byteCodec sparseU16EnumSpec).decode [.init 0 none, .uninit] == none

/--
**Byte-Level Decode Characterization (`CompactEnumVal.byteCodec_decode_eq_some_iff`)**:
decoding raw bytes `bs` via `CompactEnumVal.byteCodec spec` succeeds with `some v` if and only if
`bs` is a valid little-endian unsigned `spec.tagByteWidth`-byte encoding of `v.toTag`.

Kind: codec
Witness: universal
Assumes: S0
Subject: CompactEnumVal.byteCodec
-/
theorem CompactEnumVal.byteCodec_decode_eq_some_iff (spec : CompactEnumSpec)
    (bs : List AbstractByte) (v : CompactEnumVal spec) :
    (CompactEnumVal.byteCodec spec).decode bs = some v ↔
      (FixedByteCodec.uintBitsLE spec.tagByteWidth spec.tagByteWidth_pos).decode bs =
        some ⟨v.toTag, CompactEnumVal.toTag_lt spec v⟩ :=
  FixedByteCodec.enumRepr_decode_eq_some_iff
    spec.tagByteWidth spec.tagByteWidth_pos CompactEnumVal.toTag
    (CompactEnumVal.ofTagNat spec) (CompactEnumVal.ofTagNat_toTag spec)
    (CompactEnumVal.toTag_lt spec) bs v

/--
`sparseU16EnumSpec` satisfies `HasZeroValid` (`FromZeros` holds because `0 ∈ validDiscrs`)
while failing `IsSurjectiveInitDecoder` (`FromBytes` fails because discriminant `1` is a niche).

Kind: codec
Witness: universal
Assumes: S0
Subject: sparseU16EnumSpec
-/
theorem sparseU16EnumSpec_zeroValid_and_not_fromBytes :
    (CompactEnumVal.byteCodec sparseU16EnumSpec).HasZeroValid ∧
    ¬ (CompactEnumVal.byteCodec sparseU16EnumSpec).IsSurjectiveInitDecoder :=
  ⟨(CompactEnumVal.byteCodec_hasZeroValid_iff sparseU16EnumSpec).mpr rfl,
   CompactEnumVal.byteCodec_not_isSurjectiveInitDecoder_of_missing sparseU16EnumSpec
     (d := 1) (by decide) rfl⟩

/-- Concrete non-zero `#[repr(u32)]` enum with discriminants `#[1, 2, 4, 8]`. -/
def nonZeroU32EnumSpec : CompactEnumSpec where
  tagByteWidth := 4
  hTagWidth := Or.inr (Or.inr rfl)
  validDiscrs := #[1, 2, 4, 8]
  hSorted := rfl
  hBounded := rfl

/--
`nonZeroU32EnumSpec` rejects zero-initialized bytes (`¬ HasZeroValid`) because `0 ∉ validDiscrs`.

Kind: codec
Witness: negative
Assumes: S0
Subject: nonZeroU32EnumSpec
-/
theorem nonZeroU32EnumSpec_not_hasZeroValid :
    ¬ (CompactEnumVal.byteCodec nonZeroU32EnumSpec).HasZeroValid := by
  rw [CompactEnumVal.byteCodec_hasZeroValid_iff]
  decide

/--
**Unsorted / Duplicate / Out-of-Range Discriminant Rejection**: no `CompactEnumSpec` can carry a
duplicated (`#[7, 7]`) or unsorted (`#[2, 1]`) discriminant table, nor an out-of-range `u8`
discriminant (`256`): the kernel-checked `hSorted` / `hBounded` fields reject them at construction.

Kind: safety
Witness: negative
Assumes: S0
Subject: CompactEnumSpec
-/
theorem compactEnumSpec_rejects_duplicate_unsorted_and_out_of_range :
    (¬ ∃ spec : CompactEnumSpec, spec.validDiscrs = #[7, 7]) ∧
    (¬ ∃ spec : CompactEnumSpec, spec.validDiscrs = #[2, 1]) ∧
    (¬ ∃ spec : CompactEnumSpec, spec.tagByteWidth = 1 ∧ spec.validDiscrs = #[0, 256]) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨spec, hEq⟩
    have h := spec.hSorted
    rw [hEq] at h
    exact absurd h (by decide)
  · rintro ⟨spec, hEq⟩
    have h := spec.hSorted
    rw [hEq] at h
    exact absurd h (by decide)
  · rintro ⟨spec, hW, hEq⟩
    have h := spec.hBounded
    rw [hEq, hW] at h
    exact absurd h (by decide)

#guard isStrictlySortedArray #[7, 7] == false
#guard isStrictlySortedArray #[2, 1] == false
#guard nonZeroU32EnumSpec.isValidDiscr 8 == true
#guard nonZeroU32EnumSpec.isValidDiscr 3 == false
#guard nonZeroU32EnumSpec.isValidDiscr 9 == false

/--
Constructive bounds for `List.range' s len`: every element `x ∈ List.range' s len`
satisfies `s ≤ x ∧ x < s + len`.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem mem_range'_bounds :
    ∀ {s len x : Nat}, x ∈ List.range' s len → s ≤ x ∧ x < s + len
  | _, 0, _, h => nomatch h
  | s, k + 1, x, h => by
    rcases List.mem_cons.mp h with rfl | hTail
    · exact ⟨Nat.le_refl _, by omega⟩
    · rcases mem_range'_bounds hTail with ⟨hGe, hLt⟩
      exact ⟨by omega, by omega⟩

/--
Constructive helper: `List.range' s len` mapped by `UInt32.ofNat` is strictly sorted
(`List.Pairwise (· < ·)`) whenever `s + len ≤ UInt32.size`, proved by structural induction
on `len` without `Classical.choice`.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem map_uint32_ofNat_range'_pairwise :
    ∀ (s len : Nat), s + len ≤ UInt32.size →
      List.Pairwise (· < ·) ((List.range' s len).map UInt32.ofNat)
  | _, 0, _ => List.Pairwise.nil
  | s, k + 1, hLe => by
    dsimp only [List.range', List.map]
    refine List.Pairwise.cons ?_ (map_uint32_ofNat_range'_pairwise (s + 1) k (by omega))
    intro d hd
    rcases List.mem_map.mp hd with ⟨x, hx, rfl⟩
    rcases mem_range'_bounds hx with ⟨hGe, hLt⟩
    have hsLt : s < UInt32.size := by omega
    have hxLt : x < UInt32.size := by omega
    change (UInt32.ofNat s).toNat < (UInt32.ofNat x).toNat
    change s % UInt32.size < x % UInt32.size
    rw [Nat.mod_eq_of_lt hsLt, Nat.mod_eq_of_lt hxLt]
    omega

/--
General constructor for a contiguous `0 .. n - 1` `CompactEnumSpec`, proving
`List.Pairwise (· < ·)` constructively without `Classical.choice` or `rfl` unrolling.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem map_uint32_ofNat_range_pairwise (n : Nat) (hLe : n ≤ UInt32.size) :
    List.Pairwise (· < ·) ((List.range n).map UInt32.ofNat) := by
  rw [List.range_eq_range']
  exact map_uint32_ofNat_range'_pairwise 0 n (by omega)

/--
Kind: helper
Witness: universal
Assumes: S0
-/
theorem map_uint32_ofNat_range_bounded (n bound : Nat) (hBound : n ≤ bound)
    (hLe : n ≤ UInt32.size) :
    (((List.range n).map UInt32.ofNat).all (fun d => Nat.blt d.toNat bound)) = true := by
  rw [List.all_eq_true]
  intro d hd
  rcases List.mem_map.mp hd with ⟨k, hk, rfl⟩
  have hkLt : k < n := List.mem_range.mp hk
  have hkU32 : k < UInt32.size := Nat.lt_of_lt_of_le hkLt hLe
  rw [Nat.blt_eq]
  change k % UInt32.size < bound
  rw [Nat.mod_eq_of_lt hkU32]
  omega

/--
Exhaustive 256-variant `#[repr(u8)]` `CompactEnumSpec` (`0 .. 255`):
demonstrates `salikh` `cl/1018197791` compact enum scaling with a single structure constructor
instead of a 256-constructor `inductive` type, proved structurally in $O(1)$ kernel time.
-/
def u8ExhaustiveCompactSpec : CompactEnumSpec where
  tagByteWidth := 1
  hTagWidth := Or.inl rfl
  validDiscrs := ((List.range 256).map UInt32.ofNat).toArray
  hSorted := by
    unfold isStrictlySortedArray
    rw [isStrictlySortedList_iff_pairwise]
    exact map_uint32_ofNat_range_pairwise 256 (by decide)
  hBounded :=
    map_uint32_ofNat_range_bounded 256 (2 ^ (8 * 1)) (by decide) (by decide)

/--
The exhaustive 256-variant `#[repr(u8)]` `CompactEnumVal` codec satisfies `IsExactWidth`,
`IsInitCodec` (`IntoBytes`), `IsSurjectiveInitDecoder` (`FromBytes`), and `HasZeroValid`
(`FromZeros`) with zero 256-constructor eliminator overhead.

Kind: codec
Witness: universal
Assumes: S0
Subject: u8ExhaustiveCompactSpec
-/
theorem u8ExhaustiveCompactSpec_full_zerocopy_traits :
    (CompactEnumVal.byteCodec u8ExhaustiveCompactSpec).IsExactWidth ∧
    (CompactEnumVal.byteCodec u8ExhaustiveCompactSpec).IsInitCodec ∧
    (CompactEnumVal.byteCodec u8ExhaustiveCompactSpec).IsSurjectiveInitDecoder ∧
    (CompactEnumVal.byteCodec u8ExhaustiveCompactSpec).HasZeroValid := by
  have hSurj : (CompactEnumVal.byteCodec u8ExhaustiveCompactSpec).IsSurjectiveInitDecoder := by
    apply CompactEnumVal.byteCodec_isSurjectiveInitDecoder_of_all_valid
    intro bits hLt
    rw [CompactEnumSpec.isValidDiscr_eq_true_iff]
    dsimp only [u8ExhaustiveCompactSpec]
    exact List.mem_map.mpr ⟨bits, List.mem_range.mpr hLt, rfl⟩
  exact ⟨CompactEnumVal.byteCodec_isExactWidth u8ExhaustiveCompactSpec,
         CompactEnumVal.byteCodec_isInitCodec u8ExhaustiveCompactSpec,
         hSurj,
         hSurj.hasZeroValid⟩

#guard u8ExhaustiveCompactSpec.isValidDiscr 0 == true
#guard u8ExhaustiveCompactSpec.isValidDiscr 255 == true
#guard u8ExhaustiveCompactSpec.isValidDiscr 256 == false

/--
Every `u8` bit pattern is a valid discriminant of the exhaustive 256-variant spec.

Kind: helper
Witness: universal
Assumes: S0
-/
theorem u8ExhaustiveCompactSpec_isValidDiscr_ofNat {bits : Nat} (hLt : bits < 2 ^ (8 * 1)) :
    u8ExhaustiveCompactSpec.isValidDiscr (UInt32.ofNat bits) = true := by
  rw [CompactEnumSpec.isValidDiscr_eq_true_iff]
  dsimp only [u8ExhaustiveCompactSpec]
  exact List.mem_map.mpr ⟨bits, List.mem_range.mpr hLt, rfl⟩

/-- 256 fieldless variant shapes for the exhaustive `#[repr(u8)]` enum. -/
def u8ExhaustiveVariantShapes : List FieldsShape := List.replicate 256 (.arbitrary [] [])

/-- Concrete `TypeLayout` of a 256-variant fieldless `#[repr(u8)]` enum: direct `u8` tag at
offset `0`, valid range `0 ..= 255`, size and alignment `1`. -/
def u8ExhaustiveEnumLayout : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩),
    fields := .arbitrary [⟨0⟩] [0],
    variants := .multiple (.initialized (.int 8 false) ⟨0, 255⟩) 0 u8ExhaustiveVariantShapes,
    isUninhabited := false }

/-- Concrete single-entry `LayoutTable` holding `u8ExhaustiveEnumLayout` at index `0`. -/
def u8ExhaustiveLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [u8ExhaustiveEnumLayout] }

/--
**Concrete `MirValueCodec.fieldlessEnum` Instance**: the compact single-constructor
`CompactEnumVal u8ExhaustiveCompactSpec` is the `MirValueCodec` of a real 256-variant fieldless
`.adt` in a concrete `LayoutTable`, discharging every `fieldlessEnum` side condition
(`hTagValid`, `hTagComplete`, `hAllFieldless`) — so `CompactEnumVal.mirValueCodec` is provably
non-vacuous.
-/
def u8ExhaustiveMirValueCodec (defPath : DefPath) :
    MirValueCodec u8ExhaustiveLayouts { kind := .adt defPath [], layoutIdx := 0 }
      (CompactEnumVal u8ExhaustiveCompactSpec) u8ExhaustiveCompactSpec.tagByteWidth :=
  CompactEnumVal.mirValueCodec u8ExhaustiveCompactSpec u8ExhaustiveLayouts defPath [] 0
    u8ExhaustiveEnumLayout 8 false ⟨0, 255⟩ u8ExhaustiveVariantShapes [0]
    rfl rfl rfl rfl rfl rfl
    (fun varIdx varOffsets varMemOrder h => by
      simp only [Trusted.Sequence.get?, u8ExhaustiveVariantShapes, List.getElem?_replicate] at h
      split at h
      · simp only [Option.some.injEq, FieldsShape.arbitrary.injEq] at h
        exact h.1.symm
      · nomatch h)
    (fun v => by
      have hLt : v.toTag < 256 := CompactEnumVal.toTag_lt u8ExhaustiveCompactSpec v
      refine ⟨?_, [], ?_⟩
      · simp only [wrappingRangeContains, Nat.ble_eq, Bool.true_and, Nat.ble]
        omega
      · simp only [Trusted.Sequence.get?, u8ExhaustiveVariantShapes, List.getElem?_replicate,
          hLt, ↓reduceIte])
    (fun t _ hLt _ _ =>
      ⟨⟨UInt32.ofNat t, u8ExhaustiveCompactSpec_isValidDiscr_ofNat hLt⟩,
        CompactEnumVal.uint32_ofNat_toNat_of_lt u8ExhaustiveCompactSpec hLt⟩)

/--
**Exhaustive 256-Variant `#[repr(u8)]` `BitValidity` Theorem**: the concrete `.adt` type backed by
`u8ExhaustiveMirValueCodec` satisfies `IsFromBytes`, `IsIntoBytes`, `IsFromZeros`, and
`IsTryFromBytes` in `Anneal.BitValidity`, with zero 256-constructor inductive overhead.

Kind: codec
Witness: universal
Assumes: S0
Subject: u8ExhaustiveMirValueCodec
-/
theorem u8ExhaustiveMirValueCodec_full_bitValidity (defPath : DefPath) :
    let _m := u8ExhaustiveMirValueCodec defPath
    IsFromBytes u8ExhaustiveLayouts { kind := .adt defPath [], layoutIdx := 0 } ∧
    IsIntoBytes u8ExhaustiveLayouts { kind := .adt defPath [], layoutIdx := 0 } ∧
    IsFromZeros u8ExhaustiveLayouts { kind := .adt defPath [], layoutIdx := 0 } ∧
    IsTryFromBytes u8ExhaustiveLayouts { kind := .adt defPath [], layoutIdx := 0 } := by
  intro m
  obtain ⟨_, hInit, hSurj, _⟩ := u8ExhaustiveCompactSpec_full_zerocopy_traits
  have hFb := m.isFromBytes hSurj
  exact ⟨hFb, m.isIntoBytes hInit rfl, isFromBytes_implies_isFromZeros _ _ hFb,
    isFromBytes_implies_isTryFromBytes _ _ hFb⟩

end Anneal.ByteCodec
