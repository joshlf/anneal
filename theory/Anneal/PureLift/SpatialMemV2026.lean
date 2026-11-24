-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted.Sequence
import Trusted.Rustc.V2026_06_01.Layout
import Trusted.Rustc.V2026_06_01.MirAst.Types
import Trusted.Rustc.V2026_06_01.MirAst.Body
import Trusted.Rustc.V2026_06_01.MirSemantics.State
import Trusted.Rustc.V2026_06_01.MirSemantics.Bytes
import Trusted.Rustc.V2026_06_01.MirSemantics.Places
import Anneal.PureLift.Lens
import Anneal.PureLift.PermTree
import Anneal.PureLift.LoanGraph
import Anneal.PureLift.SpatialPin
import Anneal.PureLift.V2026_06_01Bridge

namespace Anneal.PureLift.SpatialMemV2026

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.PureLift
open Anneal.PureLift.V2026_06_01Bridge

/-!
# Spatial Memory Pinning on Unmodified `Trusted.Rustc.V2026_06_01.MirSemantics`

Bridges `Anneal.PureLift.SpatialPin` directly to unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics` (`Memory`, `CapturedAllocation`,
`AbstractByte`, `LocalSlot`, `Value`, `encodeValueToBytes`,
`decodeValueFromBytes`, `globalAllocSliceToAbstractBytes`, `lookupGlobalAlloc`),
with zero shadow operational semantics:

1. **`MirMemMirror`**: Total computable mirrors and unconditional equational
   agreement lemmas against `V2026_06_01.MirSemantics` byte codecs and global
   allocation reads, plus a byte-granularity `V2026ByteMem` allocation store
   bridged to `CapturedAllocation` via `globalAllocSliceToAbstractBytes`.
2. **`ValByteCodec`**: `u32TaggedByteCodec : SpatialCodec Value` and
   `u32TaggedStdByteCodec : SpatialCodec StdVal` with constructive `LawfulCodec`
   round-trip proofs, byte agreement with `encodeValueToBytes`, and framed
   `SpatialTriple` / `spatial_frame_law` round-trip.
3. **`PaddedPin` & `Soundness`**: `AuditedFieldSpec`, `SpatialTargetSpec`,
   `BodySpatialCtx` authenticating local types & `LayoutTable` against a real
   `CapturedMir`, `TypedSpatialMemCodec`, bidirectional `(allocId, tag)`
   provenance enforcement (`valAndBytesMatchTargetSpec`), and `PaddedSymMemState`
   (`freezePaddedToMem`, `mutatePaddedInMem`, `reabsorbPaddedFromMem`,
   `writePaddedSymPlace`, `endPaddedLoan`, `deallocatePromotedLocal`) solving
   the padded `(u8, [pad; 3], u32)` gap documented by
   `Anneal.PureLift.u8U32Padded_freeze_refused`.
4. **Concrete Lawful Codecs & Negative Guards**: `u32MemCodec`,
   `paddedU8U32MemCodec`, and `provPtrPaddedMemCodec`, with end-to-end
   soundness, cross-allocation framing, and fail-closed rejection of
   non-padding `.uninit`, provenance stripping, surplus provenance forgery,
   unauthenticated `BodySpatialCtx` / `.ref` targets, aliased `AllocId`s, and
   pure mutation while pinned.
-/

/-! ## 1. Computable `V2026_06_01` Byte & Allocation Mirrors (`MirMemMirror`) -/

private theorem natBle_of_le {a b : Nat} (h : a ≤ b) : Nat.ble a b = true :=
  Nat.ble_eq.mpr h

private theorem natLe_of_ble {a b : Nat} (h : Nat.ble a b = true) : a ≤ b :=
  Nat.ble_eq.mp h

private theorem natBlt_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true :=
  Nat.blt_eq.mpr h

private theorem natLt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  Nat.blt_eq.mp h

private theorem uint8_eq_of_toNat {a b : UInt8}
    (h : a.toBitVec.toNat = b.toBitVec.toNat) : a = b := by
  cases a; cases b
  congr 1
  exact BitVec.eq_of_toNat_eq h

private theorem takeAbstractBytes_eq_take' : ∀ (n : Nat) (bs : List AbstractByte),
    takeAbstractBytes n bs = bs.take n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, b :: bs => congrArg (List.cons b) (takeAbstractBytes_eq_take' k bs)

private theorem dropAbstractBytes_eq_drop' : ∀ (n : Nat) (bs : List AbstractByte),
    dropAbstractBytes n bs = bs.drop n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, _ :: bs => dropAbstractBytes_eq_drop' k bs

/-- Total computable little-endian encoder mirroring
`Trusted.Rustc.V2026_06_01.MirSemantics.encodeLittleEndianBytes`. -/
def execEncodeLittleEndianBytes (bits : Nat) :
    Nat → Option (Nat × Nat) → List AbstractByte
  | 0, _ => []
  | rem + 1, prov =>
    .init (UInt8.ofNat bits) prov ::
      execEncodeLittleEndianBytes (bits / 256) rem prov

theorem execEncodeLittleEndianBytes_eq (bits numBytes : Nat)
    (prov : Option (Nat × Nat)) :
    execEncodeLittleEndianBytes bits numBytes prov =
      encodeLittleEndianBytes bits numBytes prov := by
  induction numBytes generalizing bits with
  | zero => rfl
  | succ rem ih =>
    simp only [execEncodeLittleEndianBytes, encodeLittleEndianBytes]
    exact congrArg (List.cons (.init (UInt8.ofNat bits) prov)) (ih (bits / 256))

theorem encodeLittleEndianBytes_length (bits numBytes : Nat)
    (prov : Option (Nat × Nat)) :
    (encodeLittleEndianBytes bits numBytes prov).length = numBytes := by
  induction numBytes generalizing bits with
  | zero => rfl
  | succ rem ih =>
    simp only [encodeLittleEndianBytes, List.length_cons, ih]

/-- Total computable little-endian decoder mirroring
`Trusted.Rustc.V2026_06_01.MirSemantics.decodeLittleEndianBytes`. -/
def execDecodeLittleEndianBytes :
    List AbstractByte → Option (Nat × Option (Nat × Nat))
  | [] => some (0, none)
  | .uninit :: _ => none
  | .init b prov :: rest =>
    match execDecodeLittleEndianBytes rest with
    | some (highBits, restProv) =>
      some (b.toBitVec.toNat + 256 * highBits, mergeByteProvenance prov restProv)
    | none => none

theorem execDecodeLittleEndianBytes_eq (bs : List AbstractByte) :
    execDecodeLittleEndianBytes bs = decodeLittleEndianBytes bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | uninit => rfl
    | init byte prov =>
      unfold execDecodeLittleEndianBytes decodeLittleEndianBytes
      rw [ih]
      rfl

private theorem mergeByteProvenance_same (p : Option (Nat × Nat)) :
    mergeByteProvenance p p = p := by
  cases p <;> rfl

private theorem mergeByteProvenance_none_right (p : Option (Nat × Nat)) :
    mergeByteProvenance p none = p := by
  cases p <;> rfl

private theorem uint8_ofNat_toBitVec_toNat (n : Nat) :
    (UInt8.ofNat n).toBitVec.toNat = n % 256 := by
  change (BitVec.ofNat 8 n).toNat = n % 256
  simp [BitVec.toNat_ofNat]

/-- Exact little-endian round-trip: decoding `encodeLittleEndianBytes bits n prov`
recovers `(bits % 256^n, if n == 0 then none else prov)`. -/
theorem decodeLittleEndianBytes_encodeLittleEndianBytes
    (bits numBytes : Nat) (prov : Option (Nat × Nat)) :
    decodeLittleEndianBytes (encodeLittleEndianBytes bits numBytes prov) =
      some (bits % 256 ^ numBytes, if numBytes == 0 then none else prov) := by
  induction numBytes generalizing bits with
  | zero =>
    simp only [decodeLittleEndianBytes, Nat.pow_zero,
      Nat.mod_one, beq_self_eq_true, ↓reduceIte]
  | succ rem ih =>
    unfold encodeLittleEndianBytes decodeLittleEndianBytes
    change (match decodeLittleEndianBytes (encodeLittleEndianBytes (bits / 256) rem prov) with
      | some (highBits, restProv) =>
        some ((UInt8.ofNat bits).toBitVec.toNat + 256 * highBits, mergeByteProvenance prov restProv)
      | none => none) = _
    rw [ih (bits / 256), uint8_ofNat_toBitVec_toNat]
    have hMod : bits % 256 + 256 * (bits / 256 % 256 ^ rem) = bits % 256 ^ (rem + 1) := by
      have hPow : 256 ^ (rem + 1) = 256 * 256 ^ rem := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hPow, Nat.mod_mul]
    have hProv : mergeByteProvenance prov (if rem == 0 then none else prov) = prov := by
      cases rem with
      | zero => exact mergeByteProvenance_none_right prov
      | succ _ => exact mergeByteProvenance_same prov
    have hSucc : (rem + 1 == 0) = false := rfl
    simp only [hMod, hProv, hSucc, Bool.false_eq_true, ↓reduceIte]

/-- Bounded round-trip specialization when `bits < 256 ^ numBytes` and
`numBytes > 0`. -/
theorem decodeLittleEndianBytes_encodeLittleEndianBytes_of_lt
    (bits numBytes : Nat) (prov : Option (Nat × Nat))
    (hPos : 0 < numBytes) (hLt : bits < 256 ^ numBytes) :
    decodeLittleEndianBytes (encodeLittleEndianBytes bits numBytes prov) =
      some (bits, prov) := by
  rw [decodeLittleEndianBytes_encodeLittleEndianBytes, Nat.mod_eq_of_lt hLt]
  cases numBytes with
  | zero => exact absurd hPos (Nat.lt_irrefl 0)
  | succ _ => rfl

/-- Total computable mirror of `encodeScalarBytes`. -/
def execEncodeScalarBytes (sv : ScalarVal) (prov : Option (Nat × Nat) := none) :
    Option (List AbstractByte) :=
  match Nat.beq sv.sizeBytes 0 with
  | true => none
  | false => some (execEncodeLittleEndianBytes sv.bits sv.sizeBytes prov)

theorem execEncodeScalarBytes_eq (sv : ScalarVal) (prov : Option (Nat × Nat)) :
    execEncodeScalarBytes sv prov = encodeScalarBytes sv prov := by
  unfold execEncodeScalarBytes encodeScalarBytes
  rw [execEncodeLittleEndianBytes_eq]
  rfl

/-- Total computable mirror of `decodeScalarBytes`. -/
def execDecodeScalarBytes (bs : List AbstractByte) (_signed : Bool := false) :
    Option (ScalarVal × Option (Nat × Nat)) :=
  let sz := bs.length
  match Nat.beq sz 0 with
  | true => none
  | false =>
    match execDecodeLittleEndianBytes bs with
    | some (bits, prov) => some (⟨bits, sz⟩, prov)
    | none => none

theorem execDecodeScalarBytes_eq (bs : List AbstractByte) (signed : Bool) :
    execDecodeScalarBytes bs signed = decodeScalarBytes bs signed := by
  unfold execDecodeScalarBytes decodeScalarBytes
  dsimp only
  have hLen : Trusted.Sequence.length bs = bs.length := rfl
  rw [hLen, execDecodeLittleEndianBytes_eq]
  rfl

/-- Round-trip theorem for `encodeScalarBytes` followed by `decodeScalarBytes`. -/
theorem decodeScalarBytes_encodeScalarBytes (sv : ScalarVal)
    (prov : Option (Nat × Nat)) (signed : Bool)
    (hPos : 0 < sv.sizeBytes) (hLt : sv.bits < 256 ^ sv.sizeBytes) :
    ∃ bs, encodeScalarBytes sv prov = some bs ∧
      bs.length = sv.sizeBytes ∧
      decodeScalarBytes bs signed = some (sv, prov) := by
  have hNe0 : Nat.beq sv.sizeBytes 0 = false := by
    cases hSz : sv.sizeBytes with
    | zero => rw [hSz] at hPos; exact absurd hPos (Nat.lt_irrefl 0)
    | succ _ => rfl
  refine ⟨encodeLittleEndianBytes sv.bits sv.sizeBytes prov, ?_, ?_, ?_⟩
  · unfold encodeScalarBytes
    rw [hNe0]
  · exact encodeLittleEndianBytes_length sv.bits sv.sizeBytes prov
  · unfold decodeScalarBytes
    dsimp only
    have hLen : Trusted.Sequence.length (encodeLittleEndianBytes sv.bits sv.sizeBytes prov) =
        sv.sizeBytes := encodeLittleEndianBytes_length sv.bits sv.sizeBytes prov
    rw [hLen, hNe0, decodeLittleEndianBytes_encodeLittleEndianBytes_of_lt sv.bits sv.sizeBytes prov hPos hLt]

/-- Total computable mirror of `encodeValueToBytes`. -/
def execEncodeValueToBytes (fuel : Nat) (layouts : LayoutTable) (ty : Ty)
    (v : Value) : Option (List AbstractByte) :=
  encodeValueToBytes fuel layouts ty v

theorem execEncodeValueToBytes_eq (fuel : Nat) (layouts : LayoutTable) (ty : Ty)
    (v : Value) :
    execEncodeValueToBytes fuel layouts ty v =
      encodeValueToBytes fuel layouts ty v := rfl

/-- Total computable mirror of `decodeValueFromBytes`. -/
def execDecodeValueFromBytes (fuel : Nat) (layouts : LayoutTable) (ty : Ty)
    (bs : List AbstractByte) : Option Value :=
  decodeValueFromBytes fuel layouts ty bs

theorem execDecodeValueFromBytes_eq (fuel : Nat) (layouts : LayoutTable) (ty : Ty)
    (bs : List AbstractByte) :
    execDecodeValueFromBytes fuel layouts ty bs =
      decodeValueFromBytes fuel layouts ty bs := rfl

/-- Total computable mirror of `lookupGlobalAlloc`. -/
def execLookupGlobalAlloc : List CapturedAllocation → AllocId → Option CapturedAllocation
  | [], _ => none
  | a :: rest, aid =>
    if Nat.beq a.allocId aid then some a else execLookupGlobalAlloc rest aid

theorem execLookupGlobalAlloc_eq (globals : List CapturedAllocation) (aid : AllocId) :
    execLookupGlobalAlloc globals aid = lookupGlobalAlloc globals aid := by
  induction globals with
  | nil => rfl
  | cons a rest ih =>
    unfold execLookupGlobalAlloc lookupGlobalAlloc
    cases Nat.beq a.allocId aid with
    | true => rfl
    | false => exact ih

/-- Total computable mirror of `globalAllocSliceToAbstractBytes`. -/
def execGlobalAllocSliceToAbstractBytes (alloc : CapturedAllocation)
    (offset len : Nat) : Option (List AbstractByte) :=
  if Nat.ble offset alloc.bytes.length then
    globalAllocBytesAux alloc.bytes alloc.relocations offset len
  else
    none

theorem execGlobalAllocSliceToAbstractBytes_eq (alloc : CapturedAllocation)
    (offset len : Nat) :
    execGlobalAllocSliceToAbstractBytes alloc offset len =
      globalAllocSliceToAbstractBytes alloc offset len := by
  unfold execGlobalAllocSliceToAbstractBytes globalAllocSliceToAbstractBytes
  have hLen : Trusted.Sequence.length alloc.bytes = alloc.bytes.length := rfl
  rw [hLen]
  cases Nat.ble offset alloc.bytes.length <;> rfl

/-- Equality test on `Option (Nat × Nat)` provenance pairs. -/
def optProvBeq : Option (Nat × Nat) → Option (Nat × Nat) → Bool
  | none, none => true
  | some (a1, t1), some (a2, t2) => Nat.beq a1 a2 && Nat.beq t1 t2
  | _, _ => false

theorem optProvBeq_refl (p : Option (Nat × Nat)) : optProvBeq p p = true := by
  cases p with
  | none => rfl
  | some pair =>
    cases pair with
    | mk a t =>
      simp only [optProvBeq, Nat.beq_refl, Bool.and_self]

theorem optProvBeq_eq_true_iff (p1 p2 : Option (Nat × Nat)) :
    optProvBeq p1 p2 = true ↔ p1 = p2 := by
  cases p1 with
  | none =>
    cases p2 with
    | none => simp [optProvBeq]
    | some _ => simp [optProvBeq]
  | some pair1 =>
    cases pair1 with
    | mk a1 t1 =>
      cases p2 with
      | none => simp [optProvBeq]
      | some pair2 =>
        cases pair2 with
        | mk a2 t2 =>
          simp only [optProvBeq, Bool.and_eq_true, Option.some.injEq, Prod.mk.injEq]
          constructor
          · rintro ⟨hA, hT⟩
            exact ⟨Nat.eq_of_beq_eq_true hA, Nat.eq_of_beq_eq_true hT⟩
          · rintro ⟨rfl, rfl⟩
            exact ⟨Nat.beq_refl _, Nat.beq_refl _⟩

/-- Decidable equality test on `AbstractByte`. -/
def abstractByteBeq : AbstractByte → AbstractByte → Bool
  | .uninit, .uninit => true
  | .init b1 p1, .init b2 p2 => Nat.beq b1.toNat b2.toNat && optProvBeq p1 p2
  | _, _ => false

theorem abstractByteBeq_refl (b : AbstractByte) : abstractByteBeq b b = true := by
  cases b with
  | uninit => rfl
  | init byte prov =>
    simp only [abstractByteBeq, Nat.beq_refl, optProvBeq_refl, Bool.and_self]

theorem abstractByteBeq_eq_true_iff (b1 b2 : AbstractByte) :
    abstractByteBeq b1 b2 = true ↔ b1 = b2 := by
  cases b1 with
  | uninit =>
    cases b2 with
    | uninit => simp [abstractByteBeq]
    | init _ _ => simp [abstractByteBeq]
  | init x1 p1 =>
    cases b2 with
    | uninit => simp [abstractByteBeq]
    | init x2 p2 =>
      simp only [abstractByteBeq, Bool.and_eq_true, optProvBeq_eq_true_iff,
        AbstractByte.init.injEq]
      constructor
      · rintro ⟨hB, hP⟩
        refine ⟨?_, hP⟩
        exact uint8_eq_of_toNat (Nat.eq_of_beq_eq_true hB)
      · rintro ⟨rfl, rfl⟩
        exact ⟨Nat.beq_refl _, rfl⟩

/-- Decidable equality on `List AbstractByte`. -/
def abstractByteListBeq : List AbstractByte → List AbstractByte → Bool
  | [], [] => true
  | x :: xs, y :: ys => abstractByteBeq x y && abstractByteListBeq xs ys
  | _, _ => false

theorem abstractByteListBeq_refl (bs : List AbstractByte) :
    abstractByteListBeq bs bs = true := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    simp only [abstractByteListBeq, abstractByteBeq_refl, ih, Bool.and_self]

theorem abstractByteListBeq_eq_true_iff (xs ys : List AbstractByte) :
    abstractByteListBeq xs ys = true ↔ xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys <;> simp [abstractByteListBeq]
  | cons x xs ih =>
    cases ys with
    | nil => simp [abstractByteListBeq]
    | cons y ys =>
      simp only [abstractByteListBeq, Bool.and_eq_true, abstractByteBeq_eq_true_iff,
        ih, List.cons.injEq]

/-! ### Byte-Granularity `V2026_06_01` Allocation Memory (`V2026ByteMem`) -/

/-- Pointer place `(allocId, offset)` into a `V2026ByteMem` allocation. -/
structure V2026MemPlace where
  allocId : AllocId
  offset : Nat
  deriving DecidableEq

/-- Alignment & byte size layout descriptor for a promoted spatial allocation. -/
structure V2026MemLayout where
  size : Nat
  alignBytes : Nat
  deriving DecidableEq

/-- Single allocation backed directly by `Trusted.Rustc.V2026_06_01.MirSemantics.AbstractByte`. -/
structure V2026ByteAlloc where
  allocId : AllocId
  alignBytes : Nat
  mutability : Mutability
  bytes : List AbstractByte
  live : Bool

/-- Byte-granularity allocation store backed by `AbstractByte` and bridged to
`CapturedAllocation` / `Memory.globals`. -/
structure V2026ByteMem where
  nextAllocId : AllocId := 1
  allocs : List V2026ByteAlloc := []

/-- Look up an allocation by `allocId`. -/
def findV2026Alloc (aid : AllocId) : List V2026ByteAlloc → Option V2026ByteAlloc
  | [] => none
  | a :: rest =>
    if Nat.beq a.allocId aid then some a else findV2026Alloc aid rest

/-- Replace the first allocation matching `a'.allocId`. -/
def replaceV2026Alloc (a' : V2026ByteAlloc) : List V2026ByteAlloc → List V2026ByteAlloc
  | [] => []
  | a :: rest =>
    if Nat.beq a.allocId a'.allocId then a' :: rest else a :: replaceV2026Alloc a' rest

/-- Bounds check `offset + len ≤ alloc.bytes.length`. -/
def v2026InBounds (a : V2026ByteAlloc) (offset len : Nat) : Bool :=
  Nat.ble (offset + len) a.bytes.length

/-- Alignment check: `reqAlign > 0`, `reqAlign ≤ a.alignBytes`, and `offset % reqAlign == 0`. -/
def v2026Aligned (a : V2026ByteAlloc) (offset reqAlign : Nat) : Bool :=
  if reqAlign == 0 then false
  else Nat.ble reqAlign a.alignBytes && Nat.beq (offset % reqAlign) 0

/-- Allocate a fresh mutable uninitialized stack allocation in `mem`. -/
def allocV2026Stack (mem : V2026ByteMem) (size alignBytes : Nat) :
    V2026MemPlace × V2026ByteMem :=
  let aid := mem.nextAllocId
  let newAlloc : V2026ByteAlloc :=
    { allocId := aid
      alignBytes := alignBytes
      mutability := .mut
      bytes := List.replicate size .uninit
      live := true }
  (⟨aid, 0⟩, { nextAllocId := aid + 1, allocs := mem.allocs ++ [newAlloc] })

/-- Read `len` `AbstractByte`s from `mem` at `place` with required alignment `reqAlign`. -/
def readV2026Bytes (mem : V2026ByteMem) (place : V2026MemPlace)
    (len reqAlign : Nat) : Option (List AbstractByte) :=
  match findV2026Alloc place.allocId mem.allocs with
  | none => none
  | some a =>
    if !a.live || !v2026InBounds a place.offset len || !v2026Aligned a place.offset reqAlign then
      none
    else
      some ((a.bytes.drop place.offset).take len)

/-- Write `newBytes` into a live mutable allocation in `mem` at `place`. -/
def writeV2026Bytes (mem : V2026ByteMem) (place : V2026MemPlace)
    (reqAlign : Nat) (newBytes : List AbstractByte) : Option V2026ByteMem :=
  if newBytes.isEmpty then none
  else
    match findV2026Alloc place.allocId mem.allocs with
    | none => none
    | some a =>
      let isMut : Bool :=
        match a.mutability with
        | .mut => true
        | .not => false
      if !a.live || !isMut || !v2026InBounds a place.offset newBytes.length ||
         !v2026Aligned a place.offset reqAlign then
        none
      else
        let updatedBytes :=
          a.bytes.take place.offset ++ newBytes ++ a.bytes.drop (place.offset + newBytes.length)
        some { mem with allocs := replaceV2026Alloc { a with bytes := updatedBytes } mem.allocs }

/-- Overwrite `len` bytes with `.uninit` at `place`. -/
def writeV2026Uninit (mem : V2026ByteMem) (place : V2026MemPlace)
    (len reqAlign : Nat) : Option V2026ByteMem :=
  writeV2026Bytes mem place reqAlign (List.replicate len .uninit)

/-- Mark a promoted stack allocation dead (`live := false`) when accessed at offset `0`. -/
def deallocateV2026Stack (mem : V2026ByteMem) (place : V2026MemPlace) : Option V2026ByteMem :=
  if place.offset != 0 then none
  else
    match findV2026Alloc place.allocId mem.allocs with
    | none => none
    | some a =>
      let isMut : Bool :=
        match a.mutability with
        | .mut => true
        | .not => false
      if !a.live || !isMut then none
      else some { mem with allocs := replaceV2026Alloc { a with live := false } mem.allocs }

/-- Load and decode a typed `V2026_06_01.MirSemantics.Value` directly using
unmodified `decodeValueFromBytes`. -/
def loadV2026Typed (layouts : LayoutTable) (ty : Ty) (mem : V2026ByteMem)
    (place : V2026MemPlace) (len reqAlign : Nat) : Option Value :=
  match readV2026Bytes mem place len reqAlign with
  | none => none
  | some bs => decodeValueFromBytes defaultCodecFuel layouts ty bs

/-- Encode a typed `V2026_06_01.MirSemantics.Value` directly using unmodified
`encodeValueToBytes` and store into `mem`. -/
def storeV2026Typed (layouts : LayoutTable) (ty : Ty) (mem : V2026ByteMem)
    (place : V2026MemPlace) (reqAlign : Nat) (v : Value) : Option V2026ByteMem :=
  match encodeValueToBytes defaultCodecFuel layouts ty v with
  | none => none
  | some bs => writeV2026Bytes mem place reqAlign bs

/-- Convert an unmodified `CapturedAllocation` into a live `V2026ByteAlloc`
using `globalAllocSliceToAbstractBytes`. -/
def capturedAllocToByteAlloc (alloc : CapturedAllocation) : V2026ByteAlloc :=
  { allocId := alloc.allocId
    alignBytes := alloc.align.bytes
    mutability := alloc.mutability
    bytes := (globalAllocSliceToAbstractBytes alloc 0 alloc.bytes.length).getD []
    live := true }

/-- Embed all global allocations of an unmodified `V2026_06_01.MirSemantics.Memory`
into a `V2026ByteMem`. -/
def memGlobalsToByteMem (m : Memory) : V2026ByteMem :=
  { nextAllocId := m.nextAllocId
    allocs := m.globals.map capturedAllocToByteAlloc }

private theorem seqGet?_eq_listGetElem? {α : Type} :
    ∀ (xs : List α) (i : Nat), Trusted.Sequence.get? xs i = xs[i]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, k + 1 => seqGet?_eq_listGetElem? xs k

private theorem globalAllocBytesAux_length (bytes : List (Option UInt8))
    (relocs : List (Nat × ProvenancePtr)) :
    ∀ offset len, offset + len ≤ bytes.length →
      ∃ out, globalAllocBytesAux bytes relocs offset len = some out ∧ out.length = len := by
  intro offset len
  induction len generalizing offset with
  | zero =>
    intro _
    exact ⟨[], rfl, rfl⟩
  | succ rem ih =>
    intro hLe
    have hLt : offset < bytes.length := by omega
    have hOpt : Trusted.Sequence.get? bytes offset = some (bytes[offset]'hLt) := by
      rw [seqGet?_eq_listGetElem?, List.getElem?_eq_getElem hLt]
    obtain ⟨rest, hRest, hLen⟩ := ih (offset + 1) (by omega)
    let headByte : AbstractByte :=
      match bytes[offset]'hLt with
      | .none => AbstractByte.uninit
      | .some b =>
        let prov :=
          match lookupRelocAllocId relocs offset with
          | .some targetPtr => .some (targetPtr.allocId, targetPtr.tag)
          | .none => .none
        AbstractByte.init b prov
    refine ⟨headByte :: rest, ?_, ?_⟩
    · unfold globalAllocBytesAux
      rw [hOpt]
      change (match globalAllocBytesAux bytes relocs (offset + 1) rem with
        | none => none
        | some restBytes => some (headByte :: restBytes)) = some (headByte :: rest)
      rw [hRest]
    · simp only [List.length_cons, hLen]

private theorem globalAllocBytesAux_drop_take (bytes : List (Option UInt8))
    (relocs : List (Nat × ProvenancePtr)) :
    ∀ start total off len fullOut,
      globalAllocBytesAux bytes relocs start total = some fullOut →
      off + len ≤ total →
      globalAllocBytesAux bytes relocs (start + off) len =
        some ((fullOut.drop off).take len) := by
  intro start total
  induction total generalizing start with
  | zero =>
    intro off len fullOut hFull hLe
    have hOff : off = 0 := by omega
    have hLen : len = 0 := by omega
    subst hOff; subst hLen
    injection hFull with hNil
    subst hNil
    rfl
  | succ rem ih =>
    intro off len fullOut hFull hLe
    unfold globalAllocBytesAux at hFull
    cases hGet : Trusted.Sequence.get? bytes start with
    | none => rw [hGet] at hFull; nomatch hFull
    | some optB =>
      rw [hGet] at hFull
      cases hRest : globalAllocBytesAux bytes relocs (start + 1) rem with
      | none => rw [hRest] at hFull; nomatch hFull
      | some restOut =>
        rw [hRest] at hFull
        injection hFull with hCons
        subst hCons
        cases off with
        | zero =>
          cases len with
          | zero => rfl
          | succ l' =>
            simp only [Nat.add_zero, List.drop_zero, List.take_succ_cons]
            unfold globalAllocBytesAux
            rw [hGet]
            have hSub := ih (start + 1) 0 l' restOut hRest (by omega)
            simp only [Nat.add_zero, List.drop_zero] at hSub
            rw [hSub]
        | succ o' =>
          simp only [List.drop_succ_cons]
          have hAdd : start + (o' + 1) = (start + 1) + o' := by omega
          rw [hAdd]
          exact ih (start + 1) o' len restOut hRest (by omega)

/-- Exact bridge theorem: reading a slice from `capturedAllocToByteAlloc alloc`
agrees unconditionally with `Trusted.Rustc.V2026_06_01.MirSemantics.globalAllocSliceToAbstractBytes`. -/
theorem readV2026Bytes_capturedAllocToByteAlloc_eq_globalAllocSliceToAbstractBytes
    (alloc : CapturedAllocation) (offset len : Nat)
    (hAlignPos : 0 < alloc.align.bytes)
    (hBound : offset + len ≤ alloc.bytes.length) :
    readV2026Bytes { nextAllocId := alloc.allocId + 1, allocs := [capturedAllocToByteAlloc alloc] }
      ⟨alloc.allocId, offset⟩ len 1 =
      globalAllocSliceToAbstractBytes alloc offset len := by
  obtain ⟨fullOut, hFull, hFullLen⟩ :=
    globalAllocBytesAux_length alloc.bytes alloc.relocations 0 alloc.bytes.length (by omega)
  have hGlobFull :
      globalAllocSliceToAbstractBytes alloc 0 alloc.bytes.length = some fullOut := by
    unfold globalAllocSliceToAbstractBytes
    have hBle : Nat.ble 0 (Trusted.Sequence.length alloc.bytes) = true := rfl
    rw [hBle]
    exact hFull
  have hGlobSlice :
      globalAllocSliceToAbstractBytes alloc offset len =
        some ((fullOut.drop offset).take len) := by
    unfold globalAllocSliceToAbstractBytes
    have hBle : Nat.ble offset (Trusted.Sequence.length alloc.bytes) = true := by
      change Nat.ble offset alloc.bytes.length = true
      exact Nat.ble_eq.mpr (by omega)
    rw [hBle]
    have hSub := globalAllocBytesAux_drop_take alloc.bytes alloc.relocations
      0 alloc.bytes.length offset len fullOut hFull (by omega)
    simpa only [Nat.zero_add] using hSub
  rw [hGlobSlice]
  unfold readV2026Bytes findV2026Alloc capturedAllocToByteAlloc
  rw [hGlobFull]
  simp only [Option.getD_some, Nat.beq_refl, ↓reduceIte, v2026InBounds, v2026Aligned,
    hFullLen, Bool.not_true, Bool.false_or]
  have hIb : Nat.ble (offset + len) alloc.bytes.length = true :=
    Nat.ble_eq.mpr hBound
  have hAl : Nat.ble 1 alloc.align.bytes = true :=
    Nat.ble_eq.mpr hAlignPos
  have hMod : Nat.beq (offset % 1) 0 = true := by
    rw [Nat.mod_one]; rfl
  simp [hIb, hAl, hMod]

/-- All allocation IDs in `allocs` are strictly less than `bound`. -/
def v2026AllocIdsLt (allocs : List V2026ByteAlloc) (bound : AllocId) : Bool :=
  allocs.foldr (fun a acc => Nat.blt a.allocId bound && acc) true

theorem findV2026Alloc_append_lt (allocs : List V2026ByteAlloc) (aNew : V2026ByteAlloc)
    (hLt : v2026AllocIdsLt allocs aNew.allocId = true) :
    findV2026Alloc aNew.allocId (allocs ++ [aNew]) = some aNew := by
  induction allocs with
  | nil =>
    simp [findV2026Alloc]
  | cons a rest ih =>
    simp only [v2026AllocIdsLt, List.foldr, Bool.and_eq_true] at hLt
    have hNe : Nat.beq a.allocId aNew.allocId = false := by
      cases hEq : Nat.beq a.allocId aNew.allocId with
      | false => rfl
      | true =>
        have h1 : a.allocId = aNew.allocId := Nat.eq_of_beq_eq_true hEq
        have h2 : a.allocId < aNew.allocId := Nat.blt_eq.mp hLt.1
        rw [h1] at h2
        exact False.elim (Nat.lt_irrefl _ h2)
    simp only [List.cons_append, findV2026Alloc, hNe, Bool.false_eq_true, ↓reduceIte]
    exact ih hLt.2

theorem findV2026Alloc_none_of_lt (allocs : List V2026ByteAlloc) (aid : AllocId)
    (hLt : v2026AllocIdsLt allocs aid = true) :
    findV2026Alloc aid allocs = none := by
  induction allocs with
  | nil => rfl
  | cons a rest ih =>
    simp only [v2026AllocIdsLt, List.foldr, Bool.and_eq_true] at hLt
    have hNe : Nat.beq a.allocId aid = false := by
      cases hEq : Nat.beq a.allocId aid with
      | false => rfl
      | true =>
        have h1 : a.allocId = aid := Nat.eq_of_beq_eq_true hEq
        have h2 : a.allocId < aid := Nat.blt_eq.mp hLt.1
        rw [h1] at h2
        exact False.elim (Nat.lt_irrefl _ h2)
    simp only [findV2026Alloc, hNe, Bool.false_eq_true, ↓reduceIte]
    exact ih hLt.2

theorem findV2026Alloc_append_ne (allocs : List V2026ByteAlloc) (aNew : V2026ByteAlloc)
    (otherId : AllocId) (hNe : otherId ≠ aNew.allocId) :
    findV2026Alloc otherId (allocs ++ [aNew]) = findV2026Alloc otherId allocs := by
  induction allocs with
  | nil =>
    have hBeq : Nat.beq aNew.allocId otherId = false := by
      cases hEq : Nat.beq aNew.allocId otherId with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true hEq).symm hNe
    simp [findV2026Alloc, hBeq]
  | cons a rest ih =>
    simp only [List.cons_append, findV2026Alloc]
    cases Nat.beq a.allocId otherId with
    | true => rfl
    | false => exact ih

theorem findV2026Alloc_replace_ne (allocs : List V2026ByteAlloc) (a' : V2026ByteAlloc)
    (otherId : AllocId) (hNe : otherId ≠ a'.allocId) :
    findV2026Alloc otherId (replaceV2026Alloc a' allocs) = findV2026Alloc otherId allocs := by
  induction allocs with
  | nil => rfl
  | cons a rest ih =>
    simp only [replaceV2026Alloc]
    cases hMatch : Nat.beq a.allocId a'.allocId with
    | true =>
      have hEq : a.allocId = a'.allocId := Nat.eq_of_beq_eq_true hMatch
      have hNe1 : Nat.beq a'.allocId otherId = false := by
        cases h2 : Nat.beq a'.allocId otherId with
        | false => rfl
        | true => exact absurd (Nat.eq_of_beq_eq_true h2).symm hNe
      have hNe2 : Nat.beq a.allocId otherId = false := by
        rw [hEq]; exact hNe1
      simp only [↓reduceIte, findV2026Alloc, hNe1, hNe2, Bool.false_eq_true]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, findV2026Alloc]
      cases Nat.beq a.allocId otherId with
      | true => rfl
      | false => exact ih

theorem replaceV2026Alloc_append_lt (allocs : List V2026ByteAlloc)
    (aOld aNew : V2026ByteAlloc)
    (hLt : v2026AllocIdsLt allocs aNew.allocId = true)
    (hEqId : aOld.allocId = aNew.allocId) :
    replaceV2026Alloc aNew (allocs ++ [aOld]) = allocs ++ [aNew] := by
  induction allocs with
  | nil =>
    simp [replaceV2026Alloc, hEqId]
  | cons a rest ih =>
    simp only [v2026AllocIdsLt, List.foldr, Bool.and_eq_true] at hLt
    have hNe : Nat.beq a.allocId aNew.allocId = false := by
      cases hEq : Nat.beq a.allocId aNew.allocId with
      | false => rfl
      | true =>
        have h1 : a.allocId = aNew.allocId := Nat.eq_of_beq_eq_true hEq
        have h2 : a.allocId < aNew.allocId := Nat.blt_eq.mp hLt.1
        rw [h1] at h2
        exact False.elim (Nat.lt_irrefl _ h2)
    simp only [List.cons_append, replaceV2026Alloc, hNe, Bool.false_eq_true, ↓reduceIte]
    exact congrArg (List.cons a) (ih hLt.2)

/-- Cross-allocation framing for `allocV2026Stack`: reading a disjoint allocation
is invariant across stack allocation. -/
theorem readV2026Bytes_allocStack_other_alloc (mem : V2026ByteMem)
    (size alignBytes : Nat) (other : V2026MemPlace) (len reqAlign : Nat)
    (hNe : other.allocId ≠ mem.nextAllocId) :
    readV2026Bytes (allocV2026Stack mem size alignBytes).2 other len reqAlign =
      readV2026Bytes mem other len reqAlign := by
  unfold readV2026Bytes allocV2026Stack
  dsimp only
  rw [findV2026Alloc_append_ne mem.allocs
    { allocId := mem.nextAllocId, alignBytes := alignBytes, mutability := .mut,
      bytes := List.replicate size .uninit, live := true }
    other.allocId hNe]

private theorem findV2026Alloc_id_eq : ∀ (xs : List V2026ByteAlloc) (aid : AllocId) (a : V2026ByteAlloc),
    findV2026Alloc aid xs = some a → a.allocId = aid
  | [], _, _, h => nomatch h
  | hd :: tl, aid, a, h => by
    unfold findV2026Alloc at h
    cases hB : Nat.beq hd.allocId aid with
    | true =>
      rw [hB] at h
      simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      exact Nat.eq_of_beq_eq_true hB
    | false =>
      rw [hB] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact findV2026Alloc_id_eq tl aid a h

/-- Cross-allocation framing for `writeV2026Bytes`: writing into `place` leaves
reads from any disjoint `other.allocId ≠ place.allocId` unchanged. -/
theorem readV2026Bytes_writeBytes_other_alloc (mem mem' : V2026ByteMem)
    (place other : V2026MemPlace) (wAlign len rAlign : Nat)
    (newBytes : List AbstractByte)
    (hNe : other.allocId ≠ place.allocId)
    (hWrite : writeV2026Bytes mem place wAlign newBytes = some mem') :
    readV2026Bytes mem' other len rAlign = readV2026Bytes mem other len rAlign := by
  unfold writeV2026Bytes at hWrite
  cases hEmp : newBytes.isEmpty with
  | true => rw [hEmp] at hWrite; simp at hWrite
  | false =>
    rw [hEmp] at hWrite
    simp only [Bool.false_eq_true, ↓reduceIte] at hWrite
    cases hFind : findV2026Alloc place.allocId mem.allocs with
    | none => rw [hFind] at hWrite; nomatch hWrite
    | some a =>
      rw [hFind] at hWrite
      dsimp only at hWrite
      cases hMut : a.mutability with
      | not => rw [hMut] at hWrite; simp at hWrite
      | «mut» =>
        rw [hMut] at hWrite
        dsimp only at hWrite
        split at hWrite
        · nomatch hWrite
        · injection hWrite with hMem'
          subst hMem'
          have hAId : a.allocId = place.allocId := findV2026Alloc_id_eq mem.allocs place.allocId a hFind
          unfold readV2026Bytes
          rw [findV2026Alloc_replace_ne mem.allocs _ other.allocId (by simpa [hAId] using hNe)]

/-- Cross-allocation framing for `deallocateV2026Stack`. -/
theorem readV2026Bytes_deallocateStack_other_alloc (mem mem' : V2026ByteMem)
    (place other : V2026MemPlace) (len rAlign : Nat)
    (hNe : other.allocId ≠ place.allocId)
    (hDealloc : deallocateV2026Stack mem place = some mem') :
    readV2026Bytes mem' other len rAlign = readV2026Bytes mem other len rAlign := by
  unfold deallocateV2026Stack at hDealloc
  cases hOff : (place.offset != 0) with
  | true => rw [hOff] at hDealloc; simp at hDealloc
  | false =>
    rw [hOff] at hDealloc
    simp only [Bool.false_eq_true, ↓reduceIte] at hDealloc
    cases hFind : findV2026Alloc place.allocId mem.allocs with
    | none => rw [hFind] at hDealloc; nomatch hDealloc
    | some a =>
      rw [hFind] at hDealloc
      dsimp only at hDealloc
      cases hMut : a.mutability with
      | not => rw [hMut] at hDealloc; simp at hDealloc
      | «mut» =>
        rw [hMut] at hDealloc
        dsimp only at hDealloc
        split at hDealloc
        · nomatch hDealloc
        · injection hDealloc with hMem'
          subst hMem'
          have hAId : a.allocId = place.allocId := findV2026Alloc_id_eq mem.allocs place.allocId a hFind
          unfold readV2026Bytes
          rw [findV2026Alloc_replace_ne mem.allocs _ other.allocId (by simpa [hAId] using hNe)]

/-! ## 2. Tagged Scalar `SpatialCodec` (`ValByteCodec`) -/

/-- Encode a natural number `< 2^32` into 4 little-endian `UInt8` bytes. -/
def encodeU32LEBytes (n : Nat) : List UInt8 :=
  [ UInt8.ofNat n
  , UInt8.ofNat (n / 256)
  , UInt8.ofNat (n / 65536)
  , UInt8.ofNat (n / 16777216) ]

/-- Decode 4 little-endian `UInt8` bytes into a natural number `< 2^32`. -/
def decodeU32LEBytes (b0 b1 b2 b3 : UInt8) : Nat :=
  b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat))

theorem decodeU32LEBytes_encodeU32LEBytes (n : Nat) (hLt : n < 4294967296) :
    decodeU32LEBytes
      (UInt8.ofNat n)
      (UInt8.ofNat (n / 256))
      (UInt8.ofNat (n / 65536))
      (UInt8.ofNat (n / 16777216)) = n := by
  unfold decodeU32LEBytes
  have h0 : (UInt8.ofNat n).toNat = n % 256 := uint8_ofNat_toBitVec_toNat n
  have h1 : (UInt8.ofNat (n / 256)).toNat = (n / 256) % 256 := uint8_ofNat_toBitVec_toNat _
  have h2 : (UInt8.ofNat (n / 65536)).toNat = (n / 65536) % 256 := uint8_ofNat_toBitVec_toNat _
  have h3 : (UInt8.ofNat (n / 16777216)).toNat = (n / 16777216) % 256 := uint8_ofNat_toBitVec_toNat _
  rw [h0, h1, h2, h3]
  omega

theorem decodeU32LEBytes_lt (b0 b1 b2 b3 : UInt8) :
    decodeU32LEBytes b0 b1 b2 b3 < 4294967296 := by
  unfold decodeU32LEBytes
  have h0 : b0.toNat < 256 := b0.toBitVec.isLt
  have h1 : b1.toNat < 256 := b1.toBitVec.isLt
  have h2 : b2.toNat < 256 := b2.toBitVec.isLt
  have h3 : b3.toNat < 256 := b3.toBitVec.isLt
  omega

/-- Agreement between `encodeU32LEBytes` and `Trusted.Rustc.V2026_06_01.MirSemantics.encodeValueToBytes`
for `u32` scalars. -/
theorem encodeU32LEBytes_eq_mir (layouts : LayoutTable) (n : Nat)
    (hLt : n < 4294967296) :
    encodeValueToBytes defaultCodecFuel layouts { kind := .uint .u32, layoutIdx := 0 }
      (.scalar ⟨n, 4⟩) =
      some ((encodeU32LEBytes n).map (fun b => AbstractByte.init b none)) := by
  have hBlt : Nat.blt n 4294967296 = true := Nat.blt_eq.mpr hLt
  unfold encodeValueToBytes encodeScalarBytes encodeLittleEndianBytes encodeU32LEBytes
  simp only [intCastTargetBytes,
    List.map, Option.some.injEq, List.cons.injEq, AbstractByte.init.injEq, and_true, true_and]
  have hD1 : n.div 256 = n / 256 := rfl
  have hD2 : (n.div 256).div 256 = n / 65536 := by
    change (n / 256) / 256 = n / 65536
    rw [Nat.div_div_eq_div_mul]
  have hD3 : ((n.div 256).div 256).div 256 = n / 16777216 := by
    rw [hD2]
    change (n / 65536) / 256 = n / 16777216
    rw [Nat.div_div_eq_div_mul]
  rw [hD3, hD2, hD1]
  exact ⟨rfl, rfl, rfl⟩

/-- Tagged `SpatialCodec` over unmodified `Trusted.Rustc.V2026_06_01.MirSemantics.Value`:
encodes canonical `u32` scalars (`sizeBytes = 4`, `bits < 2^32`) as 5 raw byte cells
`[.rawByte 1, .rawByte b0, .rawByte b1, .rawByte b2, .rawByte b3]`, and tags all
other values losslessly as `[.rawByte 0, .init v]`. -/
def u32TaggedByteCodec : SpatialCodec Value where
  codecId := 3201
  encode v :=
    match v with
    | .scalar sv =>
      if sv.sizeBytes == 4 && Nat.blt sv.bits 4294967296 then
        .rawByte 1 :: (encodeU32LEBytes sv.bits).map CellVal.rawByte
      else
        [.rawByte 0, .init v]
    | _ => [.rawByte 0, .init v]
  decode cells :=
    match cells with
    | [.rawByte 1, .rawByte b0, .rawByte b1, .rawByte b2, .rawByte b3] =>
      some (.scalar ⟨decodeU32LEBytes b0 b1 b2 b3, 4⟩)
    | [.rawByte 0, .init v] => some v
    | _ => none
  decode_encode v := by
    cases v with
    | unit => rfl
    | ptr _ _ => rfl
    | aggregate _ _ => rfl
    | uninit => rfl
    | scalar sv =>
      cases sv with
      | mk bits sz =>
        dsimp only
        cases hCond : ((sz == 4) && Nat.blt bits 4294967296) with
        | false => rfl
        | true =>
          simp only [Bool.and_eq_true, beq_iff_eq] at hCond
          obtain ⟨rfl, hBlt⟩ := hCond
          have hLt : bits < 4294967296 := Nat.blt_eq.mp hBlt
          simp only [↓reduceIte, encodeU32LEBytes, List.map,
            decodeU32LEBytes_encodeU32LEBytes bits hLt]

theorem u32TaggedByteCodec_lawful : LawfulCodec u32TaggedByteCodec :=
  u32TaggedByteCodec.decode_encode

/-- Tagged `SpatialCodec` over `PureLift`'s lawful `StdVal` carrier, encoding
`StdVal.nat n` (`n < 2^32`) into the identical 5-cell little-endian raw byte
layout `[.rawByte 1, b0, b1, b2, b3]`. -/
def u32TaggedStdByteCodec : SpatialCodec StdVal where
  codecId := 3202
  encode v :=
    match v with
    | ⟨_, .nat n⟩ =>
      if Nat.blt n 4294967296 then
        .rawByte 1 :: (encodeU32LEBytes n).map CellVal.rawByte
      else
        [.rawByte 0, .init v]
    | _ => [.rawByte 0, .init v]
  decode cells :=
    match cells with
    | [.rawByte 1, .rawByte b0, .rawByte b1, .rawByte b2, .rawByte b3] =>
      some (StdVal.nat (decodeU32LEBytes b0 b1 b2 b3))
    | [.rawByte 0, .init v] => some v
    | _ => none
  decode_encode v := by
    cases v with
    | mk fuel tree =>
      cases tree with
      | unit => rfl
      | bool _ => rfl
      | symBool _ => rfl
      | pairBranch _ _ _ _ => rfl
      | refVal _ _ => rfl
      | choice _ _ _ _ _ _ => rfl
      | nat n =>
        dsimp only
        cases hBlt : Nat.blt n 4294967296 with
        | false => rfl
        | true =>
          have hLt : n < 4294967296 := Nat.blt_eq.mp hBlt
          simp only [↓reduceIte, encodeU32LEBytes, List.map,
            decodeU32LEBytes_encodeU32LEBytes n hLt, StdVal.nat]

theorem u32TaggedStdByteCodec_lawful : LawfulCodec u32TaggedStdByteCodec :=
  u32TaggedStdByteCodec.decode_encode

private theorem mutateSpatialBlockAt_append_disjoint {Val : Type}
    (bid tag : Nat) (newCells : List (CellVal Val))
    (b : SpatialBlock Val) (hFrame : List (SpatialBlock Val))
    (hDisj : blocksDisjoint [b] hFrame)
    (hId : b.blockId = bid) (hTag : b.provenanceTag = tag)
    (hPerm : b.perm = .readWrite) (hSub : b.activeSubSplits = 0)
    (hLen : newCells.length = b.cells.length) :
    mutateSpatialBlockAt bid tag newCells ([b] ++ hFrame) =
      some ([⟨b.blockId, b.originLoan, b.perm, b.provenanceTag,
              b.activeSubSplits, newCells⟩] ++ hFrame) := by
  let stepFn : SpatialBlock Val → Bool × Bool × List (SpatialBlock Val) →
      Bool × Bool × List (SpatialBlock Val) :=
    fun b (acc : Bool × Bool × List (SpatialBlock Val)) =>
      match acc with
      | (dup, found, rest) =>
        if b.blockId == bid then
          if found then
            (true, true, rest)
          else
            let writable : Bool :=
              match b.perm with
              | .readWrite => true
              | .readOnly => false
            if b.provenanceTag == tag && writable &&
               b.activeSubSplits == 0 &&
               newCells.length == b.cells.length then
              let b' : SpatialBlock Val :=
                ⟨b.blockId, b.originLoan, b.perm, b.provenanceTag,
                 b.activeSubSplits, newCells⟩
              (dup, true, b' :: rest)
            else
              (true, true, rest)
        else
          (dup, found, b :: rest)
  have hFrameNoBid : hFrame.foldr stepFn (false, false, []) = (false, false, hFrame) := by
    induction hFrame with
    | nil => rfl
    | cons x xs ih =>
      have hDisjX : b.blockId ≠ x.blockId :=
        (hDisj b x (List.Mem.head _) (List.Mem.head _)).1
      have hNe : (x.blockId == bid) = false := by
        rw [← hId]
        cases hEq : (x.blockId == b.blockId) with
        | false => rfl
        | true => exact absurd (beq_iff_eq.mp hEq).symm hDisjX
      have hRest : blocksDisjoint [b] xs :=
        fun b1 b2 hb1 hb2 => hDisj b1 b2 hb1 (List.Mem.tail _ hb2)
      simp only [List.foldr, ih hRest, stepFn, hNe, Bool.false_eq_true, ↓reduceIte]
  unfold mutateSpatialBlockAt
  change (match (b :: hFrame).foldr stepFn (false, false, []) with
    | (false, true, updated) => some updated
    | _ => none) = _
  rw [List.foldr, hFrameNoBid]
  simp only [stepFn, hId, hTag, hPerm, hSub, hLen, beq_self_eq_true, Bool.and_self, ↓reduceIte]
  rfl

private theorem u32TaggedStdByteCodec_encode_nat (n : Nat) (hLt : n < 4294967296) :
    u32TaggedStdByteCodec.encode (StdVal.nat n) =
      .rawByte 1 :: (encodeU32LEBytes n).map CellVal.rawByte := by
  have hB : Nat.blt n 4294967296 = true := Nat.blt_eq.mpr hLt
  dsimp only [u32TaggedStdByteCodec, StdVal.nat]
  rw [hB]
  rfl

/-- Tagged-provenance spatial points-to assertion (`blockId = bid`, `provenanceTag = bid`,
`.readWrite`, zero active sub-splits). -/
def spatialTaggedPointsTo {Val : Type} (bid : BlockId) (perm : SpatialPerm)
    (cells : List (CellVal Val)) : SpatialProp Val :=
  fun blocks =>
    match blocks with
    | [b] =>
      b.blockId = bid ∧ b.provenanceTag = bid ∧ b.perm = perm ∧
      b.activeSubSplits = 0 ∧ b.cells = cells
    | _ => False

/-- Framed `SpatialTriple` for mutating a provenance-tagged `u32TaggedStdByteCodec`
block, directly composable via `Anneal.PureLift.spatial_frame_law`. -/
theorem u32TaggedStd_tagged_mutate_spatialTriple (bid : BlockId) (x y : Nat)
    (hX : x < 4294967296) (hY : y < 4294967296) :
    SpatialTriple
      (spatialTaggedPointsTo bid .readWrite (u32TaggedStdByteCodec.encode (StdVal.nat x)))
      (mutateSpatialBlockAt bid bid (u32TaggedStdByteCodec.encode (StdVal.nat y)))
      (spatialTaggedPointsTo bid .readWrite (u32TaggedStdByteCodec.encode (StdVal.nat y))) := by
  intro h hFrame hDisj hPre
  cases h with
  | nil => exact False.elim hPre
  | cons b rest =>
    cases rest with
    | cons _ _ => exact False.elim hPre
    | nil =>
      obtain ⟨hBid, hTag, hPerm, hSub, hCells⟩ := hPre
      have hLenEq :
          (u32TaggedStdByteCodec.encode (StdVal.nat y)).length = b.cells.length := by
        rw [hCells, u32TaggedStdByteCodec_encode_nat x hX, u32TaggedStdByteCodec_encode_nat y hY]
        rfl
      let b' : SpatialBlock StdVal :=
        ⟨b.blockId, b.originLoan, b.perm, b.provenanceTag, b.activeSubSplits,
         u32TaggedStdByteCodec.encode (StdVal.nat y)⟩
      refine ⟨[b'], ?_, ?_, ⟨hBid, hTag, hPerm, hSub, rfl⟩⟩
      · exact mutateSpatialBlockAt_append_disjoint bid bid _ b hFrame hDisj
          hBid hTag hPerm hSub hLenEq
      · intro b1 b2 hb1 hb2
        cases hb1 with
        | head _ => exact hDisj b b2 (List.Mem.head _) hb2
        | tail _ hb1' => nomatch hb1'

/-- End-to-end framed `freezeToSpatialInState` → `mutateSpatialInState`
(framed via `spatial_frame_law`) → `reabsorbFromSpatialInState` round-trip
for `u32TaggedStdByteCodec`. -/
theorem u32TaggedStd_freeze_mutate_reabsorb_framed (x y : Nat)
    (hX : x < 4294967296) (hY : y < 4294967296) :
    let st0 : SymState StdVal :=
      { locals := [⟨StdVal.nat x, .mutLocked 0⟩]
        loans := [⟨0, .activeMut, ⟨StdVal.nat x, .unborrowed⟩, .direct (.localReg 0) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 1 }
    ∃ stPinned stMut stReabsorbed,
      freezeToSpatialInState stdValAlg 0 u32TaggedStdByteCodec st0 = .ok stPinned ∧
      mutateSpatialInState 1 1 (u32TaggedStdByteCodec.encode (StdVal.nat y)) stPinned = .ok stMut ∧
      reabsorbFromSpatialInState stdValAlg 0 u32TaggedStdByteCodec stMut = .ok stReabsorbed ∧
      findLoan 0 stReabsorbed.loans =
        some ⟨0, .activeMut, ⟨StdVal.nat y, .unborrowed⟩, .direct (.localReg 0) []⟩ ∧
      stReabsorbed.spatial = [] := by
  intro st0
  have hEncX : u32TaggedStdByteCodec.encode (StdVal.nat x) =
      .rawByte 1 :: (encodeU32LEBytes x).map CellVal.rawByte :=
    u32TaggedStdByteCodec_encode_nat x hX
  have hEncY : u32TaggedStdByteCodec.encode (StdVal.nat y) =
      .rawByte 1 :: (encodeU32LEBytes y).map CellVal.rawByte :=
    u32TaggedStdByteCodec_encode_nat y hY
  let stPinned : SymState StdVal :=
    { locals := [⟨StdVal.nat x, .mutLocked 0⟩]
      loans := [⟨0, .spatialPinned 1 u32TaggedStdByteCodec,
                 ⟨StdVal.nat x, .unborrowed⟩, .direct (.localReg 0) []⟩]
      regionGroups := []
      regionDeposits := []
      spatial := [⟨1, 0, .readWrite, 1, 0, u32TaggedStdByteCodec.encode (StdVal.nat x)⟩]
      nextSpatialTag := 2 }
  let stMut : SymState StdVal :=
    { stPinned with
      spatial := [⟨1, 0, .readWrite, 1, 0, u32TaggedStdByteCodec.encode (StdVal.nat y)⟩] }
  let stReabsorbed : SymState StdVal :=
    { locals := [⟨StdVal.nat x, .mutLocked 0⟩]
      loans := [⟨0, .activeMut, ⟨StdVal.nat y, .unborrowed⟩, .direct (.localReg 0) []⟩]
      regionGroups := []
      regionDeposits := []
      spatial := []
      nextSpatialTag := 2 }
  have hFreeze :
      freezeToSpatialInState stdValAlg 0 u32TaggedStdByteCodec st0 = .ok stPinned := by
    unfold freezeToSpatialInState
    have hUniq : hasUniqueLoanId 0 st0.loans = true := rfl
    have hFind : findLoan 0 st0.loans =
        some ⟨0, .activeMut, ⟨StdVal.nat x, .unborrowed⟩, .direct (.localReg 0) []⟩ := rfl
    have hChildL : noActiveChildLoanEdgesIn stdValAlg 0 st0.loans = true := rfl
    have hChildR : noActiveChildRegionEdges 0 st0.regionGroups = true := rfl
    rw [hUniq, hFind]
    dsimp only [LoanPhase.isActiveMut, isUnborrowed, hChildL, hChildR, st0, stPinned]
    rw [hChildL, hChildR, hEncX]
    rfl
  have hSepPre :
      spatialSepConj
        (spatialTaggedPointsTo 1 .readWrite (u32TaggedStdByteCodec.encode (StdVal.nat x)))
        spatialEmp stPinned.spatial :=
    Exists.intro stPinned.spatial
      (Exists.intro []
        ⟨(List.append_nil _).symm,
          (fun _ _ _ hb2 => nomatch hb2),
          ⟨rfl, rfl, rfl, rfl, rfl⟩,
          rfl⟩)
  have hFrameStep :=
    spatial_frame_law
      (spatialTaggedPointsTo 1 .readWrite (u32TaggedStdByteCodec.encode (StdVal.nat x)))
      (spatialTaggedPointsTo 1 .readWrite (u32TaggedStdByteCodec.encode (StdVal.nat y)))
      spatialEmp
      (mutateSpatialBlockAt 1 1 (u32TaggedStdByteCodec.encode (StdVal.nat y)))
      (u32TaggedStd_tagged_mutate_spatialTriple 1 x y hX hY)
      stPinned.spatial hSepPre
  obtain ⟨_, _, _⟩ := hFrameStep
  have hMut :
      mutateSpatialInState 1 1 (u32TaggedStdByteCodec.encode (StdVal.nat y)) stPinned = .ok stMut := by
    unfold mutateSpatialInState
    dsimp only [stPinned, stMut]
    have hLenY : (u32TaggedStdByteCodec.encode (StdVal.nat y)).length =
        (u32TaggedStdByteCodec.encode (StdVal.nat x)).length := by
      rw [hEncX, hEncY]; rfl
    have hMutDirect :
        mutateSpatialBlockAt 1 1 (u32TaggedStdByteCodec.encode (StdVal.nat y))
          [⟨1, 0, .readWrite, 1, 0, u32TaggedStdByteCodec.encode (StdVal.nat x)⟩] =
          some [⟨1, 0, .readWrite, 1, 0, u32TaggedStdByteCodec.encode (StdVal.nat y)⟩] :=
      mutateSpatialBlockAt_append_disjoint 1 1 _ _ []
        (fun _ _ _ hb2 => nomatch hb2) rfl rfl rfl rfl hLenY
    rw [hMutDirect]
  have hReab :
      reabsorbFromSpatialInState stdValAlg 0 u32TaggedStdByteCodec stMut = .ok stReabsorbed := by
    unfold reabsorbFromSpatialInState
    have hUniq : hasUniqueLoanId 0 stMut.loans = true := rfl
    have hFind : findLoan 0 stMut.loans =
        some ⟨0, .spatialPinned 1 u32TaggedStdByteCodec, ⟨StdVal.nat x, .unborrowed⟩,
          .direct (.localReg 0) []⟩ := rfl
    have hBlk : findSpatialBlock stMut.spatial 1 =
        some (⟨1, 0, .readWrite, 1, 0, u32TaggedStdByteCodec.encode (StdVal.nat y)⟩, []) := rfl
    have hDecY : u32TaggedStdByteCodec.decode (u32TaggedStdByteCodec.encode (StdVal.nat y)) =
        some (StdVal.nat y) := u32TaggedStdByteCodec.decode_encode (StdVal.nat y)
    have hUninitY : hasUninitCell (u32TaggedStdByteCodec.encode (StdVal.nat y)) = false := by
      rw [hEncY]; rfl
    have hAccY : cellsAccountedByVal stdValAlg stMut.loans (StdVal.nat x)
        (u32TaggedStdByteCodec.encode (StdVal.nat y)) = true := by
      rw [hEncY]; rfl
    have hRepY : replaceableVal stdValAlg stMut.loans (StdVal.nat x) (StdVal.nat y) = true := rfl
    rw [hUniq, hFind]
    dsimp only
    rw [hBlk]
    dsimp only
    rw [hUninitY, hAccY]
    simp only [countBlocksForLoan, List.foldr, beq_self_eq_true, Bool.not_false, Bool.and_self,
      ↓reduceIte, hDecY]
    rw [hRepY]
    rfl
  exact ⟨stPinned, stMut, stReabsorbed, hFreeze, hMut, hReab, rfl, rfl⟩

/-! ## 3. Padded & Provenance-Aware Spatial Pinning (`PaddedPin`) -/

/-- Audited field descriptor `(byteOffset, mirTy)` for a `#[repr(C)]` or
captured-layout aggregate. -/
structure AuditedFieldSpec where
  offset : Nat
  fieldTy : Ty

/-- Authenticated spatial target type: either a direct primitive/pointer MIR type
or a layout-audited aggregate (`#[repr(C)]` struct or padded tuple) with explicit
byte size, alignment, and field offsets checked against a `CapturedMir`'s
`LayoutTable`. -/
inductive SpatialTargetSpec where
  | mirTy (ty : Ty)
  | reprCAdt (typeId : Nat) (ty : Ty) (sizeBytes alignBytes : Nat)
      (fields : List AuditedFieldSpec)

/-- Extract the underlying `V2026_06_01.MirAst.Ty` of a `SpatialTargetSpec`. -/
def SpatialTargetSpec.toMirTy : SpatialTargetSpec → Ty
  | .mirTy ty => ty
  | .reprCAdt _ ty _ _ _ => ty

/-- Rejects `&T` / `&mut T` reference targets from being directly reinterpreted
as raw byte storage without going through borrow mediation. -/
def SpatialTargetSpec.isRefTarget : SpatialTargetSpec → Bool
  | .mirTy ty =>
    match ty.kind with
    | .ref _ _ => true
    | _ => false
  | .reprCAdt _ ty _ _ _ =>
    match ty.kind with
    | .ref _ _ => true
    | _ => false

/-- Structural equality on `UintTy`. -/
def uintTyBeq : UintTy → UintTy → Bool
  | .u8, .u8 | .u16, .u16 | .u32, .u32 | .u64, .u64 | .u128, .u128 | .usize, .usize => true
  | _, _ => false

/-- Structural equality on `IntTy`. -/
def intTyBeq : IntTy → IntTy → Bool
  | .i8, .i8 | .i16, .i16 | .i32, .i32 | .i64, .i64 | .i128, .i128 | .isize, .isize => true
  | _, _ => false

/-- Structural equality on `Mutability`. -/
def mutabilityBeq : Mutability → Mutability → Bool
  | .not, .not | .mut, .mut => true
  | _, _ => false

/-- Bounded structural equality on `RigidTy` (covering all audited spatial targets). -/
def rigidTyBeq : Nat → RigidTy → RigidTy → Bool
  | 0, _, _ => false
  | _ + 1, .bool, .bool => true
  | _ + 1, .char, .char => true
  | _ + 1, .uint a, .uint b => uintTyBeq a b
  | _ + 1, .int a, .int b => intTyBeq a b
  | fuel + 1, .rawPtr m1 p1, .rawPtr m2 p2 => mutabilityBeq m1 m2 && rigidTyBeq fuel p1 p2
  | fuel + 1, .ref m1 p1, .ref m2 p2 => mutabilityBeq m1 m2 && rigidTyBeq fuel p1 p2
  | fuel + 1, .tuple ks1, .tuple ks2 =>
    let rec go : List RigidTy → List RigidTy → Bool
      | [], [] => true
      | a :: as, b :: bs => rigidTyBeq fuel a b && go as bs
      | _, _ => false
    go ks1 ks2
  | fuel + 1, .adt p1 args1, .adt p2 args2 =>
    (p1 == p2) &&
    let rec goArgs : List RigidTy → List RigidTy → Bool
      | [], [] => true
      | a :: as, b :: bs => rigidTyBeq fuel a b && goArgs as bs
      | _, _ => false
    goArgs args1 args2
  | _, _, _ => false

/-- Structural equality on `Ty`. -/
def mirTyBeq (t1 t2 : Ty) : Bool :=
  Nat.beq t1.layoutIdx t2.layoutIdx && rigidTyBeq 8 t1.kind t2.kind

/-- Structural equality on `AuditedFieldSpec`. -/
def auditedFieldSpecBeq (f1 f2 : AuditedFieldSpec) : Bool :=
  Nat.beq f1.offset f2.offset && mirTyBeq f1.fieldTy f2.fieldTy

/-- Structural equality on `List AuditedFieldSpec`. -/
def auditedFieldSpecListBeq : List AuditedFieldSpec → List AuditedFieldSpec → Bool
  | [], [] => true
  | x :: xs, y :: ys => auditedFieldSpecBeq x y && auditedFieldSpecListBeq xs ys
  | _, _ => false

/-- Structural equality on `SpatialTargetSpec`. -/
def spatialTargetSpecBeq : SpatialTargetSpec → SpatialTargetSpec → Bool
  | .mirTy t1, .mirTy t2 => mirTyBeq t1 t2
  | .reprCAdt id1 ty1 sz1 al1 fs1, .reprCAdt id2 ty2 sz2 al2 fs2 =>
    Nat.beq id1 id2 && mirTyBeq ty1 ty2 && Nat.beq sz1 sz2 && Nat.beq al1 al2 &&
    auditedFieldSpecListBeq fs1 fs2
  | _, _ => false

/-- Check that a list of `Size` offsets equals the field offsets of `fields`. -/
def offsetsMatchFields : List Size → List AuditedFieldSpec → Bool
  | [], [] => true
  | o :: os, f :: fs => Nat.beq o.bytes f.offset && offsetsMatchFields os fs
  | _, _ => false

/-- Check that a list of `RigidTy` field kinds matches the kinds of `fields`. -/
def rigidKindsMatchFields : List RigidTy → List AuditedFieldSpec → Bool
  | [], [] => true
  | k :: ks, f :: fs => rigidTyBeq 6 k f.fieldTy.kind && rigidKindsMatchFields ks fs
  | _, _ => false

/-- Authenticate a single `SpatialTargetSpec` against the captured `LayoutTable`
and declared local type `declTy` of a real `CapturedMir` body. -/
def specMatchesDeclAndLayout (layouts : LayoutTable) (declTy : Ty)
    (spec : SpatialTargetSpec) : Bool :=
  mirTyBeq spec.toMirTy declTy &&
  match spec with
  | .mirTy _ => true
  | .reprCAdt _ ty sz al fields =>
    !spec.isRefTarget &&
    match LayoutTable.lookup layouts ty.layoutIdx with
    | none => false
    | some l =>
      l.isWellFormed &&
      Nat.beq l.size.bytes sz &&
      Nat.beq l.align.bytes al &&
      match l.fields, ty.kind with
      | .arbitrary offsets _, .tuple ks =>
        offsetsMatchFields offsets fields && rigidKindsMatchFields ks fields
      | .arbitrary offsets _, .adt _ args =>
        offsetsMatchFields offsets fields &&
        (if args.isEmpty then true else rigidKindsMatchFields args fields)
      | _, _ => false

/-- Authenticated body context pairing an unmodified `CapturedMir` with its
audited per-local `SpatialTargetSpec`s. -/
structure BodySpatialCtx where
  body : CapturedMir
  specs : List SpatialTargetSpec

/-- Check that every local spec in `ctx` is authenticated against `ctx.body`'s
`wellFormed` flag, `localDecls`, and `layouts`. -/
def bodySpatialCtxWf (ctx : BodySpatialCtx) : Bool :=
  let rec go : List LocalDecl → List SpatialTargetSpec → Bool
    | [], [] => true
    | d :: ds, s :: ss =>
      specMatchesDeclAndLayout ctx.body.layouts d.ty s && go ds ss
    | _, _ => false
  ctx.body.wellFormed && go ctx.body.localDecls ctx.specs

/-- Check that `localSpecs` matches an authenticated `BodySpatialCtx`. -/
def specsMatchBodyCtx (ctx : BodySpatialCtx) (localSpecs : List SpatialTargetSpec) : Bool :=
  let rec go : List SpatialTargetSpec → List SpatialTargetSpec → Bool
    | [], [] => true
    | a :: as, b :: bs => spatialTargetSpecBeq a b && go as bs
    | _, _ => false
  bodySpatialCtxWf ctx && go ctx.specs localSpecs

/-- True iff every byte where `padMask[i] = false` is initialized (`.init _ _`).
Rejects length mismatches fail-closed. -/
def nonPadBytesInitialized : List Bool → List AbstractByte → Bool
  | [], [] => true
  | true :: pm, _ :: bs => nonPadBytesInitialized pm bs
  | false :: pm, .init _ _ :: bs => nonPadBytesInitialized pm bs
  | _, _ => false

/-- True iff `b1` and `b2` have the same length as `padMask` and agree at every
non-padding byte (`padMask[i] = false`). Padding bytes may differ arbitrarily
(e.g. `.uninit` vs `0xAA`). -/
def sameAtNonPad : List Bool → List AbstractByte → List AbstractByte → Bool
  | [], [], [] => true
  | true :: pm, _ :: xs, _ :: ys => sameAtNonPad pm xs ys
  | false :: pm, x :: xs, y :: ys => abstractByteBeq x y && sameAtNonPad pm xs ys
  | _, _, _ => false

theorem sameAtNonPad_refl : ∀ (pm : List Bool) (bs : List AbstractByte),
    pm.length = bs.length → sameAtNonPad pm bs bs = true
  | [], [], _ => rfl
  | true :: pm, _ :: bs, h =>
    sameAtNonPad_refl pm bs (Nat.succ.inj h)
  | false :: pm, b :: bs, h => by
    simp only [sameAtNonPad, abstractByteBeq_refl, Bool.true_and]
    exact sameAtNonPad_refl pm bs (Nat.succ.inj h)

/-- True iff every byte in `bs` is initialized with NO provenance (`none`). -/
def sliceAllInitNoProv : List AbstractByte → Bool
  | [] => true
  | .init _ none :: rest => sliceAllInitNoProv rest
  | _ => false

/-- True iff every byte in `bs` is initialized with the EXACT provenance pair
`some (allocId, tag)`. -/
def allHaveExactProv (bs : List AbstractByte) (allocId tag : Nat) : Bool :=
  bs.foldr
    (fun b acc =>
      match b with
      | .init _ (some (a, t)) => Nat.beq a allocId && Nat.beq t tag && acc
      | _ => false)
    true

/-- True iff no padding byte in `bs` carries provenance (every padding byte is
either `.uninit` or `.init _ none`). -/
def padBytesProvFree : List Bool → List AbstractByte → Bool
  | [], [] => true
  | true :: pm, .uninit :: bs => padBytesProvFree pm bs
  | true :: pm, .init _ none :: bs => padBytesProvFree pm bs
  | true :: _, .init _ (some _) :: _ => false
  | false :: pm, _ :: bs => padBytesProvFree pm bs
  | _, _ => false

/-- Extract all non-padding bytes according to `padMask`. -/
def nonPadBytesOfMask : List Bool → List AbstractByte → List AbstractByte
  | [], _ => []
  | _, [] => []
  | true :: pm, _ :: bs => nonPadBytesOfMask pm bs
  | false :: pm, b :: bs => b :: nonPadBytesOfMask pm bs

/-- Check whether `prov` occurs among the bytes of `allowed`. -/
def provInBytes (p : Nat × Nat) (allowed : List AbstractByte) : Bool :=
  allowed.foldr
    (fun b acc =>
      match b with
      | .init _ (some q) => (Nat.beq p.1 q.1 && Nat.beq p.2 q.2) || acc
      | _ => acc)
    false

/-- Check that every provenance pair carried by `written` already occurs in
`allowed` (prevents out-of-thin-air provenance forgery during raw writes). -/
def bytesProvSubset (written allowed : List AbstractByte) : Bool :=
  written.foldr
    (fun b acc =>
      match b with
      | .init _ (some p) => provInBytes p allowed && acc
      | _ => acc)
    true

/-- Check that a single primitive field value `v` and its byte slice `slice`
satisfy strict bidirectional `(allocId, tag)` provenance enforcement and agree
with unmodified `Trusted.Rustc.V2026_06_01.MirSemantics.encodeValueToBytes`:
- Scalar/bool/char fields: EVERY byte must be `.init _ none` (rejects surplus
  provenance forgery!) and match `encodeValueToBytes`.
- Thin raw pointer (`.rawPtr _ pointee`): `v` must be `.ptr p 8`, EVERY byte of
  the 8-byte slice must carry `some (p.allocId, p.tag)` (rejects provenance
  stripping AND partial stripping AND wrong `allocId` OR wrong `tag`!), and
  match `encodeValueToBytes`.
- References (`.ref _ _`): rejected fail-closed! -/
def primFieldValAndBytesMatch (layouts : LayoutTable) (ty : Ty)
    (v : Value) (slice : List AbstractByte) : Bool :=
  match ty.kind with
  | .ref _ _ => false
  | .uint _ | .int _ | .bool | .char =>
    sliceAllInitNoProv slice &&
    match encodeValueToBytes defaultCodecFuel layouts ty v with
    | some expected => abstractByteListBeq slice expected
    | none => false
  | .rawPtr _ pointee =>
    let isWide :=
      match pointee with
      | .slice _ | .str | .dynamic _ => true
      | _ => false
    if isWide then false
    else
      match v with
      | .ptr p 8 =>
        Nat.beq slice.length 8 &&
        allHaveExactProv slice p.allocId p.tag &&
        match encodeValueToBytes defaultCodecFuel layouts ty v with
        | some expected => abstractByteListBeq slice expected
        | none => false
      | _ => false
  | .tuple [] =>
    match v, slice with
    | .unit, [] => true
    | _, _ => false
  | _ => false

/-- Check whether byte index `idx` is covered by any audited field in `fields`. -/
def byteIdxCoveredByFields (layouts : LayoutTable) (idx : Nat) :
    List AuditedFieldSpec → Bool
  | [] => false
  | f :: fs =>
    let sz := (rigidTyByteSize layouts f.fieldTy).getD 0
    (Nat.ble f.offset idx && Nat.blt idx (f.offset + sz)) ||
      byteIdxCoveredByFields layouts idx fs

/-- Check that all non-field (padding) bytes carry no provenance (and, when
`requirePadUninit = true`, are strictly `.uninit`). -/
def checkPaddingBytes (requirePadUninit : Bool) (layouts : LayoutTable)
    (fields : List AuditedFieldSpec) (idx : Nat) : List AbstractByte → Bool
  | [] => true
  | b :: rest =>
    let ok :=
      if byteIdxCoveredByFields layouts idx fields then true
      else
        match b with
        | .uninit => true
        | .init _ none => !requirePadUninit
        | .init _ (some _) => false
    ok && checkPaddingBytes requirePadUninit layouts fields (idx + 1) rest

/-- Strict bidirectional `(allocId, tag)` provenance + byte-encoding consistency
predicate relating a `V2026_06_01.MirSemantics.Value` and its byte buffer `bs`
under a `SpatialTargetSpec`. Rejects BOTH provenance stripping AND surplus
provenance forgery AND `.ref` targets! -/
def valAndBytesMatchTargetSpec (requirePadUninit : Bool) (layouts : LayoutTable)
    (spec : SpatialTargetSpec) (v : Value) (bs : List AbstractByte) : Bool :=
  if spec.isRefTarget then false
  else
    match spec with
    | .mirTy ty => primFieldValAndBytesMatch layouts ty v bs
    | .reprCAdt _ _ sz _ fields =>
      if !Nat.beq bs.length sz then false
      else
        match v with
        | .aggregate 0 fvals =>
          let rec goFields : List AuditedFieldSpec → List Value → Bool
            | [], [] => true
            | f :: fs, fv :: fvs =>
              match rigidTyByteSize layouts f.fieldTy with
              | none => false
              | some fsz =>
                Nat.ble (f.offset + fsz) bs.length &&
                primFieldValAndBytesMatch layouts f.fieldTy fv
                  ((bs.drop f.offset).take fsz) &&
                goFields fs fvs
            | _, _ => false
          goFields fields fvals && checkPaddingBytes requirePadUninit layouts fields 0 bs
        | _ => false

theorem valAndBytesMatchTargetSpec_false_of_true (layouts : LayoutTable)
    (spec : SpatialTargetSpec) (v : Value) (bs : List AbstractByte)
    (h : valAndBytesMatchTargetSpec true layouts spec v bs = true) :
    valAndBytesMatchTargetSpec false layouts spec v bs = true := by
  have hPad : ∀ fields idx (ys : List AbstractByte),
      checkPaddingBytes true layouts fields idx ys = true →
      checkPaddingBytes false layouts fields idx ys = true := by
    intro fields idx ys
    induction ys generalizing idx with
    | nil => intro _; rfl
    | cons b rest ih =>
      intro hC
      simp only [checkPaddingBytes, Bool.and_eq_true] at hC ⊢
      refine ⟨?_, ih (idx + 1) hC.2⟩
      cases hCov : byteIdxCoveredByFields layouts idx fields with
      | true => rfl
      | false =>
        rw [hCov] at hC
        simp only [Bool.false_eq_true, ↓reduceIte] at hC ⊢
        cases b with
        | uninit => rfl
        | init _ p =>
          cases p with
          | none => nomatch hC.1
          | some _ => exact hC.1
  unfold valAndBytesMatchTargetSpec at h ⊢
  cases hRef : spec.isRefTarget with
  | true => rw [hRef] at h; nomatch h
  | false =>
    rw [hRef] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases spec with
    | mirTy ty => exact h
    | reprCAdt id ty sz al fields =>
      dsimp only at h ⊢
      cases hLen : Nat.beq bs.length sz with
      | false => rw [hLen] at h; nomatch h
      | true =>
        rw [hLen] at h
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases v with
        | aggregate varIdx fvals =>
          cases varIdx with
          | succ _ => nomatch h
          | zero =>
            simp only [Bool.and_eq_true] at h ⊢
            exact ⟨h.1, hPad fields 0 bs h.2⟩
        | _ => nomatch h

/-- Expected padding mask for `spec` against `layouts` (`true` at padding byte
indices not covered by any field, `false` at value-carrying field bytes). -/
def expectedPadMaskForSpec (layouts : LayoutTable) : SpatialTargetSpec → Option (List Bool)
  | .mirTy ty =>
    match layouts.lookup ty.layoutIdx with
    | none => none
    | some tl => some (List.replicate tl.size.bytes false)
  | .reprCAdt _ ty sz _ fields =>
    match layouts.lookup ty.layoutIdx with
    | none => none
    | some tl =>
      if Nat.beq tl.size.bytes sz then
        some ((List.range sz).map (fun i => !byteIdxCoveredByFields layouts i fields))
      else none

/-- Runtime authentication checking that a codec's `V2026MemLayout` (`size` and
`alignBytes`) and `padMask` agree with the `CapturedMir`'s `LayoutTable` entry
for `spec`. Prevents forged under-alignment or forged all-padding masks from
passing `freezePaddedToMem`. -/
def codecLayoutAndMaskMatchSpec (layouts : LayoutTable) (spec : SpatialTargetSpec)
    (layout : V2026MemLayout) (padMask : List Bool) : Bool :=
  match layouts.lookup spec.toMirTy.layoutIdx, expectedPadMaskForSpec layouts spec with
  | some tl, some expMask =>
    Nat.beq layout.size tl.size.bytes &&
    Nat.beq layout.alignBytes tl.align.bytes &&
    Nat.blt 0 layout.alignBytes &&
    (padMask == expMask) &&
    (match spec with
     | .mirTy _ => true
     | .reprCAdt _ _ sz al _ => Nat.beq layout.size sz && Nat.beq layout.alignBytes al)
  | _, _ => false

/-- Bounded structural equality on `V2026_06_01.MirSemantics.Value` used by
`freezePaddedToMem` to verify `st.mirLocals[reg] = .immediate slotVal` matches
the loan cell's encoded MIR value (preventing symbolic/MIR local desync). -/
def mirValBeq : Nat → Value → Value → Bool
  | 0, _, _ => false
  | _ + 1, .unit, .unit => true
  | _ + 1, .uninit, .uninit => true
  | _ + 1, .scalar a, .scalar b => Nat.beq a.bits b.bits && Nat.beq a.sizeBytes b.sizeBytes
  | _ + 1, .ptr p1 sz1, .ptr p2 sz2 =>
    Nat.beq p1.allocId p2.allocId && Nat.beq p1.offsetBytes p2.offsetBytes && Nat.beq sz1 sz2
  | fuel + 1, .aggregate v1 fs1, .aggregate v2 fs2 =>
    Nat.beq v1 v2 &&
    let rec go : List Value → List Value → Bool
      | [], [] => true
      | x :: xs, y :: ys => mirValBeq fuel x y && go xs ys
      | _, _ => false
    go fs1 fs2
  | _, _, _ => false

/-- Soundness of `codecLayoutAndMaskMatchSpec`: a `true` verdict implies the
codec's `size`, `alignBytes`, and `padMask` equal the `LayoutTable`'s exact
`TypeLayout` size, alignment, and derived padding mask. -/
theorem codecLayoutAndMaskMatchSpec_sound {layouts : LayoutTable} {spec : SpatialTargetSpec}
    {layout : V2026MemLayout} {padMask : List Bool}
    (h : codecLayoutAndMaskMatchSpec layouts spec layout padMask = true) :
    ∃ tl : TypeLayout,
      layouts.lookup spec.toMirTy.layoutIdx = some tl ∧
      layout.size = tl.size.bytes ∧
      layout.alignBytes = tl.align.bytes ∧
      0 < layout.alignBytes ∧
      expectedPadMaskForSpec layouts spec = some padMask := by
  unfold codecLayoutAndMaskMatchSpec at h
  cases hLk : layouts.lookup spec.toMirTy.layoutIdx with
  | none => rw [hLk] at h; cases h
  | some tl =>
    cases hMask : expectedPadMaskForSpec layouts spec with
    | none => rw [hLk, hMask] at h; cases h
    | some expMask =>
      rw [hLk, hMask] at h
      simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, beq_iff_eq] at h
      refine ⟨tl, rfl, h.1.1.1.1, h.1.1.1.2, h.1.1.2, ?_⟩
      rw [h.1.2]

/-- Soundness of `mirValBeq`: a `true` verdict forces propositional equality of
the two `V2026_06_01.MirSemantics.Value`s. -/
theorem mirValBeq_sound : ∀ {fuel : Nat} {v1 v2 : Value},
    mirValBeq fuel v1 v2 = true → v1 = v2
  | 0, _, _, h => by unfold mirValBeq at h; cases h
  | _ + 1, .unit, .unit, _ => rfl
  | _ + 1, .uninit, .uninit, _ => rfl
  | _ + 1, .scalar a, .scalar b, h => by
    unfold mirValBeq at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    cases a; cases b; dsimp only at h; rw [h.1, h.2]
  | _ + 1, .ptr p1 sz1, .ptr p2 sz2, h => by
    unfold mirValBeq at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    cases p1; cases p2; dsimp only at h; rw [h.1.1, h.1.2, h.2]
  | fuel + 1, .aggregate v1 fs1, .aggregate v2 fs2, h => by
    unfold mirValBeq at h
    rw [Bool.and_eq_true] at h
    have hV : v1 = v2 := Nat.beq_eq.mp h.1
    have hGo : ∀ (xs ys : List Value), mirValBeq.go fuel xs ys = true → xs = ys := by
      intro xs
      induction xs with
      | nil =>
        intro ys hg; cases ys with | nil => rfl | cons _ _ => unfold mirValBeq.go at hg; cases hg
      | cons x xs ih =>
        intro ys hg; cases ys with
        | nil => unfold mirValBeq.go at hg; cases hg
        | cons y ys =>
          unfold mirValBeq.go at hg; rw [Bool.and_eq_true] at hg
          rw [mirValBeq_sound hg.1, ih ys hg.2]
    rw [hV, hGo fs1 fs2 h.2]
  | _ + 1, .unit, .uninit, h | _ + 1, .unit, .scalar _, h | _ + 1, .unit, .ptr _ _, h
  | _ + 1, .unit, .aggregate _ _, h | _ + 1, .uninit, .unit, h | _ + 1, .uninit, .scalar _, h
  | _ + 1, .uninit, .ptr _ _, h | _ + 1, .uninit, .aggregate _ _, h
  | _ + 1, .scalar _, .unit, h | _ + 1, .scalar _, .uninit, h | _ + 1, .scalar _, .ptr _ _, h
  | _ + 1, .scalar _, .aggregate _ _, h | _ + 1, .ptr _ _, .unit, h
  | _ + 1, .ptr _ _, .uninit, h | _ + 1, .ptr _ _, .scalar _, h
  | _ + 1, .ptr _ _, .aggregate _ _, h | _ + 1, .aggregate _ _, .unit, h
  | _ + 1, .aggregate _ _, .uninit, h | _ + 1, .aggregate _ _, .scalar _, h
  | _ + 1, .aggregate _ _, .ptr _ _, h => by cases h

/-- Typed spatial memory codec connecting a domain value `α` to:
1. `V2026_06_01.MirSemantics.AbstractByte` memory bytes (allowing `.uninit` padding),
2. `V2026_06_01.MirSemantics.Value` (trusted MIR value), and
3. `PureLift.StdVal` (symbolic loan-graph value). -/
structure TypedSpatialMemCodec (α : Type) where
  codecId : Nat
  targetTy : SpatialTargetSpec
  layout : V2026MemLayout
  padMask : List Bool
  encodeValToMem : α → List AbstractByte
  decodeValFromMem : List AbstractByte → Option α
  provCheck : List AbstractByte → Bool
  encodeToMirVal : α → Value
  decodeFromMirVal : Value → Option α
  encodeToSymVal : α → StdVal
  decodeFromSymVal : StdVal → Option α

/-- Constructive lawfulness obligations for a `TypedSpatialMemCodec α` under a
captured `LayoutTable`. -/
structure LawfulTypedSpatialMemCodec {α : Type} (layouts : LayoutTable)
    (c : TypedSpatialMemCodec α) : Prop where
  notRef : c.targetTy.isRefTarget = false
  sizePos : 0 < c.layout.size
  alignPos : 0 < c.layout.alignBytes
  padMaskLen : c.padMask.length = c.layout.size
  encodeProps : ∀ x : α,
    (c.encodeValToMem x).length = c.layout.size ∧
    nonPadBytesInitialized c.padMask (c.encodeValToMem x) = true ∧
    c.provCheck (c.encodeValToMem x) = true ∧
    valAndBytesMatchTargetSpec true layouts c.targetTy
      (c.encodeToMirVal x) (c.encodeValToMem x) = true ∧
    decodeValueFromBytes defaultCodecFuel layouts c.targetTy.toMirTy
      (c.encodeValToMem x) = some (c.encodeToMirVal x) ∧
    c.decodeValFromMem (c.encodeValToMem x) = some x ∧
    c.decodeFromMirVal (c.encodeToMirVal x) = some x ∧
    c.decodeFromSymVal (c.encodeToSymVal x) = some x
  decodeRespectsNonPad : ∀ b1 b2 : List AbstractByte,
    b1.length = c.layout.size →
    b2.length = c.layout.size →
    sameAtNonPad c.padMask b1 b2 = true →
    c.decodeValFromMem b1 = c.decodeValFromMem b2
  decodeImpliesMir : ∀ (bs : List AbstractByte) (x : α),
    bs.length = c.layout.size →
    nonPadBytesInitialized c.padMask bs = true →
    c.provCheck bs = true →
    c.decodeValFromMem bs = some x →
    valAndBytesMatchTargetSpec false layouts c.targetTy (c.encodeToMirVal x) bs = true ∧
    decodeValueFromBytes defaultCodecFuel layouts c.targetTy.toMirTy bs =
      some (c.encodeToMirVal x)

/-! ### `PaddedSymMemState` Lifecycle Operations -/

/-- Storage state of a MIR local in the hybrid pure/padded-spatial state. -/
inductive PaddedMirLocalSlot where
  | dead
  | uninit
  | immediate (val : Value)
  | indirect (place : V2026MemPlace)

/-- Project a `PaddedMirLocalSlot` to an unmodified `V2026_06_01.MirSemantics.LocalSlot`
(evaluating an indirect promoted slot by loading its typed value from `mem` via
`decodeValueFromBytes`). -/
def projectPaddedMirLocalSlot (layouts : LayoutTable) (mem : V2026ByteMem)
    (ty : Ty) (len alignBytes : Nat) : PaddedMirLocalSlot → Option LocalSlot
  | .dead => some .dead
  | .uninit => some .uninit
  | .immediate v => some (.init v)
  | .indirect place =>
    match loadV2026Typed layouts ty mem place len alignBytes with
    | some v => some (.init v)
    | none => none

/-- Active spatially pinned memory block backed by `V2026ByteMem`. -/
structure PaddedSpatialBlock where
  blockId : BlockId
  originLoan : LoanId
  ownerLocal : LocalId
  perm : SpatialPerm
  provenanceTag : Nat
  activeSubSplits : Nat
  layout : V2026MemLayout
  padMask : List Bool
  targetTy : SpatialTargetSpec
  place : V2026MemPlace
  codecId : Nat
  /-- Reabsorption decoder bundled at freeze time (mirrors `LoanPhase.spatialPinned`
  codec binding so forged codecs at reabsorb time cannot subvert decoding). -/
  reabsorbBytes : List AbstractByte → Option (StdVal × Value)

/-- Tracked promoted local whose canonical storage lives in `V2026ByteMem`. -/
structure PromotedLocalEntry where
  localId : LocalId
  targetTy : SpatialTargetSpec
  place : V2026MemPlace
  layout : V2026MemLayout
  padMask : List Bool
  codecId : Nat
  encodeSymToBytes : StdVal → Option (List AbstractByte × Value)

/-- Hybrid pure symbolic (`SymState StdVal`) + `V2026ByteMem` (`AbstractByte`)
state supporting padded and provenance-carrying spatial pinning. -/
structure PaddedSymMemState where
  sym : SymState StdVal
  mirLocalTypes : List SpatialTargetSpec
  mirLocals : List PaddedMirLocalSlot
  mem : V2026ByteMem
  memBlocks : List PaddedSpatialBlock
  promotedLocals : List PromotedLocalEntry

/-- Safe indexed list lookup. -/
def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

/-- Safe indexed list update. -/
def listSet? {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v =>
    match listSet? xs n v with
    | some xs' => some (x :: xs')
    | none => none

/-- Witness `SpatialCodec StdVal` stored inside `LoanPhase.spatialPinned` to bind
`codecId` and block pure reads/writes/ends while the loan is pinned in memory. -/
def paddedLoanWitnessCodec (codecId : Nat) : SpatialCodec StdVal where
  codecId := codecId
  encode v := [.init v]
  decode cells :=
    match cells with
    | [.init v] => some v
    | _ => none
  decode_encode _ := rfl

/-- Extract the direct local owner from a `BackTarget StdVal` (`[.direct (.localReg reg) []]`). -/
def loanDirectLocal? (t : BackTarget StdVal) : Option LocalId :=
  match t.steps with
  | [.direct (.localReg reg) []] => some reg
  | _ => none

def countPaddedBlocksForLoan (lid : LoanId) (blks : List PaddedSpatialBlock) : Nat :=
  blks.foldr (fun b acc => if Nat.beq b.originLoan lid then acc + 1 else acc) 0

def hasPaddedBlockId (bid : BlockId) (blks : List PaddedSpatialBlock) : Bool :=
  blks.foldr (fun b acc => Nat.beq b.blockId bid || acc) false

def anyBlockTargetsLocal (reg : LocalId) (blks : List PaddedSpatialBlock) : Bool :=
  blks.foldr (fun b acc => Nat.beq b.ownerLocal reg || acc) false

def anyBlockUsesAlloc (aid : AllocId) (blks : List PaddedSpatialBlock) : Bool :=
  blks.foldr (fun b acc => Nat.beq b.place.allocId aid || acc) false

def hasPromotedLocal (reg : LocalId) (ps : List PromotedLocalEntry) : Bool :=
  ps.foldr (fun p acc => Nat.beq p.localId reg || acc) false

def otherPromotedUsesAlloc (reg : LocalId) (aid : AllocId) (ps : List PromotedLocalEntry) : Bool :=
  ps.foldr (fun p acc => (!Nat.beq p.localId reg && Nat.beq p.place.allocId aid) || acc) false

def otherIndirectLocalUsesAlloc (reg : LocalId) (aid : AllocId)
    (slots : List PaddedMirLocalSlot) : Bool :=
  let rec go (idx : Nat) : List PaddedMirLocalSlot → Bool
    | [] => false
    | .indirect p :: rest =>
      (!Nat.beq idx reg && Nat.beq p.allocId aid) || go (idx + 1) rest
    | _ :: rest => go (idx + 1) rest
  go 0 slots

def anyIndirectLocalUsesAlloc (aid : AllocId) (slots : List PaddedMirLocalSlot) : Bool :=
  slots.foldr
    (fun s acc =>
      match s with
      | .indirect p => Nat.beq p.allocId aid || acc
      | _ => acc)
    false

def anyPromotedUsesAlloc (aid : AllocId) (ps : List PromotedLocalEntry) : Bool :=
  ps.foldr (fun p acc => Nat.beq p.place.allocId aid || acc) false

def anyAllocBytesRefAlloc (aid : AllocId) (allocs : List V2026ByteAlloc) : Bool :=
  allocs.foldr
    (fun a acc =>
      (a.live &&
       a.bytes.foldr
         (fun b bacc =>
           match b with
           | .init _ (some (pAid, _)) => Nat.beq pAid aid || bacc
           | _ => bacc)
         false) || acc)
    false

def otherLiveAllocRefsAlloc (aid : AllocId) (allocs : List V2026ByteAlloc) : Bool :=
  allocs.foldr
    (fun a acc =>
      (a.live && !Nat.beq a.allocId aid &&
       a.bytes.foldr
         (fun b bacc =>
           match b with
           | .init _ (some (pAid, _)) => Nat.beq pAid aid || bacc
           | _ => bacc)
         false) || acc)
    false

/-- Check that `aid` is completely fresh (not present in `mem.allocs`, not
referenced by any live allocation's provenance, not held by any promoted local,
indirect slot, or pinned block). Rejects stale `nextAllocId` / aliased `AllocId`! -/
def freshPromotedAllocId (aid : AllocId) (st : PaddedSymMemState) : Bool :=
  (match findV2026Alloc aid st.mem.allocs with | none => true | some _ => false) &&
  !anyAllocBytesRefAlloc aid st.mem.allocs &&
  !anyBlockUsesAlloc aid st.memBlocks &&
  !anyPromotedUsesAlloc aid st.promotedLocals &&
  !anyIndirectLocalUsesAlloc aid st.mirLocals

def slotMatchesIndirection (slots : List PaddedMirLocalSlot) (reg : LocalId)
    (place : V2026MemPlace) : Bool :=
  match listGet? slots reg with
  | some (.indirect p) => Nat.beq p.allocId place.allocId && Nat.beq p.offset place.offset
  | _ => false

def findPaddedSpatialBlock (blks : List PaddedSpatialBlock) (bid : BlockId) :
    Option (PaddedSpatialBlock × List PaddedSpatialBlock) :=
  match
    blks.foldr
      (fun b (acc : Bool × Option PaddedSpatialBlock × List PaddedSpatialBlock) =>
        match acc with
        | (dup, found, rest) =>
          if Nat.beq b.blockId bid then
            match found with
            | some _ => (true, found, rest)
            | none => (dup, some b, rest)
          else
            (dup, found, b :: rest))
      (false, none, [])
  with
  | (false, some blk, rest) => some (blk, rest)
  | _ => none

def removePromotedLocal (reg : LocalId) (ps : List PromotedLocalEntry) :
    List PromotedLocalEntry :=
  ps.filter (fun p => !Nat.beq p.localId reg)

/-- Freeze an active mutable loan `lid` on a direct local into `V2026ByteMem`
using a lawful `TypedSpatialMemCodec α`, preserving `.uninit` padding bytes
and blocking pure symbolic access until `reabsorbPaddedFromMem`. -/
def freezePaddedToMem {α : Type} (ctx : BodySpatialCtx) (lid : LoanId)
    (c : TypedSpatialMemCodec α) (_hLaw : LawfulTypedSpatialMemCodec ctx.body.layouts c)
    (st : PaddedSymMemState) : EvalOutcome PaddedSymMemState :=
  if !specsMatchBodyCtx ctx st.mirLocalTypes ||
     !Nat.beq st.mirLocalTypes.length st.mirLocals.length ||
     !Nat.beq st.sym.locals.length st.mirLocals.length ||
     c.targetTy.isRefTarget ||
     !hasUniqueLoanId lid st.sym.loans then
    .fail
  else
    match findLoan lid st.sym.loans with
    | none => .fail
    | some e =>
      if !e.phase.isActiveMut || !isUnborrowed e.cell.perm ||
         !noActiveChildLoanEdgesIn stdValAlg lid st.sym.loans ||
         !noActiveChildRegionEdges lid st.sym.regionGroups ||
         !Nat.beq (countPaddedBlocksForLoan lid st.memBlocks) 0 ||
         hasPaddedBlockId st.sym.nextSpatialTag st.memBlocks ||
         !Nat.beq (countBlocksForLoan lid st.sym.spatial) 0 ||
         hasSpatialBlockId st.sym.nextSpatialTag st.sym.spatial then
        .fail
      else
        match loanDirectLocal? e.target with
        | none => .fail
        | some reg =>
          match listGet? st.mirLocalTypes reg, listGet? st.sym.locals reg with
          | some localSpec, some ownerCell =>
            if !spatialTargetSpecBeq localSpec c.targetTy then .fail
            else
              match ownerCell.perm with
              | .mutLocked lockId =>
                if !Nat.beq lockId lid then .fail
                else
                  match c.decodeFromSymVal e.cell.val with
                  | none => .fail
                  | some x =>
                    let rawBytes := c.encodeValToMem x
                    let mirVal := c.encodeToMirVal x
                    if !stdValEq (c.encodeToSymVal x) e.cell.val ||
                       !codecLayoutAndMaskMatchSpec ctx.body.layouts c.targetTy c.layout c.padMask ||
                       !Nat.beq rawBytes.length c.layout.size ||
                       !Nat.beq c.padMask.length c.layout.size ||
                       !nonPadBytesInitialized c.padMask rawBytes ||
                       !c.provCheck rawBytes ||
                       !valAndBytesMatchTargetSpec true ctx.body.layouts c.targetTy mirVal rawBytes then
                      .fail
                    else
                      match listGet? st.mirLocals reg with
                      | some (.immediate slotVal) =>
                        if !mirValBeq 8 slotVal mirVal ||
                           hasPromotedLocal reg st.promotedLocals ||
                           !freshPromotedAllocId st.mem.nextAllocId st then
                          .fail
                        else
                          let (place, memAlloc) :=
                            allocV2026Stack st.mem c.layout.size c.layout.alignBytes
                          match writeV2026Bytes memAlloc place c.layout.alignBytes rawBytes with
                          | none => .fail
                          | some memInit =>
                            match listSet? st.mirLocals reg (.indirect place) with
                            | none => .fail
                            | some mirLocals' =>
                              let bid := st.sym.nextSpatialTag
                              let witness := paddedLoanWitnessCodec c.codecId
                              let loans' := updateLoan lid
                                (fun le => ⟨le.id, .spatialPinned bid witness, le.cell, le.target⟩)
                                st.sym.loans
                              let blk : PaddedSpatialBlock :=
                                { blockId := bid
                                  originLoan := lid
                                  ownerLocal := reg
                                  perm := .readWrite
                                  provenanceTag := bid
                                  activeSubSplits := 0
                                  layout := c.layout
                                  padMask := c.padMask
                                  targetTy := c.targetTy
                                  place := place
                                  codecId := c.codecId
                                  reabsorbBytes := fun bs =>
                                    if !Nat.beq bs.length c.layout.size ||
                                       !nonPadBytesInitialized c.padMask bs ||
                                       !c.provCheck bs then
                                      none
                                    else
                                      match c.decodeValFromMem bs with
                                      | none => none
                                      | some x' =>
                                        let vSym' := c.encodeToSymVal x'
                                        let vMir' := c.encodeToMirVal x'
                                        if valAndBytesMatchTargetSpec false ctx.body.layouts
                                            c.targetTy vMir' bs then
                                          some (vSym', vMir')
                                        else
                                          none }
                              let prom : PromotedLocalEntry :=
                                { localId := reg
                                  targetTy := c.targetTy
                                  place := place
                                  layout := c.layout
                                  padMask := c.padMask
                                  codecId := c.codecId
                                  encodeSymToBytes := fun sv =>
                                    match c.decodeFromSymVal sv with
                                    | none => none
                                    | some x' =>
                                      if stdValEq (c.encodeToSymVal x') sv then
                                        some (c.encodeValToMem x', c.encodeToMirVal x')
                                      else none }
                              .ok
                                { sym := { st.sym with
                                    loans := loans'
                                    nextSpatialTag := bid + 1 }
                                  mirLocalTypes := st.mirLocalTypes
                                  mirLocals := mirLocals'
                                  mem := memInit
                                  memBlocks := st.memBlocks ++ [blk]
                                  promotedLocals := st.promotedLocals ++ [prom] }
                      | _ => .fail
              | _ => .fail
          | _, _ => .fail

/-- Mutate a sub-range `[relOff, relOff + newBytes.length)` of pinned spatial
block `bid` inside `V2026ByteMem`, checking provenance tag, `.readWrite`
permission, alignment, exclusivity, and no out-of-thin-air provenance forgery. -/
def mutatePaddedInMem (ctx : BodySpatialCtx) (bid : BlockId) (tag : Nat)
    (relOff reqAlign : Nat) (newBytes : List AbstractByte)
    (st : PaddedSymMemState) : EvalOutcome PaddedSymMemState :=
  if !specsMatchBodyCtx ctx st.mirLocalTypes ||
     !Nat.beq st.mirLocalTypes.length st.mirLocals.length ||
     newBytes.isEmpty then
    .fail
  else
    match findPaddedSpatialBlock st.memBlocks bid with
    | none => .fail
    | some (blk, _) =>
      if !hasUniqueLoanId blk.originLoan st.sym.loans then .fail
      else
        match findLoan blk.originLoan st.sym.loans with
        | none => .fail
        | some e =>
          match e.phase with
          | .spatialPinned pinBid witness =>
            let writable : Bool :=
              match blk.perm with
              | .readWrite => true
              | .readOnly => false
            if !Nat.beq pinBid bid ||
               !Nat.beq blk.provenanceTag tag ||
               !Nat.beq blk.provenanceTag bid ||
               !Nat.beq witness.codecId blk.codecId ||
               !writable ||
               !Nat.beq blk.activeSubSplits 0 ||
               !Nat.ble (relOff + newBytes.length) blk.layout.size ||
               !Nat.ble reqAlign blk.layout.alignBytes ||
               reqAlign == 0 ||
               !Nat.beq ((blk.place.offset + relOff) % reqAlign) 0 ||
               !slotMatchesIndirection st.mirLocals blk.ownerLocal blk.place ||
               otherPromotedUsesAlloc blk.ownerLocal blk.place.allocId st.promotedLocals ||
               otherIndirectLocalUsesAlloc blk.ownerLocal blk.place.allocId st.mirLocals then
              .fail
            else
              match readV2026Bytes st.mem blk.place blk.layout.size blk.layout.alignBytes with
              | none => .fail
              | some curBytes =>
                if !bytesProvSubset newBytes (nonPadBytesOfMask blk.padMask curBytes) then
                  .fail
                else
                  let writePlace : V2026MemPlace :=
                    ⟨blk.place.allocId, blk.place.offset + relOff⟩
                  match writeV2026Bytes st.mem writePlace reqAlign newBytes with
                  | none => .fail
                  | some mem' => .ok { st with mem := mem' }
          | _ => .fail

/-- Reabsorb a spatially pinned loan `lid` from `V2026ByteMem` back into the pure
loan graph, verifying non-padding initialization, bidirectional `(allocId, tag)`
provenance enforcement, direct TCB `decodeValueFromBytes` agreement, and
handle-safety (`replaceableVal`). -/
def reabsorbPaddedFromMem (ctx : BodySpatialCtx) (lid : LoanId)
    (st : PaddedSymMemState) : EvalOutcome PaddedSymMemState :=
  if !specsMatchBodyCtx ctx st.mirLocalTypes ||
     !Nat.beq st.mirLocalTypes.length st.mirLocals.length ||
     !hasUniqueLoanId lid st.sym.loans then
    .fail
  else
    match findLoan lid st.sym.loans with
    | none => .fail
    | some e =>
      match e.phase with
      | .spatialPinned bid witness =>
        match loanDirectLocal? e.target, findPaddedSpatialBlock st.memBlocks bid with
        | some reg, some (blk, restBlks) =>
          let writable : Bool :=
            match blk.perm with
            | .readWrite => true
            | .readOnly => false
          if !Nat.beq blk.originLoan lid ||
             !Nat.beq blk.ownerLocal reg ||
             !Nat.beq blk.provenanceTag bid ||
             !Nat.beq witness.codecId blk.codecId ||
             !writable ||
             !Nat.beq blk.activeSubSplits 0 ||
             !Nat.beq (countPaddedBlocksForLoan lid restBlks) 0 ||
             !slotMatchesIndirection st.mirLocals reg blk.place ||
             otherPromotedUsesAlloc reg blk.place.allocId st.promotedLocals ||
             otherIndirectLocalUsesAlloc reg blk.place.allocId st.mirLocals then
            .fail
          else
            match listGet? st.mirLocalTypes reg with
            | none => .fail
            | some localSpec =>
              if !spatialTargetSpecBeq localSpec blk.targetTy then .fail
              else
                match readV2026Bytes st.mem blk.place blk.layout.size blk.layout.alignBytes with
                | none => .fail
                | some rawBytes =>
                  if !nonPadBytesInitialized blk.padMask rawBytes then .fail
                  else
                    match blk.reabsorbBytes rawBytes with
                    | none => .fail
                    | some (vSym', vMir') =>
                      if !valAndBytesMatchTargetSpec false ctx.body.layouts blk.targetTy vMir' rawBytes ||
                         !replaceableVal stdValAlg st.sym.loans e.cell.val vSym' then
                        .fail
                      else
                        match decodeValueFromBytes defaultCodecFuel ctx.body.layouts
                            blk.targetTy.toMirTy rawBytes with
                        | none => .fail
                        | some _ =>
                          let loans' := updateLoan lid
                            (fun le => ⟨le.id, .activeMut, ⟨vSym', le.cell.perm⟩, le.target⟩)
                            st.sym.loans
                          .ok
                            { st with
                              sym := { st.sym with loans := loans' }
                              memBlocks := restBlks }
        | _, _ => .fail
      | _ => .fail

/-- Check that every promoted local (not currently pinned) has memory bytes
agreeing with its symbolic value at all non-padding positions (`sameAtNonPad`). -/
def syncPromotedLocalsToMem (ctx : BodySpatialCtx) (st : PaddedSymMemState) :
    EvalOutcome PaddedSymMemState :=
  if !specsMatchBodyCtx ctx st.mirLocalTypes ||
     !Nat.beq st.mirLocalTypes.length st.mirLocals.length ||
     !Nat.beq st.sym.locals.length st.mirLocals.length then
    .fail
  else
    let rec go (memCur : V2026ByteMem) : List PromotedLocalEntry → EvalOutcome V2026ByteMem
      | [] => .ok memCur
      | p :: rest =>
        if anyBlockTargetsLocal p.localId st.memBlocks then
          go memCur rest
        else if !slotMatchesIndirection st.mirLocals p.localId p.place then
          .fail
        else
          match getLocal stdValAlg p.localId st.sym with
          | none => .fail
          | some sv =>
            match p.encodeSymToBytes sv with
            | none => .fail
            | some (encBytes, mirVal) =>
              match readV2026Bytes memCur p.place p.layout.size p.layout.alignBytes with
              | none => .fail
              | some curBytes =>
                if nonPadBytesInitialized p.padMask curBytes &&
                   sameAtNonPad p.padMask encBytes curBytes &&
                   valAndBytesMatchTargetSpec false ctx.body.layouts p.targetTy mirVal curBytes then
                  go memCur rest
                else
                  match writeV2026Bytes memCur p.place p.layout.alignBytes encBytes with
                  | none => .fail
                  | some mem' => go mem' rest
    match go st.mem st.promotedLocals with
    | .fail => .fail
    | .ok mem' => .ok { st with mem := mem' }

/-- Pure symbolic write through `PlaceExpr` (`writePlaceVal stdValAlg`),
automatically blocked while a loan is `.spatialPinned`, followed by promoted
local synchronization into `V2026ByteMem`. -/
def writePaddedSymPlace (ctx : BodySpatialCtx) (place : PlaceExpr) (newVal : StdVal)
    (st : PaddedSymMemState) : EvalOutcome PaddedSymMemState :=
  if !specsMatchBodyCtx ctx st.mirLocalTypes then .fail
  else
    match writePlaceVal stdValAlg place newVal st.sym with
    | none => .fail
    | some sym' => syncPromotedLocalsToMem ctx { st with sym := sym' }

/-- End mutable loan `lid` (`endLoanInState stdValAlg`), synchronizing any
promoted local back to `V2026ByteMem` (preserving `.uninit` padding whenever
non-padding bytes already agree). -/
def endPaddedLoan (ctx : BodySpatialCtx) (lid : LoanId)
    (st : PaddedSymMemState) : EvalOutcome PaddedSymMemState :=
  if !specsMatchBodyCtx ctx st.mirLocalTypes ||
     !Nat.beq st.mirLocalTypes.length st.mirLocals.length ||
     !Nat.beq st.sym.locals.length st.mirLocals.length then
    .fail
  else
    match endLoanInState stdValAlg lid st.sym with
    | .fail => .fail
    | .ok sym' => syncPromotedLocalsToMem ctx { st with sym := sym' }

/-- Deallocate a promoted non-return local (`reg ≠ 0`), requiring it to be
unborrowed with zero active blocks/loans and exclusive allocation ownership. -/
def deallocatePromotedLocal (ctx : BodySpatialCtx) (reg : LocalId)
    (st : PaddedSymMemState) : EvalOutcome PaddedSymMemState :=
  if !specsMatchBodyCtx ctx st.mirLocalTypes ||
     !Nat.beq st.mirLocalTypes.length st.mirLocals.length ||
     !Nat.beq st.sym.locals.length st.mirLocals.length ||
     Nat.beq reg 0 then
    .fail
  else
    match listGet? st.mirLocals reg, listGet? st.sym.locals reg with
    | some (.indirect place), some cell =>
      let hasActiveLoan : Bool :=
        st.sym.loans.foldr
          (fun le acc => (!le.phase.isEnded &&
            (match loanDirectLocal? le.target with
             | some r => Nat.beq r reg
             | none => false)) || acc)
          false
      if !Nat.beq place.offset 0 ||
         !isUnborrowed cell.perm ||
         hasActiveLoan ||
         anyBlockUsesAlloc place.allocId st.memBlocks ||
         otherPromotedUsesAlloc reg place.allocId st.promotedLocals ||
         otherIndirectLocalUsesAlloc reg place.allocId st.mirLocals ||
         otherLiveAllocRefsAlloc place.allocId st.mem.allocs then
        .fail
      else
        match deallocateV2026Stack st.mem place,
              listSet? st.mirLocals reg .dead,
              listSet? st.sym.locals reg ⟨StdVal.unit, .unborrowed⟩ with
        | some mem', some mirLocals', some symLocals' =>
          .ok
            { st with
              sym := { st.sym with locals := symLocals' }
              mirLocals := mirLocals'
              mem := mem'
              promotedLocals := removePromotedLocal reg st.promotedLocals }
        | _, _, _ => .fail
    | _, _ => .fail

/-! ## 4. Concrete Lawful Codecs & End-to-End Soundness (`Soundness`) -/

/-! ### 4.1 `u32MemCodec` (`size = 4, align = 4`) -/

/-- Bounded `u32` payload (`val < 2^32`). -/
abbrev U32Val := { v : Nat // v < 4294967296 }

def u32MirTy : Ty := { kind := .uint .u32, layoutIdx := 0 }

def u32TargetSpec : SpatialTargetSpec := .mirTy u32MirTy

def u32PadMask : List Bool := [false, false, false, false]

def u32MemEncode (x : U32Val) : List AbstractByte :=
  (encodeU32LEBytes x.val).map (fun b => AbstractByte.init b none)

def u32MemDecode (bs : List AbstractByte) : Option U32Val :=
  match bs with
  | [.init b0 none, .init b1 none, .init b2 none, .init b3 none] =>
    some ⟨decodeU32LEBytes b0 b1 b2 b3, decodeU32LEBytes_lt b0 b1 b2 b3⟩
  | _ => none

/-- Lawful `TypedSpatialMemCodec` for `u32` (`size = 4, align = 4`). -/
def u32MemCodec : TypedSpatialMemCodec U32Val where
  codecId := 4032
  targetTy := u32TargetSpec
  layout := ⟨4, 4⟩
  padMask := u32PadMask
  encodeValToMem := u32MemEncode
  decodeValFromMem := u32MemDecode
  provCheck := sliceAllInitNoProv
  encodeToMirVal x := .scalar ⟨x.val, 4⟩
  decodeFromMirVal v :=
    match v with
    | .scalar ⟨bits, 4⟩ =>
      if h : bits < 4294967296 then some ⟨bits, h⟩ else none
    | _ => none
  encodeToSymVal x := StdVal.nat x.val
  decodeFromSymVal v :=
    match v with
    | ⟨_, .nat n⟩ =>
      if h : n < 4294967296 then some ⟨n, h⟩ else none
    | _ => none

theorem decodeValueFromBytes_u32_4bytes (layouts : LayoutTable)
    (b0 b1 b2 b3 : UInt8) (p0 p1 p2 p3 : Option (Nat × Nat)) :
    decodeValueFromBytes defaultCodecFuel layouts u32MirTy
      [.init b0 p0, .init b1 p1, .init b2 p2, .init b3 p3] =
      some (.scalar ⟨decodeU32LEBytes b0 b1 b2 b3, 4⟩) := by
  change some (Value.scalar
    ⟨b0.toBitVec.toNat + 256 * (b1.toBitVec.toNat + 256 * (b2.toBitVec.toNat + 256 * (b3.toBitVec.toNat + 256 * 0))), 4⟩) = _
  simp only [Nat.mul_zero, Nat.add_zero]
  rfl

theorem u32MemCodec_lawful (layouts : LayoutTable) :
    LawfulTypedSpatialMemCodec layouts u32MemCodec := by
  refine ⟨rfl, by decide, by decide, rfl, ?_, ?_, ?_⟩
  · intro x
    have hEncMir :
        encodeValueToBytes defaultCodecFuel layouts { kind := .uint .u32, layoutIdx := 0 } (.scalar ⟨x.val, 4⟩) =
          some (u32MemEncode x) := encodeU32LEBytes_eq_mir layouts x.val x.property
    have hDecMir :
        decodeValueFromBytes defaultCodecFuel layouts u32MirTy (u32MemEncode x) =
          some (.scalar ⟨x.val, 4⟩) := by
      unfold u32MemEncode encodeU32LEBytes
      dsimp only [List.map]
      rw [decodeValueFromBytes_u32_4bytes, decodeU32LEBytes_encodeU32LEBytes x.val x.property]
    have hDecMem : u32MemDecode (u32MemEncode x) = some x := by
      unfold u32MemDecode u32MemEncode encodeU32LEBytes
      simp only [List.map]
      congr 1
      apply Subtype.ext
      exact decodeU32LEBytes_encodeU32LEBytes x.val x.property
    refine ⟨rfl, rfl, rfl, ?_, hDecMir, hDecMem, ?_, ?_⟩
    · unfold valAndBytesMatchTargetSpec u32MemCodec u32TargetSpec
        SpatialTargetSpec.isRefTarget primFieldValAndBytesMatch
      simp only [u32MirTy, Bool.false_eq_true, ↓reduceIte, hEncMir,
        abstractByteListBeq_refl]
      rfl
    · simp [u32MemCodec, x.property]
    · simp [u32MemCodec, StdVal.nat, x.property]
  · intro b1 b2 hL1 hL2 hSame
    cases b1 with | nil => nomatch hL1 | cons a0 r1 =>
    cases r1 with | nil => nomatch hL1 | cons a1 r2 =>
    cases r2 with | nil => nomatch hL1 | cons a2 r3 =>
    cases r3 with | nil => nomatch hL1 | cons a3 r4 =>
    cases r4 with | cons _ _ => nomatch hL1 | nil =>
    cases b2 with | nil => nomatch hL2 | cons c0 s1 =>
    cases s1 with | nil => nomatch hL2 | cons c1 s2 =>
    cases s2 with | nil => nomatch hL2 | cons c2 s3 =>
    cases s3 with | nil => nomatch hL2 | cons c3 s4 =>
    cases s4 with | cons _ _ => nomatch hL2 | nil =>
    simp only [u32MemCodec, u32PadMask, sameAtNonPad, Bool.and_eq_true,
      abstractByteBeq_eq_true_iff] at hSame
    obtain ⟨rfl, rfl, rfl, rfl, _⟩ := hSame
    rfl
  · intro bs x hLen _ _ hDec
    cases bs with | nil => nomatch hLen | cons a0 r1 =>
    cases r1 with | nil => nomatch hLen | cons a1 r2 =>
    cases r2 with | nil => nomatch hLen | cons a2 r3 =>
    cases r3 with | nil => nomatch hLen | cons a3 r4 =>
    cases r4 with | cons _ _ => nomatch hLen | nil =>
    cases a0 with
    | uninit => nomatch hDec
    | init b0 p0 =>
      cases p0 with
      | some _ => nomatch hDec
      | none =>
        cases a1 with
        | uninit => nomatch hDec
        | init b1 p1 =>
          cases p1 with
          | some _ => nomatch hDec
          | none =>
            cases a2 with
            | uninit => nomatch hDec
            | init b2 p2 =>
              cases p2 with
              | some _ => nomatch hDec
              | none =>
                cases a3 with
                | uninit => nomatch hDec
                | init b3 p3 =>
                  cases p3 with
                  | some _ => nomatch hDec
                  | none =>
                    unfold u32MemCodec u32MemDecode at hDec
                    injection hDec with hX
                    subst hX
                    have hEncEq :
                        encodeValueToBytes defaultCodecFuel layouts { kind := .uint .u32, layoutIdx := 0 }
                          (.scalar ⟨decodeU32LEBytes b0 b1 b2 b3, 4⟩) =
                        some [.init b0 none, .init b1 none, .init b2 none, .init b3 none] := by
                      rw [encodeU32LEBytes_eq_mir layouts _ (decodeU32LEBytes_lt b0 b1 b2 b3)]
                      have h0 : b0.toNat < 256 := b0.toBitVec.isLt
                      have h1 : b1.toNat < 256 := b1.toBitVec.isLt
                      have h2 : b2.toNat < 256 := b2.toBitVec.isLt
                      have h3 : b3.toNat < 256 := b3.toBitVec.isLt
                      have hE0 : UInt8.ofNat (decodeU32LEBytes b0 b1 b2 b3) = b0 := by
                        apply uint8_eq_of_toNat
                        rw [uint8_ofNat_toBitVec_toNat]; unfold decodeU32LEBytes; change _ = b0.toNat; omega
                      have hE1 : UInt8.ofNat (decodeU32LEBytes b0 b1 b2 b3 / 256) = b1 := by
                        apply uint8_eq_of_toNat
                        rw [uint8_ofNat_toBitVec_toNat]; unfold decodeU32LEBytes; change _ = b1.toNat; omega
                      have hE2 : UInt8.ofNat (decodeU32LEBytes b0 b1 b2 b3 / 65536) = b2 := by
                        apply uint8_eq_of_toNat
                        rw [uint8_ofNat_toBitVec_toNat]; unfold decodeU32LEBytes; change _ = b2.toNat; omega
                      have hE3 : UInt8.ofNat (decodeU32LEBytes b0 b1 b2 b3 / 16777216) = b3 := by
                        apply uint8_eq_of_toNat
                        rw [uint8_ofNat_toBitVec_toNat]; unfold decodeU32LEBytes; change _ = b3.toNat; omega
                      simp only [encodeU32LEBytes, List.map, hE0, hE1, hE2, hE3]
                    refine ⟨?_, ?_⟩
                    · unfold valAndBytesMatchTargetSpec u32MemCodec u32TargetSpec
                        SpatialTargetSpec.isRefTarget primFieldValAndBytesMatch
                      simp only [u32MirTy, Bool.false_eq_true, ↓reduceIte, hEncEq,
                        abstractByteListBeq_refl]
                      rfl
                    · exact decodeValueFromBytes_u32_4bytes layouts b0 b1 b2 b3 none none none none

/-! ### 4.2 Padded `#[repr(C)] (u8, [pad; 3], u32)` Codec (`size = 8, align = 4`) -/

/-- Padded `#[repr(C)] (u8, [pad; 3], u32)` payload (`size = 8, align = 4`). -/
structure U8U32Struct where
  aByte : UInt8
  bVal : U32Val

/-- Padding mask for `U8U32Struct`: bytes `1, 2, 3` are alignment padding. -/
def u8U32PadMask : List Bool :=
  [false, true, true, true, false, false, false, false]

/-- Audited `SpatialTargetSpec` for padded `(u8, [pad; 3], u32)` at layout index `idx`. -/
def u8U32TargetSpec (idx : Nat := 0) : SpatialTargetSpec :=
  .reprCAdt 8032 (u8U32Ty idx) 8 4
    [⟨0, { kind := .uint .u8, layoutIdx := 0 }⟩, ⟨4, { kind := .uint .u32, layoutIdx := 0 }⟩]

/-- Canonical rustc `TypeLayout` for padded `(u8, [pad; 3], u32)`. -/
def u8U32TypeLayout : TypeLayout :=
  { size := ⟨8⟩
    align := ⟨4⟩
    backendRepr := .memory
    fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1]
    variants := .single 0
    isUninhabited := false }

/-- Encode `U8U32Struct` into 8 `AbstractByte`s preserving `.uninit` padding at `[1..4)`. -/
def paddedU8U32Encode (s : U8U32Struct) : List AbstractByte :=
  [AbstractByte.init s.aByte none, .uninit, .uninit, .uninit] ++
    (encodeU32LEBytes s.bVal.val).map (fun b => AbstractByte.init b none)

/-- Decode `U8U32Struct` from 8 `AbstractByte`s, ignoring padding `[1..4)` and
enforcing provenance-free initialization on non-padding bytes `0, 4, 5, 6, 7`. -/
def paddedU8U32Decode (bs : List AbstractByte) : Option U8U32Struct :=
  match bs with
  | [a0, _, _, _, a4, a5, a6, a7] =>
    match a0, a4, a5, a6, a7 with
    | .init a none, .init b0 none, .init b1 none, .init b2 none, .init b3 none =>
      some ⟨a, ⟨decodeU32LEBytes b0 b1 b2 b3, decodeU32LEBytes_lt b0 b1 b2 b3⟩⟩
    | _, _, _, _, _ => none
  | _ => none

/-- Provenance check for `U8U32Struct`: non-padding bytes carry `none`, padding
bytes `[1..4)` carry no provenance (`.uninit` or `.init _ none`). -/
def paddedU8U32ProvCheck (bs : List AbstractByte) : Bool :=
  match bs with
  | [.init _ none, p1, p2, p3, .init _ none, .init _ none, .init _ none, .init _ none] =>
    padBytesProvFree [true, true, true] [p1, p2, p3]
  | _ => false

/-- Encode `U8U32Struct` to unmodified `V2026_06_01.MirSemantics.Value`. -/
def paddedU8U32ToMirVal (s : U8U32Struct) : Value :=
  .aggregate 0 [.scalar ⟨s.aByte.toNat, 1⟩, .scalar ⟨s.bVal.val, 4⟩]

/-- Decode `U8U32Struct` from unmodified `V2026_06_01.MirSemantics.Value`. -/
def paddedU8U32FromMirVal (v : Value) : Option U8U32Struct :=
  match v with
  | .aggregate 0 [.scalar ⟨a, 1⟩, .scalar ⟨b, 4⟩] =>
    if _ha : a < 256 then
      if hb : b < 4294967296 then
        some ⟨UInt8.ofNat a, ⟨b, hb⟩⟩
      else none
    else none
  | _ => none

/-- Encode `U8U32Struct` to `PureLift.StdVal` (identical to `PureLift.u8U32Embed`!). -/
def paddedU8U32ToSymVal (s : U8U32Struct) : StdVal :=
  StdVal.pair (.nat s.aByte.toNat) (.nat s.bVal.val)

/-- Decode `U8U32Struct` from `PureLift.StdVal`. -/
def paddedU8U32FromSymVal (v : StdVal) : Option U8U32Struct :=
  match v with
  | ⟨_, .pairBranch _ _ (.nat a) (.nat b)⟩ =>
    if _ha : a < 256 then
      if hb : b < 4294967296 then
        some ⟨UInt8.ofNat a, ⟨b, hb⟩⟩
      else none
    else none
  | _ => none

/-- Lawful `TypedSpatialMemCodec` for padded `#[repr(C)] (u8, [pad; 3], u32)`. -/
def paddedU8U32MemCodec (idx : Nat := 0) : TypedSpatialMemCodec U8U32Struct where
  codecId := 8032
  targetTy := u8U32TargetSpec idx
  layout := ⟨8, 4⟩
  padMask := u8U32PadMask
  encodeValToMem := paddedU8U32Encode
  decodeValFromMem := paddedU8U32Decode
  provCheck := paddedU8U32ProvCheck
  encodeToMirVal := paddedU8U32ToMirVal
  decodeFromMirVal := paddedU8U32FromMirVal
  encodeToSymVal := paddedU8U32ToSymVal
  decodeFromSymVal := paddedU8U32FromSymVal

theorem paddedU8U32_encode_eq_mir {layouts : LayoutTable} {idx : Nat}
    {l : TypeLayout} {mem : List Nat}
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size.bytes = 8)
    (hFields : l.fields = .arbitrary [⟨0⟩, ⟨4⟩] mem)
    (s : U8U32Struct) :
    encodeValueToBytes defaultCodecFuel layouts (u8U32Ty idx)
      (paddedU8U32ToMirVal s) = some (paddedU8U32Encode s) := by
  have hEnc :=
    encodeValueToBytes_u8U32PaddedLayout hLookup hSize hFields
      ⟨s.aByte.toNat, s.aByte.toBitVec.isLt⟩ s.bVal
  have hU8 : UInt8.ofNat s.aByte.toNat = s.aByte := by
    apply uint8_eq_of_toNat
    rw [uint8_ofNat_toBitVec_toNat]
    exact Nat.mod_eq_of_lt s.aByte.toBitVec.isLt
  have hBytesEq :
      u8ExactLE.encode ⟨s.aByte.toNat, s.aByte.toBitVec.isLt⟩ ++
        [.uninit, .uninit, .uninit] ++ u32ExactLE.encode s.bVal =
      paddedU8U32Encode s := by
    have hD2 : s.bVal.val / 256 / 256 = s.bVal.val / 65536 := by
      rw [Nat.div_div_eq_div_mul]
    have hD3 : s.bVal.val / 256 / 256 / 256 = s.bVal.val / 16777216 := by
      rw [hD2, Nat.div_div_eq_div_mul]
    change [.init (UInt8.ofNat s.aByte.toNat) none, .uninit, .uninit, .uninit,
        .init (UInt8.ofNat s.bVal.val) none,
        .init (UInt8.ofNat (s.bVal.val / 256)) none,
        .init (UInt8.ofNat (s.bVal.val / 256 / 256)) none,
        .init (UInt8.ofNat (s.bVal.val / 256 / 256 / 256)) none] =
      paddedU8U32Encode s
    unfold paddedU8U32Encode encodeU32LEBytes
    dsimp only [List.map, List.cons_append, List.nil_append]
    rw [hU8, hD3, hD2]
  rw [← hBytesEq]
  exact hEnc

theorem decodeValueFromBytes_u8U32_8bytes {layouts : LayoutTable} {idx : Nat}
    {l : TypeLayout} {mem : List Nat}
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size.bytes = 8)
    (hFields : l.fields = .arbitrary [⟨0⟩, ⟨4⟩] mem)
    (a b0 b1 b2 b3 : UInt8) (p1 p2 p3 : AbstractByte) :
    decodeValueFromBytes defaultCodecFuel layouts (u8U32Ty idx)
      [.init a none, p1, p2, p3, .init b0 none, .init b1 none, .init b2 none, .init b3 none] =
      some (.aggregate 0
        [.scalar ⟨a.toNat, 1⟩, .scalar ⟨decodeU32LEBytes b0 b1 b2 b3, 4⟩]) := by
  rw [decodeValueFromBytes_u8U32PaddedLayout hLookup hSize hFields]
  have hU8 : u8ExactLE.decode [.init a none] = some ⟨a.toNat, a.toBitVec.isLt⟩ := by
    have hDec1 : decodeLittleEndianBytes [.init a none] = some (a.toNat, none) := by
      change some (a.toBitVec.toNat + 256 * 0, none) = some (a.toBitVec.toNat, none)
      simp only [Nat.mul_zero, Nat.add_zero]
    unfold u8ExactLE
    simp only [List.length_cons, List.length_nil, Nat.beq_refl]
    exact dite_eq_left a.toBitVec.isLt
  have hU32 : u32ExactLE.decode [.init b0 none, .init b1 none, .init b2 none, .init b3 none] =
      some ⟨decodeU32LEBytes b0 b1 b2 b3, decodeU32LEBytes_lt b0 b1 b2 b3⟩ := by
    have hDec4 :
        decodeLittleEndianBytes [.init b0 none, .init b1 none, .init b2 none, .init b3 none] =
          some (decodeU32LEBytes b0 b1 b2 b3, none) := by
      unfold decodeU32LEBytes
      change some (b0.toBitVec.toNat + 256 * (b1.toBitVec.toNat + 256 * (b2.toBitVec.toNat + 256 * (b3.toBitVec.toNat + 256 * 0))), none) = _
      simp only [Nat.mul_zero, Nat.add_zero]
      rfl
    exact u32ExactLE_decode_of _ _ none rfl hDec4 (decodeU32LEBytes_lt b0 b1 b2 b3)
  simp only [List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero,
    List.drop_succ_cons, List.drop_zero, hU8, hU32]

private theorem encodeValueToBytes_u8_byte (layouts : LayoutTable) (a : UInt8) :
    encodeValueToBytes defaultCodecFuel layouts { kind := .uint .u8, layoutIdx := 0 }
      (.scalar ⟨a.toNat, 1⟩) = some [.init a none] := by
  have hLt : a.toNat < 256 := a.toBitVec.isLt
  have hBlt : Nat.blt a.toNat 256 = true := Nat.blt_eq.mpr hLt
  have hU8 : UInt8.ofNat a.toNat = a := by
    apply uint8_eq_of_toNat
    rw [uint8_ofNat_toBitVec_toNat]
    exact Nat.mod_eq_of_lt hLt
  unfold encodeValueToBytes encodeScalarBytes encodeLittleEndianBytes
  simp [intCastTargetBytes, hU8]

/-- Constructive `LawfulTypedSpatialMemCodec` proof for `paddedU8U32MemCodec`
against any captured `LayoutTable` mapping `idx` to the padded `(u8, [pad; 3], u32)`
layout. -/
theorem paddedU8U32MemCodec_lawful {layouts : LayoutTable} {idx : Nat}
    {l : TypeLayout} {mem : List Nat}
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size.bytes = 8)
    (hFields : l.fields = .arbitrary [⟨0⟩, ⟨4⟩] mem) :
    LawfulTypedSpatialMemCodec layouts (paddedU8U32MemCodec idx) := by
  refine ⟨rfl, by simp [paddedU8U32MemCodec], by simp [paddedU8U32MemCodec], rfl, ?_, ?_, ?_⟩
  · intro s
    have hEncU8 := encodeValueToBytes_u8_byte layouts s.aByte
    have hEncU32 := encodeU32LEBytes_eq_mir layouts s.bVal.val s.bVal.property
    have hDecMir :
        decodeValueFromBytes defaultCodecFuel layouts (u8U32Ty idx)
          (paddedU8U32Encode s) = some (paddedU8U32ToMirVal s) := by
      unfold paddedU8U32Encode encodeU32LEBytes paddedU8U32ToMirVal
      simp only [List.map, List.cons_append, List.nil_append,
        decodeValueFromBytes_u8U32_8bytes hLookup hSize hFields,
        decodeU32LEBytes_encodeU32LEBytes s.bVal.val s.bVal.property]
    have hDecMem : paddedU8U32Decode (paddedU8U32Encode s) = some s := by
      unfold paddedU8U32Decode paddedU8U32Encode encodeU32LEBytes
      simp only [List.map, List.cons_append, List.nil_append]
      congr 1
      cases s with
      | mk a b =>
        congr 1
        apply Subtype.ext
        exact decodeU32LEBytes_encodeU32LEBytes b.val b.property
    have hU8Nat : UInt8.ofNat s.aByte.toNat = s.aByte := by
      apply uint8_eq_of_toNat
      rw [uint8_ofNat_toBitVec_toNat]
      exact Nat.mod_eq_of_lt s.aByte.toBitVec.isLt
    have hALt : s.aByte.toNat < 256 := s.aByte.toBitVec.isLt
    refine ⟨rfl, rfl, rfl, ?_, hDecMir, hDecMem, ?_, ?_⟩
    · have hEncU32' :
          encodeValueToBytes defaultCodecFuel layouts { kind := .uint .u32, layoutIdx := 0 }
            (.scalar ⟨s.bVal.val, 4⟩) =
          some ((encodeU32LEBytes s.bVal.val).map (fun b => AbstractByte.init b none)) := hEncU32
      unfold valAndBytesMatchTargetSpec paddedU8U32MemCodec u8U32TargetSpec
        SpatialTargetSpec.isRefTarget paddedU8U32ToMirVal paddedU8U32Encode
      simp only [u8U32Ty, Bool.false_eq_true, ↓reduceIte, valAndBytesMatchTargetSpec.goFields,
        rigidTyByteSize, rigidTyKindByteSize, intCastTargetBytes,
        primFieldValAndBytesMatch, hEncU8, hEncU32', encodeU32LEBytes,
        List.map, List.cons_append, List.nil_append,
        List.drop_zero, List.drop_succ_cons, List.take_succ_cons, List.take_zero,
        abstractByteListBeq_refl, sliceAllInitNoProv, checkPaddingBytes,
        byteIdxCoveredByFields]
      rfl
    · simp only [paddedU8U32MemCodec, paddedU8U32FromMirVal, paddedU8U32ToMirVal,
        hALt, s.bVal.property, ↓reduceDIte, hU8Nat]
    · simp only [paddedU8U32MemCodec, paddedU8U32FromSymVal, paddedU8U32ToSymVal,
        StdVal.pair, StdVal.nat, hALt, s.bVal.property, ↓reduceDIte, hU8Nat]
  · intro b1 b2 hL1 hL2 hSame
    cases b1 with | nil => nomatch hL1 | cons a0 r1 =>
    cases r1 with | nil => nomatch hL1 | cons a1 r2 =>
    cases r2 with | nil => nomatch hL1 | cons a2 r3 =>
    cases r3 with | nil => nomatch hL1 | cons a3 r4 =>
    cases r4 with | nil => nomatch hL1 | cons a4 r5 =>
    cases r5 with | nil => nomatch hL1 | cons a5 r6 =>
    cases r6 with | nil => nomatch hL1 | cons a6 r7 =>
    cases r7 with | nil => nomatch hL1 | cons a7 r8 =>
    cases r8 with | cons _ _ => nomatch hL1 | nil =>
    cases b2 with | nil => nomatch hL2 | cons c0 s1 =>
    cases s1 with | nil => nomatch hL2 | cons c1 s2 =>
    cases s2 with | nil => nomatch hL2 | cons c2 s3 =>
    cases s3 with | nil => nomatch hL2 | cons c3 s4 =>
    cases s4 with | nil => nomatch hL2 | cons c4 s5 =>
    cases s5 with | nil => nomatch hL2 | cons c5 s6 =>
    cases s6 with | nil => nomatch hL2 | cons c6 s7 =>
    cases s7 with | nil => nomatch hL2 | cons c7 s8 =>
    cases s8 with | cons _ _ => nomatch hL2 | nil =>
    simp only [paddedU8U32MemCodec, u8U32PadMask, sameAtNonPad, Bool.and_eq_true,
      abstractByteBeq_eq_true_iff] at hSame
    obtain ⟨rfl, rfl, rfl, rfl, rfl, _⟩ := hSame
    rfl
  · intro bs x hLen _ hProv hDec
    cases bs with | nil => nomatch hLen | cons a0 r1 =>
    cases r1 with | nil => nomatch hLen | cons p1 r2 =>
    cases r2 with | nil => nomatch hLen | cons p2 r3 =>
    cases r3 with | nil => nomatch hLen | cons p3 r4 =>
    cases r4 with | nil => nomatch hLen | cons a4 r5 =>
    cases r5 with | nil => nomatch hLen | cons a5 r6 =>
    cases r6 with | nil => nomatch hLen | cons a6 r7 =>
    cases r7 with | nil => nomatch hLen | cons a7 r8 =>
    cases r8 with | cons _ _ => nomatch hLen | nil =>
    cases a0 with | uninit => nomatch hDec | init a pa =>
    cases pa with | some _ => nomatch hDec | none =>
    cases a4 with | uninit => nomatch hDec | init b0 pb0 =>
    cases pb0 with | some _ => nomatch hDec | none =>
    cases a5 with | uninit => nomatch hDec | init b1 pb1 =>
    cases pb1 with | some _ => nomatch hDec | none =>
    cases a6 with | uninit => nomatch hDec | init b2 pb2 =>
    cases pb2 with | some _ => nomatch hDec | none =>
    cases a7 with | uninit => nomatch hDec | init b3 pb3 =>
    cases pb3 with | some _ => nomatch hDec | none =>
    unfold paddedU8U32MemCodec paddedU8U32Decode at hDec
    injection hDec with hX
    subst hX
    have hEncU8 := encodeValueToBytes_u8_byte layouts a
    have hEncU32 :
        encodeValueToBytes defaultCodecFuel layouts u32MirTy
          (.scalar ⟨decodeU32LEBytes b0 b1 b2 b3, 4⟩) =
        some [.init b0 none, .init b1 none, .init b2 none, .init b3 none] := by
      unfold u32MirTy
      rw [encodeU32LEBytes_eq_mir layouts _ (decodeU32LEBytes_lt b0 b1 b2 b3)]
      have h0 : b0.toNat < 256 := b0.toBitVec.isLt
      have h1 : b1.toNat < 256 := b1.toBitVec.isLt
      have h2 : b2.toNat < 256 := b2.toBitVec.isLt
      have h3 : b3.toNat < 256 := b3.toBitVec.isLt
      have hE0 : UInt8.ofNat (decodeU32LEBytes b0 b1 b2 b3) = b0 := by
        apply uint8_eq_of_toNat
        rw [uint8_ofNat_toBitVec_toNat]; unfold decodeU32LEBytes; change _ = b0.toNat; omega
      have hE1 : UInt8.ofNat (decodeU32LEBytes b0 b1 b2 b3 / 256) = b1 := by
        apply uint8_eq_of_toNat
        rw [uint8_ofNat_toBitVec_toNat]; unfold decodeU32LEBytes; change _ = b1.toNat; omega
      have hE2 : UInt8.ofNat (decodeU32LEBytes b0 b1 b2 b3 / 65536) = b2 := by
        apply uint8_eq_of_toNat
        rw [uint8_ofNat_toBitVec_toNat]; unfold decodeU32LEBytes; change _ = b2.toNat; omega
      have hE3 : UInt8.ofNat (decodeU32LEBytes b0 b1 b2 b3 / 16777216) = b3 := by
        apply uint8_eq_of_toNat
        rw [uint8_ofNat_toBitVec_toNat]; unfold decodeU32LEBytes; change _ = b3.toNat; omega
      simp only [encodeU32LEBytes, List.map, hE0, hE1, hE2, hE3]
    refine ⟨?_, ?_⟩
    · unfold paddedU8U32MemCodec paddedU8U32ProvCheck padBytesProvFree at hProv
      have hEncU32' :
          encodeValueToBytes defaultCodecFuel layouts { kind := .uint .u32, layoutIdx := 0 }
            (.scalar ⟨decodeU32LEBytes b0 b1 b2 b3, 4⟩) =
          some [.init b0 none, .init b1 none, .init b2 none, .init b3 none] := hEncU32
      unfold valAndBytesMatchTargetSpec paddedU8U32MemCodec u8U32TargetSpec
        SpatialTargetSpec.isRefTarget paddedU8U32ToMirVal
      simp only [u8U32Ty, Bool.false_eq_true, ↓reduceIte, valAndBytesMatchTargetSpec.goFields,
        rigidTyByteSize, rigidTyKindByteSize, intCastTargetBytes,
        primFieldValAndBytesMatch, hEncU8, hEncU32', List.drop_zero, List.drop_succ_cons,
        List.take_succ_cons, List.take_zero, abstractByteListBeq_refl, sliceAllInitNoProv,
        checkPaddingBytes, byteIdxCoveredByFields, Bool.and_true]
      cases p1 with
      | uninit =>
        cases p2 with
        | uninit =>
          cases p3 with
          | uninit => rfl
          | init _ pp3 => cases pp3 with | none => rfl | some _ => nomatch hProv
        | init _ pp2 =>
          cases pp2 with
          | some _ => nomatch hProv
          | none =>
            cases p3 with
            | uninit => rfl
            | init _ pp3 => cases pp3 with | none => rfl | some _ => nomatch hProv
      | init _ pp1 =>
        cases pp1 with
        | some _ => nomatch hProv
        | none =>
          cases p2 with
          | uninit =>
            cases p3 with
            | uninit => rfl
            | init _ pp3 => cases pp3 with | none => rfl | some _ => nomatch hProv
          | init _ pp2 =>
            cases pp2 with
            | some _ => nomatch hProv
            | none =>
              cases p3 with
              | uninit => rfl
              | init _ pp3 => cases pp3 with | none => rfl | some _ => nomatch hProv
    · exact decodeValueFromBytes_u8U32_8bytes hLookup hSize hFields a b0 b1 b2 b3 p1 p2 p3

/-! ### 4.3 Provenance-Carrying `#[repr(C)] (u8, [pad; 7], *mut u8)` Codec (`size = 16, align = 8`) -/

/-- Bounded 64-bit pointer offset (`offset < 2^64`). -/
abbrev U64Offset := { v : Nat // v < 18446744073709551616 }

/-- Padded `#[repr(C)] (u8, [pad; 7], *mut u8)` payload carrying a provenance-bearing
64-bit pointer (`size = 16, align = 8`). -/
structure ProvPtrStruct where
  tagByte : UInt8
  ptrOffset : U64Offset

/-- Padding mask for `ProvPtrStruct`: bytes `1..7` are alignment padding. -/
def provPtrPadMask : List Bool :=
  [false, true, true, true, true, true, true, true,
   false, false, false, false, false, false, false, false]

/-- MIR type `(u8, *mut u8)` at layout index `idx`. -/
def provPtrMirTy (idx : Nat := 0) : Ty :=
  { kind := .tuple [.uint .u8, .rawPtr .mut (.uint .u8)], layoutIdx := idx }

/-- Audited `SpatialTargetSpec` for `ProvPtrStruct`. -/
def provPtrTargetSpec (idx : Nat := 0) : SpatialTargetSpec :=
  .reprCAdt 16064 (provPtrMirTy idx) 16 8
    [⟨0, { kind := .uint .u8, layoutIdx := 0 }⟩,
     ⟨8, { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }⟩]

/-- Canonical rustc `TypeLayout` for `ProvPtrStruct` (`size = 16, align = 8`, offsets `[0, 8]`). -/
def provPtrTypeLayout : TypeLayout :=
  { size := ⟨16⟩
    align := ⟨8⟩
    backendRepr := .memory
    fields := .arbitrary [⟨0⟩, ⟨8⟩] [0, 1]
    variants := .single 0
    isUninhabited := false }

/-- Encode `ProvPtrStruct` into 16 `AbstractByte`s attaching `some (allocId, tag)`
to all 8 pointer bytes `[8..16)` and keeping padding `[1..8)` `.uninit`. -/
def provPtrEncode (expectedAllocId expectedTag : Nat) (s : ProvPtrStruct) :
    List AbstractByte :=
  [AbstractByte.init s.tagByte none, .uninit, .uninit, .uninit,
   .uninit, .uninit, .uninit, .uninit] ++
    encodeLittleEndianBytes s.ptrOffset.val 8 (some (expectedAllocId, expectedTag))

/-- Decode `ProvPtrStruct` from 16 `AbstractByte`s, requiring exact `(allocId, tag)`
provenance on all 8 pointer bytes `[8..16)` and `none` provenance on byte `0`. -/
def provPtrDecode (expectedAllocId expectedTag : Nat) (bs : List AbstractByte) :
    Option ProvPtrStruct :=
  if !Nat.beq bs.length 16 then none
  else
    match bs with
    | a0 :: _ =>
      let ptrSlice := bs.drop 8
      match a0 with
      | .init tagB none =>
        if !allHaveExactProv ptrSlice expectedAllocId expectedTag then none
        else
          match decodeLittleEndianBytes ptrSlice with
          | some (bits, some (a, t)) =>
            if Nat.beq a expectedAllocId && Nat.beq t expectedTag then
              if hLt : bits < 18446744073709551616 then
                some ⟨tagB, ⟨bits, hLt⟩⟩
              else none
            else none
          | _ => none
      | _ => none
    | [] => none

/-- Provenance check for `ProvPtrStruct`: byte `0` has `none`, padding `[1..8)`
has no provenance, and bytes `[8..16)` ALL carry `some (expectedAllocId, expectedTag)`. -/
def provPtrCheck (expectedAllocId expectedTag : Nat) (bs : List AbstractByte) : Bool :=
  if !Nat.beq bs.length 16 then false
  else
    match bs with
    | .init _ none :: _ =>
      padBytesProvFree [true, true, true, true, true, true, true] ((bs.drop 1).take 7) &&
      allHaveExactProv (bs.drop 8) expectedAllocId expectedTag
    | _ => false

/-- Encode `ProvPtrStruct` as unmodified `V2026_06_01.MirSemantics.Value`. -/
def provPtrToMirVal (expectedAllocId : AllocId) (s : ProvPtrStruct) : Value :=
  .aggregate 0 [.scalar ⟨s.tagByte.toNat, 1⟩, .ptr ⟨expectedAllocId, s.ptrOffset.val⟩ 8]

/-- Decode `ProvPtrStruct` from unmodified `V2026_06_01.MirSemantics.Value`. -/
def provPtrFromMirVal (expectedAllocId : AllocId) (v : Value) : Option ProvPtrStruct :=
  match v with
  | .aggregate 0 [.scalar ⟨a, 1⟩, .ptr p 8] =>
    if _ha : a < 256 then
      if Nat.beq p.allocId expectedAllocId then
        if ho : p.offsetBytes < 18446744073709551616 then
          some ⟨UInt8.ofNat a, ⟨p.offsetBytes, ho⟩⟩
        else none
      else none
    else none
  | _ => none

/-- Encode `ProvPtrStruct` to `PureLift.StdVal`. -/
def provPtrToSymVal (expectedAllocId : AllocId) (s : ProvPtrStruct) : StdVal :=
  StdVal.pair (.nat s.tagByte.toNat) (StdVal.pair (.nat expectedAllocId) (.nat s.ptrOffset.val))

/-- Decode `ProvPtrStruct` from `PureLift.StdVal`. -/
def provPtrFromSymVal (expectedAllocId : AllocId) (v : StdVal) : Option ProvPtrStruct :=
  match v with
  | ⟨_, .pairBranch _ _ (.nat a) (.pairBranch _ _ (.nat aid) (.nat off))⟩ =>
    if _ha : a < 256 then
      if Nat.beq aid expectedAllocId then
        if ho : off < 18446744073709551616 then
          some ⟨UInt8.ofNat a, ⟨off, ho⟩⟩
        else none
      else none
    else none
  | _ => none

/-- Provenance-enforcing `TypedSpatialMemCodec` for `ProvPtrStruct`
(`#[repr(C)] (u8, [pad; 7], *mut u8)`), requiring every pointer byte `[8..16)` to
carry `some (expectedAllocId, expectedAllocId)` (`p.tag = p.allocId`). -/
def provPtrPaddedMemCodec (expectedAllocId : AllocId) (idx : Nat := 0) :
    TypedSpatialMemCodec ProvPtrStruct where
  codecId := 16064
  targetTy := provPtrTargetSpec idx
  layout := ⟨16, 8⟩
  padMask := provPtrPadMask
  encodeValToMem := provPtrEncode expectedAllocId expectedAllocId
  decodeValFromMem := provPtrDecode expectedAllocId expectedAllocId
  provCheck := provPtrCheck expectedAllocId expectedAllocId
  encodeToMirVal := provPtrToMirVal expectedAllocId
  decodeFromMirVal := provPtrFromMirVal expectedAllocId
  encodeToSymVal := provPtrToSymVal expectedAllocId
  decodeFromSymVal := provPtrFromSymVal expectedAllocId

private theorem allHaveExactProv_encodeLittleEndianBytes (bits n a t : Nat) :
    allHaveExactProv (encodeLittleEndianBytes bits n (some (a, t))) a t = true := by
  induction n generalizing bits with
  | zero => rfl
  | succ rem ih =>
    simp only [allHaveExactProv, List.foldr,
      Nat.beq_refl, Bool.and_self, Bool.true_and]
    exact ih (bits / 256)

private theorem nonPadBytesInitialized_allFalse_encodeLittleEndianBytes (bits n : Nat)
    (p : Option (Nat × Nat)) :
    nonPadBytesInitialized (List.replicate n false)
      (encodeLittleEndianBytes bits n p) = true := by
  induction n generalizing bits with
  | zero => rfl
  | succ rem ih =>
    simp only [List.replicate_succ, encodeLittleEndianBytes, nonPadBytesInitialized]
    exact ih (bits / 256)

private theorem encodeLittleEndianBytes_decode_uniform_prov (a t : Nat) :
    ∀ (bs : List AbstractByte) (bits : Nat) (p : Option (Nat × Nat)),
      allHaveExactProv bs a t = true →
      decodeLittleEndianBytes bs = some (bits, p) →
      encodeLittleEndianBytes bits bs.length (some (a, t)) = bs := by
  intro bs
  induction bs with
  | nil =>
    intro bits p _ hDec
    rfl
  | cons b rest ih =>
    intro bits p hAll hDec
    cases b with
    | uninit => nomatch hAll
    | init byte pb =>
      cases pb with
      | none => nomatch hAll
      | some pair =>
        cases pair with
        | mk a1 t1 =>
          simp only [allHaveExactProv, List.foldr, Bool.and_eq_true, Nat.beq_eq] at hAll
          obtain ⟨⟨rfl, rfl⟩, hRest⟩ := hAll
          simp only [decodeLittleEndianBytes] at hDec
          cases hDR : decodeLittleEndianBytes rest with
          | none => rw [hDR] at hDec; nomatch hDec
          | some pairR =>
            cases pairR with
            | mk hi pR =>
              rw [hDR] at hDec
              injection hDec with hPair
              injection hPair with hBits _
              subst hBits
              have hByteLt : byte.toBitVec.toNat < 256 := byte.toBitVec.isLt
              have hMod : UInt8.ofNat (byte.toBitVec.toNat.add (Nat.mul 256 hi)) = byte := by
                apply uint8_eq_of_toNat
                rw [uint8_ofNat_toBitVec_toNat]
                change (byte.toBitVec.toNat + 256 * hi) % 256 = byte.toBitVec.toNat
                omega
              have hDiv : Nat.div (byte.toBitVec.toNat.add (Nat.mul 256 hi)) 256 = hi := by
                change (byte.toBitVec.toNat + 256 * hi) / 256 = hi
                omega
              simp only [List.length_cons, encodeLittleEndianBytes, hMod, hDiv]
              exact congrArg (List.cons (.init byte (some (a1, t1)))) (ih hi pR hRest hDR)

private theorem decodeLittleEndianBytes_lt_pow :
    ∀ (bs : List AbstractByte) (bits : Nat) (p : Option (Nat × Nat)),
      decodeLittleEndianBytes bs = some (bits, p) → bits < 256 ^ bs.length
  | [], bits, _, hDec => by
    injection hDec with hP; injection hP with hB _
    subst hB; decide
  | .uninit :: _, _, _, hDec => nomatch hDec
  | .init b _ :: rest, bits, _, hDec => by
    simp only [decodeLittleEndianBytes] at hDec
    cases hR : decodeLittleEndianBytes rest with
    | none => rw [hR] at hDec; nomatch hDec
    | some pairR =>
      cases pairR with
      | mk hi pR =>
        rw [hR] at hDec
        injection hDec with hP; injection hP with hB _
        subst hB
        have hIH := decodeLittleEndianBytes_lt_pow rest hi pR hR
        have hByteLt : b.toBitVec.toNat < 256 := b.toBitVec.isLt
        have hPow : 256 ^ (rest.length + 1) = 256 * 256 ^ rest.length := by
          rw [Nat.pow_succ, Nat.mul_comm]
        simp only [List.length_cons, hPow]
        change b.toBitVec.toNat + 256 * hi < 256 * 256 ^ rest.length
        omega

private theorem encodeValueToBytes_rawPtr_mut_u8 (layouts : LayoutTable)
    (aid off : Nat) :
    encodeValueToBytes defaultCodecFuel layouts
      { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }
      (.ptr ⟨aid, off⟩ 8) =
      some (encodeLittleEndianBytes off 8 (some (aid, aid))) := by
  rfl

private theorem decodeValueFromBytes_provPtr_16bytes {layouts : LayoutTable} {idx : Nat}
    {l : TypeLayout} {mem : List Nat}
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size.bytes = 16)
    (hFields : l.fields = .arbitrary [⟨0⟩, ⟨8⟩] mem)
    (tagB : UInt8) (p1 p2 p3 p4 p5 p6 p7 : AbstractByte)
    (ptrBytes : List AbstractByte) (hPtrLen : ptrBytes.length = 8)
    (aid off : Nat) (hPtrDec : decodeLittleEndianBytes ptrBytes = some (off, some (aid, aid))) :
    decodeValueFromBytes defaultCodecFuel layouts (provPtrMirTy idx)
      ([.init tagB none, p1, p2, p3, p4, p5, p6, p7] ++ ptrBytes) =
      some (.aggregate 0 [.scalar ⟨tagB.toNat, 1⟩, .ptr ⟨aid, off⟩ 8]) := by
  have hTotalLen : ([AbstractByte.init tagB none, p1, p2, p3, p4, p5, p6, p7] ++ ptrBytes).length = 16 := by
    simp [hPtrLen]
  show (match LayoutTable.lookup layouts idx with
    | some l => _
    | none => _) = _
  rw [hLookup]
  dsimp only
  rw [hFields, hSize]
  have hLen16 :
      Trusted.Sequence.length ([AbstractByte.init tagB none, p1, p2, p3, p4, p5, p6, p7] ++ ptrBytes) = 16 :=
    hTotalLen
  have hTake8Ptr : takeAbstractBytes 8 ptrBytes = ptrBytes := by
    rw [takeAbstractBytes_eq_take']
    exact List.take_of_length_le (by omega)
  have hDrop8 :
      dropAbstractBytes 8 ([AbstractByte.init tagB none, p1, p2, p3, p4, p5, p6, p7] ++ ptrBytes) =
        ptrBytes := by
    rw [dropAbstractBytes_eq_drop']
    simp
  have hLenPtr : Trusted.Sequence.length ptrBytes = 8 := hPtrLen
  have hB0 : Nat.ble (Nat.add 0 1) 16 = true := rfl
  have hB8 : Nat.ble (Nat.add 8 8) 16 = true := rfl
  have hTake1 : takeAbstractBytes 1 (dropAbstractBytes 0 ([AbstractByte.init tagB none, p1, p2, p3, p4, p5, p6, p7] ++ ptrBytes)) =
      [.init tagB none] := rfl
  have hF0 :
      decodeValueFromBytes 15 layouts { kind := .uint .u8, layoutIdx := 0 } [.init tagB none] =
        some (.scalar ⟨tagB.toNat, 1⟩) := by
    unfold decodeValueFromBytes decodeScalarBytes
    change some (Value.scalar ⟨tagB.toBitVec.toNat + 256 * 0, 1⟩) =
      some (Value.scalar ⟨tagB.toBitVec.toNat, 1⟩)
    simp only [Nat.mul_zero, Nat.add_zero]
  have hF1 :
      decodeValueFromBytes 15 layouts { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 } ptrBytes =
        some (.ptr ⟨aid, off⟩ 8) := by
    unfold decodeValueFromBytes decodeScalarBytes
    simp [hLenPtr, hPtrDec]
  simp only [decodeFieldsAtOffsetsWith, sliceAbstractBytes, rigidTyByteSize, rigidTyKindByteSize,
    intCastTargetBytes, hLen16, hB0, hB8, hTake1, hDrop8, hTake8Ptr, hF0, hF1]

/-- Constructive `LawfulTypedSpatialMemCodec` proof for `provPtrPaddedMemCodec`
enforcing bidirectional `(allocId, tag)` provenance on all 8 pointer bytes. -/
theorem provPtrPaddedMemCodec_lawful {layouts : LayoutTable} {idx : Nat}
    {l : TypeLayout} {mem : List Nat}
    (hLookup : LayoutTable.lookup layouts idx = some l)
    (hSize : l.size.bytes = 16)
    (hFields : l.fields = .arbitrary [⟨0⟩, ⟨8⟩] mem)
    (expectedAllocId : AllocId) :
    LawfulTypedSpatialMemCodec layouts (provPtrPaddedMemCodec expectedAllocId idx) := by
  refine ⟨rfl, by simp [provPtrPaddedMemCodec], by simp [provPtrPaddedMemCodec], rfl, ?_, ?_, ?_⟩
  · intro s
    have hPtrLen : (encodeLittleEndianBytes s.ptrOffset.val 8 (some (expectedAllocId, expectedAllocId))).length = 8 :=
      encodeLittleEndianBytes_length s.ptrOffset.val 8 _
    have hMemLen : (provPtrEncode expectedAllocId expectedAllocId s).length = 16 := by
      unfold provPtrEncode; simp [hPtrLen]
    have hDrop8 : (provPtrEncode expectedAllocId expectedAllocId s).drop 8 =
        encodeLittleEndianBytes s.ptrOffset.val 8 (some (expectedAllocId, expectedAllocId)) := by
      unfold provPtrEncode; simp
    have hAllProv : allHaveExactProv (encodeLittleEndianBytes s.ptrOffset.val 8
        (some (expectedAllocId, expectedAllocId))) expectedAllocId expectedAllocId = true :=
      allHaveExactProv_encodeLittleEndianBytes s.ptrOffset.val 8 expectedAllocId expectedAllocId
    have hPtrDec : decodeLittleEndianBytes
        (encodeLittleEndianBytes s.ptrOffset.val 8 (some (expectedAllocId, expectedAllocId))) =
        some (s.ptrOffset.val, some (expectedAllocId, expectedAllocId)) :=
      decodeLittleEndianBytes_encodeLittleEndianBytes_of_lt s.ptrOffset.val 8 _ (by decide) s.ptrOffset.property
    have hNonPad : nonPadBytesInitialized provPtrPadMask
        (provPtrEncode expectedAllocId expectedAllocId s) = true := by
      unfold provPtrPadMask provPtrEncode
      simp only [nonPadBytesInitialized, List.cons_append, List.nil_append]
    have hProv : provPtrCheck expectedAllocId expectedAllocId
        (provPtrEncode expectedAllocId expectedAllocId s) = true := by
      unfold provPtrCheck
      rw [hMemLen]
      simp only [Nat.beq_refl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hDrop8, hAllProv]
      rfl
    have hDecMir :
        decodeValueFromBytes defaultCodecFuel layouts (provPtrMirTy idx)
          (provPtrEncode expectedAllocId expectedAllocId s) =
          some (provPtrToMirVal expectedAllocId s) :=
      decodeValueFromBytes_provPtr_16bytes hLookup hSize hFields s.tagByte
        .uninit .uninit .uninit .uninit .uninit .uninit .uninit
        _ hPtrLen expectedAllocId s.ptrOffset.val hPtrDec
    have hDecMem : provPtrDecode expectedAllocId expectedAllocId
        (provPtrEncode expectedAllocId expectedAllocId s) = some s := by
      unfold provPtrDecode
      rw [hMemLen]
      simp only [Nat.beq_refl, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        provPtrEncode, List.cons_append, List.drop_succ_cons, List.drop_zero,
        List.nil_append, hAllProv, hPtrDec, Bool.and_self, s.ptrOffset.property, ↓reduceDIte]
    have hEncU8 := encodeValueToBytes_u8_byte layouts s.tagByte
    have hEncPtr := encodeValueToBytes_rawPtr_mut_u8 layouts expectedAllocId s.ptrOffset.val
    have hU8Nat : UInt8.ofNat s.tagByte.toNat = s.tagByte := by
      apply uint8_eq_of_toNat
      rw [uint8_ofNat_toBitVec_toNat]
      exact Nat.mod_eq_of_lt s.tagByte.toBitVec.isLt
    have hBytesMatch :
        valAndBytesMatchTargetSpec true layouts (provPtrTargetSpec idx)
          (provPtrToMirVal expectedAllocId s)
          (provPtrEncode expectedAllocId expectedAllocId s) = true := by
      unfold valAndBytesMatchTargetSpec provPtrTargetSpec SpatialTargetSpec.isRefTarget
        provPtrToMirVal
      simp only [provPtrMirTy, hMemLen, Nat.beq_refl, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, valAndBytesMatchTargetSpec.goFields,
        rigidTyByteSize, rigidTyKindByteSize, intCastTargetBytes]
      have hTake1 : ((provPtrEncode expectedAllocId expectedAllocId s).drop 0).take 1 =
          [.init s.tagByte none] := rfl
      have hTake8 : ((provPtrEncode expectedAllocId expectedAllocId s).drop 8).take 8 =
          encodeLittleEndianBytes s.ptrOffset.val 8 (some (expectedAllocId, expectedAllocId)) := by
        rw [hDrop8]
        exact List.take_of_length_le (by omega)
      have hPadCheck :
          checkPaddingBytes true layouts
            [⟨0, { kind := .uint .u8, layoutIdx := 0 }⟩,
             ⟨8, { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }⟩]
            0 (provPtrEncode expectedAllocId expectedAllocId s) = true := by
        have hTail8 : ∀ idx0 (ys : List AbstractByte), 8 ≤ idx0 → idx0 + ys.length ≤ 16 →
            checkPaddingBytes true layouts
              [⟨0, { kind := .uint .u8, layoutIdx := 0 }⟩,
               ⟨8, { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }⟩]
              idx0 ys = true := by
          intro idx0 ys
          induction ys generalizing idx0 with
          | nil => intro _ _; rfl
          | cons y yr ih =>
            intro hGe hLe
            simp only [checkPaddingBytes, byteIdxCoveredByFields, rigidTyByteSize,
              rigidTyKindByteSize, intCastTargetBytes, Option.getD_some]
            have hCov : (Nat.ble 8 idx0 && Nat.blt idx0 (8 + 8)) = true := by
              rw [Nat.ble_eq.mpr hGe, Nat.blt_eq.mpr (by simp at hLe; omega)]; rfl
            simp only [hCov, Bool.or_false, Bool.or_true, ↓reduceIte, Bool.true_and]
            exact ih (idx0 + 1) (by omega) (by simp at hLe; omega)
        have hHead8 :
            checkPaddingBytes true layouts
              [⟨0, { kind := .uint .u8, layoutIdx := 0 }⟩,
               ⟨8, { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }⟩]
              0 (provPtrEncode expectedAllocId expectedAllocId s) =
            checkPaddingBytes true layouts
              [⟨0, { kind := .uint .u8, layoutIdx := 0 }⟩,
               ⟨8, { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }⟩]
              8 (encodeLittleEndianBytes s.ptrOffset.val 8 (some (expectedAllocId, expectedAllocId))) :=
          rfl
        rw [hHead8]
        exact hTail8 8
          (encodeLittleEndianBytes s.ptrOffset.val 8 (some (expectedAllocId, expectedAllocId)))
          (by omega) (by rw [hPtrLen]; omega)
      simp only [hTake1, hTake8, primFieldValAndBytesMatch, hEncU8, hEncPtr, hPtrLen,
        hAllProv, abstractByteListBeq_refl, sliceAllInitNoProv, hPadCheck, ProvenancePtr.tag]
      rfl
    have hTagLt : s.tagByte.toNat < 256 := s.tagByte.toBitVec.isLt
    refine ⟨hMemLen, hNonPad, hProv, hBytesMatch, hDecMir, hDecMem, ?_, ?_⟩
    · simp only [provPtrPaddedMemCodec, provPtrFromMirVal, provPtrToMirVal,
        hTagLt, Nat.beq_refl, ↓reduceIte, s.ptrOffset.property, ↓reduceDIte, hU8Nat]
    · simp only [provPtrPaddedMemCodec, provPtrFromSymVal, provPtrToSymVal,
        StdVal.pair, StdVal.nat, hTagLt, Nat.beq_refl, ↓reduceIte,
        s.ptrOffset.property, ↓reduceDIte, hU8Nat]
  · intro b1 b2 hL1 hL2 hSame
    cases b1 with | nil => nomatch hL1 | cons a0 r1 =>
    cases r1 with | nil => nomatch hL1 | cons _ r2 =>
    cases r2 with | nil => nomatch hL1 | cons _ r3 =>
    cases r3 with | nil => nomatch hL1 | cons _ r4 =>
    cases r4 with | nil => nomatch hL1 | cons _ r5 =>
    cases r5 with | nil => nomatch hL1 | cons _ r6 =>
    cases r6 with | nil => nomatch hL1 | cons _ r7 =>
    cases r7 with | nil => nomatch hL1 | cons _ r8 =>
    cases r8 with | nil => nomatch hL1 | cons a8 r9 =>
    cases r9 with | nil => nomatch hL1 | cons a9 r10 =>
    cases r10 with | nil => nomatch hL1 | cons a10 r11 =>
    cases r11 with | nil => nomatch hL1 | cons a11 r12 =>
    cases r12 with | nil => nomatch hL1 | cons a12 r13 =>
    cases r13 with | nil => nomatch hL1 | cons a13 r14 =>
    cases r14 with | nil => nomatch hL1 | cons a14 r15 =>
    cases r15 with | nil => nomatch hL1 | cons a15 r16 =>
    cases r16 with | cons _ _ => nomatch hL1 | nil =>
    cases b2 with | nil => nomatch hL2 | cons c0 s1 =>
    cases s1 with | nil => nomatch hL2 | cons _ s2 =>
    cases s2 with | nil => nomatch hL2 | cons _ s3 =>
    cases s3 with | nil => nomatch hL2 | cons _ s4 =>
    cases s4 with | nil => nomatch hL2 | cons _ s5 =>
    cases s5 with | nil => nomatch hL2 | cons _ s6 =>
    cases s6 with | nil => nomatch hL2 | cons _ s7 =>
    cases s7 with | nil => nomatch hL2 | cons _ s8 =>
    cases s8 with | nil => nomatch hL2 | cons c8 s9 =>
    cases s9 with | nil => nomatch hL2 | cons c9 s10 =>
    cases s10 with | nil => nomatch hL2 | cons c10 s11 =>
    cases s11 with | nil => nomatch hL2 | cons c11 s12 =>
    cases s12 with | nil => nomatch hL2 | cons c12 s13 =>
    cases s13 with | nil => nomatch hL2 | cons c13 s14 =>
    cases s14 with | nil => nomatch hL2 | cons c14 s15 =>
    cases s15 with | nil => nomatch hL2 | cons c15 s16 =>
    cases s16 with | cons _ _ => nomatch hL2 | nil =>
    simp only [provPtrPaddedMemCodec, provPtrPadMask, sameAtNonPad, Bool.and_eq_true,
      abstractByteBeq_eq_true_iff] at hSame
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, _⟩ := hSame
    rfl
  · intro bs x hLen _ hProv hDec
    cases bs with | nil => nomatch hLen | cons a0 r1 =>
    cases r1 with | nil => nomatch hLen | cons p1 r2 =>
    cases r2 with | nil => nomatch hLen | cons p2 r3 =>
    cases r3 with | nil => nomatch hLen | cons p3 r4 =>
    cases r4 with | nil => nomatch hLen | cons p4 r5 =>
    cases r5 with | nil => nomatch hLen | cons p5 r6 =>
    cases r6 with | nil => nomatch hLen | cons p6 r7 =>
    cases r7 with | nil => nomatch hLen | cons p7 ptrBytes =>
    have hPtrLen : ptrBytes.length = 8 := by simp [provPtrPaddedMemCodec] at hLen; omega
    have hBs16 : (a0 :: p1 :: p2 :: p3 :: p4 :: p5 :: p6 :: p7 :: ptrBytes).length = 16 := by
      simp [hPtrLen]
    unfold provPtrPaddedMemCodec provPtrDecode at hDec
    simp only [hBs16, Nat.beq_refl, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, List.drop_succ_cons, List.drop_zero] at hDec
    cases a0 with | uninit => nomatch hDec | init tagB p0 =>
    cases p0 with | some _ => nomatch hDec | none =>
    cases hAll : allHaveExactProv ptrBytes expectedAllocId expectedAllocId with
    | false => rw [hAll] at hDec; nomatch hDec
    | true =>
      rw [hAll] at hDec
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hDec
      cases hDL : decodeLittleEndianBytes ptrBytes with
      | none => rw [hDL] at hDec; nomatch hDec
      | some pair =>
        cases pair with
        | mk bits optP =>
          rw [hDL] at hDec
          cases optP with
          | none => nomatch hDec
          | some atPair =>
            cases atPair with
            | mk a t =>
              simp only at hDec
              cases hAT : (Nat.beq a expectedAllocId && Nat.beq t expectedAllocId) with
              | false => rw [hAT] at hDec; nomatch hDec
              | true =>
                rw [hAT] at hDec
                simp only [↓reduceIte] at hDec
                simp only [Bool.and_eq_true, Nat.beq_eq] at hAT
                obtain ⟨hAEq, hTEq⟩ := hAT
                rw [hAEq, hTEq] at hDL
                have hBitsLt : bits < 18446744073709551616 := by
                  have hPow := decodeLittleEndianBytes_lt_pow ptrBytes bits _ hDL
                  rw [hPtrLen] at hPow
                  exact hPow
                simp only [hBitsLt, ↓reduceDIte, Option.some.injEq] at hDec
                subst hDec
                have hPtrReenc :
                    encodeLittleEndianBytes bits 8 (some (expectedAllocId, expectedAllocId)) = ptrBytes := by
                  rw [← hPtrLen]
                  exact encodeLittleEndianBytes_decode_uniform_prov expectedAllocId expectedAllocId
                    ptrBytes bits _ hAll hDL
                have hEncU8 := encodeValueToBytes_u8_byte layouts tagB
                have hEncPtr := encodeValueToBytes_rawPtr_mut_u8 layouts expectedAllocId bits
                have hTakePtr : ptrBytes.take 8 = ptrBytes :=
                  List.take_of_length_le (by omega)
                unfold provPtrPaddedMemCodec provPtrCheck at hProv
                simp only [hBs16, Nat.beq_refl, Bool.not_true,
                  Bool.false_eq_true, ↓reduceIte, List.drop_succ_cons, List.drop_zero,
                  List.take_succ_cons, List.take_zero, hAll, Bool.and_true] at hProv
                refine ⟨?_, ?_⟩
                · unfold valAndBytesMatchTargetSpec provPtrPaddedMemCodec provPtrTargetSpec
                    SpatialTargetSpec.isRefTarget provPtrToMirVal
                  have hBle1 : Nat.ble (0 + 1) 16 = true := rfl
                  have hBle8 : Nat.ble (8 + 8) 16 = true := rfl
                  simp only [provPtrMirTy, hBs16, hPtrLen, hBle1, hBle8, Nat.beq_refl,
                    Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                    valAndBytesMatchTargetSpec.goFields, rigidTyByteSize,
                    rigidTyKindByteSize, intCastTargetBytes, List.drop_zero,
                    List.drop_succ_cons, List.take_succ_cons, List.take_zero, hTakePtr,
                    primFieldValAndBytesMatch, hEncU8, hEncPtr, hPtrReenc, hAll,
                    abstractByteListBeq_refl, sliceAllInitNoProv, ProvenancePtr.tag]
                  simp only [Bool.true_and, Bool.and_true]
                  -- Padding bytes 1..7 have no provenance by `hProv`, bytes 8..15 covered
                  have hPadByte : ∀ b : AbstractByte,
                      (match b with | .uninit => true | .init _ none => true | .init _ (some _) => false) = true →
                      (match b with | .uninit => true | .init _ none => !false | .init _ (some _) => false) = true :=
                    fun _ h => h
                  have hTail8 : ∀ idx0 (ys : List AbstractByte), 8 ≤ idx0 → idx0 + ys.length ≤ 16 →
                      checkPaddingBytes false layouts
                        [⟨0, { kind := .uint .u8, layoutIdx := 0 }⟩,
                         ⟨8, { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }⟩]
                        idx0 ys = true := by
                    intro idx0 ys
                    induction ys generalizing idx0 with
                    | nil => intro _ _; rfl
                    | cons y yr ih =>
                      intro hGe hLe
                      simp only [checkPaddingBytes, byteIdxCoveredByFields, rigidTyByteSize,
                        rigidTyKindByteSize, intCastTargetBytes, Option.getD_some]
                      have hCov : (Nat.ble 8 idx0 && Nat.blt idx0 (8 + 8)) = true := by
                        rw [Nat.ble_eq.mpr hGe, Nat.blt_eq.mpr (by simp at hLe; omega)]; rfl
                      simp only [hCov, Bool.or_false, Bool.or_true, ↓reduceIte, Bool.true_and]
                      exact ih (idx0 + 1) (by omega) (by simp at hLe; omega)
                  have hPadClean : ∀ (x1 x2 x3 x4 x5 x6 x7 : AbstractByte),
                      padBytesProvFree [true, true, true, true, true, true, true]
                        [x1, x2, x3, x4, x5, x6, x7] = true →
                      checkPaddingBytes false layouts
                        [⟨0, { kind := .uint .u8, layoutIdx := 0 }⟩,
                         ⟨8, { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }⟩]
                        0 (.init tagB none :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: ptrBytes) = true := by
                    intro x1 x2 x3 x4 x5 x6 x7 hP
                    have hStep : ∀ (y : AbstractByte) (idx : Nat) (rest : List AbstractByte),
                        1 ≤ idx → idx < 8 →
                        (match y with | .uninit => true | .init _ none => true | .init _ (some _) => false) = true →
                        checkPaddingBytes false layouts
                          [⟨0, { kind := .uint .u8, layoutIdx := 0 }⟩,
                           ⟨8, { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }⟩]
                          (idx + 1) rest = true →
                        checkPaddingBytes false layouts
                          [⟨0, { kind := .uint .u8, layoutIdx := 0 }⟩,
                           ⟨8, { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }⟩]
                          idx (y :: rest) = true := by
                      intro y idx rest hGe1 hLt8 hY hR
                      simp only [checkPaddingBytes, byteIdxCoveredByFields, rigidTyByteSize,
                        rigidTyKindByteSize, intCastTargetBytes, Option.getD_some]
                      have hNot0 : Nat.blt idx 1 = false := by
                        cases idx with | zero => omega | succ _ => rfl
                      have hNot8 : Nat.ble 8 idx = false := by
                        cases hB : Nat.ble 8 idx with
                        | false => rfl
                        | true => have := Nat.ble_eq.mp hB; omega
                      simp only [hNot0, hNot8, Bool.and_false, Bool.false_and, Bool.or_false,
                        Bool.false_eq_true, ↓reduceIte, hR, Bool.and_true]
                      exact hPadByte y hY
                    have hSplitPad : ∀ (b : AbstractByte) (ms : List Bool) (bs : List AbstractByte),
                        padBytesProvFree (true :: ms) (b :: bs) = true →
                        (match b with | .uninit => true | .init _ none => true | .init _ (some _) => false) = true ∧
                        padBytesProvFree ms bs = true := by
                      intro b ms bs h
                      unfold padBytesProvFree at h
                      cases b with
                      | uninit => exact ⟨rfl, h⟩
                      | init _ pp =>
                        cases pp with
                        | none => exact ⟨rfl, h⟩
                        | some _ => nomatch h
                    have hP1 := hSplitPad x1 [true, true, true, true, true, true] [x2, x3, x4, x5, x6, x7] hP
                    have hP2 := hSplitPad x2 [true, true, true, true, true] [x3, x4, x5, x6, x7] hP1.2
                    have hP3 := hSplitPad x3 [true, true, true, true] [x4, x5, x6, x7] hP2.2
                    have hP4 := hSplitPad x4 [true, true, true] [x5, x6, x7] hP3.2
                    have hP5 := hSplitPad x5 [true, true] [x6, x7] hP4.2
                    have hP6 := hSplitPad x6 [true] [x7] hP5.2
                    have hP7 := (hSplitPad x7 [] [] hP6.2).1
                    have hCov0 :
                        checkPaddingBytes false layouts
                          [⟨0, { kind := .uint .u8, layoutIdx := 0 }⟩,
                           ⟨8, { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }⟩]
                          0 (.init tagB none :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: ptrBytes) =
                        checkPaddingBytes false layouts
                          [⟨0, { kind := .uint .u8, layoutIdx := 0 }⟩,
                           ⟨8, { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }⟩]
                          1 (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: ptrBytes) := rfl
                    rw [hCov0]
                    exact hStep x1 1 _ (by omega) (by omega) hP1.1
                      (hStep x2 2 _ (by omega) (by omega) hP2.1
                        (hStep x3 3 _ (by omega) (by omega) hP3.1
                          (hStep x4 4 _ (by omega) (by omega) hP4.1
                            (hStep x5 5 _ (by omega) (by omega) hP5.1
                              (hStep x6 6 _ (by omega) (by omega) hP6.1
                                (hStep x7 7 _ (by omega) (by omega) hP7
                                  (hTail8 8 ptrBytes (by omega) (by omega))))))))
                  exact hPadClean p1 p2 p3 p4 p5 p6 p7 hProv
                · exact decodeValueFromBytes_provPtr_16bytes hLookup hSize hFields
                    tagB p1 p2 p3 p4 p5 p6 p7 ptrBytes hPtrLen expectedAllocId bits hDL

/-! ### 4.4 Canonical Authenticated `CapturedMir` Contexts & End-to-End Soundness -/

/-- Minimal well-formed `CapturedMir` body with locals `[_0 : (), _1 : (u8, u32)]`
and captured padded `(u8, [pad; 3], u32)` layout at `layoutIdx = 0`. -/
def u8U32SampleBody : CapturedMir :=
  { defPath := "spatial_mem::u8_u32_padded_demo"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 1
    localDecls :=
      [ { mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 }, debugName := none }
      , { mutability := .mut, ty := u8U32Ty 0, debugName := some "s" } ]
    basicBlocks :=
      [ { statements := [], terminator := { kind := .return_, span := "" }, isCleanup := false } ]
    fnAbi :=
      { args := []
        ret := { layout := u8U32TypeLayout, mode := .ignore }
        conv := .rust
        canUnwind := false }
    layouts := { pointerBits := 64, isLittleEndian := true, entries := [u8U32TypeLayout] }
    allocations := [] }

/-- Authenticated `BodySpatialCtx` for `u8U32SampleBody`. -/
def u8U32BodyCtx : BodySpatialCtx :=
  { body := u8U32SampleBody
    specs := [.mirTy { kind := .tuple [], layoutIdx := 0 }, u8U32TargetSpec 0] }

theorem u8U32BodyCtx_wf : bodySpatialCtxWf u8U32BodyCtx = true := rfl

/-- Minimal well-formed `CapturedMir` body with locals `[_0 : (), _1 : (u8, *mut u8)]`
and captured padded `ProvPtrStruct` layout at `layoutIdx = 0`. -/
def provPtrSampleBody : CapturedMir :=
  { defPath := "spatial_mem::prov_ptr_padded_demo"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 1
    localDecls :=
      [ { mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 }, debugName := none }
      , { mutability := .mut, ty := provPtrMirTy 0, debugName := some "p" } ]
    basicBlocks :=
      [ { statements := [], terminator := { kind := .return_, span := "" }, isCleanup := false } ]
    fnAbi :=
      { args := []
        ret := { layout := provPtrTypeLayout, mode := .ignore }
        conv := .rust
        canUnwind := false }
    layouts := { pointerBits := 64, isLittleEndian := true, entries := [provPtrTypeLayout] }
    allocations := [] }

/-- Authenticated `BodySpatialCtx` for `provPtrSampleBody`. -/
def provPtrBodyCtx : BodySpatialCtx :=
  { body := provPtrSampleBody
    specs := [.mirTy { kind := .tuple [], layoutIdx := 0 }, provPtrTargetSpec 0] }

theorem provPtrBodyCtx_wf : bodySpatialCtxWf provPtrBodyCtx = true := rfl

theorem paddedU8U32MemCodec_lawful_sample :
    LawfulTypedSpatialMemCodec u8U32BodyCtx.body.layouts (paddedU8U32MemCodec 0) :=
  paddedU8U32MemCodec_lawful (idx := 0) (l := u8U32TypeLayout) (mem := [0, 1]) rfl rfl rfl

theorem provPtrPaddedMemCodec_lawful_sample (expectedAllocId : AllocId) :
    LawfulTypedSpatialMemCodec provPtrBodyCtx.body.layouts
      (provPtrPaddedMemCodec expectedAllocId 0) :=
  provPtrPaddedMemCodec_lawful (idx := 0) (l := provPtrTypeLayout) (mem := [0, 1]) rfl rfl rfl
    expectedAllocId

/-- **Parametric full-lifecycle soundness for any `LawfulTypedSpatialMemCodec`**:
for any authenticated `ctx : BodySpatialCtx`, lawful codec `c`, handle-free
`xInit xNew : α`, valid aligned in-bounds byte patch `patchBytes` transitioning
`c.encodeValToMem xInit` to `c.encodeValToMem xNew`, fresh `V2026ByteMem` `m0`,
and disjoint sibling `otherPlace`, `freezePaddedToMem` → `mutatePaddedInMem` →
`readV2026Bytes` → `loadV2026Typed` (unmodified `decodeValueFromBytes`) →
`reabsorbPaddedFromMem` → `endPaddedLoan` → `deallocatePromotedLocal` ALL succeed
and frame `otherPlace` across every transition. -/
private theorem maxUnionHandleRef_eq_nil {xs ys : List HandleRef}
    (h : maxUnionHandleRef xs ys = []) : xs = [] ∧ ys = [] := by
  unfold maxUnionHandleRef at h
  obtain ⟨hX, hY⟩ := List.append_eq_nil_iff.mp h
  subst hX
  exact ⟨rfl, hY⟩

private theorem natFold_succ_eq {α : Type} (z : α) (s : Nat → α → α) (k : Nat) :
    natFold z s (k + 1) = s k (natFold z s k) := rfl

private theorem collectHandleRefsIn_true_empty_of_false_empty {Val : Type}
    (alg : ValAlgebra Val) (ctx : List (Val × Bool)) (v : Val)
    (h : collectHandleRefsIn alg false ctx v = some []) :
    collectHandleRefsIn alg true ctx v = some [] := by
  let stepF (lower : Bool)
      (ih : Val → Option (List HandleRef)) (w : Val) : Option (List HandleRef) :=
    match alg.decodeRef w with
    | some (lid, path) => some [(lid, path, alg.decodeRefIsShared w)]
    | none =>
      let fromFields : Option (List HandleRef) :=
        natFold (some [])
          (fun idx acc =>
            match acc, alg.getField idx w with
            | some ls, some field =>
              match ih field with
              | some ls' => some (ls ++ ls')
              | none => none
            | some ls, none => some ls
            | none, _ => none)
          (alg.sizeBound w)
      let fromArms : Option (List HandleRef) :=
        match alg.branchSplit w with
        | none => some []
        | some (cond, vt, vf) =>
          match ih cond, ih vt, ih vf with
          | some [], some lt, some lf =>
            if lt == lf then some lt
            else
              match lookupCond alg ctx cond with
              | some true => some lt
              | some false => some lf
              | none =>
                some (if lower then minInterHandleRef lt lf else maxUnionHandleRef lt lf)
          | _, _, _ => none
      match fromFields, fromArms with
      | some ls, some ls' =>
        some (if lower then maxUnionHandleRef ls ls' else ls ++ ls')
      | _, _ => none
  have hAux : ∀ (n : Nat) (w : Val) (ls : List HandleRef),
      natFold (fun _ => none) (fun _ ih => stepF false ih) n w = some ls →
      ∃ ls', natFold (fun _ => none) (fun _ ih => stepF true ih) n w = some ls' ∧
        (ls = [] → ls' = []) := by
    intro n
    induction n with
    | zero => intro w ls h0; nomatch h0
    | succ k ih =>
      intro w ls hS
      rw [natFold_succ_eq] at hS ⊢
      dsimp only [stepF] at hS ⊢
      cases hDec : alg.decodeRef w with
      | some p =>
        rw [hDec] at hS
        cases p with
        | mk lid path =>
          injection hS with hEq
          refine ⟨[(lid, path, alg.decodeRefIsShared w)], rfl, ?_⟩
          intro hNil; rw [hNil] at hEq; nomatch hEq
      | none =>
        rw [hDec] at hS
        have hFields : ∀ m (fls : List HandleRef),
            natFold (some [])
              (fun idx acc =>
                match acc, alg.getField idx w with
                | some ls0, some field =>
                  match natFold (fun _ => none) (fun _ ih => stepF false ih) k field with
                  | some ls' => some (ls0 ++ ls')
                  | none => none
                | some ls0, none => some ls0
                | none, _ => none) m = some fls →
            ∃ fls',
              natFold (some [])
                (fun idx acc =>
                  match acc, alg.getField idx w with
                  | some ls0, some field =>
                    match natFold (fun _ => none) (fun _ ih => stepF true ih) k field with
                    | some ls' => some (ls0 ++ ls')
                    | none => none
                  | some ls0, none => some ls0
                  | none, _ => none) m = some fls' ∧
              (fls = [] → fls' = []) := by
          intro m
          induction m with
          | zero =>
            intro fls hF; injection hF with hEq; exact ⟨[], rfl, fun _ => rfl⟩
          | succ j ihM =>
            intro fls hF
            rw [natFold_succ_eq] at hF ⊢
            cases hAcc :
                natFold (some [])
                  (fun idx acc =>
                    match acc, alg.getField idx w with
                    | some ls0, some field =>
                      match natFold (fun _ => none) (fun _ ih => stepF false ih) k field with
                      | some ls' => some (ls0 ++ ls')
                      | none => none
                    | some ls0, none => some ls0
                    | none, _ => none) j with
            | none => rw [hAcc] at hF; nomatch hF
            | some ls0 =>
              rw [hAcc] at hF
              obtain ⟨ls0', hAcc', hNil0⟩ := ihM ls0 hAcc
              rw [hAcc']
              cases hGet : alg.getField j w with
              | none =>
                rw [hGet] at hF; injection hF with hEq; subst hEq
                exact ⟨ls0', rfl, hNil0⟩
              | some field =>
                rw [hGet] at hF
                dsimp only at hF ⊢
                cases hFld : natFold (fun _ => none) (fun _ ih => stepF false ih) k field with
                | none => rw [hFld] at hF; nomatch hF
                | some ls1 =>
                  rw [hFld] at hF; injection hF with hEq; subst hEq
                  obtain ⟨ls1', hFld', hNil1⟩ := ih field ls1 hFld
                  rw [hFld']
                  refine ⟨ls0' ++ ls1', rfl, ?_⟩
                  intro hApp
                  obtain ⟨h0, h1⟩ := List.append_eq_nil_iff.mp hApp
                  rw [hNil0 h0, hNil1 h1]; rfl
        cases hFF :
            natFold (some [])
              (fun idx acc =>
                match acc, alg.getField idx w with
                | some ls0, some field =>
                  match natFold (fun _ => none) (fun _ ih => stepF false ih) k field with
                  | some ls' => some (ls0 ++ ls')
                  | none => none
                | some ls0, none => some ls0
                | none, _ => none) (alg.sizeBound w) with
        | none => rw [hFF] at hS; nomatch hS
        | some lsF =>
          rw [hFF] at hS
          obtain ⟨lsF', hFF', hNilF⟩ := hFields (alg.sizeBound w) lsF hFF
          rw [hFF']
          let armsF (lower : Bool) : Option (List HandleRef) :=
            match alg.branchSplit w with
            | none => some []
            | some (cond, vt, vf) =>
              match natFold (fun _ => none) (fun _ ih => stepF lower ih) k cond,
                    natFold (fun _ => none) (fun _ ih => stepF lower ih) k vt,
                    natFold (fun _ => none) (fun _ ih => stepF lower ih) k vf with
              | some [], some lt, some lf =>
                if lt == lf then some lt
                else
                  match lookupCond alg ctx cond with
                  | some true => some lt
                  | some false => some lf
                  | none =>
                    some (if lower then minInterHandleRef lt lf else maxUnionHandleRef lt lf)
              | _, _, _ => none
          have hArms : ∀ (als : List HandleRef),
              armsF false = some als →
              ∃ als', armsF true = some als' ∧ (als = [] → als' = []) := by
            intro als hA
            dsimp only [armsF] at hA ⊢
            cases hBr : alg.branchSplit w with
            | none =>
              rw [hBr] at hA; injection hA with hEq; exact ⟨[], rfl, fun _ => rfl⟩
            | some triple =>
              rw [hBr] at hA
              dsimp only at hA ⊢
              obtain ⟨cond, vt, vf⟩ := triple
              cases hC : natFold (fun _ => none) (fun _ ih => stepF false ih) k cond with
              | none => rw [hC] at hA; nomatch hA
              | some lc =>
                cases lc with
                | cons _ _ => rw [hC] at hA; nomatch hA
                | nil =>
                  rw [hC] at hA
                  obtain ⟨lc', hC', hNilC⟩ := ih cond [] hC
                  rw [hNilC rfl] at hC'
                  cases hT : natFold (fun _ => none) (fun _ ih => stepF false ih) k vt with
                  | none => rw [hT] at hA; nomatch hA
                  | some lt =>
                    rw [hT] at hA
                    obtain ⟨lt', hT', hNilT⟩ := ih vt lt hT
                    cases hV : natFold (fun _ => none) (fun _ ih => stepF false ih) k vf with
                    | none => rw [hV] at hA; nomatch hA
                    | some lf =>
                      rw [hV] at hA
                      dsimp only at hA
                      obtain ⟨lf', hV', hNilV⟩ := ih vf lf hV
                      rw [hC', hT', hV']
                      dsimp only
                      by_cases hEq' : (lt' == lf') = true
                      · simp only [hEq', ↓reduceIte]
                        refine ⟨lt', rfl, ?_⟩
                        intro hAlsNil
                        subst hAlsNil
                        by_cases hEq : (lt == lf) = true
                        · simp only [hEq, ↓reduceIte, Option.some.injEq] at hA
                          exact hNilT hA
                        · simp only [hEq, Bool.false_eq_true, ↓reduceIte] at hA
                          cases hLk : lookupCond alg ctx cond with
                          | some b =>
                            rw [hLk] at hA
                            cases b with
                            | true => injection hA with hLt; exact hNilT hLt
                            | false =>
                              injection hA with hLf
                              have hLf' : lf' = [] := hNilV hLf
                              rw [hLf'] at hEq'
                              exact beq_iff_eq.mp hEq'
                          | none =>
                            rw [hLk] at hA
                            simp only [Option.some.injEq] at hA
                            exact hNilT (maxUnionHandleRef_eq_nil hA).1
                      · simp only [hEq', Bool.false_eq_true, ↓reduceIte]
                        cases hLk : lookupCond alg ctx cond with
                        | some b =>
                          cases b with
                          | true =>
                            refine ⟨lt', rfl, ?_⟩
                            intro hAlsNil; subst hAlsNil
                            by_cases hEq : (lt == lf) = true
                            · simp only [hEq, ↓reduceIte, Option.some.injEq] at hA
                              exact hNilT hA
                            · simp only [hEq, Bool.false_eq_true, ↓reduceIte, hLk, Option.some.injEq] at hA
                              exact hNilT hA
                          | false =>
                            refine ⟨lf', rfl, ?_⟩
                            intro hAlsNil; subst hAlsNil
                            by_cases hEq : (lt == lf) = true
                            · simp only [hEq, ↓reduceIte, Option.some.injEq] at hA
                              have hLf : lf = [] := by rw [← hA]; exact (beq_iff_eq.mp hEq).symm
                              exact hNilV hLf
                            · simp only [hEq, Bool.false_eq_true, ↓reduceIte, hLk, Option.some.injEq] at hA
                              exact hNilV hA
                        | none =>
                          refine ⟨minInterHandleRef lt' lf', rfl, ?_⟩
                          intro hAlsNil; subst hAlsNil
                          by_cases hEq : (lt == lf) = true
                          · simp only [hEq, ↓reduceIte, Option.some.injEq] at hA
                            have hLf : lf = [] := by rw [← hA]; exact (beq_iff_eq.mp hEq).symm
                            rw [hNilT hA, hNilV hLf]; rfl
                          · simp only [hEq, Bool.false_eq_true, ↓reduceIte, hLk, Option.some.injEq] at hA
                            obtain ⟨hLt, hLf⟩ := maxUnionHandleRef_eq_nil hA
                            rw [hNilT hLt, hNilV hLf]; rfl
          change (match some lsF, armsF false with
            | some ls0, some ls' => some (ls0 ++ ls')
            | _, _ => none) = some ls at hS
          change ∃ ls', (match some lsF', armsF true with
            | some ls0, some ls' => some (maxUnionHandleRef ls0 ls')
            | _, _ => none) = some ls' ∧ (ls = [] → ls' = [])
          cases hFA : armsF false with
          | none => rw [hFA] at hS; nomatch hS
          | some lsA =>
            rw [hFA] at hS
            injection hS with hEq; subst hEq
            obtain ⟨lsA', hFA', hNilA⟩ := hArms lsA hFA
            rw [hFA']
            refine ⟨maxUnionHandleRef lsF' lsA', rfl, ?_⟩
            intro hApp
            obtain ⟨hF0, hA0⟩ := List.append_eq_nil_iff.mp hApp
            rw [hNilF hF0, hNilA hA0]; rfl
  obtain ⟨ls', hRes, hNil⟩ := hAux (alg.sizeBound v + 1) v [] h
  rw [hNil rfl] at hRes
  exact hRes

theorem lawfulCodec_local1_lifecycle_sound {α : Type}
    (ctx : BodySpatialCtx) (c : TypedSpatialMemCodec α)
    (hLaw : LawfulTypedSpatialMemCodec ctx.body.layouts c)
    (hSpecCtx : specsMatchBodyCtx ctx [.mirTy { kind := .tuple [], layoutIdx := 0 }, c.targetTy] = true)
    (hTargetRefl : spatialTargetSpecBeq c.targetTy c.targetTy = true)
    (hLayoutMask : codecLayoutAndMaskMatchSpec ctx.body.layouts c.targetTy c.layout c.padMask = true)
    (xInit xNew : α)
    (hMirValRefl : mirValBeq 8 (c.encodeToMirVal xInit) (c.encodeToMirVal xInit) = true)
    (relOff writeAlign : Nat) (patchBytes : List AbstractByte)
    (hPatchNonEmpty : patchBytes.isEmpty = false)
    (hPatchBounds : relOff + patchBytes.length ≤ c.layout.size)
    (hPatchAlignPos : 0 < writeAlign)
    (hPatchAlignLe : writeAlign ≤ c.layout.alignBytes)
    (hPatchAlignMod : relOff % writeAlign = 0)
    (hPatchProv : bytesProvSubset patchBytes
      (nonPadBytesOfMask c.padMask (c.encodeValToMem xInit)) = true)
    (hPatchSplice :
      (c.encodeValToMem xInit).take relOff ++ patchBytes ++
        (c.encodeValToMem xInit).drop (relOff + patchBytes.length) =
      c.encodeValToMem xNew)
    (hHandleFreeInit : collectHandleRefs stdValAlg (c.encodeToSymVal xInit) = some [])
    (hHandleFreeNew : collectHandleRefs stdValAlg (c.encodeToSymVal xNew) = some [])
    (m0 : V2026ByteMem)
    (hFresh : v2026AllocIdsLt m0.allocs m0.nextAllocId = true)
    (hNoProvRef : anyAllocBytesRefAlloc m0.nextAllocId m0.allocs = false)
    (otherPlace : V2026MemPlace) (otherLen otherAlign : Nat)
    (hOtherId : otherPlace.allocId ≠ m0.nextAllocId) :
    let initSymVal := c.encodeToSymVal xInit
    let newSymVal := c.encodeToSymVal xNew
    let st0 : PaddedSymMemState :=
      { sym :=
          { locals := [⟨StdVal.unit, .unborrowed⟩, ⟨initSymVal, .mutLocked 0⟩]
            loans := [⟨0, .activeMut, ⟨initSymVal, .unborrowed⟩, .direct (.localReg 1) []⟩]
            regionGroups := []
            regionDeposits := []
            spatial := []
            nextSpatialTag := 1 }
        mirLocalTypes := [.mirTy { kind := .tuple [], layoutIdx := 0 }, c.targetTy]
        mirLocals := [.immediate .unit, .immediate (c.encodeToMirVal xInit)]
        mem := m0
        memBlocks := []
        promotedLocals := [] }
    let place : V2026MemPlace := ⟨m0.nextAllocId, 0⟩
    ∃ stPinned stMut stReabsorbed stEnded stDealloc,
      freezePaddedToMem ctx 0 c hLaw st0 = .ok stPinned ∧
      stPinned.mirLocals = [.immediate .unit, .indirect place] ∧
      mutatePaddedInMem ctx 1 1 relOff writeAlign patchBytes stPinned = .ok stMut ∧
      readV2026Bytes stMut.mem place c.layout.size c.layout.alignBytes =
        some (c.encodeValToMem xNew) ∧
      loadV2026Typed ctx.body.layouts c.targetTy.toMirTy stMut.mem place
        c.layout.size c.layout.alignBytes = some (c.encodeToMirVal xNew) ∧
      reabsorbPaddedFromMem ctx 0 stMut = .ok stReabsorbed ∧
      endPaddedLoan ctx 0 stReabsorbed = .ok stEnded ∧
      getLocal stdValAlg 1 stEnded.sym = some newSymVal ∧
      deallocatePromotedLocal ctx 1 stEnded = .ok stDealloc ∧
      stDealloc.mirLocals = [.immediate .unit, .dead] ∧
      stDealloc.promotedLocals = [] ∧
      readV2026Bytes stPinned.mem otherPlace otherLen otherAlign =
        readV2026Bytes m0 otherPlace otherLen otherAlign ∧
      readV2026Bytes stMut.mem otherPlace otherLen otherAlign =
        readV2026Bytes m0 otherPlace otherLen otherAlign ∧
      readV2026Bytes stReabsorbed.mem otherPlace otherLen otherAlign =
        readV2026Bytes m0 otherPlace otherLen otherAlign ∧
      readV2026Bytes stDealloc.mem otherPlace otherLen otherAlign =
        readV2026Bytes m0 otherPlace otherLen otherAlign := by
  intro initSymVal newSymVal st0 place
  obtain ⟨hInitLen, hInitNonPad, hInitProv, hInitMatch, _, _, _, hInitDecSym⟩ :=
    hLaw.encodeProps xInit
  obtain ⟨hNewLen, hNewNonPad, hNewProv, hNewMatch, hNewDecMir, hNewDecMem, _, hNewDecSym⟩ :=
    hLaw.encodeProps xNew
  let initRaw := c.encodeValToMem xInit
  let newRaw := c.encodeValToMem xNew
  let allocUninit : V2026ByteAlloc :=
    ⟨m0.nextAllocId, c.layout.alignBytes, .mut, List.replicate c.layout.size .uninit, true⟩
  let allocPinned : V2026ByteAlloc :=
    ⟨m0.nextAllocId, c.layout.alignBytes, .mut, initRaw, true⟩
  let allocMut : V2026ByteAlloc :=
    ⟨m0.nextAllocId, c.layout.alignBytes, .mut, newRaw, true⟩
  let allocDealloc : V2026ByteAlloc :=
    ⟨m0.nextAllocId, c.layout.alignBytes, .mut, newRaw, false⟩
  let memPinned : V2026ByteMem := ⟨m0.nextAllocId + 1, m0.allocs ++ [allocPinned]⟩
  let memMut : V2026ByteMem := ⟨m0.nextAllocId + 1, m0.allocs ++ [allocMut]⟩
  let memDealloc : V2026ByteMem := ⟨m0.nextAllocId + 1, m0.allocs ++ [allocDealloc]⟩
  have hFindUninit : findV2026Alloc m0.nextAllocId (m0.allocs ++ [allocUninit]) = some allocUninit :=
    findV2026Alloc_append_lt m0.allocs allocUninit hFresh
  have hReplPinned : replaceV2026Alloc allocPinned (m0.allocs ++ [allocUninit]) =
      m0.allocs ++ [allocPinned] :=
    replaceV2026Alloc_append_lt m0.allocs allocUninit allocPinned hFresh rfl
  have hFindPinned : findV2026Alloc m0.nextAllocId (m0.allocs ++ [allocPinned]) = some allocPinned :=
    findV2026Alloc_append_lt m0.allocs allocPinned hFresh
  have hReplMut : replaceV2026Alloc allocMut (m0.allocs ++ [allocPinned]) =
      m0.allocs ++ [allocMut] :=
    replaceV2026Alloc_append_lt m0.allocs allocPinned allocMut hFresh rfl
  have hFindMut : findV2026Alloc m0.nextAllocId (m0.allocs ++ [allocMut]) = some allocMut :=
    findV2026Alloc_append_lt m0.allocs allocMut hFresh
  have hReplDealloc : replaceV2026Alloc allocDealloc (m0.allocs ++ [allocMut]) =
      m0.allocs ++ [allocDealloc] :=
    replaceV2026Alloc_append_lt m0.allocs allocMut allocDealloc hFresh rfl
  have hAlignNe0 : (c.layout.alignBytes == 0) = false := by
    have hP := hLaw.alignPos
    cases hA : c.layout.alignBytes with
    | zero => omega
    | succ _ => rfl
  have hWAlignNe0 : (writeAlign == 0) = false := by
    cases hA : writeAlign with
    | zero => omega
    | succ _ => rfl
  have hInitLen' : initRaw.length = c.layout.size := hInitLen
  have hNewLen' : newRaw.length = c.layout.size := hNewLen
  have hInitNonEmpty : initRaw.isEmpty = false := by
    have hSz := hLaw.sizePos
    cases hR : initRaw with
    | nil => rw [hR] at hInitLen'; simp at hInitLen'; omega
    | cons _ _ => rfl
  have hFreshId : freshPromotedAllocId m0.nextAllocId st0 = true := by
    unfold freshPromotedAllocId
    rw [findV2026Alloc_none_of_lt m0.allocs m0.nextAllocId hFresh, hNoProvRef]
    rfl
  have hNoChildInit : noActiveChildLoanEdgesIn stdValAlg 0 st0.sym.loans = true := by
    simp only [st0, noActiveChildLoanEdgesIn, List.foldr, activeTargetLeaves, BackTarget.direct,
      hasParentLoanEdge, OwnerRef.beq, Bool.false_or, Bool.and_false, Bool.false_eq_true,
      ↓reduceIte]
  have hWriteInit :
      writeV2026Bytes (allocV2026Stack m0 c.layout.size c.layout.alignBytes).2 place
        c.layout.alignBytes initRaw = some memPinned := by
    unfold writeV2026Bytes allocV2026Stack
    dsimp only [place]
    rw [hInitNonEmpty]
    simp only [Bool.false_eq_true, ↓reduceIte]
    change (match findV2026Alloc m0.nextAllocId (m0.allocs ++ [allocUninit]) with
      | none => none
      | some a => _) = some memPinned
    rw [hFindUninit]
    simp only [allocUninit, v2026InBounds, v2026Aligned, List.length_replicate, hInitLen',
      Nat.zero_add, Nat.ble_eq.mpr (Nat.le_refl _), hAlignNe0, Nat.zero_mod, Nat.beq_refl,
      Bool.false_eq_true, ↓reduceIte, Bool.and_self, Bool.not_true, Bool.false_or,
      List.take_zero, List.nil_append]
    have hDropAll : (List.replicate c.layout.size AbstractByte.uninit).drop c.layout.size = [] := by
      rw [List.drop_eq_nil_iff, List.length_replicate]
      exact Nat.le_refl _
    rw [hDropAll, List.append_nil]
    exact congrArg (fun xs => some ({ nextAllocId := m0.nextAllocId + 1, allocs := xs } : V2026ByteMem))
      hReplPinned
  let blk : PaddedSpatialBlock :=
    { blockId := 1
      originLoan := 0
      ownerLocal := 1
      perm := .readWrite
      provenanceTag := 1
      activeSubSplits := 0
      layout := c.layout
      padMask := c.padMask
      targetTy := c.targetTy
      place := place
      codecId := c.codecId
      reabsorbBytes := fun bs =>
        if !Nat.beq bs.length c.layout.size ||
           !nonPadBytesInitialized c.padMask bs ||
           !c.provCheck bs then
          none
        else
          match c.decodeValFromMem bs with
          | none => none
          | some x' =>
            let vSym' := c.encodeToSymVal x'
            let vMir' := c.encodeToMirVal x'
            if valAndBytesMatchTargetSpec false ctx.body.layouts c.targetTy vMir' bs then
              some (vSym', vMir')
            else
              none }
  let prom : PromotedLocalEntry :=
    { localId := 1
      targetTy := c.targetTy
      place := place
      layout := c.layout
      padMask := c.padMask
      codecId := c.codecId
      encodeSymToBytes := fun sv =>
        match c.decodeFromSymVal sv with
        | none => none
        | some x' =>
          if stdValEq (c.encodeToSymVal x') sv then
            some (c.encodeValToMem x', c.encodeToMirVal x')
          else none }
  let stPinned : PaddedSymMemState :=
    { sym :=
        { st0.sym with
          loans := [⟨0, .spatialPinned 1 (paddedLoanWitnessCodec c.codecId),
                     ⟨initSymVal, .unborrowed⟩, .direct (.localReg 1) []⟩]
          nextSpatialTag := 2 }
      mirLocalTypes := st0.mirLocalTypes
      mirLocals := [.immediate .unit, .indirect place]
      mem := memPinned
      memBlocks := [blk]
      promotedLocals := [prom] }
  let stMut : PaddedSymMemState := { stPinned with mem := memMut }
  let stReabsorbed : PaddedSymMemState :=
    { stMut with
      sym := { stPinned.sym with
        loans := [⟨0, .activeMut, ⟨newSymVal, .unborrowed⟩, .direct (.localReg 1) []⟩] }
      memBlocks := [] }
  let stEndedSym : SymState StdVal :=
    { locals := [⟨StdVal.unit, .unborrowed⟩, ⟨newSymVal, .unborrowed⟩]
      loans := [⟨0, .ended, ⟨newSymVal, .unborrowed⟩, .direct (.localReg 1) []⟩]
      regionGroups := []
      regionDeposits := []
      spatial := []
      nextSpatialTag := 2 }
  let stEnded : PaddedSymMemState := { stReabsorbed with sym := stEndedSym }
  let stDealloc : PaddedSymMemState :=
    { stEnded with
      sym := { stEndedSym with locals := [⟨StdVal.unit, .unborrowed⟩, ⟨StdVal.unit, .unborrowed⟩] }
      mirLocals := [.immediate .unit, .dead]
      mem := memDealloc
      promotedLocals := [] }
  have hFreeze : freezePaddedToMem ctx 0 c hLaw st0 = .ok stPinned := by
    unfold freezePaddedToMem
    dsimp only [st0]
    rw [hSpecCtx, hLaw.notRef]
    simp only [List.length_cons, List.length_nil, Nat.beq_refl, beq_self_eq_true, Bool.not_true,
      Bool.false_or, Bool.false_eq_true, ↓reduceIte, hasUniqueLoanId, countLoanId,
      findLoan, LoanPhase.isActiveMut, isUnborrowed, noActiveChildRegionEdges,
      countPaddedBlocksForLoan, hasPaddedBlockId, countBlocksForLoan, hasSpatialBlockId,
      loanDirectLocal?, BackTarget.direct, List.foldr, listGet?]
    have hNoChildInit' : noActiveChildLoanEdgesIn stdValAlg 0
        [⟨0, .activeMut, ⟨initSymVal, .unborrowed⟩,
          { steps := [BackTargetStep.direct (.localReg 1) []] }⟩] = true := hNoChildInit
    rw [hNoChildInit']
    have hInitDecSym' : c.decodeFromSymVal initSymVal = some xInit := hInitDecSym
    have hInitEncSym : c.encodeToSymVal xInit = initSymVal := rfl
    have hWriteInit' :
        writeV2026Bytes (allocV2026Stack m0 c.layout.size c.layout.alignBytes).2
          (allocV2026Stack m0 c.layout.size c.layout.alignBytes).1
          c.layout.alignBytes (c.encodeValToMem xInit) = some memPinned := hWriteInit
    have hFreshId' := hFreshId
    dsimp only [st0, BackTarget.direct] at hFreshId'
    simp only [Bool.not_true, Bool.or_false, Bool.false_eq_true,
      ↓reduceIte, bne_self_eq_false, toEntries, List.isEmpty, countSpatialBlockId,
      hTargetRefl, hLayoutMask, hMirValRefl, Nat.beq_refl, hInitDecSym', hInitEncSym, stdValEq_refl,
      hInitLen, hLaw.padMaskLen, hInitNonPad, hInitProv, hInitMatch, hasPromotedLocal, List.foldr,
      hFreshId', hWriteInit']
    rfl
  have hReadPinned :
      readV2026Bytes memPinned place c.layout.size c.layout.alignBytes = some initRaw := by
    unfold readV2026Bytes
    dsimp only [memPinned, place]
    rw [hFindPinned]
    simp only [allocPinned, v2026InBounds, v2026Aligned, hInitLen', Nat.zero_add,
      Nat.ble_eq.mpr (Nat.le_refl _), hAlignNe0, Nat.zero_mod, Nat.beq_refl,
      Bool.false_eq_true, ↓reduceIte, Bool.and_self, Bool.not_true, Bool.false_or,
      List.drop_zero, List.take_of_length_le (Nat.le_of_eq hInitLen')]
  have hWriteMut :
      writeV2026Bytes memPinned ⟨place.allocId, relOff⟩ writeAlign patchBytes = some memMut := by
    unfold writeV2026Bytes
    rw [hPatchNonEmpty]
    simp only [Bool.false_eq_true, ↓reduceIte, memPinned, place]
    rw [hFindPinned]
    simp only [allocPinned, v2026InBounds, v2026Aligned, hInitLen', Nat.ble_eq.mpr hPatchBounds,
      hWAlignNe0, Nat.ble_eq.mpr hPatchAlignLe, hPatchAlignMod, Nat.beq_refl,
      Bool.false_eq_true, ↓reduceIte, Bool.and_self, Bool.not_true, Bool.false_or]
    rw [hPatchSplice]
    exact congrArg (fun xs => some ({ nextAllocId := m0.nextAllocId + 1, allocs := xs } : V2026ByteMem))
      hReplMut
  have hMutate :
      mutatePaddedInMem ctx 1 1 relOff writeAlign patchBytes stPinned = .ok stMut := by
    unfold mutatePaddedInMem
    dsimp only [stPinned, st0]
    rw [hSpecCtx, hPatchNonEmpty]
    simp only [List.length_cons, List.length_nil, Nat.beq_refl, beq_self_eq_true, Bool.not_true,
      Bool.false_or, Bool.false_eq_true, Bool.and_true, ↓reduceIte, findPaddedSpatialBlock, blk,
      prom, hasUniqueLoanId, countLoanId, findLoan, paddedLoanWitnessCodec,
      Nat.ble_eq.mpr hPatchBounds, Nat.ble_eq.mpr hPatchAlignLe, hWAlignNe0, place, Nat.zero_add,
      hPatchAlignMod, slotMatchesIndirection, otherPromotedUsesAlloc, otherIndirectLocalUsesAlloc,
      List.foldr, listGet?]
    rw [hReadPinned]
    dsimp only
    rw [hPatchProv]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    change (match writeV2026Bytes memPinned ⟨place.allocId, relOff⟩ writeAlign patchBytes with
      | none => EvalOutcome.fail
      | some mem' => EvalOutcome.ok { stPinned with mem := mem' }) = EvalOutcome.ok stMut
    rw [hWriteMut]
  have hReadMut :
      readV2026Bytes stMut.mem place c.layout.size c.layout.alignBytes = some newRaw := by
    unfold readV2026Bytes
    dsimp only [stMut, memMut, place]
    rw [hFindMut]
    simp only [allocMut, v2026InBounds, v2026Aligned, hNewLen', Nat.zero_add,
      Nat.ble_eq.mpr (Nat.le_refl _), hAlignNe0, Nat.zero_mod, Nat.beq_refl,
      Bool.false_eq_true, ↓reduceIte, Bool.and_self, Bool.not_true, Bool.false_or,
      List.drop_zero, List.take_of_length_le (Nat.le_of_eq hNewLen')]
  have hLoadMut :
      loadV2026Typed ctx.body.layouts c.targetTy.toMirTy stMut.mem place
        c.layout.size c.layout.alignBytes = some (c.encodeToMirVal xNew) := by
    unfold loadV2026Typed
    rw [hReadMut]
    exact hNewDecMir
  have hRep : replaceableVal stdValAlg stMut.sym.loans initSymVal newSymVal = true := by
    have hNewR : collectHandleRefsListIn stdValAlg false [] [newSymVal] = some [] := by
      unfold collectHandleRefsListIn
      simp only [List.foldr]
      have hHF : collectHandleRefsIn stdValAlg false [] newSymVal = some [] := hHandleFreeNew
      rw [hHF]
      rfl
    have hOldR : collectHandleRefsListIn stdValAlg true [] [initSymVal] = some [] := by
      unfold collectHandleRefsListIn
      simp only [List.foldr]
      rw [collectHandleRefsIn_true_empty_of_false_empty stdValAlg [] initSymVal hHandleFreeInit]
      rfl
    unfold replaceableVal replaceableVals
    dsimp only
    rw [hNewR, hOldR]
    rfl
  have hReab : reabsorbPaddedFromMem ctx 0 stMut = .ok stReabsorbed := by
    unfold reabsorbPaddedFromMem
    dsimp only [stMut, stPinned, st0]
    rw [hSpecCtx]
    simp only [List.length_cons, List.length_nil, Nat.beq_refl, beq_self_eq_true, Bool.not_true,
      Bool.false_or, Bool.false_eq_true, ↓reduceIte, hasUniqueLoanId, countLoanId, findLoan,
      loanDirectLocal?, BackTarget.direct, findPaddedSpatialBlock, blk, prom, paddedLoanWitnessCodec,
      countPaddedBlocksForLoan, slotMatchesIndirection, otherPromotedUsesAlloc,
      otherIndirectLocalUsesAlloc, listGet?, List.foldr, hTargetRefl]
    change (match readV2026Bytes stMut.mem place c.layout.size c.layout.alignBytes with
      | none => EvalOutcome.fail
      | some rawBytes => _) = .ok stReabsorbed
    rw [hReadMut]
    dsimp only
    have hNewNonPad' : nonPadBytesInitialized c.padMask newRaw = true := hNewNonPad
    have hNewProv' : c.provCheck newRaw = true := hNewProv
    have hNewDecMem' : c.decodeValFromMem newRaw = some xNew := hNewDecMem
    have hNewMatch' : valAndBytesMatchTargetSpec false ctx.body.layouts c.targetTy
        (c.encodeToMirVal xNew) newRaw = true :=
      valAndBytesMatchTargetSpec_false_of_true _ _ _ _ hNewMatch
    have hNewDecMir' :
        decodeValueFromBytes defaultCodecFuel ctx.body.layouts c.targetTy.toMirTy newRaw =
          some (c.encodeToMirVal xNew) := hNewDecMir
    have hRep' : replaceableVal stdValAlg
        [⟨0, .spatialPinned 1 (paddedLoanWitnessCodec c.codecId),
          ⟨initSymVal, .unborrowed⟩, { steps := [BackTargetStep.direct (.localReg 1) []] }⟩]
        initSymVal (c.encodeToSymVal xNew) = true := hRep
    dsimp only [paddedLoanWitnessCodec] at hRep'
    simp only [hNewNonPad', hNewLen', hNewProv', hNewDecMem', hNewMatch', hNewDecMir',
      Nat.beq_refl, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte, hRep']
    rfl
  have hEnd : endPaddedLoan ctx 0 stReabsorbed = .ok stEnded := by
    have hEndSym : endLoanInState stdValAlg 0 stReabsorbed.sym = .ok stEndedSym := by
      have hNoChild : noActiveChildLoanEdgesIn stdValAlg 0
          [⟨0, .activeMut, ⟨newSymVal, .unborrowed⟩, .direct (.localReg 1) []⟩] = true := by
        simp only [noActiveChildLoanEdgesIn, List.foldr, activeTargetLeaves, BackTarget.direct,
          hasParentLoanEdge, OwnerRef.beq, Bool.false_or, Bool.and_false, Bool.false_eq_true,
          ↓reduceIte]
      have hDeact :
          deactivateLoan stdValAlg 0
            [⟨0, .activeMut, ⟨newSymVal, .unborrowed⟩, .direct (.localReg 1) []⟩] =
          some (⟨0, .activeMut, ⟨newSymVal, .unborrowed⟩, .direct (.localReg 1) []⟩,
            [⟨0, .ended, ⟨newSymVal, .unborrowed⟩, .direct (.localReg 1) []⟩]) := by
        unfold deactivateLoan
        rw [hNoChild]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.foldr, beq_self_eq_true,
          isUnborrowed, activeTargetHasSpecial, BackTarget.direct, LoanPhase.isActive]
        rfl
      have hRepEnd : replaceableVals stdValAlg
          [⟨0, .ended, ⟨newSymVal, .unborrowed⟩, .direct (.localReg 1) []⟩]
          [initSymVal] [newSymVal] = true := by
        have hNewR : collectHandleRefsListIn stdValAlg false [] [newSymVal] = some [] := by
          unfold collectHandleRefsListIn
          simp only [List.foldr]
          have hHF : collectHandleRefsIn stdValAlg false [] newSymVal = some [] := hHandleFreeNew
          rw [hHF]
          rfl
        have hOldR : collectHandleRefsListIn stdValAlg true [] [initSymVal] = some [] := by
          unfold collectHandleRefsListIn
          simp only [List.foldr]
          rw [collectHandleRefsIn_true_empty_of_false_empty stdValAlg [] initSymVal hHandleFreeInit]
          rfl
        unfold replaceableVals
        dsimp only
        rw [hNewR, hOldR]
        rfl
      let stDeactSym : SymState StdVal :=
        { locals := [⟨StdVal.unit, .unborrowed⟩, ⟨initSymVal, .mutLocked 0⟩]
          loans := [⟨0, .ended, ⟨newSymVal, .unborrowed⟩, .direct (.localReg 1) []⟩]
          regionGroups := []
          regionDeposits := []
          spatial := []
          nextSpatialTag := 2 }
      have hWb : writebackLeaves stdValAlg 0 (.direct (.localReg 1) []) newSymVal
          [(.localReg 1, [])] stDeactSym = some stEndedSym := by
        unfold writebackLeaves
        change (if !true then none
          else
            match some ([initSymVal], [newSymVal]) with
            | none => none
            | some (olds, news) =>
              if !replaceableVals stdValAlg stDeactSym.loans olds news then none
              else
                match writebackLeavesPass stdValAlg 0 (.direct (.localReg 1) [])
                    [(.localReg 1, [])] true newSymVal [(.localReg 1, [])] stDeactSym with
                | some st1 =>
                  writebackLeavesPass stdValAlg 0 (.direct (.localReg 1) [])
                    [(.localReg 1, [])] false newSymVal [(.localReg 1, [])] st1
                | none => none) = some stEndedSym
        dsimp only
        have hRepEnd' : replaceableVals stdValAlg stDeactSym.loans [initSymVal] [newSymVal] = true :=
          hRepEnd
        rw [hRepEnd']
        rfl
      unfold endLoanInState
      dsimp only [stReabsorbed, stMut, stPinned, st0]
      simp only [noActiveChildRegionEdges, List.foldr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [hDeact]
      dsimp only
      have hValTgt : validateBackTarget stdValAlg (.direct (.localReg 1) []) newSymVal = true := rfl
      rw [hValTgt]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hLeaves : dedupOwnerPaths (targetLeaves (Val := StdVal) (.direct (.localReg 1) [])) =
          [(.localReg 1, [])] := rfl
      rw [hLeaves]
      have hWb' :
          writebackLeaves stdValAlg 0 (.direct (.localReg 1) []) newSymVal
            [(.localReg 1, [])]
            { locals := [⟨StdVal.unit, .unborrowed⟩, ⟨initSymVal, .mutLocked 0⟩]
              loans := [⟨0, .ended, ⟨newSymVal, .unborrowed⟩, .direct (.localReg 1) []⟩]
              regionGroups := []
              regionDeposits := []
              spatial := []
              nextSpatialTag := 2 } = some stEndedSym := hWb
      rw [hWb']
      rfl
    unfold endPaddedLoan
    dsimp only [stReabsorbed, stMut, stPinned, st0]
    rw [hSpecCtx]
    simp only [List.length_cons, List.length_nil, Nat.beq_refl, Bool.not_true, Bool.false_or,
      Bool.false_eq_true, ↓reduceIte]
    change (match endLoanInState stdValAlg 0 stReabsorbed.sym with
      | .fail => EvalOutcome.fail
      | .ok sym' => syncPromotedLocalsToMem ctx { stReabsorbed with sym := sym' }) = .ok stEnded
    rw [hEndSym]
    unfold syncPromotedLocalsToMem
    dsimp only [stReabsorbed, stMut, stPinned, st0]
    rw [hSpecCtx]
    have hGetLoc1 : getLocal stdValAlg 1 stEndedSym = some newSymVal := rfl
    have hLenSym : stEndedSym.locals.length = 2 := rfl
    have hNewDecSym' : c.decodeFromSymVal newSymVal = some xNew := hNewDecSym
    have hNewEncSym : c.encodeToSymVal xNew = newSymVal := rfl
    have hReadMut' : readV2026Bytes memMut place c.layout.size c.layout.alignBytes = some newRaw :=
      hReadMut
    have hNewNonPad' : nonPadBytesInitialized c.padMask newRaw = true := hNewNonPad
    have hNewMatch' : valAndBytesMatchTargetSpec false ctx.body.layouts c.targetTy
        (c.encodeToMirVal xNew) newRaw = true :=
      valAndBytesMatchTargetSpec_false_of_true _ _ _ _ hNewMatch
    have hSameNew : sameAtNonPad c.padMask (c.encodeValToMem xNew) newRaw = true :=
      sameAtNonPad_refl c.padMask newRaw (hLaw.padMaskLen.trans hNewLen'.symm)
    simp only [hLenSym, List.length_cons, List.length_nil, Nat.beq_refl, Bool.not_true, Bool.false_or,
      Bool.false_eq_true, ↓reduceIte, syncPromotedLocalsToMem.go, prom,
      anyBlockTargetsLocal, List.foldr, slotMatchesIndirection, listGet?, hGetLoc1,
      hNewDecSym', hNewEncSym, stdValEq_refl, hReadMut', hNewNonPad', hSameNew, hNewMatch',
      Bool.and_self]
    rfl
  have hDealloc : deallocatePromotedLocal ctx 1 stEnded = .ok stDealloc := by
    have hOtherRefAux : ∀ (xs : List V2026ByteAlloc),
        anyAllocBytesRefAlloc m0.nextAllocId xs = false →
        otherLiveAllocRefsAlloc m0.nextAllocId (xs ++ [allocMut]) = false := by
      intro xs
      induction xs with
      | nil =>
        intro _
        simp [otherLiveAllocRefsAlloc, allocMut]
      | cons a rest ih =>
        intro hNoP
        unfold anyAllocBytesRefAlloc at hNoP
        simp only [List.foldr, Bool.or_eq_false_iff] at hNoP
        unfold otherLiveAllocRefsAlloc
        simp only [List.cons_append, List.foldr, Bool.or_eq_false_iff]
        refine ⟨?_, ih hNoP.2⟩
        cases hLive : a.live with
        | false => rfl
        | true =>
          rw [hLive, Bool.true_and] at hNoP
          simp [hNoP.1]
    have hOtherRef : otherLiveAllocRefsAlloc m0.nextAllocId (m0.allocs ++ [allocMut]) = false :=
      hOtherRefAux m0.allocs hNoProvRef
    have hDeallocMem : deallocateV2026Stack memMut place = some memDealloc := by
      unfold deallocateV2026Stack
      dsimp only [memMut, place]
      rw [hFindMut]
      dsimp only [allocMut]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact congrArg (fun xs => some ({ nextAllocId := m0.nextAllocId + 1, allocs := xs } : V2026ByteMem))
        hReplDealloc
    unfold deallocatePromotedLocal
    dsimp only [stEnded, stReabsorbed, stMut, stPinned, st0, stEndedSym]
    rw [hSpecCtx]
    have h10 : Nat.beq 1 0 = false := rfl
    have hOtherInd : otherIndirectLocalUsesAlloc 1 m0.nextAllocId
        [.immediate .unit, .indirect place] = false := rfl
    have hOtherRefMut : otherLiveAllocRefsAlloc m0.nextAllocId memMut.allocs = false := hOtherRef
    simp only [List.length_cons, List.length_nil, Nat.beq_refl, h10, Bool.not_true,
      Bool.false_and, Bool.or_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
      listGet?, listSet?, prom, place, LoanPhase.isEnded,
      isUnborrowed, toEntries, List.isEmpty, List.foldr, List.filter,
      anyBlockUsesAlloc, otherPromotedUsesAlloc, hOtherInd,
      removePromotedLocal, hOtherRefMut, hDeallocMem]
    rfl
  have hFrPinned :
      readV2026Bytes stPinned.mem otherPlace otherLen otherAlign =
        readV2026Bytes m0 otherPlace otherLen otherAlign := by
    unfold readV2026Bytes
    dsimp only [stPinned, memPinned]
    rw [findV2026Alloc_append_ne m0.allocs allocPinned otherPlace.allocId hOtherId]
  have hFrMut :
      readV2026Bytes stMut.mem otherPlace otherLen otherAlign =
        readV2026Bytes m0 otherPlace otherLen otherAlign := by
    unfold readV2026Bytes
    dsimp only [stMut, memMut]
    rw [findV2026Alloc_append_ne m0.allocs allocMut otherPlace.allocId hOtherId]
  have hFrDealloc :
      readV2026Bytes stDealloc.mem otherPlace otherLen otherAlign =
        readV2026Bytes m0 otherPlace otherLen otherAlign := by
    unfold readV2026Bytes
    dsimp only [stDealloc, memDealloc]
    rw [findV2026Alloc_append_ne m0.allocs allocDealloc otherPlace.allocId hOtherId]
  exact ⟨stPinned, stMut, stReabsorbed, stEnded, stDealloc,
    hFreeze, rfl, hMutate, hReadMut, hLoadMut, hReab, hEnd, rfl, hDealloc,
    rfl, rfl, hFrPinned, hFrMut, hFrMut, hFrDealloc⟩

/-- Sub-slice projection for `readV2026Bytes` at 1-byte alignment. -/
theorem readV2026Bytes_subslice_of_read (mem : V2026ByteMem)
    (aid len align subOff subLen : Nat) (bs : List AbstractByte)
    (hRead : readV2026Bytes mem ⟨aid, 0⟩ len align = some bs)
    (hSub : subOff + subLen ≤ len) :
    readV2026Bytes mem ⟨aid, subOff⟩ subLen 1 = some ((bs.drop subOff).take subLen) := by
  unfold readV2026Bytes at hRead ⊢
  cases hF : findV2026Alloc aid mem.allocs with
  | none => rw [hF] at hRead; nomatch hRead
  | some a =>
    rw [hF] at hRead
    simp only [List.drop_zero] at hRead
    by_cases hBad : (!a.live || !v2026InBounds a 0 len || !v2026Aligned a 0 align) = true
    · simp only [hBad, ↓reduceIte] at hRead; nomatch hRead
    · simp only [hBad] at hRead
      injection hRead with hEq
      have hFalse : (!a.live || !v2026InBounds a 0 len || !v2026Aligned a 0 align) = false :=
        Bool.eq_false_iff.mpr hBad
      simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at hFalse
      obtain ⟨⟨hLive, hIb⟩, hAl⟩ := hFalse
      have hLen : len ≤ a.bytes.length := by
        have := Nat.ble_eq.mp hIb; omega
      have hAlPos : 1 ≤ a.alignBytes := by
        unfold v2026Aligned at hAl
        cases hA : align with
        | zero => simp [hA] at hAl
        | succ _ =>
          simp only [hA, beq_iff_eq, Nat.add_one_ne_zero, ↓reduceIte, Bool.and_eq_true] at hAl
          have := Nat.ble_eq.mp hAl.1; omega
      have hSlice : (a.bytes.drop subOff).take subLen = (bs.drop subOff).take subLen := by
        rw [← hEq, List.drop_take, List.take_take, Nat.min_eq_left (by omega : subLen ≤ len - subOff)]
      have hNotBad2 : (!a.live || !v2026InBounds a subOff subLen || !v2026Aligned a subOff 1) = false := by
        simp only [hLive, v2026InBounds, v2026Aligned,
          Nat.ble_eq.mpr (by omega : subOff + subLen ≤ a.bytes.length),
          Nat.ble_eq.mpr hAlPos, Nat.mod_one, Nat.beq_refl]
        rfl
      dsimp only
      simp only [hNotBad2, Bool.false_eq_true, ↓reduceIte, hSlice]

/-- **End-to-end soundness for padded `#[repr(C)] (u8, [pad; 3], u32)` on
unmodified `V2026_06_01.MirSemantics`** (directly solving the gap documented by
`Anneal.PureLift.u8U32Padded_freeze_refused`). -/
theorem paddedStruct_mem_freeze_mutate_reabsorb_sound
    (aInit : UInt8) (bInit bNew : U32Val)
    (m0 : V2026ByteMem)
    (hFresh : v2026AllocIdsLt m0.allocs m0.nextAllocId = true)
    (hNoProvRef : anyAllocBytesRefAlloc m0.nextAllocId m0.allocs = false)
    (otherPlace : V2026MemPlace) (otherLen otherAlign : Nat)
    (hOtherId : otherPlace.allocId ≠ m0.nextAllocId) :
    let initStruct : U8U32Struct := ⟨aInit, bInit⟩
    let newStruct : U8U32Struct := ⟨aInit, bNew⟩
    let initSymVal : StdVal := (paddedU8U32MemCodec 0).encodeToSymVal initStruct
    let newSymVal : StdVal := (paddedU8U32MemCodec 0).encodeToSymVal newStruct
    let bNewBytes : List AbstractByte := u32MemEncode bNew
    let st0 : PaddedSymMemState :=
      { sym :=
          { locals := [⟨StdVal.unit, .unborrowed⟩, ⟨initSymVal, .mutLocked 0⟩]
            loans := [⟨0, .activeMut, ⟨initSymVal, .unborrowed⟩, .direct (.localReg 1) []⟩]
            regionGroups := []
            regionDeposits := []
            spatial := []
            nextSpatialTag := 1 }
        mirLocalTypes := u8U32BodyCtx.specs
        mirLocals := [.immediate .unit, .immediate (paddedU8U32ToMirVal initStruct)]
        mem := m0
        memBlocks := []
        promotedLocals := [] }
    let place : V2026MemPlace := ⟨m0.nextAllocId, 0⟩
    ∃ stPinned stMut stReabsorbed stEnded stDealloc,
      freezePaddedToMem u8U32BodyCtx 0 (paddedU8U32MemCodec 0)
        paddedU8U32MemCodec_lawful_sample st0 = .ok stPinned ∧
      stPinned.mirLocals = [.immediate .unit, .indirect place] ∧
      mutatePaddedInMem u8U32BodyCtx 1 1 4 4 bNewBytes stPinned = .ok stMut ∧
      readV2026Bytes stMut.mem ⟨place.allocId, 1⟩ 3 1 = some [.uninit, .uninit, .uninit] ∧
      loadV2026Typed u8U32BodyCtx.body.layouts (u8U32Ty 0) stMut.mem place 8 4 =
        some (paddedU8U32ToMirVal newStruct) ∧
      reabsorbPaddedFromMem u8U32BodyCtx 0 stMut = .ok stReabsorbed ∧
      endPaddedLoan u8U32BodyCtx 0 stReabsorbed = .ok stEnded ∧
      getLocal stdValAlg 1 stEnded.sym = some newSymVal ∧
      deallocatePromotedLocal u8U32BodyCtx 1 stEnded = .ok stDealloc ∧
      stDealloc.mirLocals = [.immediate .unit, .dead] ∧
      stDealloc.promotedLocals = [] ∧
      readV2026Bytes stPinned.mem otherPlace otherLen otherAlign =
        readV2026Bytes m0 otherPlace otherLen otherAlign ∧
      readV2026Bytes stMut.mem otherPlace otherLen otherAlign =
        readV2026Bytes m0 otherPlace otherLen otherAlign ∧
      readV2026Bytes stReabsorbed.mem otherPlace otherLen otherAlign =
        readV2026Bytes m0 otherPlace otherLen otherAlign ∧
      readV2026Bytes stDealloc.mem otherPlace otherLen otherAlign =
        readV2026Bytes m0 otherPlace otherLen otherAlign := by
  intro initStruct newStruct initSymVal newSymVal bNewBytes st0 place
  obtain ⟨stPinned, stMut, stReabsorbed, stEnded, stDealloc,
    hFr, hMirLoc, hMut, hReadFull, hLoad, hReab, hEnd, hGet, hDealloc, hDead, hPromEmpty,
    hFr1, hFr2, hFr3, hFr4⟩ :=
    lawfulCodec_local1_lifecycle_sound u8U32BodyCtx (paddedU8U32MemCodec 0)
      paddedU8U32MemCodec_lawful_sample rfl rfl rfl initStruct newStruct
      (by simp [paddedU8U32MemCodec, paddedU8U32ToMirVal, mirValBeq, mirValBeq.go])
      4 4 bNewBytes
      rfl (by simp [bNewBytes, u32MemEncode, encodeU32LEBytes, paddedU8U32MemCodec])
      (by decide) (by decide) rfl rfl
      (by simp [paddedU8U32MemCodec, paddedU8U32Encode, bNewBytes, u32MemEncode,
        encodeU32LEBytes, initStruct, newStruct])
      rfl rfl m0 hFresh hNoProvRef otherPlace otherLen otherAlign hOtherId
  have hReadPad : readV2026Bytes stMut.mem ⟨place.allocId, 1⟩ 3 1 =
      some [.uninit, .uninit, .uninit] :=
    readV2026Bytes_subslice_of_read stMut.mem place.allocId 8 4 1 3 _ hReadFull (by decide)
  exact ⟨stPinned, stMut, stReabsorbed, stEnded, stDealloc,
    hFr, hMirLoc, hMut, hReadPad, hLoad, hReab, hEnd, hGet, hDealloc, hDead, hPromEmpty,
    hFr1, hFr2, hFr3, hFr4⟩

/-- **End-to-end soundness for provenance-carrying `#[repr(C)] (u8, [pad; 7], *mut u8)`**:
Freezes a pointer struct carrying `(expectedAllocId, expectedAllocId)`, mutates the
leading tag byte `0` in `V2026ByteMem` while preserving all 8 pointer provenance bytes
and all 7 `.uninit` padding bytes, recovers the updated struct via unmodified
`decodeValueFromBytes`, reabsorbs, ends the loan, and frames disjoint allocations. -/
theorem provPtrStruct_mem_freeze_mutate_reabsorb_sound
    (expectedAllocId : AllocId) (tagInit tagNew : UInt8) (ptrOff : U64Offset)
    (m0 : V2026ByteMem)
    (hFresh : v2026AllocIdsLt m0.allocs m0.nextAllocId = true)
    (hNoProvRef : anyAllocBytesRefAlloc m0.nextAllocId m0.allocs = false)
    (otherPlace : V2026MemPlace) (otherLen otherAlign : Nat)
    (hOtherId : otherPlace.allocId ≠ m0.nextAllocId) :
    let codec := provPtrPaddedMemCodec expectedAllocId 0
    let initS : ProvPtrStruct := ⟨tagInit, ptrOff⟩
    let newS : ProvPtrStruct := ⟨tagNew, ptrOff⟩
    let st0 : PaddedSymMemState :=
      { sym :=
          { locals := [⟨StdVal.unit, .unborrowed⟩, ⟨codec.encodeToSymVal initS, .mutLocked 0⟩]
            loans := [⟨0, .activeMut, ⟨codec.encodeToSymVal initS, .unborrowed⟩,
                       .direct (.localReg 1) []⟩]
            regionGroups := []
            regionDeposits := []
            spatial := []
            nextSpatialTag := 1 }
        mirLocalTypes := provPtrBodyCtx.specs
        mirLocals := [.immediate .unit, .immediate (codec.encodeToMirVal initS)]
        mem := m0
        memBlocks := []
        promotedLocals := [] }
    let place : V2026MemPlace := ⟨m0.nextAllocId, 0⟩
    ∃ stPinned stMut stReabsorbed stEnded,
      freezePaddedToMem provPtrBodyCtx 0 codec
        (provPtrPaddedMemCodec_lawful_sample expectedAllocId) st0 = .ok stPinned ∧
      mutatePaddedInMem provPtrBodyCtx 1 1 0 1 [.init tagNew none] stPinned = .ok stMut ∧
      readV2026Bytes stMut.mem ⟨place.allocId, 1⟩ 7 1 =
        some [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit] ∧
      loadV2026Typed provPtrBodyCtx.body.layouts (provPtrMirTy 0) stMut.mem place 16 8 =
        some (provPtrToMirVal expectedAllocId newS) ∧
      reabsorbPaddedFromMem provPtrBodyCtx 0 stMut = .ok stReabsorbed ∧
      endPaddedLoan provPtrBodyCtx 0 stReabsorbed = .ok stEnded ∧
      getLocal stdValAlg 1 stEnded.sym = some (codec.encodeToSymVal newS) ∧
      readV2026Bytes stMut.mem otherPlace otherLen otherAlign =
        readV2026Bytes m0 otherPlace otherLen otherAlign := by
  intro codec initS newS st0 place
  obtain ⟨stPinned, stMut, stReabsorbed, stEnded, _,
    hFr, _, hMut, hReadFull, hLoad, hReab, hEnd, hGet, _, _, _,
    _, hFrMut, _, _⟩ :=
    lawfulCodec_local1_lifecycle_sound provPtrBodyCtx codec
      (provPtrPaddedMemCodec_lawful_sample expectedAllocId) rfl rfl rfl initS newS
      (by simp [codec, provPtrPaddedMemCodec, provPtrToMirVal, mirValBeq, mirValBeq.go])
      0 1 [.init tagNew none]
      rfl (by simp [codec, provPtrPaddedMemCodec]) (by decide)
      (by simp [codec, provPtrPaddedMemCodec]) rfl rfl rfl
      rfl rfl m0 hFresh hNoProvRef otherPlace otherLen otherAlign hOtherId
  have hReadPad : readV2026Bytes stMut.mem ⟨place.allocId, 1⟩ 7 1 =
      some [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit] :=
    readV2026Bytes_subslice_of_read stMut.mem place.allocId 16 8 1 7 _ hReadFull (by decide)
  exact ⟨stPinned, stMut, stReabsorbed, stEnded,
    hFr, hMut, hReadPad, hLoad, hReab, hEnd, hGet, hFrMut⟩

/-- **Direct contrast with `Anneal.PureLift.V2026_06_01Bridge.u8U32Padded_freeze_refused`**:
on the exact same padded `(u8, [pad; 3], u32)` layout (`u8U32SampleBody`, `layoutIdx = 0`)
and symbolic state `st0.sym`, `SpatialPin.freezeToSpatialInState` refuses to freeze
(because padding bytes `[1..4)` are `.uninit` in the `ByteMem` flat byte window),
whereas `SpatialMemV2026.freezePaddedToMem` succeeds, mutates field `b` in `V2026ByteMem`,
preserves `.uninit` padding, decodes via unmodified `decodeValueFromBytes`, reabsorbs,
and retires cleanly. -/
theorem paddedStruct_succeeds_where_spatialPin_refuses
    (a : UInt8) (bInit bNew : U32Val) (ms : MachineState) (lc : Local) (path : SubPath)
    (hPlace : placeValue? ms lc path =
      some (.aggregate 0 [.scalar ⟨a.toNat, 1⟩, .scalar ⟨bInit.val, 4⟩])) :
    let initStruct : U8U32Struct := ⟨a, bInit⟩
    let initSymVal := paddedU8U32ToSymVal initStruct
    let st0 : PaddedSymMemState :=
      { sym :=
          { locals := [⟨StdVal.unit, .unborrowed⟩, ⟨initSymVal, .mutLocked 0⟩]
            loans := [⟨0, .activeMut, ⟨initSymVal, .unborrowed⟩, .direct (.localReg 1) []⟩]
            regionGroups := []
            regionDeposits := []
            spatial := []
            nextSpatialTag := 1 }
        mirLocalTypes := u8U32BodyCtx.specs
        mirLocals := [.immediate .unit, .immediate (paddedU8U32ToMirVal initStruct)]
        mem := ⟨1, []⟩
        memBlocks := []
        promotedLocals := [] }
    freezeToSpatialInState stdValAlg 0 u8U32PaddedSpatialCodec st0.sym = .fail ∧
    ∃ stPinned stMut stReabsorbed stEnded stDealloc,
      freezePaddedToMem u8U32BodyCtx 0 (paddedU8U32MemCodec 0)
        paddedU8U32MemCodec_lawful_sample st0 = .ok stPinned ∧
      mutatePaddedInMem u8U32BodyCtx 1 1 4 4 (u32MemEncode bNew) stPinned = .ok stMut ∧
      loadV2026Typed u8U32BodyCtx.body.layouts (u8U32Ty 0) stMut.mem ⟨1, 0⟩ 8 4 =
        some (paddedU8U32ToMirVal ⟨a, bNew⟩) ∧
      reabsorbPaddedFromMem u8U32BodyCtx 0 stMut = .ok stReabsorbed ∧
      endPaddedLoan u8U32BodyCtx 0 stReabsorbed = .ok stEnded ∧
      deallocatePromotedLocal u8U32BodyCtx 1 stEnded = .ok stDealloc := by
  intro initStruct initSymVal st0
  have hRefused :
      freezeToSpatialInState stdValAlg 0 u8U32PaddedSpatialCodec st0.sym = .fail := by
    have hEmbed : u8U32Embed? initSymVal =
        some (⟨a.toNat, a.toBitVec.isLt⟩, bInit) := by
      unfold u8U32Embed? initSymVal paddedU8U32ToSymVal initStruct
      have hALt : a.toNat < 256 ^ 1 := a.toBitVec.isLt
      have hBLt : bInit.val < 256 ^ 4 := bInit.property
      simp only [StdVal.pair, StdVal.nat, hALt, hBLt, ↓reduceDIte]
    exact u8U32Padded_freeze_refused (layouts := u8U32BodyCtx.body.layouts) (idx := 0)
      (l := u8U32TypeLayout) (mem := [0, 1]) rfl rfl rfl stdValAlg 0
      ⟨⟨0, .activeMut, ⟨initSymVal, .unborrowed⟩, .direct (.localReg 1) []⟩, rfl, hEmbed⟩
      hPlace
  obtain ⟨stPinned, stMut, stReabsorbed, stEnded, stDealloc,
    hFr, _, hMut, _, hLoad, hReab, hEnd, _, hDealloc, _, _, _, _, _, _⟩ :=
    paddedStruct_mem_freeze_mutate_reabsorb_sound a bInit bNew ⟨1, []⟩
      rfl rfl ⟨99, 0⟩ 4 4 (by decide)
  exact ⟨hRefused, stPinned, stMut, stReabsorbed, stEnded, stDealloc,
    hFr, hMut, hLoad, hReab, hEnd, hDealloc⟩

/-! ## 5. Fail-Closed Negative Theorems (Provenance, Padding, Auth & Pinning) -/

/-- Sample initial `PaddedSymMemState` for padded `(u8, [pad; 3], u32)`. -/
def sampleU8U32InitState : PaddedSymMemState :=
  let s0 : U8U32Struct := ⟨0x11, ⟨0x22334455, by decide⟩⟩
  let vSym := (paddedU8U32MemCodec 0).encodeToSymVal s0
  { sym :=
      { locals := [⟨StdVal.unit, .unborrowed⟩, ⟨vSym, .mutLocked 0⟩]
        loans := [⟨0, .activeMut, ⟨vSym, .unborrowed⟩, .direct (.localReg 1) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 1 }
    mirLocalTypes := u8U32BodyCtx.specs
    mirLocals := [.immediate .unit, .immediate (paddedU8U32ToMirVal s0)]
    mem := { nextAllocId := 1, allocs := [] }
    memBlocks := []
    promotedLocals := [] }

/-- Sample initial `PaddedSymMemState` for provenance-carrying `(u8, [pad; 7], *mut u8)`. -/
def sampleProvPtrInitState (expectedAllocId : AllocId) : PaddedSymMemState :=
  let codec := provPtrPaddedMemCodec expectedAllocId 0
  let s0 : ProvPtrStruct := ⟨0x10, ⟨0x1000, by decide⟩⟩
  let vSym := codec.encodeToSymVal s0
  { sym :=
      { locals := [⟨StdVal.unit, .unborrowed⟩, ⟨vSym, .mutLocked 0⟩]
        loans := [⟨0, .activeMut, ⟨vSym, .unborrowed⟩, .direct (.localReg 1) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 1 }
    mirLocalTypes := provPtrBodyCtx.specs
    mirLocals := [.immediate .unit, .immediate (codec.encodeToMirVal s0)]
    mem := { nextAllocId := 1, allocs := [] }
    memBlocks := []
    promotedLocals := [] }

/-- **Negative 1 — Non-padding `.uninit` byte rejection**: overwriting any
non-padding byte (`0, 4, 5, 6, 7`) of a pinned `(u8, [pad; 3], u32)` with
`.uninit` causes BOTH `reabsorbPaddedFromMem` AND unmodified `decodeValueFromBytes`
to fail closed. -/
theorem padded_nonpad_uninit_rejected (byteOff : Nat)
    (hNonPad : byteOff = 0 ∨ byteOff = 4 ∨ byteOff = 5 ∨ byteOff = 6 ∨ byteOff = 7) :
    ∃ stPinned mBad,
      freezePaddedToMem u8U32BodyCtx 0 (paddedU8U32MemCodec 0)
        paddedU8U32MemCodec_lawful_sample sampleU8U32InitState = .ok stPinned ∧
      writeV2026Uninit stPinned.mem ⟨1, byteOff⟩ 1 1 = some mBad ∧
      reabsorbPaddedFromMem u8U32BodyCtx 0 { stPinned with mem := mBad } = .fail ∧
      loadV2026Typed u8U32BodyCtx.body.layouts (u8U32Ty 0) mBad ⟨1, 0⟩ 8 4 = none := by
  rcases hNonPad with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- **Negative 2 — Provenance stripping rejection**: stripping provenance (`none`)
on a pointer byte causes `valAndBytesMatchTargetSpec = false` AND
`reabsorbPaddedFromMem = .fail` (even though raw `decodeValueFromBytes` alone
would fall back to an integer-derived address!). -/
theorem provPtr_provenance_stripping_rejected :
    let codec := provPtrPaddedMemCodec 7 0
    let st0 := sampleProvPtrInitState 7
    ∃ stPinned mStripped bsStripped,
      freezePaddedToMem provPtrBodyCtx 0 codec
        (provPtrPaddedMemCodec_lawful_sample 7) st0 = .ok stPinned ∧
      writeV2026Bytes stPinned.mem ⟨1, 8⟩ 1 [.init 0x00 none] = some mStripped ∧
      readV2026Bytes mStripped ⟨1, 0⟩ 16 8 = some bsStripped ∧
      valAndBytesMatchTargetSpec false provPtrBodyCtx.body.layouts
        (provPtrTargetSpec 0) (provPtrToMirVal 7 ⟨0x10, ⟨0x1000, by decide⟩⟩) bsStripped = false ∧
      reabsorbPaddedFromMem provPtrBodyCtx 0 { stPinned with mem := mStripped } = .fail := by
  intro codec st0
  let stPinned : PaddedSymMemState :=
    match freezePaddedToMem provPtrBodyCtx 0 codec (provPtrPaddedMemCodec_lawful_sample 7) st0 with
    | .ok s => s
    | .fail => st0
  let mStripped : V2026ByteMem :=
    (writeV2026Bytes stPinned.mem ⟨1, 8⟩ 1 [.init 0x00 none]).getD stPinned.mem
  let bsStripped : List AbstractByte :=
    (readV2026Bytes mStripped ⟨1, 0⟩ 16 8).getD []
  exact ⟨stPinned, mStripped, bsStripped, rfl, rfl, rfl, rfl, rfl⟩

/-- **Negative 3 — Surplus provenance forgery & `(allocId, tag)` tampering rejection**:
(a) forging a different `allocId` (`some (99, 7)`),
(b) forging a different `tag` (`some (7, 99)`),
(c) attaching surplus provenance to the non-pointer `u8` field (`0`), AND
(d) attaching surplus provenance to a `u32` scalar or padding byte
ALL fail closed under `valAndBytesMatchTargetSpec` and `reabsorbPaddedFromMem`! -/
theorem provPtr_and_scalar_provenance_forgery_rejected :
    let codec := provPtrPaddedMemCodec 7 0
    let st0 := sampleProvPtrInitState 7
    ∃ stPinned mForgeAlloc mForgeTag mSurplusField mSurplusPad,
      freezePaddedToMem provPtrBodyCtx 0 codec
        (provPtrPaddedMemCodec_lawful_sample 7) st0 = .ok stPinned ∧
      writeV2026Bytes stPinned.mem ⟨1, 8⟩ 1 [.init 0x00 (some (99, 7))] = some mForgeAlloc ∧
      reabsorbPaddedFromMem provPtrBodyCtx 0 { stPinned with mem := mForgeAlloc } = .fail ∧
      writeV2026Bytes stPinned.mem ⟨1, 8⟩ 1 [.init 0x00 (some (7, 99))] = some mForgeTag ∧
      reabsorbPaddedFromMem provPtrBodyCtx 0 { stPinned with mem := mForgeTag } = .fail ∧
      writeV2026Bytes stPinned.mem ⟨1, 0⟩ 1 [.init 0x10 (some (7, 7))] = some mSurplusField ∧
      reabsorbPaddedFromMem provPtrBodyCtx 0 { stPinned with mem := mSurplusField } = .fail ∧
      writeV2026Bytes stPinned.mem ⟨1, 1⟩ 1 [.init 0x00 (some (7, 7))] = some mSurplusPad ∧
      reabsorbPaddedFromMem provPtrBodyCtx 0 { stPinned with mem := mSurplusPad } = .fail ∧
      valAndBytesMatchTargetSpec false u8U32BodyCtx.body.layouts u32TargetSpec
        (.scalar ⟨42, 4⟩)
        [.init 42 (some (7, 7)), .init 0 none, .init 0 none, .init 0 none] = false := by
  intro codec st0
  let stPinned : PaddedSymMemState :=
    match freezePaddedToMem provPtrBodyCtx 0 codec (provPtrPaddedMemCodec_lawful_sample 7) st0 with
    | .ok s => s
    | .fail => st0
  let mForgeAlloc : V2026ByteMem :=
    (writeV2026Bytes stPinned.mem ⟨1, 8⟩ 1 [.init 0x00 (some (99, 7))]).getD stPinned.mem
  let mForgeTag : V2026ByteMem :=
    (writeV2026Bytes stPinned.mem ⟨1, 8⟩ 1 [.init 0x00 (some (7, 99))]).getD stPinned.mem
  let mSurplusField : V2026ByteMem :=
    (writeV2026Bytes stPinned.mem ⟨1, 0⟩ 1 [.init 0x10 (some (7, 7))]).getD stPinned.mem
  let mSurplusPad : V2026ByteMem :=
    (writeV2026Bytes stPinned.mem ⟨1, 1⟩ 1 [.init 0x00 (some (7, 7))]).getD stPinned.mem
  exact ⟨stPinned, mForgeAlloc, mForgeTag, mSurplusField, mSurplusPad,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Negative 4 — Unauthenticated `BodySpatialCtx` & `.ref` target rejection**:
(a) mutating a `BodySpatialCtx` so `body.localDecls` disagrees with `specs` (or
    `body.layouts` omits the claimed layout) rejects `freezePaddedToMem`, and
(b) `.ref` target specs are rejected fail-closed by `valAndBytesMatchTargetSpec`. -/
theorem unauthenticated_ctx_and_ref_target_rejected :
    let forgedDeclCtx : BodySpatialCtx :=
      { body :=
          { u8U32SampleBody with
            localDecls :=
              [ { mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 }, debugName := none }
              , { mutability := .mut, ty := u32MirTy, debugName := some "forged" } ] }
        specs := u8U32BodyCtx.specs }
    let forgedLayoutCtx : BodySpatialCtx :=
      { body := { u8U32SampleBody with layouts := { pointerBits := 64, isLittleEndian := true, entries := [] } }
        specs := u8U32BodyCtx.specs }
    let refSpec : SpatialTargetSpec :=
      .mirTy { kind := .ref .mut (.uint .u32), layoutIdx := 0 }
    bodySpatialCtxWf forgedDeclCtx = false ∧
    bodySpatialCtxWf forgedLayoutCtx = false ∧
    freezePaddedToMem forgedDeclCtx 0 (paddedU8U32MemCodec 0)
      paddedU8U32MemCodec_lawful_sample sampleU8U32InitState = .fail ∧
    specsMatchBodyCtx forgedLayoutCtx sampleU8U32InitState.mirLocalTypes = false ∧
    refSpec.isRefTarget = true ∧
    valAndBytesMatchTargetSpec false u8U32BodyCtx.body.layouts refSpec
      (.ptr ⟨1, 0⟩ 8) (encodeLittleEndianBytes 0 8 (some (1, 1))) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Negative 5 — Aliased `AllocId` / stale `nextAllocId` collision rejection**:
If `st.mem.nextAllocId` collides with an existing allocation in `st.mem.allocs`
or an allocation referenced by existing pointer provenance, `freezePaddedToMem`
fails closed. -/
theorem aliased_allocId_and_stale_nextAllocId_rejected :
    let collidingAlloc : V2026ByteAlloc := ⟨1, 4, .mut, List.replicate 4 (.init 0 none), true⟩
    let provRefAlloc : V2026ByteAlloc :=
      ⟨2, 8, .mut, encodeLittleEndianBytes 0 8 (some (1, 1)), true⟩
    let stAliased : PaddedSymMemState :=
      { sampleU8U32InitState with mem := { nextAllocId := 1, allocs := [collidingAlloc] } }
    let stProvCollision : PaddedSymMemState :=
      { sampleU8U32InitState with mem := { nextAllocId := 1, allocs := [provRefAlloc] } }
    freshPromotedAllocId 1 stAliased = false ∧
    freezePaddedToMem u8U32BodyCtx 0 (paddedU8U32MemCodec 0)
      paddedU8U32MemCodec_lawful_sample stAliased = .fail ∧
    freshPromotedAllocId 1 stProvCollision = false ∧
    freezePaddedToMem u8U32BodyCtx 0 (paddedU8U32MemCodec 0)
      paddedU8U32MemCodec_lawful_sample stProvCollision = .fail :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Negative 6 — Pinned pure-mutation blocking**: while a loan is pinned in
`V2026ByteMem`, pure reads (`readPlaceVal`), pure writes (`writePlaceVal` and
`writePaddedSymPlace`), and premature `endLoanInState` / `endPaddedLoan` all
fail closed until `reabsorbPaddedFromMem` restores `.activeMut`. -/
theorem pinned_loan_blocks_pure_mutation_until_reabsorb :
    let st0 : PaddedSymMemState :=
      let s0 : U8U32Struct := ⟨0x11, ⟨0x22334455, by decide⟩⟩
      let vSym := (paddedU8U32MemCodec 0).encodeToSymVal s0
      { sym :=
          { locals := [⟨StdVal.unit, .unborrowed⟩, ⟨vSym, .mutLocked 0⟩,
                       ⟨StdVal.refVal 0 [], .unborrowed⟩]
            loans := [⟨0, .activeMut, ⟨vSym, .unborrowed⟩, .direct (.localReg 1) []⟩]
            regionGroups := []
            regionDeposits := []
            spatial := []
            nextSpatialTag := 1 }
        mirLocalTypes :=
          u8U32BodyCtx.specs ++ [.mirTy { kind := .ref .mut (u8U32Ty 0).kind, layoutIdx := 0 }]
        mirLocals :=
          [.immediate .unit, .immediate (paddedU8U32ToMirVal s0), .immediate (.ptr ⟨0, 0⟩ 8)]
        mem := { nextAllocId := 1, allocs := [] }
        memBlocks := []
        promotedLocals := [] }
    let ctx3 : BodySpatialCtx :=
      { body :=
          { u8U32SampleBody with
            localDecls :=
              u8U32SampleBody.localDecls ++
                [{ mutability := .mut
                   ty := { kind := .ref .mut (u8U32Ty 0).kind, layoutIdx := 0 }
                   debugName := some "r" }] }
        specs :=
          u8U32BodyCtx.specs ++ [.mirTy { kind := .ref .mut (u8U32Ty 0).kind, layoutIdx := 0 }] }
    let otherVal : StdVal :=
      (paddedU8U32MemCodec 0).encodeToSymVal ⟨0x22, ⟨0xAABBCCDD, by decide⟩⟩
    ∃ stPinned,
      freezePaddedToMem ctx3 0 (paddedU8U32MemCodec 0)
        paddedU8U32MemCodec_lawful_sample st0 = .ok stPinned ∧
      readPlaceVal stdValAlg (.derefSub 2 []) stPinned.sym = none ∧
      writePlaceVal stdValAlg (.derefSub 2 []) otherVal stPinned.sym = none ∧
      writePlaceVal stdValAlg (.localSub 1 []) otherVal stPinned.sym = none ∧
      writePaddedSymPlace ctx3 (.derefSub 2 []) otherVal stPinned = .fail ∧
      endLoanInState stdValAlg 0 stPinned.sym = .fail ∧
      endPaddedLoan ctx3 0 stPinned = .fail :=
  ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-! ## 6. Authentication Soundness (`#4051` `mirTyBeq_sound` / `specsMatchBodyCtx_slot_sound`)

The boolean guards `rigidTyBeq` / `mirTyBeq` / `spatialTargetSpecBeq` /
`bodySpatialCtxWf` / `specsMatchBodyCtx` are SOUND: a `true` verdict implies
propositional equality with the real `CapturedMir` declarations, and every
successful `freezePaddedToMem` / `mutatePaddedInMem` / `reabsorbPaddedFromMem`
step runs against exactly the authenticated `ctx.specs`. -/

theorem uintTyBeq_sound {a b : UintTy} (h : uintTyBeq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | (exact absurd h (by decide))

theorem intTyBeq_sound {a b : IntTy} (h : intTyBeq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | (exact absurd h (by decide))

theorem mutabilityBeq_sound {a b : Mutability} (h : mutabilityBeq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | (exact absurd h (by decide))

theorem rigidTyBeq_sound : ∀ (fuel : Nat) {a b : RigidTy}, rigidTyBeq fuel a b = true → a = b
  | 0, _, _, h => by unfold rigidTyBeq at h; exact absurd h (by decide)
  | fuel + 1, a, b, h => by
    have ih := @rigidTyBeq_sound fuel
    have hGo : ∀ ks1 ks2 : List RigidTy, rigidTyBeq.go fuel ks1 ks2 = true → ks1 = ks2 := by
      intro ks1
      induction ks1 with
      | nil => intro ks2 h; cases ks2 with
        | nil => rfl
        | cons _ _ => unfold rigidTyBeq.go at h; exact absurd h (by decide)
      | cons k ks ihk => intro ks2 h; cases ks2 with
        | nil => unfold rigidTyBeq.go at h; exact absurd h (by decide)
        | cons k2 ks2 =>
          unfold rigidTyBeq.go at h
          rw [Bool.and_eq_true] at h
          rw [ih h.1, ihk ks2 h.2]
    have hGoA : ∀ ks1 ks2 : List RigidTy, rigidTyBeq.goArgs fuel ks1 ks2 = true → ks1 = ks2 := by
      intro ks1
      induction ks1 with
      | nil => intro ks2 h; cases ks2 with
        | nil => rfl
        | cons _ _ => unfold rigidTyBeq.goArgs at h; exact absurd h (by decide)
      | cons k ks ihk => intro ks2 h; cases ks2 with
        | nil => unfold rigidTyBeq.goArgs at h; exact absurd h (by decide)
        | cons k2 ks2 =>
          unfold rigidTyBeq.goArgs at h
          rw [Bool.and_eq_true] at h
          rw [ih h.1, ihk ks2 h.2]
    cases a <;> cases b <;> simp only [rigidTyBeq, Bool.and_eq_true, Bool.false_eq_true] at h
    all_goals first
      | rfl
      | (rw [uintTyBeq_sound h])
      | (rw [intTyBeq_sound h])
      | (rw [mutabilityBeq_sound h.1, ih h.2])
      | (rw [hGo _ _ h])
      | (rw [beq_iff_eq.mp h.1, hGoA _ _ h.2])

theorem mirTyBeq_sound {t1 t2 : Ty} (h : mirTyBeq t1 t2 = true) : t1 = t2 := by
  unfold mirTyBeq at h
  rw [Bool.and_eq_true] at h
  cases t1; cases t2
  have h1 := Nat.beq_eq.mp h.1
  have h2 := rigidTyBeq_sound 8 h.2
  simp only at h1 h2
  rw [h1, h2]


theorem auditedFieldSpecListBeq_sound :
    ∀ {fs1 fs2 : List AuditedFieldSpec}, auditedFieldSpecListBeq fs1 fs2 = true → fs1 = fs2
  | [], [], _ => rfl
  | [], _ :: _, h => by unfold auditedFieldSpecListBeq at h; exact absurd h (by decide)
  | _ :: _, [], h => by unfold auditedFieldSpecListBeq at h; exact absurd h (by decide)
  | f1 :: fs1, f2 :: fs2, h => by
    unfold auditedFieldSpecListBeq auditedFieldSpecBeq at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hOff, hTy⟩, hRest⟩ := h
    cases f1; cases f2
    have h1 := Nat.beq_eq.mp hOff
    have h2 := mirTyBeq_sound hTy
    simp only at h1 h2
    rw [h1, h2, auditedFieldSpecListBeq_sound hRest]

theorem spatialTargetSpecBeq_sound {a b : SpatialTargetSpec}
    (h : spatialTargetSpecBeq a b = true) : a = b := by
  cases a <;> cases b <;> simp only [spatialTargetSpecBeq, Bool.and_eq_true,
    Bool.false_eq_true] at h
  · rw [mirTyBeq_sound h]
  · obtain ⟨⟨⟨⟨hId, hTy⟩, hSz⟩, hAl⟩, hFs⟩ := h
    rw [Nat.beq_eq.mp hId, mirTyBeq_sound hTy, Nat.beq_eq.mp hSz, Nat.beq_eq.mp hAl,
      auditedFieldSpecListBeq_sound hFs]

theorem specMatchesDeclAndLayout_toMirTy {layouts : LayoutTable} {declTy : Ty}
    {spec : SpatialTargetSpec} (h : specMatchesDeclAndLayout layouts declTy spec = true) :
    spec.toMirTy = declTy := by
  unfold specMatchesDeclAndLayout at h
  rw [Bool.and_eq_true] at h
  exact mirTyBeq_sound h.1

/-- **`BodySpatialCtx` authentication soundness**: `bodySpatialCtxWf ctx = true`
implies `ctx.body.wellFormed`, slot-for-slot length agreement, and that EVERY
spec's MIR type is EXACTLY the declared `LocalDecl.ty` of the real `CapturedMir`. -/
theorem bodySpatialCtxWf_sound {ctx : BodySpatialCtx} (h : bodySpatialCtxWf ctx = true) :
    ctx.body.wellFormed = true ∧
    ctx.body.localDecls.length = ctx.specs.length ∧
    ∀ (i : Nat) (d : LocalDecl) (s : SpatialTargetSpec),
      listGet? ctx.body.localDecls i = some d → listGet? ctx.specs i = some s →
      s.toMirTy = d.ty := by
  unfold bodySpatialCtxWf at h
  rw [Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  have hGo : ∀ (ds : List LocalDecl) (ss : List SpatialTargetSpec),
      bodySpatialCtxWf.go ctx ds ss = true →
      ds.length = ss.length ∧
      ∀ (i : Nat) (d : LocalDecl) (s : SpatialTargetSpec),
        listGet? ds i = some d → listGet? ss i = some s → s.toMirTy = d.ty := by
    intro ds
    induction ds with
    | nil =>
      intro ss hG
      cases ss with
      | nil => exact ⟨rfl, fun i _ _ hD _ => by cases i <;> cases hD⟩
      | cons _ _ => unfold bodySpatialCtxWf.go at hG; exact absurd hG (by decide)
    | cons d ds ih =>
      intro ss hG
      cases ss with
      | nil => unfold bodySpatialCtxWf.go at hG; exact absurd hG (by decide)
      | cons s ss =>
        unfold bodySpatialCtxWf.go at hG
        rw [Bool.and_eq_true] at hG
        obtain ⟨hLen, hAll⟩ := ih ss hG.2
        refine ⟨by simp only [List.length_cons, hLen], ?_⟩
        intro i d' s' hD hS
        cases i with
        | zero =>
          cases hD; cases hS
          exact specMatchesDeclAndLayout_toMirTy hG.1
        | succ i => exact hAll i d' s' hD hS
  exact hGo _ _ h.2

/-- **`specsMatchBodyCtx` soundness**: a successful authentication pins
`localSpecs` to EXACTLY the audited `ctx.specs` of a well-formed `BodySpatialCtx`. -/
theorem specsMatchBodyCtx_sound {ctx : BodySpatialCtx} {localSpecs : List SpatialTargetSpec}
    (h : specsMatchBodyCtx ctx localSpecs = true) :
    bodySpatialCtxWf ctx = true ∧ localSpecs = ctx.specs := by
  unfold specsMatchBodyCtx at h
  rw [Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  have hGo : ∀ (as bs : List SpatialTargetSpec),
      specsMatchBodyCtx.go as bs = true → bs = as := by
    intro as
    induction as with
    | nil =>
      intro bs hG
      cases bs with
      | nil => rfl
      | cons _ _ => unfold specsMatchBodyCtx.go at hG; exact absurd hG (by decide)
    | cons a as ih =>
      intro bs hG
      cases bs with
      | nil => unfold specsMatchBodyCtx.go at hG; exact absurd hG (by decide)
      | cons b bs =>
        unfold specsMatchBodyCtx.go at hG
        rw [Bool.and_eq_true] at hG
        rw [spatialTargetSpecBeq_sound hG.1, ih bs hG.2]
  exact hGo _ _ h.2

/-- **Negative 7 — Forged alignment, forged `padMask`, and desynced `mirLocals` rejection**:
1. Forging `c.layout.alignBytes := 1` (instead of `4` in `LayoutTable`) causes
   `codecLayoutAndMaskMatchSpec = false` and `freezePaddedToMem = .fail`;
2. Forging `c.padMask := List.replicate 8 true` (hiding field bytes as padding) causes
   `codecLayoutAndMaskMatchSpec = false` and `freezePaddedToMem = .fail`;
3. Desyncing `st.mirLocals[1]` from the loan cell's MIR value (`mirValBeq = false`)
   causes `freezePaddedToMem = .fail`. -/
theorem forged_align_padMask_and_desync_mirLocal_rejected :
    let baseC := paddedU8U32MemCodec 0
    let forgedAlignC : TypedSpatialMemCodec U8U32Struct :=
      { baseC with layout := { size := 8, alignBytes := 1 } }
    let forgedMaskC : TypedSpatialMemCodec U8U32Struct :=
      { baseC with padMask := List.replicate 8 true }
    let desyncSt : PaddedSymMemState :=
      { sampleU8U32InitState with
        mirLocals := [.immediate .unit, .immediate (.aggregate 0 [.scalar ⟨0xFF, 1⟩, .scalar ⟨0, 4⟩])] }
    codecLayoutAndMaskMatchSpec u8U32BodyCtx.body.layouts forgedAlignC.targetTy
      forgedAlignC.layout forgedAlignC.padMask = false ∧
    codecLayoutAndMaskMatchSpec u8U32BodyCtx.body.layouts forgedMaskC.targetTy
      forgedMaskC.layout forgedMaskC.padMask = false ∧
    freezePaddedToMem u8U32BodyCtx 0 baseC paddedU8U32MemCodec_lawful_sample desyncSt = .fail :=
  ⟨rfl, rfl, rfl⟩

/-- Every successful `freezePaddedToMem` runs against EXACTLY the authenticated
`ctx.specs` of a well-formed `BodySpatialCtx`, AND validates the codec's
`V2026MemLayout` (`size`, `alignBytes`) and `padMask` against `ctx.body.layouts`
as well as `st.mirLocals[reg]` consistency with the loan cell. -/
theorem freezePaddedToMem_ok_authenticated {α : Type} {ctx : BodySpatialCtx} {lid : LoanId}
    {c : TypedSpatialMemCodec α} {hLaw : LawfulTypedSpatialMemCodec ctx.body.layouts c}
    {st st' : PaddedSymMemState}
    (h : freezePaddedToMem ctx lid c hLaw st = .ok st') :
    bodySpatialCtxWf ctx = true ∧ st.mirLocalTypes = ctx.specs ∧
      c.targetTy.isRefTarget = false ∧
      codecLayoutAndMaskMatchSpec ctx.body.layouts c.targetTy c.layout c.padMask = true := by
  unfold freezePaddedToMem at h
  cases hS : specsMatchBodyCtx ctx st.mirLocalTypes with
  | false => simp only [hS, Bool.not_false, Bool.true_or, ↓reduceIte] at h; cases h
  | true =>
    cases hR : c.targetTy.isRefTarget with
    | true => simp only [hS, hR, Bool.or_true] at h; cases h
    | false =>
      refine ⟨(specsMatchBodyCtx_sound hS).1, (specsMatchBodyCtx_sound hS).2, rfl, ?_⟩
      cases hLM : codecLayoutAndMaskMatchSpec ctx.body.layouts c.targetTy c.layout c.padMask with
      | true => rfl
      | false =>
        simp only [hS, hR, hLM, Bool.not_true, Bool.not_false, Bool.false_or, Bool.or_false,
          Bool.true_or, Bool.or_true, ↓reduceIte] at h
        split at h <;> try cases h
        split at h <;> try cases h
        split at h <;> try cases h
        split at h <;> try cases h
        split at h <;> try cases h
        split at h <;> try cases h
        split at h <;> try cases h
        split at h <;> try cases h
        split at h <;> try cases h

theorem mutatePaddedInMem_ok_authenticated {ctx : BodySpatialCtx} {bid : BlockId} {tag : Nat}
    {relOff reqAlign : Nat} {newBytes : List AbstractByte} {st st' : PaddedSymMemState}
    (h : mutatePaddedInMem ctx bid tag relOff reqAlign newBytes st = .ok st') :
    bodySpatialCtxWf ctx = true ∧ st.mirLocalTypes = ctx.specs := by
  unfold mutatePaddedInMem at h
  cases hS : specsMatchBodyCtx ctx st.mirLocalTypes with
  | false => simp only [hS, Bool.not_false, Bool.true_or, ↓reduceIte] at h; cases h
  | true => exact specsMatchBodyCtx_sound hS

theorem reabsorbPaddedFromMem_ok_authenticated {ctx : BodySpatialCtx} {lid : LoanId}
    {st st' : PaddedSymMemState}
    (h : reabsorbPaddedFromMem ctx lid st = .ok st') :
    bodySpatialCtxWf ctx = true ∧ st.mirLocalTypes = ctx.specs := by
  unfold reabsorbPaddedFromMem at h
  cases hS : specsMatchBodyCtx ctx st.mirLocalTypes with
  | false => simp only [hS, Bool.not_false, Bool.true_or, ↓reduceIte] at h; cases h
  | true => exact specsMatchBodyCtx_sound hS

end Anneal.PureLift.SpatialMemV2026
