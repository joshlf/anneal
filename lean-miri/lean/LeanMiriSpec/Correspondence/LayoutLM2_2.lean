/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.AllocLM1_4

/-!
# Struct Layout Well-Formedness, Disjoint Field Ranges, and Padding Preservation (`LM-2.2`)

This module proves the byte-level memory and `InitMask` foundations for `LM-2.2`
(product/tuple/struct layout, padding bytes, and field projection semantics):

1. `InitMaskWordRel`: characterizes `Miri.Memory.InitMask` (both `.Lazy` and
   multi-block `.Materialized`) by its array of 64-bit initialization blocks
   `words : Array UInt64` (`64` bytes per block, `words.size = len.bytes.toNat / 64 + 1`),
   proving exact bit-level transitions (`maskBlocksGetBit`) for `InitMask.setRange`,
   `InitMask.get`, and `InitMask.isRangeInitialized` without any 64-byte size cap.
2. `alloc_writeScalar_at_offset`: proves that writing a `ScalarRel`-related
   scalar at any in-bounds byte range `[start, start + sz)` of a mutable
   allocation succeeds, reads back the written scalar at `[start, start + sz)`,
   preserves `Allocation.readScalar` and `isRangeInitialized` on every disjoint
   range `[otherStart, otherStart + otherSz)`, and preserves `InitMask.get` on
   every byte offset outside `[start, start + sz)`.
3. `ValidStructLayout` and `writeField_preserves_other_fields_and_padding`:
   connects `TypeLayout` / `Miri.ABI.LayoutData` field offsets, sizes, and
   alignments to pairwise byte-range disjointness (with no artificial 64-byte
   size limit) and proves that writing field `i` reads back field `i`, preserves
   every other field `j ≠ i`, and preserves uninitialized inter-field padding
   bytes (`InitMask.get = .ok false`).
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Replicas of private `lean-miri` `Allocation` and `InitMask` helpers -/

/-- Private byte storage (`rawBytes`) of an allocation, accessed via `casesOn`. -/
def lm22AllocRaw {P E : Type} (a : Miri.Memory.Allocation P E) : Array UInt8 :=
  Miri.Memory.Allocation.casesOn (motive := fun _ => Array UInt8) a
    (fun raw _ _ _ _ _ _ _ => raw)

/-- Replica of `Miri.Memory.pointerSize`. -/
private def lm22PointerSize (layout : Miri.ABI.TargetDataLayout) : Miri.ABI.Size :=
  Miri.ABI.Size.fromBits layout.pointerWidth.bits

/-- Replica of `Miri.Memory.targetUIntBytes`. -/
private def lm22TargetUIntBytes (layout : Miri.ABI.TargetDataLayout)
    (size : Miri.ABI.Size) (bits : Miri.ABI.U128) :
    Except Miri.Memory.AllocError (Array UInt8) := do
  if size.bytes > 16 then throw (.scalarBytesTooWide size)
  let count := size.bytes.toNat
  let mut result := #[]
  for index in [:count] do
    let valueIndex := if layout.endian == .little then index else count - index - 1
    let byte := (bits.toNat / 2 ^ (8 * valueIndex)) % 256
    result := result.push (UInt8.ofNat byte)
  return result

/-- Replica of `Miri.Memory.readTargetUInt`. -/
private def lm22ReadTargetUInt (layout : Miri.ABI.TargetDataLayout)
    (bytes : Array UInt8) : Except Miri.Memory.AllocError Miri.ABI.U128 := do
  if bytes.size > 16 then
    throw (.scalarBytesTooWide (Miri.ABI.Size.ofBytes (UInt64.ofNat bytes.size)))
  let mut value := 0
  for index in [:bytes.size] do
    let some byte := bytes[index]? | throw (.invalidSliceEndpoints index (index + 1) bytes.size)
    let valueIndex := if layout.endian == .little then index else bytes.size - index - 1
    value := value + byte.toNat * 2 ^ (8 * valueIndex)
  return BitVec.ofNat 128 value

/-- Replica of `Miri.Memory.Allocation.checkedSlice`. -/
private def lm22CheckedSlice {P E : Type} (allocation : Miri.Memory.Allocation P E)
    (range : Miri.Memory.AllocRange) : Except Miri.Memory.AllocError (Array UInt8) := do
  if (lm22AllocRaw allocation).size != allocation.byteSize.bytes.toNat then
    throw (.storageLengthMismatch allocation.byteSize (lm22AllocRaw allocation).size)
  let finish ← range.endExclusive |>.mapError Miri.Memory.AllocError.memory
  if range.start.bytes > finish.bytes || finish.bytes > allocation.byteSize.bytes then
    throw (.outOfBounds range allocation.byteSize)
  return (lm22AllocRaw allocation).extract range.start.bytes.toNat finish.bytes.toNat

private theorem lm22_getBytesUnchecked_eq {P E : Type}
    (allocation : Miri.Memory.Allocation P E) (range : Miri.Memory.AllocRange) :
    Miri.Memory.Allocation.getBytesUnchecked allocation range =
      lm22CheckedSlice allocation range := rfl

/-- Replica of `Miri.Memory.Allocation.readScalar`. -/
private def lm22ReadScalar {P E : Type} [DecidableEq P] [Miri.Memory.PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : Miri.ABI.TargetDataLayout)
    (range : Miri.Memory.AllocRange) (readProvenance : Bool) :
    Except Miri.Memory.AllocError (Miri.Memory.Scalar P) := do
  match ← (allocation.initializationMask.isRangeInitialized range).mapError
      Miri.Memory.AllocError.memory with
  | .error bad => throw (.invalidUninitBytes (some ⟨range, bad⟩))
  | .ok () => pure ()
  let bytes ← Miri.Memory.Allocation.getBytesUnchecked allocation range
  let bits ← lm22ReadTargetUInt layout bytes
  if readProvenance then
    let targetSize := lm22PointerSize layout
    if range.size != targetSize then
      throw (.scalarPointerNotTargetSized range.size targetSize)
    let provenance ← match allocation.provenanceMap.readPtr range.start targetSize with
      | .ok provenance => pure provenance
      | .error (.readPartialPointer offset) => throw (.readPartialPointer offset)
      | .error reason => throw (.provenance reason)
    match provenance with
    | some provenance =>
      if bits.toNat > 18446744073709551615 then
        throw (.pointerBitsDoNotFitOffset bits)
      return Miri.Memory.Scalar.fromPointer layout
        (Miri.Memory.Pointer.new provenance (Miri.ABI.Size.ofBytes (UInt64.ofNat bits.toNat)))
    | none =>
      let scalar ← (Miri.Memory.Scalar.fromUInt bits range.size).mapError
        Miri.Memory.AllocError.scalar
      return scalar
  else
    if Miri.Memory.PointerProvenance.offsetIsAddr (Prov := P) then
      let scalar ← (Miri.Memory.Scalar.fromUInt bits range.size).mapError
        Miri.Memory.AllocError.scalar
      return scalar
    let isEmpty ←
      (allocation.provenanceMap.rangeEmpty range (lm22PointerSize layout)).mapError
        Miri.Memory.AllocError.provenance
    if isEmpty then
      let scalar ← (Miri.Memory.Scalar.fromUInt bits range.size).mapError
        Miri.Memory.AllocError.scalar
      return scalar
    throw (.readPointerAsInt none)

private theorem lm22_readScalar_eq {P E : Type} [DecidableEq P]
    [Miri.Memory.PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : Miri.ABI.TargetDataLayout)
    (range : Miri.Memory.AllocRange) (readProvenance : Bool) :
    allocation.readScalar layout range readProvenance =
      lm22ReadScalar allocation layout range readProvenance := rfl

/-! ## 2. Replicas of `Miri.Memory.InitMask` private helpers -/

private def lm22MaxSizeBytes : Nat := 18446744073709551615
private def lm22WordMask : Nat := 18446744073709551615
private def lm22BlockSize : Nat := 64
private def lm22SizeBytes (size : Miri.ABI.Size) : Nat := size.bytes.toNat

private def lm22SizeFromNat (n : Nat) : Except Miri.Memory.InitMaskError Miri.ABI.Size :=
  if n ≤ lm22MaxSizeBytes then .ok (Miri.ABI.Size.ofBytes (UInt64.ofNat n))
  else .error (.sizeFromNatOverflow n)

private def lm22BitAt (word bit : Nat) : Bool := Nat.testBit word bit

private def lm22SetWordRange (word lo hi : Nat) (state : Bool) : UInt64 :=
  let mask := (2 ^ hi - 1) - (2 ^ lo - 1)
  UInt64.ofNat (if state then Nat.lor word mask else Nat.land word (lm22WordMask - mask))

private def lm22BitIndex (offset : Miri.ABI.Size) : Nat × Nat :=
  let bytes := lm22SizeBytes offset
  (bytes / lm22BlockSize, bytes % lm22BlockSize)

private def lm22GetBlock (self : Miri.Memory.InitMaskMaterialized) (block : Nat) :
    Except Miri.Memory.InitMaskError UInt64 :=
  match self.blocks[block]? with
  | some word => .ok word
  | none => .error (.blockIndexOutOfBounds block self.blocks.size)

private def lm22SetBlock (blocks : Array UInt64) (index : Nat) (word : UInt64) :
    Except Miri.Memory.InitMaskError (Array UInt64) :=
  if h : index < blocks.size then
    .ok (blocks.set index word h)
  else
    .error (.blockIndexOutOfBounds index blocks.size)

private def lm22MaterializedGet (self : Miri.Memory.InitMaskMaterialized)
    (offset : Miri.ABI.Size) : Except Miri.Memory.InitMaskError Bool := do
  let (block, bit) := lm22BitIndex offset
  let word ← lm22GetBlock self block
  return lm22BitAt word.toNat bit

private def lm22MaskGet (self : Miri.Memory.InitMask) (index : Miri.ABI.Size) :
    Except Miri.Memory.InitMaskError Bool := do
  match self.blocks with
  | .Lazy state => return state
  | .Materialized blocks => lm22MaterializedGet blocks index

private theorem lm22_maskGet_eq (self : Miri.Memory.InitMask) (index : Miri.ABI.Size) :
    self.get index = lm22MaskGet self index := rfl

private def lm22FirstSetBit (word startBit : Nat) : Option Nat :=
  ((List.range (64 - startBit)).find? fun offset =>
    lm22BitAt word (startBit + offset)).map (· + startBit)

private def lm22SearchBlock (word : UInt64) (block startBit : Nat)
    (isInit : Bool) : Except Miri.Memory.InitMaskError (Option Miri.ABI.Size) := do
  let bits := if isInit then word.toNat else lm22WordMask - word.toNat
  match lm22FirstSetBit bits startBit with
  | none => return none
  | some bit => return some (← lm22SizeFromNat (block * lm22BlockSize + bit))

private def lm22FindBitFast (self : Miri.Memory.InitMaskMaterialized)
    (start finish : Miri.ABI.Size) (isInit : Bool) :
    Except Miri.Memory.InitMaskError (Option Miri.ABI.Size) := do
  let startBytes := lm22SizeBytes start
  let finishBytes := lm22SizeBytes finish
  if startBytes >= finishBytes then return none
  let (startBlock, startBit) := lm22BitIndex start
  let endInclusive ← lm22SizeFromNat (finishBytes - 1)
  let (endBlockInclusive, _) := lm22BitIndex endInclusive
  let first ← lm22SearchBlock (← lm22GetBlock self startBlock) startBlock startBit isInit
  match first with
  | some index =>
    if lm22SizeBytes index < finishBytes then return some index else return none
  | none =>
    if startBlock < endBlockInclusive then
      for block in [startBlock + 1:endBlockInclusive + 1] do
        match ← lm22SearchBlock (← lm22GetBlock self block) block 0 isInit with
        | some index =>
          if lm22SizeBytes index < finishBytes then return some index else return none
        | none => pure ()
    return none

private def lm22IsRangeInitialized (self : Miri.Memory.InitMask)
    (range : Miri.Memory.AllocRange) :
    Except Miri.Memory.InitMaskError (Except Miri.Memory.AllocRange Unit) := do
  let finish ← range.endExclusive
  if finish.bytes > self.len.bytes then
    return .error (← Miri.Memory.AllocRange.fromEndpoints self.len finish)
  match self.blocks with
  | .Lazy state =>
    if state then return .ok () else return .error range
  | .Materialized blocks =>
    match ← lm22FindBitFast blocks range.start finish false with
    | none => return .ok ()
    | some uninitStart =>
      let uninitEnd := (← lm22FindBitFast blocks uninitStart finish true).getD finish
      return .error (← Miri.Memory.AllocRange.fromEndpoints uninitStart uninitEnd)

private theorem lm22_isRangeInitialized_eq (self : Miri.Memory.InitMask)
    (range : Miri.Memory.AllocRange) :
    self.isRangeInitialized range = lm22IsRangeInitialized self range := rfl

private def lm22SetRangeInbounds (self : Miri.Memory.InitMaskMaterialized)
    (start finish : Miri.ABI.Size) (newState : Bool) :
    Except Miri.Memory.InitMaskError Miri.Memory.InitMaskMaterialized := do
  let (blockA, bitA) := lm22BitIndex start
  let (blockB, bitB) := lm22BitIndex finish
  let mut words := self.blocks
  if blockA == blockB then
    let endBit := if bitB == 0 then 64 else bitB
    let word ← lm22GetBlock ⟨words⟩ blockA
    words ← lm22SetBlock words blockA (lm22SetWordRange word.toNat bitA endBit newState)
  else if newState then
    let wordA ← lm22GetBlock ⟨words⟩ blockA
    words ← lm22SetBlock words blockA (lm22SetWordRange wordA.toNat bitA 64 true)
    if bitB != 0 then
      let wordB ← lm22GetBlock ⟨words⟩ blockB
      words ← lm22SetBlock words blockB (lm22SetWordRange wordB.toNat 0 bitB true)
    for block in [blockA + 1:blockB] do
      words ← lm22SetBlock words block (UInt64.ofNat lm22WordMask)
  else
    let wordA ← lm22GetBlock ⟨words⟩ blockA
    words ← lm22SetBlock words blockA (lm22SetWordRange wordA.toNat bitA 64 false)
    if bitB != 0 then
      let wordB ← lm22GetBlock ⟨words⟩ blockB
      words ← lm22SetBlock words blockB (lm22SetWordRange wordB.toNat 0 bitB false)
    for block in [blockA + 1:blockB] do
      words ← lm22SetBlock words block 0
  return ⟨words⟩

private def lm22Grow (self : Miri.Memory.InitMaskMaterialized) (len amount : Miri.ABI.Size)
    (newState : Bool) : Except Miri.Memory.InitMaskError Miri.Memory.InitMaskMaterialized := do
  let amountBytes := lm22SizeBytes amount
  if amountBytes == 0 then return self
  let lenBytes := lm22SizeBytes len
  let capacity := self.blocks.size * lm22BlockSize
  if capacity < lenBytes then
    throw (.blockCapacityTooSmall lenBytes capacity)
  let unusedTrailingBits := capacity - lenBytes
  let mut words := self.blocks
  if amountBytes > unusedTrailingBits then
    let additionalBlocks := amountBytes / lm22BlockSize + 1
    let word := if newState then UInt64.ofNat lm22WordMask else 0
    words := words ++ Array.replicate additionalBlocks word
  if unusedTrailingBits > 0 then
    let tailEnd ← lm22SizeFromNat (lenBytes + unusedTrailingBits)
    let grown ← lm22SetRangeInbounds ⟨words⟩ len tailEnd newState
    words := grown.blocks
  return ⟨words⟩

private def lm22Materialize (self : Miri.Memory.InitMask) :
    Except Miri.Memory.InitMaskError Miri.Memory.InitMaskMaterialized := do
  match self.blocks with
  | .Lazy state => lm22Grow ⟨#[]⟩ (Miri.ABI.Size.ofBytes 0) self.len state
  | .Materialized blocks => return blocks

private def lm22SetRange (self : Miri.Memory.InitMask) (range : Miri.Memory.AllocRange)
    (newState : Bool) : Except Miri.Memory.InitMaskError Miri.Memory.InitMask := do
  let start := range.start
  let finish ← range.endExclusive
  let fullOverwrite := start.bytes = 0 ∧ self.len.bytes ≤ finish.bytes
  match self.blocks with
  | .Lazy state =>
    if fullOverwrite then return ⟨.Lazy newState, finish⟩
    else if state == newState then
      if finish.bytes > self.len.bytes then return ⟨.Lazy state, finish⟩
      else return self
    else
      let blocks ← lm22Materialize self
      if finish.bytes ≤ self.len.bytes then
        return ⟨.Materialized (← lm22SetRangeInbounds blocks start finish newState), self.len⟩
      else
        let firstPart ← if start.bytes < self.len.bytes then
          lm22SetRangeInbounds blocks start self.len newState else pure blocks
        let amount ← (Miri.ABI.Size.sub finish self.len).mapError Miri.Memory.MemoryError.sizeError
        return ⟨.Materialized (← lm22Grow firstPart self.len amount newState), finish⟩
  | .Materialized oldBlocks =>
    if fullOverwrite then return ⟨.Lazy newState, finish⟩
    else if finish.bytes ≤ self.len.bytes then
      return ⟨.Materialized (← lm22SetRangeInbounds oldBlocks start finish newState), self.len⟩
    else
      let firstPart ← if start.bytes < self.len.bytes then
        lm22SetRangeInbounds oldBlocks start self.len newState else pure oldBlocks
      let amount ← (Miri.ABI.Size.sub finish self.len).mapError Miri.Memory.MemoryError.sizeError
      return ⟨.Materialized (← lm22Grow firstPart self.len amount newState), finish⟩

private theorem lm22_setRange_eq (self : Miri.Memory.InitMask)
    (range : Miri.Memory.AllocRange) (newState : Bool) :
    self.setRange range newState = lm22SetRange self range newState := rfl

/-- Compute the updated 64-bit initialization mask word after setting bytes
`[lo, hi)` to `true`. -/
def setInitWordRange (word : UInt64) (lo hi : Nat) : UInt64 :=
  lm22SetWordRange word.toNat lo hi true

private theorem rangeMask_eq_mul_two_pow {lo hi : Nat} (hle : lo ≤ hi) :
    (2 ^ hi - 1) - (2 ^ lo - 1) = (2 ^ (hi - lo) - 1) * 2 ^ lo := by
  have hpow : 2 ^ hi = 2 ^ (hi - lo) * 2 ^ lo := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hle]
  have hpos : 1 ≤ 2 ^ lo := Nat.one_le_two_pow
  have hpos_hi : 2 ^ lo ≤ 2 ^ hi := Nat.pow_le_pow_right (by decide) hle
  rw [Nat.sub_mul, hpow, Nat.one_mul]
  omega

theorem testBit_rangeMask {lo hi b : Nat} (hle : lo ≤ hi) :
    Nat.testBit ((2 ^ hi - 1) - (2 ^ lo - 1)) b = decide (lo ≤ b ∧ b < hi) := by
  rw [rangeMask_eq_mul_two_pow hle, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases h1 : lo ≤ b <;> by_cases h2 : b < hi <;> simp [h1, h2] <;> omega

theorem testBit_setInitWordRange (word : UInt64) {lo hi b : Nat}
    (hle : lo ≤ hi) (hb : b < 64) :
    Nat.testBit (setInitWordRange word lo hi).toNat b =
      (Nat.testBit word.toNat b || decide (lo ≤ b ∧ b < hi)) := by
  unfold setInitWordRange lm22SetWordRange
  simp only [↓reduceIte, UInt64.toNat_ofNat']
  rw [Nat.testBit_mod_two_pow]
  simp [hb, Nat.testBit_or, testBit_rangeMask hle]

theorem testBit_wordMask_sub (word : UInt64) {b : Nat} (hb : b < 64) :
    Nat.testBit (lm22WordMask - word.toNat) b = !Nat.testBit word.toNat b := by
  have hcomp : lm22WordMask - word.toNat = (~~~word.toBitVec).toNat := by
    rw [BitVec.toNat_not]
    simp [lm22WordMask]
  have h1 : (~~~word.toBitVec).toNat.testBit b = (~~~word.toBitVec).getLsbD b := rfl
  have h2 : word.toNat.testBit b = word.toBitVec.getLsbD b := rfl
  rw [hcomp, h1, h2, BitVec.getLsbD_not]
  simp [hb]

/-! ## 3. Multi-Block `InitMask` Block-Array Relation (`InitMaskWordRel`) -/

/-- Read the initialization bit for byte `b` from a block array `words : Array UInt64`
(`64` bytes per `UInt64` block). -/
def maskBlocksGetBit (words : Array UInt64) (b : Nat) : Bool :=
  match words[b / 64]? with
  | some w => Nat.testBit w.toNat (b % 64)
  | none => false

/-- All-uninitialized (`false`) block array for an allocation of size `len`. -/
def initWordsFalse (len : Miri.ABI.Size) : Array UInt64 :=
  Array.replicate (len.bytes.toNat / 64 + 1) 0

/-- All-initialized (`true`) block array for an allocation of size `len`. -/
def initWordsTrue (len : Miri.ABI.Size) : Array UInt64 :=
  Array.replicate (len.bytes.toNat / 64 + 1) (UInt64.ofNat lm22WordMask)

@[simp] theorem maskBlocksGetBit_initWordsFalse (len : Miri.ABI.Size) (b : Nat) :
    maskBlocksGetBit (initWordsFalse len) b = false := by
  unfold maskBlocksGetBit initWordsFalse
  cases hget : (Array.replicate (len.bytes.toNat / 64 + 1) (0 : UInt64))[b / 64]? with
  | none => rfl
  | some w =>
    have hw : w = 0 := Array.eq_of_mem_replicate (Array.mem_of_getElem? hget)
    subst hw
    simp [Nat.zero_testBit]

theorem maskBlocksGetBit_initWordsTrue {len : Miri.ABI.Size} {b : Nat}
    (hb : b < len.bytes.toNat) :
    maskBlocksGetBit (initWordsTrue len) b = true := by
  unfold maskBlocksGetBit initWordsTrue
  have hlt : b / 64 < len.bytes.toNat / 64 + 1 := by omega
  have hmod : b % 64 < 64 := Nat.mod_lt b (by decide)
  simp only [Array.getElem?_replicate, hlt, ↓reduceIte]
  have hval : (UInt64.ofNat lm22WordMask).toNat = 2 ^ 64 - 1 := rfl
  rw [hval, Nat.testBit_two_pow_sub_one]
  simp [hmod]

/-- Representation of an `InitMask` of arbitrary size `len` by its array of
64-bit per-byte initialization blocks `words : Array UInt64` (`64` bytes per
block, `words.size = len.bytes.toNat / 64 + 1`). Covers `.Lazy false`
(`words = initWordsFalse len`), `.Lazy true` (`words = initWordsTrue len`), and
multi-block `.Materialized ⟨words⟩`. -/
def InitMaskWordRel (mask : Miri.Memory.InitMask) (len : Miri.ABI.Size)
    (words : Array UInt64) : Prop :=
  mask.len = len ∧
  words.size = len.bytes.toNat / 64 + 1 ∧
  ((mask.blocks = .Lazy false ∧ words = initWordsFalse len) ∨
   (mask.blocks = .Lazy true ∧ words = initWordsTrue len) ∨
   mask.blocks = .Materialized ⟨words⟩)

theorem initMaskWordRel_new_false {len : Miri.ABI.Size} :
    InitMaskWordRel (Miri.Memory.InitMask.new len false) len (initWordsFalse len) :=
  ⟨rfl, by simp [initWordsFalse], Or.inl ⟨rfl, rfl⟩⟩

theorem initMaskWordRel_get {mask : Miri.Memory.InitMask} {len : Miri.ABI.Size}
    {words : Array UInt64}
    (hrel : InitMaskWordRel mask len words) {p : Nat} (hp : p < len.bytes.toNat) :
    mask.get (Miri.ABI.Size.ofBytes (UInt64.ofNat p)) = .ok (maskBlocksGetBit words p) := by
  obtain ⟨_, hsize, hblocks⟩ := hrel
  have hp_lt2 : p < 2 ^ 64 := Nat.lt_trans hp len.bytes.toNat_lt
  have hp_u64 : (UInt64.ofNat p).toNat = p := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt hp_lt2
  have hdiv_lt : p / 64 < words.size := by rw [hsize]; omega
  rw [lm22_maskGet_eq]
  unfold lm22MaskGet
  rcases hblocks with ⟨hb, rfl⟩ | ⟨hb, rfl⟩ | hb
  · simp [hb, pure, Except.pure]
  · rw [hb, maskBlocksGetBit_initWordsTrue hp]
    rfl
  · simp only [hb, lm22MaterializedGet, lm22BitIndex, lm22SizeBytes, lm22BlockSize,
      Miri.ABI.Size.ofBytes, hp_u64, lm22GetBlock, lm22BitAt, maskBlocksGetBit,
      Array.getElem?_eq_getElem hdiv_lt]
    rfl

private theorem list_find_none_or_ge {l : List Nat} {p : Nat → Bool} {bound : Nat}
    (h : ∀ x ∈ l, x < bound → p x = false) :
    match l.find? p with
    | none => True
    | some x => bound ≤ x := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.find?_cons]
    cases hp : p a
    · exact ih (fun x hx => h x (by simp [hx]))
    · dsimp only
      refine Nat.le_of_not_lt fun hlt => ?_
      have hfalse := h a (by simp) hlt
      rw [hfalse] at hp
      cases hp

private theorem list_range'_find?_some_le {f : Nat → Bool} :
    ∀ k s {p : Nat}, s ≤ p → p < s + k → f p = true →
      ∃ m, (List.range' s k).find? f = some m ∧ s ≤ m ∧ m ≤ p
  | 0, _, _, h1, h2, _ => by omega
  | k + 1, s, p, h1, h2, hfp => by
    rw [List.range'_succ, List.find?_cons]
    cases hfs : f s
    · have hne : p ≠ s := by
        intro heq; subst heq; rw [hfs] at hfp; cases hfp
      obtain ⟨m, hm, hm1, hm2⟩ :=
        list_range'_find?_some_le k (s + 1) (by omega) (by omega) hfp
      exact ⟨m, hm, by omega, hm2⟩
    · exact ⟨s, rfl, Nat.le_refl s, h1⟩

private theorem lm22SearchBlock_false_exists_false (word : UInt64)
    {block startBit finishBytes : Nat}
    (hblk : block * 64 + 64 ≤ 2 ^ 64)
    {bit : Nat} (hlo : startBit ≤ bit) (hhi : bit < 64)
    (hfin : block * 64 + bit < finishBytes)
    (hfalse : Nat.testBit word.toNat bit = false) :
    ∃ idx : Miri.ABI.Size,
      lm22SearchBlock word block startBit false = .ok (some idx) ∧
      lm22SizeBytes idx < finishBytes := by
  have hfp : lm22BitAt (lm22WordMask - word.toNat) (startBit + (bit - startBit)) = true := by
    unfold lm22BitAt
    rw [Nat.add_sub_of_le hlo, testBit_wordMask_sub word hhi, hfalse]
    rfl
  obtain ⟨m, hm, _, hm_le⟩ :=
    list_range'_find?_some_le (64 - startBit) 0
      (f := fun offset => lm22BitAt (lm22WordMask - word.toNat) (startBit + offset))
      (p := bit - startBit) (by omega) (by omega) hfp
  have hfirst : lm22FirstSetBit (lm22WordMask - word.toNat) startBit = some (m + startBit) := by
    unfold lm22FirstSetBit
    rw [List.range_eq_range', hm]
    rfl
  have hm_lt64 : m + startBit < 64 := by omega
  have hm_le_max : block * lm22BlockSize + (m + startBit) ≤ lm22MaxSizeBytes := by
    unfold lm22BlockSize lm22MaxSizeBytes; omega
  have hm_u64 :
      (UInt64.ofNat (block * lm22BlockSize + (m + startBit))).toNat =
        block * lm22BlockSize + (m + startBit) := by
    rw [UInt64.toNat_ofNat']
    unfold lm22BlockSize at *
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨Miri.ABI.Size.ofBytes (UInt64.ofNat (block * lm22BlockSize + (m + startBit))), ?_, ?_⟩
  · unfold lm22SearchBlock
    simp only [Bool.false_eq_true, ↓reduceIte, hfirst, lm22SizeFromNat, hm_le_max,
      bind, Except.bind, pure, Except.pure]
  · simp only [lm22SizeBytes, Miri.ABI.Size.ofBytes, hm_u64]
    unfold lm22BlockSize
    omega

private theorem lm22SearchBlock_false_lt_succ_block (word : UInt64)
    {block startBit : Nat} (hblk : block * 64 + 64 ≤ 2 ^ 64) :
    (lm22SearchBlock word block startBit false = .ok none) ∨
    (∃ idx : Miri.ABI.Size,
      lm22SearchBlock word block startBit false = .ok (some idx) ∧
      lm22SizeBytes idx < (block + 1) * 64) := by
  unfold lm22SearchBlock lm22FirstSetBit
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases hopt : (List.range (64 - startBit)).find?
      (fun offset => lm22BitAt (lm22WordMask - word.toNat) (startBit + offset)) with
  | none =>
    exact Or.inl rfl
  | some offset =>
    have hmem : offset ∈ List.range (64 - startBit) := List.mem_of_find?_eq_some hopt
    have hoff_lt64 : offset + startBit < 64 := by
      have := List.mem_range.mp hmem
      omega
    have hoff_le_max : block * lm22BlockSize + (offset + startBit) ≤ lm22MaxSizeBytes := by
      unfold lm22BlockSize lm22MaxSizeBytes; omega
    have hoff_u64 :
        (UInt64.ofNat (block * lm22BlockSize + (offset + startBit))).toNat =
          block * lm22BlockSize + (offset + startBit) := by
      rw [UInt64.toNat_ofNat']
      unfold lm22BlockSize at *
      exact Nat.mod_eq_of_lt (by omega)
    refine Or.inr ⟨Miri.ABI.Size.ofBytes (UInt64.ofNat (block * lm22BlockSize + (offset + startBit))), ?_, ?_⟩
    · simp [Option.map, lm22SizeFromNat, hoff_le_max, bind, Except.bind, pure, Except.pure]
    · simp only [lm22SizeBytes, Miri.ABI.Size.ofBytes, hoff_u64]
      unfold lm22BlockSize
      omega

private def lm22FindBitStep (self : Miri.Memory.InitMaskMaterialized)
    (finishBytes : Nat) (isInit : Bool) (block : Nat)
    (_ : Option (Option Miri.ABI.Size) × PUnit) :
    Except Miri.Memory.InitMaskError
      (ForInStep (Option (Option Miri.ABI.Size) × PUnit)) := do
  match ← lm22SearchBlock (← lm22GetBlock self block) block 0 isInit with
  | some index =>
    if lm22SizeBytes index < finishBytes then
      return ForInStep.done (some (some index), ())
    else
      return ForInStep.done (some none, ())
  | none =>
    return ForInStep.yield (none, ())

private theorem lm22FindBitStep_loop_exists_false
    (words : Array UInt64) {finishBytes blockP : Nat}
    (hfin_lt : finishBytes < 2 ^ 64)
    (hbp_le : blockP ≤ (finishBytes - 1) / 64)
    (hbp_sz : (finishBytes - 1) / 64 < words.size)
    (hbp_fin : blockP * 64 < finishBytes)
    {idxP : Miri.ABI.Size}
    (hsearchP : lm22SearchBlock (words[blockP]'(by omega)) blockP 0 false = .ok (some idxP))
    (hidxP_lt : lm22SizeBytes idxP < finishBytes) :
    ∀ m k, k ≤ blockP → blockP < k + m →
      ∃ idx : Miri.ABI.Size,
        forIn (List.range' k m) (none, ()) (lm22FindBitStep ⟨words⟩ finishBytes false) =
          .ok (some (some idx), ()) := by
  intro m
  induction m with
  | zero => intro k h1 h2; omega
  | succ m ih =>
    intro k hk_le hbp_lt
    rw [List.range'_succ, List.forIn_cons]
    have hk_sz : k < words.size := by omega
    have hget_k : lm22GetBlock ⟨words⟩ k = .ok (words[k]'hk_sz) := by
      simp [lm22GetBlock, hk_sz]
    by_cases hkeq : k = blockP
    · subst hkeq
      refine ⟨idxP, ?_⟩
      unfold lm22FindBitStep
      simp [hget_k, hsearchP, hidxP_lt, bind, Except.bind, pure, Except.pure]
    · have hk_lt_bp : k < blockP := by omega
      have hk_blk : k * 64 + 64 ≤ 2 ^ 64 := by omega
      have hk_succ_le : (k + 1) * 64 ≤ finishBytes := by omega
      rcases lm22SearchBlock_false_lt_succ_block (words[k]'hk_sz) hk_blk (startBit := 0) with
        hnone | ⟨idxK, hsomeK, hltK⟩
      · have hstep_k :
            lm22FindBitStep ⟨words⟩ finishBytes false k (none, ()) = .ok (.yield (none, ())) := by
          unfold lm22FindBitStep
          simp [hget_k, hnone, bind, Except.bind, pure, Except.pure]
        rw [hstep_k]
        exact ih (k + 1) (by omega) (by omega)
      · have hltK_fin : lm22SizeBytes idxK < finishBytes := by omega
        refine ⟨idxK, ?_⟩
        unfold lm22FindBitStep
        simp [hget_k, hsomeK, hltK_fin, bind, Except.bind, pure, Except.pure]

theorem initMaskWordRel_not_isRangeInitialized_of_get_false
    {mask : Miri.Memory.InitMask} {len : Miri.ABI.Size} {words : Array UInt64}
    (hrel : InitMaskWordRel mask len words)
    {p : Nat} (hp : p < len.bytes.toNat)
    (hget : mask.get (Miri.ABI.Size.ofBytes (UInt64.ofNat p)) = .ok false) :
    mask.isRangeInitialized (Miri.Memory.allocRange Miri.ABI.Size.ZERO len) ≠
      .ok (.ok ()) := by
  have hget_word := initMaskWordRel_get hrel hp
  rw [hget] at hget_word
  injection hget_word with hbit_p
  obtain ⟨hlen, hsize, hblocks⟩ := hrel
  have hlen_lt : len.bytes.toNat < 2 ^ 64 := len.bytes.toNat_lt
  have hend : (Miri.Memory.allocRange Miri.ABI.Size.ZERO len).endExclusive = .ok len := by
    unfold Miri.Memory.AllocRange.endExclusive Miri.Memory.AllocRange.end Miri.Memory.allocRange
    have h0 : Miri.ABI.Size.ZERO.bytes + len.bytes = len.bytes := UInt64.zero_add len.bytes
    have hno_wrap : ¬ len.bytes < Miri.ABI.Size.ZERO.bytes := by
      simp [Miri.ABI.Size.ZERO, UInt64.lt_iff_toNat_lt]
    have hlen_of : Miri.ABI.Size.ofBytes len.bytes = len := by cases len; rfl
    simp [Miri.ABI.Size.add, h0, hno_wrap, hlen_of, Except.mapError]
  have hnot_gt : ¬ len.bytes > mask.len.bytes := by
    rw [hlen]; simp [GT.gt]
  rw [lm22_isRangeInitialized_eq]
  unfold lm22IsRangeInitialized
  simp only [hend, bind, Except.bind, hnot_gt, ↓reduceIte]
  rcases hblocks with ⟨hb, _⟩ | ⟨hb, rfl⟩ | hb
  · rw [hb]
    dsimp only
    simp [pure, Except.pure]
  · rw [maskBlocksGetBit_initWordsTrue hp] at hbit_p
    cases hbit_p
  · rw [hb]
    dsimp only
    have hbp_sz : p / 64 < words.size := by rw [hsize]; omega
    have hbit_false : Nat.testBit (words[p / 64]'hbp_sz).toNat (p % 64) = false := by
      unfold maskBlocksGetBit at hbit_p
      rw [Array.getElem?_eq_getElem hbp_sz] at hbit_p
      exact hbit_p.symm
    have hbp_blk : (p / 64) * 64 + 64 ≤ 2 ^ 64 := by omega
    obtain ⟨idxP, hsearchP, hidxP_lt⟩ :=
      lm22SearchBlock_false_exists_false (words[p / 64]'hbp_sz) hbp_blk
        (startBit := 0) (finishBytes := lm22SizeBytes len)
        (Nat.zero_le _) (Nat.mod_lt p (by decide))
        (by unfold lm22SizeBytes; omega) hbit_false
    have hfind_some :
        ∃ idx : Miri.ABI.Size,
          lm22FindBitFast ⟨words⟩
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO len).start len false =
            .ok (some idx) := by
      have hstart_zero : lm22SizeBytes (Miri.Memory.allocRange Miri.ABI.Size.ZERO len).start = 0 := rfl
      have hnot_ge : ¬ lm22SizeBytes (Miri.Memory.allocRange Miri.ABI.Size.ZERO len).start ≥
          lm22SizeBytes len := by
        rw [hstart_zero]; unfold lm22SizeBytes; omega
      have hsub1_le : len.bytes.toNat - 1 ≤ lm22MaxSizeBytes := by
        unfold lm22MaxSizeBytes; omega
      have hsub1_u64 : (UInt64.ofNat (len.bytes.toNat - 1)).toNat = len.bytes.toNat - 1 := by
        rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
      have hsz_end : lm22SizeFromNat (lm22SizeBytes len - 1) =
          .ok (Miri.ABI.Size.ofBytes (UInt64.ofNat (len.bytes.toNat - 1))) := by
        simp [lm22SizeFromNat, lm22SizeBytes, hsub1_le]
      have hbit_start : lm22BitIndex (Miri.Memory.allocRange Miri.ABI.Size.ZERO len).start = (0, 0) := by
        simp [lm22BitIndex, hstart_zero, lm22BlockSize]
      have hbit_end :
          (lm22BitIndex (Miri.ABI.Size.ofBytes (UInt64.ofNat (len.bytes.toNat - 1)))).1 =
            (len.bytes.toNat - 1) / 64 := by
        simp [lm22BitIndex, lm22SizeBytes, lm22BlockSize, Miri.ABI.Size.ofBytes, hsub1_u64]
      have h0_sz : 0 < words.size := by rw [hsize]; omega
      have hget0 : lm22GetBlock ⟨words⟩ 0 = .ok (words[0]'h0_sz) := by
        simp [lm22GetBlock, h0_sz]
      by_cases hbp0 : p / 64 = 0
      · refine ⟨idxP, ?_⟩
        have hsearch0 : lm22SearchBlock (words[0]'h0_sz) 0 0 false = .ok (some idxP) := by
          simpa [hbp0] using hsearchP
        unfold lm22FindBitFast
        simp only [hnot_ge, ↓reduceIte, hbit_start, hsz_end, bind, Except.bind,
          hget0, hsearch0, hidxP_lt, pure, Except.pure]
      · have hbp_pos : 0 < p / 64 := by omega
        have hend_pos : 0 < (len.bytes.toNat - 1) / 64 := by omega
        have h0_blk : 0 * 64 + 64 ≤ 2 ^ 64 := by decide
        rcases lm22SearchBlock_false_lt_succ_block (words[0]'h0_sz) h0_blk (startBit := 0) with
          hnone0 | ⟨idx0, hsome0, hlt0⟩
        · obtain ⟨idxL, hloop⟩ :=
            lm22FindBitStep_loop_exists_false words (finishBytes := lm22SizeBytes len)
              hlen_lt (blockP := p / 64)
              (by unfold lm22SizeBytes; omega) (by rw [hsize]; unfold lm22SizeBytes; omega)
              (by unfold lm22SizeBytes; omega) hsearchP hidxP_lt
              ((len.bytes.toNat - 1) / 64) 1 (by omega) (by omega)
          refine ⟨idxL, ?_⟩
          unfold lm22FindBitFast
          simp only [hnot_ge, ↓reduceIte, hbit_start, hsz_end, bind, Except.bind,
            hbit_end, hget0, hnone0, hend_pos, Std.Legacy.Range.forIn_eq_forIn_range',
            Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one, Nat.zero_add]
          unfold lm22FindBitStep at hloop
          dsimp only [bind, Except.bind] at hloop
          rw [hloop]
          rfl
        · have hlt0_fin : lm22SizeBytes idx0 < lm22SizeBytes len := by
            unfold lm22SizeBytes at hlt0 ⊢; omega
          refine ⟨idx0, ?_⟩
          unfold lm22FindBitFast
          simp only [hnot_ge, ↓reduceIte, hbit_start, hsz_end, bind, Except.bind,
            hget0, hsome0, hlt0_fin, pure, Except.pure]
    obtain ⟨idx, hfind⟩ := hfind_some
    rw [hfind]
    dsimp only [bind, Except.bind]
    cases lm22FindBitFast ⟨words⟩ idx len true with
    | error e => nofun
    | ok optEnd =>
      dsimp only [pure, Except.pure]
      cases Miri.Memory.AllocRange.fromEndpoints idx (optEnd.getD len) with
      | error e => nofun
      | ok rng => nofun

private theorem lm22SearchBlock_false_all_true (word : UInt64)
    {block startBit finishBytes : Nat}
    (hstart64 : startBit < 64)
    (hblk : block * 64 + 64 ≤ 2 ^ 64)
    (hinit : ∀ bit, startBit ≤ bit → bit < 64 → block * 64 + bit < finishBytes →
      Nat.testBit word.toNat bit = true) :
    ∃ first : Option Miri.ABI.Size,
      lm22SearchBlock word block startBit false = .ok first ∧
      (∀ idx, first = some idx → finishBytes ≤ lm22SizeBytes idx) ∧
      (block * 64 + 64 ≤ finishBytes → first = none) := by
  have hfind :
      match (List.range (64 - startBit)).find?
          (fun offset => lm22BitAt (lm22WordMask - word.toNat) (startBit + offset)) with
      | none => True
      | some offset => finishBytes - (block * 64 + startBit) ≤ offset := by
    apply list_find_none_or_ge
    intro offset hmem hlt
    have hoff64 : startBit + offset < 64 := by
      have := List.mem_range.mp hmem
      omega
    unfold lm22BitAt
    rw [testBit_wordMask_sub word hoff64, hinit (startBit + offset) (by omega) hoff64 (by omega)]
    rfl
  unfold lm22SearchBlock lm22FirstSetBit
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases hopt : (List.range (64 - startBit)).find?
      (fun offset => lm22BitAt (lm22WordMask - word.toNat) (startBit + offset)) with
  | none =>
    exact ⟨none, rfl, fun _ h => (by cases h), fun _ => rfl⟩
  | some offset =>
    rw [hopt] at hfind
    have hmem : offset ∈ List.range (64 - startBit) := List.mem_of_find?_eq_some hopt
    have hoff_lt64 : offset + startBit < 64 := by
      have := List.mem_range.mp hmem
      omega
    have hoff_le_max : block * lm22BlockSize + (offset + startBit) ≤ lm22MaxSizeBytes := by
      unfold lm22BlockSize lm22MaxSizeBytes; omega
    have hoff_u64 :
        (UInt64.ofNat (block * lm22BlockSize + (offset + startBit))).toNat =
          block * lm22BlockSize + (offset + startBit) := by
      rw [UInt64.toNat_ofNat']
      unfold lm22BlockSize at *
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨some (Miri.ABI.Size.ofBytes (UInt64.ofNat (block * lm22BlockSize + (offset + startBit)))),
      ?_, ?_, ?_⟩
    · simp [Option.map, lm22SizeFromNat, hoff_le_max, bind, Except.bind, pure, Except.pure]
    · intro idx hidx
      cases hidx
      simp only [lm22SizeBytes, Miri.ABI.Size.ofBytes, hoff_u64]
      unfold lm22BlockSize
      omega
    · intro hfull
      omega

private theorem lm22FindBitStep_loop_all_true
    (words : Array UInt64) {finishBytes : Nat}
    (hfin_pos : 0 < finishBytes)
    (hfin_lt : finishBytes < 2 ^ 64)
    (hend_sz : (finishBytes - 1) / 64 < words.size) :
    ∀ m k, k + m = (finishBytes - 1) / 64 + 1 →
      (∀ b, k * 64 ≤ b → b < finishBytes → maskBlocksGetBit words b = true) →
      ∃ r : Option (Option Miri.ABI.Size),
        forIn (List.range' k m) (none, ()) (lm22FindBitStep ⟨words⟩ finishBytes false) =
          .ok (r, ()) ∧
        (r = none ∨ r = some none) := by
  intro m
  induction m with
  | zero =>
    intro k _ _
    exact ⟨none, rfl, Or.inl rfl⟩
  | succ m ih =>
    intro k hkm hinit
    rw [List.range'_succ, List.forIn_cons]
    have hk_sz : k < words.size := by omega
    have hget_k : lm22GetBlock ⟨words⟩ k = .ok (words[k]'hk_sz) := by
      simp [lm22GetBlock, hk_sz]
    have hk_blk : k * 64 + 64 ≤ 2 ^ 64 := by omega
    have hk_bits : ∀ bit, 0 ≤ bit → bit < 64 → k * 64 + bit < finishBytes →
        Nat.testBit (words[k]'hk_sz).toNat bit = true := by
      intro bit _ hbit64 hlt
      have hb := hinit (k * 64 + bit) (by omega) hlt
      unfold maskBlocksGetBit at hb
      have hdiv : (k * 64 + bit) / 64 = k := by omega
      have hmod : (k * 64 + bit) % 64 = bit := by omega
      rw [hdiv, hmod, Array.getElem?_eq_getElem hk_sz] at hb
      exact hb
    obtain ⟨first, hsearch_ok, hfirst_ge, hfirst_none⟩ :=
      lm22SearchBlock_false_all_true (words[k]'hk_sz) (by decide) hk_blk hk_bits
    by_cases hm0 : m = 0
    · subst hm0
      cases first with
      | none =>
        have hstep_k :
            lm22FindBitStep ⟨words⟩ finishBytes false k (none, ()) = .ok (.yield (none, ())) := by
          unfold lm22FindBitStep
          simp [hget_k, hsearch_ok, bind, Except.bind, pure, Except.pure]
        rw [hstep_k]
        exact ⟨none, rfl, Or.inl rfl⟩
      | some idx =>
        have hge := hfirst_ge idx rfl
        have hnot_lt : ¬ lm22SizeBytes idx < finishBytes := by omega
        have hstep_k :
            lm22FindBitStep ⟨words⟩ finishBytes false k (none, ()) =
              .ok (.done (some none, ())) := by
          unfold lm22FindBitStep
          simp [hget_k, hsearch_ok, hnot_lt, bind, Except.bind, pure, Except.pure]
        rw [hstep_k]
        exact ⟨some none, rfl, Or.inr rfl⟩
    · have hfull : k * 64 + 64 ≤ finishBytes := by omega
      have hfn := hfirst_none hfull
      subst hfn
      have hstep_k :
          lm22FindBitStep ⟨words⟩ finishBytes false k (none, ()) = .ok (.yield (none, ())) := by
        unfold lm22FindBitStep
        simp [hget_k, hsearch_ok, bind, Except.bind, pure, Except.pure]
      rw [hstep_k]
      exact ih (k + 1) (by omega) (fun b hb1 hb2 => hinit b (by omega) hb2)

private theorem lm22FindBitFast_false_eq_none (words : Array UInt64)
    {start finish : Miri.ABI.Size}
    (hpos : start.bytes.toNat < finish.bytes.toNat)
    (hsz : (finish.bytes.toNat - 1) / 64 < words.size)
    (hinit : ∀ b, start.bytes.toNat ≤ b → b < finish.bytes.toNat →
      maskBlocksGetBit words b = true) :
    lm22FindBitFast ⟨words⟩ start finish false = .ok none := by
  have hfin_lt : finish.bytes.toNat < 2 ^ 64 := finish.bytes.toNat_lt
  have hsub1_le : finish.bytes.toNat - 1 ≤ lm22MaxSizeBytes := by
    unfold lm22MaxSizeBytes; omega
  have hsub1_u64 : (UInt64.ofNat (finish.bytes.toNat - 1)).toNat = finish.bytes.toNat - 1 := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  let startBlock := start.bytes.toNat / 64
  let startBit := start.bytes.toNat % 64
  let endBlock := (finish.bytes.toNat - 1) / 64
  have hstart_sz : startBlock < words.size := by omega
  have hstart_blk : startBlock * 64 + 64 ≤ 2 ^ 64 := by omega
  have hstart_bits : ∀ bit, startBit ≤ bit → bit < 64 →
      startBlock * 64 + bit < finish.bytes.toNat →
      Nat.testBit (words[startBlock]'hstart_sz).toNat bit = true := by
    intro bit hlo hhi hlt
    have hb := hinit (startBlock * 64 + bit) (by omega) hlt
    unfold maskBlocksGetBit at hb
    have hdiv : (startBlock * 64 + bit) / 64 = startBlock := by omega
    have hmod : (startBlock * 64 + bit) % 64 = bit := by omega
    rw [hdiv, hmod, Array.getElem?_eq_getElem hstart_sz] at hb
    exact hb
  obtain ⟨first, hsearch_ok, hfirst_ge, hfirst_none⟩ :=
    lm22SearchBlock_false_all_true (words[startBlock]'hstart_sz)
      (Nat.mod_lt _ (by decide)) hstart_blk hstart_bits
  have hnot_ge : ¬ lm22SizeBytes start ≥ lm22SizeBytes finish := by
    unfold lm22SizeBytes; omega
  have hget_start : lm22GetBlock ⟨words⟩ startBlock = .ok (words[startBlock]'hstart_sz) := by
    simp [lm22GetBlock, hstart_sz]
  have hbit_start : lm22BitIndex start = (startBlock, startBit) := rfl
  have hsz_end : lm22SizeFromNat (lm22SizeBytes finish - 1) =
      .ok (Miri.ABI.Size.ofBytes (UInt64.ofNat (finish.bytes.toNat - 1))) := by
    simp [lm22SizeFromNat, lm22SizeBytes, hsub1_le]
  have hbit_end :
      (lm22BitIndex (Miri.ABI.Size.ofBytes (UInt64.ofNat (finish.bytes.toNat - 1)))).1 = endBlock := by
    simp [lm22BitIndex, lm22SizeBytes, lm22BlockSize, Miri.ABI.Size.ofBytes, hsub1_u64, endBlock]
  unfold lm22FindBitFast
  simp only [hnot_ge, ↓reduceIte, hbit_start, hsz_end, bind, Except.bind,
    hbit_end, hget_start]
  rw [hsearch_ok]
  dsimp only [bind, Except.bind]
  by_cases hlt_blk : startBlock < endBlock
  · have hfull : startBlock * 64 + 64 ≤ finish.bytes.toNat := by omega
    have hfn := hfirst_none hfull
    subst hfn
    obtain ⟨r, hloop, hr⟩ :=
      lm22FindBitStep_loop_all_true words (finishBytes := lm22SizeBytes finish)
        (by unfold lm22SizeBytes; omega) hfin_lt (by unfold lm22SizeBytes; exact hsz)
        (endBlock + 1 - (startBlock + 1)) (startBlock + 1)
        (by unfold lm22SizeBytes; omega)
        (fun b hb1 hb2 => hinit b (by omega) hb2)
    simp only [hlt_blk, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
    unfold lm22FindBitStep at hloop
    dsimp only [bind, Except.bind] at hloop
    rw [hloop]
    rcases hr with rfl | rfl <;> rfl
  · cases first with
    | none =>
      simp [hlt_blk, pure, Except.pure]
    | some idx =>
      have hge : finish.bytes.toNat ≤ idx.bytes.toNat := hfirst_ge idx rfl
      have hnot_lt : ¬ lm22SizeBytes idx < lm22SizeBytes finish := by
        unfold lm22SizeBytes; omega
      simp [hnot_lt, pure, Except.pure]

theorem initMaskWordRel_isRangeInitialized {mask : Miri.Memory.InitMask}
    {len start sz : Miri.ABI.Size} {words : Array UInt64}
    (hrel : InitMaskWordRel mask len words)
    (hsz_pos : 0 < sz.bytes.toNat)
    (hbound : start.bytes.toNat + sz.bytes.toNat ≤ len.bytes.toNat)
    (hinit : ∀ b, start.bytes.toNat ≤ b → b < start.bytes.toNat + sz.bytes.toNat →
      maskBlocksGetBit words b = true) :
    mask.isRangeInitialized (Miri.Memory.allocRange start sz) = .ok (.ok ()) := by
  obtain ⟨hlen, hsize, hblocks⟩ := hrel
  have hlen_lt : len.bytes.toNat < 2 ^ 64 := len.bytes.toNat_lt
  have hfits : start.bytes.toNat + sz.bytes.toNat < 2 ^ 64 := by omega
  let finish := Miri.ABI.Size.ofBytes (start.bytes + sz.bytes)
  have hfinish_nat : finish.bytes.toNat = start.bytes.toNat + sz.bytes.toNat := by
    simp [finish, Miri.ABI.Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt hfits]
  have hend : (Miri.Memory.allocRange start sz).endExclusive = .ok finish := by
    unfold Miri.Memory.AllocRange.endExclusive Miri.Memory.AllocRange.end Miri.Memory.allocRange
    have hno_wrap : ¬ start.bytes + sz.bytes < start.bytes := by
      simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt hfits]
      omega
    simp [Miri.ABI.Size.add, hno_wrap, Except.mapError, finish]
  have hnot_gt : ¬ finish.bytes > mask.len.bytes := by
    rw [hlen]
    simp only [GT.gt, UInt64.lt_iff_toNat_lt]
    omega
  rw [lm22_isRangeInitialized_eq]
  unfold lm22IsRangeInitialized
  simp only [hend, bind, Except.bind, hnot_gt, ↓reduceIte]
  rcases hblocks with ⟨hb, rfl⟩ | ⟨hb, _⟩ | hb
  · exfalso
    have h0 := hinit start.bytes.toNat (by omega) (by omega)
    simp at h0
  · simp [hb, pure, Except.pure]
  · rw [hb]
    have hfb := lm22FindBitFast_false_eq_none words
      (start := (Miri.Memory.allocRange start sz).start) (finish := finish)
      (by simp [Miri.Memory.allocRange, hfinish_nat]; omega)
      (by rw [hsize]; simp [hfinish_nat]; omega)
      (fun b h1 h2 => hinit b h1 (by simpa [hfinish_nat] using h2))
    simp [hfb, pure, Except.pure]

private theorem lm22Materialize_lazy_false {len : Miri.ABI.Size}
    (hpos : 0 < len.bytes.toNat) :
    lm22Materialize ⟨.Lazy false, len⟩ = .ok ⟨initWordsFalse len⟩ := by
  unfold lm22Materialize lm22Grow initWordsFalse
  have hne0 : ¬ len.bytes.toNat = 0 := by omega
  simp [lm22SizeBytes, Miri.ABI.Size.ofBytes, hne0, lm22BlockSize, pure, Except.pure]

private theorem maskBlocksGetBit_set_setInitWordRange (words : Array UInt64) {idx : Nat}
    (hidx : idx < words.size) {lo hi : Nat} (hle : lo ≤ hi) (b : Nat) :
    maskBlocksGetBit (words.set idx (setInitWordRange (words[idx]'hidx) lo hi) hidx) b =
      (maskBlocksGetBit words b || decide (b / 64 = idx ∧ lo ≤ b % 64 ∧ b % 64 < hi)) := by
  unfold maskBlocksGetBit
  rw [Array.getElem?_set]
  by_cases heq : idx = b / 64
  · subst heq
    simp only [↓reduceIte, Array.getElem?_eq_getElem hidx]
    rw [testBit_setInitWordRange (words[b / 64]'hidx) hle (Nat.mod_lt b (by decide))]
    by_cases hrange : lo ≤ b % 64 ∧ b % 64 < hi <;> simp [hrange]
  · have hne : ¬ b / 64 = idx := fun h => heq h.symm
    simp [heq, hne]

private theorem maskBlocksGetBit_set_wordMask (words : Array UInt64) {idx : Nat}
    (hidx : idx < words.size) (b : Nat) :
    maskBlocksGetBit (words.set idx (UInt64.ofNat lm22WordMask) hidx) b =
      (maskBlocksGetBit words b || decide (b / 64 = idx)) := by
  unfold maskBlocksGetBit
  rw [Array.getElem?_set]
  by_cases heq : idx = b / 64
  · subst heq
    simp only [↓reduceIte, decide_true, Bool.or_true, Array.getElem?_eq_getElem hidx]
    have hval : (UInt64.ofNat lm22WordMask).toNat = 2 ^ 64 - 1 := rfl
    rw [hval, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true (Nat.mod_lt b (by decide))
  · have hne : ¬ b / 64 = idx := fun h => heq h.symm
    simp [heq, hne]

private def lm22SetFullBlockStep (block : Nat) (words : Array UInt64) :
    Except Miri.Memory.InitMaskError (ForInStep (Array UInt64)) := do
  let words' ← lm22SetBlock words block (UInt64.ofNat lm22WordMask)
  return ForInStep.yield words'

private theorem lm22SetFullBlockStep_loop :
    ∀ m k (words : Array UInt64), k + m ≤ words.size →
      ∃ words' : Array UInt64,
        forIn (List.range' k m) words lm22SetFullBlockStep = .ok words' ∧
        words'.size = words.size ∧
        ∀ b, maskBlocksGetBit words' b =
          (maskBlocksGetBit words b || decide (k ≤ b / 64 ∧ b / 64 < k + m)) := by
  intro m
  induction m with
  | zero =>
    intro k words _
    refine ⟨words, rfl, rfl, fun b => ?_⟩
    have hfalse : ¬ (k ≤ b / 64 ∧ b / 64 < k + 0) := by omega
    rw [decide_eq_false hfalse, Bool.or_false]
  | succ m ih =>
    intro k words hkm
    rw [List.range'_succ, List.forIn_cons]
    have hk_lt : k < words.size := by omega
    let words₁ := words.set k (UInt64.ofNat lm22WordMask) hk_lt
    have hstep : lm22SetFullBlockStep k words = .ok (.yield words₁) := by
      unfold lm22SetFullBlockStep lm22SetBlock
      simp [hk_lt, words₁, bind, Except.bind, pure, Except.pure]
    rw [hstep]
    have hsz₁ : words₁.size = words.size := by simp [words₁]
    obtain ⟨words', hfor, hsz', hbits'⟩ := ih (k + 1) words₁ (by omega)
    refine ⟨words', hfor, hsz'.trans hsz₁, fun b => ?_⟩
    rw [hbits' b, maskBlocksGetBit_set_wordMask words hk_lt b, Bool.or_assoc]
    congr 1
    by_cases h1 : b / 64 = k <;> by_cases h2 : k + 1 ≤ b / 64 ∧ b / 64 < k + 1 + m <;>
      simp [h1, h2] <;> omega

private theorem lm22SetRangeInbounds_true_spec (words : Array UInt64)
    {start finish : Miri.ABI.Size}
    (hpos : start.bytes.toNat < finish.bytes.toNat)
    (hsz : finish.bytes.toNat / 64 < words.size) :
    ∃ words' : Array UInt64,
      lm22SetRangeInbounds ⟨words⟩ start finish true = .ok ⟨words'⟩ ∧
      words'.size = words.size ∧
      ∀ b, maskBlocksGetBit words' b =
        (maskBlocksGetBit words b ||
          decide (start.bytes.toNat ≤ b ∧ b < finish.bytes.toNat)) := by
  let blockA := start.bytes.toNat / 64
  let bitA := start.bytes.toNat % 64
  let blockB := finish.bytes.toNat / 64
  let bitB := finish.bytes.toNat % 64
  have hblkA_sz : blockA < words.size := by omega
  have hblkB_sz : blockB < words.size := hsz
  have hgetA : lm22GetBlock ⟨words⟩ blockA = .ok (words[blockA]'hblkA_sz) := by
    simp [lm22GetBlock, hblkA_sz]
  by_cases heq_blk : blockA = blockB
  · have hbit_lt : bitA < bitB := by omega
    have hbitB_ne0 : ¬ bitB = 0 := by omega
    let words' := words.set blockA (setInitWordRange (words[blockA]'hblkA_sz) bitA bitB) hblkA_sz
    refine ⟨words', ?_, by simp [words'], fun b => ?_⟩
    · unfold lm22SetRangeInbounds
      simp [lm22BitIndex, lm22SizeBytes, lm22BlockSize, blockA, bitA, blockB, bitB,
        heq_blk, hbitB_ne0, lm22GetBlock, lm22SetBlock, hblkB_sz, setInitWordRange,
        words', bind, Except.bind, pure, Except.pure]
    · rw [maskBlocksGetBit_set_setInitWordRange words hblkA_sz (by omega) b]
      congr 1
      by_cases h1 : b / 64 = blockA ∧ bitA ≤ b % 64 ∧ b % 64 < bitB <;>
        by_cases h2 : start.bytes.toNat ≤ b ∧ b < finish.bytes.toNat <;>
        simp [h1, h2] <;> omega
  · have hblk_lt : blockA < blockB := by omega
    let wordsA := words.set blockA (setInitWordRange (words[blockA]'hblkA_sz) bitA 64) hblkA_sz
    have hszA : wordsA.size = words.size := by simp [wordsA]
    have hblkB_szA : blockB < wordsA.size := by rw [hszA]; exact hblkB_sz
    have hsetA : lm22SetBlock words blockA
        (lm22SetWordRange (words[blockA]'hblkA_sz).toNat bitA 64 true) = .ok wordsA := by
      simp [lm22SetBlock, hblkA_sz, wordsA, setInitWordRange]
    by_cases hbitB0 : bitB = 0
    · obtain ⟨words', hfor, hsz', hbits'⟩ :=
        lm22SetFullBlockStep_loop (blockB - (blockA + 1)) (blockA + 1) wordsA (by omega)
      refine ⟨words', ?_, hsz'.trans hszA, fun b => ?_⟩
      · unfold lm22SetRangeInbounds
        simp only [lm22BitIndex, lm22SizeBytes, lm22BlockSize, blockA, bitA, blockB, bitB,
          beq_iff_eq, heq_blk, ↓reduceIte, hgetA, hsetA, hbitB0, bne_self_eq_false,
          Bool.false_eq_true, bind, Except.bind, pure, Except.pure,
          Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.div_one]
        change (forIn (List.range' (blockA + 1) (blockB - (blockA + 1))) wordsA
            lm22SetFullBlockStep >>= fun ws =>
            pure (Miri.Memory.InitMaskMaterialized.mk ws)) = .ok ⟨words'⟩
        rw [hfor]
        rfl
      · rw [hbits' b,
          maskBlocksGetBit_set_setInitWordRange words hblkA_sz
            (Nat.le_of_lt (Nat.mod_lt _ (by decide))) b,
          Bool.or_assoc]
        congr 1
        by_cases h1 : b / 64 = blockA ∧ bitA ≤ b % 64 ∧ b % 64 < 64 <;>
          by_cases h2 : blockA + 1 ≤ b / 64 ∧ b / 64 < blockA + 1 + (blockB - (blockA + 1)) <;>
          by_cases h3 : start.bytes.toNat ≤ b ∧ b < finish.bytes.toNat <;>
          simp [h1, h2, h3] <;> omega
    · let wordsB := wordsA.set blockB (setInitWordRange (wordsA[blockB]'hblkB_szA) 0 bitB) hblkB_szA
      have hszB : wordsB.size = words.size := by simp [wordsB, hszA]
      have hgetB : lm22GetBlock ⟨wordsA⟩ blockB = .ok (wordsA[blockB]'hblkB_szA) := by
        simp [lm22GetBlock, hblkB_szA]
      have hsetB : lm22SetBlock wordsA blockB
          (lm22SetWordRange (wordsA[blockB]'hblkB_szA).toNat 0 bitB true) = .ok wordsB := by
        simp [lm22SetBlock, hblkB_szA, wordsB, setInitWordRange]
      obtain ⟨words', hfor, hsz', hbits'⟩ :=
        lm22SetFullBlockStep_loop (blockB - (blockA + 1)) (blockA + 1) wordsB (by omega)
      refine ⟨words', ?_, hsz'.trans hszB, fun b => ?_⟩
      · unfold lm22SetRangeInbounds
        have hbne : (bitB != 0) = true := bne_iff_ne.mpr hbitB0
        simp only [lm22BitIndex, lm22SizeBytes, lm22BlockSize, blockA, bitA, blockB, bitB,
          beq_iff_eq, heq_blk, ↓reduceIte, hgetA, hsetA, hbne, hgetB, hsetB,
          bind, Except.bind, pure, Except.pure,
          Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.div_one]
        change (forIn (List.range' (blockA + 1) (blockB - (blockA + 1))) wordsB
            lm22SetFullBlockStep >>= fun ws =>
            pure (Miri.Memory.InitMaskMaterialized.mk ws)) = .ok ⟨words'⟩
        rw [hfor]
        rfl
      · rw [hbits' b,
          maskBlocksGetBit_set_setInitWordRange wordsA hblkB_szA (Nat.zero_le _) b,
          maskBlocksGetBit_set_setInitWordRange words hblkA_sz
            (Nat.le_of_lt (Nat.mod_lt _ (by decide))) b,
          Bool.or_assoc, Bool.or_assoc]
        congr 1
        by_cases h1 : b / 64 = blockA ∧ bitA ≤ b % 64 ∧ b % 64 < 64 <;>
          by_cases h2 : b / 64 = blockB ∧ 0 ≤ b % 64 ∧ b % 64 < bitB <;>
          by_cases h3 : blockA + 1 ≤ b / 64 ∧ b / 64 < blockA + 1 + (blockB - (blockA + 1)) <;>
          by_cases h4 : start.bytes.toNat ≤ b ∧ b < finish.bytes.toNat <;>
          simp [h1, h2, h3, h4] <;> omega

theorem initMaskWordRel_setRange_true {mask : Miri.Memory.InitMask}
    {len start sz : Miri.ABI.Size} {words : Array UInt64}
    (hrel : InitMaskWordRel mask len words)
    (hsz_pos : 0 < sz.bytes.toNat)
    (hbound : start.bytes.toNat + sz.bytes.toNat ≤ len.bytes.toNat) :
    ∃ mask' words',
      mask.setRange (Miri.Memory.allocRange start sz) true = .ok mask' ∧
      InitMaskWordRel mask' len words' ∧
      ∀ b < len.bytes.toNat,
        maskBlocksGetBit words' b =
          (maskBlocksGetBit words b ||
            decide (start.bytes.toNat ≤ b ∧ b < start.bytes.toNat + sz.bytes.toNat)) := by
  obtain ⟨hlen, hsize, hblocks⟩ := hrel
  have hlen_lt : len.bytes.toNat < 2 ^ 64 := len.bytes.toNat_lt
  have hfits : start.bytes.toNat + sz.bytes.toNat < 2 ^ 64 := by omega
  obtain ⟨finish, hfin_def⟩ : ∃ f, f = Miri.ABI.Size.ofBytes (start.bytes + sz.bytes) := ⟨_, rfl⟩
  have hfinish_nat : finish.bytes.toNat = start.bytes.toNat + sz.bytes.toNat := by
    simp [hfin_def, Miri.ABI.Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt hfits]
  have hend : (Miri.Memory.allocRange start sz).endExclusive = .ok finish := by
    unfold Miri.Memory.AllocRange.endExclusive Miri.Memory.AllocRange.end Miri.Memory.allocRange
    have hno_wrap : ¬ start.bytes + sz.bytes < start.bytes := by
      simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt hfits]
      omega
    simp [Miri.ABI.Size.add, hno_wrap, Except.mapError, hfin_def]
  have hfin_le_len : finish.bytes ≤ mask.len.bytes := by
    rw [hlen]
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  have hnot_gt : ¬ finish.bytes > mask.len.bytes := by
    rw [hlen]
    simp only [GT.gt, UInt64.lt_iff_toNat_lt]
    omega
  rw [lm22_setRange_eq]
  unfold lm22SetRange
  rw [hend]
  have hstart_eq : (Miri.Memory.allocRange start sz).start = start := rfl
  simp only [hstart_eq, bind, Except.bind]
  by_cases hfull : start.bytes = 0 ∧ mask.len.bytes ≤ finish.bytes
  · have hstart0 : start.bytes.toNat = 0 := by simp [hfull.1]
    have hfin_eq_len : finish = len := by
      have hle1 := UInt64.le_iff_toNat_le.mp hfull.2
      rw [hlen] at hle1
      have heq_bytes : finish.bytes = len.bytes := UInt64.toNat_inj.mp (by omega)
      exact congrArg Miri.ABI.Size.ofBytes heq_bytes
    refine ⟨⟨.Lazy true, len⟩, initWordsTrue len, ?_,
      ⟨rfl, by simp [initWordsTrue], Or.inr (Or.inl ⟨rfl, rfl⟩)⟩, ?_⟩
    · rcases hblocks with ⟨hb, _⟩ | ⟨hb, _⟩ | hb <;>
        (rw [hb]; dsimp only; simp only [hfull]; rw [hfin_eq_len]; rfl)
    · intro b hb
      have hsz_eq : sz.bytes.toNat = len.bytes.toNat := by
        have : finish.bytes.toNat = len.bytes.toNat := by rw [hfin_eq_len]
        omega
      have hin : start.bytes.toNat ≤ b ∧ b < start.bytes.toNat + sz.bytes.toNat := by omega
      rw [maskBlocksGetBit_initWordsTrue hb]
      simp [hin]
  · rcases hblocks with ⟨hb, rfl⟩ | ⟨hb, rfl⟩ | hb
    · have hmat : lm22Materialize mask = .ok ⟨initWordsFalse len⟩ := by
        cases mask with
        | mk bl l =>
          dsimp only at hb hlen
          subst hb; subst hlen
          exact lm22Materialize_lazy_false (by omega)
      obtain ⟨words', hsri, hsz', hbits'⟩ :=
        lm22SetRangeInbounds_true_spec (initWordsFalse len)
          (start := start) (finish := finish) (by omega) (by rw [hsize]; omega)
      refine ⟨⟨.Materialized ⟨words'⟩, len⟩, words', ?_,
        ⟨rfl, hsz'.trans hsize, Or.inr (Or.inr rfl)⟩, ?_⟩
      · rw [hb]
        dsimp only
        simp only [hfull, hmat, hfin_le_len, hsri, pure, Except.pure]
        rw [hlen]
        rfl
      · intro b _
        rw [hbits' b, hfinish_nat]
    · refine ⟨mask, initWordsTrue len, ?_, ⟨hlen, hsize, Or.inr (Or.inl ⟨hb, rfl⟩)⟩, ?_⟩
      · rw [hb]
        dsimp only
        simp only [hfull, ↓reduceIte, beq_self_eq_true, hnot_gt, pure, Except.pure]
      · intro b hb
        rw [maskBlocksGetBit_initWordsTrue hb]
        simp
    · obtain ⟨words', hsri, hsz', hbits'⟩ :=
        lm22SetRangeInbounds_true_spec words
          (start := start) (finish := finish) (by omega) (by rw [hsize]; omega)
      refine ⟨⟨.Materialized ⟨words'⟩, len⟩, words', ?_,
        ⟨rfl, hsz'.trans hsize, Or.inr (Or.inr rfl)⟩, ?_⟩
      · rw [hb]
        dsimp only
        simp only [hfull, hfin_le_len, hsri, pure, Except.pure]
        rw [hlen]
        rfl
      · intro b _
        rw [hbits' b, hfinish_nat]

/-! ## 4. Byte-Array Slice Disjointness and Little-Endian Round-Trip -/

theorem extract_writeBytes_self (raw mid : Array UInt8) {s sz : Nat}
    (hmid : mid.size = sz) (hbnd : s + sz ≤ raw.size) :
    (raw.extract 0 s ++ mid ++ raw.extract (s + sz) raw.size).extract s (s + sz) = mid := by
  have hsize_total :
      (raw.extract 0 s ++ mid ++ raw.extract (s + sz) raw.size).size = raw.size := by
    simp only [Array.size_append, Array.size_extract, hmid]
    omega
  apply Array.ext
  · simp only [Array.size_extract, hsize_total, hmid]
    omega
  · intro i hi1 hi2
    rw [Array.getElem_extract]
    have hpre_sz : (raw.extract 0 s).size = s := by
      simp only [Array.size_extract]; omega
    have hpre_mid_sz : (raw.extract 0 s ++ mid).size = s + sz := by
      simp only [Array.size_append, hpre_sz, hmid]
    have hlt_mid : s + i < (raw.extract 0 s ++ mid).size := by
      rw [hpre_mid_sz]; omega
    have hge_pre : ¬ s + i < (raw.extract 0 s).size := by
      rw [hpre_sz]; omega
    rw [Array.getElem_append_left hlt_mid, Array.getElem_append_right (Nat.not_lt.mp hge_pre)]
    simp only [hpre_sz, Nat.add_sub_cancel_left]

theorem extract_writeBytes_disjoint (raw mid : Array UInt8) {s sz o osz : Nat}
    (hmid : mid.size = sz) (hbnd1 : s + sz ≤ raw.size) (hbnd2 : o + osz ≤ raw.size)
    (hdisj : o + osz ≤ s ∨ s + sz ≤ o) :
    (raw.extract 0 s ++ mid ++ raw.extract (s + sz) raw.size).extract o (o + osz) =
      raw.extract o (o + osz) := by
  have hsize_total :
      (raw.extract 0 s ++ mid ++ raw.extract (s + sz) raw.size).size = raw.size := by
    simp only [Array.size_append, Array.size_extract, hmid]
    omega
  have hpre_sz : (raw.extract 0 s).size = s := by
    simp only [Array.size_extract]; omega
  have hpre_mid_sz : (raw.extract 0 s ++ mid).size = s + sz := by
    simp only [Array.size_append, hpre_sz, hmid]
  apply Array.ext
  · simp only [Array.size_extract, hsize_total]
  · intro i hi1 hi2
    have hi_lt : i < osz := by
      simp only [Array.size_extract] at hi2
      omega
    rw [Array.getElem_extract, Array.getElem_extract]
    rcases hdisj with hleft | hright
    · have hlt_pre : o + i < (raw.extract 0 s).size := by
        rw [hpre_sz]; omega
      have hlt_mid : o + i < (raw.extract 0 s ++ mid).size := by
        rw [hpre_mid_sz]; omega
      rw [Array.getElem_append_left hlt_mid, Array.getElem_append_left hlt_pre,
        Array.getElem_extract]
      simp only [Nat.zero_add]
    · have hge_mid : (raw.extract 0 s ++ mid).size ≤ o + i := by
        rw [hpre_mid_sz]; omega
      rw [Array.getElem_append_right hge_mid, Array.getElem_extract]
      congr 1
      omega

/-- Little-endian bytes of `x` at byte positions `0, ..., n - 1`. -/
def lm22LeBytes (x n : Nat) : Array UInt8 :=
  ((List.range' 0 n).map fun i => UInt8.ofNat ((x / 2 ^ (8 * i)) % 256)).toArray

theorem lm22LeBytes_size (x n : Nat) : (lm22LeBytes x n).size = n := by
  simp [lm22LeBytes]

private theorem lm22_encode_loop (x : Nat) (l : List Nat) (acc : Array UInt8) :
    forIn (m := Except Miri.Memory.AllocError) l acc
        (fun index (r : Array UInt8) => pure (ForInStep.yield
          (r.push (UInt8.ofNat (x / 2 ^ (8 * index) % 256))))) =
      .ok (acc ++ (l.map fun i => UInt8.ofNat (x / 2 ^ (8 * i) % 256)).toArray) := by
  induction l generalizing acc with
  | nil => simp [pure, Except.pure]
  | cons i l ih =>
    rw [List.forIn_cons, pure_bind]
    simp only
    rw [ih]
    congr 1
    apply Array.toList_inj.mp
    simp

private theorem lm22TargetUIntBytes_spec (size : Miri.ABI.Size) (bits : Miri.ABI.U128)
    (hle : size.bytes.toNat ≤ 16) :
    lm22TargetUIntBytes annealTargetDataLayout size bits =
      .ok (lm22LeBytes bits.toNat size.bytes.toNat) := by
  have small : ¬ size.bytes > 16 := by
    simp only [GT.gt, UInt64.lt_iff_toNat_lt]
    simpa using Nat.not_lt.mpr hle
  have hendian : (annealTargetDataLayout.endian == Miri.ABI.Endian.little) = true := rfl
  unfold lm22TargetUIntBytes
  simp only [small, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range', hendian,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure]
  rw [lm22_encode_loop]
  simp [lm22LeBytes]

private def lm22LeSum (x k : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) + lm22LeSum x (k + 1) m

private theorem lm22LeSum_spec (x : Nat) :
    ∀ m k, x % 2 ^ (8 * k) + lm22LeSum x k m = x % 2 ^ (8 * (k + m)) := by
  intro m
  induction m with
  | zero => intro k; simp [lm22LeSum]
  | succ m ih =>
    intro k
    have hstep : x % 2 ^ (8 * k) + x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) =
        x % 2 ^ (8 * (k + 1)) := by
      rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add, Nat.mod_mul]
      simp only [show (2 : Nat) ^ 8 = 256 by rfl]
      rw [Nat.mul_comm (2 ^ (8 * k))]
    simp only [lm22LeSum]
    rw [← Nat.add_assoc, hstep, ih (k + 1), show k + 1 + m = k + (m + 1) by omega]

private theorem lm22_decode_loop (x n : Nat)
    (f : Nat → Nat → Except Miri.Memory.AllocError (ForInStep Nat))
    (hf : ∀ index s, index < n →
      f index s = .ok (.yield (s + x / 2 ^ (8 * index) % 256 * 2 ^ (8 * index)))) :
    ∀ m k acc, k + m ≤ n →
      forIn (List.range' k m) acc f = .ok (acc + lm22LeSum x k m) := by
  intro m
  induction m with
  | zero => intro k acc _; simp [lm22LeSum, pure, Except.pure]
  | succ m ih =>
    intro k acc hkm
    rw [List.range'_succ, List.forIn_cons, hf k acc (by omega)]
    simp only [lm22LeSum]
    rw [show (Except.ok (ForInStep.yield (acc + x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k))) :
        Except Miri.Memory.AllocError (ForInStep Nat)) = pure (ForInStep.yield _) from rfl,
      pure_bind]
    simp only
    rw [ih (k + 1) _ (by omega), Nat.add_assoc]

private theorem lm22ReadTargetUInt_leBytes (x n : Nat) (hn : n ≤ 16) :
    lm22ReadTargetUInt annealTargetDataLayout (lm22LeBytes x n) =
      .ok (BitVec.ofNat 128 (x % 2 ^ (8 * n))) := by
  have small : ¬ n > 16 := by omega
  have hendian : (annealTargetDataLayout.endian == Miri.ABI.Endian.little) = true := rfl
  unfold lm22ReadTargetUInt
  simp only [lm22LeBytes_size, small, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range',
    hendian, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [lm22_decode_loop x n _ ?hf n 0 0 (by omega)]
  · have := lm22LeSum_spec x n 0
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mod_one, Nat.zero_add] at this
    simp [this, pure, Except.pure, bind, Except.bind]
  · intro index s hi
    have hb : (x / 2 ^ (8 * index) % 256) < 256 := Nat.mod_lt _ (by decide)
    simp [lm22LeBytes, hi, pure, Except.pure, Nat.mod_eq_of_lt hb]

private theorem lm22_translateSizeBytes_toNat {sz : Nat} (h : ValidScalarBytes sz) :
    (translateSizeBytes sz).bytes.toNat = sz := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem lm22_translateSizeBytes_pos {sz : Nat} (h : ValidScalarBytes sz) :
    0 < (translateSizeBytes sz).bytes.toNat := by
  rw [lm22_translateSizeBytes_toNat h]
  rcases h with rfl | rfl | rfl | rfl | rfl <;> omega

private theorem lm22_translateSizeBytes_le_16 {sz : Nat} (h : ValidScalarBytes sz) :
    (translateSizeBytes sz).bytes.toNat ≤ 16 := by
  rw [lm22_translateSizeBytes_toNat h]
  rcases h with rfl | rfl | rfl | rfl | rfl <;> omega

private theorem lm22_scalarModulus_eq_two_pow (sz : Nat) :
    scalarModulus sz = 2 ^ (8 * sz) := by
  induction sz with
  | zero => rfl
  | succ k ih =>
    show 256 * scalarModulus k = 2 ^ (8 * (k + 1))
    rw [ih, show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add, Nat.mul_comm]

private theorem lm22_bitVec_ofNat_toNat {sz x : Nat}
    (hsz : ValidScalarBytes sz) (hx : x < scalarModulus sz) :
    (BitVec.ofNat 128 x).toNat = x := by
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hle : scalarModulus sz ≤ 2 ^ 128 := by
    rw [lm22_scalarModulus_eq_two_pow]
    exact Nat.pow_le_pow_right (by decide) (by rcases hsz with rfl | rfl | rfl | rfl | rfl <;> omega)
  omega

private theorem lm22_validScalarBytes_bits_pos {sz : Nat} (h : ValidScalarBytes sz) :
    0 < 8 * sz := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> omega

private theorem lm22_zeroExtend_extractLsb_eq_ofNat (w : Nat) (hw0 : 0 < w)
    (data : BitVec 128) :
    BitVec.zeroExtend 128 (BitVec.extractLsb (w - 1) 0 data) =
      BitVec.ofNat 128 (data.toNat % 2 ^ w) := by
  apply BitVec.eq_of_toNat_eq
  unfold BitVec.zeroExtend BitVec.extractLsb BitVec.extractLsb'
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hlen : w - 1 + 1 = w := by omega
  simp only [Nat.sub_zero, Nat.shiftRight_zero, hlen]

private theorem lm22_truncateFromUInt_spec {sz : Nat} (hsz : ValidScalarBytes sz)
    (data : BitVec 128) :
    ∃ msc : Miri.Memory.ScalarInt,
      Miri.Memory.ScalarInt.truncateFromUInt data (translateSizeBytes sz) =
        .ok (msc, BitVec.ofNat 128 (data.toNat % 2 ^ (8 * sz)) != data) ∧
      ScalarRel ⟨data.toNat % 2 ^ (8 * sz), sz⟩ msc := by
  have hw0 := lm22_validScalarBytes_bits_pos hsz
  have hze := lm22_zeroExtend_extractLsb_eq_ofNat (8 * sz) hw0 data
  have hmod : data.toNat % 2 ^ (8 * sz) < scalarModulus sz := by
    rw [lm22_scalarModulus_eq_two_pow]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hraw : ∃ msc : Miri.Memory.ScalarInt,
      Miri.Memory.ScalarInt.truncateFromUInt data (translateSizeBytes sz) =
        .ok (msc, BitVec.zeroExtend 128 (BitVec.extractLsb (8 * sz - 1) 0 data) != data) ∧
      ScalarRel ⟨data.toNat % 2 ^ (8 * sz), sz⟩ msc := by
    rcases hsz with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨_, rfl, ⟨by simp [ValidScalarBytes], hmod, rfl, hze⟩⟩
  obtain ⟨msc, hmsc, hrel⟩ := hraw
  rw [hze] at hmsc
  exact ⟨msc, hmsc, hrel⟩

private theorem lm22_tryFromUInt {sc : MirAst.ScalarInt}
    (hsz : ValidScalarBytes sc.sizeBytes) (hcan : sc.bits < scalarModulus sc.sizeBytes) :
    ∃ msc : Miri.Memory.ScalarInt,
      Miri.Memory.ScalarInt.tryFromUInt (BitVec.ofNat 128 sc.bits)
          (translateSizeBytes sc.sizeBytes) = .ok (some msc) ∧
      ScalarRel sc msc := by
  obtain ⟨msc, htr, hrel⟩ := lm22_truncateFromUInt_spec hsz (BitVec.ofNat 128 sc.bits)
  have hlt : sc.bits < 2 ^ (8 * sc.sizeBytes) := by
    rw [← lm22_scalarModulus_eq_two_pow]; exact hcan
  have hmod : (BitVec.ofNat 128 sc.bits).toNat % 2 ^ (8 * sc.sizeBytes) = sc.bits := by
    rw [lm22_bitVec_ofNat_toNat hsz hcan, Nat.mod_eq_of_lt hlt]
  rw [hmod] at htr hrel
  have hsc : (⟨sc.bits, sc.sizeBytes⟩ : MirAst.ScalarInt) = sc := by
    cases sc; rfl
  rw [hsc] at hrel
  refine ⟨msc, ?_, hrel⟩
  unfold Miri.Memory.ScalarInt.tryFromUInt
  change (do
    let (result, overflow) ← Miri.Memory.ScalarInt.truncateFromUInt
      (BitVec.ofNat 128 sc.bits) (translateSizeBytes sc.sizeBytes)
    if overflow then return none else return some result) = .ok (some msc)
  rw [htr]
  simp [bne_self_eq_false, bind, Except.bind, pure, Except.pure]

private theorem lm22_scalarInt_ext {a b : Miri.Memory.ScalarInt}
    (hd : a.data = b.data) (hs : a.size = b.size) : a = b := by
  cases a
  cases b
  simp only [Miri.Memory.ScalarInt.data, Miri.Memory.ScalarInt.size] at hd hs
  subst hd
  subst hs
  rfl

private theorem lm22_fromUInt {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) :
    Miri.Memory.Scalar.fromUInt (Prov := AnnealProv) (BitVec.ofNat 128 sc.bits)
        (translateSizeBytes sc.sizeBytes) = .ok (Miri.Memory.Scalar.fromScalarInt msc) := by
  obtain ⟨msc', htry, hrel'⟩ := lm22_tryFromUInt hrel.validBytes hrel.canonical
  have heq : msc' = msc :=
    lm22_scalarInt_ext (hrel'.data_eq.trans hrel.data_eq.symm)
      (hrel'.size_eq.trans hrel.size_eq.symm)
  subst heq
  unfold Miri.Memory.Scalar.fromUInt
  simp [htry, Except.mapError, bind, Except.bind, pure, Except.pure]

private theorem lm22_toBitsOrPtrInternal {sc : MirAst.ScalarInt}
    {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBitsOrPtrInternal
        (translateSizeBytes sc.sizeBytes) = .ok (.bits (BitVec.ofNat 128 sc.bits)) := by
  unfold Miri.Memory.Scalar.toBitsOrPtrInternal
  simp only [Miri.Memory.Scalar.fromScalarInt, hrel.toBits_eq, Except.mapError, bind,
    Except.bind, pure, Except.pure]

/-! ## 5. Offset-Parametric `Allocation.writeScalar` and `Allocation.readScalar` -/

theorem lm22_allocRange_end {start sz : Miri.ABI.Size}
    (hfits : start.bytes.toNat + sz.bytes.toNat < 2 ^ 64) :
    (Miri.Memory.allocRange start sz).endExclusive =
      .ok (Miri.ABI.Size.ofBytes (start.bytes + sz.bytes)) := by
  unfold Miri.Memory.AllocRange.endExclusive Miri.Memory.AllocRange.end Miri.Memory.allocRange
  have hno_wrap : ¬ start.bytes + sz.bytes < start.bytes := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt hfits]
    omega
  simp [Miri.ABI.Size.add, hno_wrap, Except.mapError]

private theorem lm22CheckedSlice_ok {P E : Type} {A : Miri.Memory.Allocation P E}
    {start sz : Miri.ABI.Size}
    (hlen : (lm22AllocRaw A).size = A.byteSize.bytes.toNat)
    (hbnd : start.bytes.toNat + sz.bytes.toNat ≤ A.byteSize.bytes.toNat) :
    lm22CheckedSlice A (Miri.Memory.allocRange start sz) =
      .ok ((lm22AllocRaw A).extract start.bytes.toNat (start.bytes.toNat + sz.bytes.toNat)) := by
  have hfits : start.bytes.toNat + sz.bytes.toNat < 2 ^ 64 := by
    have := A.byteSize.bytes.toNat_lt
    omega
  have hend := lm22_allocRange_end hfits
  have hfin_nat :
      (Miri.ABI.Size.ofBytes (start.bytes + sz.bytes)).bytes.toNat =
        start.bytes.toNat + sz.bytes.toNat := by
    simp [Miri.ABI.Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt hfits]
  have hnot_gt1 : ¬ start.bytes > (Miri.ABI.Size.ofBytes (start.bytes + sz.bytes)).bytes := by
    simp only [GT.gt, UInt64.lt_iff_toNat_lt, hfin_nat]
    omega
  have hnot_gt2 : ¬ (Miri.ABI.Size.ofBytes (start.bytes + sz.bytes)).bytes > A.byteSize.bytes := by
    simp only [GT.gt, UInt64.lt_iff_toNat_lt, hfin_nat]
    omega
  have hstart_eq : (Miri.Memory.allocRange start sz).start = start := rfl
  unfold lm22CheckedSlice
  rw [hend]
  simp only [hlen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    Except.mapError, bind, Except.bind, hstart_eq, hnot_gt1, hnot_gt2,
    Bool.or_self, hfin_nat, pure, Except.pure]
  rfl

theorem alloc_readScalar_at_offset {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) {E : Type} {A : Miri.Memory.Allocation AnnealProv E}
    {start : Miri.ABI.Size}
    (hlen : (lm22AllocRaw A).size = A.byteSize.bytes.toNat)
    (hbnd : start.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat ≤
      A.byteSize.bytes.toNat)
    (hinit : A.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange start (translateSizeBytes sc.sizeBytes)) = .ok (.ok ()))
    (hbytes : (lm22AllocRaw A).extract start.bytes.toNat
        (start.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat) =
      lm22LeBytes sc.bits (translateSizeBytes sc.sizeBytes).bytes.toNat) :
    A.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange start (translateSizeBytes sc.sizeBytes)) false =
      .ok (Miri.Memory.Scalar.fromScalarInt msc) := by
  have hrange_sz :
      (Miri.Memory.allocRange start (translateSizeBytes sc.sizeBytes)).size =
        translateSizeBytes sc.sizeBytes := rfl
  have hn := lm22_translateSizeBytes_toNat hrel.validBytes
  have hn16 := lm22_translateSizeBytes_le_16 hrel.validBytes
  have hslice : lm22CheckedSlice A
      (Miri.Memory.allocRange start (translateSizeBytes sc.sizeBytes)) =
      .ok (lm22LeBytes sc.bits (translateSizeBytes sc.sizeBytes).bytes.toNat) := by
    rw [lm22CheckedSlice_ok hlen hbnd, hbytes]
  have hoff : Miri.Memory.PointerProvenance.offsetIsAddr AnnealProv = true := rfl
  have hmod : sc.bits % 2 ^ (8 * (translateSizeBytes sc.sizeBytes).bytes.toNat) = sc.bits := by
    rw [hn, ← lm22_scalarModulus_eq_two_pow]
    exact Nat.mod_eq_of_lt hrel.canonical
  rw [lm22_readScalar_eq]
  unfold lm22ReadScalar
  rw [hinit]
  simp only [Except.mapError, bind, Except.bind]
  rw [lm22_getBytesUnchecked_eq, hslice]
  simp only []
  rw [lm22ReadTargetUInt_leBytes _ _ hn16, hmod]
  simp only [Bool.false_eq_true, ↓reduceIte, hoff, hrange_sz, lm22_fromUInt hrel]

theorem alloc_readScalar_congr {E : Type}
    {A B : Miri.Memory.Allocation AnnealProv E}
    {start sz : Miri.ABI.Size}
    (hlenA : (lm22AllocRaw A).size = A.byteSize.bytes.toNat)
    (hlenB : (lm22AllocRaw B).size = B.byteSize.bytes.toNat)
    (hsz : B.byteSize = A.byteSize)
    (hinitA : A.initializationMask.isRangeInitialized (Miri.Memory.allocRange start sz) = .ok (.ok ()))
    (hinitB : B.initializationMask.isRangeInitialized (Miri.Memory.allocRange start sz) = .ok (.ok ()))
    (hbnd : start.bytes.toNat + sz.bytes.toNat ≤ A.byteSize.bytes.toNat)
    (hextract : (lm22AllocRaw B).extract start.bytes.toNat (start.bytes.toNat + sz.bytes.toNat) =
      (lm22AllocRaw A).extract start.bytes.toNat (start.bytes.toNat + sz.bytes.toNat)) :
    B.readScalar annealTargetDataLayout (Miri.Memory.allocRange start sz) false =
      A.readScalar annealTargetDataLayout (Miri.Memory.allocRange start sz) false := by
  have hbndB : start.bytes.toNat + sz.bytes.toNat ≤ B.byteSize.bytes.toNat := by
    rw [hsz]; exact hbnd
  have hslice_eq :
      lm22CheckedSlice B (Miri.Memory.allocRange start sz) =
        lm22CheckedSlice A (Miri.Memory.allocRange start sz) := by
    rw [lm22CheckedSlice_ok hlenB hbndB, lm22CheckedSlice_ok hlenA hbnd, hextract]
  have hoff : Miri.Memory.PointerProvenance.offsetIsAddr AnnealProv = true := rfl
  rw [lm22_readScalar_eq B, lm22_readScalar_eq A]
  unfold lm22ReadScalar
  rw [hinitB, hinitA]
  simp only [Except.mapError, bind, Except.bind, lm22_getBytesUnchecked_eq, hslice_eq,
    Bool.false_eq_true, ↓reduceIte, hoff]

theorem alloc_writeScalar_at_offset {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) {E : Type} {A : Miri.Memory.Allocation AnnealProv E}
    {start : Miri.ABI.Size} {words : Array UInt64}
    (hlen : A.len = A.byteSize.bytes.toNat)
    (hmut : A.mutability = .Mut)
    (hprov : A.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask : InitMaskWordRel A.initializationMask A.byteSize words)
    (hbnd : start.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat ≤
      A.byteSize.bytes.toNat) :
    ∃ (A' : Miri.Memory.Allocation AnnealProv E) (words' : Array UInt64),
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange start msc.size)
          (Miri.Memory.Scalar.fromScalarInt msc) A = .ok () A' ∧
      A'.byteSize = A.byteSize ∧
      A'.len = A.len ∧
      A'.mutability = .Mut ∧
      A'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      InitMaskWordRel A'.initializationMask A.byteSize words' ∧
      (∀ b < A.byteSize.bytes.toNat,
        maskBlocksGetBit words' b =
          (maskBlocksGetBit words b ||
            decide (start.bytes.toNat ≤ b ∧
              b < start.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat))) ∧
      lm22AllocRaw A' =
        (lm22AllocRaw A).extract 0 start.bytes.toNat ++
          lm22LeBytes sc.bits (translateSizeBytes sc.sizeBytes).bytes.toNat ++
          (lm22AllocRaw A).extract
            (start.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat)
            (lm22AllocRaw A).size ∧
      A'.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange start (translateSizeBytes sc.sizeBytes)) = .ok (.ok ()) ∧
      A'.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange start (translateSizeBytes sc.sizeBytes)) false =
        .ok (Miri.Memory.Scalar.fromScalarInt msc) := by
  have hsz_pos : 0 < (translateSizeBytes sc.sizeBytes).bytes.toNat :=
    lm22_translateSizeBytes_pos hrel.validBytes
  have hn16 : (translateSizeBytes sc.sizeBytes).bytes.toNat ≤ 16 :=
    lm22_translateSizeBytes_le_16 hrel.validBytes
  have hfits : start.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat < 2 ^ 64 := by
    have := A.byteSize.bytes.toNat_lt
    omega
  have hend := lm22_allocRange_end hfits
  have hrange_sz :
      (Miri.Memory.allocRange start (translateSizeBytes sc.sizeBytes)).size =
        translateSizeBytes sc.sizeBytes := rfl
  have hrange_start :
      (Miri.Memory.allocRange start (translateSizeBytes sc.sizeBytes)).start = start := rfl
  have hconv := lm22_toBitsOrPtrInternal hrel
  have hraw : (lm22AllocRaw A).size = A.byteSize.bytes.toNat := hlen
  have hslice : Miri.Memory.Allocation.getBytesUnchecked A
      (Miri.Memory.allocRange start (translateSizeBytes sc.sizeBytes)) =
      .ok ((lm22AllocRaw A).extract start.bytes.toNat
        (start.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat)) := by
    rw [lm22_getBytesUnchecked_eq]
    exact lm22CheckedSlice_ok hraw hbnd
  unfold Miri.Memory.Allocation.getBytesUnchecked at hslice
  obtain ⟨mask', words', hmask_set, hmask_rel', hword_bits⟩ :=
    initMaskWordRel_setRange_true hmask hsz_pos hbnd
  have hmask2 : A.initializationMask.setRange
      (Miri.Memory.allocRange start (translateSizeBytes sc.sizeBytes)) true = .ok mask' :=
    hmask_set
  unfold Miri.Memory.Allocation.initializationMask at hmask2
  have hprov2 := hprov
  unfold Miri.Memory.Allocation.provenanceMap at hprov2
  rw [hrel.size_eq]
  unfold Miri.Memory.Allocation.writeScalar
  simp only [hmut, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hrange_sz, hconv, pure_bind]
  rw [hslice]
  simp only [hmask2]
  rw [hprov2, Miri.Memory.ProvenanceMap.clear_new _ _ _ _ ?pos hend]
  case pos => decide
  simp only []
  split
  · rename_i data hdata
    have hdata' : lm22TargetUIntBytes annealTargetDataLayout
        (translateSizeBytes sc.sizeBytes) (BitVec.ofNat 128 sc.bits) = .ok data := hdata
    rw [lm22TargetUIntBytes_spec _ _ hn16] at hdata'
    cases hdata'
    have htoNat : (BitVec.ofNat 128 sc.bits).toNat = sc.bits :=
      lm22_bitVec_ofNat_toNat hrel.validBytes hrel.canonical
    have hbytes_sz :
        ((lm22AllocRaw A).extract 0 start.bytes.toNat ++
          lm22LeBytes (BitVec.ofNat 128 sc.bits).toNat
            (translateSizeBytes sc.sizeBytes).bytes.toNat ++
          (lm22AllocRaw A).extract
            (start.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat)
            (lm22AllocRaw A).size).size =
        A.byteSize.bytes.toNat := by
      simp only [Array.size_append, Array.size_extract, lm22LeBytes_size, hraw]
      omega
    cases A
    dsimp only [lm22AllocRaw, Miri.Memory.Allocation.byteSize,
      Miri.Memory.Allocation.len, Miri.Memory.Allocation.mutability,
      Miri.Memory.Allocation.provenanceMap,
      Miri.Memory.Allocation.initializationMask] at hbytes_sz hlen hraw hbnd hmask_rel' hword_bits ⊢
    simp only [hrange_start, hbytes_sz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    have hinit_i :
        mask'.isRangeInitialized
          (Miri.Memory.allocRange start (translateSizeBytes sc.sizeBytes)) = .ok (.ok ()) := by
      apply initMaskWordRel_isRangeInitialized hmask_rel' hsz_pos hbnd
      intro b hb1 hb2
      rw [hword_bits b (by omega)]
      have hin : start.bytes.toNat ≤ b ∧
          b < start.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat := ⟨hb1, hb2⟩
      simp [hin]
    refine ⟨_, words', rfl, rfl, ?_, rfl, rfl, hmask_rel', hword_bits, ?_, hinit_i, ?_⟩
    · dsimp only [Miri.Memory.Allocation.len]
      simp only [Array.size_append, Array.size_extract, lm22LeBytes_size]
      omega
    · simp only [htoNat]
    · apply alloc_readScalar_at_offset hrel
      · dsimp only [lm22AllocRaw, Miri.Memory.Allocation.byteSize]
        exact hbytes_sz
      · exact hbnd
      · exact hinit_i
      · simp only [lm22AllocRaw, htoNat]
        exact extract_writeBytes_self _
          (lm22LeBytes sc.bits (translateSizeBytes sc.sizeBytes).bytes.toNat)
          (lm22LeBytes_size _ _) (by omega)
  · rename_i err herr
    have herr' : lm22TargetUIntBytes annealTargetDataLayout
        (translateSizeBytes sc.sizeBytes) (BitVec.ofNat 128 sc.bits) = .error err := herr
    rw [lm22TargetUIntBytes_spec _ _ hn16] at herr'
    cases herr'

/-! ## 6. `ValidStructLayout` and `writeField_preserves_other_fields_and_padding` (`LM-2.2`) -/

/-- Descriptor for a single struct/tuple leaf field: its byte offset within the
aggregate, its MirAst type `ty`, and its translated layout `fieldLayout`.
In `LM-2.2`, leaf descriptors represent positive-size primitive scalar fields
(`1, 2, 4, 8, 16` bytes, enforced by `IsPrimScalarTy` / `NoZeroByteLeaves` in
`ProjLM2_2.lean` and `SimLM2_2.lean`); zero-sized unit `()` is modeled by the
base `Simulation.lean` unit fragment rather than as a byte-level memory leaf. -/
structure StructFieldDesc where
  offset : Miri.ABI.Size
  ty : Ty
  fieldLayout : Miri.ABI.LayoutData

/-- Predicate classifying byte offset `p < totalSize.bytes.toNat` as an
inter-field or trailing alignment padding byte when it falls outside every
field interval `[f.offset, f.offset + f.fieldLayout.size)`. -/
def isStructPaddingByte
    (fields : List StructFieldDesc)
    (totalSize : Miri.ABI.Size)
    (p : Nat) : Prop :=
  p < totalSize.bytes.toNat ∧
  ∀ f ∈ fields,
    p < f.offset.bytes.toNat ∨
    f.offset.bytes.toNat + f.fieldLayout.size.bytes.toNat ≤ p

/-- Well-formedness predicate for product/tuple/struct layouts (`LM-2.2`):
1. Every field `i` has an in-bounds byte interval
   `[offsets[i], offsets[i] + fieldLayout(i).size)` within `layout.size`
   (with no artificial 64-byte size restriction; statement/allocation-level
   theorems require `layout.size.bytes.toNat < 2 ^ 32` (4 GiB) only because
   `annealStackBaseAddr id = id <<< 32` spaces stack allocations by `2 ^ 32`
   bytes so allocations `< 2 ^ 32` bytes never wrap 64-bit addresses or overlap
   while `id < 2 ^ 32`).
2. Pairwise disjointness: for all `i ≠ j`, the field byte intervals are disjoint.
3. Alignment: `(2 ^ fieldLayout(i).align.abi.pow2)` divides `offsets[i].bytes.toNat`.
4. `layout.fields` matches the field offsets (`FieldsShape.Primitive` or
   `FieldsShape.Arbitrary`). -/
structure ValidStructLayout
    (layout : Miri.ABI.LayoutData)
    (fields : List StructFieldDesc) : Prop where
  fields_in_bounds :
    ∀ i (hi : i < fields.length),
      (fields[i]'hi).offset.bytes.toNat +
        (fields[i]'hi).fieldLayout.size.bytes.toNat ≤ layout.size.bytes.toNat
  fields_disjoint :
    ∀ i j (hi : i < fields.length) (hj : j < fields.length),
      i ≠ j →
      (fields[i]'hi).offset.bytes.toNat +
        (fields[i]'hi).fieldLayout.size.bytes.toNat ≤
        (fields[j]'hj).offset.bytes.toNat ∨
      (fields[j]'hj).offset.bytes.toNat +
        (fields[j]'hj).fieldLayout.size.bytes.toNat ≤
        (fields[i]'hi).offset.bytes.toNat
  fields_aligned :
    ∀ i (hi : i < fields.length),
      (2 ^ (fields[i]'hi).fieldLayout.align.abi.pow2) ∣
        (fields[i]'hi).offset.bytes.toNat
  fields_shape_valid :
    (fields.length = 1 ∧ layout.fields = .Primitive ∧
      (fields[0]?.map (·.offset) = some Miri.ABI.Size.ZERO)) ∨
    ∃ topOffsets memoryIndex,
      layout.fields = .Arbitrary topOffsets memoryIndex ∧
      memoryIndex.size = topOffsets.size ∧
      (∀ off ∈ topOffsets.toList, off ∈ fields.map (·.offset)) ∧
      (∀ f ∈ fields, ∃ topOff ∈ topOffsets.toList,
        topOff.bytes.toNat ≤ f.offset.bytes.toNat)

/-- Writing scalar field `i` of a `ValidStructLayout`-governed aggregate into an
allocation `A` via `Allocation.writeScalar`:
1. Succeeds and reads back the newly written scalar at field `i`.
2. Preserves `isRangeInitialized` and `Allocation.readScalar` on every other
   initialized field `j ≠ i`.
3. Preserves `InitMask.get` (and in particular `InitMask.get = .ok false` for
   uninitialized inter-field padding bytes) at every padding byte offset `p`. -/
theorem writeField_preserves_other_fields_and_padding
    {layout : Miri.ABI.LayoutData}
    {fields : List StructFieldDesc}
    (hvalid : ValidStructLayout layout fields)
    {i : Nat} (hi : i < fields.length)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc)
    (hfield_sz : (fields[i]'hi).fieldLayout.size = translateSizeBytes sc.sizeBytes)
    {E : Type} {A : Miri.Memory.Allocation AnnealProv E} {words : Array UInt64}
    (hbsize : A.byteSize = layout.size)
    (hlen : A.len = A.byteSize.bytes.toNat)
    (hmut : A.mutability = .Mut)
    (hprov : A.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask : InitMaskWordRel A.initializationMask A.byteSize words) :
    ∃ (A' : Miri.Memory.Allocation AnnealProv E) (words' : Array UInt64),
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange (fields[i]'hi).offset msc.size)
          (Miri.Memory.Scalar.fromScalarInt msc) A = .ok () A' ∧
      A'.byteSize = layout.size ∧
      A'.len = A'.byteSize.bytes.toNat ∧
      A'.mutability = .Mut ∧
      A'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      InitMaskWordRel A'.initializationMask A'.byteSize words' ∧
      (∀ b, b < layout.size.bytes.toNat →
        maskBlocksGetBit words' b =
          (maskBlocksGetBit words b ||
            decide ((fields[i]'hi).offset.bytes.toNat ≤ b ∧
              b < (fields[i]'hi).offset.bytes.toNat +
                (fields[i]'hi).fieldLayout.size.bytes.toNat))) ∧
      A'.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange (fields[i]'hi).offset (fields[i]'hi).fieldLayout.size) =
        .ok (.ok ()) ∧
      A'.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange (fields[i]'hi).offset (fields[i]'hi).fieldLayout.size) false =
        .ok (Miri.Memory.Scalar.fromScalarInt msc) ∧
      (∀ j (hj : j < fields.length), j ≠ i →
        0 < (fields[j]'hj).fieldLayout.size.bytes.toNat →
        (∀ b, (fields[j]'hj).offset.bytes.toNat ≤ b →
          b < (fields[j]'hj).offset.bytes.toNat +
            (fields[j]'hj).fieldLayout.size.bytes.toNat →
          maskBlocksGetBit words b = true) →
        A'.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange (fields[j]'hj).offset (fields[j]'hj).fieldLayout.size) =
          .ok (.ok ()) ∧
        A'.readScalar annealTargetDataLayout
            (Miri.Memory.allocRange (fields[j]'hj).offset (fields[j]'hj).fieldLayout.size) false =
          A.readScalar annealTargetDataLayout
            (Miri.Memory.allocRange (fields[j]'hj).offset (fields[j]'hj).fieldLayout.size) false) ∧
      (∀ p, isStructPaddingByte fields layout.size p →
        A'.initializationMask.get (Miri.ABI.Size.ofBytes (UInt64.ofNat p)) =
          A.initializationMask.get (Miri.ABI.Size.ofBytes (UInt64.ofNat p))) := by
  have hbnd_i :
      (fields[i]'hi).offset.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat ≤
        A.byteSize.bytes.toNat := by
    rw [← hfield_sz, hbsize]
    exact hvalid.fields_in_bounds i hi
  obtain ⟨A', words', hwrite, hbsize', hlen', hmut', hprov', hmask', hword_bits, hraw', hinit_i, hread_i⟩ :=
    alloc_writeScalar_at_offset hrel hlen hmut hprov hmask hbnd_i
  rw [← hfield_sz] at hinit_i hread_i hword_bits hraw'
  have hrawA_len : (lm22AllocRaw A).size = A.byteSize.bytes.toNat := by
    have : (lm22AllocRaw A).size = A.len := by cases A; rfl
    rw [this, hlen]
  have hrawA'_len : (lm22AllocRaw A').size = A'.byteSize.bytes.toNat := by
    have : (lm22AllocRaw A').size = A'.len := by cases A'; rfl
    rw [this, hlen', hbsize', hlen]
  refine ⟨A', words', hwrite, hbsize'.trans hbsize, hlen'.trans (hlen.trans (by rw [hbsize'])),
    hmut', hprov', ?_, ?_, hinit_i, hread_i, ?_, ?_⟩
  · rw [hbsize']
    exact hmask'
  · intro b hb
    exact hword_bits b (by rw [hbsize]; exact hb)
  · intro j hj hne hj_pos hj_init
    have hbnd_j :
        (fields[j]'hj).offset.bytes.toNat +
          (fields[j]'hj).fieldLayout.size.bytes.toNat ≤ A.byteSize.bytes.toNat := by
      rw [hbsize]
      exact hvalid.fields_in_bounds j hj
    have hdisj :
        (fields[j]'hj).offset.bytes.toNat +
          (fields[j]'hj).fieldLayout.size.bytes.toNat ≤
          (fields[i]'hi).offset.bytes.toNat ∨
        (fields[i]'hi).offset.bytes.toNat +
          (fields[i]'hi).fieldLayout.size.bytes.toNat ≤
          (fields[j]'hj).offset.bytes.toNat :=
      hvalid.fields_disjoint j i hj hi hne
    have hinitA_j :
        A.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange (fields[j]'hj).offset (fields[j]'hj).fieldLayout.size) =
          .ok (.ok ()) :=
      initMaskWordRel_isRangeInitialized hmask hj_pos hbnd_j hj_init
    have hinitA'_j :
        A'.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange (fields[j]'hj).offset (fields[j]'hj).fieldLayout.size) =
          .ok (.ok ()) := by
      apply initMaskWordRel_isRangeInitialized hmask' hj_pos hbnd_j
      intro b hb1 hb2
      rw [hword_bits b (by omega), hj_init b hb1 hb2]
      simp
    refine ⟨hinitA'_j, ?_⟩
    apply alloc_readScalar_congr hrawA_len hrawA'_len hbsize'
      hinitA_j hinitA'_j hbnd_j
    rw [hraw']
    rw [hfield_sz] at hdisj ⊢
    exact extract_writeBytes_disjoint (lm22AllocRaw A)
      (lm22LeBytes sc.bits (translateSizeBytes sc.sizeBytes).bytes.toNat)
      (lm22LeBytes_size _ _)
      (by rw [hrawA_len]; exact hbnd_i)
      (by rw [hrawA_len]; exact hbnd_j)
      hdisj
  · intro p hp
    obtain ⟨hp_lt, hp_disj⟩ := hp
    have hp_lt_A : p < A.byteSize.bytes.toNat := by rw [hbsize]; exact hp_lt
    have hmem_i : fields[i]'hi ∈ fields := List.getElem_mem hi
    have hnot_in_i :
        decide ((fields[i]'hi).offset.bytes.toNat ≤ p ∧
          p < (fields[i]'hi).offset.bytes.toNat +
            (fields[i]'hi).fieldLayout.size.bytes.toNat) = false := by
      rw [decide_eq_false_iff_not]
      have h := hp_disj (fields[i]'hi) hmem_i
      omega
    rw [initMaskWordRel_get hmask' hp_lt_A, initMaskWordRel_get hmask hp_lt_A]
    congr 1
    rw [hword_bits p hp_lt_A, hnot_in_i, Bool.or_false]

/-- Writing a two-scalar `ScalarPair` field `(msc₀, msc₁)` corresponding to distinct
leaf indices `i₀ ≠ i₁` of a `ValidStructLayout`-governed aggregate into `A`:
1. Succeeds across both `Allocation.writeScalar` calls (`A → A₁ → A₂`),
2. Reads back `msc₀` at `fields[i₀]` and `msc₁` at `fields[i₁]`,
3. Preserves `isRangeInitialized` and `Allocation.readScalar` on every other
   initialized leaf `j` (`j ≠ i₀`, `j ≠ i₁`), and
4. Preserves `InitMask.get` on every padding byte `p` (`isStructPaddingByte`),
   including both outer inter-field padding and inner pair alignment padding. -/
theorem writeScalarPairField_preserves_other_fields_and_padding
    {layout : Miri.ABI.LayoutData}
    {fields : List StructFieldDesc}
    (hvalid : ValidStructLayout layout fields)
    {i₀ i₁ : Nat} (hi₀ : i₀ < fields.length) (hi₁ : i₁ < fields.length) (hne₀₁ : i₀ ≠ i₁)
    {sc₀ sc₁ : MirAst.ScalarInt} {msc₀ msc₁ : Miri.Memory.ScalarInt}
    (hrel₀ : ScalarRel sc₀ msc₀) (hrel₁ : ScalarRel sc₁ msc₁)
    (hsz₀ : (fields[i₀]'hi₀).fieldLayout.size = translateSizeBytes sc₀.sizeBytes)
    (hsz₁ : (fields[i₁]'hi₁).fieldLayout.size = translateSizeBytes sc₁.sizeBytes)
    {E : Type} {A : Miri.Memory.Allocation AnnealProv E} {words : Array UInt64}
    (hbsize : A.byteSize = layout.size)
    (hlen : A.len = A.byteSize.bytes.toNat)
    (hmut : A.mutability = .Mut)
    (hprov : A.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask : InitMaskWordRel A.initializationMask A.byteSize words) :
    ∃ (A₁ A₂ : Miri.Memory.Allocation AnnealProv E) (words₂ : Array UInt64),
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange (fields[i₀]'hi₀).offset msc₀.size)
          (Miri.Memory.Scalar.fromScalarInt msc₀) A = .ok () A₁ ∧
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange (fields[i₁]'hi₁).offset msc₁.size)
          (Miri.Memory.Scalar.fromScalarInt msc₁) A₁ = .ok () A₂ ∧
      A₂.byteSize = layout.size ∧
      A₂.len = A₂.byteSize.bytes.toNat ∧
      A₂.mutability = .Mut ∧
      A₂.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      InitMaskWordRel A₂.initializationMask A₂.byteSize words₂ ∧
      (∀ b, b < layout.size.bytes.toNat →
        maskBlocksGetBit words₂ b =
          (maskBlocksGetBit words b ||
            decide ((fields[i₀]'hi₀).offset.bytes.toNat ≤ b ∧
              b < (fields[i₀]'hi₀).offset.bytes.toNat +
                (fields[i₀]'hi₀).fieldLayout.size.bytes.toNat) ||
            decide ((fields[i₁]'hi₁).offset.bytes.toNat ≤ b ∧
              b < (fields[i₁]'hi₁).offset.bytes.toNat +
                (fields[i₁]'hi₁).fieldLayout.size.bytes.toNat))) ∧
      A₂.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange (fields[i₀]'hi₀).offset (fields[i₀]'hi₀).fieldLayout.size) =
        .ok (.ok ()) ∧
      A₂.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange (fields[i₀]'hi₀).offset (fields[i₀]'hi₀).fieldLayout.size) false =
        .ok (Miri.Memory.Scalar.fromScalarInt msc₀) ∧
      A₂.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange (fields[i₁]'hi₁).offset (fields[i₁]'hi₁).fieldLayout.size) =
        .ok (.ok ()) ∧
      A₂.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange (fields[i₁]'hi₁).offset (fields[i₁]'hi₁).fieldLayout.size) false =
        .ok (Miri.Memory.Scalar.fromScalarInt msc₁) ∧
      (∀ j (hj : j < fields.length), j ≠ i₀ → j ≠ i₁ →
        0 < (fields[j]'hj).fieldLayout.size.bytes.toNat →
        (∀ b, (fields[j]'hj).offset.bytes.toNat ≤ b →
          b < (fields[j]'hj).offset.bytes.toNat +
            (fields[j]'hj).fieldLayout.size.bytes.toNat →
          maskBlocksGetBit words b = true) →
        A₂.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange (fields[j]'hj).offset (fields[j]'hj).fieldLayout.size) =
          .ok (.ok ()) ∧
        A₂.readScalar annealTargetDataLayout
            (Miri.Memory.allocRange (fields[j]'hj).offset (fields[j]'hj).fieldLayout.size) false =
          A.readScalar annealTargetDataLayout
            (Miri.Memory.allocRange (fields[j]'hj).offset (fields[j]'hj).fieldLayout.size) false) ∧
      (∀ p, isStructPaddingByte fields layout.size p →
        A₂.initializationMask.get (Miri.ABI.Size.ofBytes (UInt64.ofNat p)) =
          A.initializationMask.get (Miri.ABI.Size.ofBytes (UInt64.ofNat p))) := by
  obtain ⟨A₁, words₁, hw₀, hbs₁, hlen₁, hmut₁, hprov₁, hmask₁, hbits₁, hinit₀_1, hread₀_1,
      hother₁, hpad₁⟩ :=
    writeField_preserves_other_fields_and_padding hvalid hi₀ hrel₀ hsz₀ hbsize hlen hmut hprov hmask
  obtain ⟨A₂, words₂, hw₁, hbs₂, hlen₂, hmut₂, hprov₂, hmask₂, hbits₂, hinit₁_2, hread₁_2,
      hother₂, hpad₂⟩ :=
    writeField_preserves_other_fields_and_padding hvalid hi₁ hrel₁ hsz₁ hbs₁ hlen₁ hmut₁ hprov₁ hmask₁
  have hsz₀_pos : 0 < (fields[i₀]'hi₀).fieldLayout.size.bytes.toNat := by
    rw [hsz₀]; exact lm22_translateSizeBytes_pos hrel₀.validBytes
  have hi₀_bits₁ : ∀ b, (fields[i₀]'hi₀).offset.bytes.toNat ≤ b →
      b < (fields[i₀]'hi₀).offset.bytes.toNat + (fields[i₀]'hi₀).fieldLayout.size.bytes.toNat →
      maskBlocksGetBit words₁ b = true := by
    intro b hlo hhi
    have hb_lt : b < layout.size.bytes.toNat := by
      have := hvalid.fields_in_bounds i₀ hi₀; omega
    rw [hbits₁ b hb_lt]
    have hin : (fields[i₀]'hi₀).offset.bytes.toNat ≤ b ∧
        b < (fields[i₀]'hi₀).offset.bytes.toNat + (fields[i₀]'hi₀).fieldLayout.size.bytes.toNat :=
      ⟨hlo, hhi⟩
    simp [hin]
  obtain ⟨hinit₀_2, hread₀_2⟩ := hother₂ i₀ hi₀ hne₀₁ hsz₀_pos hi₀_bits₁
  rw [hread₀_1] at hread₀_2
  refine ⟨A₁, A₂, words₂, hw₀, hw₁, hbs₂, hlen₂, hmut₂, hprov₂, hmask₂, ?_,
    hinit₀_2, hread₀_2, hinit₁_2, hread₁_2, ?_, ?_⟩
  · intro b hb
    rw [hbits₂ b hb, hbits₁ b hb]
  · intro j hj hne₀ hne₁ hj_pos hj_init
    obtain ⟨_, hread₁⟩ := hother₁ j hj hne₀ hj_pos hj_init
    have hj_bits₁ : ∀ b, (fields[j]'hj).offset.bytes.toNat ≤ b →
        b < (fields[j]'hj).offset.bytes.toNat + (fields[j]'hj).fieldLayout.size.bytes.toNat →
        maskBlocksGetBit words₁ b = true := by
      intro b hlo hhi
      have hb_lt : b < layout.size.bytes.toNat := by
        have := hvalid.fields_in_bounds j hj; omega
      rw [hbits₁ b hb_lt, hj_init b hlo hhi]
      simp
    obtain ⟨hinit₂, hread₂⟩ := hother₂ j hj hne₁ hj_pos hj_bits₁
    exact ⟨hinit₂, hread₂.trans hread₁⟩
  · intro p hp
    exact (hpad₂ p hp).trans (hpad₁ p hp)

/-! ## 7. Unpadded vs. Padded Struct Byte-Counting Dichotomy (`structSumFieldBytes`) -/

/-- Sum of `fieldLayout.size.bytes.toNat` across a list of `StructFieldDesc` descriptors. -/
def structSumFieldBytes : List StructFieldDesc → Nat
  | [] => 0
  | f :: fs => f.fieldLayout.size.bytes.toNat + structSumFieldBytes fs

/-- Boolean test whether byte `b` lies in `f`'s `[offset, offset + size)` interval. -/
def inStructFieldByte (f : StructFieldDesc) (b : Nat) : Bool :=
  decide (f.offset.bytes.toNat ≤ b ∧
    b < f.offset.bytes.toNat + f.fieldLayout.size.bytes.toNat)

/-- Boolean test whether byte `b` lies in at least one descriptor of `fields`. -/
def inAnyStructFieldByte : List StructFieldDesc → Nat → Bool
  | [], _ => false
  | f :: fs, b => inStructFieldByte f b || inAnyStructFieldByte fs b

private theorem inAnyStructFieldByte_iff {fields : List StructFieldDesc} {b : Nat} :
    inAnyStructFieldByte fields b = true ↔
      ∃ f ∈ fields,
        f.offset.bytes.toNat ≤ b ∧
        b < f.offset.bytes.toNat + f.fieldLayout.size.bytes.toNat := by
  induction fields with
  | nil => simp [inAnyStructFieldByte]
  | cons f fs ih =>
    simp only [inAnyStructFieldByte, inStructFieldByte, Bool.or_eq_true, decide_eq_true_eq,
      ih, List.mem_cons, exists_eq_or_imp]

private theorem countP_range_interval_aux (M lo sz : Nat) :
    (List.range M).countP (fun b => decide (lo ≤ b ∧ b < lo + sz)) =
      (if M ≤ lo + sz then M else lo + sz) - (if M ≤ lo then M else lo) := by
  induction M with
  | zero =>
    simp only [List.range_zero, List.countP_nil]
    split <;> split <;> omega
  | succ M ih =>
    rw [List.range_succ, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil]
    by_cases h : lo ≤ M ∧ M < lo + sz
    · simp only [decide_eq_true h, ↓reduceIte]
      split <;> split <;> split <;> split <;> omega
    · simp only [decide_eq_false h, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      split <;> split <;> split <;> split <;> omega

private theorem countP_range_interval {N lo sz : Nat} (hbnd : lo + sz ≤ N) :
    (List.range N).countP (fun b => decide (lo ≤ b ∧ b < lo + sz)) = sz := by
  rw [countP_range_interval_aux]
  split <;> split <;> omega

private theorem countP_or_of_disjoint {l : List Nat} {p q : Nat → Bool}
    (hdisj : ∀ b ∈ l, ¬ (p b = true ∧ q b = true)) :
    l.countP (fun b => p b || q b) = l.countP p + l.countP q := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have hhd := hdisj hd (.head _)
    have htl : ∀ b ∈ tl, ¬ (p b = true ∧ q b = true) :=
      fun b hb => hdisj b (.tail _ hb)
    simp only [List.countP_cons, ih htl]
    cases hp : p hd <;> cases hq : q hd
    · simp
    · simp; omega
    · simp; omega
    · exact absurd ⟨hp, hq⟩ hhd

private theorem countP_inAnyStructFieldByte_eq {N : Nat} {fields : List StructFieldDesc}
    (hbnd : ∀ f ∈ fields, f.offset.bytes.toNat + f.fieldLayout.size.bytes.toNat ≤ N)
    (hdisj : fields.Pairwise (fun f₁ f₂ =>
      f₁.offset.bytes.toNat + f₁.fieldLayout.size.bytes.toNat ≤ f₂.offset.bytes.toNat ∨
      f₂.offset.bytes.toNat + f₂.fieldLayout.size.bytes.toNat ≤ f₁.offset.bytes.toNat)) :
    (List.range N).countP (inAnyStructFieldByte fields) = structSumFieldBytes fields := by
  induction fields with
  | nil => simp [inAnyStructFieldByte, structSumFieldBytes]
  | cons f fs ih =>
    rcases List.pairwise_cons.mp hdisj with ⟨hf_fs, hfs_pw⟩
    have hf_bnd : f.offset.bytes.toNat + f.fieldLayout.size.bytes.toNat ≤ N :=
      hbnd f (.head _)
    have hfs_bnd : ∀ g ∈ fs, g.offset.bytes.toNat + g.fieldLayout.size.bytes.toNat ≤ N :=
      fun g hg => hbnd g (.tail _ hg)
    have hfun : inAnyStructFieldByte (f :: fs) =
        (fun b => inStructFieldByte f b || inAnyStructFieldByte fs b) := rfl
    rw [hfun, structSumFieldBytes, countP_or_of_disjoint]
    · rw [ih hfs_bnd hfs_pw]
      unfold inStructFieldByte
      rw [countP_range_interval hf_bnd]
    · intro b _ ⟨hbf, hbfs⟩
      unfold inStructFieldByte at hbf
      rw [decide_eq_true_iff] at hbf
      obtain ⟨g, hg_mem, hbg⟩ := inAnyStructFieldByte_iff.mp hbfs
      have hd := hf_fs g hg_mem
      omega

namespace ValidStructLayout

/-- Helper discharging the `.Arbitrary` branch of `fields_shape_valid` when all
fields are flat 1-level leaves (`topOffsets = (fields.map (·.offset)).toArray`). -/
theorem arbitrary_flat {layout : Miri.ABI.LayoutData} {fields : List StructFieldDesc}
    (memoryIndex : Array Nat)
    (heq : layout.fields = .Arbitrary (fields.map (·.offset)).toArray memoryIndex)
    (hsz : memoryIndex.size = (fields.map (·.offset)).toArray.size) :
    ∃ topOffsets memoryIndex,
      layout.fields = .Arbitrary topOffsets memoryIndex ∧
      memoryIndex.size = topOffsets.size ∧
      (∀ off ∈ topOffsets.toList, off ∈ fields.map (·.offset)) ∧
      (∀ f ∈ fields, ∃ topOff ∈ topOffsets.toList,
        topOff.bytes.toNat ≤ f.offset.bytes.toNat) :=
  ⟨(fields.map (·.offset)).toArray, memoryIndex, heq, hsz,
    fun _ h => by simpa using h,
    fun f hf => ⟨f.offset, by simpa using List.mem_map_of_mem hf, Nat.le_refl _⟩⟩

private theorem pairwise_disjoint {layout : Miri.ABI.LayoutData} {fields : List StructFieldDesc}
    (h : ValidStructLayout layout fields) :
    fields.Pairwise (fun f₁ f₂ =>
      f₁.offset.bytes.toNat + f₁.fieldLayout.size.bytes.toNat ≤ f₂.offset.bytes.toNat ∨
      f₂.offset.bytes.toNat + f₂.fieldLayout.size.bytes.toNat ≤ f₁.offset.bytes.toNat) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hlt
  exact h.fields_disjoint i j hi hj (Nat.ne_of_lt hlt)

private theorem mem_in_bounds {layout : Miri.ABI.LayoutData} {fields : List StructFieldDesc}
    (h : ValidStructLayout layout fields) :
    ∀ f ∈ fields,
      f.offset.bytes.toNat + f.fieldLayout.size.bytes.toNat ≤ layout.size.bytes.toNat := by
  intro f hf
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hf
  exact h.fields_in_bounds i hi

/-- The sum of field byte sizes in any `ValidStructLayout` never exceeds `layout.size`. -/
theorem sumFieldBytes_le_size {layout : Miri.ABI.LayoutData} {fields : List StructFieldDesc}
    (h : ValidStructLayout layout fields) :
    structSumFieldBytes fields ≤ layout.size.bytes.toNat := by
  rw [← countP_inAnyStructFieldByte_eq h.mem_in_bounds h.pairwise_disjoint]
  have hle := List.countP_le_length (p := inAnyStructFieldByte fields)
    (l := List.range layout.size.bytes.toNat)
  simpa using hle

/-- `structSumFieldBytes fields < layout.size.bytes.toNat` holds if and only if at
least one padding byte `isStructPaddingByte fields layout.size p` exists. -/
theorem sumFieldBytes_lt_iff_exists_padding {layout : Miri.ABI.LayoutData}
    {fields : List StructFieldDesc}
    (h : ValidStructLayout layout fields) :
    structSumFieldBytes fields < layout.size.bytes.toNat ↔
      ∃ p, isStructPaddingByte fields layout.size p := by
  have hle := h.sumFieldBytes_le_size
  rw [← countP_inAnyStructFieldByte_eq h.mem_in_bounds h.pairwise_disjoint] at hle ⊢
  have hlen : (List.range layout.size.bytes.toNat).length = layout.size.bytes.toNat :=
    List.length_range
  constructor
  · intro hlt
    have hne : (List.range layout.size.bytes.toNat).countP (inAnyStructFieldByte fields) ≠
        (List.range layout.size.bytes.toNat).length := by omega
    have hnotall : ¬ ∀ p ∈ List.range layout.size.bytes.toNat,
        inAnyStructFieldByte fields p = true :=
      fun hall => hne (List.countP_eq_length.mpr hall)
    rw [Classical.not_forall] at hnotall
    obtain ⟨p, hp⟩ := hnotall
    rw [Classical.not_imp] at hp
    rcases hp with ⟨hp_mem, hp_false⟩
    have hp_lt : p < layout.size.bytes.toNat := List.mem_range.mp hp_mem
    refine ⟨p, hp_lt, ?_⟩
    intro f hf
    by_cases hlo : p < f.offset.bytes.toNat
    · exact Or.inl hlo
    · refine Or.inr ?_
      apply Classical.byContradiction
      intro hhi
      apply hp_false
      exact inAnyStructFieldByte_iff.mpr ⟨f, hf, by omega, by omega⟩
  · rintro ⟨p, hp_lt, hp_disj⟩
    apply Classical.byContradiction
    intro hge
    have heq : (List.range layout.size.bytes.toNat).countP (inAnyStructFieldByte fields) =
        (List.range layout.size.bytes.toNat).length := by omega
    have hall := List.countP_eq_length.mp heq p (List.mem_range.mpr hp_lt)
    obtain ⟨f, hf, hlo, hhi⟩ := inAnyStructFieldByte_iff.mp hall
    have hd := hp_disj f hf
    omega

/-- When `layout.size.bytes.toNat ≤ structSumFieldBytes fields` (unpadded aggregate),
every byte `b < layout.size.bytes.toNat` belongs to some field `fields[i]`. -/
theorem byte_mem_field_of_size_le_sumFieldBytes {layout : Miri.ABI.LayoutData}
    {fields : List StructFieldDesc}
    (h : ValidStructLayout layout fields)
    (hunpad : layout.size.bytes.toNat ≤ structSumFieldBytes fields)
    {b : Nat} (hb : b < layout.size.bytes.toNat) :
    ∃ i, ∃ (hi : i < fields.length),
      (fields[i]'hi).offset.bytes.toNat ≤ b ∧
      b < (fields[i]'hi).offset.bytes.toNat +
        (fields[i]'hi).fieldLayout.size.bytes.toNat := by
  have hle := h.sumFieldBytes_le_size
  have heq_sum : structSumFieldBytes fields = layout.size.bytes.toNat := by omega
  rw [← countP_inAnyStructFieldByte_eq h.mem_in_bounds h.pairwise_disjoint] at heq_sum
  have heq_len : (List.range layout.size.bytes.toNat).countP (inAnyStructFieldByte fields) =
      (List.range layout.size.bytes.toNat).length := by
    rw [List.length_range]; exact heq_sum
  have hall := List.countP_eq_length.mp heq_len b (List.mem_range.mpr hb)
  obtain ⟨f, hf, hlo, hhi⟩ := inAnyStructFieldByte_iff.mp hall
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hf
  exact ⟨i, hi, hlo, hhi⟩

end ValidStructLayout

end LeanMiriSpec.Correspondence
