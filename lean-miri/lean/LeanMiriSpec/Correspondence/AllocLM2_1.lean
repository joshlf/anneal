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
# Byte-Slice Read, Write, Disjointness & `ArraySliceRel` Lemmas (`LM-2.1`)

Parametric byte-slice lemmas over `Miri.Memory.Allocation` at arbitrary
in-bounds element offsets `off`:

* `fromBytes_zeroed_spec`: `Allocation.fromBytes (Array.replicate sz 0) align .Mut`
  produces a mutable allocation of `sz` bytes with `InitMask.new sz true` and
  `ProvenanceMap.new`.
* `initMask_new_true_setRange_inbounds`: setting any in-bounds range to `true`
  on `InitMask.new sz true` preserves `InitMask.new sz true`.
* `alloc_writeScalar_at_offset`: writing a `ScalarRel`-related scalar at any
  in-bounds byte offset `off` succeeds, preserves `byteSize`, `len`,
  `mutability`, `provenanceMap`, and `initializationMask`, reads back the
  written scalar at `off`, and preserves `readScalar` at every disjoint
  in-bounds byte range `[otherOff, otherOff + otherSz)`.
* `ArraySliceRel.readScalar_get` and `ArraySliceRel.writeScalar_set`: element
  reads and in-place element writes preserve `ArraySliceRel` across all
  `j ≠ idx` elements.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Replicas of private `lean-miri` byte helpers -/

private def allocRaw {P E : Type} (a : Miri.Memory.Allocation P E) : Array UInt8 :=
  Miri.Memory.Allocation.casesOn (motive := fun _ => Array UInt8) a
    (fun raw _ _ _ _ _ _ _ => raw)

private def allocCheckedAlign (align : Miri.ABI.Align) :
    Except Miri.Memory.AllocError Miri.ABI.Align := do
  let bytes ← (Miri.ABI.Align.bytes align).mapError Miri.Memory.AllocError.alignment
  let normalized ← (Miri.ABI.Align.fromBytes bytes).mapError Miri.Memory.AllocError.alignment
  if normalized == align then return align
  throw (.alignment (.tooLarge bytes))

private def allocPointerSize (layout : Miri.ABI.TargetDataLayout) : Miri.ABI.Size :=
  Miri.ABI.Size.fromBits layout.pointerWidth.bits

private def allocTargetUIntBytes (layout : Miri.ABI.TargetDataLayout)
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

private def allocReadTargetUInt (layout : Miri.ABI.TargetDataLayout)
    (bytes : Array UInt8) : Except Miri.Memory.AllocError Miri.ABI.U128 := do
  if bytes.size > 16 then
    throw (.scalarBytesTooWide (Miri.ABI.Size.ofBytes (UInt64.ofNat bytes.size)))
  let mut value := 0
  for index in [:bytes.size] do
    let some byte := bytes[index]? | throw (.invalidSliceEndpoints index (index + 1) bytes.size)
    let valueIndex := if layout.endian == .little then index else bytes.size - index - 1
    value := value + byte.toNat * 2 ^ (8 * valueIndex)
  return BitVec.ofNat 128 value

private def allocCheckedSlice {P E : Type} (allocation : Miri.Memory.Allocation P E)
    (range : Miri.Memory.AllocRange) : Except Miri.Memory.AllocError (Array UInt8) := do
  if (allocRaw allocation).size != allocation.byteSize.bytes.toNat then
    throw (.storageLengthMismatch allocation.byteSize (allocRaw allocation).size)
  let finish ← range.endExclusive |>.mapError Miri.Memory.AllocError.memory
  if range.start.bytes > finish.bytes || finish.bytes > allocation.byteSize.bytes then
    throw (.outOfBounds range allocation.byteSize)
  return (allocRaw allocation).extract range.start.bytes.toNat finish.bytes.toNat

private theorem alloc_getBytesUnchecked_eq {P E : Type}
    (allocation : Miri.Memory.Allocation P E) (range : Miri.Memory.AllocRange) :
    Miri.Memory.Allocation.getBytesUnchecked allocation range =
      allocCheckedSlice allocation range := rfl

private def allocReadScalar {P E : Type} [DecidableEq P] [Miri.Memory.PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : Miri.ABI.TargetDataLayout)
    (range : Miri.Memory.AllocRange) (readProvenance : Bool) :
    Except Miri.Memory.AllocError (Miri.Memory.Scalar P) := do
  match ← (allocation.initializationMask.isRangeInitialized range).mapError
      Miri.Memory.AllocError.memory with
  | .error bad => throw (.invalidUninitBytes (some ⟨range, bad⟩))
  | .ok () => pure ()
  let bytes ← Miri.Memory.Allocation.getBytesUnchecked allocation range
  let bits ← allocReadTargetUInt layout bytes
  if readProvenance then
    let targetSize := allocPointerSize layout
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
      (allocation.provenanceMap.rangeEmpty range (allocPointerSize layout)).mapError
        Miri.Memory.AllocError.provenance
    if isEmpty then
      let scalar ← (Miri.Memory.Scalar.fromUInt bits range.size).mapError
        Miri.Memory.AllocError.scalar
      return scalar
    throw (.readPointerAsInt none)

private theorem alloc_readScalar_eq {P E : Type} [DecidableEq P]
    [Miri.Memory.PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : Miri.ABI.TargetDataLayout)
    (range : Miri.Memory.AllocRange) (readProvenance : Bool) :
    allocation.readScalar layout range readProvenance =
      allocReadScalar allocation layout range readProvenance := rfl

/-! ## 2. Little-endian encoding & decoding -/

def allocLeBytes (x n : Nat) : Array UInt8 :=
  ((List.range' 0 n).map fun i => UInt8.ofNat ((x / 2 ^ (8 * i)) % 256)).toArray

@[simp]
theorem allocLeBytes_size (x n : Nat) : (allocLeBytes x n).size = n := by
  simp [allocLeBytes]

private theorem alloc_encode_loop (x : Nat) (l : List Nat) (acc : Array UInt8) :
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

private theorem allocTargetUIntBytes_spec (size : Miri.ABI.Size) (bits : Miri.ABI.U128)
    (hle : size.bytes.toNat ≤ 16) :
    allocTargetUIntBytes annealTargetDataLayout size bits =
      .ok (allocLeBytes bits.toNat size.bytes.toNat) := by
  have small : ¬ size.bytes > 16 := by
    simp only [GT.gt, UInt64.lt_iff_toNat_lt]
    simpa using Nat.not_lt.mpr hle
  have hle' : (annealTargetDataLayout.endian == Miri.ABI.Endian.little) = true := rfl
  unfold allocTargetUIntBytes
  simp only [small, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range', hle',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure]
  rw [alloc_encode_loop]
  simp [allocLeBytes]

private def allocLeSum (x k : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) + allocLeSum x (k + 1) m

private theorem allocLeSum_spec (x : Nat) :
    ∀ m k, x % 2 ^ (8 * k) + allocLeSum x k m = x % 2 ^ (8 * (k + m)) := by
  intro m
  induction m with
  | zero => intro k; simp [allocLeSum]
  | succ m ih =>
    intro k
    have hstep : x % 2 ^ (8 * k) + x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) =
        x % 2 ^ (8 * (k + 1)) := by
      rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add, Nat.mod_mul]
      simp only [show (2 : Nat) ^ 8 = 256 by rfl]
      rw [Nat.mul_comm (2 ^ (8 * k))]
    simp only [allocLeSum]
    rw [← Nat.add_assoc, hstep, ih (k + 1), show k + 1 + m = k + (m + 1) by omega]

private theorem alloc_decode_loop (x n : Nat)
    (f : Nat → Nat → Except Miri.Memory.AllocError (ForInStep Nat))
    (hf : ∀ index s, index < n →
      f index s = .ok (.yield (s + x / 2 ^ (8 * index) % 256 * 2 ^ (8 * index)))) :
    ∀ m k acc, k + m ≤ n →
      forIn (List.range' k m) acc f = .ok (acc + allocLeSum x k m) := by
  intro m
  induction m with
  | zero => intro k acc _; simp [allocLeSum, pure, Except.pure]
  | succ m ih =>
    intro k acc hkm
    rw [List.range'_succ, List.forIn_cons, hf k acc (by omega)]
    simp only [allocLeSum]
    rw [show (Except.ok (ForInStep.yield (acc + x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k))) :
        Except Miri.Memory.AllocError (ForInStep Nat)) = pure (ForInStep.yield _) from rfl,
      pure_bind]
    simp only
    rw [ih (k + 1) _ (by omega), Nat.add_assoc]

private theorem allocReadTargetUInt_leBytes (x n : Nat) (hn : n ≤ 16) :
    allocReadTargetUInt annealTargetDataLayout (allocLeBytes x n) =
      .ok (BitVec.ofNat 128 (x % 2 ^ (8 * n))) := by
  have small : ¬ n > 16 := by omega
  have hle : (annealTargetDataLayout.endian == Miri.ABI.Endian.little) = true := rfl
  unfold allocReadTargetUInt
  simp only [allocLeBytes_size, small, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range',
    hle, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [alloc_decode_loop x n _ ?hf n 0 0 (by omega)]
  · have := allocLeSum_spec x n 0
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mod_one, Nat.zero_add] at this
    simp [this, pure, Except.pure, bind, Except.bind]
  · intro index s hi
    have hb : (x / 2 ^ (8 * index) % 256) < 256 := Nat.mod_lt _ (by decide)
    simp [allocLeBytes, hi, pure, Except.pure, Nat.mod_eq_of_lt hb]

/-! ## 3. Scalar & `InitMask` helpers -/

theorem translateSizeBytes_toNat_of_valid {sz : Nat} (h : ValidScalarBytes sz) :
    (translateSizeBytes sz).bytes.toNat = sz := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem translateSizeBytes_le_16_of_valid {sz : Nat} (h : ValidScalarBytes sz) :
    (translateSizeBytes sz).bytes.toNat ≤ 16 := by
  rw [translateSizeBytes_toNat_of_valid h]
  rcases h with h | h | h | h | h <;> omega

private theorem alloc_scalarModulus_eq_two_pow (sz : Nat) :
    scalarModulus sz = 2 ^ (8 * sz) := by
  induction sz with
  | zero => rfl
  | succ k ih =>
    show 256 * scalarModulus k = 2 ^ (8 * (k + 1))
    rw [ih, show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add, Nat.mul_comm]

theorem bitVec_ofNat_128_toNat {sz x : Nat}
    (hsz : ValidScalarBytes sz) (hx : x < scalarModulus sz) :
    (BitVec.ofNat 128 x).toNat = x := by
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hle : scalarModulus sz ≤ 2 ^ 128 := by
    rw [alloc_scalarModulus_eq_two_pow]
    exact Nat.pow_le_pow_right (by decide) (by rcases hsz with h | h | h | h | h <;> omega)
  omega

private theorem alloc_validScalarBytes_bits_le_128 {sz : Nat} (h : ValidScalarBytes sz) :
    8 * sz ≤ 128 ∧ 0 < 8 * sz := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> omega

private theorem alloc_zeroExtend_extractLsb_eq_ofNat (w : Nat) (hw0 : 0 < w)
    (hw128 : w ≤ 128) (data : BitVec 128) :
    BitVec.zeroExtend 128 (BitVec.extractLsb (w - 1) 0 data) =
      BitVec.ofNat 128 (data.toNat % 2 ^ w) := by
  apply BitVec.eq_of_toNat_eq
  unfold BitVec.zeroExtend BitVec.extractLsb BitVec.extractLsb'
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hlen : w - 1 + 1 = w := by omega
  simp only [Nat.sub_zero, Nat.shiftRight_zero, hlen]

private theorem alloc_truncateFromUInt_spec {sz : Nat} (hsz : ValidScalarBytes sz)
    (data : BitVec 128) :
    ∃ msc : Miri.Memory.ScalarInt,
      Miri.Memory.ScalarInt.truncateFromUInt data (translateSizeBytes sz) =
        .ok (msc, BitVec.ofNat 128 (data.toNat % 2 ^ (8 * sz)) != data) ∧
      ScalarRel ⟨data.toNat % 2 ^ (8 * sz), sz⟩ msc := by
  have ⟨hw128, hw0⟩ := alloc_validScalarBytes_bits_le_128 hsz
  have hze := alloc_zeroExtend_extractLsb_eq_ofNat (8 * sz) hw0 hw128 data
  have hmod : data.toNat % 2 ^ (8 * sz) < scalarModulus sz := by
    rw [alloc_scalarModulus_eq_two_pow]
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

theorem scalarInt_tryFromUInt_of_valid {sc : MirAst.ScalarInt}
    (hsz : ValidScalarBytes sc.sizeBytes) (hcan : sc.bits < scalarModulus sc.sizeBytes) :
    ∃ msc : Miri.Memory.ScalarInt,
      Miri.Memory.ScalarInt.tryFromUInt (BitVec.ofNat 128 sc.bits)
          (translateSizeBytes sc.sizeBytes) = .ok (some msc) ∧
      ScalarRel sc msc := by
  obtain ⟨msc, htr, hrel⟩ := alloc_truncateFromUInt_spec hsz (BitVec.ofNat 128 sc.bits)
  have hlt : sc.bits < 2 ^ (8 * sc.sizeBytes) := by
    rw [← alloc_scalarModulus_eq_two_pow]; exact hcan
  have hmod : (BitVec.ofNat 128 sc.bits).toNat % 2 ^ (8 * sc.sizeBytes) = sc.bits := by
    rw [bitVec_ofNat_128_toNat hsz hcan, Nat.mod_eq_of_lt hlt]
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

private theorem alloc_scalarInt_ext {a b : Miri.Memory.ScalarInt}
    (hd : a.data = b.data) (hs : a.size = b.size) : a = b := by
  cases a
  cases b
  simp only [Miri.Memory.ScalarInt.data, Miri.Memory.ScalarInt.size] at hd hs
  subst hd
  subst hs
  rfl

private theorem alloc_fromUInt {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) :
    Miri.Memory.Scalar.fromUInt (Prov := AnnealProv) (BitVec.ofNat 128 sc.bits)
        (translateSizeBytes sc.sizeBytes) = .ok (Miri.Memory.Scalar.fromScalarInt msc) := by
  obtain ⟨msc', htry, hrel'⟩ := scalarInt_tryFromUInt_of_valid hrel.validBytes hrel.canonical
  have heq : msc' = msc :=
    alloc_scalarInt_ext (hrel'.data_eq.trans hrel.data_eq.symm)
      (hrel'.size_eq.trans hrel.size_eq.symm)
  subst heq
  unfold Miri.Memory.Scalar.fromUInt
  simp [htry, Except.mapError, bind, Except.bind, pure, Except.pure]

private theorem alloc_toBitsOrPtrInternal {sc : MirAst.ScalarInt}
    {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBitsOrPtrInternal
        (translateSizeBytes sc.sizeBytes) = .ok (.bits (BitVec.ofNat 128 sc.bits)) := by
  unfold Miri.Memory.Scalar.toBitsOrPtrInternal
  simp only [Miri.Memory.Scalar.fromScalarInt, hrel.toBits_eq, Except.mapError, bind,
    Except.bind, pure, Except.pure]

/-- `allocRange off sz` has `endExclusive = .ok (Size.ofBytes (off.bytes + sz.bytes))`
whenever `off.bytes.toNat + sz.bytes.toNat < 2^64`. -/
theorem allocRange_endExclusive_of_lt {off sz : Miri.ABI.Size}
    (h : off.bytes.toNat + sz.bytes.toNat < 2 ^ 64) :
    (Miri.Memory.allocRange off sz).endExclusive =
      .ok (Miri.ABI.Size.ofBytes (off.bytes + sz.bytes)) := by
  have hadd : (off.bytes + sz.bytes).toNat = off.bytes.toNat + sz.bytes.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by simpa [UInt64.size] using h)]
  have h1 : ¬ (off.bytes + sz.bytes < off.bytes) := by
    rw [UInt64.lt_iff_toNat_lt, hadd]; omega
  unfold Miri.Memory.AllocRange.endExclusive Miri.Memory.AllocRange.end Miri.Memory.allocRange
    Miri.ABI.Size.add Miri.ABI.Size.ofBytes
  simp [h1, Except.mapError]

/-- Setting any in-bounds range to `true` on `InitMask.new totalSz true`
preserves `InitMask.new totalSz true`. -/
theorem initMask_new_true_setRange_inbounds
    {totalSz off sz : Miri.ABI.Size}
    (hin : off.bytes.toNat + sz.bytes.toNat ≤ totalSz.bytes.toNat) :
    (Miri.Memory.InitMask.new totalSz true).setRange (Miri.Memory.allocRange off sz) true =
      .ok (Miri.Memory.InitMask.new totalSz true) := by
  have htot : totalSz.bytes.toNat < 2 ^ 64 := by
    simpa [UInt64.size] using totalSz.bytes.toNat_lt_size
  have hlt : off.bytes.toNat + sz.bytes.toNat < 2 ^ 64 := by omega
  have hend := allocRange_endExclusive_of_lt hlt
  have hadd_toNat : (off.bytes + sz.bytes).toNat = off.bytes.toNat + sz.bytes.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by simpa [UInt64.size] using hlt)]
  have hle : (Miri.ABI.Size.ofBytes (off.bytes + sz.bytes)).bytes ≤ totalSz.bytes := by
    rw [UInt64.le_iff_toNat_le]
    simpa [Miri.ABI.Size.ofBytes, hadd_toNat] using hin
  have hnot_gt : ¬ (off.bytes + sz.bytes > totalSz.bytes) := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hadd_toNat]; omega
  unfold Miri.Memory.InitMask.setRange Miri.Memory.InitMask.new
  rw [hend]
  simp only [bind, Except.bind, pure, Except.pure, Miri.Memory.allocRange]
  split
  · rename_i hfull
    have heq : Miri.ABI.Size.ofBytes (off.bytes + sz.bytes) = totalSz := by
      cases totalSz with | mk tb =>
      simp only [Miri.ABI.Size.ofBytes] at hfull hle ⊢
      congr 1
      exact UInt64.le_antisymm hle hfull.2
    rw [heq]
  · simp [Miri.ABI.Size.ofBytes, hnot_gt]

/-- Querying any in-bounds range on `InitMask.new totalSz true` returns `.ok (.ok ())`. -/
theorem initMask_new_true_isRangeInitialized_inbounds
    {totalSz off sz : Miri.ABI.Size}
    (hin : off.bytes.toNat + sz.bytes.toNat ≤ totalSz.bytes.toNat) :
    (Miri.Memory.InitMask.new totalSz true).isRangeInitialized
      (Miri.Memory.allocRange off sz) = .ok (.ok ()) := by
  have htot : totalSz.bytes.toNat < 2 ^ 64 := by
    simpa [UInt64.size] using totalSz.bytes.toNat_lt_size
  have hlt : off.bytes.toNat + sz.bytes.toNat < 2 ^ 64 := by omega
  have hend := allocRange_endExclusive_of_lt hlt
  have hadd_toNat : (off.bytes + sz.bytes).toNat = off.bytes.toNat + sz.bytes.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by simpa [UInt64.size] using hlt)]
  have hle : (Miri.ABI.Size.ofBytes (off.bytes + sz.bytes)).bytes ≤ totalSz.bytes := by
    rw [UInt64.le_iff_toNat_le]
    simpa [Miri.ABI.Size.ofBytes, hadd_toNat] using hin
  exact Miri.Memory.InitMask.lazy_initialized_query totalSz
    (Miri.Memory.allocRange off sz) (Miri.ABI.Size.ofBytes (off.bytes + sz.bytes)) hend hle

/-! ## 4. Array slice extraction lemmas -/

private theorem array_extract_middle {α : Type} (a mid : Array α) (start sz : Nat)
    (h : start + sz ≤ a.size) (hmid : mid.size = sz) :
    (a.extract 0 start ++ mid ++ a.extract (start + sz) a.size).extract start (start + sz) =
      mid := by
  have hsize : (a.extract 0 start ++ mid ++ a.extract (start + sz) a.size).size = a.size := by
    simp only [Array.size_append, Array.size_extract, hmid]; omega
  have h1 : (a.extract 0 start).size = start := by
    simp only [Array.size_extract]; omega
  apply Array.ext
  · simp only [Array.size_extract, hsize, hmid]; omega
  · intro i hi₁ hi₂
    rw [Array.getElem_extract]
    have h3 : start + i < (a.extract 0 start ++ mid).size := by
      simp only [Array.size_append, h1, hmid]; omega
    rw [Array.getElem_append_left h3, Array.getElem_append_right (by omega)]
    simp [h1]

private theorem array_extract_disjoint_left {α : Type} (a mid : Array α)
    (start sz oStart oEnd : Nat)
    (h : start + sz ≤ a.size) (hmid : mid.size = sz)
    (hdisj : oEnd ≤ start) :
    (a.extract 0 start ++ mid ++ a.extract (start + sz) a.size).extract oStart oEnd =
      a.extract oStart oEnd := by
  have hsize : (a.extract 0 start ++ mid ++ a.extract (start + sz) a.size).size = a.size := by
    simp only [Array.size_append, Array.size_extract, hmid]; omega
  have h1 : (a.extract 0 start).size = start := by
    simp only [Array.size_extract]; omega
  apply Array.ext
  · simp only [Array.size_extract, hsize]
  · intro i hi₁ hi₂
    rw [Array.getElem_extract, Array.getElem_extract]
    have hlt1 : oStart + i < (a.extract 0 start).size := by
      rw [Array.size_extract] at hi₂; omega
    have hlt2 : oStart + i < (a.extract 0 start ++ mid).size := by
      simp only [Array.size_append]; omega
    rw [Array.getElem_append_left hlt2, Array.getElem_append_left hlt1, Array.getElem_extract]
    simp

private theorem array_extract_disjoint_right {α : Type} (a mid : Array α)
    (start sz oStart oEnd : Nat)
    (h : start + sz ≤ a.size) (hmid : mid.size = sz)
    (hdisj : start + sz ≤ oStart) :
    (a.extract 0 start ++ mid ++ a.extract (start + sz) a.size).extract oStart oEnd =
      a.extract oStart oEnd := by
  have hsize : (a.extract 0 start ++ mid ++ a.extract (start + sz) a.size).size = a.size := by
    simp only [Array.size_append, Array.size_extract, hmid]; omega
  have h1 : (a.extract 0 start ++ mid).size = start + sz := by
    simp only [Array.size_append, Array.size_extract, hmid]; omega
  apply Array.ext
  · simp only [Array.size_extract, hsize]
  · intro i hi₁ hi₂
    rw [Array.getElem_extract, Array.getElem_extract]
    have hge : (a.extract 0 start ++ mid).size ≤ oStart + i := by omega
    rw [Array.getElem_append_right hge, Array.getElem_extract]
    congr 1
    omega

/-! ## 5. Arbitrary-offset `writeScalar` & `readScalar` -/

/-- For any in-bounds range `allocRange off sz` on an allocation with `A.len = A.byteSize.bytes.toNat`,
`allocCheckedSlice` returns the extracted slice `[off .. off + sz)`. -/
private theorem allocCheckedSlice_of_inbounds {P E : Type}
    {A : Miri.Memory.Allocation P E} {off sz : Miri.ABI.Size}
    (hlen : A.len = A.byteSize.bytes.toNat)
    (hin : off.bytes.toNat + sz.bytes.toNat ≤ A.byteSize.bytes.toNat) :
    allocCheckedSlice A (Miri.Memory.allocRange off sz) =
      .ok ((allocRaw A).extract off.bytes.toNat (off.bytes.toNat + sz.bytes.toNat)) := by
  have htot : A.byteSize.bytes.toNat < 2 ^ 64 := by
    simpa [UInt64.size] using A.byteSize.bytes.toNat_lt_size
  have hlt : off.bytes.toNat + sz.bytes.toNat < 2 ^ 64 := by omega
  have hend := allocRange_endExclusive_of_lt hlt
  have hadd_toNat : (off.bytes + sz.bytes).toNat = off.bytes.toNat + sz.bytes.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by simpa [UInt64.size] using hlt)]
  have hrawsize : (allocRaw A).size = A.byteSize.bytes.toNat := hlen
  have hle1 : off.bytes ≤ off.bytes + sz.bytes := by
    rw [UInt64.le_iff_toNat_le, hadd_toNat]; omega
  have hle2 : off.bytes + sz.bytes ≤ A.byteSize.bytes := by
    rw [UInt64.le_iff_toNat_le, hadd_toNat]; omega
  unfold allocCheckedSlice
  rw [hend]
  simp [hrawsize, Miri.Memory.allocRange, hle1, hle2, Miri.ABI.Size.ofBytes,
    hadd_toNat, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- Reading back an in-bounds slice of `B` whose bytes equal `allocLeBytes sc.bits sz`
returns `Scalar.fromScalarInt msc`. -/
theorem alloc_readScalar_of_extract {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) {E : Type} {B : Miri.Memory.Allocation AnnealProv E}
    {off : Miri.ABI.Size}
    (hlen : B.len = B.byteSize.bytes.toNat)
    (hmask : B.initializationMask = Miri.Memory.InitMask.new B.byteSize true)
    (hin : off.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat ≤ B.byteSize.bytes.toNat)
    (hextract :
      (allocRaw B).extract off.bytes.toNat
        (off.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat) =
      allocLeBytes sc.bits (translateSizeBytes sc.sizeBytes).bytes.toNat) :
    B.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange off (translateSizeBytes sc.sizeBytes)) false =
        .ok (Miri.Memory.Scalar.fromScalarInt msc) := by
  have hslice : allocCheckedSlice B
      (Miri.Memory.allocRange off (translateSizeBytes sc.sizeBytes)) =
      .ok (allocLeBytes sc.bits (translateSizeBytes sc.sizeBytes).bytes.toNat) := by
    rw [allocCheckedSlice_of_inbounds hlen hin, hextract]
  have hn := translateSizeBytes_toNat_of_valid hrel.validBytes
  have hn16 := translateSizeBytes_le_16_of_valid hrel.validBytes
  have hoff : Miri.Memory.PointerProvenance.offsetIsAddr AnnealProv = true := rfl
  have hmod : sc.bits % 2 ^ (8 * (translateSizeBytes sc.sizeBytes).bytes.toNat) = sc.bits := by
    rw [hn, ← alloc_scalarModulus_eq_two_pow]
    exact Nat.mod_eq_of_lt hrel.canonical
  have hinit := initMask_new_true_isRangeInitialized_inbounds hin
  rw [alloc_readScalar_eq]
  unfold allocReadScalar
  rw [hmask, hinit]
  simp only [Except.mapError, bind, Except.bind]
  rw [alloc_getBytesUnchecked_eq, hslice]
  simp only []
  rw [allocReadTargetUInt_leBytes _ _ hn16, hmod]
  have hrange :
      (Miri.Memory.allocRange off (translateSizeBytes sc.sizeBytes)).size =
        translateSizeBytes sc.sizeBytes := rfl
  simp only [Bool.false_eq_true, ↓reduceIte, hoff, hrange, alloc_fromUInt hrel]

/-- If two allocations have the same `byteSize`, `len`, `initializationMask`,
`provenanceMap`, and agree on `(allocRaw _).extract off (off + sz)`, then
`readScalar` on `allocRange off sz` returns the same result on both. -/
theorem alloc_readScalar_congr_of_extract {E : Type}
    {A B : Miri.Memory.Allocation AnnealProv E}
    {off sz : Miri.ABI.Size}
    (hsz : A.byteSize = B.byteSize)
    (hlenA : A.len = A.byteSize.bytes.toNat)
    (hlenB : B.len = B.byteSize.bytes.toNat)
    (hmask : A.initializationMask = B.initializationMask)
    (hprov : A.provenanceMap = B.provenanceMap)
    (hin : off.bytes.toNat + sz.bytes.toNat ≤ B.byteSize.bytes.toNat)
    (hextract :
      (allocRaw A).extract off.bytes.toNat (off.bytes.toNat + sz.bytes.toNat) =
      (allocRaw B).extract off.bytes.toNat (off.bytes.toNat + sz.bytes.toNat)) :
    A.readScalar annealTargetDataLayout (Miri.Memory.allocRange off sz) false =
      B.readScalar annealTargetDataLayout (Miri.Memory.allocRange off sz) false := by
  have hinA : off.bytes.toNat + sz.bytes.toNat ≤ A.byteSize.bytes.toNat := by
    rw [hsz]; exact hin
  have hslice_eq :
      Miri.Memory.Allocation.getBytesUnchecked A (Miri.Memory.allocRange off sz) =
      Miri.Memory.Allocation.getBytesUnchecked B (Miri.Memory.allocRange off sz) := by
    rw [alloc_getBytesUnchecked_eq, alloc_getBytesUnchecked_eq,
      allocCheckedSlice_of_inbounds hlenA hinA,
      allocCheckedSlice_of_inbounds hlenB hin, hextract]
  rw [alloc_readScalar_eq, alloc_readScalar_eq]
  unfold allocReadScalar
  rw [hmask, hprov, hslice_eq]

/-- Writing a `ScalarRel`-related scalar at any in-bounds byte offset `off` in an
initialized mutable allocation `A` succeeds, preserves `byteSize`, `len`,
`mutability`, `provenanceMap`, and `initializationMask`, reads back `msc` at
`off`, and preserves `readScalar` at every disjoint in-bounds range. -/
theorem alloc_writeScalar_at_offset
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc)
    {E : Type} {A : Miri.Memory.Allocation AnnealProv E}
    {off : Miri.ABI.Size}
    (hlen : A.len = A.byteSize.bytes.toNat)
    (hmut : A.mutability = .Mut)
    (hprov : A.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask : A.initializationMask = Miri.Memory.InitMask.new A.byteSize true)
    (hin : off.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat ≤ A.byteSize.bytes.toNat) :
    ∃ alloc' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange off msc.size)
        (Miri.Memory.Scalar.fromScalarInt msc) A = .ok () alloc' ∧
      alloc'.byteSize = A.byteSize ∧
      alloc'.len = A.byteSize.bytes.toNat ∧
      alloc'.align = A.align ∧
      alloc'.mutability = .Mut ∧
      alloc'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      alloc'.initializationMask = Miri.Memory.InitMask.new A.byteSize true ∧
      alloc'.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange off (translateSizeBytes sc.sizeBytes)) false =
          .ok (Miri.Memory.Scalar.fromScalarInt msc) ∧
      (∀ otherOff otherSz : Miri.ABI.Size,
        otherOff.bytes.toNat + otherSz.bytes.toNat ≤ A.byteSize.bytes.toNat →
        (otherOff.bytes.toNat + otherSz.bytes.toNat ≤ off.bytes.toNat ∨
          off.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat ≤ otherOff.bytes.toNat) →
        alloc'.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange otherOff otherSz) false =
        A.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange otherOff otherSz) false) := by
  have htot : A.byteSize.bytes.toNat < 2 ^ 64 := by
    simpa [UInt64.size] using A.byteSize.bytes.toNat_lt_size
  have hlt : off.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat < 2 ^ 64 := by omega
  have hend := allocRange_endExclusive_of_lt hlt
  have hrange :
      (Miri.Memory.allocRange off (translateSizeBytes sc.sizeBytes)).size =
        translateSizeBytes sc.sizeBytes := rfl
  have hconv := alloc_toBitsOrPtrInternal hrel
  have hraw : (allocRaw A).size = A.byteSize.bytes.toNat := hlen
  have hslice : Miri.Memory.Allocation.getBytesUnchecked A
      (Miri.Memory.allocRange off (translateSizeBytes sc.sizeBytes)) =
      .ok ((allocRaw A).extract off.bytes.toNat
        (off.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat)) := by
    rw [alloc_getBytesUnchecked_eq, allocCheckedSlice_of_inbounds hlen hin]
  unfold Miri.Memory.Allocation.getBytesUnchecked at hslice
  have hmask2 : A.initializationMask.setRange
      (Miri.Memory.allocRange off (translateSizeBytes sc.sizeBytes)) true =
      .ok (Miri.Memory.InitMask.new A.byteSize true) := by
    rw [hmask]
    exact initMask_new_true_setRange_inbounds hin
  unfold Miri.Memory.Allocation.initializationMask at hmask2
  have hprov2 := hprov
  unfold Miri.Memory.Allocation.provenanceMap at hprov2
  rw [hrel.size_eq]
  unfold Miri.Memory.Allocation.writeScalar
  simp only [hmut, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hrange, hconv, pure_bind]
  rw [hslice]
  simp only [hmask2]
  rw [hprov2, Miri.Memory.ProvenanceMap.clear_new _ _ _ _ ?pos hend]
  case pos => decide
  have hn16 := translateSizeBytes_le_16_of_valid hrel.validBytes
  simp only []
  split
  · rename_i data hdata
    have hdata' : allocTargetUIntBytes annealTargetDataLayout
        (translateSizeBytes sc.sizeBytes) (BitVec.ofNat 128 sc.bits) = .ok data := hdata
    rw [allocTargetUIntBytes_spec _ _ hn16] at hdata'
    cases hdata'
    have htoNat : (BitVec.ofNat 128 sc.bits).toNat = sc.bits :=
      bitVec_ofNat_128_toNat hrel.validBytes hrel.canonical
    have hstart : (Miri.Memory.allocRange off
        (translateSizeBytes sc.sizeBytes)).start.bytes.toNat = off.bytes.toNat := rfl
    have hlen' := hlen
    unfold Miri.Memory.Allocation.len at hlen'
    have hbytes_size :
        ((allocRaw A).extract 0 off.bytes.toNat ++
          allocLeBytes sc.bits (translateSizeBytes sc.sizeBytes).bytes.toNat ++
          (allocRaw A).extract
            (off.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat)
            (allocRaw A).size).size =
          A.byteSize.bytes.toNat := by
      simp only [Array.size_append, Array.size_extract, allocLeBytes_size, hraw]
      omega
    have hbytes_size' :
        ((allocRaw A).extract 0
            (Miri.Memory.allocRange off (translateSizeBytes sc.sizeBytes)).start.bytes.toNat ++
          allocLeBytes (BitVec.ofNat 128 sc.bits).toNat
            (translateSizeBytes sc.sizeBytes).bytes.toNat ++
          (allocRaw A).extract
            ((Miri.Memory.allocRange off (translateSizeBytes sc.sizeBytes)).start.bytes.toNat +
              (translateSizeBytes sc.sizeBytes).bytes.toNat)
            (allocRaw A).size).size =
          A.byteSize.bytes.toNat := by
      simpa only [hstart, htoNat] using hbytes_size
    unfold allocRaw at hbytes_size'
    unfold Miri.Memory.Allocation.byteSize at hbytes_size'
    simp only [hbytes_size', bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    refine ⟨_, rfl, rfl, hbytes_size', rfl, rfl, rfl, hmask.symm ▸ rfl, ?_, ?_⟩
    · refine alloc_readScalar_of_extract (B := _) hrel hbytes_size' rfl hin ?_
      have hmid := array_extract_middle (allocRaw A)
        (allocLeBytes sc.bits (translateSizeBytes sc.sizeBytes).bytes.toNat)
        off.bytes.toNat (translateSizeBytes sc.sizeBytes).bytes.toNat
        (by rw [hraw]; exact hin)
        (allocLeBytes_size _ _)
      simpa only [allocRaw, hstart, htoNat] using hmid
    · intro otherOff otherSz hotherIn hdisj
      refine alloc_readScalar_congr_of_extract (A := _) (B := A) rfl hbytes_size' hlen (hmask.symm) (hprov.symm) hotherIn ?_
      rcases hdisj with hleft | hright
      · have hd := array_extract_disjoint_left (allocRaw A)
          (allocLeBytes sc.bits (translateSizeBytes sc.sizeBytes).bytes.toNat)
          off.bytes.toNat (translateSizeBytes sc.sizeBytes).bytes.toNat
          otherOff.bytes.toNat (otherOff.bytes.toNat + otherSz.bytes.toNat)
          (by rw [hraw]; exact hin) (allocLeBytes_size _ _) hleft
        simpa only [allocRaw, hstart, htoNat] using hd
      · have hd := array_extract_disjoint_right (allocRaw A)
          (allocLeBytes sc.bits (translateSizeBytes sc.sizeBytes).bytes.toNat)
          off.bytes.toNat (translateSizeBytes sc.sizeBytes).bytes.toNat
          otherOff.bytes.toNat (otherOff.bytes.toNat + otherSz.bytes.toNat)
          (by rw [hraw]; exact hin) (allocLeBytes_size _ _) hright
        simpa only [allocRaw, hstart, htoNat] using hd
  · rename_i err herr
    have herr' : allocTargetUIntBytes annealTargetDataLayout
        (translateSizeBytes sc.sizeBytes) (BitVec.ofNat 128 sc.bits) = .error err := herr
    rw [allocTargetUIntBytes_spec _ _ hn16] at herr'
    cases herr'

/-! ## 6. `Allocation.fromBytes` on zeroed storage & `ArraySliceRel` preservation -/

private def allocSizeForArray (length : Nat) :
    Except Miri.Memory.AllocError Miri.ABI.Size := do
  if length > 18446744073709551615 then throw (.storageLengthOverflow length)
  let size := Miri.ABI.Size.ofBytes (UInt64.ofNat length)
  if size.bytes.toNat == length then return size
  throw (.storageLengthOverflow length)

private theorem allocCheckedAlign_of_pow2_le_29 {align : Miri.ABI.Align}
    (h : align.pow2 ≤ 29) : allocCheckedAlign align = .ok align := by
  have H : ∀ p ≤ 29, allocCheckedAlign ⟨p⟩ = .ok ⟨p⟩ := by decide
  cases align with | mk p => exact H p h

private theorem allocSizeForArray_size (sz : Miri.ABI.Size) :
    allocSizeForArray sz.bytes.toNat = .ok sz := by
  have hlt : sz.bytes.toNat < 2 ^ 64 := by
    simpa [UInt64.size] using sz.bytes.toNat_lt_size
  have hnot : ¬ (sz.bytes.toNat > 18446744073709551615) := by omega
  cases sz with | mk b =>
  unfold allocSizeForArray
  simp [hnot, Miri.ABI.Size.ofBytes, pure, Except.pure]

/-- `Allocation.fromBytes` on `Array.replicate sz.bytes.toNat 0` succeeds for any
alignment with `align.pow2 ≤ 29` and produces a live mutable allocation with
`InitMask.new sz true`. -/
theorem fromBytes_replicate_zero_spec (sz : Miri.ABI.Size) (align : Miri.ABI.Align)
    (halign : align.pow2 ≤ 29) :
    ∃ a : Miri.Memory.Allocation AnnealProv Unit,
      Miri.Memory.Allocation.fromBytes (Array.replicate sz.bytes.toNat 0) align .Mut = .ok a ∧
      a.byteSize = sz ∧
      a.len = sz.bytes.toNat ∧
      a.align = align ∧
      a.mutability = .Mut ∧
      a.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      a.initializationMask = Miri.Memory.InitMask.new sz true ∧
      ∀ {E : Type} (extra : E),
        (a.withExtra extra).byteSize = sz ∧
        (a.withExtra extra).len = sz.bytes.toNat ∧
        (a.withExtra extra).align = align ∧
        (a.withExtra extra).mutability = .Mut ∧
        (a.withExtra extra).provenanceMap = Miri.Memory.ProvenanceMap.new ∧
        (a.withExtra extra).initializationMask = Miri.Memory.InitMask.new sz true := by
  have ha : allocCheckedAlign align = .ok align := allocCheckedAlign_of_pow2_le_29 halign
  have hs : allocSizeForArray (Array.replicate sz.bytes.toNat (0 : UInt8)).size = .ok sz := by
    rw [Array.size_replicate]
    exact allocSizeForArray_size sz
  unfold Miri.Memory.Allocation.fromBytes
  simp only [bind, Except.bind]
  split
  · rename_i err herr
    have herr' : allocCheckedAlign align = .error err := herr
    rw [ha] at herr'; cases herr'
  · rename_i align' halign'
    have halign'' : allocCheckedAlign align = .ok align' := halign'
    rw [ha] at halign''; cases halign''
    split
    · rename_i err herr
      have herr' : allocSizeForArray (Array.replicate sz.bytes.toNat (0 : UInt8)).size = .error err := herr
      rw [hs] at herr'; cases herr'
    · rename_i size' hsize'
      have hsize'' : allocSizeForArray (Array.replicate sz.bytes.toNat (0 : UInt8)).size = .ok size' := hsize'
      rw [hs] at hsize''; cases hsize''
      simp [Array.size_replicate, pure, Except.pure,
        Miri.Memory.Allocation.byteSize, Miri.Memory.Allocation.len,
        Miri.Memory.Allocation.provenanceMap, Miri.Memory.Allocation.initializationMask,
        Miri.Memory.Allocation.withExtra]

theorem align_fromBytes_pow2_le_29 {b : UInt64} {a : Miri.ABI.Align}
    (h : Miri.ABI.Align.fromBytes b = .ok a) : a.pow2 ≤ 29 := by
  unfold Miri.ABI.Align.fromBytes at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h; decide
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h; simp only [Miri.ABI.Align.MAX] at *; omega

theorem translateAlignBytes_pow2_le_29 (bytes : Nat) :
    (translateAlignBytes bytes).pow2 ≤ 29 := by
  unfold translateAlignBytes
  split
  · rename_i a ha
    exact align_fromBytes_pow2_le_29 ha
  · decide

theorem translateTypeLayout_align_pow2_le_29 (tl : Layout.TypeLayout) :
    (translateTypeLayout tl).align.abi.pow2 ≤ 29 :=
  translateAlignBytes_pow2_le_29 tl.align.bytes

theorem scalarLayoutOfRigidTy_align_pow2_le_29 {k : RigidTy} {l : Miri.ABI.LayoutData}
    (h : scalarLayoutOfRigidTy k = some l) : l.align.abi.pow2 ≤ 29 := by
  unfold scalarLayoutOfRigidTy at h
  split at h
  · cases h; exact translateAlignBytes_pow2_le_29 _
  · cases h; exact translateAlignBytes_pow2_le_29 _
  · cases h; exact translateAlignBytes_pow2_le_29 _
  · cases h; exact translateAlignBytes_pow2_le_29 _
  · cases h; exact translateAlignBytes_pow2_le_29 _
  · cases h; exact translateAlignBytes_pow2_le_29 _
  · cases h; exact translateAlignBytes_pow2_le_29 _
  · cases h; exact translateAlignBytes_pow2_le_29 _
  · cases h; decide
  · cases h; decide
  · cases h; decide
  · cases h; decide
  · cases h; decide
  · cases h; decide
  · cases h

theorem translateTy_align_pow2_le_29 (ty : Ty) (layouts : LayoutTable) :
    (translateTy ty layouts).layout.align.abi.pow2 ≤ 29 := by
  unfold translateTy
  dsimp only
  
  split
  · exact translateAlignBytes_pow2_le_29 _
  · exact translateAlignBytes_pow2_le_29 _
  · exact translateAlignBytes_pow2_le_29 _
  · exact translateAlignBytes_pow2_le_29 _
  · exact translateAlignBytes_pow2_le_29 _
  · exact translateAlignBytes_pow2_le_29 _
  · exact translateAlignBytes_pow2_le_29 _
  · exact translateAlignBytes_pow2_le_29 _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · split
    · exact translateTypeLayout_align_pow2_le_29 _
    · decide

/-- An empty `ArraySliceRel elemKind 0 layouts [] relOffset alloc` holds on any
initialized mutable allocation where `relOffset.bytes.toNat ≤ alloc.byteSize.bytes.toNat`. -/
theorem ArraySliceRel.nil
    (elemKind : RigidTy) (layouts : LayoutTable)
    {relOffset : Miri.ABI.Size}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hin : relOffset.bytes.toNat ≤ alloc.byteSize.bytes.toNat)
    (hlen : alloc.len = alloc.byteSize.bytes.toNat)
    (hmut : alloc.mutability = .Mut)
    (hprov : alloc.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask : alloc.initializationMask = Miri.Memory.InitMask.new alloc.byteSize true) :
    ArraySliceRel elemKind 0 layouts [] relOffset alloc := by
  refine ⟨rfl, hlen, hmut, hprov, hmask, by simpa using hin, ?_⟩
  intro k elemVal hget
  cases hget

/-- Reading element `idx` from an `ArraySliceRel` returns the corresponding
`ScalarRel`-related Miri scalar. -/
theorem ArraySliceRel.readScalar_get
    {elemKind : RigidTy} {count : Nat} {layouts : LayoutTable}
    {elems : List Value} {relOffset : Miri.ABI.Size}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hslice : ArraySliceRel elemKind count layouts elems relOffset alloc)
    {idx : Nat} {elemVal : Value}
    (hget : get? elems idx = some elemVal) :
    let elemTy : Ty := { kind := elemKind, layoutIdx := 0 }
    let elemLay := (translateTy elemTy layouts).layout
    let elemOff := Miri.ABI.Size.ofBytes (relOffset.bytes + UInt64.ofNat (idx * elemLay.size.bytes.toNat))
    ∃ sc msc,
      elemVal = .scalar sc ∧
      ImmediateRel elemTy layouts elemVal (.scalar (.fromScalarInt msc)) ∧
      alloc.readScalar
        annealTargetDataLayout
        (Miri.Memory.allocRange elemOff elemLay.size)
        false = .ok (.fromScalarInt msc) := by
  obtain ⟨sc, msc, rfl, hsz, hbool, hchar, hrel, hread⟩ := hslice.elem_rel idx elemVal hget
  exact ⟨sc, msc, rfl, ImmediateRel.scalar sc msc hrel hsz hbool hchar, hread⟩

/-- Appending one `ImmediateRel`-related scalar at offset `relOffset + count * elemSize`
extends `ArraySliceRel elemKind count layouts elems` to
`ArraySliceRel elemKind (count + 1) layouts (elems ++ [.scalar sc])`. -/
theorem ArraySliceRel.writeScalar_snoc
    {elemKind : RigidTy} {count : Nat} {layouts : LayoutTable}
    {elems : List Value} {relOffset : Miri.ABI.Size}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hslice : ArraySliceRel elemKind count layouts elems relOffset alloc)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc)
    (hsz : (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size =
      translateSizeBytes sc.sizeBytes)
    (hbool : elemKind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar : elemKind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true)
    (hmask_full : alloc.initializationMask = Miri.Memory.InitMask.new alloc.byteSize true)
    (hin :
      relOffset.bytes.toNat +
        (count + 1) * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat ≤
          alloc.byteSize.bytes.toNat) :
    ∃ alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange
          (Miri.ABI.Size.ofBytes
            (relOffset.bytes +
              UInt64.ofNat
                (count * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat)))
          msc.size)
        (.fromScalarInt msc) alloc = .ok () alloc' ∧
      alloc'.byteSize = alloc.byteSize ∧
      alloc'.align = alloc.align ∧
      alloc'.initializationMask = Miri.Memory.InitMask.new alloc.byteSize true ∧
      ArraySliceRel elemKind (count + 1) layouts (elems ++ [.scalar sc]) relOffset alloc' := by
  let elemSize := (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size
  have helemSize_eq : elemSize = translateSizeBytes sc.sizeBytes := hsz
  have hin' : relOffset.bytes.toNat + (count + 1) * elemSize.bytes.toNat ≤ alloc.byteSize.bytes.toNat := hin
  have hpos : 0 < elemSize.bytes.toNat := by
    rw [helemSize_eq, translateSizeBytes_toNat_of_valid hrel.validBytes]
    rcases hrel.validBytes with h | h | h | h | h <;> omega
  have htot : alloc.byteSize.bytes.toNat < 2 ^ 64 := by
    simpa [UInt64.size] using alloc.byteSize.bytes.toNat_lt_size
  have hmul_eq : (count + 1) * elemSize.bytes.toNat =
      count * elemSize.bytes.toNat + elemSize.bytes.toNat := by
    rw [Nat.add_mul, Nat.one_mul]
  let elemOff := Miri.ABI.Size.ofBytes
    (relOffset.bytes + UInt64.ofNat (count * elemSize.bytes.toNat))
  have hoff_toNat : elemOff.bytes.toNat =
      relOffset.bytes.toNat + count * elemSize.bytes.toNat := by
    have hlt1 : count * elemSize.bytes.toNat < 2 ^ 64 := by omega
    have hlt2 : relOffset.bytes.toNat + count * elemSize.bytes.toNat < 2 ^ 64 := by omega
    simp only [elemOff, Miri.ABI.Size.ofBytes, UInt64.toNat_add, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (by simpa [UInt64.size] using hlt1),
      Nat.mod_eq_of_lt (by simpa [UInt64.size] using hlt2)]
  have hin_off : elemOff.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat ≤
      alloc.byteSize.bytes.toNat := by
    rw [hoff_toNat, ← helemSize_eq]; omega
  obtain ⟨alloc', hwrite, hbyteSize, hlen', halign, hmut', hprov', hmask', hread_at, hread_disj⟩ :=
    alloc_writeScalar_at_offset hrel hslice.alloc_len hslice.alloc_mut hslice.alloc_prov hmask_full hin_off
  refine ⟨alloc', hwrite, hbyteSize, halign, hmask', ?_⟩
  refine ⟨?_, by rw [hbyteSize]; exact hlen', hmut', hprov',
    by rw [hbyteSize]; exact hmask', by rw [hbyteSize]; exact hin, ?_⟩
  · rw [List.length_append, List.length_singleton, hslice.elems_len]
  · intro idx elemVal hget
    
    change (elems ++ [.scalar sc])[idx]? = some elemVal at hget
    by_cases hlt_idx : idx < elems.length
    · rw [List.getElem?_append_left hlt_idx] at hget
      have hget' : get? elems idx = some elemVal := hget
      obtain ⟨sc_i, msc_i, rfl, hsz_i, hbool_i, hchar_i, hrel_i, hread_i⟩ :=
        hslice.elem_rel idx elemVal hget'
      refine ⟨sc_i, msc_i, rfl, hsz_i, hbool_i, hchar_i, hrel_i, ?_⟩
      let idxOff := Miri.ABI.Size.ofBytes
        (relOffset.bytes + UInt64.ofNat (idx * elemSize.bytes.toNat))
      have hidx_lt_count : idx < count := by rw [← hslice.elems_len]; exact hlt_idx
      have hidx_le : (idx + 1) * elemSize.bytes.toNat ≤ count * elemSize.bytes.toNat :=
        Nat.mul_le_mul_right _ hidx_lt_count
      have hidx_add : idx * elemSize.bytes.toNat + elemSize.bytes.toNat ≤
          count * elemSize.bytes.toNat := by
        simpa [Nat.add_mul] using hidx_le
      have hidx_toNat : idxOff.bytes.toNat =
          relOffset.bytes.toNat + idx * elemSize.bytes.toNat := by
        have hlt1 : idx * elemSize.bytes.toNat < 2 ^ 64 := by omega
        have hlt2 : relOffset.bytes.toNat + idx * elemSize.bytes.toNat < 2 ^ 64 := by omega
        simp only [idxOff, Miri.ABI.Size.ofBytes, UInt64.toNat_add, UInt64.toNat_ofNat',
          Nat.mod_eq_of_lt (by simpa [UInt64.size] using hlt1),
          Nat.mod_eq_of_lt (by simpa [UInt64.size] using hlt2)]
      have hcongr := hread_disj idxOff elemSize (by rw [hidx_toNat]; omega)
        (Or.inl (by rw [hidx_toNat, hoff_toNat]; omega))
      rw [hcongr]
      exact hread_i
    · have hge_idx : elems.length ≤ idx := Nat.le_of_not_lt hlt_idx
      rw [List.getElem?_append_right hge_idx] at hget
      have hlt_one : idx - elems.length < 1 := by
        simpa using (List.getElem?_eq_some_iff.mp hget).1
      have heq_idx : idx = elems.length := by omega
      subst heq_idx
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      intro elemTy elemLay elemOff
      refine ⟨sc, msc, rfl, hsz, hbool, hchar, hrel, ?_⟩
      dsimp [elemOff, elemLay, elemTy]; simpa only [hslice.elems_len, ← hsz] using hread_at

/-- Overwriting element `idx < count` in `ArraySliceRel elemKind count layouts elems`
updates the relation to `ArraySliceRel elemKind count layouts (elems.set idx (.scalar sc))`. -/
theorem ArraySliceRel.writeScalar_set
    {elemKind : RigidTy} {count : Nat} {layouts : LayoutTable}
    {elems : List Value} {relOffset : Miri.ABI.Size}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hslice : ArraySliceRel elemKind count layouts elems relOffset alloc)
    {idx : Nat} (hlt : idx < count)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc)
    (hsz : (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size =
      translateSizeBytes sc.sizeBytes)
    (hbool : elemKind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar : elemKind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) :
    ∃ alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange
          (Miri.ABI.Size.ofBytes
            (relOffset.bytes +
              UInt64.ofNat
                (idx * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat)))
          msc.size)
        (.fromScalarInt msc) alloc = .ok () alloc' ∧
      alloc'.byteSize = alloc.byteSize ∧
      alloc'.align = alloc.align ∧
      alloc'.initializationMask = alloc.initializationMask ∧
      ArraySliceRel elemKind count layouts (elems.set idx (.scalar sc)) relOffset alloc' := by
  let elemSize := (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size
  have helemSize_eq : elemSize = translateSizeBytes sc.sizeBytes := hsz
  have hpos : 0 < elemSize.bytes.toNat := by
    rw [helemSize_eq, translateSizeBytes_toNat_of_valid hrel.validBytes]
    rcases hrel.validBytes with h | h | h | h | h <;> omega
  have htot : alloc.byteSize.bytes.toNat < 2 ^ 64 := by
    simpa [UInt64.size] using alloc.byteSize.bytes.toNat_lt_size
  have hin : relOffset.bytes.toNat + count * elemSize.bytes.toNat ≤ alloc.byteSize.bytes.toNat :=
    hslice.slice_in_bounds
  have hidx_le : (idx + 1) * elemSize.bytes.toNat ≤ count * elemSize.bytes.toNat :=
    Nat.mul_le_mul_right _ hlt
  have hidx_add : idx * elemSize.bytes.toNat + elemSize.bytes.toNat ≤
      count * elemSize.bytes.toNat := by
    simpa [Nat.add_mul] using hidx_le
  have hmask_full := hslice.alloc_mask
  let elemOff := Miri.ABI.Size.ofBytes
    (relOffset.bytes + UInt64.ofNat (idx * elemSize.bytes.toNat))
  have hoff_toNat : elemOff.bytes.toNat =
      relOffset.bytes.toNat + idx * elemSize.bytes.toNat := by
    have hlt1 : idx * elemSize.bytes.toNat < 2 ^ 64 := by omega
    have hlt2 : relOffset.bytes.toNat + idx * elemSize.bytes.toNat < 2 ^ 64 := by omega
    simp only [elemOff, Miri.ABI.Size.ofBytes, UInt64.toNat_add, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (by simpa [UInt64.size] using hlt1),
      Nat.mod_eq_of_lt (by simpa [UInt64.size] using hlt2)]
  have hin_off : elemOff.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat ≤
      alloc.byteSize.bytes.toNat := by
    rw [hoff_toNat, ← helemSize_eq]; omega
  obtain ⟨alloc', hwrite, hbyteSize, hlen', halign, hmut', hprov', hmask', hread_at, hread_disj⟩ :=
    alloc_writeScalar_at_offset hrel hslice.alloc_len hslice.alloc_mut hslice.alloc_prov hmask_full hin_off
  refine ⟨alloc', hwrite, hbyteSize, halign, hmask'.trans hmask_full.symm, ?_⟩
  refine ⟨by rw [List.length_set, hslice.elems_len], by rw [hbyteSize]; exact hlen',
    hmut', hprov', by rw [hbyteSize]; exact hmask',
    by rw [hbyteSize]; exact hin, ?_⟩
  intro j elemVal hget
  
  change (elems.set idx (.scalar sc))[j]? = some elemVal at hget
  rw [List.getElem?_set] at hget
  by_cases heq : idx = j
  · subst heq
    have hlt_elems : idx < elems.length := by rw [hslice.elems_len]; exact hlt
    simp only [↓reduceIte, hlt_elems, Option.some.injEq] at hget
    subst hget
    intro elemTy elemLay elemOff
    refine ⟨sc, msc, rfl, hsz, hbool, hchar, hrel, ?_⟩
    dsimp [elemOff, elemLay, elemTy]; simpa only [← hsz] using hread_at
  · simp only [heq, ↓reduceIte] at hget
    have hj_lt_elems : j < elems.length := (List.getElem?_eq_some_iff.mp hget).1
    have hj_lt : j < count := by rw [← hslice.elems_len]; exact hj_lt_elems
    have hget' : get? elems j = some elemVal := hget
    obtain ⟨sc_j, msc_j, rfl, hsz_j, hbool_j, hchar_j, hrel_j, hread_j⟩ :=
      hslice.elem_rel j elemVal hget'
    have hj_le : (j + 1) * elemSize.bytes.toNat ≤ count * elemSize.bytes.toNat :=
      Nat.mul_le_mul_right _ hj_lt
    have hj_add : j * elemSize.bytes.toNat + elemSize.bytes.toNat ≤
        count * elemSize.bytes.toNat := by
      simpa [Nat.add_mul] using hj_le
    let jOff := Miri.ABI.Size.ofBytes
      (relOffset.bytes + UInt64.ofNat (j * elemSize.bytes.toNat))
    have hj_toNat : jOff.bytes.toNat =
        relOffset.bytes.toNat + j * elemSize.bytes.toNat := by
      have hlt1 : j * elemSize.bytes.toNat < 2 ^ 64 := by omega
      have hlt2 : relOffset.bytes.toNat + j * elemSize.bytes.toNat < 2 ^ 64 := by omega
      simp only [jOff, Miri.ABI.Size.ofBytes, UInt64.toNat_add, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt (by simpa [UInt64.size] using hlt1),
        Nat.mod_eq_of_lt (by simpa [UInt64.size] using hlt2)]
    have hdisj : jOff.bytes.toNat + elemSize.bytes.toNat ≤ elemOff.bytes.toNat ∨
        elemOff.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat ≤ jOff.bytes.toNat := by
      rw [hj_toNat, hoff_toNat, ← helemSize_eq]
      rcases Nat.lt_or_gt_of_ne (Ne.symm heq) with hlt_j | hgt_j
      · left
        have h1 : (j + 1) * elemSize.bytes.toNat ≤ idx * elemSize.bytes.toNat :=
          Nat.mul_le_mul_right _ hlt_j
        have h2 : j * elemSize.bytes.toNat + elemSize.bytes.toNat ≤ idx * elemSize.bytes.toNat := by
          simpa [Nat.add_mul] using h1
        omega
      · right
        have h1 : (idx + 1) * elemSize.bytes.toNat ≤ j * elemSize.bytes.toNat :=
          Nat.mul_le_mul_right _ hgt_j
        have h2 : idx * elemSize.bytes.toNat + elemSize.bytes.toNat ≤ j * elemSize.bytes.toNat := by
          simpa [Nat.add_mul] using h1
        omega
    refine ⟨sc_j, msc_j, rfl, hsz_j, hbool_j, hchar_j, hrel_j, ?_⟩
    rw [hread_disj jOff elemSize (by rw [hj_toNat]; omega) hdisj]
    exact hread_j

/-- Parametric specification of `writeScalarRepeatedly`: writing `n` copies of `msc`
starting at `relOffset + count * elemSize` extends `ArraySliceRel elemKind count layouts elems`
to `ArraySliceRel elemKind (count + n) layouts (elems ++ List.replicate n (.scalar sc))`. -/
theorem writeScalarRepeatedly_spec
    (n : Nat)
    {elemKind : RigidTy} {count : Nat} {layouts : LayoutTable}
    {elems : List Value} {relOffset : Miri.ABI.Size}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hslice : ArraySliceRel elemKind count layouts elems relOffset alloc)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc)
    (hsz : (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size =
      translateSizeBytes sc.sizeBytes)
    (hbool : elemKind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar : elemKind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true)
    (hmask_full : alloc.initializationMask = Miri.Memory.InitMask.new alloc.byteSize true)
    (hin :
      relOffset.bytes.toNat +
        (count + n) * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat ≤
          alloc.byteSize.bytes.toNat) :
    ∃ alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      writeScalarRepeatedly
        (Miri.ABI.Size.ofBytes
          (relOffset.bytes +
            UInt64.ofNat
              (count * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat)))
        (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size
        n (.fromScalarInt msc) alloc = .ok alloc' ∧
      alloc'.byteSize = alloc.byteSize ∧
      alloc'.align = alloc.align ∧
      alloc'.initializationMask = Miri.Memory.InitMask.new alloc.byteSize true ∧
      ArraySliceRel elemKind (count + n) layouts
        (elems ++ List.replicate n (.scalar sc)) relOffset alloc' := by
  let elemSize := (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size
  induction n generalizing count elems alloc with
  | zero =>
    refine ⟨alloc, rfl, rfl, rfl, hmask_full, ?_⟩
    simpa using hslice
  | succ k ih =>
    have hin' : relOffset.bytes.toNat + (count + (k + 1)) * elemSize.bytes.toNat ≤
        alloc.byteSize.bytes.toNat := hin
    have htot : alloc.byteSize.bytes.toNat < 2 ^ 64 := by
      simpa [UInt64.size] using alloc.byteSize.bytes.toNat_lt_size
    have hmul_k : (count + (k + 1)) * elemSize.bytes.toNat =
        (count + 1) * elemSize.bytes.toNat + k * elemSize.bytes.toNat := by
      have : count + (k + 1) = (count + 1) + k := by omega
      rw [this, Nat.add_mul]
    have hin1 :
        relOffset.bytes.toNat + (count + 1) * elemSize.bytes.toNat ≤
          alloc.byteSize.bytes.toNat := by omega
    obtain ⟨alloc₁, hwrite₁, hsz₁, halign₁, hmask₁, hslice₁⟩ :=
      hslice.writeScalar_snoc hrel hsz hbool hchar hmask_full hin1
    have hsc_size : msc.size = elemSize := by
      dsimp [elemSize]
      rw [hsz, ← hrel.size_eq]
    rw [hsc_size] at hwrite₁
    have hin_k :
        relOffset.bytes.toNat + ((count + 1) + k) * elemSize.bytes.toNat ≤
          alloc₁.byteSize.bytes.toNat := by
      rw [Nat.add_right_comm, hsz₁]
      exact hin
    obtain ⟨alloc₂, hwrite₂, hsz₂, halign₂, hmask₂, hslice₂⟩ :=
      ih hslice₁ (by rw [hsz₁]; exact hmask₁) hin_k
    have hoff_step :
        Miri.ABI.Size.ofBytes
          ((Miri.ABI.Size.ofBytes
              (relOffset.bytes + UInt64.ofNat (count * elemSize.bytes.toNat))).bytes +
            elemSize.bytes) =
        Miri.ABI.Size.ofBytes
          (relOffset.bytes + UInt64.ofNat ((count + 1) * elemSize.bytes.toNat)) := by
      have h1 : (count + 1) * elemSize.bytes.toNat =
          count * elemSize.bytes.toNat + elemSize.bytes.toNat := by
        rw [Nat.add_mul, Nat.one_mul]
      simp only [Miri.ABI.Size.ofBytes]
      congr 1
      apply UInt64.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      simp only [UInt64.toNat_toBitVec, UInt64.toNat_add, UInt64.toNat_ofNat']
      omega
    unfold writeScalarRepeatedly
    dsimp only [elemSize] at hwrite₁
    rw [hwrite₁]
    dsimp only
    
    rw [hoff_step, hwrite₂]
    refine ⟨alloc₂, rfl, hsz₂.trans hsz₁, halign₂.trans halign₁, by rw [← hsz₁]; exact hmask₂, ?_⟩
    have hrep : (elems ++ [.scalar sc]) ++ List.replicate k (.scalar sc) =
        elems ++ List.replicate (k + 1) (.scalar sc) := by
      rw [List.append_assoc, List.replicate_succ, List.singleton_append]
    have hcnt : (count + 1) + k = count + (k + 1) := by omega
    rw [← hrep, ← hcnt]
    exact hslice₂

end LeanMiriSpec.Correspondence
