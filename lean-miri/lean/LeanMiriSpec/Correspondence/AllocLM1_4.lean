/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.Relation

/-!
# Fresh Stack Allocations for `forceAllocation` (`LM-1.4`)

When `Miri.Interpreter.forceAllocation` moves an immediate local into memory,
Anneal's `allocateStack` hook creates the backing allocation with
`Allocation.tryNew size align .Uninit annealZeroedStorage` and stores it as
`allocation.withExtra none`; for a scalar immediate, `writeMemoryNoValidate`
then runs `Allocation.writeScalar` over the whole allocation. This module
proves:

* `freshStackAlloc_spec`: the fresh allocation has exactly `size` bytes, is
  mutable, has an alignment exponent of at most `29`, and does not report its
  bytes as initialized.
* `freshStackAlloc_writeScalar_readScalar`: writing a `ScalarRel`-related scalar
  at offset `0` succeeds, keeps size and mutability, initializes every byte, and
  reading the range back yields the same scalar.

`lean-miri` keeps the allocation fields and its byte-level helpers
(`checkedAlign`, `checkedSlice`, `pointerSize`, `targetUIntBytes`,
`readTargetUInt`) private. This module reaches them only through public
accessors (`byteSize`, `len`, `provenanceMap`, `initializationMask`,
`getBytesUnchecked`) and through `freshAlloc_*` replicas whose bodies match the
private originals, so the two agree definitionally (`rfl`). The byte-level core
is the little-endian round trip
`Σ_{i < n} (x / 2^(8i) % 256) * 2^(8i) = x % 2^(8n)` (`freshAlloc_leSum_spec`).
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Replicas of private `lean-miri` helpers -/

/-- The private byte storage (`rawBytes`) of an allocation, read through the
public `casesOn` eliminator. -/
private def freshAlloc_raw {P E : Type} (a : Miri.Memory.Allocation P E) : Array UInt8 :=
  Miri.Memory.Allocation.casesOn (motive := fun _ => Array UInt8) a
    (fun raw _ _ _ _ _ _ _ => raw)

/-- Replica of the private `Miri.Memory.checkedAlign` (identical body). -/
private def freshAlloc_checkedAlign (align : Miri.ABI.Align) :
    Except Miri.Memory.AllocError Miri.ABI.Align := do
  let bytes ← (Miri.ABI.Align.bytes align).mapError Miri.Memory.AllocError.alignment
  let normalized ← (Miri.ABI.Align.fromBytes bytes).mapError Miri.Memory.AllocError.alignment
  if normalized == align then return align
  throw (.alignment (.tooLarge bytes))

/-- Replica of the private `Miri.Memory.pointerSize` (identical body). -/
private def freshAlloc_pointerSize (layout : Miri.ABI.TargetDataLayout) : Miri.ABI.Size :=
  Miri.ABI.Size.fromBits layout.pointerWidth.bits

/-- Replica of the private `Miri.Memory.targetUIntBytes` (identical body). -/
private def freshAlloc_targetUIntBytes (layout : Miri.ABI.TargetDataLayout)
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

/-- Replica of the private `Miri.Memory.readTargetUInt` (identical body). -/
private def freshAlloc_readTargetUInt (layout : Miri.ABI.TargetDataLayout)
    (bytes : Array UInt8) : Except Miri.Memory.AllocError Miri.ABI.U128 := do
  if bytes.size > 16 then
    throw (.scalarBytesTooWide (Miri.ABI.Size.ofBytes (UInt64.ofNat bytes.size)))
  let mut value := 0
  for index in [:bytes.size] do
    let some byte := bytes[index]? | throw (.invalidSliceEndpoints index (index + 1) bytes.size)
    let valueIndex := if layout.endian == .little then index else bytes.size - index - 1
    value := value + byte.toNat * 2 ^ (8 * valueIndex)
  return BitVec.ofNat 128 value

/-- Replica of the private `Miri.Memory.Allocation.checkedSlice`, over
`freshAlloc_raw` and `byteSize`. -/
private def freshAlloc_checkedSlice {P E : Type} (allocation : Miri.Memory.Allocation P E)
    (range : Miri.Memory.AllocRange) : Except Miri.Memory.AllocError (Array UInt8) := do
  if (freshAlloc_raw allocation).size != allocation.byteSize.bytes.toNat then
    throw (.storageLengthMismatch allocation.byteSize (freshAlloc_raw allocation).size)
  let finish ← range.endExclusive |>.mapError Miri.Memory.AllocError.memory
  if range.start.bytes > finish.bytes || finish.bytes > allocation.byteSize.bytes then
    throw (.outOfBounds range allocation.byteSize)
  return (freshAlloc_raw allocation).extract range.start.bytes.toNat finish.bytes.toNat

private theorem freshAlloc_getBytesUnchecked_eq {P E : Type}
    (allocation : Miri.Memory.Allocation P E) (range : Miri.Memory.AllocRange) :
    Miri.Memory.Allocation.getBytesUnchecked allocation range =
      freshAlloc_checkedSlice allocation range := rfl

/-- Replica of `Miri.Memory.Allocation.readScalar` over public accessors and the
replicas above. -/
private def freshAlloc_readScalar {P E : Type} [DecidableEq P] [Miri.Memory.PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : Miri.ABI.TargetDataLayout)
    (range : Miri.Memory.AllocRange) (readProvenance : Bool) :
    Except Miri.Memory.AllocError (Miri.Memory.Scalar P) := do
  match ← (allocation.initializationMask.isRangeInitialized range).mapError
      Miri.Memory.AllocError.memory with
  | .error bad => throw (.invalidUninitBytes (some ⟨range, bad⟩))
  | .ok () => pure ()
  let bytes ← Miri.Memory.Allocation.getBytesUnchecked allocation range
  let bits ← freshAlloc_readTargetUInt layout bytes
  if readProvenance then
    let targetSize := freshAlloc_pointerSize layout
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
      (allocation.provenanceMap.rangeEmpty range (freshAlloc_pointerSize layout)).mapError
        Miri.Memory.AllocError.provenance
    if isEmpty then
      let scalar ← (Miri.Memory.Scalar.fromUInt bits range.size).mapError
        Miri.Memory.AllocError.scalar
      return scalar
    throw (.readPointerAsInt none)

private theorem freshAlloc_readScalar_eq {P E : Type} [DecidableEq P]
    [Miri.Memory.PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : Miri.ABI.TargetDataLayout)
    (range : Miri.Memory.AllocRange) (readProvenance : Bool) :
    allocation.readScalar layout range readProvenance =
      freshAlloc_readScalar allocation layout range readProvenance := rfl

/-! ## 2. Little-endian encoding and decoding -/

/-- Little-endian bytes of `x` at byte positions `0, ..., n - 1`. -/
private def freshAlloc_leBytes (x n : Nat) : Array UInt8 :=
  ((List.range' 0 n).map fun i => UInt8.ofNat ((x / 2 ^ (8 * i)) % 256)).toArray

private theorem freshAlloc_leBytes_size (x n : Nat) : (freshAlloc_leBytes x n).size = n := by
  simp [freshAlloc_leBytes]

private theorem freshAlloc_encode_loop (x : Nat) (l : List Nat) (acc : Array UInt8) :
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

private theorem freshAlloc_targetUIntBytes_spec (size : Miri.ABI.Size) (bits : Miri.ABI.U128)
    (hle : size.bytes.toNat ≤ 16) :
    freshAlloc_targetUIntBytes annealTargetDataLayout size bits =
      .ok (freshAlloc_leBytes bits.toNat size.bytes.toNat) := by
  have small : ¬ size.bytes > 16 := by
    simp only [GT.gt, UInt64.lt_iff_toNat_lt]
    simpa using Nat.not_lt.mpr hle
  have hle : (annealTargetDataLayout.endian == Miri.ABI.Endian.little) = true := rfl
  unfold freshAlloc_targetUIntBytes
  simp only [small, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range', hle,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure]
  rw [freshAlloc_encode_loop]
  simp [freshAlloc_leBytes]

/-- Partial little-endian sum
`Σ_{j < m} (x / 2^(8(k+j)) % 256) * 2^(8(k+j))`. -/
private def freshAlloc_leSum (x k : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) + freshAlloc_leSum x (k + 1) m

private theorem freshAlloc_leSum_spec (x : Nat) :
    ∀ m k, x % 2 ^ (8 * k) + freshAlloc_leSum x k m = x % 2 ^ (8 * (k + m)) := by
  intro m
  induction m with
  | zero => intro k; simp [freshAlloc_leSum]
  | succ m ih =>
    intro k
    have hstep : x % 2 ^ (8 * k) + x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) =
        x % 2 ^ (8 * (k + 1)) := by
      rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add, Nat.mod_mul]
      simp only [show (2 : Nat) ^ 8 = 256 by rfl]
      rw [Nat.mul_comm (2 ^ (8 * k))]
    simp only [freshAlloc_leSum]
    rw [← Nat.add_assoc, hstep, ih (k + 1), show k + 1 + m = k + (m + 1) by omega]

private theorem freshAlloc_decode_loop (x n : Nat)
    (f : Nat → Nat → Except Miri.Memory.AllocError (ForInStep Nat))
    (hf : ∀ index s, index < n →
      f index s = .ok (.yield (s + x / 2 ^ (8 * index) % 256 * 2 ^ (8 * index)))) :
    ∀ m k acc, k + m ≤ n →
      forIn (List.range' k m) acc f = .ok (acc + freshAlloc_leSum x k m) := by
  intro m
  induction m with
  | zero => intro k acc _; simp [freshAlloc_leSum, pure, Except.pure]
  | succ m ih =>
    intro k acc hkm
    rw [List.range'_succ, List.forIn_cons, hf k acc (by omega)]
    simp only [freshAlloc_leSum]
    rw [show (Except.ok (ForInStep.yield (acc + x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k))) :
        Except Miri.Memory.AllocError (ForInStep Nat)) = pure (ForInStep.yield _) from rfl,
      pure_bind]
    simp only
    rw [ih (k + 1) _ (by omega), Nat.add_assoc]

private theorem freshAlloc_readTargetUInt_leBytes (x n : Nat) (hn : n ≤ 16) :
    freshAlloc_readTargetUInt annealTargetDataLayout (freshAlloc_leBytes x n) =
      .ok (BitVec.ofNat 128 (x % 2 ^ (8 * n))) := by
  have small : ¬ n > 16 := by omega
  have hle : (annealTargetDataLayout.endian == Miri.ABI.Endian.little) = true := rfl
  unfold freshAlloc_readTargetUInt
  simp only [freshAlloc_leBytes_size, small, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range',
    hle, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [freshAlloc_decode_loop x n _ ?hf n 0 0 (by omega)]
  · have := freshAlloc_leSum_spec x n 0
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mod_one, Nat.zero_add] at this
    simp [this, pure, Except.pure, bind, Except.bind]
  · intro index s hi
    have hb : (x / 2 ^ (8 * index) % 256) < 256 := Nat.mod_lt _ (by decide)
    simp [freshAlloc_leBytes, hi, pure, Except.pure, Nat.mod_eq_of_lt hb]

/-! ## 3. Scalar helpers (adapted from `Simulation.lean`) -/

private theorem freshAlloc_translateSizeBytes_toNat {sz : Nat} (h : ValidScalarBytes sz) :
    (translateSizeBytes sz).bytes.toNat = sz := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem freshAlloc_translateSizeBytes_le_16 {sz : Nat} (h : ValidScalarBytes sz) :
    (translateSizeBytes sz).bytes.toNat ≤ 16 := by
  rw [freshAlloc_translateSizeBytes_toNat h]
  rcases h with h | h | h | h | h <;> omega

private theorem freshAlloc_scalarModulus_eq_two_pow (sz : Nat) :
    scalarModulus sz = 2 ^ (8 * sz) := by
  induction sz with
  | zero => rfl
  | succ k ih =>
    show 256 * scalarModulus k = 2 ^ (8 * (k + 1))
    rw [ih, show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add, Nat.mul_comm]

private theorem freshAlloc_bitVec_ofNat_toNat {sz x : Nat}
    (hsz : ValidScalarBytes sz) (hx : x < scalarModulus sz) :
    (BitVec.ofNat 128 x).toNat = x := by
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hle : scalarModulus sz ≤ 2 ^ 128 := by
    rw [freshAlloc_scalarModulus_eq_two_pow]
    exact Nat.pow_le_pow_right (by decide) (by rcases hsz with h | h | h | h | h <;> omega)
  omega

private theorem freshAlloc_validScalarBytes_bits_le_128 {sz : Nat} (h : ValidScalarBytes sz) :
    8 * sz ≤ 128 ∧ 0 < 8 * sz := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> omega

private theorem freshAlloc_zeroExtend_extractLsb_eq_ofNat (w : Nat) (hw0 : 0 < w)
    (hw128 : w ≤ 128) (data : BitVec 128) :
    BitVec.zeroExtend 128 (BitVec.extractLsb (w - 1) 0 data) =
      BitVec.ofNat 128 (data.toNat % 2 ^ w) := by
  apply BitVec.eq_of_toNat_eq
  unfold BitVec.zeroExtend BitVec.extractLsb BitVec.extractLsb'
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hlen : w - 1 + 1 = w := by omega
  simp only [Nat.sub_zero, Nat.shiftRight_zero, hlen]

private theorem freshAlloc_truncateFromUInt_spec {sz : Nat} (hsz : ValidScalarBytes sz)
    (data : BitVec 128) :
    ∃ msc : Miri.Memory.ScalarInt,
      Miri.Memory.ScalarInt.truncateFromUInt data (translateSizeBytes sz) =
        .ok (msc, BitVec.ofNat 128 (data.toNat % 2 ^ (8 * sz)) != data) ∧
      ScalarRel ⟨data.toNat % 2 ^ (8 * sz), sz⟩ msc := by
  have ⟨hw128, hw0⟩ := freshAlloc_validScalarBytes_bits_le_128 hsz
  have hze := freshAlloc_zeroExtend_extractLsb_eq_ofNat (8 * sz) hw0 hw128 data
  have hmod : data.toNat % 2 ^ (8 * sz) < scalarModulus sz := by
    rw [freshAlloc_scalarModulus_eq_two_pow]
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

private theorem freshAlloc_tryFromUInt {sc : MirAst.ScalarInt}
    (hsz : ValidScalarBytes sc.sizeBytes) (hcan : sc.bits < scalarModulus sc.sizeBytes) :
    ∃ msc : Miri.Memory.ScalarInt,
      Miri.Memory.ScalarInt.tryFromUInt (BitVec.ofNat 128 sc.bits)
          (translateSizeBytes sc.sizeBytes) = .ok (some msc) ∧
      ScalarRel sc msc := by
  obtain ⟨msc, htr, hrel⟩ := freshAlloc_truncateFromUInt_spec hsz (BitVec.ofNat 128 sc.bits)
  have hlt : sc.bits < 2 ^ (8 * sc.sizeBytes) := by
    rw [← freshAlloc_scalarModulus_eq_two_pow]; exact hcan
  have hmod : (BitVec.ofNat 128 sc.bits).toNat % 2 ^ (8 * sc.sizeBytes) = sc.bits := by
    rw [freshAlloc_bitVec_ofNat_toNat hsz hcan, Nat.mod_eq_of_lt hlt]
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

/-- `Miri.Memory.ScalarInt` is determined by its public `data` and `size`. -/
private theorem freshAlloc_scalarInt_ext {a b : Miri.Memory.ScalarInt}
    (hd : a.data = b.data) (hs : a.size = b.size) : a = b := by
  cases a
  cases b
  simp only [Miri.Memory.ScalarInt.data, Miri.Memory.ScalarInt.size] at hd hs
  subst hd
  subst hs
  rfl

private theorem freshAlloc_fromUInt {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) :
    Miri.Memory.Scalar.fromUInt (Prov := AnnealProv) (BitVec.ofNat 128 sc.bits)
        (translateSizeBytes sc.sizeBytes) = .ok (Miri.Memory.Scalar.fromScalarInt msc) := by
  obtain ⟨msc', htry, hrel'⟩ := freshAlloc_tryFromUInt hrel.validBytes hrel.canonical
  have heq : msc' = msc :=
    freshAlloc_scalarInt_ext (hrel'.data_eq.trans hrel.data_eq.symm)
      (hrel'.size_eq.trans hrel.size_eq.symm)
  subst heq
  unfold Miri.Memory.Scalar.fromUInt
  simp [htry, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- The scalar conversion inside `writeScalar` for a related integer scalar. -/
private theorem freshAlloc_toBitsOrPtrInternal {sc : MirAst.ScalarInt}
    {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBitsOrPtrInternal
        (translateSizeBytes sc.sizeBytes) = .ok (.bits (BitVec.ofNat 128 sc.bits)) := by
  unfold Miri.Memory.Scalar.toBitsOrPtrInternal
  simp only [Miri.Memory.Scalar.fromScalarInt, hrel.toBits_eq, Except.mapError, bind,
    Except.bind, pure, Except.pure]

/-! ## 4. Allocation, write, and read-back -/

private theorem freshAlloc_allocRange_end (size : Miri.ABI.Size) :
    (Miri.Memory.allocRange Miri.ABI.Size.ZERO size).endExclusive = .ok size := by
  cases size
  simp [Miri.Memory.AllocRange.endExclusive, Miri.Memory.AllocRange.end, Miri.Memory.allocRange,
    Miri.ABI.Size.ZERO, Miri.ABI.Size.add, Miri.ABI.Size.ofBytes, Except.mapError]

private theorem freshAlloc_fromBytes_pow2 {b : UInt64} {a : Miri.ABI.Align}
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

private theorem freshAlloc_checkedAlign_ok {align v : Miri.ABI.Align}
    (h : freshAlloc_checkedAlign align = .ok v) :
    v = align ∧
      ∃ b, Miri.ABI.Align.bytes align = .ok b ∧ Miri.ABI.Align.fromBytes b = .ok align := by
  unfold freshAlloc_checkedAlign at h
  cases hb : Miri.ABI.Align.bytes align with
  | error e => simp [hb, bind, Except.bind, Except.mapError] at h
  | ok b =>
    cases hf : Miri.ABI.Align.fromBytes b with
    | error e => simp [hb, hf, bind, Except.bind, Except.mapError] at h
    | ok n =>
      simp only [hb, hf, bind, Except.bind, Except.mapError, pure, Except.pure] at h
      by_cases hn : n = align
      · subst hn
        simp at h
        exact ⟨h.symm, b, rfl, hf⟩
      · simp [hn, throw, throwThe, MonadExceptOf.throw] at h

/-- Public-accessor facts about a successful `tryNew` with Anneal's zeroed
storage. The private `checkedAlign` step is analyzed through
`freshAlloc_checkedAlign`; the rest comes from `lean-miri`'s
`tryNew_replicate_full` and `tryNew_uninit_shape`. -/
private theorem freshAlloc_tryNew_facts {size : Miri.ABI.Size} {align : Miri.ABI.Align}
    {allocation : Miri.Memory.Allocation AnnealProv Unit}
    (h : Miri.Memory.Allocation.tryNew size align .Uninit annealZeroedStorage = .ok allocation) :
    align.pow2 ≤ 29 ∧ allocation.byteSize = size ∧ allocation.len = size.bytes.toNat ∧
    allocation.mutability = .Mut ∧ allocation.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
    allocation.initializationMask = Miri.Memory.InitMask.new size false := by
  have h' : Miri.Memory.Allocation.tryNew size align .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok allocation := h
  obtain ⟨hprov, hmask⟩ := Miri.Memory.Allocation.tryNew_uninit_shape size align allocation h'
  have h1 := h
  unfold Miri.Memory.Allocation.tryNew at h1
  simp only [bind, Except.bind] at h1
  split at h1
  · cases h1
  · rename_i v hv
    obtain ⟨_, b, hb, hn⟩ := freshAlloc_checkedAlign_ok (v := v) hv
    obtain ⟨a0, h0, hsz, hlen, _, hmut, _⟩ :=
      Miri.Memory.Allocation.tryNew_replicate_full (P := AnnealProv) size align b hb hn
    rw [h'] at h0
    cases h0
    exact ⟨freshAlloc_fromBytes_pow2 hn, hsz, hlen, hmut, hprov, hmask⟩

/-- A full-range scalar write into storage shaped like a fresh uninitialized
allocation succeeds, initializes the whole mask, and stores the little-endian
bytes of `sc.bits`. -/
private theorem freshAlloc_write {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) {E : Type} {A : Miri.Memory.Allocation AnnealProv E}
    (hsz : A.byteSize = translateSizeBytes sc.sizeBytes)
    (hlen : A.len = (translateSizeBytes sc.sizeBytes).bytes.toNat)
    (hmut : A.mutability = .Mut)
    (hprov : A.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask : A.initializationMask =
      Miri.Memory.InitMask.new (translateSizeBytes sc.sizeBytes) false) :
    ∃ alloc' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO msc.size)
          (Miri.Memory.Scalar.fromScalarInt msc) A = .ok () alloc' ∧
      alloc'.byteSize = translateSizeBytes sc.sizeBytes ∧
      alloc'.mutability = .Mut ∧
      alloc'.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes sc.sizeBytes) true ∧
      freshAlloc_raw alloc' =
        freshAlloc_leBytes sc.bits (translateSizeBytes sc.sizeBytes).bytes.toNat := by
  have hrange :
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)).size =
        translateSizeBytes sc.sizeBytes := rfl
  have hconv := freshAlloc_toBitsOrPtrInternal hrel
  have hend := freshAlloc_allocRange_end (translateSizeBytes sc.sizeBytes)
  have hraw : (freshAlloc_raw A).size = (translateSizeBytes sc.sizeBytes).bytes.toNat := hlen
  -- Each private subterm of `writeScalar` is rewritten with a hypothesis
  -- obtained by unfolding a public accessor (`getBytesUnchecked`,
  -- `initializationMask`, ...).
  have hslice : Miri.Memory.Allocation.getBytesUnchecked A
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) =
      .ok ((freshAlloc_raw A).extract 0 (translateSizeBytes sc.sizeBytes).bytes.toNat) := by
    rw [freshAlloc_getBytesUnchecked_eq]
    unfold freshAlloc_checkedSlice
    simp only [hraw, hsz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hend,
      Except.mapError, bind, Except.bind]
    simp [Miri.Memory.allocRange, Miri.ABI.Size.ZERO, pure, Except.pure]
  unfold Miri.Memory.Allocation.getBytesUnchecked at hslice
  have hmask2 : A.initializationMask.setRange
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) true =
      .ok (Miri.Memory.InitMask.new (translateSizeBytes sc.sizeBytes) true) := by
    rw [hmask]
    exact Miri.Memory.InitMask.full_overwrite_stays_lazy _ _ false true _ hend rfl
      (UInt64.le_refl _)
  unfold Miri.Memory.Allocation.initializationMask at hmask2
  unfold Miri.Memory.Allocation.provenanceMap at hprov
  rw [hrel.size_eq]
  unfold Miri.Memory.Allocation.writeScalar
  simp only [hmut, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hrange, hconv, pure_bind]
  rw [hslice]
  simp only [hmask2]
  rw [hprov, Miri.Memory.ProvenanceMap.clear_new _ _ _ _ ?pos hend]
  case pos => decide
  have hn16 := freshAlloc_translateSizeBytes_le_16 hrel.validBytes
  simp only []
  -- The private `targetUIntBytes` call is split on and identified via its
  -- replica.
  split
  · rename_i data hdata
    have hdata' : freshAlloc_targetUIntBytes annealTargetDataLayout
        (translateSizeBytes sc.sizeBytes) (BitVec.ofNat 128 sc.bits) = .ok data := hdata
    rw [freshAlloc_targetUIntBytes_spec _ _ hn16] at hdata'
    cases hdata'
    have hstart : (Miri.Memory.allocRange Miri.ABI.Size.ZERO
        (translateSizeBytes sc.sizeBytes)).start.bytes.toNat = 0 := rfl
    have hlen' := hlen
    unfold Miri.Memory.Allocation.len at hlen'
    have hsz' := hsz
    unfold Miri.Memory.Allocation.byteSize at hsz'
    simp only [hstart, freshAlloc_leBytes_size, hlen', hsz', Array.size_append,
      Array.size_extract, Nat.min_self, Nat.zero_add, Nat.sub_self, Nat.add_zero, Nat.zero_min,
      bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    have htoNat : (BitVec.ofNat 128 sc.bits).toNat = sc.bits :=
      freshAlloc_bitVec_ofNat_toNat hrel.validBytes hrel.canonical
    refine ⟨_, rfl, rfl, rfl, rfl, ?_⟩
    simp [freshAlloc_raw, htoNat, hlen']
  · rename_i err herr
    have herr' : freshAlloc_targetUIntBytes annealTargetDataLayout
        (translateSizeBytes sc.sizeBytes) (BitVec.ofNat 128 sc.bits) = .error err := herr
    rw [freshAlloc_targetUIntBytes_spec _ _ hn16] at herr'
    cases herr'

/-- Reading back (without provenance) the full range of an initialized
allocation that holds the little-endian bytes of a related scalar returns that
scalar. -/
private theorem freshAlloc_read {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) {E : Type} {B : Miri.Memory.Allocation AnnealProv E}
    (hsz : B.byteSize = translateSizeBytes sc.sizeBytes)
    (hmask : B.initializationMask =
      Miri.Memory.InitMask.new (translateSizeBytes sc.sizeBytes) true)
    (hraw : freshAlloc_raw B =
      freshAlloc_leBytes sc.bits (translateSizeBytes sc.sizeBytes).bytes.toNat) :
    B.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) false =
      .ok (Miri.Memory.Scalar.fromScalarInt msc) := by
  have hend := freshAlloc_allocRange_end (translateSizeBytes sc.sizeBytes)
  have hrange :
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)).size =
        translateSizeBytes sc.sizeBytes := rfl
  have hn := freshAlloc_translateSizeBytes_toNat hrel.validBytes
  have hn16 := freshAlloc_translateSizeBytes_le_16 hrel.validBytes
  have hslice : freshAlloc_checkedSlice B
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) =
      .ok (freshAlloc_leBytes sc.bits (translateSizeBytes sc.sizeBytes).bytes.toNat) := by
    have hrawsize : (freshAlloc_raw B).size = (translateSizeBytes sc.sizeBytes).bytes.toNat := by
      rw [hraw, freshAlloc_leBytes_size]
    unfold freshAlloc_checkedSlice
    simp only [hrawsize, hsz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hend,
      Except.mapError, bind, Except.bind]
    simp [Miri.Memory.allocRange, Miri.ABI.Size.ZERO, pure, Except.pure, hraw,
      freshAlloc_leBytes_size]
  have hoff : Miri.Memory.PointerProvenance.offsetIsAddr AnnealProv = true := rfl
  have hmod : sc.bits % 2 ^ (8 * (translateSizeBytes sc.sizeBytes).bytes.toNat) = sc.bits := by
    rw [hn, ← freshAlloc_scalarModulus_eq_two_pow]
    exact Nat.mod_eq_of_lt hrel.canonical
  rw [freshAlloc_readScalar_eq]
  unfold freshAlloc_readScalar
  rw [hmask, Miri.Memory.InitMask.lazy_initialized_query _ _ _ hend (UInt64.le_refl _)]
  simp only [Except.mapError, bind, Except.bind]
  rw [freshAlloc_getBytesUnchecked_eq, hslice]
  simp only []
  rw [freshAlloc_readTargetUInt_leBytes _ _ hn16, hmod]
  simp only [Bool.false_eq_true, ↓reduceIte, hoff, hrange, freshAlloc_fromUInt hrel]

/-! ## 5. Fresh stack allocation theorems -/

/-- A successful `Allocation.tryNew size align .Uninit annealZeroedStorage` (the
storage step of Anneal's `allocateStack` hook) yields, once tagged with an empty
Tree Borrows extra, an allocation of exactly `size` bytes that is mutable, whose
alignment exponent is at most `29` (`Align.MAX`), and whose full range is not
reported as initialized when `size` is non-zero. -/
theorem freshStackAlloc_spec {size : Miri.ABI.Size} {align : Miri.ABI.Align}
    {allocation : Miri.Memory.Allocation AnnealProv Unit}
    (h : Miri.Memory.Allocation.tryNew size align .Uninit annealZeroedStorage = .ok allocation) :
    (allocation.withExtra (none : Option Miri.TreeBorrows.BorrowTree)).byteSize = size ∧
    (allocation.withExtra (none : Option Miri.TreeBorrows.BorrowTree)).mutability = .Mut ∧
    align.pow2 ≤ 29 ∧
    (size ≠ Miri.ABI.Size.ZERO →
      (allocation.withExtra
          (none : Option Miri.TreeBorrows.BorrowTree)).initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO size) ≠ .ok (.ok ())) := by
  obtain ⟨hpow, hsz, _, hmut, _, hmask⟩ := freshAlloc_tryNew_facts h
  refine ⟨hsz, hmut, hpow, fun _ => ?_⟩
  have hmask' :
      (allocation.withExtra (none : Option Miri.TreeBorrows.BorrowTree)).initializationMask =
        Miri.Memory.InitMask.new size false := hmask
  rw [hmask', Miri.Memory.InitMask.lazy_uninitialized_query size _ size
    (freshAlloc_allocRange_end size) (UInt64.le_refl _)]
  intro heq
  cases heq

/-- Writing a `ScalarRel`-related scalar immediate at offset `0` of a fresh
stack allocation (as `forceAllocation` does through `writeMemoryNoValidate`)
succeeds; the result keeps the allocation's size and mutability, has every byte
initialized, and reading the full range back without provenance returns the
written scalar. -/
theorem freshStackAlloc_writeScalar_readScalar {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) {align : Miri.ABI.Align}
    {allocation : Miri.Memory.Allocation AnnealProv Unit}
    (h : Miri.Memory.Allocation.tryNew (translateSizeBytes sc.sizeBytes) align .Uninit
      annealZeroedStorage = .ok allocation) :
    ∃ alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO msc.size)
          (Miri.Memory.Scalar.fromScalarInt msc) (allocation.withExtra none) = .ok () alloc' ∧
      alloc'.byteSize = translateSizeBytes sc.sizeBytes ∧
      alloc'.mutability = .Mut ∧
      alloc'.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) =
        .ok (.ok ()) ∧
      alloc'.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) false =
        .ok (Miri.Memory.Scalar.fromScalarInt msc) := by
  obtain ⟨_, hsz, hlen, hmut, hprov, hmask⟩ := freshAlloc_tryNew_facts h
  obtain ⟨alloc', hw, hsz', hmut', hmask', hraw'⟩ :=
    freshAlloc_write hrel (A := allocation.withExtra none) hsz hlen hmut hprov hmask
  refine ⟨alloc', hw, hsz', hmut', ?_, freshAlloc_read hrel hsz' hmask' hraw'⟩
  rw [hmask']
  exact Miri.Memory.InitMask.lazy_initialized_query _ _ _ (freshAlloc_allocRange_end _)
    (UInt64.le_refl _)

end LeanMiriSpec.Correspondence
