/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.MemoryLemmas
import LeanMiriSpec.ValidationRankCert

set_option autoImplicit false

/-!
# Regression tests: `LeanMiriSpec.MemoryLemmas` and `LeanMiriSpec.ValidationRankCert`

Kernel-checked positive and negative regression tests (no `sorry`, no `native_decide`):

1. **Signature pins + `BinderInfo` parity.** Every one of the 50 `MemoryLemmas` theorems is checked
   against its full statement, universe parameters, and exact per-binder `BinderInfo` (`()` vs `{}`
   vs `[]`), with `-Dlinter.unusedVariables=true` active throughout.
2. **`MemoryLemmas` witnesses.** Concrete instantiations on real `lean-miri` states:
   `.Lazy false` → `.Materialized` multi-word `InitMask` transitions and framing, `ProvenanceMap.new`
   equations, `fromBytes` / `tryNew` allocations with `withExtra` / `mapExtra`, `getBytesUnchecked`
   split / subrange, partial-range `writeBytes` / `writeUninit` / `copy` / `copyRepeatedly` with byte
   and mask framing, little- and big-endian integer and pointer `readScalar` round trips, exposed
   provenance, and uninitialized-byte errors.
3. **`ValidationRankCert` witnesses.** The 150-level nested wrapper, 150-level vendored
   `ValidityVisitor.unionRanges` (with direct `vendored_unionRanges_eq_noFuel` adequacy and
   `Anneal.MirFuelFree` bridge) and vendored `ValidityVisitor.visit` pattern walk; static
   `LayoutGraph` certificates (including unclosed missing-child cycle rejection); Schema 17
   `Decoder.lean` type-table validation (pointer-indirection recursion vs by-value cycle /
   missing-child / coroutine `savedTypes` rejections); `visitOrder` (`(if isSized then 0 else 1,
   layoutOrder)`) `dyn Trait` dynamic unpacking (where `VisitLexWalk` succeeds and naive
   `layoutOrder`-only `RankedWalk` falsely rejects); LIFO pointee draining; and module-wide
   standard-axiom verification (`#assert_test_standard_axioms`).
-/

/-! ## 1. Signature pins for all 50 `MemoryLemmas` theorems

Each pin restates a theorem's full statement (with its binder names, for readability) and checks
that the theorem has exactly that type. -/

section SignaturePins

namespace Miri.Memory.InitMask.WriteProof
open Miri.ABI Miri.Memory

/-- Pin: `get_ok_of_wellFormed`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_01_get_ok_of_wellFormed : ∀ (mask : InitMask) (idx : Size)
    (_valid : WellFormed mask) (_inBounds : idx.bytes.toNat < mask.len.bytes.toNat),
    ∃ b, mask.get idx = .ok b :=
  @Miri.Memory.InitMask.WriteProof.get_ok_of_wellFormed

/-- Pin: `set_range_get`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_02_set_range_get : ∀ (mask updated : InitMask) (range : AllocRange) (finish idx : Size)
    (state : Bool)
    (_valid : WellFormed mask) (_endpoint : range.endExclusive = .ok finish)
    (_nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (_inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat)
    (_idxInBounds : idx.bytes.toNat < mask.len.bytes.toNat)
    (_h_set : mask.setRange range state = .ok updated),
    updated.get idx =
      if range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat then
        .ok state
      else
        mask.get idx :=
  @Miri.Memory.InitMask.WriteProof.set_range_get

/-- Pin: `isRangeInitialized_nonempty_iff`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_03_isRangeInitialized_nonempty_iff : ∀ (mask : InitMask) (range : AllocRange) (finish : Size)
    (_valid : WellFormed mask) (_endpoint : range.endExclusive = .ok finish)
    (_nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (_inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat),
    (mask.isRangeInitialized range = .ok (.ok ()) ↔
      ∀ (idx : Size), range.start.bytes.toNat ≤ idx.bytes.toNat → idx.bytes.toNat < finish.bytes.toNat →
        mask.get idx = .ok true) ∧
    ((∃ idx : Size, range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat ∧
        mask.get idx = .ok false) →
      ∃ bad : AllocRange, mask.isRangeInitialized range = .ok (.error bad)) :=
  @Miri.Memory.InitMask.WriteProof.isRangeInitialized_nonempty_iff

/-- Pin: `isRangeInitialized_after_setRange_true`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_04_isRangeInitialized_after_setRange_true : ∀ (mask updated : InitMask)
    (range : AllocRange) (finish : Size)
    (_valid : WellFormed mask) (_endpoint : range.endExclusive = .ok finish)
    (_nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (_inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat)
    (_h_set : mask.setRange range true = .ok updated),
    updated.isRangeInitialized range = .ok (.ok ()) :=
  @Miri.Memory.InitMask.WriteProof.isRangeInitialized_after_setRange_true

/-- Pin: `isRangeInitialized_frame`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_05_isRangeInitialized_frame : ∀ (mask updated : InitMask)
    (writeRange queryRange : AllocRange) (writeFinish queryFinish : Size) (state : Bool)
    (_valid : WellFormed mask)
    (_wEnd : writeRange.endExclusive = .ok writeFinish)
    (_qEnd : queryRange.endExclusive = .ok queryFinish)
    (_wNonempty : writeRange.start.bytes.toNat < writeFinish.bytes.toNat)
    (_qNonempty : queryRange.start.bytes.toNat < queryFinish.bytes.toNat)
    (_wInBounds : writeFinish.bytes.toNat ≤ mask.len.bytes.toNat)
    (_qInBounds : queryFinish.bytes.toNat ≤ mask.len.bytes.toNat)
    (_disjoint : writeFinish.bytes.toNat ≤ queryRange.start.bytes.toNat ∨
      queryFinish.bytes.toNat ≤ writeRange.start.bytes.toNat)
    (_h_set : mask.setRange writeRange state = .ok updated),
    (updated.isRangeInitialized queryRange = .ok (.ok ()) ↔
      mask.isRangeInitialized queryRange = .ok (.ok ())) :=
  @Miri.Memory.InitMask.WriteProof.isRangeInitialized_frame

/-- Pin: `prepareCopy_of_uniform`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_06_prepareCopy_of_uniform : ∀ (mask : InitMask) (range : AllocRange) (finish : Size) (state : Bool)
    (_valid : WellFormed mask)
    (_endpoint : range.endExclusive = .ok finish)
    (_nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (_inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat)
    (_uniform : ∀ (idx : Size), range.start.bytes.toNat ≤ idx.bytes.toNat →
      idx.bytes.toNat < finish.bytes.toNat → mask.get idx = .ok state),
    mask.prepareCopy range = .ok ⟨state, #[range.size.bytes]⟩ :=
  @Miri.Memory.InitMask.WriteProof.prepareCopy_of_uniform

/-- Pin: `applyCopy_singleton`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_07_applyCopy_singleton : ∀ (destMask : InitMask) (destStart srcSize total : Size)
    (repeatCount : UInt64) (state : Bool)
    (_nonzero : srcSize.bytes ≠ 0)
    (_h_mul : Size.mul srcSize repeatCount = .ok total),
    destMask.applyCopy ⟨state, #[srcSize.bytes]⟩ (allocRange destStart srcSize) repeatCount =
      destMask.setRange (allocRange destStart total) state :=
  @Miri.Memory.InitMask.WriteProof.applyCopy_singleton

end Miri.Memory.InitMask.WriteProof

namespace Miri.Memory.ProvenanceMap
open Miri.ABI

/-- Pin: `rangeEmpty_new`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_08_rangeEmpty_new : ∀ {P : Type} (range : AllocRange) (pointerSize finish : Size)
    (_positive : pointerSize.bytes ≠ 0) (_endEq : range.endExclusive = .ok finish),
    (new (Prov := P)).rangeEmpty range pointerSize = .ok true :=
  @Miri.Memory.ProvenanceMap.rangeEmpty_new

/-- Pin: `readPtr_new`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_09_readPtr_new : ∀ {P : Type} [DecidableEq P] [PointerProvenance P]
    (offset pointerSize finish : Size)
    (_positive : pointerSize.bytes ≠ 0)
    (_endEq : (allocRange offset pointerSize).endExclusive = .ok finish),
    (new (Prov := P)).readPtr offset pointerSize = .ok none :=
  @Miri.Memory.ProvenanceMap.readPtr_new

/-- Pin: `prepareCopy_new`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_10_prepareCopy_new : ∀ {P : Type} (range : AllocRange) (data : Array UInt8) (pointerSize finish : Size)
    (_positive : pointerSize.bytes ≠ 0)
    (_endEq : range.endExclusive = .ok finish),
    (new (Prov := P)).prepareCopy range data pointerSize = .ok ⟨#[], #[]⟩ :=
  @Miri.Memory.ProvenanceMap.prepareCopy_new

/-- Pin: `applyCopy_empty`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_11_applyCopy_empty : ∀ {P : Type} (range : AllocRange) (repeatCount : UInt64) (pm : ProvenanceMap P),
    applyCopy ⟨#[], #[]⟩ range repeatCount pm = .ok () pm :=
  @Miri.Memory.ProvenanceMap.applyCopy_empty

end Miri.Memory.ProvenanceMap

namespace Miri.Memory.Allocation
open Miri.ABI

/-- Pin: `byteSize_withExtra`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_12_byteSize_withExtra : ∀ {P E : Type} (allocation : Allocation P Unit) (extra : E),
    (allocation.withExtra extra).byteSize = allocation.byteSize :=
  @Miri.Memory.Allocation.byteSize_withExtra

/-- Pin: `len_withExtra`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_13_len_withExtra : ∀ {P E : Type} (allocation : Allocation P Unit) (extra : E),
    (allocation.withExtra extra).len = allocation.len :=
  @Miri.Memory.Allocation.len_withExtra

/-- Pin: `align_withExtra`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_14_align_withExtra : ∀ {P E : Type} (allocation : Allocation P Unit) (extra : E),
    (allocation.withExtra extra).align = allocation.align :=
  @Miri.Memory.Allocation.align_withExtra

/-- Pin: `mutability_withExtra`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_15_mutability_withExtra : ∀ {P E : Type} (allocation : Allocation P Unit) (extra : E),
    (allocation.withExtra extra).mutability = allocation.mutability :=
  @Miri.Memory.Allocation.mutability_withExtra

/-- Pin: `provenanceMap_withExtra`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_16_provenanceMap_withExtra : ∀ {P E : Type} (allocation : Allocation P Unit) (extra : E),
    (allocation.withExtra extra).provenanceMap = allocation.provenanceMap :=
  @Miri.Memory.Allocation.provenanceMap_withExtra

/-- Pin: `initializationMask_withExtra`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_17_initializationMask_withExtra : ∀ {P E : Type} (allocation : Allocation P Unit) (extra : E),
    (allocation.withExtra extra).initializationMask = allocation.initializationMask :=
  @Miri.Memory.Allocation.initializationMask_withExtra

/-- Pin: `getBytesUnchecked_withExtra`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_18_getBytesUnchecked_withExtra : ∀ {P E : Type} (allocation : Allocation P Unit) (extra : E) (range : AllocRange),
    (allocation.withExtra extra).getBytesUnchecked range = allocation.getBytesUnchecked range :=
  @Miri.Memory.Allocation.getBytesUnchecked_withExtra

/-- Pin: `byteSize_mapExtra`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_19_byteSize_mapExtra : ∀ {P E E' : Type} (allocation : Allocation P E) (f : E → E'),
    (allocation.mapExtra f).byteSize = allocation.byteSize :=
  @Miri.Memory.Allocation.byteSize_mapExtra

/-- Pin: `len_mapExtra`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_20_len_mapExtra : ∀ {P E E' : Type} (allocation : Allocation P E) (f : E → E'),
    (allocation.mapExtra f).len = allocation.len :=
  @Miri.Memory.Allocation.len_mapExtra

/-- Pin: `align_mapExtra`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_21_align_mapExtra : ∀ {P E E' : Type} (allocation : Allocation P E) (f : E → E'),
    (allocation.mapExtra f).align = allocation.align :=
  @Miri.Memory.Allocation.align_mapExtra

/-- Pin: `mutability_mapExtra`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_22_mutability_mapExtra : ∀ {P E E' : Type} (allocation : Allocation P E) (f : E → E'),
    (allocation.mapExtra f).mutability = allocation.mutability :=
  @Miri.Memory.Allocation.mutability_mapExtra

/-- Pin: `provenanceMap_mapExtra`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_23_provenanceMap_mapExtra : ∀ {P E E' : Type} (allocation : Allocation P E) (f : E → E'),
    (allocation.mapExtra f).provenanceMap = allocation.provenanceMap :=
  @Miri.Memory.Allocation.provenanceMap_mapExtra

/-- Pin: `initializationMask_mapExtra`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_24_initializationMask_mapExtra : ∀ {P E E' : Type} (allocation : Allocation P E) (f : E → E'),
    (allocation.mapExtra f).initializationMask = allocation.initializationMask :=
  @Miri.Memory.Allocation.initializationMask_mapExtra

/-- Pin: `getBytesUnchecked_mapExtra`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_25_getBytesUnchecked_mapExtra : ∀ {P E E' : Type} (allocation : Allocation P E) (f : E → E') (range : AllocRange),
    (allocation.mapExtra f).getBytesUnchecked range = allocation.getBytesUnchecked range :=
  @Miri.Memory.Allocation.getBytesUnchecked_mapExtra

/-- Pin: `getBytesStripProvenance_mapExtra`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_26_getBytesStripProvenance_mapExtra : ∀ {P E E' : Type} [PointerProvenance P]
    (allocation : Allocation P E) (f : E → E') (layout : TargetDataLayout) (range : AllocRange),
    (allocation.mapExtra f).getBytesStripProvenance layout range =
      allocation.getBytesStripProvenance layout range :=
  @Miri.Memory.Allocation.getBytesStripProvenance_mapExtra

/-- Pin: `readScalar_mapExtra`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_27_readScalar_mapExtra : ∀ {P E E' : Type} [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (f : E → E') (layout : TargetDataLayout)
    (range : AllocRange) (readProvenance : Bool),
    (allocation.mapExtra f).readScalar layout range readProvenance =
      allocation.readScalar layout range readProvenance :=
  @Miri.Memory.Allocation.readScalar_mapExtra

/-- Pin: `writeBytes_mapExtra`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_28_writeBytes_mapExtra : ∀ {P E E' : Type} (start : Size) (bytes : Array UInt8) (ptrSize : Size)
    (allocation : Allocation P E) (f : E → E'),
    Allocation.writeBytes start bytes ptrSize (allocation.mapExtra f) =
      (match Allocation.writeBytes start bytes ptrSize allocation with
       | .ok value state => .ok value (state.mapExtra f)
       | .error error state => .error error (state.mapExtra f)) :=
  @Miri.Memory.Allocation.writeBytes_mapExtra

/-- Pin: `clearProvenance_mapExtra`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_29_clearProvenance_mapExtra : ∀ {P E E' : Type} (range : AllocRange) (ptrSize : Size)
    (allocation : Allocation P E) (f : E → E'),
    Allocation.clearProvenance range ptrSize (allocation.mapExtra f) =
      (match Allocation.clearProvenance range ptrSize allocation with
       | .ok value state => .ok value (state.mapExtra f)
       | .error error state => .error error (state.mapExtra f)) :=
  @Miri.Memory.Allocation.clearProvenance_mapExtra

/-- Pin: `fromBytes_spec`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_30_fromBytes_spec : ∀ {P : Type} (bytes : Array UInt8) (align : Align) (mutability : Mutability)
    (alloc : Allocation P Unit)
    (_created : Allocation.fromBytes bytes align mutability = .ok alloc),
    alloc.byteSize.bytes.toNat = bytes.size ∧
      alloc.len = bytes.size ∧
      alloc.mutability = mutability ∧
      alloc.extra = () ∧
      alloc.nativeBuffer = none ∧
      alloc.provenanceMap = ProvenanceMap.new ∧
      alloc.initializationMask = InitMask.new alloc.byteSize true ∧
      InitMask.WriteProof.WellFormed alloc.initializationMask ∧
      ∀ (range : AllocRange) (finish : Size),
        range.endExclusive = .ok finish →
        range.start.bytes.toNat ≤ finish.bytes.toNat →
        finish.bytes.toNat ≤ bytes.size →
        alloc.getBytesUnchecked range =
          .ok (bytes.extract range.start.bytes.toNat finish.bytes.toNat) :=
  @Miri.Memory.Allocation.fromBytes_spec

/-- Pin: `fromBytes_exists`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_31_fromBytes_exists : ∀ {P : Type} (bytes : Array UInt8) (align : Align) (alignmentBytes : UInt64)
    (mutability : Mutability)
    (_h_bytes : Align.bytes align = .ok alignmentBytes)
    (_h_norm : Align.fromBytes alignmentBytes = .ok align)
    (_h_fits : bytes.size < 2 ^ 64),
    ∃ alloc : Allocation P Unit,
      Allocation.fromBytes bytes align mutability = .ok alloc ∧
      alloc.byteSize = Size.ofBytes (UInt64.ofNat bytes.size) ∧
      alloc.align = align :=
  @Miri.Memory.Allocation.fromBytes_exists

/-- Pin: `tryNew_spec`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_32_tryNew_spec : ∀ {P : Type} (size : Size) (align : Align) (init : AllocInit)
    (alloc : Allocation P Unit)
    (_created : Allocation.tryNew size align init
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok alloc),
    alloc.byteSize = size ∧
      alloc.len = size.bytes.toNat ∧
      alloc.mutability = .Mut ∧
      alloc.extra = () ∧
      alloc.nativeBuffer = none ∧
      alloc.provenanceMap = ProvenanceMap.new ∧
      (init = .Uninit → alloc.initializationMask = InitMask.new size false) ∧
      (init = .Zero → alloc.initializationMask = InitMask.new size true) ∧
      InitMask.WriteProof.WellFormed alloc.initializationMask ∧
      ∀ (range : AllocRange) (finish : Size),
        range.endExclusive = .ok finish →
        range.start.bytes.toNat ≤ finish.bytes.toNat →
        finish.bytes.toNat ≤ size.bytes.toNat →
        alloc.getBytesUnchecked range =
          .ok (Array.replicate (finish.bytes.toNat - range.start.bytes.toNat) 0) :=
  @Miri.Memory.Allocation.tryNew_spec

/-- Pin: `tryNew_exists`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_33_tryNew_exists : ∀ {P : Type} (size : Size) (align : Align) (alignmentBytes : UInt64) (init : AllocInit)
    (_h_bytes : Align.bytes align = .ok alignmentBytes)
    (_h_norm : Align.fromBytes alignmentBytes = .ok align),
    ∃ alloc : Allocation P Unit,
      Allocation.tryNew size align init
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok alloc ∧
      alloc.align = align :=
  @Miri.Memory.Allocation.tryNew_exists

/-- Pin: `getBytesUnchecked_size`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_34_getBytesUnchecked_size : ∀ {P E : Type} (allocation : Allocation P E) (range : AllocRange) (finish : Size)
    (_storage : allocation.len = allocation.byteSize.bytes.toNat)
    (_endEq : range.endExclusive = .ok finish)
    (_startLe : range.start.bytes.toNat ≤ finish.bytes.toNat)
    (_inBounds : finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat),
    ∃ slice, allocation.getBytesUnchecked range = .ok slice ∧
      slice.size = finish.bytes.toNat - range.start.bytes.toNat :=
  @Miri.Memory.Allocation.getBytesUnchecked_size

/-- Pin: `getBytesUnchecked_subrange`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_35_getBytesUnchecked_subrange : ∀ {P E : Type} (allocation : Allocation P E)
    (rOuter rInner : AllocRange) (fOuter fInner : Size) (outerBytes : Array UInt8)
    (_h_outer_end : rOuter.endExclusive = .ok fOuter)
    (_h_inner_end : rInner.endExclusive = .ok fInner)
    (_h_lo : rOuter.start.bytes.toNat ≤ rInner.start.bytes.toNat)
    (_h_mid : rInner.start.bytes.toNat ≤ fInner.bytes.toNat)
    (_h_hi : fInner.bytes.toNat ≤ fOuter.bytes.toNat)
    (_h_outer : allocation.getBytesUnchecked rOuter = .ok outerBytes),
    allocation.getBytesUnchecked rInner =
      .ok (outerBytes.extract
        (rInner.start.bytes.toNat - rOuter.start.bytes.toNat)
        (fInner.bytes.toNat - rOuter.start.bytes.toNat)) :=
  @Miri.Memory.Allocation.getBytesUnchecked_subrange

/-- Pin: `getBytesUnchecked_split`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_36_getBytesUnchecked_split : ∀ {P E : Type} (allocation : Allocation P E)
    (r1 r2 r12 : AllocRange) (mid fin : Size) (b1 b2 : Array UInt8)
    (_h_end1 : r1.endExclusive = .ok mid)
    (_h_start2 : r2.start = mid)
    (_h_end2 : r2.endExclusive = .ok fin)
    (_h_start12 : r12.start = r1.start)
    (_h_end12 : r12.endExclusive = .ok fin)
    (_h_lo1 : r1.start.bytes.toNat ≤ mid.bytes.toNat)
    (_h_lo2 : mid.bytes.toNat ≤ fin.bytes.toNat)
    (_h_get1 : allocation.getBytesUnchecked r1 = .ok b1)
    (_h_get2 : allocation.getBytesUnchecked r2 = .ok b2),
    allocation.getBytesUnchecked r12 = .ok (b1 ++ b2) :=
  @Miri.Memory.Allocation.getBytesUnchecked_split

/-- Pin: `getBytesStripProvenance_uninit_err`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_37_getBytesStripProvenance_uninit_err : ∀ {P E : Type} [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range bad : AllocRange)
    (_h_uninit : allocation.initializationMask.isRangeInitialized range = .ok (.error bad)),
    allocation.getBytesStripProvenance layout range =
      .error (.invalidUninitBytes (some ⟨range, bad⟩)) :=
  @Miri.Memory.Allocation.getBytesStripProvenance_uninit_err

/-- Pin: `getBytesStripProvenance_ok`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_38_getBytesStripProvenance_ok : ∀ {P E : Type} [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout) (range : AllocRange)
    (_h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (_h_prov : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true),
    allocation.getBytesStripProvenance layout range = allocation.getBytesUnchecked range :=
  @Miri.Memory.Allocation.getBytesStripProvenance_ok

/-- Pin: `readScalar_uninit_err`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_39_readScalar_uninit_err : ∀ {P E : Type} [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range bad : AllocRange) (readProvenance : Bool)
    (_h_uninit : allocation.initializationMask.isRangeInitialized range = .ok (.error bad)),
    allocation.readScalar layout range readProvenance =
      .error (.invalidUninitBytes (some ⟨range, bad⟩)) :=
  @Miri.Memory.Allocation.readScalar_uninit_err

/-- Pin: `readScalar_int_of_bytes`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_40_readScalar_int_of_bytes : ∀ {P E : Type} [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (bytes : Array UInt8)
    (_h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (_h_slice : allocation.getBytesUnchecked range = .ok bytes)
    (_h_limit : bytes.size ≤ 16)
    (_h_prov : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true),
    allocation.readScalar layout range false =
      (Scalar.fromUInt (BitVec.ofNat 128 ((List.range bytes.size).foldl (fun acc idx =>
        acc + (bytes[idx]?.getD 0).toNat * 2 ^ (8 *
          (if layout.endian == .little then idx else bytes.size - idx - 1))) 0))
        range.size).mapError AllocError.scalar :=
  @Miri.Memory.Allocation.readScalar_int_of_bytes

/-- Pin: `readScalar_int_roundtrip`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_41_readScalar_int_roundtrip : ∀ {P E : Type} [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (bits : U128)
    (_h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (_h_limit : range.size.bytes.toNat ≤ 16)
    (_h_bits_bound : bits.toNat < 2 ^ (8 * range.size.bytes.toNat))
    (_h_prov : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true)
    (_h_slice : allocation.getBytesUnchecked range =
      .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
        UInt8.ofNat ((bits.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))),
    allocation.readScalar layout range false =
      (Scalar.fromUInt bits range.size).mapError AllocError.scalar :=
  @Miri.Memory.Allocation.readScalar_int_roundtrip

/-- Pin: `readScalar_ptr_roundtrip`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_42_readScalar_ptr_roundtrip : ∀ {P E : Type} [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (ptr : Pointer P)
    (_h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (_h_ptr_sz : range.size = Size.fromBits layout.pointerWidth.bits)
    (_h_limit : range.size.bytes.toNat ≤ 16)
    (_h_off_bound : ptr.offset.bytes.toNat < 2 ^ (8 * range.size.bytes.toNat))
    (_h_prov : allocation.provenanceMap.readPtr range.start
      (Size.fromBits layout.pointerWidth.bits) = .ok (some ptr.provenance))
    (_h_slice : allocation.getBytesUnchecked range =
      .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
        UInt8.ofNat ((ptr.offset.bytes.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))),
    allocation.readScalar layout range true = .ok (Scalar.fromPointer layout ptr) :=
  @Miri.Memory.Allocation.readScalar_ptr_roundtrip

/-- Pin: `readScalar_ptr_none_roundtrip`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_43_readScalar_ptr_none_roundtrip : ∀ {P E : Type} [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (bits : U128)
    (_h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (_h_ptr_sz : range.size = Size.fromBits layout.pointerWidth.bits)
    (_h_limit : range.size.bytes.toNat ≤ 16)
    (_h_bits_bound : bits.toNat < 2 ^ (8 * range.size.bytes.toNat))
    (_h_prov : allocation.provenanceMap.readPtr range.start
      (Size.fromBits layout.pointerWidth.bits) = .ok none)
    (_h_slice : allocation.getBytesUnchecked range =
      .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
        UInt8.ofNat ((bits.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))),
    allocation.readScalar layout range true =
      (Scalar.fromUInt bits range.size).mapError AllocError.scalar :=
  @Miri.Memory.Allocation.readScalar_ptr_none_roundtrip

/-- Pin: `writeScalar_spec`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_44_writeScalar_spec : ∀ {P E : Type} (layout : TargetDataLayout)
    (allocation : Allocation P E) (range : AllocRange) (value : Scalar P)
    (converted : ScalarBitsOrPointer P) (cleared nextProvenance : ProvenanceMap P)
    (_storage : allocation.len = allocation.byteSize.bytes.toNat)
    (_mutable : allocation.mutability = .Mut)
    (_maskLength : allocation.initializationMask.len = allocation.byteSize)
    (_maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (_nonzero : range.size.bytes ≠ 0)
    (_width : range.size.bytes.toNat ≤ 16)
    (_bound : range.start.bytes.toNat + range.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (_conversion : value.toBitsOrPtrInternal range.size = .ok converted)
    (_clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear range fullBytes
        (Size.fromBits layout.pointerWidth.bits) = .ok () cleared)
    (_insert : match converted with
      | .bits _ => nextProvenance = cleared
      | .pointer pointer => range.size = Size.fromBits layout.pointerWidth.bits ∧
          cleared.insertPtr range.start pointer.provenance
            (Size.fromBits layout.pointerWidth.bits) = .ok () nextProvenance),
    ∃ updated,
      Allocation.writeScalar layout range value allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧
      updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧
      updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      allocation.initializationMask.setRange range true = .ok updated.initializationMask ∧
      updated.initializationMask.isRangeInitialized range = .ok (.ok ()) ∧
      updated.provenanceMap = nextProvenance ∧
      (∀ b, converted = .bits b →
        updated.getBytesUnchecked range =
          .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
            UInt8.ofNat ((b.toNat /
              2 ^ (8 * (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))) ∧
      (∀ p, converted = .pointer p →
        updated.getBytesUnchecked range =
          .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
            UInt8.ofNat (((BitVec.ofNat 128 p.offset.bytes.toNat).toNat /
              2 ^ (8 * (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))) ∧
      ∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat ≤ qFin.bytes.toNat →
        qFin.bytes.toNat ≤ allocation.byteSize.bytes.toNat →
        (range.start.bytes.toNat + range.size.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ range.start.bytes.toNat) →
        updated.getBytesUnchecked qRange = allocation.getBytesUnchecked qRange :=
  @Miri.Memory.Allocation.writeScalar_spec

/-- Pin: `writeBytes_zero_spec`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_45_writeBytes_zero_spec : ∀ {P E : Type} (start ptrSize : Size) (bytes : Array UInt8)
    (allocation : Allocation P E)
    (_h_empty : bytes.size = 0)
    (_storage : allocation.len = allocation.byteSize.bytes.toNat)
    (_inBounds : start.bytes.toNat ≤ allocation.byteSize.bytes.toNat),
    Allocation.writeBytes start bytes ptrSize allocation = .ok () allocation :=
  @Miri.Memory.Allocation.writeBytes_zero_spec

/-- Pin: `writeBytes_spec`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_46_writeBytes_spec : ∀ {P E : Type} (start ptrSize : Size) (bytes : Array UInt8)
    (allocation : Allocation P E) (nextProvenance : ProvenanceMap P)
    (_h_nonempty : 0 < bytes.size)
    (_storage : allocation.len = allocation.byteSize.bytes.toNat)
    (_mutable : allocation.mutability = .Mut)
    (_maskLength : allocation.initializationMask.len = allocation.byteSize)
    (_maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (_inBounds : start.bytes.toNat + bytes.size ≤ allocation.byteSize.bytes.toNat)
    (_clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear
        (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) fullBytes ptrSize =
        .ok () nextProvenance),
    ∃ updated,
      Allocation.writeBytes start bytes ptrSize allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧
      updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧
      updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      allocation.initializationMask.setRange
        (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) true =
        .ok updated.initializationMask ∧
      updated.initializationMask.isRangeInitialized
        (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) = .ok (.ok ()) ∧
      updated.provenanceMap = nextProvenance ∧
      updated.getBytesUnchecked (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) =
        .ok bytes ∧
      ∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat ≤ qFin.bytes.toNat →
        qFin.bytes.toNat ≤ allocation.byteSize.bytes.toNat →
        (start.bytes.toNat + bytes.size ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ start.bytes.toNat) →
        updated.getBytesUnchecked qRange = allocation.getBytesUnchecked qRange :=
  @Miri.Memory.Allocation.writeBytes_spec

/-- Pin: `writeUninit_zero_spec`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_47_writeUninit_zero_spec : ∀ {P E : Type} (range : AllocRange) (finish ptrSize : Size)
    (allocation : Allocation P E)
    (_h_zero : range.size.bytes = 0)
    (_storage : allocation.len = allocation.byteSize.bytes.toNat)
    (_endEq : range.endExclusive = .ok finish)
    (_startLe : range.start.bytes.toNat ≤ finish.bytes.toNat)
    (_inBounds : finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat),
    Allocation.writeUninit range ptrSize allocation = .ok () allocation :=
  @Miri.Memory.Allocation.writeUninit_zero_spec

/-- Pin: `writeUninit_spec`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_48_writeUninit_spec : ∀ {P E : Type} (range : AllocRange) (ptrSize : Size)
    (allocation : Allocation P E) (nextProvenance : ProvenanceMap P)
    (_nonzero : range.size.bytes ≠ 0)
    (_storage : allocation.len = allocation.byteSize.bytes.toNat)
    (_mutable : allocation.mutability = .Mut)
    (_maskLength : allocation.initializationMask.len = allocation.byteSize)
    (_maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (_inBounds : range.start.bytes.toNat + range.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (_clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear range fullBytes ptrSize = .ok () nextProvenance),
    ∃ updated,
      Allocation.writeUninit range ptrSize allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧
      updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧
      updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      allocation.initializationMask.setRange range false = .ok updated.initializationMask ∧
      updated.provenanceMap = nextProvenance ∧
      ∀ (anyRange : AllocRange),
        updated.getBytesUnchecked anyRange = allocation.getBytesUnchecked anyRange :=
  @Miri.Memory.Allocation.writeUninit_spec

/-- Pin: `copyRepeatedly_initialized_spec`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_49_copyRepeatedly_initialized_spec : ∀ {P E : Type} (source state : Allocation P E)
    (sourceRange : AllocRange) (srcFinish destStart totalSize ptrSize : Size)
    (repeatCount : UInt64) (sameAllocation nonoverlapping : Bool)
    (srcBytes : Array UInt8) (provCopy : ProvenanceCopy P)
    (clearedProv finalProv : ProvenanceMap P)
    (_srcStorage : source.len = source.byteSize.bytes.toNat)
    (_srcEnd : sourceRange.endExclusive = .ok srcFinish)
    (_srcNonzero : sourceRange.size.bytes ≠ 0)
    (_srcMaskLen : source.initializationMask.len = source.byteSize)
    (_srcMaskWF : InitMask.WriteProof.WellFormed source.initializationMask)
    (_srcInit : source.initializationMask.isRangeInitialized sourceRange = .ok (.ok ()))
    (_srcSlice : source.getBytesUnchecked sourceRange = .ok srcBytes)
    (_srcInBounds : srcFinish.bytes.toNat ≤ source.byteSize.bytes.toNat)
    (_h_prepProv : ∀ srcFull : Array UInt8,
      source.getBytesUnchecked (allocRange Size.ZERO source.byteSize) = .ok srcFull →
      source.provenanceMap.prepareCopy sourceRange srcFull ptrSize = .ok provCopy)
    (_h_repPos : 0 < repeatCount.toNat)
    (_h_mul : Size.mul sourceRange.size repeatCount = .ok totalSize)
    (_h_repMode : repeatCount > 1 → nonoverlapping = true)
    (_h_disjSame : sameAllocation = true → nonoverlapping = true →
      srcFinish.bytes.toNat ≤ destStart.bytes.toNat ∨
        destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ sourceRange.start.bytes.toNat)
    (_destStorage : state.len = state.byteSize.bytes.toNat)
    (_destMut : state.mutability = .Mut)
    (_destMaskLen : state.initializationMask.len = state.byteSize)
    (_destMaskWF : InitMask.WriteProof.WellFormed state.initializationMask)
    (_destInBounds : destStart.bytes.toNat + totalSize.bytes.toNat ≤ state.byteSize.bytes.toNat)
    (_h_clearProv : ∀ stFull : Array UInt8,
      state.getBytesUnchecked (allocRange Size.ZERO state.byteSize) = .ok stFull →
      state.provenanceMap.clear (allocRange destStart totalSize) stFull ptrSize =
        .ok () clearedProv)
    (_h_applyProv : clearedProv.applyCopy provCopy
      (allocRange destStart sourceRange.size) repeatCount = .ok () finalProv),
    ∃ updated,
      Allocation.copyRepeatedly source sourceRange destStart repeatCount
        ptrSize sameAllocation nonoverlapping state = .ok () updated ∧
      updated.byteSize = state.byteSize ∧
      updated.len = state.len ∧
      updated.mutability = state.mutability ∧
      updated.align = state.align ∧
      updated.extra = state.extra ∧
      updated.nativeBuffer = state.nativeBuffer ∧
      updated.initializationMask.len = state.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      updated.initializationMask.isRangeInitialized (allocRange destStart totalSize) = .ok (.ok ()) ∧
      (∀ (idx : Size), idx.bytes.toNat < state.byteSize.bytes.toNat →
        updated.initializationMask.get idx =
          if destStart.bytes.toNat ≤ idx.bytes.toNat ∧
              idx.bytes.toNat < destStart.bytes.toNat + totalSize.bytes.toNat then
            .ok true
          else
            state.initializationMask.get idx) ∧
      (∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat < qFin.bytes.toNat →
        qFin.bytes.toNat ≤ state.byteSize.bytes.toNat →
        (destStart.bytes.toNat + totalSize.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ destStart.bytes.toNat) →
        (updated.initializationMask.isRangeInitialized qRange = .ok (.ok ()) ↔
          state.initializationMask.isRangeInitialized qRange = .ok (.ok ()))) ∧
      updated.provenanceMap = finalProv ∧
      updated.getBytesUnchecked (allocRange destStart totalSize) =
        .ok ((List.replicate repeatCount.toNat srcBytes.toList).flatten.toArray) ∧
      ∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat ≤ qFin.bytes.toNat →
        qFin.bytes.toNat ≤ state.byteSize.bytes.toNat →
        (destStart.bytes.toNat + totalSize.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ destStart.bytes.toNat) →
        updated.getBytesUnchecked qRange = state.getBytesUnchecked qRange :=
  @Miri.Memory.Allocation.copyRepeatedly_initialized_spec

/-- Pin: `copy_initialized_spec`. -/
theorem _root_.LeanMiriMemoryLemmasTests.SignaturePins.pin_50_copy_initialized_spec : ∀ {P E : Type} (source state : Allocation P E)
    (sourceRange : AllocRange) (srcFinish destStart ptrSize : Size)
    (sameAllocation nonoverlapping : Bool)
    (srcBytes : Array UInt8) (provCopy : ProvenanceCopy P)
    (clearedProv finalProv : ProvenanceMap P)
    (_srcStorage : source.len = source.byteSize.bytes.toNat)
    (_srcEnd : sourceRange.endExclusive = .ok srcFinish)
    (_srcNonzero : sourceRange.size.bytes ≠ 0)
    (_srcMaskLen : source.initializationMask.len = source.byteSize)
    (_srcMaskWF : InitMask.WriteProof.WellFormed source.initializationMask)
    (_srcInit : source.initializationMask.isRangeInitialized sourceRange = .ok (.ok ()))
    (_srcSlice : source.getBytesUnchecked sourceRange = .ok srcBytes)
    (_srcInBounds : srcFinish.bytes.toNat ≤ source.byteSize.bytes.toNat)
    (_h_prepProv : ∀ srcFull : Array UInt8,
      source.getBytesUnchecked (allocRange Size.ZERO source.byteSize) = .ok srcFull →
      source.provenanceMap.prepareCopy sourceRange srcFull ptrSize = .ok provCopy)
    (_h_disjSame : sameAllocation = true → nonoverlapping = true →
      srcFinish.bytes.toNat ≤ destStart.bytes.toNat ∨
        destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ sourceRange.start.bytes.toNat)
    (_destStorage : state.len = state.byteSize.bytes.toNat)
    (_destMut : state.mutability = .Mut)
    (_destMaskLen : state.initializationMask.len = state.byteSize)
    (_destMaskWF : InitMask.WriteProof.WellFormed state.initializationMask)
    (_destInBounds : destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ state.byteSize.bytes.toNat)
    (_h_clearProv : ∀ stFull : Array UInt8,
      state.getBytesUnchecked (allocRange Size.ZERO state.byteSize) = .ok stFull →
      state.provenanceMap.clear (allocRange destStart sourceRange.size) stFull ptrSize =
        .ok () clearedProv)
    (_h_applyProv : clearedProv.applyCopy provCopy
      (allocRange destStart sourceRange.size) 1 = .ok () finalProv),
    ∃ updated,
      Allocation.copy source sourceRange destStart ptrSize
        sameAllocation nonoverlapping state = .ok () updated ∧
      updated.byteSize = state.byteSize ∧
      updated.len = state.len ∧
      updated.mutability = state.mutability ∧
      updated.align = state.align ∧
      updated.extra = state.extra ∧
      updated.nativeBuffer = state.nativeBuffer ∧
      updated.initializationMask.len = state.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      updated.initializationMask.isRangeInitialized (allocRange destStart sourceRange.size) = .ok (.ok ()) ∧
      (∀ (idx : Size), idx.bytes.toNat < state.byteSize.bytes.toNat →
        updated.initializationMask.get idx =
          if destStart.bytes.toNat ≤ idx.bytes.toNat ∧
              idx.bytes.toNat < destStart.bytes.toNat + sourceRange.size.bytes.toNat then
            .ok true
          else
            state.initializationMask.get idx) ∧
      (∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat < qFin.bytes.toNat →
        qFin.bytes.toNat ≤ state.byteSize.bytes.toNat →
        (destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ destStart.bytes.toNat) →
        (updated.initializationMask.isRangeInitialized qRange = .ok (.ok ()) ↔
          state.initializationMask.isRangeInitialized qRange = .ok (.ok ()))) ∧
      updated.provenanceMap = finalProv ∧
      updated.getBytesUnchecked (allocRange destStart sourceRange.size) = .ok srcBytes ∧
      ∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat ≤ qFin.bytes.toNat →
        qFin.bytes.toNat ≤ state.byteSize.bytes.toNat →
        (destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ destStart.bytes.toNat) →
        updated.getBytesUnchecked qRange = state.getBytesUnchecked qRange :=
  @Miri.Memory.Allocation.copy_initialized_spec

end Miri.Memory.Allocation

end SignaturePins

section BinderParityAudit
open Lean Elab Command

/-- Verify that all 50 `SignaturePins` theorems match their `LeanMiriSpec.MemoryLemmas` counterparts
not only up to definitional type equality, but also in `levelParams` and exact `Expr.forallE`
`BinderInfo` (`default` vs `implicit` vs `strictImplicit` vs `instImplicit`) at every binder
position, closing the `@`-application binder-erasure blind spot. -/
elab "#assert_binder_parity" : command => do
  let env ← getEnv
  let pairs : List (Name × Name) := [
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_01_get_ok_of_wellFormed, `Miri.Memory.InitMask.WriteProof.get_ok_of_wellFormed),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_02_set_range_get, `Miri.Memory.InitMask.WriteProof.set_range_get),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_03_isRangeInitialized_nonempty_iff, `Miri.Memory.InitMask.WriteProof.isRangeInitialized_nonempty_iff),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_04_isRangeInitialized_after_setRange_true, `Miri.Memory.InitMask.WriteProof.isRangeInitialized_after_setRange_true),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_05_isRangeInitialized_frame, `Miri.Memory.InitMask.WriteProof.isRangeInitialized_frame),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_06_prepareCopy_of_uniform, `Miri.Memory.InitMask.WriteProof.prepareCopy_of_uniform),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_07_applyCopy_singleton, `Miri.Memory.InitMask.WriteProof.applyCopy_singleton),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_08_rangeEmpty_new, `Miri.Memory.ProvenanceMap.rangeEmpty_new),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_09_readPtr_new, `Miri.Memory.ProvenanceMap.readPtr_new),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_10_prepareCopy_new, `Miri.Memory.ProvenanceMap.prepareCopy_new),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_11_applyCopy_empty, `Miri.Memory.ProvenanceMap.applyCopy_empty),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_12_byteSize_withExtra, `Miri.Memory.Allocation.byteSize_withExtra),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_13_len_withExtra, `Miri.Memory.Allocation.len_withExtra),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_14_align_withExtra, `Miri.Memory.Allocation.align_withExtra),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_15_mutability_withExtra, `Miri.Memory.Allocation.mutability_withExtra),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_16_provenanceMap_withExtra, `Miri.Memory.Allocation.provenanceMap_withExtra),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_17_initializationMask_withExtra, `Miri.Memory.Allocation.initializationMask_withExtra),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_18_getBytesUnchecked_withExtra, `Miri.Memory.Allocation.getBytesUnchecked_withExtra),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_19_byteSize_mapExtra, `Miri.Memory.Allocation.byteSize_mapExtra),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_20_len_mapExtra, `Miri.Memory.Allocation.len_mapExtra),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_21_align_mapExtra, `Miri.Memory.Allocation.align_mapExtra),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_22_mutability_mapExtra, `Miri.Memory.Allocation.mutability_mapExtra),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_23_provenanceMap_mapExtra, `Miri.Memory.Allocation.provenanceMap_mapExtra),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_24_initializationMask_mapExtra, `Miri.Memory.Allocation.initializationMask_mapExtra),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_25_getBytesUnchecked_mapExtra, `Miri.Memory.Allocation.getBytesUnchecked_mapExtra),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_26_getBytesStripProvenance_mapExtra, `Miri.Memory.Allocation.getBytesStripProvenance_mapExtra),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_27_readScalar_mapExtra, `Miri.Memory.Allocation.readScalar_mapExtra),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_28_writeBytes_mapExtra, `Miri.Memory.Allocation.writeBytes_mapExtra),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_29_clearProvenance_mapExtra, `Miri.Memory.Allocation.clearProvenance_mapExtra),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_30_fromBytes_spec, `Miri.Memory.Allocation.fromBytes_spec),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_31_fromBytes_exists, `Miri.Memory.Allocation.fromBytes_exists),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_32_tryNew_spec, `Miri.Memory.Allocation.tryNew_spec),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_33_tryNew_exists, `Miri.Memory.Allocation.tryNew_exists),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_34_getBytesUnchecked_size, `Miri.Memory.Allocation.getBytesUnchecked_size),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_35_getBytesUnchecked_subrange, `Miri.Memory.Allocation.getBytesUnchecked_subrange),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_36_getBytesUnchecked_split, `Miri.Memory.Allocation.getBytesUnchecked_split),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_37_getBytesStripProvenance_uninit_err, `Miri.Memory.Allocation.getBytesStripProvenance_uninit_err),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_38_getBytesStripProvenance_ok, `Miri.Memory.Allocation.getBytesStripProvenance_ok),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_39_readScalar_uninit_err, `Miri.Memory.Allocation.readScalar_uninit_err),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_40_readScalar_int_of_bytes, `Miri.Memory.Allocation.readScalar_int_of_bytes),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_41_readScalar_int_roundtrip, `Miri.Memory.Allocation.readScalar_int_roundtrip),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_42_readScalar_ptr_roundtrip, `Miri.Memory.Allocation.readScalar_ptr_roundtrip),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_43_readScalar_ptr_none_roundtrip, `Miri.Memory.Allocation.readScalar_ptr_none_roundtrip),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_44_writeScalar_spec, `Miri.Memory.Allocation.writeScalar_spec),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_45_writeBytes_zero_spec, `Miri.Memory.Allocation.writeBytes_zero_spec),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_46_writeBytes_spec, `Miri.Memory.Allocation.writeBytes_spec),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_47_writeUninit_zero_spec, `Miri.Memory.Allocation.writeUninit_zero_spec),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_48_writeUninit_spec, `Miri.Memory.Allocation.writeUninit_spec),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_49_copyRepeatedly_initialized_spec, `Miri.Memory.Allocation.copyRepeatedly_initialized_spec),
    (`LeanMiriMemoryLemmasTests.SignaturePins.pin_50_copy_initialized_spec, `Miri.Memory.Allocation.copy_initialized_spec),
  ]
  let rec checkBinders (k : Nat) (e1 e2 : Expr) : Option String :=
    match e1, e2 with
    | .forallE n1 _ b1 bi1, .forallE n2 _ b2 bi2 =>
      if bi1 != bi2 then
        some s!"binder #{k} ({n1} vs {n2}): pin has {repr bi1}, theorem has {repr bi2}"
      else
        checkBinders (k + 1) b1 b2
    | .forallE n1 _ _ _, _ =>
      some s!"binder #{k}: pin has extra forall binder {n1}"
    | _, .forallE n2 _ _ _ =>
      some s!"binder #{k}: theorem has extra forall binder {n2}"
    | _, _ => none
  if pairs.length != 50 then
    logError m!"Expected 50 signature-pin pairs, got {pairs.length}"
  for (pinName, thmName) in pairs do
    let some pinInfo := env.find? pinName
      | logError m!"Missing signature pin {pinName}"; continue
    let some thmInfo := env.find? thmName
      | logError m!"Missing MemoryLemmas theorem {thmName}"; continue
    if pinInfo.levelParams != thmInfo.levelParams then
      logError m!"Universe parameter mismatch on {thmName}: {pinInfo.levelParams} vs {thmInfo.levelParams}"
    if let some msg := checkBinders 0 pinInfo.type thmInfo.type then
      logError m!"BinderInfo mismatch on {thmName}: {msg}"

#assert_binder_parity
end BinderParityAudit

/-! ## 2. `MemoryLemmas` witnesses on concrete states -/

namespace LeanMiriMemoryLemmasTests.MemoryWitnesses
open Miri.ABI Miri.Memory

/-- 1. All 7 `InitMask.WriteProof` theorems across two 64-bit word boundaries (`64` and `128`),
starting from a `.Lazy false` mask. -/
theorem wit_initMask_full_chain :
    ∃ (u uCopy : InitMask) (b0 : Bool) (bad : AllocRange),
      (InitMask.new (Size.ofBytes 200) false).get Size.ZERO = .ok b0 ∧
      (InitMask.new (Size.ofBytes 200) false).setRange
        (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) true = .ok u ∧
      u.get (Size.ofBytes 59) = .ok false ∧ u.get (Size.ofBytes 60) = .ok true ∧
      u.get (Size.ofBytes 63) = .ok true ∧ u.get (Size.ofBytes 64) = .ok true ∧
      u.get (Size.ofBytes 127) = .ok true ∧ u.get (Size.ofBytes 128) = .ok true ∧
      u.get (Size.ofBytes 139) = .ok true ∧ u.get (Size.ofBytes 140) = .ok false ∧
      u.isRangeInitialized (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) = .ok (.ok ()) ∧
      (u.isRangeInitialized (allocRange Size.ZERO (Size.ofBytes 60)) = .ok (.ok ()) ↔
        (InitMask.new (Size.ofBytes 200) false).isRangeInitialized
          (allocRange Size.ZERO (Size.ofBytes 60)) = .ok (.ok ())) ∧
      u.isRangeInitialized (allocRange Size.ZERO (Size.ofBytes 60)) = .ok (.error bad) ∧
      u.prepareCopy (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) = .ok ⟨true, #[80]⟩ ∧
      u.applyCopy ⟨true, #[80]⟩ (allocRange Size.ZERO (Size.ofBytes 80)) 2 = .ok uCopy := by
  let m0 := InitMask.new (Size.ofBytes 200) false
  have hwf0 : InitMask.WriteProof.WellFormed m0 := trivial
  obtain ⟨b0, hb0⟩ := InitMask.WriteProof.get_ok_of_wellFormed m0 Size.ZERO hwf0 (by decide)
  have hend : (allocRange (Size.ofBytes 60) (Size.ofBytes 80)).endExclusive =
      .ok (Size.ofBytes 140) := by decide
  obtain ⟨u, hu, hlen, hwfu⟩ := InitMask.WriteProof.set_range_exists m0
    (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (Size.ofBytes 140) true hwf0 hend
    (by decide) (by decide)
  have hget : ∀ idx : Size, idx.bytes.toNat < 200 → u.get idx =
      if 60 ≤ idx.bytes.toNat ∧ idx.bytes.toNat < 140 then .ok true else .ok false :=
    fun idx hidx => InitMask.WriteProof.set_range_get m0 u
      (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (Size.ofBytes 140) idx true hwf0 hend
      (by decide) (by decide) hidx hu
  have his := InitMask.WriteProof.isRangeInitialized_after_setRange_true m0 u
    (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (Size.ofBytes 140) hwf0 hend
    (by decide) (by decide) hu
  have hfr := InitMask.WriteProof.isRangeInitialized_frame m0 u
    (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (allocRange Size.ZERO (Size.ofBytes 60))
    (Size.ofBytes 140) (Size.ofBytes 60) true hwf0 hend (by decide)
    (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide)) hu
  have hiff_true := (InitMask.WriteProof.isRangeInitialized_nonempty_iff u
    (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (Size.ofBytes 140) hwfu hend
    (by decide) (by rw [hlen]; decide)).1.mp his
  have h59 : u.get (Size.ofBytes 59) = .ok false := by rw [hget _ (by decide)]; decide
  obtain ⟨bad, hbad⟩ := (InitMask.WriteProof.isRangeInitialized_nonempty_iff u
    (allocRange Size.ZERO (Size.ofBytes 60)) (Size.ofBytes 60) hwfu (by decide)
    (by decide) (by rw [hlen]; decide)).2 ⟨Size.ofBytes 59, by decide, by decide, h59⟩
  have hpc := InitMask.WriteProof.prepareCopy_of_uniform u
    (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (Size.ofBytes 140) true hwfu hend
    (by decide) (by rw [hlen]; decide) hiff_true
  have hap := InitMask.WriteProof.applyCopy_singleton u Size.ZERO (Size.ofBytes 80)
    (Size.ofBytes 160) 2 true (by decide) (by decide)
  obtain ⟨uCopy, huCopy, -, -⟩ := InitMask.WriteProof.set_range_exists u
    (allocRange Size.ZERO (Size.ofBytes 160)) (Size.ofBytes 160) true hwfu (by decide)
    (by decide) (by rw [hlen]; decide)
  refine ⟨u, uCopy, b0, bad, hb0, hu, h59, ?_, ?_, ?_, ?_, ?_, ?_, ?_, his, hfr, hbad, hpc,
    hap.trans huCopy⟩ <;> rw [hget _ (by decide)] <;> decide

/-- 2. `fromBytes_exists` / `fromBytes_spec`, `writeBytes_spec`, `writeBytes_zero_spec`,
`getBytesUnchecked_{size,subrange,split}`, and all 18 `withExtra`/`mapExtra` lemmas. -/
theorem wit_fromBytes_writeBytes_slices_and_mapExtra :
    ∃ (alloc updated : Allocation CtfeProvenance Unit) (slice26 : Array UInt8),
      Allocation.fromBytes (Array.replicate 8 (0 : UInt8)) Align.ONE .Mut = .ok alloc ∧
      Allocation.writeBytes (Size.ofBytes 8) #[] (Size.ofBytes 8) alloc = .ok () alloc ∧
      Allocation.writeBytes (Size.ofBytes 2) #[7, 9] (Size.ofBytes 8) alloc = .ok () updated ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) = .ok #[7, 9] ∧
      updated.initializationMask.isRangeInitialized
        (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) = .ok (.ok ()) ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes 4) (Size.ofBytes 4)) = .ok #[0, 0, 0, 0] ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes 2) (Size.ofBytes 4)) = .ok slice26 ∧
      slice26.size = 4 ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes 3) (Size.ofBytes 2)) =
        .ok (slice26.extract 1 3) ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes 2) (Size.ofBytes 6)) =
        .ok (#[7, 9] ++ #[0, 0, 0, 0]) ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).byteSize = updated.byteSize ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).len = updated.len ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).align = updated.align ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).mutability = updated.mutability ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).provenanceMap = updated.provenanceMap ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).initializationMask =
        updated.initializationMask ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).getBytesUnchecked
        (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) =
        updated.getBytesUnchecked (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) ∧
      (updated.mapExtra id).getBytesStripProvenance ⟨.little, .w64⟩
        (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) =
        updated.getBytesStripProvenance ⟨.little, .w64⟩
          (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) ∧
      (updated.mapExtra id).readScalar ⟨.little, .w64⟩
        (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) false =
        updated.readScalar ⟨.little, .w64⟩
          (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) false ∧
      Allocation.writeBytes (Size.ofBytes 2) #[7, 9] (Size.ofBytes 8) (alloc.mapExtra id) =
        .ok () (updated.mapExtra id) ∧
      Allocation.clearProvenance (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 8)
        (updated.mapExtra id) =
        (match Allocation.clearProvenance (allocRange Size.ZERO (Size.ofBytes 2))
            (Size.ofBytes 8) updated with
         | .ok v s => .ok v (s.mapExtra id)
         | .error e s => .error e (s.mapExtra id)) := by
  obtain ⟨alloc, hcreated, -, -⟩ := Allocation.fromBytes_exists (P := CtfeProvenance)
    (Array.replicate 8 0) Align.ONE 1 .Mut rfl rfl (by decide)
  obtain ⟨hbs, hlen, hmut, -, -, hprov, hmask, hwf, hslice⟩ :=
    Allocation.fromBytes_spec _ _ _ alloc hcreated
  have hzero := Allocation.writeBytes_zero_spec (Size.ofBytes 8) (Size.ofBytes 8) #[] alloc
    rfl (hlen.trans hbs.symm) (by rw [hbs]; decide)
  obtain ⟨updated, hw, hbsU, hlenU, -, -, -, -, -, -, -, hinit, -, hget22, hframe⟩ :=
    Allocation.writeBytes_spec (Size.ofBytes 2) (Size.ofBytes 8) #[7, 9] alloc ProvenanceMap.new
      (by decide) (hlen.trans hbs.symm) hmut (by rw [hmask]; rfl) hwf (by rw [hbs]; decide)
      (fun _ _ => by
        rw [hprov]
        exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 4) (by decide) (by decide))
  have hget44 : updated.getBytesUnchecked (allocRange (Size.ofBytes 4) (Size.ofBytes 4)) =
      .ok #[0, 0, 0, 0] := by
    rw [hframe _ (Size.ofBytes 8) (by decide) (by decide) (by rw [hbs]; decide) (by decide),
      hslice _ (Size.ofBytes 8) (by decide) (by decide) (by decide)]
    decide
  have hstorU : updated.len = updated.byteSize.bytes.toNat :=
    hlenU.trans (hlen.trans (hbs.symm.trans (congrArg (·.bytes.toNat) hbsU.symm)))
  obtain ⟨slice26, hget24, hsz24⟩ := Allocation.getBytesUnchecked_size updated
    (allocRange (Size.ofBytes 2) (Size.ofBytes 4)) (Size.ofBytes 6) hstorU
    (by decide) (by decide) (by rw [hbsU, hbs]; decide)
  have hsub := Allocation.getBytesUnchecked_subrange updated
    (allocRange (Size.ofBytes 2) (Size.ofBytes 4)) (allocRange (Size.ofBytes 3) (Size.ofBytes 2))
    (Size.ofBytes 6) (Size.ofBytes 5) slice26 (by decide) (by decide)
    (by decide) (by decide) (by decide) hget24
  have hsplit := Allocation.getBytesUnchecked_split updated
    (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) (allocRange (Size.ofBytes 4) (Size.ofBytes 4))
    (allocRange (Size.ofBytes 2) (Size.ofBytes 6)) (Size.ofBytes 4) (Size.ofBytes 8)
    #[7, 9] #[0, 0, 0, 0] (by decide) rfl (by decide) rfl (by decide)
    (by decide) (by decide) hget22 hget44
  have hw_map := Allocation.writeBytes_mapExtra (Size.ofBytes 2) #[7, 9] (Size.ofBytes 8) alloc id
  rw [hw] at hw_map
  refine ⟨alloc, updated, slice26, hcreated, hzero, hw, hget22, hinit, hget44, hget24,
    hsz24, hsub, hsplit,
    (Allocation.byteSize_mapExtra _ _).trans (Allocation.byteSize_withExtra _ _),
    (Allocation.len_mapExtra _ _).trans (Allocation.len_withExtra _ _),
    (Allocation.align_mapExtra _ _).trans (Allocation.align_withExtra _ _),
    (Allocation.mutability_mapExtra _ _).trans (Allocation.mutability_withExtra _ _),
    (Allocation.provenanceMap_mapExtra _ _).trans (Allocation.provenanceMap_withExtra _ _),
    (Allocation.initializationMask_mapExtra _ _).trans (Allocation.initializationMask_withExtra _ _),
    (Allocation.getBytesUnchecked_mapExtra _ _ _).trans
      (Allocation.getBytesUnchecked_withExtra _ _ _),
    Allocation.getBytesStripProvenance_mapExtra _ _ _ _,
    Allocation.readScalar_mapExtra _ _ _ _ _,
    hw_map, ?_⟩
  rw [Allocation.clearProvenance_mapExtra]
  cases Allocation.clearProvenance (allocRange Size.ZERO (Size.ofBytes 2))
    (Size.ofBytes 8) updated <;> rfl

/-- 3. `tryNew_exists` / `tryNew_spec` (both `.Uninit` and `.Zero`),
`getBytesStripProvenance_{uninit_err,ok}`, `readScalar_uninit_err`, and
`writeUninit_{zero_,}spec`. -/
theorem wit_tryNew_strip_and_writeUninit :
    ∃ (aUninit aZero aDeinit : Allocation CtfeProvenance Unit) (bad : AllocRange),
      Allocation.tryNew (Size.ofBytes 8) Align.EIGHT .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok aUninit ∧
      aUninit.getBytesStripProvenance ⟨.little, .w64⟩ (allocRange Size.ZERO (Size.ofBytes 4)) =
        .error (.invalidUninitBytes (some ⟨allocRange Size.ZERO (Size.ofBytes 4), bad⟩)) ∧
      aUninit.readScalar ⟨.little, .w64⟩ (allocRange Size.ZERO (Size.ofBytes 4)) false =
        .error (.invalidUninitBytes (some ⟨allocRange Size.ZERO (Size.ofBytes 4), bad⟩)) ∧
      Allocation.tryNew (Size.ofBytes 8) Align.EIGHT .Zero
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok aZero ∧
      aZero.getBytesStripProvenance ⟨.little, .w64⟩ (allocRange Size.ZERO (Size.ofBytes 4)) =
        .ok #[0, 0, 0, 0] ∧
      Allocation.writeUninit (allocRange (Size.ofBytes 8) Size.ZERO) (Size.ofBytes 8) aZero =
        .ok () aZero ∧
      Allocation.writeUninit (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 8) aZero =
        .ok () aDeinit ∧
      aDeinit.initializationMask.get Size.ZERO = .ok false ∧
      aDeinit.initializationMask.get (Size.ofBytes 2) = .ok true ∧
      aDeinit.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 4)) = .ok #[0, 0, 0, 0] := by
  obtain ⟨aUninit, huNew, _⟩ := Allocation.tryNew_exists (P := CtfeProvenance)
    (Size.ofBytes 8) Align.EIGHT 8 .Uninit (by decide) (by decide)
  obtain ⟨hbsU, _, _, _, _, _, hmaskU, _, hwfU, _⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 8) Align.EIGHT .Uninit aUninit huNew
  have hmU := hmaskU rfl
  have hget0_false : aUninit.initializationMask.get Size.ZERO = .ok false := by rw [hmU]; rfl
  obtain ⟨bad, hbad⟩ := (InitMask.WriteProof.isRangeInitialized_nonempty_iff
    aUninit.initializationMask (allocRange Size.ZERO (Size.ofBytes 4)) (Size.ofBytes 4)
    hwfU (by decide) (by decide) (by rw [hmU]; decide)).2
    ⟨Size.ZERO, by decide, by decide, hget0_false⟩
  have hstripErr := Allocation.getBytesStripProvenance_uninit_err aUninit ⟨.little, .w64⟩ _ bad hbad
  have hreadErr := Allocation.readScalar_uninit_err aUninit ⟨.little, .w64⟩ _ bad false hbad
  obtain ⟨aZero, hzNew, _⟩ := Allocation.tryNew_exists (P := CtfeProvenance)
    (Size.ofBytes 8) Align.EIGHT 8 .Zero (by decide) (by decide)
  obtain ⟨hbsZ, hlenZ, hmutZ, _, _, hprovZ, _, hmaskZ, hwfZ, hsliceZ⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 8) Align.EIGHT .Zero aZero hzNew
  have hmZ := hmaskZ rfl
  have hend4 : (allocRange Size.ZERO (Size.ofBytes 4)).endExclusive = .ok (Size.ofBytes 4) := by
    decide
  have hps : (Size.fromBits PointerWidth.w64.bits).bytes ≠ 0 := by decide
  have hinitZ : aZero.initializationMask.isRangeInitialized
      (allocRange Size.ZERO (Size.ofBytes 4)) = .ok (.ok ()) := by
    rw [hmZ]
    exact InitMask.lazy_initialized_query _ _ _ hend4 (by decide)
  have hstripOk : aZero.getBytesStripProvenance ⟨.little, .w64⟩
      (allocRange Size.ZERO (Size.ofBytes 4)) = .ok #[0, 0, 0, 0] := by
    rw [Allocation.getBytesStripProvenance_ok aZero _ _ hinitZ
      (Or.inr (by rw [hprovZ]; exact ProvenanceMap.rangeEmpty_new _ _ _ hps hend4))]
    exact hsliceZ _ _ hend4 (by decide) (by decide)
  have hstorZ : aZero.len = aZero.byteSize.bytes.toNat := by rw [hlenZ, hbsZ]
  have hwuZero := Allocation.writeUninit_zero_spec (allocRange (Size.ofBytes 8) Size.ZERO)
    (Size.ofBytes 8) (Size.ofBytes 8) aZero rfl hstorZ (by decide) (by decide)
    (by rw [hbsZ]; decide)
  obtain ⟨aDeinit, hwu, _, _, _, _, _, _, _, _, hsetF, _, hbytesEq⟩ :=
    Allocation.writeUninit_spec (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 8)
      aZero ProvenanceMap.new (by decide) hstorZ hmutZ (by rw [hmZ, hbsZ]; rfl) hwfZ
      (by rw [hbsZ]; decide)
      (fun _ _ => by
        rw [hprovZ]
        exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 2) (by decide) (by decide))
  have hg0 := InitMask.WriteProof.set_range_get aZero.initializationMask
    aDeinit.initializationMask (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 2)
    Size.ZERO false hwfZ (by decide) (by decide) (by rw [hmZ]; decide) (by rw [hmZ]; decide) hsetF
  have hg2 := InitMask.WriteProof.set_range_get aZero.initializationMask
    aDeinit.initializationMask (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 2)
    (Size.ofBytes 2) false hwfZ (by decide) (by decide) (by rw [hmZ]; decide)
    (by rw [hmZ]; decide) hsetF
  have hmZ0 : aZero.initializationMask.get Size.ZERO = .ok true := by rw [hmZ]; rfl
  have hmZ2 : aZero.initializationMask.get (Size.ofBytes 2) = .ok true := by rw [hmZ]; rfl
  refine ⟨aUninit, aZero, aDeinit, bad, huNew, hstripErr, hreadErr, hzNew, hstripOk, hwuZero,
    hwu, ?_, ?_, (hbytesEq _).trans (hsliceZ _ _ hend4 (by decide) (by decide))⟩
  · rw [hg0, hmZ0]; decide
  · rw [hg2, hmZ2]; decide

/-- 4. `readScalar_int_of_bytes` decodes `#[1, 2]` as `0x0201` on little-endian targets and
`0x0102` on big-endian targets. -/
theorem wit_readScalar_int_of_bytes (endian : Endian) :
    ∃ alloc : Allocation CtfeProvenance Unit,
      Allocation.fromBytes #[1, 2] Align.ONE .Not = .ok alloc ∧
      alloc.readScalar ⟨endian, .w64⟩ (allocRange Size.ZERO (Size.ofBytes 2)) false =
        (Scalar.fromUInt (BitVec.ofNat 128 (if endian == .little then 0x0201 else 0x0102))
          (Size.ofBytes 2)).mapError AllocError.scalar := by
  obtain ⟨alloc, hcreated, -, -⟩ := Allocation.fromBytes_exists (P := CtfeProvenance)
    #[1, 2] Align.ONE 1 .Not rfl rfl (by decide)
  obtain ⟨hbs, -, -, -, -, hprov, hmask, -, hslice⟩ :=
    Allocation.fromBytes_spec _ _ _ alloc hcreated
  have hend : (allocRange Size.ZERO (Size.ofBytes 2)).endExclusive = .ok (Size.ofBytes 2) := by
    decide
  have hps : (Size.fromBits PointerWidth.w64.bits).bytes ≠ 0 := by decide
  refine ⟨alloc, hcreated, ?_⟩
  rw [Allocation.readScalar_int_of_bytes alloc _ _ #[1, 2]
    (by
      rw [hmask]
      exact InitMask.lazy_initialized_query _ _ _ hend
        (UInt64.le_iff_toNat_le.mpr (by rw [hbs]; decide)))
    (hslice _ _ hend (by decide) (by decide)) (by decide)
    (Or.inr (by rw [hprov]; exact ProvenanceMap.rangeEmpty_new _ _ _ hps hend))]
  cases endian <;> rfl

/-- 5. `writeScalar_spec` (both `.bits` and `.pointer` branches) chained into
`readScalar_int_roundtrip`, `readScalar_ptr_none_roundtrip`, and `readScalar_ptr_roundtrip`
across both little- and big-endian target layouts. -/
theorem wit_writeScalar_and_readScalar_roundtrips (endian : Endian) :
    ∃ (a0 aBits : Allocation CtfeProvenance Unit) (p0 pPtr : Allocation Provenance Unit),
      let layout : TargetDataLayout := ⟨endian, .w64⟩
      let intVal : Scalar CtfeProvenance := Scalar.fromScalarInt (ScalarInt.ofUInt64 0x0102030405060708)
      let ptr : Pointer Provenance := ⟨Size.ofBytes 0x1020, .wildcard⟩
      let ptrVal : Scalar Provenance := Scalar.fromPointer layout ptr
      Allocation.tryNew (Size.ofBytes 8) Align.EIGHT .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok a0 ∧
      Allocation.writeScalar layout (allocRange Size.ZERO (Size.ofBytes 8)) intVal a0 =
        .ok () aBits ∧
      aBits.readScalar layout (allocRange Size.ZERO (Size.ofBytes 8)) false = .ok intVal ∧
      aBits.readScalar layout (allocRange Size.ZERO (Size.ofBytes 8)) true = .ok intVal ∧
      Allocation.tryNew (Size.ofBytes 16) Align.EIGHT .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok p0 ∧
      Allocation.writeScalar layout (allocRange Size.ZERO (Size.ofBytes 8)) ptrVal p0 =
        .ok () pPtr ∧
      pPtr.readScalar layout (allocRange Size.ZERO (Size.ofBytes 8)) true = .ok ptrVal ∧
      pPtr.getBytesUnchecked (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) =
        .ok (Array.replicate 8 0) := by
  let layout : TargetDataLayout := ⟨endian, .w64⟩
  let bits : U128 := BitVec.ofNat 128 (0x0102030405060708 : UInt64).toNat
  let intVal : Scalar CtfeProvenance := Scalar.fromScalarInt (ScalarInt.ofUInt64 0x0102030405060708)
  let r08 := allocRange Size.ZERO (Size.ofBytes 8)
  have hend08 : r08.endExclusive = .ok (Size.ofBytes 8) := by decide
  have hps_eq : Size.fromBits layout.pointerWidth.bits = Size.ofBytes 8 := by
    dsimp only [layout]; decide
  have hps_nz : (Size.fromBits layout.pointerWidth.bits).bytes ≠ 0 := by
    dsimp only [layout]; decide
  obtain ⟨a0, ha0, _⟩ := Allocation.tryNew_exists (P := CtfeProvenance)
    (Size.ofBytes 8) Align.EIGHT 8 .Uninit (by decide) (by decide)
  obtain ⟨hbs0, hlen0, hmut0, _, _, hprov0, hmask0, _, hwf0, _⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 8) Align.EIGHT .Uninit a0 ha0
  obtain ⟨aBits, hwBits, _, _, _, _, _, _, _, _, _, hisBits, hprovBits, hbytesBits, _, _⟩ :=
    Allocation.writeScalar_spec layout a0 r08 intVal (.bits bits) ProvenanceMap.new ProvenanceMap.new
      (by rw [hlen0, hbs0]) hmut0 (by rw [hmask0 rfl, hbs0]; rfl) hwf0
      (by decide) (by decide) (by rw [hbs0]; decide) (by decide)
      (fun _ _ => by
        rw [hprov0, hps_eq]
        exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 8) (by decide) hend08)
      rfl
  have hfromUInt : (Scalar.fromUInt (Prov := CtfeProvenance) bits r08.size).mapError
      AllocError.scalar = .ok intVal := by decide
  have hreadInt := Allocation.readScalar_int_roundtrip aBits layout r08 bits
    hisBits (by decide) (by decide)
    (Or.inr (by rw [hprovBits]; exact ProvenanceMap.rangeEmpty_new _ _ _ hps_nz hend08))
    (hbytesBits bits rfl)
  have hreadPtrNone := Allocation.readScalar_ptr_none_roundtrip aBits layout r08 bits
    hisBits hps_eq.symm (by decide) (by decide)
    (by rw [hprovBits, hps_eq]; exact ProvenanceMap.readPtr_new _ _ _ (by decide) hend08)
    (hbytesBits bits rfl)
  let ptr : Pointer Provenance := ⟨Size.ofBytes 0x1020, .wildcard⟩
  let ptrVal : Scalar Provenance := Scalar.fromPointer layout ptr
  obtain ⟨pm1, hpm1_ins, hpm1_ptrs⟩ :
      ∃ pm1 : ProvenanceMap Provenance,
        ProvenanceMap.insertPtr Size.ZERO Provenance.wildcard (Size.ofBytes 8) ProvenanceMap.new =
          .ok () pm1 ∧
        pm1.ptrs = #[(Size.ZERO, Provenance.wildcard)] :=
    ⟨_, ProvenanceMap.insertPtr_new Size.ZERO (Size.ofBytes 8) (Size.ofBytes 8)
      Provenance.wildcard (by decide) hend08, rfl⟩
  have hconvPtr : ptrVal.toBitsOrPtrInternal r08.size = .ok (.pointer ptr) := by
    cases endian <;> decide
  obtain ⟨p0, hp0, _⟩ := Allocation.tryNew_exists (P := Provenance)
    (Size.ofBytes 16) Align.EIGHT 8 .Uninit (by decide) (by decide)
  obtain ⟨hbsP, hlenP, hmutP, _, _, hprovP, hmaskP, _, hwfP, hsliceP⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 16) Align.EIGHT .Uninit p0 hp0
  obtain ⟨pPtr, hwPtr, _, _, _, _, _, _, _, _, _, hisPtr, hprovPtr, _, hbytesPtr, hframePtr⟩ :=
    Allocation.writeScalar_spec layout p0 r08 ptrVal (.pointer ptr) ProvenanceMap.new pm1
      (by rw [hlenP, hbsP]) hmutP (by rw [hmaskP rfl, hbsP]; rfl) hwfP
      (by decide) (by decide) (by rw [hbsP]; decide) hconvPtr
      (fun _ _ => by
        rw [hprovP, hps_eq]
        exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 8) (by decide) hend08)
      ⟨hps_eq.symm, by rw [hps_eq]; exact hpm1_ins⟩
  have hpSlice : pPtr.getBytesUnchecked r08 =
      .ok (Array.ofFn (fun i : Fin r08.size.bytes.toNat =>
        UInt8.ofNat ((ptr.offset.bytes.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else r08.size.bytes.toNat - i.1 - 1))) % 256))) := by
    have hbv : (BitVec.ofNat 128 ptr.offset.bytes.toNat).toNat = ptr.offset.bytes.toNat := by decide
    simpa [hbv] using hbytesPtr ptr rfl
  have hgetPtr : pm1.getPtr r08.start = some ptr.provenance := by
    unfold ProvenanceMap.getPtr
    rw [hpm1_ptrs]
    decide
  have hreadPtr := Allocation.readScalar_ptr_roundtrip pPtr layout r08 ptr
    hisPtr hps_eq.symm (by decide) (by decide)
    (by rw [hprovPtr, hps_eq]; exact ProvenanceMap.read_exact_pointer pm1 _ _ _ hgetPtr) hpSlice
  have hfr8 := hframePtr (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) (Size.ofBytes 16)
    (by decide) (by decide) (by rw [hbsP]; decide) (Or.inl (by decide))
  have hp8 := hsliceP (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) (Size.ofBytes 16)
    (by decide) (by decide) (by decide)
  exact ⟨a0, aBits, p0, pPtr, ha0, hwBits, hreadInt.trans hfromUInt,
    hreadPtrNone.trans hfromUInt, hp0, hwPtr, hreadPtr, hfr8.trans hp8⟩

/-- 6. `copy_initialized_spec` (cross-allocation and non-overlapping same-allocation) and
`copyRepeatedly_initialized_spec` (`repeatCount = 3`), together with `prepareCopy_new` and
`applyCopy_empty`, verifying byte + mask `get` + `isRangeInitialized` framing. -/
theorem wit_copy_and_copyRepeatedly :
    ∃ (src d0 d1 d2 d3 : Allocation CtfeProvenance Unit),
      Allocation.fromBytes #[5, 6] Align.ONE .Not = .ok src ∧
      Allocation.tryNew (Size.ofBytes 12) Align.ONE .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok d0 ∧
      Allocation.copy src (allocRange Size.ZERO (Size.ofBytes 2)) Size.ZERO
        (Size.ofBytes 8) false true d0 = .ok () d1 ∧
      Allocation.copy d1 (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 2)
        (Size.ofBytes 8) true true d1 = .ok () d2 ∧
      d2.getBytesUnchecked (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) = .ok #[5, 6] ∧
      d2.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 2)) = .ok #[5, 6] ∧
      d2.initializationMask.get (Size.ofBytes 10) = .ok false ∧
      Allocation.copyRepeatedly d2 (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 4)
        3 (Size.ofBytes 8) true true d2 = .ok () d3 ∧
      d3.getBytesUnchecked (allocRange (Size.ofBytes 4) (Size.ofBytes 6)) =
        .ok #[5, 6, 5, 6, 5, 6] ∧
      d3.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 4)) = .ok #[5, 6, 5, 6] ∧
      d3.initializationMask.isRangeInitialized (allocRange (Size.ofBytes 4) (Size.ofBytes 6)) =
        .ok (.ok ()) ∧
      d3.initializationMask.isRangeInitialized (allocRange Size.ZERO (Size.ofBytes 2)) =
        .ok (.ok ()) ∧
      d3.initializationMask.get (Size.ofBytes 10) = .ok false := by
  obtain ⟨src, hsrc, _, _⟩ := Allocation.fromBytes_exists (P := CtfeProvenance)
    #[5, 6] Align.ONE 1 .Not rfl rfl (by decide)
  obtain ⟨hbsS, hlenS, _, _, _, hprovS, hmaskS, hwfS, hsliceS⟩ :=
    Allocation.fromBytes_spec _ _ _ src hsrc
  have hend02 : (allocRange Size.ZERO (Size.ofBytes 2)).endExclusive = .ok (Size.ofBytes 2) := by
    decide
  have hinitS : src.initializationMask.isRangeInitialized
      (allocRange Size.ZERO (Size.ofBytes 2)) = .ok (.ok ()) := by
    rw [hmaskS]
    exact InitMask.lazy_initialized_query _ _ _ hend02
      (UInt64.le_iff_toNat_le.mpr (by rw [hbsS]; decide))
  obtain ⟨d0, hd0, _⟩ := Allocation.tryNew_exists (P := CtfeProvenance)
    (Size.ofBytes 12) Align.ONE 1 .Uninit (by decide) (by decide)
  obtain ⟨hbs0, hlen0, hmut0, _, _, hprov0, hmask0, _, hwf0, _⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 12) Align.ONE .Uninit d0 hd0
  have hm0 := hmask0 rfl
  obtain ⟨d1, hc1, hbs1, hlen1, hmut1, _, _, _, hml1, hwf1, his1_02, hmget1, _, hprov1, hb1_02, _⟩ :=
    Allocation.copy_initialized_spec src d0 (allocRange Size.ZERO (Size.ofBytes 2))
      (Size.ofBytes 2) Size.ZERO (Size.ofBytes 8) false true #[5, 6]
      ⟨#[], #[]⟩ ProvenanceMap.new ProvenanceMap.new
      (hlenS.trans hbsS.symm) hend02 (by decide) (by rw [hmaskS]; rfl) hwfS hinitS
      (hsliceS _ _ hend02 (by decide) (by decide)) (by rw [hbsS]; decide)
      (fun _ _ => by rw [hprovS]; exact ProvenanceMap.prepareCopy_new _ _ _ _ (by decide) hend02)
      (fun h => by cases h)
      (by rw [hlen0, hbs0]) hmut0 (by rw [hm0, hbs0]; rfl) hwf0 (by rw [hbs0]; decide)
      (fun _ _ => by rw [hprov0]; exact ProvenanceMap.clear_new _ _ _ _ (by decide) hend02)
      (ProvenanceMap.applyCopy_empty _ 1 ProvenanceMap.new)
  have hd1_stor : d1.len = d1.byteSize.bytes.toNat := by rw [hlen1, hbs1, hlen0, hbs0]
  have hd1_ml : d1.initializationMask.len = d1.byteSize := by rw [hml1, hbs1, hm0, hbs0]; rfl
  obtain ⟨d2, hc2, hbs2, hlen2, hmut2, _, _, _, hml2, hwf2, _, hmget2, hmfr2, hprov2, hb2_22, hbfr2⟩ :=
    Allocation.copy_initialized_spec d1 d1 (allocRange Size.ZERO (Size.ofBytes 2))
      (Size.ofBytes 2) (Size.ofBytes 2) (Size.ofBytes 8) true true #[5, 6]
      ⟨#[], #[]⟩ ProvenanceMap.new ProvenanceMap.new
      hd1_stor hend02 (by decide) hd1_ml hwf1 his1_02 hb1_02 (by rw [hbs1, hbs0]; decide)
      (fun _ _ => by rw [hprov1]; exact ProvenanceMap.prepareCopy_new _ _ _ _ (by decide) hend02)
      (fun _ _ => Or.inl (by decide))
      hd1_stor (hmut1.trans hmut0) hd1_ml hwf1 (by rw [hbs1, hbs0]; decide)
      (fun _ _ => by rw [hprov1]; exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 4) (by decide) (by decide))
      (ProvenanceMap.applyCopy_empty _ 1 ProvenanceMap.new)
  have hb2_02 : d2.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 2)) = .ok #[5, 6] :=
    (hbfr2 _ (Size.ofBytes 2) hend02 (by decide) (by rw [hbs1, hbs0]; decide)
      (Or.inr (by decide))).trans hb1_02
  have his2_02 : d2.initializationMask.isRangeInitialized
      (allocRange Size.ZERO (Size.ofBytes 2)) = .ok (.ok ()) :=
    (hmfr2 _ (Size.ofBytes 2) hend02 (by decide) (by rw [hbs1, hbs0]; decide)
      (Or.inr (by decide))).mpr his1_02
  have hd2_10 : d2.initializationMask.get (Size.ofBytes 10) = .ok false := by
    have h2 := hmget2 (Size.ofBytes 10) (by rw [hbs1, hbs0]; decide)
    have h1 := hmget1 (Size.ofBytes 10) (by rw [hbs0]; decide)
    have hm0_10 : d0.initializationMask.get (Size.ofBytes 10) = .ok false := by rw [hm0]; rfl
    rw [h2, h1, hm0_10]
    decide
  have hd2_stor : d2.len = d2.byteSize.bytes.toNat := by rw [hlen2, hbs2]; exact hd1_stor
  have hd2_ml : d2.initializationMask.len = d2.byteSize := by rw [hml2, hbs2]; exact hd1_ml
  obtain ⟨d3, hc3, _, _, _, _, _, _, _, _, his3_46, hmget3, hmfr3, _, hb3_46, hbfr3⟩ :=
    Allocation.copyRepeatedly_initialized_spec d2 d2 (allocRange Size.ZERO (Size.ofBytes 2))
      (Size.ofBytes 2) (Size.ofBytes 4) (Size.ofBytes 6) (Size.ofBytes 8) 3 true true #[5, 6]
      ⟨#[], #[]⟩ ProvenanceMap.new ProvenanceMap.new
      hd2_stor hend02 (by decide) hd2_ml hwf2 his2_02 hb2_02 (by rw [hbs2, hbs1, hbs0]; decide)
      (fun _ _ => by rw [hprov2]; exact ProvenanceMap.prepareCopy_new _ _ _ _ (by decide) hend02)
      (by decide) (by decide) (fun _ => rfl) (fun _ _ => Or.inl (by decide))
      hd2_stor (hmut2.trans (hmut1.trans hmut0)) hd2_ml hwf2 (by rw [hbs2, hbs1, hbs0]; decide)
      (fun _ _ => by rw [hprov2]; exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 10) (by decide) (by decide))
      (ProvenanceMap.applyCopy_empty _ 3 ProvenanceMap.new)
  have hb2_04 : d2.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 4)) = .ok #[5, 6, 5, 6] :=
    Allocation.getBytesUnchecked_split d2 (allocRange Size.ZERO (Size.ofBytes 2))
      (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) (allocRange Size.ZERO (Size.ofBytes 4))
      (Size.ofBytes 2) (Size.ofBytes 4) #[5, 6] #[5, 6] hend02 rfl (by decide) rfl (by decide)
      (by decide) (by decide) hb2_02 hb2_22
  have hb3_04 : d3.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 4)) = .ok #[5, 6, 5, 6] :=
    (hbfr3 _ (Size.ofBytes 4) (by decide) (by decide) (by rw [hbs2, hbs1, hbs0]; decide)
      (Or.inr (by decide))).trans hb2_04
  have his3_02 : d3.initializationMask.isRangeInitialized
      (allocRange Size.ZERO (Size.ofBytes 2)) = .ok (.ok ()) :=
    (hmfr3 _ (Size.ofBytes 2) hend02 (by decide) (by rw [hbs2, hbs1, hbs0]; decide)
      (Or.inr (by decide))).mpr his2_02
  have hd3_10 : d3.initializationMask.get (Size.ofBytes 10) = .ok false := by
    have h3 := hmget3 (Size.ofBytes 10) (by rw [hbs2, hbs1, hbs0]; decide)
    rw [h3, hd2_10]
    decide
  exact ⟨src, d0, d1, d2, d3, hsrc, hd0, hc1, hc2, hb2_22, hb2_02, hd2_10,
    hc3, by simpa using hb3_46, hb3_04, his3_46, his3_02, hd3_10⟩

/-- 7. Concrete 64-bit word layouts, evaluated by the kernel (`decide +kernel`, zero
`Lean.ofReduceBool`), paired with `.Materialized`-input instantiations of `set_range_get`
(`.Materialized` → `.Materialized` clearing write straddling byte 64 and `.Materialized` → `.Lazy`
full overwrite), `isRangeInitialized_frame` (`state = false`, `Or.inl` disjoint branch on
`.Materialized`), `prepareCopy_of_uniform` (`state = false` uniform uninitialized chunk), and
`get_ok_of_wellFormed` on `.Materialized`. -/
theorem wit_initMask_word_layout :
    let m1 : InitMask :=
      ⟨.Materialized ⟨#[0xF000000000000000, 0xFFFFFFFFFFFFFFFF, 0xFFF, 0]⟩, Size.ofBytes 200⟩
    let m2 : InitMask :=
      ⟨.Materialized ⟨#[0x3000000000000000, 0xFFFFFFFFFFFFFFFC, 0xFFF, 0]⟩, Size.ofBytes 200⟩
    (InitMask.new (Size.ofBytes 200) false).setRange
        (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) true = .ok m1 ∧
    m1.setRange (allocRange (Size.ofBytes 62) (Size.ofBytes 4)) false = .ok m2 ∧
    m2.setRange (allocRange Size.ZERO (Size.ofBytes 200)) true =
      .ok (InitMask.new (Size.ofBytes 200) true) ∧
    m2.get (Size.ofBytes 61) = .ok true ∧
    m2.get (Size.ofBytes 62) = .ok false ∧
    m2.get (Size.ofBytes 65) = .ok false ∧
    m2.get (Size.ofBytes 66) = .ok true ∧
    m2.isRangeInitialized (allocRange (Size.ofBytes 66) (Size.ofBytes 74)) = .ok (.ok ()) ∧
    m2.prepareCopy (allocRange (Size.ofBytes 62) (Size.ofBytes 4)) = .ok ⟨false, #[4]⟩ ∧
    (InitMask.new (Size.ofBytes 200) true).get (Size.ofBytes 62) = .ok true ∧
    ∃ b, m2.get (Size.ofBytes 199) = .ok b := by
  let m1 : InitMask :=
    ⟨.Materialized ⟨#[0xF000000000000000, 0xFFFFFFFFFFFFFFFF, 0xFFF, 0]⟩, Size.ofBytes 200⟩
  let m2 : InitMask :=
    ⟨.Materialized ⟨#[0x3000000000000000, 0xFFFFFFFFFFFFFFFC, 0xFFF, 0]⟩, Size.ofBytes 200⟩
  have hwf0 : InitMask.WriteProof.WellFormed (InitMask.new (Size.ofBytes 200) false) := trivial
  have hwf1 : InitMask.WriteProof.WellFormed m1 := by
    simp only [InitMask.WriteProof.WellFormed]; decide
  have hwf2 : InitMask.WriteProof.WellFormed m2 := by
    simp only [InitMask.WriteProof.WellFormed]; decide
  -- Kernel-checked (`decide +kernel`, zero `Lean.ofReduceBool`) evaluation of 64-bit word layouts:
  have hset01 : (InitMask.new (Size.ofBytes 200) false).setRange
      (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) true = .ok m1 := by decide +kernel
  have hset12 : m1.setRange (allocRange (Size.ofBytes 62) (Size.ofBytes 4)) false = .ok m2 := by
    decide +kernel
  have hset23 : m2.setRange (allocRange Size.ZERO (Size.ofBytes 200)) true =
      .ok (InitMask.new (Size.ofBytes 200) true) := by decide +kernel
  have hm1_get : ∀ idx : Size, idx.bytes.toNat < 200 → m1.get idx =
      if 60 ≤ idx.bytes.toNat ∧ idx.bytes.toNat < 140 then .ok true else .ok false :=
    fun idx hidx => InitMask.WriteProof.set_range_get _ m1 _ (Size.ofBytes 140) idx true
      hwf0 (by decide) (by decide) (by decide) hidx hset01
  have hm2_get : ∀ idx : Size, idx.bytes.toNat < 200 → m2.get idx =
      if 62 ≤ idx.bytes.toNat ∧ idx.bytes.toNat < 66 then .ok false else m1.get idx :=
    fun idx hidx => InitMask.WriteProof.set_range_get m1 m2 _ (Size.ofBytes 66) idx false
      hwf1 (by decide) (by decide) (by decide) hidx hset12
  have hg61 : m2.get (Size.ofBytes 61) = .ok true := by
    rw [hm2_get _ (by decide), hm1_get _ (by decide)]; decide
  have hg62 : m2.get (Size.ofBytes 62) = .ok false := by rw [hm2_get _ (by decide)]; decide
  have hg65 : m2.get (Size.ofBytes 65) = .ok false := by rw [hm2_get _ (by decide)]; decide
  have hg66 : m2.get (Size.ofBytes 66) = .ok true := by
    rw [hm2_get _ (by decide), hm1_get _ (by decide)]; decide
  have hm1_66_140 : m1.isRangeInitialized (allocRange (Size.ofBytes 66) (Size.ofBytes 74)) =
      .ok (.ok ()) :=
    (InitMask.WriteProof.isRangeInitialized_nonempty_iff m1 _ (Size.ofBytes 140)
      hwf1 (by decide) (by decide) (by decide)).1.mpr fun idx hlo hhi => by
      change 66 ≤ idx.bytes.toNat at hlo
      change idx.bytes.toNat < 140 at hhi
      rw [hm1_get idx (by omega)]
      split
      · rfl
      · omega
  have hm2_66_140 : m2.isRangeInitialized (allocRange (Size.ofBytes 66) (Size.ofBytes 74)) =
      .ok (.ok ()) :=
    (InitMask.WriteProof.isRangeInitialized_frame m1 m2
      (allocRange (Size.ofBytes 62) (Size.ofBytes 4))
      (allocRange (Size.ofBytes 66) (Size.ofBytes 74))
      (Size.ofBytes 66) (Size.ofBytes 140) false hwf1 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide)) hset12).mpr hm1_66_140
  have hpc_false : m2.prepareCopy (allocRange (Size.ofBytes 62) (Size.ofBytes 4)) =
      .ok ⟨false, #[4]⟩ :=
    InitMask.WriteProof.prepareCopy_of_uniform m2 _ (Size.ofBytes 66) false
      hwf2 (by decide) (by decide) (by decide) fun idx hlo hhi => by
      change 62 ≤ idx.bytes.toNat at hlo
      change idx.bytes.toNat < 66 at hhi
      rw [hm2_get idx (by omega)]
      split
      · rfl
      · omega
  have hm3_62 : (InitMask.new (Size.ofBytes 200) true).get (Size.ofBytes 62) = .ok true := by
    have h := InitMask.WriteProof.set_range_get m2 (InitMask.new (Size.ofBytes 200) true)
      (allocRange Size.ZERO (Size.ofBytes 200)) (Size.ofBytes 200) (Size.ofBytes 62) true
      hwf2 (by decide) (by decide) (by decide) (by decide) hset23
    rw [h]; decide
  exact ⟨hset01, hset12, hset23, hg61, hg62, hg65, hg66, hm2_66_140, hpc_false, hm3_62,
    InitMask.WriteProof.get_ok_of_wellFormed m2 (Size.ofBytes 199) hwf2 (by decide)⟩

/-- 8. Exposed-address (`Provenance`, `PointerProvenance.offsetIsAddr = true`) `Or.inl` branch of
`getBytesStripProvenance_ok`, `readScalar_int_roundtrip`, and `readScalar_int_of_bytes` on an
allocation carrying live pointer provenance (`rangeEmpty = .ok false`, refuting `Or.inr`), pinning
the concrete serialized pointer bytes across both little- and big-endian target layouts. -/
theorem wit_exposed_provenance_strip_and_transmute (endian : Endian) :
    ∃ (p0 pPtr : Allocation Provenance Unit),
      let layout : TargetDataLayout := ⟨endian, .w64⟩
      let ptr : Pointer Provenance := ⟨Size.ofBytes 0x1020, .wildcard⟩
      let ptrVal : Scalar Provenance := Scalar.fromPointer layout ptr
      let r08 := allocRange Size.ZERO (Size.ofBytes 8)
      let subRange := if endian == .little then allocRange Size.ZERO (Size.ofBytes 2)
        else allocRange (Size.ofBytes 6) (Size.ofBytes 2)
      Allocation.tryNew (Size.ofBytes 8) Align.EIGHT .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok p0 ∧
      Allocation.writeScalar layout r08 ptrVal p0 = .ok () pPtr ∧
      pPtr.provenanceMap.rangeEmpty r08 (Size.ofBytes 8) = .ok false ∧
      pPtr.getBytesStripProvenance layout r08 =
        .ok (if endian == .little then #[0x20, 0x10, 0, 0, 0, 0, 0, 0]
          else #[0, 0, 0, 0, 0, 0, 0x10, 0x20]) ∧
      pPtr.readScalar layout r08 false =
        .ok (Scalar.fromScalarInt (ScalarInt.ofUInt64 0x1020)) ∧
      pPtr.readScalar layout subRange false =
        (Scalar.fromUInt (BitVec.ofNat 128 0x1020) (Size.ofBytes 2)).mapError AllocError.scalar := by
  let layout : TargetDataLayout := ⟨endian, .w64⟩
  let ptr : Pointer Provenance := ⟨Size.ofBytes 0x1020, .wildcard⟩
  let ptrVal : Scalar Provenance := Scalar.fromPointer layout ptr
  let r08 := allocRange Size.ZERO (Size.ofBytes 8)
  have hend08 : r08.endExclusive = .ok (Size.ofBytes 8) := by decide
  have hps_eq : Size.fromBits layout.pointerWidth.bits = Size.ofBytes 8 := by
    dsimp only [layout]; decide
  obtain ⟨pm1, hpm1_ins, hpm1_ptrs⟩ :
      ∃ pm1 : ProvenanceMap Provenance,
        ProvenanceMap.insertPtr Size.ZERO Provenance.wildcard (Size.ofBytes 8) ProvenanceMap.new =
          .ok () pm1 ∧
        pm1.ptrs = #[(Size.ZERO, Provenance.wildcard)] :=
    ⟨_, ProvenanceMap.insertPtr_new Size.ZERO (Size.ofBytes 8) (Size.ofBytes 8)
      Provenance.wildcard (by decide) hend08, rfl⟩
  have hconvPtr : ptrVal.toBitsOrPtrInternal r08.size = .ok (.pointer ptr) := by
    cases endian <;> decide
  obtain ⟨p0, hp0, _⟩ := Allocation.tryNew_exists (P := Provenance)
    (Size.ofBytes 8) Align.EIGHT 8 .Uninit (by decide) (by decide)
  obtain ⟨hbsP, hlenP, hmutP, _, _, hprovP, hmaskP, _, hwfP, _⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 8) Align.EIGHT .Uninit p0 hp0
  obtain ⟨pPtr, hwPtr, _, _, _, _, _, _, hmlPtr, hwfPtr, _, hisPtr, hprovPtr, _, hbytesPtr, _⟩ :=
    Allocation.writeScalar_spec layout p0 r08 ptrVal (.pointer ptr) ProvenanceMap.new pm1
      (by rw [hlenP, hbsP]) hmutP (by rw [hmaskP rfl, hbsP]; rfl) hwfP
      (by decide) (by decide) (by rw [hbsP]; decide) hconvPtr
      (fun _ _ => by
        rw [hprovP, hps_eq]
        exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 8) (by decide) hend08)
      ⟨hps_eq.symm, by rw [hps_eq]; exact hpm1_ins⟩
  have hnotEmpty : pPtr.provenanceMap.rangeEmpty r08 (Size.ofBytes 8) = .ok false := by
    rw [hprovPtr]
    unfold ProvenanceMap.rangeEmpty ProvenanceMap.rangePtrs
    rw [hpm1_ptrs]
    rfl
  have hrawBytes : pPtr.getBytesUnchecked r08 =
      .ok (if endian == .little then #[0x20, 0x10, 0, 0, 0, 0, 0, 0]
        else #[0, 0, 0, 0, 0, 0, 0x10, 0x20]) := by
    rw [hbytesPtr ptr rfl]
    cases endian <;> decide
  have hstrip : pPtr.getBytesStripProvenance layout r08 =
      .ok (if endian == .little then #[0x20, 0x10, 0, 0, 0, 0, 0, 0]
        else #[0, 0, 0, 0, 0, 0, 0x10, 0x20]) :=
    (Allocation.getBytesStripProvenance_ok pPtr layout r08 hisPtr (Or.inl rfl)).trans hrawBytes
  have hbv : (BitVec.ofNat 128 ptr.offset.bytes.toNat).toNat = (0x1020 : Nat) := by decide
  have hpSlice : pPtr.getBytesUnchecked r08 =
      .ok (Array.ofFn (fun i : Fin r08.size.bytes.toNat =>
        UInt8.ofNat (((BitVec.ofNat 128 0x1020).toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else r08.size.bytes.toNat - i.1 - 1))) % 256))) := by
    simpa [hbv] using hbytesPtr ptr rfl
  have hfromUInt8 : (Scalar.fromUInt (Prov := Provenance) (BitVec.ofNat 128 0x1020) r08.size).mapError
      AllocError.scalar = .ok (Scalar.fromScalarInt (ScalarInt.ofUInt64 0x1020)) := by decide
  have htransmute8 : pPtr.readScalar layout r08 false =
      .ok (Scalar.fromScalarInt (ScalarInt.ofUInt64 0x1020)) :=
    (Allocation.readScalar_int_roundtrip pPtr layout r08 (BitVec.ofNat 128 0x1020)
      hisPtr (by decide) (by decide) (Or.inl rfl) hpSlice).trans hfromUInt8
  have hlenMaskPtr : pPtr.initializationMask.len = Size.ofBytes 8 := by
    rw [hmlPtr, hmaskP rfl]; rfl
  have hallInit : ∀ idx : Size, 0 ≤ idx.bytes.toNat → idx.bytes.toNat < 8 →
      pPtr.initializationMask.get idx = .ok true :=
    (InitMask.WriteProof.isRangeInitialized_nonempty_iff pPtr.initializationMask r08
      (Size.ofBytes 8) hwfPtr hend08 (by decide) (by rw [hlenMaskPtr]; decide)).1.mp hisPtr
  have hsub : pPtr.readScalar layout
      (if endian == .little then allocRange Size.ZERO (Size.ofBytes 2)
        else allocRange (Size.ofBytes 6) (Size.ofBytes 2)) false =
      (Scalar.fromUInt (BitVec.ofNat 128 0x1020) (Size.ofBytes 2)).mapError AllocError.scalar := by
    cases endian
    · have hinitSub : pPtr.initializationMask.isRangeInitialized
          (allocRange Size.ZERO (Size.ofBytes 2)) = .ok (.ok ()) :=
        (InitMask.WriteProof.isRangeInitialized_nonempty_iff pPtr.initializationMask _
          (Size.ofBytes 2) hwfPtr (by decide) (by decide)
          (by rw [hlenMaskPtr]; decide)).1.mpr fun idx hlo hhi => by
          change idx.bytes.toNat < 2 at hhi
          exact hallInit idx hlo (by omega)
      have hsliceSub : pPtr.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 2)) =
          .ok #[0x20, 0x10] := by
        have hs := Allocation.getBytesUnchecked_subrange pPtr r08
          (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 8) (Size.ofBytes 2)
          #[0x20, 0x10, 0, 0, 0, 0, 0, 0] hend08 (by decide) (by decide) (by decide) (by decide)
          hrawBytes
        exact hs.trans (by decide)
      change pPtr.readScalar ⟨.little, .w64⟩ (allocRange Size.ZERO (Size.ofBytes 2)) false = _
      rw [Allocation.readScalar_int_of_bytes pPtr ⟨.little, .w64⟩ _ #[0x20, 0x10]
        hinitSub hsliceSub (by decide) (Or.inl rfl)]
      rfl
    · have hinitSub : pPtr.initializationMask.isRangeInitialized
          (allocRange (Size.ofBytes 6) (Size.ofBytes 2)) = .ok (.ok ()) :=
        (InitMask.WriteProof.isRangeInitialized_nonempty_iff pPtr.initializationMask _
          (Size.ofBytes 8) hwfPtr (by decide) (by decide)
          (by rw [hlenMaskPtr]; decide)).1.mpr fun idx hlo hhi => by
          change 6 ≤ idx.bytes.toNat at hlo
          change idx.bytes.toNat < 8 at hhi
          exact hallInit idx (by omega) hhi
      have hsliceSub : pPtr.getBytesUnchecked (allocRange (Size.ofBytes 6) (Size.ofBytes 2)) =
          .ok #[0x10, 0x20] := by
        have hs := Allocation.getBytesUnchecked_subrange pPtr r08
          (allocRange (Size.ofBytes 6) (Size.ofBytes 2)) (Size.ofBytes 8) (Size.ofBytes 8)
          #[0, 0, 0, 0, 0, 0, 0x10, 0x20] hend08 (by decide) (by decide) (by decide) (by decide)
          hrawBytes
        exact hs.trans (by decide)
      change pPtr.readScalar ⟨.big, .w64⟩ (allocRange (Size.ofBytes 6) (Size.ofBytes 2)) false = _
      rw [Allocation.readScalar_int_of_bytes pPtr ⟨.big, .w64⟩ _ #[0x10, 0x20]
        hinitSub hsliceSub (by decide) (Or.inl rfl)]
      rfl
  exact ⟨p0, pPtr, hp0, hwPtr, hnotEmpty, hstrip, htransmute8, hsub⟩

end LeanMiriMemoryLemmasTests.MemoryWitnesses

/-! ## 3. `ValidationRankCert` witnesses -/

namespace LeanMiriMemoryLemmasTests.RankCert
open Miri.ABI Miri.Memory Miri.Memory.Validity Miri.Interpreter
open Miri.Interpreter.ValidityVisitor (M Key Session)
open LeanMiriSpec.ValidationRankCert

/-! ### 3a. 150-level nested single-field wrapper & `Anneal.MirFuelFree` bridge -/

theorem wit_wrapper150_noFuel :
    wrapperWalk.walkNoFuel (wrapperRoot 150) () () = .ok () () :=
  wrapper150_noFuel

theorem wit_wrapper150_fuel151_ok :
    resultOk (wrapperWalk.walkFuel 151 (wrapperRoot 150) () ()) = true := by
  decide +kernel

theorem wit_wrapper150_fuel150_exhausted :
    resultExhausted "validity traversal fuel"
      (wrapperWalk.walkFuel 150 (wrapperRoot 150) () ()) = true := by
  decide +kernel

theorem wit_wrapper150_small_fuel_exhausts (fuel : Nat) (hfuel : fuel < 150) :
    wrapperWalk.walkFuel fuel (wrapperRoot 150) () () =
      .error (.resourceExhaustion "validity traversal fuel") () :=
  wrapper150_small_fuel_exhausts fuel (by omega)

theorem wit_wrapper150_fuel151_eq_noFuel :
    wrapperWalk.walkFuel 151 (wrapperRoot 150) () =
      wrapperWalk.walkNoFuel (wrapperRoot 150) () :=
  wrapper150_fuel151_eq_noFuel

/-- General adequacy at the canonical static bound `order root + 1 = 452`. -/
theorem wit_wrapper150_fuel452_adequacy :
    wrapperWalk.walkFuel 452 (wrapperRoot 150) () =
      wrapperWalk.walkNoFuel (wrapperRoot 150) () :=
  wrapperWalk.walkFuel_eq_walkNoFuel _ wrapperWalk_descendsOn 452 _ () trivial (by decide)

/-- `Anneal.MirFuelFree` bridge at a budget well above the canonical bound. -/
theorem wit_wrapper150_mirFuelFree_bridge :
    wrapperWalk.walkFuel 1000 (wrapperRoot 150) () =
      wrapperWalk.walkNoFuel (wrapperRoot 150) () :=
  walkFuel_eq_walkNoFuel_of_wpCoalBounded wrapperWalk _ wrapperWalk_descendsOn 1000 _ () trivial
    PUnit.unit (rankCountdown_canonical _ 1000 PUnit.unit (by decide))

/-- The rank countdown does not converge at the root's order (fuel must strictly exceed it). -/
theorem wit_wrapper150_countdown_tight :
    ¬ Anneal.ITreeWP.wpCoalBounded 451 emptyWP rankCountdown (fun _ _ => True)
      (wrapperWalk.order (wrapperRoot 150)) PUnit.unit := by
  rw [rankCountdown_converges_iff]
  decide

/-! ### 3b. Static `LayoutGraph` certificates (including missing-child unclosed-cycle rejection) -/

def nodeA : LocalLayout := ⟨1, wrapperLayout⟩
def nodeB : LocalLayout := ⟨2, wrapperLayout⟩
def nodeC : LocalLayout := ⟨3, wrapperLayout⟩

/-- `C ↦ B ↦ A` (closed acyclic chain). -/
def chainGraph : LayoutGraph where
  nodes := [nodeC, nodeB, nodeA]
  children := fun p => if p.ty = 3 then [nodeB] else if p.ty = 2 then [nodeA] else []

/-- `A ↦ B ↦ A` (closed 2-cycle). -/
def cycleGraph : LayoutGraph where
  nodes := [nodeA, nodeB]
  children := fun p => if p.ty = 1 then [nodeB] else [nodeA]

/-- Adversarial unclosed cycle: `C ↦ B ↦ A ↦ C`, where `nodeA` is omitted from `nodes`!
`checkCert` must reject because `B`'s child `nodeA` is missing from `nodes`. -/
def unclosedCycleGraph : LayoutGraph where
  nodes := [nodeC, nodeB]
  children := fun p => if p.ty = 3 then [nodeB] else if p.ty = 2 then [nodeA] else [nodeC]

def chainCert : ValidationRankCert := ⟨[(1, 1), (2, 2), (3, 3)]⟩

/-- Equal ranks: same-phase children do not descend. -/
def flatCert : ValidationRankCert := ⟨[(1, 5), (2, 5), (3, 5)]⟩

/-- Inverted ranks: children are larger than their parents. -/
def invertedCert : ValidationRankCert := ⟨[(1, 3), (2, 2), (3, 1)]⟩

theorem wit_chainCert_accepts : checkCert chainCert chainGraph = true := by decide +kernel
theorem wit_chainGraph_closed : chainGraph.closed = true := by decide +kernel
theorem wit_flatCert_rejects : checkCert flatCert chainGraph = false := by decide +kernel
theorem wit_invertedCert_rejects : checkCert invertedCert chainGraph = false := by decide +kernel
theorem wit_cycleGraph_rejects : checkCert chainCert cycleGraph = false := by decide +kernel
theorem wit_unclosedCycleGraph_not_closed : unclosedCycleGraph.closed = false := by decide +kernel
theorem wit_unclosedCycleGraph_rejects : checkCert chainCert unclosedCycleGraph = false := by
  decide +kernel

/-- Cyclic graphs are rejected for every rank table. -/
theorem wit_cycleGraph_rejects_any_cert (cert : ValidationRankCert) :
    checkCert cert cycleGraph = false :=
  checkCert_rejects_cycle cert cycleGraph nodeA
    (Reach.trans (Reach.edge (p := nodeA) (c := nodeB) (by decide +kernel) (by decide +kernel))
      (Reach.edge (p := nodeB) (c := nodeA) (by decide +kernel) (by decide +kernel)))

/-- Certified adequacy on the static chain at the canonical bound `order C + 1 = 11`. -/
theorem wit_certified_chain_adequacy :
    (ofGraph chainCert chainGraph fun _ acc => (pure acc : M Unit Unit)).walkFuel 11 nodeC () =
      (ofGraph chainCert chainGraph fun _ acc => (pure acc : M Unit Unit)).walkNoFuel nodeC () :=
  certified_walkFuel_eq_walkNoFuel chainCert chainGraph _ (by decide +kernel)
    nodeC (by decide +kernel) () 11 (by decide +kernel)

/-! ### 3c. Schema 17 `Decoder.lean` type-table rank validator (positive & negative cases) -/

/-- Recursive linked list `struct ListNode { head: u32, next: &ListNode }` plus a coroutine
saving `(u32, ListNode)`: pointer indirection (`ty 1`) decouples the cycle in `ListNode` (`ty 2`),
matching `lean-miri#90` `Decoder.lean` Schema 17 validation. -/
def schema17GoodTable : List Schema17TypeNode := [
  { id := 0, validationRank := 0, shape := .primitive },
  { id := 1, validationRank := 0, shape := .pointerIndirection 2 },
  { id := 2, validationRank := 1, shape := .adt [[0, 1]] },
  { id := 3, validationRank := 2, shape := .coroutine [0] #[0, 2] [[0, 1]] }
]

/-- Illegal by-value self-cycle `struct Bad { selfField: Bad }`. -/
def schema17SelfCycle : List Schema17TypeNode := [
  { id := 0, validationRank := 5, shape := .adt [[0]] }
]

/-- Illegal reference to an undeclared validation child `TyId = 99`. -/
def schema17MissingChild : List Schema17TypeNode := [
  { id := 0, validationRank := 1, shape := .tuple [99] }
]

/-- Illegal out-of-bounds coroutine `savedTypes` index `5`. -/
def schema17BadSavedType : List Schema17TypeNode := [
  { id := 0, validationRank := 1, shape := .coroutine [] #[0] [[5]] }
]

/-- Illegal `normalizedType` alias mismatch (`ty 0` claims rank `0` while normalizing to `ty 1` of rank `2`). -/
def schema17AliasMismatch : List Schema17TypeNode := [
  { id := 0, validationRank := 0, normalizedType := 1, shape := .primitive },
  { id := 1, validationRank := 2, shape := .primitive }
]

theorem wit_schema17_pointer_recursive_ok :
    checkSchema17Table schema17GoodTable = .ok () := by
  decide +kernel

theorem wit_schema17_pointer_recursive_acyclic (p : Schema17TypeNode) :
    ¬ Schema17Reach schema17GoodTable p p :=
  checkSchema17Table_acyclic schema17GoodTable wit_schema17_pointer_recursive_ok p

theorem wit_schema17_self_cycle_rejected :
    checkSchema17Table schema17SelfCycle =
      .error "validation rank does not decrease from type 0 to 0" := by
  decide +kernel

theorem wit_schema17_missing_child_rejected :
    checkSchema17Table schema17MissingChild = .error "missing validation child 99" := by
  decide +kernel

theorem wit_schema17_bad_saved_type_rejected :
    checkSchema17Table schema17BadSavedType = .error "missing coroutine saved type" := by
  decide +kernel

theorem wit_schema17_alias_mismatch_rejected :
    (checkSchema17Table schema17AliasMismatch).isOk = false := by
  decide +kernel

/-! ### 3d. `visitOrder` (`(if isSized then 0 else 1, layoutOrder)`) & `dyn Trait` dynamic unpacking -/

/-- Unsized `dyn Trait` layout (`ty = 0`, `backendRepr = .Memory (sized := false)`, `isSized = false`,
`typeRank = 0`, `layoutOrder = 1`, `visitOrder = (1, 1)`). -/
def unsizedDynTrait : LocalLayout :=
  ⟨0, { wrapperLayout with backendRepr := .Memory (sized := false) }⟩

/-- Concrete sized implementor (`ty = 50`, `isSized = true`, `typeRank = 50`, `layoutOrder = 151`,
`visitOrder = (0, 151)`): higher `layoutOrder` than `unsizedDynTrait`, but strictly smaller `visitOrder`! -/
def concreteImpl50 : LocalLayout := ⟨50, wrapperLayout⟩

/-- Sized primitive leaf field (`ty = 0`, `isSized = true`, `layoutOrder = 0`, `visitOrder = (0, 0)`). -/
def concreteLeaf0 : LocalLayout :=
  ⟨0, { wrapperLayout with fields := .Primitive }⟩

def dynUnpackChildren (p : LocalLayout) : Array LocalLayout :=
  if !p.layout.isSized then #[concreteImpl50]
  else if p.ty == 50 then #[concreteLeaf0]
  else #[]

/-- Lexicographic `visitOrder` walk (`lean-miri#90` `ValidityVisitor.visit`) over `dyn Trait` unpacking. -/
def dynUnpackLexWalk : VisitLexWalk Unit LocalLayout Nat where
  typeRank := id
  layoutOf := id
  pre := fun _ n => pure (n + 1)
  children := fun p => pure (dynUnpackChildren p)

/-- Naive `layoutOrder`-only `RankedWalk` over the exact same `dyn Trait` unpacking projection. -/
def dynUnpackNaiveRankedWalk : RankedWalk Unit LocalLayout Nat where
  typeRank := id
  layoutOf := id
  pre := fun _ n => pure (n + 1)
  children := fun p => pure (dynUnpackChildren p)

/-- `concreteImpl50` has strictly larger `layoutOrder` (`151 > 1`) yet strictly smaller `visitOrder`
(`(0, 151) <ₗₑₓ (1, 1)`) than `unsizedDynTrait`. -/
theorem wit_dynTrait_visitOrder_descends :
    layoutOrder id unsizedDynTrait < layoutOrder id concreteImpl50 ∧
      VisitOrderLt (visitOrder id concreteImpl50) (visitOrder id unsizedDynTrait) :=
  ⟨by decide +kernel, visitOrder_lt_of_unsized_unpack id unsizedDynTrait concreteImpl50 rfl rfl⟩

/-- `VisitLexWalk.walkNoFuel` succeeds across unsized-to-higher-rank-sized `dyn Trait` unpacking,
visiting all 3 nodes (`0 ↦ 1 ↦ 2 ↦ 3`). -/
theorem wit_dynTrait_visitLex_noFuel_ok :
    (match dynUnpackLexWalk.walkNoFuel unsizedDynTrait 0 () with
     | .ok n () => n == 3
     | .error _ _ => false) = true := by
  rw [← dynUnpackLexWalk.walkRank_eq_walkNoFuel]
  decide +kernel

/-- `VisitLexWalk.walkFuel_eq_walkNoFuel` adequacy across `dyn Trait` unpacking (`maxSizedOrder = 151`,
`effectiveOrder 151 unsizedDynTrait = 153 < 154`). -/
theorem wit_dynTrait_visitLex_fuel_eq_noFuel :
    dynUnpackLexWalk.walkFuel 154 unsizedDynTrait 0 =
      dynUnpackLexWalk.walkNoFuel unsizedDynTrait 0 := by
  have hd : dynUnpackLexWalk.DescendsLexOn
      (fun p => p = unsizedDynTrait ∨ p = concreteImpl50 ∨ p = concreteLeaf0) 151 := by
    intro p hp s cs s' hch c hc
    cases hch
    rcases hp with rfl | rfl | rfl
    · have hc_eq : c = concreteImpl50 := by
        have : dynUnpackChildren unsizedDynTrait = #[concreteImpl50] := by decide +kernel
        rw [this] at hc
        simpa using hc
      subst hc_eq
      exact ⟨Or.inr (Or.inl rfl),
        visitOrder_lt_of_unsized_unpack id unsizedDynTrait concreteImpl50 rfl rfl,
        fun _ => by decide +kernel⟩
    · have hc_eq : c = concreteLeaf0 := by
        have : dynUnpackChildren concreteImpl50 = #[concreteLeaf0] := by decide +kernel
        rw [this] at hc
        simpa using hc
      subst hc_eq
      exact ⟨Or.inr (Or.inr rfl),
        visitOrder_lt_of_same_sized id concreteImpl50 concreteLeaf0 rfl (by decide +kernel),
        fun _ => by decide +kernel⟩
    · have : dynUnpackChildren concreteLeaf0 = #[] := by decide +kernel
      rw [this] at hc
      nomatch hc
  exact dynUnpackLexWalk.walkFuel_eq_walkNoFuel _ 151 hd 154 unsizedDynTrait 0
    (Or.inl rfl) (by decide +kernel)

/-- Conversely, a naive `layoutOrder`-only `RankedWalk` FALSELY REJECTS valid `dyn Trait` unpacking
to a higher-rank concrete implementor with `.invalidProgram`. -/
theorem wit_dynTrait_naiveLayoutOrder_falsely_rejects :
    dynUnpackNaiveRankedWalk.walkNoFuel unsizedDynTrait 0 () =
      .error (.invalidProgram "validity projection does not descend") () :=
  dynUnpackNaiveRankedWalk.walkNoFuel_rejects_nondescending unsizedDynTrait 0 1 concreteImpl50 []
    () () () #[concreteImpl50] rfl rfl rfl (by decide +kernel)

/-- Conversely, an illegal sized-to-unsized projection IS rejected by `VisitLexWalk.walkNoFuel`. -/
def badSizedToUnsizedLexWalk : VisitLexWalk Unit LocalLayout Unit where
  typeRank := id
  layoutOf := id
  pre := fun _ acc => pure acc
  children := fun _ => pure #[unsizedDynTrait]

theorem wit_sized_to_unsized_lex_rejects :
    badSizedToUnsizedLexWalk.walkNoFuel concreteImpl50 () () =
      .error (.invalidProgram "validity projection does not descend") () :=
  badSizedToUnsizedLexWalk.walkNoFuel_rejects_nondescending concreteImpl50 () () unsizedDynTrait []
    () () () #[unsizedDynTrait] rfl rfl rfl
    (by
      intro hlt
      have ⟨hsz, _⟩ := (badSizedToUnsizedLexWalk.vOrder_lt_of_sized (p := concreteImpl50) rfl).mp hlt
      exact Bool.noConfusion hsz)

/-! ### 3e. 150-level witnesses on unmodified vendored `ValidityVisitor.{unionRanges, visit}` -/

theorem wit_deepUnion150_noFuel :
    (match realUnionRangesNoFuel deepUnionHooks () id (deepUnionLayout 150) Size.ZERO .empty () with
     | .ok ranges () => ranges.toArray == #[allocRange Size.ZERO (Size.ofBytes 1)]
     | .error _ _ => false) = true :=
  deepUnion150_noFuel

theorem wit_deepUnion150_vendored :
    (match ValidityVisitor.unionRanges deepUnionHooks () 151
        (deepUnionLayout 150) Size.ZERO .empty () with
     | .ok ranges () => ranges.toArray == #[allocRange Size.ZERO (Size.ofBytes 1)]
     | .error _ _ => false) = true ∧
    resultExhausted "union layout traversal fuel"
      (ValidityVisitor.unionRanges deepUnionHooks () 150
        (deepUnionLayout 150) Size.ZERO .empty ()) = true :=
  deepUnion150_vendored

theorem deepUnionHooks_descend :
    UnionHooksDescend deepUnionHooks () id (fun p => p = deepUnionLayout p.ty) := by
  intro layout hgood _hzst
  refine ⟨?_, ?_⟩
  · intro hnotPrim idx s child s' hm
    simp only [deepUnionHooks, minimalValidityHooks, pure, EStateM.pure,
      EStateM.Result.ok.injEq] at hm
    obtain ⟨rfl, -⟩ := hm
    cases hty : layout.ty with
    | zero =>
      rw [hgood, hty] at hnotPrim
      exact False.elim (hnotPrim rfl)
    | succ n =>
      refine ⟨by simp [deepUnionLayout], ?_⟩
      exact layoutOrder_lt_of_rank_lt id layout (deepUnionLayout n)
        (by simp [deepUnionLayout, hty])
  · rintro ⟨tag, enc, field, vs, hvs⟩
    rw [hgood] at hvs
    simp [deepUnionLayout, wrapperLayout] at hvs

/-- Direct adequacy between unmodified vendored `ValidityVisitor.unionRanges` and
`realUnionRangesNoFuel` on the 150-level nested union (`fuel = 452 > 451 = layoutOrder`). -/
theorem wit_deepUnion150_vendored_eq_noFuel :
    ValidityVisitor.unionRanges deepUnionHooks () 452 (deepUnionLayout 150) Size.ZERO .empty =
      realUnionRangesNoFuel deepUnionHooks () id (deepUnionLayout 150) Size.ZERO .empty :=
  vendored_unionRanges_eq_noFuel deepUnionHooks () id _ deepUnionHooks_descend
    452 (deepUnionLayout 150) Size.ZERO .empty rfl (by decide +kernel)

/-- `Anneal.MirFuelFree` `wpCoalBounded` bridge directly into unmodified vendored
`ValidityVisitor.unionRanges` at depth 150 (`fuel = 1000`). -/
theorem wit_deepUnion150_vendored_mirFuelFree_bridge :
    ValidityVisitor.unionRanges deepUnionHooks () 1000 (deepUnionLayout 150) Size.ZERO .empty =
      realUnionRangesNoFuel deepUnionHooks () id (deepUnionLayout 150) Size.ZERO .empty :=
  vendored_unionRanges_eq_noFuel_of_wpCoalBounded deepUnionHooks () id _ deepUnionHooks_descend
    1000 (deepUnionLayout 150) Size.ZERO .empty rfl PUnit.unit
    (rankCountdown_canonical _ 1000 PUnit.unit (by decide +kernel))

theorem wit_deepPattern150_vendored_visit :
    let root : RuntimePlace CtfeProvenance :=
      ⟨.memory ⟨⟨Size.ZERO, none⟩, .none, none⟩, ⟨150, wrapperLayout⟩⟩
    let init : Session CtfeProvenance :=
      { path := ⟨"Root", #[]⟩, flags := ⟨false, false⟩, ctfeMode := none,
        refTracking := none, dataBytes := none }
    resultOk (ValidityVisitor.visit deepPatternHooks () 151 init root ()) = true ∧
    resultExhausted "validity traversal fuel"
      (ValidityVisitor.visit deepPatternHooks () 150 init root ()) = true :=
  deepPattern150_vendored_visit

/-! ### 3f. Dynamic hook-boundary violations, `unionWrapper`, and LIFO pointee draining -/

/-- A projection hook that returns the place itself (a by-value cycle). -/
def loopWalk : RankedWalk Unit LocalLayout Unit where
  typeRank := id
  layoutOf := id
  pre := fun _ acc => pure acc
  children := fun p => pure #[p]

/-- The fuel-free traversal rejects the non-descending projection deterministically. -/
theorem wit_loopWalk_rejects :
    loopWalk.walkNoFuel nodeA () () =
      .error (.invalidProgram "validity projection does not descend") () :=
  loopWalk.walkNoFuel_rejects_nondescending nodeA () () nodeA [] () () () #[nodeA] rfl rfl rfl
    (Nat.lt_irrefl _)

/-- The vendored-style fuel traversal cannot tell the cycle from a deep value: it only exhausts. -/
theorem wit_loopWalk_fuel64_exhausts :
    resultExhausted "validity traversal fuel" (loopWalk.walkFuel 64 nodeA () ()) = true := by
  decide +kernel

/-- The union-range instance over the 150-level wrapper chain. -/
def unionWrapper : UnionWalk Unit where
  typeRank := id
  layoutOf := Prod.fst
  pre := fun _ acc => pure acc
  children := fun p => pure ((wrapperChildren p.1).map fun child => (child, p.2))
  descendMsg := "union layout projection does not descend"
  fuelMsg := "union layout traversal fuel"

theorem wit_unionWrapper150_ok :
    resultOk (unionRangesNoFuel unionWrapper (wrapperRoot 150) Size.ZERO .empty ()) = true := by
  unfold unionRangesNoFuel
  rw [← RankedWalk.walkRank_eq_walkNoFuel]
  decide +kernel

/-- LIFO: the most recently tracked pointee is drained first. -/
theorem wit_drainPointees_lifo {P S : Type} (tracking : RefTracking (Key P) ValidationPath)
    (visitPointee : Key P → ValidationPath → M S Unit) (k₁ k₂ : Key P) (p₁ p₂ : ValidationPath) :
    drainPointees { tracking with todo := (tracking.todo.push (k₁, p₁)).push (k₂, p₂) } visitPointee =
      (do visitPointee k₂ p₂; visitPointee k₁ p₁; drainPointees tracking visitPointee) := by
  have h := drainPointees_push { tracking with todo := tracking.todo.push (k₁, p₁) } visitPointee k₂ p₂
  simp only at h
  rw [h, drainPointees_push]

end LeanMiriMemoryLemmasTests.RankCert

/-! ## 4. Module-wide standard-axiom audit -/

section TestAxiomAudit
open Lean Elab Command

/-- Verify that every declaration in `LeanMiriMemoryLemmasTests` depends strictly on standard Lean
axioms (`propext`, `Quot.sound`, `Classical.choice`) — zero `sorryAx`, zero `Lean.ofReduceBool`,
and zero `Lean.trustCompiler`. -/
elab "#assert_test_standard_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Quot.sound, ``Classical.choice]
  let mut count : Nat := 0
  for (c, _) in env.constants.map₂.toList do
    let root := c.getRoot.toString
    if root.startsWith "_aux_" && root.endsWith "_command#assert_test_standard_axioms__1" then
      continue
    if root.startsWith "_aux_" && root.endsWith "_command#assert_binder_parity__1" then
      continue
    count := count + 1
    let axs ← liftCoreM <| Lean.collectAxioms c
    for ax in axs do
      if !allowed.contains ax then
        logError m!"{c} depends on non-standard axiom {ax}"
  if count < 80 then
    logError m!"Expected at least 80 declarations in LeanMiriMemoryLemmasTests, got {count}"
  logInfo m!"LeanMiriMemoryLemmasTests module-wide audit: {count} declarations depend only on standard axioms"

#assert_test_standard_axioms
end TestAxiomAudit
