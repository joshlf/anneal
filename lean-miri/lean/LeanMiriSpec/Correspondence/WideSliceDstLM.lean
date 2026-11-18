/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.PtrLM3_1
import LeanMiriSpec.Correspondence.AllocLM2_1
import Miri.Interpreter.DynamicLayout
import Miri.Interpreter.PlaceDynamic
import Miri.Interpreter.Aggregate
import Miri.Interpreter.ScalarOps
import Miri.Interpreter.Cast
import Miri.Interpreter.Intrinsics
import Miri.Interpreter.Step

/-!
# Wide-Slice DST Correspondence (`LeanMiriSpec.Correspondence.WideSliceDstLM`)

Establishes the kernel-checked `LeanMiriSpec` correspondence between Anneal's
`Trusted.Rustc.V2026_06_01.MirSemantics` and vendored `Miri` (`lean-miri/vendor/Miri`)
for dynamically sized slice (`[T]`) and string slice (`str`) wide pointers:

1. **Part 1 — Wide-Slice `LeanMiriSpec` Hooks & State Relation Overlay (Conservative Extension)**:
   * 16-byte `BackendRepr.ScalarPair` wide-pointer layout (`widePointerLayoutData`) and
     unsized `[T]` / `str` pointee layout (`unsizedSliceLayoutData`), together with
     wide-slice `Miri.MIR.TyId` encoding (`strPointeeTyId`, `slicePointeeTyId`,
     `wideRawStrPtrTyId`, `wideRefStrPtrTyId`, `wideRawSlicePtrTyId`,
     `wideRefSlicePtrTyId`, `encodeTyIdWideSlice`, `translateTyWideSlice`,
     `layoutOfEncodedTyIdWideSlice`) that agrees identically with `encodeTyId` /
     `translateTy` on all non-wide-slice types (`encodeTyIdWideSlice_eq_encodeTyId`,
     `translateTyWideSlice_eq_translateTy`).
   * `WideSliceImmediateRel` (relating Anneal `.aggregate 0 [.ptr p 8, .scalar lenSc]`
     and provenance-free `.aggregate 0 [.scalar addrSc, .scalar lenSc]` to vendored
     `Miri.Interpreter.Immediate.scalarPair` / `Immediate.newPointerWithMeta` /
     `Immediate.newSlice`), `LocalRelWideSlice`, `FrameRelWideSlice`,
     `StateRelWideSlice`, and `StepRelWideSlice`.
   * Instantiations of vendored `Miri` hooks for wide-slice DST operations:
     - `annealDynamicLayoutHooksWideSlice` (`Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta`,
       `sizeAndAlignOfVal`, `alignmentFromMeta` with `maxSizeOfVal = Size.ofBytes 0x7fff_ffff_ffff_ffff`),
     - `annealPlaceProjectionHooksWideSlice` (`Miri.Interpreter.PlaceDynamic.{length, index, constantIndex, subslice, project, evalPlace}`),
     - `annealScalarOpsHooksWideSlice` (`Miri.Interpreter.ScalarOps.unary .PtrMetadata`),
     - `annealCastHooksWideSlice` (`Miri.Interpreter.Cast.cast` / `Cast.ptrToPtr`),
     - `annealAggregateHooksWideSlice` (`Miri.Interpreter.writeAggregate` on `AggregateKind.RawPtr`),
     - `annealIntrinsicHooksWideSlice` and `annealCallHooksWideSlice`
       (`Miri.Interpreter.Intrinsics.eval` on `"size_of_val"` and `"align_of_val"` via
       `Miri.Interpreter.Call.evalCallTerminator`),
     - `annealStepHooksWideSlice` conservative overlay over `annealStepHooks`, with
       `step_wideSlice_eq_annealStepHooks_of_bodyFree`.

2. **Part 2 — Lockstep Simulation Theorems Against Vendored `Miri`**:
   * `ptr::from_raw_parts(_mut)` / `ptr::slice_from_raw_parts(_mut)` (`Rvalue.aggregate (.rawPtr pointeeTy mutability) [dataOp, metaOp]`)
     lockstep simulation against `Miri.Interpreter.writeAggregate` (`Immediate.newPointerWithMeta`),
   * `ptr::metadata` (`Rvalue.unaryOp .ptrMetadata op`) lockstep simulation against
     `Miri.Interpreter.ScalarOps.unary .PtrMetadata` (including dangling/OOB/disabled
     pointers without dereferencing memory),
   * `to_raw_parts` (`Rvalue.cast .ptrToPtr op targetTy` wide-to-thin and wide-to-wide)
     lockstep simulation against `Miri.Interpreter.Cast.ptrToPtr` / `Cast.cast` and the
     `to_raw_parts` → `from_raw_parts` round-trip identity theorem,
   * `slice::from_raw_parts(_mut)` (`&*p`, `&mut *p`, `Rvalue.len (*s)`, `(*s)[i]`,
     and `&(*s)[from..to]`) lockstep simulation against `Miri.Interpreter.PlaceDynamic.{length, index, constantIndex, subslice}`,
   * `core::intrinsics::size_of_val` (`size_of_val_raw`) and `core::intrinsics::align_of_val`
     (`align_of_val_raw`) lockstep simulation against `Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta` /
     `sizeAndAlignOfVal` and `Miri.Interpreter.Intrinsics.eval` — proving both normal
     value agreement (`elemSz * len < 2^63`) and exact `InvalidMeta(SliceTooBig)` UB
     equivalence (`elemSz * len ≥ 2^63`) across `[T]`, `str`, empty (`len = 0`), and
     ZST (`elemSz = 0`) slices.

3. **Part 3 — Concrete Real-Step Witnesses & Stage-1 Divergence Witness**:
   * Multi-step execution witnesses of `stepMirFn` and `Miri.Interpreter.Step.step`
     for `[u32]`, `str`, ZST `[()]`, exact `isize::MAX = 2^63 - 1` boundary (`len = 2^61 - 1`
     vs. `len = 2^61` on `[u32]`, `len = 2^63` on `str`), dangling metadata vs. OOB index UB,
     and the documented Stage-1 `.scalar`-address `size_of_val` / `align_of_val` divergence
     (`div_stage1_scalarAddr_wideSlice_sizeOfVal_alignOfVal`).
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## Part 1. Wide-Slice Layouts, `TyId` Encoding, State Relations & Hook Overlay -/

/-- Construct the 16-byte `BackendRepr.ScalarPair` layout of a 64-bit wide
slice/str pointer (`*const [T]`, `*mut [T]`, `&[T]`, `&mut [T]`, `*const str`,
`*mut str`, `&str`, `&mut str`), pairing an 8-byte data pointer scalar at byte
offset `0` with an 8-byte `usize` length scalar at byte offset `8`. -/
def widePointerLayoutData (nonNull : Bool := false) : Miri.ABI.LayoutData :=
  let ptrPrim : Miri.ABI.Primitive := .Pointer Miri.ABI.AddressSpace.ZERO
  let ptrRange : Miri.ABI.WrappingRange :=
    { start := BitVec.ofNat 128 (if nonNull then 1 else 0)
      «end» := BitVec.ofNat 128 ((2 ^ 64) - 1) }
  let ptrScalar : Miri.ABI.Scalar := .Initialized (value := ptrPrim) (validRange := ptrRange)
  let usizePrim : Miri.ABI.Primitive := .Int .I64 false
  let usizeRange : Miri.ABI.WrappingRange :=
    { start := 0, «end» := BitVec.ofNat 128 ((2 ^ 64) - 1) }
  let usizeScalar : Miri.ABI.Scalar := .Initialized (value := usizePrim) (validRange := usizeRange)
  { fields := .Arbitrary #[Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 8] #[0, 1]
    variants := .Single 0
    backendRepr := .ScalarPair (a := ptrScalar) (b := usizeScalar) (bOffset := Miri.ABI.Size.ofBytes 8)
    largestNiche := none
    uninhabited := false
    align := ⟨Miri.ABI.Align.EIGHT⟩
    size := Miri.ABI.Size.ofBytes 16
    maxReprAlign := none
    unadjustedAbiAlign := Miri.ABI.Align.EIGHT
    reprC := false
    randomizationSeed := 0 }

@[simp]
theorem widePointerLayoutData_isSized (nonNull : Bool) :
    (widePointerLayoutData nonNull).isSized = true := rfl

@[simp]
theorem widePointerLayoutData_size (nonNull : Bool) :
    (widePointerLayoutData nonNull).size = Miri.ABI.Size.ofBytes 16 := rfl

/-- Construct the unsized `BackendRepr.Memory (sized := false)` pointee layout
for `[T]` or `str` with element layout `elemLay`. -/
def unsizedSliceLayoutData (elemLay : Miri.ABI.LayoutData) : Miri.ABI.LayoutData :=
  { fields := .Array elemLay.size 0
    variants := .Single 0
    backendRepr := .Memory (sized := false)
    largestNiche := none
    uninhabited := false
    align := elemLay.align
    size := Miri.ABI.Size.ZERO
    maxReprAlign := none
    unadjustedAbiAlign := elemLay.unadjustedAbiAlign
    reprC := false
    randomizationSeed := 0 }

@[simp]
theorem unsizedSliceLayoutData_isSized (elemLay : Miri.ABI.LayoutData) :
    (unsizedSliceLayoutData elemLay).isSized = false := rfl

/-- Canonical `Miri.MIR.TyId` for the unsized `str` pointee type (`2000`). -/
def strPointeeTyId : Miri.MIR.TyId := 2000

/-- Canonical `Miri.MIR.TyId` for an unsized slice pointee type `[T]` whose
element `RigidTy` has scalar/pointer/unit `TyId` `elemId < 100` (`2100 + elemId`). -/
def slicePointeeTyId (elemId : Miri.MIR.TyId) : Miri.MIR.TyId := 2100 + elemId

/-- Canonical `Miri.MIR.TyId` for `*const str` / `*mut str` (`3000`). -/
def wideRawStrPtrTyId : Miri.MIR.TyId := 3000

/-- Canonical `Miri.MIR.TyId` for `&str` / `&mut str` (`3001`). -/
def wideRefStrPtrTyId : Miri.MIR.TyId := 3001

/-- Canonical `Miri.MIR.TyId` for `*const [T]` / `*mut [T]` (`3100 + elemId`). -/
def wideRawSlicePtrTyId (elemId : Miri.MIR.TyId) : Miri.MIR.TyId := 3100 + elemId

/-- Canonical `Miri.MIR.TyId` for `&[T]` / `&mut [T]` (`3200 + elemId`). -/
def wideRefSlicePtrTyId (elemId : Miri.MIR.TyId) : Miri.MIR.TyId := 3200 + elemId

/-- Encode a slice element `RigidTy` into a scalar/pointer/ZST `TyId < 100`
(defaulting to `51` for `()`). -/
def encodeSliceElemTyId (elemKind : RigidTy) : Miri.MIR.TyId :=
  (encodeScalarRigidTy elemKind).getD 51

/-- Whether `ty` is an unsized `[T]` / `str` pointee or a wide pointer/reference
to `[T]` / `str`. -/
def isWideSliceOrPointeeTy (ty : Ty) : Bool :=
  match ty.kind with
  | .str | .slice _
  | .rawPtr _ .str | .rawPtr _ (.slice _)
  | .ref _ .str | .ref _ (.slice _) => true
  | _ => false

/-- Wide-slice-aware `Miri.MIR.TyId` encoding: assigns injective `2000..3299`
IDs to `str`, `[T]`, `*const/*mut str`, `&/&mut str`, `*const/*mut [T]`, and
`&/&mut [T]`, and delegates every other `Ty` unchanged to `encodeTyId`. -/
def encodeTyIdWideSlice (ty : Ty) : Miri.MIR.TyId :=
  match ty.kind with
  | .str => strPointeeTyId
  | .slice elemKind => slicePointeeTyId (encodeSliceElemTyId elemKind)
  | .rawPtr _ .str => wideRawStrPtrTyId
  | .ref _ .str => wideRefStrPtrTyId
  | .rawPtr _ (.slice elemKind) => wideRawSlicePtrTyId (encodeSliceElemTyId elemKind)
  | .ref _ (.slice elemKind) => wideRefSlicePtrTyId (encodeSliceElemTyId elemKind)
  | _ => encodeTyId ty

theorem encodeTyIdWideSlice_eq_encodeTyId {ty : Ty}
    (h : isWideSliceOrPointeeTy ty = false) :
    encodeTyIdWideSlice ty = encodeTyId ty := by
  rcases ty with ⟨kind, lIdx⟩
  cases kind with
  | str => cases h
  | slice _ => cases h
  | rawPtr m p =>
      cases p with
      | str => cases h
      | slice _ => cases h
      | _ => rfl
  | ref m p =>
      cases p with
      | str => cases h
      | slice _ => cases h
      | _ => rfl
  | _ => rfl

/-- Wide-slice-aware `LocalLayout` translation: assigns `unsizedSliceLayoutData`
to `str` and `[T]`, `widePointerLayoutData false` to `*const/*mut [T]` and
`*const/*mut str`, `widePointerLayoutData true` to `&/&mut [T]` and `&/&mut str`,
and delegates every other `Ty` unchanged to `translateTy`. -/
def translateTyWideSlice (ty : Ty) (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.LocalLayout :=
  match ty.kind with
  | .str =>
      let u8Lay := scalarLayoutData 1 false
      { ty := strPointeeTyId, layout := unsizedSliceLayoutData u8Lay }
  | .slice elemKind =>
      let elemId := encodeSliceElemTyId elemKind
      let elemLay := (scalarLayoutOfRigidTy elemKind).getD zstLayoutData
      { ty := slicePointeeTyId elemId, layout := unsizedSliceLayoutData elemLay }
  | .rawPtr _ .str =>
      { ty := wideRawStrPtrTyId, layout := widePointerLayoutData false }
  | .ref _ .str =>
      { ty := wideRefStrPtrTyId, layout := widePointerLayoutData true }
  | .rawPtr _ (.slice elemKind) =>
      let elemId := encodeSliceElemTyId elemKind
      { ty := wideRawSlicePtrTyId elemId, layout := widePointerLayoutData false }
  | .ref _ (.slice elemKind) =>
      let elemId := encodeSliceElemTyId elemKind
      { ty := wideRefSlicePtrTyId elemId, layout := widePointerLayoutData true }
  | _ => translateTy ty layouts

theorem translateTyWideSlice_eq_translateTy {ty : Ty} (layouts : LayoutTable)
    (h : isWideSliceOrPointeeTy ty = false) :
    translateTyWideSlice ty layouts = translateTy ty layouts := by
  rcases ty with ⟨kind, lIdx⟩
  cases kind with
  | str => cases h
  | slice _ => cases h
  | rawPtr m p =>
      cases p with
      | str => cases h
      | slice _ => cases h
      | _ => rfl
  | ref m p =>
      cases p with
      | str => cases h
      | slice _ => cases h
      | _ => rfl
  | _ => rfl

/-- Reconstruct a `LocalLayout` from an encoded `Miri.MIR.TyId` (supporting both
the wide-slice `2000..3299` range and all `layoutOfEncodedTyId` IDs). -/
def layoutOfEncodedTyIdWideSlice (tyId : Miri.MIR.TyId)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.LocalLayout :=
  if tyId == strPointeeTyId then
    { ty := strPointeeTyId, layout := unsizedSliceLayoutData (scalarLayoutData 1 false) }
  else if 2100 ≤ tyId && tyId < 2200 then
    let elemId := tyId - 2100
    let elemLay := (layoutOfEncodedTyId elemId layouts).layout
    { ty := tyId, layout := unsizedSliceLayoutData elemLay }
  else if tyId == wideRawStrPtrTyId then
    { ty := wideRawStrPtrTyId, layout := widePointerLayoutData false }
  else if tyId == wideRefStrPtrTyId then
    { ty := wideRefStrPtrTyId, layout := widePointerLayoutData true }
  else if 3100 ≤ tyId && tyId < 3200 then
    { ty := tyId, layout := widePointerLayoutData false }
  else if 3200 ≤ tyId && tyId < 3300 then
    { ty := tyId, layout := widePointerLayoutData true }
  else
    layoutOfEncodedTyId tyId layouts

/-- Recover the pointee `Miri.MIR.TyId` from a thin or wide pointer/reference `TyId`. -/
def wideSlicePointeeTyId? (tyId : Miri.MIR.TyId) : Option Miri.MIR.TyId :=
  if tyId == wideRawStrPtrTyId || tyId == wideRefStrPtrTyId then
    some strPointeeTyId
  else if 3100 ≤ tyId && tyId < 3200 then
    some (slicePointeeTyId (tyId - 3100))
  else if 3200 ≤ tyId && tyId < 3300 then
    some (slicePointeeTyId (tyId - 3200))
  else
    rawPtrPointeeEncodedTyId? tyId

/-- Whether `tyId` encodes a wide slice or `str` pointer/reference (`3000..3299`). -/
def isWideSlicePtrTyId (tyId : Miri.MIR.TyId) : Bool :=
  tyId == wideRawStrPtrTyId || tyId == wideRefStrPtrTyId ||
    (3100 ≤ tyId && tyId < 3300)

/-- Whether `tyId` encodes a safe wide reference (`&str`, `&mut str`, `&[T]`,
`&mut [T]`, i.e., `3001` or `3200..3299`), as opposed to a raw wide pointer
(`*const/*mut str` = `3000`, `*const/*mut [T]` = `3100..3199`). -/
def isWideSafeRefTyId (tyId : Miri.MIR.TyId) : Bool :=
  tyId == wideRefStrPtrTyId || (3200 ≤ tyId && tyId < 3300)

/-- Classify an encoded `TyId` into `Miri.Interpreter.ScalarTypeClass`, extending
`classifyEncodedTyId` with wide-slice pointer/reference `TyId`s (`3000..3299`). -/
def classifyEncodedTyIdWideSlice (tyId : Miri.MIR.TyId) :
    Except Miri.Interpreter.StepError Miri.Interpreter.ScalarTypeClass :=
  if isWideSlicePtrTyId tyId then
    .ok .pointer
  else
    classifyEncodedTyId tyId

/-- Classify an encoded `TyId` into `Miri.Interpreter.CastTypeInfo`, extending
`castTypeInfoOfEncodedTyId` with wide raw pointers (`3000`, `3100..3199`), wide
references (`3001`, `3200..3299`), and unsized slice/str pointees (`2000`, `2100..2199`). -/
def castTypeInfoOfEncodedTyIdWideSlice (tyId : Miri.MIR.TyId) :
    Except Miri.Interpreter.StepError Miri.Interpreter.CastTypeInfo :=
  if tyId == wideRawStrPtrTyId then
    .ok (.rawPointer strPointeeTyId)
  else if tyId == wideRefStrPtrTyId then
    .ok (.reference strPointeeTyId)
  else if 3100 ≤ tyId && tyId < 3200 then
    .ok (.rawPointer (slicePointeeTyId (tyId - 3100)))
  else if 3200 ≤ tyId && tyId < 3300 then
    .ok (.reference (slicePointeeTyId (tyId - 3200)))
  else if tyId == strPointeeTyId then
    .ok (.slice 20)
  else if 2100 ≤ tyId && tyId < 2200 then
    .ok (.slice (tyId - 2100))
  else if tyId == 40 then
    .ok (.rawPointer strPointeeTyId)
  else
    castTypeInfoOfEncodedTyId tyId

/-! ### 1.2 Wide-Slice Value & Immediate Correspondence (`WideSliceImmediateRel`) -/

/-- Helper lemma: for any `x < 2^64`, `Miri.Memory.ScalarInt.tryFromUInt` at
8 bytes succeeds with `some msc` satisfying `ScalarRel ⟨x, 8⟩ msc`. -/
theorem tryFromUInt_u64_spec {x : Nat} (hx : x < 2 ^ 64) :
    ∃ msc : Miri.Memory.ScalarInt,
      Miri.Memory.ScalarInt.tryFromUInt (BitVec.ofNat 128 x) (Miri.ABI.Size.ofBytes 8) =
        .ok (some msc) ∧
      ScalarRel ⟨x, 8⟩ msc := by
  have hvalid8 : ValidScalarBytes 8 := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨msc, htr, hrel⟩ :=
    truncateFromUInt_translateSizeBytes_spec hvalid8 (BitVec.ofNat 128 x)
  have hmod128 : (BitVec.ofNat 128 x).toNat = x := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hmod64 : x % 2 ^ (8 * 8) = x :=
    Nat.mod_eq_of_lt hx
  rw [hmod128, hmod64] at htr hrel
  refine ⟨msc, ?_, hrel⟩
  unfold Miri.Memory.ScalarInt.tryFromUInt
  change (do
    let (result, overflow) ←
      Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofNat 128 x) (translateSizeBytes 8)
    if overflow then return none
    return some result) = .ok (some msc)
  rw [htr]
  have hne_f : (BitVec.ofNat 128 x != BitVec.ofNat 128 x) = false := bne_self_eq_false _
  rw [hne_f]
  rfl

/-- Helper lemma: for any 8-byte `ScalarRel lenSc mlen`, `toTargetUsize` at 8 bytes
returns `.ok (UInt64.ofNat lenSc.bits)`. -/
theorem fromScalarInt_toTargetUsize_u64 {lenSc : MirAst.ScalarInt} {mlen : Miri.Memory.ScalarInt}
    (hlen : ScalarRel lenSc mlen) (hlen_sz : lenSc.sizeBytes = 8) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) mlen).toTargetUsize
        (Miri.ABI.Size.ofBytes 8) =
      .ok (UInt64.ofNat lenSc.bits) := by
  have hlen_lt : lenSc.bits < 2 ^ 64 := by
    have hlt := hlen.canonical
    rw [hlen_sz] at hlt
    exact hlt
  have hbits : mlen.toBits (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 lenSc.bits) := by
    have hb := hlen.toBits_eq
    rw [hlen_sz] at hb
    exact hb
  have hlt128 : lenSc.bits < 2 ^ 128 := by omega
  have hbnat : (BitVec.ofNat 128 lenSc.bits).toNat = lenSc.bits := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt128]
  change (do
    let bits ← mlen.toBits (Miri.ABI.Size.ofBytes 8) |>.mapError _
    if bits.toNat > 18446744073709551615 then
      throw (Miri.Memory.ScalarError.integerConversionOverflow bits)
    return UInt64.ofNat bits.toNat) = .ok (UInt64.ofNat lenSc.bits)
  rw [hbits]
  change (if (BitVec.ofNat 128 lenSc.bits).toNat > 18446744073709551615 then
      Except.error (Miri.Memory.ScalarError.integerConversionOverflow (BitVec.ofNat 128 lenSc.bits))
    else Except.ok (UInt64.ofNat (BitVec.ofNat 128 lenSc.bits).toNat)) =
    Except.ok (UInt64.ofNat lenSc.bits)
  rw [hbnat]
  have hnot_gt : ¬ (lenSc.bits > 18446744073709551615) := by omega
  simp [hnot_gt]

/-- Value-level correspondence between Anneal wide-slice `Value`s and vendored
`Miri.Interpreter.Immediate AnnealProv`:
* `provenance`: Anneal `Value.aggregate 0 [.ptr p 8, .scalar lenSc]` relates to
  `Immediate.scalarPair (Scalar.fromPointer annealTargetDataLayout mptr) (.fromScalarInt mlen)`
  when `PtrRel allocMap p mptr` and `ScalarRel lenSc mlen` (`lenSc.sizeBytes = 8`).
* `scalarAddr`: Anneal provenance-free `Value.aggregate 0 [.scalar addrSc, .scalar lenSc]`
  relates to `Immediate.scalarPair (.fromScalarInt maddr) (.fromScalarInt mlen)`
  when `ScalarRel addrSc maddr` (`addrSc.sizeBytes = 8`) and `ScalarRel lenSc mlen`
  (`lenSc.sizeBytes = 8`). -/
inductive WideSliceImmediateRel (allocMap : List AllocMapEntry) :
    Value → Miri.Interpreter.Immediate AnnealProv → Prop where
  | provenance
      {p : ProvenancePtr} {lenSc : MirAst.ScalarInt}
      {mptr : Miri.Memory.Pointer AnnealProv} {mlen : Miri.Memory.ScalarInt}
      (hptr : PtrRel allocMap p mptr)
      (hlen : ScalarRel lenSc mlen)
      (hlen_sz : lenSc.sizeBytes = 8) :
      WideSliceImmediateRel allocMap
        (.aggregate 0 [.ptr p 8, .scalar lenSc])
        (.scalarPair
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)
          (.fromScalarInt mlen))
  | scalarAddr
      {addrSc lenSc : MirAst.ScalarInt}
      {maddr mlen : Miri.Memory.ScalarInt}
      (haddr : ScalarRel addrSc maddr)
      (hlen : ScalarRel lenSc mlen)
      (haddr_sz : addrSc.sizeBytes = 8)
      (hlen_sz : lenSc.sizeBytes = 8) :
      WideSliceImmediateRel allocMap
        (.aggregate 0 [.scalar addrSc, .scalar lenSc])
        (.scalarPair (.fromScalarInt maddr) (.fromScalarInt mlen))

namespace WideSliceImmediateRel

/-- Every `WideSliceImmediateRel`-related `Miri.Interpreter.Immediate` unpacks
via `Immediate.toScalarAndMeta` to `(dataScalar, .metadata (.fromScalarInt mlen))`. -/
theorem toScalarAndMeta_eq {allocMap : List AllocMapEntry}
    {v : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    (h : WideSliceImmediateRel allocMap v imm) :
    ∃ dataSc mlen,
      imm = .scalarPair dataSc (.fromScalarInt mlen) ∧
      imm.toScalarAndMeta = .ok (dataSc, .metadata (.fromScalarInt mlen)) ∧
      imm.toScalarPair = .ok (dataSc, .fromScalarInt mlen) := by
  cases h with
  | provenance _ _ _ =>
      exact ⟨_, _, rfl, rfl, rfl⟩
  | scalarAddr _ _ _ _ =>
      exact ⟨_, _, rfl, rfl, rfl⟩

/-- Constructing a wide pointer via vendored `Immediate.newPointerWithMeta` from
a provenance-carrying `mptr` and length `mlen` establishes `WideSliceImmediateRel`. -/
theorem newPointerWithMeta_provenance {allocMap : List AllocMapEntry}
    {p : ProvenancePtr} {lenSc : MirAst.ScalarInt}
    {mptr : Miri.Memory.Pointer AnnealProv} {mlen : Miri.Memory.ScalarInt}
    (hptr : PtrRel allocMap p mptr)
    (hlen : ScalarRel lenSc mlen)
    (hlen_sz : lenSc.sizeBytes = 8) :
    Miri.Interpreter.Immediate.newPointerWithMeta
      ⟨mptr.offset, some mptr.provenance⟩
      (.metadata (.fromScalarInt mlen))
      annealTargetDataLayout =
      .ok (.scalarPair
        (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)
        (.fromScalarInt mlen)) ∧
    WideSliceImmediateRel allocMap
      (.aggregate 0 [.ptr p 8, .scalar lenSc])
      (.scalarPair
        (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)
        (.fromScalarInt mlen)) := by
  refine ⟨rfl, .provenance hptr hlen hlen_sz⟩

/-- Constructing a wide slice via vendored `Immediate.newSlice` from a
provenance-carrying `mptr` and length `lenSc` (`lenSc.bits < 2^64`) produces a
`.scalarPair` satisfying `WideSliceImmediateRel`. -/
theorem newSlice_provenance {allocMap : List AllocMapEntry}
    {p : ProvenancePtr} {lenSc : MirAst.ScalarInt}
    {mptr : Miri.Memory.Pointer AnnealProv}
    (hptr : PtrRel allocMap p mptr)
    (hlen_lt : lenSc.bits < 2 ^ 64)
    (hlen_sz : lenSc.sizeBytes = 8) :
    ∃ mlen,
      ScalarRel lenSc mlen ∧
      Miri.Interpreter.Immediate.newSlice
        ⟨mptr.offset, some mptr.provenance⟩
        (UInt64.ofNat lenSc.bits)
        annealTargetDataLayout =
        .ok (.scalarPair
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)
          (.fromScalarInt mlen)) ∧
      WideSliceImmediateRel allocMap
        (.aggregate 0 [.ptr p 8, .scalar lenSc])
        (.scalarPair
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)
          (.fromScalarInt mlen)) := by
  obtain ⟨mlen, htry, hrel0⟩ := tryFromUInt_u64_spec hlen_lt
  have hrel : ScalarRel lenSc mlen := by
    rcases lenSc with ⟨lbits, lsz⟩
    dsimp only at hlen_sz
    subst hlen_sz
    exact hrel0
  have hu64 : (UInt64.ofNat lenSc.bits).toNat = lenSc.bits :=
    UInt64.toNat_ofNat_of_lt hlen_lt
  refine ⟨mlen, hrel, ?_, .provenance hptr hrel hlen_sz⟩
  unfold Miri.Interpreter.Immediate.newSlice Miri.Memory.Scalar.fromMaybePointer
    Miri.Memory.Scalar.fromUInt
  change (do
    let scalar ← Except.ok (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)
    let length ←
      (do
        let s ← Miri.Memory.ScalarInt.tryFromUInt
          (BitVec.ofNat 128 (UInt64.ofNat lenSc.bits).toNat)
          (Miri.ABI.Size.ofBytes 8) |>.mapError _
        match s with
        | some s => return Miri.Memory.Scalar.fromScalarInt s
        | none => throw _) |>.mapError Miri.Interpreter.ImmediateError.scalar
    return Miri.Interpreter.Immediate.scalarPair scalar length) = _
  rw [hu64, htry]
  rfl

end WideSliceImmediateRel

/-- Local-slot relation extended to wide-slice pointer/reference locals
(`WideSliceImmediateRel`), CONSERVATIVELY extending `LocalRelLM3_1`. -/
inductive LocalRelWideSlice
    (mach : AnnealMachine)
    (allocMap : List AllocMapEntry)
    (decl : LocalDecl)
    (layouts : LayoutTable) :
    LocalSlot → Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout → Prop where
  | base {slot : LocalSlot}
      {ls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
      (h : LocalRelLM3_1 mach allocMap decl layouts slot ls) :
      LocalRelWideSlice mach allocMap decl layouts slot ls
  | wideSliceInit {v : Value}
      {imm : Miri.Interpreter.Immediate AnnealProv}
      {cached : Option Miri.Interpreter.LocalLayout}
      (hwide : isWideSliceOrPointeeTy decl.ty = true)
      (hrel : WideSliceImmediateRel allocMap v imm)
      (hcached :
        cached = none ∨
        cached = some (translateTy decl.ty layouts) ∨
        cached = some (translateTyWideSlice decl.ty layouts)) :
      LocalRelWideSlice mach allocMap decl layouts (.init v) ⟨.live (.immediate imm), cached⟩
  | wideSliceUninit
      {cached : Option Miri.Interpreter.LocalLayout}
      (hwide : isWideSliceOrPointeeTy decl.ty = true)
      (hcached :
        cached = none ∨
        cached = some (translateTy decl.ty layouts) ∨
        cached = some (translateTyWideSlice decl.ty layouts)) :
      LocalRelWideSlice mach allocMap decl layouts .uninit ⟨.live (.immediate .uninit), cached⟩

/-- Frame-level correspondence for wide-slice MIR execution (`StateRelWideSlice`). -/
structure FrameRelWideSlice (cm : CapturedMir) (mach : AnnealMachine)
    (allocMap : List AllocMapEntry) (af : StackFrame)
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) : Prop where
  body_eq : mf.body = translateBody cm
  location_eq : mf.location = .mir { block := af.blockIdx, statementIndex := af.stmtIdx }
  af_locals_len : af.locals.length = cm.localDecls.length
  mf_locals_size : mf.locals.size = cm.localDecls.length
  locals_rel :
    ∀ i (decl : LocalDecl) (slot : LocalSlot)
      (ls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout),
      get? cm.localDecls i = some decl →
      get? af.locals i = some slot →
      mf.locals[i]? = some ls →
      LocalRelWideSlice mach allocMap decl cm.layouts slot ls

/-- Whole-machine state relation for wide-slice MIR execution, extending
`StateRelLM3_1` with `FrameRelWideSlice`. -/
structure StateRelWideSlice (cm : CapturedMir) (s : MachineState) (m : AnnealStepState)
    (allocMap : List AllocMapEntry) : Prop where
  activeCallee_none : s.memory.activeCallee = none
  callStack_nil : s.memory.callStack = []
  borrows_eq : s.memory.borrows = allocMap.map AllocMapEntry.toBorrowEntry
  alloc_rel : AllocMapRel cm s m allocMap
  single_frame :
    ∃ topFrame,
      m.stack.frames = #[topFrame] ∧
      FrameRelWideSlice cm m.machine allocMap s.frame topFrame ∧
      MemoryAllocDisjoint topFrame

theorem FrameRelWideSlice.of_frameRelLM3_1 {cm : CapturedMir} {mach : AnnealMachine}
    {allocMap : List AllocMapEntry} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM3_1 cm mach allocMap af mf) :
    FrameRelWideSlice cm mach allocMap af mf where
  body_eq := h.body_eq
  location_eq := h.location_eq
  af_locals_len := h.af_locals_len
  mf_locals_size := h.mf_locals_size
  locals_rel i decl slot ls hdecl hslot hls :=
    .base (h.locals_rel i decl slot ls hdecl hslot hls)

theorem StateRelWideSlice.of_stateRelLM3_1 {cm : CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (h : StateRelLM3_1 cm s m allocMap) :
    StateRelWideSlice cm s m allocMap := by
  rcases h with ⟨tf, hframes, _, _, hfr, hcal, hstack, _, _, hbor, halloc, hdisj⟩
  exact ⟨hcal, hstack, hbor, halloc, tf, hframes, FrameRelWideSlice.of_frameRelLM3_1 hfr, hdisj⟩

theorem StateRelWideSlice.of_stateRel {cm : CapturedMir} {s : MachineState}
    {m : AnnealStepState} (h : StateRel cm s m) :
    StateRelWideSlice cm s m [] :=
  StateRelWideSlice.of_stateRelLM3_1 (StateRel.toLM3_1 h)

/-- Step-outcome relation for wide-slice MIR execution (`StepRelWideSlice`). -/
inductive StepRelWideSlice (cm : CapturedMir) (m₀ : AnnealStepState)
    (allocMap : List AllocMapEntry) :
    MirStepNode → Miri.Interpreter.StepResult AnnealStepState Bool → Prop where
  | step {s' : MachineState} {m' : AnnealStepState}
      (hrel : StateRelWideSlice cm s' m' allocMap) :
      StepRelWideSlice cm m₀ allocMap (.step s') (m', .ok true)
  | retScalar {retVal : Value} {mem' : Memory} {m' : AnnealStepState}
      {decl0 : LocalDecl} {retImm : Miri.Interpreter.Immediate AnnealProv}
      (hdecl0 : get? cm.localDecls 0 = some decl0)
      (hret : ImmediateRel decl0.ty cm.layouts retVal retImm)
      (hframes : m'.stack.frames = #[]) :
      StepRelWideSlice cm m₀ allocMap (.ret (.normal (retVal, mem'))) (m', .ok false)
  | retWideSlice {retVal : Value} {mem' : Memory} {m' : AnnealStepState}
      {decl0 : LocalDecl} {retImm : Miri.Interpreter.Immediate AnnealProv}
      (hdecl0 : get? cm.localDecls 0 = some decl0)
      (hret : WideSliceImmediateRel allocMap retVal retImm)
      (hframes : m'.stack.frames = #[]) :
      StepRelWideSlice cm m₀ allocMap (.ret (.normal (retVal, mem'))) (m', .ok false)
  | ub {m' : AnnealStepState} {msg : String} :
      StepRelWideSlice cm m₀ allocMap (.fail .ub) (m', .error (.undefinedBehavior msg))

/-! ### 1.3 Vendored `Miri` Hook Instantiations for Wide-Slice DSTs -/

/-- `Miri.Interpreter.DynamicLayoutHooks` instantiated for Anneal's 64-bit
single-threaded machine (`maxSizeOfVal = Size.ofBytes 0x7fff_ffff_ffff_ffff = 2^63 - 1`),
wiring vendored `Miri.Interpreter.DynamicLayout.{sizeAndAlignFromMeta,
sizeAndAlignOfVal, alignmentFromMeta}` for `[T]` (`slicePointeeTyId`) and `str`
(`strPointeeTyId`). -/
def annealDynamicLayoutHooksWideSlice (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.DynamicLayoutHooks AnnealProv AnnealStepState Unit where
  target := annealTargetDataLayout
  maxSizeOfVal := Miri.ABI.Size.ofBytes 0x7fff_ffff_ffff_ffff
  classify := fun _ tyId =>
    if tyId == strPointeeTyId then
      pure .str
    else if 2100 ≤ tyId && tyId < 2200 then
      pure .slice
    else
      throw (.unsupported s!"DynamicLayoutHooks.classify: unsupported unsized TyId {tyId}")
  field := fun _ layout idx =>
    if idx != 0 then
      throw (.invalidProgram "slice/str has only element field 0")
    else if layout.ty == strPointeeTyId then
      pure (translateTy { kind := .uint .u8, layoutIdx := 0 } layouts)
    else if 2100 ≤ layout.ty && layout.ty < 2200 then
      pure (layoutOfEncodedTyId (layout.ty - 2100) layouts)
    else
      throw (.unsupported s!"DynamicLayoutHooks.field: unsupported TyId {layout.ty}")
  packedAlign := fun _ _ => pure none
  vtableSizeAndAlign := fun _ _ _ =>
    throw (.unsupported "vtableSizeAndAlign is outside the wide-slice fragment")

/-- Dereference a wide-slice or thin pointer `Immediate AnnealProv` into a
`MemPlace AnnealProv` with `pointeeLay`, extracting `(ptrSc, meta)` via vendored
`Immediate.toScalarAndMeta` and `Scalar.toPointer`. -/
def annealDerefWideSliceImmediate
    (imm : Miri.Interpreter.Immediate AnnealProv)
    (pointeeLay : Miri.Interpreter.LocalLayout) :
    Except Miri.Interpreter.StepError (Miri.Interpreter.MemPlace AnnealProv) := do
  let (ptrSc, metaVal) ←
    imm.toScalarAndMeta.mapError Miri.Interpreter.ScalarOps.immediateError
  let ptr ←
    (ptrSc.toPointer annealTargetDataLayout).mapError Miri.Interpreter.ScalarOps.scalarError
  if pointeeLay.layout.isSized then
    if metaVal.hasMeta then
      throw (.invalidProgram "sized pointee dereference cannot carry metadata")
    else
      let mismatch ←
        (annealOffsetMisalignment ptr.offset pointeeLay.layout.align.abi).mapError
          fun e => .invalidProgram (toString e)
      return ⟨ptr, .none, mismatch⟩
  else
    match metaVal with
    | .none => throw (.invalidProgram "unsized slice/str dereference requires metadata")
    | .metadata msc =>
        let _ ←
          (msc.toTargetUsize (Miri.ABI.Size.ofBytes 8)).mapError
            Miri.Interpreter.ScalarOps.scalarError
        let mismatch ←
          (annealOffsetMisalignment ptr.offset pointeeLay.layout.align.abi).mapError
            fun e => .invalidProgram (toString e)
        return ⟨ptr, .metadata msc, mismatch⟩

/-- Validate a safe wide reference (`&[T]`, `&mut [T]`, `&str`, `&mut str`)
in the exact source order of vendored `Miri.Memory.Validity.checkSafePointer`
(`Validity.lean:1048-1106`, invoked by `Place.writePlaceImmediate` and
non-skipped safe-reference `deref`):
1. Unpack `(ptr, .metadata msc)` and check `msc.toTargetUsize 8` via
   `annealDerefWideSliceImmediate`.
2. Compute `(totalSize, _)` via vendored
   `Miri.Interpreter.DynamicLayout.sizeAndAlignOfVal` (raising
   `.undefinedBehavior "InvalidMeta(SliceTooBig)"` whenever `elemSz * len ≥ 2^63`).
3. Check dereferenceability of `totalSize` bytes via vendored
   `Miri.Memory.checkPtrAccess` (`(.dereferenceable "pointer")`), raising
   `.undefinedBehavior "pointer dereference check failed"` on dangling, dead,
   or out-of-bounds backing allocations.
4. Reject null data pointers (`mp.ptr.offset.bytes == 0`) with
   `.undefinedBehavior "dereferencing a null reference"`.
5. Reject misaligned data pointers (`mp.misaligned.isSome`) with
   `.undefinedBehavior "misaligned pointer dereference"`. -/
def annealValidateSafeWideSliceRef (layouts : LayoutTable := emptyLayoutTable)
    (val : Miri.Interpreter.RvalueImmTy AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState Unit := do
  if !isWideSafeRefTyId val.layout.ty then
    return ()
  let some pointeeTyId := wideSlicePointeeTyId? val.layout.ty
    | throw (.unsupported s!"safe wide ref validation: pointee of TyId {val.layout.ty} not encoded")
  let pointeeLay := layoutOfEncodedTyIdWideSlice pointeeTyId layouts
  let mp ←
    match annealDerefWideSliceImmediate val.imm pointeeLay with
    | .ok mp => pure mp
    | .error err => throw err
  let some (totalSize, _) ←
    Miri.Interpreter.DynamicLayout.sizeAndAlignOfVal
      (annealDynamicLayoutHooksWideSlice layouts) () 8 ⟨.indirect mp, pointeeLay⟩
    | throw (.unsupported "extern unsized slice in annealValidateSafeWideSliceRef")
  let st ← get
  match Miri.Memory.checkPtrAccess annealPointerArithmetic mp.ptr totalSize
      (.dereferenceable "pointer") (annealResolvePtr st.machine)
      (annealLookupAlloc st.machine) with
  | .error _ => throw (.undefinedBehavior "pointer dereference check failed")
  | .ok () =>
      if mp.ptr.offset.bytes == 0 then
        throw (.undefinedBehavior "dereferencing a null reference")
      if mp.misaligned.isSome then
        throw (.undefinedBehavior "misaligned pointer dereference")
      return ()

/-- Resolve the pointee `LocalLayout` (including unsized `[T]` and `str`) of a
pointer/reference local `localId` from `localDecls` or `wideSlicePointeeTyId?`. -/
def lookupWideSlicePointeeLayout (localDecls : List LocalDecl) (layouts : LayoutTable)
    (localId : Miri.MIR.LocalId) (ptrLayout : Miri.Interpreter.LocalLayout) :
    Option Miri.Interpreter.LocalLayout :=
  match get? localDecls localId with
  | some decl =>
      match decl.ty.kind with
      | .rawPtr _ .str | .ref _ .str =>
          some (translateTyWideSlice { kind := .str, layoutIdx := 0 } layouts)
      | .rawPtr _ (.slice elemKind) | .ref _ (.slice elemKind) =>
          some (translateTyWideSlice { kind := .slice elemKind, layoutIdx := 0 } layouts)
      | .rawPtr _ pointeeKind | .ref _ pointeeKind =>
          if derefPointeeKindHasExactLayout pointeeKind then
            some (translateTy { kind := pointeeKind, layoutIdx := 0 } layouts)
          else
            none
      | _ => none
  | none =>
      (wideSlicePointeeTyId? ptrLayout.ty).map (layoutOfEncodedTyIdWideSlice · layouts)

/-- `Miri.Interpreter.PlaceProjectionHooks` instantiated for Anneal's
single-threaded machine, wiring vendored `Miri.Interpreter.PlaceDynamic.{length,
index, constantIndex, subslice, project, evalPlace}` over dereferenced wide
slices (`*s`, `(*s)[i]`, `(*s)[from..to]`). -/
def annealPlaceProjectionHooksWideSlice (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.PlaceProjectionHooks AnnealProv AnnealStepState Unit Unit where
  place := {
    annealPlaceHooks localDecls layouts with
    resolveLayout := fun _ localId =>
      match get? localDecls localId with
      | some decl => pure (translateTyWideSlice decl.ty layouts)
      | none => throw (.stack (.missingLocalType localId))
    deref := fun _ base skipValidity => do
      match base.ref with
      | .local _ localId none _ =>
          let st ← get
          let some frame := st.stack.currentFrame?
            | throw (.stack .emptyStack)
          let operand ←
            match frame.getLocalOperand localId with
            | .ok op => pure op
            | .error (.localExpectedLive _) => throw (.undefinedBehavior "read of dead local")
            | .error e => throw (.stack e)
          let imm ← annealReadImmediate ⟨operand, base.layout⟩
          if !skipValidity && isWideSafeRefTyId base.layout.ty then
            annealValidateSafeWideSliceRef layouts ⟨imm.imm, base.layout⟩
          let some pointeeLay := lookupWideSlicePointeeLayout localDecls layouts localId base.layout
            | throw (.unsupported "deref of local without pointee layout")
          match annealDerefWideSliceImmediate imm.imm pointeeLay with
          | .ok mp => return ⟨.memory mp, pointeeLay⟩
          | .error err => throw err
      | _ => throw (.unsupported "nested deref in annealPlaceProjectionHooksWideSlice")
    checkPlaceType := fun _ _ _ => pure ()
    memoryOffset := fun _ place amount mode metaValue => do
      let st ← get
      match Miri.Interpreter.projectionMemoryOffset
          annealPointerArithmetic
          (annealPointerResolver st.machine)
          (annealLiveAllocationLookup st.machine)
          place amount mode metaValue with
      | .ok mp' => return mp'
      | .error err => throw (annealLiftProjectionError err) }
  target := annealTargetDataLayout
  maxSizeOfVal := Miri.ABI.Size.ofBytes 0x7fff_ffff_ffff_ffff
  dynamic := annealDynamicLayoutHooksWideSlice layouts
  dynamicFuel := 8
  isSliceOrStr := fun _ tyId =>
    pure (tyId == strPointeeTyId || (2100 ≤ tyId && tyId < 2200))
  field := fun _ baseLay idx =>
    if idx != 0 then
      throw (.invalidProgram "slice/array element field index must be 0")
    else if baseLay.ty == strPointeeTyId then
      pure (translateTy { kind := .uint .u8, layoutIdx := 0 } layouts)
    else if 2100 ≤ baseLay.ty && baseLay.ty < 2200 then
      pure (layoutOfEncodedTyId (baseLay.ty - 2100) layouts)
    else
      match baseLay.layout.fields with
      | .Array stride _ => pure (arrayElemLayoutOf layouts baseLay stride)
      | _ => throw (.unsupported "non-slice/array field in annealPlaceProjectionHooksWideSlice")
  variant := fun _ baseLay vIdx =>
    if vIdx == 0 then pure baseLay
    else throw (.unsupported "multi-variant downcast in annealPlaceProjectionHooksWideSlice")
  packedAlign := fun _ _ => pure none
  subsliceLayout := fun _ baseLay subLen => do
    if baseLay.ty == strPointeeTyId || (2100 ≤ baseLay.ty && baseLay.ty < 2200) then
      match Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 subLen.toNat) (Miri.ABI.Size.ofBytes 8) with
      | .ok sc => return (baseLay, .metadata sc)
      | .error err => throw (Miri.Interpreter.ScalarOps.scalarError err)
    else
      throw (.unsupported "array subslice in annealPlaceProjectionHooksWideSlice")
  layoutOf := fun _ tyId => pure (layoutOfEncodedTyIdWideSlice tyId layouts)
  localIndex := fun _ localId => do
    let st ← get
    let some frame := st.stack.currentFrame?
      | throw (.stack .emptyStack)
    match annealLocalIndex frame st.machine localId with
    | .ok idx => return idx
    | .error err => throw (annealLiftProjectionError err)

/-- Validate `ScalarOpsHooks.derefValidity` on thin or wide raw/reference
pointers for `UnOp.PtrMetadata`:
* Thin pointers (`value.imm = .scalar sc`): checks `sc.toPointer annealTargetDataLayout`
  without touching memory.
* Wide slice/str pointers (`value.imm = .scalarPair dataSc metaSc`): checks
  `dataSc.toPointer annealTargetDataLayout` and `metaSc.toTargetUsize 8` without
  touching memory, matching Rust's `ptr::metadata` (which never dereferences
  even dangling, OOB, or disabled pointers). -/
def annealDerefValidityWideSlice (layouts : LayoutTable := emptyLayoutTable)
    (value : Miri.Interpreter.RvalueImmTy AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState Unit :=
  if isWideSlicePtrTyId value.layout.ty then
    match value.imm.toScalarAndMeta with
    | .error err => throw (Miri.Interpreter.ScalarOps.immediateError err)
    | .ok (_, .metadata _) => pure ()
    | .ok (_, .none) => throw (.invalidProgram "wide slice pointer immediate missing metadata")
  else if value.layout.ty == arraySliceMetaTyId || value.layout.ty == 40 || value.layout.ty == 41 then
    pure ()
  else
    annealDerefValidity layouts value

/-- `ScalarOpsHooks` extended with wide-slice pointer classification and
`annealDerefValidityWideSlice` so vendored `Miri.Interpreter.ScalarOps.unary
.PtrMetadata` evaluates `UnOp.ptrMetadata` on both wide slice/str pointers and
thin pointers. -/
def annealScalarOpsHooksWideSlice (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.ScalarOpsHooks AnnealProv AnnealStepState Unit :=
  { annealScalarOpsHooks localDecls layouts with
    classify := fun _ tyId =>
      match classifyEncodedTyIdWideSlice tyId with
      | .ok cls => pure cls
      | .error err => throw err
    derefValidity := fun _ value =>
      annealDerefValidityWideSlice layouts value }

/-- `CastHooks` extended with wide-slice `TyId` classification and wide raw-pointer
`derefPointer` validation so vendored `Miri.Interpreter.Cast.cast` / `Cast.ptrToPtr`
evaluates wide-to-thin (`*const [T] as *const ()`) and wide-to-wide
(`*const [T] as *mut [T]`, `*const str as *const [u8]`) pointer casts. -/
def annealCastHooksWideSlice (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.CastHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealCastHooks layouts with
    target := annealTargetDataLayout
    typeInfo := fun _ tyId =>
      match castTypeInfoOfEncodedTyIdWideSlice tyId with
      | .ok info => pure info
      | .error err => throw err
    layoutOf := fun _ tyId => pure (layoutOfEncodedTyIdWideSlice tyId layouts)
    derefPointer := fun _ op => do
      let imm ← annealReadImmediate op
      annealDerefValidityWideSlice layouts imm }

/-- Resolve a local's `LocalLayout` using `translateTyWideSlice` so wide-slice
pointer/reference locals receive their 16-byte `widePointerLayoutData` layout. -/
def lookupLocalDeclLayoutWideSlice (localDecls : List LocalDecl) (layouts : LayoutTable)
    (localId : Miri.MIR.LocalId) : Option Miri.Interpreter.LocalLayout :=
  match get? localDecls localId with
  | some decl => some (translateTyWideSlice decl.ty layouts)
  | none => none

/-- Wide-slice-aware local layout resolution and caching in the top frame. -/
def annealResolveAndCacheLocalLayoutWideSlice (localDecls : List LocalDecl)
    (layouts : LayoutTable) (localId : Miri.MIR.LocalId)
    (known : Option Miri.Interpreter.LocalLayout := none) :
    Miri.Interpreter.RvalueM AnnealStepState
      (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit ×
        Miri.Interpreter.LocalLayout) := do
  let st ← get
  let some frame := st.stack.currentFrame?
    | throw (.stack .emptyStack)
  let ls ←
    match frame.getLocal localId with
    | .ok ls => pure ls
    | .error e => throw (.stack e)
  let declLayOpt := lookupLocalDeclLayoutWideSlice localDecls layouts localId
  let computed ←
    match declLayOpt <|> ls.layout <|> known with
    | some l => pure l
    | none =>
        match frame.body.locals[localId]? with
        | some tyId => pure (layoutOfEncodedTyIdWideSlice tyId layouts)
        | none => throw (.stack (.missingLocalType localId))
  let frameWithWideLay : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
    if h : localId < frame.locals.size then
      { frame with locals := frame.locals.set localId { (frame.locals[localId]'h) with layout := some computed } h }
    else
      frame
  let idx := st.stack.frames.size - 1
  if h : idx < st.stack.frames.size then
    set { st with stack := { frames := st.stack.frames.set idx frameWithWideLay h } }
    return (frameWithWideLay, computed)
  else
    throw (.stack .emptyStack)

/-- Whether a `Miri.MIR.Place`'s base local `place.localId` is declared with a
wide-slice pointer/reference or unsized slice/str type in `localDecls`. -/
def isWideSliceBasePlace (localDecls : List LocalDecl) (place : Miri.MIR.Place) : Bool :=
  match get? localDecls place.localId with
  | some decl => isWideSliceOrPointeeTy decl.ty
  | none => false

/-- Wide-slice-aware operand evaluation:
1. Resolves unprojected local operands with
   `annealResolveAndCacheLocalLayoutWideSlice` (preserving `.scalarPair` wide
   pointers and their `translateTyWideSlice` layout).
2. Evaluates projected places (`*s`, `(*s)[i]`, `(*s)[from..to]`, and
   `Rvalue.len (*s)` lowered via `.UnwrapUnsafeBinder arraySliceMetaTyId`) whose
   base local has a wide-slice type in `localDecls` (`isWideSliceBasePlace`)
   through vendored `Miri.Interpreter.PlaceDynamic.evalPlace` and
   `Miri.Interpreter.PlaceDynamic.length` under
   `annealPlaceProjectionHooksWideSlice`.
3. Delegates all other projected or constant operands to `annealEvalOperand`. -/
def annealEvalOperandWideSlice (localDecls : List LocalDecl) (layouts : LayoutTable)
    (op : Miri.MIR.Operand) (known : Option Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) := do
  match op with
  | .Copy place | .Move place =>
      if place.projection.isEmpty then
        let st ← get
        if st.stack.currentFrame?.isNone then
          throw (.stack .emptyStack)
        let (frame', layout) ←
          annealResolveAndCacheLocalLayoutWideSlice localDecls layouts place.localId known
        let operand ←
          match frame'.getLocalOperand place.localId with
          | .ok opVal => pure opVal
          | .error (.localExpectedLive _) => throw (.undefinedBehavior "read of dead local")
          | .error e => throw (.stack e)
        match op with
        | .Move _ =>
            match frame'.replaceLocalValue place.localId (.live (.immediate .uninit)) with
            | .ok frame'' =>
                let st ← get
                let idx := st.stack.frames.size - 1
                if h : idx < st.stack.frames.size then
                  set { st with stack := { frames := st.stack.frames.set idx frame'' h } }
                  return ⟨operand, layout⟩
                else
                  throw (.stack .emptyStack)
            | .error e => throw (.stack e)
        | _ => return ⟨operand, layout⟩
      else if isWideSliceBasePlace localDecls place then
        let _ ← annealResolveAndCacheLocalLayoutWideSlice localDecls layouts place.localId none
        if place.projection.back? == some (.UnwrapUnsafeBinder arraySliceMetaTyId) then
          let innerPlace : Miri.MIR.Place :=
            { localId := place.localId, projection := place.projection.pop }
          let rp ←
            Miri.Interpreter.PlaceDynamic.evalPlace
              (annealPlaceProjectionHooksWideSlice localDecls layouts) ()
              innerPlace false
          let _ ←
            Miri.Interpreter.PlaceDynamic.length
              (annealPlaceProjectionHooksWideSlice localDecls layouts) () rp
          match rp.ref with
          | .memory mp =>
              match mp.toRef annealTargetDataLayout with
              | .ok imm =>
                  return ⟨.immediate imm,
                          { ty := arraySliceMetaTyId,
                            layout := widePointerLayoutData false }⟩
              | .error err => throw (.invalidProgram s!"slice len reference: {repr err}")
          | _ => throw (.invalidProgram "slice len deref did not resolve to memory place")
        else
          let rp ←
            Miri.Interpreter.PlaceDynamic.evalPlace
              (annealPlaceProjectionHooksWideSlice localDecls layouts) () place false
          match rp.ref with
          | .memory mp => return ⟨.indirect mp, rp.layout⟩
          | _ => throw (.invalidProgram "wide-slice deref projection did not resolve to memory place")
      else
        annealEvalOperand localDecls layouts op known
  | _ => annealEvalOperand localDecls layouts op known

/-- Wide-slice-aware destination/borrow place evaluation with explicit
`skipValidityForSimpleDeref` threading (`Rvalue.lean:81` passes `true` for
`Rvalue.Ref`, whereas `Rvalue.lean:97` passes `false` for `Rvalue.RawPtr` and
assignment destinations pass `false`):
1. Resolves unprojected locals with `annealResolveAndCacheLocalLayoutWideSlice`
   so wide-pointer destinations have their 16-byte `widePointerLayoutData` layout.
2. Evaluates projected places (`*s`, `(*s)[i]`, `(*s)[from..to]`) on a wide-slice
   base local (`isWideSliceBasePlace`) via vendored
   `Miri.Interpreter.PlaceDynamic.evalPlace` under
   `annealPlaceProjectionHooksWideSlice`, forwarding `skipValidityForSimpleDeref`.
3. Delegates all other projected places to `annealEvalPlace`. -/
def annealEvalPlaceWideSliceWithSkip (localDecls : List LocalDecl) (layouts : LayoutTable)
    (place : Miri.MIR.Place) (skipValidityForSimpleDeref : Bool) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RuntimePlace AnnealProv) := do
  if place.projection.isEmpty then
    let st ← get
    if st.stack.currentFrame?.isNone then
      throw (.stack .emptyStack)
    let frameIdx := st.stack.frames.size - 1
    let (frame', layout) ←
      annealResolveAndCacheLocalLayoutWideSlice localDecls layouts place.localId none
    return ⟨.local frameIdx place.localId none frame'.localsIdentity, layout⟩
  else if isWideSliceBasePlace localDecls place then
    let _ ← annealResolveAndCacheLocalLayoutWideSlice localDecls layouts place.localId none
    Miri.Interpreter.PlaceDynamic.evalPlace
      (annealPlaceProjectionHooksWideSlice localDecls layouts) () place skipValidityForSimpleDeref
  else
    annealEvalPlace localDecls layouts place

/-- Wide-slice-aware destination place evaluation (`skipValidityForSimpleDeref = false`). -/
def annealEvalPlaceWideSlice (localDecls : List LocalDecl) (layouts : LayoutTable)
    (place : Miri.MIR.Place) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RuntimePlace AnnealProv) :=
  annealEvalPlaceWideSliceWithSkip localDecls layouts place false

/-- `AggregateHooks` instantiated for wide-slice `AggregateKind.RawPtr`
construction (`ptr::from_raw_parts(_mut)` / `ptr::slice_from_raw_parts(_mut)`),
wiring vendored `Miri.Interpreter.writeAggregate` (`Immediate.newPointerWithMeta`). -/
def annealAggregateHooksWideSlice (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.AggregateHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealAggregateHooksLM2_2 localDecls layouts with
    evalOperand := fun _ op known => annealEvalOperandWideSlice localDecls layouts op known
    evalOperandAt := fun _ _ op known => do
      let opTy ← annealEvalOperandWideSlice localDecls layouts op known
      match opTy.op with
      | .immediate .uninit =>
          if opTy.layout.layout.isZst then
            return opTy
          else
            throw (.undefinedBehavior "read of uninitialized local")
      | .immediate _ =>
          let imm ← annealReadImmediate opTy
          return ⟨.immediate imm.imm, imm.layout⟩
      | .indirect _ => return opTy
    readPointer := fun _ op => do
      let imm ← annealReadImmediate op
      match imm.imm.toScalar with
      | .ok sc =>
          match sc.toPointer annealTargetDataLayout with
          | .ok p => return p
          | .error err => throw (Miri.Interpreter.ScalarOps.scalarError err)
      | .error err => throw (Miri.Interpreter.ScalarOps.immediateError err)
    readScalar := fun _ op => do
      let imm ← annealReadImmediate op
      match imm.imm.toScalar with
      | .ok sc => return sc
      | .error err => throw (Miri.Interpreter.ScalarOps.immediateError err)
    copyOp := fun _ src dest => do
      let imm ← annealReadImmediate src
      annealWriteImmediate imm.imm dest }

/-- Convert a wide-slice or thin pointer `RvalueImmTy AnnealProv` into a
dereferenced `OpTy AnnealProv` for `IntrinsicHooks.immPointerToPlace`
(used by vendored `Miri.Interpreter.Intrinsics.eval` on `"size_of_val"` and
`"align_of_val"`). -/
def annealImmPointerToPlaceWideSlice (layouts : LayoutTable := emptyLayoutTable)
    (ptrImm : Miri.Interpreter.RvalueImmTy AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) := do
  let some pointeeTyId := wideSlicePointeeTyId? ptrImm.layout.ty
    | throw (.unsupported s!"immPointerToPlace: pointee of TyId {ptrImm.layout.ty} not encoded")
  let pointeeLay := layoutOfEncodedTyIdWideSlice pointeeTyId layouts
  match annealDerefWideSliceImmediate ptrImm.imm pointeeLay with
  | .ok mp => return ⟨.indirect mp, pointeeLay⟩
  | .error err => throw err

/-- `IntrinsicHooks` extended with `immPointerToPlace` and `dynamicSizeAlign`
(`Miri.Interpreter.DynamicLayout.sizeAndAlignOfVal`) so vendored
`Miri.Interpreter.Intrinsics.eval` evaluates `"size_of_val"` and `"align_of_val"`
on wide `[T]` and `str` pointers (and thin sized pointers). -/
def annealIntrinsicHooksWideSlice (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.IntrinsicHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealIntrinsicHooks localDecls layouts with
    layoutOf := fun _ tyId => pure (layoutOfEncodedTyIdWideSlice tyId layouts)
    pointeeType := fun _ tyId =>
      match wideSlicePointeeTyId? tyId with
      | some pointee => pure pointee
      | none => throw (.unsupported s!"pointee of TyId {tyId} is not encoded")
    evalOperand := fun _ op => annealEvalOperandWideSlice localDecls layouts op none
    evalOperandAt := fun _ _ op => annealEvalOperandWideSlice localDecls layouts op none
    immPointerToPlace := fun _ imm => annealImmPointerToPlaceWideSlice layouts imm
    dynamicSizeAlign := fun _ place =>
      Miri.Interpreter.DynamicLayout.sizeAndAlignOfVal
        (annealDynamicLayoutHooksWideSlice layouts) () 8 place
    scalarOps := annealScalarOpsHooksWideSlice localDecls layouts }

/-- Intrinsics supported by the wide-slice call overlay: `size_of_val` and
`align_of_val` (`DefId`s `16` and `17`). -/
inductive WideSliceIntrinsic where
  | sizeOfVal
  | alignOfVal
  deriving DecidableEq, Repr

namespace WideSliceIntrinsic

def defPath : WideSliceIntrinsic → DefPath
  | .sizeOfVal => "core::intrinsics::size_of_val"
  | .alignOfVal => "core::intrinsics::align_of_val"

def name : WideSliceIntrinsic → String
  | .sizeOfVal => "size_of_val"
  | .alignOfVal => "align_of_val"

def defId : WideSliceIntrinsic → Miri.MIR.DefId
  | .sizeOfVal => 16
  | .alignOfVal => 17

def ofDefId? : Miri.MIR.DefId → Option WideSliceIntrinsic
  | 16 => some .sizeOfVal
  | 17 => some .alignOfVal
  | _ => none

def ofDefPath? (p : DefPath) : Option WideSliceIntrinsic :=
  if stringEq p "core::intrinsics::size_of_val" || stringEq p "std::intrinsics::size_of_val" then
    some .sizeOfVal
  else if stringEq p "core::intrinsics::align_of_val" || stringEq p "std::intrinsics::align_of_val" then
    some .alignOfVal
  else
    none

end WideSliceIntrinsic

/-- Resolve the pointee `Ty` of the first argument in a `size_of_val` /
`align_of_val` call from `func` type arguments or the first argument's declared
local type in `localDecls`. -/
def resolveWideSliceCallPointeeTy (localDecls : List LocalDecl)
    (func : Operand) (args : List Operand) : Option Ty :=
  let fromArg : Option Ty :=
    match args with
    | (.copy p) :: _ | (.move p) :: _ =>
        match get? localDecls p.local_ with
        | some decl =>
            match decl.ty.kind with
            | .rawPtr _ pk | .ref _ pk => some { kind := pk, layoutIdx := 0 }
            | _ => none
        | none => none
    | _ => none
  match func with
  | .constant c =>
      match c.ty.kind with
      | .fnDef _ (argKind :: .nil) => some { kind := argKind, layoutIdx := 0 }
      | _ => fromArg
  | _ => fromArg

/-- Dispatch an intrinsic call in `annealCallHooksWideSlice` through vendored
`Miri.Interpreter.Intrinsics.eval` under `annealIntrinsicHooksWideSlice` (handling
both `WideSliceIntrinsic` and `AnnealIntrinsic`). -/
def annealCallIntrinsicWideSlice (localDecls : List LocalDecl) (layouts : LayoutTable)
    (inst : Miri.Interpreter.CallInstance) (args : Array (Miri.Interpreter.OpTy AnnealProv))
    (dest : Miri.Interpreter.RuntimeStackPlace AnnealProv)
    (target : Option Miri.MIR.BasicBlockId) :
    Miri.Interpreter.CallM AnnealStepState (Option Miri.Interpreter.CallInstance) :=
  let name? : Option String :=
    match WideSliceIntrinsic.ofDefId? inst.defId with
    | some wk => some wk.name
    | none => (AnnealIntrinsic.ofDefId? inst.defId).map AnnealIntrinsic.name
  match name? with
  | none => annealUnsupportedLeaf "call of an intrinsic outside WideSliceIntrinsic / AnnealIntrinsic"
  | some intrName => do
      let types := inst.args.filterMap fun
        | .Type ty => some ty
        | _ => none
      let handled ← Miri.Interpreter.Intrinsics.eval
        (annealIntrinsicHooksWideSlice localDecls layouts) ()
        intrName types args dest.toRuntimePlace target
      if handled then
        pure none
      else
        pure (some { kind := .Item inst.defId, args := inst.args })

/-- Decode a callee function-item `TyId` for either `AnnealIntrinsic` (`1..15`)
or `WideSliceIntrinsic` (`16..17`). -/
def annealDecodeWideSliceFnItemTyId (tyId : Miri.MIR.TyId) :
    Option (Miri.MIR.DefId × Nat × Miri.MIR.TyId) :=
  if annealFnItemTyIdBase ≤ tyId then
    let defId := (tyId - annealFnItemTyIdBase) % 64
    let argTy := (tyId - annealFnItemTyIdBase) / 64
    match WideSliceIntrinsic.ofDefId? defId with
    | some wk => some (wk.defId, 1, argTy)
    | none =>
        match AnnealIntrinsic.ofDefId? defId with
        | some k => some (k.defId, k.arity, argTy)
        | none => none
  else
    none

/-- `CallHooks` extended with `WideSliceIntrinsic` (`size_of_val` and `align_of_val`)
for vendored `Miri.Interpreter.Call.evalCallTerminator`. -/
def annealCallHooksWideSlice (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.CallHooks AnnealProv AnnealStepState Unit Unit Unit Unit Unit Unit :=
  { annealCallHooks localDecls layouts with
    evalOperand := fun _ op => annealEvalOperandWideSlice localDecls layouts op none
    evalOperandAt := fun _ _ op => annealEvalOperandWideSlice localDecls layouts op none
    evalPlace := fun _ place _ => do
      let runtimePlace ← annealEvalPlaceWideSlice localDecls layouts place
      pure runtimePlace.stackView
    functionSignature := fun _ layout =>
      match annealDecodeWideSliceFnItemTyId layout.ty with
      | some (_, arity, _) => pure (arity, ())
      | none => annealUnsupportedLeaf "call of a function other than an intrinsic"
    functionKind := fun tyId =>
      match annealDecodeWideSliceFnItemTyId tyId with
      | some (defId, _, argTy) => pure (.FnDef defId #[.Type argTy])
      | none => annealUnsupportedLeaf "call of a function other than an intrinsic"
    resolve := fun _ defId args =>
      match WideSliceIntrinsic.ofDefId? defId with
      | some _ => pure { kind := .Intrinsic defId, args := args }
      | none =>
          match AnnealIntrinsic.ofDefId? defId with
          | some _ => pure { kind := .Intrinsic defId, args := args }
          | none => annealUnsupportedLeaf "call.resolve of a non-intrinsic item"
    callIntrinsic := fun _ inst args dest target _ =>
      annealCallIntrinsicWideSlice localDecls layouts inst args dest target }

/-- Translate a `TerminatorKind.call` of `size_of_val` / `align_of_val` into a
`Miri.MIR.TerminatorKind.Call` whose callee carries the encoded `WideSliceIntrinsic`
`DefId` (`16` or `17`) and pointee `TyId`. -/
def translateWideSliceCallTerminator (localDecls : List LocalDecl)
    (func : Operand) (args : List Operand) (destination : Place)
    (target : Option BasicBlockIdx) (unwind : UnwindAction) :
    Option Miri.MIR.TerminatorKind :=
  let defPath? : Option DefPath :=
    match func with
    | .constant c =>
        match c.ty.kind with
        | .fnDef p _ => some p
        | _ =>
            match c.val with
            | .unevaluated p => some p
            | _ => none
    | _ => none
  match defPath? >>= WideSliceIntrinsic.ofDefPath? with
  | none => none
  | some wk =>
      let pointeeTy := (resolveWideSliceCallPointeeTy localDecls func args).getD { kind := .str, layoutIdx := 0 }
      let pointeeTyId := encodeTyIdWideSlice pointeeTy
      let fnTyId := annealFnItemTyIdBase + wk.defId + 64 * pointeeTyId
      let calleeOp : Miri.MIR.Operand :=
        .Constant
          { span := defaultSpanRef
            userType := none
            value := .Val .ZeroSized fnTyId }
      some (.Call calleeOp
        (args.map fun a => ({ span := defaultSpanRef, operand := translateOperand a } : Miri.MIR.SpannedOperand)).toArray
        (translatePlace destination)
        target
        (translateUnwindAction unwind)
        .Normal
        defaultSpanRef)

/-- `RvalueHooks` instantiated for wide-slice DST operations, wiring vendored
`Miri.Interpreter.ScalarOps.unary`, `Miri.Interpreter.writeAggregate`,
`Miri.Interpreter.Cast.cast`, `Miri.Interpreter.PlaceDynamic.length`, and
`Place.writePlaceImmediate`-faithful safe wide-reference validation
(`annealValidateSafeWideSliceRef`). -/
def annealRvalueHooksWideSlice (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.RvalueHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealRvalueHooks localDecls layouts with
    evalPlace := fun _ p skipValidity =>
      annealEvalPlaceWideSliceWithSkip localDecls layouts p skipValidity
    evalOperand := fun _ op known => annealEvalOperandWideSlice localDecls layouts op known
    evalOperandAt := fun _ _ op known => annealEvalOperandWideSlice localDecls layouts op known
    evalPlaceToOp := fun _ p known => annealEvalOperandWideSlice localDecls layouts (.Copy p) known
    writeImmediate := fun _ val dest => do
      annealWriteImmediate val dest
      if isWideSafeRefTyId dest.layout.ty then
        annealValidateSafeWideSliceRef layouts ⟨val, dest.layout⟩
    copyOp := fun _ src dest => do
      let imm ← annealReadImmediate src
      annealWriteImmediate imm.imm dest
      if isWideSafeRefTyId dest.layout.ty then
        annealValidateSafeWideSliceRef layouts ⟨imm.imm, dest.layout⟩
    unaryOp := fun c op v =>
      Miri.Interpreter.ScalarOps.unary (annealScalarOpsHooksWideSlice localDecls layouts) c op v
    writeAggregate := fun c k os d =>
      Miri.Interpreter.writeAggregate (annealAggregateHooksWideSlice localDecls layouts) c k os d
    cast := fun c src kind ty dest =>
      Miri.Interpreter.Cast.cast (annealCastHooksWideSlice layouts) c 16 src kind ty dest }

/-- Whether a `Miri.MIR.Operand` references a local declared with a wide-slice
type in `localDecls`. -/
def isWideSliceMirOperand (localDecls : List LocalDecl) : Miri.MIR.Operand → Bool
  | .Copy p | .Move p =>
      match get? localDecls p.localId with
      | some decl => isWideSliceOrPointeeTy decl.ty
      | none => false
  | _ => false

/-- Whether a `Miri.MIR.StatementKind.Assign` exercises the wide-slice overlay:
`Aggregate (.RawPtr _ _)`, `UnaryOp .PtrMetadata` on a wide-slice local,
`Cast .PtrToPtr` involving a wide-slice local or wide-slice target `TyId`,
`Ref`/`RawPtr`/`Reborrow` of a wide-slice place, or an assignment whose
destination or source local has a wide-slice type. -/
def isWideSliceAssign (localDecls : List LocalDecl)
    (place : Miri.MIR.Place) (rvalue : Miri.MIR.Rvalue) : Bool :=
  let destWide := isWideSliceBasePlace localDecls place
  destWide ||
  match rvalue with
  | .Aggregate (.RawPtr _ _) _ => true
  | .UnaryOp _ op => isWideSliceMirOperand localDecls op
  | .BinaryOp _ lhs rhs =>
      isWideSliceMirOperand localDecls lhs || isWideSliceMirOperand localDecls rhs
  | .Cast .PtrToPtr op targetTy =>
      isWideSliceMirOperand localDecls op || isWideSlicePtrTyId targetTy || targetTy == 40
  | .Cast _ op _ => isWideSliceMirOperand localDecls op
  | .Use op _ => isWideSliceMirOperand localDecls op
  | .CopyForDeref p => isWideSliceBasePlace localDecls p
  | .Ref _ _ p => isWideSliceBasePlace localDecls p
  | .RawPtr _ p => isWideSliceBasePlace localDecls p
  | .Reborrow _ _ p => isWideSliceBasePlace localDecls p
  | _ => false

/-- Whether a `Miri.MIR.Terminator` is a `WideSliceIntrinsic` call (`size_of_val`
or `align_of_val`). -/
def isWideSliceCallTerminator : Miri.MIR.Terminator → Bool
  | { kind := .Call (.Constant c) _ _ _ _ _ _, .. } =>
      match c.value with
      | .Val .ZeroSized tyId =>
          if annealFnItemTyIdBase ≤ tyId then
            (WideSliceIntrinsic.ofDefId? ((tyId - annealFnItemTyIdBase) % 64)).isSome
          else
            false
      | _ => false
  | _ => false

/-- Rewrite the target `TyId` of a `Cast .PtrToPtr` when the destination local in
`localDecls` has a wide-slice pointer type (`wideRawSlicePtrTyId` / `wideRawStrPtrTyId`),
since `translateRvalue` encodes `*const [T]` / `*mut [T]` as `40`. -/
def refineWideSliceRvalue (localDecls : List LocalDecl)
    (place : Miri.MIR.Place) (rvalue : Miri.MIR.Rvalue) : Miri.MIR.Rvalue :=
  match rvalue with
  | .Cast .PtrToPtr op targetTy =>
      if targetTy == 40 then
        match get? localDecls place.localId with
        | some decl =>
            if isWideSliceOrPointeeTy decl.ty then
              .Cast .PtrToPtr op (encodeTyIdWideSlice decl.ty)
            else
              rvalue
        | none => rvalue
      else
        rvalue
  | _ => rvalue

/-- `TerminatorHooks` overlay for wide-slice `size_of_val` and `align_of_val`
intrinsic calls, delegating all non-wide-slice terminators unchanged to
`annealTerminatorHooks`. -/
def annealTerminatorHooksWideSlice (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.TerminatorHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      AnnealMachine
      Unit
      (Miri.Interpreter.Operand AnnealProv)
      (Miri.Interpreter.RvalueImmTy AnnealProv) :=
  let base := annealTerminatorHooks localDecls layouts
  { base with
    call := fun choice term state =>
      if isWideSliceCallTerminator term then
        Miri.Interpreter.Call.run
          (Miri.Interpreter.Call.evalCallTerminator
            (annealCallHooksWideSlice localDecls layouts) choice annealCallBudget term)
          state
      else
        base.call choice term state }

/-- Conservative `StepHooks` overlay for wide-slice DST operations: intercepts
only `isWideSliceAssign` assignments and `isWideSliceCallTerminator` calls,
delegating every other statement and terminator identically to `annealStepHooks`. -/
def annealStepHooksWideSlice (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.StepHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      AnnealMachine
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealStepHooks localDecls layouts
  { base with
    assign := fun choice place rvalue state =>
      if isWideSliceAssign localDecls place rvalue then
        Miri.Interpreter.runRvalue
          (Miri.Interpreter.evalRvalueIntoPlace
            (annealRvalueHooksWideSlice localDecls layouts) choice
            (refineWideSliceRvalue localDecls place rvalue) place)
          state
      else
        base.assign choice place rvalue state
    terminator := fun choice term state =>
      if isWideSliceCallTerminator term then
        Miri.Interpreter.ControlFlow.evalTerminator
          (annealTerminatorHooksWideSlice localDecls layouts) choice term state
      else
        base.terminator choice term state }

/-- Whether a `Miri.MIR.Statement` is outside the wide-slice `assign` overlay. -/
def stmtFreeOfWideSlice (localDecls : List LocalDecl) (stmt : Miri.MIR.Statement) : Prop :=
  match stmt.kind with
  | .Assign place rvalue => isWideSliceAssign localDecls place rvalue = false
  | _ => True

/-- Whether a `Miri.MIR.Terminator` is outside the wide-slice `call` overlay. -/
def termFreeOfWideSlice (term : Miri.MIR.Terminator) : Prop :=
  isWideSliceCallTerminator term = false

/-- Whether every basic block of `body` is free of wide-slice overlay statements
and terminators. -/
def BodyFreeOfWideSlice (localDecls : List LocalDecl) (body : Miri.MIR.Body) : Prop :=
  ∀ bb ∈ body.basicBlocks.toList,
    (∀ stmt ∈ bb.statements.toList, stmtFreeOfWideSlice localDecls stmt) ∧
    termFreeOfWideSlice bb.terminator

theorem evalStatement_wideSlice_eq_of_stmtFree {localDecls : List LocalDecl}
    {layouts : LayoutTable} {stmt : Miri.MIR.Statement}
    (hfree : stmtFreeOfWideSlice localDecls stmt)
    (choice : Unit) (state : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement
        (annealStepHooksWideSlice localDecls layouts) choice stmt state =
      Miri.Interpreter.Step.evalStatement
        (annealStepHooks localDecls layouts) choice stmt state := by
  rcases stmt with ⟨si, kind⟩
  cases kind with
  | Assign place rvalue =>
      dsimp [stmtFreeOfWideSlice] at hfree
      simp [Miri.Interpreter.Step.evalStatement, annealStepHooksWideSlice, hfree]
  | SetDiscriminant _ _ | StorageLive _ | StorageDead _ | Intrinsic _ | PlaceMention _
  | ConstEvalCounter | FakeRead _ | AscribeUserType _ _ | Coverage _
  | Nop | BackwardIncompatibleDropHint _ _ =>
      rfl

/-- Conservative-extension theorem: on any MIR body whose top-frame statements
and terminators are free of wide-slice overlay operations (`BodyFreeOfWideSlice`),
`annealStepHooksWideSlice` steps identically to `annealStepHooks`. -/
theorem step_wideSlice_eq_annealStepHooks_of_bodyFree {localDecls : List LocalDecl}
    {layouts : LayoutTable} {state : AnnealStepState}
    (hfree : ∀ frame, state.stack.currentFrame? = some frame →
      BodyFreeOfWideSlice localDecls frame.body)
    (choice : Unit) :
    Miri.Interpreter.Step.step
        (annealStepHooksWideSlice localDecls layouts) choice state =
      Miri.Interpreter.Step.step
        (annealStepHooks localDecls layouts) choice state := by
  unfold Miri.Interpreter.Step.step
  cases hcf : state.stack.currentFrame? with
  | none => rfl
  | some frame =>
      dsimp only [Id.run]
      cases hloc : frame.location with
      | unwinding _ => rfl
      | mir loc =>
          dsimp only
          cases hbb : frame.body.basicBlocks[loc.block]? with
          | none => rfl
          | some bb =>
              have hbb_mem : bb ∈ frame.body.basicBlocks.toList := by
                obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hbb
                exact Array.getElem_mem_toList hlt
              have ⟨hstmts_free, hterm_free⟩ := hfree frame hcf bb hbb_mem
              dsimp only
              cases hst : bb.statements[loc.statementIndex]? with
              | none =>
                  dsimp only [termFreeOfWideSlice] at hterm_free
                  simp [annealStepHooksWideSlice, hterm_free]
              | some stmt =>
                  have hst_mem : stmt ∈ bb.statements.toList := by
                    obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hst
                    exact Array.getElem_mem_toList hlt
                  have hsfree := hstmts_free stmt hst_mem
                  dsimp only
                  rw [evalStatement_wideSlice_eq_of_stmtFree hsfree]

/-! ## Part 2. Lockstep Simulation Theorems Against Vendored `Miri` -/

/-! ### 2.1 `ptr::from_raw_parts(_mut)` & `ptr::slice_from_raw_parts(_mut)` (`AggregateKind.rawPtr`) -/

/-- Symbolic lockstep simulation for `AggregateKind.rawPtr` (`ptr::from_raw_parts`
/ `ptr::slice_from_raw_parts(_mut)`) on provenance-carrying data pointers over
`[T]` and `str`:
* Anneal `evalAggregateRawPtr` evaluates `[dataOp, metaOp]` to
  `[.ptr p 8, .scalar lenSc]` and returns `.ok (.aggregate 0 [.ptr p 8, .scalar ⟨lenSc.bits, 8⟩])`.
* Vendored `Miri.Interpreter.writeAggregate` on `AggregateKind.RawPtr` reads the
  pointer `mptr` and length scalar `mlen`, calls `Immediate.newPointerWithMeta`,
  and writes the 16-byte `.scalarPair` satisfying `WideSliceImmediateRel`. -/
theorem evalAggregateRawPtr_wideSlice_provenance_simulation
    {allocMap : List AllocMapEntry}
    {locals locals' : List LocalSlot} {mem : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {pointeeTy : Ty} {dataOp metaOp : Operand}
    {p : ProvenancePtr} {lenSc : MirAst.ScalarInt}
    {mptr : Miri.Memory.Pointer AnnealProv} {mlen : Miri.Memory.ScalarInt}
    (hptrBytes : layoutPointerBytes layouts = 8)
    (hwide : wideAggregatePointeeIsDyn? pointeeTy = some false)
    (heval :
      evalOperands locals [dataOp, metaOp] mem.borrows mem.globals layouts
        mem.callerLocals localDecls mem.callStack =
      .ok [.ptr p 8, .scalar lenSc] locals')
    (hptr : PtrRel allocMap p mptr)
    (hlen : ScalarRel lenSc mlen)
    (hlen_sz : lenSc.sizeBytes = 8) :
    evalRvalue locals (.aggregate (.rawPtr pointeeTy .not) [dataOp, metaOp])
      mem localDecls layouts =
      .ok (.aggregate 0 [.ptr p 8, .scalar ⟨lenSc.bits, 8⟩]) locals' mem ∧
    evalRvalue locals (.aggregate (.rawPtr pointeeTy .mut) [dataOp, metaOp])
      mem localDecls layouts =
      .ok (.aggregate 0 [.ptr p 8, .scalar ⟨lenSc.bits, 8⟩]) locals' mem ∧
    Miri.Interpreter.Immediate.newPointerWithMeta
      ⟨mptr.offset, some mptr.provenance⟩
      (.metadata (.fromScalarInt mlen))
      annealTargetDataLayout =
      .ok (.scalarPair
        (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)
        (.fromScalarInt mlen)) ∧
    WideSliceImmediateRel allocMap
      (.aggregate 0 [.ptr p 8, .scalar ⟨lenSc.bits, 8⟩])
      (.scalarPair
        (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)
        (.fromScalarInt mlen)) := by
  rcases lenSc with ⟨lbits, lsz⟩
  dsimp only at hlen_sz
  subst hlen_sz
  refine ⟨?_, ?_, rfl, .provenance hptr hlen rfl⟩
  · dsimp only [evalRvalue, evalAggregateRawPtr]
    rw [hptrBytes, heval]
    dsimp only
    rw [hwide]
    rfl
  · dsimp only [evalRvalue, evalAggregateRawPtr]
    rw [hptrBytes, heval]
    dsimp only
    rw [hwide]
    rfl

/-- Symbolic lockstep simulation for `AggregateKind.rawPtr` on provenance-free
scalar-address data pointers (`ptr::without_provenance` / integer-cast data
pointer) over `[T]` and `str`:
* Anneal `evalAggregateRawPtr` wraps `addrSc` and `lenSc` modulo `2^64` and returns
  `.ok (.aggregate 0 [.scalar addrSc, .scalar lenSc])`.
* Vendored `Miri.Interpreter.Immediate.newPointerWithMeta` on
  `Pointer.withoutProvenance (UInt64.ofNat addrSc.bits)` and `.metadata (.fromScalarInt mlen)`
  returns `.ok (.scalarPair (.fromScalarInt maddr) (.fromScalarInt mlen))`
  satisfying `WideSliceImmediateRel`. -/
theorem evalAggregateRawPtr_wideSlice_scalarAddr_simulation
    {allocMap : List AllocMapEntry}
    {locals locals' : List LocalSlot} {mem : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {pointeeTy : Ty} {dataOp metaOp : Operand}
    {addrSc lenSc : MirAst.ScalarInt}
    {mlen : Miri.Memory.ScalarInt}
    (hptrBytes : layoutPointerBytes layouts = 8)
    (hwide : wideAggregatePointeeIsDyn? pointeeTy = some false)
    (heval :
      evalOperands locals [dataOp, metaOp] mem.borrows mem.globals layouts
        mem.callerLocals localDecls mem.callStack =
      .ok [.scalar addrSc, .scalar lenSc] locals')
    (haddr_lt : addrSc.bits < 2 ^ 64)
    (hlen : ScalarRel lenSc mlen)
    (haddr_sz : addrSc.sizeBytes = 8)
    (hlen_sz : lenSc.sizeBytes = 8) :
    ∃ maddr,
      ScalarRel addrSc maddr ∧
      evalRvalue locals (.aggregate (.rawPtr pointeeTy .not) [dataOp, metaOp])
        mem localDecls layouts =
        .ok (.aggregate 0 [.scalar addrSc, .scalar lenSc]) locals' mem ∧
      Miri.Interpreter.Immediate.newPointerWithMeta
        (Miri.Memory.Pointer.withoutProvenance (Prov := AnnealProv) (UInt64.ofNat addrSc.bits))
        (.metadata (.fromScalarInt mlen))
        annealTargetDataLayout =
        .ok (.scalarPair (.fromScalarInt maddr) (.fromScalarInt mlen)) ∧
      WideSliceImmediateRel allocMap
        (.aggregate 0 [.scalar addrSc, .scalar lenSc])
        (.scalarPair (.fromScalarInt maddr) (.fromScalarInt mlen)) := by
  obtain ⟨maddr, htry_addr, haddr0⟩ := tryFromUInt_u64_spec haddr_lt
  have haddr : ScalarRel addrSc maddr := by
    rcases addrSc with ⟨abits, asz⟩
    dsimp only at haddr_sz
    subst haddr_sz
    exact haddr0
  have hwrap_addr : wrapScalarBits addrSc.bits (scalarModulus 8) = addrSc.bits := by
    have hw := haddr.wrapScalarBits_self
    rw [haddr_sz] at hw
    exact hw
  have hwrap_len : wrapScalarBits lenSc.bits (scalarModulus 8) = lenSc.bits := by
    have hw := hlen.wrapScalarBits_self
    rw [hlen_sz] at hw
    exact hw
  have hu64_addr : (UInt64.ofNat addrSc.bits).toNat = addrSc.bits :=
    Nat.mod_eq_of_lt haddr_lt
  refine ⟨maddr, haddr, ?_, ?_, .scalarAddr haddr hlen haddr_sz hlen_sz⟩
  · rcases addrSc with ⟨abits, asz⟩
    rcases lenSc with ⟨lbits, lsz⟩
    dsimp only at haddr_sz hlen_sz hwrap_addr hwrap_len
    subst haddr_sz; subst hlen_sz
    dsimp only [evalRvalue, evalAggregateRawPtr]
    rw [hptrBytes, heval]
    dsimp only
    rw [hwide, hwrap_addr, hwrap_len]
    rfl
  · unfold Miri.Interpreter.Immediate.newPointerWithMeta
      Miri.Memory.Pointer.withoutProvenance Miri.Memory.Scalar.fromMaybePointer
    change (do
      let scalar ←
        (do
          let s ← Miri.Memory.ScalarInt.tryFromUInt
            (BitVec.ofNat 128 (UInt64.ofNat addrSc.bits).toNat)
            (Miri.ABI.Size.ofBytes 8) |>.mapError _
          match s with
          | some s => return Miri.Memory.Scalar.fromScalarInt s
          | none => throw _) |>.mapError Miri.Interpreter.ImmediateError.scalar
      return Miri.Interpreter.Immediate.scalarPair scalar (.fromScalarInt mlen)) = _
    rw [hu64_addr, htry_addr]
    rfl

/-! ### 2.2 `ptr::metadata` (`UnOp.ptrMetadata` vs. `Miri.Interpreter.ScalarOps.unary .PtrMetadata`) -/

/-- Symbolic lockstep simulation for `Rvalue.unaryOp .ptrMetadata` on a wide
slice/str pointer (`WideSliceImmediateRel`), proving that both Anneal's
`evalUnaryPtrMetadata` and vendored `Miri.Interpreter.ScalarOps.unary .PtrMetadata`
extract the 8-byte `usize` length metadata without touching memory (even when
the data pointer is OOB, dangling, or `.disabled`). -/
theorem evalUnaryPtrMetadata_wideSlice_simulation
    {allocMap : List AllocMapEntry}
    {locals locals' : List LocalSlot} {mem : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {op : Operand} {v : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    {ptrTyId : Miri.MIR.TyId} {ptrLayoutData : Miri.ABI.LayoutData}
    (hptrBytes : layoutPointerBytes layouts = 8)
    (hwideTy : isWideSlicePtrTyId ptrTyId = true)
    (hnonWideFalse : isNonWidePtrAggregateTy (operandTy localDecls layouts op) = false)
    (heval :
      evalOperand locals op mem.borrows mem.globals layouts
        mem.callerLocals localDecls mem.callStack = .ok v locals')
    (hrel : WideSliceImmediateRel allocMap v imm)
    (st : AnnealStepState) :
    ∃ lenSc mlen,
      lenSc.sizeBytes = 8 ∧
      ScalarRel lenSc mlen ∧
      evalRvalue locals (.unaryOp .ptrMetadata op) mem localDecls layouts =
        .ok (.scalar lenSc) locals' mem ∧
      Miri.Interpreter.ScalarOps.unary
        (annealScalarOpsHooksWideSlice localDecls layouts) ()
        .PtrMetadata ⟨imm, ⟨ptrTyId, ptrLayoutData⟩⟩ st =
        .ok ⟨.scalar (.fromScalarInt mlen),
             translateTy { kind := .uint .usize, layoutIdx := 0 }⟩ st := by
  have hcls : classifyEncodedTyIdWideSlice ptrTyId = .ok .pointer := by
    unfold classifyEncodedTyIdWideSlice
    rw [hwideTy]
    rfl
  cases hrel with
  | @provenance p lenSc mptr mlen hptr hlen hlen_sz =>
      refine ⟨lenSc, mlen, hlen_sz, hlen, ?_, ?_⟩
      · rcases lenSc with ⟨lbits, lsz⟩
        dsimp only at hlen_sz
        subst hlen_sz
        dsimp only [evalRvalue, evalUnaryPtrMetadata]
        rw [hptrBytes, heval]
        rfl
      · unfold Miri.Interpreter.ScalarOps.unary annealScalarOpsHooksWideSlice
          annealScalarOpsHooks annealDerefValidityWideSlice
        simp only [hcls, hwideTy, ↓reduceIte, Miri.Interpreter.Immediate.toScalarAndMeta,
          Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
        rfl
  | @scalarAddr addrSc lenSc maddr mlen haddr hlen haddr_sz hlen_sz =>
      refine ⟨lenSc, mlen, hlen_sz, hlen, ?_, ?_⟩
      · have hwrap_len : wrapScalarBits lenSc.bits (scalarModulus 8) = lenSc.bits := by
          have hw := hlen.wrapScalarBits_self
          rw [hlen_sz] at hw
          exact hw
        rcases addrSc with ⟨abits, asz⟩
        rcases lenSc with ⟨lbits, lsz⟩
        dsimp only at haddr_sz hlen_sz hwrap_len
        subst haddr_sz; subst hlen_sz
        dsimp only [evalRvalue, evalUnaryPtrMetadata]
        rw [hptrBytes, heval, hnonWideFalse]
        change RvalueEvalResult.ok (.scalar ⟨wrapScalarBits lbits (scalarModulus 8), 8⟩) locals' mem = _
        rw [hwrap_len]
      · unfold Miri.Interpreter.ScalarOps.unary annealScalarOpsHooksWideSlice
          annealScalarOpsHooks annealDerefValidityWideSlice
        simp only [hcls, hwideTy, ↓reduceIte, Miri.Interpreter.Immediate.toScalarAndMeta,
          Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
        rfl

/-- Symbolic lockstep simulation for `Rvalue.unaryOp .ptrMetadata` on a thin
provenance-carrying pointer (`.ptr p 8`), returning `Value.unit` in Anneal and
`⟨.uninit, translateTy ()⟩` in vendored `Miri.Interpreter.ScalarOps.unary .PtrMetadata`. -/
theorem evalUnaryPtrMetadata_thin_simulation
    {allocMap : List AllocMapEntry}
    {locals locals' : List LocalSlot} {mem : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {op : Operand} {p : ProvenancePtr}
    {mptr : Miri.Memory.Pointer AnnealProv}
    (hptrBytes : layoutPointerBytes layouts = 8)
    (heval :
      evalOperand locals op mem.borrows mem.globals layouts
        mem.callerLocals localDecls mem.callStack = .ok (.ptr p 8) locals')
    (hptr : PtrRel allocMap p mptr)
    (st : AnnealStepState) :
    evalRvalue locals (.unaryOp .ptrMetadata op) mem localDecls layouts =
      .ok .unit locals' mem ∧
    Miri.Interpreter.ScalarOps.unary
      (annealScalarOpsHooksWideSlice localDecls layouts) ()
      .PtrMetadata
      ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
       ⟨60, pointerLayoutData false⟩⟩ st =
      .ok ⟨.uninit, translateTy { kind := .tuple .nil, layoutIdx := 0 }⟩ st := by
  have _ := hptr
  constructor
  · dsimp only [evalRvalue, evalUnaryPtrMetadata]
    rw [hptrBytes, heval]
  · rfl

/-! ### 2.3 `to_raw_parts` (`CastKind.ptrToPtr` Wide-to-Thin & Wide-to-Wide + Round-Trip) -/

/-- Symbolic lockstep simulation for wide-to-thin `CastKind.ptrToPtr`
(`*const [T] as *const ()` / `*const T`, the data-pointer projection of
`to_raw_parts`) on a provenance-carrying wide slice pointer:
* Anneal `evalCastPtrToPtr` drops the length metadata and returns `.ok (.ptr p 8)`.
* Vendored `Miri.Interpreter.Cast.ptrToPtr` drops the second component of
  `.scalarPair` and returns `⟨.scalar (Scalar.fromPointer annealTargetDataLayout mptr), targetLay⟩`. -/
theorem evalCastPtrToPtr_wideToThin_provenance_simulation
    {allocMap : List AllocMapEntry}
    {locals locals' : List LocalSlot} {mem : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {op : Operand} {targetTy : Ty}
    {p : ProvenancePtr} {lenSc : MirAst.ScalarInt}
    {mptr : Miri.Memory.Pointer AnnealProv} {mlen : Miri.Memory.ScalarInt}
    {srcTyId dstTyId : Miri.MIR.TyId}
    (hptrBytes : layoutPointerBytes layouts = 8)
    (hthinTarget : isThinRawPtrTy targetTy = true)
    (hborrowNone : lookupBorrow mem.borrows p.tag = none)
    (heval :
      evalOperand locals op mem.borrows mem.globals layouts
        mem.callerLocals localDecls mem.callStack =
      .ok (.aggregate 0 [.ptr p 8, .scalar lenSc]) locals')
    (hptr : PtrRel allocMap p mptr)
    (hlen : ScalarRel lenSc mlen)
    (hlen_sz : lenSc.sizeBytes = 8)
    (hsrc_info : ∃ pt, castTypeInfoOfEncodedTyIdWideSlice srcTyId = .ok (.rawPointer pt))
    (hdst_info : ∃ pt, castTypeInfoOfEncodedTyIdWideSlice dstTyId = .ok (.rawPointer pt))
    (st : AnnealStepState) :
    let srcLay : Miri.Interpreter.LocalLayout := ⟨srcTyId, widePointerLayoutData false⟩
    let dstLay : Miri.Interpreter.LocalLayout := ⟨dstTyId, pointerLayoutData false⟩
    evalRvalue locals (.cast .ptrToPtr op targetTy) mem localDecls layouts =
      .ok (.ptr p 8) locals' mem ∧
    Miri.Interpreter.Cast.ptrToPtr
      (annealCastHooksWideSlice layouts) ()
      ⟨.scalarPair
        (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)
        (.fromScalarInt mlen),
       srcLay⟩
      dstLay st =
      .ok ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr), dstLay⟩ st ∧
    PtrRel allocMap p mptr := by
  have _ := hlen
  obtain ⟨srcPt, hsrc⟩ := hsrc_info
  obtain ⟨dstPt, hdst⟩ := hdst_info
  refine ⟨?_, ?_, hptr⟩
  · rcases lenSc with ⟨lbits, lsz⟩
    dsimp only at hlen_sz
    subst hlen_sz
    simp [evalRvalue, evalCastPtrToPtr, hptrBytes, heval, hthinTarget, hborrowNone]
  · unfold Miri.Interpreter.Cast.ptrToPtr annealCastHooksWideSlice
    dsimp only
    rw [hsrc, hdst]
    rfl

/-- Symbolic lockstep simulation for wide-to-wide `CastKind.ptrToPtr`
(`*const [T] as *mut [T]` or `*const str as *const [u8]`) on a wide slice/str
pointer (`WideSliceImmediateRel`): both Anneal `evalCastPtrToPtr` and vendored
`Miri.Interpreter.Cast.ptrToPtr` preserve the 16-byte wide pointer unchanged. -/
theorem evalCastPtrToPtr_wideToWide_provenance_simulation
    {allocMap : List AllocMapEntry}
    {locals locals' : List LocalSlot} {mem : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {op : Operand} {targetTy : Ty}
    {p : ProvenancePtr} {lenSc : MirAst.ScalarInt}
    {mptr : Miri.Memory.Pointer AnnealProv} {mlen : Miri.Memory.ScalarInt}
    {srcTyId dstTyId : Miri.MIR.TyId}
    (hptrBytes : layoutPointerBytes layouts = 8)
    (hthinFalse : isThinRawPtrTy targetTy = false)
    (hwideSliceTarget : wideRawPtrIsDyn? targetTy = some false)
    (heval :
      evalOperand locals op mem.borrows mem.globals layouts
        mem.callerLocals localDecls mem.callStack =
      .ok (.aggregate 0 [.ptr p 8, .scalar lenSc]) locals')
    (hptr : PtrRel allocMap p mptr)
    (hlen : ScalarRel lenSc mlen)
    (hlen_sz : lenSc.sizeBytes = 8)
    (hsrc_info : ∃ pt, castTypeInfoOfEncodedTyIdWideSlice srcTyId = .ok (.rawPointer pt))
    (hdst_info : ∃ pt, castTypeInfoOfEncodedTyIdWideSlice dstTyId = .ok (.rawPointer pt))
    (st : AnnealStepState) :
    let srcLay : Miri.Interpreter.LocalLayout := ⟨srcTyId, widePointerLayoutData false⟩
    let dstLay : Miri.Interpreter.LocalLayout := ⟨dstTyId, widePointerLayoutData false⟩
    let imm : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair
        (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)
        (.fromScalarInt mlen)
    evalRvalue locals (.cast .ptrToPtr op targetTy) mem localDecls layouts =
      .ok (.aggregate 0 [.ptr p 8, .scalar lenSc]) locals' mem ∧
    Miri.Interpreter.Cast.ptrToPtr
      (annealCastHooksWideSlice layouts) ()
      ⟨imm, srcLay⟩ dstLay st =
      .ok ⟨imm, dstLay⟩ st ∧
    WideSliceImmediateRel allocMap (.aggregate 0 [.ptr p 8, .scalar lenSc]) imm := by
  obtain ⟨srcPt, hsrc⟩ := hsrc_info
  obtain ⟨dstPt, hdst⟩ := hdst_info
  refine ⟨?_, ?_, .provenance hptr hlen hlen_sz⟩
  · rcases lenSc with ⟨lbits, lsz⟩
    dsimp only at hlen_sz
    subst hlen_sz
    simp [evalRvalue, evalCastPtrToPtr, hptrBytes, heval, hthinFalse, hwideSliceTarget]
  · unfold Miri.Interpreter.Cast.ptrToPtr annealCastHooksWideSlice
    dsimp only
    rw [hsrc, hdst]
    rfl

/-- `to_raw_parts` → `from_raw_parts` round-trip identity — vendored `Miri` side, specialised to
`*const [u32]` (`wideRawSlicePtrTyId 22`) and a thin `TyId 60` target: decomposing a wide
slice pointer via `Cast.ptrToPtr` (thin data pointer) and `ScalarOps.unary .PtrMetadata` (usize
length), then reconstructing via `Immediate.newPointerWithMeta`, recovers the exact original
`.scalarPair`. The two-sided statement (Anneal `evalRvalue` cast / `ptrMetadata` /
`AggregateKind.rawPtr` composed with the generic-`TyId` `Miri` side) is
`wideSlice_to_from_raw_parts_roundtrip_two_sided`. -/
theorem wideSlice_to_from_raw_parts_roundtrip_simulation
    {allocMap : List AllocMapEntry}
    {p : ProvenancePtr} {lenSc : MirAst.ScalarInt}
    {mptr : Miri.Memory.Pointer AnnealProv} {mlen : Miri.Memory.ScalarInt}
    (hptr : PtrRel allocMap p mptr)
    (hlen : ScalarRel lenSc mlen)
    (hlen_sz : lenSc.sizeBytes = 8)
    (st : AnnealStepState) :
    let wideVal : Value := .aggregate 0 [.ptr p 8, .scalar lenSc]
    let wideImm : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair
        (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)
        (.fromScalarInt mlen)
    let wideLay : Miri.Interpreter.LocalLayout :=
      ⟨wideRawSlicePtrTyId 22, widePointerLayoutData false⟩
    let thinLay : Miri.Interpreter.LocalLayout :=
      ⟨60, pointerLayoutData false⟩
    Miri.Interpreter.Cast.ptrToPtr (annealCastHooksWideSlice emptyLayoutTable) ()
      ⟨wideImm, wideLay⟩ thinLay st =
      .ok ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr), thinLay⟩ st ∧
    Miri.Interpreter.ScalarOps.unary (annealScalarOpsHooksWideSlice .nil emptyLayoutTable) ()
      .PtrMetadata ⟨wideImm, wideLay⟩ st =
      .ok ⟨.scalar (.fromScalarInt mlen),
           translateTy { kind := .uint .usize, layoutIdx := 0 }⟩ st ∧
    Miri.Interpreter.Immediate.newPointerWithMeta
      ⟨mptr.offset, some mptr.provenance⟩
      (.metadata (.fromScalarInt mlen))
      annealTargetDataLayout = .ok wideImm ∧
    WideSliceImmediateRel allocMap wideVal wideImm :=
  ⟨rfl, rfl, rfl, .provenance hptr hlen hlen_sz⟩

/-- **Two-sided `to_raw_parts` → `from_raw_parts` round trip
(`wideSlice_to_from_raw_parts_roundtrip_two_sided`)** for any wide slice/str raw-pointer operand,
any thin target type, and any wide-slice source / raw-pointer destination `TyId`s:
* Anneal: `p as *const U` (`CastKind.ptrToPtr`, global-backed) yields `.ptr p 8`,
  `PtrMetadata(p)` yields `.scalar lenSc`, and reassembling those parts with
  `AggregateKind.rawPtr` yields the ORIGINAL wide value `.aggregate 0 [.ptr p 8, .scalar lenSc]`;
* vendored `Miri`: `Cast.ptrToPtr` yields `Scalar.fromPointer mptr`, `ScalarOps.unary
  .PtrMetadata` yields `.fromScalarInt mlen`, and `Immediate.newPointerWithMeta` rebuilds the
  original `.scalarPair`;
* both sides stay related by `PtrRel` / `ScalarRel` / `WideSliceImmediateRel`. -/
theorem wideSlice_to_from_raw_parts_roundtrip_two_sided
    {allocMap : List AllocMapEntry}
    {locals locals₁ locals₂ : List LocalSlot} {mem : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {wideOp dataOp metaOp : Operand} {thinTy pointeeTy : Ty}
    {p : ProvenancePtr} {lenSc : MirAst.ScalarInt}
    {mptr : Miri.Memory.Pointer AnnealProv} {mlen : Miri.Memory.ScalarInt}
    {srcTyId dstTyId : Miri.MIR.TyId}
    (hptrBytes : layoutPointerBytes layouts = 8)
    (hthinTarget : isThinRawPtrTy thinTy = true)
    (hborrowNone : lookupBorrow mem.borrows p.tag = none)
    (hwide : wideAggregatePointeeIsDyn? pointeeTy = some false)
    (hevalWide :
      evalOperand locals wideOp mem.borrows mem.globals layouts
        mem.callerLocals localDecls mem.callStack =
      .ok (.aggregate 0 [.ptr p 8, .scalar lenSc]) locals₁)
    (hevalParts :
      evalOperands locals₁ [dataOp, metaOp] mem.borrows mem.globals layouts
        mem.callerLocals localDecls mem.callStack =
      .ok [.ptr p 8, .scalar lenSc] locals₂)
    (hptr : PtrRel allocMap p mptr)
    (hlen : ScalarRel lenSc mlen)
    (hlen_sz : lenSc.sizeBytes = 8)
    (hsrcWide : isWideSlicePtrTyId srcTyId = true)
    (hsrc_info : ∃ pt, castTypeInfoOfEncodedTyIdWideSlice srcTyId = .ok (.rawPointer pt))
    (hdst_info : ∃ pt, castTypeInfoOfEncodedTyIdWideSlice dstTyId = .ok (.rawPointer pt))
    (st : AnnealStepState) :
    let wideVal : Value := .aggregate 0 [.ptr p 8, .scalar lenSc]
    let wideImm : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr) (.fromScalarInt mlen)
    let srcLay : Miri.Interpreter.LocalLayout := ⟨srcTyId, widePointerLayoutData false⟩
    let dstLay : Miri.Interpreter.LocalLayout := ⟨dstTyId, pointerLayoutData false⟩
    evalRvalue locals (.cast .ptrToPtr wideOp thinTy) mem localDecls layouts =
      .ok (.ptr p 8) locals₁ mem ∧
    evalRvalue locals (.unaryOp .ptrMetadata wideOp) mem localDecls layouts =
      .ok (.scalar lenSc) locals₁ mem ∧
    evalRvalue locals₁ (.aggregate (.rawPtr pointeeTy .not) [dataOp, metaOp]) mem localDecls
        layouts =
      .ok wideVal locals₂ mem ∧
    Miri.Interpreter.Cast.ptrToPtr (annealCastHooksWideSlice layouts) () ⟨wideImm, srcLay⟩ dstLay
        st =
      .ok ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr), dstLay⟩ st ∧
    Miri.Interpreter.ScalarOps.unary (annealScalarOpsHooksWideSlice localDecls layouts) ()
        .PtrMetadata ⟨wideImm, srcLay⟩ st =
      .ok ⟨.scalar (.fromScalarInt mlen), translateTy { kind := .uint .usize, layoutIdx := 0 }⟩
        st ∧
    Miri.Interpreter.Immediate.newPointerWithMeta ⟨mptr.offset, some mptr.provenance⟩
        (.metadata (.fromScalarInt mlen)) annealTargetDataLayout = .ok wideImm ∧
    WideSliceImmediateRel allocMap wideVal wideImm := by
  dsimp only
  have hcast := evalCastPtrToPtr_wideToThin_provenance_simulation hptrBytes hthinTarget
    hborrowNone hevalWide hptr hlen hlen_sz hsrc_info hdst_info st
  have hagg := evalAggregateRawPtr_wideSlice_provenance_simulation hptrBytes hwide hevalParts
    hptr hlen hlen_sz
  have hcls : classifyEncodedTyIdWideSlice srcTyId = .ok .pointer := by
    unfold classifyEncodedTyIdWideSlice
    rw [hsrcWide]
    rfl
  have hlenEq : (⟨lenSc.bits, 8⟩ : MirAst.ScalarInt) = lenSc := by
    rcases lenSc with ⟨b, sz⟩
    dsimp only at hlen_sz
    subst hlen_sz
    rfl
  refine ⟨hcast.1, ?_, ?_, hcast.2.1, ?_, rfl, .provenance hptr hlen hlen_sz⟩
  · rcases lenSc with ⟨lbits, lsz⟩
    dsimp only at hlen_sz
    subst hlen_sz
    dsimp only [evalRvalue, evalUnaryPtrMetadata]
    rw [hptrBytes, hevalWide]
    rfl
  · rw [hagg.1, hlenEq]
  · unfold Miri.Interpreter.ScalarOps.unary annealScalarOpsHooksWideSlice
      annealScalarOpsHooks annealDerefValidityWideSlice
    simp only [hcls, hsrcWide, ↓reduceIte, Miri.Interpreter.Immediate.toScalarAndMeta,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
    rfl

/-! ### 2.4 `PlaceDynamic.{length, index, subslice}` & Two-Sided Slice Projections

`annealPlaceProjectionHooksWideSlice` is wired into `annealEvalOperandWideSlice`,
`annealEvalPlaceWideSlice`, `annealRvalueHooksWideSlice`, and
`annealStepHooksWideSlice` so projected places on wide-slice locals (`*s`,
`(*s)[i]`, `(*s)[from..to]`, and `Rvalue.len (*s)`) execute through vendored
`Miri.Interpreter.PlaceDynamic` during `Miri.Interpreter.Step.step`. Below we
provide both the standalone `PlaceDynamic` building blocks and their two-sided
Anneal-vs-Miri lockstep simulation theorems (accompanied by concrete
`stepMirFn` / `Miri.Interpreter.Step.step` witnesses in Part 3). -/

/-- Vendored `Miri.Interpreter.PlaceDynamic.length` on a
dereferenced unsized slice/str `RuntimePlace AnnealProv`: extracts the 8-byte
length `UInt64.ofNat lenSc.bits` from `mplace.metadata = .metadata (.fromScalarInt mlen)`
(the two-sided statement pairing this with Anneal's `evalRvalue (.len ...)` and
`ScalarOps.unary .PtrMetadata` is `evalRvalue_len_wideSlice_two_sided_simulation`). -/
theorem placeDynamic_length_wideSlice_simulation
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {ptr : Miri.Memory.Pointer (Option AnnealProv)}
    {lenSc : MirAst.ScalarInt} {mlen : Miri.Memory.ScalarInt}
    {sliceLay : Miri.Interpreter.LocalLayout}
    (hlen : ScalarRel lenSc mlen)
    (hlen_sz : lenSc.sizeBytes = 8)
    (hunsized : sliceLay.layout.isSized = false)
    (hsliceOrStr : sliceLay.ty == strPointeeTyId || (2100 ≤ sliceLay.ty && sliceLay.ty < 2200))
    (st : AnnealStepState) :
    Miri.Interpreter.PlaceDynamic.length
      (annealPlaceProjectionHooksWideSlice localDecls layouts) ()
      ⟨.memory ⟨ptr, .metadata (.fromScalarInt mlen), none⟩, sliceLay⟩ st =
      .ok (UInt64.ofNat lenSc.bits) st := by
  have htarget := fromScalarInt_toTargetUsize_u64 hlen hlen_sz
  have hsz8 : Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits =
      Miri.ABI.Size.ofBytes 8 := rfl
  unfold Miri.Interpreter.PlaceDynamic.length annealPlaceProjectionHooksWideSlice
  simp only [hunsized, hsliceOrStr, Bool.not_false, ↓reduceIte,
    pure_bind, hsz8, Except.mapError]
  rw [EStateM.bind_eq_ok (a := Miri.Memory.Scalar.fromScalarInt mlen) (s' := st)
    (by with_unfolding_all rfl)]
  rw [htarget]
  with_unfolding_all rfl

/-- Out-of-bounds slice index (`idx ≥ len`) in vendored
`Miri.Interpreter.PlaceDynamic.index` raises `StepError.undefinedBehavior`
(the two-sided statement pairing this with Anneal's `readProjectedValue` /
`writeProjectedValue` OOB UB is `evalPlace_index_wideSlice_oob_ub_two_sided_simulation`,
and concrete `Step.step` / `stepMirFn` runs are in
`w_wideSlice_index_oob_and_dangling_deref_ub_agrees`). -/
theorem placeDynamic_index_wideSlice_oob_ub_simulation
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {ptr : Miri.Memory.Pointer (Option AnnealProv)}
    {lenSc : MirAst.ScalarInt} {mlen : Miri.Memory.ScalarInt}
    {elemLay : Miri.ABI.LayoutData} {elemId : Miri.MIR.TyId}
    {idx : UInt64}
    (hlen : ScalarRel lenSc mlen)
    (hlen_sz : lenSc.sizeBytes = 8)
    (helemId : elemId < 100)
    (hoob : UInt64.ofNat lenSc.bits ≤ idx)
    (st : AnnealStepState) :
    ∃ msg,
      Miri.Interpreter.PlaceDynamic.index
        (annealPlaceProjectionHooksWideSlice localDecls layouts) ()
        ⟨.memory ⟨ptr, .metadata (.fromScalarInt mlen), none⟩,
         ⟨slicePointeeTyId elemId, unsizedSliceLayoutData elemLay⟩⟩ idx st =
        .error (.undefinedBehavior msg) st := by
  have hsliceOrStr :
      (slicePointeeTyId elemId == strPointeeTyId ||
        (2100 ≤ slicePointeeTyId elemId && slicePointeeTyId elemId < 2200)) = true := by
    unfold slicePointeeTyId strPointeeTyId
    rw [Bool.or_eq_true]
    right
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨Nat.le_add_right 2100 elemId, Nat.add_lt_add_left helemId 2100⟩
  have hlen_eval :=
    placeDynamic_length_wideSlice_simulation
      (localDecls := localDecls) (layouts := layouts) (ptr := ptr)
      (sliceLay := ⟨slicePointeeTyId elemId, unsizedSliceLayoutData elemLay⟩)
      hlen hlen_sz rfl hsliceOrStr st
  refine ⟨s!"place index {idx} out of bounds for {UInt64.ofNat lenSc.bits}", ?_⟩
  unfold Miri.Interpreter.PlaceDynamic.index
  dsimp only [unsizedSliceLayoutData, Bind.bind, EStateM.bind] at hlen_eval ⊢
  rw [hlen_eval]
  dsimp only
  simp [hoob, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- Out-of-bounds slice subslice (`fromEnd = true` with `fromIndex + to > len`)
in vendored `Miri.Interpreter.PlaceDynamic.subslice` raises
`StepError.undefinedBehavior "subslice bounds"` (the two-sided statement pairing
this with Anneal's `readProjectedValue` subslice OOB UB is
`evalPlace_subslice_wideSlice_oob_ub_two_sided_simulation`). -/
theorem placeDynamic_subslice_wideSlice_oob_ub_simulation
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {ptr : Miri.Memory.Pointer (Option AnnealProv)}
    {lenSc : MirAst.ScalarInt} {mlen : Miri.Memory.ScalarInt}
    {elemLay : Miri.ABI.LayoutData} {elemId : Miri.MIR.TyId}
    {fromIndex to : UInt64}
    (hlen : ScalarRel lenSc mlen)
    (hlen_sz : lenSc.sizeBytes = 8)
    (helemId : elemId < 100)
    (hoob : (UInt64.ofNat lenSc.bits).toNat < fromIndex.toNat + to.toNat)
    (st : AnnealStepState) :
    Miri.Interpreter.PlaceDynamic.subslice
      (annealPlaceProjectionHooksWideSlice localDecls layouts) ()
      ⟨.memory ⟨ptr, .metadata (.fromScalarInt mlen), none⟩,
       ⟨slicePointeeTyId elemId, unsizedSliceLayoutData elemLay⟩⟩ fromIndex to true st =
      .error (.undefinedBehavior "subslice bounds") st := by
  have hsliceOrStr :
      (slicePointeeTyId elemId == strPointeeTyId ||
        (2100 ≤ slicePointeeTyId elemId && slicePointeeTyId elemId < 2200)) = true := by
    unfold slicePointeeTyId strPointeeTyId
    rw [Bool.or_eq_true]
    right
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨Nat.le_add_right 2100 elemId, Nat.add_lt_add_left helemId 2100⟩
  have hlen_eval :=
    placeDynamic_length_wideSlice_simulation
      (localDecls := localDecls) (layouts := layouts) (ptr := ptr)
      (sliceLay := ⟨slicePointeeTyId elemId, unsizedSliceLayoutData elemLay⟩)
      hlen hlen_sz rfl hsliceOrStr st
  have hcond :
      (decide (fromIndex.toNat + to.toNat ≥ 2 ^ 64) ||
        decide (fromIndex.toNat + to.toNat > (UInt64.ofNat lenSc.bits).toNat)) = true := by
    rw [Bool.or_eq_true]
    exact Or.inr (decide_eq_true hoob)
  unfold Miri.Interpreter.PlaceDynamic.subslice
  dsimp only [Bind.bind, EStateM.bind]
  rw [hlen_eval]
  dsimp only [↓reduceIte]
  rw [hcond]
  rfl

/-- **Two-sided `Rvalue.len (*s)` lockstep simulation
(`evalRvalue_len_wideSlice_two_sided_simulation`)**:
For any wide-slice pointer local `sIdx` whose value `.aggregate 0 [.ptr p 8, .scalar lenSc]`
is related via `WideSliceImmediateRel` (`PtrRel allocMap p mptr` and `ScalarRel lenSc mlen`
with `lenSc.sizeBytes = 8`) to `mptr` and `mlen`:
1. Anneal's `evalRvalue locals (.len ⟨sIdx, [.deref]⟩) mem localDecls layouts`
   evaluates `evalPlaceLen` and returns `.ok (.scalar lenSc) locals' mem`;
2. Vendored `Miri.Interpreter.PlaceDynamic.length` on the dereferenced slice
   `RuntimePlace AnnealProv` returns `.ok (UInt64.ofNat lenSc.bits) st`, and
   `Miri.Interpreter.ScalarOps.unary .PtrMetadata` on the resulting
   `arraySliceMetaTyId` reference returns
   `.ok ⟨.scalar (.fromScalarInt mlen), translateTy { kind := .uint .usize, layoutIdx := 0 }⟩ st`;
3. The Anneal and Miri `usize` lengths remain related by `ScalarRel lenSc mlen`. -/
theorem evalRvalue_len_wideSlice_two_sided_simulation
    {allocMap : List AllocMapEntry}
    {locals locals' : List LocalSlot} {mem : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {sIdx : Local} {elemKind : RigidTy} {lIdx : LayoutIdx}
    {p : ProvenancePtr} {lenSc : MirAst.ScalarInt}
    {mptr : Miri.Memory.Pointer AnnealProv} {mlen : Miri.Memory.ScalarInt}
    {sliceLay : Miri.Interpreter.LocalLayout}
    (hptrBytes : layoutPointerBytes layouts = 8)
    (hplaceTy :
      placeTy localDecls layouts ⟨sIdx, [.deref]⟩ =
        some { kind := .slice elemKind, layoutIdx := lIdx })
    (hread :
      evalPlaceRead locals ⟨sIdx, []⟩ mem.borrows mem.globals layouts
        mem.callerLocals localDecls mem.callStack =
        .ok (.aggregate 0 [.ptr p 8, .scalar lenSc]) locals')
    (hborrowNone : lookupBorrow mem.borrows p.tag = none)
    (hglobalNone : lookupGlobalAlloc mem.globals p.allocId = none)
    (hallocNeZero : Nat.beq p.allocId 0 = false)
    (hptr : PtrRel allocMap p mptr)
    (hlen : ScalarRel lenSc mlen)
    (hlen_sz : lenSc.sizeBytes = 8)
    (hunsized : sliceLay.layout.isSized = false)
    (hsliceOrStr : sliceLay.ty == strPointeeTyId || (2100 ≤ sliceLay.ty && sliceLay.ty < 2200))
    (st : AnnealStepState) :
    let mptrOpt : Miri.Memory.Pointer (Option AnnealProv) := ⟨mptr.offset, some mptr.provenance⟩
    let metaImm : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair
        (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)
        (.fromScalarInt mlen)
    evalRvalue locals (.len ⟨sIdx, [.deref]⟩) mem localDecls layouts =
      .ok (.scalar lenSc) locals' mem ∧
    Miri.Interpreter.PlaceDynamic.length
      (annealPlaceProjectionHooksWideSlice localDecls layouts) ()
      ⟨.memory ⟨mptrOpt, .metadata (.fromScalarInt mlen), none⟩, sliceLay⟩ st =
      .ok (UInt64.ofNat lenSc.bits) st ∧
    Miri.Interpreter.ScalarOps.unary
      (annealScalarOpsHooksWideSlice localDecls layouts) ()
      .PtrMetadata ⟨metaImm, ⟨arraySliceMetaTyId, widePointerLayoutData false⟩⟩ st =
      .ok ⟨.scalar (.fromScalarInt mlen),
           translateTy { kind := .uint .usize, layoutIdx := 0 }⟩ st ∧
    WideSliceImmediateRel allocMap (.aggregate 0 [.ptr p 8, .scalar lenSc]) metaImm ∧
    ScalarRel lenSc mlen := by
  have hlen_m :=
    placeDynamic_length_wideSlice_simulation
      (localDecls := localDecls) (layouts := layouts) (ptr := ⟨mptr.offset, some mptr.provenance⟩)
      (sliceLay := sliceLay) hlen hlen_sz hunsized hsliceOrStr st
  refine ⟨?_, hlen_m, rfl, .provenance hptr hlen hlen_sz, hlen⟩
  rcases lenSc with ⟨lbits, lsz⟩
  cases hlen_sz
  simp [evalRvalue, evalPlaceLen, hptrBytes, hplaceTy, hread, hborrowNone, hglobalNone, hallocNeZero]

/-- **Two-sided out-of-bounds wide-slice `Index` UB simulation
(`evalPlace_index_wideSlice_oob_ub_two_sided_simulation`)**:
When `idx ≥ len` (`get? elems idxSc.bits = none` and `UInt64.ofNat lenSc.bits ≤ UInt64.ofNat idxSc.bits`),
BOTH Anneal's `readProjectedValue locals (.aggregate 0 elems) [.index idxLocal]` /
`writeProjectedValue locals (.aggregate 0 elems) [.index idxLocal] v` AND vendored
`Miri.Interpreter.PlaceDynamic.index` fault with undefined behavior! -/
theorem evalPlace_index_wideSlice_oob_ub_two_sided_simulation
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {locals : List LocalSlot} {elems : List Value}
    {idxLocal : Local} {idxSc lenSc : MirAst.ScalarInt}
    {ptr : Miri.Memory.Pointer (Option AnnealProv)}
    {mlen : Miri.Memory.ScalarInt}
    {elemLay : Miri.ABI.LayoutData} {elemId : Miri.MIR.TyId}
    (hidx_slot : get? locals idxLocal = some (.init (.scalar idxSc)))
    (hget_none : get? elems idxSc.bits = none)
    (hlen : ScalarRel lenSc mlen)
    (hlen_sz : lenSc.sizeBytes = 8)
    (helemId : elemId < 100)
    (hoob : UInt64.ofNat lenSc.bits ≤ UInt64.ofNat idxSc.bits)
    (st : AnnealStepState) :
    readProjectedValue locals (.aggregate 0 elems) [.index idxLocal] = .ub ∧
    (∀ v, writeProjectedValue locals (.aggregate 0 elems) [.index idxLocal] v = .ub) ∧
    ∃ msg,
      Miri.Interpreter.PlaceDynamic.index
        (annealPlaceProjectionHooksWideSlice localDecls layouts) ()
        ⟨.memory ⟨ptr, .metadata (.fromScalarInt mlen), none⟩,
         ⟨slicePointeeTyId elemId, unsizedSliceLayoutData elemLay⟩⟩
        (UInt64.ofNat idxSc.bits) st =
        .error (.undefinedBehavior msg) st := by
  refine ⟨?_, ?_, placeDynamic_index_wideSlice_oob_ub_simulation hlen hlen_sz helemId hoob st⟩
  · simp [readProjectedValue, hidx_slot, hget_none]
  · intro v
    simp [writeProjectedValue, hidx_slot, hget_none]

/-- **Two-sided out-of-bounds wide-slice `Subslice` UB simulation
(`evalPlace_subslice_wideSlice_oob_ub_two_sided_simulation`)**:
When `fromEnd = true` and `fromIndex + to > len` (`extractSubslice elems fromIndex.toNat to.toNat true = none`
and `(UInt64.ofNat lenSc.bits).toNat < fromIndex.toNat + to.toNat`), BOTH Anneal's
`readProjectedValue locals (.aggregate 0 elems) [.subslice fromIndex.toNat to.toNat true]`
AND vendored `Miri.Interpreter.PlaceDynamic.subslice` fault with undefined behavior! -/
theorem evalPlace_subslice_wideSlice_oob_ub_two_sided_simulation
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {locals : List LocalSlot} {elems : List Value}
    {ptr : Miri.Memory.Pointer (Option AnnealProv)}
    {lenSc : MirAst.ScalarInt} {mlen : Miri.Memory.ScalarInt}
    {elemLay : Miri.ABI.LayoutData} {elemId : Miri.MIR.TyId}
    {fromIndex to : UInt64}
    (hextract_none : extractSubslice elems fromIndex.toNat to.toNat true = none)
    (hlen : ScalarRel lenSc mlen)
    (hlen_sz : lenSc.sizeBytes = 8)
    (helemId : elemId < 100)
    (hoob : (UInt64.ofNat lenSc.bits).toNat < fromIndex.toNat + to.toNat)
    (st : AnnealStepState) :
    readProjectedValue locals (.aggregate 0 elems)
      [.subslice fromIndex.toNat to.toNat true] = .ub ∧
    Miri.Interpreter.PlaceDynamic.subslice
      (annealPlaceProjectionHooksWideSlice localDecls layouts) ()
      ⟨.memory ⟨ptr, .metadata (.fromScalarInt mlen), none⟩,
       ⟨slicePointeeTyId elemId, unsizedSliceLayoutData elemLay⟩⟩ fromIndex to true st =
      .error (.undefinedBehavior "subslice bounds") st := by
  refine ⟨?_, placeDynamic_subslice_wideSlice_oob_ub_simulation hlen hlen_sz helemId hoob st⟩
  simp [readProjectedValue, hextract_none]

theorem wideSlice_dropValues_eq_drop : ∀ (n : Nat) (xs : List Value), dropValues n xs = xs.drop n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, _ :: xs => wideSlice_dropValues_eq_drop k xs

theorem wideSlice_takeValues_eq_take : ∀ (n : Nat) (xs : List Value), takeValues n xs = xs.take n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, x :: xs => congrArg (x :: ·) (wideSlice_takeValues_eq_take k xs)

/-- **Two-sided borrow-backed `Rvalue.len (*s)` lockstep & OOB boundary simulation
(`evalRvalue_len_wideSlice_borrowBacked_two_sided_simulation`)**:
For any wide-slice pointer local `sIdx` backed by a live non-`.disabled` borrow entry
`lookupBorrow mem.borrows p.tag = some entry` whose target local holds backing slice
elements `elems` at `elemOffset = rawElemOffset + baseIdx`:
1. **In-bounds backing slice (`rawElemOffset + baseIdx + lenSc.bits ≤ elems.length`)**:
   Anneal's `evalRvalue locals (.len ⟨sIdx, [.deref]⟩) mem localDecls layouts` returns
   `.ok (.scalar lenSc) locals' mem`, vendored `Miri.Interpreter.PlaceDynamic.length`
   returns `.ok (UInt64.ofNat lenSc.bits) st`, `Miri.Interpreter.ScalarOps.unary .PtrMetadata`
   returns `.ok ⟨.scalar (.fromScalarInt mlen), translateTy usize⟩ st`, and
   `ScalarRel lenSc mlen` holds.
2. **OOB backing slice (`elems.length < rawElemOffset + baseIdx + lenSc.bits`)**:
   Anneal's `evalRvalue locals (.len ⟨sIdx, [.deref]⟩)` faults with `.ub` (`borrowOk = false`),
   whereas vendored `Miri.Interpreter.PlaceDynamic.length` extracts `lenSc.bits` from
   fat-pointer metadata without dereferencing memory (`DIV-LM-PLACE-LEN-BORROW-BOUNDS`). -/
theorem evalRvalue_len_wideSlice_borrowBacked_two_sided_simulation
    {allocMap : List AllocMapEntry}
    {locals locals' : List LocalSlot} {mem : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {sIdx : Local} {elemKind : RigidTy} {lIdx : LayoutIdx}
    {p : ProvenancePtr} {lenSc : MirAst.ScalarInt}
    {entry : BorrowEntry} {rootVal : Value}
    {containerProj : List ProjectionElem} {baseIdx rawElemOffset : Nat}
    {elems : List Value}
    {mptr : Miri.Memory.Pointer AnnealProv} {mlen : Miri.Memory.ScalarInt}
    {sliceLay : Miri.Interpreter.LocalLayout}
    (hptrBytes : layoutPointerBytes layouts = 8)
    (hplaceTy :
      placeTy localDecls layouts ⟨sIdx, [.deref]⟩ =
        some { kind := .slice elemKind, layoutIdx := lIdx })
    (hread :
      evalPlaceRead locals ⟨sIdx, []⟩ mem.borrows mem.globals layouts
        mem.callerLocals localDecls mem.callStack =
        .ok (.aggregate 0 [.ptr p 8, .scalar lenSc]) locals')
    (hborrow : lookupBorrow mem.borrows p.tag = some entry)
    (hperm : entry.perm ≠ .disabled)
    (hslot :
      activeFrameSlot? locals' mem.callStack entry.targetFrameDepth entry.targetLocal =
        some (.init rootVal))
    (hbacking :
      readSliceBackingAggregate? locals' rootVal entry.targetProjection lenSc.bits
        (tyByteSize localDecls layouts { kind := elemKind, layoutIdx := unresolvedLayoutIdx layouts }) =
        some (containerProj, baseIdx, elems))
    (hoff :
      byteOffsetToElemIdx? p.offsetBytes (inferElemListByteStride elems) =
        some rawElemOffset)
    (hptr : PtrRel allocMap p mptr)
    (hlen : ScalarRel lenSc mlen)
    (hlen_sz : lenSc.sizeBytes = 8)
    (hunsized : sliceLay.layout.isSized = false)
    (hsliceOrStr : sliceLay.ty == strPointeeTyId || (2100 ≤ sliceLay.ty && sliceLay.ty < 2200))
    (st : AnnealStepState) :
    let mptrOpt : Miri.Memory.Pointer (Option AnnealProv) := ⟨mptr.offset, some mptr.provenance⟩
    let metaImm : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair
        (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)
        (.fromScalarInt mlen)
    Miri.Interpreter.PlaceDynamic.length
      (annealPlaceProjectionHooksWideSlice localDecls layouts) ()
      ⟨.memory ⟨mptrOpt, .metadata (.fromScalarInt mlen), none⟩, sliceLay⟩ st =
      .ok (UInt64.ofNat lenSc.bits) st ∧
    Miri.Interpreter.ScalarOps.unary
      (annealScalarOpsHooksWideSlice localDecls layouts) ()
      .PtrMetadata ⟨metaImm, ⟨arraySliceMetaTyId, widePointerLayoutData false⟩⟩ st =
      .ok ⟨.scalar (.fromScalarInt mlen),
           translateTy { kind := .uint .usize, layoutIdx := 0 }⟩ st ∧
    WideSliceImmediateRel allocMap (.aggregate 0 [.ptr p 8, .scalar lenSc]) metaImm ∧
    ScalarRel lenSc mlen ∧
    (rawElemOffset + baseIdx + lenSc.bits ≤ elems.length →
      evalRvalue locals (.len ⟨sIdx, [.deref]⟩) mem localDecls layouts =
        .ok (.scalar lenSc) locals' mem) ∧
    (elems.length < rawElemOffset + baseIdx + lenSc.bits →
      evalRvalue locals (.len ⟨sIdx, [.deref]⟩) mem localDecls layouts = .ub) := by
  have hlen_m :=
    placeDynamic_length_wideSlice_simulation
      (localDecls := localDecls) (layouts := layouts) (ptr := ⟨mptr.offset, some mptr.provenance⟩)
      (sliceLay := sliceLay) hlen hlen_sz hunsized hsliceOrStr st
  refine ⟨hlen_m, rfl, .provenance hptr hlen hlen_sz, hlen, ?_, ?_⟩
  · intro hin
    have hble : Nat.ble (Nat.add (Nat.add rawElemOffset baseIdx) lenSc.bits) (length elems) = true := by
      change Nat.ble (rawElemOffset + baseIdx + lenSc.bits) elems.length = true
      rw [Nat.ble_eq]
      exact hin
    rcases lenSc with ⟨lbits, lsz⟩
    cases hlen_sz
    cases hp : entry.perm <;>
      try exact False.elim (hperm hp)
    all_goals
      simp only [evalRvalue, evalPlaceLen, hptrBytes, hplaceTy, hread,
        hborrow, hp, hslot, hbacking, hoff, hble, Nat.beq_refl, Bool.and_self]
  · intro hoob
    have hble : Nat.ble (Nat.add (Nat.add rawElemOffset baseIdx) lenSc.bits) (length elems) = false := by
      change Nat.ble (rawElemOffset + baseIdx + lenSc.bits) elems.length = false
      rw [Bool.eq_false_iff, Ne, Nat.ble_eq]
      omega
    rcases lenSc with ⟨lbits, lsz⟩
    cases hlen_sz
    cases hp : entry.perm <;>
      try exact False.elim (hperm hp)
    all_goals
      simp only [evalRvalue, evalPlaceLen, hptrBytes, hplaceTy, hread,
        hborrow, hp, hslot, hbacking, hoff, hble, Nat.beq_refl, Bool.and_self, Bool.false_and,
        Bool.and_false]

/-- **Full two-sided borrow-backed wide-slice `(*s)[idx]` simulation
(`evalPlaceRead_index_wideSlice_borrowBacked_two_sided_simulation`)**:
Runs the **real** Anneal `evalPlaceRead locals ⟨sIdx, [.deref, .index idxLocal]⟩`
(`evalSliceFatPtrDerefRead` → `takeValues lenSc.bits (dropValues (rawElemOffset + baseIdx) elems)`
→ `readProjectedValue`) in lockstep with vendored `Miri.Interpreter.PlaceDynamic.index`:
1. **Slice-length OOB (`lenSc.bits ≤ idxSc.bits`)**:
   Anneal's `evalPlaceRead locals ⟨sIdx, [.deref, .index idxLocal]⟩` faults with `.ub`
   (with NO unlinked `hget_none` hypothesis — proved even when
   `rawElemOffset + baseIdx + idxSc.bits < elems.length` on a subslice of a larger array!),
   AND vendored `Miri.Interpreter.PlaceDynamic.index` raises
   `.error (.undefinedBehavior msg) st`.
2. **In-bounds (`idxSc.bits < lenSc.bits`)**:
   When `get? elems (rawElemOffset + baseIdx + idxSc.bits) = some elemVal` and
   `validateValueForTy?` holds, Anneal's `evalPlaceRead` returns `.ok elemVal locals`,
   AND (given non-overflowing byte offset `elemLay.size.bytes.toNat * idxSc.bits < 2^63`
   and in-bounds `projectionMemoryOffset`) vendored `Miri.Interpreter.PlaceDynamic.index`
   returns `.ok ⟨.memory elemMp, layoutOfEncodedTyId elemId layouts⟩ st`. -/
theorem evalPlaceRead_index_wideSlice_borrowBacked_two_sided_simulation
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {locals : List LocalSlot} {mem : Memory}
    {sIdx idxLocal : Local} {elemKind : RigidTy} {lIdx : LayoutIdx}
    {p : ProvenancePtr} {lenSc idxSc : MirAst.ScalarInt}
    {entry : BorrowEntry} {rootVal : Value}
    {containerProj : List ProjectionElem} {baseIdx rawElemOffset : Nat}
    {elems : List Value}
    {ptr : Miri.Memory.Pointer (Option AnnealProv)}
    {mlen : Miri.Memory.ScalarInt}
    {elemLay : Miri.ABI.LayoutData} {elemId : Miri.MIR.TyId}
    (hptrBytes : layoutPointerBytes layouts = 8)
    (hpointeeTy :
      placeTyResolved localDecls layouts ⟨sIdx, [.deref]⟩ =
        some { kind := .slice elemKind, layoutIdx := lIdx })
    (hsl_slot : get? locals sIdx = some (.init (.aggregate 0 [.ptr p 8, .scalar lenSc])))
    (halign_deref :
      checkDerefAlign localDecls layouts (some { kind := .slice elemKind, layoutIdx := lIdx })
        p.offsetBytes = true)
    (hborrow : lookupBorrow mem.borrows p.tag = some entry)
    (hperm : entry.perm ≠ .disabled)
    (hslot :
      activeFrameSlot? locals mem.callStack entry.targetFrameDepth entry.targetLocal =
        some (.init rootVal))
    (halign_target :
      checkTargetPlaceAlign localDecls layouts
        (some { kind := .slice elemKind, layoutIdx := lIdx })
        entry p (some rootVal) layouts localDecls = true)
    (hbacking :
      readSliceBackingAggregate? locals rootVal entry.targetProjection lenSc.bits
        (rigidTyKindByteSize elemKind) =
        some (containerProj, baseIdx, elems))
    (hoff :
      byteOffsetToElemIdx? p.offsetBytes
        ((rigidTyKindByteSize elemKind).getD (inferElemListByteStride elems)) =
        some rawElemOffset)
    (hin_backing : rawElemOffset + baseIdx + lenSc.bits ≤ elems.length)
    (hidx_slot : get? locals idxLocal = some (.init (.scalar idxSc)))
    (hidx_u64 : idxSc.bits < 2 ^ 64)
    (hlen : ScalarRel lenSc mlen)
    (hlen_sz : lenSc.sizeBytes = 8)
    (helemId : elemId < 100)
    (st : AnnealStepState) :
    let slicePlace : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.memory ⟨ptr, .metadata (.fromScalarInt mlen), none⟩,
       ⟨slicePointeeTyId elemId, unsizedSliceLayoutData elemLay⟩⟩
    -- (1) Out-of-bounds (`lenSc.bits ≤ idxSc.bits`): BOTH fault `.ub`
    (lenSc.bits ≤ idxSc.bits →
      evalPlaceRead locals ⟨sIdx, [.deref, .index idxLocal]⟩ mem.borrows mem.globals
        layouts mem.callerLocals localDecls mem.callStack = .ub ∧
      ∃ msg,
        Miri.Interpreter.PlaceDynamic.index
          (annealPlaceProjectionHooksWideSlice localDecls layouts) ()
          slicePlace (UInt64.ofNat idxSc.bits) st =
          .error (.undefinedBehavior msg) st) ∧
    -- (2) In-bounds (`idxSc.bits < lenSc.bits`): BOTH succeed in lockstep
    (∀ elemVal elemMp,
      idxSc.bits < lenSc.bits →
      get? elems (rawElemOffset + baseIdx + idxSc.bits) = some elemVal →
      validateValueForTy? layouts
        (placeTyResolved localDecls layouts ⟨sIdx, [.deref, .index idxLocal]⟩) elemVal = true →
      elemLay.size.bytes.toNat * idxSc.bits < 2 ^ 63 →
      (layoutOfEncodedTyId elemId layouts).layout.isSized = true →
      Miri.Interpreter.projectionMemoryOffset
        annealPointerArithmetic
        (annealPointerResolver st.machine)
        (annealLiveAllocationLookup st.machine)
        ⟨ptr, .metadata (.fromScalarInt mlen), none⟩
        (Miri.ABI.Size.ofBytes (UInt64.ofNat (elemLay.size.bytes.toNat * idxSc.bits)))
        .inbounds .none = .ok elemMp →
      evalPlaceRead locals ⟨sIdx, [.deref, .index idxLocal]⟩ mem.borrows mem.globals
        layouts mem.callerLocals localDecls mem.callStack = .ok elemVal locals ∧
      Miri.Interpreter.PlaceDynamic.index
        (annealPlaceProjectionHooksWideSlice localDecls layouts) ()
        slicePlace (UInt64.ofNat idxSc.bits) st =
        .ok ⟨.memory elemMp, layoutOfEncodedTyId elemId layouts⟩ st) := by
  intro slicePlace
  have hlen_lt : lenSc.bits < 2 ^ 64 := by
    have hlt := hlen.canonical
    rw [hlen_sz] at hlt
    exact hlt
  have hrem_ble :
      Nat.ble lenSc.bits (length (dropValues (Nat.add rawElemOffset baseIdx) elems)) = true := by
    change Nat.ble lenSc.bits (dropValues (rawElemOffset + baseIdx) elems).length = true
    rw [wideSlice_dropValues_eq_drop, List.length_drop, Nat.ble_eq]
    omega
  have hu64_len : (UInt64.ofNat lenSc.bits).toNat = lenSc.bits :=
    Nat.mod_eq_of_lt hlen_lt
  have hu64_idx : (UInt64.ofNat idxSc.bits).toNat = idxSc.bits :=
    Nat.mod_eq_of_lt hidx_u64
  constructor
  · intro hoob_nat
    have hoob_u64 : UInt64.ofNat lenSc.bits ≤ UInt64.ofNat idxSc.bits := by
      rw [UInt64.le_iff_toNat_le, hu64_len, hu64_idx]
      exact hoob_nat
    have hget_none :
        get? (takeValues lenSc.bits (dropValues (Nat.add rawElemOffset baseIdx) elems))
          idxSc.bits = none := by
      change (takeValues lenSc.bits (dropValues (rawElemOffset + baseIdx) elems))[idxSc.bits]? = none
      rw [wideSlice_takeValues_eq_take, wideSlice_dropValues_eq_drop, List.getElem?_eq_none]
      rw [List.length_take, List.length_drop]
      omega
    refine ⟨?_, placeDynamic_index_wideSlice_oob_ub_simulation hlen hlen_sz helemId hoob_u64 st⟩
    cases hsz_opt : rigidTyKindByteSize elemKind <;>
      simp only [hsz_opt, Option.getD] at hoff hbacking
    all_goals
      cases hp : entry.perm <;>
        try exact False.elim (hperm hp)
      all_goals
        simp only [evalPlaceRead, evalSliceFatPtrDerefRead, hsl_slot, hpointeeTy, hptrBytes,
          hlen_sz, halign_deref, hborrow, hp, hslot, halign_target, hbacking, hsz_opt, hoff,
          hrem_ble, readProjectedValue, hidx_slot, hget_none, Nat.beq_refl, Bool.and_self]
  · intro elemVal elemMp hlt_idx hget_elem hvalid hmul_lt hsized hproj_off
    have hget_some :
        get? (takeValues lenSc.bits (dropValues (Nat.add rawElemOffset baseIdx) elems))
          idxSc.bits = some elemVal := by
      change (takeValues lenSc.bits (dropValues (rawElemOffset + baseIdx) elems))[idxSc.bits]? =
        some elemVal
      rw [wideSlice_takeValues_eq_take, wideSlice_dropValues_eq_drop, List.getElem?_take_of_lt hlt_idx,
        List.getElem?_drop]
      exact hget_elem
    refine ⟨?_, ?_⟩
    · cases hsz_opt : rigidTyKindByteSize elemKind <;>
        simp only [hsz_opt, Option.getD] at hoff hbacking
      all_goals
        cases hp : entry.perm <;>
          try exact False.elim (hperm hp)
        all_goals
          simp only [evalPlaceRead, evalSliceFatPtrDerefRead, hsl_slot, hpointeeTy, hptrBytes,
            hlen_sz, halign_deref, hborrow, hp, hslot, halign_target, hbacking, hsz_opt, hoff,
            hrem_ble, readProjectedValue, hidx_slot, hget_some, hvalid, Nat.beq_refl, Bool.and_self]
    · have hsliceOrStr :
          (slicePointeeTyId elemId == strPointeeTyId ||
            (2100 ≤ slicePointeeTyId elemId && slicePointeeTyId elemId < 2200)) = true := by
        unfold slicePointeeTyId strPointeeTyId
        rw [Bool.or_eq_true]
        right
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨Nat.le_add_right 2100 elemId, Nat.add_lt_add_left helemId 2100⟩
      have hlen_eval :=
        placeDynamic_length_wideSlice_simulation
          (localDecls := localDecls) (layouts := layouts) (ptr := ptr)
          (sliceLay := ⟨slicePointeeTyId elemId, unsizedSliceLayoutData elemLay⟩)
          hlen hlen_sz rfl hsliceOrStr st
      have hnot_ge : ¬ (UInt64.ofNat idxSc.bits ≥ UInt64.ofNat lenSc.bits) := by
        intro hge
        rw [GE.ge, UInt64.le_iff_toNat_le, hu64_len, hu64_idx] at hge
        omega
      have hcomp_sz :
          Miri.Interpreter.IntegerOps.computeSizeInBytes
            elemLay.size (UInt64.ofNat idxSc.bits)
            (Miri.ABI.Size.ofBytes 0x7fff_ffff_ffff_ffff) =
          some (Miri.ABI.Size.ofBytes
            (UInt64.ofNat (elemLay.size.bytes.toNat * idxSc.bits))) := by
        unfold Miri.Interpreter.IntegerOps.computeSizeInBytes
        rw [hu64_idx]
        have hmax : (Miri.ABI.Size.ofBytes 0x7fff_ffff_ffff_ffff).bytes.toNat = 2 ^ 63 - 1 := by
          decide
        have hcond :
            (decide (elemLay.size.bytes.toNat * idxSc.bits < 2 ^ 64) &&
              decide (elemLay.size.bytes.toNat * idxSc.bits ≤
                (Miri.ABI.Size.ofBytes 0x7fff_ffff_ffff_ffff).bytes.toNat)) = true := by
          rw [hmax, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
          omega
        dsimp only []
        rw [hcond]
        rfl
      have hfield_eq :
          (annealPlaceProjectionHooksWideSlice localDecls layouts).field ()
            ⟨slicePointeeTyId elemId, unsizedSliceLayoutData elemLay⟩ 0 st =
          .ok (layoutOfEncodedTyId elemId layouts) st := by
        have hne_str : (slicePointeeTyId elemId == strPointeeTyId) = false := by
          unfold slicePointeeTyId strPointeeTyId
          exact beq_false_of_ne
            (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 2000 < 2100) (Nat.le_add_right 2100 elemId)))
        have hrange : (2100 ≤ slicePointeeTyId elemId && slicePointeeTyId elemId < 2200) = true := by
          unfold slicePointeeTyId
          rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
          exact ⟨Nat.le_add_right 2100 elemId, Nat.add_lt_add_left helemId 2100⟩
        have hsub : slicePointeeTyId elemId - 2100 = elemId :=
          Nat.add_sub_cancel_left 2100 elemId
        unfold annealPlaceProjectionHooksWideSlice
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hne_str, hrange, hsub,
          Pure.pure, EStateM.pure]
      have hmax_eq :
          (annealPlaceProjectionHooksWideSlice localDecls layouts).maxSizeOfVal =
            Miri.ABI.Size.ofBytes 0x7fff_ffff_ffff_ffff := rfl
      have hfields_eq : (unsizedSliceLayoutData elemLay).fields = .Array elemLay.size 0 := rfl
      unfold Miri.Interpreter.PlaceDynamic.index
      dsimp only [slicePlace]
      rw [hfields_eq]
      dsimp only []
      rw [EStateM.bind_eq_ok hlen_eval]
      simp only [hnot_ge, ↓reduceIte]
      rw [hmax_eq, hcomp_sz]
      dsimp only []
      rw [EStateM.bind_eq_ok hfield_eq]
      change ((do
        if !(layoutOfEncodedTyId elemId layouts).layout.isSized then
          throw (Miri.Interpreter.StepError.invalidProgram "sized offset requires sized output")
        Miri.Interpreter.PlaceDynamic.offsetWithMeta
          (annealPlaceProjectionHooksWideSlice localDecls layouts) () slicePlace
          (Miri.ABI.Size.ofBytes (UInt64.ofNat (elemLay.size.bytes.toNat * idxSc.bits)))
          .inbounds .none (layoutOfEncodedTyId elemId layouts) :
        Miri.Interpreter.PlaceM AnnealStepState (Miri.Interpreter.RuntimePlace AnnealProv))) st = _
      unfold Miri.Interpreter.PlaceDynamic.offsetWithMeta
      simp only [slicePlace, hsized, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bind.bind,
        EStateM.bind, Pure.pure, EStateM.pure, annealPlaceProjectionHooksWideSlice, get, getThe,
        MonadStateOf.get, EStateM.get, hproj_off]

private theorem wideSlice_u64_sub_eq {a b : Nat} (ha : a < 2 ^ 64) (hb : b ≤ a) :
    UInt64.ofNat a - UInt64.ofNat b = UInt64.ofNat (a - b) := by
  have hb64 : b < 2 ^ 64 := Nat.lt_of_le_of_lt hb ha
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  simp [UInt64.toBitVec_sub, BitVec.toNat_sub,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb64,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le a b) ha)]
  omega

/-- **Two-sided symbolic `ConstantIndex` simulation on dereferenced wide slices**:
Relates Anneal's `readProjectedValue` over the `lenSc.bits`-element wide-slice window
`takeValues lenSc.bits (dropValues (rawElemOffset + baseIdx) elems)` to vendored
`Miri.Interpreter.PlaceDynamic.constantIndex` (`PlaceDynamic.lean:105-115`):
1. **`min_length` failure (`lenSc.bits < minLen`)**: BOTH fault with UB
   (`.ub` in Anneal and `.error (.undefinedBehavior "constant index minimum length") st`
   in `PlaceDynamic.constantIndex`).
2. **Well-formed MIR slice-pattern `ConstantIndex` (`minLen ≤ lenSc.bits` and
   `(fromEnd = false ∧ offset < minLen) ∨ (fromEnd = true ∧ 1 ≤ offset ∧ offset ≤ minLen)`)**:
   BOTH resolve the exact same element index `idx = if fromEnd then lenSc.bits - offset else offset`
   (`idx < lenSc.bits`): Anneal reads `elems[rawElemOffset + baseIdx + idx]?`, and vendored
   `Miri.Interpreter.PlaceDynamic.constantIndex` delegates directly to
   `PlaceDynamic.index ... (UInt64.ofNat idx) st`. -/
theorem placeDynamic_constantIndex_wideSlice_two_sided_simulation
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {locals : List LocalSlot}
    {lenSc : MirAst.ScalarInt} {mlen : Miri.Memory.ScalarInt}
    {offset minLen baseIdx rawElemOffset : Nat} {fromEnd : Bool}
    {elems : List Value}
    {ptr : Miri.Memory.Pointer (Option AnnealProv)}
    {elemLay : Miri.ABI.LayoutData} {elemId : Miri.MIR.TyId}
    (hin_backing : rawElemOffset + baseIdx + lenSc.bits ≤ elems.length)
    (hlen : ScalarRel lenSc mlen)
    (hlen_sz : lenSc.sizeBytes = 8)
    (helemId : elemId < 100)
    (hoff_u64 : offset < 2 ^ 64)
    (hmin_u64 : minLen < 2 ^ 64)
    (st : AnnealStepState) :
    let window := takeValues lenSc.bits (dropValues (Nat.add rawElemOffset baseIdx) elems)
    let slicePlace : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.memory ⟨ptr, .metadata (.fromScalarInt mlen), none⟩,
       ⟨slicePointeeTyId elemId, unsizedSliceLayoutData elemLay⟩⟩
    let idx := if fromEnd then lenSc.bits - offset else offset
    -- (1) `min_length` failure (`lenSc.bits < minLen`): `.ub` in both
    (lenSc.bits < minLen →
      readProjectedValue locals (.aggregate 0 window) [.constantIndex offset minLen fromEnd] = .ub ∧
      Miri.Interpreter.PlaceDynamic.constantIndex
        (annealPlaceProjectionHooksWideSlice localDecls layouts) ()
        slicePlace (UInt64.ofNat offset) (UInt64.ofNat minLen) fromEnd st =
        .error (.undefinedBehavior "constant index minimum length") st) ∧
    -- (2) Well-formed MIR `ConstantIndex`: both resolve to `idx`
    (∀ elemVal,
      minLen ≤ lenSc.bits →
      ((fromEnd = false ∧ offset < minLen) ∨ (fromEnd = true ∧ 1 ≤ offset ∧ offset ≤ minLen)) →
      get? elems (rawElemOffset + baseIdx + idx) = some elemVal →
      readProjectedValue locals (.aggregate 0 window) [.constantIndex offset minLen fromEnd] =
        .ok elemVal ∧
      Miri.Interpreter.PlaceDynamic.constantIndex
        (annealPlaceProjectionHooksWideSlice localDecls layouts) ()
        slicePlace (UInt64.ofNat offset) (UInt64.ofNat minLen) fromEnd st =
        Miri.Interpreter.PlaceDynamic.index
          (annealPlaceProjectionHooksWideSlice localDecls layouts) ()
          slicePlace (UInt64.ofNat idx) st) := by
  intro window slicePlace idx
  have hlen_lt : lenSc.bits < 2 ^ 64 := by
    have hlt := hlen.canonical
    rw [hlen_sz] at hlt
    exact hlt
  have hu_len : (UInt64.ofNat lenSc.bits).toNat = lenSc.bits := Nat.mod_eq_of_lt hlen_lt
  have hu_off : (UInt64.ofNat offset).toNat = offset := Nat.mod_eq_of_lt hoff_u64
  have hu_min : (UInt64.ofNat minLen).toNat = minLen := Nat.mod_eq_of_lt hmin_u64
  have hsliceOrStr :
      (slicePointeeTyId elemId == strPointeeTyId ||
        (2100 ≤ slicePointeeTyId elemId && slicePointeeTyId elemId < 2200)) = true := by
    unfold slicePointeeTyId strPointeeTyId
    rw [Bool.or_eq_true]
    right
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨Nat.le_add_right 2100 elemId, Nat.add_lt_add_left helemId 2100⟩
  have hlen_eval :=
    placeDynamic_length_wideSlice_simulation
      (localDecls := localDecls) (layouts := layouts) (ptr := ptr)
      (sliceLay := ⟨slicePointeeTyId elemId, unsizedSliceLayoutData elemLay⟩)
      hlen hlen_sz rfl hsliceOrStr st
  have hWinLen : length window = lenSc.bits := by
    change (takeValues lenSc.bits (dropValues (rawElemOffset + baseIdx) elems)).length = lenSc.bits
    rw [wideSlice_takeValues_eq_take, wideSlice_dropValues_eq_drop, List.length_take, List.length_drop]
    omega
  have hRpv : ∀ (fs : List Value) (o m : Nat) (fe : Bool),
      readProjectedValue locals (.aggregate 0 fs) [.constantIndex o m fe] =
        match Nat.ble m (length fs) with
        | true =>
          match get? fs (if fe then Nat.sub (length fs) o else o) with
          | some elemVal => .ok elemVal
          | none => .ub
        | false => .ub := by
    intro fs o m fe
    cases fe <;> rfl
  constructor
  · intro hLtMin
    have hBleF : Nat.ble minLen (length window) = false := by
      rw [hWinLen, Bool.eq_false_iff, Ne, Nat.ble_eq]
      omega
    have hU64Lt : UInt64.ofNat lenSc.bits < UInt64.ofNat minLen := by
      rw [UInt64.lt_iff_toNat_lt, hu_len, hu_min]
      exact hLtMin
    refine ⟨?_, ?_⟩
    · rw [hRpv, hBleF]
    · unfold Miri.Interpreter.PlaceDynamic.constantIndex
      rw [EStateM.bind_eq_ok hlen_eval]
      simp only [hU64Lt, ↓reduceIte]
      rfl
  · intro elemVal hMinLe hWf hGetElem
    have hBleT : Nat.ble minLen (length window) = true := by
      rw [hWinLen, Nat.ble_eq]
      exact hMinLe
    have hIdxLt : idx < lenSc.bits := by
      rcases hWf with ⟨hfe, hoff⟩ | ⟨hfe, h1, hoff⟩ <;>
        simp only [idx, hfe, ↓reduceIte, Bool.false_eq_true] <;> omega
    have hWinGet : get? window idx = some elemVal := by
      change (takeValues lenSc.bits (dropValues (rawElemOffset + baseIdx) elems))[idx]? =
        some elemVal
      rw [wideSlice_takeValues_eq_take, wideSlice_dropValues_eq_drop,
        List.getElem?_take_of_lt hIdxLt, List.getElem?_drop]
      exact hGetElem
    have hNotLtMin : ¬ (UInt64.ofNat lenSc.bits < UInt64.ofNat minLen) := by
      rw [UInt64.lt_iff_toNat_lt, hu_len, hu_min]
      omega
    refine ⟨?_, ?_⟩
    · rcases hWf with ⟨rfl, _⟩ | ⟨rfl, _, _⟩
      · simp only [idx, Bool.false_eq_true, ↓reduceIte] at hWinGet
        rw [hRpv, hBleT]
        simp only [Bool.false_eq_true, ↓reduceIte, hWinGet]
      · simp only [idx, ↓reduceIte] at hWinGet
        have hSubEq : Nat.sub (length window) offset = lenSc.bits - offset := by
          rw [hWinLen]; rfl
        rw [hRpv, hBleT]
        simp only [↓reduceIte, hSubEq, hWinGet]
    · unfold Miri.Interpreter.PlaceDynamic.constantIndex
      rw [EStateM.bind_eq_ok hlen_eval]
      simp only [hNotLtMin, ↓reduceIte]
      rcases hWf with ⟨rfl, hoff_lt⟩ | ⟨rfl, h1, hoff_le⟩
      · have hNotGe : ¬ (UInt64.ofNat offset ≥ UInt64.ofNat minLen) := by
          rw [GE.ge, UInt64.le_iff_toNat_le, hu_min, hu_off]
          omega
        simp only [Bool.false_eq_true, ↓reduceIte, hNotGe, idx, Bind.bind, EStateM.bind,
          Pure.pure, EStateM.pure]
      · have hNe0 : (UInt64.ofNat offset == 0) = false := by
          rw [beq_eq_false_iff_ne]
          intro heq
          have h0 : (UInt64.ofNat offset).toNat = (0 : UInt64).toNat := congrArg UInt64.toNat heq
          rw [hu_off] at h0
          change offset = 0 at h0
          omega
        have hNotGt : ¬ (UInt64.ofNat offset > UInt64.ofNat minLen) := by
          change ¬ (UInt64.ofNat minLen < UInt64.ofNat offset)
          rw [UInt64.lt_iff_toNat_lt, hu_min, hu_off]
          omega
        have hSubU64 :
            UInt64.ofNat lenSc.bits - UInt64.ofNat offset = UInt64.ofNat (lenSc.bits - offset) :=
          wideSlice_u64_sub_eq hlen_lt (Nat.le_trans hoff_le hMinLe)
        simp only [↓reduceIte, hNe0, decide_eq_false hNotGt, Bool.or_self, Bool.false_eq_true,
          idx, hSubU64, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

/-! ### 2.5 `size_of_val` & `align_of_val` vs. `DynamicLayout.sizeAndAlignFromMeta` & `Intrinsics.eval` -/

/-- Exact symbolic equivalence between Anneal's `evalSliceSizeOfVal` and vendored
`Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta` for `[T]` and `str` across
all element sizes `elemSz` and 64-bit lengths `lenSc`:
1. **In-bounds (`elemSz * lenSc.bits < 2^63`, i.e., `≤ isize::MAX = 2^63 - 1`)**:
   * `evalSliceSizeOfVal elemSz lenSc = some ⟨elemSz * lenSc.bits, 8⟩`, AND
   * `Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta (annealDynamicLayoutHooksWideSlice layouts) () (fuel + 1) (.metadata (.fromScalarInt mlen)) sliceLay st = .ok (some (Miri.ABI.Size.ofBytes (UInt64.ofNat (elemSz * lenSc.bits)), elemAlign)) st`.
2. **Overflow (`2^63 ≤ elemSz * lenSc.bits`, i.e., `> isize::MAX`)**:
   * `evalSliceSizeOfVal elemSz lenSc = none` (causing BOTH `size_of_val` and
     `align_of_val` in `evalNonSelectIntrinsicCall` to fault with `MirStepNode.fail .ub`), AND
   * `Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta (annealDynamicLayoutHooksWideSlice layouts) () (fuel + 1) (.metadata (.fromScalarInt mlen)) sliceLay st = .error (.undefinedBehavior "InvalidMeta(SliceTooBig)") st`. -/
theorem evalSliceSizeOfVal_iff_dynamicLayout_sizeAndAlignFromMeta
    {layouts : LayoutTable} {fuel : Nat}
    {lenSc : MirAst.ScalarInt} {mlen : Miri.Memory.ScalarInt}
    {sliceLay elemLay : Miri.Interpreter.LocalLayout}
    (hlen : ScalarRel lenSc mlen)
    (hlen_sz : lenSc.sizeBytes = 8)
    (hunsized : sliceLay.layout.isSized = false)
    (hkind :
      (sliceLay.ty == strPointeeTyId ∧
        elemLay = translateTy { kind := .uint .u8, layoutIdx := 0 } layouts) ∨
      (sliceLay.ty ≠ strPointeeTyId ∧
        2100 ≤ sliceLay.ty ∧ sliceLay.ty < 2200 ∧
        elemLay = layoutOfEncodedTyId (sliceLay.ty - 2100) layouts))
    (st : AnnealStepState) :
    let elemSz := elemLay.layout.size.bytes.toNat
    let elemAlign := elemLay.layout.align.abi
    let miriRes :=
      Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta
        (annealDynamicLayoutHooksWideSlice layouts) () (fuel + 1)
        (.metadata (.fromScalarInt mlen)) sliceLay st
    (elemSz * lenSc.bits < 2 ^ 63 →
      evalSliceSizeOfVal elemSz lenSc = some ⟨elemSz * lenSc.bits, 8⟩ ∧
      miriRes =
        .ok (some (Miri.ABI.Size.ofBytes (UInt64.ofNat (elemSz * lenSc.bits)), elemAlign)) st) ∧
    (2 ^ 63 ≤ elemSz * lenSc.bits →
      evalSliceSizeOfVal elemSz lenSc = none ∧
      miriRes = .error (.undefinedBehavior "InvalidMeta(SliceTooBig)") st) := by
  intro elemSz elemAlign miriRes
  have hlen_lt : lenSc.bits < 2 ^ 64 := by
    have hlt := hlen.canonical
    rw [hlen_sz] at hlt
    exact hlt
  have hwrap_len : wrapScalarBits lenSc.bits (scalarModulus 8) = lenSc.bits := by
    have hw := hlen.wrapScalarBits_self
    rw [hlen_sz] at hw
    exact hw
  have htarget := fromScalarInt_toTargetUsize_u64 hlen hlen_sz
  have hu64_len : (UInt64.ofNat lenSc.bits).toNat = lenSc.bits :=
    Nat.mod_eq_of_lt hlen_lt
  have hcls_and_field :
      ∃ kind,
        (kind = Miri.Interpreter.DynamicTypeKind.str ∨
          kind = Miri.Interpreter.DynamicTypeKind.slice) ∧
        (annealDynamicLayoutHooksWideSlice layouts).classify () sliceLay.ty st = .ok kind st ∧
        (annealDynamicLayoutHooksWideSlice layouts).field () sliceLay 0 st = .ok elemLay st := by
    rcases hkind with ⟨hstr, helem⟩ | ⟨hne, hlo, hhi, helem⟩
    · refine ⟨.str, Or.inl rfl, ?_, ?_⟩
      · unfold annealDynamicLayoutHooksWideSlice
        simp [hstr, Pure.pure, EStateM.pure]
      · unfold annealDynamicLayoutHooksWideSlice
        simp [hstr, helem, Pure.pure, EStateM.pure]
    · have hstr_f : (sliceLay.ty == strPointeeTyId) = false := beq_false_of_ne hne
      have hrange : (2100 ≤ sliceLay.ty && sliceLay.ty < 2200) = true := by
        simp [hlo, hhi]
      refine ⟨.slice, Or.inr rfl, ?_, ?_⟩
      · unfold annealDynamicLayoutHooksWideSlice
        simp [hstr_f, hrange, Pure.pure, EStateM.pure]
      · unfold annealDynamicLayoutHooksWideSlice
        simp [hstr_f, hrange, helem, Pure.pure, EStateM.pure]
  obtain ⟨kind, hkind_or, hcls_eq, hfield_eq⟩ := hcls_and_field
  have htarget_lay : (annealDynamicLayoutHooksWideSlice layouts).target = annealTargetDataLayout := rfl
  have hmax_lay : (annealDynamicLayoutHooksWideSlice layouts).maxSizeOfVal =
      Miri.ABI.Size.ofBytes 0x7fff_ffff_ffff_ffff := rfl
  have hsz8 : Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits =
      Miri.ABI.Size.ofBytes 8 := rfl
  have hmiri_reduce :
      miriRes =
        let product := elemSz * lenSc.bits
        let size := Miri.ABI.Size.ofBytes (UInt64.ofNat (min product (2 ^ 64 - 1)))
        if size.bytes > (Miri.ABI.Size.ofBytes 0x7fff_ffff_ffff_ffff).bytes then
          .error (.undefinedBehavior "InvalidMeta(SliceTooBig)") st
        else
          .ok (some (size, elemAlign)) st := by
    change Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta
        (annealDynamicLayoutHooksWideSlice layouts) () (fuel + 1)
        (.metadata (.fromScalarInt mlen)) sliceLay st = _
    unfold Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta
    simp only [hunsized, Bool.false_eq_true, ↓reduceIte, htarget_lay, hmax_lay, hsz8, Except.mapError]
    rw [EStateM.bind_eq_ok hcls_eq]
    rcases hkind_or with rfl | rfl <;>
    · dsimp only
      rw [EStateM.bind_eq_ok (a := Miri.Memory.Scalar.fromScalarInt mlen) (s' := st)
        (by with_unfolding_all rfl)]
      rw [htarget]
      rw [EStateM.bind_eq_ok (a := UInt64.ofNat lenSc.bits) (s' := st)
        (by with_unfolding_all rfl)]
      rw [EStateM.bind_eq_ok hfield_eq, hu64_len]
      split <;> rfl
  constructor
  · intro hlt
    have hble_f : Nat.ble (signedHalfModulus 8) (Nat.mul elemSz lenSc.bits) = false := by
      change Nat.ble (2 ^ 63) (elemSz * lenSc.bits) = false
      rw [Bool.eq_false_iff, Ne, Nat.ble_eq]
      omega
    have hmin : min (elemSz * lenSc.bits) (2 ^ 64 - 1) = elemSz * lenSc.bits := by
      omega
    have hgt_f :
        ¬ ((Miri.ABI.Size.ofBytes (UInt64.ofNat (elemSz * lenSc.bits))).bytes >
          (Miri.ABI.Size.ofBytes 0x7fff_ffff_ffff_ffff).bytes) := by
      intro hcontra
      have h1 : (UInt64.ofNat 0x7fff_ffff_ffff_ffff).toNat <
          (UInt64.ofNat (elemSz * lenSc.bits)).toNat := hcontra
      have h2 : (UInt64.ofNat (elemSz * lenSc.bits)).toNat = elemSz * lenSc.bits :=
        Nat.mod_eq_of_lt (by omega)
      have h3 : (UInt64.ofNat 0x7fff_ffff_ffff_ffff).toNat = 2 ^ 63 - 1 := by decide
      omega
    constructor
    · unfold evalSliceSizeOfVal
      rw [hlen_sz]
      dsimp only
      rw [hwrap_len, hble_f]
      rfl
    · rw [hmiri_reduce]
      dsimp only
      rw [hmin]
      simp only [hgt_f, ↓reduceIte]
  · intro hge
    have hble_t : Nat.ble (signedHalfModulus 8) (Nat.mul elemSz lenSc.bits) = true := by
      change Nat.ble (2 ^ 63) (elemSz * lenSc.bits) = true
      rw [Nat.ble_eq]
      exact hge
    have hgt_t :
        (Miri.ABI.Size.ofBytes (UInt64.ofNat (min (elemSz * lenSc.bits) (2 ^ 64 - 1)))).bytes >
          (Miri.ABI.Size.ofBytes 0x7fff_ffff_ffff_ffff).bytes := by
      change UInt64.ofNat 0x7fff_ffff_ffff_ffff <
        UInt64.ofNat (min (elemSz * lenSc.bits) (2 ^ 64 - 1))
      rw [UInt64.lt_iff_toNat_lt]
      have hmin_lt : min (elemSz * lenSc.bits) (2 ^ 64 - 1) < 2 ^ 64 := by omega
      have h2 : (UInt64.ofNat (min (elemSz * lenSc.bits) (2 ^ 64 - 1))).toNat =
          min (elemSz * lenSc.bits) (2 ^ 64 - 1) :=
        Nat.mod_eq_of_lt hmin_lt
      have h3 : (UInt64.ofNat 0x7fff_ffff_ffff_ffff).toNat = 2 ^ 63 - 1 := by decide
      rw [h2, h3]
      omega
    constructor
    · unfold evalSliceSizeOfVal
      rw [hlen_sz]
      dsimp only
      rw [hwrap_len, hble_t]
    · rw [hmiri_reduce]
      dsimp only
      simp only [hgt_t, ↓reduceIte]

/-- Zero-sized element slice specialization (`elemSz = 0`, e.g. `[()]`) — Anneal side: for
every 64-bit length `lenSc`, `0 * lenSc.bits = 0 < 2^63`, so `evalSliceSizeOfVal 0 lenSc`
succeeds with byte size `0`. The two-sided statement (also pinning vendored
`Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta`) is `evalSliceSizeOfVal_zst_simulation`. -/
theorem evalSliceSizeOfVal_zst_always_ok
    {lenSc : MirAst.ScalarInt} (hlen_sz : lenSc.sizeBytes = 8) :
    evalSliceSizeOfVal 0 lenSc = some ⟨0, 8⟩ := by
  unfold evalSliceSizeOfVal
  rw [hlen_sz]
  change (match Nat.ble (signedHalfModulus 8) (0 * wrapScalarBits lenSc.bits (scalarModulus 8)) with
    | true => none
    | false => some (⟨0 * wrapScalarBits lenSc.bits (scalarModulus 8), 8⟩ : MirAst.ScalarInt)) =
    some ⟨0, 8⟩
  rw [Nat.zero_mul]
  rfl

/-- Two-sided zero-sized element slice lockstep (`evalSliceSizeOfVal_zst_simulation`): for every
64-bit length and every ZST element layout (`elemLay.layout.size = 0`), BOTH Anneal's
`evalSliceSizeOfVal 0 lenSc` and vendored `Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta`
succeed with byte size `0` — even for lengths `≥ 2^63`, where any non-ZST element would fault
with `InvalidMeta(SliceTooBig)`. -/
theorem evalSliceSizeOfVal_zst_simulation
    {layouts : LayoutTable} {fuel : Nat}
    {lenSc : MirAst.ScalarInt} {mlen : Miri.Memory.ScalarInt}
    {sliceLay elemLay : Miri.Interpreter.LocalLayout}
    (hlen : ScalarRel lenSc mlen)
    (hlen_sz : lenSc.sizeBytes = 8)
    (hunsized : sliceLay.layout.isSized = false)
    (hkind :
      (sliceLay.ty == strPointeeTyId ∧
        elemLay = translateTy { kind := .uint .u8, layoutIdx := 0 } layouts) ∨
      (sliceLay.ty ≠ strPointeeTyId ∧
        2100 ≤ sliceLay.ty ∧ sliceLay.ty < 2200 ∧
        elemLay = layoutOfEncodedTyId (sliceLay.ty - 2100) layouts))
    (hzst : elemLay.layout.size.bytes.toNat = 0)
    (st : AnnealStepState) :
    evalSliceSizeOfVal 0 lenSc = some ⟨0, 8⟩ ∧
    Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta
        (annealDynamicLayoutHooksWideSlice layouts) () (fuel + 1)
        (.metadata (.fromScalarInt mlen)) sliceLay st =
      .ok (some (Miri.ABI.Size.ofBytes (UInt64.ofNat 0), elemLay.layout.align.abi)) st := by
  have h := (evalSliceSizeOfVal_iff_dynamicLayout_sizeAndAlignFromMeta (fuel := fuel)
    hlen hlen_sz hunsized hkind st).1
  simp only [hzst, Nat.zero_mul] at h
  exact ⟨evalSliceSizeOfVal_zst_always_ok hlen_sz, (h (by decide)).2⟩

theorem WideSliceIntrinsic.ofDefId?_defId (wk : WideSliceIntrinsic) :
    WideSliceIntrinsic.ofDefId? wk.defId = some wk := by
  cases wk <;> rfl

private theorem layoutOfEncodedTyId_ty_ws (tyId : Miri.MIR.TyId) (layouts : LayoutTable) :
    (layoutOfEncodedTyId tyId layouts).ty = tyId := by
  unfold layoutOfEncodedTyId
  split <;> (try rfl) <;> (dsimp only; split <;> rfl)

private theorem evalFnCallArgumentAt_copy_ws
    (h : Miri.Interpreter.CallHooks AnnealProv AnnealStepState Unit Unit Unit Unit Unit Unit)
    (p : Miri.MIR.Place) (disjoint : Bool) (path : Miri.Interpreter.OperandPath) :
    Miri.Interpreter.Call.evalFnCallArgumentAt h () (.Copy p) disjoint path =
      (do
        let v ← h.evalOperandAt () path (.Copy p)
        pure (.Copy v)) := rfl

private theorem annealEvalOperandWideSlice_fnItemConst (ld : List LocalDecl) (ly : LayoutTable)
    (fnTyId : Miri.MIR.TyId) :
    annealEvalOperandWideSlice ld ly
      (.Constant { span := defaultSpanRef, userType := none, value := .Val .ZeroSized fnTyId }) none =
      (do
        let st ← get
        if st.stack.currentFrame?.isNone then
          throw (.stack .emptyStack)
        pure ⟨.immediate .uninit, layoutOfEncodedTyId fnTyId ly⟩) := rfl

private theorem ite_bind_distrib_ws {m : Type → Type} [Monad m] {A B : Type} (c : Prop) [Decidable c]
    (x y : m A) (f : A → m B) :
    ((if c then x else y) >>= f) = if c then x >>= f else y >>= f := by
  split <;> rfl

private theorem annealUnsupportedLeaf_bind_ws {S A B : Type} (leaf : String)
    (f : A → EStateM Miri.Interpreter.StepError S B) :
    (annealUnsupportedLeaf leaf >>= f) = annealUnsupportedLeaf leaf := rfl

private theorem estate_throw_bind_ws {ε S A B : Type} (e : ε) (f : A → EStateM ε S B) :
    ((throw e : EStateM ε S A) >>= f) = throw e := rfl

private theorem genericTypes_single_ws (f : Miri.MIR.GenericArg → Option Miri.MIR.TyId)
    (a : Miri.MIR.GenericArg) :
    Array.filterMap f #[a] 0 1 = (match f a with | some b => #[b] | none => #[]) := by
  cases h : f a <;> simp [h]

/-- Reduction of vendored `Miri.Interpreter.Call.evalCallTerminator` under
`annealCallHooksWideSlice` on a 1-argument `WideSliceIntrinsic` call
(`size_of_val` or `align_of_val`). -/
theorem evalCallTerminator_wideSlice_one
    (ld : List LocalDecl) (ly : LayoutTable)
    (fnTyId : Miri.MIR.TyId) (wk : WideSliceIntrinsic) (argTy : Miri.MIR.TyId)
    (hdec : annealDecodeWideSliceFnItemTyId fnTyId = some (wk.defId, 1, argTy))
    (p₁ : Miri.MIR.Place)
    (dest : Miri.MIR.Place) (target : Option Miri.MIR.BasicBlockId)
    (unwind : Miri.MIR.UnwindAction) :
    Miri.Interpreter.Call.evalCallTerminator (annealCallHooksWideSlice ld ly) () annealCallBudget
      { sourceInfo := defaultSourceInfo
        kind := .Call
          (.Constant { span := defaultSpanRef, userType := none, value := .Val .ZeroSized fnTyId })
          #[⟨defaultSpanRef, .Copy p₁⟩] dest target unwind .Normal defaultSpanRef } =
    (do
      let oldIndex ← (annealPlaceHooks ld ly).frameIndex
      let oldFrame ← (annealPlaceHooks ld ly).getFrame
      let destPlace ← annealEvalPlaceWideSlice ld ly dest
      let _ ← annealEvalOperandWideSlice ld ly
        (.Constant { span := defaultSpanRef, userType := none, value := .Val .ZeroSized fnTyId }) none
      let v₁ ← annealEvalOperandWideSlice ld ly (.Copy p₁) none
      let handled ← Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooksWideSlice ld ly) () wk.name
        #[argTy] #[v₁] destPlace target
      if handled then pure ()
      else (annealUnsupportedLeaf
        "call.findMirOrEvalFn (MIR bodies, including intrinsic fallback bodies)")
      if target.isSome then
        if (← (annealPlaceHooks ld ly).frameIndex) == oldIndex then
          if (← (annealPlaceHooks ld ly).getFrame).location == oldFrame.location then
            throw (.invalidProgram "evaluating this call made no progress")) := by
  simp only [Miri.Interpreter.Call.evalCallTerminator, Miri.Interpreter.Call.evalCalleeAndArgs,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Array.size, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, List.range'_succ,
    List.range'_zero, List.forIn_cons, List.forIn_nil, List.getElem?_toArray,
    List.getElem?_cons_zero,
    evalFnCallArgumentAt_copy_ws,
    annealCallHooksWideSlice, annealCallHooks, annealEvalOperandWideSlice_fnItemConst,
    bind_assoc, pure_bind,
    layoutOfEncodedTyId_ty_ws, hdec,
    Miri.Interpreter.Call.initFnCall, Miri.Interpreter.Call.initFnCallStep, annealCallBudget,
    annealCallIntrinsicWideSlice, Miri.Interpreter.CallInstance.defId,
    Miri.Interpreter.CallInstanceKind.defId, wk.ofDefId?_defId,
    Miri.Interpreter.RuntimePlace.stackView_toRuntimePlace,
    Miri.Interpreter.FnArg.copyFnArg, List.map_toArray, List.map_cons, List.map_nil,
    genericTypes_single_ws, List.push_toArray, List.nil_append,
    ite_bind_distrib_ws, annealUnsupportedLeaf_bind_ws, estate_throw_bind_ws,
    Option.any_some, Bool.not_false, ↓reduceIte, Nat.le_refl, decide_true]
  rfl

/-! ## Part 3. Concrete Real-Step Witnesses & Stage-1 Divergence Witness -/

-- Serialize proof-body elaboration in `WideSliceWitnesses` so parallel `Elab.async`
-- worker threads do not hold multiple `with_unfolding_all rfl` WHNF arenas concurrently
-- under the 2-core cgroup `MemoryMax` budget.
set_option Elab.async false

namespace WideSliceWitnesses

private theorem prod_eq_fst_of_snd {α β : Type} {p : α × β} {b : β} (h : p.2 = b) :
    p = (p.1, b) := by
  cases p
  subst h
  rfl

/-- The `LocalValue` held by local `i` of the top frame of a vendored `Miri` state (`none` when
the stack is empty or the local does not exist). Used to pin the *values* computed by
`Miri.Interpreter.Step.step`, not merely the fact that it stepped. -/
def miriTopLocal? (m : AnnealStepState) (i : Nat) :
    Option (Miri.Interpreter.LocalValue AnnealProv) :=
  (m.stack.currentFrame?.bind (fun tf => tf.locals[i]?)).map (·.value)

/-- A live immediate 8-byte `usize` local holding `n` in vendored `Miri`. -/
def miriUsizeLocal (n : Nat) : Option (Miri.Interpreter.LocalValue AnnealProv) :=
  some (.live (.immediate (.scalar (.fromScalarInt
    (Miri.Memory.ScalarInt.ofUInt64 (UInt64.ofNat n))))))

/-- Concrete `[u32]` wide raw-pointer type `*const [u32]`. -/
def rawSliceU32Ty : Ty :=
  { kind := .rawPtr .not (.slice (.uint .u32)), layoutIdx := 0 }

/-- Concrete `str` wide raw-pointer type `*const str`. -/
def rawStrTy : Ty :=
  { kind := .rawPtr .not .str, layoutIdx := 0 }

/-- Concrete `[()]` ZST wide raw-pointer type `*const [()]`. -/
def rawSliceUnitTy : Ty :=
  { kind := .rawPtr .not (.slice (.tuple .nil)), layoutIdx := 0 }

/-- Concrete thin `*const u32` raw-pointer type. -/
def rawU32Ty : Ty :=
  { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 }

/-- Concrete `usize` type. -/
def usizeTy : Ty :=
  { kind := .uint .usize, layoutIdx := 0 }

/-- Concrete `[u32]` pointee type. -/
def sliceU32PointeeTy : Ty :=
  { kind := .slice (.uint .u32), layoutIdx := 0 }

/-- Concrete `str` pointee type. -/
def strPointeeTy : Ty :=
  { kind := .str, layoutIdx := 0 }

/-- Concrete `[()]` pointee type. -/
def sliceUnitPointeeTy : Ty :=
  { kind := .slice (.tuple .nil), layoutIdx := 0 }

/-- Default 8-byte `usize` ABI layout for witness bodies. -/
def usizeLayout : TypeLayout :=
  { size := { bytes := 8 }
    align := { bytes := 8 }
    backendRepr := .memory
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

/-- Function ABI returning `usize`. -/
def fnAbiUsize : FnAbi :=
  { args := []
    ret := { layout := usizeLayout, mode := .direct }
    conv := .rust
    canUnwind := false }

/-- Concrete MIR body witnessing a 5-step wide-slice pipeline:
1. `_1 = Aggregate(RawPtr([u32], const), [_2, _3])` (`ptr::slice_from_raw_parts(data, 3)`)
2. `_4 = PtrMetadata(Copy(_1))` (`ptr::metadata(_1) == 3`)
3. `_5 = Cast(PtrToPtr, Copy(_1), *const u32)` (`to_raw_parts` data pointer)
4. `_6 = Aggregate(RawPtr([u32], const), [Copy(_5), Copy(_4)])` (`from_raw_parts` round-trip)
5. `Call(core::intrinsics::size_of_val<[u32]>, [Copy(_6)], _0, Some(1))` → `Return` (`_0 == 12`). -/
def wideSlicePipelineBody : CapturedMir :=
  { defPath := "wide_slice_pipeline"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls :=
      [ { mutability := .mut, ty := usizeTy, debugName := none }           -- _0: usize
      , { mutability := .mut, ty := rawSliceU32Ty, debugName := none }     -- _1: *const [u32]
      , { mutability := .not, ty := rawU32Ty, debugName := none }          -- _2: *const u32
      , { mutability := .not, ty := usizeTy, debugName := none }           -- _3: usize
      , { mutability := .mut, ty := usizeTy, debugName := none }           -- _4: usize (metadata)
      , { mutability := .mut, ty := rawU32Ty, debugName := none }          -- _5: *const u32 (thin data)
      , { mutability := .mut, ty := rawSliceU32Ty, debugName := none }     -- _6: *const [u32] (round-trip)
      ]
    basicBlocks :=
      [ { statements :=
            [ ⟨.assign ⟨1, []⟩ (.aggregate (.rawPtr sliceU32PointeeTy .not)
                [.copy ⟨2, []⟩, .copy ⟨3, []⟩]), "s0"⟩
            , ⟨.assign ⟨4, []⟩ (.unaryOp .ptrMetadata (.copy ⟨1, []⟩)), "s1"⟩
            , ⟨.assign ⟨5, []⟩ (.cast .ptrToPtr (.copy ⟨1, []⟩) rawU32Ty), "s2"⟩
            , ⟨.assign ⟨6, []⟩ (.aggregate (.rawPtr sliceU32PointeeTy .not)
                [.copy ⟨5, []⟩, .copy ⟨4, []⟩]), "s3"⟩
            ]
          terminator :=
            ⟨.call
              (.constant
                { ty := { kind := .fnDef "core::intrinsics::size_of_val" [sliceU32PointeeTy.kind], layoutIdx := 0 }
                  val := .zeroSized })
              [.copy ⟨6, []⟩]
              ⟨0, []⟩
              (some 1)
              .unreachable, "t0"⟩
          isCleanup := false }
      , { statements := []
          terminator := ⟨.return_, "t1"⟩
          isCleanup := false }
      ]
    fnAbi := fnAbiUsize
    layouts := emptyLayoutTable
    allocations := [] }

/-- Translated `Miri.MIR.Body` for `wideSlicePipelineBody` with the `size_of_val`
terminator lowered via `translateWideSliceCallTerminator`. -/
def wideSlicePipelineMiriBody : Miri.MIR.Body :=
  let base := translateBody wideSlicePipelineBody
  match base.basicBlocks[0]? with
  | none => base
  | some bb0 =>
      let term0 : Miri.MIR.Terminator :=
        match translateWideSliceCallTerminator wideSlicePipelineBody.localDecls
            (.constant
              { ty := { kind := .fnDef "core::intrinsics::size_of_val" [sliceU32PointeeTy.kind], layoutIdx := 0 }
                val := .zeroSized })
            [.copy ⟨6, []⟩] ⟨0, []⟩ (some 1) .unreachable with
        | some tk => { sourceInfo := defaultSourceInfo, kind := tk }
        | none => bb0.terminator
      { base with basicBlocks := base.basicBlocks.set! 0 { bb0 with terminator := term0 } }

def sampleAllocId : Miri.Memory.AllocId :=
  ⟨1, by decide⟩

/-- Concrete Anneal pointer `p = { allocId := 1, offsetBytes := 0 }` and Miri
pointer `mptr = ⟨Size.ofBytes (annealStackBaseAddr sampleAllocId), .concrete sampleAllocId .one⟩`. -/
def sampleAnnealPtr : ProvenancePtr :=
  { allocId := 1, offsetBytes := 0 }

def sampleMiriPtr : Miri.Memory.Pointer AnnealProv :=
  ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr sampleAllocId),
   .concrete sampleAllocId Miri.Memory.BorTag.one⟩

def sampleMiriPtrSc : Miri.Memory.Scalar AnnealProv :=
  Miri.Memory.Scalar.fromPointer annealTargetDataLayout sampleMiriPtr

def sampleMiriLen3 : Miri.Memory.ScalarInt :=
  Miri.Memory.ScalarInt.ofUInt64 3

def sampleAllocMapEntry : AllocMapEntry :=
  { tag := 1, localIdx := 1, allocId := sampleAllocId, perm := .active, allocDead := false }

/-- Initial Anneal state for `wideSlicePipelineBody` with `_2 = .ptr sampleAnnealPtr 8`
and `_3 = .scalar ⟨3, 8⟩`. -/
def wideSlicePipelineInitAnneal : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals :=
          [ .uninit
          , .uninit
          , .init (.ptr sampleAnnealPtr 8)
          , .init (.scalar ⟨3, 8⟩)
          , .uninit
          , .uninit
          , .uninit ] }
    memory := emptyMemory }

/-- Initial Miri state for `wideSlicePipelineMiriBody`. -/
def wideSlicePipelineInitMiri : AnnealStepState :=
  { stack :=
      { frames :=
          #[ { body := wideSlicePipelineMiriBody
               bodyIdentity := .ofCanonicalIndex 0
               functionInstance := { kind := .Item 0, args := #[] }
               extra := ()
               returnContinuation := .stop false
               returnPlace := .frameLocal 0 0 none (translateTyWideSlice usizeTy) (.ofAllocationToken 0)
               localsIdentity := .ofAllocationToken 0
               locals :=
                 #[ ⟨.live (.immediate .uninit), some (translateTyWideSlice usizeTy)⟩
                  , ⟨.live (.immediate .uninit), some (translateTyWideSlice rawSliceU32Ty)⟩
                  , ⟨.live (.immediate (.scalar sampleMiriPtrSc)), some (translateTyWideSlice rawU32Ty)⟩
                  , ⟨.live (.immediate (.scalar (.fromScalarInt sampleMiriLen3))), some (translateTyWideSlice usizeTy)⟩
                  , ⟨.live (.immediate .uninit), some (translateTyWideSlice usizeTy)⟩
                  , ⟨.live (.immediate .uninit), some (translateTyWideSlice rawU32Ty)⟩
                  , ⟨.live (.immediate .uninit), some (translateTyWideSlice rawSliceU32Ty)⟩ ]
               vaList := #[]
               trackCallerArg := none
               location := .mir { block := 0, statementIndex := 0 } } ] }
    machine := AnnealMachine.empty }

/-- Wide-slice step hooks for `wideSlicePipelineBody`. -/
def wideSlicePipelineHooks :=
  annealStepHooksWideSlice wideSlicePipelineBody.localDecls wideSlicePipelineBody.layouts

/-- Successive vendored `Miri` states of `wideSlicePipelineMiriBody` (named so the kernel shares
their evaluation across the value checks of `w_wideSlice_roundtrip_and_sizeAlign_returns`). -/
def wideSlicePipelineMiri1 : AnnealStepState :=
  (Miri.Interpreter.Step.step wideSlicePipelineHooks () wideSlicePipelineInitMiri).1
def wideSlicePipelineMiri2 : AnnealStepState :=
  (Miri.Interpreter.Step.step wideSlicePipelineHooks () wideSlicePipelineMiri1).1
def wideSlicePipelineMiri3 : AnnealStepState :=
  (Miri.Interpreter.Step.step wideSlicePipelineHooks () wideSlicePipelineMiri2).1
def wideSlicePipelineMiri4 : AnnealStepState :=
  (Miri.Interpreter.Step.step wideSlicePipelineHooks () wideSlicePipelineMiri3).1
def wideSlicePipelineMiri5 : AnnealStepState :=
  (Miri.Interpreter.Step.step wideSlicePipelineHooks () wideSlicePipelineMiri4).1
def wideSlicePipelineMiri6 : AnnealStepState :=
  (Miri.Interpreter.Step.step wideSlicePipelineHooks () wideSlicePipelineMiri5).1

/-- Concrete Witness 1: Multi-step lockstep execution of `wideSlicePipelineBody`
(`AggregateKind.rawPtr` → `UnOp.ptrMetadata` → `CastKind.ptrToPtr` →
`AggregateKind.rawPtr` round-trip → `core::intrinsics::size_of_val<[u32]>` →
`Return`) returning `12` (`3 * 4`) in both `stepMirFn` and
`Miri.Interpreter.Step.step`. After every step the *values* agree: each vendored `Miri` local
written by the step (`miriTopLocal?`) is pinned and related to the matching Anneal local
(`WideSliceImmediateRel` for the wide pointers `_1` / `_6`, `PtrRel` for the thin data pointer
`_5`, `ScalarRel` for the metadata `_4` and the result `_0`); the sixth `Miri` step pops the frame
and the seventh reports termination (`.ok false`). -/
theorem w_wideSlice_roundtrip_and_sizeAlign_returns :
    let b := wideSlicePipelineBody
    let hooks := annealStepHooksWideSlice b.localDecls b.layouts
    let wideVal : Value := .aggregate 0 [.ptr sampleAnnealPtr 8, .scalar ⟨3, 8⟩]
    let wideImm : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair sampleMiriPtrSc (.fromScalarInt sampleMiriLen3)
    ∃ (s₁ s₂ s₃ s₄ s₅ : MachineState) (m₁ m₂ m₃ m₄ m₅ m₆ m₇ : AnnealStepState),
      stepMirFn b wideSlicePipelineInitAnneal = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () wideSlicePipelineInitMiri = (m₁, .ok true) ∧
      get? s₁.frame.locals 1 = some (.init wideVal) ∧
      miriTopLocal? m₁ 1 = some (.live (.immediate wideImm)) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      get? s₂.frame.locals 4 = some (.init (.scalar ⟨3, 8⟩)) ∧
      miriTopLocal? m₂ 4 = some (.live (.immediate (.scalar (.fromScalarInt sampleMiriLen3)))) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      get? s₃.frame.locals 5 = some (.init (.ptr sampleAnnealPtr 8)) ∧
      miriTopLocal? m₃ 5 = some (.live (.immediate (.scalar sampleMiriPtrSc))) ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      get? s₄.frame.locals 6 = some (.init wideVal) ∧
      miriTopLocal? m₄ 6 = some (.live (.immediate wideImm)) ∧
      stepMirFn b s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      get? s₅.frame.locals 0 = some (.init (.scalar ⟨12, 8⟩)) ∧
      miriTopLocal? m₅ 0 = miriUsizeLocal 12 ∧
      stepMirFn b s₅ = .ret (.normal (.scalar ⟨12, 8⟩, emptyMemory)) ∧
      Miri.Interpreter.Step.step hooks () m₅ = (m₆, .ok true) ∧
      m₆.stack.frames.size = 0 ∧
      Miri.Interpreter.Step.step hooks () m₆ = (m₇, .ok false) ∧
      WideSliceImmediateRel [sampleAllocMapEntry] wideVal wideImm ∧
      ScalarRel ⟨3, 8⟩ sampleMiriLen3 ∧
      PtrRel [sampleAllocMapEntry] sampleAnnealPtr sampleMiriPtr ∧
      ScalarRel ⟨12, 8⟩ (Miri.Memory.ScalarInt.ofUInt64 (UInt64.ofNat 12)) := by
  refine ⟨_, _, _, _, _, wideSlicePipelineMiri1, wideSlicePipelineMiri2, wideSlicePipelineMiri3,
    wideSlicePipelineMiri4, wideSlicePipelineMiri5, wideSlicePipelineMiri6, _,
    rfl, prod_eq_fst_of_snd rfl, rfl, (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd rfl, rfl, (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd rfl, rfl, (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd rfl, rfl, (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), rfl, (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), (by with_unfolding_all rfl),
    prod_eq_fst_of_snd (by with_unfolding_all rfl), ?_, ?_, ?_, ?_⟩
  · exact .provenance
      (PtrRel.of_stackAllocPlace (.head _) (by decide))
      ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
      rfl
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
  · exact PtrRel.of_stackAllocPlace (.head _) (by decide)
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩

/-- Concrete intrinsic-call body for `size_of_val` or `align_of_val` on a single
wide-pointer local `_1` of type `ptrTy` with pointee `pointeeTy`. -/
def singleWideIntrinsicBody (isAlign : Bool) (ptrTy pointeeTy : Ty) : CapturedMir :=
  let defPath :=
    if isAlign then "core::intrinsics::align_of_val"
    else "core::intrinsics::size_of_val"
  { defPath := "single_wide_intrinsic"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls :=
      [ { mutability := .mut, ty := usizeTy, debugName := none }
      , { mutability := .not, ty := ptrTy, debugName := none } ]
    basicBlocks :=
      [ { statements := []
          terminator :=
            ⟨.call
              (.constant
                { ty := { kind := .fnDef defPath [pointeeTy.kind], layoutIdx := 0 }
                  val := .zeroSized })
              [.copy ⟨1, []⟩]
              ⟨0, []⟩
              (some 1)
              .unreachable, "t0"⟩
          isCleanup := false }
      , { statements := []
          terminator := ⟨.return_, "t1"⟩
          isCleanup := false } ]
    fnAbi := fnAbiUsize
    layouts := emptyLayoutTable
    allocations := [] }

/-- Translated `Miri.MIR.Body` for `singleWideIntrinsicBody`. -/
def singleWideIntrinsicMiriBody (isAlign : Bool) (ptrTy pointeeTy : Ty) : Miri.MIR.Body :=
  let b := singleWideIntrinsicBody isAlign ptrTy pointeeTy
  let base := translateBody b
  let defPath :=
    if isAlign then "core::intrinsics::align_of_val"
    else "core::intrinsics::size_of_val"
  match base.basicBlocks[0]? with
  | none => base
  | some bb0 =>
      let term0 : Miri.MIR.Terminator :=
        match translateWideSliceCallTerminator b.localDecls
            (.constant
              { ty := { kind := .fnDef defPath [pointeeTy.kind], layoutIdx := 0 }
                val := .zeroSized })
            [.copy ⟨1, []⟩] ⟨0, []⟩ (some 1) .unreachable with
        | some tk => { sourceInfo := defaultSourceInfo, kind := tk }
        | none => bb0.terminator
      { base with basicBlocks := base.basicBlocks.set! 0 { bb0 with terminator := term0 } }

/-- Initial Anneal state for `singleWideIntrinsicBody` with `_1 = wideVal`. -/
def singleWideIntrinsicInitAnneal (wideVal : Value) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init wideVal] }
    memory := emptyMemory }

/-- Initial Miri state for `singleWideIntrinsicMiriBody` with `_1 = wideImm`. -/
def singleWideIntrinsicInitMiri (isAlign : Bool) (ptrTy pointeeTy : Ty)
    (wideImm : Miri.Interpreter.Immediate AnnealProv) : AnnealStepState :=
  { stack :=
      { frames :=
          #[ { body := singleWideIntrinsicMiriBody isAlign ptrTy pointeeTy
               bodyIdentity := .ofCanonicalIndex 0
               functionInstance := { kind := .Item 0, args := #[] }
               extra := ()
               returnContinuation := .stop false
               returnPlace := .frameLocal 0 0 none (translateTyWideSlice usizeTy) (.ofAllocationToken 0)
               localsIdentity := .ofAllocationToken 0
               locals :=
                 #[ ⟨.live (.immediate .uninit), some (translateTyWideSlice usizeTy)⟩
                  , ⟨.live (.immediate wideImm), some (translateTyWideSlice ptrTy)⟩ ]
               vaList := #[]
               trackCallerArg := none
               location := .mir { block := 0, statementIndex := 0 } } ] }
    machine := AnnealMachine.empty }

/-- Concrete Witness 2: `str` wide pointer (`len = 5` → `size_of_val = 5`,
`align_of_val = 1`) and ZST `[()]` wide pointer (`len = 1000` → `size_of_val = 0`,
`align_of_val = 1`) step in lockstep in both `stepMirFn` and
`Miri.Interpreter.Step.step`, with the vendored `Miri` result local `_0` pinned to the same value
as Anneal's (`miriTopLocal?`). -/
theorem w_wideStr_and_zstSlice_sizeAlign_returns :
    let strVal : Value := .aggregate 0 [.ptr sampleAnnealPtr 8, .scalar ⟨5, 8⟩]
    let strImm : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair sampleMiriPtrSc (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 5))
    let zstVal : Value := .aggregate 0 [.ptr sampleAnnealPtr 8, .scalar ⟨1000, 8⟩]
    let zstImm : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair sampleMiriPtrSc (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 1000))
    let bStrSz := singleWideIntrinsicBody false rawStrTy strPointeeTy
    let bStrAl := singleWideIntrinsicBody true rawStrTy strPointeeTy
    let bZstSz := singleWideIntrinsicBody false rawSliceUnitTy sliceUnitPointeeTy
    let bZstAl := singleWideIntrinsicBody true rawSliceUnitTy sliceUnitPointeeTy
    ∃ (sStrSz sStrAl sZstSz sZstAl : MachineState)
      (mStrSz mStrAl mZstSz mZstAl : AnnealStepState),
      stepMirFn bStrSz (singleWideIntrinsicInitAnneal strVal) = .step sStrSz ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bStrSz.localDecls bStrSz.layouts) ()
        (singleWideIntrinsicInitMiri false rawStrTy strPointeeTy strImm) = (mStrSz, .ok true) ∧
      get? sStrSz.frame.locals 0 = some (.init (.scalar ⟨5, 8⟩)) ∧
      miriTopLocal? mStrSz 0 = miriUsizeLocal 5 ∧
      stepMirFn bStrAl (singleWideIntrinsicInitAnneal strVal) = .step sStrAl ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bStrAl.localDecls bStrAl.layouts) ()
        (singleWideIntrinsicInitMiri true rawStrTy strPointeeTy strImm) = (mStrAl, .ok true) ∧
      get? sStrAl.frame.locals 0 = some (.init (.scalar ⟨1, 8⟩)) ∧
      miriTopLocal? mStrAl 0 = miriUsizeLocal 1 ∧
      stepMirFn bZstSz (singleWideIntrinsicInitAnneal zstVal) = .step sZstSz ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bZstSz.localDecls bZstSz.layouts) ()
        (singleWideIntrinsicInitMiri false rawSliceUnitTy sliceUnitPointeeTy zstImm) = (mZstSz, .ok true) ∧
      get? sZstSz.frame.locals 0 = some (.init (.scalar ⟨0, 8⟩)) ∧
      miriTopLocal? mZstSz 0 = miriUsizeLocal 0 ∧
      stepMirFn bZstAl (singleWideIntrinsicInitAnneal zstVal) = .step sZstAl ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bZstAl.localDecls bZstAl.layouts) ()
        (singleWideIntrinsicInitMiri true rawSliceUnitTy sliceUnitPointeeTy zstImm) = (mZstAl, .ok true) ∧
      get? sZstAl.frame.locals 0 = some (.init (.scalar ⟨1, 8⟩)) ∧
      miriTopLocal? mZstAl 0 = miriUsizeLocal 1 :=
  ⟨_, _, _, _, _, _, _, _,
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), rfl, (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), rfl, (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), rfl, (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), rfl, (by with_unfolding_all rfl)⟩

/-- Concrete Witness 3: Exact `isize::MAX = 2^63 - 1` (`0x7fff_ffff_ffff_ffff`)
boundary on `*const [u32]` and `*const str` for both `size_of_val` and
`align_of_val`:
* For `[u32]` (`elemSz = 4`), `len = 2^61 - 1` (`0x1fff_ffff_ffff_ffff`) has byte
  size `2^63 - 4 = 0x7fff_ffff_ffff_fffc ≤ isize::MAX` and succeeds in both
  `stepMirFn` and `Miri.Interpreter.Step.step`.
* For `[u32]` (`elemSz = 4`), `len = 2^61` (`0x2000_0000_0000_0000`) has byte
  size `2^63 > isize::MAX` and faults with `MirStepNode.fail .ub` in `stepMirFn`
  and `.error (.undefinedBehavior "InvalidMeta(SliceTooBig)")` in
  `Miri.Interpreter.Step.step` for **both** `size_of_val` and `align_of_val`.
* For `str` (`elemSz = 1`), `len = 2^63` (`0x8000_0000_0000_0000`) faults with
  `MirStepNode.fail .ub` in `stepMirFn` and
  `.error (.undefinedBehavior "InvalidMeta(SliceTooBig)")` in
  `Miri.Interpreter.Step.step` for **both** `size_of_val` and `align_of_val`. -/
theorem w_wideSlice_isizeMax_boundary_agrees :
    let okLen : Nat := 0x1fff_ffff_ffff_ffff
    let ovfU32Len : Nat := 0x2000_0000_0000_0000
    let ovfStrLen : Nat := 0x8000_0000_0000_0000
    let okVal : Value := .aggregate 0 [.ptr sampleAnnealPtr 8, .scalar ⟨okLen, 8⟩]
    let okImm : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair sampleMiriPtrSc (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 0x1fff_ffff_ffff_ffff))
    let ovfU32Val : Value := .aggregate 0 [.ptr sampleAnnealPtr 8, .scalar ⟨ovfU32Len, 8⟩]
    let ovfU32Imm : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair sampleMiriPtrSc (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 0x2000_0000_0000_0000))
    let ovfStrVal : Value := .aggregate 0 [.ptr sampleAnnealPtr 8, .scalar ⟨ovfStrLen, 8⟩]
    let ovfStrImm : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair sampleMiriPtrSc (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 0x8000_0000_0000_0000))
    let bU32Sz := singleWideIntrinsicBody false rawSliceU32Ty sliceU32PointeeTy
    let bU32Al := singleWideIntrinsicBody true rawSliceU32Ty sliceU32PointeeTy
    let bStrSz := singleWideIntrinsicBody false rawStrTy strPointeeTy
    let bStrAl := singleWideIntrinsicBody true rawStrTy strPointeeTy
    ∃ (sOk : MachineState) (mOk mOvf1 mOvf2 mOvf3 mOvf4 : AnnealStepState),
      stepMirFn bU32Sz (singleWideIntrinsicInitAnneal okVal) = .step sOk ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bU32Sz.localDecls bU32Sz.layouts) ()
        (singleWideIntrinsicInitMiri false rawSliceU32Ty sliceU32PointeeTy okImm) = (mOk, .ok true) ∧
      get? sOk.frame.locals 0 = some (.init (.scalar ⟨0x7fff_ffff_ffff_fffc, 8⟩)) ∧
      miriTopLocal? mOk 0 = miriUsizeLocal 0x7fff_ffff_ffff_fffc ∧
      stepMirFn bU32Sz (singleWideIntrinsicInitAnneal ovfU32Val) = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bU32Sz.localDecls bU32Sz.layouts) ()
        (singleWideIntrinsicInitMiri false rawSliceU32Ty sliceU32PointeeTy ovfU32Imm) =
        (mOvf1, .error (.undefinedBehavior "InvalidMeta(SliceTooBig)")) ∧
      stepMirFn bU32Al (singleWideIntrinsicInitAnneal ovfU32Val) = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bU32Al.localDecls bU32Al.layouts) ()
        (singleWideIntrinsicInitMiri true rawSliceU32Ty sliceU32PointeeTy ovfU32Imm) =
        (mOvf2, .error (.undefinedBehavior "InvalidMeta(SliceTooBig)")) ∧
      stepMirFn bStrSz (singleWideIntrinsicInitAnneal ovfStrVal) = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bStrSz.localDecls bStrSz.layouts) ()
        (singleWideIntrinsicInitMiri false rawStrTy strPointeeTy ovfStrImm) =
        (mOvf3, .error (.undefinedBehavior "InvalidMeta(SliceTooBig)")) ∧
      stepMirFn bStrAl (singleWideIntrinsicInitAnneal ovfStrVal) = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bStrAl.localDecls bStrAl.layouts) ()
        (singleWideIntrinsicInitMiri true rawStrTy strPointeeTy ovfStrImm) =
        (mOvf4, .error (.undefinedBehavior "InvalidMeta(SliceTooBig)")) :=
  ⟨_, _, _, _, _, _,
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), rfl, (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl)⟩

/-- Concrete Witness 3b: the in-bounds side of the exact `isize::MAX` boundary, with values pinned
on BOTH interpreters (`miriTopLocal?`):
* `[u32]` at `len = 2^61 - 1`: `size_of_val = 2^63 - 4` and `align_of_val = 4`;
* `str` at `len = 2^63 - 1` (`0x7fff_ffff_ffff_ffff`, the largest valid `str` length):
  `size_of_val = 2^63 - 1 = isize::MAX` and `align_of_val = 1` — one byte below the
  `len = 2^63` `InvalidMeta(SliceTooBig)` fault of `w_wideSlice_isizeMax_boundary_agrees`. -/
theorem w_wideSlice_isizeMax_exact_boundary_values_agree :
    let okU32Len : Nat := 0x1fff_ffff_ffff_ffff
    let okStrLen : Nat := 0x7fff_ffff_ffff_ffff
    let okU32Val : Value := .aggregate 0 [.ptr sampleAnnealPtr 8, .scalar ⟨okU32Len, 8⟩]
    let okU32Imm : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair sampleMiriPtrSc
        (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 0x1fff_ffff_ffff_ffff))
    let okStrVal : Value := .aggregate 0 [.ptr sampleAnnealPtr 8, .scalar ⟨okStrLen, 8⟩]
    let okStrImm : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair sampleMiriPtrSc
        (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 0x7fff_ffff_ffff_ffff))
    let bU32Sz := singleWideIntrinsicBody false rawSliceU32Ty sliceU32PointeeTy
    let bU32Al := singleWideIntrinsicBody true rawSliceU32Ty sliceU32PointeeTy
    let bStrSz := singleWideIntrinsicBody false rawStrTy strPointeeTy
    let bStrAl := singleWideIntrinsicBody true rawStrTy strPointeeTy
    ∃ (sU32Sz sU32Al sStrSz sStrAl : MachineState)
      (mU32Sz mU32Al mStrSz mStrAl : AnnealStepState),
      stepMirFn bU32Sz (singleWideIntrinsicInitAnneal okU32Val) = .step sU32Sz ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bU32Sz.localDecls bU32Sz.layouts) ()
        (singleWideIntrinsicInitMiri false rawSliceU32Ty sliceU32PointeeTy okU32Imm) =
        (mU32Sz, .ok true) ∧
      get? sU32Sz.frame.locals 0 = some (.init (.scalar ⟨0x7fff_ffff_ffff_fffc, 8⟩)) ∧
      miriTopLocal? mU32Sz 0 = miriUsizeLocal 0x7fff_ffff_ffff_fffc ∧
      stepMirFn bU32Al (singleWideIntrinsicInitAnneal okU32Val) = .step sU32Al ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bU32Al.localDecls bU32Al.layouts) ()
        (singleWideIntrinsicInitMiri true rawSliceU32Ty sliceU32PointeeTy okU32Imm) =
        (mU32Al, .ok true) ∧
      get? sU32Al.frame.locals 0 = some (.init (.scalar ⟨4, 8⟩)) ∧
      miriTopLocal? mU32Al 0 = miriUsizeLocal 4 ∧
      stepMirFn bStrSz (singleWideIntrinsicInitAnneal okStrVal) = .step sStrSz ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bStrSz.localDecls bStrSz.layouts) ()
        (singleWideIntrinsicInitMiri false rawStrTy strPointeeTy okStrImm) = (mStrSz, .ok true) ∧
      get? sStrSz.frame.locals 0 = some (.init (.scalar ⟨0x7fff_ffff_ffff_ffff, 8⟩)) ∧
      miriTopLocal? mStrSz 0 = miriUsizeLocal 0x7fff_ffff_ffff_ffff ∧
      stepMirFn bStrAl (singleWideIntrinsicInitAnneal okStrVal) = .step sStrAl ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bStrAl.localDecls bStrAl.layouts) ()
        (singleWideIntrinsicInitMiri true rawStrTy strPointeeTy okStrImm) = (mStrAl, .ok true) ∧
      get? sStrAl.frame.locals 0 = some (.init (.scalar ⟨1, 8⟩)) ∧
      miriTopLocal? mStrAl 0 = miriUsizeLocal 1 :=
  ⟨_, _, _, _, _, _, _, _,
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), rfl, (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), rfl, (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), rfl, (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), rfl, (by with_unfolding_all rfl)⟩

/-- Concrete Witness 4 (`DIV-STAGE1-SCALAR-ADDR-WIDE-SLICE-SIZE-ALIGN`):
Documented Stage-1 `.scalar`-address divergence between `Trusted.Rustc.V2026_06_01`
(`stepMirFn`) and vendored `Miri` (`Miri.Interpreter.Step.step`) on a
provenance-free wide slice pointer `ptr::slice_from_raw_parts(without_provenance(4), 0)`
(`Value.aggregate 0 [.scalar ⟨4, 8⟩, .scalar ⟨0, 8⟩]`):
1. **Agreement on `UnOp.ptrMetadata` and `CastKind.ptrToPtr`**: Both Anneal
   `evalRvalue` and vendored `Miri` (`ScalarOps.unary .PtrMetadata` and
   `Cast.ptrToPtr`) accept the provenance-free wide pointer and return length
   `0` and thin address `4`.
2. **Stage-1 Divergence on `size_of_val` and `align_of_val`**:
   * Stage-1 `evalNonSelectIntrinsicCall` (`Terminators.lean:2543, 2606`)
     pattern-matches on `.aggregate 0 (.ptr _ ptrSz :: .scalar lenSc :: .nil)`
     and therefore faults with `MirStepNode.fail .ub` when the data pointer is
     `.scalar ⟨4, 8⟩`.
   * Vendored `Miri` (`Intrinsics.eval` → `immPointerToPlace` →
     `DynamicLayout.sizeAndAlignOfVal`) converts `.scalar ⟨4, 8⟩` via
     `Scalar.toPointer` (`Pointer.withoutProvenance 4`) without requiring
     allocation provenance, succeeding with `0` for `size_of_val` and `4` for
     `align_of_val` on `*const [u32]`. -/
theorem div_stage1_scalarAddr_wideSlice_sizeOfVal_alignOfVal :
    let scVal : Value := .aggregate 0 [.scalar ⟨4, 8⟩, .scalar ⟨0, 8⟩]
    let maddr4 : Miri.Memory.ScalarInt := Miri.Memory.ScalarInt.ofUInt64 4
    let mlen0 : Miri.Memory.ScalarInt := Miri.Memory.ScalarInt.ofUInt64 0
    let scImm : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair (.fromScalarInt maddr4) (.fromScalarInt mlen0)
    let bU32Sz := singleWideIntrinsicBody false rawSliceU32Ty sliceU32PointeeTy
    let bU32Al := singleWideIntrinsicBody true rawSliceU32Ty sliceU32PointeeTy
    WideSliceImmediateRel [] scVal scImm ∧
    evalRvalue [.uninit, .init scVal] (.unaryOp .ptrMetadata (.copy ⟨1, []⟩))
      emptyMemory bU32Sz.localDecls bU32Sz.layouts =
      .ok (.scalar ⟨0, 8⟩) [.uninit, .init scVal] emptyMemory ∧
    evalRvalue [.uninit, .init scVal] (.cast .ptrToPtr (.copy ⟨1, []⟩) rawU32Ty)
      emptyMemory bU32Sz.localDecls bU32Sz.layouts =
      .ok (.scalar ⟨4, 8⟩) [.uninit, .init scVal] emptyMemory ∧
    stepMirFn bU32Sz (singleWideIntrinsicInitAnneal scVal) = .fail .ub ∧
    stepMirFn bU32Al (singleWideIntrinsicInitAnneal scVal) = .fail .ub ∧
    ∃ (mSz mAl : AnnealStepState),
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bU32Sz.localDecls bU32Sz.layouts) ()
        (singleWideIntrinsicInitMiri false rawSliceU32Ty sliceU32PointeeTy scImm) =
        (mSz, .ok true) ∧
      mSz.stack.currentFrame?.bind (fun tf => tf.locals[0]?) =
        some ⟨.live (.immediate (.scalar (.fromScalarInt mlen0))),
              some (translateTyWideSlice usizeTy)⟩ ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bU32Al.localDecls bU32Al.layouts) ()
        (singleWideIntrinsicInitMiri true rawSliceU32Ty sliceU32PointeeTy scImm) =
        (mAl, .ok true) ∧
      mAl.stack.currentFrame?.bind (fun tf => tf.locals[0]?) =
        some ⟨.live (.immediate (.scalar (.fromScalarInt maddr4))),
              some (translateTyWideSlice usizeTy)⟩ :=
  ⟨.scalarAddr
      ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
      ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
      rfl rfl,
   rfl, rfl, rfl, rfl, _, _,
   prod_eq_fst_of_snd (by with_unfolding_all rfl), (by with_unfolding_all rfl),
   prod_eq_fst_of_snd (by with_unfolding_all rfl), (by with_unfolding_all rfl)⟩

/-- A live immediate 4-byte `u32` local holding `n` in vendored `Miri`. -/
def miriU32Local (n : Nat) : Option (Miri.Interpreter.LocalValue AnnealProv) :=
  some (.live (.immediate (.scalar (.fromScalarInt
    (Miri.Memory.ScalarInt.ofUInt32 (UInt32.ofNat n))))))

/-- Concrete `u32` type (`4` bytes). -/
def u32Ty : Ty :=
  { kind := .uint .u32, layoutIdx := 0 }

/-- Concrete `[u32; 4]` array type (`16` bytes). -/
def arrU32_4Ty : Ty :=
  { kind := .array (.uint .u32) 4, layoutIdx := 0 }

/-- Concrete `*mut [u32]` wide raw-pointer type. -/
def rawMutSliceU32Ty : Ty :=
  { kind := .rawPtr .mut (.slice (.uint .u32)), layoutIdx := 0 }

/-- Default 4-byte `u32` ABI layout for witness bodies. -/
def u32Layout : TypeLayout :=
  { size := { bytes := 4 }
    align := { bytes := 4 }
    backendRepr := .memory
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

/-- Function ABI returning `u32`. -/
def fnAbiU32 : FnAbi :=
  { args := []
    ret := { layout := u32Layout, mode := .direct }
    conv := .rust
    canUnwind := false }

private def extractOkws {ε α : Type} (e : Except ε α) (h : e.isOk = true) : α :=
  match e, h with
  | .ok a, _ => a

/-- Concrete 16-byte stack allocation aligned to 4 bytes holding
`[10_u32, 20_u32, 30_u32, 40_u32]` in little-endian byte order. -/
def sampleArrU32Alloc :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  (extractOkws
    (Miri.Memory.Allocation.fromBytes (Prov := AnnealProv)
      #[10, 0, 0, 0, 20, 0, 0, 0, 30, 0, 0, 0, 40, 0, 0, 0]
      (translateAlignBytes 4) .Mut)
    rfl).withExtra none

/-- `AnnealMachine` with `sampleArrU32Alloc` live at `sampleAllocId` (`1`) and
cached base address `annealStackBaseAddr sampleAllocId`. -/
def sampleArrU32Machine : AnnealMachine :=
  { memory :=
      { AnnealMachine.empty.memory with
        live := #[(sampleAllocId, ⟨.stack, sampleArrU32Alloc⟩)] }
    addresses :=
      { provenanceMode := .default
        addressMode := .managed
        generation := none
        baseAddr := #[⟨sampleAllocId, annealStackBaseAddr sampleAllocId⟩] }
    borrowTracker := none }

/-- Anneal `[10_u32, 20_u32, 30_u32, 40_u32]` array value. -/
def sampleAnnealArrVal : Value :=
  .aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨40, 4⟩]

/-- Anneal `Memory` with active stack borrow `sampleAllocMapEntry` (`tag = 1`
targeting local `1`). -/
def sampleAnnealArrMemory : Memory :=
  { emptyMemory with
    borrows := [sampleAllocMapEntry.toBorrowEntry]
    nextTag := 2 }

/-- Single-statement MIR body evaluating `_0 = Rvalue.len (*_2)` over `_2 : *mut [u32]`. -/
def wideSliceSingleLenBody : CapturedMir :=
  { defPath := "wide_slice_single_len"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls :=
      [ { mutability := .mut, ty := usizeTy, debugName := none }           -- _0: usize
      , { mutability := .mut, ty := arrU32_4Ty, debugName := none }        -- _1: [u32; 4]
      , { mutability := .mut, ty := rawMutSliceU32Ty, debugName := none }  -- _2: *mut [u32]
      , { mutability := .not, ty := usizeTy, debugName := none }           -- _3: usize
      ]
    basicBlocks :=
      [ { statements := [ ⟨.assign ⟨0, []⟩ (.len ⟨2, [.deref]⟩), "s0"⟩ ]
          terminator := ⟨.return_, "t0"⟩
          isCleanup := false } ]
    fnAbi := fnAbiUsize
    layouts := emptyLayoutTable
    allocations := [] }

/-- Single-statement MIR body reading `_0 = copy (*_2)[_3]` over `_2 : *mut [u32]`. -/
def wideSliceSingleIndexReadBody : CapturedMir :=
  { defPath := "wide_slice_single_index_read"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls :=
      [ { mutability := .mut, ty := u32Ty, debugName := none }             -- _0: u32
      , { mutability := .mut, ty := arrU32_4Ty, debugName := none }        -- _1: [u32; 4]
      , { mutability := .mut, ty := rawMutSliceU32Ty, debugName := none }  -- _2: *mut [u32]
      , { mutability := .not, ty := usizeTy, debugName := none }           -- _3: usize
      ]
    basicBlocks :=
      [ { statements := [ ⟨.assign ⟨0, []⟩ (.use (.copy ⟨2, [.deref, .index 3]⟩)), "s0"⟩ ]
          terminator := ⟨.return_, "t0"⟩
          isCleanup := false } ]
    fnAbi := fnAbiU32
    layouts := emptyLayoutTable
    allocations := [] }

/-- Single-statement MIR body writing `(*_2)[_3] = const 99_u32` over `_2 : *mut [u32]`. -/
def wideSliceSingleIndexWriteBody : CapturedMir :=
  { defPath := "wide_slice_single_index_write"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls :=
      [ { mutability := .mut, ty := u32Ty, debugName := none }             -- _0: u32
      , { mutability := .mut, ty := arrU32_4Ty, debugName := none }        -- _1: [u32; 4]
      , { mutability := .mut, ty := rawMutSliceU32Ty, debugName := none }  -- _2: *mut [u32]
      , { mutability := .not, ty := usizeTy, debugName := none }           -- _3: usize
      ]
    basicBlocks :=
      [ { statements :=
            [ ⟨.assign ⟨2, [.deref, .index 3]⟩
                (.use (.constant { ty := u32Ty, val := .scalar (.int ⟨99, 4⟩) })), "s0"⟩ ]
          terminator := ⟨.return_, "t0"⟩
          isCleanup := false } ]
    fnAbi := fnAbiU32
    layouts := emptyLayoutTable
    allocations := [] }

/-- Single-statement MIR body extracting `_0 = PtrMetadata(copy _2)` on `_2 : *mut [u32]`. -/
def wideSliceSingleMetadataBody : CapturedMir :=
  { defPath := "wide_slice_single_metadata"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls :=
      [ { mutability := .mut, ty := usizeTy, debugName := none }           -- _0: usize
      , { mutability := .mut, ty := arrU32_4Ty, debugName := none }        -- _1: [u32; 4]
      , { mutability := .mut, ty := rawMutSliceU32Ty, debugName := none }  -- _2: *mut [u32]
      , { mutability := .not, ty := usizeTy, debugName := none }           -- _3: usize
      ]
    basicBlocks :=
      [ { statements := [ ⟨.assign ⟨0, []⟩ (.unaryOp .ptrMetadata (.copy ⟨2, []⟩)), "s0"⟩ ]
          terminator := ⟨.return_, "t0"⟩
          isCleanup := false } ]
    fnAbi := fnAbiUsize
    layouts := emptyLayoutTable
    allocations := [] }

/-- Build an initial Anneal state for the 4-local wide-slice index/metadata bodies. -/
def wideSlice4LocalInitAnneal (ptr : ProvenancePtr) (len idx : Nat) (mem : Memory) : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals :=
          [ .uninit
          , .init sampleAnnealArrVal
          , .init (.aggregate 0 [.ptr ptr 8, .scalar ⟨len, 8⟩])
          , .init (.scalar ⟨idx, 8⟩) ] }
    memory := mem }

/-- Build an initial Miri state for the 4-local wide-slice index/metadata bodies. -/
def wideSlice4LocalInitMiri (b : CapturedMir) (retTy : Ty)
    (mptr : Miri.Memory.Pointer AnnealProv) (len idx : UInt64)
    (mach : AnnealMachine) : AnnealStepState :=
  let arrMp : Miri.Interpreter.MemPlace AnnealProv :=
    ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr sampleAllocId),
      some (.concrete sampleAllocId Miri.Memory.BorTag.one)⟩, .none, none⟩
  let wideImm : Miri.Interpreter.Immediate AnnealProv :=
    .scalarPair
      (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)
      (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 len))
  let mIdx : Miri.Memory.ScalarInt := Miri.Memory.ScalarInt.ofUInt64 idx
  { stack :=
      { frames :=
          #[ { body := translateBody b
               bodyIdentity := .ofCanonicalIndex 0
               functionInstance := { kind := .Item 0, args := #[] }
               extra := ()
               returnContinuation := .stop false
               returnPlace := .frameLocal 0 0 none (translateTyWideSlice retTy) (.ofAllocationToken 0)
               localsIdentity := .ofAllocationToken 0
               locals :=
                 #[ ⟨.live (.immediate .uninit), some (translateTyWideSlice retTy)⟩
                  , ⟨.live (.indirect arrMp), some (translateTyWideSlice arrU32_4Ty)⟩
                  , ⟨.live (.immediate wideImm), some (translateTyWideSlice rawMutSliceU32Ty)⟩
                  , ⟨.live (.immediate (.scalar (.fromScalarInt mIdx))), some (translateTyWideSlice usizeTy)⟩ ]
               vaList := #[]
               trackCallerArg := none
               location := .mir { block := 0, statementIndex := 0 } } ] }
    machine := mach }

/-- Concrete Witness 5a: Real-step (`stepMirFn` and `Miri.Interpreter.Step.step`)
lockstep execution for wide-slice `Rvalue.len (*_2)` and in-bounds slice indexing
read `_0 = copy (*_2)[_3]` over a wide `*mut [u32]` pointer of length `3` into
`[10_u32, 20_u32, 30_u32, 40_u32]`:
1. `_0 = Rvalue.len (*_2)` steps to `3` in both Anneal (`get? sLen.frame.locals 0`)
   and vendored `Miri` (`miriTopLocal? mLen 0 = miriUsizeLocal 3`),
2. `_0 = copy (*_2)[1]` reads `20_u32` in both Anneal (`get? sRead.frame.locals 0`)
   and vendored `Miri` (`miriTopLocal? mRead 0 = miriU32Local 20`). -/
theorem w_wideSlice_len_and_index_read_returns :
    let bLen := wideSliceSingleLenBody
    let bRead := wideSliceSingleIndexReadBody
    let hLen := annealStepHooksWideSlice bLen.localDecls bLen.layouts
    let hRead := annealStepHooksWideSlice bRead.localDecls bRead.layouts
    ∃ (sLen sRead : MachineState) (mLen mRead : AnnealStepState),
      stepMirFn bLen (wideSlice4LocalInitAnneal sampleAnnealPtr 3 1 sampleAnnealArrMemory) =
        .step sLen ∧
      Miri.Interpreter.Step.step hLen ()
        (wideSlice4LocalInitMiri bLen usizeTy sampleMiriPtr 3 1 sampleArrU32Machine) =
        (mLen, .ok true) ∧
      get? sLen.frame.locals 0 = some (.init (.scalar ⟨3, 8⟩)) ∧
      miriTopLocal? mLen 0 = miriUsizeLocal 3 ∧
      stepMirFn bRead (wideSlice4LocalInitAnneal sampleAnnealPtr 3 1 sampleAnnealArrMemory) =
        .step sRead ∧
      Miri.Interpreter.Step.step hRead ()
        (wideSlice4LocalInitMiri bRead u32Ty sampleMiriPtr 3 1 sampleArrU32Machine) =
        (mRead, .ok true) ∧
      get? sRead.frame.locals 0 = some (.init (.scalar ⟨20, 4⟩)) ∧
      miriTopLocal? mRead 0 = miriU32Local 20 :=
  ⟨_, _, _, _,
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), rfl, (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), rfl, (by with_unfolding_all rfl)⟩

private def sampleElem1Mp : Miri.Interpreter.MemPlace AnnealProv :=
  ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr sampleAllocId + 4),
    some (.concrete sampleAllocId Miri.Memory.BorTag.one)⟩, .none, none⟩

private def estateVal? {ε σ α : Type} : EStateM.Result ε σ α → Option α
  | .ok a _ => some a
  | .error _ _ => none

private def estateState {ε σ α : Type} : EStateM.Result ε σ α → σ
  | .ok _ s => s
  | .error _ s => s

private theorem estate_eq_ok_of_val {ε σ α : Type}
    {r : EStateM.Result ε σ α} {a : α}
    (h : estateVal? r = some a) :
    r = .ok a (estateState r) := by
  cases r with
  | ok a' s' =>
      injection h with ha
      subst ha
      rfl
  | error e s' => cases h

set_option maxRecDepth 20000 in
private theorem eval_bWrite_pre_writeMemory :
    let initW := wideSlice4LocalInitMiri wideSliceSingleIndexWriteBody u32Ty sampleMiriPtr 3 1 sampleArrU32Machine
    ∃ (st1 st2 : AnnealStepState),
      annealEvalPlaceWideSliceWithSkip wideSliceSingleIndexWriteBody.localDecls
        wideSliceSingleIndexWriteBody.layouts ⟨2, #[.Deref, .Index 3]⟩ true initW =
      .ok ⟨.memory sampleElem1Mp, translateTy u32Ty emptyLayoutTable⟩ st1 ∧
      annealEvalOperandWideSlice wideSliceSingleIndexWriteBody.localDecls wideSliceSingleIndexWriteBody.layouts
        (translateOperand (.constant { ty := u32Ty, val := .scalar (.int ⟨99, 4⟩) }))
        (some (translateTy u32Ty emptyLayoutTable)) st1 =
      .ok ⟨.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 99))),
           translateTy u32Ty emptyLayoutTable⟩ st2 ∧
      st2.machine = sampleArrU32Machine ∧
      st2.stack.currentFrame?.isSome = true ∧
      st2.stack.frames.size = 1 ∧
      (st2.stack.currentFrame?.map (·.location)) =
        some (.mir { block := 0, statementIndex := 0 }) :=
  ⟨_, _,
    estate_eq_ok_of_val (by with_unfolding_all rfl),
    estate_eq_ok_of_val (by with_unfolding_all rfl),
    (by with_unfolding_all rfl),
    (by with_unfolding_all rfl),
    (by with_unfolding_all rfl),
    (by with_unfolding_all rfl)⟩

set_option maxRecDepth 20000 in
/-- Concrete Witness 5b: Real-step (`stepMirFn` and `Miri.Interpreter.Step.step`)
lockstep execution for in-bounds slice indexing write `(*_2)[_3] = const 99_u32`
over a wide `*mut [u32]` pointer of length `3` into `[10_u32, 20_u32, 30_u32, 40_u32]`:
`(*_2)[1] = const 99_u32` updates element `1` in both Anneal (`get? sWrite.frame.locals 1`)
and vendored `Miri` (`Step.step = (mWrite, .ok true)`). -/
theorem w_wideSlice_index_write_returns :
    let bWrite := wideSliceSingleIndexWriteBody
    let hWrite := annealStepHooksWideSlice bWrite.localDecls bWrite.layouts
    ∃ (sWrite : MachineState) (mWrite : AnnealStepState),
      stepMirFn bWrite (wideSlice4LocalInitAnneal sampleAnnealPtr 3 1 sampleAnnealArrMemory) =
        .step sWrite ∧
      Miri.Interpreter.Step.step hWrite ()
        (wideSlice4LocalInitMiri bWrite u32Ty sampleMiriPtr 3 1 sampleArrU32Machine) =
        (mWrite, .ok true) ∧
      get? sWrite.frame.locals 1 =
        some (.init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨99, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨40, 4⟩])) := by
  dsimp only []
  let initW := wideSlice4LocalInitMiri wideSliceSingleIndexWriteBody u32Ty sampleMiriPtr 3 1 sampleArrU32Machine
  obtain ⟨st1, st2, hevPlace, hevOp, hmach2, hcf2, hsz_st2, hloc_st2⟩ := eval_bWrite_pre_writeMemory
  have hrel99 : ScalarRel ⟨99, 4⟩ (Miri.Memory.ScalarInt.ofUInt32 99) :=
    ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, rfl, rfl⟩
  obtain ⟨alloc', hwrite, _, _, _, _, _, _, _⟩ :=
    alloc_writeScalar_at_offset (A := sampleArrU32Alloc) (off := Miri.ABI.Size.ofBytes 4)
      hrel99 (by with_unfolding_all rfl) (by with_unfolding_all rfl)
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all decide)
  have hchk :
      Miri.Memory.checkAndDerefPtr annealPointerArithmetic sampleElem1Mp.ptr 4
        .memoryAccess (annealResolvePtrWrapping sampleArrU32Machine)
        (annealLookupAlloc sampleArrU32Machine) =
      .ok (some ⟨⟨sampleAllocId, Miri.ABI.Size.ofBytes 4, Miri.Memory.BorTag.one⟩,
        ⟨Miri.ABI.Size.ofBytes 16, translateAlignBytes 4, .liveData, .Mut⟩⟩) := by
    with_unfolding_all rfl
  have hval99 :
      annealValidateScalarForTyId (translateTy u32Ty emptyLayoutTable).ty
        (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 99)) = true := by
    with_unfolding_all rfl
  have hsc_sz :
      ((Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) (Miri.Memory.ScalarInt.ofUInt32 99)).size !=
        (translateTy u32Ty emptyLayoutTable).layout.size) = false := by
    with_unfolding_all rfl
  have hwrite' :
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 4) (translateTy u32Ty emptyLayoutTable).layout.size)
        (Miri.Memory.Scalar.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 99)) sampleArrU32Alloc =
        .ok () alloc' := hwrite
  let nextMem : AnnealMemory :=
    { sampleArrU32Machine.memory with live := #[(sampleAllocId, ⟨.stack, alloc'⟩)] }
  have hset : sampleArrU32Machine.memory.setLiveAllocation sampleAllocId alloc' = .ok nextMem := by
    with_unfolding_all rfl
  have hwMem :
      annealWriteMemoryPlace (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 99)))
        sampleElem1Mp (translateTy u32Ty emptyLayoutTable) st2 =
      .ok () { st2 with machine := { st2.machine with memory := nextMem } } := by
    unfold annealWriteMemoryPlace
    have hsz4 : Miri.Memory.sizeAsI64 (translateTy u32Ty emptyLayoutTable).layout.size = .ok 4 := rfl
    dsimp only []
    rw [hsz4]
    dsimp only []
    rw [hmach2, hchk]
    dsimp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, sampleElem1Mp]
    have hfind : sampleArrU32Machine.memory.live.find? (fun entry => entry.1 == sampleAllocId) =
        some (sampleAllocId, ⟨.stack, sampleArrU32Alloc⟩) := rfl
    rw [hfind, hsc_sz]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hval99]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hwrite', hset]
    rfl
  have hassign :
      (annealStepHooksWideSlice wideSliceSingleIndexWriteBody.localDecls wideSliceSingleIndexWriteBody.layouts).assign ()
        (translatePlace ⟨2, [.deref, .index 3]⟩)
        (translateRvalue (.use (.constant { ty := u32Ty, val := .scalar (.int ⟨99, 4⟩) }))) initW =
      ({ st2 with machine := { st2.machine with memory := nextMem } }, .ok ()) := by
    have htp : translatePlace ⟨2, [.deref, .index 3]⟩ = ⟨2, #[.Deref, .Index 3]⟩ := rfl
    have hisWide :
        isWideSliceAssign wideSliceSingleIndexWriteBody.localDecls
          ⟨2, #[.Deref, .Index 3]⟩
          (translateRvalue (.use (.constant { ty := u32Ty, val := .scalar (.int ⟨99, 4⟩) }))) =
        true := rfl
    rw [htp]
    unfold annealStepHooksWideSlice
    dsimp only []
    rw [hisWide]
    simp only [↓reduceIte, refineWideSliceRvalue, translateRvalue,
      Miri.Interpreter.runRvalue, Miri.Interpreter.evalRvalueIntoPlace,
      annealRvalueHooksWideSlice]
    rw [EStateM.bind_eq_ok hevPlace]
    dsimp only [annealRvalueHooks]
    rw [EStateM.bind_eq_ok hevOp]
    dsimp only [annealReadImmediate, annealWriteImmediate,
      Pure.pure, EStateM.pure, Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
    cases hcf_eq : st2.stack.currentFrame? with
    | none => rw [hcf_eq] at hcf2; cases hcf2
    | some tf =>
        dsimp only []
        rw [hwMem]
        rfl
  have ⟨tf', hframes', _⟩ :
      ∃ tf', st2.stack.frames = #[tf'] ∧ st2.stack.frames[0]? = some tf' := by
    rcases h : st2.stack.frames with ⟨l⟩
    rw [h] at hsz_st2
    cases l with
    | nil => cases hsz_st2
    | cons x xs =>
        cases xs with
        | nil => exact ⟨x, rfl, rfl⟩
        | cons _ _ => cases hsz_st2
  have hcf_tf' : st2.stack.currentFrame? = some tf' :=
    stack_currentFrame?_singleton st2.stack tf' hframes'
  rw [hcf_tf'] at hloc_st2
  injection hloc_st2 with hloc_tf'
  exact ⟨_, _, rfl,
    miri_step_at_statement_ok
      (annealStepHooksWideSlice wideSliceSingleIndexWriteBody.localDecls wideSliceSingleIndexWriteBody.layouts)
      (body := wideSliceSingleIndexWriteBody)
      rfl rfl rfl rfl rfl hassign hframes' hloc_tf',
    rfl⟩

/-- Combined Witness 5 (`w_wideSlice_len_index_read_write_returns`). -/
theorem w_wideSlice_len_index_read_write_returns :
    let bLen := wideSliceSingleLenBody
    let bRead := wideSliceSingleIndexReadBody
    let bWrite := wideSliceSingleIndexWriteBody
    let hLen := annealStepHooksWideSlice bLen.localDecls bLen.layouts
    let hRead := annealStepHooksWideSlice bRead.localDecls bRead.layouts
    let hWrite := annealStepHooksWideSlice bWrite.localDecls bWrite.layouts
    ∃ (sLen sRead sWrite : MachineState) (mLen mRead mWrite : AnnealStepState),
      stepMirFn bLen (wideSlice4LocalInitAnneal sampleAnnealPtr 3 1 sampleAnnealArrMemory) =
        .step sLen ∧
      Miri.Interpreter.Step.step hLen ()
        (wideSlice4LocalInitMiri bLen usizeTy sampleMiriPtr 3 1 sampleArrU32Machine) =
        (mLen, .ok true) ∧
      get? sLen.frame.locals 0 = some (.init (.scalar ⟨3, 8⟩)) ∧
      miriTopLocal? mLen 0 = miriUsizeLocal 3 ∧
      stepMirFn bRead (wideSlice4LocalInitAnneal sampleAnnealPtr 3 1 sampleAnnealArrMemory) =
        .step sRead ∧
      Miri.Interpreter.Step.step hRead ()
        (wideSlice4LocalInitMiri bRead u32Ty sampleMiriPtr 3 1 sampleArrU32Machine) =
        (mRead, .ok true) ∧
      get? sRead.frame.locals 0 = some (.init (.scalar ⟨20, 4⟩)) ∧
      miriTopLocal? mRead 0 = miriU32Local 20 ∧
      stepMirFn bWrite (wideSlice4LocalInitAnneal sampleAnnealPtr 3 1 sampleAnnealArrMemory) =
        .step sWrite ∧
      Miri.Interpreter.Step.step hWrite ()
        (wideSlice4LocalInitMiri bWrite u32Ty sampleMiriPtr 3 1 sampleArrU32Machine) =
        (mWrite, .ok true) ∧
      get? sWrite.frame.locals 1 =
        some (.init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨99, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨40, 4⟩])) := by
  obtain ⟨sLen, sRead, mLen, mRead, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    w_wideSlice_len_and_index_read_returns
  obtain ⟨sWrite, mWrite, h9, h10, h11⟩ :=
    w_wideSlice_index_write_returns
  exact ⟨sLen, sRead, sWrite, mLen, mRead, mWrite, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- Concrete Witness 6: Real-step (`stepMirFn` and `Miri.Interpreter.Step.step`)
lockstep UB and metadata-without-deref witnesses for wide-slice indexing and
dereferencing:
1. **Slice-length OOB index (`idx = 3` on `len = 3`, even though the backing
   `[u32; 4]` allocation has 4 elements / 16 bytes)**:
   * Reading `_0 = copy (*_2)[3]` faults with `.fail .ub` in `stepMirFn` and
     `.error (.undefinedBehavior "place index 3 out of bounds for 3")` in
     `Miri.Interpreter.Step.step`.
   * Writing `(*_2)[3] = 99_u32` faults with `.fail .ub` in `stepMirFn` and
     `.error (.undefinedBehavior "place index 3 out of bounds for 3")` in
     `Miri.Interpreter.Step.step`.
2. **Dangling / dead-allocation wide pointer (`AnnealMachine.empty` /
   `emptyMemory`, `len = 3`)**:
   * `UnOp.ptrMetadata(copy _2)` succeeds without dereferencing and writes `3`
     in both `stepMirFn` and `Miri.Interpreter.Step.step`,
   * whereas dereferencing `(*_2)[0]` (`0 < 3`) faults with `.fail .ub` in
     `stepMirFn` and `.error (.undefinedBehavior "out-of-bounds projection offset")`
     in `Miri.Interpreter.Step.step`.
3. **Past-end offset (`offsetBytes = 16` on the live 16-byte `[u32; 4]`
   allocation, `len = 3`, `idx = 0`)**:
   * Dereferencing `(*_2)[0]` faults with `.fail .ub` in `stepMirFn` and
     `.error (.undefinedBehavior "pointer dereference check failed")` in
     `Miri.Interpreter.Step.step`. -/
theorem w_wideSlice_index_oob_and_dangling_deref_ub_agrees :
    let bRead := wideSliceSingleIndexReadBody
    let bWrite := wideSliceSingleIndexWriteBody
    let bMeta := wideSliceSingleMetadataBody
    let hRead := annealStepHooksWideSlice bRead.localDecls bRead.layouts
    let hWrite := annealStepHooksWideSlice bWrite.localDecls bWrite.layouts
    let hMeta := annealStepHooksWideSlice bMeta.localDecls bMeta.layouts
    let pastEndAnnealPtr : ProvenancePtr := { allocId := 1, offsetBytes := 16 }
    let pastEndMiriPtr : Miri.Memory.Pointer AnnealProv :=
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr sampleAllocId + 16),
       .concrete sampleAllocId Miri.Memory.BorTag.one⟩
    ∃ (sMeta : MachineState) (mOobR mOobW mMeta mDead mPastEnd : AnnealStepState),
      -- (1a) Slice-length OOB read (`idx = 3` on `len = 3`)
      stepMirFn bRead (wideSlice4LocalInitAnneal sampleAnnealPtr 3 3 sampleAnnealArrMemory) =
        .fail .ub ∧
      Miri.Interpreter.Step.step hRead ()
        (wideSlice4LocalInitMiri bRead u32Ty sampleMiriPtr 3 3 sampleArrU32Machine) =
        (mOobR, .error (.undefinedBehavior "place index 3 out of bounds for 3")) ∧
      -- (1b) Slice-length OOB write (`idx = 3` on `len = 3`)
      stepMirFn bWrite (wideSlice4LocalInitAnneal sampleAnnealPtr 3 3 sampleAnnealArrMemory) =
        .fail .ub ∧
      Miri.Interpreter.Step.step hWrite ()
        (wideSlice4LocalInitMiri bWrite u32Ty sampleMiriPtr 3 3 sampleArrU32Machine) =
        (mOobW, .error (.undefinedBehavior "place index 3 out of bounds for 3")) ∧
      -- (2a) Dangling / dead-allocation `PtrMetadata` succeeds (`3`) without deref
      stepMirFn bMeta (wideSlice4LocalInitAnneal sampleAnnealPtr 3 0 emptyMemory) =
        .step sMeta ∧
      Miri.Interpreter.Step.step hMeta ()
        (wideSlice4LocalInitMiri bMeta usizeTy sampleMiriPtr 3 0 AnnealMachine.empty) =
        (mMeta, .ok true) ∧
      get? sMeta.frame.locals 0 = some (.init (.scalar ⟨3, 8⟩)) ∧
      miriTopLocal? mMeta 0 = miriUsizeLocal 3 ∧
      -- (2b) Dangling / dead-allocation `(*_2)[0]` (`0 < 3`) faults `.ub` in both
      stepMirFn bRead (wideSlice4LocalInitAnneal sampleAnnealPtr 3 0 emptyMemory) =
        .fail .ub ∧
      Miri.Interpreter.Step.step hRead ()
        (wideSlice4LocalInitMiri bRead u32Ty sampleMiriPtr 3 0 AnnealMachine.empty) =
        (mDead, .error (.undefinedBehavior "pointer dereference check failed")) ∧
      -- (3) Past-end offset (`offsetBytes = 16` on 16-byte allocation, `idx = 0 < 3`) faults `.ub` in both
      stepMirFn bRead (wideSlice4LocalInitAnneal pastEndAnnealPtr 3 0 sampleAnnealArrMemory) =
        .fail .ub ∧
      Miri.Interpreter.Step.step hRead ()
        (wideSlice4LocalInitMiri bRead u32Ty pastEndMiriPtr 3 0 sampleArrU32Machine) =
        (mPastEnd, .error (.undefinedBehavior "pointer dereference check failed")) :=
  ⟨_, _, _, _, _, _,
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), rfl, (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl)⟩

/-- Shared slice reference type `&[u32]`. -/
def sharedRefSliceU32Ty : Ty :=
  { kind := .ref .not (.slice (.uint .u32)), layoutIdx := 0 }

/-- Single-statement reborrow body `_0 = rv` over the 4-local wide-slice frame (`_1 : [u32; 4]`,
`_2 : *mut [u32]`, `_3 : usize`) with destination `_0 : dstTy`. Only the reborrow statement is
stepped (the `Return` is never executed), so the `usize` ABI is irrelevant. -/
def wideSliceReborrowBody (dstTy : Ty) (rv : Rvalue) : CapturedMir :=
  { defPath := "wide_slice_reborrow"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls :=
      [ { mutability := .mut, ty := dstTy, debugName := none }
      , { mutability := .mut, ty := arrU32_4Ty, debugName := none }
      , { mutability := .mut, ty := rawMutSliceU32Ty, debugName := none }
      , { mutability := .not, ty := usizeTy, debugName := none } ]
    basicBlocks :=
      [ { statements := [ ⟨.assign ⟨0, []⟩ rv, "s0"⟩ ]
          terminator := ⟨.return_, "t0"⟩
          isCleanup := false } ]
    fnAbi := fnAbiUsize
    layouts := emptyLayoutTable
    allocations := [] }

/-- Concrete Witness 7 (`slice::from_raw_parts` reborrows of `*_2`, `_2 : *mut [u32]`,
`len = 3`, borrow-backed by `[10, 20, 30, 40]`), real-step on BOTH interpreters with values pinned:
1. `_0 = &raw const (*_2)` (`ptr::slice_from_raw_parts` / `addr_of!(*p)`): Anneal and vendored
   `Miri` both return the ORIGINAL wide pointer (same allocation, offset, tag, and length `3`),
   with no new Anneal borrow, and the results stay related by `WideSliceImmediateRel`.
2. `_0 = &(*_2)` (`slice::from_raw_parts(data, len)` = `&*ptr::slice_from_raw_parts(data, len)`):
   both return a wide reference to the same data with metadata `3`, but the provenance discipline
   DIVERGES (`DIV-LM-SHARED-REBORROW-FRESH-TAG`): Anneal's Stacked-Borrows-style tracker mints a
   fresh borrow (tag / alloc id `2`, `borrows.length = 2`, `nextTag = 3`), whereas vendored `Miri`
   keeps the parent tag (`BorTag.one`) because retagging is a separate `Retag` statement there.
   A state relation across such a reborrow must therefore extend `allocMap` with an entry for the
   fresh Anneal tag that maps to the parent `Miri` provenance. -/
theorem w_wideSlice_reborrow_raw_and_shared_agrees :
    let bRaw := wideSliceReborrowBody rawSliceU32Ty (.rawPtr .not ⟨2, [.deref]⟩)
    let bRef := wideSliceReborrowBody sharedRefSliceU32Ty (.ref .shared ⟨2, [.deref]⟩)
    let wideVal : Value := .aggregate 0 [.ptr sampleAnnealPtr 8, .scalar ⟨3, 8⟩]
    let wideImm : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair sampleMiriPtrSc (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 3))
    ∃ (sRaw sRef : MachineState) (mRaw mRef : AnnealStepState),
      stepMirFn bRaw (wideSlice4LocalInitAnneal sampleAnnealPtr 3 1 sampleAnnealArrMemory) =
        .step sRaw ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bRaw.localDecls bRaw.layouts) ()
        (wideSlice4LocalInitMiri bRaw rawSliceU32Ty sampleMiriPtr 3 1 sampleArrU32Machine) =
        (mRaw, .ok true) ∧
      get? sRaw.frame.locals 0 = some (.init wideVal) ∧
      sRaw.memory.borrows.length = 1 ∧
      miriTopLocal? mRaw 0 = some (.live (.immediate wideImm)) ∧
      stepMirFn bRef (wideSlice4LocalInitAnneal sampleAnnealPtr 3 1 sampleAnnealArrMemory) =
        .step sRef ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bRef.localDecls bRef.layouts) ()
        (wideSlice4LocalInitMiri bRef sharedRefSliceU32Ty sampleMiriPtr 3 1 sampleArrU32Machine) =
        (mRef, .ok true) ∧
      get? sRef.frame.locals 0 =
        some (.init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0 } 8, .scalar ⟨3, 8⟩])) ∧
      sRef.memory.borrows.length = 2 ∧
      sRef.memory.nextTag = 3 ∧
      miriTopLocal? mRef 0 = some (.live (.immediate wideImm)) ∧
      WideSliceImmediateRel [sampleAllocMapEntry] wideVal wideImm :=
  ⟨_, _, _, _,
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), rfl, rfl, (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), rfl, rfl, rfl,
    (by with_unfolding_all rfl),
    .provenance
      (PtrRel.of_stackAllocPlace (.head _) (by decide))
      ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
      rfl⟩

/-- Mutable slice reference type `&mut [u32]`. -/
def mutRefSliceU32Ty : Ty :=
  { kind := .ref .mut (.slice (.uint .u32)), layoutIdx := 0 }

/-- Concrete Witness 7b (`&raw mut (*_2)` vs. `slice::from_raw_parts_mut` `&mut (*_2)`):
1. `_0 = &raw mut (*_2)` (`len = 3` in-bounds AND `len = 5` OOB on 16-byte `[u32; 4]`):
   BOTH `stepMirFn` and `Miri.Interpreter.Step.step` succeed without dereferencing memory
   and return the raw wide pointer (`borrows.length = 1`).
2. `_0 = &mut (*_2)` (`slice::from_raw_parts_mut`, `len = 3` in-bounds on `[u32; 4]`):
   BOTH succeed with metadata `3` (Anneal mints fresh `.active` tag `2`, vendored `Miri`
   retains `BorTag.one`). -/
theorem w_wideSlice_reborrow_rawMut_and_sharedMut_agrees :
    let bRawMut := wideSliceReborrowBody rawMutSliceU32Ty (.rawPtr .mut ⟨2, [.deref]⟩)
    let bRefMut := wideSliceReborrowBody mutRefSliceU32Ty (.ref (.mut false) ⟨2, [.deref]⟩)
    let wideVal3 : Value := .aggregate 0 [.ptr sampleAnnealPtr 8, .scalar ⟨3, 8⟩]
    let wideImm3 : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair sampleMiriPtrSc (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 3))
    let wideVal5 : Value := .aggregate 0 [.ptr sampleAnnealPtr 8, .scalar ⟨5, 8⟩]
    let wideImm5 : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair sampleMiriPtrSc (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 5))
    ∃ (sRaw3 sRaw5 sMut3 : MachineState) (mRaw3 mRaw5 mMut3 : AnnealStepState),
      stepMirFn bRawMut (wideSlice4LocalInitAnneal sampleAnnealPtr 3 0 sampleAnnealArrMemory) =
        .step sRaw3 ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bRawMut.localDecls bRawMut.layouts) ()
        (wideSlice4LocalInitMiri bRawMut rawMutSliceU32Ty sampleMiriPtr 3 0 sampleArrU32Machine) =
        (mRaw3, .ok true) ∧
      get? sRaw3.frame.locals 0 = some (.init wideVal3) ∧
      miriTopLocal? mRaw3 0 = some (.live (.immediate wideImm3)) ∧
      stepMirFn bRawMut (wideSlice4LocalInitAnneal sampleAnnealPtr 5 0 sampleAnnealArrMemory) =
        .step sRaw5 ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bRawMut.localDecls bRawMut.layouts) ()
        (wideSlice4LocalInitMiri bRawMut rawMutSliceU32Ty sampleMiriPtr 5 0 sampleArrU32Machine) =
        (mRaw5, .ok true) ∧
      get? sRaw5.frame.locals 0 = some (.init wideVal5) ∧
      miriTopLocal? mRaw5 0 = some (.live (.immediate wideImm5)) ∧
      stepMirFn bRefMut (wideSlice4LocalInitAnneal sampleAnnealPtr 3 0 sampleAnnealArrMemory) =
        .step sMut3 ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bRefMut.localDecls bRefMut.layouts) ()
        (wideSlice4LocalInitMiri bRefMut mutRefSliceU32Ty sampleMiriPtr 3 0 sampleArrU32Machine) =
        (mMut3, .ok true) ∧
      get? sMut3.frame.locals 0 =
        some (.init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0 } 8, .scalar ⟨3, 8⟩])) ∧
      miriTopLocal? mMut3 0 = some (.live (.immediate wideImm3)) :=
  ⟨_, _, _, _, _, _,
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), rfl, (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), rfl, (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), rfl, (by with_unfolding_all rfl)⟩

set_option maxHeartbeats 400000 in
/-- Concrete Witness 7c (**Safe-reference validity UB lockstep** on `slice::from_raw_parts(_mut)`
via `Place.writePlaceImmediate` + `Validity.checkSafePointer` / `annealValidateSafeWideSliceRef`):
1. OOB `slice::from_raw_parts(_mut)` (`len = 5` = 20 bytes on 16-byte `[u32; 4]`):
   BOTH `stepMirFn` and `Miri.Interpreter.Step.step` fault `.ub`
   (`"pointer dereference check failed"`), on both `&(*_2)` and `&mut (*_2)`.
2. Dangling `slice::from_raw_parts` (`emptyMemory` / `AnnealMachine.empty`, `len = 3`):
   BOTH fault `.ub` (`"pointer dereference check failed"`).
3. Misaligned `slice::from_raw_parts` (`offsetBytes = 2` on `[u32; 4]`, `len = 1`):
   BOTH fault `.ub` (`"misaligned pointer dereference"`).
4. `SliceTooBig` `slice::from_raw_parts` (`len = 2^61` on `[u32; 4]`):
   BOTH fault `.ub` (`"InvalidMeta(SliceTooBig)"`). -/
theorem w_wideSlice_safe_reborrow_validity_ub_agrees :
    let bRefSh := wideSliceReborrowBody sharedRefSliceU32Ty (.ref .shared ⟨2, [.deref]⟩)
    let bRefMut := wideSliceReborrowBody mutRefSliceU32Ty (.ref (.mut false) ⟨2, [.deref]⟩)
    let misAnnealPtr : ProvenancePtr := { allocId := 1, offsetBytes := 2 }
    let misMiriPtr : Miri.Memory.Pointer AnnealProv :=
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr sampleAllocId + 2),
       .concrete sampleAllocId Miri.Memory.BorTag.one⟩
    let ovfLen : Nat := 0x2000_0000_0000_0000
    ∃ (mOobSh mOobMut mDead mMis mOvf : AnnealStepState),
      stepMirFn bRefSh (wideSlice4LocalInitAnneal sampleAnnealPtr 5 0 sampleAnnealArrMemory) =
        .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bRefSh.localDecls bRefSh.layouts) ()
        (wideSlice4LocalInitMiri bRefSh sharedRefSliceU32Ty sampleMiriPtr 5 0 sampleArrU32Machine) =
        (mOobSh, .error (.undefinedBehavior "pointer dereference check failed")) ∧
      stepMirFn bRefMut (wideSlice4LocalInitAnneal sampleAnnealPtr 5 0 sampleAnnealArrMemory) =
        .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bRefMut.localDecls bRefMut.layouts) ()
        (wideSlice4LocalInitMiri bRefMut mutRefSliceU32Ty sampleMiriPtr 5 0 sampleArrU32Machine) =
        (mOobMut, .error (.undefinedBehavior "pointer dereference check failed")) ∧
      stepMirFn bRefSh (wideSlice4LocalInitAnneal sampleAnnealPtr 3 0 emptyMemory) =
        .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bRefSh.localDecls bRefSh.layouts) ()
        (wideSlice4LocalInitMiri bRefSh sharedRefSliceU32Ty sampleMiriPtr 3 0 AnnealMachine.empty) =
        (mDead, .error (.undefinedBehavior "pointer dereference check failed")) ∧
      stepMirFn bRefSh (wideSlice4LocalInitAnneal misAnnealPtr 1 0 sampleAnnealArrMemory) =
        .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bRefSh.localDecls bRefSh.layouts) ()
        (wideSlice4LocalInitMiri bRefSh sharedRefSliceU32Ty misMiriPtr 1 0 sampleArrU32Machine) =
        (mMis, .error (.undefinedBehavior "misaligned pointer dereference")) ∧
      stepMirFn bRefSh (wideSlice4LocalInitAnneal sampleAnnealPtr ovfLen 0 sampleAnnealArrMemory) =
        .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bRefSh.localDecls bRefSh.layouts) ()
        (wideSlice4LocalInitMiri bRefSh sharedRefSliceU32Ty sampleMiriPtr 0x2000_0000_0000_0000 0 sampleArrU32Machine) =
        (mOvf, .error (.undefinedBehavior "InvalidMeta(SliceTooBig)")) :=
  ⟨_, _, _, _, _,
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl)⟩

/-- Concrete Witness 8 (`DIV-LM-PLACE-LEN-BORROW-BOUNDS` &
`DIV-LM-RAW-SLICE-PARTIAL-OOB-LEN-INDEX`):
Characterizes the exact lockstep vs. conservative-strictness boundary on raw
wide-slice `Rvalue.len (*_2)` and `(*_2)[i]`:
1. **Untracked / dangling `Rvalue.len (*_2)` lockstep (`emptyMemory` / `AnnealMachine.empty`,
   `allocId = 1 ≠ 0`, `len = 3`)**: BOTH `stepMirFn` (`evalPlaceLen` `lookupBorrow = none`,
   `lookupGlobalAlloc = none`, `allocId ≠ 0`) and `Miri.Interpreter.Step.step`
   (`PlaceDynamic.length` / `ScalarOps.unary .PtrMetadata`) succeed and return `3`.
2. **`DIV-LM-PLACE-LEN-BORROW-BOUNDS`** (borrow-backed OOB `Rvalue.len (*_2)` with
   `len = 5` on live `[u32; 4]`): Anneal's `evalPlaceLen` (`Places.lean:14778`) checks
   `elemOffset + len ≤ elems.length` (`5 ≤ 4 = false`) and faults `.fail .ub`, whereas
   vendored `Miri` (`MirPass::LowerSliceLen`) extracts metadata without dereferencing
   and returns `5`.
3. **`DIV-LM-RAW-SLICE-PARTIAL-OOB-LEN-INDEX`** (`_0 = copy (*_2)[1]` when `_2 : *mut [u32]`
   has metadata `len = 5` over live 16-byte `[10, 20, 30, 40]`): Anneal's
   `evalSliceFatPtrDerefRead` (`Places.lean:9895`) eagerly checks `5 ≤ 4 = false` before
   indexing and faults `.fail .ub`, whereas vendored `Miri` (`PlaceDynamic.index`) checks
   `1 < 5`, computes in-bounds byte offset `4 ≤ 16`, and reads `[4..8]` = `20_u32`. -/
theorem div_rawSlice_placeLen_and_partialOobLenIndex :
    let bLen := wideSliceSingleLenBody
    let bRead := wideSliceSingleIndexReadBody
    let hLen := annealStepHooksWideSlice bLen.localDecls bLen.layouts
    let hRead := annealStepHooksWideSlice bRead.localDecls bRead.layouts
    ∃ (sLenDead : MachineState) (mLenDead mLenOob mIdxPartial : AnnealStepState),
      -- (1) Untracked / dangling `Rvalue.len (*_2)` (`len = 3`): BOTH return `3`
      stepMirFn bLen (wideSlice4LocalInitAnneal sampleAnnealPtr 3 0 emptyMemory) =
        .step sLenDead ∧
      get? sLenDead.frame.locals 0 = some (.init (.scalar ⟨3, 8⟩)) ∧
      Miri.Interpreter.Step.step hLen ()
        (wideSlice4LocalInitMiri bLen usizeTy sampleMiriPtr 3 0 AnnealMachine.empty) =
        (mLenDead, .ok true) ∧
      miriTopLocal? mLenDead 0 = miriUsizeLocal 3 ∧
      -- (2) Borrow-backed OOB-length `Rvalue.len (*_2)` (`len = 5` on `[u32; 4]`): Anneal `.ub`, Miri `5`
      stepMirFn bLen (wideSlice4LocalInitAnneal sampleAnnealPtr 5 0 sampleAnnealArrMemory) =
        .fail .ub ∧
      Miri.Interpreter.Step.step hLen ()
        (wideSlice4LocalInitMiri bLen usizeTy sampleMiriPtr 5 0 sampleArrU32Machine) =
        (mLenOob, .ok true) ∧
      miriTopLocal? mLenOob 0 = miriUsizeLocal 5 ∧
      -- (3) `(*_2)[1]` with `len = 5` on live `[10, 20, 30, 40]`: Anneal `.ub`, Miri `20_u32`
      stepMirFn bRead (wideSlice4LocalInitAnneal sampleAnnealPtr 5 1 sampleAnnealArrMemory) =
        .fail .ub ∧
      Miri.Interpreter.Step.step hRead ()
        (wideSlice4LocalInitMiri bRead u32Ty sampleMiriPtr 5 1 sampleArrU32Machine) =
        (mIdxPartial, .ok true) ∧
      miriTopLocal? mIdxPartial 0 = miriU32Local 20 :=
  ⟨_, _, _, _,
    rfl, rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), (by with_unfolding_all rfl)⟩

/-- Concrete Witness 7d (**zero-sized safe references are not over-validated**): the
`annealValidateSafeWideSliceRef` / `Validity.checkSafePointer` hook added for Witness 7c must reject
only what Rust rejects. A shared reborrow `_0 = &(*_2)` of an EMPTY slice (`len = 0`, total size `0`)
is valid at any non-null, aligned address — `slice::from_raw_parts(NonNull::dangling().as_ptr(), 0)`:
1. at a dangling address (`emptyMemory` / `AnnealMachine.empty`, no live allocation, no borrow), BOTH
   `stepMirFn` and `Miri.Interpreter.Step.step` succeed and return the original pointer with length `0`
   (Anneal mints no borrow for an untracked pointer);
2. into the live `[u32; 4]`, BOTH succeed with length `0`; Anneal mints the fresh borrow (alloc/tag `2`)
   while vendored `Miri` keeps the parent tag (`DIV-LM-SHARED-REBORROW-FRESH-TAG`). -/
theorem w_wideSlice_safe_reborrow_zeroSized_dangling_ok_agrees :
    let bRefSh := wideSliceReborrowBody sharedRefSliceU32Ty (.ref .shared ⟨2, [.deref]⟩)
    let emptyImm : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair sampleMiriPtrSc (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 0))
    ∃ (sDead sLive : MachineState) (mDead mLive : AnnealStepState),
      stepMirFn bRefSh (wideSlice4LocalInitAnneal sampleAnnealPtr 0 1 emptyMemory) = .step sDead ∧
      get? sDead.frame.locals 0 =
        some (.init (.aggregate 0 [.ptr sampleAnnealPtr 8, .scalar ⟨0, 8⟩])) ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bRefSh.localDecls bRefSh.layouts) ()
        (wideSlice4LocalInitMiri bRefSh sharedRefSliceU32Ty sampleMiriPtr 0 1 AnnealMachine.empty) =
        (mDead, .ok true) ∧
      miriTopLocal? mDead 0 = some (.live (.immediate emptyImm)) ∧
      stepMirFn bRefSh (wideSlice4LocalInitAnneal sampleAnnealPtr 0 1 sampleAnnealArrMemory) =
        .step sLive ∧
      get? sLive.frame.locals 0 =
        some (.init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0 } 8, .scalar ⟨0, 8⟩])) ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bRefSh.localDecls bRefSh.layouts) ()
        (wideSlice4LocalInitMiri bRefSh sharedRefSliceU32Ty sampleMiriPtr 0 1 sampleArrU32Machine) =
        (mLive, .ok true) ∧
      miriTopLocal? mLive 0 = some (.live (.immediate emptyImm)) :=
  ⟨_, _, _, _,
    rfl, rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), (by with_unfolding_all rfl),
    rfl, rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), (by with_unfolding_all rfl)⟩

/-- Shared `&str` reference type (`wideRefStrPtrTyId = 3001`). -/
def sharedRefStrTy : Ty :=
  { kind := .ref .not .str, layoutIdx := 0 }

/-- Shared ZST slice `&[()]` reference type (`wideRefSlicePtrTyId 51 = 3251`). -/
def sharedRefSliceUnitTy : Ty :=
  { kind := .ref .not (.slice (.tuple .nil)), layoutIdx := 0 }

/-- Concrete `[u8; 16]` array type (`16` bytes, matching `sampleArrU32Machine`). -/
def arrU8_16Ty : Ty :=
  { kind := .array (.uint .u8) 16, layoutIdx := 0 }

/-- Anneal 16-byte `[u8; 16]` array value matching `sampleArrU32Machine` (`[10, 0, 0, 0, ...]`). -/
def sampleAnnealArrU8_16Val : Value :=
  .aggregate 0
    [ .scalar ⟨10, 1⟩, .scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩
    , .scalar ⟨20, 1⟩, .scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩
    , .scalar ⟨30, 1⟩, .scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩
    , .scalar ⟨40, 1⟩, .scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩ ]

/-- Generalized 4-local single-statement reborrow body `_0 = rv` with `_0 : dstTy`,
`_1 : arrTy`, `_2 : srcTy`, `_3 : usize`. -/
def wideSliceTypedReborrowBody (arrTy srcTy dstTy : Ty) (rv : Rvalue) : CapturedMir :=
  { defPath := "wide_slice_typed_reborrow"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls :=
      [ { mutability := .mut, ty := dstTy, debugName := none }
      , { mutability := .mut, ty := arrTy, debugName := none }
      , { mutability := .mut, ty := srcTy, debugName := none }
      , { mutability := .not, ty := usizeTy, debugName := none } ]
    basicBlocks :=
      [ { statements := [ ⟨.assign ⟨0, []⟩ rv, "s0"⟩ ]
          terminator := ⟨.return_, "t0"⟩
          isCleanup := false } ]
    fnAbi := fnAbiUsize
    layouts := emptyLayoutTable
    allocations := [] }

/-- Initial Anneal state for `wideSliceTypedReborrowBody` (and `wideSliceReborrowBody`). -/
def wideSliceTypedInitAnneal (arrVal wideVal : Value) (idx : Nat) (mem : Memory) : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals :=
          [ .uninit
          , .init arrVal
          , .init wideVal
          , .init (.scalar ⟨idx, 8⟩) ] }
    memory := mem }

/-- Initial Miri state for `wideSliceTypedReborrowBody` (and `wideSliceReborrowBody`). -/
def wideSliceTypedInitMiri (b : CapturedMir) (arrTy srcTy dstTy : Ty)
    (wideImm : Miri.Interpreter.Immediate AnnealProv) (idx : UInt64)
    (mach : AnnealMachine) : AnnealStepState :=
  let arrMp : Miri.Interpreter.MemPlace AnnealProv :=
    ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr sampleAllocId),
      some (.concrete sampleAllocId Miri.Memory.BorTag.one)⟩, .none, none⟩
  let mIdx : Miri.Memory.ScalarInt := Miri.Memory.ScalarInt.ofUInt64 idx
  { stack :=
      { frames :=
          #[ { body := translateBody b
               bodyIdentity := .ofCanonicalIndex 0
               functionInstance := { kind := .Item 0, args := #[] }
               extra := ()
               returnContinuation := .stop false
               returnPlace := .frameLocal 0 0 none (translateTyWideSlice dstTy) (.ofAllocationToken 0)
               localsIdentity := .ofAllocationToken 0
               locals :=
                 #[ ⟨.live (.immediate .uninit), some (translateTyWideSlice dstTy)⟩
                  , ⟨.live (.indirect arrMp), some (translateTyWideSlice arrTy)⟩
                  , ⟨.live (.immediate wideImm), some (translateTyWideSlice srcTy)⟩
                  , ⟨.live (.immediate (.scalar (.fromScalarInt mIdx))), some (translateTyWideSlice usizeTy)⟩ ]
               vaList := #[]
               trackCallerArg := none
               location := .mir { block := 0, statementIndex := 0 } } ] }
    machine := mach }

/-- Concrete Witness 7e (**Two-sided null empty-slice UB & `addr_of!(*safe_ref)` deref-validity UB**):
1. **Null provenance-free empty wide slice (`ptr::slice_from_raw_parts(ptr::null::<u32>(), 0)`)**:
   `nullScVal = .aggregate 0 [.scalar ⟨0, 8⟩, .scalar ⟨0, 8⟩]` and `nullScImm` satisfy
   `WideSliceImmediateRel [] nullScVal nullScImm`, and `_0 = &(*_2)` faults `.fail .ub` in
   `stepMirFn` AND `(mNullSc, .error (.undefinedBehavior "dereferencing a null reference"))` in
   `Miri.Interpreter.Step.step`.
2. **Null `ProvenancePtr` empty wide slice (`{ allocId := 0, offsetBytes := 0 }`, `len = 0`)**:
   BOTH `stepMirFn` (`Places.lean:16260-16262` explicit null guard) and `Miri.Interpreter.Step.step`
   (`mp.ptr.offset.bytes == 0`) fault with UB (`"dereferencing a null reference"`).
3. **`addr_of!(*_2)` (`_0 = &raw const (*_2)`) on an OOB safe wide reference `_2 : &[u32]`
   (`len = 5` on `[u32; 4]`)**: EVEN THOUGH destination `_0 : *const [u32]` is a raw wide pointer,
   `Rvalue.RawPtr` passes `skipValidity = false` (`Rvalue.lean:97`) to
   `annealEvalPlaceWideSliceWithSkip`, so dereferencing `_2` faults `.fail .ub` in `stepMirFn`
   (`Places.lean:18241`, `isRawPtrLocal = false`) AND
   `(mAddrOfSafe, .error (.undefinedBehavior "pointer dereference check failed"))` in
   `Miri.Interpreter.Step.step`! -/
theorem w_wideSlice_null_and_addrOfSafeRef_ub_agrees :
    let bRefSh := wideSliceReborrowBody sharedRefSliceU32Ty (.ref .shared ⟨2, [.deref]⟩)
    let bAddrOfSafe :=
      wideSliceTypedReborrowBody arrU32_4Ty sharedRefSliceU32Ty rawSliceU32Ty
        (.rawPtr .not ⟨2, [.deref]⟩)
    let nullScVal : Value := .aggregate 0 [.scalar ⟨0, 8⟩, .scalar ⟨0, 8⟩]
    let m0 : Miri.Memory.ScalarInt := Miri.Memory.ScalarInt.ofUInt64 0
    let nullScImm : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair (.fromScalarInt m0) (.fromScalarInt m0)
    let nullAnnealPtr : ProvenancePtr := { allocId := 0, offsetBytes := 0 }
    let nullMiriPtr : Miri.Memory.Pointer AnnealProv :=
      ⟨Miri.ABI.Size.ZERO, .concrete sampleAllocId Miri.Memory.BorTag.one⟩
    let oobSafeVal : Value := .aggregate 0 [.ptr sampleAnnealPtr 8, .scalar ⟨5, 8⟩]
    let oobSafeImm : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair sampleMiriPtrSc (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 5))
    WideSliceImmediateRel [] nullScVal nullScImm ∧
    ∃ (mNullSc mNullProv mAddrOfSafe : AnnealStepState),
      stepMirFn bRefSh
        (wideSliceTypedInitAnneal sampleAnnealArrVal nullScVal 0 emptyMemory) = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bRefSh.localDecls bRefSh.layouts) ()
        (wideSliceTypedInitMiri bRefSh arrU32_4Ty rawMutSliceU32Ty sharedRefSliceU32Ty
          nullScImm 0 AnnealMachine.empty) =
        (mNullSc, .error (.undefinedBehavior "dereferencing a null reference")) ∧
      stepMirFn bRefSh (wideSlice4LocalInitAnneal nullAnnealPtr 0 0 emptyMemory) = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bRefSh.localDecls bRefSh.layouts) ()
        (wideSlice4LocalInitMiri bRefSh sharedRefSliceU32Ty nullMiriPtr 0 0 AnnealMachine.empty) =
        (mNullProv, .error (.undefinedBehavior "dereferencing a null reference")) ∧
      stepMirFn bAddrOfSafe
        (wideSliceTypedInitAnneal sampleAnnealArrVal oobSafeVal 0 sampleAnnealArrMemory) = .fail .ub ∧
      Miri.Interpreter.Step.step
        (annealStepHooksWideSlice bAddrOfSafe.localDecls bAddrOfSafe.layouts) ()
        (wideSliceTypedInitMiri bAddrOfSafe arrU32_4Ty sharedRefSliceU32Ty rawSliceU32Ty
          oobSafeImm 0 sampleArrU32Machine) =
        (mAddrOfSafe, .error (.undefinedBehavior "pointer dereference check failed")) :=
  ⟨.scalarAddr
      ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
      ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
      rfl rfl,
   _, _, _,
   rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl),
   rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl),
   rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl)⟩

/-- Concrete Witness 8b (`DIV-LM-ZERO-BYTE-DANGLING-REBORROW`):
Right next to Witness 7d (`w_wideSlice_safe_reborrow_zeroSized_dangling_ok_agrees`), characterizes
the **three** valid Rust zero-byte dangling safe wide-reference reborrows (`totalSize = 0`, non-null,
aligned, over `emptyMemory` / `AnnealMachine.empty`) where vendored `Miri.Interpreter.Step.step`
succeeds while Stage-1 Anneal (`evalRvalueRefDeref` / `evalSliceFatPtrDerefBorrow` at
`Places.lean:16256, 16258, 17792`) conservatively faults `.fail .ub`:
1. **Mutable empty dangling slice** (`slice::from_raw_parts_mut(dangling, 0)`: `_0 = &mut (*_2)`
   with `len = 0` at `sampleAnnealPtr` / `sampleMiriPtr`): Anneal rejects (`Bool.not isMut = false`),
   whereas vendored `Miri` succeeds (`len = 0`).
2. **Non-empty ZST dangling slice** (`slice::from_raw_parts::<()>(dangling, 10)`: `_0 = &(*_2)`
   with `_2 : *const [()]`, `_0 : &[()]`, `len = 10`, `totalSize = 0`): Anneal rejects
   (`Nat.beq lenSc.bits 0 = false`, checking element count instead of byte size), whereas vendored
   `Miri` succeeds (`len = 10`).
3. **Provenance-free `NonNull::<u32>::dangling()` shared empty slice**
   (`slice::from_raw_parts(without_provenance(4), 0)` = `.aggregate 0 [.scalar ⟨4, 8⟩, .scalar ⟨0, 8⟩]`):
   `WideSliceImmediateRel [] scVal4 scImm4` holds; Stage-1 Anneal rejects (`Places.lean:17792`
   `| _ => .ub`), whereas vendored `Miri` succeeds (`len = 0`). -/
theorem div_zeroByte_dangling_reborrow_mut_zst_scalarAddr :
    let bRefSh := wideSliceReborrowBody sharedRefSliceU32Ty (.ref .shared ⟨2, [.deref]⟩)
    let bRefMut := wideSliceReborrowBody mutRefSliceU32Ty (.ref (.mut false) ⟨2, [.deref]⟩)
    let bZst :=
      wideSliceTypedReborrowBody arrU32_4Ty rawSliceUnitTy sharedRefSliceUnitTy
        (.ref .shared ⟨2, [.deref]⟩)
    let emptyImm : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair sampleMiriPtrSc (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 0))
    let zst10Val : Value := .aggregate 0 [.ptr sampleAnnealPtr 8, .scalar ⟨10, 8⟩]
    let zst10Imm : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair sampleMiriPtrSc (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 10))
    let scVal4 : Value := .aggregate 0 [.scalar ⟨4, 8⟩, .scalar ⟨0, 8⟩]
    let scImm4 : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair
        (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 4))
        (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 0))
    WideSliceImmediateRel [] scVal4 scImm4 ∧
    ∃ (mMut0 mZst10 mSc4 : AnnealStepState),
      -- (1) Mutable empty dangling slice (`&mut (*_2)`, `len = 0`): Anneal `.ub`, Miri `.ok`
      stepMirFn bRefMut (wideSlice4LocalInitAnneal sampleAnnealPtr 0 0 emptyMemory) = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bRefMut.localDecls bRefMut.layouts) ()
        (wideSlice4LocalInitMiri bRefMut mutRefSliceU32Ty sampleMiriPtr 0 0 AnnealMachine.empty) =
        (mMut0, .ok true) ∧
      miriTopLocal? mMut0 0 = some (.live (.immediate emptyImm)) ∧
      -- (2) Non-empty ZST dangling slice (`&(*_2)` on `*const [()]`, `len = 10`): Anneal `.ub`, Miri `.ok`
      stepMirFn bZst
        (wideSliceTypedInitAnneal sampleAnnealArrVal zst10Val 0 emptyMemory) = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bZst.localDecls bZst.layouts) ()
        (wideSliceTypedInitMiri bZst arrU32_4Ty rawSliceUnitTy sharedRefSliceUnitTy
          zst10Imm 0 AnnealMachine.empty) =
        (mZst10, .ok true) ∧
      miriTopLocal? mZst10 0 = some (.live (.immediate zst10Imm)) ∧
      -- (3) Provenance-free `without_provenance(4)` empty slice (`len = 0`): Anneal `.ub`, Miri `.ok`
      stepMirFn bRefSh
        (wideSliceTypedInitAnneal sampleAnnealArrVal scVal4 0 emptyMemory) = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bRefSh.localDecls bRefSh.layouts) ()
        (wideSliceTypedInitMiri bRefSh arrU32_4Ty rawMutSliceU32Ty sharedRefSliceU32Ty
          scImm4 0 AnnealMachine.empty) =
        (mSc4, .ok true) ∧
      miriTopLocal? mSc4 0 = some (.live (.immediate scImm4)) :=
  ⟨.scalarAddr
      ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
      ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
      rfl rfl,
   _, _, _,
   rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), (by with_unfolding_all rfl),
   rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), (by with_unfolding_all rfl),
   rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), (by with_unfolding_all rfl)⟩

set_option maxHeartbeats 400000 in
/-- Concrete Witness 9 (**Real-step `Subslice` (`&(*_2)[from..to]`) & `&str` safe reborrow lockstep**):
Exercises `PlaceDynamic.subslice` (`ProjectionElem.subslice fromIdx toIdx true`) and `&str`
(`wideRefStrPtrTyId = 3001`) across BOTH `stepMirFn` and `Miri.Interpreter.Step.step`:
1. **In-bounds `fromEnd = true` subslice reborrow `_0 = &(*_2)[1..1]`** on `len = 3` into live
   `[10, 20, 30, 40]`: BOTH succeed with subslice length `3 - 1 - 1 = 1` (at byte offset `+ 4` in
   vendored `Miri`, fresh frozen borrow tag `2` in Anneal).
2. **OOB `fromEnd = true` subslice reborrow `_0 = &(*_2)[2..2]`** (`2 + 2 = 4 > 3`): BOTH fault
   with UB (`.fail .ub` in `stepMirFn` and `.error (.undefinedBehavior "subslice bounds")` in
   `Miri.Interpreter.Step.step`).
3. **`&str` safe reborrow (`_2 : *const str` → `_0 : &str`) over 16-byte `[u8; 16]`**:
   `len = 4` succeeds with metadata `4` in BOTH interpreters, whereas OOB `len = 20` faults `.fail .ub`
   in `stepMirFn` AND `.error (.undefinedBehavior "pointer dereference check failed")` in
   `Miri.Interpreter.Step.step`. -/
theorem w_wideSlice_subslice_and_str_reborrow_agrees :
    let bSubOk :=
      wideSliceReborrowBody sharedRefSliceU32Ty (.ref .shared ⟨2, [.deref, .subslice 1 1 true]⟩)
    let bSubOob :=
      wideSliceReborrowBody sharedRefSliceU32Ty (.ref .shared ⟨2, [.deref, .subslice 2 2 true]⟩)
    let bStr :=
      wideSliceTypedReborrowBody arrU8_16Ty rawStrTy sharedRefStrTy (.ref .shared ⟨2, [.deref]⟩)
    let subMiriPtr4 : Miri.Memory.Pointer AnnealProv :=
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr sampleAllocId + 4),
       .concrete sampleAllocId Miri.Memory.BorTag.one⟩
    let subImm1 : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair
        (Miri.Memory.Scalar.fromPointer annealTargetDataLayout subMiriPtr4)
        (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 1))
    let strVal4 : Value := .aggregate 0 [.ptr sampleAnnealPtr 8, .scalar ⟨4, 8⟩]
    let strImm4 : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair sampleMiriPtrSc (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 4))
    let strVal20 : Value := .aggregate 0 [.ptr sampleAnnealPtr 8, .scalar ⟨20, 8⟩]
    let strImm20 : Miri.Interpreter.Immediate AnnealProv :=
      .scalarPair sampleMiriPtrSc (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 20))
    ∃ (sSubOk sStrOk : MachineState) (mSubOk mSubOob mStrOk mStrOob : AnnealStepState),
      -- (1) In-bounds subslice `&(*_2)[1..1]` on `len = 3` → subslice length `1` at offset `+4`
      stepMirFn bSubOk (wideSlice4LocalInitAnneal sampleAnnealPtr 3 0 sampleAnnealArrMemory) =
        .step sSubOk ∧
      get? sSubOk.frame.locals 0 =
        some (.init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0 } 8, .scalar ⟨1, 8⟩])) ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bSubOk.localDecls bSubOk.layouts) ()
        (wideSlice4LocalInitMiri bSubOk sharedRefSliceU32Ty sampleMiriPtr 3 0 sampleArrU32Machine) =
        (mSubOk, .ok true) ∧
      miriTopLocal? mSubOk 0 = some (.live (.immediate subImm1)) ∧
      -- (2) OOB subslice `&(*_2)[2..2]` on `len = 3` → `.ub` in both
      stepMirFn bSubOob (wideSlice4LocalInitAnneal sampleAnnealPtr 3 0 sampleAnnealArrMemory) =
        .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bSubOob.localDecls bSubOob.layouts) ()
        (wideSlice4LocalInitMiri bSubOob sharedRefSliceU32Ty sampleMiriPtr 3 0 sampleArrU32Machine) =
        (mSubOob, .error (.undefinedBehavior "subslice bounds")) ∧
      -- (3a) In-bounds `&str` safe reborrow (`len = 4` on 16-byte allocation) → length `4` in both
      stepMirFn bStr
        (wideSliceTypedInitAnneal sampleAnnealArrU8_16Val strVal4 0 sampleAnnealArrMemory) =
        .step sStrOk ∧
      get? sStrOk.frame.locals 0 =
        some (.init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0 } 8, .scalar ⟨4, 8⟩])) ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bStr.localDecls bStr.layouts) ()
        (wideSliceTypedInitMiri bStr arrU8_16Ty rawStrTy sharedRefStrTy strImm4 0 sampleArrU32Machine) =
        (mStrOk, .ok true) ∧
      miriTopLocal? mStrOk 0 = some (.live (.immediate strImm4)) ∧
      -- (3b) OOB `&str` safe reborrow (`len = 20` on 16-byte allocation) → `.ub` in both
      stepMirFn bStr
        (wideSliceTypedInitAnneal sampleAnnealArrU8_16Val strVal20 0 sampleAnnealArrMemory) =
        .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bStr.localDecls bStr.layouts) ()
        (wideSliceTypedInitMiri bStr arrU8_16Ty rawStrTy sharedRefStrTy strImm20 0 sampleArrU32Machine) =
        (mStrOob, .error (.undefinedBehavior "pointer dereference check failed")) :=
  ⟨_, _, _, _, _, _,
    rfl, rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl),
    rfl, rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl)⟩

set_option maxHeartbeats 400000 in
/-- Concrete Witness 9 (**`ProjectionElem.ConstantIndex` on a dereferenced wide slice**, the MIR
for slice patterns such as `let [.., last] = *s`), real-step on BOTH interpreters with values
pinned, over a `len = 3` window of the 4-element `[10, 20, 30, 40]` backing (so a `fromEnd` index
computed from the backing length instead of the slice metadata would read `40` and be caught):
1. `(*_2)[ConstantIndex 1 1 fromEnd]` reads element `len - 1 = 2` (`30`) in both;
2. `(*_2)[ConstantIndex 0 4]` (`min_length = 4 > len = 3`) faults `.fail .ub` in `stepMirFn` and
   `"constant index minimum length"` UB in `Miri.Interpreter.Step.step`.
(Forward `ConstantIndex 1 2` → `20` and `ConstantIndex 3 3 fromEnd` → `10` were also checked to
agree by evaluation; they are omitted here to keep kernel memory under the cgroup limit.) -/
theorem w_wideSlice_constantIndex_fromEnd_and_minLength_agrees :
    let bEnd := wideSliceReborrowBody u32Ty (.use (.copy ⟨2, [.deref, .constantIndex 1 1 true]⟩))
    let bMin := wideSliceReborrowBody u32Ty (.use (.copy ⟨2, [.deref, .constantIndex 0 4 false]⟩))
    ∃ (sEnd : MachineState) (mEnd mMin : AnnealStepState),
      stepMirFn bEnd (wideSlice4LocalInitAnneal sampleAnnealPtr 3 1 sampleAnnealArrMemory) =
        .step sEnd ∧
      get? sEnd.frame.locals 0 = some (.init (.scalar ⟨30, 4⟩)) ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bEnd.localDecls bEnd.layouts) ()
        (wideSlice4LocalInitMiri bEnd u32Ty sampleMiriPtr 3 1 sampleArrU32Machine) =
        (mEnd, .ok true) ∧
      miriTopLocal? mEnd 0 = miriU32Local 30 ∧
      stepMirFn bMin (wideSlice4LocalInitAnneal sampleAnnealPtr 3 1 sampleAnnealArrMemory) =
        .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bMin.localDecls bMin.layouts) ()
        (wideSlice4LocalInitMiri bMin u32Ty sampleMiriPtr 3 1 sampleArrU32Machine) =
        (mMin, .error (.undefinedBehavior "constant index minimum length")) :=
  ⟨_, _, _,
    rfl, rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl)⟩

/-- Shared thin `&u32` reference type. -/
def sharedRefU32Ty : Ty :=
  { kind := .ref .not (.uint .u32), layoutIdx := 0 }

set_option maxHeartbeats 600000 in
/-- Concrete Witness 9b (**Forward & first-from-end `ConstantIndex` reads on dereferenced wide slices**):
Kernel-checks both cases left as unproved docstring comments in Witness 9 (`2613d77c`) on `len = 3`
over `[10, 20, 30, 40]` (kept well within cgroup RAM by `Elab.async false`):
1. Forward `(*_2)[ConstantIndex 1 2 false]` reads `20_u32` in both `stepMirFn` and `Step.step`.
2. First-from-end `(*_2)[ConstantIndex 3 3 true]` reads `len - 3 = 0` (`10_u32`) in both. -/
theorem w_wideSlice_constantIndex_forward_and_firstFromEnd_agrees :
    let bFwd := wideSliceReborrowBody u32Ty (.use (.copy ⟨2, [.deref, .constantIndex 1 2 false]⟩))
    let bFirstEnd := wideSliceReborrowBody u32Ty (.use (.copy ⟨2, [.deref, .constantIndex 3 3 true]⟩))
    ∃ (sFwd sFirstEnd : MachineState) (mFwd mFirstEnd : AnnealStepState),
      stepMirFn bFwd (wideSlice4LocalInitAnneal sampleAnnealPtr 3 0 sampleAnnealArrMemory) =
        .step sFwd ∧
      get? sFwd.frame.locals 0 = some (.init (.scalar ⟨20, 4⟩)) ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bFwd.localDecls bFwd.layouts) ()
        (wideSlice4LocalInitMiri bFwd u32Ty sampleMiriPtr 3 0 sampleArrU32Machine) =
        (mFwd, .ok true) ∧
      miriTopLocal? mFwd 0 = miriU32Local 20 ∧
      stepMirFn bFirstEnd (wideSlice4LocalInitAnneal sampleAnnealPtr 3 0 sampleAnnealArrMemory) =
        .step sFirstEnd ∧
      get? sFirstEnd.frame.locals 0 = some (.init (.scalar ⟨10, 4⟩)) ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bFirstEnd.localDecls bFirstEnd.layouts) ()
        (wideSlice4LocalInitMiri bFirstEnd u32Ty sampleMiriPtr 3 0 sampleArrU32Machine) =
        (mFirstEnd, .ok true) ∧
      miriTopLocal? mFirstEnd 0 = miriU32Local 10 :=
  ⟨_, _, _, _,
    rfl, rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), (by with_unfolding_all rfl),
    rfl, rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), (by with_unfolding_all rfl)⟩

set_option maxHeartbeats 600000 in
/-- Concrete Witness 9c (**Thin element-ref `ConstantIndex` reborrow & `DIV-LM-CONSTANT-INDEX-NAT-SUB-SATURATION`**):
1. **Thin element-reference reborrow `_0 = &(*_2)[ConstantIndex 1 1 true]` (`_0 : &u32`)**:
   BOTH `stepMirFn` (`evalSliceFatPtrDerefBorrow` line `16059`, fresh tag `2`) and
   `Miri.Interpreter.Step.step` (`PlaceDynamic.constantIndex` → byte offset `+ 8`) succeed in lockstep.
2. **`DIV-LM-CONSTANT-INDEX-NAT-SUB-SATURATION`** (`copy (*_2)[ConstantIndex 4 1 true]` where
   `offset = 4 > len = 3 ≥ minLen = 1`): Anneal's `readProjectedValue` (`Places.lean:2398`)
   evaluates `Nat.sub 3 4 = 0` via saturating `Nat` subtraction and silently succeeds with `10_u32`,
   whereas vendored `Miri.Interpreter.Step.step` (`PlaceDynamic.lean:110`) rejects with
   `.error (.invalidProgram "invalid from-end constant index")`! (Contrast with reborrow
   `&(*_2)[ConstantIndex 4 1 true]`, where `evalSliceFatPtrDerefBorrow` at `Places.lean:16065`
   checks `offset ≤ len` and faults `.fail .ub`.) -/
theorem w_wideSlice_constantIndex_reborrow_and_malformed_divergence :
    let bRefElem := wideSliceReborrowBody sharedRefU32Ty (.ref .shared ⟨2, [.deref, .constantIndex 1 1 true]⟩)
    let bMalRead := wideSliceReborrowBody u32Ty (.use (.copy ⟨2, [.deref, .constantIndex 4 1 true]⟩))
    let bMalRef := wideSliceReborrowBody sharedRefU32Ty (.ref .shared ⟨2, [.deref, .constantIndex 4 1 true]⟩)
    let elem2MiriPtr : Miri.Memory.Pointer AnnealProv :=
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr sampleAllocId + 8),
       .concrete sampleAllocId Miri.Memory.BorTag.one⟩
    let elem2MiriPtrSc : Miri.Memory.Scalar AnnealProv :=
      Miri.Memory.Scalar.fromPointer annealTargetDataLayout elem2MiriPtr
    ∃ (sRefElem sMalRead : MachineState) (mRefElem mMalRead mMalRef : AnnealStepState),
      stepMirFn bRefElem (wideSlice4LocalInitAnneal sampleAnnealPtr 3 0 sampleAnnealArrMemory) =
        .step sRefElem ∧
      get? sRefElem.frame.locals 0 =
        some (.init (.ptr { allocId := 2, offsetBytes := 0 } 8)) ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bRefElem.localDecls bRefElem.layouts) ()
        (wideSlice4LocalInitMiri bRefElem sharedRefU32Ty sampleMiriPtr 3 0 sampleArrU32Machine) =
        (mRefElem, .ok true) ∧
      miriTopLocal? mRefElem 0 = some (.live (.immediate (.scalar elem2MiriPtrSc))) ∧
      stepMirFn bMalRead (wideSlice4LocalInitAnneal sampleAnnealPtr 3 0 sampleAnnealArrMemory) =
        .step sMalRead ∧
      get? sMalRead.frame.locals 0 = some (.init (.scalar ⟨10, 4⟩)) ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bMalRead.localDecls bMalRead.layouts) ()
        (wideSlice4LocalInitMiri bMalRead u32Ty sampleMiriPtr 3 0 sampleArrU32Machine) =
        (mMalRead, .error (.invalidProgram "invalid from-end constant index")) ∧
      stepMirFn bMalRef (wideSlice4LocalInitAnneal sampleAnnealPtr 3 0 sampleAnnealArrMemory) =
        .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksWideSlice bMalRef.localDecls bMalRef.layouts) ()
        (wideSlice4LocalInitMiri bMalRef sharedRefU32Ty sampleMiriPtr 3 0 sampleArrU32Machine) =
        (mMalRef, .error (.invalidProgram "invalid from-end constant index")) :=
  ⟨_, _, _, _, _,
    rfl, rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl), (by with_unfolding_all rfl),
    rfl, rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl),
    rfl, prod_eq_fst_of_snd (by with_unfolding_all rfl)⟩

end WideSliceWitnesses

end LeanMiriSpec.Correspondence
