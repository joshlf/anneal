/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import MiniRustSpec.UnwindSetDiscrAndFnPtrMR

/-!
# Episode 2 Dual-Authority Correspondence (`MiniRustSpec` Authority):
# Drop, Unsafe Binders, ShallowInitBox, Subtype, RawPtr, Closures, Coverage & Drop Hints

Universal operational step-simulation, fault-equivalence, boundary, and
`Classical.choice`-free byte-codec theorems relating
`Trusted.Rustc.V2026_06_01.MirSemantics.{evalStmt, evalRvalue, evalTerminator, stepMirFn}`
directly to `MiniRustSpec.Interp` across **both `Mach` (`BasicMemory<x86_64>`)
and `MachTB` (`TreeBorrowsMemory<x86_64>`, preserving `MachTB.wfLive`)** for all
8 already-trusted MIR variants:

1. **`V1` (`StatementKind.coverage`)** — unconditional stuttering PC-advance,
   erased-program equivalence, and UB-after-coverage fault equivalence.
2. **`V2` (`StatementKind.backwardIncompatibleDropHint`)** — unconditional
   stuttering PC-advance (never faulting even on dead/uninit/OOB places) and
   subsequent dead-place read UB contrast.
3. **`V3` (`TerminatorKind.drop`)** — whole-local drop (`Deinit + Goto`),
   projected sub-place drop on `(u32, u32)` preserving sibling fields,
   dead-local UB equivalence, active-protector write conflict UB (genuine
   `Mach` vs. `MachTB` mode sensitivity), cleanup-block unwind/post-drop
   target transitions, and explicit deinit vs. runtime-nop phase boundary.
4. **`V4` (`Rvalue.shallowInitBox`)** — thin raw-pointer operand to
   `Box<u32>` (`PtrType.Box` and `PtrType.Raw .None`) preserving pointer
   provenance without reading or writing uninitialized pointee memory,
   dead/uninit operand UB equivalence, `PtrType.Box` safe-pointer validity
   boundary, and Trusted fail-closed `.unsupported` on non-raw-pointer or
   wrong-width operands.
5. **`V5` (`Rvalue.wrapUnsafeBinder`)** — transparent unsafe-binder targets
   AND single-field `binderStructLayout?` wrapper structs (`BinderU32` and
   `NonZeroU8`), scalar validity-range UB (`scalarValidRangeOk`), identity
   when `opTy.kind = targetTy.kind`, unknown-operand `.unsupported`, and
   full round-trip with `ProjectionElem.unwrapUnsafeBinder`.
6. **`V6` (`CastKind.subtype`)** — definitional identity with `.transmute`
   (`evalByteCast`), scalars (`u32 → i32`), pointers (`*mut u32 → *const u32`),
   validity-range UB (`bool` byte `2`, `NonZeroU8` byte `0`), dead/uninit UB,
   and size-mismatch `.unsupported`.
7. **`V7` (`AggregateKind.rawPtr`)** — thin raw pointers with `()` unit
   metadata AND wide slice `[u32]` / `str` raw pointers with `usize`
   element-count metadata, directly exercising Episode 1's newly executable
   `UnOp.GetMetadata`, `UnOp.ComputeSize`, and `UnOp.ComputeAlign` on `Mach`
   and `MachTB`, plus dead/uninit operand UB (both data-pointer and metadata
   operands) and shape-mismatch UB / dyn-scalar `.unsupported`.
8. **`V8` (`AggregateKind.closure`)** — 0-capture ZST closures and
   multi-capture `(u32, *const u32)` closures with left-to-right operand
   evaluation, upvar mutation/read-back, and dead/uninit upvar UB propagation.

Strict import isolation: this module NEVER imports `Anneal.*`,
`MiniRustSpec.Correspondence.DeinitBridge`, or
`MiniRustSpec.Correspondence.IntrinsicBoundary` (verified by the trailing
`#assert_drop_binder_subtype_mr_audit` check).
-/

namespace MiniRustSpec.DropBinderAndSubtypeMR

set_option Elab.async false
set_option linter.unusedSimpArgs false

open Trusted.Effect Trusted.ITree Trusted.Sequence
open Trusted.Rustc.V2026_06_01 Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics Trusted.Rustc.V2026_06_01.Layout
open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp
open MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.Witness hiding constU32
open MiniRustSpec.Correspondence.PointerWitness MiniRustSpec.Correspondence.RefWitness
open MiniRustSpec.Correspondence.TbWitness
open MiniRustSpec.Correspondence.WideSliceDst hiding usizeMirTy
open MiniRustSpec.UnwindSetDiscrAndFnPtrMR

/-! ## §0. Shared Episode 2 Types, Layouts, and `Classical.choice`-Free Codecs -/

/-- Pair `(u32, u32)` MIR type (size 8, align 4). -/
@[reducible] def pairU32MirTy : MirAst.Ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 0 }

/-- Pair `(u32, u32)` MiniRust tuple type (size 8, align 4, fields at offsets 0 and 4). -/
@[reducible] def mrPairU32Ty : Gen.Type :=
  .Tuple [(⟨0⟩, u32MrTy), (⟨4⟩, u32MrTy)] ⟨⟨8⟩, ⟨4⟩, none⟩ none

/-- MiniRust `Box<u32>` safe pointer type (`PointeeInfo` sized 4, align 4, inhabited, freeze, unpin). -/
@[reducible] def boxU32MrTy : Gen.Type :=
  .Ptr (.Box (intPointeeInfo u32))

/-- MiniRust `Box<u64>` safe pointer type (`PointeeInfo` sized 8, align 8, inhabited, freeze, unpin). -/
@[reducible] def boxU64MrTy : Gen.Type :=
  .Ptr (.Box (intPointeeInfo IntType.usize_ty))

/-- Anneal `Box<u32>` MIR representation (`*mut u32` / `alloc::boxed::Box` thin raw pointer). -/
@[reducible] def boxU32MirTy : MirAst.Ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 0 }

/-- Anneal `Box<u64>` MIR representation (`*mut u64` thin raw pointer, distinct pointee/contentTy for `V4.okSecondary`). -/
@[reducible] def boxU64MirTy : MirAst.Ty := { kind := .rawPtr .mut (.uint .u64), layoutIdx := 0 }

/-- Anneal `*mut u8` raw pointer MIR type (rustc's `ShallowInitBox` input operand type). -/
@[reducible] def rawMutU8MirTy : MirAst.Ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }

/-- Anneal `*const str` wide raw pointer MIR type. -/
@[reducible] def rawConstStrMirTy : MirAst.Ty := { kind := .rawPtr .not .str, layoutIdx := 0 }

/-- Anneal `str` unsized pointee MIR type. -/
@[reducible] def strMirTy : MirAst.Ty := { kind := .str, layoutIdx := 0 }

/-- Anneal `[u32]` unsized slice pointee MIR type. -/
@[reducible] def sliceU32MirTy : MirAst.Ty := { kind := .slice (.uint .u32), layoutIdx := 0 }

/-- Single-field `BinderU32(u32)` Anneal `TypeLayout` triggering `binderStructLayout? = some _`. -/
def binderU32MirLayout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0xffffffff⟩),
    fields := .arbitrary [⟨0⟩] [0],
    variants := .single 0,
    isUninhabited := false }

/-- Transparent `bool` layout enforcing `0..=1` scalar validity range. -/
def boolScalarMirLayout : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .primitive,
    variants := .single 0,
    isUninhabited := false }

/-- Layout table with dummy index `0` (reserved by `isUnresolvedLayoutIdx`),
`binderU32MirLayout` at index `1`, `nonZeroU8MirLayout` at index `2`, and
`boolScalarMirLayout` at index `3`. -/
def ep2BinderLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [binderU32MirLayout, binderU32MirLayout, nonZeroU8MirLayout, boolScalarMirLayout] }

/-- Single-field `BinderU32` ADT MIR type (layoutIdx `1` in `ep2BinderLayouts`). -/
@[reducible] def binderU32MirTy : MirAst.Ty := { kind := .adt "ep2::BinderU32" [], layoutIdx := 1 }

/-- Single-field `NonZeroU8` binder struct ADT MIR type (layoutIdx `2` in `ep2BinderLayouts`). -/
@[reducible] def binderNzU8MirTy : MirAst.Ty := { kind := .adt "ep2::BinderNonZeroU8" [], layoutIdx := 2 }

/-- Transparent `bool` binder target MIR type with recorded `0..=1` layout (layoutIdx `3` in `ep2BinderLayouts`). -/
@[reducible] def binderBoolMirTy : MirAst.Ty := { kind := .bool, layoutIdx := 3 }

/-- MiniRust `(*const T, ())` pair type (size 8, align 8) for thin `AggregateKind.rawPtr` lowering. -/
@[reducible] def mrRawPtrThinPairTy : Gen.Type :=
  .Tuple [(⟨0⟩, thinRawPtrTy), (⟨8⟩, unitType)] ⟨⟨8⟩, ⟨8⟩, none⟩ none

/-- MiniRust `(*const T, usize)` pair type (size 16, align 8) for wide slice/str `AggregateKind.rawPtr` lowering. -/
@[reducible] def mrRawPtrWidePairTy : Gen.Type :=
  .Tuple [(⟨0⟩, thinRawPtrTy), (⟨8⟩, usizeMrTy)] ⟨⟨16⟩, ⟨8⟩, none⟩ none

/-- Constant `()` unit operand. -/
@[reducible] def constUnit : MirAst.Operand :=
  .constant { ty := unitMirTy, val := .zeroSized }

/-- Constant `usize` operand. -/
@[reducible] def constUsize (n : Nat) : MirAst.Operand :=
  .constant { ty := usizeMirTy, val := .scalar (.int ⟨n, 8⟩) }

/-- Constant `u64` operand. -/
@[reducible] def constU64 (n : Nat) : MirAst.Operand :=
  .constant { ty := u64MirTy, val := .scalar (.int ⟨n, 8⟩) }

private theorem size_ne_self_ite_ep2 {α : Type} (s : LibSpecr.Size) (a b : α) :
    (if s ≠ s then a else b) = b := by simp

private theorem writeSubsliceAtIndex_zero_exact {α : Type} (buf xs : List α)
    (hLen : xs.length = buf.length) :
    writeSubsliceAtIndex buf 0 xs = .ok xs := by
  unfold writeSubsliceAtIndex
  have hCond : (0 : Int) ≤ 0 ∧ (0 : Int) + (xs.length : Int) ≤ (buf.length : Int) := by
    rw [hLen]; simp
  rw [ite_eq_left_iff.mpr (fun hn => absurd hCond hn)]
  simp [hLen, pure, Except.pure]

private theorem writeSubsliceAtIndex_empty_at_end {α : Type} (xs : List α) :
    writeSubsliceAtIndex xs (xs.length : Int) [] = .ok xs := by
  unfold writeSubsliceAtIndex
  have hCond : (0 : Int) ≤ (xs.length : Int) ∧
      (xs.length : Int) + (([] : List α).length : Int) ≤ (xs.length : Int) := by
    simp
  rw [ite_eq_left_iff.mpr (fun hn => absurd hCond hn)]
  simp [Int.toNat_natCast, List.take_length, List.drop_length, pure, Except.pure]

private theorem writeSubsliceAtIndex_replicate_half1 {α : Type} (d : α) (a : List α) (n : Nat)
    (ha : a.length = n) :
    writeSubsliceAtIndex (List.replicate (n + n) d) 0 a = .ok (a ++ List.replicate n d) := by
  unfold writeSubsliceAtIndex
  have hCond : (0 : Int) ≤ 0 ∧ (0 : Int) + (a.length : Int) ≤ ((List.replicate (n + n) d).length : Int) := by
    simp only [List.length_replicate, ha, Int.zero_add, Int.ofNat_le]
    exact ⟨Int.le_refl 0, Nat.le_add_right n n⟩
  rw [ite_eq_left_iff.mpr (fun hn => absurd hCond hn)]
  simp [Int.toNat_zero, ha, List.drop_replicate, Nat.add_sub_cancel_left, pure, Except.pure]

private theorem writeSubsliceAtIndex_replicate_half2 {α : Type} (d : α) (a b : List α) (n : Nat)
    (ha : a.length = n) (hb : b.length = n) :
    writeSubsliceAtIndex (a ++ List.replicate n d) (n : Int) b = .ok (a ++ b) := by
  have hLenBuf : (a ++ List.replicate n d).length = n + n := by
    rw [List.length_append, ha, List.length_replicate]
  unfold writeSubsliceAtIndex
  have hCond : (0 : Int) ≤ (n : Int) ∧ (n : Int) + (b.length : Int) ≤ ((a ++ List.replicate n d).length : Int) := by
    rw [hLenBuf, hb]; simp
  rw [ite_eq_left_iff.mpr (fun hn => absurd hCond hn)]
  have hTake : (a ++ List.replicate n d).take n = a := by
    rw [← ha]; exact List.take_left
  have hDrop : (a ++ List.replicate n d).drop (n + b.length) = [] := by
    rw [hb, ← hLenBuf]; exact List.drop_length
  simp [Int.toNat_natCast, hTake, hDrop, pure, Except.pure]

private theorem inBounds_signed_ptrSize_small (k : Nat) (hk : k < 8) :
    inBounds (k : Int) .Signed x86_64.PTR_SIZE = true := by
  have hPow3 : k < 2 ^ 3 := hk
  have hPow63 : k < 2 ^ 63 := Nat.lt_of_lt_of_le hPow3 (Nat.pow_le_pow_right (by decide) (by decide : 3 ≤ 63))
  have hLtI : (k : Int) < (2 : Int) ^ 63 := by
    rw [← two_pow_int_cf]; exact Int.ofNat_lt.mpr hPow63
  have hNegLe : -((2 : Int) ^ 63) ≤ (k : Int) :=
    Int.le_trans (Int.neg_nonpos_of_nonneg (Int.pow_nonneg (by decide))) (Int.natCast_nonneg k)
  unfold inBounds Interp.Size.bits
  simp only [x86_64.PTR_SIZE, Bool.and_eq_true]
  change decide (-((2 : Int) ^ 63) ≤ (k : Int)) = true ∧ decide ((k : Int) < (2 : Int) ^ 63) = true
  exact ⟨decide_eq_true hNegLe, decide_eq_true hLtI⟩

private theorem subsliceWithLength_append_left {α : Type} (a b : List α) (n : Nat)
    (ha : a.length = n) :
    subsliceWithLength (a ++ b) 0 (n : Int) = .ok a := by
  unfold subsliceWithLength
  have hCond : (0 : Int) ≤ 0 ∧ (0 : Int) ≤ (n : Int) ∧ (0 : Int) + (n : Int) ≤ ((a ++ b).length : Int) := by
    simp only [List.length_append, ha, Int.zero_add, Int.ofNat_le]
    exact ⟨Int.le_refl 0, Int.natCast_nonneg n, Nat.le_add_right n b.length⟩
  rw [ite_eq_left_iff.mpr (fun hn => absurd hCond hn)]
  simp only [Int.toNat_zero, List.drop_zero, Int.toNat_natCast]
  rw [← ha, List.take_left]; rfl

private theorem subsliceWithLength_append_right {α : Type} (a b : List α) (n : Nat)
    (ha : a.length = n) (hb : b.length = n) :
    subsliceWithLength (a ++ b) (n : Int) (n : Int) = .ok b := by
  unfold subsliceWithLength
  have hCond : (0 : Int) ≤ (n : Int) ∧ (0 : Int) ≤ (n : Int) ∧ (n : Int) + (n : Int) ≤ ((a ++ b).length : Int) := by
    simp only [List.length_append, ha, hb]; exact ⟨Int.natCast_nonneg n, Int.natCast_nonneg n, Int.le_refl _⟩
  rw [ite_eq_left_iff.mpr (fun hn => absurd hCond hn)]
  simp only [Int.toNat_natCast]
  rw [← ha, List.drop_left, ha, ← hb, List.take_length]; rfl

/-- `Classical.choice`-free polymorphic codec for thin `AggregateKind.rawPtr`:
`transmuteM` turns `Tuple [thinPtr, ()]` at `mrRawPtrThinPairTy` into `thinPtr`
at `thinRawPtrTy` across BOTH `Mach` and `MachTB`, preserving exact address and
provenance. -/
theorem transmuteM_rawPtrThinPair_to_thinRawPtr {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr : Nat) (hAddr : addr < 2 ^ 64) (prov : Option (Gen.Memory.Provenance M))
    (m : Option (Machine M)) :
    let vPtr : Gen.Value M := .Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)
    transmuteM (M := M) (.Tuple [vPtr, .Tuple []]) mrRawPtrThinPairTy thinRawPtrTy m = .ok vPtr := by
  intro vPtr
  let ptrBs := encodePtrBytesM (M := M) prov 0 (leBytes addr 8)
  have hPtrLen : ptrBs.length = 8 := by
    dsimp only [ptrBs]; rw [encodePtrBytesM_length, leBytes_length]
  have hEncPtr : Type.encodeM (M := M) thinRawPtrTy vPtr = .ok ptrBs := by
    simp only [thinRawPtrTy, Type.encodeM, PtrType.as_wide_pair, PtrType.meta_kind,
      vPtr, ThinPointer.widen]
    exact encodePtrM_eq addr hAddr prov
  have hDecPtr : Type.decodeM (M := M) thinRawPtrTy ptrBs = .ok (some vPtr) := by
    simp only [thinRawPtrTy, Type.decodeM, PtrType.as_wide_pair, PtrType.meta_kind,
      vPtr, ThinPointer.widen]
    rw [decodePtrM_encodePtrBytesM addr hAddr prov, ok_bind]; rfl
  have hW1 : writeSubsliceAtIndex (List.replicate 8 (AbstractByte.Uninit : AbstractByte (Gen.Memory.Provenance M))) 0 ptrBs = .ok ptrBs :=
    writeSubsliceAtIndex_zero_exact _ ptrBs (by rw [hPtrLen, List.length_replicate])
  have hW2 : writeSubsliceAtIndex ptrBs 8 [] = .ok ptrBs := by
    simpa [hPtrLen] using writeSubsliceAtIndex_empty_at_end ptrBs
  have hEncPair : Type.encodeM (M := M) mrRawPtrThinPairTy (.Tuple [vPtr, .Tuple []]) = .ok ptrBs := by
    unfold mrRawPtrThinPairTy Type.encodeM
    dsimp only [TupleHeadLayout.head_size_and_align, List.length, ne_eq, not_true_eq_false, ↓reduceIte]
    unfold Type.encodeFieldsM
    rw [hEncPtr, ok_bind]
    change writeSubsliceAtIndex (List.replicate 8 .Uninit) 0 ptrBs >>=
      (fun buf => Type.encodeFieldsM [(⟨8⟩, unitType)] [.Tuple []] buf) = .ok ptrBs
    rw [hW1, ok_bind]
    unfold Type.encodeFieldsM
    have hUnit : Type.encodeM (M := M) unitType (.Tuple []) = .ok [] := rfl
    rw [hUnit, ok_bind]
    change writeSubsliceAtIndex ptrBs 8 [] >>= (fun buf => Type.encodeFieldsM [] [] buf) = .ok ptrBs
    rw [hW2, ok_bind]; rfl
  have hLayPair : Type.layout mrRawPtrThinPairTy = .ok (.Sized ⟨8⟩ ⟨8⟩) := rfl
  have hLayThin : Type.layout thinRawPtrTy = .ok (.Sized ⟨8⟩ ⟨8⟩) := layout_thinRawPtr
  unfold transmuteM
  rw [hLayPair, ok_bind, expect_size_sized, ok_bind, hLayThin, ok_bind, expect_size_sized,
      ok_bind, size_ne_self_ite_ep2, hEncPair, ok_bind, hDecPtr, ok_bind]
  dsimp only []
  rw [checkValueM_thinRawPtr_of_inBounds (addr : Int) prov m (inBounds_usize_cf addr hAddr), ok_bind]
  rfl

private theorem transmuteM_rawPtrWidePair_to_wideSlicePtr_of_codec {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr len : Int) (prov : Option (Gen.Memory.Provenance M))
    (bs : List (AbstractByte (Gen.Memory.Provenance M))) (m : Option (Machine M))
    (hInAddr : inBounds addr .Unsigned x86_64.PTR_SIZE = true)
    (hInLen : inBounds len .Unsigned x86_64.PTR_SIZE = true)
    (hEnc : Type.encodeM (M := M) mrRawPtrWidePairTy
      (.Tuple [.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none), .Int len]) = .ok bs)
    (hDec : Type.decodeM (M := M) wideSlicePtrMrTy bs =
      .ok (some (mrWidePtrValM { addr := addr, provenance := prov } len))) :
    let vThin : Gen.Value M := .Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)
    let vWide : Gen.Value M := mrWidePtrValM { addr := addr, provenance := prov } len
    transmuteM (M := M) (.Tuple [vThin, .Int len]) mrRawPtrWidePairTy wideSlicePtrMrTy m =
      .ok vWide := by
  intro vThin vWide
  have hLayPair : Type.layout mrRawPtrWidePairTy = .ok (.Sized ⟨16⟩ ⟨8⟩) := rfl
  have hLayWide : Type.layout wideSlicePtrMrTy = .ok (.Sized ⟨16⟩ ⟨8⟩) := rfl
  have hCanRep : IntType.can_represent IntType.usize_ty len = true := hInLen
  have hChkWide : checkValueM (M := M) vWide wideSlicePtrMrTy m = .ok () := by
    dsimp only [vWide, mrWidePtrValM]
    unfold checkValueM checkPtrM
    simp only [wideSlicePtrMrTy, ThinPointer.widen, ensureElseUb, hInAddr, ↓reduceIte,
      PtrType.meta_kind, checkPtrMetadataM, hCanRep, PtrType.safe_pointee,
      Bool.not_true, Bool.false_eq_true, pure, Except.pure, bind, Except.bind]
  unfold transmuteM
  rw [hLayPair, ok_bind, expect_size_sized, ok_bind, hLayWide, ok_bind, expect_size_sized,
      ok_bind, size_ne_self_ite_ep2]
  rw [show Type.encodeM (M := M) mrRawPtrWidePairTy (.Tuple [vThin, .Int len]) = .ok bs from hEnc, ok_bind,
      show Type.decodeM (M := M) wideSlicePtrMrTy bs = .ok (some vWide) from hDec, ok_bind]
  dsimp only []
  rw [hChkWide, ok_bind]; rfl

/-- `Classical.choice`-free polymorphic codec for wide slice/str `AggregateKind.rawPtr`:
`transmuteM` turns `Tuple [thinPtr, len]` at `mrRawPtrWidePairTy` into the wide
raw pointer `mrWidePtrValM { addr, provenance } len` at `wideSlicePtrMrTy` across
BOTH `Mach` and `MachTB`, preserving exact data pointer provenance and `usize`
element-count metadata. -/
theorem transmuteM_rawPtrWidePair_to_wideSlicePtr {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr len : Nat) (hAddr : addr < 2 ^ 64) (hLen : len < 2 ^ 64)
    (prov : Option (Gen.Memory.Provenance M)) (m : Option (Machine M)) :
    let vThin : Gen.Value M := .Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)
    let vWide : Gen.Value M := mrWidePtrValM { addr := addr, provenance := prov } (len : Int)
    transmuteM (M := M) (.Tuple [vThin, .Int (len : Int)]) mrRawPtrWidePairTy wideSlicePtrMrTy m =
      .ok vWide := by
  intro vThin vWide
  let thinBs := encodePtrBytesM (M := M) prov 0 (leBytes addr 8)
  let metaBs : List (AbstractByte (Gen.Memory.Provenance M)) :=
    (leBytes len 8).map (fun b => .Init b none)
  have hThinLen : thinBs.length = 8 := by
    dsimp only [thinBs]; rw [encodePtrBytesM_length, leBytes_length]
  have hMetaLen : metaBs.length = 8 := by
    dsimp only [metaBs]; rw [List.length_map, leBytes_length]
  have hEncThin : Type.encodeM (M := M) thinRawPtrTy vThin = .ok thinBs := by
    simp only [thinRawPtrTy, Type.encodeM, PtrType.as_wide_pair, PtrType.meta_kind,
      vThin, ThinPointer.widen]
    exact encodePtrM_eq addr hAddr prov
  have hEncMeta : Type.encodeM (M := M) usizeMrTy (.Int (len : Int)) = .ok metaBs := by
    simpa [usizeMrTy, Type.encodeM, metaBs] using
      encodeUsizeIntM_of_encode (M := M) (len : Int) (leBytes len 8) (encode_usize_cf len hLen)
  have hEncPair : Type.encodeM (M := M) mrRawPtrWidePairTy (.Tuple [vThin, .Int (len : Int)]) =
      .ok (thinBs ++ metaBs) := by
    have hW1 : writeSubsliceAtIndex (List.replicate 16 (AbstractByte.Uninit : AbstractByte (Gen.Memory.Provenance M))) 0 thinBs =
        .ok (thinBs ++ List.replicate 8 .Uninit) :=
      writeSubsliceAtIndex_replicate_half1 .Uninit thinBs 8 hThinLen
    have hW2 : writeSubsliceAtIndex (thinBs ++ List.replicate 8 (AbstractByte.Uninit : AbstractByte (Gen.Memory.Provenance M))) 8 metaBs =
        .ok (thinBs ++ metaBs) :=
      writeSubsliceAtIndex_replicate_half2 .Uninit thinBs metaBs 8 hThinLen hMetaLen
    unfold mrRawPtrWidePairTy Type.encodeM
    dsimp only [TupleHeadLayout.head_size_and_align, List.length, ne_eq, not_true_eq_false, ↓reduceIte]
    unfold Type.encodeFieldsM
    rw [hEncThin, ok_bind]
    change writeSubsliceAtIndex (List.replicate 16 .Uninit) 0 thinBs >>=
      (fun buf => Type.encodeFieldsM [(⟨8⟩, usizeMrTy)] [.Int (len : Int)] buf) = .ok (thinBs ++ metaBs)
    rw [hW1, ok_bind]
    unfold Type.encodeFieldsM
    rw [hEncMeta, ok_bind]
    change writeSubsliceAtIndex (thinBs ++ List.replicate 8 .Uninit) 8 metaBs >>=
      (fun buf => Type.encodeFieldsM [] [] buf) = .ok (thinBs ++ metaBs)
    rw [hW2, ok_bind]; rfl
  exact transmuteM_rawPtrWidePair_to_wideSlicePtr_of_codec (M := M) (addr : Int) (len : Int) prov
    (thinBs ++ metaBs) m (inBounds_usize_cf addr hAddr) (inBounds_usize_cf len hLen)
    hEncPair (decodeWideSliceRawPtrM_eq addr len hAddr hLen prov)

private theorem transmuteM_thinRawPtr_to_boxU32_of_codec {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr : Int) (prov : Option (Gen.Memory.Provenance M))
    (bs : List (AbstractByte (Gen.Memory.Provenance M))) (m : Machine M)
    (hInAddr : inBounds addr .Unsigned x86_64.PTR_SIZE = true)
    (hIn4 : inBounds ((4 : Nat) : Int) .Signed x86_64.PTR_SIZE = true)
    (hNe0 : (addr != 0) = true)
    (hAl : Align.is_aligned ⟨4⟩ addr = true)
    (hDeref : ConcurrentMemory.dereferenceable m.mem { addr := addr, provenance := prov } ⟨4⟩ = .ok ())
    (hEnc : Type.encodeM (M := M) thinRawPtrTy
      (.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)) = .ok bs)
    (hDec : Type.decodeM (M := M) boxU32MrTy bs =
      .ok (some (.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)))) :
    let vPtr : Gen.Value M := .Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)
    transmuteM (M := M) vPtr thinRawPtrTy boxU32MrTy (some m) = .ok vPtr := by
  intro vPtr
  have hLayThin : Type.layout thinRawPtrTy = .ok (.Sized ⟨8⟩ ⟨8⟩) := layout_thinRawPtr
  have hLayBox : Type.layout boxU32MrTy = .ok (.Sized ⟨8⟩ ⟨8⟩) := rfl
  have hChkBox : checkValueM (M := M) vPtr boxU32MrTy (some m) = .ok () := by
    dsimp only [vPtr]
    unfold checkValueM checkPtrM
    simp only [boxU32MrTy, intPointeeInfo, u32, ThinPointer.widen, ensureElseUb, hInAddr, hIn4, ↓reduceIte,
      PtrType.meta_kind, LayoutStrategy.meta_kind, checkPtrMetadataM, PtrType.safe_pointee,
      LayoutStrategy.compute_size_and_align, hNe0, hAl, hDeref,
      Bool.not_true, Bool.false_eq_true, pure, Except.pure, bind, Except.bind]
  unfold transmuteM
  rw [hLayThin, ok_bind, expect_size_sized, ok_bind, hLayBox, ok_bind, expect_size_sized,
      ok_bind, size_ne_self_ite_ep2]
  rw [show Type.encodeM (M := M) thinRawPtrTy vPtr = .ok bs from hEnc, ok_bind,
      show Type.decodeM (M := M) boxU32MrTy bs = .ok (some vPtr) from hDec, ok_bind]
  dsimp only []
  rw [hChkBox, ok_bind]; rfl

/-- `Classical.choice`-free polymorphic `ShallowInitBox` codec: transmuting a thin
raw pointer (`thinRawPtrTy`) to `boxU32MrTy` (`Box<u32>`) on ANY machine `m`
(`Mach` or `MachTB`) whose memory validates `ConcurrentMemory.dereferenceable`
for 4 bytes at `{ addr, provenance }` succeeds without reading or writing
pointee bytes, preserving exact `(addr, provenance)`. -/
theorem transmuteM_thinRawPtr_to_boxU32 {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr : Nat) (hAddr : addr < 2 ^ 64) (hNonNull : addr ≠ 0) (hAlign : addr % 4 = 0)
    (prov : Option (Gen.Memory.Provenance M)) (m : Machine M)
    (hDeref : ConcurrentMemory.dereferenceable m.mem { addr := addr, provenance := prov } ⟨4⟩ = .ok ()) :
    let vPtr : Gen.Value M := .Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)
    transmuteM (M := M) vPtr thinRawPtrTy boxU32MrTy (some m) = .ok vPtr := by
  intro vPtr
  let ptrBs := encodePtrBytesM (M := M) prov 0 (leBytes addr 8)
  have hEnc : Type.encodeM (M := M) thinRawPtrTy vPtr = .ok ptrBs := by
    simp only [thinRawPtrTy, Type.encodeM, PtrType.as_wide_pair, PtrType.meta_kind,
      vPtr, ThinPointer.widen]
    exact encodePtrM_eq addr hAddr prov
  have hDec : Type.decodeM (M := M) boxU32MrTy ptrBs = .ok (some vPtr) := by
    simp only [boxU32MrTy, intPointeeInfo, Type.decodeM, PtrType.as_wide_pair, PtrType.meta_kind,
      LayoutStrategy.meta_kind, vPtr, ThinPointer.widen]
    rw [decodePtrM_encodePtrBytesM addr hAddr prov, ok_bind]; rfl
  have hNe0 : ((addr : Int) != 0) = true := by
    simp only [bne_iff_ne, ne_eq]; intro h; exact hNonNull (Int.ofNat.inj h)
  have hAl : Align.is_aligned ⟨4⟩ (addr : Int) = true := by
    unfold Align.is_aligned
    simp only [beq_iff_eq]
    have : (addr : Int) % ((4 : Nat) : Int) = ((addr % 4 : Nat) : Int) := (Int.natCast_emod addr 4).symm
    rw [this, hAlign]; rfl
  exact transmuteM_thinRawPtr_to_boxU32_of_codec (M := M) (addr : Int) prov ptrBs m
    (inBounds_usize_cf addr hAddr) (inBounds_signed_ptrSize_small 4 (by decide))
    hNe0 hAl hDeref hEnc hDec

/-- `Classical.choice`-free polymorphic `(u32, u32)` encode/decode round-trip across
`Mach` and `MachTB` (used for projected sub-place `TerminatorKind.drop`). -/
theorem encodeM_decodeM_mrPairU32 {M : Type} [Gen.Memory M] [MemoryOps M]
    (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    let v : Gen.Value M := .Tuple [.Int (intFromBits a u32), .Int (intFromBits b u32)]
    let bs : List (AbstractByte (Gen.Memory.Provenance M)) :=
      (leBytes a 4).map (fun x => .Init x none) ++ (leBytes b 4).map (fun x => .Init x none)
    Type.encodeM (M := M) mrPairU32Ty v = .ok bs ∧
    Type.decodeM (M := M) mrPairU32Ty bs = .ok (some v) := by
  intro v bs
  let bsA : List (AbstractByte (Gen.Memory.Provenance M)) := (leBytes a 4).map (fun x => .Init x none)
  let bsB : List (AbstractByte (Gen.Memory.Provenance M)) := (leBytes b 4).map (fun x => .Init x none)
  have hLenA : bsA.length = 4 := by dsimp only [bsA]; rw [List.length_map, leBytes_length]
  have hLenB : bsB.length = 4 := by dsimp only [bsB]; rw [List.length_map, leBytes_length]
  have hEncA : Type.encodeM (M := M) u32MrTy (.Int (intFromBits a u32)) = .ok bsA :=
    encodeIntM_intFromBits (M := M) u32 (by decide) a ha
  have hEncB : Type.encodeM (M := M) u32MrTy (.Int (intFromBits b u32)) = .ok bsB :=
    encodeIntM_intFromBits (M := M) u32 (by decide) b hb
  have hDecA : Type.decodeM (M := M) u32MrTy bsA = .ok (some (.Int (intFromBits a u32))) :=
    decodeIntM_leBytes (M := M) u32 (by decide) a ha
  have hDecB : Type.decodeM (M := M) u32MrTy bsB = .ok (some (.Int (intFromBits b u32))) :=
    decodeIntM_leBytes (M := M) u32 (by decide) b hb
  constructor
  · have hW1 : writeSubsliceAtIndex (List.replicate 8 (AbstractByte.Uninit : AbstractByte (Gen.Memory.Provenance M))) 0 bsA =
        .ok (bsA ++ List.replicate 4 .Uninit) :=
      writeSubsliceAtIndex_replicate_half1 .Uninit bsA 4 hLenA
    have hW2 : writeSubsliceAtIndex (bsA ++ List.replicate 4 (AbstractByte.Uninit : AbstractByte (Gen.Memory.Provenance M))) 4 bsB =
        .ok bs :=
      writeSubsliceAtIndex_replicate_half2 .Uninit bsA bsB 4 hLenA hLenB
    unfold mrPairU32Ty Type.encodeM
    dsimp only [v, TupleHeadLayout.head_size_and_align, List.length, ne_eq, not_true_eq_false, ↓reduceIte]
    unfold Type.encodeFieldsM
    rw [hEncA, ok_bind]
    change writeSubsliceAtIndex (List.replicate 8 .Uninit) 0 bsA >>=
      (fun buf => Type.encodeFieldsM [(⟨4⟩, u32MrTy)] [.Int (intFromBits b u32)] buf) = .ok bs
    rw [hW1, ok_bind]
    unfold Type.encodeFieldsM
    rw [hEncB, ok_bind]
    change writeSubsliceAtIndex (bsA ++ List.replicate 4 .Uninit) 4 bsB >>=
      (fun buf => Type.encodeFieldsM [] [] buf) = .ok bs
    rw [hW2, ok_bind]; rfl
  · have hLenAll : bs.length = (Size.align_to { bytes := 8 } { bytes := 4 }).bytes := by
      dsimp only [bs]; rw [List.length_append, hLenA, hLenB]; rfl
    have hSub0 : subsliceWithLength bs 0 (4 : Int) = .ok bsA :=
      subsliceWithLength_append_left bsA bsB 4 hLenA
    have hSub4 : subsliceWithLength bs 4 (4 : Int) = .ok bsB :=
      subsliceWithLength_append_right bsA bsB 4 hLenA hLenB
    unfold mrPairU32Ty Type.decodeM
    dsimp only [TupleHeadLayout.head_size_and_align]
    rw [ite_eq_right_iff.mpr (fun hn => absurd hLenAll hn)]
    unfold Type.decodeFieldsM
    dsimp only [Type.layout, LayoutStrategy.expect_size, u32MrTy, u32, bind, Except.bind]
    change (subsliceWithLength bs 0 (4 : Int) >>= fun s0 =>
      Type.decodeM u32MrTy s0 >>= fun o0 =>
      match o0 with
      | none => pure none
      | some v0 =>
        Type.decodeFieldsM [(⟨4⟩, u32MrTy)] bs >>= fun rest =>
        pure (rest.map (v0 :: ·))) >>= (fun o =>
          match o with | some vals => pure (some (Gen.Value.Tuple vals)) | none => pure none) = .ok (some v)
    rw [hSub0, ok_bind, hDecA, ok_bind]
    unfold Type.decodeFieldsM
    dsimp only [Type.layout, LayoutStrategy.expect_size, u32MrTy, u32, bind, Except.bind]
    change ((subsliceWithLength bs 4 (4 : Int) >>= fun s1 =>
      Type.decodeM u32MrTy s1 >>= fun o1 =>
      match o1 with
      | none => pure none
      | some v1 =>
        Type.decodeFieldsM [] bs >>= fun rest =>
        pure (rest.map (v1 :: ·))) >>= fun rest =>
      pure (rest.map (Gen.Value.Int (intFromBits a u32) :: ·))) >>= (fun o =>
        match o with | some vals => pure (some (Gen.Value.Tuple vals)) | none => pure none) = .ok (some v)
    rw [hSub4, ok_bind, hDecB, ok_bind]; rfl

private theorem evalUnOpM_thin_getMeta {M : Type} [Gen.Memory M] [MemoryOps M]
    (thin : ThinPointer (Gen.Memory.Provenance M)) (m : Option (Machine M)) :
    evalUnOpM (M := M) .GetMetadata (.Ptr (ThinPointer.widen thin none), thinRawPtrTy) m =
      .ok (.Tuple [], unitType) := rfl

private theorem evalUnOpM_wide_getThin {M : Type} [Gen.Memory M] [MemoryOps M]
    (thin : ThinPointer (Gen.Memory.Provenance M)) (len : Int) (m : Option (Machine M)) :
    evalUnOpM (M := M) .GetThinPointer (mrWidePtrValM thin len, wideSlicePtrMrTy) m =
      .ok (.Ptr (ThinPointer.widen thin none), thinRawPtrTy) := rfl

private theorem evalUnOpM_wide_getMeta {M : Type} [Gen.Memory M] [MemoryOps M]
    (thin : ThinPointer (Gen.Memory.Provenance M)) (len : Int) (m : Option (Machine M))
    (hChkLen : checkValueM (M := M) (.Int len) (.Int IntType.usize_ty) m = .ok ()) :
    evalUnOpM (M := M) .GetMetadata (mrWidePtrValM thin len, wideSlicePtrMrTy) m =
      .ok (.Int len, usizeMrTy) := by
  change (match checkValueM (M := M) (Gen.Value.Int len) (Gen.Type.Int IntType.usize_ty) m with
    | Except.ok () => Except.ok (Gen.Value.Int len, Gen.Type.Int IntType.usize_ty)
    | Except.error _ => specPanic "GetMetadata: sanity check, returned meta is well-formed") =
    Except.ok (Gen.Value.Int len, Gen.Type.Int IntType.usize_ty)
  rw [hChkLen]

private theorem evalUnOpM_u32_size_align {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Option (Machine M)) :
    evalUnOpM (M := M) (.ComputeSize u32MrTy) (.Tuple [], unitType) m = .ok (.Int 4, usizeMrTy) ∧
    evalUnOpM (M := M) (.ComputeAlign u32MrTy) (.Tuple [], unitType) m = .ok (.Int 4, usizeMrTy) := by
  have hLayU32 : Type.layout u32MrTy = .ok (.Sized ⟨4⟩ ⟨4⟩) := rfl
  constructor
  · cases m <;> (
      unfold evalUnOpM
      simp only [Type.meta_kind, u32MrTy, u32, PointerMetaKind.decode_valueM]
      rw [show Type.layout (.Int { signed := .Unsigned, size := { bytes := 4 } }) = .ok (.Sized ⟨4⟩ ⟨4⟩) from hLayU32]
      simp only [computeSizeM, LayoutStrategy.compute_size_and_align,
        bind, Except.bind, pure, Except.pure, Functor.map, Except.map, usizeMrTy]; rfl)
  · cases m <;> (
      unfold evalUnOpM
      simp only [Type.meta_kind, u32MrTy, u32, PointerMetaKind.decode_valueM]
      rw [show Type.layout (.Int { signed := .Unsigned, size := { bytes := 4 } }) = .ok (.Sized ⟨4⟩ ⟨4⟩) from hLayU32]
      simp only [computeAlignM, LayoutStrategy.compute_size_and_align,
        bind, Except.bind, pure, Except.pure, Functor.map, Except.map, usizeMrTy]; rfl)

private theorem evalUnOpM_sliceU32_size_align {M : Type} [Gen.Memory M] [MemoryOps M]
    (len : Nat) (m : Option (Machine M)) :
    evalUnOpM (M := M) (.ComputeSize (.Slice u32MrTy)) (.Int (len : Int), usizeMrTy) m =
      .ok (.Int ((4 * len : Nat) : Int), usizeMrTy) ∧
    evalUnOpM (M := M) (.ComputeAlign (.Slice u32MrTy)) (.Int (len : Int), usizeMrTy) m =
      .ok (.Int 4, usizeMrTy) := by
  have hLaySliceU32 : Type.layout (.Slice u32MrTy) = .ok (.Slice ⟨4⟩ ⟨4⟩) := rfl
  have hNn4 : (0 : Int) ≤ (len : Int) * ((4 : Nat) : Int) :=
    Int.mul_nonneg (Int.natCast_nonneg len) (by decide)
  have hToNat4 : ((len : Int) * ((4 : Nat) : Int)).toNat = 4 * len := by
    rw [← Int.natCast_mul, Int.toNat_natCast, Nat.mul_comm]
  constructor
  · cases m <;> (
      unfold evalUnOpM
      simp only [Type.meta_kind, PointerMetaKind.decode_valueM]
      rw [hLaySliceU32]
      simp only [computeSizeM, LayoutStrategy.compute_size_and_align, hNn4, ↓reduceIte, hToNat4,
        bind, Except.bind, pure, Except.pure, Functor.map, Except.map, usizeMrTy])
  · cases m <;> (
      unfold evalUnOpM
      simp only [Type.meta_kind, PointerMetaKind.decode_valueM]
      rw [hLaySliceU32]
      simp only [computeAlignM, LayoutStrategy.compute_size_and_align, hNn4, ↓reduceIte,
        bind, Except.bind, pure, Except.pure, Functor.map, Except.map, usizeMrTy]; rfl)

private theorem evalUnOpM_sliceU8_size_align {M : Type} [Gen.Memory M] [MemoryOps M]
    (len : Nat) (m : Option (Machine M)) :
    evalUnOpM (M := M) (.ComputeSize (.Slice u8MrTy)) (.Int (len : Int), usizeMrTy) m =
      .ok (.Int (len : Int), usizeMrTy) ∧
    evalUnOpM (M := M) (.ComputeAlign (.Slice u8MrTy)) (.Int (len : Int), usizeMrTy) m =
      .ok (.Int 1, usizeMrTy) := by
  have hLaySliceU8 : Type.layout (.Slice u8MrTy) = .ok (.Slice ⟨1⟩ ⟨1⟩) := rfl
  have hNn1 : (0 : Int) ≤ (len : Int) * ((1 : Nat) : Int) :=
    Int.mul_nonneg (Int.natCast_nonneg len) (by decide)
  have hToNat1 : ((len : Int) * ((1 : Nat) : Int)).toNat = len := by
    rw [← Int.natCast_mul, Int.toNat_natCast, Nat.mul_one]
  constructor
  · cases m <;> (
      unfold evalUnOpM
      simp only [Type.meta_kind, PointerMetaKind.decode_valueM]
      rw [hLaySliceU8]
      simp only [computeSizeM, LayoutStrategy.compute_size_and_align, hNn1, ↓reduceIte, hToNat1,
        bind, Except.bind, pure, Except.pure, Functor.map, Except.map, usizeMrTy])
  · cases m <;> (
      unfold evalUnOpM
      simp only [Type.meta_kind, PointerMetaKind.decode_valueM]
      rw [hLaySliceU8]
      simp only [computeAlignM, LayoutStrategy.compute_size_and_align, hNn1, ↓reduceIte,
        bind, Except.bind, pure, Except.pure, Functor.map, Except.map, usizeMrTy]; rfl)

/-- `Classical.choice`-free polymorphic Episode-1 `UnOp.GetMetadata` /
`ComputeSize` / `ComputeAlign` characterization for constructed thin (`*const u32`)
and wide (`*const [u32]`, `*const str`) raw pointers across BOTH `Mach` and
`MachTB`! -/
theorem evalUnOpM_rawPtr_meta_size_align {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr len : Nat) (hAddr : addr < 2 ^ 64) (hLen : len < 2 ^ 64)
    (prov : Option (Gen.Memory.Provenance M)) (m : Option (Machine M)) :
    let thin : ThinPointer (Gen.Memory.Provenance M) := { addr := addr, provenance := prov }
    let vThin : Gen.Value M := .Ptr (ThinPointer.widen thin none)
    let vWide : Gen.Value M := mrWidePtrValM thin (len : Int)
    evalUnOpM (M := M) .GetMetadata (vThin, thinRawPtrTy) m = .ok (.Tuple [], unitType) ∧
    evalUnOpM (M := M) (.ComputeSize u32MrTy) (.Tuple [], unitType) m = .ok (.Int 4, usizeMrTy) ∧
    evalUnOpM (M := M) (.ComputeAlign u32MrTy) (.Tuple [], unitType) m = .ok (.Int 4, usizeMrTy) ∧
    evalUnOpM (M := M) .GetThinPointer (vWide, wideSlicePtrMrTy) m = .ok (vThin, thinRawPtrTy) ∧
    evalUnOpM (M := M) .GetMetadata (vWide, wideSlicePtrMrTy) m = .ok (.Int (len : Int), usizeMrTy) ∧
    evalUnOpM (M := M) (.ComputeSize (.Slice u32MrTy)) (.Int (len : Int), usizeMrTy) m =
      .ok (.Int ((4 * len : Nat) : Int), usizeMrTy) ∧
    evalUnOpM (M := M) (.ComputeAlign (.Slice u32MrTy)) (.Int (len : Int), usizeMrTy) m =
      .ok (.Int 4, usizeMrTy) ∧
    evalUnOpM (M := M) (.ComputeSize (.Slice u8MrTy)) (.Int (len : Int), usizeMrTy) m =
      .ok (.Int (len : Int), usizeMrTy) ∧
    evalUnOpM (M := M) (.ComputeAlign (.Slice u8MrTy)) (.Int (len : Int), usizeMrTy) m =
      .ok (.Int 1, usizeMrTy) :=
  let _ := hAddr
  let thin : ThinPointer (Gen.Memory.Provenance M) := { addr := addr, provenance := prov }
  let hU32 := evalUnOpM_u32_size_align (M := M) m
  let hChkLen := checkValueM_int_of_inBounds (M := M) (len : Int) IntType.usize_ty m (inBounds_usize_cf len hLen)
  let hS32 := evalUnOpM_sliceU32_size_align (M := M) len m
  let hS8 := evalUnOpM_sliceU8_size_align (M := M) len m
  ⟨evalUnOpM_thin_getMeta (M := M) thin m, hU32.1, hU32.2,
   evalUnOpM_wide_getThin (M := M) thin (len : Int) m,
   evalUnOpM_wide_getMeta (M := M) thin (len : Int) m hChkLen,
   hS32.1, hS32.2, hS8.1, hS8.2⟩

/-! ## §1 (`V1`): `StatementKind.coverage` (`Mach` & `MachTB`) -/

/-- **V1 Universal Step Simulation & Fault-Equivalence (`v1_coverage_universal_sim`)**:
`StatementKind.coverage` takes a silent `.tau` step advancing only `stmtIdx` with
unchanged locals and memory; prepending any number of `.coverage` statements
preserves both normal returns (`runA`) and faults (`faultsA`). -/
theorem v1_coverage_universal_sim (body : CapturedMir) (bb : BasicBlockData)
    (s : MachineState) (span : String) (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (hPhase : (s.memory.activeCallee.getD body).phase = .runtimePostCleanup)
    (hBb : get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx = some bb)
    (hSt : get? bb.statements s.frame.stmtIdx = some { kind := .coverage, span := span }) :
    translateStatement decls { kind := .coverage, span := span } layouts = none ∧
    evalStmt s { kind := .coverage, span := span } decls layouts =
      MirStepNode.step (advanceStmt s s.frame.locals) ∧
    stepMirFn body s = .tau (.running (advanceStmt s s.frame.locals)) ∧
    (advanceStmt s s.frame.locals).frame.locals = s.frame.locals ∧
    (advanceStmt s s.frame.locals).memory = s.memory :=
  have h := coverage_stuttering_step body bb s span decls layouts hPhase hBb hSt
  ⟨rfl, h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- V1 positive body (`coverage; _0 = 17; return`). -/
def v1CoverageOkMir : CapturedMir := c4CoverageMir

/-- V1 UB body (`coverage; unreachable`) exercising fault equivalence after coverage. -/
def v1CoverageUbMir : CapturedMir :=
  mkMirBody "ep2::v1_coverage_ub" [mkDecl u32MirTy] 0
    [mkBb [mkSt .coverage] .unreachable]

/-- MiniRust erased counterpart for `v1CoverageOkMir` (returns `17 : u32`). -/
def v1CoverageOkMach : Mach :=
  let fn := mkMrFn [(localName 0, u32MrTy)] [] (localName 0)
    [(bbName 0, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 17) u32MrTy)], .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)]) [mkStackAlloc 128 (List.replicate 4 .Uninit) 4]
    [mkRootFrame fn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]]

/-- MiniRust erased counterpart for `v1CoverageUbMir` (`Unreachable` UB). -/
def v1CoverageUbMach : Mach :=
  let fn := mkMrFn [(localName 0, u32MrTy)] [] (localName 0)
    [(bbName 0, ⟨[], .Unreachable, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)]) [mkStackAlloc 128 (List.replicate 4 .Uninit) 4]
    [mkRootFrame fn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]]

/-- **V1 Concrete Positive & UB Witnesses (`Mach` & `MachTB` with `MachTB.wfLive`)**. -/
theorem v1_coverage_positive_and_ub_witness :
    runAVal v1CoverageOkMir 4 (initMachineState v1CoverageOkMir []) = some (.scalar ⟨17, 4⟩) ∧
    (∃ m1, Interp.step v1CoverageOkMach = .ok m1 ∧
      m1.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes u32 17)) ∧
    (∃ m1, Interp.stepTB (liftMachToTB v1CoverageOkMach) = .ok m1 ∧ MachTB.wfLive m1 ∧
      m1.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes u32 17).map (projByteTB ∘ liftByteTB))) ∧
    faultsA v1CoverageUbMir 4 (initMachineState v1CoverageUbMir []) = true ∧
    Interp.step v1CoverageUbMach = .error (.ub "reached unreachable code") ∧
    Interp.stepTB (liftMachToTB v1CoverageUbMach) = .error (.ub "reached unreachable code") :=
  ⟨rfl, ok_of_map_toOption (by decide +kernel), ok_stepTB_wfLive (by decide +kernel),
   rfl, eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel)⟩

/-! ## §2 (`V2`): `StatementKind.backwardIncompatibleDropHint` (`Mach` & `MachTB`) -/

/-- **V2 Universal Step Simulation (`v2_dropHint_universal_sim`)**:
`StatementKind.backwardIncompatibleDropHint p` unconditionally takes a silent `.tau`
step advancing `stmtIdx` with unchanged locals and memory, even when `p` refers to
a dead, uninitialized, or out-of-bounds local. -/
theorem v2_dropHint_universal_sim (body : CapturedMir) (bb : BasicBlockData)
    (s : MachineState) (p : MirAst.Place) (span : String)
    (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (hPhase : (s.memory.activeCallee.getD body).phase = .runtimePostCleanup)
    (hBb : get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx = some bb)
    (hSt : get? bb.statements s.frame.stmtIdx =
      some { kind := .backwardIncompatibleDropHint p, span := span }) :
    translateStatement decls { kind := .backwardIncompatibleDropHint p, span := span } layouts = none ∧
    evalStmt s { kind := .backwardIncompatibleDropHint p, span := span } decls layouts =
      MirStepNode.step (advanceStmt s s.frame.locals) ∧
    stepMirFn body s = .tau (.running (advanceStmt s s.frame.locals)) ∧
    (advanceStmt s s.frame.locals).frame.locals = s.frame.locals ∧
    (advanceStmt s s.frame.locals).memory = s.memory :=
  have h := backwardIncompatibleDropHint_stuttering_step body bb s p span decls layouts hPhase hBb hSt
  ⟨rfl, h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- V2 positive body: drop hint on dead local `_1`, OOB local `_99`, and uninit `_0`, then `_0 = 23`. -/
def v2DropHintOkMir : CapturedMir := c5DropHintMir

/-- V2 UB contrast body: drop hint on dead local `_1` succeeds, then reading dead `_1` faults UB. -/
def v2DropHintDeadReadUbMir : CapturedMir :=
  mkMirBody "ep2::v2_drophint_ub" [mkDecl u32MirTy, mkDecl u32MirTy] 0
    [mkBb [mkSt (.storageDead 1),
           mkSt (.backwardIncompatibleDropHint (locPlace 1)),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1))))] .return_]

/-- MiniRust erased counterpart for `v2DropHintOkMir` (returns `23 : u32`). -/
def v2DropHintOkMach : Mach :=
  let fn := mkMrFn [(localName 0, u32MrTy)] [] (localName 0)
    [(bbName 0, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 23) u32MrTy)], .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)]) [mkStackAlloc 128 (List.replicate 4 .Uninit) 4]
    [mkRootFrame fn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]]

/-- MiniRust erased counterpart for `v2DropHintDeadReadUbMir`: `StorageDead _1`, then load `_1` (UB). -/
def v2DropHintUbMach : Mach :=
  let fn := mkMrFn [(localName 0, u32MrTy), (localName 1, u32MrTy)] [] (localName 0)
    [(bbName 0, ⟨[.StorageDead (localName 1),
                  .Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
                 .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4, mkStackAlloc 256 (scalarBytes u32 9) 4]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]]

/-- **V2 Concrete Positive & Dead-Read UB Contrast Witness (`Mach` & `MachTB`)**. -/
theorem v2_dropHint_positive_and_ub_witness :
    runAVal v2DropHintOkMir 8 (initMachineState v2DropHintOkMir []) = some (.scalar ⟨23, 4⟩) ∧
    (∃ m1, Interp.step v2DropHintOkMach = .ok m1 ∧
      m1.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes u32 23)) ∧
    (∃ m1, Interp.stepTB (liftMachToTB v2DropHintOkMach) = .ok m1 ∧ MachTB.wfLive m1 ∧
      m1.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes u32 23).map (projByteTB ∘ liftByteTB))) ∧
    faultsA v2DropHintDeadReadUbMir 6 (initMachineState v2DropHintDeadReadUbMir []) = true ∧
    Interp.steps 2 v2DropHintUbMach = .error (.ub "access to a dead local") ∧
    Interp.stepsTB 2 (liftMachToTB v2DropHintUbMach) = .error (.ub "access to a dead local") :=
  ⟨rfl, ok_of_map_toOption (by decide +kernel), ok_stepTB_wfLive (by decide +kernel),
   rfl, eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel)⟩

/-! ## §3 (`V3`): `TerminatorKind.drop` (`Mach` & `MachTB`) -/

/-- **V3 Fragment Boundary (`translateTerminator_drop_none`)**:
`Translate.translateTerminator` returns `none` on `TerminatorKind.drop`. -/
theorem translateTerminator_drop_none (layouts : LayoutTable) (decls : List MirAst.LocalDecl)
    (place : MirAst.Place) (target : BasicBlockIdx) (unwind : MirAst.UnwindAction) (span : String) :
    translateTerminator layouts decls { kind := .drop place target unwind, span := span } = none := rfl

/-- **V3 Universal Trusted `TerminatorKind.drop` Operational Law
(`trusted_drop_universal_laws`)**: Characterizes all four branches of
`MirSemantics.evalTerminator s (.drop place target unwind)`:
1. Dead local (`get? locals loc = some .dead`) -> `MirStepNode.fail .ub`.
2. Bare live local (`proj = []`, no active protectors) -> sets `loc` to `.uninit`,
   invalidates conflicting borrows, and transitions to `(target, 0)`.
3. Bare live local with active protector conflict (`hasProtectedWriteConflict = true`)
   -> `MirStepNode.fail .ub`.
4. Projected field-0 drop on initialized 2-field aggregate `.aggregate 0 [v0, v1]`
   (no active protectors) -> sets field `0` to `.uninit` while preserving sibling
   field `1` (`v1`) and transitions to `(target, 0)`. -/
theorem trusted_drop_universal_laws (s : MachineState) (loc target : Nat)
    (unwind : MirAst.UnwindAction) (span : String) (currentBody : Option CapturedMir) :
    (get? s.frame.locals loc = some .dead →
      MirSemantics.evalTerminator s { kind := .drop (locPlace loc) target unwind, span := span } currentBody =
        MirStepNode.fail .ub) ∧
    (∀ slot locals',
      get? s.frame.locals loc = some slot → slot ≠ .dead →
      set? s.frame.locals loc .uninit = some locals' →
      s.memory.activeProtectors = [] →
      MirSemantics.evalTerminator s { kind := .drop (locPlace loc) target unwind, span := span } currentBody =
        MirStepNode.step {
          s with
          frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
          memory := { s.memory with
            borrows := invalidateConflictingBorrows s.memory.borrows loc .none
              (length s.memory.callStack) } }) ∧
    (∀ slot locals' pHead pTail,
      get? s.frame.locals loc = some slot → slot ≠ .dead →
      set? s.frame.locals loc .uninit = some locals' →
      s.memory.activeProtectors = pHead :: pTail →
      hasProtectedWriteConflict s.memory.borrows (pHead :: pTail) loc .none .nil 0 0
        (length s.memory.callStack) = true →
      MirSemantics.evalTerminator s { kind := .drop (locPlace loc) target unwind, span := span } currentBody =
        MirStepNode.fail .ub) ∧
    (∀ v0 v1 locals' fTy,
      get? s.frame.locals loc = some (.init (.aggregate 0 [v0, v1])) →
      set? s.frame.locals loc (.init (.aggregate 0 [.uninit, v1])) = some locals' →
      s.memory.activeProtectors = [] →
      let bodyLocalDecls := bodyLocalDeclsOf currentBody
      let bodyLayouts := match currentBody with | some b => b.layouts | none => emptyLayoutTable
      placeTouchesUnion bodyLocalDecls bodyLayouts (locPlace loc [.field 0 fTy]) = false →
      MirSemantics.evalTerminator s { kind := .drop (locPlace loc [.field 0 fTy]) target unwind, span := span }
        currentBody =
        MirStepNode.step {
          s with
          frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
          memory := { s.memory with
            borrows := invalidateConflictingBorrowsAtProj s.memory.borrows loc .none
              (resolveBorrowWriteLocalProj bodyLocalDecls bodyLayouts s.frame.locals loc [.field 0 fTy])
              0 0 (length s.memory.callStack) } }) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hDead; simp only [MirSemantics.evalTerminator, locPlace, hDead]
  · intro slot locals' hGet hNe hSet hProt
    cases slot with
    | dead => exact absurd rfl hNe
    | uninit => simp only [MirSemantics.evalTerminator, locPlace, hGet, hSet, hProt]
    | init _ => simp only [MirSemantics.evalTerminator, locPlace, hGet, hSet, hProt]
  · intro slot locals' pHead pTail hGet hNe hSet hProt hConf
    cases slot with
    | dead => exact absurd rfl hNe
    | uninit => simp only [MirSemantics.evalTerminator, locPlace, hGet, hSet, hProt, hConf]
    | init _ => simp only [MirSemantics.evalTerminator, locPlace, hGet, hSet, hProt, hConf]
  · intro v0 v1 locals' fTy hGet hSet hProt bodyLocalDecls bodyLayouts hNoUnion
    have hDeinit : deinitProjectedForLocal s.frame.locals bodyLocalDecls bodyLayouts loc
        (.aggregate 0 [v0, v1]) [.field 0 fTy] = .ok (.aggregate 0 [.uninit, v1]) := by
      unfold deinitProjectedForLocal
      simp only [hNoUnion, Bool.false_eq_true, ↓reduceIte, deinitProjectedValue,
        get?, set?, writeProjectedValue]; rfl
    unfold MirSemantics.evalTerminator
    dsimp only [locPlace]
    rw [hGet]
    change (match deinitProjectedForLocal s.frame.locals bodyLocalDecls bodyLayouts loc
        (.aggregate 0 [v0, v1]) [.field 0 fTy] with
      | .ok rootVal' => _
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported) = _
    rw [hDeinit]
    dsimp only []
    rw [hSet, hProt]
    rfl

/-- **V3 Polymorphic MiniRust `Deinit` Lockstep Law (`Mach` & `MachTB`)**:
Executing `Statement.Deinit place` on any live aligned sized place writes
`List.replicate sz.bytes .Uninit` via `ConcurrentMemory.deinit`. -/
theorem minirust_deinit_step_and_wfLive {M : Type} [Gen.Memory M] [MemoryOps M]
    (m m1 : Machine M) (pe : Gen.PlaceExpr) (pl : Gen.Place M) (ty : Gen.Type)
    (sz : LibSpecr.Size) (al : LibSpecr.Align) (cm' : ConcurrentMemory M)
    (hPl : evalPlaceM m pe = .ok ((pl, ty), m1))
    (hAl : pl.aligned = true)
    (hLay : Type.layout ty = .ok (.Sized sz al))
    (hDeinit : ConcurrentMemory.deinit m1.mem pl.ptr.thin_pointer sz ⟨1⟩ = .ok cm') :
    evalStatementM m (.Deinit pe) = .ok { m1 with mem := cm' } := by
  unfold evalStatementM; dsimp only []
  rw [hPl, ok_bind, hAl]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hLay, ok_bind,
    expect_size_sized, hDeinit, pure, Except.pure, bind, Except.bind]

/-- **V3 `MachTB.wfLive` Preservation for `Deinit`**: on `TreeBorrowsMemory`, every
successful `Statement.Deinit` step (the MiniRust image of Anneal's deinitializing
`TerminatorKind.drop`) preserves `MachTB.wfLive`. -/
theorem minirust_deinit_step_tb_wfLive
    (m m1 : MachTB) (pe : Gen.PlaceExpr) (pl : Gen.Place TBM) (ty : Gen.Type)
    (sz : LibSpecr.Size) (al : LibSpecr.Align) (cm' : ConcurrentMemory TBM)
    (hwf : MachTB.wfLive m)
    (hPl : evalPlaceM m pe = .ok ((pl, ty), m1))
    (hAl : pl.aligned = true)
    (hLay : Type.layout ty = .ok (.Sized sz al))
    (hDeinit : ConcurrentMemory.deinit m1.mem pl.ptr.thin_pointer sz ⟨1⟩ = .ok cm') :
    evalStatementM m (.Deinit pe) = .ok { m1 with mem := cm' } ∧
    MachTB.wfLive { m1 with mem := cm' } :=
  have h := minirust_deinit_step_and_wfLive (M := TBM) m m1 pe pl ty sz al cm' hPl hAl hLay hDeinit
  ⟨h, evalStatementM_tb_wfLive hwf h⟩

/-- **V3 Universal Coupled Whole-Local Drop Lockstep (`Mach` & `MachTB`, with
`MachTB.wfLive`)**: for EVERY Trusted state whose dropped local `loc` is live and has
no active protectors, `TerminatorKind.drop (locPlace loc) target unwind` deinitializes
`loc` and jumps to `(target, 0)`; simultaneously, for EVERY `Mach` / `MachTB` whose
place `pe` evaluates to a live aligned sized place, the MiniRust image
`Statement.Deinit pe` succeeds on both memories (writing `Uninit` over the place) and
preserves `MachTB.wfLive`. -/
theorem v3_drop_whole_coupled_lockstep_and_wfLive (s : MachineState) (loc target : Nat)
    (unwind : MirAst.UnwindAction) (span : String) (currentBody : Option CapturedMir)
    (slot : LocalSlot) (locals' : List LocalSlot)
    (hGet : get? s.frame.locals loc = some slot) (hNe : slot ≠ .dead)
    (hSet : set? s.frame.locals loc .uninit = some locals')
    (hProt : s.memory.activeProtectors = [])
    (pe : Gen.PlaceExpr) (ty : Gen.Type) (sz : LibSpecr.Size) (al : LibSpecr.Align)
    (hLay : Type.layout ty = .ok (.Sized sz al))
    (mBM mBM1 : Mach) (plBM : Gen.Place BM) (cmBM : ConcurrentMemory BM)
    (hPlBM : evalPlaceM mBM pe = .ok ((plBM, ty), mBM1)) (hAlBM : plBM.aligned = true)
    (hDeBM : ConcurrentMemory.deinit mBM1.mem plBM.ptr.thin_pointer sz ⟨1⟩ = .ok cmBM)
    (mTB mTB1 : MachTB) (plTB : Gen.Place TBM) (cmTB : ConcurrentMemory TBM)
    (hwf : MachTB.wfLive mTB)
    (hPlTB : evalPlaceM mTB pe = .ok ((plTB, ty), mTB1)) (hAlTB : plTB.aligned = true)
    (hDeTB : ConcurrentMemory.deinit mTB1.mem plTB.ptr.thin_pointer sz ⟨1⟩ = .ok cmTB) :
    MirSemantics.evalTerminator s { kind := .drop (locPlace loc) target unwind, span := span } currentBody =
      MirStepNode.step {
        s with
        frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
        memory := { s.memory with
          borrows := invalidateConflictingBorrows s.memory.borrows loc .none
            (length s.memory.callStack) } } ∧
    evalStatementM mBM (.Deinit pe) = .ok { mBM1 with mem := cmBM } ∧
    evalStatementM mTB (.Deinit pe) = .ok { mTB1 with mem := cmTB } ∧
    MachTB.wfLive { mTB1 with mem := cmTB } :=
  have hTB := minirust_deinit_step_tb_wfLive mTB mTB1 pe plTB ty sz al cmTB hwf hPlTB hAlTB hLay hDeTB
  ⟨(trusted_drop_universal_laws s loc target unwind span currentBody).2.1 slot locals' hGet hNe hSet hProt,
   minirust_deinit_step_and_wfLive (M := BM) mBM mBM1 pe plBM ty sz al cmBM hPlBM hAlBM hLay hDeBM,
   hTB.1, hTB.2⟩

/-- V3 positive body: whole-local drop on `_1`, jump to `bb1`, assign `_0 = 42`, return. -/
def v3DropWholeOkMir : CapturedMir :=
  mkMirBody "ep2::v3_drop_whole_ok" [mkDecl u32MirTy, mkDecl u32MirTy] 1
    [mkBb [] (.drop (locPlace 1) 1 .continue_),
     mkBb [mkSt (.assign (locPlace 0) (.use (constU32 42)))] .return_]

/-- V3 projected-drop positive body: drop `_1.0` of `(u32, u32)`, jump to `bb1`,
read surviving sibling `_1.1` into `_0`, return (`99`). -/
def v3DropProjSiblingOkMir : CapturedMir :=
  mkMirBody "ep2::v3_drop_proj_sibling_ok" [mkDecl u32MirTy, mkDecl pairU32MirTy] 1
    [mkBb [] (.drop (locPlace 1 [.field 0 u32MirTy]) 1 .continue_),
     mkBb [mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1 [.field 1 u32MirTy]))))] .return_]

/-- V3 projected-drop post-drop read UB body: drop `_1.0`, jump to `bb1`, read dropped `_1.0` -> UB. -/
def v3DropProjReadDroppedUbMir : CapturedMir :=
  mkMirBody "ep2::v3_drop_proj_read_dropped_ub" [mkDecl u32MirTy, mkDecl pairU32MirTy] 1
    [mkBb [] (.drop (locPlace 1 [.field 0 u32MirTy]) 1 .continue_),
     mkBb [mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1 [.field 0 u32MirTy]))))] .return_]

/-- V3 dead-local drop UB body: `StorageDead _1`, then `Drop(_1)` -> UB. -/
def v3DropDeadUbMir : CapturedMir :=
  mkMirBody "ep2::v3_drop_dead_ub" [mkDecl u32MirTy, mkDecl u32MirTy] 1
    [mkBb [mkSt (.storageDead 1)] (.drop (locPlace 1) 1 .continue_),
     mkBb [mkSt (.assign (locPlace 0) (.use (constU32 42)))] .return_]

/-- V3 post-drop live-read body (phase-boundary witness!): drops `_1`, jumps to `bb1`, reads `_1`. -/
def v3DropPostReadMir : CapturedMir :=
  mkMirBody "ep2::v3_drop_post_read" [mkDecl u32MirTy, mkDecl u32MirTy] 1
    [mkBb [] (.drop (locPlace 1) 1 .continue_),
     mkBb [mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1))))] .return_]

/-- V3 protected-borrow drop body (mode sensitivity: `BasicMemory` succeeds vs. `TreeBorrows` UB!). -/
def v3DropProtectedMir : CapturedMir := v3DropWholeOkMir

/-- Initial Trusted `MachineState` for `v3DropProtectedMir` under `protectedMode = true`
(installing an active protector on borrow tag `1` of local `1`, matching MiniRust `Validate _ true`)
versus `protectedMode = false` (no active protectors, matching MiniRust `BasicMemory`). -/
def v3DropProtectedInitState (protectedMode : Bool) : MachineState :=
  let base := initMachineState v3DropProtectedMir [.scalar ⟨11, 4⟩]
  let bEntry : BorrowEntry :=
    { tag := 1, targetLocal := 1, targetProjection := [], perm := .active,
      rangeOffset := 0, rangeLen := 4, protector := if protectedMode then some 1 else none,
      parentTag := none, targetFrameDepth := 0, allocDead := false }
  { base with
    memory := { base.memory with
      borrows := [bEntry],
      activeProtectors := if protectedMode then [1] else [] } }

/-- MiniRust machine for `v3DropWholeOkMir` (`Deinit _1; Goto bb1; _0 = 42; Return`). -/
def v3DropWholeOkMach : Mach :=
  let fn := mkMrFn [(localName 0, u32MrTy), (localName 1, u32MrTy)] [localName 1] (localName 0)
    [(bbName 0, ⟨[.Deinit (.Local (localName 1))], .Goto (bbName 1), .Regular⟩),
     (bbName 1, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 42) u32MrTy)], .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4, mkStackAlloc 256 (scalarBytes u32 11) 4]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]]

/-- MiniRust machine for `v3DropProjSiblingOkMir` (`readField1 = true`, returns `99`)
and `v3DropProjReadDroppedUbMir` (`readField1 = false`, reads dropped field `0` -> UB). -/
def v3DropProjMach (readField1 : Bool) : Mach :=
  let fn := mkMrFn [(localName 0, u32MrTy), (localName 1, mrPairU32Ty)] [localName 1] (localName 0)
    [(bbName 0, ⟨[.Deinit (.Field (.Local (localName 1)) 0)], .Goto (bbName 1), .Regular⟩),
     (bbName 1, ⟨[.Assign (.Local (localName 0))
                    (.Load (.Field (.Local (localName 1)) (if readField1 then 1 else 0)))],
                 .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 256 (scalarBytes u32 11 ++ scalarBytes u32 99) 4]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]]

/-- MiniRust machine for `v3DropDeadUbMir` (`StorageDead _1; Deinit _1` -> UB). -/
def v3DropDeadUbMach : Mach :=
  let fn := mkMrFn [(localName 0, u32MrTy), (localName 1, u32MrTy)] [localName 1] (localName 0)
    [(bbName 0, ⟨[.StorageDead (localName 1), .Deinit (.Local (localName 1))],
                 .Goto (bbName 1), .Regular⟩),
     (bbName 1, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 42) u32MrTy)], .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4, mkStackAlloc 256 (scalarBytes u32 11) 4]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]]

/-- MiniRust machine for `v3DropProtectedMir` (genuine `Mach` vs. `MachTB` mode sensitivity!):
`Validate (.Local _2) true` installs a Tree Borrows protector on `&u32` pointing to `_1`
(`BasicMemory` ignores `Validate`, so `Deinit _1` succeeds and returns `42`; `TreeBorrowsMemory`
enforces the protector, so `Deinit _1` faults with Tree Borrows UB!). -/
def v3DropProtectedMach : Mach :=
  let fn := mkMrFn [(localName 0, u32MrTy), (localName 1, u32MrTy), (localName 2, refTy .not u32)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[.Validate (.Local (localName 2)) true,
                  .Deinit (.Local (localName 1))],
                 .Goto (bbName 1), .Regular⟩),
     (bbName 1, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 42) u32MrTy)], .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 256 (scalarBytes u32 11) 4,
     mkStackAlloc 384 (ptrBytes 256 (some (⟨1⟩, ()))) 8]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) }),
       (localName 2, { addr := 384, provenance := some (⟨2⟩, ()) })]]

/-- MiniRust phase-boundary machine for `v3DropPostReadMir`: when `deinitDrop = true`
(Anneal's deinitializing drop), `Deinit _1; Goto bb1; _0 = Load _1` faults UB; when
`deinitDrop = false` (canonical post-elaboration no-glue runtime nop), bare
`Goto bb1; _0 = Load _1` succeeds returning `11`. -/
def v3DropPhaseBoundaryMach (deinitDrop : Bool) : Mach :=
  let fn := mkMrFn [(localName 0, u32MrTy), (localName 1, u32MrTy)] [localName 1] (localName 0)
    [(bbName 0, ⟨if deinitDrop then [.Deinit (.Local (localName 1))] else [],
                 .Goto (bbName 1), .Regular⟩),
     (bbName 1, ⟨[.Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
                 .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4, mkStackAlloc 256 (scalarBytes u32 11) 4]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]]

/-- V3 cleanup-block unwind + post-drop target transition machine (`Mach` & `MachTB`):
callee enters cleanup via `StartUnwind`, runs `Deinit _1; Goto bb2`, executes `ResumeUnwind`,
and caller catches with `StopUnwind` before returning `42`. -/
def v3DropCleanupUnwindMach : Mach :=
  let calleeFn := mkMrFn [(localName 0, unitType), (localName 1, u32MrTy)] [localName 1] (localName 0)
    [(bbName 0, ⟨[], .StartUnwind (.Constant (.PointerWithoutProvenance 4096) thinRawPtrTy) (bbName 1), .Regular⟩),
     (bbName 1, ⟨[.Deinit (.Local (localName 1))], .Goto (bbName 2), .Cleanup⟩),
     (bbName 2, ⟨[], .ResumeUnwind, .Cleanup⟩)]
  let callerFn := mkMrFn [(localName 0, u32MrTy)] [] (localName 0)
    [(bbName 0, ⟨[], .Goto (bbName 1), .Regular⟩),
     (bbName 1, ⟨[], .StopUnwind (bbName 2), .Cleanup⟩),
     (bbName 2, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 42) u32MrTy)], .Return, .Regular⟩)]
  let callerFr := mkRootFrame callerFn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]
  let calleeFr : Frame :=
    { func := calleeFn,
      locals := ⟨[(localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]⟩,
      stack_pop_action := .BackToCaller (some (bbName 0)) (some (bbName 1)) dummyRetPtr,
      next_block := bbName 0, next_stmt := 0, extra := () }
  mkMrMach (mkMrProg [(fnName 0, callerFn), (fnName 1, calleeFn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4, mkStackAlloc 256 (scalarBytes u32 11) 4]
    [callerFr, calleeFr]

/-- Trusted cleanup-block drop-then-`unwindResume` witness body: drops `_1` in cleanup `bb0`,
transitions to `bb1`, then `unwindResume` pops back to caller's cleanup block `bb1` which
returns `42`. -/
def v3DropCleanupCalleeMir : CapturedMir :=
  mkMirBody "ep2::v3_drop_cleanup_callee" [mkDecl unitMirTy, mkDecl u32MirTy] 1
    [mkBb [] (.drop (locPlace 1) 1 .terminate) true,
     mkBb [] .unwindResume true]

def v3DropCleanupCallerMir : CapturedMir :=
  mkMirBody "ep2::v3_drop_cleanup_caller" [mkDecl u32MirTy] 0
    [mkBb [] (.goto 1),
     mkBb [mkSt (.assign (locPlace 0) (.use (constU32 42)))] .return_ true]

/-- **V3 Concrete Witness Suite (`Mach` & `MachTB` with `MachTB.wfLive`)**:
1. Whole-local drop -> `42` (and `_1` deinitialized to `Uninit`);
2. Projected drop `_1.0` -> sibling `_1.1 = 99` preserved, reading dropped `_1.0` UB;
3. Dead-local drop -> UB;
4. Active protector mode sensitivity: `BasicMemory` (`Mach`) succeeds (`42`),
   `TreeBorrowsMemory` (`MachTB`) faults with Tree Borrows protector UB (matching Trusted!);
5. Cleanup-block drop -> `unwindResume` -> caller cleanup -> `42` on Trusted, `Mach`, `MachTB`;
6. Explicit phase-boundary witness: `Deinit + Goto` faults UB on post-drop read (matching Trusted),
   whereas canonical no-glue bare `Goto` returns `11`. -/
theorem v3_drop_comprehensive_witness :
    -- 1. Whole-local drop
    runAVal v3DropWholeOkMir 5 (initMachineState v3DropWholeOkMir [.scalar ⟨11, 4⟩]) = some (.scalar ⟨42, 4⟩) ∧
    (∃ m3, Interp.steps 3 v3DropWholeOkMach = .ok m3 ∧
      (m3.mem.memory.allocations[0]?.map (fun a => a.data.map (projByteTB ∘ liftByteTB)),
       m3.mem.memory.allocations[1]?.map (fun a => a.data.map (projByteTB ∘ liftByteTB))) =
        (some ((scalarBytes u32 42).map (projByteTB ∘ liftByteTB)),
         some ((List.replicate 4 .Uninit).map (projByteTB ∘ liftByteTB)))) ∧
    (∃ m3, Interp.stepsTB 3 (liftMachToTB v3DropWholeOkMach) = .ok m3 ∧ MachTB.wfLive m3 ∧
      m3.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes u32 42).map (projByteTB ∘ liftByteTB))) ∧
    -- 2. Projected sub-place drop: sibling read succeeds, dropped field read faults UB
    runAVal v3DropProjSiblingOkMir 5
      (initMachineState v3DropProjSiblingOkMir [.aggregate 0 [.scalar ⟨11, 4⟩, .scalar ⟨99, 4⟩]]) =
      some (.scalar ⟨99, 4⟩) ∧
    (∃ m3, Interp.steps 3 (v3DropProjMach true) = .ok m3 ∧
      m3.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes u32 99)) ∧
    (∃ m3, Interp.stepsTB 3 (liftMachToTB (v3DropProjMach true)) = .ok m3 ∧ MachTB.wfLive m3 ∧
      m3.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes u32 99).map (projByteTB ∘ liftByteTB))) ∧
    faultsA v3DropProjReadDroppedUbMir 5
      (initMachineState v3DropProjReadDroppedUbMir [.aggregate 0 [.scalar ⟨11, 4⟩, .scalar ⟨99, 4⟩]]) =
      true ∧
    Interp.steps 3 (v3DropProjMach false) =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    Interp.stepsTB 3 (liftMachToTB (v3DropProjMach false)) =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    -- 3. Dead-local drop UB
    faultsA v3DropDeadUbMir 4 (initMachineState v3DropDeadUbMir [.scalar ⟨11, 4⟩]) = true ∧
    Interp.steps 2 v3DropDeadUbMach = .error (.ub "access to a dead local") ∧
    Interp.stepsTB 2 (liftMachToTB v3DropDeadUbMach) = .error (.ub "access to a dead local") ∧
    -- 4. Mode sensitivity: BasicMemory succeeds (42) vs. TreeBorrows protector UB
    runAVal v3DropProtectedMir 5 (v3DropProtectedInitState false) = some (.scalar ⟨42, 4⟩) ∧
    (∃ m4, Interp.steps 4 v3DropProtectedMach = .ok m4 ∧
      m4.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes u32 42)) ∧
    faultsA v3DropProtectedMir 5 (v3DropProtectedInitState true) = true ∧
    (interpUbMsg (Interp.stepsTB 4 (liftMachToTB v3DropProtectedMach))).isSome = true ∧
    -- 5. Cleanup-block drop -> unwindResume -> caller cleanup -> 42
    (let callerFr : SavedCallerFrame :=
      { callerBody := v3DropCleanupCallerMir,
        frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] },
        destination := locPlace 0, returnTarget := 0, returnUnwind := .cleanup 1 }
     let s0 : MachineState :=
       { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.scalar ⟨11, 4⟩)] },
         memory := { emptyMemory with callStack := [callerFr], activeCallee := some v3DropCleanupCalleeMir } }
     runAVal v3DropCleanupCallerMir 8 s0 = some (.scalar ⟨42, 4⟩)) ∧
    (∃ m6, Interp.steps 6 v3DropCleanupUnwindMach = .ok m6 ∧
      (m6.mem.memory.allocations[0]?.map (fun a => a.data.map (projByteTB ∘ liftByteTB)),
       m6.mem.memory.allocations[1]?.map (·.live)) =
        (some ((scalarBytes u32 42).map (projByteTB ∘ liftByteTB)), some false)) ∧
    (∃ m6, Interp.stepsTB 6 (liftMachToTB v3DropCleanupUnwindMach) = .ok m6 ∧ MachTB.wfLive m6 ∧
      m6.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes u32 42).map (projByteTB ∘ liftByteTB))) ∧
    -- 6. Explicit phase boundary: deinit drop faults UB on post-drop read vs. bare Goto returns 11
    faultsA v3DropPostReadMir 5 (initMachineState v3DropPostReadMir [.scalar ⟨11, 4⟩]) = true ∧
    Interp.steps 3 (v3DropPhaseBoundaryMach true) =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    (∃ m2, Interp.steps 2 (v3DropPhaseBoundaryMach false) = .ok m2 ∧
      m2.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes u32 11)) := by
  refine ⟨rfl,
    ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
    rfl,
    ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
    rfl,
    eq_error_ub_of_interpUbMsg (by decide +kernel),
    eq_error_ub_of_interpUbMsg (by decide +kernel),
    rfl,
    eq_error_ub_of_interpUbMsg (by decide +kernel),
    eq_error_ub_of_interpUbMsg (by decide +kernel),
    rfl,
    ok_of_map_toOption (by decide +kernel),
    rfl,
    by decide +kernel,
    eq_some_scalar_of_valAsScalar (by decide +kernel),
    ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
    rfl,
    eq_error_ub_of_interpUbMsg (by decide +kernel),
    ok_of_map_toOption (by decide +kernel)⟩

/-! ## §4 (`V4`): `Rvalue.shallowInitBox` (`Mach` & `MachTB`) -/

/-- **V4 Fragment Boundary (`translateRvalue_shallowInitBox_none`)**:
`Translate.translateRvalue` returns `none` on `Rvalue.shallowInitBox`. -/
theorem translateRvalue_shallowInitBox_none (layouts : LayoutTable) (decls : List MirAst.LocalDecl)
    (targetTy : Option MirAst.Ty) (op : MirAst.Operand) (contentTy : MirAst.Ty) :
    translateRvalue layouts decls targetTy (.shallowInitBox op contentTy) = none := rfl

/-- **V4 Universal `Rvalue.shallowInitBox` Step Simulation & Fail-Closed Boundaries
(`v4_shallowInitBox_universal_sim`)**:
1. Positive lockstep (`Mach` & `MachTB`): for EVERY 8-byte thin raw pointer
   `p` (`operandTy = some (.rawPtr ..)`), `evalRvalue ... (.shallowInitBox op u32)`
   returns `.ok (.ptr p 8)` without reading or writing pointee memory, matched
   by MiniRust `transmuteM` to BOTH `boxU32MrTy` (on aligned non-null live
   uninitialized allocations) and `thinRawPtrTy`!
2. Dead/uninit operand UB propagation (`evalUseRvalue = .ub` -> `evalShallowInitBox = .ub`).
3. Fail-closed `.unsupported` on non-raw-pointer operand (`u64` scalar) and on
   wrong pointer width (`sz ≠ 8`). -/
theorem v4_shallowInitBox_universal_sim (locals locals' : List LocalSlot) (op : MirAst.Operand)
    (mem mem' : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (p : ProvenancePtr)
    (addr : Nat) (hAddr : addr < 2 ^ 64) (hNonNull : addr ≠ 0) (hAlign : addr % 4 = 0)
    (provBM : Option Prov) (provTB : Option TreeBorrowsProvenance)
    (mBM : Mach) (mTB : MachTB) :
    (evalUseRvalue locals op mem decls emptyLayoutTable = .ok (.ptr p 8) locals' mem' →
      operandTy decls emptyLayoutTable op = some rawMutU8MirTy →
      ConcurrentMemory.dereferenceable mBM.mem { addr := addr, provenance := provBM } ⟨4⟩ = .ok () →
      ConcurrentMemory.dereferenceable mTB.mem { addr := addr, provenance := provTB } ⟨4⟩ = .ok () →
      evalRvalue locals (.shallowInitBox op u32MirTy) mem decls emptyLayoutTable =
        .ok (.ptr p 8) locals' mem' ∧
      transmuteM (M := BM) (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none))
        thinRawPtrTy boxU32MrTy (some mBM) =
        .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none)) ∧
      transmuteM (M := TBM) (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none))
        thinRawPtrTy boxU32MrTy (some mTB) =
        .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none))) ∧
    (evalUseRvalue locals op mem decls emptyLayoutTable = .ub →
      evalRvalue locals (.shallowInitBox op u32MirTy) mem decls emptyLayoutTable = .ub) ∧
    (∀ bits,
      evalUseRvalue locals op mem decls emptyLayoutTable = .ok (.scalar ⟨bits, 8⟩) locals' mem' →
      operandTy decls emptyLayoutTable op = some u64MirTy →
      evalRvalue locals (.shallowInitBox op u32MirTy) mem decls emptyLayoutTable = .unsupported) ∧
    (∀ sz, sz ≠ 8 →
      evalUseRvalue locals op mem decls emptyLayoutTable = .ok (.ptr p sz) locals' mem' →
      operandTy decls emptyLayoutTable op = some rawMutU8MirTy →
      evalRvalue locals (.shallowInitBox op u32MirTy) mem decls emptyLayoutTable = .unsupported) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hUse hTy hDerBM hDerTB
    refine ⟨?_,
      transmuteM_thinRawPtr_to_boxU32 (M := BM) addr hAddr hNonNull hAlign provBM mBM hDerBM,
      transmuteM_thinRawPtr_to_boxU32 (M := TBM) addr hAddr hNonNull hAlign provTB mTB hDerTB⟩
    show evalShallowInitBox locals op u32MirTy mem decls emptyLayoutTable = _
    unfold evalShallowInitBox; simp only [hUse, hTy, rawMutU8MirTy, layoutPointerBytes, emptyLayoutTable]
  · intro hUb
    show evalShallowInitBox locals op u32MirTy mem decls emptyLayoutTable = .ub
    unfold evalShallowInitBox; rw [hUb]
  · intro bits hUse hTy
    show evalShallowInitBox locals op u32MirTy mem decls emptyLayoutTable = .unsupported
    unfold evalShallowInitBox; simp only [hUse, hTy, u64MirTy]
  · intro sz hNe hUse hTy
    show evalShallowInitBox locals op u32MirTy mem decls emptyLayoutTable = .unsupported
    unfold evalShallowInitBox
    have hBeq : Nat.beq sz (layoutPointerBytes emptyLayoutTable) = false := by
      change Nat.beq sz 8 = false
      exact Bool.eq_false_iff.mpr (fun h => hNe (Nat.eq_of_beq_eq_true h))
    simp only [hUse, hTy, rawMutU8MirTy, hBeq]

/-- **V4 Exhaustive Branch Characterization of `Rvalue.shallowInitBox`
(`v4_shallowInitBox_exhaustive`)**: universally over EVERY operand, EVERY content
type, EVERY local-decl list and EVERY layout table (not just `*mut u8` / `u32` /
`emptyLayoutTable`):
1. The result never depends on `contentTy` (the pointee type is never consulted, so
   pointee memory is never read or written).
2. A pointer value of exactly `layoutPointerBytes layouts` bytes from an operand of
   ANY raw-pointer type `*mu T` is returned verbatim, with the operand's
   `locals'`/`mem'` threading.
3. The same holds when the operand type is unknown (`operandTy = none`), the only
   other accepting branch of Trusted.
4. A pointer of any other width is `.unsupported` (raw-pointer or unknown type).
5. ANY operand type whose kind is not `.rawPtr` is `.unsupported`, whatever the value.
6. ANY non-pointer value is `.unsupported`, whatever the operand type.
7. Operand `.ub` / `.unsupported` propagate unchanged. -/
theorem v4_shallowInitBox_exhaustive (locals : List LocalSlot) (op : MirAst.Operand)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable) :
    (∀ c1 c2 : MirAst.Ty,
      evalRvalue locals (.shallowInitBox op c1) mem decls layouts =
        evalRvalue locals (.shallowInitBox op c2) mem decls layouts) ∧
    (∀ contentTy mu t li p locals' mem',
      evalUseRvalue locals op mem decls layouts = .ok (.ptr p (layoutPointerBytes layouts)) locals' mem' →
      operandTy decls layouts op = some { kind := .rawPtr mu t, layoutIdx := li } →
      evalRvalue locals (.shallowInitBox op contentTy) mem decls layouts =
        .ok (.ptr p (layoutPointerBytes layouts)) locals' mem') ∧
    (∀ contentTy p locals' mem',
      evalUseRvalue locals op mem decls layouts = .ok (.ptr p (layoutPointerBytes layouts)) locals' mem' →
      operandTy decls layouts op = none →
      evalRvalue locals (.shallowInitBox op contentTy) mem decls layouts =
        .ok (.ptr p (layoutPointerBytes layouts)) locals' mem') ∧
    (∀ contentTy p sz locals' mem', sz ≠ layoutPointerBytes layouts →
      evalUseRvalue locals op mem decls layouts = .ok (.ptr p sz) locals' mem' →
      (operandTy decls layouts op = none ∨
        ∃ mu t li, operandTy decls layouts op = some { kind := .rawPtr mu t, layoutIdx := li }) →
      evalRvalue locals (.shallowInitBox op contentTy) mem decls layouts = .unsupported) ∧
    (∀ contentTy (ty : MirAst.Ty) v locals' mem', (∀ mu t, ty.kind ≠ .rawPtr mu t) →
      evalUseRvalue locals op mem decls layouts = .ok v locals' mem' →
      operandTy decls layouts op = some ty →
      evalRvalue locals (.shallowInitBox op contentTy) mem decls layouts = .unsupported) ∧
    (∀ contentTy v locals' mem', (∀ p sz, v ≠ .ptr p sz) →
      evalUseRvalue locals op mem decls layouts = .ok v locals' mem' →
      evalRvalue locals (.shallowInitBox op contentTy) mem decls layouts = .unsupported) ∧
    (∀ contentTy, evalUseRvalue locals op mem decls layouts = .ub →
      evalRvalue locals (.shallowInitBox op contentTy) mem decls layouts = .ub) ∧
    (∀ contentTy, evalUseRvalue locals op mem decls layouts = .unsupported →
      evalRvalue locals (.shallowInitBox op contentTy) mem decls layouts = .unsupported) := by
  have hBeqSelf : Nat.beq (layoutPointerBytes layouts) (layoutPointerBytes layouts) = true :=
    Nat.beq_refl _
  refine ⟨fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro contentTy mu t li p locals' mem' hUse hTy
    show evalShallowInitBox locals op contentTy mem decls layouts = _
    unfold evalShallowInitBox; simp only [hUse, hTy, hBeqSelf]
  · intro contentTy p locals' mem' hUse hTy
    show evalShallowInitBox locals op contentTy mem decls layouts = _
    unfold evalShallowInitBox; simp only [hUse, hTy, hBeqSelf]
  · intro contentTy p sz locals' mem' hNe hUse hTy
    have hBeq : Nat.beq sz (layoutPointerBytes layouts) = false :=
      Bool.eq_false_iff.mpr (fun h => hNe (Nat.eq_of_beq_eq_true h))
    show evalShallowInitBox locals op contentTy mem decls layouts = _
    unfold evalShallowInitBox
    rcases hTy with hTy | ⟨mu, t, li, hTy⟩ <;> simp only [hUse, hTy, hBeq]
  · intro contentTy ty v locals' mem' hKind hUse hTy
    show evalShallowInitBox locals op contentTy mem decls layouts = _
    unfold evalShallowInitBox
    rcases ty with ⟨kind, li⟩
    cases kind with
    | rawPtr mu t => exact absurd rfl (hKind mu t)
    | _ => simp only [hUse, hTy]
  · intro contentTy v locals' mem' hV hUse
    show evalShallowInitBox locals op contentTy mem decls layouts = _
    unfold evalShallowInitBox
    cases v with
    | ptr p sz => exact absurd rfl (hV p sz)
    | _ => simp only [hUse]; split <;> first | rfl | contradiction
  · intro contentTy hUb
    show evalShallowInitBox locals op contentTy mem decls layouts = _
    unfold evalShallowInitBox; rw [hUb]
  · intro contentTy hUns
    show evalShallowInitBox locals op contentTy mem decls layouts = _
    unfold evalShallowInitBox; rw [hUns]

/-- V4 positive body: `shallowInitBox` on thin `*mut u8` operand `_1` -> `Box<u32>`. -/
def v4ShallowInitBoxOkMir : CapturedMir :=
  mkMirBody "ep2::v4_shallow_init_box_ok" [mkDecl boxU32MirTy, mkDecl rawMutU8MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.shallowInitBox (.copy (locPlace 1)) u32MirTy))] .return_]

/-- V4 distinct secondary positive body: `shallowInitBox` on `*mut u32` -> `Box<u64>`
(distinct source pointee, distinct `contentTy`, and distinct allocation `5` / address `1024`). -/
def v4ShallowInitBoxDistinctOkMir : CapturedMir :=
  mkMirBody "ep2::v4_shallow_init_box_distinct_ok" [mkDecl boxU64MirTy, mkDecl rawMutU32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.shallowInitBox (.copy (locPlace 1)) u64MirTy))] .return_]

/-- MiniRust machine for `v4ShallowInitBoxDistinctOkMir`: converts a `*mut u32` pointing
to an uninitialized 8-byte allocation `5` at `1024` into `Box<u64>` (`boxU64MrTy`) without
reading or writing allocation `5`! -/
def v4ShallowInitBoxDistinctMach : Mach :=
  let fn := mkMrFn [(localName 0, boxU64MrTy), (localName 1, thinRawPtrTy)] [localName 1] (localName 0)
    [(bbName 0, ⟨[.Assign (.Local (localName 0))
                    (.UnOp (.Cast (.Transmute boxU64MrTy)) (.Load (.Local (localName 1))))],
                 .Return, .Regular⟩)]
  let locs : List (Gen.LocalName × Ptr) :=
    [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
     (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 8 .Uninit) 8,
     mkStackAlloc 256 (ptrBytes 1024 (some (⟨5⟩, ()))) 8,
     mkStackAlloc 384 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 512 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 768 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 1024 (List.replicate 8 .Uninit) 8]
    [mkRootFrame fn locs]

/-- V4 non-raw-ptr fail-closed `.unsupported` body (`u64` operand). -/
def v4ShallowInitBoxNonPtrUnsupMir : CapturedMir :=
  mkMirBody "ep2::v4_shallow_init_box_nonptr_unsup" [mkDecl boxU32MirTy, mkDecl u64MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.shallowInitBox (.copy (locPlace 1)) u32MirTy))] .return_]

/-- MiniRust `ShallowInitBox` machine parameterized by target pointer type (`boxU32MrTy` or
`thinRawPtrTy`), liveness/init of operand `_1`, and pointer address (`384` aligned live uninit
heap/stack buffer vs. `0` null pointer). Notice allocation `2` (the pointee at `384`) is
**completely uninitialized** (`List.replicate 4 .Uninit`) and remains untouched! -/
def v4ShallowInitBoxMach (dstTy : Gen.Type := boxU32MrTy)
    (srcLive : Bool := true) (srcInit : Bool := true) (ptrAddr : Nat := 384)
    (ptrProv : Option Prov := some (⟨2⟩, ())) : Mach :=
  let fn := mkMrFn [(localName 0, dstTy), (localName 1, thinRawPtrTy)] [localName 1] (localName 0)
    [(bbName 0, ⟨[.Assign (.Local (localName 0))
                    (.UnOp (.Cast (.Transmute dstTy)) (.Load (.Local (localName 1))))],
                 .Return, .Regular⟩)]
  let locs : List (Gen.LocalName × Ptr) :=
    (localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }) ::
    (if srcLive then [(localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })] else [])
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 8 .Uninit) 8,
     mkStackAlloc 256 (if srcInit then ptrBytes ptrAddr ptrProv else List.replicate 8 .Uninit) 8,
     mkStackAlloc 384 (List.replicate 4 .Uninit) 4]
    [mkRootFrame fn locs]

/-- **V4 Concrete Witness Suite (`Mach` & `MachTB` with `MachTB.wfLive`)**:
1. Positive `shallowInitBox` on uninitialized 4-byte pointee buffer: preserves pointer bytes and
   leaves uninitialized pointee untouched on Trusted, `Mach`, and `MachTB`;
2. Dead-local and uninitialized-operand UB equivalence across Trusted, `Mach`, and `MachTB`;
3. Fail-closed `.unsupported` on non-raw-ptr (`u64`) and wrong-width (`sz = 4`) operands;
4. Explicit `PtrType.Box` safe-pointer validity boundary: null pointer (`addr = 0`) faults with
   `"Value::Ptr: null safe pointer"` at `boxU32MrTy` while succeeding at `thinRawPtrTy` / Trusted! -/
theorem v4_shallowInitBox_comprehensive_witness :
    let ptrB := ptrBytes 384 (some (⟨2⟩, ()))
    -- 1. Positive: preserves pointer without touching uninit pointee allocation 2
    runAVal v4ShallowInitBoxOkMir 4
      (initMachineState v4ShallowInitBoxOkMir [.ptr { allocId := 2, offsetBytes := 0 } 8]) =
      some (.ptr { allocId := 2, offsetBytes := 0 } 8) ∧
    (∃ m1, Interp.step (v4ShallowInitBoxMach boxU32MrTy) = .ok m1 ∧
      (m1.mem.memory.allocations[0]?.map (fun a => a.data.map (projByteTB ∘ liftByteTB)),
       m1.mem.memory.allocations[2]?.map (fun a => a.data.map (projByteTB ∘ liftByteTB))) =
        (some (ptrB.map (projByteTB ∘ liftByteTB)),
         some ((List.replicate 4 .Uninit).map (projByteTB ∘ liftByteTB)))) ∧
    (∃ m1, Interp.stepTB (liftMachToTB (v4ShallowInitBoxMach boxU32MrTy)) = .ok m1 ∧
      MachTB.wfLive m1 ∧
      m1.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some (ptrB.map (projByteTB ∘ liftByteTB))) ∧
    -- 2. Dead operand UB & uninit operand UB
    stepMirFn v4ShallowInitBoxOkMir
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .dead] },
        memory := emptyMemory } = MirStepNode.fail .ub ∧
    Interp.step (v4ShallowInitBoxMach boxU32MrTy false true) = .error (.ub "access to a dead local") ∧
    Interp.stepTB (liftMachToTB (v4ShallowInitBoxMach boxU32MrTy false true)) =
      .error (.ub "access to a dead local") ∧
    stepMirFn v4ShallowInitBoxOkMir
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] },
        memory := emptyMemory } = MirStepNode.fail .ub ∧
    Interp.step (v4ShallowInitBoxMach boxU32MrTy true false) =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    Interp.stepTB (liftMachToTB (v4ShallowInitBoxMach boxU32MrTy true false)) =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    -- 3. Fail-closed `.unsupported` on non-raw-ptr (`u64`) and wrong pointer width (`sz = 4`)
    stepMirFn v4ShallowInitBoxNonPtrUnsupMir
      (initMachineState v4ShallowInitBoxNonPtrUnsupMir [.scalar ⟨384, 8⟩]) =
      MirStepNode.unsupported ∧
    stepMirFn v4ShallowInitBoxOkMir
      (initMachineState v4ShallowInitBoxOkMir [.ptr { allocId := 2, offsetBytes := 0 } 4]) =
      MirStepNode.unsupported ∧
    -- 4. Explicit `PtrType.Box` safe-pointer validity boundary (null ptr)
    Interp.step (v4ShallowInitBoxMach boxU32MrTy true true 0 none) =
      .error (.ub "Value::Ptr: null safe pointer") ∧
    (∃ m1, Interp.step (v4ShallowInitBoxMach thinRawPtrTy true true 0 none) = .ok m1 ∧
      m1.mem.memory.allocations[0]?.map (·.data) = some (ptrBytes 0 none)) :=
  ⟨rfl,
   ok_of_map_toOption (by decide +kernel),
   ok_stepTB_wfLive (by decide +kernel),
   rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   rfl,
   rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   ok_of_map_toOption (by decide +kernel)⟩

/-! ## §5 (`V5`): `Rvalue.wrapUnsafeBinder` (`Mach` & `MachTB`) -/

/-- **V5 Fragment Boundary (`translateRvalue_wrapUnsafeBinder_none`)**:
`Translate.translateRvalue` returns `none` on `Rvalue.wrapUnsafeBinder`. -/
theorem translateRvalue_wrapUnsafeBinder_none (layouts : LayoutTable) (decls : List MirAst.LocalDecl)
    (targetTy : Option MirAst.Ty) (op : MirAst.Operand) (binderTy : MirAst.Ty) :
    translateRvalue layouts decls targetTy (.wrapUnsafeBinder op binderTy) = none := rfl

/-- **V5 Universal `Rvalue.wrapUnsafeBinder` Step Simulation (`Mach` & `MachTB`)**:
Covers ALL branches of `evalWrapUnsafeBinder`:
1. Single-field `binderStructLayout?` wrapper struct `BinderU32`: wraps `u32` operand into
   `.aggregate 0 [.scalar ⟨bits, 4⟩]` (matched by MiniRust `transmuteM` into
   `mrBinderWrapperTy u32MrTy ⟨4⟩ ⟨4⟩`).
2. Single-field `BinderU32` identity when operand already has `BinderU32` type.
3. Transparent `bool` target (`binderBoolMirTy` in `ep2BinderLayouts`): `b ∈ {0, 1}` succeeds and
   `2 ≤ b < 256` faults `.ub` (`scalarValidRangeOk = false`), matching MiniRust `transmuteM_u8_to_bool`!
4. Single-field `binderStructLayout?` `NonZeroU8` wrapper struct (`binderNzU8MirTy`):
   `b = 0` faults `.ub` (`scalarValidRangeOk = false`) and `1 ≤ b < 256` wraps to
   `.aggregate 0 [.scalar ⟨b, 1⟩]`, matching MiniRust `transmuteM_u8_to_nonZeroU8` (`Mach` & `MachTB`)!
5. Unknown operand type (`operandTy = none`) with single-field `binderStructLayout?` -> `.unsupported`. -/
theorem v5_wrapUnsafeBinder_universal_sim (locals locals' : List LocalSlot) (op : MirAst.Operand)
    (mem mem' : MirSemantics.Memory) (bits b : Nat) (hBits : bits < 2 ^ 32) (hb : b < 256)
    (mBM : Option Mach) (mTB : Option MachTB) :
    let declsU32 := [mkDecl binderU32MirTy, mkDecl u32MirTy]
    let declsId := [mkDecl binderU32MirTy, mkDecl binderU32MirTy]
    let declsBool := [mkDecl binderBoolMirTy, mkDecl u8MirTy]
    let declsNz := [mkDecl binderNzU8MirTy, mkDecl u8MirTy]
    -- 1. Single-field BinderU32 wrap (`u32 → BinderU32`)
    (evalUseRvalue locals op mem declsU32 ep2BinderLayouts = .ok (.scalar ⟨bits, 4⟩) locals' mem' →
      operandTy declsU32 ep2BinderLayouts op = some u32MirTy →
      evalRvalue locals (.wrapUnsafeBinder op binderU32MirTy) mem declsU32 ep2BinderLayouts =
        .ok (.aggregate 0 [.scalar ⟨bits, 4⟩]) locals' mem' ∧
      transmuteM (M := BM) (.Int (intFromBits bits u32)) u32MrTy (mrBinderWrapperTy u32MrTy ⟨4⟩ ⟨4⟩) mBM =
        .ok (.Tuple [.Int (intFromBits bits u32)]) ∧
      transmuteM (M := TBM) (.Int (intFromBits bits u32)) u32MrTy (mrBinderWrapperTy u32MrTy ⟨4⟩ ⟨4⟩) mTB =
        .ok (.Tuple [.Int (intFromBits bits u32)])) ∧
    -- 2. Single-field BinderU32 identity when operand already has `BinderU32` type
    (evalUseRvalue locals op mem declsId ep2BinderLayouts = .ok (.aggregate 0 [.scalar ⟨bits, 4⟩]) locals' mem' →
      operandTy declsId ep2BinderLayouts op = some binderU32MirTy →
      evalRvalue locals (.wrapUnsafeBinder op binderU32MirTy) mem declsId ep2BinderLayouts =
        .ok (.aggregate 0 [.scalar ⟨bits, 4⟩]) locals' mem') ∧
    -- 3. Transparent `bool` binder target: valid `0/1` vs. invalid `2 ≤ b` UB
    ((b = 0 ∨ b = 1) →
      evalUseRvalue locals op mem declsBool ep2BinderLayouts = .ok (.scalar ⟨b, 1⟩) locals' mem' →
      evalRvalue locals (.wrapUnsafeBinder op binderBoolMirTy) mem declsBool ep2BinderLayouts =
        .ok (.scalar ⟨b, 1⟩) locals' mem' ∧
      transmuteM (M := BM) (.Int (Int.ofNat b)) u8MrTy .Bool mBM = .ok (.Bool (b == 1)) ∧
      transmuteM (M := TBM) (.Int (Int.ofNat b)) u8MrTy .Bool mTB = .ok (.Bool (b == 1))) ∧
    (2 ≤ b →
      evalUseRvalue locals op mem declsBool ep2BinderLayouts = .ok (.scalar ⟨b, 1⟩) locals' mem' →
      evalRvalue locals (.wrapUnsafeBinder op binderBoolMirTy) mem declsBool ep2BinderLayouts = .ub ∧
      transmuteM (M := BM) (.Int (Int.ofNat b)) u8MrTy .Bool mBM =
        .error (.ub "transmuted value is not valid at new type") ∧
      transmuteM (M := TBM) (.Int (Int.ofNat b)) u8MrTy .Bool mTB =
        .error (.ub "transmuted value is not valid at new type")) ∧
    -- 4. Single-field `NonZeroU8` binder struct: `0` UB vs. `1 ≤ b` wrap
    (evalUseRvalue locals op mem declsNz ep2BinderLayouts = .ok (.scalar ⟨0, 1⟩) locals' mem' →
      operandTy declsNz ep2BinderLayouts op = some u8MirTy →
      evalRvalue locals (.wrapUnsafeBinder op binderNzU8MirTy) mem declsNz ep2BinderLayouts = .ub ∧
      transmuteM (M := BM) (.Int 0) u8MrTy nonZeroU8MrTy mBM =
        .error (.ub "transmuted value is not valid at new type") ∧
      transmuteM (M := TBM) (.Int 0) u8MrTy nonZeroU8MrTy mTB =
        .error (.ub "transmuted value is not valid at new type")) ∧
    (1 ≤ b →
      evalUseRvalue locals op mem declsNz ep2BinderLayouts = .ok (.scalar ⟨b, 1⟩) locals' mem' →
      operandTy declsNz ep2BinderLayouts op = some u8MirTy →
      evalRvalue locals (.wrapUnsafeBinder op binderNzU8MirTy) mem declsNz ep2BinderLayouts =
        .ok (.aggregate 0 [.scalar ⟨b, 1⟩]) locals' mem' ∧
      transmuteM (M := BM) (.Int (Int.ofNat b)) u8MrTy nonZeroU8MrTy mBM =
        .ok (.Variant 0 (.Int (Int.ofNat b))) ∧
      transmuteM (M := TBM) (.Int (Int.ofNat b)) u8MrTy nonZeroU8MrTy mTB =
        .ok (.Variant 0 (.Int (Int.ofNat b)))) ∧
    -- 5. Unknown operand type with `binderStructLayout?` -> `.unsupported`
    (∀ v, evalUseRvalue locals op mem [] ep2BinderLayouts = .ok v locals' mem' →
      operandTy [] ep2BinderLayouts op = none →
      evalRvalue locals (.wrapUnsafeBinder op binderU32MirTy) mem [] ep2BinderLayouts = .unsupported) := by
  intro declsU32 declsId declsBool declsNz
  have hBndU32 : binderStructLayout? declsU32 ep2BinderLayouts binderU32MirTy = some binderU32MirLayout := rfl
  have hBndId : binderStructLayout? declsId ep2BinderLayouts binderU32MirTy = some binderU32MirLayout := rfl
  have hBndBool : binderStructLayout? declsBool ep2BinderLayouts binderBoolMirTy = none := rfl
  have hResBool : resolvedTyLayout? declsBool ep2BinderLayouts binderBoolMirTy = some boolScalarMirLayout := rfl
  have hBndNz : binderStructLayout? declsNz ep2BinderLayouts binderNzU8MirTy = some nonZeroU8MirLayout := rfl
  have hBndNil : binderStructLayout? [] ep2BinderLayouts binderU32MirTy = some binderU32MirLayout := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hUse hTy
    have hRange : scalarValidRangeOk binderU32MirLayout (.scalar ⟨bits, 4⟩) = true := by
      unfold scalarValidRangeOk binderU32MirLayout wrappingRangeContains
      have hLe : Nat.ble bits 0xffffffff = true := Nat.ble_eq.mpr (Nat.le_of_lt_succ hBits)
      simp [hLe]
    refine ⟨?_,
      (transmuteM_binderWrapper_u32_and_thinPtr (M := BM) bits 0 hBits (by decide) none mBM).2.1,
      (transmuteM_binderWrapper_u32_and_thinPtr (M := TBM) bits 0 hBits (by decide) none mTB).2.1⟩
    show evalWrapUnsafeBinder locals op binderU32MirTy mem declsU32 ep2BinderLayouts = _
    unfold evalWrapUnsafeBinder; simp only [hUse, hBndU32, hTy, hRange]
  · intro hUse hTy
    show evalWrapUnsafeBinder locals op binderU32MirTy mem declsId ep2BinderLayouts = _
    unfold evalWrapUnsafeBinder; simp only [hUse, hBndId, hTy, scalarValidRangeOk]; rfl
  · intro hb01 hUse
    rcases hb01 with rfl | rfl <;> (
      refine ⟨?_, rfl, rfl⟩
      show evalWrapUnsafeBinder locals op binderBoolMirTy mem declsBool ep2BinderLayouts = _
      unfold evalWrapUnsafeBinder; simp only [hUse, hBndBool, hResBool]; rfl)
  · intro hGe hUse
    have hRangeFalse : scalarValidRangeOk boolScalarMirLayout (.scalar ⟨b, 1⟩) = false := by
      unfold scalarValidRangeOk boolScalarMirLayout wrappingRangeContains
      have hNotLe : Nat.ble b 1 = false := by
        cases b with
        | zero => exact absurd hGe (by decide)
        | succ k => cases k with | zero => exact absurd hGe (by decide) | succ _ => rfl
      simp [hNotLe]
    refine ⟨?_, (transmuteM_u8_to_bool b hb mBM).2.2 hGe, (transmuteM_u8_to_bool b hb mTB).2.2 hGe⟩
    show evalWrapUnsafeBinder locals op binderBoolMirTy mem declsBool ep2BinderLayouts = .ub
    unfold evalWrapUnsafeBinder; simp only [hUse, hBndBool, hResBool, hRangeFalse]
  · intro hUse hTy
    refine ⟨?_, rfl, rfl⟩
    show evalWrapUnsafeBinder locals op binderNzU8MirTy mem declsNz ep2BinderLayouts = .ub
    unfold evalWrapUnsafeBinder; simp only [hUse, hBndNz, hTy]; rfl
  · intro h1 hUse hTy
    have hRange : scalarValidRangeOk nonZeroU8MirLayout (.scalar ⟨b, 1⟩) = true := by
      unfold scalarValidRangeOk nonZeroU8MirLayout wrappingRangeContains
      have h1' : Nat.ble 1 b = true := Nat.ble_eq.mpr h1
      have h2' : Nat.ble b 255 = true := Nat.ble_eq.mpr (Nat.le_of_lt_succ hb)
      simp [h1', h2']
    refine ⟨?_, (transmuteM_u8_to_nonZeroU8 b hb mBM).2 h1, (transmuteM_u8_to_nonZeroU8 b hb mTB).2 h1⟩
    show evalWrapUnsafeBinder locals op binderNzU8MirTy mem declsNz ep2BinderLayouts = _
    unfold evalWrapUnsafeBinder; simp only [hUse, hBndNz, hTy, hRange]
  · intro v hUse hTy
    show evalWrapUnsafeBinder locals op binderU32MirTy mem [] ep2BinderLayouts = .unsupported
    unfold evalWrapUnsafeBinder; simp only [hUse, hBndNil, hTy]

/-- V5 transparent round-trip body: `wrapUnsafeBinder` (`u32 → u32`) then `unwrapUnsafeBinder` -> `73`. -/
def v5WrapTransparentRoundtripMir : CapturedMir :=
  mkMirBody "ep2::v5_wrap_transparent_rt" [mkDecl u32MirTy, mkDecl u32MirTy, mkDecl u32MirTy] 1
    [mkBb [mkSt (.storageLive 2),
           mkSt (.assign (locPlace 2) (.wrapUnsafeBinder (.copy (locPlace 1)) u32MirTy)),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 2 [.unwrapUnsafeBinder u32MirTy]))))]
      .return_]

/-- V5 single-field binder struct round-trip body: `wrapUnsafeBinder` (`u32 → BinderU32`) then
`unwrapUnsafeBinder` + `.field 0` -> `73`. -/
def v5WrapStructRoundtripMir : CapturedMir :=
  mkMirBody "ep2::v5_wrap_struct_rt" [mkDecl u32MirTy, mkDecl u32MirTy, mkDecl binderU32MirTy] 1
    [mkBb [mkSt (.storageLive 2),
           mkSt (.assign (locPlace 2) (.wrapUnsafeBinder (.copy (locPlace 1)) binderU32MirTy)),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 2 [.unwrapUnsafeBinder binderU32MirTy, .field 0 u32MirTy]))))]
      .return_]
    ep2BinderLayouts

/-- V5 `NonZeroU8` binder struct validity body (`u8 → BinderNonZeroU8`: `7` ok, `0` UB). -/
def v5WrapNzU8Mir : CapturedMir :=
  mkMirBody "ep2::v5_wrap_nzu8" [mkDecl binderNzU8MirTy, mkDecl u8MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.wrapUnsafeBinder (.copy (locPlace 1)) binderNzU8MirTy))] .return_]
    ep2BinderLayouts

/-- V5 transparent `bool` binder validity body (`u8 → bool`: `1` ok, `2` UB). -/
def v5WrapBoolMir : CapturedMir :=
  mkMirBody "ep2::v5_wrap_bool" [mkDecl binderBoolMirTy, mkDecl u8MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.wrapUnsafeBinder (.copy (locPlace 1)) binderBoolMirTy))] .return_]
    ep2BinderLayouts

/-- MiniRust wrap-and-unwrap round-trip machine (`mrBinderWrapperTy u32MrTy ⟨4⟩ ⟨4⟩`). -/
def v5WrapRoundtripMach (val : Nat := 73) : Mach :=
  let wrapTy := mrBinderWrapperTy u32MrTy ⟨4⟩ ⟨4⟩
  let fn := mkMrFn [(localName 0, u32MrTy), (localName 1, u32MrTy), (localName 2, wrapTy)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[.Assign (.Local (localName 2)) (.Tuple [.Load (.Local (localName 1))] wrapTy),
                  .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 2)) 0))],
                 .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 256 (scalarBytes u32 val) 4,
     mkStackAlloc 384 (List.replicate 4 .Uninit) 4]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) }),
       (localName 2, { addr := 384, provenance := some (⟨2⟩, ()) })]]

/-- **V5 Concrete Witness Suite (`Mach` & `MachTB` with `MachTB.wfLive`)**:
transparent & single-field `BinderU32` round-trips with `unwrapUnsafeBinder`,
`NonZeroU8` (`7` ok vs. `0` UB), and transparent `bool` (`1` ok vs. `2` UB). -/
theorem v5_wrapUnsafeBinder_comprehensive_witness :
    runAVal v5WrapTransparentRoundtripMir 6 (initMachineState v5WrapTransparentRoundtripMir [.scalar ⟨73, 4⟩]) =
      some (.scalar ⟨73, 4⟩) ∧
    runAVal v5WrapStructRoundtripMir 6 (initMachineState v5WrapStructRoundtripMir [.scalar ⟨73, 4⟩]) =
      some (.scalar ⟨73, 4⟩) ∧
    (∃ m2, Interp.steps 2 (v5WrapRoundtripMach 73) = .ok m2 ∧
      m2.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes u32 73)) ∧
    (∃ m2, Interp.stepsTB 2 (liftMachToTB (v5WrapRoundtripMach 73)) = .ok m2 ∧ MachTB.wfLive m2 ∧
      m2.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes u32 73).map (projByteTB ∘ liftByteTB))) ∧
    runAVal v5WrapNzU8Mir 4 (initMachineState v5WrapNzU8Mir [.scalar ⟨7, 1⟩]) =
      some (.aggregate 0 [.scalar ⟨7, 1⟩]) ∧
    (∃ m1, Interp.step (c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 7 none] 1) = .ok m1 ∧
      m1.mem.memory.allocations[0]?.map (·.data) = some [.Init 7 none]) ∧
    (∃ m1, Interp.stepTB (liftMachToTB (c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 7 none] 1)) = .ok m1 ∧
      MachTB.wfLive m1) ∧
    stepMirFn v5WrapNzU8Mir (initMachineState v5WrapNzU8Mir [.scalar ⟨0, 1⟩]) = MirStepNode.fail .ub ∧
    Interp.step (c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 0 none] 1) =
      .error (.ub "transmuted value is not valid at new type") ∧
    Interp.stepTB (liftMachToTB (c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 0 none] 1)) =
      .error (.ub "transmuted value is not valid at new type") ∧
    runAVal v5WrapBoolMir 4 (initMachineState v5WrapBoolMir [.scalar ⟨1, 1⟩]) = some (.scalar ⟨1, 1⟩) ∧
    stepMirFn v5WrapBoolMir (initMachineState v5WrapBoolMir [.scalar ⟨2, 1⟩]) = MirStepNode.fail .ub ∧
    Interp.step (c7MkTransmuteMach u8MrTy .Bool [.Init 2 none] 1) =
      .error (.ub "transmuted value is not valid at new type") ∧
    Interp.stepTB (liftMachToTB (c7MkTransmuteMach u8MrTy .Bool [.Init 2 none] 1)) =
      .error (.ub "transmuted value is not valid at new type") :=
  ⟨rfl, rfl,
   ok_of_map_toOption (by decide +kernel),
   ok_stepsTB_wfLive (by decide +kernel),
   rfl,
   ok_of_map_toOption (by decide +kernel),
   by obtain ⟨m1, hm1, hwf, _⟩ := ok_stepTB_wfLive (m := c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 7 none] 1) (f := fun _ => ()) (b := ()) (by decide +kernel); exact ⟨m1, hm1, hwf⟩,
   rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   rfl, rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel)⟩

/-! ## §6 (`V6`): `CastKind.subtype` (`Mach` & `MachTB`) -/

/-- **V6 Universal `CastKind.subtype` Equivalence with `.transmute` & Coupled Simulation**:
re-exports and packages `UnwindSetDiscrAndFnPtrMR`'s hypothesis-free `Classical.choice`-free
coupled simulation across `u32 → i32`, `*mut u32 → *const u32`, `u8 → bool`, and `u8 → NonZeroU8`
on `Mach` and `MachTB`. -/
theorem v6_subtype_eq_transmute_and_sim (locals : List LocalSlot) (op : MirAst.Operand)
    (dstTy : MirAst.Ty) (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl)
    (layouts : LayoutTable) :
    translateRvalue layouts decls none (.cast .subtype op dstTy) = none ∧
    evalRvalue locals (.cast .subtype op dstTy) mem decls layouts =
      evalRvalue locals (.cast .transmute op dstTy) mem decls layouts ∧
    evalRvalue locals (.cast .subtype op dstTy) mem decls layouts =
      evalByteCast locals op dstTy mem decls layouts :=
  ⟨rfl, rfl, rfl⟩

/-- **V6 Concrete Witness Suite (`Mach` & `MachTB` with `MachTB.wfLive`)**. -/
abbrev v6_subtype_comprehensive_witness := @c7_subtype_positive_and_invalid_ub_three_way_witness

/-! ## §7 (`V7`): `AggregateKind.rawPtr` (`Mach` & `MachTB`, with Episode 1 `GetMetadata`/`ComputeSize`/`ComputeAlign`) -/

/-- **V7 Fragment Boundary (`translateRvalue_aggregateRawPtr_none`)**:
`Translate.translateRvalue` returns `none` on `AggregateKind.rawPtr`. -/
theorem translateRvalue_aggregateRawPtr_none (layouts : LayoutTable) (decls : List MirAst.LocalDecl)
    (targetTy : Option MirAst.Ty) (pointeeTy : MirAst.Ty) (mutbl : MirAst.Mutability)
    (ops : List MirAst.Operand) :
    translateRvalue layouts decls targetTy (.aggregate (.rawPtr pointeeTy mutbl) ops) = none := rfl

/-- **V7 Universal `AggregateKind.rawPtr` Simulation (`Mach` & `MachTB`)**:
Couples Trusted `evalRvalue ... (.aggregate (.rawPtr pointeeTy mutbl) [dataOp, metaOp])`
directly with MiniRust `transmuteM` + Episode 1's `evalUnOpM (.GetMetadata / .ComputeSize / .ComputeAlign)`
across BOTH:
1. Thin raw pointers (`*const u32`, unit `()` metadata) -> `GetMetadata = ()`, `ComputeSize = 4`, `ComputeAlign = 4`;
2. Wide slice raw pointers (`*const [u32]`, `usize` metadata) -> `GetMetadata = len`, `ComputeSize = 4 * len`, `ComputeAlign = 4`;
3. Wide `str` raw pointers (`*const str`, `usize` metadata) -> `GetMetadata = len`, `ComputeSize = len`, `ComputeAlign = 1`;
4. Left-to-right operand UB propagation (`evalOperands = .ub` -> `evalAggregateRawPtr = .ub`);
5. Sized/unsized shape mismatch UB and `dyn Trait` + scalar metadata `.unsupported` boundary. -/
theorem v7_aggregateRawPtr_universal_sim (locals locals' : List LocalSlot)
    (dataOp metaOp : MirAst.Operand) (mem : MirSemantics.Memory)
    (decls : List MirAst.LocalDecl) (mutbl : MirAst.Mutability)
    (p : ProvenancePtr) (addr len : Nat) (hAddr : addr < 2 ^ 64) (hLen : len < 2 ^ 64)
    (provBM : Option Prov) (provTB : Option TreeBorrowsProvenance)
    (mBM : Option Mach) (mTB : Option MachTB) :
    let vThinBM : Gen.Value BM := .Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none)
    let vThinTB : Gen.Value TBM := .Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none)
    let vWideBM : Gen.Value BM := mrWidePtrValM { addr := addr, provenance := provBM } (len : Int)
    let vWideTB : Gen.Value TBM := mrWidePtrValM { addr := addr, provenance := provTB } (len : Int)
    -- 1. Thin raw pointer (`*const/*mut u32`) with `()` unit metadata
    (evalOperands locals [dataOp, metaOp] mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls mem.callStack =
        .ok [.ptr p 8, .unit] locals' →
      evalRvalue locals (.aggregate (.rawPtr u32MirTy mutbl) [dataOp, metaOp]) mem decls emptyLayoutTable =
        .ok (.ptr p 8) locals' mem ∧
      transmuteM (M := BM) (.Tuple [vThinBM, .Tuple []]) mrRawPtrThinPairTy thinRawPtrTy mBM = .ok vThinBM ∧
      transmuteM (M := TBM) (.Tuple [vThinTB, .Tuple []]) mrRawPtrThinPairTy thinRawPtrTy mTB = .ok vThinTB ∧
      evalUnOpM (M := BM) .GetMetadata (vThinBM, thinRawPtrTy) mBM = .ok (.Tuple [], unitType) ∧
      evalUnOpM (M := TBM) .GetMetadata (vThinTB, thinRawPtrTy) mTB = .ok (.Tuple [], unitType)) ∧
    -- 2. Wide slice raw pointer (`*const/*mut [u32]`) with `usize` element-count metadata + Episode 1 UnOps
    (evalOperands locals [dataOp, metaOp] mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls mem.callStack =
        .ok [.ptr p 8, .scalar ⟨len, 8⟩] locals' →
      evalRvalue locals (.aggregate (.rawPtr sliceU32MirTy mutbl) [dataOp, metaOp]) mem decls emptyLayoutTable =
        .ok (.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]) locals' mem ∧
      transmuteM (M := BM) (.Tuple [vThinBM, .Int (len : Int)]) mrRawPtrWidePairTy wideSlicePtrMrTy mBM = .ok vWideBM ∧
      transmuteM (M := TBM) (.Tuple [vThinTB, .Int (len : Int)]) mrRawPtrWidePairTy wideSlicePtrMrTy mTB = .ok vWideTB ∧
      evalUnOpM (M := BM) .GetMetadata (vWideBM, wideSlicePtrMrTy) mBM = .ok (.Int (len : Int), usizeMrTy) ∧
      evalUnOpM (M := TBM) .GetMetadata (vWideTB, wideSlicePtrMrTy) mTB = .ok (.Int (len : Int), usizeMrTy) ∧
      evalUnOpM (M := BM) (.ComputeSize (.Slice u32MrTy)) (.Int (len : Int), usizeMrTy) mBM =
        .ok (.Int ((4 * len : Nat) : Int), usizeMrTy) ∧
      evalUnOpM (M := TBM) (.ComputeSize (.Slice u32MrTy)) (.Int (len : Int), usizeMrTy) mTB =
        .ok (.Int ((4 * len : Nat) : Int), usizeMrTy)) ∧
    -- 3. Wide `str` raw pointer (`*const/*mut str`) with `usize` byte-count metadata + Episode 1 UnOps
    (evalOperands locals [dataOp, metaOp] mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls mem.callStack =
        .ok [.ptr p 8, .scalar ⟨len, 8⟩] locals' →
      evalRvalue locals (.aggregate (.rawPtr strMirTy mutbl) [dataOp, metaOp]) mem decls emptyLayoutTable =
        .ok (.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]) locals' mem ∧
      evalUnOpM (M := BM) (.ComputeSize (.Slice u8MrTy)) (.Int (len : Int), usizeMrTy) mBM =
        .ok (.Int (len : Int), usizeMrTy) ∧
      evalUnOpM (M := TBM) (.ComputeSize (.Slice u8MrTy)) (.Int (len : Int), usizeMrTy) mTB =
        .ok (.Int (len : Int), usizeMrTy) ∧
      evalUnOpM (M := BM) (.ComputeAlign (.Slice u8MrTy)) (.Int (len : Int), usizeMrTy) mBM =
        .ok (.Int 1, usizeMrTy) ∧
      evalUnOpM (M := TBM) (.ComputeAlign (.Slice u8MrTy)) (.Int (len : Int), usizeMrTy) mTB =
        .ok (.Int 1, usizeMrTy)) ∧
    -- 4. Dead/uninit operand UB propagation
    (∀ ptTy,
      evalOperands locals [dataOp, metaOp] mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls mem.callStack = .ub →
      evalRvalue locals (.aggregate (.rawPtr ptTy mutbl) [dataOp, metaOp]) mem decls emptyLayoutTable = .ub) ∧
    -- 5. Shape mismatch UB (sized pointee with scalar meta) & dyn-with-scalar-meta `.unsupported`
    (evalOperands locals [dataOp, metaOp] mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls mem.callStack =
        .ok [.ptr p 8, .scalar ⟨len, 8⟩] locals' →
      evalRvalue locals (.aggregate (.rawPtr u32MirTy mutbl) [dataOp, metaOp]) mem decls emptyLayoutTable = .ub ∧
      evalRvalue locals (.aggregate (.rawPtr { kind := .dynamic "ep2::Tr", layoutIdx := 0 } mutbl) [dataOp, metaOp])
        mem decls emptyLayoutTable = .unsupported) := by
  intro vThinBM vThinTB vWideBM vWideTB
  have hUnBM := evalUnOpM_rawPtr_meta_size_align (M := BM) addr len hAddr hLen provBM mBM
  have hUnTB := evalUnOpM_rawPtr_meta_size_align (M := TBM) addr len hAddr hLen provTB mTB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hOps
    refine ⟨?_,
      transmuteM_rawPtrThinPair_to_thinRawPtr (M := BM) addr hAddr provBM mBM,
      transmuteM_rawPtrThinPair_to_thinRawPtr (M := TBM) addr hAddr provTB mTB,
      hUnBM.1, hUnTB.1⟩
    show evalAggregateRawPtr locals u32MirTy [dataOp, metaOp] mem decls emptyLayoutTable = _
    unfold evalAggregateRawPtr; simp only [hOps, layoutPointerBytes, emptyLayoutTable, isUnsizedRawPtrPointee, u32MirTy]
  · intro hOps
    refine ⟨?_,
      transmuteM_rawPtrWidePair_to_wideSlicePtr (M := BM) addr len hAddr hLen provBM mBM,
      transmuteM_rawPtrWidePair_to_wideSlicePtr (M := TBM) addr len hAddr hLen provTB mTB,
      hUnBM.2.2.2.2.1, hUnTB.2.2.2.2.1, hUnBM.2.2.2.2.2.1, hUnTB.2.2.2.2.2.1⟩
    show evalAggregateRawPtr locals sliceU32MirTy [dataOp, metaOp] mem decls emptyLayoutTable = _
    unfold evalAggregateRawPtr; simp only [hOps, layoutPointerBytes, emptyLayoutTable, wideAggregatePointeeIsDyn?, sliceU32MirTy]; rfl
  · intro hOps
    refine ⟨?_, hUnBM.2.2.2.2.2.2.2.1, hUnTB.2.2.2.2.2.2.2.1, hUnBM.2.2.2.2.2.2.2.2, hUnTB.2.2.2.2.2.2.2.2⟩
    show evalAggregateRawPtr locals strMirTy [dataOp, metaOp] mem decls emptyLayoutTable = _
    unfold evalAggregateRawPtr; simp only [hOps, layoutPointerBytes, emptyLayoutTable, wideAggregatePointeeIsDyn?, strMirTy]; rfl
  · intro ptTy hUb
    show evalAggregateRawPtr locals ptTy [dataOp, metaOp] mem decls emptyLayoutTable = .ub
    unfold evalAggregateRawPtr; rw [hUb]
  · intro hOps
    refine ⟨?_, ?_⟩
    · show evalAggregateRawPtr locals u32MirTy [dataOp, metaOp] mem decls emptyLayoutTable = .ub
      unfold evalAggregateRawPtr; simp only [hOps, layoutPointerBytes, emptyLayoutTable, wideAggregatePointeeIsDyn?, u32MirTy]
    · show evalAggregateRawPtr locals { kind := .dynamic "ep2::Tr", layoutIdx := 0 } [dataOp, metaOp] mem decls emptyLayoutTable = .unsupported
      unfold evalAggregateRawPtr; simp only [hOps, layoutPointerBytes, emptyLayoutTable, wideAggregatePointeeIsDyn?]

/-- V7 thin raw pointer MIR body: builds `*const u32` from `(dataPtr, ())`. -/
def v7RawPtrThinMir : CapturedMir :=
  mkMirBody "ep2::v7_rawptr_thin" [mkDecl rawConstU32MirTy, mkDecl rawConstUnitMirTy, mkDecl unitMirTy] 2
    [mkBb [mkSt (.assign (locPlace 0) (.aggregate (.rawPtr u32MirTy .not) [.copy (locPlace 1), .copy (locPlace 2)]))] .return_]

/-- V7 wide slice raw pointer + `PtrMetadata` round-trip MIR body: builds `*const [u32]` from
`(dataPtr, len)` and extracts metadata via `Rvalue.unaryOp .ptrMetadata` (returns `len : usize`). -/
def v7RawPtrWideSliceMetaMir : CapturedMir :=
  mkMirBody "ep2::v7_rawptr_wide_slice" [mkDecl usizeMirTy, mkDecl rawConstUnitMirTy, mkDecl usizeMirTy, mkDecl rawConstSliceU32MirTy] 2
    [mkBb [mkSt (.storageLive 3),
           mkSt (.assign (locPlace 3) (.aggregate (.rawPtr sliceU32MirTy .not) [.copy (locPlace 1), .copy (locPlace 2)])),
           mkSt (.assign (locPlace 0) (.unaryOp .ptrMetadata (.copy (locPlace 3))))] .return_]

/-- V7 wide `str` raw pointer + `PtrMetadata` round-trip MIR body. -/
def v7RawPtrWideStrMetaMir : CapturedMir :=
  mkMirBody "ep2::v7_rawptr_wide_str" [mkDecl usizeMirTy, mkDecl rawConstUnitMirTy, mkDecl usizeMirTy, mkDecl rawConstStrMirTy] 2
    [mkBb [mkSt (.storageLive 3),
           mkSt (.assign (locPlace 3) (.aggregate (.rawPtr strMirTy .not) [.copy (locPlace 1), .copy (locPlace 2)])),
           mkSt (.assign (locPlace 0) (.unaryOp .ptrMetadata (.copy (locPlace 3))))] .return_]

/-- MiniRust thin `AggregateKind.rawPtr` machine executing `Transmute thinRawPtrTy (Tuple [data, ()])`,
then `UnOp.GetMetadata`, `UnOp.ComputeSize u32MrTy`, and `UnOp.ComputeAlign u32MrTy`. -/
def v7RawPtrThinMach (dataLive : Bool := true) (dataInit : Bool := true) : Mach :=
  let fn := mkMrFn
    [(localName 0, thinRawPtrTy), (localName 1, thinRawPtrTy), (localName 2, unitType),
     (localName 3, usizeMrTy), (localName 4, usizeMrTy)]
    [localName 1, localName 2] (localName 0)
    [(bbName 0, ⟨[
        .Assign (.Local (localName 0))
          (.UnOp (.Cast (.Transmute thinRawPtrTy))
            (.Tuple [.Load (.Local (localName 1)), .Load (.Local (localName 2))] mrRawPtrThinPairTy)),
        .Assign (.Local (localName 3))
          (.UnOp (.ComputeSize u32MrTy) (.UnOp .GetMetadata (.Load (.Local (localName 0))))),
        .Assign (.Local (localName 4))
          (.UnOp (.ComputeAlign u32MrTy) (.UnOp .GetMetadata (.Load (.Local (localName 0)))))],
      .Return, .Regular⟩)]
  let locs : List (Gen.LocalName × Ptr) :=
    (localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }) ::
    (if dataLive then [(localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })] else []) ++
    [(localName 2, { addr := 384, provenance := some (⟨2⟩, ()) }),
     (localName 3, { addr := 512, provenance := some (⟨3⟩, ()) }),
     (localName 4, { addr := 640, provenance := some (⟨4⟩, ()) })]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 8 .Uninit) 8,
     mkStackAlloc 256 (if dataInit then ptrBytes 1024 (some (⟨5⟩, ())) else List.replicate 8 .Uninit) 8,
     mkStackAlloc 384 [] 1,
     mkStackAlloc 512 (List.replicate 8 .Uninit) 8,
     mkStackAlloc 640 (List.replicate 8 .Uninit) 8,
     mkStackAlloc 1024 (scalarBytes u32 77) 4]
    [mkRootFrame fn locs]

/-- MiniRust wide slice/str `AggregateKind.rawPtr` machine executing
`Transmute wideSlicePtrMrTy (Tuple [data, len])`, then Episode 1's `UnOp.GetMetadata` (`_0`),
`UnOp.ComputeSize (.Slice elemTy)` (`_4`), and `UnOp.ComputeAlign (.Slice elemTy)` (`_5`)! -/
def v7RawPtrWideMach (elemTy : Gen.Type := u32MrTy) (len : Nat := 5)
    (dataLive : Bool := true) (metaLive : Bool := true) (metaInit : Bool := true) : Mach :=
  let fn := mkMrFn
    [(localName 0, usizeMrTy), (localName 1, thinRawPtrTy), (localName 2, usizeMrTy),
     (localName 3, wideSlicePtrMrTy), (localName 4, usizeMrTy), (localName 5, usizeMrTy)]
    [localName 1, localName 2] (localName 0)
    [(bbName 0, ⟨[
        .Assign (.Local (localName 3))
          (.UnOp (.Cast (.Transmute wideSlicePtrMrTy))
            (.Tuple [.Load (.Local (localName 1)), .Load (.Local (localName 2))] mrRawPtrWidePairTy)),
        .Assign (.Local (localName 0)) (.UnOp .GetMetadata (.Load (.Local (localName 3)))),
        .Assign (.Local (localName 4)) (.UnOp (.ComputeSize (.Slice elemTy)) (.Load (.Local (localName 0)))),
        .Assign (.Local (localName 5)) (.UnOp (.ComputeAlign (.Slice elemTy)) (.Load (.Local (localName 0))))],
      .Return, .Regular⟩)]
  let locs : List (Gen.LocalName × Ptr) :=
    (localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }) ::
    (if dataLive then [(localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })] else []) ++
    (if metaLive then [(localName 2, { addr := 384, provenance := some (⟨2⟩, ()) })] else []) ++
    [(localName 3, { addr := 512, provenance := some (⟨3⟩, ()) }),
     (localName 4, { addr := 640, provenance := some (⟨4⟩, ()) }),
     (localName 5, { addr := 768, provenance := some (⟨5⟩, ()) })]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 8 .Uninit) 8,
     mkStackAlloc 256 (ptrBytes 1024 (some (⟨6⟩, ()))) 8,
     mkStackAlloc 384 (if metaInit then scalarBytes IntType.usize_ty len else List.replicate 8 .Uninit) 8,
     mkStackAlloc 512 (List.replicate 16 .Uninit) 8,
     mkStackAlloc 640 (List.replicate 8 .Uninit) 8,
     mkStackAlloc 768 (List.replicate 8 .Uninit) 8,
     mkStackAlloc 1024 (List.replicate 20 .Uninit) 4]
    [mkRootFrame fn locs]

/-- **V7 Concrete Witness Suite (`Mach` & `MachTB` with `MachTB.wfLive`)**:
1. Thin `*const u32` from `(ptr, ())` + Episode 1 `GetMetadata`/`ComputeSize(4)`/`ComputeAlign(4)`;
2. Wide `*const [u32]` from `(ptr, 5)` + Episode 1 `GetMetadata(5)`/`ComputeSize(20)`/`ComputeAlign(4)`;
3. Wide `*const str` from `(ptr, 7)` + Episode 1 `GetMetadata(7)`/`ComputeSize(7)`/`ComputeAlign(1)`;
4. Dead data-ptr UB, dead metadata UB, and uninit metadata UB across Trusted, `Mach`, `MachTB`. -/
theorem v7_aggregateRawPtr_comprehensive_witness :
    let ptrB := ptrBytes 1024 (some (⟨5⟩, ()))
    -- 1. Thin raw pointer
    runAVal v7RawPtrThinMir 4
      (initMachineState v7RawPtrThinMir [.ptr { allocId := 5, offsetBytes := 0 } 8, .unit]) =
      some (.ptr { allocId := 5, offsetBytes := 0 } 8) ∧
    (∃ m3, Interp.steps 3 (v7RawPtrThinMach true true) = .ok m3 ∧
      (m3.mem.memory.allocations[0]?.map (fun a => a.data.map (projByteTB ∘ liftByteTB)),
       m3.mem.memory.allocations[3]?.map (fun a => a.data.map (projByteTB ∘ liftByteTB)),
       m3.mem.memory.allocations[4]?.map (fun a => a.data.map (projByteTB ∘ liftByteTB))) =
        (some (ptrB.map (projByteTB ∘ liftByteTB)),
         some ((scalarBytes IntType.usize_ty 4).map (projByteTB ∘ liftByteTB)),
         some ((scalarBytes IntType.usize_ty 4).map (projByteTB ∘ liftByteTB)))) ∧
    (∃ m3, Interp.stepsTB 3 (liftMachToTB (v7RawPtrThinMach true true)) = .ok m3 ∧ MachTB.wfLive m3 ∧
      m3.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some (ptrB.map (projByteTB ∘ liftByteTB))) ∧
    -- 2. Wide slice `[u32]` raw pointer + GetMetadata / ComputeSize / ComputeAlign
    runAVal v7RawPtrWideSliceMetaMir 6
      (initMachineState v7RawPtrWideSliceMetaMir [.ptr { allocId := 6, offsetBytes := 0 } 8, .scalar ⟨5, 8⟩]) =
      some (.scalar ⟨5, 8⟩) ∧
    (∃ m4, Interp.steps 4 (v7RawPtrWideMach u32MrTy 5) = .ok m4 ∧
      (m4.mem.memory.allocations[0]?.map (fun a => a.data.map (projByteTB ∘ liftByteTB)),
       m4.mem.memory.allocations[4]?.map (fun a => a.data.map (projByteTB ∘ liftByteTB)),
       m4.mem.memory.allocations[5]?.map (fun a => a.data.map (projByteTB ∘ liftByteTB))) =
        (some ((scalarBytes IntType.usize_ty 5).map (projByteTB ∘ liftByteTB)),
         some ((scalarBytes IntType.usize_ty 20).map (projByteTB ∘ liftByteTB)),
         some ((scalarBytes IntType.usize_ty 4).map (projByteTB ∘ liftByteTB)))) ∧
    (∃ m4, Interp.stepsTB 4 (liftMachToTB (v7RawPtrWideMach u32MrTy 5)) = .ok m4 ∧ MachTB.wfLive m4 ∧
      (m4.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB),
       m4.mem.memory.mem.allocations[4]?.map (fun a => a.data.map projByteTB)) =
        (some ((scalarBytes IntType.usize_ty 5).map (projByteTB ∘ liftByteTB)),
         some ((scalarBytes IntType.usize_ty 20).map (projByteTB ∘ liftByteTB)))) ∧
    -- 3. Wide `str` raw pointer + GetMetadata / ComputeSize / ComputeAlign
    runAVal v7RawPtrWideStrMetaMir 6
      (initMachineState v7RawPtrWideStrMetaMir [.ptr { allocId := 6, offsetBytes := 0 } 8, .scalar ⟨7, 8⟩]) =
      some (.scalar ⟨7, 8⟩) ∧
    (∃ m4, Interp.steps 4 (v7RawPtrWideMach u8MrTy 7) = .ok m4 ∧
      (m4.mem.memory.allocations[0]?.map (fun a => a.data.map (projByteTB ∘ liftByteTB)),
       m4.mem.memory.allocations[4]?.map (fun a => a.data.map (projByteTB ∘ liftByteTB)),
       m4.mem.memory.allocations[5]?.map (fun a => a.data.map (projByteTB ∘ liftByteTB))) =
        (some ((scalarBytes IntType.usize_ty 7).map (projByteTB ∘ liftByteTB)),
         some ((scalarBytes IntType.usize_ty 7).map (projByteTB ∘ liftByteTB)),
         some ((scalarBytes IntType.usize_ty 1).map (projByteTB ∘ liftByteTB)))) ∧
    -- 4. Dead data-ptr UB, dead metadata UB, and uninit metadata UB
    stepMirFn v7RawPtrThinMir
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .dead, .init .unit] },
        memory := emptyMemory } = MirStepNode.fail .ub ∧
    Interp.step (v7RawPtrThinMach false true) = .error (.ub "access to a dead local") ∧
    Interp.stepTB (liftMachToTB (v7RawPtrThinMach false true)) = .error (.ub "access to a dead local") ∧
    stepMirFn v7RawPtrWideSliceMetaMir
      { frame := { blockIdx := 0, stmtIdx := 1,
                   locals := [.uninit, .init (.ptr { allocId := 6, offsetBytes := 0 } 8), .dead, .uninit] },
        memory := emptyMemory } = MirStepNode.fail .ub ∧
    Interp.step (v7RawPtrWideMach u32MrTy 5 true false true) = .error (.ub "access to a dead local") ∧
    Interp.stepTB (liftMachToTB (v7RawPtrWideMach u32MrTy 5 true false true)) =
      .error (.ub "access to a dead local") ∧
    stepMirFn v7RawPtrWideSliceMetaMir
      { frame := { blockIdx := 0, stmtIdx := 1,
                   locals := [.uninit, .init (.ptr { allocId := 6, offsetBytes := 0 } 8), .uninit, .uninit] },
        memory := emptyMemory } = MirStepNode.fail .ub ∧
    Interp.step (v7RawPtrWideMach u32MrTy 5 true true false) =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    Interp.stepTB (liftMachToTB (v7RawPtrWideMach u32MrTy 5 true true false)) =
      .error (.ub "load at type but the data in memory violates the language invariant") :=
  ⟨rfl,
   ok_of_map_toOption (by decide +kernel),
   ok_stepsTB_wfLive (by decide +kernel),
   rfl,
   ok_of_map_toOption (by decide +kernel),
   ok_stepsTB_wfLive (by decide +kernel),
   rfl,
   ok_of_map_toOption (by decide +kernel),
   rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel)⟩

/-! ## §8 (`V8`): `AggregateKind.closure` (`Mach` & `MachTB`) -/

/-- **V8 Universal `AggregateKind.closure` Coupled Simulation (`Mach` & `MachTB`)**:
universally over EVERY capture list `ops` and EVERY MiniRust tuple image `es`:
1. `n`-capture lockstep: Trusted `.aggregate (.closure dp) ops` returns
   `.aggregate 0 vals` (length-preserving, `mem` untouched) exactly when MiniRust
   `ValueExpr.Tuple es` returns `.Tuple mvals` on BOTH `Mach` and `MachTB`;
2. left-to-right UB propagation at ANY index (prefix evaluated, first faulting
   upvar faults both sides, suffix never evaluated);
3. coupled `Assign` statement step with `MachTB.wfLive` preservation (re-exported
   `closure_assign_coupled_lockstep_and_wfLive`). -/
theorem v8_closure_universal_sim :
    (∀ (locals locals' : List LocalSlot) (dp : DefPath) (ops : List MirAst.Operand)
        (vals : List MirSemantics.Value) (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl)
        (layouts : LayoutTable) (m m' : Mach) (es : List Gen.ValueExpr) (mvals : List Val)
        (mrClTy : Gen.Type),
      evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals decls mem.callStack =
          .ok vals locals' → evalValuesM m es = .ok (mvals, m') →
        vals.length = ops.length ∧ mvals.length = es.length ∧
        evalRvalue locals (.aggregate (.closure dp) ops) mem decls layouts = .ok (.aggregate 0 vals) locals' mem ∧
        evalValueM m (.Tuple es mrClTy) = .ok ((.Tuple mvals, mrClTy), m')) ∧
    (∀ (locals locals' : List LocalSlot) (dp : DefPath) (ops : List MirAst.Operand)
        (vals : List MirSemantics.Value) (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl)
        (layouts : LayoutTable) (m m' : MachTB) (es : List Gen.ValueExpr) (mvals : List (Gen.Value TBM))
        (mrClTy : Gen.Type),
      evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals decls mem.callStack =
          .ok vals locals' → evalValuesM m es = .ok (mvals, m') →
        vals.length = ops.length ∧ mvals.length = es.length ∧
        evalRvalue locals (.aggregate (.closure dp) ops) mem decls layouts = .ok (.aggregate 0 vals) locals' mem ∧
        evalValueM m (.Tuple es mrClTy) = .ok ((.Tuple mvals, mrClTy), m')) ∧
    (∀ (locals : List LocalSlot) (dp : DefPath) (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl)
        (layouts : LayoutTable) (pre : List MirAst.Operand) (bad : MirAst.Operand) (suf : List MirAst.Operand)
        (preVals : List MirSemantics.Value) (localsMid : List LocalSlot)
        (m mMid : MachTB) (mpre : List Gen.ValueExpr) (mbad : Gen.ValueExpr) (msuf : List Gen.ValueExpr)
        (mpreVals : List (Gen.Value TBM)) (msg : String) (mrClTy : Gen.Type),
      evalOperands locals pre mem.borrows mem.globals layouts mem.callerLocals decls mem.callStack = .ok preVals localsMid →
      evalOperand localsMid bad mem.borrows mem.globals layouts mem.callerLocals decls mem.callStack = .ub →
      evalValuesM m mpre = .ok (mpreVals, mMid) → evalValueM mMid mbad = .error (.ub msg) →
      evalRvalue locals (.aggregate (.closure dp) (pre ++ bad :: suf)) mem decls layouts = .ub ∧
      evalValueM m (.Tuple (mpre ++ mbad :: msuf) mrClTy) = .error (.ub msg)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro locals locals' dp ops vals mem decls layouts m m' es mvals mrClTy hOps hEs
    exact (closure_n_capture_lockstep_M (M := BM) locals locals' dp ops vals mem decls layouts
      m m' es mvals mrClTy).1 hOps hEs
  · intro locals locals' dp ops vals mem decls layouts m m' es mvals mrClTy hOps hEs
    exact (closure_n_capture_lockstep_M (M := TBM) locals locals' dp ops vals mem decls layouts
      m m' es mvals mrClTy).1 hOps hEs
  · intro locals dp mem decls layouts pre bad suf preVals localsMid m mMid mpre mbad msuf mpreVals msg mrClTy
      hPre hBad hmPre hmBad
    exact (closure_n_capture_lockstep_M (M := TBM) locals locals dp [] [] mem decls layouts
      m m [] [] mrClTy).2 pre bad suf preVals localsMid mpre mbad msuf mpreVals mMid msg hPre hBad hmPre hmBad

/-- V8 coupled `Assign` step re-export (`MachTB.wfLive` preserved). -/
abbrev v8_closure_assign_coupled_lockstep_and_wfLive := @closure_assign_coupled_lockstep_and_wfLive

/-- V8 concrete witness suite re-export (`Mach` & `MachTB`). -/
abbrev v8_closure_comprehensive_witness := @c10_closure_zst_capture_and_ub_three_way_witness

/-! ## §8b. Value-Coupled (`Ep2ValRel`) Universal Simulations Across `Mach` & `MachTB`

Closes the value-relation link between Trusted `MirSemantics.Value` (including
`ProvenancePtr.allocId` / `offsetBytes`, wide metadata, scalars, and aggregates)
and MiniRust `Gen.Value M` (`BasicMemory` and `TreeBorrowsMemory`) via a single
allocation base-address map `allocBase : Nat → Nat` and provenance allocator ID
projection `provAllocId : Gen.Memory.Provenance M → Nat`. -/

mutual
/-- Value-coupling relation directly linking Trusted `MirSemantics.Value` to
MiniRust `Gen.Value M` across both `BasicMemory` (`BM`) and `TreeBorrowsMemory` (`TBM`),
enforcing bit-width bounds (`bits < 2 ^ (8 * sz)` for scalars, `metaVal < 2 ^ 64` for
wide metadata) so out-of-range Trusted scalars cannot relate to MiniRust integers. -/
inductive Ep2ValRel {M : Type} [Gen.Memory M]
    (allocBase : Nat → Nat) (provAllocId : Gen.Memory.Provenance M → Nat) :
    MirSemantics.Value → Gen.Value M → Prop where
  | scalar (bits sz : Nat) (hBound : bits < 2 ^ (8 * sz)) :
      Ep2ValRel allocBase provAllocId (.scalar ⟨bits, sz⟩) (.Int (Int.ofNat bits))
  | unit :
      Ep2ValRel allocBase provAllocId .unit (.Tuple [])
  | thinPtr (p : ProvenancePtr) (addr : Nat) (prov : Option (Gen.Memory.Provenance M))
      (hAddr : addr = allocBase p.allocId + p.offsetBytes)
      (hProv : prov.map provAllocId = some p.allocId) :
      Ep2ValRel allocBase provAllocId (.ptr p 8)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none))
  | widePtr (p : ProvenancePtr) (metaVal : Nat) (hMeta : metaVal < 2 ^ 64)
      (addr : Nat) (prov : Option (Gen.Memory.Provenance M))
      (hAddr : addr = allocBase p.allocId + p.offsetBytes)
      (hProv : prov.map provAllocId = some p.allocId) :
      Ep2ValRel allocBase provAllocId (.aggregate 0 [.ptr p 8, .scalar ⟨metaVal, 8⟩])
        (mrWidePtrValM (M := M) { addr := addr, provenance := prov } (Int.ofNat metaVal))
  /-- Struct/tuple/closure/binder-struct aggregates (Trusted variant index `0`) are
  MiniRust tuples. (A0/A1 accepted ANY variant index here, relating Trusted enum
  variants `.aggregate v _` with `v ≠ 0` to MiniRust `.Tuple`; MiniRust represents
  those as `.Variant`, see `enumVariant`.) -/
  | aggregate (vs : List MirSemantics.Value) (mvs : List (Gen.Value M))
      (hFields : Ep2ValListRel allocBase provAllocId vs mvs) :
      Ep2ValRel allocBase provAllocId (.aggregate 0 vs) (.Tuple mvs)
  /-- Single-payload enum variants (e.g. `NonZero<u8>`, whose MiniRust image is
  `.Variant 0 payload`): Trusted `.aggregate variant [v]` is MiniRust
  `.Variant variant mv`. -/
  | enumVariant (variant : Nat) (v : MirSemantics.Value) (mv : Gen.Value M)
      (hPayload : Ep2ValRel allocBase provAllocId v mv) :
      Ep2ValRel allocBase provAllocId (.aggregate variant [v]) (.Variant (Int.ofNat variant) mv)

inductive Ep2ValListRel {M : Type} [Gen.Memory M]
    (allocBase : Nat → Nat) (provAllocId : Gen.Memory.Provenance M → Nat) :
    List MirSemantics.Value → List (Gen.Value M) → Prop where
  | nil : Ep2ValListRel allocBase provAllocId [] []
  | cons {v vs mv mvs} :
      Ep2ValRel allocBase provAllocId v mv →
      Ep2ValListRel allocBase provAllocId vs mvs →
      Ep2ValListRel allocBase provAllocId (v :: vs) (mv :: mvs)
end

/-- **V4 Value-Coupled Universal Simulation (`v4_shallowInitBox_coupled_valRel_sim`)**:
for EVERY `M ∈ {BM, TBM}`, whenever a Trusted thin raw-pointer operand relates to
a MiniRust thin pointer value via `Ep2ValRel allocBase provAllocId` (preserving
exact `allocId`, `offsetBytes`, and base address), `evalRvalue (.shallowInitBox ..)`
and `transmuteM ... thinRawPtrTy boxU32MrTy` produce outputs STILL related by
`Ep2ValRel allocBase provAllocId`! -/
theorem v4_shallowInitBox_coupled_valRel_sim {M : Type} [Gen.Memory M] [MemoryOps M]
    (allocBase : Nat → Nat) (provAllocId : Gen.Memory.Provenance M → Nat)
    (locals locals' : List LocalSlot) (op : MirAst.Operand) (contentTy : MirAst.Ty)
    (mem mem' : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (hPtr8 : layoutPointerBytes layouts = 8)
    (p : ProvenancePtr) (mv : Gen.Value M) (m : Gen.Machine M)
    (hUse : evalUseRvalue locals op mem decls layouts = .ok (.ptr p 8) locals' mem')
    (hOpTy : operandTy decls layouts op = none ∨
      ∃ mu t li, operandTy decls layouts op = some { kind := .rawPtr mu t, layoutIdx := li })
    (hRel : Ep2ValRel allocBase provAllocId (.ptr p 8) mv)
    (hAddr : allocBase p.allocId + p.offsetBytes < 2 ^ 64)
    (hNonNull : allocBase p.allocId + p.offsetBytes ≠ 0)
    (hAlign : (allocBase p.allocId + p.offsetBytes) % 4 = 0)
    (hDer : ∀ prov, prov.map provAllocId = some p.allocId →
      ConcurrentMemory.dereferenceable m.mem
        { addr := allocBase p.allocId + p.offsetBytes, provenance := prov } ⟨4⟩ = .ok ()) :
    ∃ tv mv',
      evalRvalue locals (.shallowInitBox op contentTy) mem decls layouts = .ok tv locals' mem' ∧
      transmuteM (M := M) mv thinRawPtrTy boxU32MrTy (some m) = .ok mv' ∧
      Ep2ValRel allocBase provAllocId tv mv' := by
  cases hRel with
  | thinPtr _ addr prov hA hP =>
    subst hA
    have hExh := v4_shallowInitBox_exhaustive locals op mem decls layouts
    have hUse' : evalUseRvalue locals op mem decls layouts =
        .ok (.ptr p (layoutPointerBytes layouts)) locals' mem' := by rw [hPtr8]; exact hUse
    have hTr : evalRvalue locals (.shallowInitBox op contentTy) mem decls layouts =
        .ok (.ptr p 8) locals' mem' := by
      rw [← hPtr8]
      rcases hOpTy with hNone | ⟨mu, t, li, hSome⟩
      · exact hExh.2.2.1 contentTy p locals' mem' hUse' hNone
      · exact hExh.2.1 contentTy mu t li p locals' mem' hUse' hSome
    refine ⟨.ptr p 8, .Ptr (ThinPointer.widen { addr := allocBase p.allocId + p.offsetBytes, provenance := prov } none),
      hTr,
      transmuteM_thinRawPtr_to_boxU32 (M := M) (allocBase p.allocId + p.offsetBytes) hAddr hNonNull hAlign prov m (hDer prov hP),
      .thinPtr p (allocBase p.allocId + p.offsetBytes) prov rfl hP⟩

private theorem resolveTyWithLocalDecls_kind_mr (decls : List MirAst.LocalDecl)
    (layouts : LayoutTable) (ty : MirAst.Ty) :
    (resolveTyWithLocalDecls decls layouts ty).kind = ty.kind := by
  unfold resolveTyWithLocalDecls
  split
  · rfl
  · split
    · rfl
    · split
      · split <;> rfl
      · rfl

private theorem lookup_emptyLayoutTable_mr (k : Nat) :
    LayoutTable.lookup emptyLayoutTable k = none := by
  cases k <;> rfl

/-- **V5 & V6 Value-Coupled Universal Scalar Simulation (`v5_v6_binder_and_subtype_coupled_valRel_sim`)**:
for EVERY `M ∈ {BM, TBM}` and EVERY `decls`, whenever a Trusted `u32` scalar operand relates
to a MiniRust `.Int` value via `Ep2ValRel` (which enforces `bits < 2 ^ 32`),
`Rvalue.wrapUnsafeBinder`, `CastKind.subtype`, and `CastKind.transmute` produce outputs
related by `Ep2ValRel` to MiniRust's `transmuteM` (no redundant layout-resolution hypotheses!). -/
theorem v5_v6_binder_and_subtype_coupled_valRel_sim {M : Type} [Gen.Memory M] [MemoryOps M]
    (allocBase : Nat → Nat) (provAllocId : Gen.Memory.Provenance M → Nat)
    (locals locals' : List LocalSlot) (op : MirAst.Operand)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl)
    (bits : Nat) (mv : Gen.Value M) (m : Option (Gen.Machine M))
    (hOp : evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls mem.callStack =
      .ok (.scalar ⟨bits, 4⟩) locals')
    (hUse : evalUseRvalue locals op mem decls emptyLayoutTable = .ok (.scalar ⟨bits, 4⟩) locals' mem)
    (hRel : Ep2ValRel allocBase provAllocId (.scalar ⟨bits, 4⟩) mv)
    (hSrcTy : operandTy decls emptyLayoutTable op = some u32MirTy) :
    ∃ tv mv',
      evalRvalue locals (.wrapUnsafeBinder op u32MirTy) mem decls emptyLayoutTable = .ok tv locals' mem ∧
      evalRvalue locals (.cast .subtype op u32MirTy) mem decls emptyLayoutTable = .ok tv locals' mem ∧
      evalRvalue locals (.cast .transmute op u32MirTy) mem decls emptyLayoutTable = .ok tv locals' mem ∧
      transmuteM (M := M) mv u32MrTy u32MrTy m = .ok mv' ∧
      Ep2ValRel allocBase provAllocId tv mv' := by
  cases hRel with
  | scalar _ _ hBits =>
    have hBits32 : bits < 2 ^ 32 := hBits
    have hKind : ∀ ty, (resolveTyWithLocalDecls decls emptyLayoutTable ty).kind = ty.kind :=
      resolveTyWithLocalDecls_kind_mr decls emptyLayoutTable
    have hU32Ty : ∀ k, tyByteSize decls emptyLayoutTable { kind := .uint .u32, layoutIdx := k } = some 4 := by
      intro k
      unfold tyByteSize tyByteSizeAndAlignAux
      have hk : (resolveTyWithLocalDecls decls emptyLayoutTable { kind := .uint .u32, layoutIdx := k }).kind = .uint .u32 :=
        hKind _
      cases hr : resolveTyWithLocalDecls decls emptyLayoutTable { kind := .uint .u32, layoutIdx := k } with
      | mk kd li =>
        rw [hr] at hk; dsimp only at hk; subst hk
        simp only [rigidTyByteSize, lookup_emptyLayoutTable_mr]
        rfl
    have hWrap : evalRvalue locals (.wrapUnsafeBinder op u32MirTy) mem decls emptyLayoutTable =
        .ok (.scalar ⟨bits, 4⟩) locals' mem := by
      show evalWrapUnsafeBinder locals op u32MirTy mem decls emptyLayoutTable = _
      have hBnd : binderStructLayout? decls emptyLayoutTable u32MirTy = none := rfl
      have hRes : resolvedTyLayout? decls emptyLayoutTable u32MirTy = none := by
        unfold resolvedTyLayout?
        dsimp only
        cases isUnresolvedLayoutIdx emptyLayoutTable (resolveTyWithLocalDecls decls emptyLayoutTable u32MirTy).layoutIdx
        · exact lookup_emptyLayoutTable_mr _
        · rfl
      unfold evalWrapUnsafeBinder
      simp only [hUse, hBnd, hRes]
    have hCast : evalRvalue locals (.cast .subtype op u32MirTy) mem decls emptyLayoutTable =
        .ok (.scalar ⟨bits, 4⟩) locals' mem := by
      have hrk : (resolveTyWithLocalDecls decls emptyLayoutTable u32MirTy).kind = .uint .u32 := hKind u32MirTy
      have hDstSz : tyByteSize decls emptyLayoutTable (resolveTyWithLocalDecls decls emptyLayoutTable u32MirTy) = some 4 := by
        cases hr : resolveTyWithLocalDecls decls emptyLayoutTable u32MirTy with
        | mk kd li => rw [hr] at hrk; dsimp only at hrk; subst hrk; exact hU32Ty li
      have hSrcSz : resolveByteCastSrcTyAndSize decls emptyLayoutTable op u32MirTy =
          some (resolveTyWithLocalDecls decls emptyLayoutTable u32MirTy, 4) := by
        unfold resolveByteCastSrcTyAndSize; dsimp only; rw [hDstSz]
      have hEnc : encodeByteCastSourceBytes emptyLayoutTable
          (resolveTyWithLocalDecls decls emptyLayoutTable u32MirTy) (.scalar ⟨bits, 4⟩) =
          some (encodeLittleEndianBytes bits 4 none) := by
        cases hr : resolveTyWithLocalDecls decls emptyLayoutTable u32MirTy with
        | mk kd li =>
          rw [hr] at hrk; dsimp only at hrk; subst hrk
          unfold encodeByteCastSourceBytes encodeTypedValueToBytes normalizeCodecTy encodeValueToBytes
          simp only [lookup_emptyLayoutTable_mr]; rfl
      have hLen : length (encodeLittleEndianBytes bits 4 none) = 4 := encodeLittleEndianBytes_len bits 4 none
      have hDecAux : ∀ (li : LayoutIdx) (bs : List MirSemantics.AbstractByte),
          length bs = 4 → decodeLittleEndianBytes bs = some (bits, none) →
          decodeValueFromBytes 16 emptyLayoutTable { kind := .uint .u32, layoutIdx := li } bs =
            some (.scalar ⟨bits, 4⟩) := by
        intro li bs hl hd
        unfold decodeValueFromBytes decodeScalarBytes
        simp [hl, hd]; rfl
      have hDec : decodeTypedValueFromBytes defaultCodecFuel emptyLayoutTable
          (resolveTyWithLocalDecls decls emptyLayoutTable u32MirTy)
          (encodeLittleEndianBytes bits 4 none) = some (.scalar ⟨bits, 4⟩) := by
        cases hr : resolveTyWithLocalDecls decls emptyLayoutTable u32MirTy with
        | mk kd li =>
          rw [hr] at hrk; dsimp only at hrk; subst hrk
          unfold decodeTypedValueFromBytes
          dsimp only [normalizeCodecTy, defaultCodecFuel]
          exact hDecAux li _ hLen (by
            rw [decodeLittleEndianBytes_encode, show 256 ^ 4 = 2 ^ 32 by decide, Nat.mod_eq_of_lt hBits32]; rfl)
      show evalByteCast locals op u32MirTy mem decls emptyLayoutTable = _
      unfold evalByteCast
      dsimp only
      rw [hOp]; dsimp only
      rw [hDstSz]; dsimp only
      rw [hSrcTy]; dsimp only
      rw [hSrcSz]; dsimp only
      rw [hEnc]; dsimp only
      rw [hLen]; dsimp only
      rw [hDec]
    have hMr : transmuteM (M := M) (.Int (Int.ofNat bits)) u32MrTy u32MrTy m =
        .ok (.Int (Int.ofNat bits)) :=
      transmuteM_int_sameSize (M := M) u32 u32 rfl (by decide) ⟨4⟩ rfl rfl bits hBits32 m
    exact ⟨.scalar ⟨bits, 4⟩, .Int (Int.ofNat bits), hWrap, hCast, hCast, hMr, .scalar bits 4 hBits32⟩

/-- **V5 Value-Coupled Universal Binder-Struct, `NonZero`, & Transparent `bool` Wrapping
(`v5_wrapUnsafeBinder_struct_nonZero_coupled_valRel_sim`)**: for EVERY `M ∈ {BM, TBM}`
and EVERY operand (beyond the transparent `u32 → u32` identity of
`v5_v6_binder_and_subtype_coupled_valRel_sim`):
1. single-field `BinderU32` wrapping of ANY `u32` related by `Ep2ValRel` yields a
   Trusted aggregate related (`aggregate`) to MiniRust's `transmuteM` tuple image;
2. `NonZeroU8` wrapping of ANY `1 ≤ b < 256` yields a Trusted aggregate related
   (`enumVariant 0`) to MiniRust's `.Variant 0` image;
3. `NonZeroU8` wrapping of `0` faults UB on Trusted AND MiniRust;
4. transparent `bool` wrapping (`binderBoolMirTy`): `b ∈ {0, 1}` succeeds on BOTH
   Trusted (`.scalar ⟨b, 1⟩`) and MiniRust (`.Bool (b == 1)`), while `2 ≤ b < 256`
   faults UB on BOTH Trusted and MiniRust! -/
theorem v5_wrapUnsafeBinder_struct_nonZero_coupled_valRel_sim {M : Type} [Gen.Memory M] [MemoryOps M]
    (allocBase : Nat → Nat) (provAllocId : Gen.Memory.Provenance M → Nat)
    (locals locals' : List LocalSlot) (op : MirAst.Operand) (mem mem' : MirSemantics.Memory)
    (m : Option (Machine M)) :
    (∀ (bits : Nat) (mv : Gen.Value M),
      evalUseRvalue locals op mem [mkDecl binderU32MirTy, mkDecl u32MirTy] ep2BinderLayouts =
        .ok (.scalar ⟨bits, 4⟩) locals' mem' →
      operandTy [mkDecl binderU32MirTy, mkDecl u32MirTy] ep2BinderLayouts op = some u32MirTy →
      Ep2ValRel allocBase provAllocId (.scalar ⟨bits, 4⟩) mv →
      ∃ tv mv',
        evalRvalue locals (.wrapUnsafeBinder op binderU32MirTy) mem
          [mkDecl binderU32MirTy, mkDecl u32MirTy] ep2BinderLayouts = .ok tv locals' mem' ∧
        transmuteM (M := M) mv u32MrTy (mrBinderWrapperTy u32MrTy ⟨4⟩ ⟨4⟩) m = .ok mv' ∧
        Ep2ValRel allocBase provAllocId tv mv') ∧
    (∀ (b : Nat) (mv : Gen.Value M), 1 ≤ b →
      evalUseRvalue locals op mem [mkDecl binderNzU8MirTy, mkDecl u8MirTy] ep2BinderLayouts =
        .ok (.scalar ⟨b, 1⟩) locals' mem' →
      operandTy [mkDecl binderNzU8MirTy, mkDecl u8MirTy] ep2BinderLayouts op = some u8MirTy →
      Ep2ValRel allocBase provAllocId (.scalar ⟨b, 1⟩) mv →
      ∃ tv mv',
        evalRvalue locals (.wrapUnsafeBinder op binderNzU8MirTy) mem
          [mkDecl binderNzU8MirTy, mkDecl u8MirTy] ep2BinderLayouts = .ok tv locals' mem' ∧
        transmuteM (M := M) mv u8MrTy nonZeroU8MrTy m = .ok mv' ∧
        Ep2ValRel allocBase provAllocId tv mv') ∧
    (∀ (mv : Gen.Value M),
      evalUseRvalue locals op mem [mkDecl binderNzU8MirTy, mkDecl u8MirTy] ep2BinderLayouts =
        .ok (.scalar ⟨0, 1⟩) locals' mem' →
      operandTy [mkDecl binderNzU8MirTy, mkDecl u8MirTy] ep2BinderLayouts op = some u8MirTy →
      Ep2ValRel allocBase provAllocId (.scalar ⟨0, 1⟩) mv →
      evalRvalue locals (.wrapUnsafeBinder op binderNzU8MirTy) mem
          [mkDecl binderNzU8MirTy, mkDecl u8MirTy] ep2BinderLayouts = .ub ∧
        ∃ msg, transmuteM (M := M) mv u8MrTy nonZeroU8MrTy m = .error (.ub msg)) ∧
    (∀ (b : Nat) (mv : Gen.Value M),
      evalUseRvalue locals op mem [mkDecl binderBoolMirTy, mkDecl u8MirTy] ep2BinderLayouts =
        .ok (.scalar ⟨b, 1⟩) locals' mem' →
      Ep2ValRel allocBase provAllocId (.scalar ⟨b, 1⟩) mv →
      ((b = 0 ∨ b = 1) →
        evalRvalue locals (.wrapUnsafeBinder op binderBoolMirTy) mem
          [mkDecl binderBoolMirTy, mkDecl u8MirTy] ep2BinderLayouts = .ok (.scalar ⟨b, 1⟩) locals' mem' ∧
        transmuteM (M := M) mv u8MrTy .Bool m = .ok (.Bool (b == 1))) ∧
      (2 ≤ b →
        evalRvalue locals (.wrapUnsafeBinder op binderBoolMirTy) mem
          [mkDecl binderBoolMirTy, mkDecl u8MirTy] ep2BinderLayouts = .ub ∧
        ∃ msg, transmuteM (M := M) mv u8MrTy .Bool m = .error (.ub msg))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro bits mv hUse hTy hRel
    cases hRel with
    | scalar _ _ hBits =>
      have hT := ((v5_wrapUnsafeBinder_universal_sim locals locals' op mem mem' bits 0 hBits (by decide)
        none none).1 hUse hTy).1
      have hM := (transmuteM_binderWrapper_u32_and_thinPtr (M := M) bits 0 hBits (by decide) none m).2.1
      have hI : intFromBits bits u32 = Int.ofNat bits := rfl
      rw [hI] at hM
      exact ⟨_, _, hT, hM, .aggregate _ _ (.cons (.scalar bits 4 hBits) .nil)⟩
  · intro b mv h1 hUse hTy hRel
    cases hRel with
    | scalar _ _ hb =>
      have hT := ((v5_wrapUnsafeBinder_universal_sim locals locals' op mem mem' 0 b (by decide) hb
        none none).2.2.2.2.2.1 h1 hUse hTy).1
      have hM := (transmuteM_u8_to_nonZeroU8 (M := M) b hb m).2 h1
      exact ⟨_, _, hT, hM, .enumVariant 0 _ _ (.scalar b 1 hb)⟩
  · intro mv hUse hTy hRel
    cases hRel with
    | scalar _ _ _ =>
      have hT := ((v5_wrapUnsafeBinder_universal_sim locals locals' op mem mem' 0 0 (by decide) (by decide)
        none none).2.2.2.2.1 hUse hTy).1
      exact ⟨hT, _, (transmuteM_u8_to_nonZeroU8 (M := M) 0 (by decide) m).1 rfl⟩
  · intro b mv hUse hRel
    cases hRel with
    | scalar _ _ hb =>
      refine ⟨?_, ?_⟩
      · intro hb01
        have hT := ((v5_wrapUnsafeBinder_universal_sim locals locals' op mem mem' 0 b (by decide) hb
          none none).2.2.1 hb01 hUse).1
        rcases hb01 with rfl | rfl
        · exact ⟨hT, (transmuteM_u8_to_bool (M := M) 0 (by decide) m).1 rfl⟩
        · exact ⟨hT, (transmuteM_u8_to_bool (M := M) 1 (by decide) m).2.1 rfl⟩
      · intro hGe
        have hT := ((v5_wrapUnsafeBinder_universal_sim locals locals' op mem mem' 0 b (by decide) hb
          none none).2.2.2.1 hGe hUse).1
        exact ⟨hT, _, (transmuteM_u8_to_bool (M := M) b hb m).2.2 hGe⟩

/-- **V7 Value-Coupled Universal Thin & Wide `AggregateKind.rawPtr` + Episode 1 `UnOp.GetMetadata`
Simulation (`v7_rawPtr_coupled_valRel_sim`)**: for EVERY `M ∈ {BM, TBM}`, whenever
Trusted data pointer `p` and metadata (`unit` for thin, `usize` `len` for wide)
relate to MiniRust values via `Ep2ValRel`, BOTH thin and wide `AggregateKind.rawPtr`
construction (via `transmuteM`) AND Episode 1's `UnOp.GetMetadata` preserve
`Ep2ValRel` with exact `allocId`, `offsetBytes`, and metadata length! -/
theorem v7_rawPtr_coupled_valRel_sim {M : Type} [Gen.Memory M] [MemoryOps M]
    (allocBase : Nat → Nat) (provAllocId : Gen.Memory.Provenance M → Nat) :
    (∀ (locals locals' : List LocalSlot) (dOp mOp : MirAst.Operand)
        (ptee : MirAst.Ty) (mut_ : MirAst.Mutability) (mem : MirSemantics.Memory)
        (decls : List MirAst.LocalDecl)
        (p : ProvenancePtr) (md mv : Gen.Value M) (m : Option (Gen.Machine M)),
      isUnsizedRawPtrPointee ptee = false →
      evalOperands locals [dOp, mOp] mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls mem.callStack =
        .ok [.ptr p 8, .unit] locals' →
      Ep2ValRel allocBase provAllocId (.ptr p 8) md →
      Ep2ValRel allocBase provAllocId .unit mv →
      allocBase p.allocId + p.offsetBytes < 2 ^ 64 →
      ∃ tv mv',
        evalRvalue locals (.aggregate (.rawPtr ptee mut_) [dOp, mOp]) mem decls emptyLayoutTable = .ok tv locals' mem ∧
        transmuteM (M := M) (.Tuple [md, mv]) mrRawPtrThinPairTy thinRawPtrTy m = .ok mv' ∧
        Ep2ValRel allocBase provAllocId tv mv') ∧
    (∀ (locals locals' : List LocalSlot) (dOp mOp : MirAst.Operand)
        (ptee : MirAst.Ty) (mut_ : MirAst.Mutability) (mem : MirSemantics.Memory)
        (decls : List MirAst.LocalDecl)
        (p : ProvenancePtr) (len : Nat) (md mm : Gen.Value M) (m : Option (Gen.Machine M)),
      wideAggregatePointeeIsDyn? ptee = some false →
      evalOperands locals [dOp, mOp] mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls mem.callStack =
        .ok [.ptr p 8, .scalar ⟨len, 8⟩] locals' →
      Ep2ValRel allocBase provAllocId (.ptr p 8) md →
      Ep2ValRel allocBase provAllocId (.scalar ⟨len, 8⟩) mm →
      allocBase p.allocId + p.offsetBytes < 2 ^ 64 →
      ∃ tv mv',
        evalRvalue locals (.aggregate (.rawPtr ptee mut_) [dOp, mOp]) mem decls emptyLayoutTable = .ok tv locals' mem ∧
        transmuteM (M := M) (.Tuple [md, mm]) mrRawPtrWidePairTy wideSlicePtrMrTy m = .ok mv' ∧
        evalUnOpM (M := M) .GetMetadata (mv', wideSlicePtrMrTy) m = .ok (.Int (Int.ofNat len), usizeMrTy) ∧
        Ep2ValRel allocBase provAllocId tv mv' ∧
        Ep2ValRel allocBase provAllocId (.scalar ⟨len, 8⟩) (.Int (Int.ofNat len))) := by
  refine ⟨?_, ?_⟩
  · intro locals locals' dOp mOp ptee mut_ mem decls p md mv m hSized hOps hRelD hRelM hAddr
    cases hRelD with
    | thinPtr _ addr prov hA hP =>
      cases hRelM with
      | unit =>
        subst hA
        have hTr : evalRvalue locals (.aggregate (.rawPtr ptee mut_) [dOp, mOp]) mem decls emptyLayoutTable =
            .ok (.ptr p 8) locals' mem := by
          show evalAggregateRawPtr locals ptee [dOp, mOp] mem decls emptyLayoutTable = _
          unfold evalAggregateRawPtr
          simp only [hOps, layoutPointerBytes, emptyLayoutTable, hSized]
        refine ⟨.ptr p 8, .Ptr (ThinPointer.widen { addr := allocBase p.allocId + p.offsetBytes, provenance := prov } none),
          hTr,
          transmuteM_rawPtrThinPair_to_thinRawPtr (M := M) (allocBase p.allocId + p.offsetBytes) hAddr prov m,
          .thinPtr p (allocBase p.allocId + p.offsetBytes) prov rfl hP⟩
  · intro locals locals' dOp mOp ptee mut_ mem decls p len md mm m hWide hOps hRelD hRelM hAddr
    cases hRelD with
    | thinPtr _ addr prov hA hP =>
      cases hRelM with
      | scalar _ _ hLen =>
        subst hA
        have hTr : evalRvalue locals (.aggregate (.rawPtr ptee mut_) [dOp, mOp]) mem decls emptyLayoutTable =
            .ok (.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]) locals' mem := by
          show evalAggregateRawPtr locals ptee [dOp, mOp] mem decls emptyLayoutTable = _
          unfold evalAggregateRawPtr
          simp only [hOps, layoutPointerBytes, emptyLayoutTable, hWide]
          rfl
        refine ⟨.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩],
          mrWidePtrValM (M := M) { addr := allocBase p.allocId + p.offsetBytes, provenance := prov } (Int.ofNat len),
          hTr,
          transmuteM_rawPtrWidePair_to_wideSlicePtr (M := M) (allocBase p.allocId + p.offsetBytes) len hAddr hLen prov m,
          (evalUnOpM_rawPtr_meta_size_align (M := M) (allocBase p.allocId + p.offsetBytes) len hAddr hLen prov m).2.2.2.2.1,
          .widePtr p len hLen (allocBase p.allocId + p.offsetBytes) prov rfl hP,
          .scalar len 8 hLen⟩

/-- **V8 Value-Coupled Universal `n`-Capture Closure Simulation (`v8_closure_coupled_valRel_sim`)**:
for EVERY `M ∈ {BM, TBM}` and EVERY capture list `ops` whose evaluated Trusted
upvars relate element-by-element to MiniRust tuple elements via
`Ep2ValListRel allocBase provAllocId`, `AggregateKind.closure` and
MiniRust `ValueExpr.Tuple` produce outputs related by `Ep2ValRel`! -/
theorem v8_closure_coupled_valRel_sim {M : Type} [Gen.Memory M] [MemoryOps M]
    (allocBase : Nat → Nat) (provAllocId : Gen.Memory.Provenance M → Nat)
    (locals locals' : List LocalSlot) (dp : DefPath) (ops : List MirAst.Operand)
    (vals : List MirSemantics.Value) (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl)
    (layouts : LayoutTable) (m m' : Gen.Machine M) (es : List Gen.ValueExpr)
    (mvals : List (Gen.Value M)) (mrClTy : Gen.Type)
    (hOps : evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals decls mem.callStack = .ok vals locals')
    (hEs : evalValuesM m es = .ok (mvals, m'))
    (hRel : Ep2ValListRel allocBase provAllocId vals mvals) :
    ∃ tv mv',
      evalRvalue locals (.aggregate (.closure dp) ops) mem decls layouts = .ok tv locals' mem ∧
      evalValueM m (.Tuple es mrClTy) = .ok ((mv', mrClTy), m') ∧
      Ep2ValRel allocBase provAllocId tv mv' :=
  have h := (closure_n_capture_lockstep_M (M := M) locals locals' dp ops vals mem decls layouts
    m m' es mvals mrClTy).1 hOps hEs
  ⟨.aggregate 0 vals, .Tuple mvals, h.2.2.1, h.2.2.2, .aggregate vals mvals hRel⟩

/-! ## §9. Canonical Executable MiniRust Corpus Observation Interface

Directly executes `MiniRustSpec.Interp.{step, steps, stepTB, stepsTB}` for all 8
Episode 2 MIR variants (normal returns, UB faults, fail-closed boundaries, and
`Mach` vs. `MachTB` mode sensitivity) without any shadow evaluator, so
`Anneal.Mir.DropBinderAndSubtypeBundle` can wire `MiniRustSpec.Interp` directly
into `DualCorrespondenceBundle`. -/

/-- The 8 already-trusted Episode 2 MIR variants. -/
inductive Ep2Variant : Type where
  | coverage
  | backwardIncompatibleDropHint
  | dropTerminator
  | shallowInitBox
  | wrapUnsafeBinder
  | castSubtype
  | aggregateRawPtr
  | aggregateClosure
  deriving DecidableEq, Repr

/-- Corpus test case selector within each of the 8 variants. -/
inductive Ep2Case : Type where
  /-- Primary positive normal-return case. -/
  | okPrimary
  /-- Secondary positive normal-return case (e.g. projected drop, wide slice rawPtr, 2-capture closure, binder struct). -/
  | okSecondary
  /-- Primary UB fault case (dead/uninit/invalid-value UB). -/
  | ubFault
  /-- Mode-sensitive case (`BasicMemory` succeeds vs. `TreeBorrows` protector UB on `dropTerminator`,
      and secondary UB/ok check elsewhere). -/
  | modeCase
  deriving DecidableEq, Repr

/-- MiniRust execution mode: `BasicMemory` (`Mach`) versus `TreeBorrowsMemory` (`MachTB`). -/
inductive Ep2MrMode : Type where
  | basicMemory
  | treeBorrows
  deriving DecidableEq, Repr

/-- Normalized authority-typed observation produced directly by `MiniRustSpec.Interp`. -/
inductive Ep2MrObs : Type where
  | retBytes (bs : List TBByteOutcome)
  | ub
  | unsupported
  deriving DecidableEq

/-- Run `n` steps of `MiniRustSpec.Interp` in mode `mode` and extract allocation `allocIdx`'s
observable bytes (`projByteTB`), or `.ub` / `.unsupported`. -/
def runMrObs (mode : Ep2MrMode) (n : Nat) (allocIdx : Nat) (m : Mach) : Ep2MrObs :=
  match mode with
  | .basicMemory =>
    match Interp.steps n m with
    | .ok m' =>
      match m'.mem.memory.allocations[allocIdx]? with
      | some a => .retBytes (a.data.map (projByteTB ∘ liftByteTB))
      | none => .unsupported
    | .error (.ub _) => .ub
    | .error _ => .unsupported
  | .treeBorrows =>
    match Interp.stepsTB n (liftMachToTB m) with
    | .ok m' =>
      match m'.mem.memory.mem.allocations[allocIdx]? with
      | some a => .retBytes (a.data.map projByteTB)
      | none => .unsupported
    | .error (.ub _) => .ub
    | .error _ => .unsupported

/-- Direct `MiniRustSpec.Interp` observation for every `(mode, variant, case)` key
across all 8 MIR variants. Every entry executes the actual MiniRust interpreter
(`Interp.steps` or `Interp.stepsTB`) on a concrete `Mach` / `MachTB` machine. -/
def ep2MrObserve (mode : Ep2MrMode) (v : Ep2Variant) (c : Ep2Case) : Ep2MrObs :=
  match v, c with
  | .coverage, .okPrimary => runMrObs mode 1 0 v1CoverageOkMach
  | .coverage, .okSecondary => runMrObs mode 1 0 v1CoverageOkMach
  | .coverage, .ubFault => runMrObs mode 1 0 v1CoverageUbMach
  | .coverage, .modeCase => runMrObs mode 1 0 v1CoverageOkMach
  | .backwardIncompatibleDropHint, .okPrimary => runMrObs mode 1 0 v2DropHintOkMach
  | .backwardIncompatibleDropHint, .okSecondary => runMrObs mode 1 0 v2DropHintOkMach
  | .backwardIncompatibleDropHint, .ubFault => runMrObs mode 2 0 v2DropHintUbMach
  | .backwardIncompatibleDropHint, .modeCase => runMrObs mode 1 0 v2DropHintOkMach
  | .dropTerminator, .okPrimary => runMrObs mode 3 0 v3DropWholeOkMach
  | .dropTerminator, .okSecondary => runMrObs mode 3 0 (v3DropProjMach true)
  | .dropTerminator, .ubFault => runMrObs mode 2 0 v3DropDeadUbMach
  | .dropTerminator, .modeCase => runMrObs mode 4 0 v3DropProtectedMach
  | .shallowInitBox, .okPrimary => runMrObs mode 1 0 (v4ShallowInitBoxMach boxU32MrTy)
  | .shallowInitBox, .okSecondary => runMrObs mode 1 0 v4ShallowInitBoxDistinctMach
  | .shallowInitBox, .ubFault => runMrObs mode 1 0 (v4ShallowInitBoxMach boxU32MrTy false true)
  | .shallowInitBox, .modeCase => runMrObs mode 1 0 (v4ShallowInitBoxMach boxU32MrTy true false)
  | .wrapUnsafeBinder, .okPrimary => runMrObs mode 2 0 (v5WrapRoundtripMach 73)
  | .wrapUnsafeBinder, .okSecondary => runMrObs mode 1 0 (c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 7 none] 1)
  | .wrapUnsafeBinder, .ubFault => runMrObs mode 1 0 (c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 0 none] 1)
  | .wrapUnsafeBinder, .modeCase => runMrObs mode 1 0 (c7MkTransmuteMach u8MrTy .Bool [.Init 2 none] 1)
  | .castSubtype, .okPrimary => runMrObs mode 1 0 (c7MkTransmuteMach u32MrTy i32MrTy (scalarBytes u32 4294967295) 4)
  | .castSubtype, .okSecondary => runMrObs mode 1 0 (c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 7 none] 1)
  | .castSubtype, .ubFault => runMrObs mode 1 0 (c7MkTransmuteMach u8MrTy .Bool [.Init 2 none] 1)
  | .castSubtype, .modeCase => runMrObs mode 1 0 (c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 0 none] 1)
  | .aggregateRawPtr, .okPrimary => runMrObs mode 3 0 (v7RawPtrThinMach true true)
  | .aggregateRawPtr, .okSecondary => runMrObs mode 4 0 (v7RawPtrWideMach u32MrTy 5)
  | .aggregateRawPtr, .ubFault => runMrObs mode 1 0 (v7RawPtrThinMach false true)
  | .aggregateRawPtr, .modeCase => runMrObs mode 1 0 (v7RawPtrWideMach u32MrTy 5 true true false)
  | .aggregateClosure, .okPrimary => runMrObs mode 1 0 c10ZstMach
  | .aggregateClosure, .okSecondary => runMrObs mode 2 0 (c10CapMach true true)
  | .aggregateClosure, .ubFault => runMrObs mode 1 0 (c10CapMach false true)
  | .aggregateClosure, .modeCase => runMrObs mode 1 0 (c10CapMach true false)

/-- Mode sensitivity certified directly on `ep2MrObserve`: `dropTerminator.modeCase`
returns `42` under `BasicMemory` (`Mach`) and faults `.ub` under `TreeBorrowsMemory` (`MachTB`). -/
theorem ep2MrObserve_drop_mode_sensitivity :
    ep2MrObserve .basicMemory .dropTerminator .modeCase =
      .retBytes ((scalarBytes u32 42).map (projByteTB ∘ liftByteTB)) ∧
    ep2MrObserve .treeBorrows .dropTerminator .modeCase = .ub :=
  ⟨by decide +kernel, by decide +kernel⟩

/-! ## §10. Exhaustive Axiom, Import-Isolation, & `Classical.choice`-Free Codec Audit -/

section AxiomAudit
open Lean Elab Command

/-- Exhaustively verify that:
1. This module obeys `[IMPORT-ISOLATION]` (zero `Anneal.*`, zero `DeinitBridge`,
   zero `IntrinsicBoundary` imports).
2. Every declaration defined in `MiniRustSpec.DropBinderAndSubtypeMR` depends ONLY
   on standard Lean axioms (`propext`, `Quot.sound`, `Classical.choice`) with zero
   `sorryAx` and zero `Lean.ofReduceBool` / `Lean.trustCompiler`.
3. All executable codecs and codec theorems in this module are strictly
   `Classical.choice`-free. -/
elab "#assert_drop_binder_subtype_mr_audit" : command => do
  let env ← getEnv
  for modName in env.header.moduleNames do
    if (`Anneal).isPrefixOf modName ||
        modName == `MiniRustSpec.Correspondence.DeinitBridge ||
        modName == `MiniRustSpec.Correspondence.IntrinsicBoundary then
      throwError "import-isolation violation: {modName} must not be imported"
  let mut checked : Nat := 0
  for (c, _) in env.constants.map₂.toList do
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    checked := checked + 1
  if checked == 0 then
    throwError "MiniRustSpec.DropBinderAndSubtypeMR: 0 declarations found"
  let choiceFreeCodecs : List Lean.Name := [
    ``transmuteM_rawPtrThinPair_to_thinRawPtr,
    ``transmuteM_rawPtrWidePair_to_wideSlicePtr,
    ``transmuteM_thinRawPtr_to_boxU32,
    ``encodeM_decodeM_mrPairU32,
    ``evalUnOpM_rawPtr_meta_size_align,
    ``runMrObs,
    ``ep2MrObserve
  ]
  for c in choiceFreeCodecs do
    let axs ← liftCoreM <| Lean.collectAxioms c
    if axs.contains ``Classical.choice then
      throwError "MR codec/def {c} unexpectedly depends on Classical.choice"
  logInfo m!"MiniRustSpec.DropBinderAndSubtypeMR: verified {checked} declarations (sorry_free=true, import_isolated=true, choice_free_codecs={choiceFreeCodecs.length})"

#assert_drop_binder_subtype_mr_audit

end AxiomAudit

end MiniRustSpec.DropBinderAndSubtypeMR
