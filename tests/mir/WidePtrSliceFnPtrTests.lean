/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.Mir.Cast
import Anneal.Mir.PlaceAndRvalue
import Lean.Elab.Command

/-!
# Concrete Non-Vacuity Witnesses, UB Refutations & Axiom Audit for Episode 2

Every theorem family added to `Anneal.Mir.Cast` (Section 9) and `Anneal.Mir.PlaceAndRvalue`
(Section 3.B) is *instantiated* below on concrete 64-bit (`pointerBits := 64`) and 32-bit
(`pointerBits := 32`) layout tables, `LocalDecl`s, `LocalSlot`s, and `BorrowEntry` tables: each
general theorem is applied with every hypothesis discharged by the kernel (`rfl` / `decide`, never
`native_decide`), on both positive (`.ok`) and negative (`.ub`) executions. The final `run_cmd`
audits *every* declaration added to both modules (selected by source position, so later additions are
covered automatically) for `sorryAx`, `unsafe`, and any axiom outside
`{propext, Classical.choice, Quot.sound}` (in particular `Lean.ofReduceBool`).
-/

namespace Anneal.WidePtrSliceFnPtrTests

open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirSemantics.RvalueEvalResult
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.Mir.Cast

/-! ## Concrete environments -/

/-- Layout entries shared by both pointer widths (`0`: ZST, `1`: `u32`, `2`: `[u32; 5]`). -/
def commonEntries : List TypeLayout := [
  { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false, fieldLayouts := [] },
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false, fieldLayouts := [] },
  { size := { bytes := 20 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false, fieldLayouts := [] }]

def testLayouts64 : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries := commonEntries ++ [
    { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := .memory,
      fields := .arbitrary [] [], variants := .single 0, isUninhabited := false,
      fieldLayouts := [] }]
}

def testLayouts32 : LayoutTable := {
  pointerBits := 32
  isLittleEndian := true
  entries := commonEntries ++ [
    { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := .memory,
      fields := .arbitrary [] [], variants := .single 0, isUninhabited := false,
      fieldLayouts := [] }]
}

theorem ptrBytes64 : layoutPointerBytes testLayouts64 = 8 := rfl
theorem ptrBytes32 : layoutPointerBytes testLayouts32 = 4 := rfl

def u32Ty : RigidTy := .uint .u32
def fnSigSafe : RigidTy := .fnPtr [] (.tuple []) .safe .rust
def fnSigUnsafe : RigidTy := .fnPtr [] (.tuple []) .unsafe_ .rust
def fnSigIntrinsic : RigidTy := .fnPtr [] (.tuple []) .safe .rustIntrinsic

/-- Declarations indexed by local:
`0 : [u32; 5]`, `1 : &[u32; 5]`, `2 : *const [u32; 5]`, `3 : &mut [u32; 5]`, `4 : *mut [u32; 5]`,
`5 : *const [u32]`, `6 : *mut [u32]`, `7 : fn item f`, `8 : fn()`, `9 : closure c`,
`10 : closure d (capturing u32)`, `11 : *mut u32`, `12 : *const u32`, `13 : u32`,
`14 : *const [u32; 5]` (dangling), `15 : &[u32]`, `16 : [u32; 0]`, `17 : &[u32; 0]`, `18 : usize`,
`19 : ()`, `20 .. 22 : *const [u32]`, `23 .. 26 : &[u32]`, `27 : *const [u32]`, `28 : &[u32]`,
`29 : &str`, `30 : &[u32; 0]` (ZST borrow), `31 : &[u32; 5]` (uninit borrow), `32 : &[u32; 5]`
(global), `33 : &[u32]` (dangling, non-empty), `34 : *mut [u32; 5]` (read-only global). -/
def testDecls : List LocalDecl := [
  { mutability := .not, ty := { kind := .array u32Ty 5, layoutIdx := 2 }, debugName := none },
  { mutability := .not, ty := { kind := .ref .not (.array u32Ty 5), layoutIdx := 1 }, debugName := none },
  { mutability := .not, ty := { kind := .rawPtr .not (.array u32Ty 5), layoutIdx := 1 }, debugName := none },
  { mutability := .not, ty := { kind := .ref .mut (.array u32Ty 5), layoutIdx := 1 }, debugName := none },
  { mutability := .not, ty := { kind := .rawPtr .mut (.array u32Ty 5), layoutIdx := 1 }, debugName := none },
  { mutability := .not, ty := { kind := .rawPtr .not (.slice u32Ty), layoutIdx := 3 }, debugName := none },
  { mutability := .not, ty := { kind := .rawPtr .mut (.slice u32Ty), layoutIdx := 3 }, debugName := none },
  { mutability := .not, ty := { kind := .fnDef "f" [], layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := fnSigSafe, layoutIdx := 1 }, debugName := none },
  { mutability := .not, ty := { kind := .closure "c" [], layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .closure "d" [u32Ty], layoutIdx := 1 }, debugName := none },
  { mutability := .not, ty := { kind := .rawPtr .mut u32Ty, layoutIdx := 1 }, debugName := none },
  { mutability := .not, ty := { kind := .rawPtr .not u32Ty, layoutIdx := 1 }, debugName := none },
  { mutability := .not, ty := { kind := u32Ty, layoutIdx := 1 }, debugName := none },
  { mutability := .not, ty := { kind := .rawPtr .not (.array u32Ty 5), layoutIdx := 1 }, debugName := none },
  { mutability := .not, ty := { kind := .ref .not (.slice u32Ty), layoutIdx := 3 }, debugName := none },
  { mutability := .not, ty := { kind := .array u32Ty 0, layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .ref .not (.array u32Ty 0), layoutIdx := 1 }, debugName := none },
  { mutability := .not, ty := { kind := .uint .usize, layoutIdx := 1 }, debugName := none },
  { mutability := .not, ty := { kind := .tuple [], layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .rawPtr .not (.slice u32Ty), layoutIdx := 3 }, debugName := none },
  { mutability := .not, ty := { kind := .rawPtr .not (.slice u32Ty), layoutIdx := 3 }, debugName := none },
  { mutability := .not, ty := { kind := .rawPtr .not (.slice u32Ty), layoutIdx := 3 }, debugName := none },
  { mutability := .not, ty := { kind := .ref .not (.slice u32Ty), layoutIdx := 3 }, debugName := none },
  { mutability := .not, ty := { kind := .ref .not (.slice u32Ty), layoutIdx := 3 }, debugName := none },
  { mutability := .not, ty := { kind := .ref .not (.slice u32Ty), layoutIdx := 3 }, debugName := none },
  { mutability := .not, ty := { kind := .ref .not (.slice u32Ty), layoutIdx := 3 }, debugName := none },
  { mutability := .not, ty := { kind := .rawPtr .not (.slice u32Ty), layoutIdx := 3 }, debugName := none },
  { mutability := .not, ty := { kind := .ref .not (.slice u32Ty), layoutIdx := 3 }, debugName := none },
  { mutability := .not, ty := { kind := .ref .not .str, layoutIdx := 3 }, debugName := none },
  { mutability := .not, ty := { kind := .ref .not (.array u32Ty 0), layoutIdx := 1 }, debugName := none },
  { mutability := .not, ty := { kind := .ref .not (.array u32Ty 5), layoutIdx := 1 }, debugName := none },
  { mutability := .not, ty := { kind := .ref .not (.array u32Ty 5), layoutIdx := 1 }, debugName := none },
  { mutability := .not, ty := { kind := .ref .not (.slice u32Ty), layoutIdx := 3 }, debugName := none },
  { mutability := .not, ty := { kind := .rawPtr .mut (.array u32Ty 5), layoutIdx := 1 }, debugName := none }]

def backing : Value :=
  .aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩, .scalar ⟨5, 4⟩]

def backingElems : List Value :=
  [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩, .scalar ⟨5, 4⟩]

/-- Borrow table: tag `1` active and tag `2` disabled on local `0`; tag `3` frozen on local `0`;
tag `4` active on the `.uninit` local `13`; tag `5` active on the ZST `.unit` local `19`. -/
def testBorrows : List BorrowEntry := [
  { tag := 1, targetLocal := 0, targetProjection := [], perm := .active },
  { tag := 2, targetLocal := 0, targetProjection := [], perm := .disabled },
  { tag := 3, targetLocal := 0, targetProjection := [], perm := .frozen },
  { tag := 4, targetLocal := 13, targetProjection := [], perm := .active },
  { tag := 5, targetLocal := 19, targetProjection := [], perm := .active }]

/-- A read-only global allocation (`allocId = 9`) holding 20 bytes. -/
def testGlobal : CapturedAllocation := {
  allocId := 9
  bytes := List.replicate 20 (some 0)
  relocations := []
  align := { bytes := 4 }
  mutability := .not }

def testMem : Memory := {
  borrows := testBorrows
  globals := [testGlobal]
  nextTag := 10 }

/-- Locals for pointer width `pb` (`8` or `4`): every pointer value is `pb` bytes wide, except the
function pointers, which `Trusted` always models as 8-byte values. -/
def testLocals (pb : Nat) : List LocalSlot := [
  .init backing,                                                       -- 0
  .init (.ptr ⟨1, 0⟩ pb),                                              -- 1 : &[u32;5] (tag 1)
  .init (.ptr ⟨7, 16⟩ pb),                                             -- 2 : *const [u32;5] unbacked
  .init (.ptr ⟨2, 0⟩ pb),                                              -- 3 : &mut [u32;5] (tag 2, disabled)
  .init (.ptr ⟨3, 0⟩ pb),                                              -- 4 : *mut [u32;5] (tag 3, frozen)
  .init (.aggregate 0 [.ptr ⟨1, 0⟩ pb, .scalar ⟨5, pb⟩]),              -- 5 : *const [u32] (tag 1)
  .init (.aggregate 0 [.ptr ⟨7, 0⟩ pb, .scalar ⟨5, pb⟩]),              -- 6 : *mut [u32] unbacked
  .init .unit,                                                         -- 7 : fn item f
  .init (.ptr ⟨65536, 0⟩ 8),                                           -- 8 : fn() (8-byte)
  .init (.aggregate 0 []),                                             -- 9 : closure c
  .init (.aggregate 0 [.scalar ⟨7, 4⟩]),                               -- 10 : closure d
  .init (.ptr ⟨7, 0⟩ pb),                                              -- 11 : *mut u32 unbacked
  .init (.scalar ⟨4096, pb⟩),                                          -- 12 : *const u32 (no provenance)
  .uninit,                                                             -- 13 : u32 (uninit)
  .init (.ptr ⟨0, 16⟩ pb),                                             -- 14 : *const [u32;5] dangling
  .init (.aggregate 0 [.ptr ⟨1, 0⟩ pb, .scalar ⟨5, pb⟩]),              -- 15 : &[u32] (tag 1)
  .init (.aggregate 0 []),                                             -- 16 : [u32; 0]
  .init (.ptr ⟨0, 16⟩ pb),                                             -- 17 : &[u32; 0] dangling
  .init (.scalar ⟨5, pb⟩),                                             -- 18 : usize
  .init .unit,                                                         -- 19 : ()
  .init (.aggregate 0 [.ptr ⟨7, 4⟩ pb, .scalar ⟨5, pb⟩]),              -- 20 : *const [u32]
  .init (.aggregate 0 [.ptr ⟨7, 4⟩ pb, .scalar ⟨3, pb⟩]),              -- 21 : *const [u32]
  .init (.aggregate 0 [.ptr ⟨7, 8⟩ pb, .scalar ⟨1, pb⟩]),              -- 22 : *const [u32]
  .init (.aggregate 0 [.ptr ⟨2, 0⟩ pb, .scalar ⟨5, pb⟩]),              -- 23 : &[u32] (disabled)
  .init (.aggregate 0 [.ptr ⟨1, 0⟩ pb, .scalar ⟨6, pb⟩]),              -- 24 : &[u32] (len 6 > 5)
  .init (.aggregate 0 [.ptr ⟨9, 0⟩ pb, .scalar ⟨5, pb⟩]),              -- 25 : &[u32] (global)
  .init (.aggregate 0 [.ptr ⟨0, 16⟩ pb, .scalar ⟨0, pb⟩]),             -- 26 : &[u32] (dangling, empty)
  .init (.aggregate 0 [.scalar ⟨4096, pb⟩, .scalar ⟨5, pb⟩]),          -- 27 : *const [u32] (no prov.)
  .init (.aggregate 0 [.ptr ⟨4, 0⟩ pb, .scalar ⟨5, pb⟩]),              -- 28 : &[u32] (uninit target)
  .init (.aggregate 0 [.ptr ⟨7, 0⟩ pb, .scalar ⟨3, pb⟩]),              -- 29 : &str
  .init (.ptr ⟨5, 0⟩ pb),                                              -- 30 : &[u32; 0] (tag 5, ZST)
  .init (.ptr ⟨4, 0⟩ pb),                                              -- 31 : &[u32; 5] (tag 4, uninit)
  .init (.ptr ⟨9, 0⟩ pb),                                              -- 32 : &[u32; 5] (global 9)
  .init (.aggregate 0 [.ptr ⟨0, 16⟩ pb, .scalar ⟨3, pb⟩]),             -- 33 : &[u32] (dangling, len 3)
  .init (.ptr ⟨9, 0⟩ pb)]                                              -- 34 : *mut [u32; 5] (global 9)

def L64 : List LocalSlot := testLocals 8
def L32 : List LocalSlot := testLocals 4

def cp (i : Nat) : Operand := .copy { local_ := i, projection := [] }

def sliceTy (k : RigidTy) : Ty := { kind := k, layoutIdx := 3 }

def activeEntry : BorrowEntry := { tag := 1, targetLocal := 0, targetProjection := [], perm := .active }
def disabledEntry : BorrowEntry :=
  { tag := 2, targetLocal := 0, targetProjection := [], perm := .disabled }
def frozenEntry : BorrowEntry := { tag := 3, targetLocal := 0, targetProjection := [], perm := .frozen }
def uninitEntry : BorrowEntry :=
  { tag := 4, targetLocal := 13, targetProjection := [], perm := .active }
def zstEntry : BorrowEntry := { tag := 5, targetLocal := 19, targetProjection := [], perm := .active }

/-- Local `12` re-typed as `*const [u32; 5]` (a provenance-less raw array pointer). -/
def rawArrayDecl : LocalDecl :=
  { mutability := .not, ty := { kind := .rawPtr .not (.array u32Ty 5), layoutIdx := 1 },
    debugName := none }

/-- Local `12` re-typed as `*mut u32` (a provenance-less mutable thin pointer). -/
def rawMutU32Decl : LocalDecl :=
  { mutability := .not, ty := { kind := .rawPtr .mut u32Ty, layoutIdx := 1 }, debugName := none }

def declsScalarRawArray : List LocalDecl := testDecls.set 12 rawArrayDecl

def declsScalarRawMut : List LocalDecl := testDecls.set 12 rawMutU32Decl

/-- The fresh narrowed borrow allocated by `ArrayToPointer` on the stack borrow of local `0`. -/
def narrowedEntry : BorrowEntry :=
  { tag := 10, targetLocal := 0, targetProjection := [.subslice 0 5 false], perm := .active }

def memAfterNarrow : Memory := { testMem with borrows := narrowedEntry :: testMem.borrows, nextTag := 11 }

def fnEntryF : FnPtrEntry := { allocId := 65536, defPath := "f", typeArgs := [], fnSig := some fnSigSafe }

def fnEntryC : FnPtrEntry := { allocId := 65536, defPath := "c", typeArgs := [], fnSig := some fnSigSafe }

def memAfterInternF : Memory := { testMem with fnPtrs := [fnEntryF] }

def memAfterInternC : Memory := { testMem with fnPtrs := [fnEntryC] }

/-! ## 9.1 Spelling bridge -/

theorem spelling_reify_unsafe_roundtrip :
    LPointerCoercionKind.lowerPointerCoercionKind_V2026_06_01
        (LPointerCoercionKind.toRustcSpelling_V2026_06_01 (.reifyFnPointerWithSafety .unsafe_)) =
      some (.reifyFnPointerWithSafety .unsafe_) :=
  LPointerCoercionKind.lowerPointerCoercionKind_toRustcSpelling_V2026_06_01 _

/-- Two-sided spelling bijection: `"ClosureFnPointer"` lowers exactly to the any-safety closure
coercion, and `"UnsafeFnPointer"` is the spelling of `unsafeFnPointer`. -/
theorem spelling_bijection_witnesses :
    LPointerCoercionKind.lowerPointerCoercionKind_V2026_06_01 "ClosureFnPointer" =
        some .closureFnPointerAnySafety ∧
    LPointerCoercionKind.toRustcSpelling_V2026_06_01 .unsafeFnPointer = "UnsafeFnPointer" :=
  ⟨(LPointerCoercionKind.lowerPointerCoercionKind_V2026_06_01_eq_some_iff _ _).mpr rfl,
    (LPointerCoercionKind.lowerPointerCoercionKind_V2026_06_01_eq_some_iff _ _).mp rfl⟩

theorem spelling_unknown_rejected :
    LPointerCoercionKind.lowerPointerCoercionKind_V2026_06_01 "ReifyFnPointer(Maybe)" = none := rfl

theorem spelling_closure_safe_compat :
    reifyCoercionSafetyCompatible "ClosureFnPointer(Safe)" .unsafe_ = false :=
  (LPointerCoercionKind.reifyCoercionSafetyCompatible_toRustcSpelling_V2026_06_01
    (.closureFnPointer .safe) .unsafe_).trans rfl

theorem widePtr_injective_witness :
    (LWidePtr.ofProv ⟨1, 0⟩ 5 8).toValue ≠ (LWidePtr.ofScalar 65536 5 8).toValue := by
  intro h
  cases LWidePtr.toValue_injective h

/-! ## 9.2 `Unsize` -/

theorem unsize_spec_witnesses :
    unsizeArrayToSliceSpec? (.ref .not (.array u32Ty 5)) (.ref .not (.slice u32Ty)) = some 5 ∧
    unsizeArrayToSliceSpec? (.ref .not (.array u32Ty 5)) (.ref .mut (.slice u32Ty)) = none ∧
    unsizeArrayToSliceSpec? (.rawPtr .not (.array u32Ty 5)) (.ref .not (.slice u32Ty)) = none ∧
    unsizeArrayToSliceSpec? (.ref .mut (.array u32Ty 5)) (.rawPtr .mut (.slice u32Ty)) = some 5 :=
  ⟨rfl, (unsizeArrayToSliceSpec?_mutability_escalation_eq_none u32Ty u32Ty 5).1,
    unsizeArrayToSliceSpec?_rawPtr_to_ref_eq_none _ _ _ _ _, rfl⟩

theorem unsize_spec_iff_witness :
    unsizeArrayToSliceSpec? (arrayPtrSourceKind true .mut u32Ty 5)
      (slicePtrTargetKind false .mut u32Ty) = some 5 :=
  (unsizeArrayToSliceSpec?_array_to_slice_eq_some_iff true false .mut .mut u32Ty u32Ty 5 5).mpr
    ⟨Or.inl rfl, rfl, rfl, rfl⟩

/-- Stack-borrowed `&[u32; 5] -> &[u32]` (64-bit): `.ok` with length `5`. -/
theorem unsize_stack_ok_64 :
    evalRvalue L64 (.cast (.pointerCoercion "Unsize") (cp 1) (sliceTy (.ref .not (.slice u32Ty))))
        testMem testDecls testLayouts64 =
      .ok (LWidePtr.encodeProv ⟨1, 0⟩ 5 8) L64 testMem :=
  (trusted_evalUnsizeCoercion_stack_borrow_backing_iff L64 L64 (cp 1) testMem testDecls
    testLayouts64 true .not u32Ty 3 { kind := .ref .not (.array u32Ty 5), layoutIdx := 1 } ⟨1, 0⟩ 5
    activeEntry backing [] 0 backingElems 0 rfl rfl rfl rfl rfl rfl rfl rfl).2.2.1.mpr rfl

/-- Stack-borrowed `&[u32; 5] -> &[u32]` (32-bit): `.ok` with a 4-byte length word. -/
theorem unsize_stack_ok_32 :
    evalRvalue L32 (.cast (.pointerCoercion "Unsize") (cp 1) (sliceTy (.ref .not (.slice u32Ty))))
        testMem testDecls testLayouts32 =
      .ok (LWidePtr.encodeProv ⟨1, 0⟩ 5 4) L32 testMem :=
  (trusted_evalUnsizeCoercion_stack_borrow_backing_iff L32 L32 (cp 1) testMem testDecls
    testLayouts32 true .not u32Ty 3 { kind := .ref .not (.array u32Ty 5), layoutIdx := 1 } ⟨1, 0⟩ 5
    activeEntry backing [] 0 backingElems 0 rfl rfl rfl rfl rfl rfl rfl rfl).2.2.1.mpr rfl

/-- `.disabled` borrow: `Unsize` faults. -/
theorem unsize_disabled_ub_64 :
    evalRvalue L64 (.cast (.pointerCoercion "Unsize") (cp 3) (sliceTy (.ref .mut (.slice u32Ty))))
        testMem testDecls testLayouts64 = .ub :=
  (trusted_evalUnsizeCoercion_stack_borrow_perm_ub L64 L64 (cp 3) testMem testDecls testLayouts64
    true .mut u32Ty 3 ⟨2, 0⟩ disabledEntry rfl rfl rfl).2

/-- `.frozen` borrow coerced to a *mutable* slice pointer: `Unsize` faults (32-bit). -/
theorem unsize_frozen_mut_ub_32 :
    evalRvalue L32 (.cast (.pointerCoercion "Unsize") (cp 4) (sliceTy (.rawPtr .mut (.slice u32Ty))))
        testMem testDecls testLayouts32 = .ub :=
  (trusted_evalUnsizeCoercion_stack_borrow_perm_ub L32 L32 (cp 4) testMem testDecls testLayouts32
    false .mut u32Ty 3 ⟨3, 0⟩ frozenEntry rfl rfl rfl).2

/-- Unbacked non-null `allocId ≠ 0` raw pointer: `Unsize` succeeds. -/
theorem unsize_unbacked_ok_64 :
    evalRvalue L64 (.cast (.pointerCoercion "Unsize") (cp 2) (sliceTy (.rawPtr .not (.slice u32Ty))))
        testMem testDecls testLayouts64 =
      .ok (LWidePtr.encodeProv ⟨7, 16⟩ 5 8) L64 testMem :=
  (trusted_evalUnsizeCoercion_unbacked_nonzero_allocId L64 L64 (cp 2) testMem testDecls
    testLayouts64 false .not u32Ty 3 { kind := .rawPtr .not (.array u32Ty 5), layoutIdx := 1 }
    ⟨7, 16⟩ 5 rfl rfl rfl rfl rfl rfl).2

/-- Dangling `allocId = 0` pointer to a non-empty array: `Unsize` faults. -/
theorem unsize_dangling_nonempty_ub_64 :
    evalRvalue L64 (.cast (.pointerCoercion "Unsize") (cp 14) (sliceTy (.rawPtr .not (.slice u32Ty))))
        testMem testDecls testLayouts64 = .ub :=
  (trusted_evalUnsizeCoercion_allocId_zero_iff L64 L64 (cp 14) testMem testDecls testLayouts64
    false .not u32Ty 3 { kind := .rawPtr .not (.array u32Ty 5), layoutIdx := 1 } 16 5
    rfl rfl rfl rfl rfl).2.2.2.mpr rfl

/-- Dangling non-null `allocId = 0` pointer to an *empty* array: `Unsize` succeeds (`n = 0`). -/
theorem unsize_dangling_empty_ok_64 :
    evalRvalue L64 (.cast (.pointerCoercion "Unsize") (cp 17) (sliceTy (.ref .not (.slice u32Ty))))
        testMem testDecls testLayouts64 =
      .ok (LWidePtr.encodeProv ⟨0, 16⟩ 0 8) L64 testMem :=
  (trusted_evalUnsizeCoercion_allocId_zero_iff L64 L64 (cp 17) testMem testDecls testLayouts64
    true .not u32Ty 3 { kind := .ref .not (.array u32Ty 0), layoutIdx := 1 } 16 0
    rfl rfl rfl rfl rfl).2.2.1.mpr rfl

/-- Provenance-less raw array pointer (32-bit): `Unsize` to `*const [u32]` succeeds. -/
theorem unsize_scalar_ok_32 :
    evalRvalue L32 (.cast (.pointerCoercion "Unsize") (cp 12) (sliceTy (.rawPtr .not (.slice u32Ty))))
        testMem
        declsScalarRawArray
        testLayouts32 =
      .ok (LWidePtr.encodeScalar 4096 5 4) L32 testMem := by
  have h := (trusted_evalUnsizeCoercion_scalar_iff L32 L32 (cp 12)
    (sliceTy (.rawPtr .not (.slice u32Ty))) testMem
    declsScalarRawArray
    testLayouts32 ⟨4096, 4⟩ rfl rfl).2.2.1 5
  exact h.mpr rfl

/-- Provenance-less pointer coerced to a *reference* slice: `Unsize` faults. -/
theorem unsize_scalar_to_ref_ub_64 :
    evalRvalue L64 (.cast (.pointerCoercion "Unsize") (cp 12) (sliceTy (.ref .not (.slice u32Ty))))
        testMem testDecls testLayouts64 = .ub :=
  (trusted_evalUnsizeCoercion_scalar_to_ref_ub L64 L64 (cp 12) testMem testDecls testLayouts64
    .not u32Ty 3 ⟨4096, 8⟩ rfl rfl).2

/-- Stack borrow of a ZST `.unit` local: `&[u32; 0] -> &[u32]` succeeds with length `0`. -/
theorem unsize_zst_unit_ok_64 :
    evalUnsizeCoercion L64 (cp 30) (sliceTy (.ref .not (.slice u32Ty))) testMem testDecls
        testLayouts64 = .ok (LWidePtr.encodeProv ⟨5, 0⟩ 0 8) L64 testMem :=
  (trusted_evalUnsizeCoercion_stack_borrow_zst_unit_iff L64 L64 (cp 30) testMem testDecls
    testLayouts64 true .not u32Ty 3 { kind := .ref .not (.array u32Ty 0), layoutIdx := 1 } ⟨5, 0⟩ 0
    zstEntry .unit rfl rfl rfl rfl rfl rfl rfl rfl).1.mpr rfl

/-- Live borrow of an `.uninit` local: `Unsize` faults (on both the step and `evalRvalue`). -/
theorem unsize_uninit_ub_64 :
    evalRvalue L64 (.cast (.pointerCoercion "Unsize") (cp 31) (sliceTy (.ref .not (.slice u32Ty))))
        testMem testDecls testLayouts64 = .ub :=
  (trusted_evalUnsizeCoercion_stack_borrow_uninit_ub L64 L64 (cp 31) testMem testDecls
    testLayouts64 true .not u32Ty 3 { kind := .ref .not (.array u32Ty 5), layoutIdx := 1 } ⟨4, 0⟩ 5
    uninitEntry rfl rfl rfl rfl rfl rfl).2

/-- Unborrowed pointer into the 20-byte global: `&[u32; 5] -> &[u32]` succeeds. -/
theorem unsize_global_ok_64 :
    evalRvalue L64 (.cast (.pointerCoercion "Unsize") (cp 32) (sliceTy (.ref .not (.slice u32Ty))))
        testMem testDecls testLayouts64 = .ok (LWidePtr.encodeProv ⟨9, 0⟩ 5 8) L64 testMem :=
  (trusted_evalUnsizeCoercion_global_alloc_iff L64 L64 (cp 32) testMem testDecls testLayouts64
    true .not u32Ty 3 { kind := .ref .not (.array u32Ty 5), layoutIdx := 1 } ⟨9, 0⟩ 5 testGlobal
    rfl rfl rfl rfl rfl).2.2.1.mpr rfl

/-- Read-only global coerced to a *mutable* raw slice pointer: `Unsize` faults (32-bit). -/
theorem unsize_global_readonly_mut_ub_32 :
    evalRvalue L32 (.cast (.pointerCoercion "Unsize") (cp 34) (sliceTy (.rawPtr .mut (.slice u32Ty))))
        testMem testDecls testLayouts32 = .ub :=
  (trusted_evalUnsizeCoercion_global_alloc_iff L32 L32 (cp 34) testMem testDecls testLayouts32
    false .mut u32Ty 3 { kind := .rawPtr .mut (.array u32Ty 5), layoutIdx := 1 } ⟨9, 0⟩ 5 testGlobal
    rfl rfl rfl rfl rfl).2.2.2.mpr rfl

theorem unsize_spec_lemma_witnesses :
    unsizeArrayToSliceSpec? (.ref .mut (.array u32Ty 5)) (.ref .not (.slice u32Ty)) = some 5 ∧
    unsizeArrayToSliceSpec? (.ref .not (.array u32Ty 5)) (.rawPtr .not (.slice u32Ty)) = some 5 ∧
    unsizeArrayToSliceSpec? (.rawPtr .mut (.array u32Ty 5)) (.rawPtr .not (.slice u32Ty)) = some 5 ∧
    unsizeArrayToSliceSpec? (arrayPtrSourceKind true .not u32Ty 5)
      (slicePtrTargetKind true .not (.uint .u8)) = none ∧
    rawPtrUnsizeArrayToSliceLen? (some { kind := .rawPtr .mut (.array u32Ty 5), layoutIdx := 1 })
      (sliceTy (.rawPtr .not (.slice u32Ty))) 4 = some 5 :=
  ⟨(unsizeArrayToSliceSpec?_ref_to_ref .mut .not u32Ty u32Ty 5).trans rfl,
    (unsizeArrayToSliceSpec?_ref_to_rawPtr .not .not u32Ty u32Ty 5).trans rfl,
    (unsizeArrayToSliceSpec?_rawPtr_to_rawPtr .mut .not u32Ty u32Ty 5).trans rfl,
    unsizeArrayToSliceSpec?_elem_mismatch_eq_none true true .not .not u32Ty (.uint .u8) 5 rfl,
    (rawPtrUnsizeArrayToSliceLen?_eq_some_iff .mut .not u32Ty u32Ty 5 5 1 3 4).mpr ⟨rfl, rfl⟩⟩

/-- Cross-frame `callerLocals` borrow (tag `99` targeting caller local `0`, which is out of bounds
in the 1-slot current frame `[.init (.ptr ⟨99, 0⟩ 8)]`): `Unsize` resolves the backing array from
`mem.callerLocals`. -/
def callerBorrowEntry : BorrowEntry :=
  { tag := 99, targetLocal := 1, targetProjection := [], perm := .active }

def memWithCallerLocals : Memory :=
  { testMem with
    borrows := callerBorrowEntry :: testMem.borrows
    callerLocals := [.init .unit, .init backing] }

def refArray5Decl : LocalDecl :=
  { mutability := .not, ty := { kind := .ref .not (.array u32Ty 5), layoutIdx := 1 }, debugName := none }

theorem unsize_callerLocals_ok_64 :
    evalRvalue [.init (.ptr ⟨99, 0⟩ 8)]
        (.cast (.pointerCoercion "Unsize") (cp 0) (sliceTy (.ref .not (.slice u32Ty))))
        memWithCallerLocals [refArray5Decl] testLayouts64 =
      .ok (LWidePtr.encodeProv ⟨99, 0⟩ 5 8) [.init (.ptr ⟨99, 0⟩ 8)] memWithCallerLocals :=
  (trusted_evalUnsizeCoercion_callerLocals_backing_iff
    [.init (.ptr ⟨99, 0⟩ 8)] [.init (.ptr ⟨99, 0⟩ 8)] (cp 0) memWithCallerLocals
    [refArray5Decl] testLayouts64 true .not u32Ty 3
    { kind := .ref .not (.array u32Ty 5), layoutIdx := 1 } ⟨99, 0⟩ 5
    callerBorrowEntry backing [] 0 backingElems 0
    rfl rfl rfl rfl rfl rfl rfl rfl rfl).2.2.1.mpr rfl

/-- Cross-frame `callerLocals` borrow at element offset `1` with array length `5`: the window
`[1 .. 6)` overflows the 5-element caller array, so `Unsize` faults (the `.ub` half of the two-sided
characterization). -/
theorem unsize_callerLocals_out_of_bounds_ub_64 :
    evalRvalue [.init (.ptr ⟨99, 4⟩ 8)]
        (.cast (.pointerCoercion "Unsize") (cp 0) (sliceTy (.ref .not (.slice u32Ty))))
        memWithCallerLocals [refArray5Decl] testLayouts64 = .ub :=
  (trusted_evalUnsizeCoercion_callerLocals_backing_iff
    [.init (.ptr ⟨99, 4⟩ 8)] [.init (.ptr ⟨99, 4⟩ 8)] (cp 0) memWithCallerLocals
    [refArray5Decl] testLayouts64 true .not u32Ty 3
    { kind := .ref .not (.array u32Ty 5), layoutIdx := 1 } ⟨99, 4⟩ 5
    callerBorrowEntry backing [] 0 backingElems 1
    rfl rfl rfl rfl rfl rfl rfl rfl rfl).2.2.2.mpr rfl

/-- Untyped operand (`localDecls = []`, so `operandTy [] _ (cp 1) = none`) on a stack borrow:
`Unsize` infers length `5 - 0 = 5` directly from `backing`. -/
theorem unsize_untyped_stack_ok_64 :
    evalRvalue L64 (.cast (.pointerCoercion "Unsize") (cp 1) (sliceTy (.ref .not (.slice u32Ty))))
        testMem [] testLayouts64 =
      .ok (LWidePtr.encodeProv ⟨1, 0⟩ 5 8) L64 testMem :=
  (trusted_evalUnsizeCoercion_untyped_stack_borrow L64 L64 (cp 1) testMem [] testLayouts64
    true .not u32Ty 3 ⟨1, 0⟩ activeEntry backing [] 0 backingElems 0
    rfl rfl rfl rfl rfl rfl rfl rfl).2

/-- Untyped operand (`localDecls = []`) on the 20-byte global allocation (`allocId = 9`):
`Unsize` infers `20 / 4 = 5` elements (32-bit). -/
theorem unsize_untyped_global_ok_32 :
    evalRvalue L32 (.cast (.pointerCoercion "Unsize") (cp 32) (sliceTy (.ref .not (.slice u32Ty))))
        testMem [] testLayouts32 =
      .ok (LWidePtr.encodeProv ⟨9, 0⟩ 5 4) L32 testMem :=
  (trusted_evalUnsizeCoercion_untyped_global_alloc L32 L32 (cp 32) testMem [] testLayouts32
    true .not u32Ty 3 ⟨9, 0⟩ testGlobal 4 0 5
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).2

/-- Untyped operand (`localDecls = []`) on an unbacked pointer (`allocId = 7`): `Unsize` faults. -/
theorem unsize_untyped_unbacked_ub_64 :
    evalRvalue L64 (.cast (.pointerCoercion "Unsize") (cp 2) (sliceTy (.rawPtr .not (.slice u32Ty))))
        testMem [] testLayouts64 = .ub :=
  (trusted_evalUnsizeCoercion_untyped_unbacked_ub L64 L64 (cp 2) testMem [] testLayouts64
    false .not u32Ty 3 ⟨7, 16⟩ rfl rfl rfl rfl).2

/-! ## 9.3 `MutToConstPointer`, `ArrayToPointer`, reification, `UnsafeFnPointer` -/

/-- `*mut u32 -> *const u32` on a thin provenance pointer (64-bit). -/
theorem mutToConst_thin_ok_64 :
    evalRvalue L64 (.cast (.pointerCoercion "MutToConstPointer") (cp 11)
        { kind := .rawPtr .not u32Ty, layoutIdx := 1 }) testMem testDecls testLayouts64 =
      .ok (.ptr ⟨7, 0⟩ 8) L64 testMem :=
  (trusted_evalRvalue_mutToConstPointer_thin_ptr_iff L64 L64 (cp 11)
    { kind := .rawPtr .not u32Ty, layoutIdx := 1 } testMem testDecls testLayouts64 ⟨7, 0⟩ 8
    rfl).1.mpr ⟨rfl, rfl⟩

/-- `*mut u32 -> *mut u32` is not a `MutToConstPointer` coercion: `.ub`. -/
theorem mutToConst_mut_target_ub_64 :
    evalRvalue L64 (.cast (.pointerCoercion "MutToConstPointer") (cp 11)
        { kind := .rawPtr .mut u32Ty, layoutIdx := 1 }) testMem testDecls testLayouts64 = .ub :=
  (trusted_evalRvalue_mutToConstPointer_thin_ptr_iff L64 L64 (cp 11)
    { kind := .rawPtr .mut u32Ty, layoutIdx := 1 } testMem testDecls testLayouts64 ⟨7, 0⟩ 8
    rfl).2.mpr (fun ⟨_, h⟩ => by cases h)

/-- `*const u32 -> *const u32` (const source) is rejected: `.ub`. -/
theorem mutToConst_const_source_ub_64 :
    evalRvalue L64 (.cast (.pointerCoercion "MutToConstPointer") (cp 12)
        { kind := .rawPtr .not u32Ty, layoutIdx := 1 }) testMem testDecls testLayouts64 = .ub :=
  (trusted_evalRvalue_mutToConstPointer_thin_scalar_iff L64 L64 (cp 12)
    { kind := .rawPtr .not u32Ty, layoutIdx := 1 } testMem testDecls testLayouts64 ⟨4096, 8⟩
    rfl).2.mpr (fun ⟨_, h⟩ => by cases h)

/-- `*mut [u32] -> *const [u32]` preserves the length metadata (32-bit). -/
theorem mutToConst_wide_ok_32 :
    evalRvalue L32 (.cast (.pointerCoercion "MutToConstPointer") (cp 6)
        (sliceTy (.rawPtr .not (.slice u32Ty)))) testMem testDecls testLayouts32 =
      .ok (.aggregate 0 [.ptr ⟨7, 0⟩ 4, .scalar ⟨5, 4⟩]) L32 testMem :=
  (trusted_evalRvalue_mutToConstPointer_wide_ptr_iff L32 L32 (cp 6)
    (sliceTy (.rawPtr .not (.slice u32Ty))) testMem testDecls testLayouts32 ⟨7, 0⟩ 4 ⟨5, 4⟩
    rfl).1.mpr ⟨rfl, rfl, rfl⟩

/-- Provenance-less `*mut u32 -> *const u32` canonicalizes the address. -/
theorem mutToConst_thin_scalar_ok_64 :
    evalRvalue L64 (.cast (.pointerCoercion "MutToConstPointer") (cp 12)
        { kind := .rawPtr .not u32Ty, layoutIdx := 1 }) testMem
        declsScalarRawMut testLayouts64 =
      .ok (.scalar ⟨4096, 8⟩) L64 testMem :=
  (trusted_evalRvalue_mutToConstPointer_thin_scalar_iff L64 L64 (cp 12)
    { kind := .rawPtr .not u32Ty, layoutIdx := 1 } testMem
    declsScalarRawMut testLayouts64 ⟨4096, 8⟩ rfl).1.mpr ⟨rfl, rfl⟩

/-- Provenance-less `*mut [u32] -> *const [u32]` (64-bit). -/
theorem mutToConst_wide_scalar_ok_64 :
    evalRvalue (L64.set 6 (.init (.aggregate 0 [.scalar ⟨4096, 8⟩, .scalar ⟨5, 8⟩])))
        (.cast (.pointerCoercion "MutToConstPointer") (cp 6)
        (sliceTy (.rawPtr .not (.slice u32Ty)))) testMem testDecls testLayouts64 =
      .ok (LWidePtr.encodeScalar 4096 5 8)
        (L64.set 6 (.init (.aggregate 0 [.scalar ⟨4096, 8⟩, .scalar ⟨5, 8⟩]))) testMem :=
  (trusted_evalRvalue_mutToConstPointer_wide_scalar_iff
    (L64.set 6 (.init (.aggregate 0 [.scalar ⟨4096, 8⟩, .scalar ⟨5, 8⟩])))
    (L64.set 6 (.init (.aggregate 0 [.scalar ⟨4096, 8⟩, .scalar ⟨5, 8⟩]))) (cp 6)
    (sliceTy (.rawPtr .not (.slice u32Ty))) testMem testDecls testLayouts64 ⟨4096, 8⟩ ⟨5, 8⟩
    rfl).1.mpr ⟨rfl, rfl, rfl⟩

theorem mutToConst_shape_witnesses :
    mutToConstTargetShape? (some { kind := .rawPtr .mut (.slice u32Ty), layoutIdx := 3 })
        (sliceTy (.rawPtr .not (.slice u32Ty))) = some (some false) ∧
    mutToConstTargetShape? (some { kind := .rawPtr .mut u32Ty, layoutIdx := 1 })
        { kind := .rawPtr .not u32Ty, layoutIdx := 1 } = some none ∧
    mutToConstTargetShape? (some { kind := .rawPtr .mut u32Ty, layoutIdx := 1 })
        { kind := .rawPtr .not (.uint .u8), layoutIdx := 1 } = none :=
  ⟨(mutToConstTargetShape?_rawPtr_mut_to_const _ _ _ _).trans rfl,
    (mutToConstTargetShape?_rawPtr_mut_to_const _ _ _ _).trans rfl,
    (mutToConstTargetShape?_rawPtr_mut_to_const _ _ _ _).trans rfl⟩

def rawMutDynDecl : LocalDecl :=
  { mutability := .not, ty := { kind := .rawPtr .mut (.dynamic "Tr"), layoutIdx := 3 },
    debugName := none }

def declsDynMut : List LocalDecl := testDecls.set 6 rawMutDynDecl

/-- `*mut dyn Tr -> *const dyn Tr` on a vtable-carrying `[.ptr, .ptr]` aggregate preserves the
vtable pointer `⟨65536, 0⟩` (64-bit). -/
theorem mutToConst_dyn_ptr_ok_64 :
    evalRvalue (L64.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .ptr ⟨65536, 0⟩ 8])))
        (.cast (.pointerCoercion "MutToConstPointer") (cp 6)
          (sliceTy (.rawPtr .not (.dynamic "Tr"))))
        testMem declsDynMut testLayouts64 =
      .ok (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .ptr ⟨65536, 0⟩ 8])
        (L64.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .ptr ⟨65536, 0⟩ 8]))) testMem :=
  (trusted_evalRvalue_mutToConstPointer_dyn_ptr_iff
    (L64.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .ptr ⟨65536, 0⟩ 8])))
    (L64.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .ptr ⟨65536, 0⟩ 8]))) (cp 6)
    (sliceTy (.rawPtr .not (.dynamic "Tr"))) testMem declsDynMut testLayouts64 ⟨7, 0⟩ ⟨65536, 0⟩
    8 8 rfl).1.mpr ⟨rfl, rfl, rfl⟩

/-- A vtable-carrying `[.ptr, .ptr]` aggregate is rejected when the target is `*const [u32]`
(`mutToConstTargetShape? = some (some false)`). -/
theorem mutToConst_dyn_ptr_slice_target_ub_64 :
    evalRvalue (L64.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .ptr ⟨65536, 0⟩ 8])))
        (.cast (.pointerCoercion "MutToConstPointer") (cp 6)
          (sliceTy (.rawPtr .not (.slice u32Ty))))
        testMem testDecls testLayouts64 = .ub :=
  (trusted_evalRvalue_mutToConstPointer_dyn_ptr_iff
    (L64.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .ptr ⟨65536, 0⟩ 8])))
    (L64.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .ptr ⟨65536, 0⟩ 8]))) (cp 6)
    (sliceTy (.rawPtr .not (.slice u32Ty))) testMem testDecls testLayouts64 ⟨7, 0⟩ ⟨65536, 0⟩
    8 8 rfl).2.mpr (fun ⟨_, _, h⟩ => by cases h)

/-- Scalar-address, vtable-carrying `*mut dyn Tr -> *const dyn Tr` (32-bit). -/
theorem mutToConst_dyn_scalar_ok_32 :
    evalRvalue (L32.set 6 (.init (.aggregate 0 [.scalar ⟨4096, 4⟩, .ptr ⟨65536, 0⟩ 4])))
        (.cast (.pointerCoercion "MutToConstPointer") (cp 6)
          (sliceTy (.rawPtr .not (.dynamic "Tr"))))
        testMem declsDynMut testLayouts32 =
      .ok (.aggregate 0 [.scalar ⟨4096, 4⟩, .ptr ⟨65536, 0⟩ 4])
        (L32.set 6 (.init (.aggregate 0 [.scalar ⟨4096, 4⟩, .ptr ⟨65536, 0⟩ 4]))) testMem :=
  (trusted_evalRvalue_mutToConstPointer_dyn_scalar_iff
    (L32.set 6 (.init (.aggregate 0 [.scalar ⟨4096, 4⟩, .ptr ⟨65536, 0⟩ 4])))
    (L32.set 6 (.init (.aggregate 0 [.scalar ⟨4096, 4⟩, .ptr ⟨65536, 0⟩ 4]))) (cp 6)
    (sliceTy (.rawPtr .not (.dynamic "Tr"))) testMem declsDynMut testLayouts32 ⟨4096, 4⟩ ⟨65536, 0⟩
    4 rfl).1.mpr ⟨rfl, rfl, rfl⟩

/-- `*const [u32; 5] -> *const u32` on a stack borrow refines to `deriveStackElemThinPtr`, which
allocates the fresh narrowed tag `10` with projection `[.subslice 0 5 false]` at offset `0`. -/
theorem arrayToPointer_stack_narrowing_64 :
    evalRvalue (L64.set 2 (.init (.ptr ⟨1, 0⟩ 8))) (.cast (.pointerCoercion "ArrayToPointer") (cp 2)
        { kind := .rawPtr .not u32Ty, layoutIdx := 1 }) testMem testDecls testLayouts64 =
      .ok (.ptr ⟨10, 0⟩ 8) (L64.set 2 (.init (.ptr ⟨1, 0⟩ 8))) memAfterNarrow := by
  rw [trusted_evalRvalue_arrayToPointer_stack_borrow (L64.set 2 (.init (.ptr ⟨1, 0⟩ 8)))
    (L64.set 2 (.init (.ptr ⟨1, 0⟩ 8))) (cp 2) { kind := .rawPtr .not u32Ty, layoutIdx := 1 }
    testMem testDecls testLayouts64 ⟨1, 0⟩ (some 5) activeEntry rfl rfl rfl]
  exact deriveStackElemThinPtr_fresh_subslice (L64.set 2 (.init (.ptr ⟨1, 0⟩ 8))) testMem ⟨1, 0⟩
    activeEntry 5 8 backing [] 0 backingElems 0 (fun h => by cases h) rfl rfl rfl rfl rfl

/-- `ArrayToPointer` on an unbacked array pointer is the identity. -/
theorem arrayToPointer_unborrowed_ok_32 :
    evalRvalue L32 (.cast (.pointerCoercion "ArrayToPointer") (cp 2)
        { kind := .rawPtr .not u32Ty, layoutIdx := 1 }) testMem testDecls testLayouts32 =
      .ok (.ptr ⟨7, 16⟩ 4) L32 testMem :=
  trusted_evalRvalue_arrayToPointer_unborrowed L32 L32 (cp 2)
    { kind := .rawPtr .not u32Ty, layoutIdx := 1 } testMem testDecls testLayouts32 ⟨7, 16⟩ (some 5)
    rfl rfl rfl

/-- `ArrayToPointer` to a wide raw pointer is not an `ArrayToPointer` coercion: `.ub`. -/
theorem arrayToPointer_wide_target_ub_64 :
    evalRvalue L64 (.cast (.pointerCoercion "ArrayToPointer") (cp 2)
        (sliceTy (.rawPtr .not (.slice u32Ty)))) testMem testDecls testLayouts64 = .ub :=
  trusted_evalRvalue_arrayToPointer_ptr_ub L64 L64 (cp 2) (sliceTy (.rawPtr .not (.slice u32Ty)))
    testMem testDecls testLayouts64 ⟨7, 16⟩ 8 rfl
    (Or.inr (arrayToPointerElemLen?_wide_target_eq_none _ _ _ _ rfl))

/-- Provenance-less `ArrayToPointer` canonicalizes the address. -/
theorem arrayToPointer_scalar_ok_64 :
    evalRvalue L64 (.cast (.pointerCoercion "ArrayToPointer") (cp 12)
        { kind := .rawPtr .not u32Ty, layoutIdx := 1 }) testMem
        declsScalarRawArray
        testLayouts64 =
      .ok (.scalar ⟨4096, 8⟩) L64 testMem :=
  trusted_evalRvalue_arrayToPointer_scalar L64 L64 (cp 12)
    { kind := .rawPtr .not u32Ty, layoutIdx := 1 } testMem
    declsScalarRawArray
    testLayouts64 ⟨4096, 8⟩ (some 5) rfl rfl rfl

theorem arrayToPointer_elemLen_witness :
    arrayToPointerElemLen? (some { kind := .rawPtr .mut (.array u32Ty 5), layoutIdx := 1 })
        { kind := .rawPtr .not u32Ty, layoutIdx := 1 } = some (some 5) :=
  (arrayToPointerElemLen?_rawPtr_array .mut .not u32Ty u32Ty 5 1 1 rfl).trans rfl

/-- `ReifyFnPointer`: the ZST fn item `f` is interned at the first function-pointer `AllocId`
`65536 = fnPtrAllocBase` (64-bit). -/
theorem reify_fnItem_ok_64 :
    evalRvalue L64 (.cast (.pointerCoercion "ReifyFnPointer") (cp 7) { kind := fnSigSafe, layoutIdx := 1 })
        testMem testDecls testLayouts64 =
      .ok (.ptr ⟨65536, 0⟩ 8) L64 memAfterInternF :=
  trusted_evalRvalue_reifyFnPointer_ok L64 L64 (cp 7) { kind := fnSigSafe, layoutIdx := 1 } testMem
    testDecls testLayouts64 "ReifyFnPointer" .unit [] (.tuple []) .safe .rust "f" [] rfl rfl rfl rfl
    rfl rfl rfl rfl rfl

theorem reify_intern_fresh_witness :
    isFnPtrAllocId (internFnPtr testMem "f" [] (some fnSigSafe)).1 = true :=
  (internFnPtr_fresh testMem "f" [] (some fnSigSafe) rfl).1

/-- `ClosureFnPointer(Safe)` on the captureless closure `c` (32-bit: the result is still an
8-byte function pointer). -/
theorem reify_closure_ok_32 :
    evalRvalue L32 (.cast (.pointerCoercion "ClosureFnPointer(Safe)") (cp 9)
        { kind := fnSigSafe, layoutIdx := 1 }) testMem testDecls testLayouts32 =
      .ok (.ptr ⟨65536, 0⟩ 8) L32 memAfterInternC :=
  trusted_evalRvalue_reifyFnPointer_ok L32 L32 (cp 9) { kind := fnSigSafe, layoutIdx := 1 } testMem
    testDecls testLayouts32 "ClosureFnPointer(Safe)" (.aggregate 0 []) [] (.tuple []) .safe .rust
    "c" [] rfl rfl rfl rfl rfl rfl rfl
    (extractReifyCoercionTarget?_captureless_closure _ rfl "c" 0) rfl

/-- Capturing closure: `ClosureFnPointer` faults (non-ZST value and no reification target). -/
theorem reify_capturing_closure_ub_64 :
    evalRvalue L64 (.cast (.pointerCoercion "ClosureFnPointer") (cp 10)
        { kind := fnSigSafe, layoutIdx := 1 }) testMem testDecls testLayouts64 = .ub :=
  trusted_evalRvalue_reifyFnPointer_ub L64 L64 (cp 10) { kind := fnSigSafe, layoutIdx := 1 } testMem
    testDecls testLayouts64 "ClosureFnPointer" (.aggregate 0 [.scalar ⟨7, 4⟩]) rfl rfl rfl
    (Or.inl rfl)

theorem reify_capturing_closure_target_none :
    extractReifyCoercionTarget? "ClosureFnPointer"
      (some { kind := .closure "d" [u32Ty], layoutIdx := 1 }) = none :=
  extractReifyCoercionTarget?_capturing_closure_eq_none _ rfl "d" u32Ty [] 1

/-- `ReifyFnPointer` to a `rustIntrinsic` ABI faults. -/
theorem reify_intrinsic_ub_64 :
    evalRvalue L64 (.cast (.pointerCoercion "ReifyFnPointer") (cp 7)
        { kind := fnSigIntrinsic, layoutIdx := 1 }) testMem testDecls testLayouts64 = .ub :=
  trusted_evalRvalue_reifyFnPointer_ub L64 L64 (cp 7) { kind := fnSigIntrinsic, layoutIdx := 1 }
    testMem testDecls testLayouts64 "ReifyFnPointer" .unit rfl rfl rfl
    (Or.inr (fun _ _ _ _ h => by cases h; exact Or.inl rfl))

/-- `ReifyFnPointer(Safe)` to an `unsafe fn` target faults (safety mismatch). -/
theorem reify_safety_mismatch_ub_64 :
    evalRvalue L64 (.cast (.pointerCoercion "ReifyFnPointer(Safe)") (cp 7)
        { kind := fnSigUnsafe, layoutIdx := 1 }) testMem testDecls testLayouts64 = .ub :=
  trusted_evalRvalue_reifyFnPointer_ub L64 L64 (cp 7) { kind := fnSigUnsafe, layoutIdx := 1 }
    testMem testDecls testLayouts64 "ReifyFnPointer(Safe)" .unit rfl rfl rfl
    (Or.inr (fun _ _ _ _ h => by cases h; exact Or.inr (Or.inl rfl)))

/-- Every reifying `LPointerCoercionKind` dispatches through its spelling. -/
theorem reify_dispatch_witness :
    evalRvalue L64 (.cast (.pointerCoercion
        (LPointerCoercionKind.toRustcSpelling_V2026_06_01 (.closureFnPointer .unsafe_))) (cp 9)
        { kind := fnSigUnsafe, layoutIdx := 1 }) testMem testDecls testLayouts64 =
      reifyFnPointerStep L64 (cp 9) { kind := fnSigUnsafe, layoutIdx := 1 } testMem testDecls
        testLayouts64 "ClosureFnPointer(Unsafe)" :=
  evalRvalue_cast_reifyFnPointer_eq_of_isReify _ _ _ _ _ _ (.closureFnPointer .unsafe_) rfl

/-- `UnsafeFnPointer`: a safe 8-byte `fn()` pointer in the synthetic range coerces to `unsafe fn()`. -/
theorem unsafeFnPtr_ok_64 :
    evalRvalue L64 (.cast (.pointerCoercion "UnsafeFnPointer") (cp 8)
        { kind := fnSigUnsafe, layoutIdx := 1 }) testMem testDecls testLayouts64 =
      .ok (.ptr ⟨65536, 0⟩ 8) L64 testMem :=
  (trusted_evalRvalue_unsafeFnPointer_iff L64 L64 (cp 8) { kind := fnSigUnsafe, layoutIdx := 1 }
    testMem testDecls testLayouts64 ⟨65536, 0⟩ 8 [] (.tuple []) .rust rfl rfl).1.mpr ⟨rfl, rfl, rfl⟩

/-- `UnsafeFnPointer` to a *safe* `fn` pointer faults. -/
theorem unsafeFnPtr_safe_target_ub_64 :
    evalRvalue L64 (.cast (.pointerCoercion "UnsafeFnPointer") (cp 8)
        { kind := fnSigSafe, layoutIdx := 1 }) testMem testDecls testLayouts64 = .ub :=
  trusted_evalRvalue_unsafeFnPointer_safe_target_ub L64 L64 (cp 8)
    { kind := fnSigSafe, layoutIdx := 1 } testMem testDecls testLayouts64 ⟨65536, 0⟩ 8 [] (.tuple [])
    .rust rfl rfl

/-- `UnsafeFnPointer` on an offset function pointer faults. -/
theorem unsafeFnPtr_offset_ub_64 :
    evalRvalue (L64.set 8 (.init (.ptr ⟨65536, 4⟩ 8))) (.cast (.pointerCoercion "UnsafeFnPointer")
        (cp 8) { kind := fnSigUnsafe, layoutIdx := 1 }) testMem testDecls testLayouts64 = .ub :=
  (trusted_evalRvalue_unsafeFnPointer_iff (L64.set 8 (.init (.ptr ⟨65536, 4⟩ 8)))
    (L64.set 8 (.init (.ptr ⟨65536, 4⟩ 8))) (cp 8) { kind := fnSigUnsafe, layoutIdx := 1 } testMem
    testDecls testLayouts64 ⟨65536, 4⟩ 8 [] (.tuple []) .rust rfl rfl).2.mpr
    (fun ⟨_, _, h⟩ => by
      rw [unsafeFnPtrValid_eq_false_of_offset_or_borrow _ _ _ _ _ _ (Or.inl (by decide))] at h
      cases h)

theorem reify_fnDef_target_witness :
    extractReifyCoercionTarget? "ReifyFnPointer" (some { kind := .fnDef "f" [], layoutIdx := 0 }) =
      some ("f", []) :=
  extractReifyCoercionTarget?_fnDef "ReifyFnPointer" rfl "f" [] 0

/-- Re-reifying `f` after it was interned reuses `AllocId 65536` and leaves memory unchanged. -/
theorem reify_intern_existing_witness :
    internFnPtr memAfterInternF "f" [] (some fnSigSafe) = (65536, memAfterInternF) :=
  internFnPtr_existing memAfterInternF "f" [] (some fnSigSafe) fnEntryF rfl

/-- … so reifying `f` twice yields the same function pointer (64-bit). -/
theorem reify_twice_same_ptr_64 :
    evalRvalue L64 (.cast (.pointerCoercion "ReifyFnPointer") (cp 7) { kind := fnSigSafe, layoutIdx := 1 })
        memAfterInternF testDecls testLayouts64 = .ok (.ptr ⟨65536, 0⟩ 8) L64 memAfterInternF :=
  trusted_evalRvalue_reifyFnPointer_ok L64 L64 (cp 7) { kind := fnSigSafe, layoutIdx := 1 }
    memAfterInternF testDecls testLayouts64 "ReifyFnPointer" .unit [] (.tuple []) .safe .rust "f" []
    rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- `UnsafeFnPointer` from an `unsafe fn` source type is rejected; a stack-borrowed pointer is
rejected. -/
theorem unsafeFnPtr_invalid_witnesses :
    unsafeFnPtrSrcTyValid (some { kind := fnSigUnsafe, layoutIdx := 1 }) [] (.tuple []) .rust = false ∧
    unsafeFnPtrValid testMem ⟨1, 0⟩ 8 [] (.tuple []) .rust = false :=
  ⟨unsafeFnPtrSrcTyValid_unsafe_source_eq_false _ _ _ _ _ _ _,
    unsafeFnPtrValid_eq_false_of_offset_or_borrow _ _ _ _ _ _ (Or.inr ⟨activeEntry, rfl⟩)⟩

/-- Minimal `ArgAbi` for a unit return. -/
def unitRetAbi : ArgAbi :=
  { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory,
                fields := .arbitrary [] [], variants := .single 0, isUninhabited := false,
                fieldLayouts := [] }
    mode := .ignore }

/-- A `CapturedMir` callee for `"f"` whose own `FnAbi.conv` is `.rustIntrinsic`. -/
def intrinsicCalleeF : CapturedMir := {
  defPath := "f"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [{ mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 }, debugName := none }]
  basicBlocks := []
  fnAbi := { args := [], ret := unitRetAbi, conv := .rustIntrinsic, canUnwind := false }
  layouts := testLayouts64
  allocations := [] }

/-- A `CapturedMir` callee for `"f"` with `argCount = 1` (mismatching a 0-arg `fn()` target). -/
def arityMismatchCalleeF : CapturedMir := {
  intrinsicCalleeF with
  argCount := 1
  fnAbi := { args := [], ret := unitRetAbi, conv := .rust, canUnwind := true } }

/-- Reifying `"f"` into a `"Rust"` `fn()` pointer faults when `"f"` resolves in `mem.callees` to a
`.rustIntrinsic` body (`checkCalleeSig = false`). -/
theorem reify_intrinsic_callee_ub_64 :
    evalRvalue L64 (.cast (.pointerCoercion "ReifyFnPointer") (cp 7)
        { kind := fnSigSafe, layoutIdx := 1 })
        { testMem with callees := [intrinsicCalleeF] } testDecls testLayouts64 = .ub :=
  trusted_evalRvalue_reifyFnPointer_ub L64 L64 (cp 7) { kind := fnSigSafe, layoutIdx := 1 }
    { testMem with callees := [intrinsicCalleeF] } testDecls testLayouts64 "ReifyFnPointer" .unit
    rfl rfl rfl
    (Or.inr (fun _ _ _ _ h => by
      cases h
      exact Or.inr (Or.inr (Or.inr (fun _ _ hT => by
        cases hT
        exact checkCalleeSig_rustIntrinsic_callee_eq_false intrinsicCalleeF [] "f" [] (.tuple [])
          .rust [] [] intrinsicCalleeF [] rfl rfl)))))

/-- Reifying `"f"` into a 0-arg `fn()` pointer faults when `"f"` resolves in `mem.callees` to a
1-arg body (`checkCalleeSig = false`). -/
theorem reify_arity_mismatch_callee_ub_64 :
    evalRvalue L64 (.cast (.pointerCoercion "ReifyFnPointer") (cp 7)
        { kind := fnSigSafe, layoutIdx := 1 })
        { testMem with callees := [arityMismatchCalleeF] } testDecls testLayouts64 = .ub :=
  trusted_evalRvalue_reifyFnPointer_ub L64 L64 (cp 7) { kind := fnSigSafe, layoutIdx := 1 }
    { testMem with callees := [arityMismatchCalleeF] } testDecls testLayouts64 "ReifyFnPointer" .unit
    rfl rfl rfl
    (Or.inr (fun _ _ _ _ h => by
      cases h
      exact Or.inr (Or.inr (Or.inr (fun _ _ hT => by
        cases hT
        exact checkCalleeSig_arity_or_abi_mismatch_eq_false arityMismatchCalleeF [] "f" []
          (.tuple []) .rust [] [] arityMismatchCalleeF [] rfl (Or.inl (by decide)))))))

/-! ## 9.4 `FnPtrToPtr` -/

/-- `fn() as *const u32` preserves the function pointer's provenance (64-bit). -/
theorem fnPtrToPtr_ok_64 :
    evalRvalue L64 (.cast .fnPtrToPtr (cp 8) { kind := .rawPtr .not u32Ty, layoutIdx := 1 }) testMem
        testDecls testLayouts64 = .ok (.ptr ⟨65536, 0⟩ 8) L64 testMem :=
  (trusted_evalRvalue_fnPtrToPtr_iff L64 L64 (cp 8) { kind := .rawPtr .not u32Ty, layoutIdx := 1 }
    testMem testDecls testLayouts64 ⟨65536, 0⟩ 8 rfl).1.mpr ⟨rfl, rfl, rfl⟩

/-- `fn() as *const [u32]` (wide target) faults. -/
theorem fnPtrToPtr_wide_target_ub_64 :
    evalRvalue L64 (.cast .fnPtrToPtr (cp 8) (sliceTy (.rawPtr .not (.slice u32Ty)))) testMem
        testDecls testLayouts64 = .ub :=
  trusted_evalRvalue_fnPtrToPtr_wide_target_ub L64 L64 (cp 8) (sliceTy (.rawPtr .not (.slice u32Ty)))
    testMem testDecls testLayouts64 ⟨65536, 0⟩ 8 rfl
    (isThinRawPtrTy_eq_false_of_wide_or_ref _ (Or.inl ⟨.not, u32Ty, rfl⟩))

/-- `fn() as &u32` (reference target) faults (32-bit). -/
theorem fnPtrToPtr_ref_target_ub_32 :
    evalRvalue L32 (.cast .fnPtrToPtr (cp 8) { kind := .ref .not u32Ty, layoutIdx := 1 }) testMem
        testDecls testLayouts32 = .ub :=
  trusted_evalRvalue_fnPtrToPtr_wide_target_ub L32 L32 (cp 8) { kind := .ref .not u32Ty, layoutIdx := 1 }
    testMem testDecls testLayouts32 ⟨65536, 0⟩ 8 rfl
    (isThinRawPtrTy_eq_false_of_wide_or_ref _ (Or.inr (Or.inr ⟨.not, u32Ty, rfl⟩)))

/-- An offset / stack-borrowed function pointer is rejected by `FnPtrToPtr`. -/
theorem fnPtrToPtr_invalid_ptr_witnesses :
    fnPtrToPtrPtrValid testMem ⟨65536, 4⟩ 8 = false ∧ fnPtrToPtrPtrValid testMem ⟨1, 0⟩ 8 = false ∧
    fnPtrToPtrSrcTyValid (some { kind := fnSigIntrinsic, layoutIdx := 1 }) = false :=
  ⟨fnPtrToPtrPtrValid_eq_false _ _ _ (Or.inr (Or.inl (by decide))),
    fnPtrToPtrPtrValid_eq_false _ _ _ (Or.inr (Or.inr ⟨activeEntry, rfl⟩)),
    fnPtrToPtrSrcTyValid_rustIntrinsic_eq_false _ _ _ _⟩

/-! ## 9.5 `PtrToPtr` -/

/-- Wide -> thin on a stack-borrowed slice pointer refines to `deriveStackElemThinPtr` (element count
`5` from the metadata). -/
theorem ptrToPtr_wide_to_thin_stack_64 :
    evalRvalue L64 (.cast .ptrToPtr (cp 5) { kind := .rawPtr .not u32Ty, layoutIdx := 1 }) testMem
        testDecls testLayouts64 =
      deriveStackElemThinPtr L64 testMem ⟨1, 0⟩ activeEntry (some 5) 8 :=
  trusted_evalRvalue_ptrToPtr_wide_to_thin_stack_borrow L64 L64 (cp 5)
    { kind := .rawPtr .not u32Ty, layoutIdx := 1 } testMem testDecls testLayouts64 ⟨1, 0⟩ ⟨5, 8⟩
    activeEntry rfl rfl rfl rfl

/-- Wide -> thin on an unbacked slice pointer strips the metadata (32-bit). -/
theorem ptrToPtr_wide_to_thin_unborrowed_32 :
    evalRvalue L32 (.cast .ptrToPtr (cp 6) { kind := .rawPtr .not u32Ty, layoutIdx := 1 }) testMem
        testDecls testLayouts32 = .ok (.ptr ⟨7, 0⟩ 4) L32 testMem :=
  trusted_evalRvalue_ptrToPtr_wide_to_thin_unborrowed L32 L32 (cp 6)
    { kind := .rawPtr .not u32Ty, layoutIdx := 1 } testMem testDecls testLayouts32 ⟨7, 0⟩ ⟨5, 4⟩
    rfl rfl rfl rfl

/-- Wide -> wide preserves the slice metadata unchanged (64-bit). -/
theorem ptrToPtr_wide_to_wide_64 :
    evalRvalue L64 (.cast .ptrToPtr (cp 6) (sliceTy (.rawPtr .not (.slice (.uint .u8))))) testMem
        testDecls testLayouts64 = .ok (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .scalar ⟨5, 8⟩]) L64 testMem :=
  trusted_evalRvalue_ptrToPtr_wide_to_wide L64 L64 (cp 6) (sliceTy (.rawPtr .not (.slice (.uint .u8))))
    testMem testDecls testLayouts64 ⟨7, 0⟩ ⟨5, 8⟩ rfl rfl rfl

/-- Slice -> `dyn Trait` raw pointer faults. -/
theorem ptrToPtr_slice_to_dyn_ub_64 :
    evalRvalue L64 (.cast .ptrToPtr (cp 6) (sliceTy (.rawPtr .not (.dynamic "Tr")))) testMem
        testDecls testLayouts64 = .ub :=
  trusted_evalRvalue_ptrToPtr_slice_to_dyn_ub L64 L64 (cp 6) (sliceTy (.rawPtr .not (.dynamic "Tr")))
    testMem testDecls testLayouts64 ⟨7, 0⟩ ⟨5, 8⟩ rfl rfl rfl rfl

/-- A 4-byte metadata word on a 64-bit layout faults under every target. -/
theorem ptrToPtr_width_ub_64 :
    evalRvalue (L64.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .scalar ⟨5, 4⟩]))) (.cast .ptrToPtr
        (cp 6) { kind := .rawPtr .not u32Ty, layoutIdx := 1 }) testMem testDecls testLayouts64 = .ub :=
  trusted_evalRvalue_ptrToPtr_wide_ptr_width_ub
    (L64.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .scalar ⟨5, 4⟩])))
    (L64.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .scalar ⟨5, 4⟩]))) (cp 6)
    { kind := .rawPtr .not u32Ty, layoutIdx := 1 } testMem testDecls testLayouts64 ⟨7, 0⟩ 8 ⟨5, 4⟩
    rfl (Or.inr (by decide))

/-- Provenance-less wide -> thin returns the canonical address (64-bit). -/
theorem ptrToPtr_wide_scalar_to_thin_64 :
    evalRvalue (L64.set 6 (.init (.aggregate 0 [.scalar ⟨4096, 8⟩, .scalar ⟨5, 8⟩])))
        (.cast .ptrToPtr (cp 6) { kind := .rawPtr .not u32Ty, layoutIdx := 1 }) testMem testDecls
        testLayouts64 =
      .ok (.scalar ⟨4096, 8⟩) (L64.set 6 (.init (.aggregate 0 [.scalar ⟨4096, 8⟩, .scalar ⟨5, 8⟩])))
        testMem :=
  trusted_evalRvalue_ptrToPtr_wide_scalar_to_thin
    (L64.set 6 (.init (.aggregate 0 [.scalar ⟨4096, 8⟩, .scalar ⟨5, 8⟩])))
    (L64.set 6 (.init (.aggregate 0 [.scalar ⟨4096, 8⟩, .scalar ⟨5, 8⟩]))) (cp 6)
    { kind := .rawPtr .not u32Ty, layoutIdx := 1 } testMem testDecls testLayouts64 ⟨4096, 8⟩ ⟨5, 8⟩
    rfl rfl rfl rfl

/-- Provenance-less wide -> wide preserves the metadata (32-bit). -/
theorem ptrToPtr_wide_scalar_to_wide_32 :
    evalRvalue (L32.set 6 (.init (.aggregate 0 [.scalar ⟨4096, 4⟩, .scalar ⟨5, 4⟩])))
        (.cast .ptrToPtr (cp 6) (sliceTy (.rawPtr .not (.slice u32Ty)))) testMem testDecls
        testLayouts32 =
      .ok (LWidePtr.encodeScalar 4096 5 4)
        (L32.set 6 (.init (.aggregate 0 [.scalar ⟨4096, 4⟩, .scalar ⟨5, 4⟩]))) testMem :=
  trusted_evalRvalue_ptrToPtr_wide_scalar_to_wide
    (L32.set 6 (.init (.aggregate 0 [.scalar ⟨4096, 4⟩, .scalar ⟨5, 4⟩])))
    (L32.set 6 (.init (.aggregate 0 [.scalar ⟨4096, 4⟩, .scalar ⟨5, 4⟩]))) (cp 6)
    (sliceTy (.rawPtr .not (.slice u32Ty))) testMem testDecls testLayouts32 ⟨4096, 4⟩ ⟨5, 4⟩
    rfl rfl rfl rfl

/-- Thin -> wide faults (no metadata can be synthesized). -/
theorem ptrToPtr_thin_to_wide_ub_64 :
    evalRvalue L64 (.cast .ptrToPtr (cp 11) (sliceTy (.rawPtr .not (.slice u32Ty)))) testMem
        testDecls testLayouts64 = .ub :=
  trusted_evalRvalue_ptrToPtr_thin_to_wide_ub L64 L64 (cp 11) (sliceTy (.rawPtr .not (.slice u32Ty)))
    testMem testDecls testLayouts64 ⟨7, 0⟩ 8 rfl rfl

/-- Wide `dyn` `[.ptr, .ptr]` -> thin `*const u32` strips the vtable pointer directly (64-bit). -/
theorem ptrToPtr_dyn_to_thin_64 :
    evalRvalue (L64.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .ptr ⟨65536, 0⟩ 8])))
        (.cast .ptrToPtr (cp 6) { kind := .rawPtr .not u32Ty, layoutIdx := 1 })
        testMem declsDynMut testLayouts64 =
      .ok (.ptr ⟨7, 0⟩ 8)
        (L64.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .ptr ⟨65536, 0⟩ 8]))) testMem :=
  trusted_evalRvalue_ptrToPtr_dyn_to_thin
    (L64.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .ptr ⟨65536, 0⟩ 8])))
    (L64.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .ptr ⟨65536, 0⟩ 8]))) (cp 6)
    { kind := .rawPtr .not u32Ty, layoutIdx := 1 } testMem declsDynMut testLayouts64 ⟨7, 0⟩
    ⟨65536, 0⟩ rfl rfl

/-- Wide `dyn` `[.ptr, .ptr]` -> wide `*const dyn Tr` preserves the vtable pointer (32-bit). -/
theorem ptrToPtr_dyn_to_dyn_32 :
    evalRvalue (L32.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 4, .ptr ⟨65536, 0⟩ 4])))
        (.cast .ptrToPtr (cp 6) (sliceTy (.rawPtr .not (.dynamic "Tr"))))
        testMem declsDynMut testLayouts32 =
      .ok (.aggregate 0 [.ptr ⟨7, 0⟩ 4, .ptr ⟨65536, 0⟩ 4])
        (L32.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 4, .ptr ⟨65536, 0⟩ 4]))) testMem :=
  trusted_evalRvalue_ptrToPtr_dyn_to_dyn
    (L32.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 4, .ptr ⟨65536, 0⟩ 4])))
    (L32.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 4, .ptr ⟨65536, 0⟩ 4]))) (cp 6)
    (sliceTy (.rawPtr .not (.dynamic "Tr"))) testMem declsDynMut testLayouts32 ⟨7, 0⟩ ⟨65536, 0⟩
    rfl rfl rfl

/-- Wide `dyn` `[.ptr, .ptr]` -> `*const [u32]` faults with `.ub` (64-bit). -/
theorem ptrToPtr_dyn_to_slice_ub_64 :
    evalRvalue (L64.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .ptr ⟨65536, 0⟩ 8])))
        (.cast .ptrToPtr (cp 6) (sliceTy (.rawPtr .not (.slice u32Ty))))
        testMem declsDynMut testLayouts64 = .ub :=
  trusted_evalRvalue_ptrToPtr_dyn_to_slice_ub
    (L64.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .ptr ⟨65536, 0⟩ 8])))
    (L64.set 6 (.init (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .ptr ⟨65536, 0⟩ 8]))) (cp 6)
    (sliceTy (.rawPtr .not (.slice u32Ty))) testMem declsDynMut testLayouts64 ⟨7, 0⟩ ⟨65536, 0⟩
    8 8 rfl rfl

/-! ## 3.B.1 `AggregateKind.rawPtr` -/

section PlaceAndRvalueWitnesses

open Anneal.Mir.PlaceAndRvalue

/-- `ptr::from_raw_parts::<[u32]>(p, 5)` (64-bit). -/
theorem rawPtrAgg_wide_ok_64 :
    evalRvalue L64 (.aggregate (.rawPtr { kind := .slice u32Ty, layoutIdx := 3 } .not) [cp 11, cp 18])
        testMem testDecls testLayouts64 =
      .ok (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .scalar ⟨5, 8⟩]) L64 testMem :=
  (trusted_evalRvalue_aggregate_rawPtr_wide_ptr_iff L64 L64 { kind := .slice u32Ty, layoutIdx := 3 } .not
    [cp 11, cp 18] testMem testDecls testLayouts64 ⟨7, 0⟩ 8 ⟨5, 8⟩ rfl
    (wideAggregatePointeeIsDyn?_slice _ _)).1.mpr ⟨rfl, rfl⟩

/-- `ptr::from_raw_parts::<[u32]>(addr, 5)` on a provenance-less address (32-bit). -/
theorem rawPtrAgg_wide_scalar_ok_32 :
    evalRvalue L32 (.aggregate (.rawPtr { kind := .slice u32Ty, layoutIdx := 3 } .not) [cp 12, cp 18])
        testMem testDecls testLayouts32 =
      .ok (.aggregate 0 [.scalar ⟨4096, 4⟩, .scalar ⟨5, 4⟩]) L32 testMem :=
  (trusted_evalRvalue_aggregate_rawPtr_wide_scalar_iff L32 L32 { kind := .slice u32Ty, layoutIdx := 3 }
    .not [cp 12, cp 18] testMem testDecls testLayouts32 ⟨4096, 4⟩ ⟨5, 4⟩ rfl
    (wideAggregatePointeeIsDyn?_slice _ _)).1.mpr ⟨rfl, rfl⟩

/-- Wide metadata on a sized `u32` pointee faults. -/
theorem rawPtrAgg_wide_on_sized_ub_64 :
    evalRvalue L64 (.aggregate (.rawPtr { kind := u32Ty, layoutIdx := 1 } .not) [cp 11, cp 18])
        testMem testDecls testLayouts64 = .ub :=
  trusted_evalRvalue_aggregate_rawPtr_wide_on_sized_ub L64 L64 { kind := u32Ty, layoutIdx := 1 } .not
    [cp 11, cp 18] testMem testDecls testLayouts64 ⟨7, 0⟩ 8 ⟨5, 8⟩ rfl
    (wideAggregatePointeeIsDyn?_uint _ _)

/-- A 4-byte length word on a 64-bit layout faults. -/
theorem rawPtrAgg_wide_width_ub_64 :
    evalRvalue (L64.set 18 (.init (.scalar ⟨5, 4⟩)))
        (.aggregate (.rawPtr { kind := .slice u32Ty, layoutIdx := 3 } .not) [cp 11, cp 18])
        testMem testDecls testLayouts64 = .ub :=
  (trusted_evalRvalue_aggregate_rawPtr_wide_ptr_iff (L64.set 18 (.init (.scalar ⟨5, 4⟩)))
    (L64.set 18 (.init (.scalar ⟨5, 4⟩))) { kind := .slice u32Ty, layoutIdx := 3 } .not
    [cp 11, cp 18] testMem testDecls testLayouts64 ⟨7, 0⟩ 8 ⟨5, 4⟩ rfl
    (wideAggregatePointeeIsDyn?_slice _ _)).2.mpr (fun ⟨_, h⟩ => by cases h)

/-- Thin `ptr::from_raw_parts::<u32>(p, ())` (32-bit). -/
theorem rawPtrAgg_thin_ok_32 :
    evalRvalue L32 (.aggregate (.rawPtr { kind := u32Ty, layoutIdx := 1 } .not) [cp 11, cp 19])
        testMem testDecls testLayouts32 = .ok (.ptr ⟨7, 0⟩ 4) L32 testMem :=
  (trusted_evalRvalue_aggregate_rawPtr_thin_iff L32 L32 { kind := u32Ty, layoutIdx := 1 } .not
    [cp 11, cp 19] testMem testDecls testLayouts32 ⟨7, 0⟩ 4 rfl).1.mpr ⟨rfl, rfl⟩

/-- Thin `()` metadata on an unsized `[u32]` pointee faults. -/
theorem rawPtrAgg_thin_on_unsized_ub_64 :
    evalRvalue L64 (.aggregate (.rawPtr { kind := .slice u32Ty, layoutIdx := 3 } .not) [cp 11, cp 19])
        testMem testDecls testLayouts64 = .ub :=
  (trusted_evalRvalue_aggregate_rawPtr_thin_iff L64 L64 { kind := .slice u32Ty, layoutIdx := 3 } .not
    [cp 11, cp 19] testMem testDecls testLayouts64 ⟨7, 0⟩ 8 rfl).2.mpr (fun ⟨h, _⟩ => by cases h)

/-! ## 3.B.2 `UnOp.ptrMetadata` -/

/-- `PtrMetadata` of a wide slice pointer returns its length word (64-bit). -/
theorem ptrMetadata_wide_ok_64 :
    evalRvalue L64 (.unaryOp .ptrMetadata (cp 5)) testMem testDecls testLayouts64 =
      .ok (.scalar ⟨5, 8⟩) L64 testMem :=
  (trusted_evalRvalue_ptrMetadata_wide_ptr_iff L64 L64 (cp 5) testMem testDecls testLayouts64
    ⟨1, 0⟩ 8 ⟨5, 8⟩ rfl).1.mpr ⟨rfl, rfl⟩

/-- `PtrMetadata` of a thin pointer is `()` (32-bit). -/
theorem ptrMetadata_thin_ok_32 :
    evalRvalue L32 (.unaryOp .ptrMetadata (cp 11)) testMem testDecls testLayouts32 =
      .ok .unit L32 testMem :=
  (trusted_evalRvalue_ptrMetadata_thin_ptr_iff L32 L32 (cp 11) testMem testDecls testLayouts32
    ⟨7, 0⟩ 4 rfl).1.mpr rfl

/-- `Trusted` function pointers are 8 bytes: `PtrMetadata` of `fn()` is `()` on 64-bit … -/
theorem ptrMetadata_fnPtr_ok_64 :
    evalRvalue L64 (.unaryOp .ptrMetadata (cp 8)) testMem testDecls testLayouts64 =
      .ok .unit L64 testMem :=
  (trusted_evalRvalue_ptrMetadata_fnPtr8_iff_ptrBytes L64 L64 (cp 8) testMem testDecls
    testLayouts64 ⟨65536, 0⟩ rfl).1 ptrBytes64

/-- … but faults on a 32-bit layout (the 8-byte function pointer is not pointer-width). -/
theorem ptrMetadata_fnPtr_ub_32 :
    evalRvalue L32 (.unaryOp .ptrMetadata (cp 8)) testMem testDecls testLayouts32 = .ub :=
  (trusted_evalRvalue_ptrMetadata_fnPtr8_iff_ptrBytes L32 L32 (cp 8) testMem testDecls
    testLayouts32 ⟨65536, 0⟩ rfl).2 ptrBytes32

/-- `PtrMetadata` of a provenance-less wide pointer returns the canonical length (32-bit). -/
theorem ptrMetadata_wide_scalar_ok_32 :
    evalRvalue L32 (.unaryOp .ptrMetadata (cp 27)) testMem testDecls testLayouts32 =
      .ok (.scalar ⟨5, 4⟩) L32 testMem :=
  (trusted_evalRvalue_ptrMetadata_wide_scalar_iff L32 L32 (cp 27) testMem testDecls testLayouts32
    ⟨4096, 4⟩ ⟨5, 4⟩ rfl rfl).1.mpr ⟨rfl, rfl⟩

/-! ## 3.B.3 `Rvalue.len` of a dereferenced slice -/

def derefPlace (i : Nat) : Place := { local_ := i, projection := [.deref] }

/-- `(*s).len()` on a stack-borrowed `&[u32]` of the 5-element backing array (64-bit). -/
theorem len_stack_ok_64 :
    evalRvalue L64 (.len (derefPlace 15)) testMem testDecls testLayouts64 =
      .ok (.scalar ⟨5, 8⟩) L64 testMem :=
  (trusted_evalRvalue_len_deref_slice_iff L64 L64 (derefPlace 15) testMem testDecls testLayouts64 []
    u32Ty _ ⟨1, 0⟩ 8 ⟨5, 8⟩ rfl rfl rfl).1.mpr
    ⟨rfl, rfl, (sliceLenBorrowOk_stack_backing L64 testMem testDecls testLayouts64 u32Ty ⟨1, 0⟩
      ⟨5, 8⟩ activeEntry backing [] 0 backingElems 0 rfl (fun h => by cases h) rfl rfl rfl).trans
        rfl⟩

/-- `(*s).len()` on a stack-borrowed `&[u32]` (32-bit). -/
theorem len_stack_ok_32 :
    evalRvalue L32 (.len (derefPlace 15)) testMem testDecls testLayouts32 =
      .ok (.scalar ⟨5, 4⟩) L32 testMem :=
  (trusted_evalRvalue_len_deref_slice_iff L32 L32 (derefPlace 15) testMem testDecls testLayouts32 []
    u32Ty _ ⟨1, 0⟩ 4 ⟨5, 4⟩ rfl rfl rfl).1.mpr
    ⟨rfl, rfl, (sliceLenBorrowOk_stack_backing L32 testMem testDecls testLayouts32 u32Ty ⟨1, 0⟩
      ⟨5, 4⟩ activeEntry backing [] 0 backingElems 0 rfl (fun h => by cases h) rfl rfl rfl).trans
        rfl⟩

/-- `.disabled` borrow: `Rvalue.len` faults. -/
theorem len_disabled_ub_64 :
    evalRvalue L64 (.len (derefPlace 23)) testMem testDecls testLayouts64 = .ub :=
  (trusted_evalRvalue_len_deref_slice_iff L64 L64 (derefPlace 23) testMem testDecls testLayouts64 []
    u32Ty _ ⟨2, 0⟩ 8 ⟨5, 8⟩ rfl rfl rfl).2.mpr
    (fun ⟨_, _, h⟩ => by
      rw [sliceLenBorrowOk_disabled L64 testMem testDecls testLayouts64 u32Ty ⟨2, 0⟩ ⟨5, 8⟩
        disabledEntry rfl rfl] at h
      cases h)

/-- Length word `6` exceeding the 5-element backing array: `Rvalue.len` faults. -/
theorem len_out_of_bounds_ub_64 :
    evalRvalue L64 (.len (derefPlace 24)) testMem testDecls testLayouts64 = .ub :=
  (trusted_evalRvalue_len_deref_slice_iff L64 L64 (derefPlace 24) testMem testDecls testLayouts64 []
    u32Ty _ ⟨1, 0⟩ 8 ⟨6, 8⟩ rfl rfl rfl).2.mpr (fun ⟨_, _, h⟩ => absurd h (by decide))

/-- Live borrow of an `.uninit` local: `Rvalue.len` faults. -/
theorem len_uninit_ub_32 :
    evalRvalue L32 (.len (derefPlace 28)) testMem testDecls testLayouts32 = .ub :=
  (trusted_evalRvalue_len_deref_slice_iff L32 L32 (derefPlace 28) testMem testDecls testLayouts32 []
    u32Ty _ ⟨4, 0⟩ 4 ⟨5, 4⟩ rfl rfl rfl).2.mpr
    (fun ⟨_, _, h⟩ => by
      rw [sliceLenBorrowOk_uninit L32 testMem testDecls testLayouts32 u32Ty ⟨4, 0⟩ ⟨5, 4⟩
        uninitEntry rfl (fun h => by cases h) rfl] at h
      cases h)

/-- Global allocation of 20 bytes holds 5 `u32`s: `Rvalue.len` succeeds. -/
theorem len_global_ok_64 :
    evalRvalue L64 (.len (derefPlace 25)) testMem testDecls testLayouts64 =
      .ok (.scalar ⟨5, 8⟩) L64 testMem :=
  (trusted_evalRvalue_len_deref_slice_iff L64 L64 (derefPlace 25) testMem testDecls testLayouts64 []
    u32Ty _ ⟨9, 0⟩ 8 ⟨5, 8⟩ rfl rfl rfl).1.mpr
    ⟨rfl, rfl, (sliceLenBorrowOk_global L64 testMem testDecls testLayouts64 u32Ty ⟨9, 0⟩ ⟨5, 8⟩
      testGlobal 4 rfl rfl rfl).trans rfl⟩

/-- Non-null dangling empty slice (`allocId = 0`, offset `16`, length `0`): `Rvalue.len` succeeds. -/
theorem len_dangling_empty_ok_32 :
    evalRvalue L32 (.len (derefPlace 26)) testMem testDecls testLayouts32 =
      .ok (.scalar ⟨0, 4⟩) L32 testMem :=
  (trusted_evalRvalue_len_deref_slice_iff L32 L32 (derefPlace 26) testMem testDecls testLayouts32 []
    u32Ty _ ⟨0, 16⟩ 4 ⟨0, 4⟩ rfl rfl rfl).1.mpr
    ⟨rfl, rfl, (sliceLenBorrowOk_allocId_zero L32 testMem testDecls testLayouts32 u32Ty 16 ⟨0, 4⟩
      rfl rfl).trans rfl⟩

/-- Unbacked non-zero `allocId`: `Rvalue.len` trusts the length word. -/
theorem len_unbacked_ok_64 :
    evalRvalue L64 (.len (derefPlace 20)) testMem testDecls testLayouts64 =
      .ok (.scalar ⟨5, 8⟩) L64 testMem :=
  (trusted_evalRvalue_len_deref_slice_iff L64 L64 (derefPlace 20) testMem testDecls testLayouts64 []
    u32Ty _ ⟨7, 4⟩ 8 ⟨5, 8⟩ rfl rfl rfl).1.mpr
    ⟨rfl, rfl, sliceLenBorrowOk_unbacked L64 testMem testDecls testLayouts64 u32Ty ⟨7, 4⟩ ⟨5, 8⟩
      rfl rfl (by decide)⟩

/-- Provenance-less wide pointer: `Rvalue.len` faults. -/
theorem len_wide_scalar_ub_64 :
    evalRvalue L64 (.len (derefPlace 27)) testMem testDecls testLayouts64 = .ub :=
  trusted_evalRvalue_len_deref_wide_scalar_ub L64 L64 (derefPlace 27) testMem testDecls testLayouts64
    [] u32Ty _ ⟨4096, 8⟩ ⟨5, 8⟩ rfl rfl rfl

/-- `str` place: `Rvalue.len` faults. -/
theorem len_str_ub_64 :
    evalRvalue L64 (.len (derefPlace 29)) testMem testDecls testLayouts64 = .ub :=
  trusted_evalRvalue_len_str_ub L64 (derefPlace 29) testMem testDecls testLayouts64 _ rfl

/-- ZST `.unit` backing slot (tag `5` on local `19`) with `offsetBytes = 0` and `len = 0`:
`Rvalue.len` succeeds returning `0` (64-bit). -/
theorem len_zst_unit_ok_64 :
    evalRvalue (L64.set 15 (.init (.aggregate 0 [.ptr ⟨5, 0⟩ 8, .scalar ⟨0, 8⟩])))
        (.len (derefPlace 15)) testMem testDecls testLayouts64 =
      .ok (.scalar ⟨0, 8⟩)
        (L64.set 15 (.init (.aggregate 0 [.ptr ⟨5, 0⟩ 8, .scalar ⟨0, 8⟩]))) testMem :=
  (trusted_evalRvalue_len_deref_slice_iff
    (L64.set 15 (.init (.aggregate 0 [.ptr ⟨5, 0⟩ 8, .scalar ⟨0, 8⟩])))
    (L64.set 15 (.init (.aggregate 0 [.ptr ⟨5, 0⟩ 8, .scalar ⟨0, 8⟩])))
    (derefPlace 15) testMem testDecls testLayouts64 [] u32Ty _ ⟨5, 0⟩ 8 ⟨0, 8⟩
    rfl rfl rfl).1.mpr
    ⟨rfl, rfl,
      (sliceLenBorrowOk_zst_unit
        (L64.set 15 (.init (.aggregate 0 [.ptr ⟨5, 0⟩ 8, .scalar ⟨0, 8⟩])))
        testMem testDecls testLayouts64 u32Ty ⟨5, 0⟩ ⟨0, 8⟩ zstEntry .unit
        rfl (fun h => by cases h) rfl rfl rfl).trans rfl⟩

/-- ZST `.unit` backing slot (tag `5` on local `19`) with `len = 1 > 0`: `Rvalue.len` faults. -/
theorem len_zst_unit_nonzero_ub_64 :
    evalRvalue (L64.set 15 (.init (.aggregate 0 [.ptr ⟨5, 0⟩ 8, .scalar ⟨1, 8⟩])))
        (.len (derefPlace 15)) testMem testDecls testLayouts64 = .ub :=
  (trusted_evalRvalue_len_deref_slice_iff
    (L64.set 15 (.init (.aggregate 0 [.ptr ⟨5, 0⟩ 8, .scalar ⟨1, 8⟩])))
    (L64.set 15 (.init (.aggregate 0 [.ptr ⟨5, 0⟩ 8, .scalar ⟨1, 8⟩])))
    (derefPlace 15) testMem testDecls testLayouts64 [] u32Ty _ ⟨5, 0⟩ 8 ⟨1, 8⟩
    rfl rfl rfl).2.mpr (fun ⟨_, _, h⟩ => by
      rw [sliceLenBorrowOk_zst_unit
        (L64.set 15 (.init (.aggregate 0 [.ptr ⟨5, 0⟩ 8, .scalar ⟨1, 8⟩])))
        testMem testDecls testLayouts64 u32Ty ⟨5, 0⟩ ⟨1, 8⟩ zstEntry .unit
        rfl (fun hc => by cases hc) rfl rfl rfl] at h
      cases h)

def refSliceU32Decl : LocalDecl :=
  { mutability := .not, ty := { kind := .ref .not (.slice u32Ty), layoutIdx := 3 }, debugName := none }

/-- Cross-frame `callerLocals` backing array (tag `99` targeting caller local `1`):
`Rvalue.len` succeeds returning `5` (64-bit). -/
theorem len_callerLocals_ok_64 :
    evalRvalue [.init (.aggregate 0 [.ptr ⟨99, 0⟩ 8, .scalar ⟨5, 8⟩])]
        (.len (derefPlace 0)) memWithCallerLocals [refSliceU32Decl] testLayouts64 =
      .ok (.scalar ⟨5, 8⟩)
        [.init (.aggregate 0 [.ptr ⟨99, 0⟩ 8, .scalar ⟨5, 8⟩])] memWithCallerLocals :=
  (trusted_evalRvalue_len_deref_slice_iff
    [.init (.aggregate 0 [.ptr ⟨99, 0⟩ 8, .scalar ⟨5, 8⟩])]
    [.init (.aggregate 0 [.ptr ⟨99, 0⟩ 8, .scalar ⟨5, 8⟩])]
    (derefPlace 0) memWithCallerLocals [refSliceU32Decl] testLayouts64 [] u32Ty _ ⟨99, 0⟩ 8 ⟨5, 8⟩
    rfl rfl rfl).1.mpr
    ⟨rfl, rfl,
      (sliceLenBorrowOk_callerLocals_backing
        [.init (.aggregate 0 [.ptr ⟨99, 0⟩ 8, .scalar ⟨5, 8⟩])]
        memWithCallerLocals [refSliceU32Decl] testLayouts64 u32Ty ⟨99, 0⟩ ⟨5, 8⟩
        callerBorrowEntry backing [] 0 backingElems 0
        rfl (fun h => by cases h) rfl rfl rfl rfl).trans rfl⟩

/-! ## 3.B.4 Subslice window laws (Episode 1 `Subslice` / `ConstantIndex` formulas) -/

/-- `s[2..5][1..2] = s[3..4]`. -/
theorem subslice_compose_witness :
    normalizeSubsliceProjections [.subslice 2 5 false, .subslice 1 2 false] =
      [.subslice 3 4 false] :=
  (normalizeSubsliceProjections_subslice_subslice 2 5 1 2 [] (by decide) (by decide) (by decide)).trans
    (normalizeSubsliceProjectionsAux_window_nil 3 4)

/-- `s[2..7][1..len-1] = s[3..6]` (`fromEnd = true`). -/
theorem subslice_compose_fromEnd_witness :
    normalizeSubsliceProjections [.subslice 2 7 false, .subslice 1 1 true] =
      [.subslice 3 6 false] :=
  (normalizeSubsliceProjections_subslice_subslice_fromEnd 2 7 1 1 [] (by decide) (by decide)
    (by decide)).trans (normalizeSubsliceProjectionsAux_window_nil 3 6)

/-- `s[2..5][1] = s[3]` and `s[2..5][len-1] = s[4]`. -/
theorem subslice_constantIndex_witnesses :
    normalizeSubsliceProjections [.subslice 2 5 false, .constantIndex 1 3 false] =
      [.constantIndex 3 3 false] ∧
    normalizeSubsliceProjections [.subslice 2 5 false, .constantIndex 1 3 true] =
      [.constantIndex 4 3 false] :=
  ⟨(normalizeSubsliceProjections_subslice_constantIndex 2 5 1 3 [] (by decide) (by decide)
      (by decide)).trans rfl,
    (normalizeSubsliceProjections_subslice_constantIndex_fromEnd 2 5 1 3 [] (by decide) (by decide)
      (by decide) (by decide)).trans rfl⟩

/-- `s[2..5][0..4]` (inner window past the outer length `3`) is not folded. -/
theorem subslice_out_of_window_witness :
    normalizeSubsliceProjections [.subslice 2 5 false, .subslice 0 4 false] =
      [.subslice 2 5 false, .subslice 0 4 false] :=
  (normalizeSubsliceProjections_subslice_subslice_out_of_window 2 5 0 4 [] (by decide)
    (by decide)).trans rfl

/-- Three-level nested `fromEnd = false` composition: `s[1..9][2..7][1..4] = s[4..7]`. -/
theorem subslice_compose_3_witness :
    normalizeSubsliceProjections
        [.subslice 1 9 false, .subslice 2 7 false, .subslice 1 4 false] =
      [.subslice 4 7 false] :=
  (normalizeSubsliceProjections_subslice_3 1 9 2 7 1 4 []
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    (normalizeSubsliceProjectionsAux_window_nil 4 7)

/-- Three-level nested composition with trailing `fromEnd = true`:
`s[1..9][2..7][1..len-1] = s[4..7]`. -/
theorem subslice_compose_3_fromEnd_witness :
    normalizeSubsliceProjections
        [.subslice 1 9 false, .subslice 2 7 false, .subslice 1 1 true] =
      [.subslice 4 7 false] :=
  (normalizeSubsliceProjections_subslice_3_fromEnd 1 9 2 7 1 1 []
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    (normalizeSubsliceProjectionsAux_window_nil 4 7)

/-! ### Instantiations of the step-level (non-`evalRvalue`) lemmas -/

theorem step_rawPtr_ptrMetadata_witnesses :
    evalAggregateRawPtr L64 { kind := .slice u32Ty, layoutIdx := 3 } [cp 11, cp 18] testMem testDecls
        testLayouts64 = .ok (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .scalar ⟨5, 8⟩]) L64 testMem ∧
    evalUnaryPtrMetadata L64 (cp 5) testMem testDecls testLayouts64 =
      .ok (.scalar ⟨5, 8⟩) L64 testMem :=
  ⟨evalAggregateRawPtr_ptr_scalar_ok L64 L64 { kind := .slice u32Ty, layoutIdx := 3 } [cp 11, cp 18]
      testMem testDecls testLayouts64 ⟨7, 0⟩ ⟨5, 8⟩ rfl rfl rfl,
    evalUnaryPtrMetadata_ptr_scalar_ok L64 L64 (cp 5) testMem testDecls testLayouts64 ⟨1, 0⟩ ⟨5, 8⟩
      rfl rfl⟩

theorem step_placeLen_witnesses :
    evalPlaceLen L64 (derefPlace 15) testMem testDecls testLayouts64 =
      .ok (.scalar ⟨5, 8⟩) L64 testMem ∧
    evalPlaceLen L64 (derefPlace 25) testMem testDecls testLayouts64 =
      .ok (.scalar ⟨5, 8⟩) L64 testMem ∧
    evalPlaceLen L64 (derefPlace 33) testMem testDecls testLayouts64 = .ub :=
  ⟨evalPlaceLen_slice_borrow_ok L64 L64 (derefPlace 15) testMem testDecls testLayouts64 [] [] ⟨1, 0⟩
      ⟨5, 8⟩ u32Ty _ activeEntry backing 0 backingElems 0 rfl rfl rfl rfl rfl (fun h => by cases h)
      rfl rfl rfl rfl,
    evalPlaceLen_slice_alloc_ok L64 L64 (derefPlace 25) testMem testDecls testLayouts64 [] ⟨9, 0⟩
      ⟨5, 8⟩ u32Ty _ testGlobal 4 rfl rfl rfl rfl rfl rfl rfl rfl,
    evalPlaceLen_null_len_nonzero_ub L64 L64 (derefPlace 33) testMem testDecls testLayouts64 []
      ⟨0, 16⟩ ⟨3, 8⟩ u32Ty _ rfl rfl rfl rfl rfl rfl rfl rfl⟩

theorem step_widePtr_rel_witnesses :
    evalWidePtrAggregateRelBinOp .ge (cp 21) 0 [.ptr ⟨7, 4⟩ 8, .scalar ⟨3, 8⟩] 0
        [.ptr ⟨7, 8⟩ 8, .scalar ⟨1, 8⟩] L64 testMem testDecls testLayouts64 =
      evalScalarBinOp .ge ⟨458756, 8⟩ ⟨458760, 8⟩ L64 testMem false ∧
    evalWidePtrAggregateRelBinOp .cmp (cp 20) 0 [.ptr ⟨7, 4⟩ 8, .scalar ⟨5, 8⟩] 0
        [.ptr ⟨7, 4⟩ 8, .scalar ⟨3, 8⟩] L64 testMem testDecls testLayouts64 =
      evalScalarBinOp .cmp ⟨5, 8⟩ ⟨3, 8⟩ L64 testMem false :=
  ⟨evalWidePtrAggregateRelBinOp_ge_addr_ne (cp 21) (.ptr ⟨7, 4⟩ 8) (.scalar ⟨3, 8⟩) (.ptr ⟨7, 8⟩ 8)
      (.scalar ⟨1, 8⟩) L64 testMem testDecls testLayouts64 ⟨458756, 8⟩ ⟨458760, 8⟩ ⟨3, 8⟩ ⟨1, 8⟩
      rfl rfl rfl rfl rfl rfl rfl rfl rfl,
    evalWidePtrAggregateRelBinOp_cmp_addr_eq (cp 20) (.ptr ⟨7, 4⟩ 8) (.scalar ⟨5, 8⟩) (.ptr ⟨7, 4⟩ 8)
      (.scalar ⟨3, 8⟩) L64 testMem testDecls testLayouts64 ⟨458756, 8⟩ ⟨458756, 8⟩ ⟨5, 8⟩ ⟨3, 8⟩
      rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

/-! ## 3.B.5 Lexicographic wide-pointer comparisons on `evalRvalue` -/

/-- Same data address (`7 * 65536 + 4`), metadata `5` vs `3`: `lhs < rhs` is `false` (64-bit). -/
theorem widePtr_lt_same_addr_64 :
    evalRvalue L64 (.binaryOp .lt (cp 20) (cp 21)) testMem testDecls testLayouts64 =
      .ok (.scalar (boolToScalar false)) L64 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_lt_lex L64 L64 L64 (cp 20) (cp 21) testMem testDecls
    testLayouts64 (.ptr ⟨7, 4⟩ 8) (.scalar ⟨5, 8⟩) (.ptr ⟨7, 4⟩ 8) (.scalar ⟨3, 8⟩) 458756 458756 5 3
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)).trans rfl

/-- Smaller data address wins regardless of metadata: `lhs < rhs` is `true` (32-bit). -/
theorem widePtr_lt_addr_32 :
    evalRvalue L32 (.binaryOp .lt (cp 21) (cp 22)) testMem testDecls testLayouts32 =
      .ok (.scalar (boolToScalar true)) L32 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_lt_lex L32 L32 L32 (cp 21) (cp 22) testMem testDecls
    testLayouts32 (.ptr ⟨7, 4⟩ 4) (.scalar ⟨3, 4⟩) (.ptr ⟨7, 8⟩ 4) (.scalar ⟨1, 4⟩) 458756 458760 3 1
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)).trans rfl

/-- Same data address, different metadata: `lhs == rhs` is `false` (64-bit). -/
theorem widePtr_eq_meta_differs_64 :
    evalRvalue L64 (.binaryOp .eq (cp 20) (cp 21)) testMem testDecls testLayouts64 =
      .ok (.scalar (boolToScalar false)) L64 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_eq_lex L64 L64 L64 (cp 20) (cp 21) testMem testDecls
    testLayouts64 (.ptr ⟨7, 4⟩ 8) (.scalar ⟨5, 8⟩) (.ptr ⟨7, 4⟩ 8) (.scalar ⟨3, 8⟩) 458756 458756 5 3
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)).trans rfl

/-- Identical wide pointers compare equal (64-bit). -/
theorem widePtr_eq_refl_64 :
    evalRvalue L64 (.binaryOp .eq (cp 20) (cp 20)) testMem testDecls testLayouts64 =
      .ok (.scalar (boolToScalar true)) L64 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_eq_lex L64 L64 L64 (cp 20) (cp 20) testMem testDecls
    testLayouts64 (.ptr ⟨7, 4⟩ 8) (.scalar ⟨5, 8⟩) (.ptr ⟨7, 4⟩ 8) (.scalar ⟨5, 8⟩) 458756 458756 5 5
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)).trans rfl

/-- Same data address, different metadata: `lhs != rhs` is `true` (64-bit). -/
theorem widePtr_ne_meta_differs_64 :
    evalRvalue L64 (.binaryOp .ne (cp 20) (cp 21)) testMem testDecls testLayouts64 =
      .ok (.scalar (boolToScalar true)) L64 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_ne_lex L64 L64 L64 (cp 20) (cp 21) testMem testDecls
    testLayouts64 (.ptr ⟨7, 4⟩ 8) (.scalar ⟨5, 8⟩) (.ptr ⟨7, 4⟩ 8) (.scalar ⟨3, 8⟩) 458756 458756 5 3
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)).trans rfl

/-- Identical wide pointers: `lhs != rhs` is `false` (32-bit). -/
theorem widePtr_ne_refl_32 :
    evalRvalue L32 (.binaryOp .ne (cp 20) (cp 20)) testMem testDecls testLayouts32 =
      .ok (.scalar (boolToScalar false)) L32 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_ne_lex L32 L32 L32 (cp 20) (cp 20) testMem testDecls
    testLayouts32 (.ptr ⟨7, 4⟩ 4) (.scalar ⟨5, 4⟩) (.ptr ⟨7, 4⟩ 4) (.scalar ⟨5, 4⟩) 458756 458756 5 5
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)).trans rfl

/-- Same data address, metadata `3 <= 5`: `lhs <= rhs` is `true` (64-bit). -/
theorem widePtr_le_same_addr_64 :
    evalRvalue L64 (.binaryOp .le (cp 21) (cp 20)) testMem testDecls testLayouts64 =
      .ok (.scalar (boolToScalar true)) L64 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_le_lex L64 L64 L64 (cp 21) (cp 20) testMem testDecls
    testLayouts64 (.ptr ⟨7, 4⟩ 8) (.scalar ⟨3, 8⟩) (.ptr ⟨7, 4⟩ 8) (.scalar ⟨5, 8⟩) 458756 458756 3 5
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)).trans rfl

/-- Larger data address: `lhs <= rhs` is `false` even when `m₁ < m₂` (32-bit). -/
theorem widePtr_le_addr_gt_false_32 :
    evalRvalue L32 (.binaryOp .le (cp 22) (cp 21)) testMem testDecls testLayouts32 =
      .ok (.scalar (boolToScalar false)) L32 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_le_lex L32 L32 L32 (cp 22) (cp 21)) testMem testDecls
    testLayouts32 (.ptr ⟨7, 8⟩ 4) (.scalar ⟨1, 4⟩) (.ptr ⟨7, 4⟩ 4) (.scalar ⟨3, 4⟩) 458760 458756 1 3
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) |>.trans rfl

/-- Same data address, metadata `5 > 3`: `lhs > rhs` is `true` (64-bit). -/
theorem widePtr_gt_same_addr_64 :
    evalRvalue L64 (.binaryOp .gt (cp 20) (cp 21)) testMem testDecls testLayouts64 =
      .ok (.scalar (boolToScalar true)) L64 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_gt_lex L64 L64 L64 (cp 20) (cp 21) testMem testDecls
    testLayouts64 (.ptr ⟨7, 4⟩ 8) (.scalar ⟨5, 8⟩) (.ptr ⟨7, 4⟩ 8) (.scalar ⟨3, 8⟩) 458756 458756 5 3
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)).trans rfl

/-- Smaller data address: `lhs > rhs` is `false` even when `m₁ > m₂` (32-bit). -/
theorem widePtr_gt_addr_lt_false_32 :
    evalRvalue L32 (.binaryOp .gt (cp 21) (cp 22)) testMem testDecls testLayouts32 =
      .ok (.scalar (boolToScalar false)) L32 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_gt_lex L32 L32 L32 (cp 21) (cp 22) testMem testDecls
    testLayouts32 (.ptr ⟨7, 4⟩ 4) (.scalar ⟨3, 4⟩) (.ptr ⟨7, 8⟩ 4) (.scalar ⟨1, 4⟩) 458756 458760 3 1
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)).trans rfl

/-- Same data address, metadata `3 >= 5`: `lhs >= rhs` is `false` (64-bit). -/
theorem widePtr_ge_same_addr_64 :
    evalRvalue L64 (.binaryOp .ge (cp 21) (cp 20)) testMem testDecls testLayouts64 =
      .ok (.scalar (boolToScalar false)) L64 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_ge_lex L64 L64 L64 (cp 21) (cp 20) testMem testDecls
    testLayouts64 (.ptr ⟨7, 4⟩ 8) (.scalar ⟨3, 8⟩) (.ptr ⟨7, 4⟩ 8) (.scalar ⟨5, 8⟩) 458756 458756 3 5
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)).trans rfl

/-- Identical wide pointers: `lhs >= rhs` is `true` (32-bit). -/
theorem widePtr_ge_refl_32 :
    evalRvalue L32 (.binaryOp .ge (cp 20) (cp 20)) testMem testDecls testLayouts32 =
      .ok (.scalar (boolToScalar true)) L32 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_ge_lex L32 L32 L32 (cp 20) (cp 20) testMem testDecls
    testLayouts32 (.ptr ⟨7, 4⟩ 4) (.scalar ⟨5, 4⟩) (.ptr ⟨7, 4⟩ 4) (.scalar ⟨5, 4⟩) 458756 458756 5 5
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)).trans rfl

/-- Lexicographic `cmp` on wide pointers: returns `Ordering::Greater` (`1`), `Ordering::Less`
(`255`), and `Ordering::Equal` (`0`) as 1-byte scalars. -/
theorem widePtr_cmp_same_addr_gt_64 :
    evalRvalue L64 (.binaryOp .cmp (cp 20) (cp 21)) testMem testDecls testLayouts64 =
      .ok (.scalar ⟨1, 1⟩) L64 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_cmp_lex L64 L64 L64 (cp 20) (cp 21) testMem testDecls
    testLayouts64 (.ptr ⟨7, 4⟩ 8) (.scalar ⟨5, 8⟩) (.ptr ⟨7, 4⟩ 8) (.scalar ⟨3, 8⟩) 458756 458756 5 3
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)).trans rfl

theorem widePtr_cmp_addr_lt_32 :
    evalRvalue L32 (.binaryOp .cmp (cp 21) (cp 22)) testMem testDecls testLayouts32 =
      .ok (.scalar ⟨255, 1⟩) L32 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_cmp_lex L32 L32 L32 (cp 21) (cp 22) testMem testDecls
    testLayouts32 (.ptr ⟨7, 4⟩ 4) (.scalar ⟨3, 4⟩) (.ptr ⟨7, 8⟩ 4) (.scalar ⟨1, 4⟩) 458756 458760 3 1
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)).trans rfl

theorem widePtr_cmp_eq_64 :
    evalRvalue L64 (.binaryOp .cmp (cp 20) (cp 20)) testMem testDecls testLayouts64 =
      .ok (.scalar ⟨0, 1⟩) L64 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_cmp_lex L64 L64 L64 (cp 20) (cp 20) testMem testDecls
    testLayouts64 (.ptr ⟨7, 4⟩ 8) (.scalar ⟨5, 8⟩) (.ptr ⟨7, 4⟩ 8) (.scalar ⟨5, 8⟩) 458756 458756 5 5
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)).trans rfl

/-- `evalScalarBinOp` relational semantics on concrete words (`cmp` ordering encoding). -/
theorem scalar_rel_witnesses :
    evalScalarBinOp .cmp ⟨3, 8⟩ ⟨5, 8⟩ [] {} false = .ok (.scalar ⟨255, 1⟩) [] {} ∧
    evalScalarBinOp .ge ⟨3, 8⟩ ⟨5, 8⟩ [] {} false = .ok (.scalar (boolToScalar false)) [] {} :=
  ⟨(evalScalarBinOp_rel_unsigned .cmp 3 5 8 [] {} (by decide)).trans rfl,
    (evalScalarBinOp_rel_unsigned .ge 3 5 8 [] {} (by decide)).trans rfl⟩

end PlaceAndRvalueWitnesses

/-! ## Dispatch exhaustiveness, representability, function-pointer width, and `Ordering` -/

section DispatchAndRangeWitnesses

open Anneal.Mir.PlaceAndRvalue

/-- Total dispatch: the `Unsize` spelling of `LPointerCoercionKind.unsize` runs `evalUnsizeCoercion`
(here the stack-borrowed `&[u32; 5] -> &[u32]` success). -/
theorem dispatch_unsize_witness :
    evalRvalue L64
        (.cast (.pointerCoercion (LPointerCoercionKind.toRustcSpelling_V2026_06_01 .unsize)) (cp 1)
          (sliceTy (.ref .not (.slice u32Ty)))) testMem testDecls testLayouts64 =
      .ok (LWidePtr.encodeProv ⟨1, 0⟩ 5 8) L64 testMem :=
  (evalRvalue_cast_pointerCoercion_dispatch L64 (cp 1) (sliceTy (.ref .not (.slice u32Ty))) testMem
    testDecls testLayouts64 .unsize).trans unsize_stack_ok_64

/-- Total dispatch: `ReifyFnPointer(Safe)` runs `reifyFnPointerStep` under its own spelling. -/
theorem dispatch_reify_safe_witness :
    evalRvalue L64
        (.cast (.pointerCoercion
          (LPointerCoercionKind.toRustcSpelling_V2026_06_01 (.reifyFnPointerWithSafety .safe))) (cp 7)
          { kind := fnSigSafe, layoutIdx := 1 }) testMem testDecls testLayouts64 =
      reifyFnPointerStep L64 (cp 7) { kind := fnSigSafe, layoutIdx := 1 } testMem testDecls
        testLayouts64 "ReifyFnPointer(Safe)" :=
  evalRvalue_cast_pointerCoercion_dispatch L64 (cp 7) { kind := fnSigSafe, layoutIdx := 1 } testMem
    testDecls testLayouts64 (.reifyFnPointerWithSafety .safe)

/-- An unknown `rustc` coercion tag (rejected by Episode 1's lowering) is `.unsupported` in
`Trusted` — neither `.ok` nor `.ub`. -/
theorem unknown_spelling_unsupported_witness :
    evalRvalue L64 (.cast (.pointerCoercion "ReifyFnPointer(Maybe)") (cp 7)
        { kind := fnSigSafe, layoutIdx := 1 }) testMem testDecls testLayouts64 = .unsupported :=
  evalRvalue_cast_pointerCoercion_unknown_spelling L64 (cp 7) { kind := fnSigSafe, layoutIdx := 1 }
    testMem testDecls testLayouts64 "ReifyFnPointer(Maybe)" rfl

/-- Untyped stack-borrowed `Unsize` at element offset `2`: length inferred as `5 - 2 = 3`. -/
theorem unsize_untyped_offset_ok_64 :
    evalRvalue (L64.set 1 (.init (.ptr ⟨1, 8⟩ 8)))
        (.cast (.pointerCoercion "Unsize") (cp 1) (sliceTy (.ref .not (.slice u32Ty)))) testMem []
        testLayouts64 =
      .ok (LWidePtr.encodeProv ⟨1, 8⟩ 3 8) (L64.set 1 (.init (.ptr ⟨1, 8⟩ 8))) testMem :=
  (trusted_evalUnsizeCoercion_untyped_stack_borrow_iff (L64.set 1 (.init (.ptr ⟨1, 8⟩ 8)))
    (L64.set 1 (.init (.ptr ⟨1, 8⟩ 8))) (cp 1) testMem [] testLayouts64 true .not u32Ty 3 ⟨1, 8⟩
    activeEntry backing [] 0 backingElems 2 rfl rfl rfl rfl rfl rfl rfl).2.2.1.mpr rfl

/-- Untyped stack-borrowed `Unsize` at element offset `6` (past the 5-element array): `.ub`. -/
theorem unsize_untyped_offset_ub_64 :
    evalRvalue (L64.set 1 (.init (.ptr ⟨1, 24⟩ 8)))
        (.cast (.pointerCoercion "Unsize") (cp 1) (sliceTy (.ref .not (.slice u32Ty)))) testMem []
        testLayouts64 = .ub :=
  (trusted_evalUnsizeCoercion_untyped_stack_borrow_iff (L64.set 1 (.init (.ptr ⟨1, 24⟩ 8)))
    (L64.set 1 (.init (.ptr ⟨1, 24⟩ 8))) (cp 1) testMem [] testLayouts64 true .not u32Ty 3 ⟨1, 24⟩
    activeEntry backing [] 0 backingElems 6 rfl rfl rfl rfl rfl rfl rfl).2.2.2.mpr rfl

/-- `*const [u8; 2^32]` (an array whose length does not fit a 32-bit metadata word). -/
def hugeArrDecl : LocalDecl :=
  { mutability := .not, ty := { kind := .rawPtr .not (.array (.uint .u8) 4294967296), layoutIdx := 1 },
    debugName := none }

def declsHugeScalar : List LocalDecl := testDecls.set 12 hugeArrDecl

def declsHugePtr : List LocalDecl := testDecls.set 11 hugeArrDecl

def u8SliceRawTy : Ty := sliceTy (.rawPtr .not (.slice (.uint .u8)))

/-- 32-bit: provenance-less `*const [u8; 2^32] -> *const [u8]` faults (length not representable). -/
theorem unsize_scalar_huge_len_ub_32 :
    evalRvalue L32 (.cast (.pointerCoercion "Unsize") (cp 12) u8SliceRawTy) testMem declsHugeScalar
        testLayouts32 = .ub :=
  (trusted_evalUnsizeCoercion_scalar_iff L32 L32 (cp 12) u8SliceRawTy testMem declsHugeScalar
    testLayouts32 ⟨4096, 4⟩ rfl rfl).2.2.2.mpr
    (rawPtrUnsizeArrayToSliceLen?_eq_none_of_len_ge .not .not (.uint .u8) (.uint .u8) 4294967296 1 3
      4 (by decide))

/-- 64-bit: the same provenance-less coercion succeeds with length `2^32`. -/
theorem unsize_scalar_huge_len_ok_64 :
    evalRvalue L64 (.cast (.pointerCoercion "Unsize") (cp 12) u8SliceRawTy) testMem declsHugeScalar
        testLayouts64 = .ok (LWidePtr.encodeScalar 4096 4294967296 8) L64 testMem :=
  ((trusted_evalUnsizeCoercion_scalar_iff L64 L64 (cp 12) u8SliceRawTy testMem declsHugeScalar
    testLayouts64 ⟨4096, 8⟩ rfl rfl).2.2.1 4294967296).mpr rfl

/-- FINDING (32-bit): `Trusted`'s *provenance* `Unsize` path performs no such range check — an
unbacked `*const [u8; 2^32]` is unsized to a non-canonical 4-byte length word holding `2^32 ≥
scalarModulus 4`, while the provenance-less path above faults. -/
theorem unsize_ptr_huge_len_noncanonical_32 :
    evalRvalue L32 (.cast (.pointerCoercion "Unsize") (cp 11) u8SliceRawTy) testMem declsHugePtr
        testLayouts32 = .ok (.aggregate 0 [.ptr ⟨7, 0⟩ 4, .scalar ⟨4294967296, 4⟩]) L32 testMem ∧
      scalarModulus 4 ≤ 4294967296 :=
  ⟨(trusted_evalUnsizeCoercion_unbacked_nonzero_allocId L32 L32 (cp 11) testMem declsHugePtr
      testLayouts32 false .not (.uint .u8) 3
      { kind := .rawPtr .not (.array (.uint .u8) 4294967296), layoutIdx := 1 } ⟨7, 0⟩ 4294967296
      rfl rfl rfl rfl rfl rfl).2, by decide⟩

/-- 32-bit: `fn() as *const u32` yields an 8-byte thin pointer (function pointers are always 8 bytes
in `Trusted`) … -/
theorem fnPtrToPtr_ok_32 :
    evalRvalue L32 (.cast .fnPtrToPtr (cp 8) { kind := .rawPtr .not u32Ty, layoutIdx := 1 }) testMem
        testDecls testLayouts32 = .ok (.ptr ⟨65536, 0⟩ 8) L32 testMem :=
  (trusted_evalRvalue_fnPtrToPtr_iff L32 L32 (cp 8) { kind := .rawPtr .not u32Ty, layoutIdx := 1 }
    testMem testDecls testLayouts32 ⟨65536, 0⟩ 8 rfl).1.mpr ⟨rfl, rfl, rfl⟩

/-- … which a subsequent `PtrToPtr` rejects on the 32-bit layout (`8 ≠ 4`): `.ub`. -/
theorem ptrToPtr_fnPtr8_ub_32 :
    evalRvalue (L32.set 11 (.init (.ptr ⟨65536, 0⟩ 8)))
        (.cast .ptrToPtr (cp 11) { kind := .rawPtr .not (.uint .u8), layoutIdx := 1 }) testMem
        testDecls testLayouts32 = .ub :=
  trusted_evalRvalue_ptrToPtr_ptr8_width_ub (L32.set 11 (.init (.ptr ⟨65536, 0⟩ 8)))
    (L32.set 11 (.init (.ptr ⟨65536, 0⟩ 8))) (cp 11) { kind := .rawPtr .not (.uint .u8), layoutIdx := 1 }
    testMem testDecls testLayouts32 ⟨65536, 0⟩ rfl (by decide)

/-- `*mut u32 -> *const u8` (mismatched pointees) is not a `MutToConstPointer` coercion: `.ub`. -/
theorem mutToConst_pointee_mismatch_ub_64 :
    evalRvalue L64 (.cast (.pointerCoercion "MutToConstPointer") (cp 11)
        { kind := .rawPtr .not (.uint .u8), layoutIdx := 1 }) testMem testDecls testLayouts64 = .ub :=
  (trusted_evalRvalue_mutToConstPointer_thin_ptr_iff L64 L64 (cp 11)
    { kind := .rawPtr .not (.uint .u8), layoutIdx := 1 } testMem testDecls testLayouts64 ⟨7, 0⟩ 8
    rfl).2.mpr (fun ⟨_, h⟩ => by cases h)

/-- Same data address, metadata `5` vs `3`: `cmp` is `Greater` (64-bit). -/
theorem widePtr_cmp_ordering_gt_64 :
    evalRvalue L64 (.binaryOp .cmp (cp 20) (cp 21)) testMem testDecls testLayouts64 =
      .ok (.scalar (orderingCmpScalar .gt)) L64 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_cmp_ordering L64 L64 L64 (cp 20) (cp 21) testMem testDecls
    testLayouts64 (.ptr ⟨7, 4⟩ 8) (.scalar ⟨5, 8⟩) (.ptr ⟨7, 4⟩ 8) (.scalar ⟨3, 8⟩) 458756 458756 5 3
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)).trans rfl

/-- Smaller data address: `cmp` is `Less` regardless of metadata (32-bit). -/
theorem widePtr_cmp_ordering_lt_32 :
    evalRvalue L32 (.binaryOp .cmp (cp 21) (cp 22)) testMem testDecls testLayouts32 =
      .ok (.scalar (orderingCmpScalar .lt)) L32 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_cmp_ordering L32 L32 L32 (cp 21) (cp 22) testMem testDecls
    testLayouts32 (.ptr ⟨7, 4⟩ 4) (.scalar ⟨3, 4⟩) (.ptr ⟨7, 8⟩ 4) (.scalar ⟨1, 4⟩) 458756 458760 3 1
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)).trans rfl

/-- Identical wide pointers: `cmp` is `Equal` (64-bit). -/
theorem widePtr_cmp_ordering_eq_64 :
    evalRvalue L64 (.binaryOp .cmp (cp 20) (cp 20)) testMem testDecls testLayouts64 =
      .ok (.scalar (orderingCmpScalar .eq)) L64 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_cmp_ordering L64 L64 L64 (cp 20) (cp 20) testMem testDecls
    testLayouts64 (.ptr ⟨7, 4⟩ 8) (.scalar ⟨5, 8⟩) (.ptr ⟨7, 4⟩ 8) (.scalar ⟨5, 8⟩) 458756 458756 5 5
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)).trans rfl

/-- Pointer arithmetic on two fat pointers (`BinOp.add`) is `.unsupported` (32-bit). -/
theorem widePtr_add_unsupported_32 :
    evalRvalue L32 (.binaryOp .add (cp 20) (cp 21)) testMem testDecls testLayouts32 = .unsupported :=
  trusted_evalRvalue_binaryOp_wide_ptr_nonrelational_unsupported L32 L32 L32 .add (cp 20) (cp 21)
    testMem testDecls testLayouts32 (.ptr ⟨7, 4⟩ 4) (.scalar ⟨5, 4⟩) (.ptr ⟨7, 4⟩ 4) (.scalar ⟨3, 4⟩)
    rfl rfl rfl

/-! ### Pass A2 witnesses: `.dead` locals, nested-`.ptr` asymmetry, untyped global/ZST `.ub`,
`deriveStackElemThinPtr` subslice-reuse & union-field branches, thin-array `PtrToPtr` narrowing,
same-place distinct borrow tags, and untyped / width-mismatched wide-pointer comparisons -/

/-- Stack borrow of a `.dead` (`StorageDead`) local slot: `Unsize` faults with `.ub` (64-bit). -/
theorem unsize_dead_local_ub_64 :
    evalRvalue (L64.set 13 .dead)
        (.cast (.pointerCoercion "Unsize") (cp 31) (sliceTy (.ref .not (.slice u32Ty))))
        testMem testDecls testLayouts64 = .ub :=
  (trusted_evalUnsizeCoercion_stack_borrow_dead_or_missing_ub
    (L64.set 13 .dead) (L64.set 13 .dead) (cp 31) testMem testDecls testLayouts64
    true .not u32Ty 3 { kind := .ref .not (.array u32Ty 5), layoutIdx := 1 } ⟨4, 0⟩ 5
    uninitEntry rfl rfl rfl rfl rfl (Or.inl rfl)).2

/-- Cross-frame `callerLocals` borrow where `mem.callerLocals` is empty (`get? = .none`):
`Unsize` faults with `.ub` (32-bit). -/
theorem unsize_callerLocals_missing_ub_32 :
    evalRvalue [.init (.ptr ⟨99, 0⟩ 4)]
        (.cast (.pointerCoercion "Unsize") (cp 0) (sliceTy (.ref .not (.slice u32Ty))))
        { testMem with borrows := callerBorrowEntry :: testMem.borrows }
        [refArray5Decl] testLayouts32 = .ub :=
  (trusted_evalUnsizeCoercion_stack_borrow_dead_or_missing_ub
    [.init (.ptr ⟨99, 0⟩ 4)] [.init (.ptr ⟨99, 0⟩ 4)] (cp 0)
    { testMem with borrows := callerBorrowEntry :: testMem.borrows }
    [refArray5Decl] testLayouts32 true .not u32Ty 3
    { kind := .ref .not (.array u32Ty 5), layoutIdx := 1 } ⟨99, 0⟩ 5
    callerBorrowEntry rfl rfl rfl rfl rfl (Or.inr ⟨rfl, Or.inl rfl⟩)).2

/-- Asymmetry finding between `evalUnsizeCoercion` (`Places.lean:13432`) and `evalPlaceLen`
(`sliceLenBorrowOk`, `Places.lean:14449`): when a stack borrow's target local holds a nested thin
pointer `.ptr ⟨7, 0⟩ 8` (local `11`, borrowed by tag `60`), `Unsize` accepts it (`stackTargetValid =
true`), whereas `Rvalue.len` on the resulting dereferenced slice pointer faults with `.ub`! -/
def nestedPtrEntry : BorrowEntry :=
  { tag := 60, targetLocal := 11, targetProjection := [], perm := .active }

def memWithNestedPtrBorrow : Memory :=
  { testMem with borrows := nestedPtrEntry :: testMem.borrows }

theorem unsize_vs_len_nested_ptr_asymmetry_64 :
    evalRvalue (L64.set 1 (.init (.ptr ⟨60, 0⟩ 8)))
        (.cast (.pointerCoercion "Unsize") (cp 1) (sliceTy (.ref .not (.slice u32Ty))))
        memWithNestedPtrBorrow testDecls testLayouts64 =
      .ok (LWidePtr.encodeProv ⟨60, 0⟩ 5 8) (L64.set 1 (.init (.ptr ⟨60, 0⟩ 8)))
        memWithNestedPtrBorrow ∧
    evalRvalue (L64.set 15 (.init (LWidePtr.encodeProv ⟨60, 0⟩ 5 8)))
        (.len (derefPlace 15)) memWithNestedPtrBorrow testDecls testLayouts64 = .ub :=
  ⟨(trusted_evalUnsizeCoercion_stack_borrow_nested_ptr_ok
      (L64.set 1 (.init (.ptr ⟨60, 0⟩ 8))) (L64.set 1 (.init (.ptr ⟨60, 0⟩ 8))) (cp 1)
      memWithNestedPtrBorrow testDecls testLayouts64 true .not u32Ty 3
      { kind := .ref .not (.array u32Ty 5), layoutIdx := 1 } ⟨60, 0⟩ ⟨7, 0⟩ 5 8
      nestedPtrEntry (.ptr ⟨7, 0⟩ 8) rfl rfl rfl rfl rfl rfl rfl rfl).2,
    (trusted_evalRvalue_len_deref_slice_iff
      (L64.set 15 (.init (LWidePtr.encodeProv ⟨60, 0⟩ 5 8)))
      (L64.set 15 (.init (LWidePtr.encodeProv ⟨60, 0⟩ 5 8)))
      (derefPlace 15) memWithNestedPtrBorrow testDecls testLayouts64 [] u32Ty _ ⟨60, 0⟩ 8 ⟨5, 8⟩
      rfl rfl rfl).2.mpr (fun ⟨_, _, h⟩ => by
        rw [sliceLenBorrowOk_nested_ptr_eq_false
          (L64.set 15 (.init (LWidePtr.encodeProv ⟨60, 0⟩ 5 8)))
          memWithNestedPtrBorrow testDecls testLayouts64 u32Ty ⟨60, 0⟩ ⟨5, 8⟩
          nestedPtrEntry (.ptr ⟨7, 0⟩ 8) ⟨7, 0⟩ 8 rfl (fun hc => by cases hc) rfl rfl rfl] at h
        cases h)⟩

/-- Untyped (`localDecls = []`) stack borrow of a ZST `.unit` slot (tag `5` on local `19`):
succeeds with length `0` at byte offset `0`, and faults with `.ub` at byte offset `4`. -/
theorem unsize_untyped_zst_unit_ok_and_ub_64 :
    evalRvalue L64 (.cast (.pointerCoercion "Unsize") (cp 30) (sliceTy (.ref .not (.slice u32Ty))))
        testMem [] testLayouts64 =
      .ok (LWidePtr.encodeProv ⟨5, 0⟩ 0 8) L64 testMem ∧
    evalRvalue (L64.set 30 (.init (.ptr ⟨5, 4⟩ 8)))
        (.cast (.pointerCoercion "Unsize") (cp 30) (sliceTy (.ref .not (.slice u32Ty))))
        testMem [] testLayouts64 = .ub :=
  ⟨(trusted_evalUnsizeCoercion_untyped_zst_unit_iff L64 L64 (cp 30) testMem [] testLayouts64
      true .not u32Ty 3 ⟨5, 0⟩ zstEntry .unit rfl rfl rfl rfl rfl rfl rfl).2.2.1.mpr rfl,
    (trusted_evalUnsizeCoercion_untyped_zst_unit_iff
      (L64.set 30 (.init (.ptr ⟨5, 4⟩ 8))) (L64.set 30 (.init (.ptr ⟨5, 4⟩ 8))) (cp 30)
      testMem [] testLayouts64 true .not u32Ty 3 ⟨5, 4⟩ zstEntry .unit
      rfl rfl rfl rfl rfl rfl rfl).2.2.2.mpr rfl⟩

/-- Untyped (`localDecls = []`) global allocation `Unsize` `.ub` witnesses:
1. Read-only global coerced to `*mut [u32]`;
2. Misaligned byte offset (`offsetBytes = 2`, `elemSz = 4`);
3. ZST element type `()` (`elemSz = 0`). -/
theorem unsize_untyped_global_ub_witnesses :
    evalRvalue L64 (.cast (.pointerCoercion "Unsize") (cp 34) (sliceTy (.rawPtr .mut (.slice u32Ty))))
        testMem [] testLayouts64 = .ub ∧
    evalRvalue (L32.set 32 (.init (.ptr ⟨9, 2⟩ 4)))
        (.cast (.pointerCoercion "Unsize") (cp 32) (sliceTy (.ref .not (.slice u32Ty))))
        testMem [] testLayouts32 = .ub ∧
    evalRvalue L64 (.cast (.pointerCoercion "Unsize") (cp 32)
        (sliceTy (.ref .not (.slice (.tuple [])))))
        testMem [] testLayouts64 = .ub :=
  ⟨(trusted_evalUnsizeCoercion_untyped_global_alloc_ub L64 L64 (cp 34) testMem [] testLayouts64
      false .mut u32Ty 3 ⟨9, 0⟩ testGlobal rfl rfl rfl rfl (Or.inl ⟨rfl, rfl⟩)).2,
    (trusted_evalUnsizeCoercion_untyped_global_alloc_ub
      (L32.set 32 (.init (.ptr ⟨9, 2⟩ 4))) (L32.set 32 (.init (.ptr ⟨9, 2⟩ 4))) (cp 32)
      testMem [] testLayouts32 true .not u32Ty 3 ⟨9, 2⟩ testGlobal
      rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨4, rfl, Or.inl rfl⟩)))).2,
    (trusted_evalUnsizeCoercion_untyped_global_alloc_ub L64 L64 (cp 32) testMem [] testLayouts64
      true .not (.tuple []) 3 ⟨9, 0⟩ testGlobal rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inl rfl)))).2⟩

/-- `deriveStackElemThinPtr` on `narrowedEntry` (whose `targetProjection = [.subslice 0 5 false]`
already ends with a `.subslice` covering `[0 .. 5)`): reuses tag `10` without allocating a fresh
tag (`memAfterNarrow.nextTag` remains `11`). -/
theorem deriveStackElemThinPtr_already_subslice_witness :
    deriveStackElemThinPtr L64 memAfterNarrow ⟨10, 0⟩ narrowedEntry (some 5) 8 =
      .ok (.ptr ⟨10, 0⟩ 8) L64 memAfterNarrow :=
  deriveStackElemThinPtr_already_subslice L64 memAfterNarrow ⟨10, 0⟩ narrowedEntry 5 8 backing
    [.subslice 0 5 false] 0 backingElems 0 (fun h => by cases h) rfl rfl rfl rfl rfl

/-- Borrow entry projecting an uninitialized union array field `.field 0 [u32; 5]` on a `.aggregate 0
[.unit]` union local (local `19` overridden to `.aggregate 0 [.unit]`). -/
def unionFieldBorrowEntry : BorrowEntry :=
  { tag := 70
    targetLocal := 19
    targetProjection := [.field 0 { kind := .array u32Ty 5, layoutIdx := 2 }]
    perm := .active }

/-- `deriveStackElemThinPtr` on an uninitialized union array field of capacity `5`: succeeds at
`offsetBytes = 0` when `n = 5 ≤ 5`, and faults with `.ub` when `n = 6 > 5` or `offsetBytes = 4`. -/
theorem deriveStackElemThinPtr_union_field_ok_and_ub_64 :
    deriveStackElemThinPtr (L64.set 19 (.init (.aggregate 0 [.unit]))) testMem ⟨70, 0⟩
        unionFieldBorrowEntry (some 5) 8 =
      .ok (.ptr ⟨70, 0⟩ 8) (L64.set 19 (.init (.aggregate 0 [.unit]))) testMem ∧
    deriveStackElemThinPtr (L64.set 19 (.init (.aggregate 0 [.unit]))) testMem ⟨70, 0⟩
        unionFieldBorrowEntry (some 6) 8 = .ub :=
  ⟨(deriveStackElemThinPtr_uninit_union_field_array_iff
      (L64.set 19 (.init (.aggregate 0 [.unit]))) testMem ⟨70, 0⟩ unionFieldBorrowEntry 5 8
      (.aggregate 0 [.unit]) 0 { kind := .array u32Ty 5, layoutIdx := 2 } [] 5
      (fun h => by cases h) rfl rfl rfl rfl rfl rfl).1.mpr rfl,
    (deriveStackElemThinPtr_uninit_union_field_array_iff
      (L64.set 19 (.init (.aggregate 0 [.unit]))) testMem ⟨70, 0⟩ unionFieldBorrowEntry 6 8
      (.aggregate 0 [.unit]) 0 { kind := .array u32Ty 5, layoutIdx := 2 } [] 5
      (fun h => by cases h) rfl rfl rfl rfl rfl rfl).2.mpr rfl⟩

/-- `deriveStackElemThinPtr` faults on `.disabled`, `.uninit`, and `.dead` stack borrows. -/
theorem deriveStackElemThinPtr_disabled_uninit_dead_witnesses :
    deriveStackElemThinPtr L64 testMem ⟨2, 0⟩ disabledEntry (some 5) 8 = .ub ∧
    deriveStackElemThinPtr L64 testMem ⟨4, 0⟩ uninitEntry (some 5) 8 = .ub ∧
    deriveStackElemThinPtr (L64.set 13 .dead) testMem ⟨4, 0⟩ uninitEntry (some 5) 8 = .ub :=
  ⟨deriveStackElemThinPtr_disabled_or_uninit_or_dead_ub L64 testMem ⟨2, 0⟩ disabledEntry (some 5) 8
      (Or.inl rfl),
    deriveStackElemThinPtr_disabled_or_uninit_or_dead_ub L64 testMem ⟨4, 0⟩ uninitEntry (some 5) 8
      (Or.inr (Or.inl rfl)),
    deriveStackElemThinPtr_disabled_or_uninit_or_dead_ub (L64.set 13 .dead) testMem ⟨4, 0⟩
      uninitEntry (some 5) 8 (Or.inr (Or.inr rfl))⟩

/-- Concrete thin-to-thin `PtrToPtr` stack-borrowed array narrowing (`&[u32; 5] as *const u32` on
local `1`, tag `1`): refines via `trusted_evalRvalue_ptrToPtr_thin_array_stack_borrow` and
`deriveStackElemThinPtr_fresh_subslice` to `.ok (.ptr ⟨10, 0⟩ 8)` with `memAfterNarrow`. -/
theorem ptrToPtr_thin_array_stack_narrowing_64 :
    evalRvalue L64 (.cast .ptrToPtr (cp 1) { kind := .rawPtr .not u32Ty, layoutIdx := 1 })
        testMem testDecls testLayouts64 =
      .ok (.ptr ⟨10, 0⟩ 8) L64 memAfterNarrow ∧
    evalRvalue L32 (.cast .ptrToPtr (cp 11) { kind := .rawPtr .not u32Ty, layoutIdx := 1 })
        testMem testDecls testLayouts32 =
      .ok (.ptr ⟨7, 0⟩ 4) L32 testMem :=
  ⟨(trusted_evalRvalue_ptrToPtr_thin_array_stack_borrow L64 L64 (cp 1)
      { kind := .rawPtr .not u32Ty, layoutIdx := 1 } testMem testDecls testLayouts64 ⟨1, 0⟩ u32Ty 5
      activeEntry rfl rfl
      ((arrayPtrOrRefElemLen?_rawPtr_or_ref .not u32Ty u32Ty 5 1).2.trans rfl) rfl).trans
      (deriveStackElemThinPtr_fresh_subslice L64 testMem ⟨1, 0⟩ activeEntry 5 8 backing [] 0
        backingElems 0 (fun h => by cases h) rfl rfl rfl rfl rfl),
    trusted_evalRvalue_ptrToPtr_thin_nonarray_or_unborrowed L32 L32 (cp 11)
      { kind := .rawPtr .not u32Ty, layoutIdx := 1 } testMem testDecls testLayouts32 ⟨7, 0⟩ u32Ty
      rfl rfl (Or.inl rfl)⟩

/-- `Rvalue.len` on a `.dead` backing local or missing `callerLocals` entry faults with `.ub`. -/
theorem len_dead_and_missing_caller_ub_witnesses :
    evalRvalue (L64.set 13 .dead) (.len (derefPlace 28)) testMem testDecls testLayouts64 = .ub ∧
    evalRvalue [.init (.aggregate 0 [.ptr ⟨99, 0⟩ 4, .scalar ⟨5, 4⟩])]
        (.len (derefPlace 0)) { testMem with borrows := callerBorrowEntry :: testMem.borrows }
        [refSliceU32Decl] testLayouts32 = .ub :=
  ⟨(trusted_evalRvalue_len_deref_slice_iff (L64.set 13 .dead) (L64.set 13 .dead) (derefPlace 28)
      testMem testDecls testLayouts64 [] u32Ty _ ⟨4, 0⟩ 8 ⟨5, 8⟩ rfl rfl rfl).2.mpr
      (fun ⟨_, _, h⟩ => by
        rw [sliceLenBorrowOk_dead (L64.set 13 .dead) testMem testDecls testLayouts64 u32Ty ⟨4, 0⟩
          ⟨5, 8⟩ uninitEntry rfl (fun hc => by cases hc) rfl] at h
        cases h),
    (trusted_evalRvalue_len_deref_slice_iff
      [.init (.aggregate 0 [.ptr ⟨99, 0⟩ 4, .scalar ⟨5, 4⟩])]
      [.init (.aggregate 0 [.ptr ⟨99, 0⟩ 4, .scalar ⟨5, 4⟩])]
      (derefPlace 0) { testMem with borrows := callerBorrowEntry :: testMem.borrows }
      [refSliceU32Decl] testLayouts32 [] u32Ty _ ⟨99, 0⟩ 4 ⟨5, 4⟩ rfl rfl rfl).2.mpr
      (fun ⟨_, _, h⟩ => by
        rw [sliceLenBorrowOk_callerLocals_missing
          [.init (.aggregate 0 [.ptr ⟨99, 0⟩ 4, .scalar ⟨5, 4⟩])]
          { testMem with borrows := callerBorrowEntry :: testMem.borrows }
          [refSliceU32Decl] testLayouts32 u32Ty ⟨99, 0⟩ ⟨5, 4⟩ callerBorrowEntry
          rfl (fun hc => by cases hc) rfl (Or.inl rfl)] at h
        cases h)⟩

/-- Distinct stack-borrow tags (`activeEntry` tag `1` and `frozenEntry` tag `3`) targeting the same
stack local `0` at offset `0` resolve to the *exact same* canonical address via
`resolveWideWordScalar?_stack_borrow_eq_of_same_place`, so wide slice pointers carrying tag `1` and
tag `3` with equal length `5` compare equal (`==` evaluates to `true`). -/
theorem widePtr_distinct_borrow_tags_same_place_eq_64 :
    resolveWideWordScalar? (.ptr ⟨1, 0⟩ 8) L64 testMem.borrows testMem.callerLocals testDecls
        testLayouts64 8 =
      resolveWideWordScalar? (.ptr ⟨3, 0⟩ 8) L64 testMem.borrows testMem.callerLocals testDecls
        testLayouts64 8 ∧
    evalRvalue (L64.set 6 (.init (.aggregate 0 [.ptr ⟨3, 0⟩ 8, .scalar ⟨5, 8⟩])))
        (.binaryOp .eq (cp 5) (cp 6)) testMem testDecls testLayouts64 =
      .ok (.scalar (boolToScalar true))
        (L64.set 6 (.init (.aggregate 0 [.ptr ⟨3, 0⟩ 8, .scalar ⟨5, 8⟩]))) testMem :=
  ⟨resolveWideWordScalar?_stack_borrow_eq_of_same_place ⟨1, 0⟩ ⟨3, 0⟩ activeEntry frozenEntry L64
      testMem.borrows testMem.callerLocals testDecls testLayouts64 8 rfl rfl rfl rfl rfl,
    (trusted_evalRvalue_binaryOp_wide_ptr_eq_lex
      (L64.set 6 (.init (.aggregate 0 [.ptr ⟨3, 0⟩ 8, .scalar ⟨5, 8⟩])))
      (L64.set 6 (.init (.aggregate 0 [.ptr ⟨3, 0⟩ 8, .scalar ⟨5, 8⟩])))
      (L64.set 6 (.init (.aggregate 0 [.ptr ⟨3, 0⟩ 8, .scalar ⟨5, 8⟩])))
      (cp 5) (cp 6) testMem testDecls testLayouts64 (.ptr ⟨1, 0⟩ 8) (.scalar ⟨5, 8⟩)
      (.ptr ⟨3, 0⟩ 8) (.scalar ⟨5, 8⟩) 68719476736 68719476736 5 5
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)).trans rfl⟩

/-- Untyped (`localDecls = []`, so `isExplicitWidePtrTy = false`) wide-pointer comparisons:
1. When at least one data word is `.ptr _ _`, `evalRvalue` still dispatches to `evalWidePtrRelBinOp`;
2. When both data words are `.scalar`, `evalRvalue` returns `.unsupported` (avoiding misinterpreting
   a 2-integer struct/tuple as a wide pointer);
3. When any word has mismatched byte width (`resolveWideWordScalar? = .none`), `evalRvalue` returns
   `.unsupported`. -/
theorem widePtr_untyped_and_resolve_none_witnesses :
    resolveWideWordScalar? (.ptr ⟨7, 4⟩ 8) L64 testMem.borrows testMem.callerLocals [] testLayouts64
        8 = some ⟨458756, 8⟩ ∧
    evalRvalue L64 (.binaryOp .lt (cp 20) (cp 21)) testMem [] testLayouts64 =
      .ok (.scalar (boolToScalar false)) L64 testMem ∧
    evalRvalue L64 (.binaryOp .eq (cp 27) (cp 27)) testMem [] testLayouts64 = .unsupported ∧
    evalRvalue (L64.set 20 (.init (.aggregate 0 [.ptr ⟨7, 4⟩ 4, .scalar ⟨5, 8⟩])))
        (.binaryOp .eq (cp 20) (cp 21)) testMem testDecls testLayouts64 = .unsupported :=
  ⟨resolveWideWordScalar?_unborrowed_ptr ⟨7, 4⟩ L64 testMem.borrows testMem.callerLocals []
      testLayouts64 8 rfl,
    (trusted_evalRvalue_binaryOp_wide_ptr_untyped_rel_eq L64 L64 L64 .lt (cp 20) (cp 21) testMem []
      testLayouts64 (.ptr ⟨7, 4⟩ 8) (.scalar ⟨5, 8⟩) (.ptr ⟨7, 4⟩ 8) (.scalar ⟨3, 8⟩)
      rfl rfl rfl rfl rfl rfl rfl (Or.inl ⟨⟨7, 4⟩, 8, rfl⟩)).trans rfl,
    trusted_evalRvalue_binaryOp_untyped_two_scalars_unsupported L64 L64 L64 .eq (cp 27) (cp 27)
      testMem [] testLayouts64 ⟨4096, 8⟩ ⟨4096, 8⟩ (.scalar ⟨5, 8⟩) (.scalar ⟨5, 8⟩) rfl rfl rfl,
    trusted_evalRvalue_binaryOp_wide_ptr_resolve_none_unsupported
      (L64.set 20 (.init (.aggregate 0 [.ptr ⟨7, 4⟩ 4, .scalar ⟨5, 8⟩])))
      (L64.set 20 (.init (.aggregate 0 [.ptr ⟨7, 4⟩ 4, .scalar ⟨5, 8⟩])))
      (L64.set 20 (.init (.aggregate 0 [.ptr ⟨7, 4⟩ 4, .scalar ⟨5, 8⟩])))
      .eq (cp 20) (cp 21) testMem testDecls testLayouts64
      (.ptr ⟨7, 4⟩ 4) (.scalar ⟨5, 8⟩) (.ptr ⟨7, 4⟩ 8) (.scalar ⟨3, 8⟩) rfl rfl
      (Or.inl ((resolveWideWordScalar?_width_mismatch_eq_none _ _ _ _ _ 8).1 ⟨7, 4⟩ 4 (by decide)))⟩

end DispatchAndRangeWitnesses

/-! ## Uniform lexicographic ordering, structural `FnPtrToPtr`, misaligned `Unsize`, base lemmas -/

section OrderingAndStructuralWitnesses

open Anneal.Mir.PlaceAndRvalue

/-- Two stack borrows of local `0` with distinct tags: tag `1` at offset `0` (length `5`, local `5`)
and tag `3` at offset `4` (length `2`, local `6`). -/
def stackPairLocals (pb : Nat) : List LocalSlot :=
  (testLocals pb).set 6 (.init (.aggregate 0 [.ptr ⟨3, 4⟩ pb, .scalar ⟨2, pb⟩]))

/-- Provenance-less wide pointers: local `27` holds address `4096` (length `5`) and local `20` is
overwritten with address `8192` (length `1`). -/
def scalarPairLocals (pb : Nat) : List LocalSlot :=
  (testLocals pb).set 20 (.init (.aggregate 0 [.scalar ⟨8192, pb⟩, .scalar ⟨1, pb⟩]))

/-- Same unborrowed allocation `7`, offsets `4 < 8`: `lhs < rhs` holds even though the left length
`3` exceeds the right length `1` (the offset decides first; 64-bit). -/
theorem widePtr_same_alloc_lt_64 :
    evalRvalue L64 (.binaryOp .lt (cp 21) (cp 22)) testMem testDecls testLayouts64 =
      .ok (.scalar (boolToScalar true)) L64 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_same_alloc_ordering L64 L64 L64 .lt (cp 21) (cp 22) testMem
    testDecls testLayouts64 7 4 8 3 1 rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans rfl

/-- Same allocation and offset `4`: the length decides, `5 ≥ 3` (32-bit). -/
theorem widePtr_same_alloc_ge_len_32 :
    evalRvalue L32 (.binaryOp .ge (cp 20) (cp 21)) testMem testDecls testLayouts32 =
      .ok (.scalar (boolToScalar true)) L32 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_same_alloc_ordering L32 L32 L32 .ge (cp 20) (cp 21) testMem
    testDecls testLayouts32 7 4 4 5 3 rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans rfl

/-- `cmp` of offset `8` against offset `4` in the same allocation is `Greater` (`1`; 64-bit). -/
theorem widePtr_same_alloc_cmp_64 :
    evalRvalue L64 (.binaryOp .cmp (cp 22) (cp 20)) testMem testDecls testLayouts64 =
      .ok (.scalar ⟨1, 1⟩) L64 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_same_alloc_ordering L64 L64 L64 .cmp (cp 22) (cp 20) testMem
    testDecls testLayouts64 7 8 4 1 5 rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans rfl

/-- Distinct tags `1` (active) and `3` (frozen) of the same stack place compare by offset: `0 ≤ 4`
(64-bit, base address `(2^20 + 0) * 2^16`). -/
theorem widePtr_same_stack_place_le_64 :
    evalRvalue (stackPairLocals 8) (.binaryOp .le (cp 5) (cp 6)) testMem testDecls testLayouts64 =
      .ok (.scalar (boolToScalar true)) (stackPairLocals 8) testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_same_stack_place_ordering (stackPairLocals 8)
    (stackPairLocals 8) (stackPairLocals 8) .le (cp 5) (cp 6) testMem testDecls testLayouts64
    1 3 0 4 5 2 68719476736 activeEntry frozenEntry rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl

/-- The same pair on a 32-bit layout (base address `2^15 * 2^16`): `offset 4 > offset 0`. -/
theorem widePtr_same_stack_place_gt_32 :
    evalRvalue (stackPairLocals 4) (.binaryOp .gt (cp 6) (cp 5)) testMem testDecls testLayouts32 =
      .ok (.scalar (boolToScalar true)) (stackPairLocals 4) testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_same_stack_place_ordering (stackPairLocals 4)
    (stackPairLocals 4) (stackPairLocals 4) .gt (cp 6) (cp 5) testMem testDecls testLayouts32
    3 1 4 0 2 5 2147483648 frozenEntry activeEntry rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl

/-- Provenance-less addresses `4096` and `8192` differ, so `!=` holds (64-bit). -/
theorem widePtr_scalar_addr_ne_64 :
    evalRvalue (scalarPairLocals 8) (.binaryOp .ne (cp 27) (cp 20)) testMem testDecls
        testLayouts64 =
      .ok (.scalar (boolToScalar true)) (scalarPairLocals 8) testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_scalar_addr_ordering (scalarPairLocals 8)
    (scalarPairLocals 8) (scalarPairLocals 8) .ne (cp 27) (cp 20) testMem testDecls testLayouts64
    4096 8192 5 1 rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans rfl

/-- `cmp` of address `8192` against `4096` is `Greater` although the length is smaller (32-bit). -/
theorem widePtr_scalar_addr_cmp_32 :
    evalRvalue (scalarPairLocals 4) (.binaryOp .cmp (cp 20) (cp 27)) testMem testDecls
        testLayouts32 =
      .ok (.scalar ⟨1, 1⟩) (scalarPairLocals 4) testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_scalar_addr_ordering (scalarPairLocals 4)
    (scalarPairLocals 4) (scalarPairLocals 4) .cmp (cp 20) (cp 27) testMem testDecls testLayouts32
    8192 4096 1 5 rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans rfl

/-- A provenance-less wide pointer is `==` to itself (32-bit). -/
theorem widePtr_scalar_addr_eq_self_32 :
    evalRvalue L32 (.binaryOp .eq (cp 27) (cp 27)) testMem testDecls testLayouts32 =
      .ok (.scalar (boolToScalar true)) L32 testMem :=
  (trusted_evalRvalue_binaryOp_wide_ptr_scalar_addr_ordering L32 L32 L32 .eq (cp 27) (cp 27) testMem
    testDecls testLayouts32 4096 4096 5 5 rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans rfl

/-- A registered function pointer whose recorded signature is `rust-intrinsic`. -/
def intrinsicSigEntry : FnPtrEntry :=
  { allocId := 65536, defPath := "i", typeArgs := [], fnSig := some fnSigIntrinsic }

def memIntrinsicSig : Memory := { testMem with fnPtrs := [intrinsicSigEntry] }

/-- Structural `FnPtrToPtr` success: thin target, `fn()` source with ABI `rust`, and an 8-byte,
offset-0, unborrowed pointer in the synthetic function-pointer range of an empty `fnPtrs` table
(64-bit). -/
theorem fnPtrToPtr_structural_ok_64 :
    evalRvalue L64 (.cast .fnPtrToPtr (cp 8) { kind := .rawPtr .not u32Ty, layoutIdx := 1 }) testMem
        testDecls testLayouts64 = .ok (.ptr ⟨65536, 0⟩ 8) L64 testMem :=
  (trusted_evalRvalue_fnPtrToPtr_structural_iff L64 L64 (cp 8)
    { kind := .rawPtr .not u32Ty, layoutIdx := 1 } testMem testDecls testLayouts64 ⟨65536, 0⟩ 8
    rfl).1.mpr
    ⟨rfl, Or.inr ⟨[], .tuple [], .safe, .rust, 1, rfl, (fun h => by cases h)⟩, rfl, rfl, rfl,
      Or.inl ⟨rfl, rfl⟩⟩

/-- Structural `FnPtrToPtr` rejection: the source type is a non-intrinsic `fn()`, but the registered
`FnPtrEntry` records a `rust-intrinsic` signature, so `fnPtrToPtrRegistryOk` fails (32-bit). -/
theorem fnPtrToPtr_structural_intrinsic_registry_ub_32 :
    evalRvalue L32 (.cast .fnPtrToPtr (cp 8) { kind := .rawPtr .not u32Ty, layoutIdx := 1 })
        memIntrinsicSig testDecls testLayouts32 = .ub :=
  (trusted_evalRvalue_fnPtrToPtr_structural_iff L32 L32 (cp 8)
    { kind := .rawPtr .not u32Ty, layoutIdx := 1 } memIntrinsicSig testDecls testLayouts32
    ⟨65536, 0⟩ 8 rfl).2.mpr
    (fun ⟨_, _, _, _, _, hReg⟩ => by
      rcases hReg with ⟨hNil, _⟩ | ⟨_, entry, hE, hSig⟩
      · cases hNil
      · cases hE
        rcases hSig with h | ⟨_, _, _, _, h, hNe⟩
        · cases h
        · cases h
          exact hNe rfl)

/-- Locals whose `&[u32; 5]` (local `1`, tag `1`) points at byte offset `2` of the backing array. -/
def misalignedLocals (pb : Nat) : List LocalSlot := (testLocals pb).set 1 (.init (.ptr ⟨1, 2⟩ pb))

/-- A reborrow at byte offset `2` is not a whole `u32` element: `Unsize` faults on both widths. -/
theorem unsize_stack_misaligned_ub :
    evalRvalue (misalignedLocals 8)
        (.cast (.pointerCoercion "Unsize") (cp 1) (sliceTy (.ref .not (.slice u32Ty))))
        testMem testDecls testLayouts64 = .ub ∧
    evalRvalue (misalignedLocals 4)
        (.cast (.pointerCoercion "Unsize") (cp 1) (sliceTy (.ref .not (.slice u32Ty))))
        testMem testDecls testLayouts32 = .ub :=
  ⟨(trusted_evalUnsizeCoercion_stack_borrow_misaligned_ub (misalignedLocals 8) (misalignedLocals 8)
      (cp 1) testMem testDecls testLayouts64 true .not u32Ty 3
      { kind := .ref .not (.array u32Ty 5), layoutIdx := 1 } ⟨1, 2⟩ 5 activeEntry backing [] 0
      backingElems rfl rfl rfl rfl rfl rfl rfl rfl).2,
    (trusted_evalUnsizeCoercion_stack_borrow_misaligned_ub (misalignedLocals 4) (misalignedLocals 4)
      (cp 1) testMem testDecls testLayouts32 true .not u32Ty 3
      { kind := .ref .not (.array u32Ty 5), layoutIdx := 1 } ⟨1, 2⟩ 5 activeEntry backing [] 0
      backingElems rfl rfl rfl rfl rfl rfl rfl rfl).2⟩

/-- `LWidePtr` encoders produce exactly the runtime wide-pointer values of locals `20` and `27`. -/
theorem lwideptr_toValue_witnesses :
    (LWidePtr.ofProv ⟨7, 4⟩ 5 8).toValue = .aggregate 0 [.ptr ⟨7, 4⟩ 8, .scalar ⟨5, 8⟩] ∧
    (LWidePtr.ofScalar 4096 5 4).toValue = .aggregate 0 [.scalar ⟨4096, 4⟩, .scalar ⟨5, 4⟩] :=
  ⟨LWidePtr.toValue_ofProv _ _ _, LWidePtr.toValue_ofScalar _ _ _⟩

/-- `ClosureFnPointer(Safe)` is a closure coercion spelling; `ReifyFnPointer(Unsafe)` is not. -/
theorem closure_spelling_witnesses :
    isClosureFnPointerCoercion
        (LPointerCoercionKind.toRustcSpelling_V2026_06_01 (.closureFnPointer .safe)) = true ∧
    isClosureFnPointerCoercion
        (LPointerCoercionKind.toRustcSpelling_V2026_06_01 (.reifyFnPointerWithSafety .unsafe_)) =
      false :=
  ⟨(LPointerCoercionKind.isClosureFnPointerCoercion_toRustcSpelling_V2026_06_01 _).trans rfl,
    (LPointerCoercionKind.isClosureFnPointerCoercion_toRustcSpelling_V2026_06_01 _).trans rfl⟩

/-- `MutToConstPointer` has no target shape for a `*const` source or a `*mut` target. -/
theorem mutToConst_shape_none_witnesses :
    mutToConstTargetShape? (some { kind := .rawPtr .not u32Ty, layoutIdx := 1 })
        { kind := .rawPtr .not u32Ty, layoutIdx := 1 } = none ∧
    mutToConstTargetShape? (some { kind := .rawPtr .mut u32Ty, layoutIdx := 1 })
        { kind := .rawPtr .mut u32Ty, layoutIdx := 1 } = none :=
  ⟨mutToConstTargetShape?_const_source_eq_none _ _ _ _, mutToConstTargetShape?_mut_target_eq_none _ _ _⟩

/-- Direct witnesses of the step-level `evalAggregateRawPtr` lemmas (§3.B.1). -/
theorem rawPtrAgg_base_lemma_witnesses :
    evalAggregateRawPtr L32 { kind := .slice u32Ty, layoutIdx := 3 } [cp 12, cp 18] testMem
        testDecls testLayouts32 =
      .ok (.aggregate 0 [.scalar ⟨4096, 4⟩, .scalar ⟨5, 4⟩]) L32 testMem ∧
    evalAggregateRawPtr L64 { kind := u32Ty, layoutIdx := 1 } [cp 11, cp 19] testMem testDecls
        testLayouts64 = .ok (.ptr ⟨7, 0⟩ 8) L64 testMem ∧
    evalAggregateRawPtr L64 { kind := u32Ty, layoutIdx := 1 } [cp 11, cp 16] testMem testDecls
        testLayouts64 = .ok (.ptr ⟨7, 0⟩ 8) L64 testMem ∧
    evalAggregateRawPtr L32 { kind := .slice u32Ty, layoutIdx := 3 } [cp 11, cp 19] testMem
        testDecls testLayouts32 = .ub ∧
    evalAggregateRawPtr L64 { kind := u32Ty, layoutIdx := 1 } [cp 11, cp 18] testMem testDecls
        testLayouts64 = .ub ∧
    evalRvalue L64 (.aggregate (.rawPtr { kind := .str, layoutIdx := 3 } .not) [cp 11, cp 18])
        testMem testDecls testLayouts64 =
      .ok (.aggregate 0 [.ptr ⟨7, 0⟩ 8, .scalar ⟨5, 8⟩]) L64 testMem :=
  ⟨(evalAggregateRawPtr_scalar_scalar_ok L32 L32 _ [cp 12, cp 18] testMem testDecls testLayouts32
      ⟨4096, 4⟩ ⟨5, 4⟩ rfl (wideAggregatePointeeIsDyn?_slice _ _) rfl rfl).trans rfl,
    evalAggregateRawPtr_ptr_unit_ok L64 L64 _ [cp 11, cp 19] testMem testDecls testLayouts64
      ⟨7, 0⟩ rfl rfl,
    evalAggregateRawPtr_ptr_aggregate_nil_ok L64 L64 _ [cp 11, cp 16] testMem testDecls
      testLayouts64 ⟨7, 0⟩ rfl rfl,
    evalAggregateRawPtr_ptr_unit_unsized_ub L32 L32 _ [cp 11, cp 19] testMem testDecls
      testLayouts32 ⟨7, 0⟩ rfl rfl,
    evalAggregateRawPtr_ptr_scalar_sized_ub L64 L64 _ [cp 11, cp 18] testMem testDecls
      testLayouts64 ⟨7, 0⟩ ⟨5, 8⟩ rfl rfl,
    evalRvalue_aggregate_rawPtr_ptr_scalar_ok L64 L64 .not _ [cp 11, cp 18] testMem testDecls
      testLayouts64 ⟨7, 0⟩ ⟨5, 8⟩ rfl (wideAggregatePointeeIsDyn?_str _) rfl⟩

/-- Direct witnesses of the step-level `evalUnaryPtrMetadata` lemmas (§3.B.2). -/
theorem ptrMetadata_base_lemma_witnesses :
    evalUnaryPtrMetadata L64 (cp 11) testMem testDecls testLayouts64 = .ok .unit L64 testMem ∧
    evalUnaryPtrMetadata L32 (cp 12) testMem testDecls testLayouts32 = .ok .unit L32 testMem ∧
    evalUnaryPtrMetadata L64 (cp 27) testMem testDecls testLayouts64 =
      .ok (.scalar ⟨5, 8⟩) L64 testMem ∧
    evalUnaryPtrMetadata (L64.set 5 (.init (.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨5, 4⟩])))
        (cp 5) testMem testDecls testLayouts64 = .ub ∧
    evalRvalue L32 (.unaryOp .ptrMetadata (cp 5)) testMem testDecls testLayouts32 =
      .ok (.scalar ⟨5, 4⟩) L32 testMem :=
  ⟨evalUnaryPtrMetadata_ptr_ok L64 L64 (cp 11) testMem testDecls testLayouts64 ⟨7, 0⟩ rfl,
    evalUnaryPtrMetadata_scalar_ok L32 L32 (cp 12) testMem testDecls testLayouts32 ⟨4096, 4⟩ rfl rfl
      rfl,
    (evalUnaryPtrMetadata_scalar_scalar_ok L64 L64 (cp 27) testMem testDecls testLayouts64
      ⟨4096, 8⟩ ⟨5, 8⟩ rfl rfl rfl rfl).trans rfl,
    evalUnaryPtrMetadata_ptr_scalar_width_mismatch_ub
      (L64.set 5 (.init (.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨5, 4⟩])))
      (L64.set 5 (.init (.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨5, 4⟩]))) (cp 5) testMem testDecls
      testLayouts64 ⟨1, 0⟩ ⟨5, 4⟩ rfl rfl,
    evalRvalue_unaryOp_ptrMetadata_ptr_scalar_ok L32 L32 (cp 5) testMem testDecls testLayouts32
      ⟨1, 0⟩ ⟨5, 4⟩ rfl rfl⟩

/-- Direct witness of the step-level `evalPlaceLen` out-of-bounds lemma (§3.B.3): length word `6`
over the 5-element backing array of tag `1`. -/
theorem len_base_lemma_ub_witness :
    evalPlaceLen L64 (derefPlace 24) testMem testDecls testLayouts64 = .ub :=
  evalPlaceLen_slice_borrow_ub L64 L64 (derefPlace 24) testMem testDecls testLayouts64 [] []
    ⟨1, 0⟩ ⟨6, 8⟩ u32Ty _ activeEntry backing 0 backingElems 0 rfl rfl rfl rfl rfl
    (fun h => by cases h) rfl rfl rfl rfl

/-- Locals re-typed so that local `8` is an `unsafe fn()` pointer (an invalid `UnsafeFnPointer`
source). -/
def declsUnsafeFn8 : List LocalDecl :=
  testDecls.set 8 { mutability := .not, ty := { kind := fnSigUnsafe, layoutIdx := 1 }, debugName := none }

/-- Structural `UnsafeFnPointer` success through a *registered* `fnPtrs` entry whose recorded
signature is the safe `fn()` with ABI `rust` (32-bit; function pointers stay 8 bytes). -/
theorem unsafeFnPtr_structural_registered_ok_32 :
    evalRvalue L32 (.cast (.pointerCoercion "UnsafeFnPointer") (cp 8)
        { kind := fnSigUnsafe, layoutIdx := 1 }) memAfterInternF testDecls testLayouts32 =
      .ok (.ptr ⟨65536, 0⟩ 8) L32 memAfterInternF :=
  (trusted_evalRvalue_unsafeFnPointer_structural_iff L32 L32 (cp 8)
    { kind := fnSigUnsafe, layoutIdx := 1 } memAfterInternF testDecls testLayouts32 ⟨65536, 0⟩ 8 []
    (.tuple []) .rust rfl rfl).1.mpr
    ⟨(fun h => by cases h), Or.inr ⟨[], .tuple [], 1, rfl, rfl, rfl⟩, rfl, rfl, rfl,
      Or.inr ⟨(fun h => by cases h), fnEntryF, rfl, Or.inr ⟨[], .tuple [], rfl, rfl, rfl⟩⟩⟩

/-- Structural `UnsafeFnPointer` rejection: an `unsafe fn()` source is not a *safe* `fn` pointer, so
the coercion faults (64-bit). -/
theorem unsafeFnPtr_structural_unsafe_source_ub_64 :
    evalRvalue L64 (.cast (.pointerCoercion "UnsafeFnPointer") (cp 8)
        { kind := fnSigUnsafe, layoutIdx := 1 }) testMem declsUnsafeFn8 testLayouts64 = .ub :=
  (trusted_evalRvalue_unsafeFnPointer_structural_iff L64 L64 (cp 8)
    { kind := fnSigUnsafe, layoutIdx := 1 } testMem declsUnsafeFn8 testLayouts64 ⟨65536, 0⟩ 8 []
    (.tuple []) .rust rfl rfl).2.mpr
    (fun ⟨_, hSrc, _⟩ => by
      rcases hSrc with h | ⟨_, _, _, h, _⟩ <;> cases h)

end OrderingAndStructuralWitnesses

/-! ## Kernel axiom audit -/

/-! Audits every declaration added by Episode 2 to `Anneal.Mir.Cast` (Section 9, starting at
`LWidePtrData`) and `Anneal.Mir.PlaceAndRvalue` (Section 3.B, starting at
`evalAggregateRawPtr_ptr_scalar_ok`), plus every witness in this file: no `unsafe` declaration, and
every axiom used is in `{propext, Classical.choice, Quot.sound}` (so no `sorryAx` and no
`Lean.ofReduceBool` / `native_decide`). Fails if fewer declarations than expected are found.

Non-vacuity: additionally fails unless *every* audited module theorem is reachable from the concrete
witnesses of this file, i.e. used by some witness either directly or through a chain of other
audited declarations, so no Episode 2 theorem is left uninstantiated. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut audited : Nat := 0
  let mut theorems : Nat := 0
  let mut auditedSet : NameSet := {}
  let mut auditedThms : Array Name := #[]
  for (modName, anchor, minCount) in
      [(`Anneal.Mir.Cast, ``Anneal.Mir.Cast.LWidePtrData, 90),
       (`Anneal.Mir.PlaceAndRvalue,
         ``Anneal.Mir.PlaceAndRvalue.evalAggregateRawPtr_ptr_scalar_ok, 50)] do
    let some modIdx := env.getModuleIdx? modName | throwError "module {modName} not imported"
    let some anchorRange ← findDeclarationRanges? anchor | throwError "no range for {anchor}"
    let startLine := anchorRange.range.pos.line
    let mut count : Nat := 0
    for (n, ci) in env.constants.map₁.toList do
      if env.getModuleIdxFor? n == some modIdx then
        if let some r ← findDeclarationRanges? n then
          if r.range.pos.line ≥ startLine then
            if ci.isUnsafe then throwError "unsafe declaration: {n}"
            let axs ← collectAxioms n
            for a in axs do
              unless allowed.contains a do
                throwError "{n} depends on disallowed axiom {a}"
            count := count + 1
            auditedSet := auditedSet.insert n
            if ci matches .thmInfo _ then
              theorems := theorems + 1
              auditedThms := auditedThms.push n
    if count < minCount then
      throwError "{modName}: audited only {count} declarations (expected ≥ {minCount})"
    audited := audited + count
  let mut reached : NameSet := {}
  let mut work : Array Name := #[]
  for (n, ci) in env.constants.map₂.toList do
    if (`Anneal.WidePtrSliceFnPtrTests).isPrefixOf n then
      if ci.isUnsafe then throwError "unsafe declaration: {n}"
      let axs ← collectAxioms n
      for a in axs do
        unless allowed.contains a do
          throwError "{n} depends on disallowed axiom {a}"
      audited := audited + 1
      for c in ci.getUsedConstantsAsSet do
        if auditedSet.contains c && !reached.contains c then
          reached := reached.insert c
          work := work.push c
  while !work.isEmpty do
    let c := work.back!
    work := work.pop
    if let some ci := env.find? c then
      for d in ci.getUsedConstantsAsSet do
        if auditedSet.contains d && !reached.contains d then
          reached := reached.insert d
          work := work.push d
  let unreached := auditedThms.filter (fun n => !reached.contains n)
  unless unreached.isEmpty do
    throwError "theorems not instantiated by any witness: {unreached.toList}"
  logInfo m!"axiom audit passed: {audited} declarations ({theorems} module theorems, all \
    instantiated by witnesses)"

end Anneal.WidePtrSliceFnPtrTests
