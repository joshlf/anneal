/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.MirLoops

namespace Anneal.TcbCorrespondenceDiv8Tests

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open Anneal.MirLoops (mkMirBody)

/-!
# Concrete witnesses for the eight tracked `Trusted.MirSemantics` correspondence repairs

Each section pins one repaired divergence (see `TRACKED_CORRESPONDENCE_DIVERGENCES` in
`scripts/run_nightly_verification_suite.py`) on a small concrete state, checked by `rfl` /
`decide` against `Trusted.Rustc.V2026_06_01.MirSemantics`:

1. `DIV-MR-CALL-TARGET-LOCAL`: a dereference through a tag minted in the caller (frame depth `0`)
   reads the caller's saved local, not the callee's local of the same index.
2. `DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL`: a callee write to its own local `_1` (depth `1`)
   leaves the caller's borrow of the caller's `_1` (depth `0`) untouched.
3. `DIV-MR-TB-TWOPHASE-DIRECT-WRITE`: a direct write disables an unprotected `Reserved` tag.
4. `DIV-MR-TB-FNENTRY-LOCAL-DEALLOC`: frame teardown with a protected, deallocation-preventing
   borrow of a returning-frame local is a protector conflict.
5. `DIV-MR-TB-UNSAFECELL-PROTECTED-IM`: a protected `Cell` (interior-mutable) tag does not prevent
   deallocation.
6. `DIV-LM-RAW-OVERWRITE-CHAR-COPY`: typed loads of `char` reject surrogates.
7. `DIV-LM-D6-OFFSET-DISABLED-TAG`: `BinOp.Offset` through a `.disabled` tag on a live local
   follows allocation bounds; only `allocDead` collapses the bound to `0`.
8. `DIV-LM-ENUM-SET-DISCR-UNINIT`: `SetDiscriminant` on an uninitialized enum local writes the
   variant.
-/

/-- `u32` type (`layoutIdx` `0`). -/
def u32T : Ty := { kind := .uint .u32, layoutIdx := 0 }

/-- Caller body (empty; only its saved frame matters for these witnesses). -/
def callerBody : CapturedMir := mkMirBody "tests::caller" 0 [] []

/-- Saved caller frame (depth `0`): `_0 = 0`, `_1 = 42`. -/
def callerFrame : SavedCallerFrame := {
  callerBody := callerBody
  frame := { blockIdx := 0, stmtIdx := 0,
             locals := [.init (.scalar ⟨0, 4⟩), .init (.scalar ⟨42, 4⟩)] }
  destination := { local_ := 0, projection := [] }
}

/-- Caller-minted `&mut _1` (tag `5`) targeting the caller's local `_1` at depth `0`. -/
def callerEntry : BorrowEntry :=
  { tag := 5, targetLocal := 1, targetProjection := [], perm := .active, targetFrameDepth := 0 }

/-- Callee frame (depth `1`): `_0` uninit, `_1 = 137`, `_2 = ptr(tag 5)`. -/
def calleeLocals : List LocalSlot :=
  [.uninit, .init (.scalar ⟨137, 4⟩), .init (.ptr { allocId := 5, offsetBytes := 0 } 8)]

/-! ## 1. `DIV-MR-CALL-TARGET-LOCAL` -/

/-- Reading `*_2` in the callee returns the caller's `_1 = 42` (not the callee's `_1 = 137`). -/
theorem call_target_local_reads_owning_frame :
    evalOperand calleeLocals (.copy { local_ := 2, projection := [.deref] }) [callerEntry] []
        emptyLayoutTable [] [] [callerFrame] =
      .ok (.scalar ⟨42, 4⟩) calleeLocals := rfl

/-- At the root frame (`callStack = []`) the same tag targets the active frame's `_1`. -/
theorem call_target_local_root_frame_reads_active_local :
    evalOperand calleeLocals (.copy { local_ := 2, projection := [.deref] }) [callerEntry] []
        emptyLayoutTable [] [] [] =
      .ok (.scalar ⟨137, 4⟩) calleeLocals := rfl

/-! ## 2. `DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL` -/

/-- A callee (depth `1`) direct write to its `_1` neither conflicts with nor invalidates the
caller's borrow of the caller's `_1`; the same write at depth `0` would disable it. -/
theorem caller_borrow_survives_callee_write :
    hasProtectedWriteConflict [{ callerEntry with protector := .some 3 }] [3] 1 .none .nil 0 0 1 =
      false ∧
    invalidateConflictingBorrows [callerEntry] 1 .none 1 = [callerEntry] ∧
    ((invalidateConflictingBorrows [callerEntry] 1 .none 0).map (·.perm)) = [.disabled] := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## 3. `DIV-MR-TB-TWOPHASE-DIRECT-WRITE` -/

/-- An unprotected two-phase (`.reservedFrz false`) tag is disabled by a direct root write. -/
theorem twophase_direct_write_disables_reserved :
    (updateBorrowPerm { callerEntry with perm := .reservedFrz false } 1 .none).perm = .disabled :=
  rfl

/-! ## 4–5. `DIV-MR-TB-FNENTRY-LOCAL-DEALLOC` and `DIV-MR-TB-UNSAFECELL-PROTECTED-IM` -/

/-- Protected `&mut` of a returning-frame (depth `1`) local blocks teardown; a protected `Cell`
tag, a borrow of another frame, or no active protector does not. -/
theorem frame_dealloc_protector_conflict :
    hasFrameDeallocProtectorConflict
        [{ callerEntry with targetFrameDepth := 1, protector := .some 7 }] [7] 1 3 = true ∧
    hasFrameDeallocProtectorConflict
        [{ callerEntry with targetFrameDepth := 1, protector := .some 7, perm := .cell }] [7] 1 3 =
      false ∧
    hasFrameDeallocProtectorConflict
        [{ callerEntry with protector := .some 7 }] [7] 1 3 = false ∧
    hasFrameDeallocProtectorConflict
        [{ callerEntry with targetFrameDepth := 1, protector := .some 7 }] [] 1 3 = false := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- `StorageDead` of a local protected by a `Cell` tag is allowed; by `&mut` it is not. -/
theorem unsafecell_protected_storage_dead :
    hasProtectedLocalBorrow [{ callerEntry with protector := .some 7, perm := .cell }] [7] 1 =
      false ∧
    hasProtectedLocalBorrow [{ callerEntry with protector := .some 7 }] [7] 1 = true := by
  refine ⟨rfl, rfl⟩

/-- Returning-frame teardown disables the frame's borrows and marks their allocation dead. -/
theorem frame_teardown_disables_and_kills :
    disableFrameBorrows [{ callerEntry with targetFrameDepth := 1 }, callerEntry] 1 3 =
      [{ callerEntry with targetFrameDepth := 1, perm := .disabled, allocDead := true },
        callerEntry] := rfl

/-! ## 6. `DIV-LM-RAW-OVERWRITE-CHAR-COPY` -/

/-- Single `char` local `_0`. -/
def charDecls : List LocalDecl :=
  [{ mutability := .mut, ty := { kind := .char, layoutIdx := 0 }, debugName := none }]

/-- Typed `char` loads reject the surrogate `0xD800` and out-of-range codes. -/
theorem char_load_validation :
    validateLoadedValue emptyLayoutTable charDecls (.copy { local_ := 0, projection := [] })
        (.scalar ⟨0xD800, 4⟩) = false ∧
    validateLoadedValue emptyLayoutTable charDecls (.copy { local_ := 0, projection := [] })
        (.scalar ⟨0x110000, 4⟩) = false ∧
    validateLoadedValue emptyLayoutTable charDecls (.copy { local_ := 0, projection := [] })
        (.scalar ⟨0x41, 4⟩) = true := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## 7. `DIV-LM-D6-OFFSET-DISABLED-TAG` -/

/-- Root-frame local `_0 : [u32; 4]`-like storage (`aggregate` of four `u32`). -/
def arrLocals : List LocalSlot :=
  [.init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩])]

/-- A `.disabled` tag on a live local keeps the local's byte bound; `allocDead` makes it `0`. -/
theorem offset_bound_disabled_vs_dead :
    ptrAllocByteBound? arrLocals
        { emptyMemory with borrows := [{ callerEntry with targetLocal := 0, perm := .disabled }] }
        [] emptyLayoutTable { allocId := 5, offsetBytes := 0 } =
      ptrAllocByteBound? arrLocals
        { emptyMemory with borrows := [{ callerEntry with targetLocal := 0 }] }
        [] emptyLayoutTable { allocId := 5, offsetBytes := 0 } ∧
    ptrAllocByteBound? arrLocals
        { emptyMemory with
          borrows := [{ callerEntry with targetLocal := 0, perm := .disabled, allocDead := true }] }
        [] emptyLayoutTable { allocId := 5, offsetBytes := 0 } = .some 0 := by
  refine ⟨rfl, rfl⟩

/-! ## 8. `DIV-LM-ENUM-SET-DISCR-UNINIT` -/

/-- `SetDiscriminant` on an uninitialized ADT local initializes the variant (no fields). -/
theorem set_discriminant_on_uninit_adt :
    setDiscriminantUninitDeclOk
        [{ mutability := .mut, ty := { kind := .adt "tests::E" [], layoutIdx := 0 },
           debugName := none }] 0 = true ∧
    setDiscriminantUninitDeclOk
        [{ mutability := .mut, ty := u32T, debugName := none }] 0 = false ∧
    evalSetDiscriminantLocal
        { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }, memory := emptyMemory }
        0 1 [] =
      MirStepNode.step
        (advanceStmt
          { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }, memory := emptyMemory }
          [.init (.aggregate 1 [])] emptyMemory) := by
  refine ⟨rfl, rfl, rfl⟩

end Anneal.TcbCorrespondenceDiv8Tests
