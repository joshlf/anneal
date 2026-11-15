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

/-! ## End-to-End `stepMirFn` Witness & Canary Execution Suite -/

/-- Fuel-bounded execution of `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn`, returning
`.some (bits, sizeBytes)` on normal scalar return. -/
def runScalarFuel (body : CapturedMir) : Nat → MachineState → Option (Nat × Nat)
  | 0, _ => .none
  | fuel + 1, s =>
    match stepMirFn body s with
    | .tau (.running s') => runScalarFuel body fuel s'
    | .ret (.normal (.scalar sc, _)) => .some (sc.bits, sc.sizeBytes)
    | _ => .none

/-- Fuel-bounded fault check on `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn`, returning
`true` when execution faults with `.ub` (`MirStepNode.fail .ub` or `.tau (.faulted .ub)`). -/
def faultsUBFuel (body : CapturedMir) : Nat → MachineState → Bool
  | 0, _ => false
  | fuel + 1, s =>
    match stepMirFn body s with
    | .tau next =>
      match next with
      | .running s' => faultsUBFuel body fuel s'
      | .faulted .ub => true
      | _ => false
    | .vis op _ =>
      match op with
      | .inl (.fail .ub) => true
      | _ => false
    | _ => false

/-- Run `body` from `initMachineStateWithCallees body args callees` and return scalar result. -/
def runTrustedScalar? (body : CapturedMir) (callees : List CapturedMir) (args : List Value)
    (fuel : Nat := 40) : Option (Nat × Nat) :=
  runScalarFuel body fuel (initMachineStateWithCallees body args callees)

/-- Check whether `body` faults with `.ub` from `initMachineStateWithCallees body args callees`. -/
def trustedFaultsUB (body : CapturedMir) (callees : List CapturedMir) (args : List Value)
    (fuel : Nat := 40) : Bool :=
  faultsUBFuel body fuel (initMachineStateWithCallees body args callees)

def u32Decl : LocalDecl := { mutability := .mut, ty := u32T, debugName := none }
def u64T : Ty := { kind := .uint .u64, layoutIdx := 0 }
def u64Decl : LocalDecl := { mutability := .mut, ty := u64T, debugName := none }
def usizeT : Ty := { kind := .uint .usize, layoutIdx := 0 }
def isizeT : Ty := { kind := .int .isize, layoutIdx := 0 }
def isizeDecl : LocalDecl := { mutability := .mut, ty := isizeT, debugName := none }
def charT : Ty := { kind := .char, layoutIdx := 0 }
def charDecl : LocalDecl := { mutability := .mut, ty := charT, debugName := none }
def refSharedU32Decl : LocalDecl :=
  { mutability := .mut, ty := { kind := .ref .not (.uint .u32), layoutIdx := 0 }, debugName := none }
def refMutU32Decl : LocalDecl :=
  { mutability := .mut, ty := { kind := .ref .mut (.uint .u32), layoutIdx := 0 }, debugName := none }
def ptrConstU32Decl : LocalDecl :=
  { mutability := .mut, ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 }, debugName := none }
def ptrMutU32Decl : LocalDecl :=
  { mutability := .mut, ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 0 }, debugName := none }
def ptrMutU64Decl : LocalDecl :=
  { mutability := .mut, ty := { kind := .rawPtr .mut (.uint .u64), layoutIdx := 0 }, debugName := none }
def ptrMutCharDecl : LocalDecl :=
  { mutability := .mut, ty := { kind := .rawPtr .mut .char, layoutIdx := 0 }, debugName := none }
def optionU32T : Ty := { kind := .adt "core::option::Option" [.uint .u32], layoutIdx := 0 }
def optionU32Decl : LocalDecl := { mutability := .mut, ty := optionU32T, debugName := none }
def refSharedOptionU32Decl : LocalDecl :=
  { mutability := .mut,
    ty := { kind := .ref .not (.adt "core::option::Option" [.uint .u32]), layoutIdx := 0 },
    debugName := none }
def unsafeCellU32T : Ty := { kind := .adt "core::cell::UnsafeCell" [.uint .u32], layoutIdx := 0 }
def unsafeCellU32Decl : LocalDecl := { mutability := .mut, ty := unsafeCellU32T, debugName := none }
def refSharedUnsafeCellU32Decl : LocalDecl :=
  { mutability := .mut,
    ty := { kind := .ref .not (.adt "core::cell::UnsafeCell" [.uint .u32]), layoutIdx := 0 },
    debugName := none }
def refMutUnsafeCellU32Decl : LocalDecl :=
  { mutability := .mut,
    ty := { kind := .ref .mut (.adt "core::cell::UnsafeCell" [.uint .u32]), layoutIdx := 0 },
    debugName := none }

def unsafeCellU32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .arbitrary [{ bytes := 0 }] [0],
    variants := .single 0, isUninhabited := false, fieldLayouts := [0] }

def unsafeCellU32Layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [unsafeCellU32Layout] }

def locPlace (n : Nat) : Place := { local_ := n, projection := [] }
def derefPlace (n : Nat) : Place := { local_ := n, projection := [.deref] }
def derefField0U32Place (n : Nat) : Place :=
  { local_ := n, projection := [.deref, .field 0 u32T] }
def somePayloadPlace (n : Nat) : Place :=
  { local_ := n, projection := [.downcast (some "Some") 1, .field 0 u32T] }
def constU32 (n : Nat) : Operand :=
  .constant { ty := u32T, val := .scalar (.int ⟨n, 4⟩) }
def constU64 (n : Nat) : Operand :=
  .constant { ty := u64T, val := .scalar (.int ⟨n, 8⟩) }
def constUsize (n : Nat) : Operand :=
  .constant { ty := usizeT, val := .scalar (.int ⟨n, 8⟩) }
def constIsize (n : Nat) : Operand :=
  .constant { ty := isizeT, val := .scalar (.int ⟨n, 8⟩) }
def fnDefOp (dp : DefPath) (typeArgs : List RigidTy := []) : Operand :=
  .constant { ty := { kind := .fnDef dp typeArgs, layoutIdx := 0 }, val := .zeroSized }
def mkStmt (k : StatementKind) : Statement := { kind := k, span := "" }
def mkTerm (k : TerminatorKind) : Terminator := { kind := k, span := "" }

def singleBlockBody (dp : DefPath) (argCount : Nat) (decls : List LocalDecl)
    (stmts : List StatementKind) (layouts : LayoutTable := emptyLayoutTable) : CapturedMir :=
  { (mkMirBody dp argCount decls
      [{ statements := stmts.map mkStmt, terminator := mkTerm .return_, isCleanup := false }]) with
    layouts := layouts }

/-- 1a. `DIV-MR-CALL-TARGET-LOCAL` read witness (`callerRefMutSilentWrongLocalMir` +
`calleeReadRefWithLocalMir`). -/
def calleeReadRefWithLocalMir : CapturedMir :=
  singleBlockBody "witness::callee_read_ref_with_local" 2
    [u32Decl, u32Decl, refMutU32Decl]
    [.retag .fnEntry (locPlace 2),
     .assign (locPlace 0) (.binaryOp .add (.copy (derefPlace 2)) (constU32 37))]

def callerRefMutSilentWrongLocalMir : CapturedMir :=
  mkMirBody "witness::caller_ref_mut_silent_wrong_local" 1
    [u32Decl, u32Decl, refMutU32Decl]
    [{ statements :=
         [mkStmt (.storageLive 2),
          mkStmt (.assign (locPlace 2) (.ref (.mut false) (locPlace 1)))],
       terminator := mkTerm (.call (fnDefOp "witness::callee_read_ref_with_local")
         [constU32 100, .move (locPlace 2)] (locPlace 0) (some 1) .continue_),
       isCleanup := false },
     { statements := [mkStmt (.storageDead 2)],
       terminator := mkTerm .return_,
       isCleanup := false }]

/-- 1b. `DIV-MR-CALL-TARGET-LOCAL` write-back witness (`callerWriteBackMir` +
`calleeWriteRefWithLocalMir`). -/
def calleeWriteRefWithLocalMir : CapturedMir :=
  singleBlockBody "witness::write_ref_with_local" 2
    [u32Decl, u32Decl, refMutU32Decl]
    [.retag .fnEntry (locPlace 2),
     .assign (derefPlace 2) (.binaryOp .add (.copy (derefPlace 2)) (constU32 37)),
     .assign (locPlace 0) (.use (.copy (locPlace 1)))]

def callerWriteBackMir : CapturedMir :=
  mkMirBody "witness::caller_write_back" 1
    [u32Decl, u32Decl, refMutU32Decl, u32Decl, u32Decl]
    [{ statements :=
         [mkStmt (.storageLive 2),
          mkStmt (.storageLive 3),
          mkStmt (.assign (locPlace 2) (.ref (.mut false) (locPlace 1)))],
       terminator := mkTerm (.call (fnDefOp "witness::write_ref_with_local")
         [constU32 100, .move (locPlace 2)] (locPlace 3) (some 1) .continue_),
       isCleanup := false },
     { statements :=
         [mkStmt (.storageLive 4),
          mkStmt (.assign (locPlace 4) (.binaryOp .mul (.copy (locPlace 1)) (constU32 1000))),
          mkStmt (.assign (locPlace 0) (.binaryOp .add (.copy (locPlace 4)) (.copy (locPlace 3)))),
          mkStmt (.storageDead 4),
          mkStmt (.storageDead 3),
          mkStmt (.storageDead 2)],
       terminator := mkTerm .return_,
       isCleanup := false }]

/-- 1c. `DIV-MR-CALL-TARGET-LOCAL` cross-frame `copy_nonoverlapping` canary:
`calleeCopyNonOverlappingMir` copies `1` element from `src` (`&raw const caller._1`) to
`dst` (`&raw mut caller._2`) while its own `_1 = 100` and `_2 = 200` share the same local
indices. -/
def calleeCopyNonOverlappingMir : CapturedMir :=
  singleBlockBody "witness::callee_copy_nonoverlapping" 4
    [u32Decl, u32Decl, u32Decl, ptrConstU32Decl, ptrMutU32Decl]
    [.intrinsic (.copyNonOverlapping (.copy (locPlace 3)) (.copy (locPlace 4)) (constUsize 1)),
     .assign (locPlace 0) (.binaryOp .add (.copy (locPlace 1)) (.copy (locPlace 2)))]

def callerCopyNonOverlappingMir : CapturedMir :=
  mkMirBody "witness::caller_copy_nonoverlapping" 1
    [u32Decl, u32Decl, u32Decl, ptrConstU32Decl, ptrMutU32Decl, u32Decl, u32Decl]
    [{ statements :=
         [mkStmt (.storageLive 2),
          mkStmt (.storageLive 3),
          mkStmt (.storageLive 4),
          mkStmt (.storageLive 5),
          mkStmt (.assign (locPlace 2) (.use (constU32 0))),
          mkStmt (.assign (locPlace 3) (.rawPtr .not (locPlace 1))),
          mkStmt (.assign (locPlace 4) (.rawPtr .mut (locPlace 2)))],
       terminator := mkTerm (.call (fnDefOp "witness::callee_copy_nonoverlapping")
         [constU32 100, constU32 200, .move (locPlace 3), .move (locPlace 4)]
         (locPlace 5) (some 1) .continue_),
       isCleanup := false },
     { statements :=
         [mkStmt (.storageLive 6),
          mkStmt (.assign (locPlace 6) (.binaryOp .mul (.copy (locPlace 2)) (constU32 1000))),
          mkStmt (.assign (locPlace 0) (.binaryOp .add (.copy (locPlace 6)) (.copy (locPlace 5)))),
          mkStmt (.storageDead 6),
          mkStmt (.storageDead 5),
          mkStmt (.storageDead 4),
          mkStmt (.storageDead 3),
          mkStmt (.storageDead 2)],
       terminator := mkTerm .return_,
       isCleanup := false }]

/-- 1d. `DIV-MR-CALL-TARGET-LOCAL` cross-frame inline intrinsic destination canary:
`calleeIntrinsicDestDerefMir` calls `core::intrinsics::wrapping_add` with `destination = *_2`
(where `_2 : &mut u32` points to the caller's `_1` at depth `0` while the callee's own `_1` is
`100`). -/
def calleeIntrinsicDestDerefMir : CapturedMir :=
  mkMirBody "witness::callee_intrinsic_dest_deref" 2
    [u32Decl, u32Decl, refMutU32Decl]
    [{ statements := [mkStmt (.retag .fnEntry (locPlace 2))],
       terminator := mkTerm (.call (fnDefOp "core::intrinsics::wrapping_add" [.uint .u32])
         [.copy (derefPlace 2), constU32 37] (derefPlace 2) (some 1) .continue_),
       isCleanup := false },
     { statements := [mkStmt (.assign (locPlace 0) (.use (.copy (locPlace 1))))],
       terminator := mkTerm .return_,
       isCleanup := false }]

def callerIntrinsicDestDerefMir : CapturedMir :=
  mkMirBody "witness::caller_intrinsic_dest_deref" 1
    [u32Decl, u32Decl, refMutU32Decl, u32Decl, u32Decl]
    [{ statements :=
         [mkStmt (.storageLive 2),
          mkStmt (.storageLive 3),
          mkStmt (.assign (locPlace 2) (.ref (.mut false) (locPlace 1)))],
       terminator := mkTerm (.call (fnDefOp "witness::callee_intrinsic_dest_deref")
         [constU32 100, .move (locPlace 2)] (locPlace 3) (some 1) .continue_),
       isCleanup := false },
     { statements :=
         [mkStmt (.storageLive 4),
          mkStmt (.assign (locPlace 4) (.binaryOp .mul (.copy (locPlace 1)) (constU32 1000))),
          mkStmt (.assign (locPlace 0) (.binaryOp .add (.copy (locPlace 4)) (.copy (locPlace 3)))),
          mkStmt (.storageDead 4),
          mkStmt (.storageDead 3),
          mkStmt (.storageDead 2)],
       terminator := mkTerm .return_,
       isCleanup := false }]

theorem div1_call_target_local_end_to_end :
    runTrustedScalar? callerRefMutSilentWrongLocalMir [calleeReadRefWithLocalMir]
      [.scalar ⟨5, 4⟩] = .some (42, 4) ∧
    runTrustedScalar? callerWriteBackMir [calleeWriteRefWithLocalMir]
      [.scalar ⟨5, 4⟩] = .some (42100, 4) ∧
    runTrustedScalar? callerCopyNonOverlappingMir [calleeCopyNonOverlappingMir]
      [.scalar ⟨42, 4⟩] = .some (42300, 4) ∧
    runTrustedScalar? callerIntrinsicDestDerefMir [calleeIntrinsicDestDerefMir]
      [.scalar ⟨5, 4⟩] = .some (42100, 4) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- 2. `DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL` end-to-end witness. -/
def calleeScalarAssignLocal1Mir : CapturedMir :=
  singleBlockBody "witness::callee_scalar_assign_local1" 1
    [u32Decl, u32Decl]
    [.assign (locPlace 1) (.binaryOp .add (.copy (locPlace 1)) (constU32 1)),
     .assign (locPlace 0) (.use (.copy (locPlace 1)))]

def callerBorrowAcrossScalarCallMir : CapturedMir :=
  mkMirBody "witness::caller_borrow_across_scalar_call" 1
    [u32Decl, u32Decl, refMutU32Decl, u32Decl]
    [{ statements :=
         [mkStmt (.storageLive 2),
          mkStmt (.storageLive 3),
          mkStmt (.assign (locPlace 2) (.ref (.mut false) (locPlace 1))),
          mkStmt (.assign (derefPlace 2) (.use (constU32 41)))],
       terminator := mkTerm (.call (fnDefOp "witness::callee_scalar_assign_local1")
         [constU32 0] (locPlace 3) (some 1) .continue_),
       isCleanup := false },
     { statements :=
         [mkStmt (.assign (locPlace 0)
            (.binaryOp .add (.copy (derefPlace 2)) (.copy (locPlace 3)))),
          mkStmt (.storageDead 3),
          mkStmt (.storageDead 2)],
       terminator := mkTerm .return_,
       isCleanup := false }]

theorem div2_caller_borrow_across_scalar_call_end_to_end :
    runTrustedScalar? callerBorrowAcrossScalarCallMir [calleeScalarAssignLocal1Mir]
      [.scalar ⟨5, 4⟩] = .some (42, 4) := by
  decide +kernel

/-- 3. `DIV-MR-TB-TWOPHASE-DIRECT-WRITE` end-to-end witness & `UnsafeCell` survival canary. -/
def twoPhaseDirectWriteMir : CapturedMir :=
  singleBlockBody "witness::twophase_direct_write" 1
    [u32Decl, u32Decl, refMutU32Decl]
    [.storageLive 2,
     .assign (locPlace 2) (.ref (.mut true) (locPlace 1)),
     .retag .twoPhase (locPlace 2),
     .assign (locPlace 1) (.use (constU32 99)),
     .assign (locPlace 0) (.use (.copy (derefPlace 2))),
     .storageDead 2]

def unsafeCellDirectWriteSurvivesMir : CapturedMir :=
  singleBlockBody "witness::unsafe_cell_direct_write_survives" 1
    [u32Decl, unsafeCellU32Decl, refMutUnsafeCellU32Decl, refSharedUnsafeCellU32Decl,
     u32Decl, u32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
     .assign (locPlace 2) (.ref (.mut false) (locPlace 1)),
     .assign (locPlace 3) (.ref .shared (locPlace 1)),
     .assign (locPlace 1) (.aggregate (.adt "core::cell::UnsafeCell" 0 none) [constU32 44]),
     .assign (locPlace 4) (.use (.copy (derefField0U32Place 2))),
     .assign (locPlace 5) (.use (.copy (derefField0U32Place 3))),
     .assign (locPlace 0) (.binaryOp .add (.copy (locPlace 4)) (.copy (locPlace 5))),
     .storageDead 5, .storageDead 4, .storageDead 3, .storageDead 2]
    unsafeCellU32Layouts

theorem div3_twophase_direct_write_end_to_end :
    trustedFaultsUB twoPhaseDirectWriteMir [] [.scalar ⟨5, 4⟩] = true ∧
    runTrustedScalar? unsafeCellDirectWriteSurvivesMir []
      [.aggregate 0 [.scalar ⟨5, 4⟩]] = .some (88, 4) := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- 4–5. `DIV-MR-TB-FNENTRY-LOCAL-DEALLOC` & `DIV-MR-TB-UNSAFECELL-PROTECTED-IM` end-to-end
witnesses and canaries. -/
def retagFnEntryLocalDeallocUbMir : CapturedMir :=
  singleBlockBody "witness::retag_fn_entry_local_dealloc_ub" 1
    [u32Decl, u32Decl, refSharedU32Decl]
    [.storageLive 2,
     .assign (locPlace 2) (.ref .shared (locPlace 1)),
     .retag .fnEntry (locPlace 2),
     .assign (locPlace 0) (.use (.copy (derefPlace 2)))]

def callerOfFnEntryLocalDeallocMir : CapturedMir :=
  mkMirBody "witness::caller_of_fn_entry_local_dealloc" 1
    [u32Decl, u32Decl]
    [{ statements := [],
       terminator := mkTerm (.call (fnDefOp "witness::retag_fn_entry_local_dealloc_ub")
         [.copy (locPlace 1)] (locPlace 0) (some 1) .continue_),
       isCleanup := false },
     { statements := [],
       terminator := mkTerm .return_,
       isCleanup := false }]

def calleeReturnRawPtrToLocalMir : CapturedMir :=
  singleBlockBody "witness::callee_return_raw_ptr_to_local" 1
    [ptrMutU32Decl, u32Decl]
    [.assign (locPlace 0) (.rawPtr .mut (locPlace 1))]

def callerDerefReturnedCalleeRawPtrMir : CapturedMir :=
  mkMirBody "witness::caller_deref_returned_callee_raw_ptr" 1
    [u32Decl, u32Decl, ptrMutU32Decl]
    [{ statements := [mkStmt (.storageLive 2)],
       terminator := mkTerm (.call (fnDefOp "witness::callee_return_raw_ptr_to_local")
         [.copy (locPlace 1)] (locPlace 2) (some 1) .continue_),
       isCleanup := false },
     { statements :=
         [mkStmt (.assign (locPlace 0) (.use (.copy (derefPlace 2)))),
          mkStmt (.storageDead 2)],
       terminator := mkTerm .return_,
       isCleanup := false }]

def calleeRetConst42Mir : CapturedMir :=
  singleBlockBody "witness::callee_ret_const42" 0
    [u32Decl]
    [.assign (locPlace 0) (.use (constU32 42))]

def callerRetDestConflictMir (protectBorrow : Bool) : CapturedMir :=
  mkMirBody "witness::caller_ret_dest_conflict" 1
    [u32Decl, u32Decl, refSharedU32Decl]
    [{ statements :=
         [mkStmt (.storageLive 2),
          mkStmt (.assign (locPlace 2) (.ref .shared (locPlace 1)))] ++
         (match protectBorrow with
          | true => [mkStmt (.retag .fnEntry (locPlace 2))]
          | false => []),
       terminator := mkTerm (.call (fnDefOp "witness::callee_ret_const42")
         [] (locPlace 1) (some 1) .continue_),
       isCleanup := false },
     { statements :=
         [mkStmt (.assign (locPlace 0)
            (.use (.copy (match protectBorrow with | true => locPlace 1 | false => derefPlace 2)))),
          mkStmt (.storageDead 2)],
       terminator := mkTerm .return_,
       isCleanup := false }]

def unsafeCellProtectedInteriorMutMir : CapturedMir :=
  singleBlockBody "witness::unsafe_cell_protected_interior_mut" 1
    [u32Decl, unsafeCellU32Decl, refSharedUnsafeCellU32Decl, ptrMutU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (locPlace 2) (.ref .shared (locPlace 1)),
     .retag .fnEntry (locPlace 2),
     .assign (locPlace 3) (.rawPtr .mut (derefField0U32Place 2)),
     .assign (derefPlace 3) (.use (constU32 77)),
     .assign (locPlace 0) (.use (.copy (derefField0U32Place 2))),
     .storageDead 3, .storageDead 2]
    unsafeCellU32Layouts

def unsafeCellProtectedStorageDeadMir : CapturedMir :=
  singleBlockBody "witness::unsafe_cell_protected_storage_dead" 1
    [u32Decl, unsafeCellU32Decl, refSharedUnsafeCellU32Decl, unsafeCellU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (locPlace 3) (.use (.copy (locPlace 1))),
     .assign (locPlace 2) (.ref .shared (locPlace 3)),
     .retag .fnEntry (locPlace 2),
     .assign (locPlace 0) (.use (.copy (derefField0U32Place 2))),
     .storageDead 3]
    unsafeCellU32Layouts

theorem div4_5_fnentry_dealloc_and_unsafecell_end_to_end :
    trustedFaultsUB retagFnEntryLocalDeallocUbMir [] [.scalar ⟨5, 4⟩] = true ∧
    trustedFaultsUB callerOfFnEntryLocalDeallocMir [retagFnEntryLocalDeallocUbMir]
      [.scalar ⟨5, 4⟩] = true ∧
    trustedFaultsUB callerDerefReturnedCalleeRawPtrMir [calleeReturnRawPtrToLocalMir]
      [.scalar ⟨5, 4⟩] = true ∧
    trustedFaultsUB (callerRetDestConflictMir false) [calleeRetConst42Mir]
      [.scalar ⟨5, 4⟩] = true ∧
    trustedFaultsUB (callerRetDestConflictMir true) [calleeRetConst42Mir]
      [.scalar ⟨5, 4⟩] = true ∧
    runTrustedScalar? unsafeCellProtectedInteriorMutMir []
      [.aggregate 0 [.scalar ⟨5, 4⟩]] = .some (77, 4) ∧
    runTrustedScalar? unsafeCellProtectedStorageDeadMir []
      [.aggregate 0 [.scalar ⟨5, 4⟩]] = .some (5, 4) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- 6. `DIV-LM-RAW-OVERWRITE-CHAR-COPY` end-to-end witness and deref-move canary. -/
def rawOverwriteCharLoadMir (code : Nat) (useMove : Bool) : CapturedMir :=
  singleBlockBody "witness::raw_overwrite_char_load" 1
    [charDecl, charDecl, ptrMutU32Decl, charDecl]
    [.storageLive 2, .storageLive 3,
     .assign (locPlace 2) (.rawPtr .mut (locPlace 1)),
     .assign (derefPlace 2) (.use (constU32 code)),
     .assign (locPlace 3) (.use (match useMove with | true => .move (locPlace 1) | false => .copy (locPlace 1))),
     .assign (locPlace 0) (.use (.copy (locPlace 3))),
     .storageDead 3, .storageDead 2]

def rawOverwriteCharDerefMoveMir (code : Nat) : CapturedMir :=
  singleBlockBody "witness::raw_overwrite_char_deref_move" 1
    [charDecl, charDecl, ptrMutU32Decl, ptrMutCharDecl]
    [.storageLive 2, .storageLive 3,
     .assign (locPlace 2) (.rawPtr .mut (locPlace 1)),
     .assign (derefPlace 2) (.use (constU32 code)),
     .assign (locPlace 3) (.rawPtr .mut (locPlace 1)),
     .assign (locPlace 0) (.use (.move (derefPlace 3))),
     .storageDead 3, .storageDead 2]

theorem div6_raw_overwrite_char_end_to_end :
    trustedFaultsUB (rawOverwriteCharLoadMir 0xD800 false) [] [.scalar ⟨0x41, 4⟩] = true ∧
    trustedFaultsUB (rawOverwriteCharLoadMir 0xDFFF false) [] [.scalar ⟨0x41, 4⟩] = true ∧
    trustedFaultsUB (rawOverwriteCharLoadMir 0x110000 false) [] [.scalar ⟨0x41, 4⟩] = true ∧
    trustedFaultsUB (rawOverwriteCharLoadMir 0xD800 true) [] [.scalar ⟨0x41, 4⟩] = true ∧
    trustedFaultsUB (rawOverwriteCharDerefMoveMir 0xD800) [] [.scalar ⟨0x41, 4⟩] = true ∧
    runTrustedScalar? (rawOverwriteCharLoadMir 0x41 false) [] [.scalar ⟨0x41, 4⟩] = .some (0x41, 4) ∧
    runTrustedScalar? (rawOverwriteCharLoadMir 0xD7FF false) [] [.scalar ⟨0x41, 4⟩] = .some (0xD7FF, 4) ∧
    runTrustedScalar? (rawOverwriteCharLoadMir 0xE000 true) [] [.scalar ⟨0x41, 4⟩] = .some (0xE000, 4) ∧
    runTrustedScalar? (rawOverwriteCharLoadMir 0x10FFFF true) [] [.scalar ⟨0x41, 4⟩] = .some (0x10FFFF, 4) ∧
    runTrustedScalar? (rawOverwriteCharDerefMoveMir 0x10FFFF) [] [.scalar ⟨0x41, 4⟩] = .some (0x10FFFF, 4) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- 7. `DIV-LM-D6-OFFSET-DISABLED-TAG` end-to-end 4-witness suite and storage-revival canary. -/
def lm31OffsetDisabledLiveMir : CapturedMir :=
  singleBlockBody "witness::lm31_offset_disabled_live_stride" 1
    [u64Decl, u64Decl, ptrMutU64Decl, ptrMutU64Decl]
    [.storageLive 2, .storageLive 3,
     .assign (locPlace 2) (.rawPtr .mut (locPlace 1)),
     .assign (locPlace 1) (.use (constU64 7)),
     .assign (locPlace 3) (.binaryOp .offset (.move (locPlace 2)) (constUsize 1)),
     .assign (locPlace 0) (.use (constU64 1)),
     .storageDead 3, .storageDead 2]

def lm31OffsetDisabledNegMir : CapturedMir :=
  singleBlockBody "witness::lm31_offset_disabled_live_neg_isize" 1
    [u64Decl, u64Decl, ptrMutU64Decl, ptrMutU64Decl, ptrMutU64Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4,
     .assign (locPlace 2) (.rawPtr .mut (locPlace 1)),
     .assign (locPlace 3) (.binaryOp .offset (.copy (locPlace 2)) (constUsize 1)),
     .assign (locPlace 1) (.use (constU64 7)),
     .assign (locPlace 4) (.binaryOp .offset (.move (locPlace 3)) (constIsize 18446744073709551615)),
     .assign (locPlace 0) (.use (constU64 1)),
     .storageDead 4, .storageDead 3, .storageDead 2]

def lm31OffsetDisabledUsizeMaxMir : CapturedMir :=
  singleBlockBody "witness::lm31_offset_disabled_usize_max" 1
    [u64Decl, u64Decl, ptrMutU64Decl, ptrMutU64Decl]
    [.storageLive 2, .storageLive 3,
     .assign (locPlace 2) (.rawPtr .mut (locPlace 1)),
     .assign (locPlace 1) (.use (constU64 7)),
     .assign (locPlace 3) (.binaryOp .offset (.copy (locPlace 2)) (constUsize 18446744073709551615)),
     .assign (locPlace 0) (.use (constU64 1)),
     .storageDead 3, .storageDead 2]

def lm31OffsetDisabledDeadZeroMir : CapturedMir :=
  singleBlockBody "witness::lm31_offset_disabled_dead_zero_at_8" 1
    [u64Decl, u64Decl, ptrMutU64Decl, ptrMutU64Decl, ptrMutU64Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4,
     .assign (locPlace 2) (.rawPtr .mut (locPlace 1)),
     .assign (locPlace 3) (.binaryOp .offset (.copy (locPlace 2)) (constUsize 1)),
     .storageDead 1,
     .assign (locPlace 4) (.binaryOp .offset (.copy (locPlace 3)) (constUsize 0)),
     .assign (locPlace 0) (.use (constU64 1)),
     .storageDead 4, .storageDead 3, .storageDead 2]

def stmtDivRevivePtrOffsetMir (offCount : Nat) : CapturedMir :=
  singleBlockBody "witness::stmt_div_revive_ptr_offset" 1
    [u64Decl, u64Decl, ptrMutU64Decl, ptrMutU64Decl]
    [.storageLive 2, .storageLive 3,
     .assign (locPlace 1) (.use (constU64 10)),
     .assign (locPlace 2) (.rawPtr .mut (locPlace 1)),
     .storageDead 1,
     .storageLive 1,
     .assign (locPlace 3) (.binaryOp .offset (.copy (locPlace 2)) (constIsize offCount)),
     .assign (locPlace 0) (.use (constU64 0)),
     .storageDead 3, .storageDead 2, .storageDead 1]

theorem div7_offset_disabled_tag_end_to_end :
    runTrustedScalar? lm31OffsetDisabledLiveMir [] [.scalar ⟨42, 8⟩] = .some (1, 8) ∧
    runTrustedScalar? lm31OffsetDisabledNegMir [] [.scalar ⟨42, 8⟩] = .some (1, 8) ∧
    trustedFaultsUB lm31OffsetDisabledUsizeMaxMir [] [.scalar ⟨42, 8⟩] = true ∧
    runTrustedScalar? lm31OffsetDisabledDeadZeroMir [] [.scalar ⟨42, 8⟩] = .some (1, 8) ∧
    trustedFaultsUB (stmtDivRevivePtrOffsetMir 1) [] [.scalar ⟨10, 8⟩] = true ∧
    runTrustedScalar? (stmtDivRevivePtrOffsetMir 0) [] [.scalar ⟨10, 8⟩] = .some (0, 8) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- 8. `DIV-LM-ENUM-SET-DISCR-UNINIT` end-to-end witnesses and borrow/protector canaries. -/
def setDiscrUninitObsMir (variantIdx : Nat) : CapturedMir :=
  singleBlockBody "witness::set_discriminant_uninit_obs" 1
    [isizeDecl, u32Decl, optionU32Decl]
    [.storageLive 2,
     .setDiscriminant (locPlace 2) variantIdx,
     .assign (locPlace 0) (.discriminant (locPlace 2)),
     .storageDead 2]

def setDiscrUninitPayloadMir : CapturedMir :=
  singleBlockBody "witness::set_discriminant_uninit_payload" 1
    [u32Decl, u32Decl, optionU32Decl]
    [.storageLive 2,
     .setDiscriminant (locPlace 2) 1,
     .assign (locPlace 0) (.use (.copy (somePayloadPlace 2))),
     .storageDead 2]

def setDiscrInvalidatesBorrowMir : CapturedMir :=
  singleBlockBody "witness::set_discr_invalidates_borrow" 1
    [isizeDecl, optionU32Decl, refSharedOptionU32Decl]
    [.storageLive 2,
     .assign (locPlace 2) (.ref .shared (locPlace 1)),
     .setDiscriminant (locPlace 1) 1,
     .assign (locPlace 0) (.discriminant (derefPlace 2)),
     .storageDead 2]

def setDiscrProtectedConflictMir (uninitSlot : Bool) : CapturedMir :=
  singleBlockBody "witness::set_discr_protected_conflict" 1
    [isizeDecl, optionU32Decl, refSharedOptionU32Decl, optionU32Decl]
    ([.storageLive 2, .storageLive 3] ++
     (match uninitSlot with
      | true =>
        [.assign (locPlace 2) (.ref .shared (locPlace 3)),
         .retag .fnEntry (locPlace 2),
         .setDiscriminant (locPlace 3) 1,
         .assign (locPlace 0) (.discriminant (locPlace 3))]
      | false =>
        [.assign (locPlace 2) (.ref .shared (locPlace 1)),
         .retag .fnEntry (locPlace 2),
         .setDiscriminant (locPlace 1) 1,
         .assign (locPlace 0) (.discriminant (locPlace 1))]) ++
     [.storageDead 3, .storageDead 2])

theorem div8_set_discriminant_uninit_end_to_end :
    runTrustedScalar? (setDiscrUninitObsMir 1) [] [.scalar ⟨5, 4⟩] = .some (1, 8) ∧
    runTrustedScalar? (setDiscrUninitObsMir 0) [] [.scalar ⟨5, 4⟩] = .some (0, 8) ∧
    trustedFaultsUB setDiscrUninitPayloadMir [] [.scalar ⟨5, 4⟩] = true ∧
    trustedFaultsUB setDiscrInvalidatesBorrowMir [] [.aggregate 0 []] = true ∧
    trustedFaultsUB (setDiscrProtectedConflictMir true) [] [.aggregate 0 []] = true ∧
    trustedFaultsUB (setDiscrProtectedConflictMir false) [] [.aggregate 0 []] = true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## 9. Pass A1 Cross-Frame & Tree Borrows Regression Witnesses -/

def ptrConstCharDecl : LocalDecl :=
  { mutability := .mut, ty := { kind := .rawPtr .not .char, layoutIdx := 0 }, debugName := none }
def refMutOptionU32Decl : LocalDecl :=
  { mutability := .mut,
    ty := { kind := .ref .mut (.adt "core::option::Option" [.uint .u32]), layoutIdx := 0 },
    debugName := none }
def ptrMutOptionU32Decl : LocalDecl :=
  { mutability := .mut,
    ty := { kind := .rawPtr .mut (.adt "core::option::Option" [.uint .u32]), layoutIdx := 0 },
    debugName := none }
def pairU32T : Ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 0 }
def pairU32Decl : LocalDecl := { mutability := .mut, ty := pairU32T, debugName := none }

/-- A1-1: Cross-frame `evalOperand` `.copy` / `.move` deref of raw-overwritten `char` validates
surrogates (`0xD800` -> `.ub`, `0x41` / `0x10FFFF` -> `.ok`). -/
def calleeDerefPtrCharMir (useMove : Bool) : CapturedMir :=
  singleBlockBody "witness::callee_deref_ptr_char" 1
    [charDecl, ptrConstCharDecl]
    [.assign (locPlace 0)
       (.use (match useMove with
              | true => .move (derefPlace 1)
              | false => .copy (derefPlace 1)))]

def callerCrossFrameCharLoadMir (code : Nat) : CapturedMir :=
  mkMirBody "witness::caller_cross_frame_char_load" 1
    [charDecl, charDecl, ptrMutU32Decl, ptrConstCharDecl]
    [{ statements :=
         [mkStmt (.storageLive 2),
          mkStmt (.storageLive 3),
          mkStmt (.assign (locPlace 2) (.rawPtr .mut (locPlace 1))),
          mkStmt (.assign (derefPlace 2) (.use (constU32 code))),
          mkStmt (.assign (locPlace 3) (.rawPtr .not (locPlace 1)))],
       terminator := mkTerm (.call (fnDefOp "witness::callee_deref_ptr_char")
         [.move (locPlace 3)] (locPlace 0) (some 1) .continue_),
       isCleanup := false },
     { statements := [mkStmt (.storageDead 3), mkStmt (.storageDead 2)],
       terminator := mkTerm .return_,
       isCleanup := false }]

theorem a1_cross_frame_char_raw_overwrite_end_to_end :
    trustedFaultsUB (callerCrossFrameCharLoadMir 0xD800) [calleeDerefPtrCharMir false]
      [.scalar ⟨0x41, 4⟩] = true ∧
    trustedFaultsUB (callerCrossFrameCharLoadMir 0xD800) [calleeDerefPtrCharMir true]
      [.scalar ⟨0x41, 4⟩] = true ∧
    runTrustedScalar? (callerCrossFrameCharLoadMir 0x41) [calleeDerefPtrCharMir false]
      [.scalar ⟨0x41, 4⟩] = .some (0x41, 4) ∧
    runTrustedScalar? (callerCrossFrameCharLoadMir 0x10FFFF) [calleeDerefPtrCharMir true]
      [.scalar ⟨0x41, 4⟩] = .some (0x10FFFF, 4) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- A1-2: `writeIntrinsicReturn` & `resumeExternalCall` destination Tree Borrows invalidation and
root-frame `callerLocals` deref write support. -/
def intrinsicDirectWriteInvalidatesBorrowMir : CapturedMir :=
  mkMirBody "witness::intrinsic_direct_write_invalidates_borrow" 1
    [u32Decl, u32Decl, refSharedU32Decl]
    [{ statements :=
         [mkStmt (.storageLive 2),
          mkStmt (.assign (locPlace 2) (.ref .shared (locPlace 1)))],
       terminator := mkTerm (.call
         (fnDefOp "core::intrinsics::wrapping_add" [.uint .u32])
         [.copy (locPlace 1), constU32 1]
         (locPlace 1) (some 1) .continue_),
       isCleanup := false },
     { statements :=
         [mkStmt (.assign (locPlace 0) (.use (.copy (derefPlace 2)))),
          mkStmt (.storageDead 2)],
       terminator := mkTerm .return_,
       isCleanup := false }]

def intrinsicDerefWriteInvalidatesSiblingMir (readStaleShared : Bool) : CapturedMir :=
  mkMirBody "witness::intrinsic_deref_write_invalidates_sibling" 1
    [u32Decl, u32Decl, refMutU32Decl, refSharedU32Decl]
    [{ statements :=
         [mkStmt (.storageLive 2),
          mkStmt (.storageLive 3),
          mkStmt (.assign (locPlace 2) (.ref (.mut false) (locPlace 1))),
          mkStmt (.assign (locPlace 3) (.ref .shared (derefPlace 2)))],
       terminator := mkTerm (.call
         (fnDefOp "core::intrinsics::wrapping_add" [.uint .u32])
         [constU32 10, constU32 20]
         (derefPlace 2) (some 1) .continue_),
       isCleanup := false },
     { statements :=
         [mkStmt (.assign (locPlace 0)
           (.use (.copy (match readStaleShared with
                         | true => derefPlace 3
                         | false => locPlace 1)))),
          mkStmt (.storageDead 3),
          mkStmt (.storageDead 2)],
       terminator := mkTerm .return_,
       isCleanup := false }]

def rootCallerLocalsIntrinsicDerefMir : CapturedMir :=
  mkMirBody "witness::root_caller_locals_intrinsic_deref" 1
    [u32Decl, refMutU32Decl]
    [{ statements := [],
       terminator := mkTerm (.call
         (fnDefOp "core::intrinsics::wrapping_add" [.uint .u32])
         [constU32 10, constU32 20]
         (derefPlace 1) (some 1) .continue_),
       isCleanup := false },
     { statements := [mkStmt (.assign (locPlace 0) (.use (.copy (derefPlace 1))))],
       terminator := mkTerm .return_,
       isCleanup := false }]

def rootCallerLocalsMachineState : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0,
               locals := [.uninit, .init (.ptr { allocId := 9, offsetBytes := 0 } 8)] }
    memory := { emptyMemory with
                borrows := [{ tag := 9, targetLocal := 2, targetProjection := [],
                              perm := .active, targetFrameDepth := 0 }]
                callerLocals := [.dead, .dead, .init (.scalar ⟨5, 4⟩)] } }

theorem a1_intrinsic_and_extcall_dest_borrows_end_to_end :
    trustedFaultsUB intrinsicDirectWriteInvalidatesBorrowMir [] [.scalar ⟨7, 4⟩] = true ∧
    trustedFaultsUB (intrinsicDerefWriteInvalidatesSiblingMir true) [] [.scalar ⟨7, 4⟩] = true ∧
    runTrustedScalar? (intrinsicDerefWriteInvalidatesSiblingMir false) [] [.scalar ⟨7, 4⟩] =
      .some (30, 4) ∧
    runScalarFuel rootCallerLocalsIntrinsicDerefMir 10 rootCallerLocalsMachineState =
      .some (30, 4) ∧
    (match resumeExternalCall
        { frame := { blockIdx := 0, stmtIdx := 0,
                     locals := [.uninit, .init (.scalar ⟨7, 4⟩)] }
          memory := { emptyMemory with
                      borrows := [{ tag := 4, targetLocal := 1, targetProjection := [],
                                    perm := .frozen, targetFrameDepth := 0 }] } }
        [.uninit, .init (.scalar ⟨7, 4⟩)]
        (locPlace 1) 1 .continue_
        (.returned (.scalar ⟨8, 4⟩)
          { emptyMemory with
            borrows := [{ tag := 4, targetLocal := 1, targetProjection := [],
                          perm := .frozen, targetFrameDepth := 0 }] }) with
     | .running s' => s'.memory.borrows.map (·.perm)
     | _ => []) = [.disabled] := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, rfl⟩

/-- A1-3: Cross-frame `SetDiscriminant(*out, variantIdx)` on both initialized and `.uninit` enum
referents. -/
def calleeSetDiscrSomeMir : CapturedMir :=
  singleBlockBody "witness::callee_set_discr_some" 1
    [isizeDecl, refMutOptionU32Decl]
    [.setDiscriminant (derefPlace 1) 1,
     .assign (locPlace 0) (.use (constIsize 0))]

def callerSetDiscrCrossFrameInitMir : CapturedMir :=
  mkMirBody "witness::caller_set_discr_cross_frame_init" 1
    [isizeDecl, optionU32Decl, refMutOptionU32Decl]
    [{ statements :=
         [mkStmt (.storageLive 2),
          mkStmt (.assign (locPlace 2) (.ref (.mut false) (locPlace 1)))],
       terminator := mkTerm (.call (fnDefOp "witness::callee_set_discr_some")
         [.move (locPlace 2)] { local_ := 0, projection := [] } (some 1) .continue_),
       isCleanup := false },
     { statements :=
         [mkStmt (.assign (locPlace 0) (.discriminant (locPlace 1))),
          mkStmt (.storageDead 2)],
       terminator := mkTerm .return_,
       isCleanup := false }]

def calleeSetDiscrPtrNoneMir : CapturedMir :=
  singleBlockBody "witness::callee_set_discr_ptr_none" 1
    [isizeDecl, ptrMutOptionU32Decl]
    [.setDiscriminant (derefPlace 1) 0,
     .assign (locPlace 0) (.use (constIsize 9))]

def callerSetDiscrCrossFrameUninitMir : CapturedMir :=
  mkMirBody "witness::caller_set_discr_cross_frame_uninit" 1
    [isizeDecl, u32Decl, optionU32Decl, ptrMutOptionU32Decl]
    [{ statements :=
         [mkStmt (.storageLive 2),
          mkStmt (.storageLive 3),
          mkStmt (.assign (locPlace 3) (.rawPtr .mut (locPlace 2)))],
       terminator := mkTerm (.call (fnDefOp "witness::callee_set_discr_ptr_none")
         [.move (locPlace 3)] (locPlace 0) (some 1) .continue_),
       isCleanup := false },
     { statements :=
         [mkStmt (.assign (locPlace 0) (.discriminant (locPlace 2))),
          mkStmt (.storageDead 3),
          mkStmt (.storageDead 2)],
       terminator := mkTerm .return_,
       isCleanup := false }]

theorem a1_cross_frame_set_discriminant_deref_end_to_end :
    runTrustedScalar? callerSetDiscrCrossFrameInitMir [calleeSetDiscrSomeMir]
      [.aggregate 0 [.scalar ⟨0, 4⟩]] = .some (1, 8) ∧
    runTrustedScalar? callerSetDiscrCrossFrameUninitMir [calleeSetDiscrPtrNoneMir]
      [.scalar ⟨0, 4⟩] = .some (0, 8) := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- A1-4: Cross-frame `copy_nonoverlapping` preserves parent `&mut` tag on child `*mut` write and
preserves sibling field borrow `&pair.1` on `copy_nonoverlapping` into `&raw mut pair.0`. -/
def calleeCopyU32Mir : CapturedMir :=
  singleBlockBody "witness::callee_copy_u32" 2
    [u32Decl, ptrConstU32Decl, ptrMutU32Decl]
    [.intrinsic (.copyNonOverlapping (.copy (locPlace 1)) (.copy (locPlace 2)) (constUsize 1)),
     .assign (locPlace 0) (.use (constU32 0))]

def callerChildPtrCopyPreservesParentMir : CapturedMir :=
  mkMirBody "witness::caller_child_ptr_copy_preserves_parent" 1
    [u32Decl, u32Decl, u32Decl, refMutU32Decl, ptrMutU32Decl, ptrConstU32Decl]
    [{ statements :=
         [mkStmt (.storageLive 2),
          mkStmt (.storageLive 3),
          mkStmt (.storageLive 4),
          mkStmt (.storageLive 5),
          mkStmt (.assign (locPlace 2) (.use (constU32 99))),
          mkStmt (.assign (locPlace 3) (.ref (.mut false) (locPlace 1))),
          mkStmt (.assign (locPlace 4) (.rawPtr .mut (derefPlace 3))),
          mkStmt (.assign (locPlace 5) (.rawPtr .not (locPlace 2)))],
       terminator := mkTerm (.call (fnDefOp "witness::callee_copy_u32")
         [.move (locPlace 5), .move (locPlace 4)] (locPlace 0) (some 1) .continue_),
       isCleanup := false },
     { statements :=
         [mkStmt (.assign (locPlace 0) (.use (.copy (derefPlace 3)))),
          mkStmt (.storageDead 5),
          mkStmt (.storageDead 4),
          mkStmt (.storageDead 3),
          mkStmt (.storageDead 2)],
       terminator := mkTerm .return_,
       isCleanup := false }]

def callerFieldCopyPreservesSiblingBorrowMir : CapturedMir :=
  mkMirBody "witness::caller_field_copy_preserves_sibling_borrow" 1
    [u32Decl, pairU32Decl, u32Decl, refSharedU32Decl, ptrMutU32Decl, ptrConstU32Decl]
    [{ statements :=
         [mkStmt (.storageLive 2),
          mkStmt (.storageLive 3),
          mkStmt (.storageLive 4),
          mkStmt (.storageLive 5),
          mkStmt (.assign (locPlace 2) (.use (constU32 88))),
          mkStmt (.assign (locPlace 3) (.ref .shared { local_ := 1, projection := [.field 1 u32T] })),
          mkStmt (.assign (locPlace 4) (.rawPtr .mut { local_ := 1, projection := [.field 0 u32T] })),
          mkStmt (.assign (locPlace 5) (.rawPtr .not (locPlace 2)))],
       terminator := mkTerm (.call (fnDefOp "witness::callee_copy_u32")
         [.move (locPlace 5), .move (locPlace 4)] (locPlace 0) (some 1) .continue_),
       isCleanup := false },
     { statements :=
         [mkStmt (.assign (locPlace 0) (.use (.copy (derefPlace 3)))),
          mkStmt (.storageDead 5),
          mkStmt (.storageDead 4),
          mkStmt (.storageDead 3),
          mkStmt (.storageDead 2)],
       terminator := mkTerm .return_,
       isCleanup := false }]

theorem a1_foreign_copy_nonoverlapping_tree_borrows_end_to_end :
    runTrustedScalar? callerChildPtrCopyPreservesParentMir [calleeCopyU32Mir]
      [.scalar ⟨11, 4⟩] = .some (99, 4) ∧
    runTrustedScalar? callerFieldCopyPreservesSiblingBorrowMir [calleeCopyU32Mir]
      [.aggregate 0 [.scalar ⟨11, 4⟩, .scalar ⟨77, 4⟩]] = .some (77, 4) := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-! ## 10. Pass B2 Cross-Frame Layout, Alignment, Protector & Byte-Offset Regression Witnesses -/

def arr4U32T : Ty := { kind := .array (.uint .u32) 4, layoutIdx := 0 }
def arr4U32Decl : LocalDecl := { mutability := .mut, ty := arr4U32T, debugName := none }
def ptrMutArr4U32Decl : LocalDecl :=
  { mutability := .mut, ty := { kind := .rawPtr .mut (.array (.uint .u32) 4), layoutIdx := 0 },
    debugName := none }
def sliceU32T : Ty := { kind := .slice (.uint .u32), layoutIdx := 0 }
def ptrMutSliceU32Decl : LocalDecl :=
  { mutability := .mut, ty := { kind := .rawPtr .mut (.slice (.uint .u32)), layoutIdx := 0 },
    debugName := none }

/-- B2-1: `evalRvalueRawPtr` `fallbackByByteOffset` threads `callStack := mem.callStack` into
`boundMem`, so reborrowing a subslice from an offset pointer into an `.uninit` caller allocation
uses the caller frame's allocation bound (`16` bytes) rather than colliding with the callee's `.dead`
local of the same index (`0` bytes), while still rejecting out-of-bounds subslices (`4 + 16 > 16`). -/
def b2CallerUninitArr4Frame : SavedCallerFrame := {
  callerBody := mkMirBody "witness::b2_caller_uninit_arr4" 0 [u32Decl, arr4U32Decl] []
  frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] }
  destination := locPlace 0
}

def b2CalleeDeadLocal1Decls : List LocalDecl :=
  [ptrMutU32Decl, arr4U32Decl, ptrMutArr4U32Decl]

def b2CalleeDeadLocal1Locals (offBytes : Nat) : List LocalSlot :=
  [.uninit, .dead, .init (.ptr { allocId := 12, offsetBytes := offBytes } 8)]

def b2CallerArr4BorrowEntry : BorrowEntry :=
  { tag := 12, targetLocal := 1, targetProjection := [], perm := .active, targetFrameDepth := 0 }

def b2RawPtrSubsliceMem : Memory :=
  { emptyMemory with
    borrows := [b2CallerArr4BorrowEntry]
    callStack := [b2CallerUninitArr4Frame] }

theorem b2_1_raw_ptr_fallback_byte_offset_cross_frame :
    (match evalRvalue (b2CalleeDeadLocal1Locals 4)
        (.rawPtr .mut { local_ := 2, projection := [.deref, .constantIndex 1 4 false] })
        b2RawPtrSubsliceMem b2CalleeDeadLocal1Decls emptyLayoutTable with
     | .ok (.ptr p 8) _ _ => some p.offsetBytes
     | _ => none) = some 8 ∧
    evalRvalue (b2CalleeDeadLocal1Locals 16)
      (.rawPtr .mut { local_ := 2, projection := [.deref, .constantIndex 1 4 false] })
      b2RawPtrSubsliceMem b2CalleeDeadLocal1Decls emptyLayoutTable = .ub := by
  refine ⟨rfl, rfl⟩

/-- B2-2: `evalCallerPlaceWrite` passes `callerLocals` and `callStack` to
`resolveDerefWriteFullProj`, so writing through an element-offset pointer (`offsetBytes = 4` on
`targetProjection = [.constantIndex 0 0 false]`) into an intermediate caller frame at
`targetFrameDepth = 1` resolves to `[.constantIndex 1 0 false]` (disjoint from a protected sibling
borrow at `[.constantIndex 0 0 false]`) instead of failing to look up the caller frame and falsely
faulting `.ub`. -/
def b2RootDummyFrame : SavedCallerFrame := {
  callerBody := callerBody
  frame := { blockIdx := 0, stmtIdx := 0, locals := [.init (.scalar ⟨0, 4⟩)] }
  destination := locPlace 0
}

def b2MidArrLocals : List LocalSlot :=
  [.init (.scalar ⟨0, 4⟩), .init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩])]

def b2MidCallerFrame : SavedCallerFrame := {
  callerBody := callerBody
  frame := { blockIdx := 0, stmtIdx := 0, locals := b2MidArrLocals }
  destination := locPlace 0
}

def b2ProtectedElem0Borrow : BorrowEntry :=
  { tag := 20, targetLocal := 1, targetProjection := [.constantIndex 0 0 false],
    perm := .frozen, protector := .some 7, targetFrameDepth := 1 }

def b2ElemOffsetWriteBorrow : BorrowEntry :=
  { tag := 21, targetLocal := 1, targetProjection := [.constantIndex 0 0 false],
    perm := .active, targetFrameDepth := 1 }

def b2LeafFrameLocals (offBytes : Nat) : List LocalSlot :=
  [.uninit, .init (.ptr { allocId := 21, offsetBytes := offBytes } 8)]

theorem b2_2_eval_caller_place_write_protector_depth_gt_zero :
    evalCallerPlaceWrite
      (b2LeafFrameLocals 4)
      b2MidArrLocals
      [b2ElemOffsetWriteBorrow, b2ProtectedElem0Borrow]
      (derefPlace 1)
      (.scalar ⟨99, 4⟩)
      [7]
      []
      emptyLayoutTable
      [b2MidCallerFrame, b2RootDummyFrame] =
    .ok [.init (.scalar ⟨0, 4⟩), .init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨99, 4⟩])] ∧
    evalCallerPlaceWrite
      (b2LeafFrameLocals 0)
      b2MidArrLocals
      [b2ElemOffsetWriteBorrow, b2ProtectedElem0Borrow]
      (derefPlace 1)
      (.scalar ⟨99, 4⟩)
      [7]
      []
      emptyLayoutTable
      [b2MidCallerFrame, b2RootDummyFrame] = .ub := by
  refine ⟨rfl, rfl⟩

/-- B2-3: Cross-frame per-body `LayoutTable` isolation (`targetLayouts`) across
`evalStackThinPtrTypedDerefRead`, `writeStackThinPtrTypedDeref`, `checkTargetPlaceAlign`,
`borrowPlaceByteOffset?`, and slice fat-pointer writes/reborrows.
In `b2CallerCustomPairMir`, `layoutIdx = 0` is an 8-byte `CustomPair` struct with field offsets
`[0, 4]`; in `b2CalleeReadWriteOffsetPtrMir`, `layoutIdx = 0` is a 4-byte primitive `u32`. -/
def customPairT : Ty := { kind := .adt "witness::CustomPair" [], layoutIdx := 0 }
def customPairDecl : LocalDecl := { mutability := .mut, ty := customPairT, debugName := none }
def ptrMutCustomPairDecl : LocalDecl :=
  { mutability := .mut, ty := { kind := .rawPtr .mut customPairT.kind, layoutIdx := 0 },
    debugName := none }

def u32PrimLayout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .primitive, variants := .single 0, isUninhabited := false, fieldLayouts := [] }

def customPairLayout : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }] [0, 1],
    variants := .single 0, isUninhabited := false, fieldLayouts := [1, 1] }

def b2CallerPairLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [customPairLayout, u32PrimLayout] }

def b2CalleeU32OnlyLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [u32PrimLayout] }

def b2CalleeReadWriteOffsetPtrMir : CapturedMir :=
  singleBlockBody "witness::b2_callee_rw_offset_ptr" 1
    [u32Decl, ptrMutU32Decl, u32Decl]
    [.storageLive 2,
     .assign (locPlace 2) (.use (.copy (derefPlace 1))),
     .assign (derefPlace 1) (.use (constU32 77)),
     .assign (locPlace 0) (.use (.copy (locPlace 2))),
     .storageDead 2]
    b2CalleeU32OnlyLayouts

def b2CallerCustomPairMir : CapturedMir :=
  { (mkMirBody "witness::b2_caller_custom_pair" 1
      [u32Decl, customPairDecl, ptrMutCustomPairDecl, ptrMutU32Decl, ptrMutU32Decl, u32Decl]
      [{ statements :=
           [mkStmt (.storageLive 2),
            mkStmt (.storageLive 3),
            mkStmt (.storageLive 4),
            mkStmt (.storageLive 5),
            mkStmt (.assign (locPlace 2) (.rawPtr .mut (locPlace 1))),
            mkStmt (.assign (locPlace 3)
              (.cast .ptrToPtr (.copy (locPlace 2)) { kind := .rawPtr .mut (.uint .u32), layoutIdx := 1 })),
            mkStmt (.assign (locPlace 4)
              (.binaryOp .offset (.copy (locPlace 3)) (constUsize 1)))],
         terminator := mkTerm (.call (fnDefOp "witness::b2_callee_rw_offset_ptr")
           [.move (locPlace 4)] (locPlace 5) (some 1) .continue_),
         isCleanup := false },
       { statements :=
           [mkStmt (.assign (locPlace 0)
              (.binaryOp .add (.copy (locPlace 5))
                (.copy { local_ := 1, projection := [.field 1 { kind := .uint .u32, layoutIdx := 1 }] }))),
            mkStmt (.storageDead 5),
            mkStmt (.storageDead 4),
            mkStmt (.storageDead 3),
            mkStmt (.storageDead 2)],
         terminator := mkTerm .return_,
         isCleanup := false }]) with
    layouts := b2CallerPairLayouts }

def packedWrapLayout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .arbitrary [{ bytes := 0 }] [0],
    variants := .single 0, isUninhabited := false, fieldLayouts := [1] }

def b2CallerPackedLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [packedWrapLayout, u32PrimLayout] }

def packedWrapT : Ty := { kind := .adt "witness::PackedWrap" [], layoutIdx := 0 }
def packedWrapDecl : LocalDecl := { mutability := .mut, ty := packedWrapT, debugName := none }

def b2CallerPackedFrame : SavedCallerFrame := {
  callerBody :=
    { (mkMirBody "witness::b2_caller_packed" 0 [u32Decl, packedWrapDecl] []) with
      layouts := b2CallerPackedLayouts }
  frame := { blockIdx := 0, stmtIdx := 0,
             locals := [.init (.scalar ⟨0, 4⟩), .init (.aggregate 0 [.scalar ⟨55, 4⟩])] }
  destination := locPlace 0
}

def b2PackedBorrowEntry : BorrowEntry :=
  { tag := 30, targetLocal := 1, targetProjection := [], perm := .active, targetFrameDepth := 0 }

theorem b2_3_cross_frame_target_layouts_and_slice_align_end_to_end :
    runTrustedScalar? b2CallerCustomPairMir [b2CalleeReadWriteOffsetPtrMir]
      [.aggregate 0 [.scalar ⟨11, 4⟩, .scalar ⟨22, 4⟩]] = .some (99, 4) ∧
    borrowPlaceByteOffset?
      [.uninit] [] [u32Decl] b2CalleeU32OnlyLayouts
      { b2PackedBorrowEntry with
        targetProjection := [.field 1 { kind := .uint .u32, layoutIdx := 1 }] }
      [{ b2CallerPackedFrame with
         callerBody := { b2CallerPackedFrame.callerBody with
                         localDecls := [u32Decl, customPairDecl]
                         layouts := b2CallerPairLayouts }
         frame := { blockIdx := 0, stmtIdx := 0,
                    locals := [.init (.scalar ⟨0, 4⟩),
                               .init (.aggregate 0 [.scalar ⟨11, 4⟩, .scalar ⟨22, 4⟩])] } }] =
      .some 4 ∧
    writeCallerPlaceValue
      [.uninit,
       .init (.aggregate 0 [.ptr { allocId := 30, offsetBytes := 0 } 8, .scalar ⟨1, 8⟩])]
      [.init (.scalar ⟨0, 4⟩), .init (.aggregate 0 [.scalar ⟨55, 4⟩])]
      [b2PackedBorrowEntry]
      { local_ := 1, projection := [.deref, .constantIndex 0 1 false] }
      (.scalar ⟨99, 4⟩)
      [u32Decl,
       { mutability := .mut, ty := { kind := .ref .mut (.slice (.uint .u32)), layoutIdx := 0 },
         debugName := none }]
      b2CalleeU32OnlyLayouts
      [b2CallerPackedFrame] = .ub := by
  refine ⟨by decide +kernel, rfl, rfl⟩

end Anneal.TcbCorrespondenceDiv8Tests
