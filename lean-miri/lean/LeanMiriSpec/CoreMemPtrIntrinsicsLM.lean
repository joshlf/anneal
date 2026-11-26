/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import LeanMiriSpec.NullaryAndPtrCoercionLM

/-!
# Episode 2 Dual-Authority Correspondence (`LeanMiriSpec` Authority):
# the 8 core memory & pointer intrinsics vs. unmodified vendored `Miri.Interpreter.Intrinsics`

Executes the frozen cross-root `CapturedMir` fixtures of
`MiniRustSpec.CoreMemPtrIntrinsicsMR` (shared verbatim, locked by `Eq.refl` in
`tests/mir/CoreMemPtrIntrinsicsTests.lean`) through the UNMODIFIED vendored
`Miri.Interpreter.Step.step` -> `ControlFlow.evalTerminator` ->
`Call.evalCallTerminator` -> `Intrinsics.eval` pipeline, whose arms for
`"copy"` (`copyWith`, `Intrinsics.lean:143-161`), `"compare_bytes"`
(`compareBytes`, `:174-187`), `"raw_eq"` (`rawEq`, `:188-197`),
`"typed_swap_nonoverlapping"` (`typedSwap`, `:199-214`), `"ptr_offset_from"` /
`"ptr_offset_from_unsigned"` (`pointerOffsetFrom`, `:215-274`), `"black_box"`
(`:441`), and `"ptr_mask"` (`:504-508`) are the reference semantics.

The machine-dependent leaves of the vendored `IntrinsicHooks` that
`annealIntrinsicHooks` leaves fail-closed (`readBytesStripProvenance`,
`tryAllocId`, `checkSignedAccess`, `copyOp`, `derefPointer`, `placeToOp`,
`placePointer`, `allocateStack`, `deallocateStack`, `validatePlace`) are
instantiated here (`cmIntrinsicHooks`) over Anneal's single-threaded machine
with the vendored memory primitives (`Miri.Memory.checkAndDerefPtr`,
`Allocation.getBytesStripProvenance`, `Allocation.tryNew`, `annealMemCopy`,
`annealReadImmediate`, `annealWriteImmediate`); in `treeBorrows` mode the copy
and byte-read leaves first apply the vendored Tree Borrows transitions
(`npApplyTreeBorrowsReadAt`, `npApplyTreeBorrowsWriteAt`).

Also witnesses the two deliberate stricter-than-`lean-miri` library-UB deltas
of the Trusted semantics (`compare_bytes` with a null pointer at `bytes = 0`
and `typed_swap_nonoverlapping` with a null pointer at a ZST `T`, which
`lean-miri` accepts because zero-sized accesses skip every check) and the
agreement on `copy` with a null pointer at `count = 0`.

Strict import isolation: this module NEVER imports `MiniRustSpec.*` (verified
by the trailing `#assert_core_mem_ptr_lm_audit`).
-/

namespace LeanMiriSpec.CoreMemPtrIntrinsicsLM

set_option Elab.async false
set_option linter.unusedSimpArgs false

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence
open LeanMiriSpec.UnwindSetDiscrAndFnPtrLM
open LeanMiriSpec.DropBinderAndSubtypeLM
open LeanMiriSpec.NullaryAndPtrCoercionLM

/-! ## §0. Frozen Cross-Root Types, Allocations, and `CapturedMir` Fixtures

Shared verbatim with `MiniRustSpec.CoreMemPtrIntrinsicsMR`. -/

@[reducible] def cmIsizeTy : MirAst.Ty := { kind := .int .isize, layoutIdx := 0 }
@[reducible] def cmRawConstU8Ty : MirAst.Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 0 }
@[reducible] def cmRawConstU16Ty : MirAst.Ty := { kind := .rawPtr .not (.uint .u16), layoutIdx := 0 }
@[reducible] def cmRawMutU16Ty : MirAst.Ty := { kind := .rawPtr .mut (.uint .u16), layoutIdx := 0 }
@[reducible] def cmRefU32Ty : MirAst.Ty := { kind := .ref .not (.uint .u32), layoutIdx := 0 }
@[reducible] def cmRefUnitTy : MirAst.Ty := { kind := .ref .not (.tuple []), layoutIdx := 0 }

/-- The function-item operand `core::intrinsics::<path>::<tys>`. -/
def cmIntrinsicOp (path : String) (tys : List RigidTy) : Operand :=
  .constant { ty := { kind := .fnDef path tys, layoutIdx := 0 }, val := .zeroSized }

/-- A `usize` constant operand. -/
def cmUsizeConst (n : Nat) : Operand := .constant { ty := usizeMirTy, val := .scalar (.int ⟨n, 8⟩) }

/-- A mutable captured global allocation with id `aid`. -/
def cmGlobal (aid : Nat) (bytes : List (Option UInt8)) (align : Nat := 4) : CapturedAllocation :=
  { allocId := aid, bytes, relocations := [], align := ⟨align⟩, mutability := .mut }

/-- Little-endian `u32` bytes. -/
def cmU32Bytes (n : Nat) : List (Option UInt8) :=
  [some (UInt8.ofNat n), some (UInt8.ofNat (n / 256)), some (UInt8.ofNat (n / 65536)),
   some (UInt8.ofNat (n / 16777216))]

/-- A one-call body: `bb0: dest = call f(args) -> bb1; bb1: stmts; return`. -/
def cmCallBody (name : String) (decls : List MirAst.LocalDecl) (argCount : Nat)
    (f : Operand) (args : List Operand) (dest : Nat) (after : List MirAst.Statement)
    (allocs : List CapturedAllocation) : CapturedMir :=
  { mkMirBody name decls argCount
      [mkBb [] (.call f args (locPlace dest) (some 1) .continue_),
       mkBb after .return_] with
    allocations := allocs }

-- 1. copy
/-- `copy::<u32>(_1, _2, 1); _0 = *_2` over globals `100 = 42u32`, `101`. -/
def cmCopyMir : CapturedMir :=
  cmCallBody "cm::copy_u32"
    [mkDecl u32MirTy, mkDecl rawConstU32MirTy, mkDecl rawMutU32MirTy, mkDecl unitMirTy] 2
    (cmIntrinsicOp "core::intrinsics::copy" [.uint .u32])
    [.copy (locPlace 1), .copy (locPlace 2), cmUsizeConst 1] 3
    [mkSt (.assign (locPlace 0) (.use (.copy (locPlace 2 [.deref]))))]
    [cmGlobal 100 (cmU32Bytes 42), cmGlobal 101 (cmU32Bytes 0x04030201)]

/-- Overlapping `memmove`: `copy::<u16>(_1 = &G[0], _2 = &G[2], 2); _0 = *(_3 = &G[4] as *const u32)`
over `G = [1, 2, 3, 4, 5, 6, 7, 8]`. A snapshot copy leaves `[1, 2, 1, 2, 3, 4, 7, 8]`. -/
def cmCopyOverlapMir : CapturedMir :=
  cmCallBody "cm::copy_overlap_u16"
    [mkDecl u32MirTy, mkDecl cmRawConstU16Ty, mkDecl cmRawMutU16Ty, mkDecl rawConstU32MirTy,
     mkDecl unitMirTy] 3
    (cmIntrinsicOp "core::intrinsics::copy" [.uint .u16])
    [.copy (locPlace 1), .copy (locPlace 2), cmUsizeConst 2] 4
    [mkSt (.assign (locPlace 0) (.use (.copy (locPlace 3 [.deref]))))]
    [cmGlobal 100 [some 1, some 2, some 3, some 4, some 5, some 6, some 7, some 8]]

/-- Mode-sensitive copy: the destination `_2` points (through borrow tag `2`)
into the stack local `_3`, on which a sibling borrow (tag `1`) carries an active
protector in `protectedTB` mode; `_0 = _3` afterwards. -/
def cmCopyModeMir : CapturedMir :=
  cmCallBody "cm::copy_mode"
    [mkDecl u32MirTy, mkDecl rawConstU32MirTy, mkDecl rawMutU32MirTy, mkDecl u32MirTy,
     mkDecl unitMirTy] 2
    (cmIntrinsicOp "core::intrinsics::copy" [.uint .u32])
    [.copy (locPlace 1), .copy (locPlace 2), cmUsizeConst 1] 4
    [mkSt (.assign (locPlace 0) (.use (.copy (locPlace 3))))]
    [cmGlobal 100 (cmU32Bytes 42)]

-- 2. compare_bytes
/-- `compare_bytes(_1, _2, 3)` over `100 = [1,2,3]`, `101 = [1,2,4]`,
`102 = [2,0,uninit]`, `103 = [1,2,3]`. -/
def cmCmpBytes3Mir : CapturedMir :=
  cmCallBody "cm::compare_bytes_3"
    [mkDecl i32MirTy, mkDecl cmRawConstU8Ty, mkDecl cmRawConstU8Ty] 2
    (cmIntrinsicOp "core::intrinsics::compare_bytes" [])
    [.copy (locPlace 1), .copy (locPlace 2), cmUsizeConst 3] 0 []
    [cmGlobal 100 [some 1, some 2, some 3] 1, cmGlobal 101 [some 1, some 2, some 4] 1,
     cmGlobal 102 [some 2, some 0, none] 1, cmGlobal 103 [some 1, some 2, some 3] 1]

/-- `compare_bytes(_1, _2, 1)` over `100 = [0x80]`, `101 = [0x01]` (unsigned). -/
def cmCmpBytes1Mir : CapturedMir :=
  cmCallBody "cm::compare_bytes_1"
    [mkDecl i32MirTy, mkDecl cmRawConstU8Ty, mkDecl cmRawConstU8Ty] 2
    (cmIntrinsicOp "core::intrinsics::compare_bytes" [])
    [.copy (locPlace 1), .copy (locPlace 2), cmUsizeConst 1] 0 []
    [cmGlobal 100 [some 0x80] 1, cmGlobal 101 [some 0x01] 1]

-- 3. raw_eq
/-- `raw_eq::<u32>(_1, _2)` over `100 = 7`, `101 = 7`, `102 = 9`,
`103 = [7, uninit, 0, 0]`. -/
def cmRawEqU32Mir : CapturedMir :=
  cmCallBody "cm::raw_eq_u32"
    [mkDecl boolMirTy, mkDecl cmRefU32Ty, mkDecl cmRefU32Ty] 2
    (cmIntrinsicOp "core::intrinsics::raw_eq" [.uint .u32])
    [.copy (locPlace 1), .copy (locPlace 2)] 0 []
    [cmGlobal 100 (cmU32Bytes 7), cmGlobal 101 (cmU32Bytes 7), cmGlobal 102 (cmU32Bytes 9),
     cmGlobal 103 [some 7, none, some 0, some 0]]

/-- `raw_eq::<()>(_1, _2)` (ZST: `true` for aligned non-null pointers). -/
def cmRawEqZstMir : CapturedMir :=
  cmCallBody "cm::raw_eq_zst"
    [mkDecl boolMirTy, mkDecl cmRefUnitTy, mkDecl cmRefUnitTy] 2
    (cmIntrinsicOp "core::intrinsics::raw_eq" [.tuple []])
    [.copy (locPlace 1), .copy (locPlace 2)] 0 [] []

-- 4. typed_swap_nonoverlapping
/-- `typed_swap_nonoverlapping::<u32>(_1, _2); _0 = *_1` over `100 = 7`, `101 = 9`. -/
def cmSwapReadXMir : CapturedMir :=
  cmCallBody "cm::typed_swap_read_x"
    [mkDecl u32MirTy, mkDecl rawMutU32MirTy, mkDecl rawMutU32MirTy, mkDecl unitMirTy] 2
    (cmIntrinsicOp "core::intrinsics::typed_swap_nonoverlapping" [.uint .u32])
    [.copy (locPlace 1), .copy (locPlace 2)] 3
    [mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1 [.deref]))))]
    [cmGlobal 100 (cmU32Bytes 7), cmGlobal 101 (cmU32Bytes 9)]

/-- `typed_swap_nonoverlapping::<u32>(_1, _2); _0 = *_2` over `100 = 7`, `101 = 9`. -/
def cmSwapReadYMir : CapturedMir :=
  cmCallBody "cm::typed_swap_read_y"
    [mkDecl u32MirTy, mkDecl rawMutU32MirTy, mkDecl rawMutU32MirTy, mkDecl unitMirTy] 2
    (cmIntrinsicOp "core::intrinsics::typed_swap_nonoverlapping" [.uint .u32])
    [.copy (locPlace 1), .copy (locPlace 2)] 3
    [mkSt (.assign (locPlace 0) (.use (.copy (locPlace 2 [.deref]))))]
    [cmGlobal 100 (cmU32Bytes 7), cmGlobal 101 (cmU32Bytes 9)]

/-- Disjoint elements of ONE allocation: `100 = [5u32, 6u32]`, swap `&G[0]` and
`&G[4]`, `_0 = *_1`. -/
def cmSwapSameAllocMir : CapturedMir :=
  cmCallBody "cm::typed_swap_same_alloc"
    [mkDecl u32MirTy, mkDecl rawMutU32MirTy, mkDecl rawMutU32MirTy, mkDecl unitMirTy] 2
    (cmIntrinsicOp "core::intrinsics::typed_swap_nonoverlapping" [.uint .u32])
    [.copy (locPlace 1), .copy (locPlace 2)] 3
    [mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1 [.deref]))))]
    [cmGlobal 100 (cmU32Bytes 5 ++ cmU32Bytes 6)]

/-- Mode-sensitive `typed_swap_nonoverlapping`: `_1` points to global `100 = 7u32`
and `_2` points (through borrow tag `2`) to stack local `_3 = 9u32`, on which a
sibling `.frozen` borrow (tag `1`) carries an active protector in `protectedTB`
mode; `_0 = *_1` afterwards (`9` in `basic`, `.ub` in `protectedTB`). -/
def cmSwapModeMir : CapturedMir :=
  cmCallBody "cm::typed_swap_mode"
    [mkDecl u32MirTy, mkDecl rawMutU32MirTy, mkDecl rawMutU32MirTy, mkDecl u32MirTy,
     mkDecl unitMirTy] 2
    (cmIntrinsicOp "core::intrinsics::typed_swap_nonoverlapping" [.uint .u32])
    [.copy (locPlace 1), .copy (locPlace 2)] 4
    [mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1 [.deref]))))]
    [cmGlobal 100 (cmU32Bytes 7)]

-- 5./6. ptr_offset_from[_unsigned]
/-- `ptr_offset_from::<u32>(_1, _2)` over two 16-byte globals `100`, `101`. -/
def cmPofMir : CapturedMir :=
  cmCallBody "cm::ptr_offset_from_u32"
    [mkDecl cmIsizeTy, mkDecl rawConstU32MirTy, mkDecl rawConstU32MirTy] 2
    (cmIntrinsicOp "core::intrinsics::ptr_offset_from" [.uint .u32])
    [.copy (locPlace 1), .copy (locPlace 2)] 0 []
    [cmGlobal 100 (List.replicate 16 (some 0)), cmGlobal 101 (List.replicate 16 (some 0))]

/-- `ptr_offset_from_unsigned::<u32>(_1, _2)` over two 16-byte globals. -/
def cmPofuMir : CapturedMir :=
  cmCallBody "cm::ptr_offset_from_unsigned_u32"
    [mkDecl usizeMirTy, mkDecl rawConstU32MirTy, mkDecl rawConstU32MirTy] 2
    (cmIntrinsicOp "core::intrinsics::ptr_offset_from_unsigned" [.uint .u32])
    [.copy (locPlace 1), .copy (locPlace 2)] 0 []
    [cmGlobal 100 (List.replicate 16 (some 0)), cmGlobal 101 (List.replicate 16 (some 0))]

-- 7. ptr_mask
/-- `ptr_mask::<u32>(_1, mask)` over a 16-byte, 16-aligned global `100`. -/
def cmMaskMir (name : String) (mask : Nat) : CapturedMir :=
  cmCallBody name
    [mkDecl rawConstU32MirTy, mkDecl rawConstU32MirTy] 1
    (cmIntrinsicOp "core::intrinsics::ptr_mask" [.uint .u32])
    [.copy (locPlace 1), cmUsizeConst mask] 0 []
    [cmGlobal 100 (List.replicate 16 (some 0)) 16]

/-- `!7` (clears the low 3 address bits; base-address invariant for 16-aligned allocations). -/
def cmMaskAlign8Mir : CapturedMir := cmMaskMir "cm::ptr_mask_not7" (2 ^ 64 - 8)
/-- The identity mask `usize::MAX`. -/
def cmMaskIdentityMir : CapturedMir := cmMaskMir "cm::ptr_mask_identity" (2 ^ 64 - 1)
/-- `!3`. -/
def cmMaskAlign4Mir : CapturedMir := cmMaskMir "cm::ptr_mask_not3" (2 ^ 64 - 4)

-- 8. black_box
/-- `black_box::<u32>(_1)`. -/
def cmBlackBoxU32Mir : CapturedMir :=
  cmCallBody "cm::black_box_u32" [mkDecl u32MirTy, mkDecl u32MirTy] 1
    (cmIntrinsicOp "core::intrinsics::black_box" [.uint .u32]) [.copy (locPlace 1)] 0 [] []

/-- `black_box::<*const u32>(_1)` (provenance identity). -/
def cmBlackBoxPtrMir : CapturedMir :=
  cmCallBody "cm::black_box_ptr" [mkDecl rawConstU32MirTy, mkDecl rawConstU32MirTy] 1
    (cmIntrinsicOp "core::intrinsics::black_box" [.rawPtr .not (.uint .u32)]) [.copy (locPlace 1)] 0 []
    [cmGlobal 100 (List.replicate 16 (some 0))]

/-- `black_box::<bool>(_1)`. -/
def cmBlackBoxBoolMir : CapturedMir :=
  cmCallBody "cm::black_box_bool" [mkDecl boolMirTy, mkDecl boolMirTy] 1
    (cmIntrinsicOp "core::intrinsics::black_box" [.bool]) [.copy (locPlace 1)] 0 [] []

-- 9. Zero-size null-pointer delta / agreement fixtures (shared verbatim with MR)
/-- `compare_bytes(_1, _2, 0)`. -/
def cmCmpBytes0Mir : CapturedMir :=
  cmCallBody "cm::compare_bytes_0"
    [mkDecl i32MirTy, mkDecl cmRawConstU8Ty, mkDecl cmRawConstU8Ty] 2
    (cmIntrinsicOp "core::intrinsics::compare_bytes" [])
    [.copy (locPlace 1), .copy (locPlace 2), cmUsizeConst 0] 0 [] []

/-- `typed_swap_nonoverlapping::<()>(_1, _2); _0 = 7u32`. -/
def cmSwapZstMir : CapturedMir :=
  cmCallBody "cm::typed_swap_zst"
    [mkDecl u32MirTy, mkDecl { kind := .rawPtr .mut (.tuple []), layoutIdx := 0 },
     mkDecl { kind := .rawPtr .mut (.tuple []), layoutIdx := 0 }, mkDecl unitMirTy] 2
    (cmIntrinsicOp "core::intrinsics::typed_swap_nonoverlapping" [.tuple []])
    [.copy (locPlace 1), .copy (locPlace 2)] 3
    [mkSt (.assign (locPlace 0) (.use (.constant { ty := u32MirTy, val := .scalar (.int ⟨7, 4⟩) })))]
    []

/-- `copy::<u32>(_1, _2, 0); _0 = 7u32`. -/
def cmCopy0Mir : CapturedMir :=
  cmCallBody "cm::copy_0"
    [mkDecl u32MirTy, mkDecl rawConstU32MirTy, mkDecl rawMutU32MirTy, mkDecl unitMirTy] 2
    (cmIntrinsicOp "core::intrinsics::copy" [.uint .u32])
    [.copy (locPlace 1), .copy (locPlace 2), cmUsizeConst 0] 3
    [mkSt (.assign (locPlace 0) (.use (.constant { ty := u32MirTy, val := .scalar (.int ⟨7, 4⟩) })))]
    []

/-! ## §1. Vendored Call Overlay for the 8 Intrinsics (`cmStepHooks`) -/

inductive CmIntrinsic : Type where
  | copy | compareBytes | rawEq | typedSwap | ptrOffsetFrom | ptrOffsetFromUnsigned | ptrMask | blackBox
  deriving DecidableEq, Repr

namespace CmIntrinsic
def defPath : CmIntrinsic → DefPath
  | .copy => "core::intrinsics::copy"
  | .compareBytes => "core::intrinsics::compare_bytes"
  | .rawEq => "core::intrinsics::raw_eq"
  | .typedSwap => "core::intrinsics::typed_swap_nonoverlapping"
  | .ptrOffsetFrom => "core::intrinsics::ptr_offset_from"
  | .ptrOffsetFromUnsigned => "core::intrinsics::ptr_offset_from_unsigned"
  | .ptrMask => "core::intrinsics::ptr_mask"
  | .blackBox => "core::intrinsics::black_box"
def name : CmIntrinsic → String
  | .copy => "copy" | .compareBytes => "compare_bytes" | .rawEq => "raw_eq"
  | .typedSwap => "typed_swap_nonoverlapping" | .ptrOffsetFrom => "ptr_offset_from"
  | .ptrOffsetFromUnsigned => "ptr_offset_from_unsigned" | .ptrMask => "ptr_mask" | .blackBox => "black_box"
def arity : CmIntrinsic → Nat
  | .copy | .compareBytes => 3
  | .rawEq | .typedSwap | .ptrOffsetFrom | .ptrOffsetFromUnsigned | .ptrMask => 2
  | .blackBox => 1
def defId : CmIntrinsic → Miri.MIR.DefId
  | .copy => 40 | .compareBytes => 41 | .rawEq => 42 | .typedSwap => 43
  | .ptrOffsetFrom => 44 | .ptrOffsetFromUnsigned => 45 | .ptrMask => 46 | .blackBox => 47
def ofDefId? : Miri.MIR.DefId → Option CmIntrinsic
  | 40 => some .copy | 41 => some .compareBytes | 42 => some .rawEq | 43 => some .typedSwap
  | 44 => some .ptrOffsetFrom | 45 => some .ptrOffsetFromUnsigned | 46 => some .ptrMask
  | 47 => some .blackBox | _ => none
def all : List CmIntrinsic := [.copy, .compareBytes, .rawEq, .typedSwap, .ptrOffsetFrom, .ptrOffsetFromUnsigned, .ptrMask, .blackBox]
def ofDefPath? (p : DefPath) : Option CmIntrinsic := all.find? (fun k => stringEq p k.defPath)
end CmIntrinsic

def cmFnItemTyId (k : CmIntrinsic) (argTy : Miri.MIR.TyId) : Miri.MIR.TyId :=
  annealFnItemTyIdBase + k.defId + 64 * argTy

def cmDecodeFnItemTyId (tyId : Miri.MIR.TyId) : Option (CmIntrinsic × Miri.MIR.TyId) :=
  if annealFnItemTyIdBase ≤ tyId then
    (CmIntrinsic.ofDefId? ((tyId - annealFnItemTyIdBase) % 64)).map fun k => (k, (tyId - annealFnItemTyIdBase) / 64)
  else none

def cmTyArgId : List RigidTy → Miri.MIR.TyId
  | [] => 0
  | k :: _ => encodeTyId { kind := k, layoutIdx := 0 }

def cmTranslateTerminatorKind : TerminatorKind → Miri.MIR.TerminatorKind
  | .call (.constant c) args dest target unwind =>
    match c.ty.kind with
    | .fnDef p tys =>
      match CmIntrinsic.ofDefPath? p with
      | some k =>
        .Call (.Constant { span := defaultSpanRef, userType := none,
                           value := .Val .ZeroSized (cmFnItemTyId k (cmTyArgId tys)) })
          (args.map fun a => ({ span := defaultSpanRef, operand := translateOperand a } : Miri.MIR.SpannedOperand)).toArray
          (translatePlace dest) target (translateUnwindAction unwind) .Normal defaultSpanRef
      | none => translateTerminatorKind (.call (.constant c) args dest target unwind)
    | _ => translateTerminatorKind (.call (.constant c) args dest target unwind)
  | t => translateTerminatorKind t

def cmTranslateBody (cm : CapturedMir) : Miri.MIR.Body :=
  { translateBody cm with
    basicBlocks := (cm.basicBlocks.map fun bb =>
      ({ translateBasicBlockData bb with
          terminator := { sourceInfo := defaultSourceInfo, kind := cmTranslateTerminatorKind bb.terminator.kind } }
        : Miri.MIR.BasicBlock)).toArray }

/-- The vendored rvalue monad over Anneal's step state. -/
abbrev LmM := Miri.Interpreter.RvalueM AnnealStepState

def cmReadBytesStripProvenance (tb : Bool) (ptr : Miri.Memory.Pointer (Option AnnealProv))
    (size : Miri.ABI.Size) : LmM (Array UInt8) := fun st =>
  match Miri.Memory.sizeAsI64 size with
  | .error _ => .error (.invalidProgram "read size overflow") st
  | .ok signedSize =>
    match Miri.Memory.checkAndDerefPtr annealPointerArithmetic ptr signedSize .memoryAccess
        (annealResolvePtr st.machine) (annealLookupAlloc st.machine) with
    | .error _ => .error (.undefinedBehavior "read_bytes pointer check failed") st
    | .ok none => .ok #[] st
    | .ok (some access) =>
      let st1 : Except Miri.Interpreter.StepError AnnealStepState :=
        if tb then npApplyTreeBorrowsReadAt ptr.provenance ptr.offset.bytes size st else .ok st
      match st1 with
      | .error e => .error e st
      | .ok st1 =>
        match st1.machine.memory.live.find? (fun e => e.1 == access.pointer.allocId) with
        | none => .error (.undefinedBehavior "read of dead allocation") st1
        | some (_, la) =>
          match la.allocation.getBytesStripProvenance annealTargetDataLayout
              (Miri.Memory.allocRange access.pointer.offset size) with
          | .ok bytes => .ok bytes st1
          | .error (.invalidUninitBytes _) => .error (.undefinedBehavior "read of uninitialized bytes") st1
          | .error (.readPointerAsInt _) => .error (.unsupported "pointer bytes read as integers") st1
          | .error _ => .error (.invalidProgram "read_bytes allocation error") st1

def cmTryAllocId (ptr : Miri.Memory.Pointer (Option AnnealProv)) :
    LmM (Except UInt64 (Miri.Memory.AllocId × Miri.ABI.Size)) := fun st =>
  match annealResolvePtr st.machine ptr 0 with
  | .ok r => .ok (.ok (r.allocId, r.offset)) st
  | .error a => .ok (.error a) st

def cmCheckSignedAccess (ptr : Miri.Memory.Pointer (Option AnnealProv)) (dist : Int64) :
    LmM (Except Miri.Interpreter.StepError Unit) := fun st =>
  match Miri.Memory.checkAndDerefPtr annealPointerArithmetic ptr dist.toInt .inboundsPointerArithmetic
      (annealResolvePtr st.machine) (annealLookupAlloc st.machine) with
  | .ok _ => .ok (.ok ()) st
  | .error _ => .ok (.error (.undefinedBehavior "signed access out of bounds")) st

def cmMemCopy (tb : Bool) (src dst : Miri.Memory.Pointer (Option AnnealProv)) (size : Miri.ABI.Size)
    (nonov : Bool) : LmM Unit := fun st =>
  let st1 : Except Miri.Interpreter.StepError AnnealStepState :=
    if tb then
      match npApplyTreeBorrowsReadAt src.provenance src.offset.bytes size st with
      | .ok s => npApplyTreeBorrowsWriteAt dst.provenance dst.offset.bytes size s
      | .error e => .error e
    else .ok st
  match st1 with
  | .error e => .error e st
  | .ok s => annealMemCopy src dst size nonov s

def cmTempAid : Miri.Memory.AllocId := ⟨9000, by decide⟩
def cmTempBase : UInt64 := 65536

def cmAllocateStack (layout : Miri.Interpreter.LocalLayout) : LmM (Miri.Interpreter.RuntimePlace AnnealProv) := fun st =>
  match Miri.Memory.Allocation.tryNew (Prov := AnnealProv) layout.layout.size layout.layout.align.abi .Uninit
      (fun s _ => some (Array.replicate s.bytes.toNat 0)) with
  | .error _ => .error (.unsupported "temp allocation failed") st
  | .ok a =>
    let mach := st.machine
    let mach' : AnnealMachine :=
      { mach with
        memory := { mach.memory with live := mach.memory.live.push (cmTempAid, ⟨.stack, a.withExtra none⟩) }
        addresses := { mach.addresses with baseAddr := mach.addresses.baseAddr.push ⟨cmTempAid, cmTempBase⟩ } }
    .ok ⟨.memory ⟨⟨Miri.ABI.Size.ofBytes cmTempBase, some (.concrete cmTempAid .one)⟩, .none, none⟩, layout⟩
      { st with machine := mach' }

def cmDeallocateStack (ptr : Miri.Memory.Pointer (Option AnnealProv)) : LmM Unit := fun st =>
  match ptr.provenance with
  | some (.concrete aid _) =>
    let mach := st.machine
    .ok () { st with machine := { mach with memory := { mach.memory with live := mach.memory.live.filter (fun e => e.1 != aid) } } }
  | _ => .error (.unsupported "deallocate without provenance") st

def cmPointeeLayout (tyArg : Miri.MIR.TyId) (ly : LayoutTable) : Miri.Interpreter.LocalLayout :=
  layoutOfEncodedTyId tyArg ly

def cmDerefPointer (tyArg : Miri.MIR.TyId) (ly : LayoutTable) (op : Miri.Interpreter.OpTy AnnealProv) :
    LmM (Miri.Interpreter.RuntimePlace AnnealProv) := do
  let imm ← annealReadImmediate op
  match imm.imm.toScalar with
  | .error e => throw (Miri.Interpreter.ScalarOps.immediateError e)
  | .ok sc =>
    match sc.toPointer annealTargetDataLayout with
    | .error e => throw (Miri.Interpreter.ScalarOps.scalarError e)
    | .ok ptr =>
      let pointeeLay := cmPointeeLayout tyArg ly
      let mismatch ←
        match annealOffsetMisalignment ptr.offset pointeeLay.layout.align.abi with
        | .ok m => pure m
        | .error err => throw (.invalidProgram (toString err))
      pure ⟨.memory ⟨ptr, .none, mismatch⟩, pointeeLay⟩

/-- Typed copy leaf (`copyOp`) enforcing uninhabitedness, immediate scalar
validity (`bool`/`char`/non-null `&T`/`fn()`/`!`), and (when `tb = true`)
vendored Tree Borrows read/write transitions on memory-backed sources and
destinations. -/
def cmCopyOp (tb : Bool) (src : Miri.Interpreter.OpTy AnnealProv)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) : LmM Unit := do
  if src.layout.layout.uninhabited then
    throw (.undefinedBehavior "copyOp of uninhabited type")
  if tb then
    match src.op with
    | .indirect mp =>
      let st ← get
      match npApplyTreeBorrowsReadAt mp.ptr.provenance mp.ptr.offset.bytes src.layout.layout.size st with
      | .ok st' => set st'
      | .error e => throw e
    | _ => pure ()
  let imm ← annealReadImmediate src
  match imm.imm with
  | .scalar sc =>
    if !annealValidateScalarForTyId src.layout.ty sc then
      throw (.undefinedBehavior "copyOp of invalid scalar value")
  | _ => pure ()
  if tb then
    match dest.ref with
    | .memory mp =>
      let st ← get
      match npApplyTreeBorrowsWriteAt mp.ptr.provenance mp.ptr.offset.bytes dest.layout.layout.size st with
      | .ok st' => set st'
      | .error e => throw e
    | _ => pure ()
  annealWriteImmediate imm.imm dest

def cmIntrinsicHooks (ld : List LocalDecl) (ly : LayoutTable) (tb : Bool) (tyArg : Miri.MIR.TyId) :
    Miri.Interpreter.IntrinsicHooks AnnealProv AnnealStepState Unit (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealIntrinsicHooks ld ly with
    pointeeType := fun _ tyId =>
      match rawPtrPointeeEncodedTyId? tyId with
      | some p => pure p
      | none => pure tyArg
    copyOp := fun _ src dest => cmCopyOp tb src dest
    placeToOp := fun _ place =>
      match place.ref with
      | .memory mp => pure ⟨.indirect mp, place.layout⟩
      | _ => throw (.unsupported "placeToOp of a local place")
    placePointer := fun place =>
      match place.ref with
      | .memory mp => .ok mp.ptr
      | _ => .error (.unsupported "placePointer of a local place")
    derefPointer := fun _ op => cmDerefPointer tyArg ly op
    memCopy := fun _ src dst size nonov => cmMemCopy tb src dst size nonov
    readBytesStripProvenance := fun _ ptr size => cmReadBytesStripProvenance tb ptr size
    allocateStack := fun _ layout => cmAllocateStack layout
    deallocateStack := fun _ ptr => cmDeallocateStack ptr
    validatePlace := fun _ place _ _ =>
      match place.ref with
      | .memory mp => do
        if place.layout.layout.uninhabited then
          throw (.undefinedBehavior "validatePlace of uninhabited type")
        let imm ← annealReadImmediate ⟨.indirect mp, place.layout⟩
        match imm.imm with
        | .scalar sc =>
          if !annealValidateScalarForTyId place.layout.ty sc then
            throw (.undefinedBehavior "validatePlace of invalid scalar value")
        | _ => pure ()
      | _ => throw (.unsupported "validatePlace of a local place")
    tryAllocId := fun _ ptr => cmTryAllocId ptr
    checkSignedAccess := fun _ ptr dist => cmCheckSignedAccess ptr dist }

def cmCallIntrinsic (ld : List LocalDecl) (ly : LayoutTable) (tb : Bool)
    (inst : Miri.Interpreter.CallInstance) (args : Array (Miri.Interpreter.OpTy AnnealProv))
    (dest : Miri.Interpreter.RuntimeStackPlace AnnealProv) (target : Option Miri.MIR.BasicBlockId) :
    Miri.Interpreter.CallM AnnealStepState (Option Miri.Interpreter.CallInstance) :=
  match CmIntrinsic.ofDefId? inst.defId with
  | none => annealUnsupportedLeaf "call of an intrinsic outside CmIntrinsic"
  | some k => do
    let types := inst.args.filterMap fun
      | .Type ty => some ty
      | _ => none
    let tyArg := (types[0]?).getD 0
    let handled ← Miri.Interpreter.Intrinsics.eval (cmIntrinsicHooks ld ly tb tyArg) ()
      k.name types args dest.toRuntimePlace target
    if handled then pure none
    else annealUnsupportedLeaf "CmIntrinsic not handled by Intrinsics.eval"

def cmCallHooks (ld : List LocalDecl) (ly : LayoutTable) (tb : Bool) :
    Miri.Interpreter.CallHooks AnnealProv AnnealStepState Unit Unit Unit Unit Unit Unit :=
  { annealCallHooks ld ly with
    functionSignature := fun _ layout =>
      match cmDecodeFnItemTyId layout.ty with
      | some (k, _) => pure (k.arity, ())
      | none => annealUnsupportedLeaf "call of a function other than a CmIntrinsic"
    functionKind := fun tyId =>
      match cmDecodeFnItemTyId tyId with
      | some (k, argTy) => pure (.FnDef k.defId #[.Type argTy])
      | none => annealUnsupportedLeaf "call of a function other than a CmIntrinsic"
    resolve := fun _ defId args =>
      match CmIntrinsic.ofDefId? defId with
      | some _ => pure { kind := .Intrinsic defId, args := args }
      | none => annealUnsupportedLeaf "call.resolve of a non-CmIntrinsic item"
    callIntrinsic := fun _ inst args dest target _ => cmCallIntrinsic ld ly tb inst args dest target }

def isCmCallTerminator : Miri.MIR.Terminator → Bool
  | { kind := .Call (.Constant c) _ _ _ _ _ _, .. } =>
    match c.value with
    | .Val .ZeroSized tyId => (cmDecodeFnItemTyId tyId).isSome
    | _ => false
  | _ => false

def cmTerminatorHooks (ld : List LocalDecl) (ly : LayoutTable) (tb : Bool) :=
  let base := annealTerminatorHooks ld ly
  { base with
    call := fun choice term state =>
      Miri.Interpreter.Call.run
        (Miri.Interpreter.Call.evalCallTerminator (cmCallHooks ld ly tb) choice annealCallBudget term)
        state }

def cmStepHooks (cm : CapturedMir) (tb : Bool) :
    Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealStepHooks cm.localDecls cm.layouts
  { base with
    terminator := fun choice term state =>
      if isCmCallTerminator term then
        Miri.Interpreter.ControlFlow.evalTerminator (cmTerminatorHooks cm.localDecls cm.layouts tb) choice term state
      else base.terminator choice term state }


/-! ## §2. Universal Overlay Laws -/

/-- **Basic mode is exactly the base copy leaf**: outside `treeBorrows` mode the
overlay's `memCopy` is `annealMemCopy` (no borrow-tracker effect). -/
theorem cmMemCopy_basic_mode (src dst : Miri.Memory.Pointer (Option AnnealProv))
    (size : Miri.ABI.Size) (nonov : Bool) (st : AnnealStepState) :
    cmMemCopy false src dst size nonov st = annealMemCopy src dst size nonov st := rfl

/-- **Name/arity/defId round trip** for all 8 intrinsics. -/
theorem cmIntrinsic_ofDefId_defId (k : CmIntrinsic) : CmIntrinsic.ofDefId? k.defId = some k := by
  cases k <;> rfl

/-- **Path recognition** for all 8 intrinsics. -/
theorem cmIntrinsic_ofDefPath_defPath (k : CmIntrinsic) :
    CmIntrinsic.ofDefPath? k.defPath = some k := by
  cases k <;> decide +kernel

/-- **Callee TyId round trip**: `cmDecodeFnItemTyId` inverts `cmFnItemTyId`. -/
theorem cmDecodeFnItemTyId_cmFnItemTyId (k : CmIntrinsic) (argTy : Miri.MIR.TyId) :
    cmDecodeFnItemTyId (cmFnItemTyId k argTy) = some (k, argTy) := by
  have hd : k.defId < 64 := by cases k <;> decide
  have h : annealFnItemTyIdBase + k.defId + 64 * argTy - annealFnItemTyIdBase =
      k.defId + 64 * argTy := by
    rw [Nat.add_assoc]; exact Nat.add_sub_cancel_left _ _
  have hle : annealFnItemTyIdBase ≤ annealFnItemTyIdBase + k.defId + 64 * argTy := by
    rw [Nat.add_assoc]; exact Nat.le_add_right _ _
  have h1 : (k.defId + 64 * argTy) % 64 = k.defId := by
    rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hd
  have h2 : (k.defId + 64 * argTy) / 64 = argTy := by
    rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hd, Nat.zero_add]
  unfold cmDecodeFnItemTyId cmFnItemTyId
  simp only [hle, ↓reduceIte]
  rw [h, h1, h2, cmIntrinsic_ofDefId_defId]
  rfl

/-- The 8 vendored intrinsic names are exactly the arms of `Intrinsics.eval`. -/
theorem cmIntrinsic_names :
    CmIntrinsic.all.map CmIntrinsic.name =
      ["copy", "compare_bytes", "raw_eq", "typed_swap_nonoverlapping", "ptr_offset_from",
       "ptr_offset_from_unsigned", "ptr_mask", "black_box"] := rfl

/-- Exact mirror of vendored `Miri/Interpreter/Intrinsics.lean:174-176` `bytesCompare`. -/
def cmMiriBytesCompare : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => if a == b then cmMiriBytesCompare as bs else compare a b

/-- The 32-bit `i32` bit pattern produced by vendored `Intrinsics.compareBytes`
(`Intrinsics.lean:185-186`: `.lt => -1`, `.eq => 0`, `.gt => 1`). -/
def cmMiriBytesCompareI32Bits (l r : List UInt8) : Nat :=
  match cmMiriBytesCompare l r with
  | .lt => 4294967295
  | .eq => 0
  | .gt => 1

/-- **Universal `compare_bytes` algebraic correspondence** (`Trusted.compareUnsignedBytesI32`
= vendored `Miri/Interpreter/Intrinsics.lean:174-186` `bytesCompare`): for ALL
equal-length byte lists `l` and `r`, Trusted's `compareUnsignedBytesI32 l r`
equals the exact `Int32` bit pattern returned by `Intrinsics.compareBytes`. -/
theorem cm_compareUnsignedBytesI32_eq_miriBytesCompare (l r : List UInt8)
    (hLen : l.length = r.length) :
    compareUnsignedBytesI32 l r = cmMiriBytesCompareI32Bits l r := by
  induction l generalizing r with
  | nil =>
    cases r with
    | nil => rfl
    | cons _ _ => simp at hLen
  | cons a as ih =>
    cases r with
    | nil => simp at hLen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
      unfold compareUnsignedBytesI32 cmMiriBytesCompareI32Bits cmMiriBytesCompare
      by_cases hab : a = b
      · subst hab
        have hlt : Nat.blt a.toBitVec.toNat a.toBitVec.toNat = false := by
          cases h : Nat.blt a.toBitVec.toNat a.toBitVec.toNat with
          | false => rfl
          | true => exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_succ_le_self _)
        simp only [hlt, beq_self_eq_true, ↓reduceIte]
        exact ih bs hLen
      · have hne : (a == b) = false := beq_false_of_ne hab
        have hnatNe : a.toBitVec.toNat ≠ b.toBitVec.toNat := by
          intro heq
          apply hab
          apply UInt8.eq_of_toBitVec_eq
          exact BitVec.eq_of_toNat_eq heq
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        by_cases hlt : a.toBitVec.toNat < b.toBitVec.toNat
        · have hblt1 : Nat.blt a.toNat b.toNat = true := Nat.blt_eq.mpr hlt
          have hltU : a < b := UInt8.lt_iff_toBitVec_lt.mpr (BitVec.lt_def.mpr hlt)
          have hcmp : compare a b = .lt := by
            change compareOfLessAndEq a b = .lt
            simp [compareOfLessAndEq, hltU]
          simp [hblt1, hcmp]
        · have hgt : b.toBitVec.toNat < a.toBitVec.toNat := by omega
          have hblt1 : Nat.blt a.toNat b.toNat = false := by
            cases h : Nat.blt a.toNat b.toNat with
            | false => rfl
            | true => exact absurd (Nat.blt_eq.mp h) hlt
          have hblt2 : Nat.blt b.toNat a.toNat = true := Nat.blt_eq.mpr hgt
          have hnotlt : ¬ a < b := fun h => hlt (BitVec.lt_def.mp (UInt8.lt_iff_toBitVec_lt.mp h))
          have hcmp : compare a b = .gt := by
            change compareOfLessAndEq a b = .gt
            simp [compareOfLessAndEq, hnotlt, hab]
          simp [hblt1, hblt2, hcmp]

/-- Exact specification of vendored `Miri/Interpreter/Intrinsics.lean:239-273`
`pointerOffsetFrom` arithmetic (64-bit `SubWithOverflow`, signed `Int64`
distance, `overflow` + `isize::MIN = -2^63` guards, `Scalar.fromInt` bound on
`elemSize`, and `exactDiv` with truncated signed division `Int.tdiv`/`Int.tmod`). -/
def cmMiriPtrOffsetFromSpec (unsigned : Bool) (elemSize : Nat) (aOff bOff : UInt64) : Option Nat :=
  let overflow := aOff.toNat < bOff.toNat
  let distance : Int :=
    if overflow then
      let raw := (2 ^ 64 + aOff.toNat - bOff.toNat)
      if raw ≥ 2 ^ 63 then Int.ofNat raw - 2 ^ 64 else Int.ofNat raw
    else
      let raw := aOff.toNat - bOff.toNat
      if raw ≥ 2 ^ 63 then Int.ofNat raw - 2 ^ 64 else Int.ofNat raw
  let minIsize : Int := -(2 ^ 63 : Int)
  if overflow then
    if unsigned || distance ≥ 0 || distance == minIsize then none
    else if elemSize == 0 || elemSize ≥ 2 ^ 63 then none
    else if Int.tmod distance (Int.ofNat elemSize) != 0 then none
    else some ((2 ^ 64 + Int.tdiv distance (Int.ofNat elemSize)).toNat)
  else if distance < 0 then none
  else if elemSize == 0 || elemSize ≥ 2 ^ 63 then none
  else if Int.tmod distance (Int.ofNat elemSize) != 0 then none
  else some ((Int.tdiv distance (Int.ofNat elemSize)).toNat)

/-- Direct invocation of unmodified vendored `Miri.Interpreter.IntegerOps.binary .SubWithOverflow`
and `Miri.Interpreter.IntegerArithmeticIntrinsic.exactDiv` (`Intrinsics.lean:239-273`). -/
def cmMiriPtrOffsetFromVendored (unsigned : Bool) (elemSize : Nat) (aOff bOff : UInt64) :
    Option Nat :=
  let uTy : Miri.Interpreter.IntegerType := ⟨Miri.ABI.Size.ofBytes 8, .usize⟩
  let sTy : Miri.Interpreter.IntegerType := ⟨Miri.ABI.Size.ofBytes 8, .isize⟩
  let retTy := if unsigned then uTy else sTy
  match Miri.Interpreter.IntegerOps.binary .SubWithOverflow
      ⟨Miri.Memory.ScalarInt.ofUInt64 aOff, uTy⟩
      ⟨Miri.Memory.ScalarInt.ofUInt64 bOff, uTy⟩ with
  | .ok (.withOverflow diffSc overflow) =>
    match diffSc.toTargetIsize (Miri.ABI.Size.ofBytes 8) with
    | .ok distI64 =>
      let dist := distI64.toInt
      let minIsize : Int := -(2 ^ 63 : Int)
      let okRange : Bool :=
        if overflow then !unsigned && !(dist ≥ 0 || dist == minIsize)
        else !(dist < 0)
      if !okRange then none
      else
        match Miri.Memory.ScalarInt.tryFromInt dist (Miri.ABI.Size.ofBytes 8),
              Miri.Memory.ScalarInt.tryFromInt (Int.ofNat elemSize) (Miri.ABI.Size.ofBytes 8) with
        | .ok (some aSc), .ok (some bSc) =>
          match Miri.Interpreter.IntegerArithmeticIntrinsic.exactDiv ⟨aSc, retTy⟩ ⟨bSc, retTy⟩ with
          | .ok qSc => some qSc.data.toNat
          | .error _ => none
        | _, _ => none
    | .error _ => none
  | _ => none

/-- **Universal `ptr_offset_from` / `ptr_offset_from_unsigned` arithmetic equivalence**:
for ALL signednesses `unsigned`, ALL element sizes `elemSize`, and ALL 64-bit
offsets `aOff bOff : UInt64`, Trusted `evalPtrOffsetFromDistance 8` equals the
exact `SubWithOverflow` / `isize::MIN` / `exactDiv` specification of vendored
`Miri/Interpreter/Intrinsics.lean:239-273`. -/
theorem cm_evalPtrOffsetFromDistance_eq_miriSpec (unsigned : Bool) (elemSize : Nat)
    (aOff bOff : UInt64) :
    (evalPtrOffsetFromDistance 8 unsigned elemSize aOff.toNat bOff.toNat).map (·.bits) =
      cmMiriPtrOffsetFromSpec unsigned elemSize aOff bOff := by
  have ha : aOff.toNat < 2 ^ 64 := aOff.toBitVec.isLt
  have hb : bOff.toNat < 2 ^ 64 := bOff.toBitVec.isLt
  have hMod : scalarModulus 8 = 2 ^ 64 := by decide
  have hHalf : scalarModulus 8 / 2 - 1 = 2 ^ 63 - 1 := by decide
  unfold evalPtrOffsetFromDistance cmMiriPtrOffsetFromSpec
  simp only [Int.ofNat_eq_natCast]
  change (match Bool.or (Nat.beq elemSize 0) (Bool.not (Nat.ble elemSize (2 ^ 63 - 1))) with
    | true => none
    | false =>
      match Nat.ble bOff.toNat aOff.toNat with
      | true =>
        let dist := aOff.toNat - bOff.toNat
        match Bool.and (Nat.ble dist (2 ^ 63 - 1)) (Nat.beq (dist % elemSize) 0) with
        | true => some (ScalarInt.mk (dist / elemSize) 8)
        | false => none
      | false =>
        match unsigned with
        | true => none
        | false =>
          let negDist := bOff.toNat - aOff.toNat
          match Bool.and (Nat.ble negDist (2 ^ 63 - 1)) (Nat.beq (negDist % elemSize) 0) with
          | true => some (ScalarInt.mk (2 ^ 64 - negDist / elemSize) 8)
          | false => none).map ScalarInt.bits = _
  by_cases hlt : aOff.toNat < bOff.toNat
  · have hble : Nat.ble bOff.toNat aOff.toNat = false := by
      cases h : Nat.ble bOff.toNat aOff.toNat with
      | false => rfl
      | true => exact absurd (Nat.le_of_ble_eq_true h) (by omega)
    simp only [hlt, ↓reduceIte, hble]
    by_cases hBadElem : elemSize = 0 ∨ 2 ^ 63 ≤ elemSize
    · have hElemCond : Bool.or (Nat.beq elemSize 0) (Bool.not (Nat.ble elemSize (2 ^ 63 - 1))) = true := by
        rcases hBadElem with rfl | hge
        · rfl
        · have : Nat.ble elemSize (2 ^ 63 - 1) = false := by
            cases h : Nat.ble elemSize (2 ^ 63 - 1) with
            | false => rfl
            | true => exact absurd (Nat.le_of_ble_eq_true h) (by omega)
          simp [this]
      have hElemOr : (elemSize == 0 || decide (elemSize ≥ 2 ^ 63)) = true := by
        rcases hBadElem with rfl | hge
        · rfl
        · simp [hge]
      simp [hElemCond, hElemOr]
    · have hElemPos : 0 < elemSize := by omega
      have hElemLe : elemSize ≤ 2 ^ 63 - 1 := by omega
      have hElemCond : Bool.or (Nat.beq elemSize 0) (Bool.not (Nat.ble elemSize (2 ^ 63 - 1))) = false := by
        have h1 : Nat.beq elemSize 0 = false := by
          cases elemSize with | zero => omega | succ _ => rfl
        have h2 : Nat.ble elemSize (2 ^ 63 - 1) = true := Nat.ble_eq.mpr hElemLe
        simp [h1, h2]
      have hElemOr : (elemSize == 0 || decide (elemSize ≥ 2 ^ 63)) = false := by
        simp [show elemSize ≠ 0 by omega, show ¬ (elemSize ≥ 2 ^ 63) by omega]
      simp only [hElemCond, hElemOr, Bool.false_eq_true, ↓reduceIte]
      cases unsigned with
      | true => simp
      | false =>
        simp only [Bool.false_or]
        by_cases hRange : bOff.toNat - aOff.toNat ≤ 2 ^ 63 - 1
        · have hRawGe : 2 ^ 64 + aOff.toNat - bOff.toNat ≥ 2 ^ 63 := by omega
          have hDistEq : ((2 ^ 64 + aOff.toNat - bOff.toNat : Nat) : Int) - 2 ^ 64 =
              -(((bOff.toNat - aOff.toNat : Nat) : Int)) := by omega
          have hNotGe0 : ¬ (-(((bOff.toNat - aOff.toNat : Nat) : Int)) ≥ 0) := by omega
          have hNotMin : (-(((bOff.toNat - aOff.toNat : Nat) : Int)) == -(2 ^ 63 : Int)) = false := by
            exact beq_false_of_ne (by omega)
          have hBleNeg : Nat.ble (bOff.toNat - aOff.toNat) (2 ^ 63 - 1) = true :=
            Nat.ble_eq.mpr hRange
          have hTmod : Int.tmod (-(((bOff.toNat - aOff.toNat : Nat) : Int))) (elemSize : Int) =
              -((((bOff.toNat - aOff.toNat) % elemSize : Nat) : Int)) := by
            rw [Int.neg_tmod]; rfl
          have hTdiv : Int.tdiv (-(((bOff.toNat - aOff.toNat : Nat) : Int))) (elemSize : Int) =
              -((((bOff.toNat - aOff.toNat) / elemSize : Nat) : Int)) := by
            rw [Int.neg_tdiv]; rfl
          simp only [hRawGe, ↓reduceIte, hDistEq, hNotGe0, hNotMin, decide_false, Bool.or_self,
            hBleNeg, Bool.true_and, hTmod, hTdiv]
          by_cases hRem : (bOff.toNat - aOff.toNat) % elemSize = 0
          · have hBeq0 : Nat.beq ((bOff.toNat - aOff.toNat) % elemSize) 0 = true := by
              rw [hRem]; rfl
            have hTmod0 : (-((((bOff.toNat - aOff.toNat) % elemSize : Nat) : Int)) != 0) = false := by
              rw [hRem]; rfl
            simp only [hBeq0, hTmod0, Bool.false_eq_true, ↓reduceIte, Option.map_some]
            have hqLe : (bOff.toNat - aOff.toNat) / elemSize ≤ 2 ^ 63 - 1 :=
              Nat.le_trans (Nat.div_le_self _ _) hRange
            congr 1; omega
          · have hBeq0 : Nat.beq ((bOff.toNat - aOff.toNat) % elemSize) 0 = false := by
              cases h : Nat.beq ((bOff.toNat - aOff.toNat) % elemSize) 0 with
              | false => rfl
              | true => exact absurd (Nat.eq_of_beq_eq_true h) hRem
            have hTmodNe : (-((((bOff.toNat - aOff.toNat) % elemSize : Nat) : Int)) != 0) = true := by
              have hEqF : (-((((bOff.toNat - aOff.toNat) % elemSize : Nat) : Int)) == 0) = false :=
                beq_false_of_ne (by omega)
              simp only [bne, hEqF, Bool.not_false]
            simp only [hBeq0, hTmodNe, Bool.false_eq_true, ↓reduceIte, Option.map_none]
        · have hBleNeg : Nat.ble (bOff.toNat - aOff.toNat) (2 ^ 63 - 1) = false := by
            cases h : Nat.ble (bOff.toNat - aOff.toNat) (2 ^ 63 - 1) with
            | false => rfl
            | true => exact absurd (Nat.le_of_ble_eq_true h) hRange
          simp only [hBleNeg, Bool.false_and, Option.map_none]
          by_cases hEqHalf : bOff.toNat - aOff.toNat = 2 ^ 63
          · have hRawGe : 2 ^ 64 + aOff.toNat - bOff.toNat ≥ 2 ^ 63 := by omega
            have hMin : (((2 ^ 64 + aOff.toNat - bOff.toNat : Nat) : Int) - 2 ^ 64 == -(2 ^ 63 : Int)) = true := by
              have : ((2 ^ 64 + aOff.toNat - bOff.toNat : Nat) : Int) - 2 ^ 64 = -(2 ^ 63 : Int) := by omega
              rw [this]; rfl
            simp only [hRawGe, hMin, Bool.or_true, ↓reduceIte]
          · have hRawLt : ¬ (2 ^ 64 + aOff.toNat - bOff.toNat ≥ 2 ^ 63) := by omega
            have hGe0 : ((2 ^ 64 + aOff.toNat - bOff.toNat : Nat) : Int) ≥ 0 := by omega
            simp only [hRawLt, hGe0, decide_true, Bool.true_or, ↓reduceIte]
  · have hle : bOff.toNat ≤ aOff.toNat := by omega
    have hble : Nat.ble bOff.toNat aOff.toNat = true := Nat.ble_eq.mpr hle
    simp only [hlt, ↓reduceIte, hble]
    by_cases hBadElem : elemSize = 0 ∨ 2 ^ 63 ≤ elemSize
    · have hElemCond : Bool.or (Nat.beq elemSize 0) (Bool.not (Nat.ble elemSize (2 ^ 63 - 1))) = true := by
        rcases hBadElem with rfl | hge
        · rfl
        · have : Nat.ble elemSize (2 ^ 63 - 1) = false := by
            cases h : Nat.ble elemSize (2 ^ 63 - 1) with
            | false => rfl
            | true => exact absurd (Nat.le_of_ble_eq_true h) (by omega)
          simp [this]
      have hElemOr : (elemSize == 0 || decide (elemSize ≥ 2 ^ 63)) = true := by
        rcases hBadElem with rfl | hge
        · rfl
        · simp [hge]
      simp [hElemCond, hElemOr]
    · have hElemPos : 0 < elemSize := by omega
      have hElemLe : elemSize ≤ 2 ^ 63 - 1 := by omega
      have hElemCond : Bool.or (Nat.beq elemSize 0) (Bool.not (Nat.ble elemSize (2 ^ 63 - 1))) = false := by
        have h1 : Nat.beq elemSize 0 = false := by
          cases elemSize with | zero => omega | succ _ => rfl
        have h2 : Nat.ble elemSize (2 ^ 63 - 1) = true := Nat.ble_eq.mpr hElemLe
        simp [h1, h2]
      have hElemOr : (elemSize == 0 || decide (elemSize ≥ 2 ^ 63)) = false := by
        simp [show elemSize ≠ 0 by omega, show ¬ (elemSize ≥ 2 ^ 63) by omega]
      simp only [hElemCond, hElemOr, Bool.false_eq_true, ↓reduceIte]
      by_cases hRange : aOff.toNat - bOff.toNat ≤ 2 ^ 63 - 1
      · have hRawLt : ¬ (aOff.toNat - bOff.toNat ≥ 2 ^ 63) := by omega
        have hNotNeg : ¬ (((aOff.toNat - bOff.toNat : Nat) : Int) < 0) := by omega
        have hBlePos : Nat.ble (aOff.toNat - bOff.toNat) (2 ^ 63 - 1) = true :=
          Nat.ble_eq.mpr hRange
        have hTmod : Int.tmod ((aOff.toNat - bOff.toNat : Nat) : Int) (elemSize : Int) =
            (((aOff.toNat - bOff.toNat) % elemSize : Nat) : Int) := rfl
        have hTdiv : Int.tdiv ((aOff.toNat - bOff.toNat : Nat) : Int) (elemSize : Int) =
            (((aOff.toNat - bOff.toNat) / elemSize : Nat) : Int) := rfl
        simp only [hRawLt, ↓reduceIte, hNotNeg, hBlePos, Bool.true_and, hTmod, hTdiv]
        by_cases hRem : (aOff.toNat - bOff.toNat) % elemSize = 0
        · have hBeq0 : Nat.beq ((aOff.toNat - bOff.toNat) % elemSize) 0 = true := by
            rw [hRem]; rfl
          have hTmod0 : ((((aOff.toNat - bOff.toNat) % elemSize : Nat) : Int) != 0) = false := by
            rw [hRem]; rfl
          simp only [hBeq0, hTmod0, Bool.false_eq_true, ↓reduceIte, Option.map_some, Int.toNat_natCast]
        · have hBeq0 : Nat.beq ((aOff.toNat - bOff.toNat) % elemSize) 0 = false := by
            cases h : Nat.beq ((aOff.toNat - bOff.toNat) % elemSize) 0 with
            | false => rfl
            | true => exact absurd (Nat.eq_of_beq_eq_true h) hRem
          have hTmodNe : ((((aOff.toNat - bOff.toNat) % elemSize : Nat) : Int) != 0) = true := by
            have hEqF : ((((aOff.toNat - bOff.toNat) % elemSize : Nat) : Int) == 0) = false :=
              beq_false_of_ne (by omega)
            simp only [bne, hEqF, Bool.not_false]
          simp only [hBeq0, hTmodNe, Bool.false_eq_true, ↓reduceIte, Option.map_none]
      · have hRawGe : aOff.toNat - bOff.toNat ≥ 2 ^ 63 := by omega
        have hNeg : ((aOff.toNat - bOff.toNat : Nat) : Int) - 2 ^ 64 < 0 := by omega
        have hBlePos : Nat.ble (aOff.toNat - bOff.toNat) (2 ^ 63 - 1) = false := by
          cases h : Nat.ble (aOff.toNat - bOff.toNat) (2 ^ 63 - 1) with
          | false => rfl
          | true => exact absurd (Nat.le_of_ble_eq_true h) hRange
        simp only [hRawGe, hNeg, hBlePos, Bool.false_and, ↓reduceIte, Option.map_none]

/-- **Kernel-checked vendored `SubWithOverflow` + `exactDiv` edge-regime matrix**:
verifies `cmMiriPtrOffsetFromVendored` (calling unmodified vendored
`IntegerOps.binary .SubWithOverflow` and `IntegerArithmeticIntrinsic.exactDiv`)
equals `evalPtrOffsetFromDistance 8` across positive, negative, zero, `isize::MIN`,
positive overflow, unsigned underflow, ZST div-by-0, oversized `elemSize = 2^63`,
and non-divisible distances. -/
theorem cm_miri_ptrOffsetFrom_vendored_matrix :
    cmMiriPtrOffsetFromVendored false 4 1036 1028 = some 2 ∧
    cmMiriPtrOffsetFromVendored false 4 1028 1036 = some (2 ^ 64 - 2) ∧
    cmMiriPtrOffsetFromVendored false 4 4096 4096 = some 0 ∧
    cmMiriPtrOffsetFromVendored false 4 0 (UInt64.ofNat (2 ^ 63)) = none ∧
    cmMiriPtrOffsetFromVendored false 4 (UInt64.ofNat (2 ^ 63)) 0 = none ∧
    cmMiriPtrOffsetFromVendored true 4 1028 1036 = none ∧
    cmMiriPtrOffsetFromVendored true 4 1040 1024 = some 4 ∧
    cmMiriPtrOffsetFromVendored false 0 1024 1024 = none ∧
    cmMiriPtrOffsetFromVendored false (2 ^ 63) 1024 1024 = none ∧
    cmMiriPtrOffsetFromVendored false 4 1030 1024 = none ∧
    cmMiriPtrOffsetFromVendored false 4 1024 1030 = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

private theorem cm_miri_size8_truncate_bv (v : Miri.ABI.U128) :
    BitVec.zeroExtend 128 (BitVec.extractLsb (64 - 1) 0 v) =
      BitVec.ofNat 128 (v.toNat % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.zeroExtend, BitVec.extractLsb, BitVec.extractLsb',
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_zero]

private theorem cm_miri_size8_signExtend (v : Miri.ABI.U128) :
    (Miri.ABI.Size.ofBytes 8).signExtend v =
      .ok (if v.toNat % 2 ^ 64 ≥ 2 ^ 63 then ((v.toNat % 2 ^ 64 : Nat) : Int) - 2 ^ 64
           else ((v.toNat % 2 ^ 64 : Nat) : Int)) := by
  change Except.ok (BitVec.signExtend 128 (BitVec.extractLsb (64 - 1) 0 v)).toInt = _
  congr 1
  have hExt : (BitVec.signExtend 128 (BitVec.extractLsb (64 - 1) 0 v)).toInt =
      (BitVec.extractLsb (64 - 1) 0 v).toInt := by
    rw [BitVec.toInt_signExtend]; simp
  rw [hExt, BitVec.toInt_eq_toNat_cond]
  have hToNat : (BitVec.extractLsb (64 - 1) 0 v).toNat = v.toNat % 2 ^ 64 := by
    simp only [BitVec.extractLsb, BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_zero]
  rw [hToNat]
  by_cases h : v.toNat % 2 ^ 64 ≥ 2 ^ 63
  · have h2 : ¬ (2 * (v.toNat % 2 ^ 64) < 2 ^ (64 - 1 - 0 + 1)) := by omega
    simp only [h, h2, ↓reduceIte]
    have hpow : (2 ^ (64 - 1 - 0 + 1) : Nat) = 2 ^ 64 := by decide
    rw [hpow]; rfl
  · have h2 : 2 * (v.toNat % 2 ^ 64) < 2 ^ (64 - 1 - 0 + 1) := by omega
    simp only [h, h2, ↓reduceIte]

private theorem cm_miri_toBits_8 (sc : Miri.Memory.ScalarInt)
    (hSz : sc.size = Miri.ABI.Size.ofBytes 8) :
    sc.toBits (Miri.ABI.Size.ofBytes 8) = .ok sc.data := by
  change (if (Miri.ABI.Size.ofBytes 8 != sc.size) = true then
      Except.error (Miri.Memory.ScalarIntError.sizeMismatch (Miri.ABI.Size.ofBytes 8) sc.size)
    else Except.ok sc.data) = Except.ok sc.data
  rw [hSz]; rfl

private theorem cm_miri_truncateFromUInt_8 (v : Miri.ABI.U128) :
    ∃ sc : Miri.Memory.ScalarInt,
      Miri.Memory.ScalarInt.truncateFromUInt v (Miri.ABI.Size.ofBytes 8) =
        .ok (sc, BitVec.ofNat 128 (v.toNat % 2 ^ 64) != v) ∧
      sc.size = Miri.ABI.Size.ofBytes 8 ∧
      sc.data = BitVec.ofNat 128 (v.toNat % 2 ^ 64) := by
  let sc : Miri.Memory.ScalarInt :=
    match Miri.Memory.ScalarInt.truncateFromUInt v (Miri.ABI.Size.ofBytes 8) with
    | .ok (s, _) => s
    | .error _ => Miri.Memory.ScalarInt.ofUInt64 0
  refine ⟨sc, ?_, rfl, ?_⟩
  · have hLow := cm_miri_size8_truncate_bv v
    change Except.ok (sc, BitVec.zeroExtend 128 (BitVec.extractLsb (64 - 1) 0 v) != v) =
      Except.ok (sc, BitVec.ofNat 128 (v.toNat % 2 ^ 64) != v)
    rw [hLow]
  · exact cm_miri_size8_truncate_bv v

private theorem cm_miri_truncateFromInt_8 (n : Int)
    (hLo : -(2 ^ 127 : Int) ≤ n) (hHi : n < (2 ^ 127 : Int)) :
    ∃ sc : Miri.Memory.ScalarInt,
      Miri.Memory.ScalarInt.truncateFromInt n (Miri.ABI.Size.ofBytes 8) =
        .ok (sc,
          (if (BitVec.ofInt 128 n).toNat % 2 ^ 64 ≥ 2 ^ 63 then
             (((BitVec.ofInt 128 n).toNat % 2 ^ 64 : Nat) : Int) - 2 ^ 64
           else (((BitVec.ofInt 128 n).toNat % 2 ^ 64 : Nat) : Int)) != n) ∧
      sc.size = Miri.ABI.Size.ofBytes 8 ∧
      sc.data = BitVec.ofNat 128 ((BitVec.ofInt 128 n).toNat % 2 ^ 64) := by
  obtain ⟨sc, hTr, hSz, hDat⟩ := cm_miri_truncateFromUInt_8 (BitVec.ofInt 128 n)
  refine ⟨sc, ?_, hSz, hDat⟩
  have h1 : ¬ (n < -(2 ^ 127 : Int)) := by omega
  have h2 : ¬ (n ≥ (2 ^ 127 : Int)) := by omega
  have hNotOut : (decide (n < -(2 ^ 127 : Int)) || decide (n ≥ (2 ^ 127 : Int))) = false := by
    simp only [h1, h2, decide_false, Bool.or_self]
  unfold Miri.Memory.ScalarInt.truncateFromInt
  simp only [hNotOut, Bool.false_eq_true, ↓reduceIte]
  change (do
    let (result, _) ← Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofInt 128 n) (Miri.ABI.Size.ofBytes 8)
    let decoded ← (Miri.ABI.Size.ofBytes 8).signExtend result.data |>.mapError Miri.Memory.ScalarIntError.sizeError
    pure (result, decoded != n)) = _
  rw [hTr]
  simp only [bind, Except.bind, pure, Except.pure, Except.mapError, hDat, cm_miri_size8_signExtend]
  have hModEq : (BitVec.ofNat 128 ((BitVec.ofInt 128 n).toNat % 2 ^ 64)).toNat % 2 ^ 64 =
      (BitVec.ofInt 128 n).toNat % 2 ^ 64 := by
    have hlt := Nat.mod_lt (BitVec.ofInt 128 n).toNat (show 0 < 2 ^ 64 by decide)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hlt (by decide)), Nat.mod_eq_of_lt hlt]
  rw [hModEq]

private theorem cm_miri_subWithOverflow_u64 (aOff bOff : UInt64) :
    ∃ sc : Miri.Memory.ScalarInt,
      Miri.Interpreter.IntegerOps.binary .SubWithOverflow
        ⟨Miri.Memory.ScalarInt.ofUInt64 aOff, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩
        ⟨Miri.Memory.ScalarInt.ofUInt64 bOff, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩ =
        .ok (.withOverflow sc (decide (aOff.toNat < bOff.toNat))) ∧
      sc.size = Miri.ABI.Size.ofBytes 8 ∧
      sc.data = BitVec.ofNat 128
        (if aOff.toNat < bOff.toNat then 2 ^ 64 + aOff.toNat - bOff.toNat
         else aOff.toNat - bOff.toNat) := by
  have ha : aOff.toNat < 2 ^ 64 := aOff.toBitVec.isLt
  have hb : bOff.toNat < 2 ^ 64 := bOff.toBitVec.isLt
  have hA128 : (BitVec.ofNat 128 aOff.toNat).toNat = aOff.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hB128 : (BitVec.ofNat 128 bOff.toNat).toNat = bOff.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hBin :
      Miri.Interpreter.IntegerOps.binary .SubWithOverflow
        ⟨Miri.Memory.ScalarInt.ofUInt64 aOff, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩
        ⟨Miri.Memory.ScalarInt.ofUInt64 bOff, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩ =
      (do
        let l : Int := Int.ofNat (BitVec.ofNat 128 aOff.toNat).toNat
        let r : Int := Int.ofNat (BitVec.ofNat 128 bOff.toNat).toNat
        if r == 0 then pure () else pure ()
        let result : Int := l - r
        let hostOverflow := decide (result < 0) || decide (result ≥ (2 ^ 128 : Int))
        let (value, lossy) ←
          (Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofInt 128 result) (Miri.ABI.Size.ofBytes 8)).mapError
            Miri.Interpreter.IntegerOpError.scalar
        if (hostOverflow || lossy) && false then
          throw (Miri.Interpreter.IntegerOpError.undefinedBehavior (.arithmeticOverflow .SubWithOverflow))
        pure (Miri.Interpreter.IntegerResult.withOverflow value (hostOverflow || lossy))) := rfl
  obtain ⟨sc, hTr, hSz, hDat⟩ :=
    cm_miri_truncateFromUInt_8 (BitVec.ofInt 128 ((aOff.toNat : Int) - (bOff.toNat : Int)))
  refine ⟨sc, ?_, hSz, ?_⟩
  · rw [hBin, hA128, hB128]
    simp only [Int.ofNat_eq_natCast, ite_self, bind, Except.bind, pure, Except.pure,
      Except.mapError, hTr, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    by_cases hlt : aOff.toNat < bOff.toNat
    · have hNeg : ((aOff.toNat : Int) - (bOff.toNat : Int)) < 0 := by omega
      simp only [hlt, hNeg, decide_true, Bool.true_or]
    · have hNonneg : ¬ (((aOff.toNat : Int) - (bOff.toNat : Int)) < 0) := by omega
      have hNotGe : ¬ (((aOff.toNat : Int) - (bOff.toNat : Int)) ≥ (2 ^ 128 : Int)) := by omega
      have hBvNat : (BitVec.ofInt 128 ((aOff.toNat : Int) - (bOff.toNat : Int))).toNat =
          aOff.toNat - bOff.toNat := by
        rw [BitVec.toNat_ofInt]
        have hP : (↑(2 ^ 128 : Nat) : Int) = (2 ^ 128 : Int) := by decide
        rw [hP]
        have h1 : (((aOff.toNat : Int) - (bOff.toNat : Int)) % (2 ^ 128 : Int)) =
            ((aOff.toNat - bOff.toNat : Nat) : Int) := by omega
        rw [h1]; rfl
      have hMod64 : (aOff.toNat - bOff.toNat) % 2 ^ 64 = aOff.toNat - bOff.toNat :=
        Nat.mod_eq_of_lt (by omega)
      have hBvEq : BitVec.ofNat 128 (aOff.toNat - bOff.toNat) =
          BitVec.ofInt 128 ((aOff.toNat : Int) - (bOff.toNat : Int)) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hBvNat]
      simp only [hlt, hNonneg, hNotGe, decide_false, Bool.false_or, hBvNat, hMod64,
        hBvEq, bne_self_eq_false]
  · rw [hDat]
    by_cases hlt : aOff.toNat < bOff.toNat
    · have hBvNat : (BitVec.ofInt 128 ((aOff.toNat : Int) - (bOff.toNat : Int))).toNat =
          2 ^ 128 + aOff.toNat - bOff.toNat := by
        rw [BitVec.toNat_ofInt]
        have hP : (↑(2 ^ 128 : Nat) : Int) = (2 ^ 128 : Int) := by decide
        rw [hP]
        have h1 : (((aOff.toNat : Int) - (bOff.toNat : Int)) % (2 ^ 128 : Int)) =
            ((2 ^ 128 + aOff.toNat - bOff.toNat : Nat) : Int) := by omega
        rw [h1]; rfl
      have hMod64 : (2 ^ 128 + aOff.toNat - bOff.toNat) % 2 ^ 64 = 2 ^ 64 + aOff.toNat - bOff.toNat := by
        have hSplit : 2 ^ 128 + aOff.toNat - bOff.toNat =
            (2 ^ 64 - 1) * 2 ^ 64 + (2 ^ 64 + aOff.toNat - bOff.toNat) := by omega
        rw [hSplit, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      simp only [hlt, ↓reduceIte, hBvNat, hMod64]
    · have hBvNat : (BitVec.ofInt 128 ((aOff.toNat : Int) - (bOff.toNat : Int))).toNat =
          aOff.toNat - bOff.toNat := by
        rw [BitVec.toNat_ofInt]
        have hP : (↑(2 ^ 128 : Nat) : Int) = (2 ^ 128 : Int) := by decide
        rw [hP]
        have h1 : (((aOff.toNat : Int) - (bOff.toNat : Int)) % (2 ^ 128 : Int)) =
            ((aOff.toNat - bOff.toNat : Nat) : Int) := by omega
        rw [h1]; rfl
      have hMod64 : (aOff.toNat - bOff.toNat) % 2 ^ 64 = aOff.toNat - bOff.toNat :=
        Nat.mod_eq_of_lt (by omega)
      simp only [hlt, ↓reduceIte, hBvNat, hMod64]

private theorem cm_miri_toTargetIsize_8 (sc : Miri.Memory.ScalarInt) (raw : Nat)
    (hSz : sc.size = Miri.ABI.Size.ofBytes 8)
    (hDat : sc.data = BitVec.ofNat 128 raw) (hRaw : raw < 2 ^ 64) :
    sc.toTargetIsize (Miri.ABI.Size.ofBytes 8) =
      .ok (Int64.ofInt (if raw ≥ 2 ^ 63 then (raw : Int) - 2 ^ 64 else (raw : Int))) := by
  have hBv : (BitVec.ofNat 128 raw).toNat % 2 ^ 64 = raw := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show raw < 2 ^ 128 by omega), Nat.mod_eq_of_lt hRaw]
  unfold Miri.Memory.ScalarInt.toTargetIsize Miri.Memory.ScalarInt.toInt
  rw [cm_miri_toBits_8 sc hSz, hDat]
  simp only [bind, Except.bind, pure, Except.pure, Except.mapError, cm_miri_size8_signExtend, hBv]
  by_cases h : raw ≥ 2 ^ 63
  · have hRng1 : ¬ (((raw : Int) - 2 ^ 64) < -(2 ^ 63 : Int)) := by omega
    have hRng2 : ¬ (((raw : Int) - 2 ^ 64) ≥ (2 ^ 63 : Int)) := by omega
    simp only [h, hRng1, hRng2, decide_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  · have hRng1 : ¬ ((raw : Int) < -(2 ^ 63 : Int)) := by omega
    have hRng2 : ¬ ((raw : Int) ≥ (2 ^ 63 : Int)) := by omega
    simp only [h, hRng1, hRng2, decide_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte]

private theorem cm_miri_tryFromInt_8_in (n : Int)
    (hLo : -(2 ^ 63 : Int) ≤ n) (hHi : n < (2 ^ 63 : Int)) :
    ∃ sc : Miri.Memory.ScalarInt,
      Miri.Memory.ScalarInt.tryFromInt n (Miri.ABI.Size.ofBytes 8) = .ok (some sc) ∧
      sc.size = Miri.ABI.Size.ofBytes 8 ∧
      sc.data = BitVec.ofNat 128 (if n < 0 then (n + 2 ^ 64).toNat else n.toNat) := by
  obtain ⟨sc, hTr, hSz, hDat⟩ := cm_miri_truncateFromInt_8 n (by omega) (by omega)
  have hBvMod : (BitVec.ofInt 128 n).toNat % 2 ^ 64 =
      if n < 0 then (n + 2 ^ 64).toNat else n.toNat := by
    have hP : (↑(2 ^ 128 : Nat) : Int) = (2 ^ 128 : Int) := by decide
    by_cases hn : n < 0
    · simp only [hn, ↓reduceIte]
      rw [BitVec.toNat_ofInt, hP]
      have h1 : (n % (2 ^ 128 : Int)).toNat = 2 ^ 128 - (-n).toNat := by omega
      rw [h1]
      have hSplit : 2 ^ 128 - (-n).toNat = (2 ^ 64 - 1) * 2 ^ 64 + (n + 2 ^ 64).toNat := by omega
      rw [hSplit, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    · simp only [hn, ↓reduceIte]
      rw [BitVec.toNat_ofInt, hP]
      have h1 : (n % (2 ^ 128 : Int)).toNat = n.toNat := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]
  have hDecEq : (if (BitVec.ofInt 128 n).toNat % 2 ^ 64 ≥ 2 ^ 63 then
      (((BitVec.ofInt 128 n).toNat % 2 ^ 64 : Nat) : Int) - 2 ^ 64
    else (((BitVec.ofInt 128 n).toNat % 2 ^ 64 : Nat) : Int)) = n := by
    rw [hBvMod]
    by_cases hn : n < 0
    · have hGe : (n + 2 ^ 64).toNat ≥ 2 ^ 63 := by omega
      simp only [hn, hGe, ↓reduceIte]; omega
    · have hLt : ¬ (n.toNat ≥ 2 ^ 63) := by omega
      simp only [hn, hLt, ↓reduceIte]; omega
  refine ⟨sc, ?_, hSz, by rw [hDat, hBvMod]⟩
  unfold Miri.Memory.ScalarInt.tryFromInt
  rw [hTr, hDecEq]
  simp only [bne_self_eq_false, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte]

private theorem cm_miri_tryFromInt_8_not_some (n : Int)
    (hOut : n < -(2 ^ 63 : Int) ∨ n ≥ (2 ^ 63 : Int)) :
    Miri.Memory.ScalarInt.tryFromInt n (Miri.ABI.Size.ofBytes 8) = .ok none ∨
    Miri.Memory.ScalarInt.tryFromInt n (Miri.ABI.Size.ofBytes 8) = .error (.integerOutsideI128 n) := by
  by_cases h128 : n < -(2 ^ 127 : Int) ∨ n ≥ (2 ^ 127 : Int)
  · right
    have hCond : (decide (n < -(2 ^ 127 : Int)) || decide (n ≥ (2 ^ 127 : Int))) = true := by
      rcases h128 with h | h
      · simp only [h, decide_true, Bool.true_or]
      · simp only [h, decide_true, Bool.or_true]
    unfold Miri.Memory.ScalarInt.tryFromInt Miri.Memory.ScalarInt.truncateFromInt
    simp only [hCond, ↓reduceIte, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · left
    obtain ⟨sc, hTr, _, _⟩ := cm_miri_truncateFromInt_8 n (by omega) (by omega)
    let dec : Int := if (BitVec.ofInt 128 n).toNat % 2 ^ 64 ≥ 2 ^ 63 then
        (((BitVec.ofInt 128 n).toNat % 2 ^ 64 : Nat) : Int) - 2 ^ 64
      else (((BitVec.ofInt 128 n).toNat % 2 ^ 64 : Nat) : Int)
    have hDecRange : -(2 ^ 63 : Int) ≤ dec ∧ dec < (2 ^ 63 : Int) := by
      have hlt := Nat.mod_lt (BitVec.ofInt 128 n).toNat (show 0 < 2 ^ 64 by decide)
      dsimp only [dec]
      by_cases h : (BitVec.ofInt 128 n).toNat % 2 ^ 64 ≥ 2 ^ 63 <;> simp only [h, ↓reduceIte] <;> omega
    have hNe : (dec != n) = true := by
      have hEqF : (dec == n) = false := beq_false_of_ne (by omega)
      simp only [bne, hEqF, Bool.not_false]
    unfold Miri.Memory.ScalarInt.tryFromInt
    rw [hTr]
    change (do let (result, overflow) ← Except.ok (sc, dec != n); if overflow then pure none else pure (some result)) = _
    simp only [hNe, bind, Except.bind, pure, Except.pure, ↓reduceIte]

private theorem cm_miri_decode_8 (unsigned : Bool) (sc : Miri.Memory.ScalarInt) (a : Int)
    (hSz : sc.size = Miri.ABI.Size.ofBytes 8)
    (hDat : sc.data = BitVec.ofNat 128 (if a < 0 then (a + 2 ^ 64).toNat else a.toNat))
    (hA : if unsigned then 0 ≤ a ∧ a < 2 ^ 63 else -(2 ^ 63 : Int) < a ∧ a < 2 ^ 63) :
    Miri.Interpreter.IntegerOps.decode
      ⟨sc, if unsigned then ⟨Miri.ABI.Size.ofBytes 8, .usize⟩ else ⟨Miri.ABI.Size.ofBytes 8, .isize⟩⟩ =
      .ok a := by
  cases unsigned with
  | true =>
    simp only [↓reduceIte] at hA ⊢
    have haNotNeg : ¬ (a < 0) := by omega
    simp only [haNotNeg, ↓reduceIte] at hDat
    unfold Miri.Interpreter.IntegerOps.decode Miri.Interpreter.IntegerType.signed Miri.MIR.IntegerKind.signed
      Miri.Memory.ScalarInt.toUInt
    simp only [Bool.false_eq_true, ↓reduceIte, cm_miri_toBits_8 sc hSz, hDat, Except.mapError,
      bind, Except.bind, pure, Except.pure, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show a.toNat < 2 ^ 128 by omega), Int.ofNat_eq_natCast]
    congr 1; omega
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hA ⊢
    unfold Miri.Interpreter.IntegerOps.decode Miri.Interpreter.IntegerType.signed Miri.MIR.IntegerKind.signed
      Miri.Memory.ScalarInt.toInt
    simp only [↓reduceIte, cm_miri_toBits_8 sc hSz, hDat, bind, Except.bind, Except.mapError,
      cm_miri_size8_signExtend]
    by_cases haNeg : a < 0
    · have hBv : (BitVec.ofNat 128 (a + 2 ^ 64).toNat).toNat % 2 ^ 64 = (a + 2 ^ 64).toNat := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hGe : (a + 2 ^ 64).toNat ≥ 2 ^ 63 := by omega
      simp only [haNeg, ↓reduceIte, hBv, hGe]
      congr 1; omega
    · have hBv : (BitVec.ofNat 128 a.toNat).toNat % 2 ^ 64 = a.toNat := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hLt : ¬ (a.toNat ≥ 2 ^ 63) := by omega
      simp only [haNeg, ↓reduceIte, hBv, hLt]
      congr 1; omega

private theorem cm_miri_binary_divrem_8 (isDiv unsigned : Bool)
    (aSc bSc : Miri.Memory.ScalarInt) (a b : Int)
    (hASz : aSc.size = Miri.ABI.Size.ofBytes 8)
    (hADat : aSc.data = BitVec.ofNat 128 (if a < 0 then (a + 2 ^ 64).toNat else a.toNat))
    (hBSz : bSc.size = Miri.ABI.Size.ofBytes 8)
    (hBDat : bSc.data = BitVec.ofNat 128 b.toNat)
    (hA : if unsigned then 0 ≤ a ∧ a < 2 ^ 63 else -(2 ^ 63 : Int) < a ∧ a < 2 ^ 63)
    (hB : 0 < b ∧ b < 2 ^ 63) :
    let retTy : Miri.Interpreter.IntegerType :=
      if unsigned then ⟨Miri.ABI.Size.ofBytes 8, .usize⟩ else ⟨Miri.ABI.Size.ofBytes 8, .isize⟩
    let q := if isDiv then Int.tdiv a b else Int.tmod a b
    ∃ qSc : Miri.Memory.ScalarInt,
      Miri.Interpreter.IntegerOps.binary (if isDiv then .Div else .Rem) ⟨aSc, retTy⟩ ⟨bSc, retTy⟩ =
        .ok (.scalar qSc) ∧
      qSc.size = Miri.ABI.Size.ofBytes 8 ∧
      qSc.data = BitVec.ofNat 128 (if q < 0 then (q + 2 ^ 64).toNat else q.toNat) := by
  have hbNotNeg : ¬ (b < 0) := by omega
  have hBDatIf : bSc.data = BitVec.ofNat 128 (if b < 0 then (b + 2 ^ 64).toNat else b.toNat) := by
    simp only [hbNotNeg, ↓reduceIte]; exact hBDat
  have hBIn : if unsigned then 0 ≤ b ∧ b < 2 ^ 63 else -(2 ^ 63 : Int) < b ∧ b < 2 ^ 63 := by
    cases unsigned <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hDecA := cm_miri_decode_8 unsigned aSc a hASz hADat hA
  have hDecB := cm_miri_decode_8 unsigned bSc b hBSz hBDatIf hBIn
  have hBNe : (b == 0) = false := beq_false_of_ne (by omega)
  have hQBounds :
      (if unsigned then 0 ≤ (if isDiv then Int.tdiv a b else Int.tmod a b) ∧
          (if isDiv then Int.tdiv a b else Int.tmod a b) < 2 ^ 63
       else -(2 ^ 63 : Int) < (if isDiv then Int.tdiv a b else Int.tmod a b) ∧
          (if isDiv then Int.tdiv a b else Int.tmod a b) < 2 ^ 63) := by
    cases unsigned with
    | true =>
      simp only [↓reduceIte] at hA ⊢
      have haEq : a = (a.toNat : Int) := by omega
      have hbEq : b = (b.toNat : Int) := by omega
      cases isDiv with
      | true =>
        simp only [↓reduceIte]; rw [haEq, hbEq]
        have h1 : Int.tdiv (a.toNat : Int) (b.toNat : Int) = ((a.toNat / b.toNat : Nat) : Int) := rfl
        rw [h1]
        have hle : ((a.toNat / b.toNat : Nat) : Int) ≤ (a.toNat : Int) :=
          Int.ofNat_le.mpr (Nat.div_le_self a.toNat b.toNat)
        have hnn : (0 : Int) ≤ ((a.toNat / b.toNat : Nat) : Int) := Int.natCast_nonneg _
        generalize ((a.toNat / b.toNat : Nat) : Int) = qn at hle hnn ⊢
        omega
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]; rw [haEq, hbEq]
        have h1 : Int.tmod (a.toNat : Int) (b.toNat : Int) = ((a.toNat % b.toNat : Nat) : Int) := rfl
        rw [h1]; have hlt := Nat.mod_lt a.toNat (show 0 < b.toNat by omega); omega
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hA ⊢
      have hbEq : b = (b.toNat : Int) := by omega
      by_cases haNeg : a < 0
      · have haEq : a = -((-a).toNat : Int) := by omega
        cases isDiv with
        | true =>
          simp only [↓reduceIte]; rw [haEq, hbEq, Int.neg_tdiv]
          have h1 : Int.tdiv ((-a).toNat : Int) (b.toNat : Int) = (((-a).toNat / b.toNat : Nat) : Int) := rfl
          rw [h1]
          have hle : (((-a).toNat / b.toNat : Nat) : Int) ≤ ((-a).toNat : Int) :=
            Int.ofNat_le.mpr (Nat.div_le_self (-a).toNat b.toNat)
          have hnn : (0 : Int) ≤ (((-a).toNat / b.toNat : Nat) : Int) := Int.natCast_nonneg _
          generalize (((-a).toNat / b.toNat : Nat) : Int) = qn at hle hnn ⊢
          omega
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]; rw [haEq, hbEq, Int.neg_tmod]
          have h1 : Int.tmod ((-a).toNat : Int) (b.toNat : Int) = (((-a).toNat % b.toNat : Nat) : Int) := rfl
          rw [h1]; have hlt := Nat.mod_lt (-a).toNat (show 0 < b.toNat by omega); omega
      · have haEq : a = (a.toNat : Int) := by omega
        cases isDiv with
        | true =>
          simp only [↓reduceIte]; rw [haEq, hbEq]
          have h1 : Int.tdiv (a.toNat : Int) (b.toNat : Int) = ((a.toNat / b.toNat : Nat) : Int) := rfl
          rw [h1]
          have hle : ((a.toNat / b.toNat : Nat) : Int) ≤ (a.toNat : Int) :=
            Int.ofNat_le.mpr (Nat.div_le_self a.toNat b.toNat)
          have hnn : (0 : Int) ≤ ((a.toNat / b.toNat : Nat) : Int) := Int.natCast_nonneg _
          generalize ((a.toNat / b.toNat : Nat) : Int) = qn at hle hnn ⊢
          omega
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]; rw [haEq, hbEq]
          have h1 : Int.tmod (a.toNat : Int) (b.toNat : Int) = ((a.toNat % b.toNat : Nat) : Int) := rfl
          rw [h1]; have hlt := Nat.mod_lt a.toNat (show 0 < b.toNat by omega); omega
  cases unsigned with
  | true =>
    simp only [↓reduceIte] at hA hQBounds hDecA hDecB ⊢
    let q : Int := if isDiv then Int.tdiv a b else Int.tmod a b
    have hqNotNeg : ¬ (q < 0) := by dsimp only [q]; omega
    have hqLt : q < 2 ^ 63 := hQBounds.2
    have hqGe : 0 ≤ q := hQBounds.1
    obtain ⟨qSc, hTr, hQSz, hQDat⟩ := cm_miri_truncateFromUInt_8 (BitVec.ofInt 128 q)
    have hBvMod : (BitVec.ofInt 128 q).toNat % 2 ^ 64 = q.toNat := by
      have hP : (↑(2 ^ 128 : Nat) : Int) = (2 ^ 128 : Int) := by decide
      rw [BitVec.toNat_ofInt, hP]
      have h1 : (q % (2 ^ 128 : Int)).toNat = q.toNat := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]
    refine ⟨qSc, ?_, hQSz, ?_⟩
    · cases isDiv with
      | true =>
        simp only [q, ↓reduceIte] at hTr ⊢
        have hBin :
            Miri.Interpreter.IntegerOps.binary .Div
              ⟨aSc, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩ ⟨bSc, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩ =
            (do
              let l ← Miri.Interpreter.IntegerOps.decode ⟨aSc, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩
              let r ← Miri.Interpreter.IntegerOps.decode ⟨bSc, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩
              if r == 0 then throw (Miri.Interpreter.IntegerOpError.undefinedBehavior .divisionByZero)
              let result := Int.tdiv l r
              let hostOverflow := decide (result < 0) || decide (result ≥ (2 ^ 128 : Int))
              let (value, lossy) ←
                (Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofInt 128 result) (Miri.ABI.Size.ofBytes 8)).mapError
                  Miri.Interpreter.IntegerOpError.scalar
              if (hostOverflow || lossy) && false then
                throw (Miri.Interpreter.IntegerOpError.undefinedBehavior (.arithmeticOverflow .Div))
              pure (Miri.Interpreter.IntegerResult.scalar value)) := rfl
        rw [hBin, hDecA, hDecB]
        simp only [bind, Except.bind, pure, Except.pure, Except.mapError, hBNe,
          Bool.false_eq_true, ↓reduceIte, hTr, Bool.and_false]
      | false =>
        simp only [q, Bool.false_eq_true, ↓reduceIte] at hTr ⊢
        have hBin :
            Miri.Interpreter.IntegerOps.binary .Rem
              ⟨aSc, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩ ⟨bSc, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩ =
            (do
              let l ← Miri.Interpreter.IntegerOps.decode ⟨aSc, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩
              let r ← Miri.Interpreter.IntegerOps.decode ⟨bSc, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩
              if r == 0 then throw (Miri.Interpreter.IntegerOpError.undefinedBehavior .remainderByZero)
              let result := Int.tmod l r
              let hostOverflow := decide (result < 0) || decide (result ≥ (2 ^ 128 : Int))
              let (value, lossy) ←
                (Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofInt 128 result) (Miri.ABI.Size.ofBytes 8)).mapError
                  Miri.Interpreter.IntegerOpError.scalar
              if (hostOverflow || lossy) && false then
                throw (Miri.Interpreter.IntegerOpError.undefinedBehavior (.arithmeticOverflow .Rem))
              pure (Miri.Interpreter.IntegerResult.scalar value)) := rfl
        rw [hBin, hDecA, hDecB]
        simp only [bind, Except.bind, pure, Except.pure, Except.mapError, hBNe,
          Bool.false_eq_true, ↓reduceIte, hTr, Bool.and_false]
    · rw [hQDat, hBvMod]
      change BitVec.ofNat 128 q.toNat = BitVec.ofNat 128 (if q < 0 then (q + 2 ^ 64).toNat else q.toNat)
      simp only [hqNotNeg, ↓reduceIte]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hA hQBounds hDecA hDecB ⊢
    let q : Int := if isDiv then Int.tdiv a b else Int.tmod a b
    have hqLo : -(2 ^ 63 : Int) < q := hQBounds.1
    have hqHi : q < (2 ^ 63 : Int) := hQBounds.2
    have hNoOv : (a == -(Int.ofNat (2 ^ (64 - 1))) && b == -1) = false := by
      have hBNotNeg1 : (b == -1) = false := beq_false_of_ne (by omega)
      simp only [hBNotNeg1, Bool.and_false]
    have hP128 : (↑(2 ^ 128 : Nat) : Int) = (2 ^ 128 : Int) := by decide
    have hWrap : (BitVec.ofInt 128 q).toInt = q := by
      rw [BitVec.toInt_ofInt, Int.bmod_def, hP128]
      have hMod : q % (2 ^ 128 : Int) = if q < 0 then q + 2 ^ 128 else q := by omega
      by_cases hqn : q < 0 <;> simp only [hqn, ↓reduceIte] at hMod <;> rw [hMod] <;> omega
    obtain ⟨qSc, hTr, hQSz, hQDat⟩ := cm_miri_truncateFromInt_8 q (by omega) (by omega)
    have hBvMod : (BitVec.ofInt 128 q).toNat % 2 ^ 64 =
        if q < 0 then (q + 2 ^ 64).toNat else q.toNat := by
      by_cases hqn : q < 0
      · simp only [hqn, ↓reduceIte]
        rw [BitVec.toNat_ofInt, hP128]
        have h1 : (q % (2 ^ 128 : Int)).toNat = 2 ^ 128 - (-q).toNat := by omega
        rw [h1]
        have hSplit : 2 ^ 128 - (-q).toNat = (2 ^ 64 - 1) * 2 ^ 64 + (q + 2 ^ 64).toNat := by omega
        rw [hSplit, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      · simp only [hqn, ↓reduceIte]
        rw [BitVec.toNat_ofInt, hP128]
        have h1 : (q % (2 ^ 128 : Int)).toNat = q.toNat := by omega
        rw [h1, Nat.mod_eq_of_lt (by omega)]
    refine ⟨qSc, ?_, hQSz, by rw [hQDat, hBvMod]⟩
    cases isDiv with
    | true =>
      simp only [q, ↓reduceIte] at hWrap hTr ⊢
      have hBin :
          Miri.Interpreter.IntegerOps.binary .Div
            ⟨aSc, ⟨Miri.ABI.Size.ofBytes 8, .isize⟩⟩ ⟨bSc, ⟨Miri.ABI.Size.ofBytes 8, .isize⟩⟩ =
          (do
            let l ← Miri.Interpreter.IntegerOps.decode ⟨aSc, ⟨Miri.ABI.Size.ofBytes 8, .isize⟩⟩
            let r ← Miri.Interpreter.IntegerOps.decode ⟨bSc, ⟨Miri.ABI.Size.ofBytes 8, .isize⟩⟩
            if r == 0 then throw (Miri.Interpreter.IntegerOpError.undefinedBehavior .divisionByZero)
            if l == -(Int.ofNat (2 ^ (64 - 1))) && r == -1 then
              throw (Miri.Interpreter.IntegerOpError.undefinedBehavior .divisionOverflow)
            let result := Int.tdiv l r
            let hostOverflow := decide (result < -(2 ^ 127 : Int)) || decide (result ≥ (2 ^ 127 : Int))
            let (value, lossy) ←
              (Miri.Memory.ScalarInt.truncateFromInt (BitVec.ofInt 128 result).toInt (Miri.ABI.Size.ofBytes 8)).mapError
                Miri.Interpreter.IntegerOpError.scalar
            if (hostOverflow || lossy) && false then
              throw (Miri.Interpreter.IntegerOpError.undefinedBehavior (.arithmeticOverflow .Div))
            pure (Miri.Interpreter.IntegerResult.scalar value)) := rfl
      rw [hBin, hDecA, hDecB]
      simp only [bind, Except.bind, pure, Except.pure, Except.mapError, hBNe, hNoOv,
        Bool.false_eq_true, ↓reduceIte, hWrap, hTr, Bool.and_false]
    | false =>
      simp only [q, Bool.false_eq_true, ↓reduceIte] at hWrap hTr ⊢
      have hBin :
          Miri.Interpreter.IntegerOps.binary .Rem
            ⟨aSc, ⟨Miri.ABI.Size.ofBytes 8, .isize⟩⟩ ⟨bSc, ⟨Miri.ABI.Size.ofBytes 8, .isize⟩⟩ =
          (do
            let l ← Miri.Interpreter.IntegerOps.decode ⟨aSc, ⟨Miri.ABI.Size.ofBytes 8, .isize⟩⟩
            let r ← Miri.Interpreter.IntegerOps.decode ⟨bSc, ⟨Miri.ABI.Size.ofBytes 8, .isize⟩⟩
            if r == 0 then throw (Miri.Interpreter.IntegerOpError.undefinedBehavior .remainderByZero)
            if l == -(Int.ofNat (2 ^ (64 - 1))) && r == -1 then
              throw (Miri.Interpreter.IntegerOpError.undefinedBehavior .remainderOverflow)
            let result := Int.tmod l r
            let hostOverflow := decide (result < -(2 ^ 127 : Int)) || decide (result ≥ (2 ^ 127 : Int))
            let (value, lossy) ←
              (Miri.Memory.ScalarInt.truncateFromInt (BitVec.ofInt 128 result).toInt (Miri.ABI.Size.ofBytes 8)).mapError
                Miri.Interpreter.IntegerOpError.scalar
            if (hostOverflow || lossy) && false then
              throw (Miri.Interpreter.IntegerOpError.undefinedBehavior (.arithmeticOverflow .Rem))
            pure (Miri.Interpreter.IntegerResult.scalar value)) := rfl
      rw [hBin, hDecA, hDecB]
      simp only [bind, Except.bind, pure, Except.pure, Except.mapError, hBNe, hNoOv,
        Bool.false_eq_true, ↓reduceIte, hWrap, hTr, Bool.and_false]

private theorem cm_miri_binary_rem_zero_8 (unsigned : Bool)
    (aSc bSc : Miri.Memory.ScalarInt) (a : Int)
    (hASz : aSc.size = Miri.ABI.Size.ofBytes 8)
    (hADat : aSc.data = BitVec.ofNat 128 (if a < 0 then (a + 2 ^ 64).toNat else a.toNat))
    (hBSz : bSc.size = Miri.ABI.Size.ofBytes 8)
    (hBDat : bSc.data = BitVec.ofNat 128 0)
    (hA : if unsigned then 0 ≤ a ∧ a < 2 ^ 63 else -(2 ^ 63 : Int) < a ∧ a < 2 ^ 63) :
    let retTy : Miri.Interpreter.IntegerType :=
      if unsigned then ⟨Miri.ABI.Size.ofBytes 8, .usize⟩ else ⟨Miri.ABI.Size.ofBytes 8, .isize⟩
    Miri.Interpreter.IntegerOps.binary .Rem ⟨aSc, retTy⟩ ⟨bSc, retTy⟩ =
      .error (.undefinedBehavior .remainderByZero) := by
  have hDecA := cm_miri_decode_8 unsigned aSc a hASz hADat hA
  have h0In : if unsigned then 0 ≤ (0 : Int) ∧ (0 : Int) < 2 ^ 63
      else -(2 ^ 63 : Int) < (0 : Int) ∧ (0 : Int) < 2 ^ 63 := by
    cases unsigned <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hBDatIf : bSc.data = BitVec.ofNat 128 (if (0 : Int) < 0 then ((0 : Int) + 2 ^ 64).toNat else (0 : Int).toNat) :=
    hBDat
  have hDecB := cm_miri_decode_8 unsigned bSc 0 hBSz hBDatIf h0In
  exact Miri.Interpreter.IntegerOps.binary_remainder_by_zero _ _ a hDecA hDecB rfl

/-- **Universal vendored-mirror faithfulness for `ptr_offset_from[_unsigned]`**:
for ALL `unsigned : Bool`, ALL `elemSize : Nat`, and ALL 64-bit offsets
`aOff bOff : UInt64`, `cmMiriPtrOffsetFromVendored` (calling UNMODIFIED vendored
`Miri.Interpreter.IntegerOps.binary .SubWithOverflow`, `ScalarInt.toTargetIsize`,
`ScalarInt.tryFromInt`, and `Miri.Interpreter.IntegerArithmeticIntrinsic.exactDiv`)
equals `cmMiriPtrOffsetFromSpec`. -/
theorem cm_miriPtrOffsetFromVendored_eq_spec (unsigned : Bool) (elemSize : Nat)
    (aOff bOff : UInt64) :
    cmMiriPtrOffsetFromVendored unsigned elemSize aOff bOff =
      cmMiriPtrOffsetFromSpec unsigned elemSize aOff bOff := by
  have ha : aOff.toNat < 2 ^ 64 := aOff.toBitVec.isLt
  have hb : bOff.toNat < 2 ^ 64 := bOff.toBitVec.isLt
  let raw : Nat := if aOff.toNat < bOff.toNat then 2 ^ 64 + aOff.toNat - bOff.toNat else aOff.toNat - bOff.toNat
  let dist : Int := if raw ≥ 2 ^ 63 then (raw : Int) - 2 ^ 64 else (raw : Int)
  have hRawLt : raw < 2 ^ 64 := by
    dsimp only [raw]; by_cases h : aOff.toNat < bOff.toNat <;> simp only [h, ↓reduceIte] <;> omega
  have hDistRng : -(2 ^ 63 : Int) ≤ dist ∧ dist < (2 ^ 63 : Int) := by
    dsimp only [dist]; by_cases h : raw ≥ 2 ^ 63 <;> simp only [h, ↓reduceIte] <;> omega
  obtain ⟨diffSc, hSub, hDiffSz, hDiffDat⟩ := cm_miri_subWithOverflow_u64 aOff bOff
  have hToIsize := cm_miri_toTargetIsize_8 diffSc raw hDiffSz hDiffDat hRawLt
  have hI64ToInt : (Int64.ofInt dist).toInt = dist := by
    have hP64 : (↑(2 ^ 64 : Nat) : Int) = (2 ^ 64 : Int) := by decide
    rw [Int64.toInt_ofInt, Int.bmod_def, hP64]
    have h1 : dist % (2 ^ 64 : Int) = if dist < 0 then dist + 2 ^ 64 else dist := by omega
    by_cases hdn : dist < 0 <;> simp only [hdn, ↓reduceIte] at h1 <;> rw [h1] <;> omega
  have hDistEqSpec :
      (if aOff.toNat < bOff.toNat then
        if 2 ^ 64 + aOff.toNat - bOff.toNat ≥ 2 ^ 63 then
          Int.ofNat (2 ^ 64 + aOff.toNat - bOff.toNat) - 2 ^ 64
        else Int.ofNat (2 ^ 64 + aOff.toNat - bOff.toNat)
      else
        if aOff.toNat - bOff.toNat ≥ 2 ^ 63 then
          Int.ofNat (aOff.toNat - bOff.toNat) - 2 ^ 64
        else Int.ofNat (aOff.toNat - bOff.toNat)) = dist := by
    dsimp only [dist, raw]
    by_cases h : aOff.toNat < bOff.toNat <;> simp only [h, ↓reduceIte, Int.ofNat_eq_natCast]
  unfold cmMiriPtrOffsetFromVendored cmMiriPtrOffsetFromSpec
  dsimp only
  rw [hSub]
  dsimp only
  rw [hToIsize]
  dsimp only
  rw [hI64ToInt, hDistEqSpec]
  have hRangeCheck :
      (if (decide (aOff.toNat < bOff.toNat)) = true then
        !unsigned && !(decide (dist ≥ 0) || dist == -(2 ^ 63 : Int))
      else !decide (dist < 0)) =
      !(if aOff.toNat < bOff.toNat then
          unsigned || decide (dist ≥ 0) || dist == -(2 ^ 63 : Int)
        else decide (dist < 0)) := by
    by_cases h : aOff.toNat < bOff.toNat <;> simp [h, Bool.and_assoc]
  by_cases hBadRange :
      (if aOff.toNat < bOff.toNat then
        unsigned || decide (dist ≥ 0) || dist == -(2 ^ 63 : Int)
      else decide (dist < 0)) = true
  · rw [hRangeCheck, hBadRange]
    simp only [Bool.not_true, Bool.not_false, ↓reduceIte]
    by_cases h : aOff.toNat < bOff.toNat
    · simp only [h, ↓reduceIte] at hBadRange ⊢
      rw [hBadRange]; rfl
    · simp only [h, ↓reduceIte] at hBadRange ⊢
      simp only [decide_eq_true_eq.mp hBadRange, ↓reduceIte]
  · have hBadFalse :
        (if aOff.toNat < bOff.toNat then
          unsigned || decide (dist ≥ 0) || dist == -(2 ^ 63 : Int)
        else decide (dist < 0)) = false := Bool.eq_false_iff.mpr hBadRange
    rw [hRangeCheck, hBadFalse]
    simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    have hDistGood : if unsigned then 0 ≤ dist ∧ dist < 2 ^ 63 else -(2 ^ 63 : Int) < dist ∧ dist < 2 ^ 63 := by
      by_cases h : aOff.toNat < bOff.toNat
      · simp only [h, ↓reduceIte] at hBadFalse
        have hU : unsigned = false := by cases unsigned <;> simp_all
        have hNotGe0 : ¬ (dist ≥ 0) := by
          intro hc; simp [hU, hc] at hBadFalse
        have hNotMin : dist ≠ -(2 ^ 63 : Int) := by
          intro hc; simp [hU, hc] at hBadFalse
        simp only [hU, Bool.false_eq_true, ↓reduceIte]; omega
      · simp only [h, ↓reduceIte] at hBadFalse
        have hGe0 : 0 ≤ dist := by
          have : ¬ (dist < 0) := decide_eq_false_iff_not.mp hBadFalse
          omega
        cases unsigned <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    obtain ⟨aSc, hTryA, hASz, hADat⟩ := cm_miri_tryFromInt_8_in dist hDistRng.1 hDistRng.2
    rw [hTryA]
    by_cases hElemBig : elemSize ≥ 2 ^ 63
    · have hElemCond : (elemSize == 0 || decide (elemSize ≥ 2 ^ 63)) = true := by simp [hElemBig]
      have hOut : Int.ofNat elemSize < -(2 ^ 63 : Int) ∨ Int.ofNat elemSize ≥ (2 ^ 63 : Int) := by
        right; rw [Int.ofNat_eq_natCast]; omega
      rcases cm_miri_tryFromInt_8_not_some (Int.ofNat elemSize) hOut with hBNone | hBErr
      · rw [hBNone]; dsimp only
        by_cases h : aOff.toNat < bOff.toNat
        · simp only [h, ↓reduceIte] at hBadFalse ⊢
          simp [hBadFalse, hElemCond]
        · simp only [h, ↓reduceIte] at hBadFalse ⊢
          have hNotNeg : ¬ (dist < 0) := decide_eq_false_iff_not.mp hBadFalse
          simp [hNotNeg, hElemCond]
      · rw [hBErr]; dsimp only
        by_cases h : aOff.toNat < bOff.toNat
        · simp only [h, ↓reduceIte] at hBadFalse ⊢
          simp [hBadFalse, hElemCond]
        · simp only [h, ↓reduceIte] at hBadFalse ⊢
          have hNotNeg : ¬ (dist < 0) := decide_eq_false_iff_not.mp hBadFalse
          simp [hNotNeg, hElemCond]
    · have hElemLt : elemSize < 2 ^ 63 := by omega
      have hElemLo : -(2 ^ 63 : Int) ≤ Int.ofNat elemSize := by rw [Int.ofNat_eq_natCast]; omega
      have hElemHi : Int.ofNat elemSize < (2 ^ 63 : Int) := by rw [Int.ofNat_eq_natCast]; omega
      obtain ⟨bSc, hTryB, hBSz, hBDatRaw⟩ := cm_miri_tryFromInt_8_in (Int.ofNat elemSize) hElemLo hElemHi
      have hElemNotNeg : ¬ (Int.ofNat elemSize < 0) := by rw [Int.ofNat_eq_natCast]; omega
      have hBDat : bSc.data = BitVec.ofNat 128 elemSize := by
        simp only [hElemNotNeg, ↓reduceIte] at hBDatRaw; exact hBDatRaw
      rw [hTryB]
      dsimp only
      by_cases hElem0 : elemSize = 0
      · subst hElem0
        unfold Miri.Interpreter.IntegerArithmeticIntrinsic.exactDiv
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind, Except.bind,
          Except.mapError, cm_miri_binary_rem_zero_8 unsigned aSc bSc dist hASz hADat hBSz hBDat hDistGood]
        by_cases h : aOff.toNat < bOff.toNat
        · simp only [h, ↓reduceIte] at hBadFalse ⊢
          simp [hBadFalse]
        · simp only [h, ↓reduceIte] at hBadFalse ⊢
          have hNotNeg : ¬ (dist < 0) := decide_eq_false_iff_not.mp hBadFalse
          simp [hNotNeg]
      · have hElemPos : 0 < elemSize := by omega
        have hElemB : 0 < (elemSize : Int) ∧ (elemSize : Int) < 2 ^ 63 := by omega
        have hElemCondF : (elemSize == 0 || decide (elemSize ≥ 2 ^ 63)) = false := by
          simp [hElem0, show ¬ (elemSize ≥ 2 ^ 63) by omega]
        unfold Miri.Interpreter.IntegerArithmeticIntrinsic.exactDiv
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind, Except.bind,
          Except.mapError]
        obtain ⟨rSc, hRemStep, _, hRDat⟩ :=
          cm_miri_binary_divrem_8 false unsigned aSc bSc dist (elemSize : Int) hASz hADat hBSz hBDat hDistGood hElemB
        obtain ⟨qSc, hDivStep, _, hQDat⟩ :=
          cm_miri_binary_divrem_8 true unsigned aSc bSc dist (elemSize : Int) hASz hADat hBSz hBDat hDistGood hElemB
        simp only [Bool.false_eq_true, ↓reduceIte] at hRemStep hDivStep hRDat hQDat
        rw [hRemStep]
        dsimp only
        by_cases hRem0 : Int.tmod dist (elemSize : Int) = 0
        · have hRemNotNeg : ¬ (Int.tmod dist (elemSize : Int) < 0) := by omega
          have hRemNull : rSc.isNull = true := by
            change (rSc.data == (0 : Miri.ABI.U128)) = true
            rw [hRDat]
            simp only [hRemNotNeg, ↓reduceIte, hRem0]; rfl
          simp only [hRemNull, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hDivStep, pure, Except.pure]
          have hTdivRng : -(2 ^ 63 : Int) < Int.tdiv dist (elemSize : Int) ∧
              Int.tdiv dist (elemSize : Int) < (2 ^ 63 : Int) := by
            by_cases hdn : dist < 0
            · have hde : dist = -((-dist).toNat : Int) := by omega
              rw [hde, Int.neg_tdiv]
              have h1 : Int.tdiv ((-dist).toNat : Int) (elemSize : Int) =
                  (((-dist).toNat / elemSize : Nat) : Int) := rfl
              rw [h1]
              have hle : (((-dist).toNat / elemSize : Nat) : Int) ≤ ((-dist).toNat : Int) :=
                Int.ofNat_le.mpr (Nat.div_le_self _ _)
              have hnn : (0 : Int) ≤ (((-dist).toNat / elemSize : Nat) : Int) := Int.natCast_nonneg _
              generalize (((-dist).toNat / elemSize : Nat) : Int) = qn at hle hnn ⊢
              cases unsigned <;> simp only [Bool.false_eq_true, ↓reduceIte] at hDistGood <;> omega
            · have hde : dist = (dist.toNat : Int) := by omega
              rw [hde]
              have h1 : Int.tdiv (dist.toNat : Int) (elemSize : Int) =
                  ((dist.toNat / elemSize : Nat) : Int) := rfl
              rw [h1]
              have hle : ((dist.toNat / elemSize : Nat) : Int) ≤ (dist.toNat : Int) :=
                Int.ofNat_le.mpr (Nat.div_le_self _ _)
              have hnn : (0 : Int) ≤ ((dist.toNat / elemSize : Nat) : Int) := Int.natCast_nonneg _
              generalize ((dist.toNat / elemSize : Nat) : Int) = qn at hle hnn ⊢
              omega
          have hQDataNat : qSc.data.toNat =
              if Int.tdiv dist (elemSize : Int) < 0 then (Int.tdiv dist (elemSize : Int) + 2 ^ 64).toNat
              else (Int.tdiv dist (elemSize : Int)).toNat := by
            rw [hQDat, BitVec.toNat_ofNat]
            by_cases hqn : Int.tdiv dist (elemSize : Int) < 0 <;>
              simp only [hqn, ↓reduceIte] <;> exact Nat.mod_eq_of_lt (by omega)
          rw [hQDataNat]
          by_cases h : aOff.toNat < bOff.toNat
          · simp only [h, ↓reduceIte] at hBadFalse ⊢
            have hU : unsigned = false := by cases unsigned <;> simp_all
            have hDistNeg : dist < 0 := by
              have : ¬ (dist ≥ 0) := by intro hc; simp [hU, hc] at hBadFalse
              omega
            have hQNeg : Int.tdiv dist (elemSize : Int) < 0 := by
              have hde : dist = -((-dist).toNat : Int) := by omega
              rw [hde, Int.neg_tmod] at hRem0
              have hm0 : (-dist).toNat % elemSize = 0 := by
                change -(((-dist).toNat % elemSize : Nat) : Int) = 0 at hRem0; omega
              have hGe : elemSize ≤ (-dist).toNat := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hm0)
              have hPosQ : (0 : Int) < (((-dist).toNat / elemSize : Nat) : Int) :=
                Int.ofNat_lt.mpr (Nat.div_pos hGe hElemPos)
              rw [hde, Int.neg_tdiv]
              change -(((-dist).toNat / elemSize : Nat) : Int) < 0
              omega
            have hModEq : Int.tmod dist (Int.ofNat elemSize) = 0 := hRem0
            simp only [hBadFalse, hElemCondF, hModEq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hQNeg]
            congr 1; rw [Int.add_comm]; rfl
          · simp only [h, ↓reduceIte] at hBadFalse ⊢
            have hNotNeg : ¬ (dist < 0) := decide_eq_false_iff_not.mp hBadFalse
            have hQNotNeg : ¬ (Int.tdiv dist (elemSize : Int) < 0) := by
              have hde : dist = (dist.toNat : Int) := by omega
              rw [hde]; change ¬ (((dist.toNat / elemSize : Nat) : Int) < 0)
              exact Int.not_lt.mpr (Int.natCast_nonneg _)
            have hModEq : Int.tmod dist (Int.ofNat elemSize) = 0 := hRem0
            simp only [hNotNeg, hElemCondF, hModEq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hQNotNeg]
            rfl
        · have hRemRng : -(2 ^ 63 : Int) < Int.tmod dist (elemSize : Int) ∧
              Int.tmod dist (elemSize : Int) < (2 ^ 63 : Int) := by
            by_cases hdn : dist < 0
            · have hde : dist = -((-dist).toNat : Int) := by omega
              rw [hde, Int.neg_tmod]
              have h1 : Int.tmod ((-dist).toNat : Int) (elemSize : Int) =
                  (((-dist).toNat % elemSize : Nat) : Int) := rfl
              rw [h1]
              have hlt := Nat.mod_lt (-dist).toNat hElemPos
              omega
            · have hde : dist = (dist.toNat : Int) := by omega
              rw [hde]
              have h1 : Int.tmod (dist.toNat : Int) (elemSize : Int) =
                  ((dist.toNat % elemSize : Nat) : Int) := rfl
              rw [h1]
              have hlt := Nat.mod_lt dist.toNat hElemPos
              omega
          have hRemNotNull : rSc.isNull = false := by
            change (rSc.data == (0 : Miri.ABI.U128)) = false
            rw [hRDat]
            apply beq_false_of_ne
            intro hEq
            have hNat := congrArg BitVec.toNat hEq
            have h0 : (0 : Miri.ABI.U128).toNat = 0 := rfl
            rw [BitVec.toNat_ofNat, h0] at hNat
            by_cases hrn : Int.tmod dist (elemSize : Int) < 0
            · simp only [hrn, ↓reduceIte] at hNat
              rw [Nat.mod_eq_of_lt (by omega)] at hNat; omega
            · simp only [hrn, ↓reduceIte] at hNat
              rw [Nat.mod_eq_of_lt (by omega)] at hNat; omega
          have hBneTrue : (Int.tmod dist (Int.ofNat elemSize) != 0) = true := by
            have hf : (Int.tmod dist (Int.ofNat elemSize) == 0) = false := beq_false_of_ne hRem0
            simp only [bne, hf, Bool.not_false]
          simp only [pure, Except.pure, hRemNotNull, Bool.not_false, ↓reduceIte, throw, throwThe, MonadExceptOf.throw]
          by_cases h : aOff.toNat < bOff.toNat
          · simp only [h, ↓reduceIte] at hBadFalse ⊢
            simp [hBadFalse, hElemCondF, hBneTrue, hRem0]
          · simp only [h, ↓reduceIte] at hBadFalse ⊢
            have hNotNeg : ¬ (dist < 0) := decide_eq_false_iff_not.mp hBadFalse
            simp [hNotNeg, hElemCondF, hBneTrue, hRem0]

/-- **Universal Trusted ↔ unmodified vendored `ptr_offset_from[_unsigned]`
correspondence**: for ALL `unsigned : Bool`, ALL `elemSize : Nat`, and ALL
64-bit offsets `aOff bOff : UInt64`, Trusted `evalPtrOffsetFromDistance 8` agrees
bit-for-bit with UNMODIFIED vendored `Miri.Interpreter.IntegerOps.binary .SubWithOverflow`
+ `ScalarInt.toTargetIsize` + `ScalarInt.tryFromInt` +
`Miri.Interpreter.IntegerArithmeticIntrinsic.exactDiv`. -/
theorem cm_evalPtrOffsetFromDistance_eq_vendored (unsigned : Bool) (elemSize : Nat)
    (aOff bOff : UInt64) :
    (evalPtrOffsetFromDistance 8 unsigned elemSize aOff.toNat bOff.toNat).map ScalarInt.bits =
      cmMiriPtrOffsetFromVendored unsigned elemSize aOff bOff := by
  rw [cm_miriPtrOffsetFromVendored_eq_spec]
  exact cm_evalPtrOffsetFromDistance_eq_miriSpec unsigned elemSize aOff bOff

private theorem cm_lm_bitwiseAndBits_testBit (k a b i : Nat) :
    (bitwiseAndBits k a b).testBit i = (decide (i < k) && a.testBit i && b.testBit i) := by
  induction k generalizing a b i with
  | zero => simp [bitwiseAndBits]
  | succ k ih =>
    have hbit :
        (match Bool.and (Nat.beq (Nat.mod a 2) 1) (Nat.beq (Nat.mod b 2) 1) with
         | true => 1 | false => 0) = if (a.testBit 0 && b.testBit 0) then 1 else 0 := by
      have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
      have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
      change (match Bool.and (Nat.beq (a % 2) 1) (Nat.beq (b % 2) 1) with
         | true => 1 | false => 0) = if (a.testBit 0 && b.testBit 0) then 1 else 0
      simp only [Nat.testBit_zero]
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> decide
    have hUnfold : bitwiseAndBits (k + 1) a b =
        (if (a.testBit 0 && b.testBit 0) then 1 else 0) + 2 * bitwiseAndBits k (a / 2) (b / 2) := by
      change (match Bool.and (Nat.beq (Nat.mod a 2) 1) (Nat.beq (Nat.mod b 2) 1) with
          | true => 1 | false => 0) + 2 * bitwiseAndBits k (a / 2) (b / 2) = _
      rw [hbit]
    rw [hUnfold]
    cases i with
    | zero =>
      have h0l : ((if (a.testBit 0 && b.testBit 0) then 1 else 0) +
          2 * bitwiseAndBits k (a / 2) (b / 2)).testBit 0 = (a.testBit 0 && b.testBit 0) := by
        cases (a.testBit 0 && b.testBit 0) <;> simp [Nat.testBit_zero]
      rw [h0l]; simp
    | succ j =>
      have hdiv : ((if (a.testBit 0 && b.testBit 0) then 1 else 0) +
          2 * bitwiseAndBits k (a / 2) (b / 2)) / 2 = bitwiseAndBits k (a / 2) (b / 2) := by
        cases a.testBit 0 && b.testBit 0 <;> simp <;> omega
      rw [Nat.testBit_succ, hdiv, ih (a / 2) (b / 2) j, Nat.testBit_succ, Nat.testBit_succ]
      simp [Nat.succ_lt_succ_iff]

/-- **Universal `ptr_mask` bit-operator correspondence**: Trusted
`bitwiseAndBits 64` equals unmodified vendored `UInt64.land` (`Intrinsics.lean:508`)
for EVERY `a b : UInt64`. -/
theorem cm_bitwiseAndBits_64_eq_u64_land (a b : UInt64) :
    bitwiseAndBits 64 a.toNat b.toNat = (UInt64.land a b).toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [cm_lm_bitwiseAndBits_testBit]
  have hland : (UInt64.land a b).toNat = a.toNat &&& b.toNat := by
    change (a.toBitVec &&& b.toBitVec).toNat = a.toBitVec.toNat &&& b.toBitVec.toNat
    exact BitVec.toNat_and a.toBitVec b.toBitVec
  rw [hland, Nat.testBit_and]
  by_cases hi : i < 64
  · simp [hi]
  · have hge : 64 ≤ i := Nat.le_of_not_lt hi
    have hlt : a.toNat < 2 ^ i := Nat.lt_of_lt_of_le a.toBitVec.isLt (Nat.pow_le_pow_right (by decide) hge)
    simp [hi, Nat.testBit_lt_two_pow hlt]

/-- **Universal `ptr_mask` `UInt64.land` base-address invariance** (`Intrinsics.lean:508`
vs. Trusted symbolic `evalPtrMaskCall`): for EVERY `2^m`-aligned base address
`baseAddr : UInt64`, relative offset `relOff : UInt64` with `baseAddr + relOff < 2^64`,
and mask `mask : UInt64` satisfying `(2^64 - 1) - mask.toNat < 2^m`, vendored
`UInt64.land (baseAddr + relOff) mask` equals `baseAddr + UInt64.land relOff mask`,
so subtracting `baseAddr` yields Trusted's exact symbolic offset
`bitwiseAndBits 64 relOff.toNat mask.toNat`. -/
theorem cm_miri_ptrMask_u64_baseAddr_invariant (baseAddr relOff mask : UInt64) (m : Nat)
    (hm : m ≤ 64) (hAlign : 2 ^ m ∣ baseAddr.toNat)
    (hSum : baseAddr.toNat + relOff.toNat < 2 ^ 64)
    (hInv : (2 ^ 64 - 1) - mask.toNat < 2 ^ m) :
    UInt64.land (baseAddr + relOff) mask = baseAddr + UInt64.land relOff mask ∧
    ((UInt64.land (baseAddr + relOff) mask) - baseAddr).toNat =
      bitwiseAndBits 64 relOff.toNat mask.toNat := by
  have h2mPos : 0 < 2 ^ m := Nat.pow_pos (by decide)
  rcases hAlign with ⟨q, hBase⟩
  have hAddNat : (baseAddr + relOff).toNat = baseAddr.toNat + relOff.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hSum]
  have hLandLe : (UInt64.land relOff mask).toNat ≤ relOff.toNat := by
    have h1 : (UInt64.land relOff mask).toNat = relOff.toNat &&& mask.toNat := by
      change (relOff.toBitVec &&& mask.toBitVec).toNat = relOff.toBitVec.toNat &&& mask.toBitVec.toNat
      exact BitVec.toNat_and relOff.toBitVec mask.toBitVec
    rw [h1]; exact Nat.and_le_left
  have hMaskHigh : ∀ i, m ≤ i → i < 64 → mask.toNat.testBit i = true := by
    intro i hmi hi64
    have hMaskLt : mask.toNat < 2 ^ 64 := mask.toBitVec.isLt
    have hmul : 2 ^ m * 2 ^ (64 - m) = 2 ^ 64 := by rw [← Nat.pow_add, Nat.add_sub_of_le hm]
    have h1 : (2 ^ (64 - m) - 1) * 2 ^ m = 2 ^ 64 - 2 ^ m := by
      rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm, hmul]
    have h2 : 2 ^ (64 - m) * 2 ^ m = 2 ^ 64 := by rw [Nat.mul_comm, hmul]
    have hPowPos : 0 < 2 ^ (64 - m) := Nat.pow_pos (by decide)
    have hGe : (2 ^ (64 - m) - 1) * 2 ^ m ≤ mask.toNat := by omega
    have hLt : mask.toNat < (2 ^ (64 - m) - 1 + 1) * 2 ^ m := by
      rw [Nat.sub_add_cancel hPowPos]; omega
    have hdiv : mask.toNat / 2 ^ m = 2 ^ (64 - m) - 1 := Nat.div_eq_of_lt_le hGe hLt
    have hsub : i = (i - m) + m := by omega
    rw [hsub, ← Nat.testBit_div_two_pow, hdiv, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true (by omega)
  have hNatEq : (UInt64.land (baseAddr + relOff) mask).toNat =
      baseAddr.toNat + (UInt64.land relOff mask).toNat := by
    rw [← cm_bitwiseAndBits_64_eq_u64_land, ← cm_bitwiseAndBits_64_eq_u64_land, hAddNat]
    have hSplit : ∀ x, x < 2 ^ 64 →
        bitwiseAndBits 64 x mask.toNat =
          2 ^ m * (x / 2 ^ m) + bitwiseAndBits m (x % 2 ^ m) (mask.toNat % 2 ^ m) := by
      intro x hx
      have hLowLt : bitwiseAndBits m (x % 2 ^ m) (mask.toNat % 2 ^ m) < 2 ^ m := by
        have : ∀ k a b, bitwiseAndBits k a b < 2 ^ k := by
          intro k; induction k with
          | zero => intro a b; simp [bitwiseAndBits]
          | succ k ih =>
            intro a b
            change (match Bool.and (Nat.beq (Nat.mod a 2) 1) (Nat.beq (Nat.mod b 2) 1) with
                | true => 1 | false => 0) + 2 * bitwiseAndBits k (a / 2) (b / 2) < 2 ^ (k + 1)
            have h1 : bitwiseAndBits k (a / 2) (b / 2) < 2 ^ k := ih (a / 2) (b / 2)
            cases Bool.and (Nat.beq (Nat.mod a 2) 1) (Nat.beq (Nat.mod b 2) 1)
            · change 0 + 2 * bitwiseAndBits k (a / 2) (b / 2) < 2 ^ (k + 1)
              rw [Nat.pow_succ]; omega
            · change 1 + 2 * bitwiseAndBits k (a / 2) (b / 2) < 2 ^ (k + 1)
              rw [Nat.pow_succ]; omega
        exact this m _ _
      apply Nat.eq_of_testBit_eq
      intro i
      rw [cm_lm_bitwiseAndBits_testBit, Nat.testBit_two_pow_mul_add _ hLowLt]
      by_cases him : i < m
      · have hi64 : i < 64 := Nat.lt_of_lt_of_le him hm
        simp only [him, ↓reduceIte, cm_lm_bitwiseAndBits_testBit, Nat.testBit_mod_two_pow, hi64,
          decide_true, Bool.true_and]
      · simp only [him, ↓reduceIte]
        have hmi : m ≤ i := Nat.le_of_not_lt him
        have hSubDiv : (x / 2 ^ m).testBit (i - m) = x.testBit i := by
          rw [Nat.testBit_div_two_pow, Nat.sub_add_cancel hmi]
        rw [hSubDiv]
        by_cases hi64 : i < 64
        · simp [hi64, hMaskHigh i hmi hi64]
        · have hlt : x < 2 ^ i := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hi64))
          simp [hi64, Nat.testBit_lt_two_pow hlt]
    rw [hBase] at hSum ⊢
    rw [hSplit (2 ^ m * q + relOff.toNat) hSum, hSplit relOff.toNat (by omega)]
    rw [Nat.mul_add_div h2mPos, Nat.mul_add_mod, Nat.mul_add, Nat.add_assoc]
  have hEq : UInt64.land (baseAddr + relOff) mask = baseAddr + UInt64.land relOff mask := by
    apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
    change (UInt64.land (baseAddr + relOff) mask).toNat = (baseAddr + UInt64.land relOff mask).toNat
    rw [hNatEq, UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hEq, ?_⟩
  rw [hEq, cm_bitwiseAndBits_64_eq_u64_land]
  have hSub : baseAddr + UInt64.land relOff mask - baseAddr = UInt64.land relOff mask := by
    apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
    change (baseAddr + UInt64.land relOff mask - baseAddr).toNat = (UInt64.land relOff mask).toNat
    rw [UInt64.toNat_sub_of_le]
    · rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega), Nat.add_sub_cancel_left]
    · rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
  rw [hSub]

private def cmLiftRes {S A : Type} (r : Except Miri.Interpreter.StepError A) :
    Miri.Interpreter.RvalueM S A :=
  match r with | .ok v => pure v | .error e => throw e

private def cmMirrorScalar {P S C V : Type} [Miri.Memory.PointerProvenance P]
    (h : Miri.Interpreter.IntrinsicHooks P S C V) (choice : C) (value : Miri.Interpreter.OpTy P) :
    Miri.Interpreter.RvalueM S (Miri.Memory.Scalar P) := do
  let immediate ← h.readImmediate choice value
  cmLiftRes (immediate.imm.toScalar |>.mapError Miri.Interpreter.ScalarOps.immediateError)

private def cmMirrorPointer {P S C V : Type} [Miri.Memory.PointerProvenance P]
    (h : Miri.Interpreter.IntrinsicHooks P S C V) (choice : C) (value : Miri.Interpreter.OpTy P) :
    Miri.Interpreter.RvalueM S (Miri.Memory.Pointer (Option P)) := do
  let sc ← cmMirrorScalar h choice value
  cmLiftRes (sc.toPointer h.target |>.mapError Miri.Interpreter.ScalarOps.scalarError)

private def cmMirrorUsize {P S C V : Type} [Miri.Memory.PointerProvenance P]
    (h : Miri.Interpreter.IntrinsicHooks P S C V) (choice : C) (value : Miri.Interpreter.OpTy P) :
    Miri.Interpreter.RvalueM S UInt64 := do
  let sc ← cmMirrorScalar h choice value
  cmLiftRes (sc.toTargetUsize (Miri.ABI.Size.fromBits h.target.pointerWidth.bits)
    |>.mapError Miri.Interpreter.ScalarOps.scalarError)

/-- **Universal vendored `Miri.Interpreter.Intrinsics.eval` step-simulation for `ptr_mask`**
(`Intrinsics.lean:504-508`): for EVERY `ld`, `ly`, `tb`, `tyArg`, concrete pointer
scalar `ptrSc` decoding to `ptr` (with arbitrary provenance `ptr.provenance` and
address `ptr.offset`), `mask : UInt64`, destination `dest`, successor `ret`, and
state `st`, calling unmodified vendored `Intrinsics.eval ... "ptr_mask"` preserves
`ptr.provenance` identically and writes
`{ ptr with offset := Size.ofBytes (UInt64.land ptr.offset.bytes mask) }` via
`annealWritePointer` followed by `annealReturnToBlock ret`. -/
theorem cm_miri_ptrMask_eval_universal (ld : List LocalDecl) (ly : LayoutTable) (tb : Bool)
    (tyArg : Miri.MIR.TyId) (ptrSc : Miri.Memory.Scalar AnnealProv)
    (ptr : Miri.Memory.Pointer (Option AnnealProv)) (mask : UInt64)
    (ptrLay maskLay : Miri.Interpreter.LocalLayout)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) (ret : Option Miri.MIR.BasicBlockId)
    (st : AnnealStepState)
    (hToPtr : ptrSc.toPointer annealTargetDataLayout = .ok ptr) :
    Miri.Interpreter.Intrinsics.eval (cmIntrinsicHooks ld ly tb tyArg) () "ptr_mask" #[]
      #[⟨.immediate (.scalar ptrSc), ptrLay⟩,
        ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 mask))), maskLay⟩] dest ret st =
      ((do
          annealWritePointer { ptr with offset := Miri.ABI.Size.ofBytes (UInt64.land ptr.offset.bytes mask) } dest
          annealReturnToBlock ret
          pure true) : LmM Bool) st := by
  have hMask : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) (.ofUInt64 mask)).toTargetUsize
      (Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits) = .ok mask := by
    have hMaskLt : mask.toNat < 2 ^ 64 := mask.toBitVec.isLt
    have hNotGt : ¬ (mask.toNat > 18446744073709551615) := by omega
    have hBitsEq : (BitVec.ofNat 128 mask.toNat).toNat = mask.toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hOfNat : UInt64.ofNat mask.toNat = mask := by
      apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
      change mask.toNat % 2 ^ 64 = mask.toNat
      exact Nat.mod_eq_of_lt hMaskLt
    change (if (BitVec.ofNat 128 mask.toNat).toNat > 18446744073709551615 then
        Except.error (Miri.Memory.ScalarError.integerConversionOverflow (BitVec.ofNat 128 mask.toNat))
      else Except.ok (UInt64.ofNat (BitVec.ofNat 128 mask.toNat).toNat)) = Except.ok mask
    rw [hBitsEq, hOfNat]
    simp only [hNotGt, ↓reduceIte]
  have hNA : ("ptr_mask".startsWith "atomic_") = false := by simp
  have hNS : ("ptr_mask".startsWith "simd_") = false := by simp
  have hEval :
      Miri.Interpreter.Intrinsics.eval (cmIntrinsicHooks ld ly tb tyArg) () "ptr_mask" #[]
        #[⟨.immediate (.scalar ptrSc), ptrLay⟩,
          ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 mask))), maskLay⟩] dest ret =
      ((do
          let p ← cmMirrorPointer (cmIntrinsicHooks ld ly tb tyArg) ()
            ⟨.immediate (.scalar ptrSc), ptrLay⟩
          let m ← cmMirrorUsize (cmIntrinsicHooks ld ly tb tyArg) ()
            ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 mask))), maskLay⟩
          annealWritePointer { p with offset := Miri.ABI.Size.ofBytes (UInt64.land p.offset.bytes m) } dest
          annealReturnToBlock ret
          pure true) : LmM Bool) := by
    unfold Miri.Interpreter.Intrinsics.eval
    simp only [hNA, hNS, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [hEval]
  simp only [cmMirrorPointer, cmMirrorUsize, cmMirrorScalar, cmLiftRes, cmIntrinsicHooks,
    annealIntrinsicHooks, annealReadImmediate, Miri.Interpreter.Immediate.toScalar,
    hToPtr, hMask, Except.mapError, bind, EStateM.bind, pure, EStateM.pure]

/-- **Universal vendored `Miri.Interpreter.Intrinsics.eval` step-simulation for `black_box`**
(`Intrinsics.lean:441`), for **ALL `tb : Bool`** (both `basic` and `protectedTB`)
on any non-memory destination `dest` (`∀ mp, dest.ref ≠ .memory mp`):
1. For EVERY valid immediate scalar/pointer `sc` (`!srcLay.layout.uninhabited` and
   `annealValidateScalarForTyId srcLay.ty sc = true`), `Intrinsics.eval ... "black_box"`
   preserves `sc` identically into `dest` and transitions to `ret`.
2. For EVERY invalid immediate scalar `sc` (`annealValidateScalarForTyId srcLay.ty sc = false`,
   e.g. `bool = 2`, surrogate `char`, null `&T`, null `fn()`, `!`),
   `Intrinsics.eval ... "black_box"` deterministically faults `.undefinedBehavior`. -/
theorem cm_miri_blackBox_eval_universal (ld : List LocalDecl) (ly : LayoutTable) (tb : Bool)
    (tyArg : Miri.MIR.TyId) (sc : Miri.Memory.Scalar AnnealProv)
    (srcLay : Miri.Interpreter.LocalLayout) (dest : Miri.Interpreter.RuntimePlace AnnealProv)
    (ret : Option Miri.MIR.BasicBlockId) (st : AnnealStepState)
    (hInh : srcLay.layout.uninhabited = false)
    (hDest : ∀ mp, dest.ref ≠ .memory mp) :
    (annealValidateScalarForTyId srcLay.ty sc = true →
      Miri.Interpreter.Intrinsics.eval (cmIntrinsicHooks ld ly tb tyArg) () "black_box" #[]
        #[⟨.immediate (.scalar sc), srcLay⟩] dest ret st =
      ((do annealWriteImmediate (.scalar sc) dest; annealReturnToBlock ret; pure true) : LmM Bool) st) ∧
    (annealValidateScalarForTyId srcLay.ty sc = false →
      Miri.Interpreter.Intrinsics.eval (cmIntrinsicHooks ld ly tb tyArg) () "black_box" #[]
        #[⟨.immediate (.scalar sc), srcLay⟩] dest ret st =
      .error (.undefinedBehavior "copyOp of invalid scalar value") st) := by
  have hNA : ("black_box".startsWith "atomic_") = false := by simp
  have hNS : ("black_box".startsWith "simd_") = false := by simp
  have hEval :
      Miri.Interpreter.Intrinsics.eval (cmIntrinsicHooks ld ly tb tyArg) () "black_box" #[]
        #[⟨.immediate (.scalar sc), srcLay⟩] dest ret =
      ((do cmCopyOp tb ⟨.immediate (.scalar sc), srcLay⟩ dest;
           annealReturnToBlock ret; pure true) : LmM Bool) := by
    unfold Miri.Interpreter.Intrinsics.eval
    simp only [hNA, hNS, Bool.false_eq_true, ↓reduceIte]
    rfl
  constructor
  · intro hVal
    rw [hEval]
    cases hRef : dest.ref with
    | memory mp => exact absurd hRef (hDest mp)
    | _ =>
      cases tb <;>
        simp [cmCopyOp, hInh, annealReadImmediate, hVal, hRef, bind, EStateM.bind, pure, EStateM.pure]
  · intro hInval
    rw [hEval]
    cases hRef : dest.ref with
    | memory mp => exact absurd hRef (hDest mp)
    | _ =>
      cases tb <;>
        simp [cmCopyOp, hInh, annealReadImmediate, hInval, hRef, bind, EStateM.bind, pure, EStateM.pure,
          throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- **Universal vendored `Miri.Interpreter.Intrinsics.copyWith` step-simulation**
(`Intrinsics.lean:143-158`): for ANY hooks `h`, proves BOTH:
1. When `IntegerOps.computeSizeInBytes` succeeds with `size`, `copyWith` aligns
   both pointers and delegates to `h.memCopy choice srcPtr dstPtr size nonov`;
2. When `IntegerOps.computeSizeInBytes` overflows (`none`), `copyWith`
   deterministically faults `.undefinedBehavior "overflow computing total size of copy"`. -/
theorem cm_miri_copyWith_eval_universal {P S C : Type} [Miri.Memory.PointerProvenance P]
    (h : Miri.Interpreter.MemoryIntrinsicHooks P S C) (choice : C)
    (srcOp dstOp cntOp : Miri.Interpreter.OpTy P) (nonov : Bool)
    (st0 st1 st2 st3 st4 st5 st6 st7 st8 : S)
    (cImm sImm dImm : Miri.Interpreter.RvalueImmTy P)
    (cSc sSc dSc : Miri.Memory.Scalar P) (count : UInt64)
    (ptTy : Miri.MIR.TyId) (ptLay : Miri.ABI.TyAndLayout Miri.MIR.TyId)
    (sPtr dPtr : Miri.Memory.Pointer (Option P))
    (hRdC : h.readImmediate choice cntOp st0 = .ok cImm st1)
    (hScC : cImm.imm.toScalar = .ok cSc)
    (hCnt : cSc.toTargetUsize (Miri.ABI.Size.fromBits h.target.pointerWidth.bits) = .ok count)
    (hPt : h.pointeeType choice srcOp.layout.ty st1 = .ok ptTy st2)
    (hLay : h.layoutOf choice ptTy st2 = .ok ptLay st3) :
    (∀ size,
      Miri.Interpreter.IntegerOps.computeSizeInBytes ptLay.layout.size count h.maxSizeOfVal = some size →
      h.readImmediate choice srcOp st3 = .ok sImm st4 →
      sImm.imm.toScalar = .ok sSc →
      sSc.toPointer h.target = .ok sPtr →
      h.readImmediate choice dstOp st4 = .ok dImm st5 →
      dImm.imm.toScalar = .ok dSc →
      dSc.toPointer h.target = .ok dPtr →
      h.checkAlign choice sPtr ptLay.layout.align.abi st5 = .ok () st6 →
      h.checkAlign choice dPtr ptLay.layout.align.abi st6 = .ok () st7 →
      h.memCopy choice sPtr dPtr size nonov st7 = .ok () st8 →
      Miri.Interpreter.Intrinsics.copyWith h choice srcOp dstOp cntOp nonov st0 = .ok () st8) ∧
    (Miri.Interpreter.IntegerOps.computeSizeInBytes ptLay.layout.size count h.maxSizeOfVal = none →
      Miri.Interpreter.Intrinsics.copyWith h choice srcOp dstOp cntOp nonov st0 =
        .error (.undefinedBehavior "overflow computing total size of copy") st3) := by
  have hCopy :
      Miri.Interpreter.Intrinsics.copyWith h choice srcOp dstOp cntOp nonov =
      (do
        let read := fun operand => do
          let value ← h.readImmediate choice operand
          cmLiftRes (value.imm.toScalar |>.mapError Miri.Interpreter.ScalarOps.immediateError)
        let count ← cmLiftRes ((← read cntOp).toTargetUsize
          (Miri.ABI.Size.fromBits h.target.pointerWidth.bits) |>.mapError Miri.Interpreter.ScalarOps.scalarError)
        let ty ← h.pointeeType choice srcOp.layout.ty
        let layout ← h.layoutOf choice ty
        let some size := Miri.Interpreter.IntegerOps.computeSizeInBytes layout.layout.size count h.maxSizeOfVal
          | throw (.undefinedBehavior "overflow computing total size of copy")
        let source ← cmLiftRes ((← read srcOp).toPointer h.target |>.mapError Miri.Interpreter.ScalarOps.scalarError)
        let dest ← cmLiftRes ((← read dstOp).toPointer h.target |>.mapError Miri.Interpreter.ScalarOps.scalarError)
        h.checkAlign choice source layout.layout.align.abi
        h.checkAlign choice dest layout.layout.align.abi
        h.memCopy choice source dest size nonov) := rfl
  constructor
  · intro size hMul hRdS hScS hPtrS hRdD hScD hPtrD hAlS hAlD hMem
    rw [hCopy]
    simp only [cmLiftRes, bind, EStateM.bind, pure, EStateM.pure, Except.mapError,
      hRdC, hScC, hCnt, hPt, hLay, hMul, hRdS, hScS, hPtrS, hRdD, hScD, hPtrD, hAlS, hAlD, hMem]
  · intro hOv
    rw [hCopy]
    simp only [cmLiftRes, bind, EStateM.bind, pure, EStateM.pure, Except.mapError,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw, hRdC, hScC, hCnt, hPt, hLay, hOv]

/-- **Universal vendored `Miri.Interpreter.Intrinsics.typedSwap` step-simulation**
(`Intrinsics.lean:199-214`): for ANY hooks `h`, traces the full vendored swap
(`derefPointer` left/right -> layout/sized check -> `allocateStack` -> `copyOp`
left→temp -> nonoverlapping `memCopy` right→left -> `validatePlace` when
`enforceValidity = true` -> `copyOp` temp→right -> `deallocateStack`). -/
theorem cm_miri_typedSwap_eval_universal {P S C V : Type} [Miri.Memory.PointerProvenance P]
    (h : Miri.Interpreter.IntrinsicHooks P S C V) (choice : C)
    (leftOp rightOp : Miri.Interpreter.OpTy P)
    (st0 st1 st2 st3 st4 st5 st6 st7 st8 st9 st10 st11 st12 : S)
    (leftP rightP tempP : V) (leftValOp tempValOp : Miri.Interpreter.OpTy P)
    (leftPtr rightPtr tempPtr : Miri.Memory.Pointer (Option P)) (recFlag : Bool)
    (hDerefL : h.derefPointer choice leftOp st0 = .ok leftP st1)
    (hDerefR : h.derefPointer choice rightOp st1 = .ok rightP st2)
    (hLayEq : h.destLayout leftP = h.destLayout rightP)
    (hSized : (h.destLayout leftP).layout.isSized = true)
    (hAlloc : h.allocateStack choice (h.destLayout leftP) st2 = .ok tempP st3)
    (hToOpL : h.placeToOp choice leftP st3 = .ok leftValOp st4)
    (hCopyL : h.copyOp choice leftValOp tempP st4 = .ok () st5)
    (hPtrR : h.placePointer rightP = .ok rightPtr)
    (hPtrL : h.placePointer leftP = .ok leftPtr)
    (hMem : h.memCopy choice rightPtr leftPtr (h.destLayout leftP).layout.size true st5 = .ok () st6)
    (hEnf : h.enforceValidity choice (h.destLayout leftP) st6 = .ok true st7)
    (hRec : h.enforceValidityRecursively choice (h.destLayout leftP) st7 = .ok recFlag st8)
    (hValP : h.validatePlace choice leftP recFlag true st8 = .ok () st9)
    (hToOpT : h.placeToOp choice tempP st9 = .ok tempValOp st10)
    (hCopyR : h.copyOp choice tempValOp rightP st10 = .ok () st11)
    (hPtrT : h.placePointer tempP = .ok tempPtr)
    (hDealloc : h.deallocateStack choice tempPtr st11 = .ok () st12) :
    Miri.Interpreter.Intrinsics.typedSwap h choice leftOp rightOp st0 = .ok () st12 := by
  have hSwap :
      Miri.Interpreter.Intrinsics.typedSwap h choice leftOp rightOp =
      (do
        let left ← h.derefPointer choice leftOp
        let right ← h.derefPointer choice rightOp
        let layout := h.destLayout left
        if layout != h.destLayout right || !layout.layout.isSized then
          throw (.invalidProgram "typed swap layout mismatch or unsized type")
        let temp ← h.allocateStack choice layout
        h.copyOp choice (← h.placeToOp choice left) temp
        let rightPtr ← cmLiftRes (h.placePointer right)
        let leftPtr ← cmLiftRes (h.placePointer left)
        h.memCopy choice rightPtr leftPtr layout.layout.size true
        if ← h.enforceValidity choice layout then
          let recursive ← h.enforceValidityRecursively choice layout
          h.validatePlace choice left recursive true
        h.copyOp choice (← h.placeToOp choice temp) right
        h.deallocateStack choice (← cmLiftRes (h.placePointer temp))) := rfl
  have hNe : (h.destLayout leftP != h.destLayout rightP) = false := by
    rw [hLayEq]; exact bne_self_eq_false _
  rw [hSwap]
  simp only [cmLiftRes, bind, EStateM.bind, pure, EStateM.pure,
    hDerefL, hDerefR, hNe, hSized, Bool.not_true, Bool.or_self,
    Bool.false_eq_true, ↓reduceIte, hAlloc, hToOpL, hCopyL, hPtrR, hPtrL, hMem,
    hEnf, hRec, hValP, hToOpT, hCopyR, hPtrT, hDealloc]

/-- **Universal vendored `Miri.Interpreter.Intrinsics.rawEq` step-simulation**
(`Intrinsics.lean:188-197`): for ANY hooks `h`, whenever pointee layout is sized,
both pointers align, and `readBytesStripProvenance` yields byte arrays `lBytes`
and `rBytes`, `Intrinsics.rawEq` returns `lBytes == rBytes`. -/
theorem cm_miri_rawEq_eval_universal {P S C V : Type} [Miri.Memory.PointerProvenance P]
    (h : Miri.Interpreter.IntrinsicHooks P S C V) (choice : C)
    (leftOp rightOp : Miri.Interpreter.OpTy P) (st0 st1 st2 st3 st4 st5 st6 st7 st8 : S)
    (ptTy : Miri.MIR.TyId) (ptLay : Miri.ABI.TyAndLayout Miri.MIR.TyId)
    (lImm rImm : Miri.Interpreter.RvalueImmTy P)
    (lSc rSc : Miri.Memory.Scalar P) (lPtr rPtr : Miri.Memory.Pointer (Option P))
    (lBytes rBytes : Array UInt8)
    (hPt : h.pointeeType choice leftOp.layout.ty st0 = .ok ptTy st1)
    (hLay : h.layoutOf choice ptTy st1 = .ok ptLay st2)
    (hSized : ptLay.layout.isSized = true)
    (hRdL : h.readImmediate choice leftOp st2 = .ok lImm st3)
    (hScL : lImm.imm.toScalar = .ok lSc)
    (hPtrL : lSc.toPointer h.target = .ok lPtr)
    (hAlL : h.checkAlign choice lPtr ptLay.layout.align.abi st3 = .ok () st4)
    (hBytesL : h.readBytesStripProvenance choice lPtr ptLay.layout.size st4 = .ok lBytes st5)
    (hRdR : h.readImmediate choice rightOp st5 = .ok rImm st6)
    (hScR : rImm.imm.toScalar = .ok rSc)
    (hPtrR : rSc.toPointer h.target = .ok rPtr)
    (hAlR : h.checkAlign choice rPtr ptLay.layout.align.abi st6 = .ok () st7)
    (hBytesR : h.readBytesStripProvenance choice rPtr ptLay.layout.size st7 = .ok rBytes st8) :
    Miri.Interpreter.Intrinsics.rawEq h choice leftOp rightOp st0 = .ok (lBytes == rBytes) st8 := by
  have hRaw :
      Miri.Interpreter.Intrinsics.rawEq h choice leftOp rightOp =
      (do
        let layout ← h.layoutOf choice (← h.pointeeType choice leftOp.layout.ty)
        if !layout.layout.isSized then throw (.invalidProgram "raw_eq requires sized pointee")
        let read := fun (op : Miri.Interpreter.OpTy P) => do
          let ptr ← cmMirrorPointer h choice op
          h.checkAlign choice ptr layout.layout.align.abi
          h.readBytesStripProvenance choice ptr layout.layout.size
        let left ← read leftOp
        let right ← read rightOp
        pure (left == right)) := rfl
  rw [hRaw]
  simp only [cmMirrorPointer, cmMirrorScalar, cmLiftRes, bind, EStateM.bind, pure, EStateM.pure,
    hPt, hLay, hSized, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hRdL, hScL, hPtrL, hAlL,
    hBytesL, hRdR, hScR, hPtrR, hAlR, hBytesR, Except.mapError]

section VendoredBytesCompare
open Lean Elab Term

/-- Elaborates to the UNMODIFIED vendored `private def bytesCompare`
(`Miri/Interpreter/Intrinsics.lean:174-176`), resolved by its exact private
name in the imported `Miri.Interpreter.Intrinsics` module (fails closed if the
vendored declaration is renamed or removed). -/
elab "cm_vendored_bytesCompare%" : term => do
  let n : Name :=
    (Name.mkNum (`_private ++ `Miri.Interpreter.Intrinsics) 0) ++ `Miri.Interpreter.Intrinsics.bytesCompare
  unless (← getEnv).contains n do
    throwError "vendored Miri.Interpreter.Intrinsics.bytesCompare not found ({n})"
  return mkConst n

end VendoredBytesCompare

/-- The unmodified vendored `Miri.Interpreter.Intrinsics.bytesCompare` itself
(a definitional alias of the private vendored constant, NOT a re-implementation). -/
def cmVendoredBytesCompare : List UInt8 → List UInt8 → Ordering := cm_vendored_bytesCompare%

/-- **Mirror faithfulness**: the documented mirror `cmMiriBytesCompare` IS the
unmodified vendored `bytesCompare`, for EVERY pair of byte lists. -/
theorem cmMiriBytesCompare_eq_vendored : cmMiriBytesCompare = cmVendoredBytesCompare := by
  funext l r
  induction l generalizing r with
  | nil => cases r <;> rfl
  | cons a as ih =>
    cases r with
    | nil => rfl
    | cons b bs =>
      have h1 : cmMiriBytesCompare (a :: as) (b :: bs) =
          if a == b then cmMiriBytesCompare as bs else compare a b := rfl
      have h2 : cmVendoredBytesCompare (a :: as) (b :: bs) =
          if a == b then cmVendoredBytesCompare as bs else compare a b := rfl
      rw [h1, h2, ih]

/-- The `Int32` result selected by vendored `Intrinsics.compareBytes`
(`Intrinsics.lean:186`). -/
def cmMiriOrderingI32 : Ordering → Int32
  | .lt => -1
  | .eq => 0
  | .gt => 1

/-- The vendored `Int32` result's 32-bit `ScalarInt` image has exactly the bit
pattern `cmMiriBytesCompareI32Bits` assigns to the same ordering. -/
theorem cm_miri_ofInt32_bits (o : Ordering) :
    (Miri.Memory.ScalarInt.ofInt32 (cmMiriOrderingI32 o)).data.toNat =
      (match o with | .lt => 4294967295 | .eq => 0 | .gt => 1) := by
  cases o <;> decide

/-- **Universal `compare_bytes` Trusted ↔ vendored bit correspondence**: for ALL
equal-length byte lists, the `ScalarInt` that UNMODIFIED vendored
`bytesCompare` + `Intrinsics.compareBytes` (`Intrinsics.lean:174-187`) produce
carries exactly Trusted's `compareUnsignedBytesI32 l r` bits. -/
theorem cm_compareUnsignedBytesI32_eq_vendored (l r : List UInt8) (hLen : l.length = r.length) :
    (Miri.Memory.ScalarInt.ofInt32 (cmMiriOrderingI32 (cmVendoredBytesCompare l r))).data.toNat =
      compareUnsignedBytesI32 l r := by
  rw [cm_compareUnsignedBytesI32_eq_miriBytesCompare l r hLen, ← cmMiriBytesCompare_eq_vendored,
    cm_miri_ofInt32_bits]
  unfold cmMiriBytesCompareI32Bits
  rfl

/-- **Universal vendored `Miri.Interpreter.Intrinsics.compareBytes` step-simulation**
(`Intrinsics.lean:178-187`): for ANY hooks `h`, whenever both pointer operands
and the count operand decode, and `readBytesStripProvenance` yields `lBytes` and
`rBytes` over `count` bytes, `Intrinsics.compareBytes` returns the `Int32`
scalar of the UNMODIFIED vendored `bytesCompare lBytes rBytes`. -/
theorem cm_miri_compareBytes_eval_universal {P S C V : Type} [Miri.Memory.PointerProvenance P]
    (h : Miri.Interpreter.IntrinsicHooks P S C V) (choice : C)
    (leftOp rightOp countOp : Miri.Interpreter.OpTy P) (st0 st1 st2 st3 st4 st5 : S)
    (lImm rImm cImm : Miri.Interpreter.RvalueImmTy P)
    (lSc rSc cSc : Miri.Memory.Scalar P) (lPtr rPtr : Miri.Memory.Pointer (Option P))
    (count : UInt64) (lBytes rBytes : Array UInt8)
    (hRdL : h.readImmediate choice leftOp st0 = .ok lImm st1)
    (hScL : lImm.imm.toScalar = .ok lSc)
    (hPtrL : lSc.toPointer h.target = .ok lPtr)
    (hRdR : h.readImmediate choice rightOp st1 = .ok rImm st2)
    (hScR : rImm.imm.toScalar = .ok rSc)
    (hPtrR : rSc.toPointer h.target = .ok rPtr)
    (hRdC : h.readImmediate choice countOp st2 = .ok cImm st3)
    (hScC : cImm.imm.toScalar = .ok cSc)
    (hUsize : cSc.toTargetUsize (Miri.ABI.Size.fromBits h.target.pointerWidth.bits) = .ok count)
    (hBytesL : h.readBytesStripProvenance choice lPtr (Miri.ABI.Size.ofBytes count) st3 = .ok lBytes st4)
    (hBytesR : h.readBytesStripProvenance choice rPtr (Miri.ABI.Size.ofBytes count) st4 = .ok rBytes st5) :
    Miri.Interpreter.Intrinsics.compareBytes h choice leftOp rightOp countOp st0 =
      .ok (.fromScalarInt (.ofInt32 (cmMiriOrderingI32
        (cmVendoredBytesCompare lBytes.toList rBytes.toList)))) st5 := by
  have hCmp :
      Miri.Interpreter.Intrinsics.compareBytes h choice leftOp rightOp countOp =
      (do
        let left ← cmMirrorPointer h choice leftOp
        let right ← cmMirrorPointer h choice rightOp
        let count := Miri.ABI.Size.ofBytes (← cmMirrorUsize h choice countOp)
        let left ← h.readBytesStripProvenance choice left count
        let right ← h.readBytesStripProvenance choice right count
        pure (.fromScalarInt (.ofInt32 (cmMiriOrderingI32
          (cmVendoredBytesCompare left.toList right.toList))))) := rfl
  rw [hCmp]
  simp only [cmMirrorPointer, cmMirrorUsize, cmMirrorScalar, cmLiftRes, bind, EStateM.bind, pure,
    EStateM.pure, hRdL, hScL, hPtrL, hRdR, hScR, hPtrR, hRdC, hScC, hUsize, hBytesL, hBytesR,
    Except.mapError]

private theorem cm_miri_ofUInt64_toTargetUsize (u : UInt64) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) (.ofUInt64 u)).toTargetUsize
      (Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits) = .ok u := by
  have hLt : u.toNat < 2 ^ 64 := u.toBitVec.isLt
  have hNotGt : ¬ (u.toNat > 18446744073709551615) := by omega
  have hBitsEq : (BitVec.ofNat 128 u.toNat).toNat = u.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hOfNat : UInt64.ofNat u.toNat = u := by
    apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
    change u.toNat % 2 ^ 64 = u.toNat
    exact Nat.mod_eq_of_lt hLt
  change (if (BitVec.ofNat 128 u.toNat).toNat > 18446744073709551615 then
      Except.error (Miri.Memory.ScalarError.integerConversionOverflow (BitVec.ofNat 128 u.toNat))
    else Except.ok (UInt64.ofNat (BitVec.ofNat 128 u.toNat).toNat)) = Except.ok u
  rw [hBitsEq, hOfNat]
  simp only [hNotGt, ↓reduceIte]

/-- **Concrete `cmIntrinsicHooks`-instantiated `compare_bytes` universal
Trusted ↔ vendored correspondence**: for ALL `ld`, `ly`, `tb`, `tyArg`, pointer
scalars `lSc`/`rSc`, `count : UInt64`, and equal-length `lBytes`/`rBytes` read
via `cmReadBytesStripProvenance tb`, unmodified vendored
`Miri.Interpreter.Intrinsics.compareBytes (cmIntrinsicHooks ld ly tb tyArg) ()`
returns a 32-bit `ScalarInt` whose bit pattern equals Trusted's
`compareUnsignedBytesI32 lBytes.toList rBytes.toList`. -/
theorem cm_miri_compareBytes_cmHooks_universal (ld : List LocalDecl) (ly : LayoutTable)
    (tb : Bool) (tyArg : Miri.MIR.TyId)
    (lSc rSc : Miri.Memory.Scalar AnnealProv) (lPtr rPtr : Miri.Memory.Pointer (Option AnnealProv))
    (count : UInt64) (lLay rLay cLay : Miri.Interpreter.LocalLayout)
    (st0 st1 st2 : AnnealStepState) (lBytes rBytes : Array UInt8)
    (hPtrL : lSc.toPointer annealTargetDataLayout = .ok lPtr)
    (hPtrR : rSc.toPointer annealTargetDataLayout = .ok rPtr)
    (hRdL : cmReadBytesStripProvenance tb lPtr (Miri.ABI.Size.ofBytes count) st0 = .ok lBytes st1)
    (hRdR : cmReadBytesStripProvenance tb rPtr (Miri.ABI.Size.ofBytes count) st1 = .ok rBytes st2)
    (hLen : lBytes.size = rBytes.size) :
    let qSc := Miri.Memory.ScalarInt.ofInt32 (cmMiriOrderingI32
      (cmVendoredBytesCompare lBytes.toList rBytes.toList))
    Miri.Interpreter.Intrinsics.compareBytes (cmIntrinsicHooks ld ly tb tyArg) ()
      ⟨.immediate (.scalar lSc), lLay⟩ ⟨.immediate (.scalar rSc), rLay⟩
      ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 count))), cLay⟩ st0 =
      .ok (.fromScalarInt qSc) st2 ∧
    qSc.data.toNat = compareUnsignedBytesI32 lBytes.toList rBytes.toList := by
  refine ⟨?_, cm_compareUnsignedBytesI32_eq_vendored lBytes.toList rBytes.toList hLen⟩
  exact cm_miri_compareBytes_eval_universal (cmIntrinsicHooks ld ly tb tyArg) ()
    ⟨.immediate (.scalar lSc), lLay⟩ ⟨.immediate (.scalar rSc), rLay⟩
    ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 count))), cLay⟩
    st0 st0 st0 st0 st1 st2
    ⟨.scalar lSc, lLay⟩ ⟨.scalar rSc, rLay⟩ ⟨.scalar (.fromScalarInt (.ofUInt64 count)), cLay⟩
    lSc rSc (.fromScalarInt (.ofUInt64 count)) lPtr rPtr count lBytes rBytes
    rfl rfl hPtrL rfl rfl hPtrR rfl rfl (cm_miri_ofUInt64_toTargetUsize count) hRdL hRdR

/-- **Concrete `cmIntrinsicHooks`-instantiated `raw_eq` universal Trusted ↔
vendored correspondence**: for ALL `ld`, `ly`, `tb`, `tyArg`, sized pointee
type `ptTy`, aligned pointers `lPtr`/`rPtr` whose `cmReadBytesStripProvenance tb`
reads `lBytes`/`rBytes`, unmodified vendored
`Miri.Interpreter.Intrinsics.rawEq (cmIntrinsicHooks ld ly tb tyArg) ()` returns
`lBytes == rBytes`, which equals Trusted's initialized bytewise equality
`lBytes.toList.map some == rBytes.toList.map some`. -/
theorem cm_miri_rawEq_cmHooks_universal (ld : List LocalDecl) (ly : LayoutTable)
    (tb : Bool) (tyArg : Miri.MIR.TyId)
    (lSc rSc : Miri.Memory.Scalar AnnealProv) (lPtr rPtr : Miri.Memory.Pointer (Option AnnealProv))
    (lLay rLay : Miri.Interpreter.LocalLayout) (ptTy : Miri.MIR.TyId)
    (ptLay : Miri.ABI.TyAndLayout Miri.MIR.TyId) (st0 st1 st2 : AnnealStepState)
    (lBytes rBytes : Array UInt8)
    (hPt : (cmIntrinsicHooks ld ly tb tyArg).pointeeType () lLay.ty st0 = .ok ptTy st0)
    (hLay : (cmIntrinsicHooks ld ly tb tyArg).layoutOf () ptTy st0 = .ok ptLay st0)
    (hSized : ptLay.layout.isSized = true)
    (hPtrL : lSc.toPointer annealTargetDataLayout = .ok lPtr)
    (hAlL : (cmIntrinsicHooks ld ly tb tyArg).checkAlign () lPtr ptLay.layout.align.abi st0 = .ok () st0)
    (hRdL : cmReadBytesStripProvenance tb lPtr ptLay.layout.size st0 = .ok lBytes st1)
    (hPtrR : rSc.toPointer annealTargetDataLayout = .ok rPtr)
    (hAlR : (cmIntrinsicHooks ld ly tb tyArg).checkAlign () rPtr ptLay.layout.align.abi st1 = .ok () st1)
    (hRdR : cmReadBytesStripProvenance tb rPtr ptLay.layout.size st1 = .ok rBytes st2) :
    Miri.Interpreter.Intrinsics.rawEq (cmIntrinsicHooks ld ly tb tyArg) ()
      ⟨.immediate (.scalar lSc), lLay⟩ ⟨.immediate (.scalar rSc), rLay⟩ st0 =
      .ok (lBytes == rBytes) st2 ∧
    (lBytes == rBytes) = (lBytes.toList.map Option.some == rBytes.toList.map Option.some) := by
  refine ⟨?_, ?_⟩
  · exact cm_miri_rawEq_eval_universal (cmIntrinsicHooks ld ly tb tyArg) ()
      ⟨.immediate (.scalar lSc), lLay⟩ ⟨.immediate (.scalar rSc), rLay⟩
      st0 st0 st0 st0 st0 st1 st1 st1 st2 ptTy ptLay
      ⟨.scalar lSc, lLay⟩ ⟨.scalar rSc, rLay⟩ lSc rSc lPtr rPtr lBytes rBytes
      hPt hLay hSized rfl rfl hPtrL hAlL hRdL rfl rfl hPtrR hAlR hRdR
  · cases hEq : (lBytes == rBytes) with
    | true =>
      have hArr : lBytes = rBytes := eq_of_beq hEq
      subst hArr; simp
    | false =>
      symm
      apply beq_false_of_ne
      intro hMap
      have hMapInj : ∀ (a b : List UInt8), a.map Option.some = b.map Option.some → a = b := by
        intro a; induction a with
        | nil => intro b hb; cases b with | nil => rfl | cons _ _ => cases hb
        | cons x xs ih =>
          intro b hb; cases b with
          | nil => cases hb
          | cons y ys =>
            simp only [List.map_cons, List.cons.injEq, Option.some.injEq] at hb
            rw [hb.1, ih ys hb.2]
      have hList : lBytes.toList = rBytes.toList := hMapInj lBytes.toList rBytes.toList hMap
      have hArr : lBytes = rBytes := Array.ext' hList
      subst hArr
      simp at hEq

/-- **Concrete `cmIntrinsicHooks`-instantiated `copy` universal zero-count &
overflow-UB laws**:
1. At `count = 0`, for ANY aligned pointers `sPtr`/`dPtr` (including NULL
   `offset = 0, provenance = none`), unmodified vendored
   `Miri.Interpreter.Intrinsics.copy (cmIntrinsicHooks ld ly tb tyArg)`
   (= `copyWith (cmIntrinsicHooks ld ly tb tyArg).memory`) computes `size = 0`
   and succeeds via `cmMemCopy tb sPtr dPtr (Size.ofBytes 0) nonov`;
2. Whenever `ptLay.layout.size.bytes.toNat * count.toNat` overflows `u64` or
   exceeds `maxSizeOfVal`, `copy` deterministically faults
   `.undefinedBehavior "overflow computing total size of copy"`. -/
theorem cm_miri_copyWith_cmHooks_zero_count_and_overflow_universal (ld : List LocalDecl)
    (ly : LayoutTable) (tb : Bool) (tyArg : Miri.MIR.TyId) (nonov : Bool)
    (sSc dSc : Miri.Memory.Scalar AnnealProv) (sPtr dPtr : Miri.Memory.Pointer (Option AnnealProv))
    (sLay dLay cLay : Miri.Interpreter.LocalLayout) (ptTy : Miri.MIR.TyId)
    (ptLay : Miri.ABI.TyAndLayout Miri.MIR.TyId) (st0 st1 : AnnealStepState)
    (hPt : (cmIntrinsicHooks ld ly tb tyArg).pointeeType () sLay.ty st0 = .ok ptTy st0)
    (hLay : (cmIntrinsicHooks ld ly tb tyArg).layoutOf () ptTy st0 = .ok ptLay st0) :
    (sSc.toPointer annealTargetDataLayout = .ok sPtr →
     dSc.toPointer annealTargetDataLayout = .ok dPtr →
     (cmIntrinsicHooks ld ly tb tyArg).checkAlign () sPtr ptLay.layout.align.abi st0 = .ok () st0 →
     (cmIntrinsicHooks ld ly tb tyArg).checkAlign () dPtr ptLay.layout.align.abi st0 = .ok () st0 →
     cmMemCopy tb sPtr dPtr (Miri.ABI.Size.ofBytes 0) nonov st0 = .ok () st1 →
     Miri.Interpreter.Intrinsics.copy (cmIntrinsicHooks ld ly tb tyArg) ()
       ⟨.immediate (.scalar sSc), sLay⟩ ⟨.immediate (.scalar dSc), dLay⟩
       ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 0))), cLay⟩ nonov st0 = .ok () st1) ∧
    (∀ count : UInt64,
     (ptLay.layout.size.bytes.toNat * count.toNat ≥ 2 ^ 64 ∨
      ptLay.layout.size.bytes.toNat * count.toNat >
        (cmIntrinsicHooks ld ly tb tyArg).memory.maxSizeOfVal.bytes.toNat) →
     Miri.Interpreter.Intrinsics.copy (cmIntrinsicHooks ld ly tb tyArg) ()
       ⟨.immediate (.scalar sSc), sLay⟩ ⟨.immediate (.scalar dSc), dLay⟩
       ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 count))), cLay⟩ nonov st0 =
       .error (.undefinedBehavior "overflow computing total size of copy") st0) := by
  constructor
  · intro hPtrS hPtrD hAlS hAlD hMem
    have hMul0 : Miri.Interpreter.IntegerOps.computeSizeInBytes ptLay.layout.size 0
        (cmIntrinsicHooks ld ly tb tyArg).memory.maxSizeOfVal =
        some (Miri.ABI.Size.ofBytes 0) := by
      unfold Miri.Interpreter.IntegerOps.computeSizeInBytes
      have h0 : ptLay.layout.size.bytes.toNat * (0 : UInt64).toNat = 0 := Nat.mul_zero _
      rw [h0]
      simp only [show (0 : Nat) < 2 ^ 64 by decide, decide_true, Nat.zero_le, Bool.and_self, ↓reduceIte]
      rfl
    exact (cm_miri_copyWith_eval_universal (cmIntrinsicHooks ld ly tb tyArg).memory ()
      ⟨.immediate (.scalar sSc), sLay⟩ ⟨.immediate (.scalar dSc), dLay⟩
      ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 0))), cLay⟩ nonov
      st0 st0 st0 st0 st0 st0 st0 st0 st1
      ⟨.scalar (.fromScalarInt (.ofUInt64 0)), cLay⟩ ⟨.scalar sSc, sLay⟩ ⟨.scalar dSc, dLay⟩
      (.fromScalarInt (.ofUInt64 0)) sSc dSc 0 ptTy ptLay sPtr dPtr
      rfl rfl (cm_miri_ofUInt64_toTargetUsize 0) hPt hLay).1
      (Miri.ABI.Size.ofBytes 0) hMul0 rfl rfl hPtrS rfl rfl hPtrD hAlS hAlD hMem
  · intro count hOv
    have hNone : Miri.Interpreter.IntegerOps.computeSizeInBytes ptLay.layout.size count
        (cmIntrinsicHooks ld ly tb tyArg).memory.maxSizeOfVal = none := by
      unfold Miri.Interpreter.IntegerOps.computeSizeInBytes
      have hF : (decide (ptLay.layout.size.bytes.toNat * count.toNat < 2 ^ 64) &&
          decide (ptLay.layout.size.bytes.toNat * count.toNat ≤
            (cmIntrinsicHooks ld ly tb tyArg).memory.maxSizeOfVal.bytes.toNat)) = false := by
        rcases hOv with h | h
        · have h1 : ¬ (ptLay.layout.size.bytes.toNat * count.toNat < 2 ^ 64) := by omega
          simp only [h1, decide_false, Bool.false_and]
        · have h2 : ¬ (ptLay.layout.size.bytes.toNat * count.toNat ≤
              (cmIntrinsicHooks ld ly tb tyArg).memory.maxSizeOfVal.bytes.toNat) := by omega
          simp only [h2, decide_false, Bool.and_false]
      simp only [hF, Bool.false_eq_true, ↓reduceIte]
    exact (cm_miri_copyWith_eval_universal (cmIntrinsicHooks ld ly tb tyArg).memory ()
      ⟨.immediate (.scalar sSc), sLay⟩ ⟨.immediate (.scalar dSc), dLay⟩
      ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 count))), cLay⟩ nonov
      st0 st0 st0 st0 st0 st0 st0 st0 st1
      ⟨.scalar (.fromScalarInt (.ofUInt64 count)), cLay⟩ ⟨.scalar sSc, sLay⟩ ⟨.scalar dSc, dLay⟩
      (.fromScalarInt (.ofUInt64 count)) sSc dSc count ptTy ptLay sPtr dPtr
      rfl rfl (cm_miri_ofUInt64_toTargetUsize count) hPt hLay).2 hNone

/-- **Concrete `cmIntrinsicHooks`-instantiated `typedSwap` & `validatePlace`
universal laws**:
1. Instantiates unmodified vendored `Miri.Interpreter.Intrinsics.typedSwap`
   directly on `cmIntrinsicHooks ld ly tb tyArg` (`cmDerefPointer`,
   `cmAllocateStack`, `cmCopyOp`, `cmMemCopy`, `validatePlace`,
   `cmDeallocateStack`);
2. Proves `(cmIntrinsicHooks ld ly tb tyArg).validatePlace` universally rejects
   BOTH uninhabited layouts AND invalid scalars (`annealValidateScalarForTyId = false`)
   with `.undefinedBehavior` (preventing any regression of the `right`-hand
   invalid-scalar swap defect). -/
theorem cm_miri_typedSwap_and_validatePlace_cmHooks_universal (ld : List LocalDecl)
    (ly : LayoutTable) (tb : Bool) (tyArg : Miri.MIR.TyId) :
    (∀ (mp : Miri.Interpreter.MemPlace AnnealProv) (lay : Miri.Interpreter.LocalLayout)
       (recFlag isWrite : Bool) (st : AnnealStepState),
      (lay.layout.uninhabited = true →
        (cmIntrinsicHooks ld ly tb tyArg).validatePlace () ⟨.memory mp, lay⟩ recFlag isWrite st =
          .error (.undefinedBehavior "validatePlace of uninhabited type") st) ∧
      (∀ (sc : Miri.Memory.Scalar AnnealProv) (st1 : AnnealStepState),
        lay.layout.uninhabited = false →
        annealReadImmediate ⟨.indirect mp, lay⟩ st = .ok ⟨.scalar sc, lay⟩ st1 →
        annealValidateScalarForTyId lay.ty sc = false →
        (cmIntrinsicHooks ld ly tb tyArg).validatePlace () ⟨.memory mp, lay⟩ recFlag isWrite st =
          .error (.undefinedBehavior "validatePlace of invalid scalar value") st1)) ∧
    (∀ (leftOp rightOp : Miri.Interpreter.OpTy AnnealProv)
       (st0 st1 st2 st3 st4 st5 st6 st7 st8 st9 st10 st11 st12 : AnnealStepState)
       (leftP rightP tempP : Miri.Interpreter.RuntimePlace AnnealProv)
       (leftValOp tempValOp : Miri.Interpreter.OpTy AnnealProv)
       (leftPtr rightPtr tempPtr : Miri.Memory.Pointer (Option AnnealProv)) (recFlag : Bool),
      cmDerefPointer tyArg ly leftOp st0 = .ok leftP st1 →
      cmDerefPointer tyArg ly rightOp st1 = .ok rightP st2 →
      leftP.layout = rightP.layout →
      leftP.layout.layout.isSized = true →
      cmAllocateStack leftP.layout st2 = .ok tempP st3 →
      (cmIntrinsicHooks ld ly tb tyArg).placeToOp () leftP st3 = .ok leftValOp st4 →
      cmCopyOp tb leftValOp tempP st4 = .ok () st5 →
      (cmIntrinsicHooks ld ly tb tyArg).placePointer rightP = .ok rightPtr →
      (cmIntrinsicHooks ld ly tb tyArg).placePointer leftP = .ok leftPtr →
      cmMemCopy tb rightPtr leftPtr leftP.layout.layout.size true st5 = .ok () st6 →
      (cmIntrinsicHooks ld ly tb tyArg).enforceValidity () leftP.layout st6 = .ok true st7 →
      (cmIntrinsicHooks ld ly tb tyArg).enforceValidityRecursively () leftP.layout st7 = .ok recFlag st8 →
      (cmIntrinsicHooks ld ly tb tyArg).validatePlace () leftP recFlag true st8 = .ok () st9 →
      (cmIntrinsicHooks ld ly tb tyArg).placeToOp () tempP st9 = .ok tempValOp st10 →
      cmCopyOp tb tempValOp rightP st10 = .ok () st11 →
      (cmIntrinsicHooks ld ly tb tyArg).placePointer tempP = .ok tempPtr →
      cmDeallocateStack tempPtr st11 = .ok () st12 →
      Miri.Interpreter.Intrinsics.typedSwap (cmIntrinsicHooks ld ly tb tyArg) () leftOp rightOp st0 =
        .ok () st12) := by
  constructor
  · intro mp lay recFlag isWrite st
    constructor
    · intro hUninh
      simp [cmIntrinsicHooks, hUninh, bind, EStateM.bind,
        throw, throwThe, MonadExceptOf.throw, EStateM.throw]
    · intro sc st1 hInh hRd hInval
      simp [cmIntrinsicHooks, hInh, hRd, hInval, bind, EStateM.bind,
        throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  · intro leftOp rightOp st0 st1 st2 st3 st4 st5 st6 st7 st8 st9 st10 st11 st12
      leftP rightP tempP leftValOp tempValOp leftPtr rightPtr tempPtr recFlag
      hDL hDR hLayEq hSized hAlloc hToL hCopyL hPtrR hPtrL hMem hEnf hRec hValP hToT hCopyR hPtrT hDealloc
    exact cm_miri_typedSwap_eval_universal (cmIntrinsicHooks ld ly tb tyArg) () leftOp rightOp
      st0 st1 st2 st3 st4 st5 st6 st7 st8 st9 st10 st11 st12
      leftP rightP tempP leftValOp tempValOp leftPtr rightPtr tempPtr recFlag
      hDL hDR hLayEq hSized hAlloc hToL hCopyL hPtrR hPtrL hMem hEnf hRec hValP hToT hCopyR hPtrT hDealloc

/-! ## §3. LeanMiri Observations, States, and the Corpus Observation (`cmLmObserve`) -/

/-- Normalized observation of a vendored `Miri.Interpreter.Step.step` run: the
returned `_0` scalar (`bits`, width) or thin pointer (allocation id, absolute
address), or the fault class. -/
inductive CmLmObs : Type where
  | scalar (bits size : Nat)
  | ptr (allocId addr : Nat)
  | ub
  | unsupported
  deriving DecidableEq, Repr

/-- Decode a vendored scalar. -/
def cmDecodeScalar (sc : Miri.Memory.Scalar AnnealProv) : CmLmObs :=
  if sc.isPointer then
    match sc.toPointer annealTargetDataLayout with
    | .ok p =>
      match p.provenance with
      | some (.concrete aid _) => .ptr aid.value.toNat p.offset.bytes.toNat
      | _ => .unsupported
    | .error _ => .unsupported
  else
    match sc.toScalarInt with
    | .ok msc => .scalar msc.data.toNat msc.size.bytes.toNat
    | .error _ => .unsupported

/-- Decode a `runMiriSteps` result. -/
def cmToObs (res : Except Miri.Interpreter.StepError
    (AnnealStepState × Option (Miri.Interpreter.LocalValue AnnealProv))) : CmLmObs :=
  match res with
  | .ok (_, some (.live (.immediate (.scalar sc)))) => cmDecodeScalar sc
  | .ok _ => .unsupported
  | .error (.undefinedBehavior _) => .ub
  | .error _ => .unsupported

/-- Initial vendored step state running `cmTranslateBody body`. -/
def cmMkState (body : CapturedMir) (retTy : Ty)
    (locs : Array (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout))
    (mach : AnnealMachine) : AnnealStepState :=
  { stack := { frames := #[{
      body := cmTranslateBody body,
      bodyIdentity := .ofCanonicalIndex 0,
      functionInstance := { kind := .Item 0, args := #[] },
      extra := (), returnContinuation := .stop false,
      returnPlace := .frameLocal 0 0 none (translateTyOverlay retTy body.layouts) (.ofAllocationToken 0),
      localsIdentity := .ofAllocationToken 0, locals := locs, vaList := #[],
      trackCallerArg := none, location := .mir ⟨0, 0⟩ }] },
    machine := mach }

/-- A non-zero vendored allocation id. -/
def cmAid (n : Nat) (h : UInt64.ofNat n ≠ 0 := by decide) : Miri.Memory.AllocId := ⟨UInt64.ofNat n, h⟩

/-- Allocations `100` (base `1024`), `101` (base `1088`), `102` (base `2048`),
`103` (base `2112`): the counterparts of the Trusted globals of the same ids. -/
def cmA100 : Miri.Memory.AllocId := cmAid 100
def cmA101 : Miri.Memory.AllocId := cmAid 101
def cmA102 : Miri.Memory.AllocId := cmAid 102
def cmA103 : Miri.Memory.AllocId := cmAid 103

/-- A pointer scalar with concrete provenance `aid` at absolute address `addr`. -/
def cmPtrSc (a : Miri.Memory.AllocId) (addr : UInt64) (tag : Miri.Memory.BorTag := .one) :
    Miri.Memory.Scalar AnnealProv :=
  Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨Miri.ABI.Size.ofBytes addr, .concrete a tag⟩

/-- A provenance-free pointer-width integer scalar. -/
def cmIntSc (bits : Nat) (sz : UInt64 := 8) : Miri.Memory.Scalar AnnealProv :=
  match Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 bits) (Miri.ABI.Size.ofBytes sz) with
  | .ok s => s
  | .error _ => Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨.ZERO, .wildcard⟩

def cmUninitLoc (ty : Ty) (ly : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
  ⟨.live (.immediate .uninit), some (translateTyOverlay ty ly)⟩

def cmScLoc (sc : Miri.Memory.Scalar AnnealProv) (ty : Ty) (ly : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
  ⟨.live (.immediate (.scalar sc)), some (translateTyOverlay ty ly)⟩

private def cmExtractOk {ε α : Type} : (r : Except ε α) → r.isOk = true → α
  | .ok a, _ => a
  | .error _, h => nomatch h

/-- The empty allocation (fallback of `cmAlloc`). -/
def cmEmptyAlloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  (cmExtractOk (Miri.Memory.Allocation.tryNew (Prov := AnnealProv) (Miri.ABI.Size.ofBytes 0) ⟨0⟩ .Uninit
    (fun _ _ => some #[])) (by decide +kernel)).withExtra none

/-- A mutable allocation with the given bytes (`none` = uninitialized) and
alignment `2 ^ alignLog`, built with vendored `Allocation.fromBytes` and
`Allocation.writeUninit`. -/
def cmAlloc (bytes : List (Option UInt8)) (alignLog : Nat) :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  match Miri.Memory.Allocation.fromBytes (Prov := AnnealProv) (bytes.map (·.getD 0)).toArray ⟨alignLog⟩ .Mut with
  | .ok al =>
    (List.range bytes.length).foldl (fun acc i =>
      match bytes[i]? with
      | some none =>
        match Miri.Memory.Allocation.writeUninit
            (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat i)) (Miri.ABI.Size.ofBytes 1))
            (Miri.ABI.Size.ofBytes 8) acc with
        | .ok () a' => a'
        | .error _ _ => acc
      | _ => acc) (al.withExtra none)
  | .error _ => cmEmptyAlloc

/-- A machine whose live allocations are `allocs` at the given base addresses. -/
def cmMach (allocs : List (Miri.Memory.AllocId × UInt64 ×
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)))
    (tracker : Option Miri.Interpreter.MachineHooks.BorrowState := none) : AnnealMachine :=
  { memory := { AnnealMachine.empty.memory with live := (allocs.map fun (a, _, al) => (a, ⟨.stack, al⟩)).toArray },
    addresses := { AnnealMachine.empty.addresses with baseAddr := (allocs.map fun (a, b, _) => ⟨a, b⟩).toArray },
    borrowTracker := tracker }

def cmBytesOf (c : CapturedMir) (aid : Nat) : List (Option UInt8) :=
  match c.allocations.find? (fun g => g.allocId == aid) with
  | some g => g.bytes
  | none => []

def cmAlignLogOf (c : CapturedMir) (aid : Nat) : Nat :=
  match c.allocations.find? (fun g => g.allocId == aid) with
  | some g => if g.align.bytes == 16 then 4 else if g.align.bytes == 4 then 2 else 0
  | none => 0

/-- The LeanMiri machine mirroring the captured globals of `c`: allocation `n`
of `c` becomes live allocation `n` at its base address. -/
def cmGlobalsMach (c : CapturedMir) : AnnealMachine :=
  cmMach ((c.allocations.filterMap fun g =>
    match g.allocId with
    | 100 => some (cmA100, (1024 : UInt64), cmAlloc g.bytes (cmAlignLogOf c 100))
    | 101 => some (cmA101, (1088 : UInt64), cmAlloc g.bytes (cmAlignLogOf c 101))
    | 102 => some (cmA102, (2048 : UInt64), cmAlloc g.bytes (cmAlignLogOf c 102))
    | 103 => some (cmA103, (2112 : UInt64), cmAlloc g.bytes (cmAlignLogOf c 103))
    | _ => none))

/-- Base address of LeanMiri allocation `n` (`cmGlobalsMach`). -/
def cmBase : Nat → UInt64
  | 100 => 1024
  | 101 => 1088
  | 102 => 2048
  | 103 => 2112
  | _ => 0

/-- A pointer into LeanMiri allocation `aid` at offset `off`. -/
def cmGP (aid off : Nat) : Miri.Memory.Scalar AnnealProv :=
  match aid with
  | 100 => cmPtrSc cmA100 (1024 + UInt64.ofNat off)
  | 101 => cmPtrSc cmA101 (1088 + UInt64.ofNat off)
  | 102 => cmPtrSc cmA102 (2048 + UInt64.ofNat off)
  | _ => cmPtrSc cmA103 (2112 + UInt64.ofNat off)

/-- State for a fixture `c` whose locals are `_0` (`retTy`, uninitialized), the
argument scalars `args`, and further uninitialized locals. -/
def cmStd (c : CapturedMir) (args : List (Option (Miri.Memory.Scalar AnnealProv))) : AnnealStepState :=
  let decls := c.localDecls
  let retTy := match decls with | d :: _ => d.ty | [] => unitMirTy
  let locs := (List.range decls.length).map fun i =>
    let ty := match decls[i]? with | some d => d.ty | none => unitMirTy
    if i = 0 then cmUninitLoc ty c.layouts
    else match args[i - 1]? with
      | some (some sc) => cmScLoc sc ty c.layouts
      | _ => cmUninitLoc ty c.layouts
  cmMkState c retTy locs.toArray (cmGlobalsMach c)

/-- Two-node vendored Tree Borrows tree over the 4 bytes of a `u32`: root
`retagParentTag` with an accessed child `retagChildTag` carrying `perm`. -/
def cmU32ChildTreeWith (perm : TreeBorrowPerm) : Miri.TreeBorrows.BorrowTree :=
  { hooksTwoNodeTree perm with
    locations := Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 4) (hooksLocTree perm) }

def cmU32ChildTree : Miri.TreeBorrows.BorrowTree := cmU32ChildTreeWith .unique

/-- State of `cmCopyModeMir`: `_3 = 11u32` is memory-backed at allocation `1`
(base `256`) carrying `cmU32ChildTree`; the destination `_2` points at it with
the ROOT tag `retagParentTag`, while the child `retagChildTag` carries a strong
protector (vendored global protected-tag table). -/
def cmCopyModeState : AnnealStepState :=
  let a1 : Miri.Memory.AllocId := cmAid 1
  let dstAlloc :=
    match Miri.Memory.Allocation.fromBytes (Prov := AnnealProv) #[11, 0, 0, 0] ⟨2⟩ .Mut with
    | .ok al => al.withExtra (some cmU32ChildTree)
    | .error _ => cmEmptyAlloc
  let mach : AnnealMachine :=
    { memory := { AnnealMachine.empty.memory with
        live := #[(cmA100, ⟨.stack, cmAlloc (cmU32Bytes 42) 2⟩), (a1, ⟨.stack, dstAlloc⟩)] },
      addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨cmA100, 1024⟩, ⟨a1, 256⟩] },
      borrowTracker := some
        { global := { protectedTags := (hooksForChildProtected true).protectedTags },
          retagMode := .Default } }
  let mp : Miri.Interpreter.MemPlace AnnealProv :=
    ⟨⟨Miri.ABI.Size.ofBytes 256, some (.concrete a1 retagParentTag)⟩, .none, none⟩
  cmMkState cmCopyModeMir u32MirTy
    #[cmUninitLoc u32MirTy, cmScLoc (cmGP 100 0) rawConstU32MirTy,
      cmScLoc (cmPtrSc a1 256 retagParentTag) rawMutU32MirTy,
      ⟨.live (.indirect mp), some (translateTyOverlay u32MirTy)⟩, cmUninitLoc unitMirTy] mach

/-- State of `cmSwapModeMir`: `_1` points to global `100 = 7u32` and `_2` points
(via root tag `retagParentTag`) to memory-backed `_3 = 9u32` at allocation `1`
carrying a strongly protected `.frozen` child `retagChildTag`. Under `tb = true`,
`typedSwap`'s read of `_2` (`memCopy`) is allowed on `.frozen`, and step 4's
write to `_2` (`cmCopyOp` Tree Borrows write) deterministically faults `.ub`. -/
def cmSwapModeState : AnnealStepState :=
  let a1 : Miri.Memory.AllocId := cmAid 1
  let yAlloc :=
    match Miri.Memory.Allocation.fromBytes (Prov := AnnealProv) #[9, 0, 0, 0] ⟨2⟩ .Mut with
    | .ok al => al.withExtra (some (cmU32ChildTreeWith .frozen))
    | .error _ => cmEmptyAlloc
  let mach : AnnealMachine :=
    { memory := { AnnealMachine.empty.memory with
        live := #[(cmA100, ⟨.stack, cmAlloc (cmU32Bytes 7) 2⟩), (a1, ⟨.stack, yAlloc⟩)] },
      addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨cmA100, 1024⟩, ⟨a1, 256⟩] },
      borrowTracker := some
        { global := { protectedTags := (hooksForChildProtected true).protectedTags },
          retagMode := .Default } }
  let mp : Miri.Interpreter.MemPlace AnnealProv :=
    ⟨⟨Miri.ABI.Size.ofBytes 256, some (.concrete a1 retagParentTag)⟩, .none, none⟩
  cmMkState cmSwapModeMir u32MirTy
    #[cmUninitLoc u32MirTy, cmScLoc (cmGP 100 0) rawMutU32MirTy,
      cmScLoc (cmPtrSc a1 256 retagParentTag) rawMutU32MirTy,
      ⟨.live (.indirect mp), some (translateTyOverlay u32MirTy)⟩, cmUninitLoc unitMirTy] mach

/-- Step budget of every LeanMiri corpus execution. -/
def cmLmFuel : Nat := 8

/-- Run fixture `c` from state `st` through vendored `Step.step` under `cmStepHooks`. -/
def cmRunLm (c : CapturedMir) (tb : Bool) (st : AnnealStepState) : CmLmObs :=
  cmToObs (runMiriSteps (cmStepHooks c tb) cmLmFuel st)

/-- Direct vendored `Miri.Interpreter.Step.step` observation for EVERY
`(treeBorrows, variantIdx, caseIdx)` key (`variantIdx ∈ 0..7` in the order
`copy, compare_bytes, raw_eq, typed_swap_nonoverlapping, ptr_offset_from,
ptr_offset_from_unsigned, ptr_mask, black_box`; `caseIdx ∈ 0..3` in the order
`okPrimary, okSecondary, ubFault, modeCase`). Zero shadow evaluators. -/
def cmLmObserve (tb : Bool) (variantIdx caseIdx : Nat) : CmLmObs :=
  match variantIdx, caseIdx with
  | 0, 0 => cmRunLm cmCopyMir tb (cmStd cmCopyMir [some (cmGP 100 0), some (cmGP 101 0)])
  | 0, 1 => cmRunLm cmCopyOverlapMir tb
      (cmStd cmCopyOverlapMir [some (cmGP 100 0), some (cmGP 100 2), some (cmGP 100 4)])
  | 0, 2 => cmRunLm cmCopyMir tb (cmStd cmCopyMir [some (cmIntSc 0), some (cmGP 101 0)])
  | 0, 3 => cmRunLm cmCopyModeMir tb cmCopyModeState
  | 1, 0 => cmRunLm cmCmpBytes3Mir tb (cmStd cmCmpBytes3Mir [some (cmGP 100 0), some (cmGP 101 0)])
  | 1, 1 => cmRunLm cmCmpBytes1Mir tb (cmStd cmCmpBytes1Mir [some (cmGP 100 0), some (cmGP 101 0)])
  | 1, 2 => cmRunLm cmCmpBytes3Mir tb (cmStd cmCmpBytes3Mir [some (cmGP 102 0), some (cmGP 101 0)])
  | 1, 3 => cmRunLm cmCmpBytes3Mir tb (cmStd cmCmpBytes3Mir [some (cmGP 100 0), some (cmGP 103 0)])
  | 2, 0 => cmRunLm cmRawEqU32Mir tb (cmStd cmRawEqU32Mir [some (cmGP 100 0), some (cmGP 101 0)])
  | 2, 1 => cmRunLm cmRawEqU32Mir tb (cmStd cmRawEqU32Mir [some (cmGP 100 0), some (cmGP 102 0)])
  | 2, 2 => cmRunLm cmRawEqU32Mir tb (cmStd cmRawEqU32Mir [some (cmGP 103 0), some (cmGP 102 0)])
  | 2, 3 => cmRunLm cmRawEqZstMir tb (cmStd cmRawEqZstMir [some (cmIntSc 4096), some (cmIntSc 4096)])
  | 3, 0 => cmRunLm cmSwapReadXMir tb (cmStd cmSwapReadXMir [some (cmGP 100 0), some (cmGP 101 0)])
  | 3, 1 => cmRunLm cmSwapSameAllocMir tb (cmStd cmSwapSameAllocMir [some (cmGP 100 0), some (cmGP 100 4)])
  | 3, 2 => cmRunLm cmSwapReadXMir tb (cmStd cmSwapReadXMir [some (cmIntSc 0), some (cmGP 101 0)])
  | 3, 3 => cmRunLm cmSwapModeMir tb cmSwapModeState
  | 4, 0 => cmRunLm cmPofMir tb (cmStd cmPofMir [some (cmGP 100 12), some (cmGP 100 4)])
  | 4, 1 => cmRunLm cmPofMir tb (cmStd cmPofMir [some (cmGP 100 4), some (cmGP 100 12)])
  | 4, 2 => cmRunLm cmPofMir tb (cmStd cmPofMir [some (cmGP 100 4), some (cmGP 101 12)])
  | 4, 3 => cmRunLm cmPofMir tb (cmStd cmPofMir [some (cmIntSc 4096), some (cmIntSc 4096)])
  | 5, 0 => cmRunLm cmPofuMir tb (cmStd cmPofuMir [some (cmGP 100 12), some (cmGP 100 4)])
  | 5, 1 => cmRunLm cmPofuMir tb (cmStd cmPofuMir [some (cmGP 100 16), some (cmGP 100 0)])
  | 5, 2 => cmRunLm cmPofuMir tb (cmStd cmPofuMir [some (cmGP 100 4), some (cmGP 100 12)])
  | 5, 3 => cmRunLm cmPofuMir tb (cmStd cmPofuMir [some (cmGP 100 6), some (cmGP 100 0)])
  | 6, 0 => cmRunLm cmMaskAlign8Mir tb (cmStd cmMaskAlign8Mir [some (cmGP 100 12)])
  | 6, 1 => cmRunLm cmMaskIdentityMir tb (cmStd cmMaskIdentityMir [some (cmGP 100 12)])
  | 6, 2 => cmRunLm cmMaskAlign8Mir tb (cmStd cmMaskAlign8Mir [])
  | 6, 3 => cmRunLm cmMaskAlign4Mir tb (cmStd cmMaskAlign4Mir [some (cmGP 100 6)])
  | 7, 0 => cmRunLm cmBlackBoxU32Mir tb (cmStd cmBlackBoxU32Mir [some (cmIntSc 77 4)])
  | 7, 1 => cmRunLm cmBlackBoxPtrMir tb (cmStd cmBlackBoxPtrMir [some (cmGP 100 4)])
  | 7, 2 => cmRunLm cmBlackBoxU32Mir tb (cmStd cmBlackBoxU32Mir [])
  | 7, 3 => cmRunLm cmBlackBoxBoolMir tb (cmStd cmBlackBoxBoolMir [some (cmIntSc 1 1)])
  | _, _ => .unsupported

/-- The frozen 64-key LeanMiri observation table. -/
def cmLmExpected (tb : Bool) : Nat → Nat → CmLmObs
  | 0, 0 => .scalar 42 4
  | 0, 1 => .scalar 0x08070403 4
  | 0, 2 => .ub
  | 0, 3 => if tb then .ub else .scalar 42 4
  | 1, 0 => .scalar 0xFFFFFFFF 4
  | 1, 1 => .scalar 1 4
  | 1, 2 => .ub
  | 1, 3 => .scalar 0 4
  | 2, 0 => .scalar 1 1
  | 2, 1 => .scalar 0 1
  | 2, 2 => .ub
  | 2, 3 => .scalar 1 1
  | 3, 0 => .scalar 9 4
  | 3, 1 => .scalar 6 4
  | 3, 2 => .ub
  | 3, 3 => if tb then .ub else .scalar 9 4
  | 4, 0 => .scalar 2 8
  | 4, 1 => .scalar (2 ^ 64 - 2) 8
  | 4, 2 => .ub
  | 4, 3 => .scalar 0 8
  | 5, 0 => .scalar 2 8
  | 5, 1 => .scalar 4 8
  | 5, 2 => .ub
  | 5, 3 => .ub
  | 6, 0 => .ptr 100 1032
  | 6, 1 => .ptr 100 1036
  | 6, 2 => .ub
  | 6, 3 => .ptr 100 1028
  | 7, 0 => .scalar 77 4
  | 7, 1 => .ptr 100 1028
  | 7, 2 => .ub
  | 7, 3 => .scalar 1 1
  | _, _ => .unsupported

/-- Boolean 32-key table check for one `treeBorrows` mode. -/
def cmLmTableCheck (tb : Bool) : Bool :=
  (List.range 8).all fun v => (List.range 4).all fun c => decide (cmLmObserve tb v c = cmLmExpected tb v c)

/-- **Kernel-checked 64-key LeanMiri table** (both `treeBorrows` modes, all 32
`(variantIdx, caseIdx)` keys): every vendored execution yields exactly the
frozen observation. -/
theorem cmLmTableCheck_true (tb : Bool) : cmLmTableCheck tb = true := by
  cases tb <;> decide +kernel

/-- Per-key form of `cmLmTableCheck_true`. -/
theorem cmLmObserve_table (tb : Bool) (v c : Nat) (hv : v < 8) (hc : c < 4) :
    cmLmObserve tb v c = cmLmExpected tb v c := by
  have h := cmLmTableCheck_true tb
  simp only [cmLmTableCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h v hv c hc

/-- Mode sensitivity certified directly on `cmLmObserve`: `copy.modeCase` (the
destination's borrow tree has a strongly protected child) returns `42` with
`treeBorrows = false` and faults `.ub` with `treeBorrows = true`, and
`typedSwap.modeCase` (strongly protected `.frozen` child on `y`) returns `9`
with `treeBorrows = false` and faults `.ub` with `treeBorrows = true`. -/
theorem cmLmObserve_copy_mode_sensitivity :
    cmLmObserve false 0 3 = .scalar 42 4 ∧ cmLmObserve true 0 3 = .ub :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem cmLmObserve_typedSwap_mode_sensitivity :
    cmLmObserve false 3 3 = .scalar 9 4 ∧ cmLmObserve true 3 3 = .ub :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- **Hardened vendored hook witnesses** (exercising alignment in `cmDerefPointer`,
typed validity in `cmCopyOp`, overlap UB in `typedSwap`, TB read-then-write
`.unique -> .frozen` UB with ZERO protectors in `copy`, and ZST / `isize::MIN` UB
in `ptr_offset_from`):
1. `typed_swap_nonoverlapping::<u32>` on misaligned `&G[2]` -> `.ub`;
2. `typed_swap_nonoverlapping::<u32>` on overlapping `&G[0]`, `&G[2]` -> `.ub`;
3. `typed_swap_nonoverlapping::<bool>` on invalid `bool = 2` -> `.ub`;
4. `black_box::<bool>(2)` -> `.ub`;
5. `black_box::<&u32>(null)` -> `.ub`;
6. `copy::<u32>` with NO protectors where `src` (`retagParentTag`) reads and
   freezes child `dst` (`retagChildTag`, `.unique -> .frozen`) before writing
   `dst`: returns `11` in `tb = false` and faults `.ub` in `tb = true`;
7. `ptr_offset_from::<()>` (ZST) -> `.ub`;
8. `ptr_offset_from::<u32>(0, 2^63)` (`isize::MIN`) -> `.ub`. -/
theorem cmLm_hardened_hooks_witness :
    let swapBoolMir :=
      cmCallBody "cm::lm_swap_bool"
        [mkDecl boolMirTy, mkDecl { kind := .rawPtr .mut .bool, layoutIdx := 0 },
         mkDecl { kind := .rawPtr .mut .bool, layoutIdx := 0 }, mkDecl unitMirTy] 2
        (cmIntrinsicOp "core::intrinsics::typed_swap_nonoverlapping" [.bool])
        [.copy (locPlace 1), .copy (locPlace 2)] 3
        [mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1 [.deref]))))]
        [cmGlobal 100 [some 2] 1, cmGlobal 101 [some 1] 1, cmGlobal 102 [some 0] 1]
    let bbRefMir :=
      cmCallBody "cm::lm_bb_ref" [mkDecl cmRefU32Ty, mkDecl cmRefU32Ty] 1
        (cmIntrinsicOp "core::intrinsics::black_box" [.ref .not (.uint .u32)])
        [.copy (locPlace 1)] 0 [] []
    let pofZstMir :=
      cmCallBody "cm::lm_pof_zst"
        [mkDecl cmIsizeTy, mkDecl { kind := .rawPtr .not (.tuple []), layoutIdx := 0 },
         mkDecl { kind := .rawPtr .not (.tuple []), layoutIdx := 0 }] 2
        (cmIntrinsicOp "core::intrinsics::ptr_offset_from" [.tuple []])
        [.copy (locPlace 1), .copy (locPlace 2)] 0 [] []
    let a1 : Miri.Memory.AllocId := cmAid 1
    let rwAlloc :=
      match Miri.Memory.Allocation.fromBytes (Prov := AnnealProv) #[11, 0, 0, 0] ⟨2⟩ .Mut with
      | .ok al => al.withExtra (some cmU32ChildTree)
      | .error _ => cmEmptyAlloc
    let rwMach : AnnealMachine :=
      { memory := { AnnealMachine.empty.memory with live := #[(a1, ⟨.stack, rwAlloc⟩)] },
        addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨a1, 256⟩] },
        borrowTracker := some { global := { protectedTags := {} }, retagMode := .Default } }
    let rwMp : Miri.Interpreter.MemPlace AnnealProv :=
      ⟨⟨Miri.ABI.Size.ofBytes 256, some (.concrete a1 retagParentTag)⟩, .none, none⟩
    let rwState := cmMkState cmCopyModeMir u32MirTy
      #[cmUninitLoc u32MirTy, cmScLoc (cmPtrSc a1 256 retagParentTag) rawConstU32MirTy,
        cmScLoc (cmPtrSc a1 256 retagChildTag) rawMutU32MirTy,
        ⟨.live (.indirect rwMp), some (translateTyOverlay u32MirTy)⟩, cmUninitLoc unitMirTy] rwMach
    cmRunLm cmSwapSameAllocMir false (cmStd cmSwapSameAllocMir [some (cmGP 100 2), some (cmGP 100 4)]) = .ub ∧
    cmRunLm cmSwapSameAllocMir false (cmStd cmSwapSameAllocMir [some (cmGP 100 0), some (cmGP 100 2)]) = .ub ∧
    cmRunLm swapBoolMir false (cmStd swapBoolMir [some (cmGP 101 0), some (cmGP 102 0)]) = .scalar 0 1 ∧
    cmRunLm swapBoolMir false (cmStd swapBoolMir [some (cmGP 100 0), some (cmGP 101 0)]) = .ub ∧
    cmRunLm swapBoolMir false (cmStd swapBoolMir [some (cmGP 101 0), some (cmGP 100 0)]) = .ub ∧
    cmRunLm cmBlackBoxBoolMir false (cmStd cmBlackBoxBoolMir [some (cmIntSc 2 1)]) = .ub ∧
    cmRunLm bbRefMir false (cmStd bbRefMir [some (cmIntSc 0 8)]) = .ub ∧
    cmRunLm cmCopyModeMir false rwState = .scalar 11 4 ∧
    cmRunLm cmCopyModeMir true rwState = .ub ∧
    cmRunLm pofZstMir false (cmStd pofZstMir [some (cmIntSc 4096), some (cmIntSc 4096)]) = .ub ∧
    cmRunLm cmPofMir false (cmStd cmPofMir [some (cmIntSc 0), some (cmIntSc (2 ^ 63))]) = .ub := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## §4. Deliberate Library-UB Deltas vs. `lean-miri` (and the `copy` Agreement) -/

/-- A bounded Trusted run of `stepMirFn` observed as a `CmLmObs`. -/
def cmTrustedStepLm (body : CapturedMir) : (Option MachineState) → CmLmObs ⊕ MachineState
  | none => .inl .unsupported
  | some s =>
    match stepMirFn body s with
    | .tau (.running s') => .inr s'
    | .ret (.normal r) =>
      match r.1 with
      | .scalar sc => .inl (.scalar sc.bits sc.sizeBytes)
      | _ => .inl .unsupported
    | .vis (.inl (.fail .ub)) _ => .inl .ub
    | _ => .inl .unsupported

/-- Run Trusted `stepMirFn` for up to `fuel` steps. -/
def cmTrustedRunLm (body : CapturedMir) : Nat → MachineState → CmLmObs
  | 0, _ => .unsupported
  | n + 1, s =>
    match cmTrustedStepLm body (some s) with
    | .inl o => o
    | .inr s' => cmTrustedRunLm body n s'

/-- Trusted initial state with all locals live and argument values `args`. -/
def cmTrustedInitLm (body : CapturedMir) (args : List Value) : MachineState :=
  let base := initMachineState body args
  { base with frame := { base.frame with locals := base.frame.locals.map fun
      | .dead => .uninit
      | slot => slot } }

/-- **Deliberate deltas and the `copy` agreement** (Trusted `stepMirFn` vs.
vendored `Step.step`):
1. `compare_bytes(null, null, 0)`: Trusted `.ub` (the pinned contract requires
   pointers valid for reads, and a null pointer is never valid); `lean-miri`
   returns `0` (zero-sized accesses skip `checkAndDerefPtr`);
2. `typed_swap_nonoverlapping::<()>(null, null)`: Trusted `.ub`; `lean-miri`
   completes the swap;
3. `copy::<u32>(null, null, 0)`: both complete (the pinned `ptr::copy`
   contract exempts zero-byte copies from validity; alignment is checked). -/
theorem cm_lm_trusted_null_zero_size_deltas :
    cmTrustedRunLm cmCmpBytes0Mir 8 (cmTrustedInitLm cmCmpBytes0Mir [.ptr ⟨0, 0⟩ 8, .ptr ⟨0, 0⟩ 8]) = .ub ∧
    cmRunLm cmCmpBytes0Mir false (cmStd cmCmpBytes0Mir [some (cmIntSc 0), some (cmIntSc 0)]) = .scalar 0 4 ∧
    cmTrustedRunLm cmSwapZstMir 8 (cmTrustedInitLm cmSwapZstMir [.ptr ⟨0, 0⟩ 8, .ptr ⟨0, 0⟩ 8]) = .ub ∧
    cmRunLm cmSwapZstMir false (cmStd cmSwapZstMir [some (cmIntSc 0), some (cmIntSc 0)]) = .scalar 7 4 ∧
    cmTrustedRunLm cmCopy0Mir 8 (cmTrustedInitLm cmCopy0Mir [.ptr ⟨0, 0⟩ 8, .ptr ⟨0, 0⟩ 8]) = .scalar 7 4 ∧
    cmRunLm cmCopy0Mir false (cmStd cmCopy0Mir [some (cmIntSc 0), some (cmIntSc 0)]) = .scalar 7 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **Trusted-side anchors on the corpus fixtures**: Trusted `stepMirFn` produces
the same scalar results as the vendored runs of `cmLmExpected` (e.g. `copy`
`42`, `compare_bytes` `-1`, `ptr_offset_from` `-2`). -/
theorem cm_lm_trusted_side_witness :
    cmTrustedRunLm cmCopyMir 8 (cmTrustedInitLm cmCopyMir [.ptr ⟨100, 0⟩ 8, .ptr ⟨101, 0⟩ 8]) =
      .scalar 42 4 ∧
    cmTrustedRunLm cmCmpBytes3Mir 8 (cmTrustedInitLm cmCmpBytes3Mir [.ptr ⟨100, 0⟩ 8, .ptr ⟨101, 0⟩ 8]) =
      .scalar 0xFFFFFFFF 4 ∧
    cmTrustedRunLm cmPofMir 8 (cmTrustedInitLm cmPofMir [.ptr ⟨100, 4⟩ 8, .ptr ⟨100, 12⟩ 8]) =
      .scalar (2 ^ 64 - 2) 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-! ## §5. Exhaustive Axiom, Non-Triviality, & Import-Isolation Audit -/

section AxiomAudit
open Lean Elab Command

elab "#assert_core_mem_ptr_lm_audit" : command => do
  let env ← getEnv
  for modName in env.header.moduleNames do
    if (`MiniRustSpec).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported in LeanMiriSpec"
  let rec isTrivialProp : Expr → Bool
    | .forallE _ _ body _ => isTrivialProp body
    | .letE _ _ _ body _ => isTrivialProp body
    | e =>
      if e.isConstOf ``True then true
      else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
      else if e.isAppOfArity ``Iff 2 then e.appFn!.appArg! == e.appArg!
      else false
  let mut checked : Nat := 0
  for (c, ci) in env.constants.map₂.toList do
    if let .thmInfo v := ci then
      let u := (Lean.privateToUserName? c).getD c
      if !u.isInternal && isTrivialProp v.type then
        throwError "{c} is a trivial theorem"
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    checked := checked + 1
  if checked == 0 then
    throwError "LeanMiriSpec.CoreMemPtrIntrinsicsLM: 0 declarations found"
  logInfo m!"LeanMiriSpec.CoreMemPtrIntrinsicsLM: verified {checked} declarations (sorry_free=true, import_isolated=true, 0 trivial, 0 ofReduceBool)"

#assert_core_mem_ptr_lm_audit

end AxiomAudit

end LeanMiriSpec.CoreMemPtrIntrinsicsLM
