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
    | .ok ptr => pure ⟨.memory ⟨ptr, .none, none⟩, cmPointeeLayout tyArg ly⟩

def cmIntrinsicHooks (ld : List LocalDecl) (ly : LayoutTable) (tb : Bool) (tyArg : Miri.MIR.TyId) :
    Miri.Interpreter.IntrinsicHooks AnnealProv AnnealStepState Unit (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealIntrinsicHooks ld ly with
    pointeeType := fun _ tyId =>
      match rawPtrPointeeEncodedTyId? tyId with
      | some p => pure p
      | none => pure tyArg
    copyOp := fun _ src dest => do
      let imm ← annealReadImmediate src
      annealWriteImmediate imm.imm dest
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
      | .memory mp => do let _ ← annealReadImmediate ⟨.indirect mp, place.layout⟩; pure ()
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
`retagParentTag` with an accessed child `retagChildTag`. -/
def cmU32ChildTree : Miri.TreeBorrows.BorrowTree :=
  { hooksTwoNodeTree .unique with
    locations := Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 4) (hooksLocTree .unique) }

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
  | 3, 1 => cmRunLm cmSwapReadYMir tb (cmStd cmSwapReadYMir [some (cmGP 100 0), some (cmGP 101 0)])
  | 3, 2 => cmRunLm cmSwapReadXMir tb (cmStd cmSwapReadXMir [some (cmIntSc 0), some (cmGP 101 0)])
  | 3, 3 => cmRunLm cmSwapSameAllocMir tb (cmStd cmSwapSameAllocMir [some (cmGP 100 0), some (cmGP 100 4)])
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
  | 3, 1 => .scalar 7 4
  | 3, 2 => .ub
  | 3, 3 => .scalar 6 4
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
`treeBorrows = false` and faults `.ub` with `treeBorrows = true` (vendored Tree
Borrows foreign write to a protected tag). -/
theorem cmLmObserve_copy_mode_sensitivity :
    cmLmObserve false 0 3 = .scalar 42 4 ∧ cmLmObserve true 0 3 = .ub :=
  ⟨by decide +kernel, by decide +kernel⟩

/-! ## §4. Deliberate Library-UB Deltas vs. `lean-miri` (and the `copy` Agreement) -/

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
