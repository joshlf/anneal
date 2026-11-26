/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import MiniRustSpec.NullaryAndPtrCoercionMR
import Trusted.Rustc.V2026_08_01.MirSemantics.Machine

/-!
# Episode 2 Dual-Authority Correspondence (`MiniRustSpec` Authority):
# the 8 core memory & pointer intrinsics of `Trusted.Rustc.V2026_06_01.MirSemantics`

Universal operational laws, dispatch theorems, and kernel-checked concrete
three-way witnesses relating the 8 core memory & pointer intrinsics promoted
into `Trusted.Rustc.{V2026_06_01,V2026_08_01}.MirSemantics` in Episode 1
(`evalCopyCall`, `evalCompareBytesCall`, `evalRawEqCall`,
`evalTypedSwapNonOverlappingCall`, `evalPtrOffsetFromCall` (signed and
unsigned), `evalPtrMaskCall`, `evalBlackBoxCall`, all reached through the real
`stepMirFn` -> `evalTerminator` -> `evalDirectRustIntrinsic?` dispatch) to
`MiniRustSpec.Interp` across **both `Mach` (`BasicMemory<x86_64>`) and `MachTB`
(`TreeBorrowsMemory<x86_64>`, preserving `MachTB.wfLive`)**:

1. `core::intrinsics::copy` — overlapping `memmove` (snapshot read then write),
   null source UB at a non-zero count, and genuine `Mach` vs. `MachTB` /
   `basic` vs. `protectedTB` mode sensitivity (a foreign write through the
   destination to a protected sibling borrow).
2. `core::intrinsics::compare_bytes` — unsigned lexicographic comparison
   (`-1`/`0`/`1`), with the eager whole-slice read making a later `.uninit`
   byte UB even when an earlier byte already decides the result.
3. `core::intrinsics::raw_eq` — `MiniRustSpec.Interp.evalIntrinsic .RawEq`
   (equal, unequal, uninitialized-byte UB, ZST `true`).
4. `core::intrinsics::typed_swap_nonoverlapping` — typed read/read/write/write
   swap (disjoint allocations, disjoint elements of one allocation, null UB).
5. `core::intrinsics::ptr_offset_from` — MiniRust `BinOp::PtrOffsetFrom
   { inbounds: true, nonneg: false }` + `DivExact` (positive, negative,
   cross-allocation UB, dangling same-address `0`).
6. `core::intrinsics::ptr_offset_from_unsigned` — `PtrOffsetFrom { nonneg:
   true }` (positive, one-past-the-end, negative UB, non-divisible UB).
7. `core::intrinsics::ptr_mask` — strict-provenance `ptr.with_addr(addr &
   mask)` (MiniRust: provenance-free `Transmute` of the address and
   `PtrOffset { inbounds: false }`), preserving provenance (no `expose`).
8. `core::intrinsics::black_box` — value / provenance identity and validity
   enforcement (uninitialized `u32` is UB).

The trailing corpus interface (`cmTrustedObserve`, `cmMrObserve`,
`cmMrObserveClass`) executes `stepMirFn` and `MiniRustSpec.Interp.{steps,
stepsTB}` directly (no shadow evaluator) and exports kernel-checked 64-key
table lemmas consumed by `Anneal.Mir.CoreMemPtrIntrinsicsBundle`.

Strict import isolation: this module NEVER imports `Anneal.*`, `Miri.*`, or
`LeanMiriSpec.*` (verified by the trailing `#assert_core_mem_ptr_mr_audit`).
-/

namespace MiniRustSpec.CoreMemPtrIntrinsicsMR

set_option Elab.async false
set_option linter.unusedSimpArgs false

open Trusted.Effect Trusted.ITree Trusted.Sequence
open Trusted.Rustc.V2026_06_01 Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics Trusted.Rustc.V2026_06_01.Layout
open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp
open MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.RefWitness
open MiniRustSpec.UnwindSetDiscrAndFnPtrMR

/-! ## §0. Frozen Cross-Root Types, Allocations, and `CapturedMir` Fixtures

Every definition in this section is shared verbatim with
`LeanMiriSpec.CoreMemPtrIntrinsicsLM`; the cross-root kernel bridge in
`tests/mir/CoreMemPtrIntrinsicsTests.lean` locks each fixture by `Eq.refl`.
Memory operated on by the intrinsics lives in the fixtures' captured global
allocations (`CapturedMir.allocations`, ids `100`..`103`), except for the
`copy` mode-sensitivity fixture, whose destination is the stack local `_3`. -/

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

/-! ## §1. Corpus Keys and the Direct Trusted `stepMirFn` Runner -/

/-- The 8 core memory & pointer intrinsics of this correspondence. -/
inductive CmVariant : Type where
  | copy
  | compareBytes
  | rawEq
  | typedSwap
  | ptrOffsetFrom
  | ptrOffsetFromUnsigned
  | ptrMask
  | blackBox
  deriving DecidableEq, Repr

/-- Corpus test case selector within each of the 8 intrinsics. -/
inductive CmCase : Type where
  /-- Primary positive normal-return case. -/
  | okPrimary
  /-- Secondary positive normal-return case. -/
  | okSecondary
  /-- Primary UB fault case. -/
  | ubFault
  /-- Mode-sensitive case on `copy` (`basic` returns vs. `protectedTB` UB); a
      further edge case (normal return or UB) on every other intrinsic. -/
  | modeCase
  deriving DecidableEq, Repr

/-- Normalized observation of one bounded Trusted `stepMirFn` execution. -/
inductive CmTrustedObs : Type where
  /-- A scalar return value (`bits`, width in bytes). -/
  | scalar (bits size : Nat)
  /-- A thin pointer return value (`allocId`, byte offset). -/
  | ptr (allocId off : Nat)
  | ub
  | unsupported
  /-- Out of fuel, a pending interaction, or a return outside the observable domain. -/
  | stuck
  deriving DecidableEq, Repr

/-- Observe a Trusted return `MirSemantics.Value`. -/
def cmTrustedValueObs : MirSemantics.Value → CmTrustedObs
  | .scalar sc => .scalar sc.bits sc.sizeBytes
  | .ptr p 8 => .ptr p.allocId p.offsetBytes
  | _ => .stuck

/-- State of a bounded Trusted `stepMirFn` execution. -/
inductive CmTrustedRunState : Type where
  | running (s : MachineState)
  | done (o : CmTrustedObs)

/-- One `stepMirFn` step of the bounded Trusted runner. -/
def cmTrustedRunStep (body : CapturedMir) : CmTrustedRunState → CmTrustedRunState
  | .done o => .done o
  | .running s =>
    match stepMirFn body s with
    | .tau (.running s') => .running s'
    | .vis (.inr (.inl (.emit _))) k =>
      match k PUnit.unit with
      | .running s' => .running s'
      | _ => .done .stuck
    | .ret (.normal r) => .done (cmTrustedValueObs r.1)
    | .vis (.inl (.fail .ub)) _ => .done .ub
    | .vis (.inl (.fail .unsupported)) _ => .done .unsupported
    | _ => .done .stuck

/-- Execute `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` directly for up
to `fuel` steps and return the normalized observation. -/
def cmRunTrusted (body : CapturedMir) (fuel : Nat) (s : MachineState) : CmTrustedObs :=
  match Nat.repeat (cmTrustedRunStep body) fuel (.running s) with
  | .done o => o
  | .running _ => .stuck

/-- Initial Trusted state with all declared locals live (`.uninit` for `_0` and
temporaries, `.init v` for arguments), globals from `body.allocations`. -/
def cmInitLiveState (body : CapturedMir) (args : List Value) : MachineState :=
  let base := initMachineState body args
  { base with
    frame := { base.frame with
      locals := base.frame.locals.map fun
        | .dead => .uninit
        | slot => slot } }

/-- A thin pointer into global allocation `aid` at offset `off`. -/
def cmGPtr (aid off : Nat) : Value := .ptr ⟨aid, off⟩ 8

/-- A provenance-free (unbacked `allocId = 0`) thin pointer at address `addr`. -/
def cmIntPtr (addr : Nat) : Value := .ptr ⟨0, addr⟩ 8

/-- Initial state of `cmCopyModeMir`: `_3 = 11u32`, `_2` points into `_3`
through root borrow tag `2` (`.unique`), and a sibling root borrow tag `1`
(`.frozen`) on `_3` carries the active protector `1` exactly when
`protectedMode = true`. -/
def cmCopyModeInit (protectedMode : Bool) : MachineState :=
  let base := cmInitLiveState cmCopyModeMir [cmGPtr 100 0, .ptr ⟨2, 0⟩ 8]
  let b1 : BorrowEntry :=
    { tag := 1, targetLocal := 3, targetProjection := [], perm := TreeBorrowPerm.frozen,
      rangeOffset := 0, rangeLen := 4, protector := (if protectedMode then some 1 else none),
      parentTag := none, targetFrameDepth := 0, allocDead := false }
  let b2 : BorrowEntry :=
    { tag := 2, targetLocal := 3, targetProjection := [], perm := TreeBorrowPerm.unique,
      rangeOffset := 0, rangeLen := 4, protector := none, parentTag := none,
      targetFrameDepth := 0, allocDead := false }
  { base with
    frame := { base.frame with
      locals := [.uninit, .init (cmGPtr 100 0), .init (.ptr ⟨2, 0⟩ 8), .init (.scalar ⟨11, 4⟩),
                 .uninit] },
    memory := { base.memory with
      borrows := [b1, b2], nextTag := 3,
      activeProtectors := (if protectedMode then [1] else []) } }

/-- The `CapturedMir` fixture executed for each `(variant, case)` key. -/
def cmTrustedFixture : CmVariant → CmCase → CapturedMir
  | .copy, .okPrimary => cmCopyMir
  | .copy, .okSecondary => cmCopyOverlapMir
  | .copy, .ubFault => cmCopyMir
  | .copy, .modeCase => cmCopyModeMir
  | .compareBytes, .okPrimary => cmCmpBytes3Mir
  | .compareBytes, .okSecondary => cmCmpBytes1Mir
  | .compareBytes, .ubFault => cmCmpBytes3Mir
  | .compareBytes, .modeCase => cmCmpBytes3Mir
  | .rawEq, .okPrimary => cmRawEqU32Mir
  | .rawEq, .okSecondary => cmRawEqU32Mir
  | .rawEq, .ubFault => cmRawEqU32Mir
  | .rawEq, .modeCase => cmRawEqZstMir
  | .typedSwap, .okPrimary => cmSwapReadXMir
  | .typedSwap, .okSecondary => cmSwapReadYMir
  | .typedSwap, .ubFault => cmSwapReadXMir
  | .typedSwap, .modeCase => cmSwapSameAllocMir
  | .ptrOffsetFrom, _ => cmPofMir
  | .ptrOffsetFromUnsigned, _ => cmPofuMir
  | .ptrMask, .okPrimary => cmMaskAlign8Mir
  | .ptrMask, .okSecondary => cmMaskIdentityMir
  | .ptrMask, .ubFault => cmMaskAlign8Mir
  | .ptrMask, .modeCase => cmMaskAlign4Mir
  | .blackBox, .okPrimary => cmBlackBoxU32Mir
  | .blackBox, .okSecondary => cmBlackBoxPtrMir
  | .blackBox, .ubFault => cmBlackBoxU32Mir
  | .blackBox, .modeCase => cmBlackBoxBoolMir

/-- The initial Trusted `MachineState` for each `(protectedMode, variant, case)` key. -/
def cmTrustedInit (protectedMode : Bool) : CmVariant → CmCase → MachineState
  | .copy, .okPrimary => cmInitLiveState cmCopyMir [cmGPtr 100 0, cmGPtr 101 0]
  | .copy, .okSecondary =>
    cmInitLiveState cmCopyOverlapMir [cmGPtr 100 0, cmGPtr 100 2, cmGPtr 100 4]
  | .copy, .ubFault => cmInitLiveState cmCopyMir [cmIntPtr 0, cmGPtr 101 0]
  | .copy, .modeCase => cmCopyModeInit protectedMode
  | .compareBytes, .okPrimary => cmInitLiveState cmCmpBytes3Mir [cmGPtr 100 0, cmGPtr 101 0]
  | .compareBytes, .okSecondary => cmInitLiveState cmCmpBytes1Mir [cmGPtr 100 0, cmGPtr 101 0]
  | .compareBytes, .ubFault => cmInitLiveState cmCmpBytes3Mir [cmGPtr 102 0, cmGPtr 101 0]
  | .compareBytes, .modeCase => cmInitLiveState cmCmpBytes3Mir [cmGPtr 100 0, cmGPtr 103 0]
  | .rawEq, .okPrimary => cmInitLiveState cmRawEqU32Mir [cmGPtr 100 0, cmGPtr 101 0]
  | .rawEq, .okSecondary => cmInitLiveState cmRawEqU32Mir [cmGPtr 100 0, cmGPtr 102 0]
  | .rawEq, .ubFault => cmInitLiveState cmRawEqU32Mir [cmGPtr 103 0, cmGPtr 102 0]
  | .rawEq, .modeCase => cmInitLiveState cmRawEqZstMir [cmIntPtr 4096, cmIntPtr 4096]
  | .typedSwap, .okPrimary => cmInitLiveState cmSwapReadXMir [cmGPtr 100 0, cmGPtr 101 0]
  | .typedSwap, .okSecondary => cmInitLiveState cmSwapReadYMir [cmGPtr 100 0, cmGPtr 101 0]
  | .typedSwap, .ubFault => cmInitLiveState cmSwapReadXMir [cmIntPtr 0, cmGPtr 101 0]
  | .typedSwap, .modeCase => cmInitLiveState cmSwapSameAllocMir [cmGPtr 100 0, cmGPtr 100 4]
  | .ptrOffsetFrom, .okPrimary => cmInitLiveState cmPofMir [cmGPtr 100 12, cmGPtr 100 4]
  | .ptrOffsetFrom, .okSecondary => cmInitLiveState cmPofMir [cmGPtr 100 4, cmGPtr 100 12]
  | .ptrOffsetFrom, .ubFault => cmInitLiveState cmPofMir [cmGPtr 100 4, cmGPtr 101 12]
  | .ptrOffsetFrom, .modeCase => cmInitLiveState cmPofMir [cmIntPtr 4096, cmIntPtr 4096]
  | .ptrOffsetFromUnsigned, .okPrimary => cmInitLiveState cmPofuMir [cmGPtr 100 12, cmGPtr 100 4]
  | .ptrOffsetFromUnsigned, .okSecondary => cmInitLiveState cmPofuMir [cmGPtr 100 16, cmGPtr 100 0]
  | .ptrOffsetFromUnsigned, .ubFault => cmInitLiveState cmPofuMir [cmGPtr 100 4, cmGPtr 100 12]
  | .ptrOffsetFromUnsigned, .modeCase => cmInitLiveState cmPofuMir [cmGPtr 100 6, cmGPtr 100 0]
  | .ptrMask, .okPrimary => cmInitLiveState cmMaskAlign8Mir [cmGPtr 100 12]
  | .ptrMask, .okSecondary => cmInitLiveState cmMaskIdentityMir [cmGPtr 100 12]
  | .ptrMask, .ubFault => cmInitLiveState cmMaskAlign8Mir []
  | .ptrMask, .modeCase => cmInitLiveState cmMaskAlign4Mir [cmGPtr 100 6]
  | .blackBox, .okPrimary => cmInitLiveState cmBlackBoxU32Mir [.scalar ⟨77, 4⟩]
  | .blackBox, .okSecondary => cmInitLiveState cmBlackBoxPtrMir [cmGPtr 100 4]
  | .blackBox, .ubFault => cmInitLiveState cmBlackBoxU32Mir []
  | .blackBox, .modeCase => cmInitLiveState cmBlackBoxBoolMir [.scalar ⟨1, 1⟩]

/-- Step budget of every Trusted corpus execution (one call terminator, at most
one statement, one `return`). -/
def cmTrustedFuel : Nat := 8

/-- Direct Trusted observation for every `(protectedMode, variant, case)` key. -/
def cmTrustedObserve (protectedMode : Bool) (v : CmVariant) (c : CmCase) : CmTrustedObs :=
  cmRunTrusted (cmTrustedFixture v c) cmTrustedFuel (cmTrustedInit protectedMode v c)

/-- The frozen 64-key Trusted observation table. -/
def cmTrustedExpected (protectedMode : Bool) : CmVariant → CmCase → CmTrustedObs
  | .copy, .okPrimary => .scalar 42 4
  | .copy, .okSecondary => .scalar 0x08070403 4
  | .copy, .ubFault => .ub
  | .copy, .modeCase =>
    match protectedMode with
    | false => .scalar 42 4
    | true => .ub
  | .compareBytes, .okPrimary => .scalar 0xFFFFFFFF 4
  | .compareBytes, .okSecondary => .scalar 1 4
  | .compareBytes, .ubFault => .ub
  | .compareBytes, .modeCase => .scalar 0 4
  | .rawEq, .okPrimary => .scalar 1 1
  | .rawEq, .okSecondary => .scalar 0 1
  | .rawEq, .ubFault => .ub
  | .rawEq, .modeCase => .scalar 1 1
  | .typedSwap, .okPrimary => .scalar 9 4
  | .typedSwap, .okSecondary => .scalar 7 4
  | .typedSwap, .ubFault => .ub
  | .typedSwap, .modeCase => .scalar 6 4
  | .ptrOffsetFrom, .okPrimary => .scalar 2 8
  | .ptrOffsetFrom, .okSecondary => .scalar (2 ^ 64 - 2) 8
  | .ptrOffsetFrom, .ubFault => .ub
  | .ptrOffsetFrom, .modeCase => .scalar 0 8
  | .ptrOffsetFromUnsigned, .okPrimary => .scalar 2 8
  | .ptrOffsetFromUnsigned, .okSecondary => .scalar 4 8
  | .ptrOffsetFromUnsigned, .ubFault => .ub
  | .ptrOffsetFromUnsigned, .modeCase => .ub
  | .ptrMask, .okPrimary => .ptr 100 8
  | .ptrMask, .okSecondary => .ptr 100 12
  | .ptrMask, .ubFault => .ub
  | .ptrMask, .modeCase => .ptr 100 4
  | .blackBox, .okPrimary => .scalar 77 4
  | .blackBox, .okSecondary => .ptr 100 4
  | .blackBox, .ubFault => .ub
  | .blackBox, .modeCase => .scalar 1 1

/-- **Kernel-checked Trusted table**: on all 64 keys, executing `stepMirFn` on
the fixture yields exactly the frozen observation. -/
theorem cmTrustedObserve_table (protectedMode : Bool) (v : CmVariant) (c : CmCase) :
    cmTrustedObserve protectedMode v c = cmTrustedExpected protectedMode v c := by
  cases protectedMode <;> cases v <;> cases c <;> decide +kernel



/-! ## §2. Universal Dispatch and Algebraic Laws of the Trusted Evaluators -/

/-- The Trusted classifier result of a `DefPath`, as the corpus variant it
names (`none` for every other path). -/
def cmClassifyVariant? (p : DefPath) : Option CmVariant :=
  match classifyRustIntrinsic? p with
  | some .copy => some .copy
  | some .compareBytes => some .compareBytes
  | some .rawEq => some .rawEq
  | some .typedSwapNonOverlapping => some .typedSwap
  | some .ptrOffsetFrom => some .ptrOffsetFrom
  | some .ptrOffsetFromUnsigned => some .ptrOffsetFromUnsigned
  | some .ptrMask => some .ptrMask
  | some .blackBox => some .blackBox
  | _ => none

/-- **Classification (`classifyRustIntrinsic?`)**: the 8 canonical
`core::intrinsics::*` paths classify to exactly their intrinsic, while the
library wrappers `core::ptr::copy`, `core::ptr::swap_nonoverlapping`,
`core::mem::swap`, `core::hint::black_box`, and `core::ptr::mask` are ordinary
callees. -/
theorem cm_classify_core_mem_ptr_intrinsics :
    cmClassifyVariant? "core::intrinsics::copy" = some .copy ∧
    cmClassifyVariant? "core::intrinsics::compare_bytes" = some .compareBytes ∧
    cmClassifyVariant? "core::intrinsics::raw_eq" = some .rawEq ∧
    cmClassifyVariant? "core::intrinsics::typed_swap_nonoverlapping" = some .typedSwap ∧
    cmClassifyVariant? "core::intrinsics::ptr_offset_from" = some .ptrOffsetFrom ∧
    cmClassifyVariant? "core::intrinsics::ptr_offset_from_unsigned" = some .ptrOffsetFromUnsigned ∧
    cmClassifyVariant? "core::intrinsics::ptr_mask" = some .ptrMask ∧
    cmClassifyVariant? "core::intrinsics::black_box" = some .blackBox ∧
    cmClassifyVariant? "core::ptr::copy" = none ∧
    cmClassifyVariant? "core::ptr::swap_nonoverlapping" = none ∧
    cmClassifyVariant? "core::mem::swap" = none ∧
    cmClassifyVariant? "core::hint::black_box" = none ∧
    cmClassifyVariant? "core::ptr::mask" = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **Routing (`evalCoreMemPtrIntrinsicCall?`)**: for every state, target,
declarations, layouts, operands, values, locals, destination, and successor,
each of the 8 kinds dispatches to exactly its Episode 1 evaluator. -/
theorem cm_evalCoreMemPtrIntrinsicCall?_routes (s : MachineState) (t : ResolvedCallTarget)
    (decls : List MirAst.LocalDecl) (lay : LayoutTable) (ops : List Operand) (vals : List Value)
    (locals : List LocalSlot) (dest : Place) (tgt : Option BasicBlockIdx) :
    evalCoreMemPtrIntrinsicCall? .copy s t decls lay ops vals locals dest tgt =
      some (evalCopyCall s t decls lay ops vals locals dest tgt) ∧
    evalCoreMemPtrIntrinsicCall? .compareBytes s t decls lay ops vals locals dest tgt =
      some (evalCompareBytesCall s decls lay vals locals dest tgt) ∧
    evalCoreMemPtrIntrinsicCall? .rawEq s t decls lay ops vals locals dest tgt =
      some (evalRawEqCall s t decls lay ops vals locals dest tgt) ∧
    evalCoreMemPtrIntrinsicCall? .typedSwapNonOverlapping s t decls lay ops vals locals dest tgt =
      some (evalTypedSwapNonOverlappingCall s t decls lay ops vals locals dest tgt) ∧
    evalCoreMemPtrIntrinsicCall? .ptrOffsetFrom s t decls lay ops vals locals dest tgt =
      some (evalPtrOffsetFromCall s t decls lay ops vals locals dest tgt false) ∧
    evalCoreMemPtrIntrinsicCall? .ptrOffsetFromUnsigned s t decls lay ops vals locals dest tgt =
      some (evalPtrOffsetFromCall s t decls lay ops vals locals dest tgt true) ∧
    evalCoreMemPtrIntrinsicCall? .ptrMask s t decls lay ops vals locals dest tgt =
      some (evalPtrMaskCall s decls lay vals locals dest tgt) ∧
    evalCoreMemPtrIntrinsicCall? .blackBox s t decls lay ops vals locals dest tgt =
      some (evalBlackBoxCall s t decls lay ops vals locals dest tgt) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem cm_blt_irrefl (n : Nat) : Nat.blt n n = false := by
  cases h : Nat.blt n n with
  | false => rfl
  | true => exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_succ_le_self n)

/-- **`compare_bytes` reflexivity**: every byte list compares equal to itself. -/
theorem cm_compareUnsignedBytesI32_refl (l : List UInt8) : compareUnsignedBytesI32 l l = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [compareUnsignedBytesI32, cm_blt_irrefl]
    exact ih

/-- **`compare_bytes` result range**: the result is `0`, `1`, or `-1` as `i32`
(`0xFFFF_FFFF`), for all inputs. -/
theorem cm_compareUnsignedBytesI32_range (l r : List UInt8) :
    compareUnsignedBytesI32 l r = 0 ∨ compareUnsignedBytesI32 l r = 1 ∨
      compareUnsignedBytesI32 l r = 4294967295 := by
  induction l generalizing r with
  | nil => cases r <;> simp [compareUnsignedBytesI32]
  | cons a as ih =>
    cases r with
    | nil => simp [compareUnsignedBytesI32]
    | cons b bs =>
      simp only [compareUnsignedBytesI32]
      cases Nat.blt a.toBitVec.toNat b.toBitVec.toNat <;>
        cases Nat.blt b.toBitVec.toNat a.toBitVec.toNat <;> simp [ih bs]

/-- **`compare_bytes` antisymmetry** (equal lengths): `left > right` iff
`right < left`. -/
theorem cm_compareUnsignedBytesI32_antisymm (l r : List UInt8) (h : l.length = r.length) :
    compareUnsignedBytesI32 l r = 1 ↔ compareUnsignedBytesI32 r l = 4294967295 := by
  induction l generalizing r with
  | nil => cases r <;> simp_all [compareUnsignedBytesI32]
  | cons a as ih =>
    cases r with
    | nil => simp at h
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [compareUnsignedBytesI32]
      cases h1 : Nat.blt a.toBitVec.toNat b.toBitVec.toNat <;>
        cases h2 : Nat.blt b.toBitVec.toNat a.toBitVec.toNat <;> simp [ih bs h]
      · simp [Nat.blt_eq] at h1 h2; omega

/-- **`ptr_offset_from` same-address law** (all widths, both signednesses):
for every pointee size `0 < elemSize ≤ isize::MAX`, equal effective offsets
yield distance `0`. -/
theorem cm_evalPtrOffsetFromDistance_same_offset (ptrBytes : Nat) (unsigned : Bool)
    (elemSize off : Nat) (hPos : 0 < elemSize)
    (hLe : elemSize ≤ scalarModulus ptrBytes / 2 - 1) :
    evalPtrOffsetFromDistance ptrBytes unsigned elemSize off off = some ⟨0, ptrBytes⟩ := by
  have h0 : Nat.beq elemSize 0 = false := by
    cases elemSize with
    | zero => exact absurd hPos (Nat.lt_irrefl 0)
    | succ n => rfl
  have h1 : Nat.ble elemSize (Nat.sub (Nat.div (scalarModulus ptrBytes) 2) 1) = true :=
    Nat.ble_eq.mpr hLe
  have h2 : Nat.ble off off = true := Nat.ble_eq.mpr (Nat.le_refl off)
  have h3 : Nat.sub off off = 0 := Nat.sub_self off
  have h4 : Nat.ble 0 (Nat.sub (Nat.div (scalarModulus ptrBytes) 2) 1) = true :=
    Nat.ble_eq.mpr (Nat.zero_le _)
  have h5 : Nat.beq (Nat.mod 0 elemSize) 0 = true := by
    rw [show Nat.mod 0 elemSize = 0 from Nat.zero_mod elemSize]; rfl
  have h6 : Nat.div 0 elemSize = 0 := Nat.zero_div elemSize
  unfold evalPtrOffsetFromDistance
  simp only [h0, h1, h2, h3, h4, h5, h6, Bool.false_or, Bool.not_true, Bool.and_self]

/-- **`ptr_offset_from` ZST law**: a zero-sized pointee is always UB (`none`). -/
theorem cm_evalPtrOffsetFromDistance_zst (ptrBytes : Nat) (unsigned : Bool) (p b : Nat) :
    evalPtrOffsetFromDistance ptrBytes unsigned 0 p b = none := by
  unfold evalPtrOffsetFromDistance
  rfl

/-- **`ptr_offset_from_unsigned` negative-distance law**: `ptr < origin` is UB. -/
theorem cm_evalPtrOffsetFromDistance_unsigned_negative (ptrBytes elemSize p b : Nat)
    (hlt : p < b) :
    evalPtrOffsetFromDistance ptrBytes true elemSize p b = none := by
  have h : Nat.ble b p = false := by
    cases hb : Nat.ble b p with
    | false => rfl
    | true => exact absurd (Nat.le_of_ble_eq_true hb) (Nat.not_le_of_lt hlt)
  unfold evalPtrOffsetFromDistance
  simp only [h]
  split <;> rfl

/-- **`ptr_offset_from` exact-multiple law**: `ptr = origin + k * elemSize`
(with `k * elemSize ≤ isize::MAX`) yields exactly `k`, for both signednesses;
this is the value MiniRust computes as `PtrOffsetFrom` followed by `DivExact`. -/
theorem cm_evalPtrOffsetFromDistance_exact (ptrBytes : Nat) (unsigned : Bool)
    (elemSize b k : Nat) (hPos : 0 < elemSize)
    (hLe : elemSize ≤ scalarModulus ptrBytes / 2 - 1)
    (hDist : k * elemSize ≤ scalarModulus ptrBytes / 2 - 1) :
    evalPtrOffsetFromDistance ptrBytes unsigned elemSize (b + k * elemSize) b =
      some ⟨k, ptrBytes⟩ := by
  have h0 : Nat.beq elemSize 0 = false := by
    cases elemSize with
    | zero => exact absurd hPos (Nat.lt_irrefl 0)
    | succ n => rfl
  have h1 : Nat.ble elemSize (Nat.sub (Nat.div (scalarModulus ptrBytes) 2) 1) = true :=
    Nat.ble_eq.mpr hLe
  have h2 : Nat.ble b (b + k * elemSize) = true := Nat.ble_eq.mpr (Nat.le_add_right b _)
  have h3 : Nat.sub (b + k * elemSize) b = k * elemSize := Nat.add_sub_cancel_left b (k * elemSize)
  have h4 : Nat.ble (k * elemSize) (Nat.sub (Nat.div (scalarModulus ptrBytes) 2) 1) = true :=
    Nat.ble_eq.mpr hDist
  have hm : (k * elemSize) % elemSize = 0 := Nat.mul_mod_left k elemSize
  have h5 : Nat.beq (Nat.mod (k * elemSize) elemSize) 0 = true := by
    rw [show Nat.mod (k * elemSize) elemSize = 0 from hm]; rfl
  have h6 : Nat.div (k * elemSize) elemSize = k := Nat.mul_div_cancel k hPos
  unfold evalPtrOffsetFromDistance
  simp only [h0, h1, h2, h3, h4, h5, h6, Bool.false_or, Bool.not_true, Bool.and_self]

/-- **MiniRust `DivExact` agreement**: the exact quotient of the byte distance
`k * elemSize` by `elemSize` is `k`, as `evalPtrOffsetFromDistance` returns. -/
theorem cm_divExact_byte_distance (k elemSize : Nat) (hPos : 0 < elemSize) :
    (k * elemSize) % elemSize = 0 ∧ (k * elemSize) / elemSize = k :=
  ⟨Nat.mul_mod_left _ _, Nat.mul_div_cancel _ hPos⟩

/-! ## §3. MiniRust Reference Programs (`Mach` & `MachTB`)

Each intrinsic is executed in `MiniRustSpec.Interp` as its MiniRust reference
lowering: `raw_eq` is the native `IntrinsicOp::RawEq`; `ptr_offset_from[_unsigned]`
are the native `BinOp::PtrOffsetFrom { inbounds: true, nonneg }` followed by
`IntBinOp::DivExact` by `size_of::<u32>()`; `copy` is a whole-value load (the
snapshot) followed by a store; `typed_swap_nonoverlapping` is the typed
read(x) -> read(y) -> write(x) -> write(y) sequence; `compare_bytes` loads both
whole `[u8; n]` slices first (eagerly, so an uninitialized byte anywhere is UB)
and then compares bytewise as unsigned integers; `ptr_mask` reads the address
by a provenance-free `Transmute` and moves the pointer with the
non-`inbounds` `PtrOffset` (strict provenance: no `expose`); `black_box` is a
value copy. Every program ends in a self-loop, so running more steps than the
program needs leaves the observed return local `_0` (allocation `0`) fixed. -/

/-- `u32` as a MiniRust integer type. -/
@[reducible] def cmU32It : IntType := ⟨.Unsigned, ⟨4⟩⟩
@[reducible] def cmRawMrTy : Gen.Type := .Ptr (.Raw .None)
@[reducible] def cmI16MrTy : Gen.Type := .Int ⟨.Signed, ⟨2⟩⟩
@[reducible] def cmIsizeMrTy : Gen.Type := .Int ⟨.Signed, ⟨8⟩⟩
@[reducible] def cmU32RefMrTy : Gen.Type := refTy .not cmU32It
/-- `&()`: a reference to a sized, inhabited zero-sized pointee. -/
@[reducible] def cmUnitPointee : PointeeInfo :=
  { layout := .Sized ⟨0⟩ ⟨1⟩, inhabited := true, unsafe_cells := .Sized [], freeze := true,
    unpin := true }
@[reducible] def cmUnitRefMrTy : Gen.Type := .Ptr (.Ref .Immutable cmUnitPointee)
@[reducible] def cmArrMrTy (elem : Gen.Type) (n : Nat) : Gen.Type := .Array elem n

def cmLd (i : Nat) : ValueExpr := .Load (.Local (localName i))
def cmLc (i : Nat) : PlaceExpr := .Local (localName i)
def cmInt (n : Int) (t : Gen.Type) : ValueExpr := .Constant (.Int n) t
def cmBlk (ss : List Gen.Statement) (t : Gen.Terminator) : Gen.BasicBlock := ⟨ss, t, .Regular⟩
/-- The final self-loop block. -/
def cmLoopBb (i : Nat) : Gen.BbName × Gen.BasicBlock := (bbName i, cmBlk [] (.Goto (bbName i)))

/-- Address of local `i`'s stack allocation in every corpus machine. -/
def cmMrLocalAddr (i : Nat) : Nat := 128 * (i + 1)

/-- Stack allocations of the locals, numbered from `i`. -/
def cmMrLocalAllocs : Nat → List (List Byte × Nat) → List Gen.Allocation
  | _, [] => []
  | i, (bs, al) :: rest => mkStackAlloc (cmMrLocalAddr i) bs al :: cmMrLocalAllocs (i + 1) rest

/-- Bytes of a thin pointer to address `addr` in MiniRust allocation `idx`. -/
def cmMrPtr (addr idx : Nat) : List Byte := ptrBytes addr (some (⟨idx⟩, ()))

/-- `n` uninitialized bytes. -/
def cmUninit (n : Nat) : List Byte := List.replicate n .Uninit

/-- Initialized bytes without provenance. -/
def cmInitBytes (l : List Nat) : List Byte := l.map fun n => .Init (UInt8.ofNat n) none

/-- A corpus machine: root frame running `fn` with locals `_0.._{k-1}` backed by
allocations `0..k-1` (initial bytes and alignment from `locals`), followed by
the data allocations `data` (address, bytes, alignment) at indices `k..`. -/
def cmMrMach (fn : Gen.Function) (locals : List (List Byte × Nat))
    (data : List (Nat × List Byte × Nat)) : Mach :=
  mkMrMach (mkMrProg [(fnName 0, fn)])
    (cmMrLocalAllocs 0 locals ++ data.map fun (a, bs, al) => mkStackAlloc a bs al)
    [mkRootFrame fn ((List.range locals.length).map fun i =>
      (localName i, ⟨cmMrLocalAddr i, some (⟨i⟩, ())⟩))]

-- 1. copy
/-- `*_2 = *_1 (at ty); _0 = *_read (at u32)`. -/
def cmMrCopyFn (ty : Gen.Type) (readLocal : Nat) (nLocals : Nat) (validateRef : Bool) : Gen.Function :=
  mkMrFn ((List.range nLocals).map fun i =>
      (localName i, if i == 0 then u32MrTy else if validateRef && i == 3 then cmU32RefMrTy else cmRawMrTy))
    ((List.range nLocals).drop 1 |>.map localName) (localName 0)
    [(bbName 0, cmBlk
        ((if validateRef then [.Validate (cmLc 3) true] else []) ++
         [.Assign (.Deref (cmLd 2) ty) (.Load (.Deref (cmLd 1) ty)),
          .Assign (cmLc 0) (.Load (.Deref (cmLd readLocal) u32MrTy))])
        (.Goto (bbName 1))),
     cmLoopBb 1]

/-- `copy::<u32>(src, &G101, 1); _0 = *dst` with `src` given by `srcBytes`. -/
def cmMrCopyMach (srcBytes : List Byte) : Mach :=
  cmMrMach (cmMrCopyFn u32MrTy 2 3 false)
    [(cmUninit 4, 4), (srcBytes, 8), (cmMrPtr 1088 4, 8)]
    [(1024, scalarBytes cmU32It 42, 4), (1088, scalarBytes cmU32It 0x04030201, 4)]

/-- Overlapping `copy::<u16>(&G[0], &G[2], 2); _0 = *(&G[4] as *const u32)`. -/
def cmMrCopyOverlapMach : Mach :=
  cmMrMach (cmMrCopyFn (cmArrMrTy (.Int ⟨.Unsigned, ⟨2⟩⟩) 2) 3 4 false)
    [(cmUninit 4, 4), (cmMrPtr 1024 4, 8), (cmMrPtr 1026 4, 8), (cmMrPtr 1028 4, 8)]
    [(1024, cmInitBytes [1, 2, 3, 4, 5, 6, 7, 8], 4)]

/-- Mode-sensitive copy: `Validate(_3: &u32 -> dst, fn_entry)` installs a
protected (Tree Borrows) shared reborrow of the destination; the copy then
writes through the root provenance of `_2`. -/
def cmMrCopyModeMach : Mach :=
  cmMrMach (cmMrCopyFn u32MrTy 2 4 true)
    [(cmUninit 4, 4), (cmMrPtr 1024 4, 8), (cmMrPtr 1088 5, 8), (cmMrPtr 1088 5, 8)]
    [(1024, scalarBytes cmU32It 42, 4), (1088, scalarBytes cmU32It 11, 4)]

-- 2. compare_bytes
/-- Eager unsigned lexicographic comparison of two `[u8; n]` slices. Blocks:
`bb0` loads both slices; `bb(1+i)` computes `_5 = a[i] as i16 - b[i] as i16`
and continues on `0`; `bb(n+11)` branches on the sign; `bb(n+1)`/`bb(n+2)`/
`bb(n+3)` write `-1`/`1`/`0`; `bb(n+4)` loops. -/
def cmMrCmpBlocks (n : Nat) : List (Gen.BbName × Gen.BasicBlock) :=
  let neg := n + 1
  let pos := n + 2
  let eq := n + 3
  let fin := n + 4
  let sign := n + 11
  let diffBlock (i : Nat) : Gen.BbName × Gen.BasicBlock :=
    (bbName (1 + i), cmBlk [.Assign (cmLc 5) (.BinOp (.Int .Sub)
        (.UnOp (.Cast (.IntToInt ⟨.Signed, ⟨2⟩⟩)) (.Load (.Index (cmLc 3) (cmInt i usizeMrTy))))
        (.UnOp (.Cast (.IntToInt ⟨.Signed, ⟨2⟩⟩)) (.Load (.Index (cmLc 4) (cmInt i usizeMrTy)))))]
      (.Switch (cmLd 5) ⟨[(0, bbName (if i + 1 = n then eq else 2 + i))]⟩ (bbName sign)))
  [(bbName 0, cmBlk [.Assign (cmLc 3) (.Load (.Deref (cmLd 1) (cmArrMrTy u8MrTy n))),
                     .Assign (cmLc 4) (.Load (.Deref (cmLd 2) (cmArrMrTy u8MrTy n)))] (.Goto (bbName 1)))] ++
  (List.range n).map diffBlock ++
  [(bbName sign, cmBlk [] (.Switch (.UnOp (.Cast (.Transmute u8MrTy)) (.BinOp (.Rel .Lt) (cmLd 5) (cmInt 0 cmI16MrTy)))
      ⟨[(1, bbName neg)]⟩ (bbName pos))),
   (bbName neg, cmBlk [.Assign (cmLc 0) (cmInt (-1) i32MrTy)] (.Goto (bbName fin))),
   (bbName pos, cmBlk [.Assign (cmLc 0) (cmInt 1 i32MrTy)] (.Goto (bbName fin))),
   (bbName eq, cmBlk [.Assign (cmLc 0) (cmInt 0 i32MrTy)] (.Goto (bbName fin))),
   cmLoopBb fin]

def cmMrCmpMach (n : Nat) (a b : List Byte) : Mach :=
  cmMrMach
    (mkMrFn [(localName 0, i32MrTy), (localName 1, cmRawMrTy), (localName 2, cmRawMrTy),
        (localName 3, cmArrMrTy u8MrTy n), (localName 4, cmArrMrTy u8MrTy n), (localName 5, cmI16MrTy)]
      [localName 1, localName 2] (localName 0) (cmMrCmpBlocks n))
    [(cmUninit 4, 4), (cmMrPtr 1024 6, 8), (cmMrPtr 1088 7, 8), (cmUninit n, 1), (cmUninit n, 1),
     (cmUninit 2, 2)]
    [(1024, a, 1), (1088, b, 1)]

-- 3. raw_eq
def cmMrRawEqFn (refTy : Gen.Type) : Gen.Function :=
  mkMrFn [(localName 0, .Bool), (localName 1, refTy), (localName 2, refTy)]
    [localName 1, localName 2] (localName 0)
    [(bbName 0, cmBlk [] (.Intrinsic .RawEq [cmLd 1, cmLd 2] (cmLc 0) (some (bbName 1)))),
     cmLoopBb 1]

/-- `raw_eq::<u32>(&a, &b)`. -/
def cmMrRawEqMach (a b : List Byte) : Mach :=
  cmMrMach (cmMrRawEqFn cmU32RefMrTy) [(cmUninit 1, 1), (cmMrPtr 1024 3, 8), (cmMrPtr 1088 4, 8)]
    [(1024, a, 4), (1088, b, 4)]

/-- `raw_eq::<()>` on two equal dangling, aligned, non-null references. -/
def cmMrRawEqZstMach : Mach :=
  cmMrMach (cmMrRawEqFn cmUnitRefMrTy) [(cmUninit 1, 1), (ptrBytes 4096 none, 8), (ptrBytes 4096 none, 8)] []

-- 4. typed_swap_nonoverlapping
def cmMrSwapFn (readLocal : Nat) : Gen.Function :=
  mkMrFn [(localName 0, u32MrTy), (localName 1, cmRawMrTy), (localName 2, cmRawMrTy), (localName 3, u32MrTy)]
    [localName 1, localName 2] (localName 0)
    [(bbName 0, cmBlk [.Assign (cmLc 3) (.Load (.Deref (cmLd 1) u32MrTy)),
                       .Assign (.Deref (cmLd 1) u32MrTy) (.Load (.Deref (cmLd 2) u32MrTy)),
                       .Assign (.Deref (cmLd 2) u32MrTy) (cmLd 3),
                       .Assign (cmLc 0) (.Load (.Deref (cmLd readLocal) u32MrTy))] (.Goto (bbName 1))),
     cmLoopBb 1]

def cmMrSwapMach (readLocal : Nat) (xBytes yBytes : List Byte) (data : List (Nat × List Byte × Nat)) : Mach :=
  cmMrMach (cmMrSwapFn readLocal) [(cmUninit 4, 4), (xBytes, 8), (yBytes, 8), (cmUninit 4, 4)] data

/-- Swap two disjoint allocations `7` and `9`. -/
def cmMrSwapTwoMach (readLocal : Nat) (xBytes : List Byte) : Mach :=
  cmMrSwapMach readLocal xBytes (cmMrPtr 1088 5)
    [(1024, scalarBytes cmU32It 7, 4), (1088, scalarBytes cmU32It 9, 4)]

/-- Swap two disjoint elements of one allocation `[5, 6]`. -/
def cmMrSwapSameAllocMach : Mach :=
  cmMrSwapMach 1 (cmMrPtr 1024 4) (cmMrPtr 1028 4)
    [(1024, scalarBytes cmU32It 5 ++ scalarBytes cmU32It 6, 4)]

-- 5./6. ptr_offset_from[_unsigned]
def cmMrPofFn (unsigned : Bool) : Gen.Function :=
  let dist : ValueExpr :=
    .BinOp (.Int .DivExact) (.BinOp (.PtrOffsetFrom true unsigned) (cmLd 1) (cmLd 2)) (cmInt 4 cmIsizeMrTy)
  mkMrFn [(localName 0, if unsigned then usizeMrTy else cmIsizeMrTy), (localName 1, cmRawMrTy),
      (localName 2, cmRawMrTy)]
    [localName 1, localName 2] (localName 0)
    [(bbName 0, cmBlk [.Assign (cmLc 0)
        (if unsigned then .UnOp (.Cast (.IntToInt IntType.usize_ty)) dist else dist)] (.Goto (bbName 1))),
     cmLoopBb 1]

def cmMrPofMach (unsigned : Bool) (a b : List Byte) : Mach :=
  cmMrMach (cmMrPofFn unsigned) [(cmUninit 8, 8), (a, 8), (b, 8)]
    [(1024, cmInitBytes (List.replicate 16 0), 16), (2048, cmInitBytes (List.replicate 16 0), 16)]

-- 7. ptr_mask
/-- `_2 = transmute::<_, isize>(_1); _0 = _1.wrapping_byte_offset((_2 & mask) - _2)`. -/
def cmMrMaskFn (mask : Int) : Gen.Function :=
  mkMrFn [(localName 0, cmRawMrTy), (localName 1, cmRawMrTy), (localName 2, cmIsizeMrTy)]
    [localName 1] (localName 0)
    [(bbName 0, cmBlk [.Assign (cmLc 2) (.UnOp (.Cast (.Transmute cmIsizeMrTy)) (cmLd 1)),
                       .Assign (cmLc 0) (.BinOp (.PtrOffset false) (cmLd 1)
                         (.BinOp (.Int .Sub) (.BinOp (.Int .BitAnd) (cmLd 2) (cmInt mask cmIsizeMrTy)) (cmLd 2)))]
        (.Goto (bbName 1))),
     cmLoopBb 1]

def cmMrMaskMach (mask : Int) (ptr : List Byte) : Mach :=
  cmMrMach (cmMrMaskFn mask) [(cmUninit 8, 8), (ptr, 8), (cmUninit 8, 8)]
    [(1024, cmInitBytes (List.replicate 16 0), 16)]

-- 8. black_box
def cmMrBlackBoxFn (ty : Gen.Type) : Gen.Function :=
  mkMrFn [(localName 0, ty), (localName 1, ty), (localName 2, cmRawMrTy)] [localName 1] (localName 0)
    [(bbName 0, cmBlk [.Assign (cmLc 0) (cmLd 1)] (.Goto (bbName 1))), cmLoopBb 1]

def cmMrBlackBoxMach (ty : Gen.Type) (sz : Nat) (v : List Byte) : Mach :=
  cmMrMach (cmMrBlackBoxFn ty) [(cmUninit sz, sz), (v, sz), (cmUninit 8, 8)]
    [(1024, cmInitBytes (List.replicate 16 0), 16)]

/-! ## §6. Canonical Executable MiniRust Corpus Observation Interface -/

/-- MiniRust execution mode: `BasicMemory` (`Mach`) versus `TreeBorrowsMemory` (`MachTB`). -/
inductive CmMrMode : Type where
  | basicMemory
  | treeBorrows
  deriving DecidableEq, Repr

/-- Raw observation produced directly by `MiniRustSpec.Interp`: the bytes (with
provenance) of the return allocation `0`, or the fault class. -/
inductive CmMrObs : Type where
  | retBytes (bs : List TBByteOutcome)
  | ub
  | unsupported
  deriving DecidableEq

/-- Run `n` steps of `MiniRustSpec.Interp` in mode `mode` and extract allocation
`0`'s observable bytes, or `.ub` / `.unsupported`. -/
def cmRunMrObs (mode : CmMrMode) (n : Nat) (m : Mach) : CmMrObs :=
  match mode with
  | .basicMemory =>
    match Interp.steps n m with
    | .ok m' =>
      match m'.mem.memory.allocations[0]? with
      | some a => .retBytes (a.data.map (projByteTB ∘ liftByteTB))
      | none => .unsupported
    | .error (.ub _) => .ub
    | .error _ => .unsupported
  | .treeBorrows =>
    match Interp.stepsTB n (liftMachToTB m) with
    | .ok m' =>
      match m'.mem.memory.mem.allocations[0]? with
      | some a => .retBytes (a.data.map projByteTB)
      | none => .unsupported
    | .error (.ub _) => .ub
    | .error _ => .unsupported

/-- The MiniRust reference machine of each `(variant, case)` key. -/
def cmMrMachine : CmVariant → CmCase → Mach
  | .copy, .okPrimary => cmMrCopyMach (cmMrPtr 1024 3)
  | .copy, .okSecondary => cmMrCopyOverlapMach
  | .copy, .ubFault => cmMrCopyMach (ptrBytes 0 none)
  | .copy, .modeCase => cmMrCopyModeMach
  | .compareBytes, .okPrimary => cmMrCmpMach 3 (cmInitBytes [1, 2, 3]) (cmInitBytes [1, 2, 4])
  | .compareBytes, .okSecondary => cmMrCmpMach 1 (cmInitBytes [0x80]) (cmInitBytes [1])
  | .compareBytes, .ubFault => cmMrCmpMach 3 (cmInitBytes [2, 0] ++ cmUninit 1) (cmInitBytes [1, 2, 4])
  | .compareBytes, .modeCase => cmMrCmpMach 3 (cmInitBytes [1, 2, 3]) (cmInitBytes [1, 2, 3])
  | .rawEq, .okPrimary => cmMrRawEqMach (scalarBytes cmU32It 7) (scalarBytes cmU32It 7)
  | .rawEq, .okSecondary => cmMrRawEqMach (scalarBytes cmU32It 7) (scalarBytes cmU32It 9)
  | .rawEq, .ubFault => cmMrRawEqMach (cmInitBytes [7] ++ cmUninit 1 ++ cmInitBytes [0, 0]) (scalarBytes cmU32It 9)
  | .rawEq, .modeCase => cmMrRawEqZstMach
  | .typedSwap, .okPrimary => cmMrSwapTwoMach 1 (cmMrPtr 1024 4)
  | .typedSwap, .okSecondary => cmMrSwapTwoMach 2 (cmMrPtr 1024 4)
  | .typedSwap, .ubFault => cmMrSwapTwoMach 1 (ptrBytes 0 none)
  | .typedSwap, .modeCase => cmMrSwapSameAllocMach
  | .ptrOffsetFrom, .okPrimary => cmMrPofMach false (cmMrPtr 1036 3) (cmMrPtr 1028 3)
  | .ptrOffsetFrom, .okSecondary => cmMrPofMach false (cmMrPtr 1028 3) (cmMrPtr 1036 3)
  | .ptrOffsetFrom, .ubFault => cmMrPofMach false (cmMrPtr 1028 3) (cmMrPtr 2060 4)
  | .ptrOffsetFrom, .modeCase => cmMrPofMach false (ptrBytes 4096 none) (ptrBytes 4096 none)
  | .ptrOffsetFromUnsigned, .okPrimary => cmMrPofMach true (cmMrPtr 1036 3) (cmMrPtr 1028 3)
  | .ptrOffsetFromUnsigned, .okSecondary => cmMrPofMach true (cmMrPtr 1040 3) (cmMrPtr 1024 3)
  | .ptrOffsetFromUnsigned, .ubFault => cmMrPofMach true (cmMrPtr 1028 3) (cmMrPtr 1036 3)
  | .ptrOffsetFromUnsigned, .modeCase => cmMrPofMach true (cmMrPtr 1030 3) (cmMrPtr 1024 3)
  | .ptrMask, .okPrimary => cmMrMaskMach (-8) (cmMrPtr 1036 3)
  | .ptrMask, .okSecondary => cmMrMaskMach (-1) (cmMrPtr 1036 3)
  | .ptrMask, .ubFault => cmMrMaskMach (-8) (cmUninit 8)
  | .ptrMask, .modeCase => cmMrMaskMach (-4) (cmMrPtr 1030 3)
  | .blackBox, .okPrimary => cmMrBlackBoxMach u32MrTy 4 (scalarBytes cmU32It 77)
  | .blackBox, .okSecondary => cmMrBlackBoxMach cmRawMrTy 8 (cmMrPtr 1028 3)
  | .blackBox, .ubFault => cmMrBlackBoxMach u32MrTy 4 (cmUninit 4)
  | .blackBox, .modeCase => cmMrBlackBoxMach .Bool 1 (cmInitBytes [1])

/-- Step budget of every MiniRust corpus execution. -/
def cmMrFuel : Nat := 16

/-- Direct `MiniRustSpec.Interp` observation for every `(mode, variant, case)` key. -/
def cmMrObserve (mode : CmMrMode) (v : CmVariant) (c : CmCase) : CmMrObs :=
  cmRunMrObs mode cmMrFuel (cmMrMachine v c)

/-- Mode sensitivity certified directly on `cmMrObserve`: `copy.modeCase`
returns `42` under `BasicMemory` and faults `.ub` under `TreeBorrowsMemory`. -/
theorem cmMrObserve_copy_mode_sensitivity :
    cmMrObserve .basicMemory .copy .modeCase =
      .retBytes ((scalarBytes cmU32It 42).map (projByteTB ∘ liftByteTB)) ∧
    cmMrObserve .treeBorrows .copy .modeCase = .ub :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- The raw observation of a `BasicMemory` byte list. -/
def cmMrBytesObs (bs : List Byte) : CmMrObs :=
  .retBytes (bs.map (projByteTB ∘ liftByteTB))

/-- The frozen dictionary of distinct raw MiniRust observations of the corpus;
the class of an observation is its index:

| class | raw observation                          |
|------:|------------------------------------------|
| 0     | `u32` `42`                               |
| 1     | `u32` `0x08070403`                       |
| 2     | `i32` `-1`                               |
| 3     | `i32` `1`                                |
| 4     | `i32` `0`                                |
| 5     | `bool` `true`                            |
| 6     | `bool` `false`                           |
| 7     | `u32` `9`                                |
| 8     | `u32` `7`                                |
| 9     | `u32` `6`                                |
| 10    | `isize`/`usize` `2`                      |
| 11    | `isize` `-2`                             |
| 12    | `isize` `0`                              |
| 13    | `usize` `4`                              |
| 14    | pointer to allocation `3` at `1032`      |
| 15    | pointer to allocation `3` at `1036`      |
| 16    | pointer to allocation `3` at `1028`      |
| 17    | `u32` `77`                               |
| 18    | undefined behavior                       |
| 19    | unsupported                              | -/
def cmMrObsDict : List CmMrObs :=
  [ cmMrBytesObs (scalarBytes cmU32It 42),
    cmMrBytesObs (scalarBytes cmU32It 0x08070403),
    cmMrBytesObs (cmInitBytes [255, 255, 255, 255]),
    cmMrBytesObs (cmInitBytes [1, 0, 0, 0]),
    cmMrBytesObs (cmInitBytes [0, 0, 0, 0]),
    cmMrBytesObs (cmInitBytes [1]),
    cmMrBytesObs (cmInitBytes [0]),
    cmMrBytesObs (scalarBytes cmU32It 9),
    cmMrBytesObs (scalarBytes cmU32It 7),
    cmMrBytesObs (scalarBytes cmU32It 6),
    cmMrBytesObs (scalarBytes IntType.usize_ty 2),
    cmMrBytesObs (scalarBytes IntType.usize_ty (2 ^ 64 - 2)),
    cmMrBytesObs (scalarBytes IntType.usize_ty 0),
    cmMrBytesObs (scalarBytes IntType.usize_ty 4),
    cmMrBytesObs (cmMrPtr 1032 3),
    cmMrBytesObs (cmMrPtr 1036 3),
    cmMrBytesObs (cmMrPtr 1028 3),
    cmMrBytesObs (scalarBytes cmU32It 77),
    .ub,
    .unsupported ]

/-- Index of the first entry of `dict` equal to `o`, counting from `i`. -/
def cmMrObsClassAux (o : CmMrObs) : List CmMrObs → Nat → Option Nat
  | [], _ => none
  | d :: ds, i => if d = o then some i else cmMrObsClassAux o ds (i + 1)

/-- The class of a raw observation (its index in `cmMrObsDict`). -/
def cmMrObsClass (o : CmMrObs) : Option Nat :=
  cmMrObsClassAux o cmMrObsDict 0

/-- The class of the direct `MiniRustSpec.Interp` observation of a key. -/
def cmMrObserveClass (mode : CmMrMode) (v : CmVariant) (c : CmCase) : Option Nat :=
  cmMrObsClass (cmMrObserve mode v c)

/-- Boolean check that `cmMrObsDict` has no duplicate entries and that every
entry's class is its own index. -/
def cmMrObsDictDistinct : Bool :=
  (List.range cmMrObsDict.length).all fun i =>
    decide ((cmMrObsDict[i]?).bind cmMrObsClass = some i) &&
    (List.range cmMrObsDict.length).all fun j =>
      decide (i = j) || decide (cmMrObsDict[i]? ≠ cmMrObsDict[j]?)

/-- **Kernel-checked injectivity of the class dictionary**. -/
theorem cmMrObsDict_distinct : cmMrObsDictDistinct = true := by
  decide +kernel

/-- The frozen 64-key MiniRust observation-class table. -/
def cmMrExpectedClass (mode : CmMrMode) : CmVariant → CmCase → Nat
  | .copy, .okPrimary => 0
  | .copy, .okSecondary => 1
  | .copy, .ubFault => 18
  | .copy, .modeCase =>
    match mode with
    | .basicMemory => 0
    | .treeBorrows => 18
  | .compareBytes, .okPrimary => 2
  | .compareBytes, .okSecondary => 3
  | .compareBytes, .ubFault => 18
  | .compareBytes, .modeCase => 4
  | .rawEq, .okPrimary => 5
  | .rawEq, .okSecondary => 6
  | .rawEq, .ubFault => 18
  | .rawEq, .modeCase => 5
  | .typedSwap, .okPrimary => 7
  | .typedSwap, .okSecondary => 8
  | .typedSwap, .ubFault => 18
  | .typedSwap, .modeCase => 9
  | .ptrOffsetFrom, .okPrimary => 10
  | .ptrOffsetFrom, .okSecondary => 11
  | .ptrOffsetFrom, .ubFault => 18
  | .ptrOffsetFrom, .modeCase => 12
  | .ptrOffsetFromUnsigned, .okPrimary => 10
  | .ptrOffsetFromUnsigned, .okSecondary => 13
  | .ptrOffsetFromUnsigned, .ubFault => 18
  | .ptrOffsetFromUnsigned, .modeCase => 18
  | .ptrMask, .okPrimary => 14
  | .ptrMask, .okSecondary => 15
  | .ptrMask, .ubFault => 18
  | .ptrMask, .modeCase => 16
  | .blackBox, .okPrimary => 17
  | .blackBox, .okSecondary => 16
  | .blackBox, .ubFault => 18
  | .blackBox, .modeCase => 5

/-- **Kernel-checked MiniRust table**: on all 64 keys, executing
`MiniRustSpec.Interp.{steps, stepsTB}` yields a raw observation of exactly the
frozen class. -/
theorem cmMrObserveClass_table (mode : CmMrMode) (v : CmVariant) (c : CmCase) :
    cmMrObserveClass mode v c = some (cmMrExpectedClass mode v c) := by
  cases mode <;> cases v <;> cases c <;> decide +kernel


/-! ## §4. Concrete Three-Way Witnesses (Trusted `stepMirFn`, `Mach`, `MachTB` with `MachTB.wfLive`) -/

/-- The bytes of a `BasicMemory` allocation projected for comparison with `MachTB`. -/
def cmProjBM (bs : List Byte) : List TBByteOutcome := bs.map (projByteTB ∘ liftByteTB)

/-- **`copy` three-way witness**: `42` on Trusted, `Mach`, and `MachTB` (with
`MachTB.wfLive`); the overlapping `memmove` snapshot value `0x08070403` (a naive
forward byte loop would give `0x08070201`); null source UB on all three; and the
`basic`/`Mach` vs. `protectedTB`/`MachTB` flip. -/
theorem cm_copy_three_way_witness :
    cmTrustedObserve false .copy .okPrimary = .scalar 42 4 ∧
    (∃ m', Interp.steps cmMrFuel (cmMrMachine .copy .okPrimary) = .ok m' ∧
      m'.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes cmU32It 42)) ∧
    (∃ m', Interp.stepsTB cmMrFuel (liftMachToTB (cmMrMachine .copy .okPrimary)) = .ok m' ∧
      MachTB.wfLive m' ∧
      m'.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some (cmProjBM (scalarBytes cmU32It 42))) ∧
    cmTrustedObserve false .copy .okSecondary = .scalar 0x08070403 4 ∧
    cmMrObserve .basicMemory .copy .okSecondary = cmMrBytesObs (scalarBytes cmU32It 0x08070403) ∧
    cmTrustedObserve false .copy .ubFault = .ub ∧
    (interpUbMsg (Interp.steps cmMrFuel (cmMrMachine .copy .ubFault))).isSome = true ∧
    (interpUbMsg (Interp.stepsTB cmMrFuel (liftMachToTB (cmMrMachine .copy .ubFault)))).isSome = true ∧
    cmTrustedObserve false .copy .modeCase = .scalar 42 4 ∧
    cmTrustedObserve true .copy .modeCase = .ub ∧
    (∃ m', Interp.steps cmMrFuel (cmMrMachine .copy .modeCase) = .ok m' ∧
      m'.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes cmU32It 42)) ∧
    (interpUbMsg (Interp.stepsTB cmMrFuel (liftMachToTB (cmMrMachine .copy .modeCase)))).isSome = true :=
  ⟨by decide +kernel, ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, ok_of_map_toOption (by decide +kernel), by decide +kernel⟩

/-- **`compare_bytes` three-way witness**: `-1` (lexicographic), `1` (unsigned:
`0x80 > 0x01`), eager uninitialized-byte UB even though byte `0` already
decides, and `0` on equal slices — on Trusted, `Mach`, and `MachTB` (`wfLive`). -/
theorem cm_compareBytes_three_way_witness :
    cmTrustedObserve false .compareBytes .okPrimary = .scalar 0xFFFFFFFF 4 ∧
    (∃ m', Interp.stepsTB cmMrFuel (liftMachToTB (cmMrMachine .compareBytes .okPrimary)) = .ok m' ∧
      MachTB.wfLive m' ∧
      m'.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some (cmProjBM (cmInitBytes [255, 255, 255, 255]))) ∧
    cmMrObserve .basicMemory .compareBytes .okPrimary = cmMrBytesObs (cmInitBytes [255, 255, 255, 255]) ∧
    cmTrustedObserve false .compareBytes .okSecondary = .scalar 1 4 ∧
    cmMrObserve .basicMemory .compareBytes .okSecondary = cmMrBytesObs (cmInitBytes [1, 0, 0, 0]) ∧
    cmTrustedObserve false .compareBytes .ubFault = .ub ∧
    cmMrObserve .basicMemory .compareBytes .ubFault = .ub ∧
    cmMrObserve .treeBorrows .compareBytes .ubFault = .ub ∧
    cmTrustedObserve false .compareBytes .modeCase = .scalar 0 4 ∧
    cmMrObserve .treeBorrows .compareBytes .modeCase = .retBytes (cmProjBM (cmInitBytes [0, 0, 0, 0])) :=
  ⟨by decide +kernel, ok_stepsTB_wfLive (by decide +kernel), by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel⟩

/-- **`raw_eq` three-way witness** (`MiniRustSpec.Interp.evalIntrinsic .RawEq`):
equal `true`, unequal `false`, uninitialized-byte UB, ZST `true`. -/
theorem cm_rawEq_three_way_witness :
    cmTrustedObserve false .rawEq .okPrimary = .scalar 1 1 ∧
    (∃ m', Interp.stepsTB cmMrFuel (liftMachToTB (cmMrMachine .rawEq .okPrimary)) = .ok m' ∧
      MachTB.wfLive m' ∧
      m'.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some (cmProjBM (cmInitBytes [1]))) ∧
    cmTrustedObserve false .rawEq .okSecondary = .scalar 0 1 ∧
    cmMrObserve .basicMemory .rawEq .okSecondary = cmMrBytesObs (cmInitBytes [0]) ∧
    cmTrustedObserve false .rawEq .ubFault = .ub ∧
    Interp.steps cmMrFuel (cmMrMachine .rawEq .ubFault) =
      .error (.ub "invalid argument to `RawEq` intrinsic: byte is uninitialized") ∧
    cmTrustedObserve false .rawEq .modeCase = .scalar 1 1 ∧
    cmMrObserve .treeBorrows .rawEq .modeCase = .retBytes (cmProjBM (cmInitBytes [1])) :=
  ⟨by decide +kernel, ok_stepsTB_wfLive (by decide +kernel), by decide +kernel, by decide +kernel,
   by decide +kernel, eq_error_ub_of_interpUbMsg (by decide +kernel), by decide +kernel,
   by decide +kernel⟩

/-- **`typed_swap_nonoverlapping` three-way witness**: `*x` and `*y` after
swapping two allocations, null UB, and disjoint elements of one allocation. -/
theorem cm_typedSwap_three_way_witness :
    cmTrustedObserve false .typedSwap .okPrimary = .scalar 9 4 ∧
    (∃ m', Interp.stepsTB cmMrFuel (liftMachToTB (cmMrMachine .typedSwap .okPrimary)) = .ok m' ∧
      MachTB.wfLive m' ∧
      m'.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some (cmProjBM (scalarBytes cmU32It 9))) ∧
    cmTrustedObserve false .typedSwap .okSecondary = .scalar 7 4 ∧
    cmMrObserve .basicMemory .typedSwap .okSecondary = cmMrBytesObs (scalarBytes cmU32It 7) ∧
    cmTrustedObserve false .typedSwap .ubFault = .ub ∧
    cmMrObserve .basicMemory .typedSwap .ubFault = .ub ∧
    cmTrustedObserve false .typedSwap .modeCase = .scalar 6 4 ∧
    cmMrObserve .treeBorrows .typedSwap .modeCase = .retBytes (cmProjBM (scalarBytes cmU32It 6)) :=
  ⟨by decide +kernel, ok_stepsTB_wfLive (by decide +kernel), by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **`ptr_offset_from` three-way witness** (`BinOp::PtrOffsetFrom { inbounds:
true, nonneg: false }`): `2`, `-2`, cross-allocation UB, dangling same-address
`0`. -/
theorem cm_ptrOffsetFrom_three_way_witness :
    cmTrustedObserve false .ptrOffsetFrom .okPrimary = .scalar 2 8 ∧
    (∃ m', Interp.stepsTB cmMrFuel (liftMachToTB (cmMrMachine .ptrOffsetFrom .okPrimary)) = .ok m' ∧
      MachTB.wfLive m' ∧
      m'.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some (cmProjBM (scalarBytes IntType.usize_ty 2))) ∧
    cmTrustedObserve false .ptrOffsetFrom .okSecondary = .scalar (2 ^ 64 - 2) 8 ∧
    cmMrObserve .basicMemory .ptrOffsetFrom .okSecondary =
      cmMrBytesObs (scalarBytes IntType.usize_ty (2 ^ 64 - 2)) ∧
    cmTrustedObserve false .ptrOffsetFrom .ubFault = .ub ∧
    Interp.steps cmMrFuel (cmMrMachine .ptrOffsetFrom .ubFault) =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
    cmTrustedObserve false .ptrOffsetFrom .modeCase = .scalar 0 8 ∧
    cmMrObserve .treeBorrows .ptrOffsetFrom .modeCase =
      .retBytes (cmProjBM (scalarBytes IntType.usize_ty 0)) :=
  ⟨by decide +kernel, ok_stepsTB_wfLive (by decide +kernel), by decide +kernel, by decide +kernel,
   by decide +kernel, eq_error_ub_of_interpUbMsg (by decide +kernel), by decide +kernel,
   by decide +kernel⟩

/-- **`ptr_offset_from_unsigned` three-way witness** (`nonneg: true`): `2`,
one-past-the-end `4`, negative-distance UB, non-divisible UB. -/
theorem cm_ptrOffsetFromUnsigned_three_way_witness :
    cmTrustedObserve false .ptrOffsetFromUnsigned .okPrimary = .scalar 2 8 ∧
    cmTrustedObserve false .ptrOffsetFromUnsigned .okSecondary = .scalar 4 8 ∧
    (∃ m', Interp.stepsTB cmMrFuel (liftMachToTB (cmMrMachine .ptrOffsetFromUnsigned .okSecondary)) =
        .ok m' ∧ MachTB.wfLive m' ∧
      m'.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some (cmProjBM (scalarBytes IntType.usize_ty 4))) ∧
    cmTrustedObserve false .ptrOffsetFromUnsigned .ubFault = .ub ∧
    Interp.steps cmMrFuel (cmMrMachine .ptrOffsetFromUnsigned .ubFault) =
      .error (.ub "PtrOffsetFrom: negative result with `nonneg` flag set") ∧
    cmTrustedObserve false .ptrOffsetFromUnsigned .modeCase = .ub ∧
    Interp.steps cmMrFuel (cmMrMachine .ptrOffsetFromUnsigned .modeCase) =
      .error (.ub "non-zero remainder in exact division") :=
  ⟨by decide +kernel, by decide +kernel, ok_stepsTB_wfLive (by decide +kernel), by decide +kernel,
   eq_error_ub_of_interpUbMsg (by decide +kernel), by decide +kernel,
   eq_error_ub_of_interpUbMsg (by decide +kernel)⟩

/-- **`ptr_mask` three-way witness**: `!7` on offset `12` gives offset `8` in
the SAME allocation (provenance kept: Trusted allocation `100`, MiniRust
provenance of allocation `3`, with no `expose`), the identity mask keeps the
pointer, an uninitialized pointer is UB, and `!3` on offset `6` gives `4`. -/
theorem cm_ptrMask_three_way_witness :
    cmTrustedObserve false .ptrMask .okPrimary = .ptr 100 8 ∧
    (∃ m', Interp.stepsTB cmMrFuel (liftMachToTB (cmMrMachine .ptrMask .okPrimary)) = .ok m' ∧
      MachTB.wfLive m' ∧
      m'.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some (cmProjBM (cmMrPtr 1032 3))) ∧
    (∃ m', Interp.steps cmMrFuel (cmMrMachine .ptrMask .okPrimary) = .ok m' ∧
      m'.intptrcast.exposed.elems = []) ∧
    cmTrustedObserve false .ptrMask .okSecondary = .ptr 100 12 ∧
    cmMrObserve .basicMemory .ptrMask .okSecondary = cmMrBytesObs (cmMrPtr 1036 3) ∧
    cmTrustedObserve false .ptrMask .ubFault = .ub ∧
    cmMrObserve .basicMemory .ptrMask .ubFault = .ub ∧
    cmTrustedObserve false .ptrMask .modeCase = .ptr 100 4 ∧
    cmMrObserve .treeBorrows .ptrMask .modeCase = .retBytes (cmProjBM (cmMrPtr 1028 3)) :=
  ⟨by decide +kernel, ok_stepsTB_wfLive (by decide +kernel), ok_of_map_toOption (by decide +kernel),
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel⟩

/-- **`black_box` three-way witness**: value identity (`77`), provenance
identity (pointer to allocation `100` / MiniRust allocation `3` at offset `4`),
uninitialized `u32` UB, `bool` identity. -/
theorem cm_blackBox_three_way_witness :
    cmTrustedObserve false .blackBox .okPrimary = .scalar 77 4 ∧
    (∃ m', Interp.stepsTB cmMrFuel (liftMachToTB (cmMrMachine .blackBox .okPrimary)) = .ok m' ∧
      MachTB.wfLive m' ∧
      m'.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some (cmProjBM (scalarBytes cmU32It 77))) ∧
    cmTrustedObserve false .blackBox .okSecondary = .ptr 100 4 ∧
    cmMrObserve .basicMemory .blackBox .okSecondary = cmMrBytesObs (cmMrPtr 1028 3) ∧
    cmTrustedObserve false .blackBox .ubFault = .ub ∧
    cmMrObserve .basicMemory .blackBox .ubFault = .ub ∧
    cmMrObserve .treeBorrows .blackBox .ubFault = .ub ∧
    cmTrustedObserve false .blackBox .modeCase = .scalar 1 1 ∧
    cmMrObserve .treeBorrows .blackBox .modeCase = .retBytes (cmProjBM (cmInitBytes [1])) :=
  ⟨by decide +kernel, ok_stepsTB_wfLive (by decide +kernel), by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## §7. Exhaustive Axiom, Import-Isolation, & `Classical.choice`-Free Codec Audit -/

section AxiomAudit
open Lean Elab Command

/-- Exhaustively verify that this module imports no `Anneal.*`, `Miri.*`, or
`LeanMiriSpec.*` module; that every declaration depends only on the standard
axioms (`propext`, `Quot.sound`, `Classical.choice`) with zero `sorryAx` and
zero `Lean.ofReduceBool`; that no non-internal theorem is trivial; and that the
executable observers, class codecs, and table theorems are `Classical.choice`-free. -/
elab "#assert_core_mem_ptr_mr_audit" : command => do
  let env ← getEnv
  for modName in env.header.moduleNames do
    if (`Anneal).isPrefixOf modName || (`Miri).isPrefixOf modName ||
        (`LeanMiriSpec).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported"
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
    throwError "MiniRustSpec.CoreMemPtrIntrinsicsMR: 0 declarations found"
  let choiceFreeCodecs : List Lean.Name := [
    ``cmTrustedValueObs, ``cmRunTrusted, ``cmTrustedObserve, ``cmTrustedObserve_table,
    ``cmRunMrObs, ``cmMrObserve, ``cmMrObsClass, ``cmMrObserveClass, ``cmMrObsDict_distinct,
    ``cmMrObserveClass_table, ``cmMrObserve_copy_mode_sensitivity ]
  for c in choiceFreeCodecs do
    let axs ← liftCoreM <| Lean.collectAxioms c
    if axs.contains ``Classical.choice then
      throwError "MR codec/def {c} unexpectedly depends on Classical.choice"
  logInfo m!"MiniRustSpec.CoreMemPtrIntrinsicsMR: verified {checked} declarations (sorry_free=true, import_isolated=true, choice_free_codecs={choiceFreeCodecs.length})"

#assert_core_mem_ptr_mr_audit

end AxiomAudit

end MiniRustSpec.CoreMemPtrIntrinsicsMR
