/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted.MirSemantics
import Anneal.MirFuelFree
import MiniRustSpec.Correspondence.VTablePtr
import Lean.Elab.Tactic

namespace Anneal.Mir.UnalignedVolatileVTableTests

open Trusted.ITree
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.MirFuelFree

/-!
# End-to-End Canaries: Unaligned & Volatile Raw-Pointer Operations, `nullaryOp`, `fnPtrToPtr`

Every canary runs a whole `CapturedMir` body of `Trusted.Rustc.V2026_06_01.MirSemantics` from
`initMachineState` (or `initMachineStateWithCallees`). Pointers into locals are built by the
body's own `&raw` / `&` / `PtrToPtr` / `Offset` statements; the null and MMIO addresses are
provenance-less constants or arguments, and the `*const dyn Trait` pointer is an argument. The
operation under test is a `TerminatorKind.call` to one of the 7 `core::intrinsics::*` volatile
intrinsics, the 4 `core::ptr::{read,write}_{unaligned,volatile}` helpers or
`size_of_val` / `align_of_val`, or an `Rvalue` statement.

* Positive canaries prove `ReachesRet` of the exact return value and final memory together with
  `MirNoUBTree` of the body's interaction tree (`ReturnsNoUB`).
* Negative canaries prove that the body silently reaches a state whose next `stepMirFn` step is
  exactly `MirStepNode.fail .ub` or exactly `MirStepNode.fail .unsupported`
  (`= MirStepNode.unsupported`), which are distinct nodes (`fail_ub_ne_unsupported`) and each
  refute `MirNoUBTree` (`StepsTo.not_noUB`).

The executions are computed by the kernel's definitional unfolding (`kernel_rfl`); the
`#print axioms` guards at the end of the file pin every group to the standard axioms `propext`
and `Quot.sound`.

Section 4 adds the MiniRust side (`MiniRustSpec.Interp` on `Mach = Machine<BasicMemory>` and
`MachTB = Machine<TreeBorrowsMemory>`): `VTablePtr` and `&dyn Trait` `check_ptr` / `check_value` /
`CastOp::Transmute` canaries (positive, UB, and the machine-free `Stop.unsupported` fallback), and
the alignment-first, out-of-bounds, dead-allocation, and provenance-free UB of the byte memory.
-/

-- ============================================================================
-- Shared 64-bit little-endian layout fixtures (as in `VolatileUnalignedPtrTests.lean`)
-- ============================================================================

private def lU8 : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 0xFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def lU32 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0xFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def lU64 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.int 64 false) ⟨0, 0xFFFFFFFFFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def lBool : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def lF32 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.float 32) ⟨0, 0xFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def lPtr : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.pointer 0) ⟨0, 0xFFFFFFFFFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def lUnit : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩,
    backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }

private def lNever : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩,
    backendRepr := .memory,
    fields := .primitive, variants := .empty, isUninhabited := true }

private def lZstAlign4 : TypeLayout :=
  { size := ⟨0⟩, align := ⟨4⟩,
    backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }

private def lArrU8_8 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨1⟩,
    backendRepr := .memory,
    fields := .array ⟨1⟩ 8, variants := .single 0, isUninhabited := false,
    fieldLayouts := [0] }

private def lArrU8_4 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨1⟩,
    backendRepr := .memory,
    fields := .array ⟨1⟩ 4, variants := .single 0, isUninhabited := false,
    fieldLayouts := [0] }

private def lPackedU8U32 : TypeLayout :=
  { size := ⟨5⟩, align := ⟨1⟩,
    backendRepr := .memory,
    fields := .arbitrary [⟨0⟩, ⟨1⟩] [0, 1], variants := .single 0, isUninhabited := false,
    fieldLayouts := [0, 1] }

private def lAlign4BytesAndU32 : TypeLayout :=
  -- #[repr(C)] struct S { a: u8 (0), b: [u8; 3] (1), c: u32 (4) }
  { size := ⟨8⟩, align := ⟨4⟩,
    backendRepr := .memory,
    fields := .arbitrary [⟨0⟩, ⟨1⟩, ⟨4⟩] [0, 1, 2], variants := .single 0, isUninhabited := false,
    fieldLayouts := [0, 13, 1] }

private def lArrU8_3 : TypeLayout :=
  { size := ⟨3⟩, align := ⟨1⟩,
    backendRepr := .memory,
    fields := .array ⟨1⟩ 3, variants := .single 0, isUninhabited := false,
    fieldLayouts := [0] }

private def lPairU32 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨4⟩,
    backendRepr := .memory,
    fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1], variants := .single 0, isUninhabited := false,
    fieldLayouts := [1, 1] }

private def lPairBoolU8 : TypeLayout :=
  { size := ⟨2⟩, align := ⟨1⟩,
    backendRepr := .memory,
    fields := .arbitrary [⟨0⟩, ⟨1⟩] [0, 1], variants := .single 0, isUninhabited := false,
    fieldLayouts := [3, 0] }

private def lNonZeroU32 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨1, 0xFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def lArrU32_0 : TypeLayout :=
  { size := ⟨0⟩, align := ⟨4⟩,
    backendRepr := .memory,
    fields := .array ⟨4⟩ 0, variants := .single 0, isUninhabited := false,
    fieldLayouts := [1] }

private def lPairUnit : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩,
    backendRepr := .memory,
    fields := .arbitrary [⟨0⟩, ⟨0⟩] [0, 1], variants := .single 0, isUninhabited := false,
    fieldLayouts := [6, 6] }

private def lU32AndPairUnit : TypeLayout :=
  -- (u32, ((), ())): the zero-sized second field sits at offset 4.
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .memory,
    fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1], variants := .single 0, isUninhabited := false,
    fieldLayouts := [1, 18] }

private def lUnionU32Arr3 : TypeLayout :=
  -- union U { a: u32, b: [u8; 3] }: both fields start at offset 0.
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [1, 13] }

private def lChar : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0x10FFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def lWidePtr : TypeLayout :=
  { size := ⟨16⟩, align := ⟨8⟩,
    backendRepr := .scalarPair
      (.initialized (.pointer 0) ⟨0, 0xFFFFFFFFFFFFFFFF⟩)
      (.initialized (.pointer 0) ⟨0, 0xFFFFFFFFFFFFFFFF⟩),
    fields := .arbitrary [⟨0⟩, ⟨8⟩] [0, 1], variants := .single 0, isUninhabited := false }

private def tbl : LayoutTable :=
  { pointerBits := 64,
    isLittleEndian := true,
    entries := [
      lU8,               -- 0
      lU32,              -- 1
      lU64,              -- 2
      lBool,             -- 3
      lF32,              -- 4
      lPtr,              -- 5
      lUnit,             -- 6
      lNever,            -- 7
      lZstAlign4,        -- 8
      lArrU8_8,          -- 9
      lArrU8_4,          -- 10
      lPackedU8U32,      -- 11
      lAlign4BytesAndU32,-- 12
      lArrU8_3,          -- 13
      lPairU32,          -- 14
      lPairBoolU8,       -- 15
      lNonZeroU32,       -- 16
      lArrU32_0,         -- 17
      lPairUnit,         -- 18
      lU32AndPairUnit,   -- 19
      lUnionU32Arr3,     -- 20
      lChar,             -- 21
      lWidePtr           -- 22
    ] }

private def tyU8 : Ty := ⟨.uint .u8, 0⟩
private def tyU32 : Ty := ⟨.uint .u32, 1⟩
private def tyUsize : Ty := ⟨.uint .usize, 2⟩
private def tyBool : Ty := ⟨.bool, 3⟩
private def tyPtrConstU32 : Ty := ⟨.rawPtr .not (.uint .u32), 5⟩
private def tyPtrMutU32 : Ty := ⟨.rawPtr .mut (.uint .u32), 5⟩
private def tyPtrConstU8 : Ty := ⟨.rawPtr .not (.uint .u8), 5⟩
private def tyPtrMutU8 : Ty := ⟨.rawPtr .mut (.uint .u8), 5⟩
private def tyRefU32 : Ty := ⟨.ref .not (.uint .u32), 5⟩
private def tyRefMutU32 : Ty := ⟨.ref .mut (.uint .u32), 5⟩
private def tyUnit : Ty := ⟨.tuple [], 6⟩
private def tyNever : Ty := ⟨.never, 7⟩
private def tyZstAlign4 : Ty := ⟨.adt "Zst4" [], 8⟩
private def tyArrU8_8 : Ty := ⟨.array (.uint .u8) 8, 9⟩
private def tyArrU8_4 : Ty := ⟨.array (.uint .u8) 4, 10⟩
private def tyPacked : Ty := ⟨.adt "Packed" [], 11⟩
private def tyAlign4S : Ty := ⟨.adt "Align4S" [], 12⟩
private def tyPairU32 : Ty := ⟨.tuple [.uint .u32, .uint .u32], 14⟩
private def tyArrU32_0 : Ty := ⟨.array (.uint .u32) 0, 17⟩
private def tyChar : Ty := ⟨.char, 21⟩
private def tyPtrConstArr8 : Ty := ⟨.rawPtr .not (.array (.uint .u8) 8), 5⟩
private def tyPtrMutArr8 : Ty := ⟨.rawPtr .mut (.array (.uint .u8) 8), 5⟩
private def tyPtrMutArr4 : Ty := ⟨.rawPtr .mut (.array (.uint .u8) 4), 5⟩
private def tyPtrMutPairU32 : Ty := ⟨.rawPtr .mut (.tuple [.uint .u32, .uint .u32]), 5⟩
private def tyPtrConstUnit : Ty := ⟨.rawPtr .not (.tuple []), 5⟩
private def tyPtrMutUnit : Ty := ⟨.rawPtr .mut (.tuple []), 5⟩
private def tyPtrMutNever : Ty := ⟨.rawPtr .mut .never, 5⟩
private def tyFnPtr : Ty := ⟨.fnPtr [] (.tuple []) .safe .rust, 5⟩
private def tyPtrConstDyn : Ty := ⟨.rawPtr .not (.dynamic "Trait"), 22⟩

private def mkDecl (ty : Ty) : LocalDecl :=
  { mutability := .mut, ty := ty, debugName := .none }

private def u8Val (b : Nat) : Value := .scalar ⟨b, 1⟩
private def u32Val (v : Nat) : Value := .scalar ⟨v, 4⟩
private def usizeVal (v : Nat) : Value := .scalar ⟨v, 8⟩

private def uvLoad : String := "core::intrinsics::unaligned_volatile_load"
private def uvStore : String := "core::intrinsics::unaligned_volatile_store"
private def vLoad : String := "core::intrinsics::volatile_load"
private def vStore : String := "core::intrinsics::volatile_store"
private def vCopyNonoverlapping : String := "core::intrinsics::volatile_copy_nonoverlapping_memory"
private def vCopy : String := "core::intrinsics::volatile_copy_memory"
private def vSet : String := "core::intrinsics::volatile_set_memory"
private def readUnaligned : String := "core::ptr::read_unaligned"
private def writeUnaligned : String := "core::ptr::write_unaligned"
private def readVolatile : String := "core::ptr::read_volatile"
private def writeVolatile : String := "core::ptr::write_volatile"

-- ============================================================================
-- MIR body builders
-- ============================================================================

private def pl (l : Nat) : Place := { local_ := l, projection := [] }
private def st (k : StatementKind) : Statement := { kind := k, span := "" }
private def live (l : Nat) : Statement := st (.storageLive l)
private def asg (l : Nat) (rv : Rvalue) : Statement := st (.assign (pl l) rv)
private def cU8 (v : Nat) : Operand := .constant { ty := tyU8, val := .scalar (.int ⟨v, 1⟩) }
private def cU32 (v : Nat) : Operand := .constant { ty := tyU32, val := .scalar (.int ⟨v, 4⟩) }
private def cUsize (v : Nat) : Operand := .constant { ty := tyUsize, val := .scalar (.int ⟨v, 8⟩) }
/-- A raw-pointer constant with no provenance (`addr as *const T`). -/
private def cAddr (ptrTy : Ty) (addr : Nat) : Operand :=
  .constant { ty := ptrTy, val := .scalar (.int ⟨addr, 8⟩) }
private def cZst (ty : Ty) : Operand := .constant { ty := ty, val := .zeroSized }
private def fnOp (path : String) (targs : List RigidTy) : Operand :=
  .constant { ty := ⟨.fnDef path targs, 6⟩, val := .zeroSized }
private def callTerm (path : String) (targs : List RigidTy) (args : List Operand)
    (dest : Nat) (tgt : Nat) : Terminator :=
  { kind := .call (fnOp path targs) args (pl dest) (.some tgt) .continue_, span := "" }
private def retTerm : Terminator := { kind := .return_, span := "" }
private def bb (stmts : List Statement) (t : Terminator) : BasicBlockData :=
  { statements := stmts, terminator := t, isCleanup := false }

private def mkBodyN (argCount : Nat) (decls : List LocalDecl) (blocks : List BasicBlockData) :
    CapturedMir :=
  { defPath := "test::canary",
    phase := .runtimePostCleanup,
    role := .subject,
    argCount := argCount,
    localDecls := decls,
    basicBlocks := blocks,
    fnAbi := { args := [], ret := { layout := lUnit, mode := .ignore },
               conv := .rust, canUnwind := false },
    layouts := tbl,
    allocations := [] }

private def mkBody (decls : List LocalDecl) (blocks : List BasicBlockData) : CapturedMir :=
  mkBodyN 0 decls blocks

private def arr8Ops : List Operand :=
  [cU8 0xAA, cU8 0x78, cU8 0x56, cU8 0x34, cU8 0x12, cU8 0xBB, cU8 0xCC, cU8 0xDD]

/-- `let a: [u8; 8] = [0xAA, 0x78, 0x56, 0x34, 0x12, 0xBB, 0xCC, 0xDD];`
`path::<elem>((&raw const a).cast::<u8>().add(off).cast::<elem>())`. -/
private def arrLoadBody (path : String) (off : Nat) (elem : Ty) : CapturedMir :=
  mkBody [mkDecl elem, mkDecl tyArrU8_8, mkDecl tyPtrConstArr8, mkDecl tyPtrConstU8,
          mkDecl tyPtrConstU8, mkDecl ⟨.rawPtr .not elem.kind, 5⟩]
    [bb [live 1, live 2, live 3, live 4, live 5,
         asg 1 (.aggregate (.array tyU8) arr8Ops),
         asg 2 (.rawPtr .not (pl 1)),
         asg 3 (.cast .ptrToPtr (.copy (pl 2)) tyPtrConstU8),
         asg 4 (.binaryOp .offset (.copy (pl 3)) (cUsize off)),
         asg 5 (.cast .ptrToPtr (.copy (pl 4)) ⟨.rawPtr .not elem.kind, 5⟩)]
        (callTerm path [elem.kind] [.copy (pl 5)] 0 1),
     bb [] retTerm]

/-- As `arrLoadBody` through `&raw mut a`, then `path::<u32>(p, 0x04030201)`; returns `a`. -/
private def arrStoreBody (path : String) (off : Nat) : CapturedMir :=
  mkBody [mkDecl tyArrU8_8, mkDecl tyArrU8_8, mkDecl tyPtrMutArr8, mkDecl tyPtrMutU8,
          mkDecl tyPtrMutU8, mkDecl tyPtrMutU32, mkDecl tyUnit]
    [bb [live 1, live 2, live 3, live 4, live 5, live 6,
         asg 1 (.aggregate (.array tyU8) arr8Ops),
         asg 2 (.rawPtr .mut (pl 1)),
         asg 3 (.cast .ptrToPtr (.copy (pl 2)) tyPtrMutU8),
         asg 4 (.binaryOp .offset (.copy (pl 3)) (cUsize off)),
         asg 5 (.cast .ptrToPtr (.copy (pl 4)) tyPtrMutU32)]
        (callTerm path [.uint .u32] [.copy (pl 5), cU32 0x04030201] 6 1),
     bb [asg 0 (.use (.copy (pl 1)))] retTerm]

/-- `#[repr(packed)] struct Packed { a: u8, b: u32 }`: `path::<u32>(&raw const p.b)`. -/
private def packedLoadBody (path : String) : CapturedMir :=
  mkBody [mkDecl tyU32, mkDecl tyPacked, mkDecl tyPtrConstU32]
    [bb [live 1, live 2,
         asg 1 (.aggregate (.adt "Packed" 0 .none) [cU8 7, cU32 42]),
         asg 2 (.rawPtr .not ⟨1, [.field 1 tyU32]⟩)]
        (callTerm path [.uint .u32] [.copy (pl 2)] 0 1),
     bb [] retTerm]

/-- `path::<u32>(&raw mut p.b, 0xDEADBEEF)`; returns `p`. -/
private def packedStoreBody (path : String) : CapturedMir :=
  mkBody [mkDecl tyPacked, mkDecl tyPacked, mkDecl tyPtrMutU32, mkDecl tyUnit]
    [bb [live 1, live 2, live 3,
         asg 1 (.aggregate (.adt "Packed" 0 .none) [cU8 7, cU32 42]),
         asg 2 (.rawPtr .mut ⟨1, [.field 1 tyU32]⟩)]
        (callTerm path [.uint .u32] [.copy (pl 2), cU32 0xDEADBEEF] 3 1),
     bb [asg 0 (.use (.copy (pl 1)))] retTerm]

/-- `let x: u32 = 0x11223344; path::<u32>(&raw const x)`. -/
private def u32LoadBody (path : String) : CapturedMir :=
  mkBody [mkDecl tyU32, mkDecl tyU32, mkDecl tyPtrConstU32]
    [bb [live 1, live 2,
         asg 1 (.use (cU32 0x11223344)),
         asg 2 (.rawPtr .not (pl 1))]
        (callTerm path [.uint .u32] [.copy (pl 2)] 0 1),
     bb [] retTerm]

/-- `let mut x: u32 = 0x11223344; path::<u32>(&raw mut x, 0xCAFEBABE); x`. -/
private def u32StoreBody (path : String) : CapturedMir :=
  mkBody [mkDecl tyU32, mkDecl tyU32, mkDecl tyPtrMutU32, mkDecl tyUnit]
    [bb [live 1, live 2, live 3,
         asg 1 (.use (cU32 0x11223344)),
         asg 2 (.rawPtr .mut (pl 1))]
        (callTerm path [.uint .u32] [.copy (pl 2), cU32 0xCAFEBABE] 3 1),
     bb [asg 0 (.use (.copy (pl 1)))] retTerm]

/-- `let src = 0x11223344u32; let mut dst = 0x99887766u32;`
`path::<u32>(&raw mut dst, &raw const src, count); (src, dst)`. -/
private def copyPairBody (path : String) (count : Nat) : CapturedMir :=
  mkBody [mkDecl tyPairU32, mkDecl tyU32, mkDecl tyU32, mkDecl tyPtrConstU32, mkDecl tyPtrMutU32,
          mkDecl tyUnit]
    [bb [live 1, live 2, live 3, live 4, live 5,
         asg 1 (.use (cU32 0x11223344)),
         asg 2 (.use (cU32 0x99887766)),
         asg 3 (.rawPtr .not (pl 1)),
         asg 4 (.rawPtr .mut (pl 2))]
        (callTerm path [.uint .u32] [.copy (pl 4), .copy (pl 3), cUsize count] 5 1),
     bb [asg 0 (.aggregate .tuple [.copy (pl 1), .copy (pl 2)])] retTerm]

/-- `let mut a: [u8; 4] = [10, 20, 30, 40]; let p = (&raw mut a).cast::<u8>();`
`path::<u8>(p.add(dstOff), p.add(srcOff), count); a`. -/
private def arr4CopyBody (path : String) (dstOff srcOff count : Nat) : CapturedMir :=
  mkBody [mkDecl tyArrU8_4, mkDecl tyArrU8_4, mkDecl tyPtrMutArr4, mkDecl tyPtrMutU8,
          mkDecl tyPtrMutU8, mkDecl tyPtrMutU8, mkDecl tyPtrConstU8, mkDecl tyUnit]
    [bb [live 1, live 2, live 3, live 4, live 5, live 6, live 7,
         asg 1 (.aggregate (.array tyU8) [cU8 10, cU8 20, cU8 30, cU8 40]),
         asg 2 (.rawPtr .mut (pl 1)),
         asg 3 (.cast .ptrToPtr (.copy (pl 2)) tyPtrMutU8),
         asg 4 (.binaryOp .offset (.copy (pl 3)) (cUsize dstOff)),
         asg 5 (.binaryOp .offset (.copy (pl 3)) (cUsize srcOff)),
         asg 6 (.cast .ptrToPtr (.copy (pl 5)) tyPtrConstU8)]
        (callTerm path [.uint .u8] [.copy (pl 4), .copy (pl 6), cUsize count] 7 1),
     bb [asg 0 (.use (.copy (pl 1)))] retTerm]

/-- `let mut a: [u8; 4] = [1, 2, 3, 4];`
`volatile_set_memory::<u8>((&raw mut a).cast::<u8>().add(off), val, count); a`. -/
private def arr4SetBody (off val count : Nat) : CapturedMir :=
  mkBody [mkDecl tyArrU8_4, mkDecl tyArrU8_4, mkDecl tyPtrMutArr4, mkDecl tyPtrMutU8,
          mkDecl tyPtrMutU8, mkDecl tyUnit]
    [bb [live 1, live 2, live 3, live 4, live 5,
         asg 1 (.aggregate (.array tyU8) [cU8 1, cU8 2, cU8 3, cU8 4]),
         asg 2 (.rawPtr .mut (pl 1)),
         asg 3 (.cast .ptrToPtr (.copy (pl 2)) tyPtrMutU8),
         asg 4 (.binaryOp .offset (.copy (pl 3)) (cUsize off))]
        (callTerm vSet [.uint .u8]
          [.copy (pl 4), cU8 val, cUsize count] 5 1),
     bb [asg 0 (.use (.copy (pl 1)))] retTerm]

/-- `_0 = NullaryOp(op, ty)`; the unused local `_1: Align4S` puts the `repr(C)` struct's
layout in scope. -/
private def nullaryBody (op : NullOp) (ty retTy : Ty) : CapturedMir :=
  mkBody [mkDecl retTy, mkDecl tyAlign4S]
    [bb [asg 0 (.nullaryOp op ty)] retTerm]

/-- `let f: fn() = callee;` (`ReifyFnPointer`) `f as *const ()` (`FnPtrToPtr`). -/
private def fnPtrToPtrBody : CapturedMir :=
  mkBody [mkDecl tyPtrConstUnit, mkDecl tyFnPtr]
    [bb [live 1,
         asg 1 (.cast (.pointerCoercion "ReifyFnPointer") (fnOp "test::callee" []) tyFnPtr),
         asg 0 (.cast .fnPtrToPtr (.copy (pl 1)) tyPtrConstUnit)]
        retTerm]

/-- `let x = 5u32; (&raw const x) as *const ()` through `CastKind.fnPtrToPtr`. -/
private def fnPtrToPtrDataBody : CapturedMir :=
  mkBody [mkDecl tyPtrConstUnit, mkDecl tyU32, mkDecl tyPtrConstU32]
    [bb [live 1, live 2,
         asg 1 (.use (cU32 5)),
         asg 2 (.rawPtr .not (pl 1)),
         asg 0 (.cast .fnPtrToPtr (.copy (pl 2)) tyPtrConstUnit)]
        retTerm]

/-- `let mut t: (u32, u32) = (0x11223344, 0x55667788);`
`let p = (&raw mut t).cast::<u8>().add(off).cast::<elem>(); path::<elem>(p, extra...)`. -/
private def pairPtrBody (path : String) (off : Nat) (elem : Ty) (extra : List Operand)
    (retTy : Ty) : CapturedMir :=
  mkBody [mkDecl retTy, mkDecl tyPairU32, mkDecl tyPtrMutPairU32, mkDecl tyPtrMutU8,
          mkDecl tyPtrMutU8, mkDecl ⟨.rawPtr .mut elem.kind, 5⟩]
    [bb [live 1, live 2, live 3, live 4, live 5,
         asg 1 (.aggregate .tuple [cU32 0x11223344, cU32 0x55667788]),
         asg 2 (.rawPtr .mut (pl 1)),
         asg 3 (.cast .ptrToPtr (.copy (pl 2)) tyPtrMutU8),
         asg 4 (.binaryOp .offset (.copy (pl 3)) (cUsize off)),
         asg 5 (.cast .ptrToPtr (.copy (pl 4)) ⟨.rawPtr .mut elem.kind, 5⟩)]
        (callTerm path [elem.kind] (.copy (pl 5) :: extra) 0 1),
     bb [] retTerm]

/-- As `pairPtrBody` with two pointers `dst = base.add(dstOff)`, `src = base.add(srcOff)`:
`path::<elem>(dst, src, count)`. -/
private def pairCopyBody (path : String) (dstOff srcOff count : Nat) (elem : Ty) : CapturedMir :=
  mkBody [mkDecl tyUnit, mkDecl tyPairU32, mkDecl tyPtrMutPairU32, mkDecl tyPtrMutU8,
          mkDecl tyPtrMutU8, mkDecl ⟨.rawPtr .mut elem.kind, 5⟩,
          mkDecl tyPtrMutU8, mkDecl ⟨.rawPtr .not elem.kind, 5⟩]
    [bb [live 1, live 2, live 3, live 4, live 5, live 6, live 7,
         asg 1 (.aggregate .tuple [cU32 0x11223344, cU32 0x55667788]),
         asg 2 (.rawPtr .mut (pl 1)),
         asg 3 (.cast .ptrToPtr (.copy (pl 2)) tyPtrMutU8),
         asg 4 (.binaryOp .offset (.copy (pl 3)) (cUsize dstOff)),
         asg 5 (.cast .ptrToPtr (.copy (pl 4)) ⟨.rawPtr .mut elem.kind, 5⟩),
         asg 6 (.binaryOp .offset (.copy (pl 3)) (cUsize srcOff)),
         asg 7 (.cast .ptrToPtr (.copy (pl 6)) ⟨.rawPtr .not elem.kind, 5⟩)]
        (callTerm path [elem.kind] [.copy (pl 5), .copy (pl 7), cUsize count] 0 1),
     bb [] retTerm]

/-- `let x = 7u32; let p = &raw const x; StorageDead(x); path::<u32>(p)`. -/
private def uafLoadBody (path : String) : CapturedMir :=
  mkBody [mkDecl tyU32, mkDecl tyU32, mkDecl tyPtrConstU32]
    [bb [live 1, live 2,
         asg 1 (.use (cU32 7)),
         asg 2 (.rawPtr .not (pl 1)),
         st (.storageDead 1)]
        (callTerm path [.uint .u32] [.copy (pl 2)] 0 1),
     bb [] retTerm]

/-- `let mut x = 7u32; let p = &raw mut x; StorageDead(x); path::<u32>(p, 9)`. -/
private def uafStoreBody (path : String) : CapturedMir :=
  mkBody [mkDecl tyUnit, mkDecl tyU32, mkDecl tyPtrMutU32]
    [bb [live 1, live 2,
         asg 1 (.use (cU32 7)),
         asg 2 (.rawPtr .mut (pl 1)),
         st (.storageDead 1)]
        (callTerm path [.uint .u32] [.copy (pl 2), cU32 9] 0 1),
     bb [] retTerm]

/-- `path::<elem>(args...)` on constant operands only (null / MMIO addresses). -/
private def constCallBody (path : String) (elem : Ty) (args : List Operand) (retTy : Ty) :
    CapturedMir :=
  mkBody [mkDecl retTy] [bb [] (callTerm path [elem.kind] args 0 1), bb [] retTerm]

/-- `let x = 7u32; let r = &x; let p = (&raw const *r) as *mut u32; path::<u32>(p, 9)`. -/
private def frozenWriteBody (path : String) : CapturedMir :=
  mkBody [mkDecl tyUnit, mkDecl tyU32, mkDecl tyRefU32, mkDecl tyPtrConstU32, mkDecl tyPtrMutU32]
    [bb [live 1, live 2, live 3, live 4,
         asg 1 (.use (cU32 7)),
         asg 2 (.ref .shared (pl 1)),
         asg 3 (.rawPtr .not ⟨2, [.deref]⟩),
         asg 4 (.cast .ptrToPtr (.copy (pl 3)) tyPtrMutU32)]
        (callTerm path [.uint .u32] [.copy (pl 4), cU32 9] 0 1),
     bb [] retTerm]

/-- `let mut x = 7u32; let r = &mut x; let p = &raw mut *r; x = 8;` (invalidates `r`'s tag)
`path::<u32>(p, extra...)`. -/
private def disabledBody (path : String) (extra : List Operand) (retTy : Ty) : CapturedMir :=
  mkBody [mkDecl retTy, mkDecl tyU32, mkDecl tyRefMutU32, mkDecl tyPtrMutU32]
    [bb [live 1, live 2, live 3,
         asg 1 (.use (cU32 7)),
         asg 2 (.ref (.mut false) (pl 1)),
         asg 3 (.rawPtr .mut ⟨2, [.deref]⟩),
         asg 1 (.use (cU32 8))]
        (callTerm path [.uint .u32] (.copy (pl 3) :: extra) 0 1),
     bb [] retTerm]

/-- `let b = raw: srcTy; path::<elem>((&raw const b) as *const elem)`. -/
private def reinterpretLoadBody (path : String) (srcTy : Ty) (src : Operand) (elem : Ty) :
    CapturedMir :=
  mkBody [mkDecl elem, mkDecl srcTy, mkDecl ⟨.rawPtr .not srcTy.kind, 5⟩,
          mkDecl ⟨.rawPtr .not elem.kind, 5⟩]
    [bb [live 1, live 2, live 3,
         asg 1 (.use src),
         asg 2 (.rawPtr .not (pl 1)),
         asg 3 (.cast .ptrToPtr (.copy (pl 2)) ⟨.rawPtr .not elem.kind, 5⟩)]
        (callTerm path [elem.kind] [.copy (pl 3)] 0 1),
     bb [] retTerm]

/-- `let mut u = (); path::<!>((&raw mut u) as *mut !, <zero-sized constant at !>)`. -/
private def neverStoreBody (path : String) : CapturedMir :=
  mkBody [mkDecl tyUnit, mkDecl tyUnit, mkDecl tyPtrMutUnit, mkDecl tyPtrMutNever]
    [bb [live 1, live 2, live 3,
         asg 1 (.use (cZst tyUnit)),
         asg 2 (.rawPtr .mut (pl 1)),
         asg 3 (.cast .ptrToPtr (.copy (pl 2)) tyPtrMutNever)]
        (callTerm path [.never] [.copy (pl 3), cZst tyNever] 0 1),
     bb [] retTerm]

/-- `fn f(p: ptrTy) -> R { path::<T>(p, extra...) }`: the pointer is the body's argument. -/
private def ptrArgCallBody (path : String) (targ : RigidTy) (ptrTy : Ty) (extra : List Operand)
    (retTy : Ty) : CapturedMir :=
  mkBodyN 1 [mkDecl retTy, mkDecl ptrTy]
    [bb [] (callTerm path [targ] (.copy (pl 1) :: extra) 0 1), bb [] retTerm]

/-- `fn f(p: *const dyn Trait) -> usize { path::<dyn Trait>(p) }`. -/
private def dynValBody (path : String) : CapturedMir :=
  ptrArgCallBody path (.dynamic "Trait") tyPtrConstDyn [] tyUsize

/-- `fn callee_prot(r: &mut u32, p: *mut u32) -> R { path::<u32>(p, extra...) }`; with `retag`,
the body starts with the `FnEntry` retag that protects `r` for the duration of the call. -/
private def protCallee (retag : Bool) (path : String) (extra : List Operand) (retTy : Ty) :
    CapturedMir :=
  { mkBodyN 2 [mkDecl retTy, mkDecl tyRefMutU32, mkDecl tyPtrMutU32]
      [bb (match retag with
           | true => [st (.retag .fnEntry (pl 1))]
           | false => [])
          (callTerm path [.uint .u32] (.copy (pl 2) :: extra) 0 1),
       bb [] retTerm] with
    defPath := "test::callee_prot" }

/-- `let mut x = 7u32; let r = &mut x; let p = &raw mut *r; callee_prot(r, p)`: `p` carries the
tag of `r`, the parent of the tag the callee's `FnEntry` retag creates and protects. -/
private def protCaller (retTy : Ty) : CapturedMir :=
  mkBody [mkDecl retTy, mkDecl tyU32, mkDecl tyPtrMutU32, mkDecl tyRefMutU32]
    [bb [live 1, live 2, live 3,
         asg 1 (.use (cU32 7)),
         asg 3 (.ref (.mut false) (pl 1)),
         asg 2 (.rawPtr .mut ⟨3, [.deref]⟩)]
        (callTerm "test::callee_prot" [] [.move (pl 3), .copy (pl 2)] 0 1),
     bb [] retTerm]

-- ============================================================================
-- Kernel-evaluated execution of `stepMirState` / `stepMirFn`
-- ============================================================================

/-- Closes `lhs = rhs` with `Eq.refl lhs`: the two sides are compared by the kernel's definitional
unfolding alone (no elaborator `whnf`, no compiled evaluation). -/
local elab "kernel_rfl" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let tgt ← Lean.MVarId.getType' mvarId
  let some (ty, lhs, _) := tgt.eq? |
    Lean.Meta.throwTacticEx `kernel_rfl mvarId "expected equality goal"
  let u ← Lean.Meta.getLevel ty
  mvarId.assign (Lean.mkApp2 (Lean.mkConst ``Eq.refl [u]) ty lhs)
  Lean.Elab.Tactic.replaceMainGoal []

/-- `body` run from state `s` returns `v` with final memory `mem` without any visible event, and
its interaction tree is UB-free on every prefix (`ReachesRet` + `MirNoUBTree`). -/
private abbrev ReturnsNoUBFrom (body : CapturedMir) (s : MachineState) (v : Value)
    (mem : Memory) : Prop :=
  ReachesRet (mirTree body s) [] (.normal (v, mem)) ∧ MirNoUBTree (mirTree body s)

/-- A silent `fuel`-step run of `stepMirState body` to `.ret (.normal (v, mem))`, computed twice by
the kernel (`evalTauApprox ∘ approxCofix` for `ReachesRet`, `runMirBounded` for `TreeSafe`). -/
private theorem returnsNoUB_of_run {body : CapturedMir} {s : MachineState} {v : Value}
    {mem : Memory} (fuel : Nat)
    (hret : Anneal.ITree.evalTauApprox
        (Anneal.ITree.approxCofix (stepMirState body) fuel (.running s)) =
      some (.normal (v, mem)))
    (hrun : runMirBounded fuel body s = some (.normal (v, mem))) :
    ReturnsNoUBFrom body s v mem :=
  ⟨Anneal.ITree.evalTauApprox_approxCofix_sound_reachesRet (stepMirState body) (.running s) hret,
   (Anneal.PureMirExec.treeSafe_and_ret_of_mirWpConverges
      (MirWpConverges.of_runMirBounded (post := fun _ => True) hrun trivial)).1⟩

/-- Follows at most `fuel` silent `stepMirFn body` steps from `s` and returns the first node that
is not a silent step to a running state (`none` when `fuel` runs out first). -/
private def firstNonSilent (body : CapturedMir) : Nat → MachineState → Option MirStepNode
  | 0, _ => none
  | fuel + 1, s =>
    match stepMirFn body s with
    | .tau (.running s') => firstNonSilent body fuel s'
    | node => some node

/-- `body`, run from `s₀`, silently reaches a state `s` whose next `stepMirFn` step is `node`. -/
private def StepsTo (body : CapturedMir) (s₀ : MachineState) (node : MirStepNode) : Prop :=
  ∃ s, Trusted.ITree.TauStar (mirTree body s₀) (mirTree body s) ∧ stepMirFn body s = node

private theorem mirTree_observe (body : CapturedMir) (s : MachineState) :
    (mirTree body s).observe =
      (stepMirFn body s).map (Trusted.ITree.ITree.cofix (stepMirState body)) := by
  simp [mirTree, Trusted.ITree.ITree.observe_cofix, stepMirState]

private theorem firstNonSilent_sound (body : CapturedMir) :
    ∀ (fuel : Nat) (s : MachineState) (node : MirStepNode),
      firstNonSilent body fuel s = some node → StepsTo body s node := by
  intro fuel
  induction fuel with
  | zero => intro s node h; simp [firstNonSilent] at h
  | succ fuel ih =>
    intro s node h
    have hobs := mirTree_observe body s
    simp only [firstNonSilent] at h
    generalize hn : stepMirFn body s = n at h hobs
    cases n with
    | tau x =>
      cases x with
      | running s' =>
        obtain ⟨s'', hstar, hstep⟩ := ih s' node h
        exact ⟨s'', .step hobs hstar, hstep⟩
      | halted o => exact ⟨s, .refl _, hn.trans (Option.some.inj h)⟩
      | faulted k => exact ⟨s, .refl _, hn.trans (Option.some.inj h)⟩
    | ret o => exact ⟨s, .refl _, hn.trans (Option.some.inj h)⟩
    | vis i k => exact ⟨s, .refl _, hn.trans (Option.some.inj h)⟩

/-- A kernel-computed `firstNonSilent` result is a genuine `StepsTo`. -/
private theorem stepsTo_of_run {body : CapturedMir} {s₀ : MachineState} {node : MirStepNode}
    (fuel : Nat) (h : firstNonSilent body fuel s₀ = some node) : StepsTo body s₀ node :=
  firstNonSilent_sound body fuel s₀ node h

/-- The failure kind of a fault node. -/
private def nodeFailKind? : MirStepNode → Option Trusted.Effect.FailureKind
  | .vis (.inl (.fail k)) _ => some k
  | _ => none

/-- `.ub` and `.unsupported` are different step nodes: a canary stepping to
`MirStepNode.fail .ub` does not step to `MirStepNode.unsupported`, and conversely. -/
theorem fail_ub_ne_unsupported : MirStepNode.fail .ub ≠ MirStepNode.unsupported := by
  intro h
  have h' : nodeFailKind? (MirStepNode.fail .ub) = nodeFailKind? MirStepNode.unsupported :=
    congrArg nodeFailKind? h
  exact absurd (Option.some.inj h') (by decide)

/-- A fault node is not a silent step: it is neither `.ok` nor a return. -/
theorem fail_ne_step (fk : Trusted.Effect.FailureKind) (s : MachineState) :
    MirStepNode.fail fk ≠ MirStepNode.step s := by
  intro h
  have h' : nodeFailKind? (MirStepNode.fail fk) = nodeFailKind? (MirStepNode.step s) :=
    congrArg nodeFailKind? h
  exact Option.some_ne_none fk h'

/-- Reaching a fault node of either kind refutes `MirNoUBTree`. -/
private theorem StepsTo.not_noUB {body : CapturedMir} {s₀ : MachineState}
    {fk : Trusted.Effect.FailureKind} (h : StepsTo body s₀ (MirStepNode.fail fk)) :
    ¬ MirNoUBTree (mirTree body s₀) := by
  intro hsafe
  obtain ⟨s, hstar, hstep⟩ := h
  have hobs := mirTree_observe body s
  rw [hstep] at hobs
  exact hsafe [] (mirTree body s) (Anneal.ITree.Reaches.of_tauStar hstar (.refl _))
    ⟨mirTree body s, _, _, .refl _, hobs, trivial⟩

/-- `ReturnsNoUBFrom` the initial state of `body` on `args`: `ReachesRet` + `MirNoUBTree` of
`mirCallTree body args`. -/
private abbrev ReturnsNoUB (body : CapturedMir) (args : List Value) (v : Value) (mem : Memory) :
    Prop :=
  ReachesRet (mirCallTree body args) [] (.normal (v, mem)) ∧ MirNoUBTree (mirCallTree body args)

/-- `body`, started on `args`, silently reaches a state whose next `stepMirFn` step is exactly
the fault `fk`. -/
private abbrev FaultsWith (body : CapturedMir) (args : List Value)
    (fk : Trusted.Effect.FailureKind) : Prop :=
  StepsTo body (initMachineState body args) (MirStepNode.fail fk)

/-- Proves a `ReturnsNoUB` / `ReturnsNoUBFrom` canary by running the body in the kernel. -/
local macro "run_ok" : tactic =>
  `(tactic| exact returnsNoUB_of_run 24 (by kernel_rfl) (by kernel_rfl))

/-- Proves a `FaultsWith` / `StepsTo` canary by running the body in the kernel. -/
local macro "run_fault" : tactic => `(tactic| exact stepsTo_of_run 24 (by kernel_rfl))

/-- A borrow entry after its frame returned: `disabled`, allocation dead. -/
private def deadEntry (tag loc : Nat) (proj : List ProjectionElem := []) : BorrowEntry :=
  { tag := tag, targetLocal := loc, targetProjection := proj, perm := .disabled, allocDead := true }

/-- Final memory of a returned body: only `nextTag` and the (dead) borrow entries changed. -/
private def retMem (nextTag : Nat) (borrows : List BorrowEntry) : Memory :=
  { nextTag := nextTag, borrows := borrows }

/-- Final memory of the array bodies: the `&raw` pointer to the whole `[u8; n]` (tag 1) and the
`*u8` element pointer its `PtrToPtr` cast derives (tag 2, `[0..n)`). -/
private def arrRetMem (n : Nat) : Memory :=
  retMem 3 [deadEntry 2 1 [.subslice 0 n false], deadEntry 1 1]

-- ============================================================================
-- 1. Positive ok canaries
-- ============================================================================

/-! ### 1.1 Unaligned load & store at misaligned byte offset 1 inside `[u8; 8]` -/

/-- `unaligned_volatile_load::<u32>` and `core::ptr::read_unaligned::<u32>` at byte offset 1 of
`[0xAA, 0x78, 0x56, 0x34, 0x12, 0xBB, 0xCC, 0xDD]` return the little-endian `0x12345678`. -/
theorem unaligned_load_array_offset1_ok :
    ReturnsNoUB (arrLoadBody uvLoad 1 tyU32) [] (u32Val 0x12345678) (arrRetMem 8) ∧
    ReturnsNoUB (arrLoadBody readUnaligned 1 tyU32) [] (u32Val 0x12345678) (arrRetMem 8) :=
  ⟨by run_ok, by run_ok⟩

/-- `unaligned_volatile_store::<u32>` and `core::ptr::write_unaligned::<u32>` of `0x04030201` at
byte offset 1 of the same array rewrite exactly bytes `1..5`. -/
theorem unaligned_store_array_offset1_ok :
    ReturnsNoUB (arrStoreBody uvStore 1) []
      (.aggregate 0 [u8Val 0xAA, u8Val 0x01, u8Val 0x02, u8Val 0x03, u8Val 0x04,
                     u8Val 0xBB, u8Val 0xCC, u8Val 0xDD]) (arrRetMem 8) ∧
    ReturnsNoUB (arrStoreBody writeUnaligned 1) []
      (.aggregate 0 [u8Val 0xAA, u8Val 0x01, u8Val 0x02, u8Val 0x03, u8Val 0x04,
                     u8Val 0xBB, u8Val 0xCC, u8Val 0xDD]) (arrRetMem 8) :=
  ⟨by run_ok, by run_ok⟩

/-- An unaligned load that straddles the two `u32` fields of an `align(4)` tuple
`(0x11223344, 0x55667788)` at byte offset 1 returns bytes `33 22 11 88`. The aligned
`volatile_load` through the same pointer is UB (`volatile_load_store_misaligned_ub`). -/
theorem unaligned_load_tuple_offset1_ok :
    ReturnsNoUB (pairPtrBody uvLoad 1 tyU32 [] tyU32) [] (u32Val 0x88112233)
      (retMem 2 [deadEntry 1 1]) ∧
    ReturnsNoUB (pairPtrBody readUnaligned 1 tyU32 [] tyU32) [] (u32Val 0x88112233)
      (retMem 2 [deadEntry 1 1]) :=
  ⟨by run_ok, by run_ok⟩

/-! ### 1.2 Unaligned load & store on a misaligned `#[repr(packed)]` struct field -/

/-- Final memory of the packed bodies: the `&raw` pointer to field `b` (offset 1). -/
private def packedRetMem : Memory := retMem 2 [deadEntry 1 1 [.field 1 tyU32]]

/-- `unaligned_volatile_load::<u32>` and `read_unaligned::<u32>` of `Packed { a: 7, b: 42 }.b`
(byte offset 1 of an `align(1)` struct) return `42`. -/
theorem unaligned_load_packed_field_ok :
    ReturnsNoUB (packedLoadBody uvLoad) [] (u32Val 42) packedRetMem ∧
    ReturnsNoUB (packedLoadBody readUnaligned) [] (u32Val 42) packedRetMem :=
  ⟨by run_ok, by run_ok⟩

/-- `unaligned_volatile_store::<u32>` and `write_unaligned::<u32>` of `0xDEADBEEF` to the packed
field `b` leave field `a` untouched. -/
theorem unaligned_store_packed_field_ok :
    ReturnsNoUB (packedStoreBody uvStore) [] (.aggregate 0 [u8Val 7, u32Val 0xDEADBEEF])
      packedRetMem ∧
    ReturnsNoUB (packedStoreBody writeUnaligned) [] (.aggregate 0 [u8Val 7, u32Val 0xDEADBEEF])
      packedRetMem :=
  ⟨by run_ok, by run_ok⟩

/-! ### 1.3 Aligned volatile load & store -/

/-- `volatile_load::<u32>` and `core::ptr::read_volatile::<u32>` of an aligned `u32` local. -/
theorem volatile_load_aligned_ok :
    ReturnsNoUB (u32LoadBody vLoad) [] (u32Val 0x11223344) (retMem 2 [deadEntry 1 1]) ∧
    ReturnsNoUB (u32LoadBody readVolatile) [] (u32Val 0x11223344) (retMem 2 [deadEntry 1 1]) :=
  ⟨by run_ok, by run_ok⟩

/-- `volatile_store::<u32>` and `core::ptr::write_volatile::<u32>` of `0xCAFEBABE` to an aligned
`u32` local, read back through the local. -/
theorem volatile_store_aligned_ok :
    ReturnsNoUB (u32StoreBody vStore) [] (u32Val 0xCAFEBABE) (retMem 2 [deadEntry 1 1]) ∧
    ReturnsNoUB (u32StoreBody writeVolatile) [] (u32Val 0xCAFEBABE) (retMem 2 [deadEntry 1 1]) :=
  ⟨by run_ok, by run_ok⟩

/-- `volatile_load::<u32>` at the aligned interior byte offset 4 of `(0x11223344, 0x55667788)`
returns the second field. -/
theorem volatile_load_aligned_interior_offset_ok :
    ReturnsNoUB (pairPtrBody vLoad 4 tyU32 [] tyU32) [] (u32Val 0x55667788)
      (retMem 2 [deadEntry 1 1]) := by
  run_ok

/-- Aligned volatile access to zero-sized values: `volatile_load::<[u32; 0]>` returns the empty
array, `volatile_store::<[u32; 0]>` is a no-op, and `volatile_load::<()>` through the null
address returns `()` (a volatile access does not require a non-null pointer). -/
theorem volatile_zero_sized_aligned_ok :
    ReturnsNoUB (pairPtrBody vLoad 4 tyArrU32_0 [] tyArrU32_0) [] (.aggregate 0 [])
      (retMem 2 [deadEntry 1 1]) ∧
    ReturnsNoUB (pairPtrBody vStore 4 tyArrU32_0 [cZst tyArrU32_0] tyUnit) [] .unit
      (retMem 2 [deadEntry 1 1]) ∧
    ReturnsNoUB (constCallBody vLoad tyUnit [cAddr tyPtrConstUnit 0] tyUnit) [] .unit
      (retMem 1 []) :=
  ⟨by run_ok, by run_ok, by run_ok⟩

/-! ### 1.4 `volatile_copy_nonoverlapping_memory`: `(dst, src, count)` argument order -/

/-- With `src = 0x11223344` and `dst = 0x99887766`,
`volatile_copy_nonoverlapping_memory::<u32>(&raw mut dst, &raw const src, 1)` leaves
`(src, dst) = (0x11223344, 0x11223344)`: the first argument is the destination. Under the
swapped `(src, dst, count)` order the result would be `(0x99887766, 0x99887766)`. -/
theorem volatile_copy_nonoverlapping_memory_dst_src_count_order_ok :
    ReturnsNoUB (copyPairBody vCopyNonoverlapping 1) []
      (.aggregate 0 [u32Val 0x11223344, u32Val 0x11223344])
      (retMem 3 [deadEntry 2 2, deadEntry 1 1]) := by
  run_ok

/-- Disjoint ranges of one array (`[0..2)` to `[2..4)` of `[10, 20, 30, 40]`) are not an overlap
for `volatile_copy_nonoverlapping_memory`. -/
theorem volatile_copy_nonoverlapping_memory_same_array_disjoint_ok :
    ReturnsNoUB (arr4CopyBody vCopyNonoverlapping 2 0 2) []
      (.aggregate 0 [u8Val 10, u8Val 20, u8Val 10, u8Val 20]) (arrRetMem 4) := by
  run_ok

/-! ### 1.5 Overlapping `volatile_copy_memory` (`memmove`) inside one array -/

/-- `volatile_copy_memory::<u8>` on `[10, 20, 30, 40]` with overlapping ranges copies as
`memmove` in both directions: `dst > src` (`[0..3)` to `[1..4)`) gives `[10, 10, 20, 30]`,
and `dst < src` (`[1..4)` to `[0..3)`) gives `[20, 30, 40, 40]`. -/
theorem volatile_copy_memory_overlapping_memmove_ok :
    ReturnsNoUB (arr4CopyBody vCopy 1 0 3) []
      (.aggregate 0 [u8Val 10, u8Val 10, u8Val 20, u8Val 30]) (arrRetMem 4) ∧
    ReturnsNoUB (arr4CopyBody vCopy 0 1 3) []
      (.aggregate 0 [u8Val 20, u8Val 30, u8Val 40, u8Val 40]) (arrRetMem 4) :=
  ⟨by run_ok, by run_ok⟩

/-! ### 1.6 `volatile_set_memory` -/

/-- `volatile_set_memory::<u8>(p.add(1), 0x5A, 2)` on `[1, 2, 3, 4]` fills exactly bytes
`1..3`. -/
theorem volatile_set_memory_ok :
    ReturnsNoUB (arr4SetBody 1 0x5A 2) []
      (.aggregate 0 [u8Val 1, u8Val 0x5A, u8Val 0x5A, u8Val 4]) (arrRetMem 4) := by
  run_ok

/-- With aligned pointers, `count = 0` is a no-op for all three memory intrinsics (the misaligned
`count = 0` calls are UB, `volatile_copy_set_misaligned_count_zero_ub`). -/
theorem volatile_copy_set_aligned_count_zero_ok :
    ReturnsNoUB (pairCopyBody vCopyNonoverlapping 4 0 0 tyU32) [] .unit
      (retMem 2 [deadEntry 1 1]) ∧
    ReturnsNoUB (pairCopyBody vCopy 4 0 0 tyU32) [] .unit (retMem 2 [deadEntry 1 1]) ∧
    ReturnsNoUB (pairPtrBody vSet 4 tyU32 [cU8 0, cUsize 0] tyUnit) [] .unit
      (retMem 2 [deadEntry 1 1]) :=
  ⟨by run_ok, by run_ok, by run_ok⟩

/-! ### 1.7 `Rvalue.nullaryOp` -/

/-- `SizeOf` of `u32` and of `#[repr(C)] struct Align4S { a: u8, b: [u8; 3], c: u32 }`. -/
theorem nullaryOp_sizeOf_ok :
    ReturnsNoUB (nullaryBody .sizeOf tyU32 tyUsize) [] (usizeVal 4) (retMem 1 []) ∧
    ReturnsNoUB (nullaryBody .sizeOf tyAlign4S tyUsize) [] (usizeVal 8) (retMem 1 []) :=
  ⟨by run_ok, by run_ok⟩

/-- `AlignOf` of `u32` and of `Align4S`. -/
theorem nullaryOp_alignOf_ok :
    ReturnsNoUB (nullaryBody .alignOf tyU32 tyUsize) [] (usizeVal 4) (retMem 1 []) ∧
    ReturnsNoUB (nullaryBody .alignOf tyAlign4S tyUsize) [] (usizeVal 4) (retMem 1 []) :=
  ⟨by run_ok, by run_ok⟩

/-- `OffsetOf` of fields `b` (1) and `c` (4) of `Align4S`, and of field 1 of `(u32, u32)`. -/
theorem nullaryOp_offsetOf_ok :
    ReturnsNoUB (nullaryBody (.offsetOf [(0, 1)]) tyAlign4S tyUsize) [] (usizeVal 1)
      (retMem 1 []) ∧
    ReturnsNoUB (nullaryBody (.offsetOf [(0, 2)]) tyAlign4S tyUsize) [] (usizeVal 4)
      (retMem 1 []) ∧
    ReturnsNoUB (nullaryBody (.offsetOf [(0, 1)]) tyPairU32 tyUsize) [] (usizeVal 4)
      (retMem 1 []) :=
  ⟨by run_ok, by run_ok, by run_ok⟩

/-- `UbChecks` evaluates to `true`. -/
theorem nullaryOp_ubChecks_ok :
    ReturnsNoUB (nullaryBody .ubChecks tyBool tyBool) [] (u8Val 1) (retMem 1 []) := by
  run_ok

/-! ### 1.8 `CastKind.fnPtrToPtr` -/

/-- Reifying the `FnDef` `test::callee` through the `ReifyFnPointer` coercion interns it at
`fnPtrAllocBase = 65536`, and `CastKind.fnPtrToPtr` to `*const ()` keeps that address and
provenance. -/
theorem fnPtrToPtr_reified_fn_ok :
    ReturnsNoUB fnPtrToPtrBody [] (.ptr ⟨65536, 0⟩ 8)
      { fnPtrs := [{ allocId := 65536, defPath := "test::callee",
                     fnSig := some tyFnPtr.kind }] } := by
  run_ok

/-! ### 1.9 Valid bit patterns and unprotected / read-only accesses (controls for section 2) -/

/-- `read_unaligned::<bool>` of the byte `1` and `volatile_load::<char>` of `0x41` are valid
(the invalid patterns are UB, `load_invalid_bool_char_ub`). -/
theorem load_valid_bool_char_ok :
    ReturnsNoUB (reinterpretLoadBody readUnaligned tyU8 (cU8 1) tyBool) [] (u8Val 1)
      (retMem 2 [deadEntry 1 1]) ∧
    ReturnsNoUB (reinterpretLoadBody vLoad tyU32 (cU32 0x41) tyChar) [] (u32Val 0x41)
      (retMem 2 [deadEntry 1 1]) :=
  ⟨by run_ok, by run_ok⟩

/-- Without the callee's `FnEntry` retag there is no protected tag, and the same store through
`p` that is UB in `protector_conflict_store_ub` returns normally. -/
theorem unprotected_store_in_callee_ok :
    ReturnsNoUBFrom (protCaller tyUnit)
      (initMachineStateWithCallees (protCaller tyUnit) []
        [protCallee false uvStore [cU32 9] tyUnit])
      .unit
      { callees := [protCallee false uvStore [cU32 9] tyUnit],
        activeCallee := some (protCaller tyUnit),
        nextTag := 2, borrows := [deadEntry 1 1] } := by
  run_ok

/-- A load through `p` while the callee's reborrow of `r` is protected is a foreign read of a
protected `Reserved` tag, which is not a conflict: the call returns `7`. -/
theorem protected_read_in_callee_ok :
    ReturnsNoUBFrom (protCaller tyU32)
      (initMachineStateWithCallees (protCaller tyU32) []
        [protCallee true uvLoad [] tyU32])
      (u32Val 7)
      { callees := [protCallee true uvLoad [] tyU32],
        activeCallee := some (protCaller tyU32),
        nextTag := 3, nextProtector := 2,
        borrows := [{ tag := 2, targetLocal := 1, targetProjection := [], perm := .disabled,
                      protector := some 1, parentTag := some 1, allocDead := true },
                    deadEntry 1 1] } := by
  run_ok

-- ============================================================================
-- 2. Negative undefined (.ub) canaries
-- ============================================================================

/-! ### 2.1 Misaligned aligned-volatile accesses (alignment is checked first) -/

/-- `volatile_load` / `read_volatile` / `volatile_store` / `write_volatile` at `u32` through a
pointer at byte offset 1 of an `align(4)` tuple are UB. -/
theorem volatile_load_store_misaligned_ub :
    FaultsWith (pairPtrBody vLoad 1 tyU32 [] tyU32) [] .ub ∧
    FaultsWith (pairPtrBody readVolatile 1 tyU32 [] tyU32) [] .ub ∧
    FaultsWith (pairPtrBody vStore 1 tyU32 [cU32 9] tyUnit) [] .ub ∧
    FaultsWith (pairPtrBody writeVolatile 1 tyU32 [cU32 9] tyUnit) [] .ub :=
  ⟨by run_fault, by run_fault, by run_fault, by run_fault⟩

/-- The pointers of section 1.1 and 1.2 (offset 1 of `[u8; 8]`, the packed field `b`) are
misaligned for the aligned `volatile_load` / `volatile_store`. -/
theorem volatile_load_store_array_and_packed_field_misaligned_ub :
    FaultsWith (arrLoadBody vLoad 1 tyU32) [] .ub ∧
    FaultsWith (arrStoreBody vStore 1) [] .ub ∧
    FaultsWith (packedLoadBody vLoad) [] .ub ∧
    FaultsWith (packedStoreBody vStore) [] .ub :=
  ⟨by run_fault, by run_fault, by run_fault, by run_fault⟩

/-- A misaligned destination or source is UB for `volatile_copy_nonoverlapping_memory`,
`volatile_copy_memory` and `volatile_set_memory` with `count = 1`. -/
theorem volatile_copy_set_misaligned_ub :
    FaultsWith (pairCopyBody vCopyNonoverlapping 1 4 1 tyU32) [] .ub ∧
    FaultsWith (pairCopyBody vCopyNonoverlapping 4 1 1 tyU32) [] .ub ∧
    FaultsWith (pairCopyBody vCopy 1 4 1 tyU32) [] .ub ∧
    FaultsWith (pairCopyBody vCopy 4 1 1 tyU32) [] .ub ∧
    FaultsWith (pairPtrBody vSet 1 tyU32 [cU8 0, cUsize 1] tyUnit) [] .ub :=
  ⟨by run_fault, by run_fault, by run_fault, by run_fault, by run_fault⟩

/-- The same calls with `count = 0` are still UB: alignment is required even when no byte is
accessed. -/
theorem volatile_copy_set_misaligned_count_zero_ub :
    FaultsWith (pairCopyBody vCopyNonoverlapping 1 4 0 tyU32) [] .ub ∧
    FaultsWith (pairCopyBody vCopyNonoverlapping 4 1 0 tyU32) [] .ub ∧
    FaultsWith (pairCopyBody vCopy 1 4 0 tyU32) [] .ub ∧
    FaultsWith (pairCopyBody vCopy 4 1 0 tyU32) [] .ub ∧
    FaultsWith (pairPtrBody vSet 1 tyU32 [cU8 0, cUsize 0] tyUnit) [] .ub :=
  ⟨by run_fault, by run_fault, by run_fault, by run_fault, by run_fault⟩

/-- Misaligned pointers at the zero-sized `align(4)` types `[u32; 0]` and `Zst4` are UB for all
five aligned intrinsics, although no byte is accessed. -/
theorem volatile_zero_sized_misaligned_ub :
    FaultsWith (pairPtrBody vLoad 1 tyArrU32_0 [] tyArrU32_0) [] .ub ∧
    FaultsWith (pairPtrBody vLoad 1 tyZstAlign4 [] tyZstAlign4) [] .ub ∧
    FaultsWith (pairPtrBody vStore 1 tyArrU32_0 [cZst tyArrU32_0] tyUnit) [] .ub ∧
    FaultsWith (pairCopyBody vCopyNonoverlapping 1 0 3 tyArrU32_0) [] .ub ∧
    FaultsWith (pairCopyBody vCopy 1 0 3 tyArrU32_0) [] .ub ∧
    FaultsWith (pairPtrBody vSet 1 tyArrU32_0 [cU8 0, cUsize 3] tyUnit) [] .ub :=
  ⟨by run_fault, by run_fault, by run_fault, by run_fault, by run_fault, by run_fault⟩

/-! ### 2.2 Out-of-bounds accesses -/

/-- A `u32` access at byte offset 6 of the 8-byte tuple, through a pointer to the whole local,
is UB for `unaligned_volatile_load`, `read_unaligned`, `unaligned_volatile_store` and
`write_unaligned`; so is `unaligned_volatile_load::<usize>` of a 4-byte `u32` local. -/
theorem unaligned_load_store_out_of_bounds_ub :
    FaultsWith (pairPtrBody uvLoad 6 tyU32 [] tyU32) [] .ub ∧
    FaultsWith (pairPtrBody readUnaligned 6 tyU32 [] tyU32) [] .ub ∧
    FaultsWith (pairPtrBody uvStore 6 tyU32 [cU32 9] tyUnit) [] .ub ∧
    FaultsWith (pairPtrBody writeUnaligned 6 tyU32 [cU32 9] tyUnit) [] .ub ∧
    FaultsWith (reinterpretLoadBody uvLoad tyU32 (cU32 5) tyUsize) [] .ub :=
  ⟨by run_fault, by run_fault, by run_fault, by run_fault, by run_fault⟩

/-- Out-of-bounds `volatile_set_memory` and `volatile_copy_memory` (3 bytes at offset 6 of 8). -/
theorem volatile_copy_set_out_of_bounds_ub :
    FaultsWith (pairPtrBody vSet 6 tyU8 [cU8 0, cUsize 3] tyUnit) [] .ub ∧
    FaultsWith (pairCopyBody vCopy 6 0 3 tyU8) [] .ub :=
  ⟨by run_fault, by run_fault⟩

/-! ### 2.3 Dead allocation (`StorageDead`) use after free -/

/-- Loading or storing through a pointer to a local after its `StorageDead` is UB. -/
theorem load_store_after_storage_dead_ub :
    FaultsWith (uafLoadBody uvLoad) [] .ub ∧
    FaultsWith (uafLoadBody readUnaligned) [] .ub ∧
    FaultsWith (uafLoadBody vLoad) [] .ub ∧
    FaultsWith (uafStoreBody uvStore) [] .ub ∧
    FaultsWith (uafStoreBody writeUnaligned) [] .ub ∧
    FaultsWith (uafStoreBody vStore) [] .ub :=
  ⟨by run_fault, by run_fault, by run_fault, by run_fault, by run_fault, by run_fault⟩

/-! ### 2.4 Null pointer on the non-volatile `core::ptr::read_unaligned` / `write_unaligned` -/

/-- `read_unaligned::<u32>(null)` is UB at the first step. -/
theorem read_unaligned_null_ub :
    stepMirFn (constCallBody readUnaligned tyU32 [cAddr tyPtrConstU32 0] tyU32)
        (initMachineState
          (constCallBody readUnaligned tyU32 [cAddr tyPtrConstU32 0] tyU32) []) =
      MirStepNode.fail .ub := by
  kernel_rfl

/-- `read_unaligned::<()>(null)` is UB although `()` is zero-sized. -/
theorem read_unaligned_null_zst_ub :
    stepMirFn (constCallBody readUnaligned tyUnit [cAddr tyPtrConstUnit 0] tyUnit)
        (initMachineState
          (constCallBody readUnaligned tyUnit [cAddr tyPtrConstUnit 0] tyUnit) []) =
      MirStepNode.fail .ub := by
  kernel_rfl

/-- `write_unaligned::<u32>(null, 5)` is UB at the first step. -/
theorem write_unaligned_null_ub :
    stepMirFn (constCallBody writeUnaligned tyU32 [cAddr tyPtrMutU32 0, cU32 5] tyUnit)
        (initMachineState
          (constCallBody writeUnaligned tyU32 [cAddr tyPtrMutU32 0, cU32 5] tyUnit) []) =
      MirStepNode.fail .ub := by
  kernel_rfl

/-- `write_unaligned::<()>(null, ())` is UB although `()` is zero-sized. -/
theorem write_unaligned_null_zst_ub :
    stepMirFn (constCallBody writeUnaligned tyUnit [cAddr tyPtrMutUnit 0, cZst tyUnit] tyUnit)
        (initMachineState
          (constCallBody writeUnaligned tyUnit [cAddr tyPtrMutUnit 0, cZst tyUnit] tyUnit) []) =
      MirStepNode.fail .ub := by
  kernel_rfl

/-! ### 2.5 Overlapping `volatile_copy_nonoverlapping_memory` -/

/-- The overlapping ranges that `volatile_copy_memory` copies as `memmove`
(`volatile_copy_memory_overlapping_memmove_ok`) are UB for
`volatile_copy_nonoverlapping_memory`, in both directions. -/
theorem volatile_copy_nonoverlapping_memory_overlap_ub :
    FaultsWith (arr4CopyBody vCopyNonoverlapping 1 0 3) [] .ub ∧
    FaultsWith (arr4CopyBody vCopyNonoverlapping 0 1 3) [] .ub :=
  ⟨by run_fault, by run_fault⟩

/-! ### 2.6 Tree Borrows -/

/-- `.frozen` write: storing through a pointer derived from a shared reference `&x` is UB for
the unaligned and the volatile stores. -/
theorem tree_borrows_frozen_write_ub :
    FaultsWith (frozenWriteBody uvStore) [] .ub ∧
    FaultsWith (frozenWriteBody vStore) [] .ub ∧
    FaultsWith (frozenWriteBody writeUnaligned) [] .ub ∧
    FaultsWith (frozenWriteBody writeVolatile) [] .ub :=
  ⟨by run_fault, by run_fault, by run_fault, by run_fault⟩

/-- `.disabled` read and write: after the direct write `x = 8` invalidates the `&mut x` tag,
loading or storing through the raw pointer derived from it is UB across both intrinsic and
`core::ptr::{read,write}_{unaligned,volatile}` entry points. -/
theorem tree_borrows_disabled_read_write_ub :
    FaultsWith (disabledBody uvLoad [] tyU32) [] .ub ∧
    FaultsWith (disabledBody vLoad [] tyU32) [] .ub ∧
    FaultsWith (disabledBody readUnaligned [] tyU32) [] .ub ∧
    FaultsWith (disabledBody readVolatile [] tyU32) [] .ub ∧
    FaultsWith (disabledBody uvStore [cU32 9] tyUnit) [] .ub ∧
    FaultsWith (disabledBody vStore [cU32 9] tyUnit) [] .ub ∧
    FaultsWith (disabledBody writeUnaligned [cU32 9] tyUnit) [] .ub ∧
    FaultsWith (disabledBody writeVolatile [cU32 9] tyUnit) [] .ub :=
  ⟨by run_fault, by run_fault, by run_fault, by run_fault,
   by run_fault, by run_fault, by run_fault, by run_fault⟩

/-- Active-protector conflict: inside `callee_prot`, after the `FnEntry` retag protects the
reborrow of `r`, a store through `p` (a foreign write for the protected tag) is UB for the
unaligned and the volatile stores (both intrinsics and `core::ptr::write_{unaligned,volatile}`).
The same call without the retag (`unprotected_store_in_callee_ok`) and the protected read
(`protected_read_in_callee_ok`) return normally. -/
theorem protector_conflict_store_ub :
    StepsTo (protCaller tyUnit)
      (initMachineStateWithCallees (protCaller tyUnit) []
        [protCallee true uvStore [cU32 9] tyUnit])
      (MirStepNode.fail .ub) ∧
    StepsTo (protCaller tyUnit)
      (initMachineStateWithCallees (protCaller tyUnit) []
        [protCallee true vStore [cU32 9] tyUnit])
      (MirStepNode.fail .ub) ∧
    StepsTo (protCaller tyUnit)
      (initMachineStateWithCallees (protCaller tyUnit) []
        [protCallee true writeUnaligned [cU32 9] tyUnit])
      (MirStepNode.fail .ub) ∧
    StepsTo (protCaller tyUnit)
      (initMachineStateWithCallees (protCaller tyUnit) []
        [protCallee true writeVolatile [cU32 9] tyUnit])
      (MirStepNode.fail .ub) :=
  ⟨by run_fault, by run_fault, by run_fault, by run_fault⟩

/-! ### 2.7 Invalid bit patterns and the uninhabited type `!` -/

/-- Loading the byte `2` at `bool`, the surrogate `0xD800` at `char`, or the out-of-range
`0x110000` at `char` is UB. -/
theorem load_invalid_bool_char_ub :
    FaultsWith (reinterpretLoadBody readUnaligned tyU8 (cU8 2) tyBool) [] .ub ∧
    FaultsWith (reinterpretLoadBody uvLoad tyU8 (cU8 2) tyBool) [] .ub ∧
    FaultsWith (reinterpretLoadBody vLoad tyU8 (cU8 2) tyBool) [] .ub ∧
    FaultsWith (reinterpretLoadBody vLoad tyU32 (cU32 0xD800) tyChar) [] .ub ∧
    FaultsWith (reinterpretLoadBody readUnaligned tyU32 (cU32 0xD800) tyChar) [] .ub ∧
    FaultsWith (reinterpretLoadBody vLoad tyU32 (cU32 0x110000) tyChar) [] .ub :=
  ⟨by run_fault, by run_fault, by run_fault, by run_fault, by run_fault, by run_fault⟩

/-- Loading or storing at the uninhabited type `!` is UB across all 8 typed load/store entry
points (`{unaligned_volatile,volatile}_{load,store}` and
`core::ptr::{read,write}_{unaligned,volatile}`). -/
theorem load_store_uninhabited_never_ub :
    FaultsWith (reinterpretLoadBody uvLoad tyUnit (cZst tyUnit) tyNever) [] .ub ∧
    FaultsWith (reinterpretLoadBody vLoad tyUnit (cZst tyUnit) tyNever) [] .ub ∧
    FaultsWith (reinterpretLoadBody readUnaligned tyUnit (cZst tyUnit) tyNever) [] .ub ∧
    FaultsWith (reinterpretLoadBody readVolatile tyUnit (cZst tyUnit) tyNever) [] .ub ∧
    FaultsWith (neverStoreBody uvStore) [] .ub ∧
    FaultsWith (neverStoreBody vStore) [] .ub ∧
    FaultsWith (neverStoreBody writeUnaligned) [] .ub ∧
    FaultsWith (neverStoreBody writeVolatile) [] .ub :=
  ⟨by run_fault, by run_fault, by run_fault, by run_fault,
   by run_fault, by run_fault, by run_fault, by run_fault⟩

/-! ### 2.8 `CastKind.fnPtrToPtr` on a data pointer -/

/-- `CastKind.fnPtrToPtr` applied to the stack-borrowed data pointer `&raw const x` is UB. -/
theorem fnPtrToPtr_stack_data_pointer_ub : FaultsWith fnPtrToPtrDataBody [] .ub := by
  run_fault

/-! ### 2.9 A `.ub` canary is not `.ok` and not `.unsupported` -/

/-- Every `FaultsWith` canary refutes `MirNoUBTree` of the body's call tree. -/
theorem faultsWith_not_noUB {body : CapturedMir} {args : List Value}
    {fk : Trusted.Effect.FailureKind} (h : FaultsWith body args fk) :
    ¬ MirNoUBTree (mirCallTree body args) :=
  StepsTo.not_noUB h

/-- For instance, the misaligned `volatile_load` body is not UB-free. -/
theorem volatile_load_misaligned_not_noUB :
    ¬ MirNoUBTree (mirCallTree (pairPtrBody vLoad 1 tyU32 [] tyU32) []) :=
  faultsWith_not_noUB volatile_load_store_misaligned_ub.1

-- ============================================================================
-- 3. Negative unsupported canaries
-- ============================================================================

/-! ### 3.1 Aligned provenance-less MMIO addresses -/

/-- The provenance-less MMIO address `0x4000_0000`, aligned for `u32`. -/
private def mmioAddr : Value := .scalar ⟨0x4000_0000, 8⟩

/-- `volatile_load::<u32>` and `read_volatile::<u32>` at the aligned provenance-less argument
`Value.scalar ⟨0x4000_0000, 8⟩` step to `MirStepNode.unsupported`. -/
theorem volatile_load_mmio_aligned_unsupported :
    stepMirFn (ptrArgCallBody vLoad (.uint .u32) tyPtrConstU32 [] tyU32)
        (initMachineState (ptrArgCallBody vLoad (.uint .u32) tyPtrConstU32 [] tyU32)
          [mmioAddr]) =
      MirStepNode.unsupported ∧
    stepMirFn (ptrArgCallBody readVolatile (.uint .u32) tyPtrConstU32 [] tyU32)
        (initMachineState (ptrArgCallBody readVolatile (.uint .u32) tyPtrConstU32 [] tyU32)
          [mmioAddr]) =
      MirStepNode.unsupported :=
  ⟨by kernel_rfl, by kernel_rfl⟩

/-- `volatile_store::<u32>` and `write_volatile::<u32>` of `7` to the aligned provenance-less
argument `Value.scalar ⟨0x4000_0000, 8⟩` step to `MirStepNode.unsupported`. -/
theorem volatile_store_mmio_aligned_unsupported :
    stepMirFn (ptrArgCallBody vStore (.uint .u32) tyPtrMutU32 [cU32 7] tyUnit)
        (initMachineState (ptrArgCallBody vStore (.uint .u32) tyPtrMutU32 [cU32 7] tyUnit)
          [mmioAddr]) =
      MirStepNode.unsupported ∧
    stepMirFn (ptrArgCallBody writeVolatile (.uint .u32) tyPtrMutU32 [cU32 7] tyUnit)
        (initMachineState (ptrArgCallBody writeVolatile (.uint .u32) tyPtrMutU32 [cU32 7] tyUnit)
          [mmioAddr]) =
      MirStepNode.unsupported :=
  ⟨by kernel_rfl, by kernel_rfl⟩

/-- The same calls at the misaligned provenance-less argument `0x4000_0001` are UB, not
`.unsupported`: alignment is decided before the address is classified. -/
theorem volatile_load_store_mmio_misaligned_ub :
    stepMirFn (ptrArgCallBody vLoad (.uint .u32) tyPtrConstU32 [] tyU32)
        (initMachineState (ptrArgCallBody vLoad (.uint .u32) tyPtrConstU32 [] tyU32)
          [.scalar ⟨0x4000_0001, 8⟩]) =
      MirStepNode.fail .ub ∧
    stepMirFn (ptrArgCallBody vStore (.uint .u32) tyPtrMutU32 [cU32 7] tyUnit)
        (initMachineState (ptrArgCallBody vStore (.uint .u32) tyPtrMutU32 [cU32 7] tyUnit)
          [.scalar ⟨0x4000_0001, 8⟩]) =
      MirStepNode.fail .ub :=
  ⟨by kernel_rfl, by kernel_rfl⟩

/-- `volatile_copy_nonoverlapping_memory`, `volatile_copy_memory`, and `volatile_set_memory` on
aligned provenance-less addresses step to `MirStepNode.unsupported`. -/
theorem volatile_copy_set_mmio_aligned_unsupported :
    stepMirFn
        (constCallBody vCopyNonoverlapping tyU32
          [cAddr tyPtrMutU32 0x40000000, cAddr tyPtrConstU32 0x40001000, cUsize 1] tyUnit)
        (initMachineState
          (constCallBody vCopyNonoverlapping tyU32
            [cAddr tyPtrMutU32 0x40000000, cAddr tyPtrConstU32 0x40001000, cUsize 1] tyUnit)
          []) =
      MirStepNode.unsupported ∧
    stepMirFn
        (constCallBody vCopy tyU32
          [cAddr tyPtrMutU32 0x40000000, cAddr tyPtrConstU32 0x40001000, cUsize 1] tyUnit)
        (initMachineState
          (constCallBody vCopy tyU32
            [cAddr tyPtrMutU32 0x40000000, cAddr tyPtrConstU32 0x40001000, cUsize 1] tyUnit)
          []) =
      MirStepNode.unsupported ∧
    stepMirFn (constCallBody vSet tyU32 [cAddr tyPtrMutU32 0x40000000, cU8 0, cUsize 1] tyUnit)
        (initMachineState
          (constCallBody vSet tyU32 [cAddr tyPtrMutU32 0x40000000, cU8 0, cUsize 1] tyUnit) []) =
      MirStepNode.unsupported :=
  ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

/-- A volatile load of a non-zero-sized type at the null address is treated as an access outside
all Rust allocations: `MirStepNode.unsupported`, not `.ub` (the non-volatile `read_unaligned` at
null is UB, `read_unaligned_null_ub`). -/
theorem unaligned_volatile_load_null_unsupported :
    stepMirFn (constCallBody uvLoad tyU32 [cAddr tyPtrConstU32 0] tyU32)
        (initMachineState (constCallBody uvLoad tyU32 [cAddr tyPtrConstU32 0] tyU32) []) =
      MirStepNode.unsupported := by
  kernel_rfl

/-! ### 3.2 `Rvalue.nullaryOp .contractChecks` -/

/-- `NullaryOp(ContractChecks)` steps to `MirStepNode.unsupported`. -/
theorem nullaryOp_contractChecks_unsupported :
    stepMirFn (nullaryBody .contractChecks tyBool tyBool)
        (initMachineState (nullaryBody .contractChecks tyBool tyBool) []) =
      MirStepNode.unsupported := by
  kernel_rfl

/-! ### 3.3 `size_of_val` / `align_of_val` on `*const dyn Trait` -/

/-- A well-formed wide `*const dyn Trait` argument (data pointer and vtable pointer). -/
private def wideDynPtr : Value := .aggregate 0 [.ptr ⟨3, 0⟩ 8, .ptr ⟨9, 0⟩ 8]

/-- `core::intrinsics::size_of_val::<dyn Trait>` on a well-formed wide pointer steps to
`MirStepNode.unsupported` (the vtable is not modelled), while a non-wide pointer is UB. -/
theorem size_of_val_dyn_wide_unsupported_thin_ub :
    stepMirFn (dynValBody "core::intrinsics::size_of_val")
        (initMachineState (dynValBody "core::intrinsics::size_of_val") [wideDynPtr]) =
      MirStepNode.unsupported ∧
    stepMirFn (dynValBody "core::intrinsics::size_of_val")
        (initMachineState (dynValBody "core::intrinsics::size_of_val") [.ptr ⟨3, 0⟩ 8]) =
      MirStepNode.fail .ub :=
  ⟨by kernel_rfl, by kernel_rfl⟩

/-- `core::intrinsics::align_of_val::<dyn Trait>` on a well-formed wide pointer steps to
`MirStepNode.unsupported`, while a non-wide pointer is UB. -/
theorem align_of_val_dyn_wide_unsupported_thin_ub :
    stepMirFn (dynValBody "core::intrinsics::align_of_val")
        (initMachineState (dynValBody "core::intrinsics::align_of_val") [wideDynPtr]) =
      MirStepNode.unsupported ∧
    stepMirFn (dynValBody "core::intrinsics::align_of_val")
        (initMachineState (dynValBody "core::intrinsics::align_of_val") [.ptr ⟨3, 0⟩ 8]) =
      MirStepNode.fail .ub :=
  ⟨by kernel_rfl, by kernel_rfl⟩

/-! ### 3.4 Out-of-bounds access through a pointer to a sub-place -/

/-- A `u32` access at byte offset 6 of `[u8; 8]` through the element pointer that `PtrToPtr`
derives from `&raw a` (a borrow of the sub-place `a[0..8]`, not of the whole local) runs past
that sub-place and steps to `MirStepNode.unsupported`, not `.ub`: only an access past a
whole-local borrow is classified as out of bounds
(`unaligned_load_store_out_of_bounds_ub`). -/
theorem unaligned_load_store_past_subplace_unsupported :
    FaultsWith (arrLoadBody uvLoad 6 tyU32) [] .unsupported ∧
    FaultsWith (arrLoadBody readUnaligned 6 tyU32) [] .unsupported ∧
    FaultsWith (arrStoreBody uvStore 6) [] .unsupported :=
  ⟨by run_fault, by run_fault, by run_fault⟩

-- ============================================================================
-- 4. MiniRust (`Mach` & `MachTB`): vtable pointers, `&dyn Trait`, and misaligned accesses
-- ============================================================================

/-!
The MiniRust side of the canaries runs the executable interpretation of the pinned MiniRust
specification (`MiniRustSpec.Interp`) on the two witness machines of
`MiniRustSpec.Correspondence.VTablePtr`: `vtMach : Machine<BasicMemory>` and
`vtMachTB : Machine<TreeBorrowsMemory>`, which register `vtableA` (trait `traitA`, size 4,
align 4) at address `4096` and `vtableB` (trait `traitB`, size 8, align 8) at `8192`, and hold a
live 8-byte allocation at address `64` and a dead one at `128`. Every statement is evaluated by
the kernel (`rfl`).
-/

section MiniRustCanaries

open MiniRustSpec.Interp (checkPtr checkPtrM checkValue checkValueM vtableFromPtr vtableFromPtrM
  evalValue evalValueM)
open MiniRustSpec.Correspondence.VTablePtr (vtMach vtMachTB vtPtrA vtPtrB vtPtrATB vtPtrBTB
  vtNameA vtNameB dataPtr dataPtrTB traitA traitB dynRefA dynBoxA vtableA)

/-! ### 4.1 Positive `ok` canaries -/

/-- A registered vtable pointer passes `check_ptr` at `PtrType::VTablePtr` of its trait, and
`vtable_from_ptr` returns its vtable, on both machines. -/
theorem minirust_vtablePtr_checkPtr_ok :
    vtableFromPtr vtMach vtPtrA = .ok vtableA ∧
    vtableFromPtrM vtMachTB vtPtrATB = .ok vtableA ∧
    checkPtr ⟨vtPtrA, none⟩ (.VTablePtr traitA) (some vtMach) = .ok () ∧
    checkPtrM ⟨vtPtrATB, none⟩ (.VTablePtr traitA) (some vtMachTB) = .ok () ∧
    checkValue (.Ptr ⟨vtPtrB, none⟩) (.Ptr (.VTablePtr traitB)) (some vtMach) = .ok () ∧
    checkValueM (.Ptr ⟨vtPtrBTB, none⟩) (.Ptr (.VTablePtr traitB)) (some vtMachTB) = .ok () :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `&dyn TraitA` and `Box<dyn TraitA>` with an aligned, non-null, dereferenceable data pointer
and the vtable pointer of `traitA` pass `check_ptr` / `check_value` on both machines (dynamic
size 4 and alignment 4 come from the vtable). -/
theorem minirust_dyn_ref_checkPtr_checkValue_ok :
    checkPtr ⟨dataPtr 64, some (.VTablePointer vtPtrA)⟩ dynRefA (some vtMach) = .ok () ∧
    checkPtrM ⟨dataPtrTB 64, some (.VTablePointer vtPtrATB)⟩ dynRefA (some vtMachTB) = .ok () ∧
    checkPtr ⟨dataPtr 68, some (.VTablePointer vtPtrA)⟩ dynBoxA (some vtMach) = .ok () ∧
    checkPtrM ⟨dataPtrTB 68, some (.VTablePointer vtPtrATB)⟩ dynBoxA (some vtMachTB) = .ok () ∧
    checkValue (.Ptr ⟨dataPtr 64, some (.VTablePointer vtPtrA)⟩) (.Ptr dynRefA) (some vtMach) =
      .ok () ∧
    checkValueM (.Ptr ⟨dataPtrTB 64, some (.VTablePointer vtPtrATB)⟩) (.Ptr dynRefA)
      (some vtMachTB) = .ok () :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `CastOp::Transmute` with a machine reaches the vtable and safe-pointer checks and succeeds:
a thin raw pointer to a stand-alone vtable pointer, and a wide raw `*const dyn TraitA` to
`&dyn TraitA`, on both machines. -/
theorem minirust_transmute_vtablePtr_and_dyn_ref_ok :
    MiniRustSpec.Interp.evalUnOp (.Cast (.Transmute (.Ptr (.VTablePtr traitA))))
      (.Ptr ⟨vtPtrA, none⟩, .Ptr (.Raw .None)) (some vtMach) =
      .ok (.Ptr ⟨vtPtrA, none⟩, .Ptr (.VTablePtr traitA)) ∧
    MiniRustSpec.Interp.evalUnOpM (.Cast (.Transmute (.Ptr (.VTablePtr traitA))))
      (.Ptr ⟨vtPtrATB, none⟩, .Ptr (.Raw .None)) (some vtMachTB) =
      .ok (.Ptr ⟨vtPtrATB, none⟩, .Ptr (.VTablePtr traitA)) ∧
    MiniRustSpec.Interp.evalUnOp (.Cast (.Transmute (.Ptr dynRefA)))
      (.Ptr ⟨dataPtr 64, some (.VTablePointer vtPtrA)⟩,
        .Ptr (.Raw (.VTablePointer traitA))) (some vtMach) =
      .ok (.Ptr ⟨dataPtr 64, some (.VTablePointer vtPtrA)⟩, .Ptr dynRefA) ∧
    MiniRustSpec.Interp.evalUnOpM (.Cast (.Transmute (.Ptr dynRefA)))
      (.Ptr ⟨dataPtrTB 64, some (.VTablePointer vtPtrATB)⟩,
        .Ptr (.Raw (.VTablePointer traitA))) (some vtMachTB) =
      .ok (.Ptr ⟨dataPtrTB 64, some (.VTablePointer vtPtrATB)⟩, .Ptr dynRefA) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- End-to-end machine-level `evalValue` / `evalValueM` on `vtMach` and `vtMachTB`: evaluating
`ValueExpr.Constant (.VTablePointer ...)` piped through `ValueExpr.UnOp (.Cast (.Transmute ...))`
threads `(some m)` from `evalValue(M)` into `evalUnOp(M)` / `transmute(M)` / `checkPtr(M)`,
succeeding for `vtNameA` at `PtrType.VTablePtr traitA` and reporting UB (never `Stop.unsupported`)
for wrong-trait `vtNameB` and unregistered `PointerWithoutProvenance 64`. -/
theorem minirust_evalValue_vtablePtr_ok_and_ub :
    evalValue vtMach
      (.UnOp (.Cast (.Transmute (.Ptr (.VTablePtr traitA))))
        (.Constant (.VTablePointer vtNameA) (.Ptr (.Raw .None)))) =
      .ok ((.Ptr ⟨vtPtrA, none⟩, .Ptr (.VTablePtr traitA)), vtMach) ∧
    evalValueM vtMachTB
      (.UnOp (.Cast (.Transmute (.Ptr (.VTablePtr traitA))))
        (.Constant (.VTablePointer vtNameA) (.Ptr (.Raw .None)))) =
      .ok ((.Ptr ⟨vtPtrATB, none⟩, .Ptr (.VTablePtr traitA)), vtMachTB) ∧
    evalValue vtMach
      (.UnOp (.Cast (.Transmute (.Ptr (.VTablePtr traitA))))
        (.Constant (.VTablePointer vtNameB) (.Ptr (.Raw .None)))) =
      .error (.ub "Value::Ptr: invalid vtable in metadata") ∧
    evalValueM vtMachTB
      (.UnOp (.Cast (.Transmute (.Ptr (.VTablePtr traitA))))
        (.Constant (.VTablePointer vtNameB) (.Ptr (.Raw .None)))) =
      .error (.ub "Value::Ptr: invalid vtable in metadata") ∧
    evalValue vtMach
      (.UnOp (.Cast (.Transmute (.Ptr (.VTablePtr traitA))))
        (.Constant (.PointerWithoutProvenance 64) (.Ptr (.Raw .None)))) =
      .error (.ub "invalid pointer for vtable lookup") ∧
    evalValueM vtMachTB
      (.UnOp (.Cast (.Transmute (.Ptr (.VTablePtr traitA))))
        (.Constant (.PointerWithoutProvenance 64) (.Ptr (.Raw .None)))) =
      .error (.ub "invalid pointer for vtable lookup") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Single-allocation `TreeBorrowsMemory` (8 bytes at address 64) with borrow tree `root`. -/
private def tbMemOf (root : MiniRustSpec.Gen.Node) : MiniRustSpec.Interp.TBM :=
  { params := { implicit_writes := false },
    mem :=
      { allocations :=
          [{ data := List.replicate 8 (.Init 0x11 none), addr := 64, align := ⟨4⟩, kind := .Stack,
             live := true, extra := { root := root } }],
        _phantom := ⟨⟩ } }

private def tbSingleNode (perm : MiniRustSpec.Gen.Permission) : MiniRustSpec.Gen.Node :=
  { children := [], permissions := List.replicate 8 perm, «protected» := .No }

/-- MiniRust's byte memory accepts an unaligned load at an odd address at alignment 1 (4 bytes
at address 65 of the live allocation) and zero-sized accesses through an aligned
provenance-free pointer, on both `BasicMemory` and `TreeBorrowsMemory`. -/
theorem minirust_unaligned_and_zero_sized_access_ok :
    (MiniRustSpec.Interp.BM.load vtMach.mem.memory (dataPtr 65) ⟨4⟩ ⟨1⟩).map Prod.fst =
      .ok (List.replicate 4 .Uninit) ∧
    (MiniRustSpec.Interp.TreeBorrowsMemory.load (tbMemOf (tbSingleNode (.Unprot .Unique)))
      (dataPtrTB 65) ⟨4⟩ ⟨1⟩).map Prod.fst = .ok (List.replicate 4 (.Init 0x11 none)) ∧
    (MiniRustSpec.Interp.BM.load vtMach.mem.memory { addr := 4, provenance := none } ⟨0⟩ ⟨4⟩).map
      Prod.fst = .ok [] ∧
    (MiniRustSpec.Interp.TreeBorrowsMemory.load vtMachTB.mem.memory
      { addr := 4, provenance := none } ⟨0⟩ ⟨4⟩).map Prod.fst = .ok [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Custom DST struct `struct CustomDst { head: u32, tail: dyn TraitA }` (head size 4, align 4,
plus `vtableA` dynamic size 4, align 4 = total size 8, align 4). -/
private def customDstDynRefA : MiniRustSpec.Gen.PtrType :=
  .Ref .Immutable { layout := .Tuple ⟨⟨4⟩, ⟨4⟩, none⟩ (.TraitObject traitA), inhabited := true,
                    unsafe_cells := .TraitObject, freeze := true, unpin := true }

/-- `&CustomDst` passes `check_ptr` at address 64 (8 bytes `[64..72)` fit inside `[64..72)`),
fails with unaligned UB at address 66, and fails with non-dereferenceable UB at address 68
(distinguishing it from bare `&dyn TraitA`, whose dynamic size 4 succeeds at 68), on both
`Mach` and `MachTB`. -/
theorem minirust_custom_dst_dyn_tail_checkPtr :
    checkPtr ⟨dataPtr 64, some (.VTablePointer vtPtrA)⟩ customDstDynRefA (some vtMach) = .ok () ∧
    checkPtrM ⟨dataPtrTB 64, some (.VTablePointer vtPtrATB)⟩ customDstDynRefA (some vtMachTB) =
      .ok () ∧
    checkPtr ⟨dataPtr 66, some (.VTablePointer vtPtrA)⟩ customDstDynRefA (some vtMach) =
      .error (.ub "Value::Ptr: unaligned safe pointer") ∧
    checkPtrM ⟨dataPtrTB 66, some (.VTablePointer vtPtrATB)⟩ customDstDynRefA (some vtMachTB) =
      .error (.ub "Value::Ptr: unaligned safe pointer") ∧
    checkPtr ⟨dataPtr 68, some (.VTablePointer vtPtrA)⟩ customDstDynRefA (some vtMach) =
      .error (.ub "Value::Ptr: non-dereferenceable safe pointer") ∧
    checkPtrM ⟨dataPtrTB 68, some (.VTablePointer vtPtrATB)⟩ customDstDynRefA (some vtMachTB) =
      .error (.ub "Value::Ptr: non-dereferenceable safe pointer") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### 4.2 Negative `undefined` (`.error (.ub _)`) canaries -/

/-- An unregistered pointer (a data pointer, or the vtable's address without provenance) is not
a vtable pointer: UB `"invalid pointer for vtable lookup"` on both machines. -/
theorem minirust_vtablePtr_unregistered_ub :
    vtableFromPtr vtMach (dataPtr 64) = .error (.ub "invalid pointer for vtable lookup") ∧
    vtableFromPtrM vtMachTB (dataPtrTB 64) = .error (.ub "invalid pointer for vtable lookup") ∧
    checkPtr ⟨dataPtr 64, none⟩ (.VTablePtr traitA) (some vtMach) =
      .error (.ub "invalid pointer for vtable lookup") ∧
    checkPtrM ⟨dataPtrTB 64, none⟩ (.VTablePtr traitA) (some vtMachTB) =
      .error (.ub "invalid pointer for vtable lookup") ∧
    checkPtr ⟨{ addr := 4096, provenance := none }, none⟩ (.VTablePtr traitA) (some vtMach) =
      .error (.ub "invalid pointer for vtable lookup") ∧
    checkPtrM ⟨{ addr := 4096, provenance := none }, none⟩ (.VTablePtr traitA) (some vtMachTB) =
      .error (.ub "invalid pointer for vtable lookup") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The vtable of another trait is UB `"Value::Ptr: invalid vtable in metadata"`, both as a
stand-alone vtable pointer and as the metadata of `&dyn TraitA`, on both machines. -/
theorem minirust_vtablePtr_wrong_trait_ub :
    checkPtr ⟨vtPtrB, none⟩ (.VTablePtr traitA) (some vtMach) =
      .error (.ub "Value::Ptr: invalid vtable in metadata") ∧
    checkPtrM ⟨vtPtrBTB, none⟩ (.VTablePtr traitA) (some vtMachTB) =
      .error (.ub "Value::Ptr: invalid vtable in metadata") ∧
    checkPtr ⟨dataPtr 64, some (.VTablePointer vtPtrB)⟩ dynRefA (some vtMach) =
      .error (.ub "Value::Ptr: invalid vtable in metadata") ∧
    checkPtrM ⟨dataPtrTB 64, some (.VTablePointer vtPtrBTB)⟩ dynRefA (some vtMachTB) =
      .error (.ub "Value::Ptr: invalid vtable in metadata") :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Metadata on a stand-alone vtable pointer, and missing or slice metadata on `&dyn TraitA`,
are UB `"Value::Ptr: invalid metadata"` on both machines. -/
theorem minirust_vtablePtr_metadata_ub :
    checkPtr ⟨vtPtrA, some (.ElementCount 1)⟩ (.VTablePtr traitA) (some vtMach) =
      .error (.ub "Value::Ptr: invalid metadata") ∧
    checkPtrM ⟨vtPtrATB, some (.VTablePointer vtPtrATB)⟩ (.VTablePtr traitA) (some vtMachTB) =
      .error (.ub "Value::Ptr: invalid metadata") ∧
    checkPtr ⟨dataPtr 64, none⟩ dynRefA (some vtMach) =
      .error (.ub "Value::Ptr: invalid metadata") ∧
    checkPtrM ⟨dataPtrTB 64, some (.ElementCount 1)⟩ dynRefA (some vtMachTB) =
      .error (.ub "Value::Ptr: invalid metadata") :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `&dyn TraitA` that is unaligned for the vtable's alignment, null, out of bounds for the
vtable's size, or into a dead allocation is UB on both machines, each with the spec's message. -/
theorem minirust_dyn_ref_unaligned_null_oob_ub :
    -- unaligned (address 66, vtable alignment 4)
    checkPtr ⟨dataPtr 66, some (.VTablePointer vtPtrA)⟩ dynRefA (some vtMach) =
      .error (.ub "Value::Ptr: unaligned safe pointer") ∧
    checkPtrM ⟨dataPtrTB 66, some (.VTablePointer vtPtrATB)⟩ dynRefA (some vtMachTB) =
      .error (.ub "Value::Ptr: unaligned safe pointer") ∧
    -- null
    checkPtr ⟨{ addr := 0, provenance := none }, some (.VTablePointer vtPtrA)⟩ dynRefA
      (some vtMach) = .error (.ub "Value::Ptr: null safe pointer") ∧
    checkPtrM ⟨{ addr := 0, provenance := none }, some (.VTablePointer vtPtrATB)⟩ dynRefA
      (some vtMachTB) = .error (.ub "Value::Ptr: null safe pointer") ∧
    -- out of bounds (address 72 is one past the 8-byte allocation; the vtable needs 4 bytes)
    checkPtr ⟨dataPtr 72, some (.VTablePointer vtPtrA)⟩ dynRefA (some vtMach) =
      .error (.ub "Value::Ptr: non-dereferenceable safe pointer") ∧
    checkPtrM ⟨dataPtrTB 72, some (.VTablePointer vtPtrATB)⟩ dynRefA (some vtMachTB) =
      .error (.ub "Value::Ptr: non-dereferenceable safe pointer") ∧
    -- dead allocation
    checkPtr ⟨{ addr := 128, provenance := some (⟨1⟩, ()) }, some (.VTablePointer vtPtrA)⟩
      dynRefA (some vtMach) = .error (.ub "Value::Ptr: non-dereferenceable safe pointer") ∧
    checkPtrM ⟨{ addr := 128, provenance := some (⟨1⟩, []) }, some (.VTablePointer vtPtrATB)⟩
      dynRefA (some vtMachTB) = .error (.ub "Value::Ptr: non-dereferenceable safe pointer") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `CastOp::Transmute` with a machine reports the vtable and safe-pointer violations as UB
(never `Stop.unsupported`): an unregistered pointer, the vtable of another trait, and an
unaligned `&dyn TraitA`, on both machines. -/
theorem minirust_transmute_vtablePtr_ub :
    MiniRustSpec.Interp.evalUnOp (.Cast (.Transmute (.Ptr (.VTablePtr traitA))))
      (.Ptr ⟨dataPtr 64, none⟩, .Ptr (.Raw .None)) (some vtMach) =
      .error (.ub "invalid pointer for vtable lookup") ∧
    MiniRustSpec.Interp.evalUnOpM (.Cast (.Transmute (.Ptr (.VTablePtr traitA))))
      (.Ptr ⟨dataPtrTB 64, none⟩, .Ptr (.Raw .None)) (some vtMachTB) =
      .error (.ub "invalid pointer for vtable lookup") ∧
    MiniRustSpec.Interp.evalUnOp (.Cast (.Transmute (.Ptr (.VTablePtr traitA))))
      (.Ptr ⟨vtPtrB, none⟩, .Ptr (.Raw .None)) (some vtMach) =
      .error (.ub "Value::Ptr: invalid vtable in metadata") ∧
    MiniRustSpec.Interp.evalUnOpM (.Cast (.Transmute (.Ptr (.VTablePtr traitA))))
      (.Ptr ⟨vtPtrBTB, none⟩, .Ptr (.Raw .None)) (some vtMachTB) =
      .error (.ub "Value::Ptr: invalid vtable in metadata") ∧
    MiniRustSpec.Interp.evalUnOp (.Cast (.Transmute (.Ptr dynRefA)))
      (.Ptr ⟨dataPtr 66, some (.VTablePointer vtPtrA)⟩,
        .Ptr (.Raw (.VTablePointer traitA))) (some vtMach) =
      .error (.ub "Value::Ptr: unaligned safe pointer") ∧
    MiniRustSpec.Interp.evalUnOpM (.Cast (.Transmute (.Ptr dynRefA)))
      (.Ptr ⟨dataPtrTB 66, some (.VTablePointer vtPtrATB)⟩,
        .Ptr (.Raw (.VTablePointer traitA))) (some vtMachTB) =
      .error (.ub "Value::Ptr: unaligned safe pointer") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- MiniRust checks alignment first on loads and stores: a misaligned pointer is UB at
alignment 4 for every length, including zero (ZST / `count = 0`), on `BasicMemory` and
`TreeBorrowsMemory`; an out-of-bounds, dead, or provenance-free non-zero-sized access is UB. -/
theorem minirust_misaligned_oob_dead_access_ub :
    -- misaligned, 4 bytes and 0 bytes
    MiniRustSpec.Interp.BM.load vtMach.mem.memory (dataPtr 65) ⟨4⟩ ⟨4⟩ =
      .error (.ub "load from a misaligned pointer") ∧
    MiniRustSpec.Interp.BM.load vtMach.mem.memory (dataPtr 65) ⟨0⟩ ⟨4⟩ =
      .error (.ub "load from a misaligned pointer") ∧
    MiniRustSpec.Interp.BM.store vtMach.mem.memory (dataPtr 65) [] ⟨4⟩ =
      .error (.ub "store to a misaligned pointer") ∧
    MiniRustSpec.Interp.TreeBorrowsMemory.load vtMachTB.mem.memory (dataPtrTB 65) ⟨4⟩ ⟨4⟩ =
      .error (.ub "load from a misaligned pointer") ∧
    MiniRustSpec.Interp.TreeBorrowsMemory.load vtMachTB.mem.memory (dataPtrTB 65) ⟨0⟩ ⟨4⟩ =
      .error (.ub "load from a misaligned pointer") ∧
    MiniRustSpec.Interp.TreeBorrowsMemory.store vtMachTB.mem.memory (dataPtrTB 65) [] ⟨4⟩ =
      .error (.ub "store to a misaligned pointer") ∧
    -- out of bounds, dead allocation, no provenance (alignment 1)
    MiniRustSpec.Interp.BM.load vtMach.mem.memory (dataPtr 69) ⟨4⟩ ⟨1⟩ =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
    MiniRustSpec.Interp.TreeBorrowsMemory.load vtMachTB.mem.memory (dataPtrTB 69) ⟨4⟩ ⟨1⟩ =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
    MiniRustSpec.Interp.BM.load vtMach.mem.memory { addr := 128, provenance := some (⟨1⟩, ()) }
      ⟨4⟩ ⟨1⟩ = .error (.ub "dereferencing pointer to dead allocation") ∧
    MiniRustSpec.Interp.TreeBorrowsMemory.load vtMachTB.mem.memory
      { addr := 128, provenance := some (⟨1⟩, []) } ⟨4⟩ ⟨1⟩ =
      .error (.ub "dereferencing pointer to dead allocation") ∧
    MiniRustSpec.Interp.BM.load vtMach.mem.memory { addr := 0, provenance := none } ⟨4⟩ ⟨1⟩ =
      .error (.ub "dereferencing pointer without provenance") ∧
    MiniRustSpec.Interp.TreeBorrowsMemory.load vtMachTB.mem.memory
      { addr := 0, provenance := none } ⟨4⟩ ⟨1⟩ =
      .error (.ub "dereferencing pointer without provenance") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private def tbProtTree (childPerm : MiniRustSpec.Gen.Permission) : MiniRustSpec.Gen.Node :=
  { children := [{ children := [], permissions := List.replicate 8 childPerm,
                   «protected» := .Strong }],
    permissions := List.replicate 8 (.Unprot .Unique),
    «protected» := .No }

/-- MiniRust `TreeBorrowsMemory` negative UB + positive control canaries for `.Frozen` write,
`.Disabled` read/write, and `Protected.Strong` active-protector foreign-write conflicts, across
both unaligned (align 1, address 65) and aligned (align 4, address 64) accesses. -/
theorem minirust_tb_frozen_disabled_protector_ub :
    -- Frozen write UB (align 1 & align 4), plus positive Frozen read control
    MiniRustSpec.Interp.TreeBorrowsMemory.store (tbMemOf (tbSingleNode (.Unprot .Frozen)))
        (dataPtrTB 65) (List.replicate 4 (.Init 0x22 none)) ⟨1⟩ =
      .error (.ub "Tree Borrows: local write of Frozen reference") ∧
    MiniRustSpec.Interp.TreeBorrowsMemory.store (tbMemOf (tbSingleNode (.Unprot .Frozen)))
        (dataPtrTB 64) (List.replicate 4 (.Init 0x22 none)) ⟨4⟩ =
      .error (.ub "Tree Borrows: local write of Frozen reference") ∧
    (MiniRustSpec.Interp.TreeBorrowsMemory.load (tbMemOf (tbSingleNode (.Unprot .Frozen)))
        (dataPtrTB 65) ⟨4⟩ ⟨1⟩).map Prod.fst =
      .ok (List.replicate 4 (.Init 0x11 none)) ∧
    -- Disabled read & write UB
    MiniRustSpec.Interp.TreeBorrowsMemory.load (tbMemOf (tbSingleNode (.Unprot .Disabled)))
        (dataPtrTB 65) ⟨4⟩ ⟨1⟩ =
      .error (.ub "Tree Borrows: local read of Disabled reference") ∧
    MiniRustSpec.Interp.TreeBorrowsMemory.store (tbMemOf (tbSingleNode (.Unprot .Disabled)))
        (dataPtrTB 65) (List.replicate 4 (.Init 0x22 none)) ⟨1⟩ =
      .error (.ub "Tree Borrows: local write of Disabled reference") ∧
    -- Protected Reserved (had local read) foreign-write UB (align 1 & align 4) + foreign-read ok
    MiniRustSpec.Interp.TreeBorrowsMemory.store (tbMemOf (tbProtTree (.Prot (.Reserved true false))))
        (dataPtrTB 65) (List.replicate 4 (.Init 0x22 none)) ⟨1⟩ =
      .error (.ub "Tree Borrows: foreign write of protected Reserved reference which had a local read") ∧
    MiniRustSpec.Interp.TreeBorrowsMemory.store (tbMemOf (tbProtTree (.Prot (.Reserved true false))))
        (dataPtrTB 64) (List.replicate 4 (.Init 0x22 none)) ⟨4⟩ =
      .error (.ub "Tree Borrows: foreign write of protected Reserved reference which had a local read") ∧
    (MiniRustSpec.Interp.TreeBorrowsMemory.load (tbMemOf (tbProtTree (.Prot (.Reserved true false))))
        (dataPtrTB 65) ⟨4⟩ ⟨1⟩).map Prod.fst =
      .ok (List.replicate 4 (.Init 0x11 none)) ∧
    -- Protected Frozen (had local read) foreign-write UB
    MiniRustSpec.Interp.TreeBorrowsMemory.store (tbMemOf (tbProtTree (.Prot (.Frozen true))))
        (dataPtrTB 65) (List.replicate 4 (.Init 0x22 none)) ⟨1⟩ =
      .error (.ub "Tree Borrows: foreign write of protected Frozen reference which had a local read") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private def canaryFnName : MiniRustSpec.Gen.FnName := ⟨⟨0⟩⟩

private def canaryFn : MiniRustSpec.Gen.Function :=
  { locals := ⟨[]⟩, args := [], ret := ⟨⟨0⟩⟩, calling_convention := .Rust, blocks := ⟨[]⟩,
    start := ⟨⟨0⟩⟩, implicit_writes := false }

private def canaryFnThin : MiniRustSpec.Interp.Ptr :=
  { addr := 4096, provenance := some (⟨0⟩, ()) }

private def canaryFnThinTB : MiniRustSpec.Gen.ThinPointer MiniRustSpec.Gen.TreeBorrowsProvenance :=
  { addr := 4096, provenance := some (⟨0⟩, []) }

private def canaryFnMach : MiniRustSpec.Interp.Mach :=
  { vtMach with
    prog := { vtMach.prog with functions := ⟨[(canaryFnName, canaryFn)]⟩ },
    fn_ptrs := ⟨[(canaryFnName, canaryFnThin)]⟩ }

private def canaryFnMachTB : MiniRustSpec.Interp.MachTB :=
  { vtMachTB with
    prog := { vtMachTB.prog with functions := ⟨[(canaryFnName, canaryFn)]⟩ },
    fn_ptrs := ⟨[(canaryFnName, canaryFnThinTB)]⟩ }

/-- MiniRust `CastKind.fnPtrToPtr` lowering (`Transmute` from `PtrType::FnPtr` to
`PtrType::Raw { meta_kind: None }`) and `Machine::fn_from_ptr` on both `Mach` and `MachTB`:
the transmute preserves the thin pointer, `fn_from_ptr` resolves the registered function, and
`fn_from_ptr` rejects a data pointer with UB `"invalid pointer for function lookup"`. -/
theorem minirust_fnPtrToPtr_transmute_and_fnFromPtr :
    MiniRustSpec.Interp.evalUnOp (.Cast (.Transmute (.Ptr (.Raw .None))))
        (.Ptr ⟨canaryFnThin, none⟩, .Ptr .FnPtr) (some canaryFnMach) =
      .ok (.Ptr ⟨canaryFnThin, none⟩, .Ptr (.Raw .None)) ∧
    MiniRustSpec.Interp.evalUnOpM (.Cast (.Transmute (.Ptr (.Raw .None))))
        (.Ptr ⟨canaryFnThinTB, none⟩, .Ptr .FnPtr) (some canaryFnMachTB) =
      .ok (.Ptr ⟨canaryFnThinTB, none⟩, .Ptr (.Raw .None)) ∧
    MiniRustSpec.Interp.fnFromPtr canaryFnMach (.Ptr ⟨canaryFnThin, none⟩) = .ok canaryFn ∧
    MiniRustSpec.Interp.fnFromPtrM canaryFnMachTB (.Ptr ⟨canaryFnThinTB, none⟩) = .ok canaryFn ∧
    MiniRustSpec.Interp.fnFromPtr canaryFnMach (.Ptr ⟨dataPtr 64, none⟩) =
      .error (.ub "invalid pointer for function lookup") ∧
    MiniRustSpec.Interp.fnFromPtrM canaryFnMachTB (.Ptr ⟨dataPtrTB 64, none⟩) =
      .error (.ub "invalid pointer for function lookup") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### 4.3 `Stop.unsupported` only without a machine -/

/-- With a machine, `check_value` never stops with `Stop.unsupported`, for every value and type,
on both witness machines (instances of the symbolic theorems of
`MiniRustSpec.Correspondence.VTablePtr`); without a machine (`m = none`), the same vtable
pointer and `&dyn TraitA` checks are exactly the machine-free `Stop.unsupported` fallbacks. -/
theorem minirust_unsupported_only_without_machine :
    (∀ (val : MiniRustSpec.Interp.Val) (ty : MiniRustSpec.Gen.«Type») (w : String),
      checkValueM val ty (some vtMach) ≠ .error (.unsupported w)) ∧
    (∀ (val : MiniRustSpec.Gen.Value MiniRustSpec.Interp.TBM) (ty : MiniRustSpec.Gen.«Type»)
      (w : String), checkValueM val ty (some vtMachTB) ≠ .error (.unsupported w)) ∧
    checkPtr ⟨vtPtrA, none⟩ (.VTablePtr traitA) none =
      .error (.unsupported "check_ptr for a vtable pointer (Machine::vtable_from_ptr)") ∧
    checkPtrM ⟨vtPtrATB, none⟩ (.VTablePtr traitA) (none : Option MiniRustSpec.Interp.MachTB) =
      .error (.unsupported "check_ptr for a vtable pointer (Machine::vtable_from_ptr)") ∧
    checkPtr ⟨dataPtr 64, some (.VTablePointer vtPtrA)⟩ dynRefA none =
      .error (.unsupported
        "check_ptr_metadata for vtable pointer metadata (Machine::vtable_from_ptr)") :=
  ⟨fun val ty => MiniRustSpec.Correspondence.VTablePtr.checkValueBM_noUnsupported vtMach val ty,
    fun val ty => MiniRustSpec.Correspondence.VTablePtr.checkValueTB_noUnsupported vtMachTB val ty,
    rfl, rfl, rfl⟩

end MiniRustCanaries

-- ============================================================================
-- Axiom audit (standard axioms only)
-- ============================================================================

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.unaligned_load_array_offset1_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms unaligned_load_array_offset1_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.unaligned_store_packed_field_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms unaligned_store_packed_field_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_store_aligned_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_store_aligned_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_copy_nonoverlapping_memory_dst_src_count_order_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_copy_nonoverlapping_memory_dst_src_count_order_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_copy_memory_overlapping_memmove_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_copy_memory_overlapping_memmove_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_set_memory_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_set_memory_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.nullaryOp_offsetOf_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms nullaryOp_offsetOf_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.fnPtrToPtr_reified_fn_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fnPtrToPtr_reified_fn_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.protected_read_in_callee_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms protected_read_in_callee_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_load_store_misaligned_ub' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_load_store_misaligned_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_copy_set_misaligned_count_zero_ub' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_copy_set_misaligned_count_zero_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_zero_sized_misaligned_ub' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_zero_sized_misaligned_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.unaligned_load_store_out_of_bounds_ub' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms unaligned_load_store_out_of_bounds_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.load_store_after_storage_dead_ub' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms load_store_after_storage_dead_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.read_unaligned_null_zst_ub' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms read_unaligned_null_zst_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_copy_nonoverlapping_memory_overlap_ub' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_copy_nonoverlapping_memory_overlap_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.tree_borrows_frozen_write_ub' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tree_borrows_frozen_write_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.tree_borrows_disabled_read_write_ub' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tree_borrows_disabled_read_write_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.protector_conflict_store_ub' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms protector_conflict_store_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.load_invalid_bool_char_ub' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms load_invalid_bool_char_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.load_store_uninhabited_never_ub' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms load_store_uninhabited_never_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.fnPtrToPtr_stack_data_pointer_ub' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fnPtrToPtr_stack_data_pointer_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_load_misaligned_not_noUB' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_load_misaligned_not_noUB

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.fail_ub_ne_unsupported' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms fail_ub_ne_unsupported

/-- info: 'Anneal.Mir.UnalignedVolatileVTableTests.fail_ne_step' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms fail_ne_step

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_load_store_mmio_misaligned_ub' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_load_store_mmio_misaligned_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_load_mmio_aligned_unsupported' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_load_mmio_aligned_unsupported

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_store_mmio_aligned_unsupported' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_store_mmio_aligned_unsupported

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.nullaryOp_contractChecks_unsupported' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms nullaryOp_contractChecks_unsupported

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.size_of_val_dyn_wide_unsupported_thin_ub' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms size_of_val_dyn_wide_unsupported_thin_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.align_of_val_dyn_wide_unsupported_thin_ub' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms align_of_val_dyn_wide_unsupported_thin_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.unaligned_load_store_past_subplace_unsupported' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms unaligned_load_store_past_subplace_unsupported

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.minirust_vtablePtr_checkPtr_ok' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms minirust_vtablePtr_checkPtr_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.minirust_dyn_ref_checkPtr_checkValue_ok' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms minirust_dyn_ref_checkPtr_checkValue_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.minirust_transmute_vtablePtr_and_dyn_ref_ok' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms minirust_transmute_vtablePtr_and_dyn_ref_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.minirust_unaligned_and_zero_sized_access_ok' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms minirust_unaligned_and_zero_sized_access_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.minirust_vtablePtr_unregistered_ub' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms minirust_vtablePtr_unregistered_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.minirust_vtablePtr_wrong_trait_ub' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms minirust_vtablePtr_wrong_trait_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.minirust_vtablePtr_metadata_ub' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms minirust_vtablePtr_metadata_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.minirust_dyn_ref_unaligned_null_oob_ub' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms minirust_dyn_ref_unaligned_null_oob_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.minirust_transmute_vtablePtr_ub' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms minirust_transmute_vtablePtr_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.minirust_misaligned_oob_dead_access_ub' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms minirust_misaligned_oob_dead_access_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.minirust_unsupported_only_without_machine' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms minirust_unsupported_only_without_machine

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.minirust_custom_dst_dyn_tail_checkPtr' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms minirust_custom_dst_dyn_tail_checkPtr

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.minirust_tb_frozen_disabled_protector_ub' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms minirust_tb_frozen_disabled_protector_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.minirust_fnPtrToPtr_transmute_and_fnFromPtr' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms minirust_fnPtrToPtr_transmute_and_fnFromPtr

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.minirust_evalValue_vtablePtr_ok_and_ub' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms minirust_evalValue_vtablePtr_ok_and_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.unaligned_store_array_offset1_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms unaligned_store_array_offset1_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.unaligned_load_tuple_offset1_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms unaligned_load_tuple_offset1_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.unaligned_load_packed_field_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms unaligned_load_packed_field_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_load_aligned_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_load_aligned_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_load_aligned_interior_offset_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_load_aligned_interior_offset_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_zero_sized_aligned_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_zero_sized_aligned_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_copy_nonoverlapping_memory_same_array_disjoint_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_copy_nonoverlapping_memory_same_array_disjoint_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_copy_set_aligned_count_zero_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_copy_set_aligned_count_zero_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.nullaryOp_sizeOf_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms nullaryOp_sizeOf_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.nullaryOp_alignOf_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms nullaryOp_alignOf_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.nullaryOp_ubChecks_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms nullaryOp_ubChecks_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.load_valid_bool_char_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms load_valid_bool_char_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.unprotected_store_in_callee_ok' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms unprotected_store_in_callee_ok

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_load_store_array_and_packed_field_misaligned_ub' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_load_store_array_and_packed_field_misaligned_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_copy_set_misaligned_ub' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_copy_set_misaligned_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_copy_set_out_of_bounds_ub' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_copy_set_out_of_bounds_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.read_unaligned_null_ub' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms read_unaligned_null_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.write_unaligned_null_ub' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms write_unaligned_null_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.write_unaligned_null_zst_ub' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms write_unaligned_null_zst_ub

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.faultsWith_not_noUB' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms faultsWith_not_noUB

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.volatile_copy_set_mmio_aligned_unsupported' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms volatile_copy_set_mmio_aligned_unsupported

/--
info: 'Anneal.Mir.UnalignedVolatileVTableTests.unaligned_volatile_load_null_unsupported' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms unaligned_volatile_load_null_unsupported

end Anneal.Mir.UnalignedVolatileVTableTests
