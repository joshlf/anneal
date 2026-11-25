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

/-!
# Episode 2 Dual-Authority Correspondence (`MiniRustSpec` Authority):
# `dyn Trait` Unsizing, Trait Upcasting, Vtable Layout, Virtual Dispatch, and Wide-Pointer Queries

Universal operational laws, fault-equivalence, fail-closed boundary theorems,
and kernel-checked concrete witnesses relating
`Trusted.Rustc.V2026_06_01.MirSemantics.{wfVTableEntry, vtableEnvOk,
checkDynVTablePtr, evalThinToDynUnsize, evalDynToDynUnsize, evalUnsizeCoercion,
evalVirtualCall, protectDynReceiverOnEntry, evalDynSizeAlignOfVal,
evalSafeDynSizeAlignOfValCall, evalAddrEqCall, stepMirFn}` directly to
`MiniRustSpec.Interp.{vtableFromPtr, vtableFromPtrM, vtableLookup,
vtableLookupM, computeSize, computeSizeM, computeAlign, computeAlignM,
checkPtrM, evalUnOpM, steps, stepsTB}` across **both `Mach`
(`BasicMemory<x86_64>`) and `MachTB` (`TreeBorrowsMemory<x86_64>`)** for the 4
`dyn Trait` variants of this episode:

1. **`V1` (`thinUnsize`)** — `&T -> &dyn Trait`, `&mut T -> &mut dyn Trait`,
   `*const T -> *const dyn Trait`, `Pin<&mut T> -> Pin<&mut dyn Trait>`; a
   dangling / misaligned / `Disabled` reference is UB while the same raw pointer
   unsizes;
   `Box<T> -> Box<dyn Trait>`, `&Wrapper<T> -> &Wrapper<dyn Trait>`, and
   `Pin<*const T> -> Pin<&dyn Trait>` fail closed (`.unsupported`).
2. **`V2` (`dynUpcastAndNop`)** — `&dyn Sub -> &dyn Super` through the primary
   prefix, a `TraitVPtr` slot, and the supertrait diamond; NOP `dyn A -> dyn A`
   (forged / wrong-trait vtable and dangling `&dyn` are UB, dangling
   `*const dyn` is allowed); an unrelated target trait and an auto-trait
   addition fail closed.
3. **`V3` (`virtualDispatchAndProtector`)** — `InstanceKind::Virtual` dispatch
   on two concrete receiver layouts, `Pin<&mut dyn Trait>` receiver unwrapping
   and re-wrapping, non-method / out-of-bounds slot UB, and the
   Crubit `c16` receiver call protector (`protectDynReceiverOnEntry`), which is
   genuinely `Mach` vs. `MachTB` mode sensitive.
4. **`V4` (`dynLayoutRawBorrowAndAddrEq`)** — dynamic `size_of_val` /
   `align_of_val` (the safe `core::mem` forms check reference validity without
   Tree Borrows permissions), `&raw const (*r)` on `*dyn`, wide `==`
   (`(dataAddr, vtableAddr)` lexicographic), and `rust#166144`
   `core::ptr::addr_eq`.

The trailing corpus interface (`dvTrustedObserve`, `dvMrObserve`,
`dvMrObserveClass`) executes `stepMirFn` and `MiniRustSpec.Interp.{steps,
stepsTB}` directly (no shadow evaluator) and exports kernel-checked 32-key
table lemmas consumed by `Anneal.Mir.DynTraitVTableBundle`.

Cross-authority divergences and modelling notes documented by the theorems of
this module:
- **MiniRust `VTableMethodLookup` on a missing method is `Stop.specPanic`**,
  while Trusted (and Miri) report UB for a non-method or out-of-bounds slot
  (`dv_v3_nonMethod_slot_ub_vs_minirust_specPanic`).
- **MiniRust `checkPtrM` ignores Tree Borrows permissions on `MachTB`**: a typed
  `Load` of a `&dyn Trait` whose tag is `Disabled` succeeds, matching Trusted's
  `dynRefDataValid … checkTB := false` for the safe `size_of_val` /
  `align_of_val` and `&raw const (*r)` (`dv_v4_dynLayout_three_way_witness`,
  `dv_v4_rawBorrow_trusted_witness`).
- **A raw `*const dyn Trait` must still carry a vtable of the right trait** on
  a NOP coercion, on all three interpreters
  (`dv_v2_upcast_and_nop_three_way_witness`).
- **MiniRust has no `ConstructWidePointer` evaluation and no supertrait-vptr
  slots**: the corpus lowers unsizing to a raw-pair write plus a typed `Load`,
  and a trait upcast pairs the validated source data pointer with the
  statically known target vtable (§2).
- **Authority 0 is always Tree Borrows**: the `basic` / `protectedTB` modes of
  the Crubit `c16` key differ in the initial state (protector absent / present);
  `dv_v3_c16_callee_entry_matches_corpus_state` ties that state to the full
  virtual call.

Strict import isolation: this module NEVER imports `Anneal.*`,
`LeanMiriSpec.*`, `MiniRustSpec.Correspondence.DeinitBridge`, or
`MiniRustSpec.Correspondence.IntrinsicBoundary` (verified by the trailing
`#assert_dyn_trait_vtable_mr_audit` check).
-/

namespace MiniRustSpec.DynTraitVTableMR

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
open MiniRustSpec.DropBinderAndSubtypeMR
open MiniRustSpec.NullaryAndPtrCoercionMR

/-! ## §0. Frozen Cross-Root Types, VTable Table, and `CapturedMir` Fixtures

Every definition in this section is shared verbatim between
`MiniRustSpec.DynTraitVTableMR` and `LeanMiriSpec.DynTraitVTableLM`; the
cross-root kernel bridge in `tests/mir/DynTraitVTableTests.lean` locks each
fixture by `Eq.refl`. The section depends on `Trusted.*` only. -/

@[reducible] def dvSpan : String := "dv.rs:1:1"
@[reducible] def dvSt (k : MirAst.StatementKind) : MirAst.Statement := { kind := k, span := dvSpan }
@[reducible] def dvTm (k : MirAst.TerminatorKind) : MirAst.Terminator :=
  { kind := k, span := dvSpan }
@[reducible] def dvBb (stmts : List MirAst.Statement) (term : MirAst.TerminatorKind)
    (isCleanup : Bool := false) : MirAst.BasicBlockData :=
  { statements := stmts, terminator := dvTm term, isCleanup }
@[reducible] def dvDecl (ty : MirAst.Ty) : MirAst.LocalDecl :=
  { mutability := .mut, ty, debugName := none }
@[reducible] def dvLoc (i : Nat) (proj : List MirAst.ProjectionElem := []) : MirAst.Place :=
  { local_ := i, projection := proj }

/-- Trait-object keys (`RigidTy.dynamic` keys) of the corpus: `Tr` (two methods,
implemented for `u32` and `u64`), `Alt` (an unrelated trait implemented for
`u32`), and the supertrait diamond `Sub: Super + Side`, `Super: Base`,
`Side: Base` (all implemented for `u32`). -/
@[reducible] def dvTrKey : String := "dv::Tr"
@[reducible] def dvAltKey : String := "dv::Alt"
@[reducible] def dvSubKey : String := "dv::Sub"
@[reducible] def dvSuperKey : String := "dv::Super"
@[reducible] def dvSideKey : String := "dv::Side"
@[reducible] def dvBaseKey : String := "dv::Base"

@[reducible] def dvU32Ty : MirAst.Ty := { kind := .uint .u32, layoutIdx := 0 }
@[reducible] def dvU64Ty : MirAst.Ty := { kind := .uint .u64, layoutIdx := 0 }
@[reducible] def dvUsizeTy : MirAst.Ty := { kind := .uint .usize, layoutIdx := 0 }
@[reducible] def dvBoolTy : MirAst.Ty := { kind := .bool, layoutIdx := 0 }
@[reducible] def dvRefU32Ty : MirAst.Ty := { kind := .ref .not (.uint .u32), layoutIdx := 0 }
@[reducible] def dvRefMutU32Ty : MirAst.Ty := { kind := .ref .mut (.uint .u32), layoutIdx := 0 }
@[reducible] def dvRefU64Ty : MirAst.Ty := { kind := .ref .not (.uint .u64), layoutIdx := 0 }
@[reducible] def dvRefMutU64Ty : MirAst.Ty := { kind := .ref .mut (.uint .u64), layoutIdx := 0 }
@[reducible] def dvRawConstU32Ty : MirAst.Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 }
@[reducible] def dvRawMutU32Ty : MirAst.Ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 0 }
@[reducible] def dvRefDynTy (k : String) : MirAst.Ty :=
  { kind := .ref .not (.dynamic k), layoutIdx := 0 }
@[reducible] def dvRefMutDynTy (k : String) : MirAst.Ty :=
  { kind := .ref .mut (.dynamic k), layoutIdx := 0 }
@[reducible] def dvRawConstDynTy (k : String) : MirAst.Ty :=
  { kind := .rawPtr .not (.dynamic k), layoutIdx := 0 }
@[reducible] def dvRawMutDynTy (k : String) : MirAst.Ty :=
  { kind := .rawPtr .mut (.dynamic k), layoutIdx := 0 }
@[reducible] def dvPinTy (inner : RigidTy) : MirAst.Ty :=
  { kind := .adt "core::pin::Pin" [inner], layoutIdx := 0 }
@[reducible] def dvBoxTy (inner : RigidTy) : MirAst.Ty :=
  { kind := .adt "alloc::boxed::Box" [inner, .adt "alloc::alloc::Global" []], layoutIdx := 0 }
@[reducible] def dvConstU32 (n : Nat) : MirAst.Operand :=
  .constant { ty := dvU32Ty, val := .scalar (.int ⟨n, 4⟩) }
/-- Zero-sized function-item constant `path::<tyArgs>` (a direct call target). -/
@[reducible] def dvFnConst (path : String) (tyArgs : List RigidTy) : MirAst.Operand :=
  .constant { ty := { kind := .fnDef path tyArgs, layoutIdx := 0 }, val := .zeroSized }

/-- Layout of an unsigned integer scalar of `bytes` bytes. -/
def dvScalarLayout (bytes : Nat) : TypeLayout :=
  { size := ⟨bytes⟩, align := ⟨bytes⟩,
    backendRepr := .scalar (.initialized (.int (bytes * 8) false) ⟨0, 2 ^ (bytes * 8) - 1⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- Layout of a thin pointer on the 64-bit target. -/
def dvPtrLayout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.pointer 0) ⟨1, 2 ^ 64 - 1⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

@[reducible] def dvPtrArg : ArgAbi := { layout := dvPtrLayout, mode := .direct }
@[reducible] def dvU32Arg : ArgAbi := { layout := dvScalarLayout 4, mode := .direct }

/-- The frozen crate-level vtable table of the corpus.

| id | alloc   | concrete | trait   | size | align | slots after the 3-entry header            |
|---:|--------:|----------|---------|-----:|------:|-------------------------------------------|
| 0  | `16384` | `u32`    | `Tr`    | 4    | 4     | `get`, `poke`                             |
| 1  | `16385` | `u64`    | `Tr`    | 8    | 8     | `get`, `poke`                             |
| 2  | `16386` | `u32`    | `Alt`   | 4    | 4     | `alt`                                     |
| 3  | `16387` | `u32`    | `Sub`   | 4    | 4     | `sup`, `sub`, `TraitVPtr(Side)`; prefix `Super` |
| 4  | `16388` | `u32`    | `Super` | 4    | 4     | `sup`; prefix `Base`                      |
| 5  | `16389` | `u32`    | `Side`  | 4    | 4     | `side`; prefix `Base`                     |
| 6  | `16390` | `u32`    | `Base`  | 4    | 4     | (none)                                    | -/
def dvVTables : List CapturedVTable :=
  [ { vtableId := 0, vtableAllocId := 16384, concreteTy := .uint .u32, dynKey := dvTrKey,
      sizeBytes := 4, alignBytes := 4,
      slots := [.dropInPlace none, .size, .align, .method "dv::<u32 as Tr>::get" [],
                .method "dv::<u32 as Tr>::poke" []] },
    { vtableId := 1, vtableAllocId := 16385, concreteTy := .uint .u64, dynKey := dvTrKey,
      sizeBytes := 8, alignBytes := 8,
      slots := [.dropInPlace none, .size, .align, .method "dv::<u64 as Tr>::get" [],
                .method "dv::<u64 as Tr>::poke" []] },
    { vtableId := 2, vtableAllocId := 16386, concreteTy := .uint .u32, dynKey := dvAltKey,
      sizeBytes := 4, alignBytes := 4,
      slots := [.dropInPlace none, .size, .align, .method "dv::<u32 as Alt>::alt" []] },
    { vtableId := 3, vtableAllocId := 16387, concreteTy := .uint .u32, dynKey := dvSubKey,
      sizeBytes := 4, alignBytes := 4, primarySuperVTableId? := some 4,
      slots := [.dropInPlace none, .size, .align, .method "dv::<u32 as Super>::sup" [],
                .method "dv::<u32 as Sub>::sub" [], .traitVPtr 5] },
    { vtableId := 4, vtableAllocId := 16388, concreteTy := .uint .u32, dynKey := dvSuperKey,
      sizeBytes := 4, alignBytes := 4, primarySuperVTableId? := some 6,
      slots := [.dropInPlace none, .size, .align, .method "dv::<u32 as Super>::sup" []] },
    { vtableId := 5, vtableAllocId := 16389, concreteTy := .uint .u32, dynKey := dvSideKey,
      sizeBytes := 4, alignBytes := 4, primarySuperVTableId? := some 6,
      slots := [.dropInPlace none, .size, .align, .method "dv::<u32 as Side>::side" []] },
    { vtableId := 6, vtableAllocId := 16390, concreteTy := .uint .u32, dynKey := dvBaseKey,
      sizeBytes := 4, alignBytes := 4,
      slots := [.dropInPlace none, .size, .align] } ]

/-- `InstanceKind::Virtual` records of the corpus: `Tr::get` (slot `3`) and
`Tr::poke` (slot `4`), plus two deliberately invalid records used by negative
witnesses: `Tr::oob` (slot `9`, out of bounds) and `Tr::hdr` (slot `1`, the
`MetadataSize` header slot, which is not a method). -/
def dvVirtualMethods : List CapturedVirtualMethod :=
  [ { methodDefPath := "dv::Tr::get", dynKey := dvTrKey, slotIdx := 3 },
    { methodDefPath := "dv::Tr::poke", dynKey := dvTrKey, slotIdx := 4 },
    { methodDefPath := "dv::Tr::oob", dynKey := dvTrKey, slotIdx := 9 },
    { methodDefPath := "dv::Tr::hdr", dynKey := dvTrKey, slotIdx := 1 } ]

/-- Build a `CapturedMir` body in `Runtime(PostCleanup)` phase that carries the
frozen `dvVTables` / `dvVirtualMethods` tables. -/
def dvMkBody (defPath : String) (decls : List MirAst.LocalDecl) (argCount : Nat)
    (blocks : List MirAst.BasicBlockData) (args : List ArgAbi := []) : MirAst.CapturedMir :=
  { defPath, phase := .runtimePostCleanup, role := .subject, argCount, localDecls := decls,
    basicBlocks := blocks, layouts := emptyLayoutTable, allocations := [],
    vtables := dvVTables, virtualMethods := dvVirtualMethods,
    fnAbi := { args := args, ret := { layout := dvScalarLayout 4, mode := .direct },
               conv := .rust, canUnwind := true } }

-- V1 (`thinUnsize`) fixtures

/-- `fn(x: u32) -> &dyn Tr { &x as &dyn Tr }`: `&T -> &dyn Trait`. -/
def dvV1RefUnsizeMir : CapturedMir :=
  dvMkBody "dv::v1_ref_unsize"
    [dvDecl (dvRefDynTy dvTrKey), dvDecl dvU32Ty, dvDecl dvRefU32Ty] 1
    [dvBb [dvSt (.assign (dvLoc 2) (.ref .shared (dvLoc 1))),
           dvSt (.assign (dvLoc 0)
             (.cast (.pointerCoercion "Unsize") (.move (dvLoc 2)) (dvRefDynTy dvTrKey)))]
      .return_]

/-- `fn(p: *const u32) -> *const dyn Tr { p as *const dyn Tr }`:
`*const T -> *const dyn Trait`. -/
def dvV1RawUnsizeMir : CapturedMir :=
  dvMkBody "dv::v1_raw_unsize"
    [dvDecl (dvRawConstDynTy dvTrKey), dvDecl dvRawConstU32Ty] 1
    [dvBb [dvSt (.assign (dvLoc 0)
             (.cast (.pointerCoercion "Unsize") (.copy (dvLoc 1)) (dvRawConstDynTy dvTrKey)))]
      .return_]

/-- `fn(r: &u32) -> &dyn Tr { r as &dyn Tr }` on an argument reference. -/
def dvV1RefArgUnsizeMir : CapturedMir :=
  dvMkBody "dv::v1_ref_arg_unsize"
    [dvDecl (dvRefDynTy dvTrKey), dvDecl dvRefU32Ty] 1
    [dvBb [dvSt (.assign (dvLoc 0)
             (.cast (.pointerCoercion "Unsize") (.copy (dvLoc 1)) (dvRefDynTy dvTrKey)))]
      .return_]

/-- `fn(x: u64) -> &mut dyn Tr { &mut x as &mut dyn Tr }`: `&mut T -> &mut dyn Trait`
on the alternate (`u64`) receiver layout. -/
def dvV1MutUnsizeMir : CapturedMir :=
  dvMkBody "dv::v1_mut_unsize"
    [dvDecl (dvRefMutDynTy dvTrKey), dvDecl dvU64Ty, dvDecl dvRefMutU64Ty] 1
    [dvBb [dvSt (.assign (dvLoc 2) (.ref (.mut false) (dvLoc 1))),
           dvSt (.assign (dvLoc 0)
             (.cast (.pointerCoercion "Unsize") (.move (dvLoc 2)) (dvRefMutDynTy dvTrKey)))]
      .return_]

/-- `Pin<&mut u32> -> Pin<&mut dyn Tr>` (`CoerceUnsized` on the transparent
single-field `Pin` wrapper). -/
def dvV1PinUnsizeMir : CapturedMir :=
  dvMkBody "dv::v1_pin_unsize"
    [dvDecl (dvPinTy (.ref .mut (.dynamic dvTrKey))), dvDecl dvU32Ty, dvDecl dvRefMutU32Ty,
     dvDecl (dvPinTy (.ref .mut (.uint .u32)))] 1
    [dvBb [dvSt (.assign (dvLoc 2) (.ref (.mut false) (dvLoc 1))),
           dvSt (.assign (dvLoc 3)
             (.aggregate (.adt "core::pin::Pin" 0 none) [.move (dvLoc 2)])),
           dvSt (.assign (dvLoc 0)
             (.cast (.pointerCoercion "Unsize") (.move (dvLoc 3))
               (dvPinTy (.ref .mut (.dynamic dvTrKey)))))]
      .return_]

/-- An `Unsize` coercion of the argument `_1 : srcTy` to `dstTy` (used for the
fail-closed `Box<T> -> Box<dyn Tr>`, `&Wrapper<T> -> &Wrapper<dyn Tr>`, and
`Pin<*const T> -> Pin<&dyn Tr>` boundary witnesses). -/
def dvV1ArgUnsizeMir (srcTy dstTy : MirAst.Ty) : CapturedMir :=
  dvMkBody "dv::v1_arg_unsize" [dvDecl dstTy, dvDecl srcTy] 1
    [dvBb [dvSt (.assign (dvLoc 0)
             (.cast (.pointerCoercion "Unsize") (.copy (dvLoc 1)) dstTy))]
      .return_]

-- V2 (`dynUpcastAndNop`) fixtures

/-- `fn(x: u32) -> &dyn Dst { (&x as &dyn Sub) as &dyn Dst }`: unsize to
`dyn Sub`, then the `dyn Sub -> dyn Dst` coercion (trait upcast, or NOP when
`dst = Sub`). -/
def dvV2UpcastMir (dst : String) : CapturedMir :=
  dvMkBody "dv::v2_upcast"
    [dvDecl (dvRefDynTy dst), dvDecl dvU32Ty, dvDecl dvRefU32Ty, dvDecl (dvRefDynTy dvSubKey)] 1
    [dvBb [dvSt (.assign (dvLoc 2) (.ref .shared (dvLoc 1))),
           dvSt (.assign (dvLoc 3)
             (.cast (.pointerCoercion "Unsize") (.move (dvLoc 2)) (dvRefDynTy dvSubKey))),
           dvSt (.assign (dvLoc 0)
             (.cast (.pointerCoercion "Unsize") (.move (dvLoc 3)) (dvRefDynTy dst)))]
      .return_]

/-- `&dyn Sub -> &dyn Super`: the primary supertrait (vtable prefix). -/
def dvV2UpcastSuperMir : CapturedMir := dvV2UpcastMir dvSuperKey
/-- `&dyn Sub -> &dyn Side`: a secondary supertrait behind a `TraitVPtr` slot. -/
def dvV2UpcastSideMir : CapturedMir := dvV2UpcastMir dvSideKey
/-- `&dyn Sub -> &dyn Base`: the top of the supertrait diamond. -/
def dvV2UpcastBaseMir : CapturedMir := dvV2UpcastMir dvBaseKey
/-- `&dyn Sub -> &dyn Alt`: not a supertrait (ill-typed; fails closed). -/
def dvV2UpcastAltMir : CapturedMir := dvV2UpcastMir dvAltKey

/-- NOP `&dyn Tr -> &dyn Tr` coercion of the argument `_1`; local `_2 : u32` is
the pointee of the argument in the corpus initial states. -/
def dvV2NopRefMir : CapturedMir :=
  dvMkBody "dv::v2_nop_ref"
    [dvDecl (dvRefDynTy dvTrKey), dvDecl (dvRefDynTy dvTrKey), dvDecl dvU32Ty] 1
    [dvBb [dvSt (.assign (dvLoc 0)
             (.cast (.pointerCoercion "Unsize") (.copy (dvLoc 1)) (dvRefDynTy dvTrKey)))]
      .return_]

/-- NOP `*const dyn Tr -> *const dyn Tr` coercion of the argument `_1`. -/
def dvV2NopRawMir : CapturedMir :=
  dvMkBody "dv::v2_nop_raw"
    [dvDecl (dvRawConstDynTy dvTrKey), dvDecl (dvRawConstDynTy dvTrKey)] 1
    [dvBb [dvSt (.assign (dvLoc 0)
             (.cast (.pointerCoercion "Unsize") (.copy (dvLoc 1)) (dvRawConstDynTy dvTrKey)))]
      .return_]

-- V3 (`virtualDispatchAndProtector`) fixtures

/-- `<u32 as Tr>::get(&self, x: u32) -> u32 { *self ^ x }`. -/
def dvGetU32Mir : CapturedMir :=
  dvMkBody "dv::<u32 as Tr>::get" [dvDecl dvU32Ty, dvDecl dvRefU32Ty, dvDecl dvU32Ty] 2
    [dvBb [dvSt (.assign (dvLoc 0)
             (.binaryOp .bitXor (.copy (dvLoc 1 [.deref])) (.copy (dvLoc 2))))]
      .return_]
    [dvPtrArg, dvU32Arg]

/-- `<u64 as Tr>::get(&self, x: u32) -> u32 { (*self as u32) | x }` (the
alternate receiver layout: size `8`, alignment `8`). -/
def dvGetU64Mir : CapturedMir :=
  dvMkBody "dv::<u64 as Tr>::get"
    [dvDecl dvU32Ty, dvDecl dvRefU64Ty, dvDecl dvU32Ty, dvDecl dvU32Ty] 2
    [dvBb [dvSt (.storageLive 3),
           dvSt (.assign (dvLoc 3) (.cast .intToInt (.copy (dvLoc 1 [.deref])) dvU32Ty)),
           dvSt (.assign (dvLoc 0) (.binaryOp .bitOr (.copy (dvLoc 3)) (.copy (dvLoc 2)))),
           dvSt (.storageDead 3)]
      .return_]
    [dvPtrArg, dvU32Arg]

/-- `<u32 as Tr>::poke(&self, p: *mut u32) -> u32 { *p = 99; 77 }`: writes
through a raw pointer that may alias the receiver. -/
def dvPokeU32Mir : CapturedMir :=
  dvMkBody "dv::<u32 as Tr>::poke" [dvDecl dvU32Ty, dvDecl dvRefU32Ty, dvDecl dvRawMutU32Ty] 2
    [dvBb [dvSt (.assign (dvLoc 2 [.deref]) (.use (dvConstU32 99))),
           dvSt (.assign (dvLoc 0) (.use (dvConstU32 77)))]
      .return_]
    [dvPtrArg, dvPtrArg]

/-- The concrete trait-method bodies linked into every corpus call. -/
def dvCallees : List CapturedMir := [dvGetU32Mir, dvGetU64Mir, dvPokeU32Mir]

/-- `fn(x: T) -> u32 { (&x as &dyn Tr).get(5) }`: unsize, then an
`InstanceKind::Virtual` call of `Tr::get` (vtable slot `3`). -/
def dvV3CallMir (recvTy refTy : MirAst.Ty) (meth : String) : CapturedMir :=
  dvMkBody "dv::v3_call"
    [dvDecl dvU32Ty, dvDecl recvTy, dvDecl refTy, dvDecl (dvRefDynTy dvTrKey)] 1
    [dvBb [dvSt (.assign (dvLoc 2) (.ref .shared (dvLoc 1))),
           dvSt (.assign (dvLoc 3)
             (.cast (.pointerCoercion "Unsize") (.move (dvLoc 2)) (dvRefDynTy dvTrKey)))]
       (.call (dvFnConst meth [.dynamic dvTrKey]) [.move (dvLoc 3), dvConstU32 5] (dvLoc 0)
         (some 1) .continue_),
     dvBb [] .return_]

/-- Virtual `Tr::get` on a `u32` receiver (`__AnnealVtableReceiver` layout). -/
def dvV3CallU32Mir : CapturedMir := dvV3CallMir dvU32Ty dvRefU32Ty "dv::Tr::get"
/-- Virtual `Tr::get` on a `u64` receiver (`__AnnealVtableAltReceiver` layout). -/
def dvV3CallU64Mir : CapturedMir := dvV3CallMir dvU64Ty dvRefU64Ty "dv::Tr::get"
/-- Virtual call through the out-of-bounds slot `9`. -/
def dvV3CallOobMir : CapturedMir := dvV3CallMir dvU32Ty dvRefU32Ty "dv::Tr::oob"
/-- Virtual call through the non-method `MetadataSize` header slot `1`. -/
def dvV3CallHdrMir : CapturedMir := dvV3CallMir dvU32Ty dvRefU32Ty "dv::Tr::hdr"

/-- `fn(r: &dyn Tr) -> u32 { r.get(5) }` on an argument receiver; local
`_2 : u32` is the receiver's pointee in the corpus initial states. -/
def dvV3ArgCallMir : CapturedMir :=
  dvMkBody "dv::v3_arg_call"
    [dvDecl dvU32Ty, dvDecl (dvRefDynTy dvTrKey), dvDecl dvU32Ty] 1
    [dvBb [] (.call (dvFnConst "dv::Tr::get" [.dynamic dvTrKey]) [.move (dvLoc 1), dvConstU32 5]
        (dvLoc 0) (some 1) .continue_),
     dvBb [] .return_]

/-- The body of `<u32 as Tr>::poke` run in its own frame, with the receiver's
pointee as the extra local `_3 : u32`: the Crubit `c16` protected-receiver
aliased write isolated at callee level (`*p = 99` while `&self` is live). -/
def dvV3ProtectedPokeMir : CapturedMir :=
  dvMkBody "dv::v3_protected_poke"
    [dvDecl dvU32Ty, dvDecl dvRefU32Ty, dvDecl dvRawMutU32Ty, dvDecl dvU32Ty] 2
    [dvBb [dvSt (.assign (dvLoc 2 [.deref]) (.use (dvConstU32 99))),
           dvSt (.assign (dvLoc 0) (.use (dvConstU32 77)))]
      .return_]
    [dvPtrArg, dvPtrArg]

/-- The full Crubit `c16` caller:
`let m = &mut x; let p = &raw mut *m; let r: &dyn Tr = &*m; r.poke(p)`. -/
def dvV3PokeCallerMir : CapturedMir :=
  dvMkBody "dv::v3_poke_caller"
    [dvDecl dvU32Ty, dvDecl dvU32Ty, dvDecl dvRefMutU32Ty, dvDecl dvRawMutU32Ty, dvDecl dvRefU32Ty,
     dvDecl (dvRefDynTy dvTrKey)] 1
    [dvBb [dvSt (.assign (dvLoc 2) (.ref (.mut false) (dvLoc 1))),
           dvSt (.assign (dvLoc 3) (.rawPtr .mut (dvLoc 2 [.deref]))),
           dvSt (.assign (dvLoc 4) (.ref .shared (dvLoc 2 [.deref]))),
           dvSt (.assign (dvLoc 5)
             (.cast (.pointerCoercion "Unsize") (.move (dvLoc 4)) (dvRefDynTy dvTrKey)))]
       (.call (dvFnConst "dv::Tr::poke" [.dynamic dvTrKey]) [.move (dvLoc 5), .move (dvLoc 3)]
         (dvLoc 0) (some 1) .continue_),
     dvBb [] .return_]

-- V4 (`dynLayoutRawBorrowAndAddrEq`) fixtures

/-- `fn(r: &dyn Tr) -> usize { path(r) }` for the safe
`core::mem::{size_of_val, align_of_val}`; local `_2 : u32` is the argument's
pointee in the corpus initial states. -/
def dvV4SafeLayoutMir (path : String) : CapturedMir :=
  dvMkBody "dv::v4_safe_layout"
    [dvDecl dvUsizeTy, dvDecl (dvRefDynTy dvTrKey), dvDecl dvU32Ty] 1
    [dvBb [] (.call (dvFnConst path [.dynamic dvTrKey]) [.copy (dvLoc 1)] (dvLoc 0) (some 1)
        .continue_),
     dvBb [] .return_]

/-- Safe `core::mem::size_of_val(&dyn Tr)`. -/
def dvV4SizeSafeMir : CapturedMir := dvV4SafeLayoutMir "core::mem::size_of_val"
/-- Safe `core::mem::align_of_val(&dyn Tr)`. -/
def dvV4AlignSafeMir : CapturedMir := dvV4SafeLayoutMir "core::mem::align_of_val"

/-- `fn(x: T) -> usize { intr(&raw const *(&x as &dyn Tr)) }` for the raw
`core::intrinsics::{size_of_val, align_of_val}` on `*const dyn Tr`. -/
def dvV4IntrLayoutMir (recvTy refTy : MirAst.Ty) (intr : String) : CapturedMir :=
  dvMkBody "dv::v4_intr_layout"
    [dvDecl dvUsizeTy, dvDecl recvTy, dvDecl refTy, dvDecl (dvRefDynTy dvTrKey),
     dvDecl (dvRawConstDynTy dvTrKey)] 1
    [dvBb [dvSt (.assign (dvLoc 2) (.ref .shared (dvLoc 1))),
           dvSt (.assign (dvLoc 3)
             (.cast (.pointerCoercion "Unsize") (.move (dvLoc 2)) (dvRefDynTy dvTrKey))),
           dvSt (.assign (dvLoc 4) (.rawPtr .not (dvLoc 3 [.deref])))]
       (.call (dvFnConst intr [.dynamic dvTrKey]) [.move (dvLoc 4)] (dvLoc 0) (some 1)
         .continue_),
     dvBb [] .return_]

/-- `&raw [const|mut] (*_1)` on the `dyn Tr` pointer argument `_1 : srcTy`;
local `_2 : u32` is the argument's pointee in the corpus initial states. -/
def dvV4RawBorrowMir (mutb : MirAst.Mutability) (srcTy dstTy : MirAst.Ty) : CapturedMir :=
  dvMkBody "dv::v4_raw_borrow" [dvDecl dstTy, dvDecl srcTy, dvDecl dvU32Ty] 1
    [dvBb [dvSt (.assign (dvLoc 0) (.rawPtr mutb (dvLoc 1 [.deref])))] .return_]

/-- `fn(p: *const dyn Tr, q: *const dyn Tr) -> bool { p op q }`: the wide
pointer comparison (`(dataAddr, vtableAddr)` lexicographic). -/
def dvV4WideCmpMir (op : MirAst.BinOp) : CapturedMir :=
  dvMkBody "dv::v4_wide_cmp"
    [dvDecl dvBoolTy, dvDecl (dvRawConstDynTy dvTrKey), dvDecl (dvRawConstDynTy dvTrKey)] 2
    [dvBb [dvSt (.assign (dvLoc 0) (.binaryOp op (.copy (dvLoc 1)) (.copy (dvLoc 2))))] .return_]

/-- Wide `p == q`. -/
def dvV4WideEqMir : CapturedMir := dvV4WideCmpMir .eq

/-- `fn(p: *const dyn Tr, q: *const dyn Alt) -> bool { core::ptr::addr_eq(p, q) }`
(`rust#166144`: thin data-address equality across two trait-object types). -/
def dvV4AddrEqMir : CapturedMir :=
  dvMkBody "dv::v4_addr_eq"
    [dvDecl dvBoolTy, dvDecl (dvRawConstDynTy dvTrKey), dvDecl (dvRawConstDynTy dvAltKey)] 2
    [dvBb [] (.call (dvFnConst "core::ptr::addr_eq" [.dynamic dvTrKey, .dynamic dvAltKey])
        [.copy (dvLoc 1), .copy (dvLoc 2)] (dvLoc 0) (some 1) .continue_),
     dvBb [] .return_]

/-! ## §1. Corpus Keys and the Direct Trusted `stepMirFn` Runner -/

/-- The 4 `dyn Trait` variants of this correspondence. -/
inductive DynVtVariant : Type where
  /-- `&T -> &dyn Trait`, `&mut T -> &mut dyn Trait`, `*const T -> *const dyn Trait`. -/
  | thinUnsize
  /-- `&dyn Sub -> &dyn Super` (trait upcasting) and NOP `dyn A -> dyn A`. -/
  | dynUpcastAndNop
  /-- `InstanceKind::Virtual` method dispatch and the receiver call protector. -/
  | virtualDispatchAndProtector
  /-- Dynamic `size_of_val` / `align_of_val`, `&raw (*r)` on `*dyn`, wide `==`, `addr_eq`. -/
  | dynLayoutRawBorrowAndAddrEq
  deriving DecidableEq, Repr

/-- Corpus test case selector within each of the 4 variants. -/
inductive DynVtCase : Type where
  /-- Primary positive normal-return case. -/
  | okPrimary
  /-- Secondary positive normal-return case. -/
  | okSecondary
  /-- Primary UB fault case. -/
  | ubFault
  /-- Mode-sensitive case on `virtualDispatchAndProtector` (`BasicMemory` returns
      vs. Tree Borrows protector UB); a further normal-return check elsewhere. -/
  | modeCase
  deriving DecidableEq, Repr

/-- Normalized authority-typed observation of one bounded Trusted `stepMirFn`
execution. -/
inductive DynVtTrustedObs : Type where
  | u32Val (bits : Nat)
  | usizeVal (bits : Nat)
  | boolVal (bits : Nat)
  /-- A `dyn Trait` wide pointer `(data pointer, vtable pointer)`: the data
      pointer's allocation / borrow-tag identifier and byte offset, and the
      vtable pointer's `vtableAllocId`. -/
  | widePtr (dataId : Nat) (dataOff : Nat) (vtableAllocId : Nat)
  | ub
  | unsupported
  /-- Out of fuel, a pending interaction, or a return value outside the
      observable domain. -/
  | stuck
  deriving DecidableEq, Repr

/-- Observe a Trusted return `MirSemantics.Value`. -/
def dvTrustedValueObs : MirSemantics.Value → DynVtTrustedObs
  | .scalar ⟨bits, 1⟩ => .boolVal bits
  | .scalar ⟨bits, 4⟩ => .u32Val bits
  | .scalar ⟨bits, 8⟩ => .usizeVal bits
  | .aggregate 0 [.ptr p 8, .ptr vt 8] => .widePtr p.allocId p.offsetBytes vt.allocId
  | _ => .stuck

/-- State of a bounded Trusted `stepMirFn` execution. -/
inductive DvTrustedRunState : Type where
  | running (s : MachineState)
  | done (o : DynVtTrustedObs)

/-- One `stepMirFn` step of the bounded Trusted runner. An uninterpreted
external call is not an observable verdict (`.stuck`). -/
def dvTrustedRunStep (body : CapturedMir) : DvTrustedRunState → DvTrustedRunState
  | .done o => .done o
  | .running s =>
    match stepMirFn body s with
    | .tau (.running s') => .running s'
    | .vis (.inr (.inl (.emit _))) k =>
      match k PUnit.unit with
      | .running s' => .running s'
      | _ => .done .stuck
    | .ret (.normal r) => .done (dvTrustedValueObs r.1)
    | .vis (.inl (.fail .ub)) _ => .done .ub
    | .vis (.inl (.fail .unsupported)) _ => .done .unsupported
    | _ => .done .stuck

/-- Execute `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` directly for up
to `fuel` steps and return the normalized observation. -/
def dvRunTrusted (body : CapturedMir) (fuel : Nat) (s : MachineState) : DynVtTrustedObs :=
  match Nat.repeat (dvTrustedRunStep body) fuel (.running s) with
  | .done o => o
  | .running _ => .stuck

/-- Initialize a Trusted `MachineState` for `body` with all declared frame
locals live (`.uninit` for `_0` and temporaries, `.init v` for arguments), the
concrete trait-method bodies `callees` linked (`initMachineStateWithCallees`),
and `body`'s `dyn` metadata tables registered (`withBodyDynMetadata`). -/
def dvInitLive (body : CapturedMir) (args : List Value) (callees : List CapturedMir := []) :
    MachineState :=
  let base := initMachineStateWithCallees body args callees
  { frame := { base.frame with
      locals := base.frame.locals.map fun
        | .dead => .uninit
        | slot => slot },
    memory := withBodyDynMetadata body base.memory }

/-- A `dyn Trait` wide pointer value `(data, vtable pointer)`. -/
def dvWide (data : Value) (vtableAllocId : Nat) : Value :=
  .aggregate 0 [data, .ptr { allocId := vtableAllocId, offsetBytes := 0 } 8]

/-- The dangling, misaligned data pointer used by the raw-vs-reference
witnesses: byte offset `1` into the untracked allocation `5`. -/
def dvDanglingPtr : Value := .ptr { allocId := 5, offsetBytes := 1 } 8

/-- Initial Trusted state for the fixtures whose argument `_1` is a `dyn Tr`
wide pointer to the frame local `_2 : u32` (`dvV2NopRefMir`, `dvV3ArgCallMir`,
`dvV4SafeLayoutMir`, `dvV4RawBorrowMir`): `_1 = (borrow tag 1, vtable)`, tag `1`
is a borrow of local `2` with permission `perm`, and local `2` holds `slot`. -/
def dvPointeeInit (body : CapturedMir) (vtableAllocId : Nat) (perm : TreeBorrowPerm)
    (slot : LocalSlot) (dataOff : Nat := 0) : MachineState :=
  let base := dvInitLive body
    [dvWide (.ptr { allocId := 1, offsetBytes := dataOff } 8) vtableAllocId] dvCallees
  { frame := { base.frame with locals := base.frame.locals.set 2 slot },
    memory := { base.memory with
      borrows := [ { tag := 1, targetLocal := 2, targetProjection := [], perm := perm,
                     rangeOffset := 0, rangeLen := 4 } ],
      nextTag := 2 } }

/-- Initial Trusted state for `dvV3ProtectedPokeMir`, the state at the callee
entry of the Crubit `c16` call `dvV3PokeCallerMir`
(`dv_v3_c16_callee_entry_matches_corpus_state`): the receiver `_1` carries the
`Frozen` child tag `3` that `protectDynReceiverOnEntry` creates under the
caller's shared reborrow (tag `2`, a child of the `&mut` tag `1`), the raw
alias `_2` carries tag `1`, and all three tags target the pointee local `_3`.
Tag `3` carries the active call protector `1` exactly when
`protectedMode = true`. -/
def dvV3ProtectedInit (protectedMode : Bool) : MachineState :=
  let base := dvInitLive dvV3ProtectedPokeMir
    [.ptr { allocId := 3, offsetBytes := 0 } 8, .ptr { allocId := 1, offsetBytes := 0 } 8]
  { frame := { base.frame with locals := base.frame.locals.set 3 (.init (.scalar ⟨7, 4⟩)) },
    memory := { base.memory with
      borrows :=
        [ { tag := 3, targetLocal := 3, targetProjection := [], perm := .frozen,
            parentTag := some 2, protector := if protectedMode then some 1 else none },
          { tag := 2, targetLocal := 3, targetProjection := [], perm := .frozen,
            parentTag := some 1 },
          { tag := 1, targetLocal := 3, targetProjection := [], perm := .reserved } ],
      nextTag := 4,
      activeProtectors := if protectedMode then [1] else [],
      nextProtector := 2 } }

/-- The `CapturedMir` fixture executed for each `(variant, case)` key. -/
def dvTrustedFixture : DynVtVariant → DynVtCase → CapturedMir
  | .thinUnsize, .okPrimary => dvV1RefUnsizeMir
  | .thinUnsize, .okSecondary => dvV1RawUnsizeMir
  | .thinUnsize, .ubFault => dvV1RefArgUnsizeMir
  | .thinUnsize, .modeCase => dvV1MutUnsizeMir
  | .dynUpcastAndNop, .okPrimary => dvV2UpcastSuperMir
  | .dynUpcastAndNop, .okSecondary => dvV2UpcastSideMir
  | .dynUpcastAndNop, .ubFault => dvV2NopRefMir
  | .dynUpcastAndNop, .modeCase => dvV2NopRawMir
  | .virtualDispatchAndProtector, .okPrimary => dvV3CallU32Mir
  | .virtualDispatchAndProtector, .okSecondary => dvV3CallU64Mir
  | .virtualDispatchAndProtector, .ubFault => dvV3ArgCallMir
  | .virtualDispatchAndProtector, .modeCase => dvV3ProtectedPokeMir
  | .dynLayoutRawBorrowAndAddrEq, .okPrimary => dvV4SizeSafeMir
  | .dynLayoutRawBorrowAndAddrEq, .okSecondary => dvV4AddrEqMir
  | .dynLayoutRawBorrowAndAddrEq, .ubFault => dvV4SizeSafeMir
  | .dynLayoutRawBorrowAndAddrEq, .modeCase => dvV4WideEqMir

/-- The initial Trusted `MachineState` for each `(protectedMode, variant, case)`
key.

| key                       | initial state                                                       |
|---------------------------|---------------------------------------------------------------------|
| `thinUnsize.okPrimary`    | `x = 7u32`                                                          |
| `thinUnsize.okSecondary`  | the dangling, misaligned raw pointer `dvDanglingPtr`                |
| `thinUnsize.ubFault`      | the same dangling pointer, typed `&u32`                             |
| `thinUnsize.modeCase`     | `x = 64u64`                                                         |
| `dynUpcastAndNop.ok*`     | `x = 7u32`                                                          |
| `dynUpcastAndNop.ubFault` | live, aligned `&dyn Tr` whose metadata is the `(u32, Alt)` vtable   |
| `dynUpcastAndNop.modeCase`| dangling `*const dyn Tr` with the valid `(u32, Tr)` vtable          |
| `virtual….okPrimary`      | `x = 7u32`, callees linked                                          |
| `virtual….okSecondary`    | `x = 64u64`, callees linked                                         |
| `virtual….ubFault`        | live, aligned receiver whose metadata is the `(u32, Alt)` vtable    |
| `virtual….modeCase`       | `dvV3ProtectedInit protectedMode`                                   |
| `dynLayout….okPrimary`    | `&dyn Tr` whose borrow tag is `Disabled` (pointee live)             |
| `dynLayout….okSecondary`  | `*const dyn Tr` and `*const dyn Alt` to the same address            |
| `dynLayout….ubFault`      | `&dyn Tr` whose pointee local is dead (`StorageDead`)               |
| `dynLayout….modeCase`     | two `*const dyn Tr` to the same address: `(u32, Tr)` vs `(u64, Tr)` | -/
def dvTrustedInit (protectedMode : Bool) : DynVtVariant → DynVtCase → MachineState
  | .thinUnsize, .okPrimary => dvInitLive dvV1RefUnsizeMir [.scalar ⟨7, 4⟩]
  | .thinUnsize, .okSecondary => dvInitLive dvV1RawUnsizeMir [dvDanglingPtr]
  | .thinUnsize, .ubFault => dvInitLive dvV1RefArgUnsizeMir [dvDanglingPtr]
  | .thinUnsize, .modeCase => dvInitLive dvV1MutUnsizeMir [.scalar ⟨64, 8⟩]
  | .dynUpcastAndNop, .okPrimary => dvInitLive dvV2UpcastSuperMir [.scalar ⟨7, 4⟩]
  | .dynUpcastAndNop, .okSecondary => dvInitLive dvV2UpcastSideMir [.scalar ⟨7, 4⟩]
  | .dynUpcastAndNop, .ubFault =>
    dvPointeeInit dvV2NopRefMir 16386 .frozen (.init (.scalar ⟨7, 4⟩))
  | .dynUpcastAndNop, .modeCase => dvInitLive dvV2NopRawMir [dvWide dvDanglingPtr 16384]
  | .virtualDispatchAndProtector, .okPrimary =>
    dvInitLive dvV3CallU32Mir [.scalar ⟨7, 4⟩] dvCallees
  | .virtualDispatchAndProtector, .okSecondary =>
    dvInitLive dvV3CallU64Mir [.scalar ⟨64, 8⟩] dvCallees
  | .virtualDispatchAndProtector, .ubFault =>
    dvPointeeInit dvV3ArgCallMir 16386 .frozen (.init (.scalar ⟨7, 4⟩))
  | .virtualDispatchAndProtector, .modeCase => dvV3ProtectedInit protectedMode
  | .dynLayoutRawBorrowAndAddrEq, .okPrimary =>
    dvPointeeInit dvV4SizeSafeMir 16384 .disabled (.init (.scalar ⟨7, 4⟩))
  | .dynLayoutRawBorrowAndAddrEq, .okSecondary =>
    dvInitLive dvV4AddrEqMir
      [dvWide (.ptr { allocId := 5, offsetBytes := 0 } 8) 16384,
       dvWide (.ptr { allocId := 5, offsetBytes := 0 } 8) 16386]
  | .dynLayoutRawBorrowAndAddrEq, .ubFault => dvPointeeInit dvV4SizeSafeMir 16384 .frozen .dead
  | .dynLayoutRawBorrowAndAddrEq, .modeCase =>
    dvInitLive dvV4WideEqMir
      [dvWide (.ptr { allocId := 5, offsetBytes := 0 } 8) 16384,
       dvWide (.ptr { allocId := 5, offsetBytes := 0 } 8) 16385]

/-- Step budget of every Trusted corpus execution (the longest run is the
virtual call on the `u64` receiver: 2 caller statements, the call, 4 callee
statements, the callee `return`, and the caller `return`). -/
def dvTrustedFuel : Nat := 24

/-- Direct Trusted observation for every `(protectedMode, variant, case)` key:
runs `stepMirFn` on the actual `CapturedMir` fixture from its initial state. -/
def dvTrustedObserve (protectedMode : Bool) (v : DynVtVariant) (c : DynVtCase) :
    DynVtTrustedObs :=
  dvRunTrusted (dvTrustedFixture v c) dvTrustedFuel (dvTrustedInit protectedMode v c)

/-- The frozen 32-key Trusted observation table. -/
def dvTrustedExpected (protectedMode : Bool) : DynVtVariant → DynVtCase → DynVtTrustedObs
  | .thinUnsize, .okPrimary => .widePtr 1 0 16384
  | .thinUnsize, .okSecondary => .widePtr 5 1 16384
  | .thinUnsize, .ubFault => .ub
  | .thinUnsize, .modeCase => .widePtr 1 0 16385
  | .dynUpcastAndNop, .okPrimary => .widePtr 1 0 16388
  | .dynUpcastAndNop, .okSecondary => .widePtr 1 0 16389
  | .dynUpcastAndNop, .ubFault => .ub
  | .dynUpcastAndNop, .modeCase => .widePtr 5 1 16384
  | .virtualDispatchAndProtector, .okPrimary => .u32Val 2
  | .virtualDispatchAndProtector, .okSecondary => .u32Val 69
  | .virtualDispatchAndProtector, .ubFault => .ub
  | .virtualDispatchAndProtector, .modeCase =>
    match protectedMode with
    | false => .u32Val 77
    | true => .ub
  | .dynLayoutRawBorrowAndAddrEq, .okPrimary => .usizeVal 4
  | .dynLayoutRawBorrowAndAddrEq, .okSecondary => .boolVal 1
  | .dynLayoutRawBorrowAndAddrEq, .ubFault => .ub
  | .dynLayoutRawBorrowAndAddrEq, .modeCase => .boolVal 0

/-- **Kernel-checked Trusted table**: on all 32 keys, executing `stepMirFn` on
the fixture yields exactly the frozen observation. -/
theorem dvTrustedObserve_table (protectedMode : Bool) (v : DynVtVariant) (c : DynVtCase) :
    dvTrustedObserve protectedMode v c = dvTrustedExpected protectedMode v c := by
  cases protectedMode <;> cases v <;> cases c <;> decide +kernel

/-! ## §2. MiniRust Corpus Program, Vtables, and Machines (`Mach` & `MachTB`)

`MiniRustSpec.Interp` keeps `BinOp.ConstructWidePointer` fail-closed
(`.unsupported`), and MiniRust has no supertrait-vptr vtable slots. The corpus
therefore lowers every unsizing coercion the way Episode 1 builds trait-object
pointers: the raw 16-byte pair `(data pointer, vtable pointer)` is written into
a wide-pointer local, and the result is produced by a typed `Load` of that
local, which runs `Machine::vtable_from_ptr`, the trait check, and (for safe
pointers) the dynamic size / alignment / `Memory::dereferenceable` checks of
`check_ptr` (`vtableFromPtrM`, `checkPtrM`). A trait upcast reloads the source
wide pointer at its own type (validating the source vtable) and pairs its thin
data pointer with the statically known target vtable. -/

/-- MiniRust traits of the corpus: `0 = Tr`, `1 = Alt`, `2 = Sub`, `3 = Super`,
`4 = Side`, `5 = Base`. -/
@[reducible] def dvMethGet : Gen.TraitMethodName := ⟨⟨0⟩⟩
/-- The trait method `Tr::poke`. -/
@[reducible] def dvMethPoke : Gen.TraitMethodName := ⟨⟨1⟩⟩

/-- `&dyn Trait_i`. -/
@[reducible] def dvRefDynMrTy (i : Nat) : Gen.Type :=
  .Ptr (.Ref .Immutable ⟨.TraitObject (traitNameOf i), true, .TraitObject, true, true⟩)
/-- `&mut dyn Trait_i`. -/
@[reducible] def dvMutDynMrTy (i : Nat) : Gen.Type :=
  .Ptr (.Ref .Mutable ⟨.TraitObject (traitNameOf i), true, .TraitObject, true, true⟩)
/-- `*const dyn Trait_i`. -/
@[reducible] def dvRawDynMrTy (i : Nat) : Gen.Type := wideDynPtrMrTy i
/-- The MiniRust integer type `u64`. -/
@[reducible] def dvU64It : Gen.IntType := ⟨.Unsigned, ⟨8⟩⟩
/-- `&u32`. -/
@[reducible] def dvRefU32MrTy : Gen.Type :=
  .Ptr (.Ref .Immutable ⟨.Sized ⟨4⟩ ⟨4⟩, true, .Sized [], true, true⟩)

/-- The MiniRust vtables of the corpus, mirroring `dvVTables` (same concrete
sizes and alignments; MiniRust vtables have no header or supertrait slots):

| name | trait   | size | align | methods                         |
|-----:|---------|-----:|------:|---------------------------------|
| 0    | `Tr`    | 4    | 4     | `get -> fn 1`, `poke -> fn 3`   |
| 1    | `Tr`    | 8    | 8     | `get -> fn 2`, `poke -> fn 3`   |
| 2    | `Alt`   | 4    | 4     |                                 |
| 3    | `Sub`   | 4    | 4     |                                 |
| 4    | `Super` | 4    | 4     |                                 |
| 5    | `Side`  | 4    | 4     |                                 |
| 6    | `Base`  | 4    | 4     |                                 | -/
def dvMrVTable : Nat → Gen.VTable
  | 0 =>
    { trait_name := traitNameOf 0, size := ⟨4⟩, align := ⟨4⟩, cells := [],
      methods := ⟨[(dvMethGet, fnName 1), (dvMethPoke, fnName 3)]⟩ }
  | 1 =>
    { trait_name := traitNameOf 0, size := ⟨8⟩, align := ⟨8⟩, cells := [],
      methods := ⟨[(dvMethGet, fnName 2), (dvMethPoke, fnName 3)]⟩ }
  | n + 2 =>
    { trait_name := traitNameOf (n + 1), size := ⟨4⟩, align := ⟨4⟩, cells := [],
      methods := ⟨[]⟩ }

/-- Address of the allocation of MiniRust vtable `i` (`8192 + 16 * i`). -/
@[reducible] def dvVtAddr (i : Nat) : Nat := 8192 + 16 * i
/-- The registered thin pointer of MiniRust vtable `i` (allocation `3 + i`). -/
@[reducible] def dvVtPtr (i : Nat) : Ptr := { addr := dvVtAddr i, provenance := some (⟨3 + i⟩, ()) }
/-- The 8 bytes of the pointer to MiniRust vtable `i`. -/
def dvVtBytes (i : Nat) : List Byte := ptrBytes (dvVtAddr i) (some (⟨3 + i⟩, ()))

/-- The `Constant::VTablePointer` thin-pointer expression of vtable `i`, a
vtable of trait `tr`. -/
def dvVtExpr (i tr : Nat) : ValueExpr :=
  .UnOp .GetThinPointer (.Constant (.VTablePointer ⟨⟨i⟩⟩) (.Ptr (.VTablePtr (traitNameOf tr))))

/-- The lowered unsizing step: write the raw pair `(thin, vtable i)` into the
wide-pointer local `dst`. -/
def dvUnsizeStmt (dst : Nat) (thin : ValueExpr) (i tr : Nat) : Gen.Statement :=
  .Assign (.Deref (.AddrOf (.Local (localName dst)) (.Raw .None)) rawDynPairMrTy)
    (.Tuple [thin, dvVtExpr i tr] rawDynPairMrTy)

/-- `<u32 as Tr>::get(&self, x) = *self ^ x` (function `1`): validates the
`&dyn Tr` receiver at function entry and reads the `u32` pointee. -/
def dvMrGetU32 : Gen.Function :=
  mkMrFn [(localName 0, u32MrTy), (localName 1, dvRefDynMrTy 0), (localName 2, u32MrTy)]
    [localName 1, localName 2] (localName 0)
    [(bbName 0, ⟨[.Validate (.Local (localName 1)) true,
        .Assign (.Local (localName 0))
          (.BinOp (.Int .BitXor)
            (.Load (.Deref (.UnOp .GetThinPointer (.Load (.Local (localName 1)))) u32MrTy))
            (.Load (.Local (localName 2))))], .Return, .Regular⟩)]

/-- `<u64 as Tr>::get(&self, x) = (*self as u32) | x` (function `2`). -/
def dvMrGetU64 : Gen.Function :=
  mkMrFn [(localName 0, u32MrTy), (localName 1, dvRefDynMrTy 0), (localName 2, u32MrTy)]
    [localName 1, localName 2] (localName 0)
    [(bbName 0, ⟨[.Validate (.Local (localName 1)) true,
        .Assign (.Local (localName 0))
          (.BinOp (.Int .BitOr)
            (.UnOp (.Cast (.IntToInt u32))
              (.Load (.Deref (.UnOp .GetThinPointer (.Load (.Local (localName 1)))) u64MrTy)))
            (.Load (.Local (localName 2))))], .Return, .Regular⟩)]

/-- `<u32 as Tr>::poke(&self, p) = { *p = 99; 77 }` (function `3`): validates
the receiver at function entry (a protected retag under Tree Borrows), then
writes through the raw alias `p`. -/
def dvMrPoke : Gen.Function :=
  mkMrFn [(localName 0, u32MrTy), (localName 1, dvRefDynMrTy 0), (localName 2, thinRawPtrMrTy)]
    [localName 1, localName 2] (localName 0)
    [(bbName 0, ⟨[.Validate (.Local (localName 1)) true,
        .Assign (.Deref (.Load (.Local (localName 2))) u32MrTy) (.Constant (.Int 99) u32MrTy),
        .Assign (.Local (localName 0)) (.Constant (.Int 77) u32MrTy)], .Return, .Regular⟩)]

/-- The corpus program around the root function `root`. -/
def dvMrProg (root : Gen.Function) : Gen.Program :=
  { functions := ⟨[(fnName 0, root), (fnName 1, dvMrGetU32), (fnName 2, dvMrGetU64),
                   (fnName 3, dvMrPoke)]⟩,
    start := fnName 0, globals := ⟨[]⟩,
    traits := ⟨[(traitNameOf 0, ⟨[dvMethGet, dvMethPoke]⟩), (traitNameOf 1, ⟨[]⟩),
                (traitNameOf 2, ⟨[]⟩), (traitNameOf 3, ⟨[]⟩), (traitNameOf 4, ⟨[]⟩),
                (traitNameOf 5, ⟨[]⟩)]⟩,
    vtables := ⟨(List.range 7).map fun i => (⟨⟨i⟩⟩, dvMrVTable i)⟩ }

/-- A corpus `BasicMemory` machine. Allocations `0..2` are the functions `1..3`
(at `4096`, `4112`, `4128`), `3..9` the vtables `0..6` (at `8192 + 16 * i`), and
`10..` the frame `allocs`; `locs` maps the root locals to their allocations. -/
def dvMrMach (root : Gen.Function) (allocs : List Gen.Allocation)
    (locs : List (Gen.LocalName × Ptr)) : Mach :=
  let base := mkMrMach (dvMrProg root)
    ([mkFnAlloc 4096, mkFnAlloc 4112, mkFnAlloc 4128] ++
      (List.range 7).map (fun i => mkVTableAlloc (dvVtAddr i)) ++ allocs)
    [mkRootFrame root locs]
    [(fnName 1, { addr := 4096, provenance := some (⟨0⟩, ()) }),
     (fnName 2, { addr := 4112, provenance := some (⟨1⟩, ()) }),
     (fnName 3, { addr := 4128, provenance := some (⟨2⟩, ()) })]
  { base with vtable_ptrs := ⟨(List.range 7).map fun i => (⟨⟨i⟩⟩, dvVtPtr i)⟩ }

/-- The root local `i` lives in frame allocation `10 + i` at address
`128 * (i + 1)`. -/
@[reducible] def dvLocPtr (i : Nat) : Ptr :=
  { addr := 128 * (i + 1), provenance := some (⟨10 + i⟩, ()) }

/-- The data object of the corpus machines: allocation `dataIdx` at `640`. -/
@[reducible] def dvDataBytes (dataIdx : Nat) : List Byte := ptrBytes 640 (some (⟨dataIdx⟩, ()))
/-- The dangling, misaligned thin pointer of the corpus machines (address `641`,
no provenance), the MiniRust counterpart of `dvDanglingPtr`. -/
@[reducible] def dvDanglingBytes : List Byte := ptrBytes 641 none

-- V1 (`thinUnsize`) machines

/-- Unsize the thin pointer in local `1` to the wide pointer type `retTy` with
vtable `i` (a vtable of trait `0`), via the staging local `2`. -/
def dvMrV1Fn (retTy : Gen.Type) (i : Nat) : Gen.Function :=
  mkMrFn [(localName 0, retTy), (localName 1, thinRawPtrMrTy), (localName 2, retTy)] []
    (localName 0)
    [(bbName 0, ⟨[dvUnsizeStmt 2 (.Load (.Local (localName 1))) i 0,
        .Assign (.Local (localName 0)) (.Load (.Local (localName 2)))], .Return, .Regular⟩)]

/-- Machine for `dvMrV1Fn retTy i`: allocation `10` is the 16-byte result local,
`11` the thin-pointer local (holding `thin`), `12` the staging local, and `13`
the live data object `data` at `640` with alignment `align`. -/
def dvMrV1Mach (retTy : Gen.Type) (i : Nat) (thin data : List Byte) (align : Nat) : Mach :=
  dvMrMach (dvMrV1Fn retTy i)
    [mkStackAlloc 128 (List.replicate 16 .Uninit) 8, mkStackAlloc 256 thin 8,
     mkStackAlloc 384 (List.replicate 16 .Uninit) 8, mkHeapAlloc 640 data align]
    [(localName 0, dvLocPtr 0), (localName 1, dvLocPtr 1), (localName 2, dvLocPtr 2)]

-- V2 (`dynUpcastAndNop`) machines

/-- Upcast the `&dyn Sub` (trait `2`) in local `1` to `&dyn Trait_dst` with the
statically known vtable `i`: the source is loaded (and validated) at `&dyn Sub`,
and its thin data pointer is paired with vtable `i`. -/
def dvMrV2UpcastFn (dst i : Nat) : Gen.Function :=
  mkMrFn [(localName 0, dvRefDynMrTy dst), (localName 1, dvRefDynMrTy 2),
      (localName 2, dvRefDynMrTy dst)] [] (localName 0)
    [(bbName 0, ⟨[dvUnsizeStmt 2 (.UnOp .GetThinPointer (.Load (.Local (localName 1)))) i dst,
        .Assign (.Local (localName 0)) (.Load (.Local (localName 2)))], .Return, .Regular⟩)]

/-- Machine for `dvMrV2UpcastFn`: local `1` (allocation `11`) holds the
`(u32, Sub)` wide pointer to the data object (allocation `13`). -/
def dvMrV2UpcastMach (dst i : Nat) : Mach :=
  dvMrMach (dvMrV2UpcastFn dst i)
    [mkStackAlloc 128 (List.replicate 16 .Uninit) 8,
     mkStackAlloc 256 (dvDataBytes 13 ++ dvVtBytes 3) 8,
     mkStackAlloc 384 (List.replicate 16 .Uninit) 8, mkHeapAlloc 640 (scalarBytes u32 7) 4]
    [(localName 0, dvLocPtr 0), (localName 1, dvLocPtr 1), (localName 2, dvLocPtr 2)]

/-- NOP coercion: copy the wide pointer in local `1` at type `ty`. -/
def dvMrV2NopFn (ty : Gen.Type) : Gen.Function :=
  mkMrFn [(localName 0, ty), (localName 1, ty)] [] (localName 0)
    [(bbName 0, ⟨[.Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
      .Return, .Regular⟩)]

/-- Machine for `dvMrV2NopFn ty`: local `1` (allocation `11`) holds `wide`, and
allocation `12` is the live `u32` data object at `640`. -/
def dvMrV2NopMach (ty : Gen.Type) (wide : List Byte) : Mach :=
  dvMrMach (dvMrV2NopFn ty)
    [mkStackAlloc 128 (List.replicate 16 .Uninit) 8, mkStackAlloc 256 wide 8,
     mkHeapAlloc 640 (scalarBytes u32 7) 4]
    [(localName 0, dvLocPtr 0), (localName 1, dvLocPtr 1)]

-- V3 (`virtualDispatchAndProtector`) machines

/-- `r.get(5)` on the `&dyn Tr` receiver in local `1`: the callee is
`VTableMethodLookup(get)(GetMetadata(r))`, and the receiver is passed by
value. -/
def dvMrV3Caller : Gen.Function :=
  mkMrFn [(localName 0, u32MrTy), (localName 1, dvRefDynMrTy 0)] [] (localName 0)
    [(bbName 0, ⟨[], .Call (.UnOp (.VTableMethodLookup dvMethGet)
          (.UnOp .GetMetadata (.Load (.Local (localName 1)))))
        .Rust [.ByValue (.Load (.Local (localName 1))), .ByValue (.Constant (.Int 5) u32MrTy)]
        (.Local (localName 0)) (some (bbName 1)) none, .Regular⟩),
     (bbName 1, ⟨[], .Return, .Regular⟩)]

/-- Machine for `dvMrV3Caller`: allocation `10` is the `u32` result local, `11`
the receiver local (data pointer to allocation `12`, vtable `i`), and `12` the
live data object `data` at `640` with alignment `align`. -/
def dvMrV3Mach (i : Nat) (data : List Byte) (align : Nat) : Mach :=
  dvMrMach dvMrV3Caller
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 256 (dvDataBytes 12 ++ dvVtBytes i) 8, mkHeapAlloc 640 data align]
    [(localName 0, dvLocPtr 0), (localName 1, dvLocPtr 1)]

/-- The Crubit `c16` caller: `r.poke(p)` where the raw alias `p` (local `2`)
points to the receiver's pointee. -/
def dvMrV3PokeCaller : Gen.Function :=
  mkMrFn [(localName 0, u32MrTy), (localName 1, dvRefDynMrTy 0), (localName 2, thinRawPtrMrTy)] []
    (localName 0)
    [(bbName 0, ⟨[], .Call (.UnOp (.VTableMethodLookup dvMethPoke)
          (.UnOp .GetMetadata (.Load (.Local (localName 1)))))
        .Rust [.ByValue (.Load (.Local (localName 1))), .ByValue (.Load (.Local (localName 2)))]
        (.Local (localName 0)) (some (bbName 1)) none, .Regular⟩),
     (bbName 1, ⟨[], .Return, .Regular⟩)]

/-- Machine for `dvMrV3PokeCaller`: allocation `11` is the receiver local, `12`
the raw alias local, and `13` the live `u32` pointee at `640` that both point
to. -/
def dvMrV3PokeMach : Mach :=
  dvMrMach dvMrV3PokeCaller
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 256 (dvDataBytes 13 ++ dvVtBytes 0) 8, mkStackAlloc 384 (dvDataBytes 13) 8,
     mkHeapAlloc 640 (scalarBytes u32 7) 4]
    [(localName 0, dvLocPtr 0), (localName 1, dvLocPtr 1), (localName 2, dvLocPtr 2)]

-- V4 (`dynLayoutRawBorrowAndAddrEq`) machines

/-- `size_of_val(r)` / `align_of_val(r)` on a `&dyn Tr` whose Tree Borrows tag
has been disabled: `r = &x` is retagged (`Validate`), unsized into local `3`,
then `x` is written directly (a foreign write that disables `r`'s tag under Tree
Borrows), and finally the wide reference is loaded at `&dyn Tr` and its
vtable-backed size (`isSize`) or alignment is read. `tail` runs afterwards. -/
def dvMrV4SizeFn (isSize : Bool) (tail : List Gen.Statement := []) : Gen.Function :=
  mkMrFn [(localName 0, usizeMrTy), (localName 1, u32MrTy), (localName 2, dvRefU32MrTy),
      (localName 3, dvRefDynMrTy 0), (localName 4, u32MrTy)] [] (localName 0)
    [(bbName 0, ⟨[
        .Assign (.Local (localName 2))
          (.AddrOf (.Local (localName 1))
            (.Ref .Immutable ⟨.Sized ⟨4⟩ ⟨4⟩, true, .Sized [], true, true⟩)),
        .Validate (.Local (localName 2)) false,
        dvUnsizeStmt 3 (.Load (.Local (localName 2))) 0 0,
        .Assign (.Local (localName 1)) (.Constant (.Int 9) u32MrTy),
        .Assign (.Local (localName 0))
          (.UnOp (if isSize then .ComputeSize (.TraitObject (traitNameOf 0))
                  else .ComputeAlign (.TraitObject (traitNameOf 0)))
            (.UnOp .GetMetadata (.Load (.Local (localName 3)))))] ++ tail,
      .Return, .Regular⟩)]

/-- Machine for `dvMrV4SizeFn`: allocation `10` is the `usize` result local,
`11` the pointee `x = 7u32`, `12` the `&u32` local, `13` the wide local, and
`14` a scratch `u32` local. -/
def dvMrV4SizeMach (isSize : Bool) (tail : List Gen.Statement := []) : Mach :=
  dvMrMach (dvMrV4SizeFn isSize tail)
    [mkStackAlloc 128 (List.replicate 8 .Uninit) 8, mkStackAlloc 256 (scalarBytes u32 7) 4,
     mkStackAlloc 384 (List.replicate 8 .Uninit) 8, mkStackAlloc 512 (List.replicate 16 .Uninit) 8,
     mkStackAlloc 640 (List.replicate 4 .Uninit) 4]
    [(localName 0, dvLocPtr 0), (localName 1, dvLocPtr 1), (localName 2, dvLocPtr 2),
     (localName 3, dvLocPtr 3), (localName 4, dvLocPtr 4)]

/-- `size_of_val(r)` on the `&dyn Tr` argument in local `1`. -/
def dvMrV4ArgSizeFn : Gen.Function :=
  mkMrFn [(localName 0, usizeMrTy), (localName 1, dvRefDynMrTy 0)] [] (localName 0)
    [(bbName 0, ⟨[.Assign (.Local (localName 0))
          (.UnOp (.ComputeSize (.TraitObject (traitNameOf 0)))
            (.UnOp .GetMetadata (.Load (.Local (localName 1)))))], .Return, .Regular⟩)]

/-- Machine for `dvMrV4ArgSizeFn`: the receiver (allocation `11`) points to
allocation `12`, a `u32` object at `640` that is live exactly when `live`. -/
def dvMrV4ArgSizeMach (live : Bool) : Mach :=
  dvMrMach dvMrV4ArgSizeFn
    [mkStackAlloc 128 (List.replicate 8 .Uninit) 8,
     mkStackAlloc 256 (dvDataBytes 12 ++ dvVtBytes 0) 8,
     { mkStackAlloc 640 (scalarBytes u32 7) 4 with live := live }]
    [(localName 0, dvLocPtr 0), (localName 1, dvLocPtr 1)]

/-- Compare the wide pointers in locals `1` (`*const dyn Trait_t1`) and `2`
(`*const dyn Trait_t2`): the whole wide pointers (`thin = false`; MiniRust
`compare_ptr` orders by address, then metadata) or only their thin data
pointers (`thin = true`, i.e. `core::ptr::addr_eq`). -/
def dvMrV4CmpFn (thin : Bool) (t1 t2 : Nat) : Gen.Function :=
  mkMrFn [(localName 0, .Bool), (localName 1, dvRawDynMrTy t1), (localName 2, dvRawDynMrTy t2)] []
    (localName 0)
    [(bbName 0, ⟨[.Assign (.Local (localName 0))
          (if thin then
            .BinOp (.Rel .Eq) (.UnOp .GetThinPointer (.Load (.Local (localName 1))))
              (.UnOp .GetThinPointer (.Load (.Local (localName 2))))
          else
            .BinOp (.Rel .Eq) (.Load (.Local (localName 1))) (.Load (.Local (localName 2))))],
      .Return, .Regular⟩)]

/-- Machine for `dvMrV4CmpFn`: both wide pointers have the provenance-free data
address `640`; local `1` carries vtable `i1` and local `2` vtable `i2`. -/
def dvMrV4CmpMach (thin : Bool) (t1 t2 i1 i2 : Nat) : Mach :=
  dvMrMach (dvMrV4CmpFn thin t1 t2)
    [mkStackAlloc 128 [.Uninit] 1, mkStackAlloc 256 (ptrBytes 640 none ++ dvVtBytes i1) 8,
     mkStackAlloc 384 (ptrBytes 640 none ++ dvVtBytes i2) 8]
    [(localName 0, dvLocPtr 0), (localName 1, dvLocPtr 1), (localName 2, dvLocPtr 2)]

/-! ## §3. Universal Vtable Laws (every `Machine M`: `Mach`, `MachTB`, any `Gen.Memory`)

The corpus tables of §6 run fixed fixtures. The results of this section hold
for EVERY Trusted state / memory view, every captured vtable, and every
MiniRust machine `m` on every memory model `M` (`BasicMemory`, Tree Borrows, or
any other `Gen.Memory` instance). Each universal theorem is followed by a
concrete realizability witness of its hypotheses on `Mach` and `MachTB`. -/

/-- Layout agreement between a Trusted `CapturedVTable` and a MiniRust
`VTable`: the same concrete size and alignment. -/
def DvVTableLayoutRel (cv : CapturedVTable) (vt : Gen.VTable) : Prop :=
  vt.size = ⟨cv.sizeBytes⟩ ∧ vt.align = ⟨cv.alignBytes⟩

instance (cv : CapturedVTable) (vt : Gen.VTable) : Decidable (DvVTableLayoutRel cv vt) := by
  unfold DvVTableLayoutRel
  exact inferInstance

/-- The corpus tables agree: MiniRust vtable `i` has the layout of the Trusted
vtable with `vtableId = i`, for all 7 vtables. -/
theorem dvVTables_layoutRel :
    ∀ i, i < 7 → ∃ cv, lookupVTableById dvVTables i = some cv ∧
      DvVTableLayoutRel cv (dvMrVTable i) := by
  intro i hi
  match i, hi with
  | 0, _ => exact ⟨_, rfl, by decide⟩
  | 1, _ => exact ⟨_, rfl, by decide⟩
  | 2, _ => exact ⟨_, rfl, by decide⟩
  | 3, _ => exact ⟨_, rfl, by decide⟩
  | 4, _ => exact ⟨_, rfl, by decide⟩
  | 5, _ => exact ⟨_, rfl, by decide⟩
  | 6, _ => exact ⟨_, rfl, by decide⟩

/-- **Universal: Trusted `wfVTableEntry` implies the MiniRust `check_ptr`
layout preconditions**. For every captured vtable `v` that is well formed on
the 64-bit target and every MiniRust vtable `vt` with the same layout, the
dynamic size fits in `isize::MAX` (the `"total size exeeds isize::MAX"` check of
`check_ptr`), the alignment is non-zero, and the size is a multiple of the
alignment. -/
theorem dv_wfVTableEntry_minirust_valid_layout (v : CapturedVTable) (vt : Gen.VTable)
    (hWf : wfVTableEntry 8 v = true) (hRel : DvVTableLayoutRel v vt) :
    inBounds (vt.size.bytes : Int) .Signed x86_64.PTR_SIZE = true ∧
    vt.align.bytes ≠ 0 ∧ vt.size.bytes % vt.align.bytes = 0 := by
  obtain ⟨hSize, hAlign⟩ := hRel
  rw [hSize, hAlign]
  unfold wfVTableEntry at hWf
  simp only [Bool.and_eq_true] at hWf
  obtain ⟨⟨hPow, _⟩, _, hLt, hMod, _⟩ := hWf
  have hHalf : Nat.pow 2 (Nat.sub (Nat.mul 8 8) 1) = 9223372036854775808 := by decide
  rw [hHalf] at hLt
  have hLt' : v.sizeBytes + (v.alignBytes - 1) < 9223372036854775808 :=
    Nat.le_of_ble_eq_true hLt
  have hAlignNe : v.alignBytes ≠ 0 := by
    intro h0
    rw [h0] at hPow
    exact absurd hPow (by decide)
  have hMod' : v.sizeBytes % v.alignBytes = 0 := Nat.eq_of_beq_eq_true hMod
  refine ⟨?_, hAlignNe, hMod'⟩
  have hBits : (2 : Int) ^ (Size.bits x86_64.PTR_SIZE - 1) = 9223372036854775808 := by decide
  unfold inBounds
  simp only [hBits, Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> omega

/-- **Universal: dynamic `size_of_val` / `align_of_val` agree with MiniRust
`ComputeSize` / `ComputeAlign`** (`evalDynSizeAlignOfVal` vs. `evalUnOpM` over
`computeSizeM` / `computeAlignM`, on every memory model `M`). Whenever Trusted
`checkDynVTablePtr` resolves the metadata word of a `dyn` wide pointer to the
captured vtable `entry`, and the MiniRust machine registers a vtable `vt` of
trait `tr` with the same layout at `vtThin`, then:
1. Trusted `evalDynSizeAlignOfVal` returns `entry.sizeBytes`, respectively
   `entry.alignBytes`, through `writeIntrinsicReturn` (it never inspects the
   data word beyond its pointer shape);
2. MiniRust `UnOp::ComputeSize(TraitObject tr)` and
   `UnOp::ComputeAlign(TraitObject tr)` on the vtable pointer return the same
   two numbers. -/
theorem dv_dynSizeAlignOfVal_agrees_computeSizeAlign_M {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Gen.Machine M) (tr : Gen.TraitName) (vt : Gen.VTable) (vtName : Gen.VTableName)
    (vtThin vp : Gen.ThinPointer (Gen.Memory.Provenance M))
    (hFind : m.vtable_ptrs.entries.find?
      (fun (_, (vtablePtr : Gen.ThinPointer (Gen.Memory.Provenance M))) =>
        decide (vtablePtr = vtThin)) = some (vtName, vp))
    (hVt : mapIndex m.prog.vtables vtName "self.prog.vtables[vtable_name]" = .ok vt)
    (hTrait : vt.trait_name = tr)
    (hVAddr : inBounds vtThin.addr .Unsigned x86_64.PTR_SIZE = true)
    (s : MachineState) (layouts : LayoutTable) (locals' : List LocalSlot) (dest : Place)
    (bb : BasicBlockIdx) (dataVal metaVal : Value) (dynKey : DefPath)
    (entry : CapturedVTable) (vts : List CapturedVTable) (dts : List CapturedDynType)
    (hData : isPtrSizedWord (layoutPointerBytes layouts) dataVal = true)
    (hChk : checkDynVTablePtr .none (DynMemView.ofMemory s.memory) (layoutPointerBytes layouts)
      metaVal dynKey = .ok (entry, vts, dts))
    (hRel : DvVTableLayoutRel entry vt) (opTy : Gen.Type) :
    evalDynSizeAlignOfVal s layouts locals' dest bb (.aggregate 0 [dataVal, metaVal]) dynKey true =
      writeIntrinsicReturn s locals' dest bb
        (.scalar ⟨entry.sizeBytes, layoutPointerBytes layouts⟩) ∧
    evalDynSizeAlignOfVal s layouts locals' dest bb (.aggregate 0 [dataVal, metaVal]) dynKey false =
      writeIntrinsicReturn s locals' dest bb
        (.scalar ⟨entry.alignBytes, layoutPointerBytes layouts⟩) ∧
    evalUnOpM (.ComputeSize (.TraitObject tr)) (.Ptr (ThinPointer.widen vtThin none), opTy)
        (some m) =
      .ok (.Int (entry.sizeBytes : Int), .Int IntType.usize_ty) ∧
    evalUnOpM (.ComputeAlign (.TraitObject tr)) (.Ptr (ThinPointer.widen vtThin none), opTy)
        (some m) =
      .ok (.Int (entry.alignBytes : Int), .Int IntType.usize_ty) := by
  have hMR := (np_v2_dyn_wide_ptr_vtable_ops_universal_M m tr vt vtName vtThin vtThin vp hFind hVt
    hTrait hVAddr).2.2.2.2.1 opTy
  obtain ⟨hSize, hAlign⟩ := hRel
  rw [hSize, hAlign] at hMR
  refine ⟨?_, ?_, hMR.1, hMR.2⟩
  · unfold evalDynSizeAlignOfVal
    cases dataVal <;> simp only [isPtrSizedWord] at hData <;>
      first | exact absurd hData (by decide) | simp only [hData, hChk]
  · unfold evalDynSizeAlignOfVal
    cases dataVal <;> simp only [isPtrSizedWord] at hData <;>
      first | exact absurd hData (by decide) | simp only [hData, hChk]

/-- **Universal fault / fail-closed law of dynamic `size_of_val` /
`align_of_val`**: `evalDynSizeAlignOfVal` is UB exactly when
`checkDynVTablePtr` is UB and fails closed (`.unsupported`) exactly when
`checkDynVTablePtr` does, for every pointer-shaped data word. -/
theorem dv_dynSizeAlignOfVal_fault_universal
    (s : MachineState) (layouts : LayoutTable) (locals' : List LocalSlot) (dest : Place)
    (bb : BasicBlockIdx) (dataVal metaVal : Value) (dynKey : DefPath) (isSize : Bool)
    (hData : isPtrSizedWord (layoutPointerBytes layouts) dataVal = true) :
    (checkDynVTablePtr .none (DynMemView.ofMemory s.memory) (layoutPointerBytes layouts)
        metaVal dynKey = .ub →
      evalDynSizeAlignOfVal s layouts locals' dest bb (.aggregate 0 [dataVal, metaVal]) dynKey
        isSize = MirStepNode.fail .ub) ∧
    (checkDynVTablePtr .none (DynMemView.ofMemory s.memory) (layoutPointerBytes layouts)
        metaVal dynKey = .unsupported →
      evalDynSizeAlignOfVal s layouts locals' dest bb (.aggregate 0 [dataVal, metaVal]) dynKey
        isSize = MirStepNode.unsupported) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold evalDynSizeAlignOfVal
    cases dataVal <;> simp only [isPtrSizedWord] at hData <;>
      first | exact absurd hData (by decide) | simp only [hData, h]
  · unfold evalDynSizeAlignOfVal
    cases dataVal <;> simp only [isPtrSizedWord] at hData <;>
      first | exact absurd hData (by decide) | simp only [hData, h]

/-- **Universal (`C2`): raw `*const T -> *const dyn Trait` unsizing never
inspects the data pointer**. For EVERY pointer-shaped data word (dangling,
misaligned, null, any provenance), whenever the vtable environment is
consistent and the `(srcPointee, dynKey)` vtable is captured, Trusted
`evalThinToDynUnsize … isRef := false` returns the wide pointer
`(dataVal, vtable)`; and on the reference path (`isRef := true`) the verdict is
exactly `dynRefDataValid` (`.ok` when it holds, `.ub` otherwise). -/
theorem dv_v1_evalThinToDynUnsize_universal
    (locals' : List LocalSlot) (mv : DynMemView) (decls : List MirAst.LocalDecl)
    (layouts : LayoutTable) (dataVal : Value) (srcPointee : RigidTy) (dynKey : DefPath)
    (isMut : Bool) (vts : List CapturedVTable) (dts : List CapturedDynType)
    (entry : CapturedVTable)
    (hData : isPtrSizedWord (layoutPointerBytes layouts) dataVal = true)
    (hEnv : dynVTableEnv? .none mv (layoutPointerBytes layouts) = some (vts, dts))
    (hModeled : dynTypeModeled dts dynKey = true)
    (hVt : lookupVTableFor vts srcPointee dynKey = some entry) :
    evalThinToDynUnsize locals' mv decls layouts dataVal srcPointee dynKey false isMut =
      .ok (.aggregate 0 [dataVal,
        .ptr { allocId := entry.vtableAllocId, offsetBytes := 0 } (layoutPointerBytes layouts)]) ∧
    evalThinToDynUnsize locals' mv decls layouts dataVal srcPointee dynKey true isMut =
      (match dynRefDataValid locals' mv decls layouts (layoutPointerBytes layouts) dataVal entry
          isMut true with
       | true => .ok (.aggregate 0 [dataVal,
           .ptr { allocId := entry.vtableAllocId, offsetBytes := 0 } (layoutPointerBytes layouts)])
       | false => .ub) := by
  constructor
  · unfold evalThinToDynUnsize
    cases dataVal <;> simp only [isPtrSizedWord] at hData <;>
      first | exact absurd hData (by decide) | simp only [hData, hEnv, hModeled, hVt]
  · unfold evalThinToDynUnsize
    cases dataVal <;> simp only [isPtrSizedWord] at hData <;>
      first
      | exact absurd hData (by decide)
      | (simp only [hData, hEnv, hModeled, hVt]
         cases dynRefDataValid locals' mv decls layouts (layoutPointerBytes layouts) _ entry
           isMut true <;> rfl)

/-- **Universal (`C2`, MiniRust side): a raw `*const dyn Trait` is checked only
through its vtable metadata**. On every memory model, for EVERY data pointer
whose address fits in `usize` (null, dangling, unaligned), `check_ptr` of the
raw wide pointer `(dataThin, vtThin)` is `check_ptr` of the vtable pointer at
`PtrType::VTablePtr`: it passes when `vtThin` is a vtable of the trait, is UB
(`"invalid pointer for vtable lookup"`) when `vtThin` is not a registered
vtable, and is UB (`"Value::Ptr: invalid vtable in metadata"`) for a vtable of
another trait. -/
theorem dv_v1_raw_wide_ptr_checkPtrM_universal {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Gen.Machine M) (tr : Gen.TraitName)
    (dataThin vtThin : Gen.ThinPointer (Gen.Memory.Provenance M))
    (hAddr : inBounds dataThin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hVAddr : inBounds vtThin.addr .Unsigned x86_64.PTR_SIZE = true) :
    (∀ vt, vtableFromPtrM m vtThin = .ok vt → vt.trait_name = tr →
      checkPtrM (ThinPointer.widen dataThin (some (.VTablePointer vtThin)))
        (.Raw (.VTablePointer tr)) (some m) = .ok ()) ∧
    ((∀ e ∈ m.vtable_ptrs.entries, e.2 ≠ vtThin) →
      checkPtrM (ThinPointer.widen dataThin (some (.VTablePointer vtThin)))
        (.Raw (.VTablePointer tr)) (some m) =
        .error (.ub "invalid pointer for vtable lookup")) ∧
    (∀ vt, vtableFromPtrM m vtThin = .ok vt → vt.trait_name ≠ tr →
      checkPtrM (ThinPointer.widen dataThin (some (.VTablePointer vtThin)))
        (.Raw (.VTablePointer tr)) (some m) =
        .error (.ub "Value::Ptr: invalid vtable in metadata")) := by
  refine ⟨fun vt hvt hTr => ?_, fun hNot => ?_, fun vt hvt hTr => ?_⟩
  · rw [checkPtrM_rawTraitObject_eq_vtablePtr dataThin vtThin tr m hAddr]
    exact checkPtrM_vtablePtr_ok vtThin tr m vt hVAddr hvt hTr
  · rw [checkPtrM_rawTraitObject_eq_vtablePtr dataThin vtThin tr m hAddr]
    exact checkPtrM_vtablePtr_invalid_ptr_ub vtThin tr m hVAddr hNot
  · rw [checkPtrM_rawTraitObject_eq_vtablePtr dataThin vtThin tr m hAddr]
    exact checkPtrM_vtablePtr_wrong_trait_ub vtThin tr m vt hVAddr hvt hTr

/-- **Universal: the scalar (provenance-free) case of Trusted
`dynRefDataValid`**. For a data word that is an integer address, the reference
is valid exactly when the concrete type is inhabited and zero-sized, its
alignment is non-zero with `size + align - 1 < 2^63`, and the address (modulo
`2^64`) is non-null and aligned; Tree Borrows permissions (`checkTB`) and the
mutability (`isMut`) play no role. -/
theorem dv_dynRefDataValid_scalar_universal
    (locals : List LocalSlot) (mv : DynMemView) (decls : List MirAst.LocalDecl)
    (layouts : LayoutTable) (addr : Nat) (entry : CapturedVTable) (isMut checkTB : Bool) :
    dynRefDataValid locals mv decls layouts 8 (.scalar ⟨addr, 8⟩) entry isMut checkTB = true ↔
      (entry.isUninhabited = false ∧ entry.alignBytes ≠ 0 ∧
       entry.sizeBytes + (entry.alignBytes - 1) < 9223372036854775808 ∧
       wrapScalarBits addr (scalarModulus 8) ≠ 0 ∧
       wrapScalarBits addr (scalarModulus 8) % entry.alignBytes = 0 ∧
       entry.sizeBytes = 0) := by
  unfold dynRefDataValid
  simp only []
  split
  · rename_i hF
    simp only [Bool.false_eq_true, false_iff]
    intro ⟨hU, hA, hS, _, _, _⟩
    have hA' : Nat.beq entry.alignBytes 0 = false := by
      cases h : Nat.beq entry.alignBytes 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hA
    have hS' : Nat.blt (entry.sizeBytes + (entry.alignBytes - 1)) 9223372036854775808 = true :=
      Nat.ble_eq_true_of_le hS
    simp [hU, hA', hS'] at hF
  · rename_i hT
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hT
    obtain ⟨hU, hA, hS⟩ := hT
    have hA' : entry.alignBytes ≠ 0 := by
      intro h0; rw [h0] at hA; exact absurd hA (by decide)
    have hS' : entry.sizeBytes + (entry.alignBytes - 1) < 9223372036854775808 :=
      Nat.le_of_ble_eq_true hS
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    constructor
    · intro ⟨_, hNz, hMod, hZ⟩
      refine ⟨hU, hA', hS', ?_, Nat.eq_of_beq_eq_true hMod, Nat.eq_of_beq_eq_true hZ⟩
      intro h0; rw [h0] at hNz; exact absurd hNz (by decide)
    · intro ⟨_, _, _, hNz, hMod, hZ⟩
      refine ⟨by decide, ?_, ?_, ?_⟩
      · cases h : Nat.beq (wrapScalarBits addr (scalarModulus 8)) 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hNz
      · show Nat.beq (wrapScalarBits addr (scalarModulus 8) % entry.alignBytes) 0 = true
        rw [hMod]; rfl
      · rw [hZ]; rfl

/-- **Universal fault equivalence: unsizing a null address to a safe
`&dyn Trait` is UB on both authorities**, for every consistent vtable
environment, captured vtable, MiniRust machine, and memory model: Trusted
`evalThinToDynUnsize … isRef := true` on the null scalar address faults `.ub`,
and MiniRust `check_ptr` of the wide safe pointer faults
`"Value::Ptr: null safe pointer"`. -/
theorem dv_v1_null_ref_unsize_ub_universal_M {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Gen.Machine M) (tr : Gen.TraitName) (vt : Gen.VTable)
    (thin vptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject tr)
    (hVAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtrM m vptr = .ok vt) (hTrait : vt.trait_name = tr)
    (hSize : inBounds (vt.size.bytes : Int) .Signed x86_64.PTR_SIZE = true)
    (hNull : thin.addr = 0)
    (locals' : List LocalSlot) (mv : DynMemView) (decls : List MirAst.LocalDecl)
    (srcPointee : RigidTy) (dynKey : DefPath) (isMut : Bool)
    (vts : List CapturedVTable) (dts : List CapturedDynType) (entry : CapturedVTable)
    (hEnv : dynVTableEnv? .none mv (layoutPointerBytes emptyLayoutTable) = some (vts, dts))
    (hModeled : dynTypeModeled dts dynKey = true)
    (hVt : lookupVTableFor vts srcPointee dynKey = some entry) :
    evalThinToDynUnsize locals' mv decls emptyLayoutTable (.scalar ⟨0, 8⟩) srcPointee dynKey true
        isMut = .ub ∧
    checkPtrM (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      .error (.ub "Value::Ptr: null safe pointer") := by
  refine ⟨?_, checkPtrM_traitObject_null_ub thin vptr mk pointee tr m vt hMk hLayout hVAddr hvt
    hTrait hSize hNull⟩
  have h := (dv_v1_evalThinToDynUnsize_universal locals' mv decls emptyLayoutTable
    (.scalar ⟨0, 8⟩) srcPointee dynKey isMut vts dts entry rfl hEnv hModeled hVt).2
  rw [h]
  have hPb : layoutPointerBytes emptyLayoutTable = 8 := rfl
  rw [hPb]
  have hF : dynRefDataValid locals' mv decls emptyLayoutTable 8 (.scalar ⟨0, 8⟩) entry isMut
      true = false := by
    cases hv : dynRefDataValid locals' mv decls emptyLayoutTable 8 (.scalar ⟨0, 8⟩) entry isMut
      true with
    | false => rfl
    | true =>
      exact absurd (by decide : wrapScalarBits 0 (scalarModulus 8) = 0)
        ((dv_dynRefDataValid_scalar_universal locals' mv decls emptyLayoutTable 0 entry isMut
          true).mp hv).2.2.2.1
  rw [hF]

/-- **Universal fault equivalence: unsizing a misaligned address to a safe
`&dyn Trait` is UB on both authorities**. For every address `addr < 2^64` that
is not a multiple of the vtable's alignment, Trusted
`evalThinToDynUnsize … isRef := true` on the scalar address faults `.ub`, and
MiniRust `check_ptr` of the wide safe pointer at that address (non-null, with a
vtable of the same layout) faults `"Value::Ptr: unaligned safe pointer"`, on
every memory model. -/
theorem dv_v1_misaligned_ref_unsize_ub_universal_M {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Gen.Machine M) (tr : Gen.TraitName) (vt : Gen.VTable)
    (thin vptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject tr)
    (hVAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtrM m vptr = .ok vt) (hTrait : vt.trait_name = tr)
    (hSize : inBounds (vt.size.bytes : Int) .Signed x86_64.PTR_SIZE = true)
    (addr : Nat) (hAddrLt : addr < 18446744073709551616) (hThin : thin.addr = (addr : Int))
    (hNonNull : addr ≠ 0)
    (locals' : List LocalSlot) (mv : DynMemView) (decls : List MirAst.LocalDecl)
    (srcPointee : RigidTy) (dynKey : DefPath) (isMut : Bool)
    (vts : List CapturedVTable) (dts : List CapturedDynType) (entry : CapturedVTable)
    (hEnv : dynVTableEnv? .none mv (layoutPointerBytes emptyLayoutTable) = some (vts, dts))
    (hModeled : dynTypeModeled dts dynKey = true)
    (hVt : lookupVTableFor vts srcPointee dynKey = some entry)
    (hRel : DvVTableLayoutRel entry vt)
    (hMis : addr % entry.alignBytes ≠ 0) :
    evalThinToDynUnsize locals' mv decls emptyLayoutTable (.scalar ⟨addr, 8⟩) srcPointee dynKey
        true isMut = .ub ∧
    checkPtrM (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      .error (.ub "Value::Ptr: unaligned safe pointer") := by
  have hWrap : wrapScalarBits addr (scalarModulus 8) = addr := by
    unfold wrapScalarBits
    have hMod : scalarModulus 8 = 18446744073709551616 := by decide
    rw [hMod]
    have hBle : Nat.ble 18446744073709551616 addr = false := by
      cases h : Nat.ble 18446744073709551616 addr
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_le_of_lt hAddrLt)
    rw [hBle]
  constructor
  · have h := (dv_v1_evalThinToDynUnsize_universal locals' mv decls emptyLayoutTable
      (.scalar ⟨addr, 8⟩) srcPointee dynKey isMut vts dts entry rfl hEnv hModeled hVt).2
    rw [h]
    have hPb : layoutPointerBytes emptyLayoutTable = 8 := rfl
    rw [hPb]
    have hF : dynRefDataValid locals' mv decls emptyLayoutTable 8 (.scalar ⟨addr, 8⟩) entry
        isMut true = false := by
      cases hv : dynRefDataValid locals' mv decls emptyLayoutTable 8 (.scalar ⟨addr, 8⟩) entry
        isMut true with
      | false => rfl
      | true =>
        have hAl := ((dv_dynRefDataValid_scalar_universal locals' mv decls emptyLayoutTable addr
          entry isMut true).mp hv).2.2.2.2.1
        rw [hWrap] at hAl
        exact absurd hAl hMis
    rw [hF]
  · obtain ⟨_, hAlign⟩ := hRel
    have hAddrIn : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true := by
      rw [hThin]
      have hBits : (2 : Int) ^ Size.bits x86_64.PTR_SIZE = 18446744073709551616 := by decide
      unfold inBounds
      simp only [hBits, Bool.and_eq_true, decide_eq_true_eq]
      constructor <;> omega
    have hNN : (thin.addr != 0) = true := by
      rw [hThin]
      exact bne_iff_ne.mpr (Int.natCast_ne_zero.mpr hNonNull)
    have hUn : Align.is_aligned vt.align thin.addr = false := by
      unfold Align.is_aligned
      rw [hThin, hAlign]
      have hNe : ((addr : Int) % ((entry.alignBytes : Nat) : Int)) ≠ 0 := by
        rw [← Int.natCast_emod]
        exact Int.natCast_ne_zero.mpr hMis
      simp only [beq_eq_false_iff_ne, ne_eq]
      exact hNe
    exact checkPtrM_traitObject_unaligned_ub thin vptr mk pointee tr m vt hMk hLayout hAddrIn
      hVAddr hvt hTrait hSize hNN hUn

/-! ## §4 (`V3`): Virtual Method Dispatch (`evalVirtualCall` vs. `VTableMethodLookup`) -/

/-- A vtable slot lookup that does not yield a method slot: an out-of-bounds
index, or one of the non-method entries `MetadataDropInPlace`, `MetadataSize`,
`MetadataAlign`, `Vacant`, `TraitVPtr`. -/
def dvSlotIsNonMethod : Option CapturedVTableSlot → Bool
  | some (.method _ _) => false
  | some .unmodeledMethod => false
  | _ => true

/-- Whether the receiver of a virtual call passes the pre-dispatch validity
gate: raw receivers always do; safe (`&dyn`, `&mut dyn`, `Pin<&[mut] dyn>`)
receivers must satisfy `dynRefDataValid` with Tree Borrows checks at the
receiver's mutability. -/
def dvRecvOk (kind : DynReceiverKind) (locals' : List LocalSlot) (mem : MirSemantics.Memory)
    (decls : List MirAst.LocalDecl) (layouts : LayoutTable) (dataVal : Value)
    (entry : CapturedVTable) : Bool :=
  match kind with
  | .raw _ => true
  | .ref .mut => dynRefDataValid locals' (DynMemView.ofMemory mem) decls layouts
      (layoutPointerBytes layouts) dataVal entry true true
  | .ref .not => dynRefDataValid locals' (DynMemView.ofMemory mem) decls layouts
      (layoutPointerBytes layouts) dataVal entry false true
  | .pinRef .mut => dynRefDataValid locals' (DynMemView.ofMemory mem) decls layouts
      (layoutPointerBytes layouts) dataVal entry true true
  | .pinRef .not => dynRefDataValid locals' (DynMemView.ofMemory mem) decls layouts
      (layoutPointerBytes layouts) dataVal entry false true

/-- **Universal (`C3`): the slot and receiver gates of Trusted
`evalVirtualCall`**. For every state, receiver kind (`&dyn`, `&mut dyn`,
`*const dyn`, `*mut dyn`, `Pin<&[mut] dyn>`), and captured vtable `entry` that
`checkDynVTablePtr` resolves for the receiver's metadata word:
1. a non-method or out-of-bounds slot is UB;
2. a method slot with an invalid safe-reference receiver is UB, even when the
   callee is not linked (the reference gate precedes any external call);
3. a method slot with a valid receiver and an unlinked callee emits the
   external call of exactly the slot's concrete method `p`, with the receiver
   narrowed to the thin data pointer (`narrowDynReceiver`). -/
theorem dv_v3_evalVirtualCall_slot_universal
    (s : MachineState) (currentBody : Option CapturedMir) (vm : CapturedVirtualMethod)
    (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (recvOp : MirAst.Operand) (restOps : List MirAst.Operand)
    (recvVal : Value) (restVals : List Value) (locals' : List LocalSlot)
    (dest : MirAst.Place) (targetBbOpt : Option BasicBlockIdx) (unwind : MirAst.UnwindAction)
    (recvTy : MirAst.Ty) (kind : DynReceiverKind) (recvKey : DefPath)
    (dataVal metaVal : Value) (entry : CapturedVTable)
    (vts : List CapturedVTable) (dts : List CapturedDynType)
    (hTy : operandTy decls layouts recvOp = some recvTy)
    (hKind : classifyDynReceiver? recvTy.kind = some (kind, recvKey))
    (hCompat : dynKeysCompatible (collectMemoryDynTypes currentBody s.memory) recvKey vm.dynKey
      = true)
    (hUnpack : unpackDynReceiver? kind recvVal = .ok (dataVal, metaVal))
    (hChk : checkDynVTablePtr currentBody (DynMemView.ofMemory s.memory)
      (layoutPointerBytes layouts) metaVal recvKey = .ok (entry, vts, dts)) :
    (dvSlotIsNonMethod (get? entry.slots vm.slotIdx) = true →
      evalVirtualCall s currentBody vm decls layouts (recvOp :: restOps) (recvVal :: restVals)
        locals' dest targetBbOpt unwind = MirStepNode.fail .ub) ∧
    (∀ p args, get? entry.slots vm.slotIdx = some (.method p args) →
      dvRecvOk kind locals' s.memory decls layouts dataVal entry = false →
      evalVirtualCall s currentBody vm decls layouts (recvOp :: restOps) (recvVal :: restVals)
        locals' dest targetBbOpt unwind = MirStepNode.fail .ub) ∧
    (∀ p args bb, get? entry.slots vm.slotIdx = some (.method p args) →
      dvRecvOk kind locals' s.memory decls layouts dataVal entry = true →
      lookupCallee s.memory.callees layouts p args s.memory.traitImpls = none →
      targetBbOpt = some bb →
      evalVirtualCall s currentBody vm decls layouts (recvOp :: restOps) (recvVal :: restVals)
        locals' dest targetBbOpt unwind =
        MirStepNode.extCall
          { defPath := p, typeArgs := args, args := narrowDynReceiver kind dataVal :: restVals,
            memory := s.memory }
          (resumeExternalCall s locals' dest bb unwind)) := by
  refine ⟨fun hSlot => ?_, fun p args hSlot hOk => ?_, fun p args bb hSlot hOk hCallee hBb => ?_⟩
  · unfold evalVirtualCall
    simp only [hTy, hKind, hCompat, hUnpack, hChk]
    cases hG : get? entry.slots vm.slotIdx with
    | none => rfl
    | some slot =>
      rw [hG] at hSlot
      cases slot <;> first | rfl | exact Bool.noConfusion hSlot
  · unfold evalVirtualCall
    simp only [hTy, hKind, hCompat, hUnpack, hChk, hSlot]
    rcases kind with (m | m | m) <;> cases m <;>
      simp only [dvRecvOk] at hOk <;>
      first
      | exact absurd hOk (by decide)
      | simp only [hOk]
  · subst hBb
    unfold evalVirtualCall
    simp only [hTy, hKind, hCompat, hUnpack, hChk, hSlot, hCallee]
    rcases kind with (m | m | m) <;> cases m <;>
      simp only [dvRecvOk] at hOk <;>
      simp only [hOk]

/-- **Universal: MiniRust `VTableMethodLookup` on a resolved vtable** (every
memory model). When the vtable pointer resolves to `vt`
(`Machine::vtable_lookup`):
1. a method `meth` that `vt` implements by `fnName` resolves to the
   `Constant::FnPointer` value of `fnName` (the callee `Terminator::Call`
   enters);
2. a method that `vt` does not implement is a **`Stop.specPanic`**, not UB.
   This is the documented divergence from Trusted / Miri, which report UB for
   a non-method or out-of-bounds slot (`dv_v3_evalVirtualCall_slot_universal`,
   conjunct 1). -/
theorem dv_v3_vtableMethodLookup_universal_M {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Gen.Machine M) (vptr : Gen.ThinPointer (Gen.Memory.Provenance M)) (ty : Gen.PtrType)
    (meth : Gen.TraitMethodName) (vt : Gen.VTable)
    (hvt : vtableLookupM m vptr = .ok vt) :
    (∀ fnName, mapIndex vt.methods meth "vtable.methods[method]" = .ok fnName →
      evalUnOpM (.VTableMethodLookup meth) (.Ptr (ThinPointer.widen vptr none), .Ptr ty) (some m) =
        (do
          let fnPtr ← evalConstantM m (.FnPointer fnName)
          pure (fnPtr, .Ptr .FnPtr))) ∧
    (mapGet vt.methods meth = none →
      evalUnOpM (.VTableMethodLookup meth) (.Ptr (ThinPointer.widen vptr none), .Ptr ty) (some m) =
        .error (.specPanic "map index: missing key (vtable.methods[method])")) := by
  refine ⟨fun fnName hfn =>
    evalUnOpM_vtableMethodLookup_eq_fnPointer m vptr ty meth vt fnName hvt hfn, fun hNone => ?_⟩
  have h : evalUnOpM (.VTableMethodLookup meth) (.Ptr (ThinPointer.widen vptr none), .Ptr ty)
      (some m) =
      (do
        let vtable ← vtableLookupM m vptr
        let fnName ← mapIndex vtable.methods meth "vtable.methods[method]"
        let fnThin ← mapIndex m.fn_ptrs fnName "self.fn_ptrs[fn_name]"
        pure (.Ptr (ThinPointer.widen fnThin none), .Ptr .FnPtr)) := rfl
  have hIdx : mapIndex vt.methods meth "vtable.methods[method]" =
      .error (.specPanic "map index: missing key (vtable.methods[method])") := by
    unfold mapIndex
    rw [hNone]
    rfl
  rw [h, hvt, ok_bind, hIdx]
  rfl

/-- A Trusted `MirStepNode` classified for the witnesses of this section:
`0` = UB, `1` = unsupported, `2` = external call (with its `defPath`), `3` =
anything else. -/
def dvStepNodeClass : MirStepNode → Nat × String
  | .vis (.inl (.fail .ub)) _ => (0, "")
  | .vis (.inl (.fail .unsupported)) _ => (1, "")
  | .vis (.inr (.inr (.call req))) _ => (2, req.defPath)
  | _ => (3, "")

/-- Run `n` `stepMirFn` steps and classify the next step node (`dvStepNodeClass`). -/
def dvTrustedNodeAfter (body : CapturedMir) (n : Nat) (s : MachineState) : Nat × String :=
  match Nat.repeat (dvTrustedRunStep body) n (.running s) with
  | .running s' => dvStepNodeClass (stepMirFn body s')
  | .done _ => (3, "done")

/-- `fn(r: &dyn Tr) -> u32 { r.get(<uninit>) }`: a virtual call whose trailing
argument operand `_3` is uninitialized (`kani#5172`); local `_2 : u32` is the
receiver's pointee. -/
def dvV3UninitArgCallMir : CapturedMir :=
  dvMkBody "dv::v3_uninit_arg_call"
    [dvDecl dvU32Ty, dvDecl (dvRefDynTy dvTrKey), dvDecl dvU32Ty, dvDecl dvU32Ty] 1
    [dvBb [] (.call (dvFnConst "dv::Tr::get" [.dynamic dvTrKey]) [.move (dvLoc 1), .copy (dvLoc 3)]
        (dvLoc 0) (some 1) .continue_),
     dvBb [] .return_]

/-- **V3 Trusted dispatch witnesses (`C3`, `stepMirFn`)**:
1. the non-method header slot `1` (`MetadataSize`) and the out-of-bounds slot
   `9` are UB (Miri: "dyn call trying to call something that is not a method");
2. with the concrete method body not linked, a valid receiver steps to the
   external call of exactly the vtable's slot-`3` method
   `dv::<u32 as Tr>::get`;
3. `kani#5172` / pre-`extCall` gates: with the callee still not linked, an
   uninitialized trailing argument is UB, and a receiver whose pointee local is
   dead (a dangling `&dyn`) is UB, before any external call;
4. a forged receiver vtable (metadata that is not a vtable allocation) is UB. -/
theorem dv_v3_trusted_dispatch_gates_witness :
    dvRunTrusted dvV3CallHdrMir dvTrustedFuel (dvInitLive dvV3CallHdrMir [.scalar ⟨7, 4⟩] dvCallees)
      = .ub ∧
    dvRunTrusted dvV3CallOobMir dvTrustedFuel (dvInitLive dvV3CallOobMir [.scalar ⟨7, 4⟩] dvCallees)
      = .ub ∧
    dvTrustedNodeAfter dvV3CallU32Mir 2 (dvInitLive dvV3CallU32Mir [.scalar ⟨7, 4⟩])
      = (2, "dv::<u32 as Tr>::get") ∧
    dvTrustedNodeAfter dvV3UninitArgCallMir 0
      ({ dvPointeeInit dvV3UninitArgCallMir 16384 .frozen (.init (.scalar ⟨7, 4⟩)) with
         memory := { (dvPointeeInit dvV3UninitArgCallMir 16384 .frozen
           (.init (.scalar ⟨7, 4⟩))).memory with callees := [dvV3UninitArgCallMir] } })
      = (0, "") ∧
    dvTrustedNodeAfter dvV3ArgCallMir 0
      ({ dvPointeeInit dvV3ArgCallMir 16384 .frozen .dead with
         memory := { (dvPointeeInit dvV3ArgCallMir 16384 .frozen .dead).memory with
           callees := [dvV3ArgCallMir] } })
      = (0, "") ∧
    dvTrustedNodeAfter dvV3ArgCallMir 0
      ({ dvPointeeInit dvV3ArgCallMir 16384 .frozen (.init (.scalar ⟨7, 4⟩)) with
         memory := { (dvPointeeInit dvV3ArgCallMir 16384 .frozen
           (.init (.scalar ⟨7, 4⟩))).memory with callees := [dvV3ArgCallMir] } })
      = (2, "dv::<u32 as Tr>::get") ∧
    dvRunTrusted dvV3ArgCallMir dvTrustedFuel
      (dvPointeeInit dvV3ArgCallMir 0 .frozen (.init (.scalar ⟨7, 4⟩))) = .ub :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- A caller that looks up the method `meth` in the vtable of the `&dyn Tr`
receiver in local `1` and calls it with no arguments. -/
def dvMrV3LookupCaller (meth : Gen.TraitMethodName) : Gen.Function :=
  mkMrFn [(localName 0, u32MrTy), (localName 1, dvRefDynMrTy 0)] [] (localName 0)
    [(bbName 0, ⟨[], .Call (.UnOp (.VTableMethodLookup meth)
          (.UnOp .GetMetadata (.Load (.Local (localName 1)))))
        .Rust [] (.Local (localName 0)) (some (bbName 1)) none, .Regular⟩),
     (bbName 1, ⟨[], .Return, .Regular⟩)]

/-- Machine for `dvMrV3LookupCaller meth` on the valid `(u32, Tr)` receiver. -/
def dvMrV3LookupMach (meth : Gen.TraitMethodName) : Mach :=
  dvMrMach (dvMrV3LookupCaller meth)
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 256 (dvDataBytes 12 ++ dvVtBytes 0) 8, mkHeapAlloc 640 (scalarBytes u32 7) 4]
    [(localName 0, dvLocPtr 0), (localName 1, dvLocPtr 1)]

/-- **Documented divergence (`PROTOTYPE_REPORT.md` §5.1): a non-method slot is
`Stop.specPanic` in MiniRust and UB in Trusted**. Looking up a method the
vtable does not implement (`⟨⟨7⟩⟩`) is a specification panic on `Mach` and
`MachTB`, while the Trusted virtual call through the non-method slot `1`
(`dvV3CallHdrMir`) and through the out-of-bounds slot `9` (`dvV3CallOobMir`)
faults `.ub`. -/
theorem dv_v3_nonMethod_slot_ub_vs_minirust_specPanic :
    interpSpecPanicMsg (Interp.steps 1 (dvMrV3LookupMach ⟨⟨7⟩⟩)) =
      some "map index: missing key (vtable.methods[method])" ∧
    interpSpecPanicMsg (Interp.stepsTB 1 (liftMachToTB (dvMrV3LookupMach ⟨⟨7⟩⟩))) =
      some "map index: missing key (vtable.methods[method])" ∧
    dvRunTrusted dvV3CallHdrMir dvTrustedFuel (dvInitLive dvV3CallHdrMir [.scalar ⟨7, 4⟩] dvCallees)
      = .ub ∧
    dvRunTrusted dvV3CallOobMir dvTrustedFuel (dvInitLive dvV3CallOobMir [.scalar ⟨7, 4⟩] dvCallees)
      = .ub :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Decidable frame view of a running Trusted state after `n` steps: the
call-stack depth, the active protectors, and the frame locals that hold thin
pointers (as `(local, allocId)`). -/
def dvTrustedFrameView (body : CapturedMir) (n : Nat) (s : MachineState) :
    Option (Nat × List Nat × List (Nat × Nat)) :=
  match Nat.repeat (dvTrustedRunStep body) n (.running s) with
  | .running s' =>
    some (s'.memory.callStack.length, s'.memory.activeProtectors,
      (List.range s'.frame.locals.length).filterMap (fun i =>
        match (s'.frame.locals[i]? : Option LocalSlot) with
        | some (LocalSlot.init (Value.ptr p _)) => some (i, p.allocId)
        | _ => none))
  | .done _ => none

/-- Decidable view of the Tree Borrows table of a running Trusted state after
`n` steps, as `(tag, permission code, parent tag, protector)` with permission
codes `0 = Active`, `1 = Frozen`, `2 = Disabled`, `3 = Reserved`, `4 = other`. -/
def dvTrustedBorrowView (body : CapturedMir) (n : Nat) (s : MachineState) :
    List (Nat × Nat × Option Nat × Option Nat) :=
  match Nat.repeat (dvTrustedRunStep body) n (.running s) with
  | .running s' =>
    s'.memory.borrows.map (fun b =>
      (b.tag,
       (match b.perm with
        | .active => 0 | .frozen => 1 | .disabled => 2 | .reserved => 3 | _ => 4),
       b.parentTag, b.protector))
  | .done _ => []

/-- **V3 Crubit `c16` bridge (`protectDynReceiverOnEntry`, `C4`)**: the corpus
mode key runs the `poke` body from `dvV3ProtectedInit`. This theorem ties that
state to the real virtual call:
1. stepping the full caller `dvV3PokeCallerMir`
   (`m = &mut x; p = &raw mut *m; r = &*m as &dyn Tr; r.poke(p)`) for 5 steps
   enters the callee frame (depth `1`) with the receiver `_1` narrowed to the
   fresh tag `3` and the alias `_2` carrying the `&mut` tag `1`, where
   `protectDynReceiverOnEntry` has installed the `Frozen` child tag `3` under
   the shared reborrow `2` with the active call protector `1`;
2. `dvV3ProtectedInit true` has exactly the same pointer locals, active
   protectors, and borrow table (tags, permissions, parents, protectors), and
   `dvV3ProtectedInit false` differs only in carrying no protector;
3. the full call then faults `.ub` (the aliased write `*p = 99` is a foreign
   write to the protected `Frozen` receiver tag), as does the corpus state in
   `protectedTB` mode, while the unprotected corpus state returns `77`. -/
theorem dv_v3_c16_callee_entry_matches_corpus_state :
    dvTrustedFrameView dvV3PokeCallerMir 5
        (dvInitLive dvV3PokeCallerMir [.scalar ⟨7, 4⟩] dvCallees) =
      some (1, [1], [(1, 3), (2, 1)]) ∧
    dvTrustedBorrowView dvV3PokeCallerMir 5
        (dvInitLive dvV3PokeCallerMir [.scalar ⟨7, 4⟩] dvCallees) =
      [(3, 1, some 2, some 1), (2, 1, some 1, none), (1, 3, none, none)] ∧
    dvTrustedFrameView dvV3ProtectedPokeMir 0 (dvV3ProtectedInit true) =
      some (0, [1], [(1, 3), (2, 1)]) ∧
    dvTrustedBorrowView dvV3ProtectedPokeMir 0 (dvV3ProtectedInit true) =
      [(3, 1, some 2, some 1), (2, 1, some 1, none), (1, 3, none, none)] ∧
    dvTrustedFrameView dvV3ProtectedPokeMir 0 (dvV3ProtectedInit false) =
      some (0, [], [(1, 3), (2, 1)]) ∧
    dvTrustedBorrowView dvV3ProtectedPokeMir 0 (dvV3ProtectedInit false) =
      [(3, 1, some 2, none), (2, 1, some 1, none), (1, 3, none, none)] ∧
    dvRunTrusted dvV3PokeCallerMir dvTrustedFuel
        (dvInitLive dvV3PokeCallerMir [.scalar ⟨7, 4⟩] dvCallees) = .ub ∧
    dvRunTrusted dvV3ProtectedPokeMir dvTrustedFuel (dvV3ProtectedInit true) = .ub ∧
    dvRunTrusted dvV3ProtectedPokeMir dvTrustedFuel (dvV3ProtectedInit false) = .u32Val 77 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel⟩

/-- **V3 three-way witness (`Trusted`, `Mach`, `MachTB`)**: virtual `Tr::get`
on the two concrete receiver layouts (`u32`: `7 ^ 5 = 2`; `u64`: `64 | 5 = 69`),
a wrong-trait receiver vtable (UB on all three), and the Crubit `c16` aliased
write through the full dynamic dispatch: `Mach` returns `77` and stores `99`
through the alias, `MachTB` completes the call and the function-entry
`Validate` (preserving `MachTB.wfLive`) and faults at the aliased write with the
receiver-protector error, and Trusted faults `.ub`. -/
theorem dv_v3_virtualDispatch_three_way_witness :
    dvTrustedObserve false .virtualDispatchAndProtector .okPrimary = .u32Val 2 ∧
    (∃ m4, Interp.steps 4 (dvMrV3Mach 0 (scalarBytes u32 7) 4) = .ok m4 ∧
      m4.mem.memory.allocations[10]?.map (·.data) = some (scalarBytes u32 2)) ∧
    (∃ m4, Interp.stepsTB 4 (liftMachToTB (dvMrV3Mach 0 (scalarBytes u32 7) 4)) = .ok m4 ∧
      MachTB.wfLive m4 ∧
      m4.mem.memory.mem.allocations[10]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes u32 2).map (projByteTB ∘ liftByteTB))) ∧
    dvTrustedObserve false .virtualDispatchAndProtector .okSecondary = .u32Val 69 ∧
    (∃ m4, Interp.steps 4 (dvMrV3Mach 1 (scalarBytes dvU64It 64) 8) = .ok m4 ∧
      m4.mem.memory.allocations[10]?.map (·.data) = some (scalarBytes u32 69)) ∧
    (∃ m4, Interp.stepsTB 4 (liftMachToTB (dvMrV3Mach 1 (scalarBytes dvU64It 64) 8)) = .ok m4 ∧
      MachTB.wfLive m4 ∧
      m4.mem.memory.mem.allocations[10]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes u32 69).map (projByteTB ∘ liftByteTB))) ∧
    dvTrustedObserve false .virtualDispatchAndProtector .ubFault = .ub ∧
    Interp.steps 1 (dvMrV3Mach 2 (scalarBytes u32 7) 4) =
      .error (.ub "Value::Ptr: invalid vtable in metadata") ∧
    Interp.stepsTB 1 (liftMachToTB (dvMrV3Mach 2 (scalarBytes u32 7) 4)) =
      .error (.ub "Value::Ptr: invalid vtable in metadata") ∧
    (∃ m5, Interp.steps 5 dvMrV3PokeMach = .ok m5 ∧
      ([10, 13].map (fun i => m5.mem.memory.allocations[i]?.map (·.data))) =
        [some (scalarBytes u32 77), some (scalarBytes u32 99)]) ∧
    (∃ m2, Interp.stepsTB 2 (liftMachToTB dvMrV3PokeMach) = .ok m2 ∧ MachTB.wfLive m2) ∧
    Interp.stepsTB 3 (liftMachToTB dvMrV3PokeMach) =
      .error (.ub "Tree Borrows: foreign write of protected Frozen reference which had a local read") ∧
    dvTrustedObserve true .virtualDispatchAndProtector .modeCase = .ub ∧
    dvTrustedObserve false .virtualDispatchAndProtector .modeCase = .u32Val 77 :=
  ⟨by decide +kernel,
   ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
   by decide +kernel,
   ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
   by decide +kernel,
   eq_error_ub_of_interpUbMsg (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel),
   ok_of_map_toOption (by decide +kernel),
   (ok_stepsTB_wfLive (f := fun _ => ()) (b := ()) (by decide +kernel)).imp
     (fun _ h => ⟨h.1, h.2.1⟩),
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   by decide +kernel, by decide +kernel⟩

/-! ## §5. Three-Way Witnesses (`Trusted`, `Mach`, `MachTB`), Fail-Closed Boundaries, and Realizability of the Universal Laws -/

/-- `Mach` runs `n` steps of `Interp.steps` normally, and frame allocation `idx`
then holds exactly the bytes `bs`. -/
abbrev DvMachRet (n : Nat) (m : Mach) (bs : List Byte) (idx : Nat := 10) : Prop :=
  ∃ m', Interp.steps n m = .ok m' ∧ m'.mem.memory.allocations[idx]?.map (·.data) = some bs

/-- `MachTB` (`liftMachToTB m`) runs `n` steps of `Interp.stepsTB` normally,
preserving `MachTB.wfLive`, and frame allocation `idx` then holds exactly the
bytes `bs` (compared through `projByteTB`). -/
abbrev DvMachTBRet (n : Nat) (m : Mach) (bs : List Byte) (idx : Nat := 10) : Prop :=
  ∃ m', Interp.stepsTB n (liftMachToTB m) = .ok m' ∧ MachTB.wfLive m' ∧
    m'.mem.memory.mem.allocations[idx]?.map (fun a => a.data.map projByteTB) =
      some (bs.map (projByteTB ∘ liftByteTB))

/-- Both MiniRust memory models return `bs` in allocation `idx` after `n` steps. -/
abbrev DvBothRet (n : Nat) (m : Mach) (bs : List Byte) (idx : Nat := 10) : Prop :=
  DvMachRet n m bs idx ∧ DvMachTBRet n m bs idx

/-- Both MiniRust memory models fault with UB message `msg` within `n` steps. -/
abbrev DvBothUb (n : Nat) (m : Mach) (msg : String) : Prop :=
  Interp.steps n m = .error (.ub msg) ∧ Interp.stepsTB n (liftMachToTB m) = .error (.ub msg)

theorem dvBothRet_intro {n : Nat} {m : Mach} {bs : List Byte} {idx : Nat}
    (hBM : (Interp.steps n m).toOption.map
      (fun m' => m'.mem.memory.allocations[idx]?.map (·.data)) = some (some bs))
    (hTB : (Interp.stepsTB n (liftMachToTB m)).toOption.map
      (fun m' => m'.mem.memory.mem.allocations[idx]?.map (fun a => a.data.map projByteTB)) =
        some (some (bs.map (projByteTB ∘ liftByteTB)))) :
    DvBothRet n m bs idx :=
  ⟨ok_of_map_toOption hBM, ok_stepsTB_wfLive hTB⟩

theorem dvBothUb_intro {n : Nat} {m : Mach} {msg : String}
    (hBM : interpUbMsg (Interp.steps n m) = some msg)
    (hTB : interpUbMsg (Interp.stepsTB n (liftMachToTB m)) = some msg) :
    DvBothUb n m msg :=
  ⟨eq_error_ub_of_interpUbMsg hBM, eq_error_ub_of_interpUbMsg hTB⟩

/-- The raw `Value` returned by the `stepMirFn` step taken after `n` steps. -/
def dvTrustedReturnAfter? (body : CapturedMir) (n : Nat) (s : MachineState) : Option Value :=
  match Nat.repeat (dvTrustedRunStep body) n (.running s) with
  | .running s' =>
    match stepMirFn body s' with
    | .ret (.normal r) => some r.1
    | _ => none
  | .done _ => none

/-- Observe a wide pointer whose data word is an integer address:
`(address, vtableAllocId)`. -/
def dvTrustedScalarWideObs : Value → Option (Nat × Nat)
  | .aggregate 0 [.scalar ⟨addr, 8⟩, .ptr vt 8] => some (addr, vt.allocId)
  | _ => none

/-- Observe a one-field transparent wrapper (`Pin<P>`) around a wide pointer. -/
def dvTrustedPinObs : Value → DynVtTrustedObs
  | .aggregate 0 [inner] => dvTrustedValueObs inner
  | _ => .stuck

/-- `Tr`'s trait-object descriptor (`CapturedDynType`) with the given
`charon#1640` / outlives flags. -/
def dvTrDynType (unresolvedBinder : Bool) (outlivesOk : Bool) : CapturedDynType :=
  { dynKey := dvTrKey, predicateKey := dvTrKey, principalTrait? := some dvTrKey,
    hasUnresolvedExistentialBinder := unresolvedBinder, supertraitOutlivesOk := outlivesOk }

/-- `dvV1RefUnsizeMir` with an explicit trait-object descriptor table. -/
def dvV1DynTypeMir (d : CapturedDynType) : CapturedMir :=
  { dvV1RefUnsizeMir with dynTypes := [d] }

/-- A thin pointer argument into the untracked allocation `5`. -/
@[reducible] def dvArgPtr (off : Nat := 0) : Value := .ptr { allocId := 5, offsetBytes := off } 8

/-- **V1 three-way witness (`Trusted`, `Mach`, `MachTB`; `C1`, `C2`)**:
1. `&u32 -> &dyn Tr` returns the wide pointer `(data, (u32, Tr) vtable)`;
2. raw-vs-reference: the dangling, misaligned pointer unsizes to
   `*const dyn Tr` on all three interpreters, and the same pointer as `&u32` is
   UB on all three (`"Value::Ptr: unaligned safe pointer"`);
3. `&mut u64 -> &mut dyn Tr` returns `(data, (u64, Tr) vtable)`;
4. a null address is UB as a reference (`"Value::Ptr: null safe pointer"`) and
   accepted as a raw pointer;
5. an aligned, non-null address without provenance is UB as a reference to the
   4-byte `u32` (`"Value::Ptr: non-dereferenceable safe pointer"`). -/
theorem dv_v1_thinUnsize_three_way_witness :
    dvTrustedObserve false .thinUnsize .okPrimary = .widePtr 1 0 16384 ∧
    DvBothRet 2 (dvMrV1Mach (dvRefDynMrTy 0) 0 (dvDataBytes 13) (scalarBytes u32 7) 4)
      (dvDataBytes 13 ++ dvVtBytes 0) ∧
    dvTrustedObserve false .thinUnsize .okSecondary = .widePtr 5 1 16384 ∧
    DvBothRet 2 (dvMrV1Mach (dvRawDynMrTy 0) 0 dvDanglingBytes (scalarBytes u32 7) 4)
      (dvDanglingBytes ++ dvVtBytes 0) ∧
    dvTrustedObserve false .thinUnsize .ubFault = .ub ∧
    DvBothUb 2 (dvMrV1Mach (dvRefDynMrTy 0) 0 dvDanglingBytes (scalarBytes u32 7) 4)
      "Value::Ptr: unaligned safe pointer" ∧
    dvTrustedObserve false .thinUnsize .modeCase = .widePtr 1 0 16385 ∧
    DvBothRet 2 (dvMrV1Mach (dvMutDynMrTy 0) 1 (dvDataBytes 13) (scalarBytes dvU64It 64) 8)
      (dvDataBytes 13 ++ dvVtBytes 1) ∧
    dvRunTrusted dvV1RefArgUnsizeMir dvTrustedFuel
      (dvInitLive dvV1RefArgUnsizeMir [.scalar ⟨0, 8⟩]) = .ub ∧
    DvBothUb 2 (dvMrV1Mach (dvRefDynMrTy 0) 0 (ptrBytes 0 none) (scalarBytes u32 7) 4)
      "Value::Ptr: null safe pointer" ∧
    (dvTrustedReturnAfter? dvV1RawUnsizeMir 1
      (dvInitLive dvV1RawUnsizeMir [.scalar ⟨0, 8⟩])).bind dvTrustedScalarWideObs
        = some (0, 16384) ∧
    DvBothRet 2 (dvMrV1Mach (dvRawDynMrTy 0) 0 (ptrBytes 0 none) (scalarBytes u32 7) 4)
      (ptrBytes 0 none ++ dvVtBytes 0) ∧
    dvRunTrusted dvV1RefArgUnsizeMir dvTrustedFuel
      (dvInitLive dvV1RefArgUnsizeMir [.scalar ⟨644, 8⟩]) = .ub ∧
    DvBothUb 2 (dvMrV1Mach (dvRefDynMrTy 0) 0 (ptrBytes 644 none) (scalarBytes u32 7) 4)
      "Value::Ptr: non-dereferenceable safe pointer" :=
  ⟨by decide +kernel, dvBothRet_intro (by decide +kernel) (by decide +kernel),
   by decide +kernel, dvBothRet_intro (by decide +kernel) (by decide +kernel),
   by decide +kernel, dvBothUb_intro (by decide +kernel) (by decide +kernel),
   by decide +kernel, dvBothRet_intro (by decide +kernel) (by decide +kernel),
   by decide +kernel, dvBothUb_intro (by decide +kernel) (by decide +kernel),
   by decide +kernel, dvBothRet_intro (by decide +kernel) (by decide +kernel),
   by decide +kernel, dvBothUb_intro (by decide +kernel) (by decide +kernel)⟩

/-- **V1 fail-closed boundary of the Trusted model (`C1`)**: every unsizing
coercion outside `&T` / `&mut T` / `*const T` / `*mut T` / `Pin<&[mut] T>` to
`dyn Trait` is `.unsupported`, never a wrong value and never `.ub`:
1. `Box<T> -> Box<dyn K>` and `&Wrapper<T> -> &Wrapper<dyn K>`, universally
   (`evalUnsizeCoercion_box_dyn_unsupported`,
   `evalUnsizeCoercion_ref_adt_unsupported`), and on the `stepMirFn` fixtures;
2. `Pin<*const T> -> Pin<&dyn Tr>` and `Pin<*const T> -> Pin<*const dyn Tr>`;
3. `Pin<&mut u32> -> Pin<&mut dyn Tr>` is modeled and returns the wrapped wide
   pointer;
4. `charon#1640`: a trait-object descriptor that retains an unresolved
   existential binder, or whose supertrait outlives obligation was not
   discharged, fails closed, while the same descriptor without those flags
   unsizes normally. -/
theorem dv_v1_failClosed_boundary_witness :
    (∀ (locals : List LocalSlot) (op : MirAst.Operand) (k : DefPath) (lIdx : LayoutIdx)
        (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable),
      evalUnsizeCoercion locals op
        { kind := .adt "alloc::boxed::Box" [.dynamic k, .adt "alloc::alloc::Global" []],
          layoutIdx := lIdx } mem decls layouts = .unsupported) ∧
    (∀ (locals : List LocalSlot) (op : MirAst.Operand) (m : MirAst.Mutability) (p : DefPath)
        (args : List RigidTy) (lIdx : LayoutIdx) (mem : MirSemantics.Memory)
        (decls : List MirAst.LocalDecl) (layouts : LayoutTable),
      evalUnsizeCoercion locals op { kind := .ref m (.adt p args), layoutIdx := lIdx } mem decls
        layouts = .unsupported) ∧
    dvRunTrusted (dvV1ArgUnsizeMir (dvBoxTy (.uint .u32)) (dvBoxTy (.dynamic dvTrKey)))
      dvTrustedFuel
      (dvInitLive (dvV1ArgUnsizeMir (dvBoxTy (.uint .u32)) (dvBoxTy (.dynamic dvTrKey)))
        [dvArgPtr]) = .unsupported ∧
    dvRunTrusted
      (dvV1ArgUnsizeMir { kind := .ref .not (.adt "dv::Wrapper" [.uint .u32]), layoutIdx := 0 }
        { kind := .ref .not (.adt "dv::Wrapper" [.dynamic dvTrKey]), layoutIdx := 0 })
      dvTrustedFuel
      (dvInitLive
        (dvV1ArgUnsizeMir { kind := .ref .not (.adt "dv::Wrapper" [.uint .u32]), layoutIdx := 0 }
          { kind := .ref .not (.adt "dv::Wrapper" [.dynamic dvTrKey]), layoutIdx := 0 })
        [dvArgPtr]) = .unsupported ∧
    dvRunTrusted
      (dvV1ArgUnsizeMir (dvPinTy (.rawPtr .not (.uint .u32)))
        (dvPinTy (.ref .not (.dynamic dvTrKey))))
      dvTrustedFuel
      (dvInitLive
        (dvV1ArgUnsizeMir (dvPinTy (.rawPtr .not (.uint .u32)))
          (dvPinTy (.ref .not (.dynamic dvTrKey))))
        [.aggregate 0 [dvArgPtr]]) = .unsupported ∧
    dvRunTrusted
      (dvV1ArgUnsizeMir (dvPinTy (.rawPtr .not (.uint .u32)))
        (dvPinTy (.rawPtr .not (.dynamic dvTrKey))))
      dvTrustedFuel
      (dvInitLive
        (dvV1ArgUnsizeMir (dvPinTy (.rawPtr .not (.uint .u32)))
          (dvPinTy (.rawPtr .not (.dynamic dvTrKey))))
        [.aggregate 0 [dvArgPtr]]) = .unsupported ∧
    (dvTrustedReturnAfter? dvV1PinUnsizeMir 3
      (dvInitLive dvV1PinUnsizeMir [.scalar ⟨7, 4⟩])).map dvTrustedPinObs
        = some (.widePtr 1 0 16384) ∧
    dvRunTrusted (dvV1DynTypeMir (dvTrDynType true true)) dvTrustedFuel
      (dvInitLive (dvV1DynTypeMir (dvTrDynType true true)) [.scalar ⟨7, 4⟩]) = .unsupported ∧
    dvRunTrusted (dvV1DynTypeMir (dvTrDynType false false)) dvTrustedFuel
      (dvInitLive (dvV1DynTypeMir (dvTrDynType false false)) [.scalar ⟨7, 4⟩]) = .unsupported ∧
    dvRunTrusted (dvV1DynTypeMir (dvTrDynType false true)) dvTrustedFuel
      (dvInitLive (dvV1DynTypeMir (dvTrDynType false true)) [.scalar ⟨7, 4⟩])
        = .widePtr 1 0 16384 :=
  ⟨fun locals op k lIdx mem decls layouts =>
     evalUnsizeCoercion_box_dyn_unsupported locals op k lIdx mem decls layouts,
   fun locals op m p args lIdx mem decls layouts =>
     evalUnsizeCoercion_ref_adt_unsupported locals op m p args lIdx mem decls layouts,
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **V2 `resolveUpcastVTable?` on the frozen supertrait diamond (`C2`)**: from
the `(u32, Sub)` vtable, the primary supertrait `Super`, the secondary supertrait
`Side` (behind a `TraitVPtr` slot), the diamond top `Base`, and `Sub` itself
resolve to their own vtables; the unrelated `Alt`, the sibling direction
`Side -> Super`, and the downcast `Super -> Sub` are rejected. Every corpus
vtable is `wfVTableEntry` on the 64-bit target. -/
theorem dv_v2_resolveUpcastVTable_diamond_witness :
    ((dvVTables[3]?).bind fun e => resolveUpcastVTable? dvVTables [] e dvSuperKey).map
      (·.vtableAllocId) = some 16388 ∧
    ((dvVTables[3]?).bind fun e => resolveUpcastVTable? dvVTables [] e dvSideKey).map
      (·.vtableAllocId) = some 16389 ∧
    ((dvVTables[3]?).bind fun e => resolveUpcastVTable? dvVTables [] e dvBaseKey).map
      (·.vtableAllocId) = some 16390 ∧
    ((dvVTables[3]?).bind fun e => resolveUpcastVTable? dvVTables [] e dvSubKey).map
      (·.vtableAllocId) = some 16387 ∧
    ((dvVTables[3]?).bind fun e => resolveUpcastVTable? dvVTables [] e dvAltKey).map
      (·.vtableAllocId) = none ∧
    ((dvVTables[5]?).bind fun e => resolveUpcastVTable? dvVTables [] e dvSuperKey).map
      (·.vtableAllocId) = none ∧
    ((dvVTables[4]?).bind fun e => resolveUpcastVTable? dvVTables [] e dvSubKey).map
      (·.vtableAllocId) = none ∧
    dvVTables.all (wfVTableEntry 8) = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **V2 three-way witness (`Trusted`, `Mach`, `MachTB`; `C2`)**:
1. `&dyn Sub -> &dyn Super` (primary) and `-> &dyn Side` (secondary) keep the
   data pointer and install the target vtable; so does the diamond top
   `-> &dyn Base`; the NOP `&dyn Sub -> &dyn Sub` keeps the `(u32, Sub)` vtable;
2. the ill-typed `&dyn Sub -> &dyn Alt` fails closed in Trusted;
3. a NOP coercion validates the vtable trait: a `&dyn Tr` (and a raw
   `*const dyn Tr`) whose metadata is the `(u32, Alt)` vtable is UB on all
   three (`"Value::Ptr: invalid vtable in metadata"`), and raw metadata that is
   not a vtable is UB on all three (`"invalid pointer for vtable lookup"`);
4. a NOP on a dangling `*const dyn Tr` with a valid vtable is accepted on all
   three, while a `&dyn Tr` to a dead local is UB in Trusted. -/
theorem dv_v2_upcast_and_nop_three_way_witness :
    dvTrustedObserve false .dynUpcastAndNop .okPrimary = .widePtr 1 0 16388 ∧
    DvBothRet 2 (dvMrV2UpcastMach 3 4) (dvDataBytes 13 ++ dvVtBytes 4) ∧
    dvTrustedObserve false .dynUpcastAndNop .okSecondary = .widePtr 1 0 16389 ∧
    DvBothRet 2 (dvMrV2UpcastMach 4 5) (dvDataBytes 13 ++ dvVtBytes 5) ∧
    dvRunTrusted dvV2UpcastBaseMir dvTrustedFuel (dvInitLive dvV2UpcastBaseMir [.scalar ⟨7, 4⟩])
      = .widePtr 1 0 16390 ∧
    DvBothRet 2 (dvMrV2UpcastMach 5 6) (dvDataBytes 13 ++ dvVtBytes 6) ∧
    dvRunTrusted (dvV2UpcastMir dvSubKey) dvTrustedFuel
      (dvInitLive (dvV2UpcastMir dvSubKey) [.scalar ⟨7, 4⟩]) = .widePtr 1 0 16387 ∧
    dvRunTrusted dvV2UpcastAltMir dvTrustedFuel (dvInitLive dvV2UpcastAltMir [.scalar ⟨7, 4⟩])
      = .unsupported ∧
    dvTrustedObserve false .dynUpcastAndNop .ubFault = .ub ∧
    DvBothUb 1 (dvMrV2NopMach (dvRefDynMrTy 0) (dvDataBytes 12 ++ dvVtBytes 2))
      "Value::Ptr: invalid vtable in metadata" ∧
    dvRunTrusted dvV2NopRawMir dvTrustedFuel
      (dvInitLive dvV2NopRawMir [dvWide dvDanglingPtr 16386]) = .ub ∧
    DvBothUb 1 (dvMrV2NopMach (dvRawDynMrTy 0) (dvDanglingBytes ++ dvVtBytes 2))
      "Value::Ptr: invalid vtable in metadata" ∧
    dvRunTrusted dvV2NopRawMir dvTrustedFuel
      (dvInitLive dvV2NopRawMir [dvWide dvDanglingPtr 0]) = .ub ∧
    DvBothUb 1 (dvMrV2NopMach (dvRawDynMrTy 0) (dvDanglingBytes ++ ptrBytes 640 none))
      "invalid pointer for vtable lookup" ∧
    dvTrustedObserve false .dynUpcastAndNop .modeCase = .widePtr 5 1 16384 ∧
    DvBothRet 1 (dvMrV2NopMach (dvRawDynMrTy 0) (dvDanglingBytes ++ dvVtBytes 0))
      (dvDanglingBytes ++ dvVtBytes 0) ∧
    dvRunTrusted dvV2NopRefMir dvTrustedFuel
      (dvPointeeInit dvV2NopRefMir 16384 .frozen (.init (.scalar ⟨7, 4⟩))) = .widePtr 1 0 16384 ∧
    DvBothRet 1 (dvMrV2NopMach (dvRefDynMrTy 0) (dvDataBytes 12 ++ dvVtBytes 0))
      (dvDataBytes 12 ++ dvVtBytes 0) ∧
    dvRunTrusted dvV2NopRefMir dvTrustedFuel (dvPointeeInit dvV2NopRefMir 16384 .frozen .dead)
      = .ub :=
  ⟨by decide +kernel, dvBothRet_intro (by decide +kernel) (by decide +kernel),
   by decide +kernel, dvBothRet_intro (by decide +kernel) (by decide +kernel),
   by decide +kernel, dvBothRet_intro (by decide +kernel) (by decide +kernel),
   by decide +kernel, by decide +kernel,
   by decide +kernel, dvBothUb_intro (by decide +kernel) (by decide +kernel),
   by decide +kernel, dvBothUb_intro (by decide +kernel) (by decide +kernel),
   by decide +kernel, dvBothUb_intro (by decide +kernel) (by decide +kernel),
   by decide +kernel, dvBothRet_intro (by decide +kernel) (by decide +kernel),
   by decide +kernel, dvBothRet_intro (by decide +kernel) (by decide +kernel),
   by decide +kernel⟩

/-- The read of the pointee through the (disabled) `&u32` local `2`, appended
to `dvMrV4SizeFn` as the Tree Borrows control. -/
def dvMrV4ReadTail : List Gen.Statement :=
  [.Assign (.Local (localName 4)) (.Load (.Deref (.Load (.Local (localName 2))) u32MrTy))]

/-- **V4 dynamic layout three-way witness (`Trusted`, `Mach`, `MachTB`; `C5`)**:
1. `size_of_val` / `align_of_val` on a `&dyn Tr` whose Tree Borrows tag is
   `Disabled` return the vtable's `4` / `4` on all three: they read only the
   vtable header and perform no memory access through the data pointer;
2. the tag really is disabled: reading the pointee through it afterwards is
   accepted by `Mach` and is UB on `MachTB`
   (`"Tree Borrows: local read of Disabled reference"`);
3. the pointer must still be a valid reference: a dead pointee is UB on all
   three (`"Value::Ptr: non-dereferenceable safe pointer"`), and a misaligned
   data pointer or a wrong-trait vtable is UB in Trusted; the live control
   returns `4`;
4. the raw `core::intrinsics::{size_of_val, align_of_val}` on `*const dyn Tr`
   return `8` / `8` for the `u64` receiver and `4` / `4` for `u32`. -/
theorem dv_v4_dynLayout_three_way_witness :
    dvTrustedObserve false .dynLayoutRawBorrowAndAddrEq .okPrimary = .usizeVal 4 ∧
    DvBothRet 5 (dvMrV4SizeMach true) (scalarBytes IntType.usize_ty 4) ∧
    dvRunTrusted dvV4AlignSafeMir dvTrustedFuel
      (dvPointeeInit dvV4AlignSafeMir 16384 .disabled (.init (.scalar ⟨7, 4⟩))) = .usizeVal 4 ∧
    DvBothRet 5 (dvMrV4SizeMach false) (scalarBytes IntType.usize_ty 4) ∧
    DvMachRet 6 (dvMrV4SizeMach true dvMrV4ReadTail) (scalarBytes u32 9) 14 ∧
    Interp.stepsTB 6 (liftMachToTB (dvMrV4SizeMach true dvMrV4ReadTail)) =
      .error (.ub "Tree Borrows: local read of Disabled reference") ∧
    dvTrustedObserve false .dynLayoutRawBorrowAndAddrEq .ubFault = .ub ∧
    DvBothUb 1 (dvMrV4ArgSizeMach false) "Value::Ptr: non-dereferenceable safe pointer" ∧
    dvRunTrusted dvV4SizeSafeMir dvTrustedFuel
      (dvPointeeInit dvV4SizeSafeMir 16384 .frozen (.init (.scalar ⟨7, 4⟩))) = .usizeVal 4 ∧
    DvBothRet 1 (dvMrV4ArgSizeMach true) (scalarBytes IntType.usize_ty 4) ∧
    dvRunTrusted dvV4AlignSafeMir dvTrustedFuel
      (dvPointeeInit dvV4AlignSafeMir 16384 .frozen .dead) = .ub ∧
    dvRunTrusted dvV4SizeSafeMir dvTrustedFuel
      (dvPointeeInit dvV4SizeSafeMir 16384 .frozen (.init (.scalar ⟨7, 4⟩)) 1) = .ub ∧
    dvRunTrusted dvV4SizeSafeMir dvTrustedFuel
      (dvPointeeInit dvV4SizeSafeMir 16386 .frozen (.init (.scalar ⟨7, 4⟩))) = .ub ∧
    dvRunTrusted (dvV4IntrLayoutMir dvU64Ty dvRefU64Ty "core::intrinsics::size_of_val")
      dvTrustedFuel
      (dvInitLive (dvV4IntrLayoutMir dvU64Ty dvRefU64Ty "core::intrinsics::size_of_val")
        [.scalar ⟨64, 8⟩]) = .usizeVal 8 ∧
    dvRunTrusted (dvV4IntrLayoutMir dvU64Ty dvRefU64Ty "core::intrinsics::align_of_val")
      dvTrustedFuel
      (dvInitLive (dvV4IntrLayoutMir dvU64Ty dvRefU64Ty "core::intrinsics::align_of_val")
        [.scalar ⟨64, 8⟩]) = .usizeVal 8 ∧
    dvRunTrusted (dvV4IntrLayoutMir dvU32Ty dvRefU32Ty "core::intrinsics::size_of_val")
      dvTrustedFuel
      (dvInitLive (dvV4IntrLayoutMir dvU32Ty dvRefU32Ty "core::intrinsics::size_of_val")
        [.scalar ⟨7, 4⟩]) = .usizeVal 4 ∧
    dvRunTrusted (dvV4IntrLayoutMir dvU32Ty dvRefU32Ty "core::intrinsics::align_of_val")
      dvTrustedFuel
      (dvInitLive (dvV4IntrLayoutMir dvU32Ty dvRefU32Ty "core::intrinsics::align_of_val")
        [.scalar ⟨7, 4⟩]) = .usizeVal 4 :=
  ⟨by decide +kernel, dvBothRet_intro (by decide +kernel) (by decide +kernel),
   by decide +kernel, dvBothRet_intro (by decide +kernel) (by decide +kernel),
   ok_of_map_toOption (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel),
   by decide +kernel, dvBothUb_intro (by decide +kernel) (by decide +kernel),
   by decide +kernel, dvBothRet_intro (by decide +kernel) (by decide +kernel),
   by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **V4 raw borrow of a `dyn` place, Trusted `stepMirFn` (`C6`)**:
`&raw const (*r)` on a `&dyn Tr` preserves `(data, vtable)` without a Tree
Borrows access (a `Disabled` tag is accepted) but requires the place to be
live (a dead pointee is UB) and the vtable to be of the place's trait (UB);
through a raw `*const dyn Tr` not even liveness is required; `&raw mut (*r)`
through a shared `&dyn Tr` is ill-typed and fails closed, and through a
`&mut dyn Tr` it preserves the wide pointer. -/
theorem dv_v4_rawBorrow_trusted_witness :
    dvRunTrusted (dvV4RawBorrowMir .not (dvRefDynTy dvTrKey) (dvRawConstDynTy dvTrKey))
      dvTrustedFuel
      (dvPointeeInit (dvV4RawBorrowMir .not (dvRefDynTy dvTrKey) (dvRawConstDynTy dvTrKey))
        16384 .disabled (.init (.scalar ⟨7, 4⟩))) = .widePtr 1 0 16384 ∧
    dvRunTrusted (dvV4RawBorrowMir .not (dvRefDynTy dvTrKey) (dvRawConstDynTy dvTrKey))
      dvTrustedFuel
      (dvPointeeInit (dvV4RawBorrowMir .not (dvRefDynTy dvTrKey) (dvRawConstDynTy dvTrKey))
        16384 .frozen .dead) = .ub ∧
    dvRunTrusted (dvV4RawBorrowMir .not (dvRefDynTy dvTrKey) (dvRawConstDynTy dvTrKey))
      dvTrustedFuel
      (dvPointeeInit (dvV4RawBorrowMir .not (dvRefDynTy dvTrKey) (dvRawConstDynTy dvTrKey))
        16386 .frozen (.init (.scalar ⟨7, 4⟩))) = .ub ∧
    dvRunTrusted (dvV4RawBorrowMir .not (dvRawConstDynTy dvTrKey) (dvRawConstDynTy dvTrKey))
      dvTrustedFuel
      (dvPointeeInit (dvV4RawBorrowMir .not (dvRawConstDynTy dvTrKey) (dvRawConstDynTy dvTrKey))
        16384 .frozen .dead) = .widePtr 1 0 16384 ∧
    dvRunTrusted (dvV4RawBorrowMir .mut (dvRefDynTy dvTrKey) (dvRawMutDynTy dvTrKey))
      dvTrustedFuel
      (dvPointeeInit (dvV4RawBorrowMir .mut (dvRefDynTy dvTrKey) (dvRawMutDynTy dvTrKey))
        16384 .frozen (.init (.scalar ⟨7, 4⟩))) = .unsupported ∧
    dvRunTrusted (dvV4RawBorrowMir .mut (dvRefMutDynTy dvTrKey) (dvRawMutDynTy dvTrKey))
      dvTrustedFuel
      (dvPointeeInit (dvV4RawBorrowMir .mut (dvRefMutDynTy dvTrKey) (dvRawMutDynTy dvTrKey))
        16384 .active (.init (.scalar ⟨7, 4⟩))) = .widePtr 1 0 16384 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel⟩

/-- **V4 wide-pointer comparison and `core::ptr::addr_eq` three-way witness
(`Trusted`, `Mach`, `MachTB`; `C6`, `rust#166144`)**:
1. `addr_eq` of a `*const dyn Tr` and a `*const dyn Alt` to the same address is
   `true` although the vtables differ, and `false` for different addresses;
2. wide `==` of two `*const dyn Tr` to the same address compares the vtable
   pointers too: `false` for the `(u32, Tr)` and `(u64, Tr)` vtables, `true` for
   equal vtables (and `!=` is the negation);
3. wide `<` is lexicographic on `(data address, vtable address)`. -/
theorem dv_v4_wideCmp_addrEq_three_way_witness :
    dvTrustedObserve false .dynLayoutRawBorrowAndAddrEq .okSecondary = .boolVal 1 ∧
    DvBothRet 1 (dvMrV4CmpMach true 0 1 0 2) [.Init 1 none] ∧
    dvRunTrusted dvV4AddrEqMir dvTrustedFuel
      (dvInitLive dvV4AddrEqMir [dvWide dvArgPtr 16384, dvWide (dvArgPtr 1) 16386]) = .boolVal 0 ∧
    dvRunTrusted dvV4AddrEqMir dvTrustedFuel
      (dvInitLive dvV4AddrEqMir
        [dvWide (.scalar ⟨640, 8⟩) 16384, dvWide (.scalar ⟨640, 8⟩) 16386]) = .boolVal 1 ∧
    dvRunTrusted dvV4AddrEqMir dvTrustedFuel
      (dvInitLive dvV4AddrEqMir
        [dvWide (.scalar ⟨640, 8⟩) 16384, dvWide (.scalar ⟨644, 8⟩) 16386]) = .boolVal 0 ∧
    dvTrustedObserve false .dynLayoutRawBorrowAndAddrEq .modeCase = .boolVal 0 ∧
    DvBothRet 1 (dvMrV4CmpMach false 0 0 0 1) [.Init 0 none] ∧
    dvRunTrusted dvV4WideEqMir dvTrustedFuel
      (dvInitLive dvV4WideEqMir [dvWide dvArgPtr 16384, dvWide dvArgPtr 16384]) = .boolVal 1 ∧
    DvBothRet 1 (dvMrV4CmpMach false 0 0 0 0) [.Init 1 none] ∧
    dvRunTrusted (dvV4WideCmpMir .ne) dvTrustedFuel
      (dvInitLive (dvV4WideCmpMir .ne) [dvWide dvArgPtr 16384, dvWide dvArgPtr 16385])
        = .boolVal 1 ∧
    dvRunTrusted (dvV4WideCmpMir .lt) dvTrustedFuel
      (dvInitLive (dvV4WideCmpMir .lt) [dvWide dvArgPtr 16384, dvWide dvArgPtr 16385])
        = .boolVal 1 ∧
    dvRunTrusted (dvV4WideCmpMir .lt) dvTrustedFuel
      (dvInitLive (dvV4WideCmpMir .lt) [dvWide dvArgPtr 16385, dvWide dvArgPtr 16384])
        = .boolVal 0 ∧
    dvRunTrusted (dvV4WideCmpMir .lt) dvTrustedFuel
      (dvInitLive (dvV4WideCmpMir .lt) [dvWide dvArgPtr 16385, dvWide (dvArgPtr 1) 16384])
        = .boolVal 1 :=
  ⟨by decide +kernel, dvBothRet_intro (by decide +kernel) (by decide +kernel),
   by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, dvBothRet_intro (by decide +kernel) (by decide +kernel),
   by decide +kernel, dvBothRet_intro (by decide +kernel) (by decide +kernel),
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ### Realizability of the universal laws on `Mach` and `MachTB` -/

/-- The `.ok` payload of a Trusted `DynCheck`. -/
def dvDynCheckOk? {α : Type} : DynCheck α → Option α
  | .ok a => some a
  | _ => none

/-- Outcome code of a Trusted `DynCheck`: `0 = ok`, `1 = ub`, `2 = unsupported`. -/
def dvDynCheckCode {α : Type} : DynCheck α → Nat
  | .ok _ => 0
  | .ub => 1
  | .unsupported => 2

theorem dvDynCheck_ok_of_map {α β : Type} {r : DynCheck α} {f : α → β} {b : β}
    (h : (dvDynCheckOk? r).map f = some b) : ∃ a, r = .ok a ∧ f a = b := by
  cases r with
  | ok a => exact ⟨a, rfl, Option.some.inj h⟩
  | ub => cases h
  | unsupported => cases h

theorem dvDynCheck_eq_ub_of_code {α : Type} {r : DynCheck α} (h : dvDynCheckCode r = 1) :
    r = .ub := by
  cases r with
  | ok a => cases h
  | ub => rfl
  | unsupported => cases h

theorem dvDynCheck_eq_unsupported_of_code {α : Type} {r : DynCheck α}
    (h : dvDynCheckCode r = 2) : r = .unsupported := by
  cases r with
  | ok a => cases h
  | ub => cases h
  | unsupported => rfl

theorem dv_some_of_map {α β : Type} {o : Option α} {f : α → β} {b : β}
    (h : o.map f = some b) : ∃ a, o = some a ∧ f a = b := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, Option.some.inj h⟩

/-- Metadata word of the `(u32, Tr)` vtable (allocation `16384`). -/
@[reducible] def dvMetaTr : Value := .ptr { allocId := 16384, offsetBytes := 0 } 8
/-- Data word of the corpus receiver: borrow tag `1`. -/
@[reducible] def dvDataTag1 : Value := .ptr { allocId := 1, offsetBytes := 0 } 8
/-- The Trusted state of the `size_of_val` corpus key (`dvVTables` registered). -/
@[reducible] def dvNvState : MachineState :=
  dvTrustedInit false .dynLayoutRawBorrowAndAddrEq .okPrimary

/-- **Realizability of `dv_wfVTableEntry_minirust_valid_layout`**: its
hypotheses hold for all 7 corpus vtable pairs, so each MiniRust corpus vtable
satisfies the `check_ptr` layout preconditions. -/
theorem dv_wfVTableEntry_minirust_valid_layout_nonvacuous :
    ∀ i, i < 7 →
      inBounds ((dvMrVTable i).size.bytes : Int) .Signed x86_64.PTR_SIZE = true ∧
      (dvMrVTable i).align.bytes ≠ 0 ∧
      (dvMrVTable i).size.bytes % (dvMrVTable i).align.bytes = 0 := by
  intro i hi
  have hAll : ∀ cv, lookupVTableById dvVTables i = some cv → wfVTableEntry 8 cv = true := by
    intro cv hcv
    match i, hi, hcv with
    | 0, _, hcv => cases hcv; decide +kernel
    | 1, _, hcv => cases hcv; decide +kernel
    | 2, _, hcv => cases hcv; decide +kernel
    | 3, _, hcv => cases hcv; decide +kernel
    | 4, _, hcv => cases hcv; decide +kernel
    | 5, _, hcv => cases hcv; decide +kernel
    | 6, _, hcv => cases hcv; decide +kernel
  obtain ⟨cv, hcv, hRel⟩ := dvVTables_layoutRel i hi
  exact dv_wfVTableEntry_minirust_valid_layout cv (dvMrVTable i) (hAll cv hcv) hRel

/-- **Realizability of `dv_dynSizeAlignOfVal_agrees_computeSizeAlign_M` (`Mach`
& `MachTB`)**: all of its hypotheses hold jointly for the Trusted corpus state
of `size_of_val` (whose `checkDynVTablePtr` resolves the `(u32, Tr)` vtable)
and the MiniRust corpus machine on BOTH memory models (`M = BM` and `M = TBM`
with `MachTB.wfLive`), where the law yields size `4` and alignment `4` on both
authorities. -/
theorem dv_dynSizeAlignOfVal_agrees_computeSizeAlign_M_nonvacuous
    (locals' : List LocalSlot) (dest : Place) (bb : BasicBlockIdx) (opTy : Gen.Type) :
    evalDynSizeAlignOfVal dvNvState emptyLayoutTable locals' dest bb
        (.aggregate 0 [dvDataTag1, dvMetaTr]) dvTrKey true =
      writeIntrinsicReturn dvNvState locals' dest bb (.scalar ⟨4, 8⟩) ∧
    evalDynSizeAlignOfVal dvNvState emptyLayoutTable locals' dest bb
        (.aggregate 0 [dvDataTag1, dvMetaTr]) dvTrKey false =
      writeIntrinsicReturn dvNvState locals' dest bb (.scalar ⟨4, 8⟩) ∧
    evalUnOpM (.ComputeSize (.TraitObject (traitNameOf 0)))
        (.Ptr (ThinPointer.widen (dvVtPtr 0) none), opTy) (some (dvMrV4ArgSizeMach true)) =
      .ok (.Int 4, .Int IntType.usize_ty) ∧
    evalUnOpM (.ComputeAlign (.TraitObject (traitNameOf 0)))
        (.Ptr (ThinPointer.widen (dvVtPtr 0) none), opTy) (some (dvMrV4ArgSizeMach true)) =
      .ok (.Int 4, .Int IntType.usize_ty) ∧
    MachTB.wfLive (liftMachToTB (dvMrV4ArgSizeMach true)) ∧
    evalUnOpM (.ComputeSize (.TraitObject (traitNameOf 0)))
        (.Ptr (ThinPointer.widen (liftThinPtrTB (dvVtPtr 0)) none), opTy)
        (some (liftMachToTB (dvMrV4ArgSizeMach true))) =
      .ok (.Int 4, .Int IntType.usize_ty) ∧
    evalUnOpM (.ComputeAlign (.TraitObject (traitNameOf 0)))
        (.Ptr (ThinPointer.widen (liftThinPtrTB (dvVtPtr 0)) none), opTy)
        (some (liftMachToTB (dvMrV4ArgSizeMach true))) =
      .ok (.Int 4, .Int IntType.usize_ty) := by
  obtain ⟨⟨entry, vts, dts⟩, hChk, hProj⟩ := dvDynCheck_ok_of_map
    (r := checkDynVTablePtr .none (DynMemView.ofMemory dvNvState.memory)
      (layoutPointerBytes emptyLayoutTable) dvMetaTr dvTrKey)
    (f := fun a => (a.1.sizeBytes, a.1.alignBytes)) (b := (4, 4)) (by decide +kernel)
  have hSz : entry.sizeBytes = 4 := congrArg Prod.fst hProj
  have hAl : entry.alignBytes = 4 := congrArg Prod.snd hProj
  have hRel : DvVTableLayoutRel entry (dvMrVTable 0) := by
    unfold DvVTableLayoutRel
    rw [hSz, hAl]
    exact ⟨rfl, rfl⟩
  have hBM := dv_dynSizeAlignOfVal_agrees_computeSizeAlign_M (M := BM) (dvMrV4ArgSizeMach true)
    (traitNameOf 0) (dvMrVTable 0) ⟨⟨0⟩⟩ (dvVtPtr 0) (dvVtPtr 0)
    (by first | rfl | decide +kernel) (by first | rfl | decide +kernel)
    (by first | rfl | decide +kernel) (by first | rfl | decide +kernel)
    dvNvState emptyLayoutTable locals' dest bb dvDataTag1 dvMetaTr dvTrKey entry vts dts rfl hChk
    hRel opTy
  have hTB := dv_dynSizeAlignOfVal_agrees_computeSizeAlign_M (M := TBM)
    (liftMachToTB (dvMrV4ArgSizeMach true))
    (traitNameOf 0) (dvMrVTable 0) ⟨⟨0⟩⟩ (liftThinPtrTB (dvVtPtr 0)) (liftThinPtrTB (dvVtPtr 0))
    (by first | rfl | decide +kernel) (by first | rfl | decide +kernel)
    (by first | rfl | decide +kernel) (by first | rfl | decide +kernel)
    dvNvState emptyLayoutTable locals' dest bb dvDataTag1 dvMetaTr dvTrKey entry vts dts rfl hChk
    hRel opTy
  rw [hSz, hAl] at hBM hTB
  exact ⟨hBM.1, hBM.2.1, hBM.2.2.1, hBM.2.2.2, liftMachToTB_wfLive _, hTB.2.2.1, hTB.2.2.2⟩

/-- **Realizability of `dv_dynSizeAlignOfVal_fault_universal`**: both premises
are realized on the corpus state. A wrong-trait vtable (`(u32, Alt)` for
`dyn Tr`) and a null vtable allocation make `checkDynVTablePtr` UB, and an
allocation that is not provably a non-vtable (`99999`) makes it fail closed;
dynamic `size_of_val` / `align_of_val` then fault `.ub`, respectively fail
closed, for every destination. -/
theorem dv_dynSizeAlignOfVal_fault_universal_nonvacuous
    (locals' : List LocalSlot) (dest : Place) (bb : BasicBlockIdx) (isSize : Bool) :
    evalDynSizeAlignOfVal dvNvState emptyLayoutTable locals' dest bb
        (.aggregate 0 [dvDataTag1, .ptr { allocId := 16386, offsetBytes := 0 } 8]) dvTrKey isSize =
      MirStepNode.fail .ub ∧
    evalDynSizeAlignOfVal dvNvState emptyLayoutTable locals' dest bb
        (.aggregate 0 [dvDataTag1, .ptr { allocId := 0, offsetBytes := 0 } 8]) dvTrKey isSize =
      MirStepNode.fail .ub ∧
    evalDynSizeAlignOfVal dvNvState emptyLayoutTable locals' dest bb
        (.aggregate 0 [dvDataTag1, .ptr { allocId := 99999, offsetBytes := 0 } 8]) dvTrKey isSize =
      MirStepNode.unsupported :=
  ⟨(dv_dynSizeAlignOfVal_fault_universal dvNvState emptyLayoutTable locals' dest bb dvDataTag1
      (.ptr { allocId := 16386, offsetBytes := 0 } 8) dvTrKey isSize rfl).1
      (dvDynCheck_eq_ub_of_code (by decide +kernel)),
   (dv_dynSizeAlignOfVal_fault_universal dvNvState emptyLayoutTable locals' dest bb dvDataTag1
      (.ptr { allocId := 0, offsetBytes := 0 } 8) dvTrKey isSize rfl).1
      (dvDynCheck_eq_ub_of_code (by decide +kernel)),
   (dv_dynSizeAlignOfVal_fault_universal dvNvState emptyLayoutTable locals' dest bb dvDataTag1
      (.ptr { allocId := 99999, offsetBytes := 0 } 8) dvTrKey isSize rfl).2
      (dvDynCheck_eq_unsupported_of_code (by decide +kernel))⟩

/-- **Realizability of `dv_v1_evalThinToDynUnsize_universal`**: on the corpus
state the vtable environment is consistent, `dyn Tr` is modeled, and the
`(u32, Tr)` vtable is captured, so the raw path returns `(dataVal, 16384)` for
EVERY pointer-shaped data word, in particular the dangling `dvDanglingPtr` and
the null address. -/
theorem dv_v1_evalThinToDynUnsize_universal_nonvacuous
    (locals' : List LocalSlot) (decls : List MirAst.LocalDecl) (dataVal : Value) (isMut : Bool)
    (hData : isPtrSizedWord (layoutPointerBytes emptyLayoutTable) dataVal = true) :
    evalThinToDynUnsize locals' (DynMemView.ofMemory dvNvState.memory) decls emptyLayoutTable
        dataVal (.uint .u32) dvTrKey false isMut =
      .ok (.aggregate 0 [dataVal, dvMetaTr]) ∧
    isPtrSizedWord (layoutPointerBytes emptyLayoutTable) dvDanglingPtr = true ∧
    isPtrSizedWord (layoutPointerBytes emptyLayoutTable) (.scalar ⟨0, 8⟩) = true := by
  obtain ⟨⟨vts, dts⟩, hEnv, hProj⟩ := dv_some_of_map
    (o := dynVTableEnv? .none (DynMemView.ofMemory dvNvState.memory)
      (layoutPointerBytes emptyLayoutTable))
    (f := fun a => (dynTypeModeled a.2 dvTrKey,
      (lookupVTableFor a.1 (.uint .u32) dvTrKey).map (·.vtableAllocId)))
    (b := (true, some 16384)) (by decide +kernel)
  have hModeled : dynTypeModeled dts dvTrKey = true := congrArg Prod.fst hProj
  obtain ⟨entry, hVt, hId⟩ := dv_some_of_map (congrArg Prod.snd hProj)
  have h := (dv_v1_evalThinToDynUnsize_universal locals' (DynMemView.ofMemory dvNvState.memory)
    decls emptyLayoutTable dataVal (.uint .u32) dvTrKey isMut vts dts entry hData hEnv hModeled
    hVt).1
  rw [hId] at h
  exact ⟨h, rfl, rfl⟩

/-- A thin pointer that is not a registered vtable (address `640`, no
provenance). -/
@[reducible] def dvNotVtPtr : Ptr := { addr := 640, provenance := none }
/-- The dangling, misaligned thin data pointer (address `641`, no provenance). -/
@[reducible] def dvDanglingThin : Ptr := { addr := 641, provenance := none }

/-- **Realizability of `dv_v1_raw_wide_ptr_checkPtrM_universal` (`Mach` &
`MachTB`)**: each of its three premises is realized on BOTH memory models with
the dangling data pointer `641`: the `(u32, Tr)` vtable passes at `dyn Tr`, the
unregistered pointer `640` is `"invalid pointer for vtable lookup"`, and the
`(u32, Alt)` vtable is `"Value::Ptr: invalid vtable in metadata"`. -/
theorem dv_v1_raw_wide_ptr_checkPtrM_universal_nonvacuous :
    checkPtrM (ThinPointer.widen dvDanglingThin (some (.VTablePointer (dvVtPtr 0))))
      (.Raw (.VTablePointer (traitNameOf 0))) (some (dvMrV4ArgSizeMach true)) = .ok () ∧
    checkPtrM (ThinPointer.widen dvDanglingThin (some (.VTablePointer dvNotVtPtr)))
      (.Raw (.VTablePointer (traitNameOf 0))) (some (dvMrV4ArgSizeMach true)) =
        .error (.ub "invalid pointer for vtable lookup") ∧
    checkPtrM (ThinPointer.widen dvDanglingThin (some (.VTablePointer (dvVtPtr 2))))
      (.Raw (.VTablePointer (traitNameOf 0))) (some (dvMrV4ArgSizeMach true)) =
        .error (.ub "Value::Ptr: invalid vtable in metadata") ∧
    MachTB.wfLive (liftMachToTB (dvMrV4ArgSizeMach true)) ∧
    checkPtrM (ThinPointer.widen (liftThinPtrTB dvDanglingThin)
        (some (.VTablePointer (liftThinPtrTB (dvVtPtr 0)))))
      (.Raw (.VTablePointer (traitNameOf 0))) (some (liftMachToTB (dvMrV4ArgSizeMach true))) =
        .ok () ∧
    checkPtrM (ThinPointer.widen (liftThinPtrTB dvDanglingThin)
        (some (.VTablePointer (liftThinPtrTB dvNotVtPtr))))
      (.Raw (.VTablePointer (traitNameOf 0))) (some (liftMachToTB (dvMrV4ArgSizeMach true))) =
        .error (.ub "invalid pointer for vtable lookup") ∧
    checkPtrM (ThinPointer.widen (liftThinPtrTB dvDanglingThin)
        (some (.VTablePointer (liftThinPtrTB (dvVtPtr 2)))))
      (.Raw (.VTablePointer (traitNameOf 0))) (some (liftMachToTB (dvMrV4ArgSizeMach true))) =
        .error (.ub "Value::Ptr: invalid vtable in metadata") :=
  have hBM := fun (vtThin : Ptr) (h : inBounds vtThin.addr .Unsigned x86_64.PTR_SIZE = true) =>
    dv_v1_raw_wide_ptr_checkPtrM_universal (M := BM) (dvMrV4ArgSizeMach true) (traitNameOf 0)
      dvDanglingThin vtThin (by decide +kernel) h
  have hTB := fun (vtThin : Ptr)
      (h : inBounds (liftThinPtrTB vtThin).addr .Unsigned x86_64.PTR_SIZE = true) =>
    dv_v1_raw_wide_ptr_checkPtrM_universal (M := TBM) (liftMachToTB (dvMrV4ArgSizeMach true))
      (traitNameOf 0) (liftThinPtrTB dvDanglingThin) (liftThinPtrTB vtThin) (by decide +kernel) h
  ⟨(hBM (dvVtPtr 0) (by decide +kernel)).1 (dvMrVTable 0) (by first | rfl | decide +kernel)
      (by first | rfl | decide +kernel),
   (hBM dvNotVtPtr (by decide +kernel)).2.1 (by decide +kernel),
   (hBM (dvVtPtr 2) (by decide +kernel)).2.2 (dvMrVTable 2) (by first | rfl | decide +kernel)
      (by decide +kernel),
   liftMachToTB_wfLive _,
   (hTB (dvVtPtr 0) (by decide +kernel)).1 (dvMrVTable 0) (by first | rfl | decide +kernel)
      (by first | rfl | decide +kernel),
   (hTB dvNotVtPtr (by decide +kernel)).2.1 (by decide +kernel),
   (hTB (dvVtPtr 2) (by decide +kernel)).2.2 (dvMrVTable 2) (by first | rfl | decide +kernel)
      (by decide +kernel)⟩

/-- A zero-sized, 4-aligned concrete type's `Tr` vtable (not part of the corpus
table), realizing the `true` side of `dv_dynRefDataValid_scalar_universal`. -/
def dvZstVTable : CapturedVTable :=
  { vtableId := 0, vtableAllocId := 16384, concreteTy := .tuple [], dynKey := dvTrKey,
    sizeBytes := 0, alignBytes := 4, slots := [.dropInPlace none, .size, .align] }

/-- **Both sides of `dv_dynRefDataValid_scalar_universal` are realized**: an
integer address is a valid `&dyn Tr` data word for a zero-sized concrete type
exactly when it is non-null and aligned (`644` valid; `0` and `641` invalid),
and never for the 4-byte `(u32, Tr)` corpus vtable. -/
theorem dv_dynRefDataValid_scalar_universal_nonvacuous
    (locals : List LocalSlot) (mv : DynMemView) (decls : List MirAst.LocalDecl)
    (layouts : LayoutTable) (isMut checkTB : Bool) :
    dynRefDataValid locals mv decls layouts 8 (.scalar ⟨644, 8⟩) dvZstVTable isMut checkTB = true ∧
    dynRefDataValid locals mv decls layouts 8 (.scalar ⟨0, 8⟩) dvZstVTable isMut checkTB = false ∧
    dynRefDataValid locals mv decls layouts 8 (.scalar ⟨641, 8⟩) dvZstVTable isMut checkTB
      = false ∧
    (∀ cv, dvVTables[0]? = some cv →
      dynRefDataValid locals mv decls layouts 8 (.scalar ⟨644, 8⟩) cv isMut checkTB = false) := by
  have hF : ∀ (addr : Nat) (cv : CapturedVTable),
      ¬ (cv.isUninhabited = false ∧ cv.alignBytes ≠ 0 ∧
         cv.sizeBytes + (cv.alignBytes - 1) < 9223372036854775808 ∧
         wrapScalarBits addr (scalarModulus 8) ≠ 0 ∧
         wrapScalarBits addr (scalarModulus 8) % cv.alignBytes = 0 ∧ cv.sizeBytes = 0) →
      dynRefDataValid locals mv decls layouts 8 (.scalar ⟨addr, 8⟩) cv isMut checkTB = false := by
    intro addr cv hNot
    cases hv : dynRefDataValid locals mv decls layouts 8 (.scalar ⟨addr, 8⟩) cv isMut checkTB with
    | false => rfl
    | true =>
      exact absurd ((dv_dynRefDataValid_scalar_universal locals mv decls layouts addr cv isMut
        checkTB).mp hv) hNot
  refine ⟨(dv_dynRefDataValid_scalar_universal locals mv decls layouts 644 dvZstVTable isMut
      checkTB).mpr (by decide +kernel), hF 0 dvZstVTable (by decide +kernel),
    hF 641 dvZstVTable (by decide +kernel), ?_⟩
  intro cv hcv
  cases hcv
  exact hF 644 _ (by decide +kernel)

/-- The MiniRust `&dyn Tr` pointee descriptor of the corpus. -/
@[reducible] def dvDynPointee : Gen.PointeeInfo :=
  ⟨.TraitObject (traitNameOf 0), true, .TraitObject, true, true⟩

/-- **Realizability of the null / misaligned universal fault equivalences
(`Mach` & `MachTB`)**: all hypotheses of
`dv_v1_null_ref_unsize_ub_universal_M` and
`dv_v1_misaligned_ref_unsize_ub_universal_M` hold jointly on the corpus state
and the corpus machine on BOTH memory models, for the null address and the
misaligned address `641`. -/
theorem dv_v1_null_and_misaligned_ref_unsize_ub_universal_M_nonvacuous
    (locals' : List LocalSlot) (decls : List MirAst.LocalDecl) (isMut : Bool) :
    evalThinToDynUnsize locals' (DynMemView.ofMemory dvNvState.memory) decls emptyLayoutTable
        (.scalar ⟨0, 8⟩) (.uint .u32) dvTrKey true isMut = .ub ∧
    evalThinToDynUnsize locals' (DynMemView.ofMemory dvNvState.memory) decls emptyLayoutTable
        (.scalar ⟨641, 8⟩) (.uint .u32) dvTrKey true isMut = .ub ∧
    checkPtrM (ThinPointer.widen ({ addr := 0, provenance := none } : Ptr)
        (some (.VTablePointer (dvVtPtr 0)))) (.Ref .Immutable dvDynPointee)
        (some (dvMrV4ArgSizeMach true)) = .error (.ub "Value::Ptr: null safe pointer") ∧
    checkPtrM (ThinPointer.widen dvDanglingThin (some (.VTablePointer (dvVtPtr 0))))
        (.Ref .Immutable dvDynPointee) (some (dvMrV4ArgSizeMach true)) =
      .error (.ub "Value::Ptr: unaligned safe pointer") ∧
    MachTB.wfLive (liftMachToTB (dvMrV4ArgSizeMach true)) ∧
    checkPtrM (ThinPointer.widen (liftThinPtrTB ({ addr := 0, provenance := none } : Ptr))
        (some (.VTablePointer (liftThinPtrTB (dvVtPtr 0))))) (.Ref .Immutable dvDynPointee)
        (some (liftMachToTB (dvMrV4ArgSizeMach true))) =
      .error (.ub "Value::Ptr: null safe pointer") ∧
    checkPtrM (ThinPointer.widen (liftThinPtrTB dvDanglingThin)
        (some (.VTablePointer (liftThinPtrTB (dvVtPtr 0))))) (.Ref .Immutable dvDynPointee)
        (some (liftMachToTB (dvMrV4ArgSizeMach true))) =
      .error (.ub "Value::Ptr: unaligned safe pointer") := by
  obtain ⟨⟨vts, dts⟩, hEnv, hProj⟩ := dv_some_of_map
    (o := dynVTableEnv? .none (DynMemView.ofMemory dvNvState.memory)
      (layoutPointerBytes emptyLayoutTable))
    (f := fun a => (dynTypeModeled a.2 dvTrKey,
      (lookupVTableFor a.1 (.uint .u32) dvTrKey).map (fun e => (e.sizeBytes, e.alignBytes))))
    (b := (true, some (4, 4))) (by decide +kernel)
  have hModeled : dynTypeModeled dts dvTrKey = true := congrArg Prod.fst hProj
  obtain ⟨entry, hVt, hLay⟩ := dv_some_of_map (congrArg Prod.snd hProj)
  have hSz : entry.sizeBytes = 4 := congrArg Prod.fst hLay
  have hAl : entry.alignBytes = 4 := congrArg Prod.snd hLay
  have hRel : DvVTableLayoutRel entry (dvMrVTable 0) := by
    unfold DvVTableLayoutRel
    rw [hSz, hAl]
    exact ⟨rfl, rfl⟩
  have hMis : 641 % entry.alignBytes ≠ 0 := by
    rw [hAl]
    decide
  have hNullBM := dv_v1_null_ref_unsize_ub_universal_M (M := BM) (dvMrV4ArgSizeMach true)
    (traitNameOf 0) (dvMrVTable 0) ({ addr := 0, provenance := none } : Ptr) (dvVtPtr 0)
    (.Ref .Immutable) dvDynPointee (.inl ⟨_, rfl⟩) rfl (by decide +kernel)
    (by first | rfl | decide +kernel) (by first | rfl | decide +kernel) (by decide +kernel) rfl
    locals' (DynMemView.ofMemory dvNvState.memory) decls (.uint .u32) dvTrKey isMut vts dts entry
    hEnv hModeled hVt
  have hNullTB := dv_v1_null_ref_unsize_ub_universal_M (M := TBM)
    (liftMachToTB (dvMrV4ArgSizeMach true))
    (traitNameOf 0) (dvMrVTable 0) (liftThinPtrTB ({ addr := 0, provenance := none } : Ptr))
    (liftThinPtrTB (dvVtPtr 0))
    (.Ref .Immutable) dvDynPointee (.inl ⟨_, rfl⟩) rfl (by decide +kernel)
    (by first | rfl | decide +kernel) (by first | rfl | decide +kernel) (by decide +kernel) rfl
    locals' (DynMemView.ofMemory dvNvState.memory) decls (.uint .u32) dvTrKey isMut vts dts entry
    hEnv hModeled hVt
  have hMisBM := dv_v1_misaligned_ref_unsize_ub_universal_M (M := BM) (dvMrV4ArgSizeMach true)
    (traitNameOf 0) (dvMrVTable 0) dvDanglingThin (dvVtPtr 0)
    (.Ref .Immutable) dvDynPointee (.inl ⟨_, rfl⟩) rfl (by decide +kernel)
    (by first | rfl | decide +kernel) (by first | rfl | decide +kernel) (by decide +kernel)
    641 (by decide) rfl (by decide)
    locals' (DynMemView.ofMemory dvNvState.memory) decls (.uint .u32) dvTrKey isMut vts dts entry
    hEnv hModeled hVt hRel hMis
  have hMisTB := dv_v1_misaligned_ref_unsize_ub_universal_M (M := TBM)
    (liftMachToTB (dvMrV4ArgSizeMach true))
    (traitNameOf 0) (dvMrVTable 0) (liftThinPtrTB dvDanglingThin) (liftThinPtrTB (dvVtPtr 0))
    (.Ref .Immutable) dvDynPointee (.inl ⟨_, rfl⟩) rfl (by decide +kernel)
    (by first | rfl | decide +kernel) (by first | rfl | decide +kernel) (by decide +kernel)
    641 (by decide) rfl (by decide)
    locals' (DynMemView.ofMemory dvNvState.memory) decls (.uint .u32) dvTrKey isMut vts dts entry
    hEnv hModeled hVt hRel hMis
  exact ⟨hNullBM.1, hMisBM.1, hNullBM.2, hMisBM.2, liftMachToTB_wfLive _, hNullTB.2, hMisTB.2⟩

/-- **Realizability of `dv_v3_vtableMethodLookup_universal_M` (`Mach` &
`MachTB`)**: on BOTH memory models the `(u32, Tr)` vtable pointer resolves
(`vtableLookupM`), the method `get` is implemented by function `1` and the
lookup returns its function pointer, and the unimplemented method `7` is a
specification panic. -/
theorem dv_v3_vtableMethodLookup_universal_M_nonvacuous (ty : Gen.PtrType) :
    vtableLookupM (dvMrV3Mach 0 (scalarBytes u32 7) 4) (dvVtPtr 0) = .ok (dvMrVTable 0) ∧
    evalUnOpM (.VTableMethodLookup dvMethGet) (.Ptr (ThinPointer.widen (dvVtPtr 0) none), .Ptr ty)
        (some (dvMrV3Mach 0 (scalarBytes u32 7) 4)) =
      .ok (.Ptr (ThinPointer.widen ({ addr := 4096, provenance := some (⟨0⟩, ()) } : Ptr) none),
        .Ptr .FnPtr) ∧
    evalUnOpM (.VTableMethodLookup ⟨⟨7⟩⟩) (.Ptr (ThinPointer.widen (dvVtPtr 0) none), .Ptr ty)
        (some (dvMrV3Mach 0 (scalarBytes u32 7) 4)) =
      .error (.specPanic "map index: missing key (vtable.methods[method])") ∧
    MachTB.wfLive (liftMachToTB (dvMrV3Mach 0 (scalarBytes u32 7) 4)) ∧
    vtableLookupM (liftMachToTB (dvMrV3Mach 0 (scalarBytes u32 7) 4)) (liftThinPtrTB (dvVtPtr 0))
      = .ok (dvMrVTable 0) ∧
    evalUnOpM (.VTableMethodLookup dvMethGet)
        (.Ptr (ThinPointer.widen (liftThinPtrTB (dvVtPtr 0)) none), .Ptr ty)
        (some (liftMachToTB (dvMrV3Mach 0 (scalarBytes u32 7) 4))) =
      .ok (.Ptr (ThinPointer.widen
          (liftThinPtrTB ({ addr := 4096, provenance := some (⟨0⟩, ()) } : Ptr)) none),
        .Ptr .FnPtr) ∧
    evalUnOpM (.VTableMethodLookup ⟨⟨7⟩⟩)
        (.Ptr (ThinPointer.widen (liftThinPtrTB (dvVtPtr 0)) none), .Ptr ty)
        (some (liftMachToTB (dvMrV3Mach 0 (scalarBytes u32 7) 4))) =
      .error (.specPanic "map index: missing key (vtable.methods[method])") := by
  have hLBM : vtableLookupM (dvMrV3Mach 0 (scalarBytes u32 7) 4) (dvVtPtr 0) =
      .ok (dvMrVTable 0) := by first | rfl | decide +kernel
  have hLTB : vtableLookupM (liftMachToTB (dvMrV3Mach 0 (scalarBytes u32 7) 4))
      (liftThinPtrTB (dvVtPtr 0)) = .ok (dvMrVTable 0) := by first | rfl | decide +kernel
  have hBM := dv_v3_vtableMethodLookup_universal_M (M := BM) (dvMrV3Mach 0 (scalarBytes u32 7) 4)
    (dvVtPtr 0) ty
  have hTB := dv_v3_vtableMethodLookup_universal_M (M := TBM)
    (liftMachToTB (dvMrV3Mach 0 (scalarBytes u32 7) 4)) (liftThinPtrTB (dvVtPtr 0)) ty
  refine ⟨hLBM, ?_, (hBM ⟨⟨7⟩⟩ (dvMrVTable 0) hLBM).2 (by decide +kernel),
    liftMachToTB_wfLive _, hLTB, ?_, (hTB ⟨⟨7⟩⟩ (dvMrVTable 0) hLTB).2 (by decide +kernel)⟩
  · rw [(hBM dvMethGet (dvMrVTable 0) hLBM).1 (fnName 1) (by first | rfl | decide +kernel)]
    first | rfl | decide +kernel
  · rw [(hTB dvMethGet (dvMrVTable 0) hLTB).1 (fnName 1) (by first | rfl | decide +kernel)]
    first | rfl | decide +kernel

/-- View of a vtable slot as `(method path, number of generic arguments)`. -/
def dvMethodSlotView : Option CapturedVTableSlot → Option (DefPath × Nat)
  | some (.method p args) => some (p, args.length)
  | _ => none

theorem dv_method_slot_of_view {o : Option CapturedVTableSlot} {p : DefPath}
    (h : dvMethodSlotView o = some (p, 0)) : o = some (.method p []) := by
  cases o with
  | none => cases h
  | some sl =>
    cases sl with
    | method p' args =>
      have hp : p' = p := congrArg Prod.fst (Option.some.inj h)
      have hl : args.length = 0 := congrArg Prod.snd (Option.some.inj h)
      rw [hp, List.eq_nil_of_length_eq_zero hl]
    | _ => cases h

/-- The corpus receiver state for the dispatch law: `_1 = (tag 1, (u32, Tr)
vtable)`, tag `1` a `Frozen` borrow of the pointee local `_2` holding `slot`,
with only the caller linked (the concrete method bodies are NOT linked). -/
def dvNvCallState (slot : LocalSlot) : MachineState :=
  { dvPointeeInit dvV3ArgCallMir 16384 .frozen slot with
    memory := { (dvPointeeInit dvV3ArgCallMir 16384 .frozen slot).memory with
      callees := [dvV3ArgCallMir] } }

/-- **Realizability of `dv_v3_evalVirtualCall_slot_universal`**: its five
shared hypotheses and each conjunct's premises hold on the corpus receiver
state, for every trailing argument list, destination, and unwind action:
1. the header slot `1` and the out-of-bounds slot `9` are UB;
2. with the pointee local dead, the method slot `3` is UB although the callee
   is not linked;
3. with a live pointee and the callee not linked, the method slot `3` emits
   the external call of `dv::<u32 as Tr>::get` with the receiver narrowed to
   the thin data pointer. -/
theorem dv_v3_evalVirtualCall_slot_universal_nonvacuous
    (restOps : List MirAst.Operand) (restVals : List Value) (dest : MirAst.Place)
    (unwind : MirAst.UnwindAction) :
    evalVirtualCall (dvNvCallState (.init (.scalar ⟨7, 4⟩))) (some dvV3ArgCallMir)
        { methodDefPath := "dv::Tr::hdr", dynKey := dvTrKey, slotIdx := 1 }
        dvV3ArgCallMir.localDecls emptyLayoutTable (.move (dvLoc 1) :: restOps)
        (.aggregate 0 [dvDataTag1, dvMetaTr] :: restVals)
        (dvNvCallState (.init (.scalar ⟨7, 4⟩))).frame.locals dest (some 1) unwind =
      MirStepNode.fail .ub ∧
    evalVirtualCall (dvNvCallState (.init (.scalar ⟨7, 4⟩))) (some dvV3ArgCallMir)
        { methodDefPath := "dv::Tr::oob", dynKey := dvTrKey, slotIdx := 9 }
        dvV3ArgCallMir.localDecls emptyLayoutTable (.move (dvLoc 1) :: restOps)
        (.aggregate 0 [dvDataTag1, dvMetaTr] :: restVals)
        (dvNvCallState (.init (.scalar ⟨7, 4⟩))).frame.locals dest (some 1) unwind =
      MirStepNode.fail .ub ∧
    evalVirtualCall (dvNvCallState .dead) (some dvV3ArgCallMir)
        { methodDefPath := "dv::Tr::get", dynKey := dvTrKey, slotIdx := 3 }
        dvV3ArgCallMir.localDecls emptyLayoutTable (.move (dvLoc 1) :: restOps)
        (.aggregate 0 [dvDataTag1, dvMetaTr] :: restVals)
        (dvNvCallState .dead).frame.locals dest (some 1) unwind =
      MirStepNode.fail .ub ∧
    evalVirtualCall (dvNvCallState (.init (.scalar ⟨7, 4⟩))) (some dvV3ArgCallMir)
        { methodDefPath := "dv::Tr::get", dynKey := dvTrKey, slotIdx := 3 }
        dvV3ArgCallMir.localDecls emptyLayoutTable (.move (dvLoc 1) :: restOps)
        (.aggregate 0 [dvDataTag1, dvMetaTr] :: restVals)
        (dvNvCallState (.init (.scalar ⟨7, 4⟩))).frame.locals dest (some 1) unwind =
      MirStepNode.extCall
        { defPath := "dv::<u32 as Tr>::get", typeArgs := [], args := dvDataTag1 :: restVals,
          memory := (dvNvCallState (.init (.scalar ⟨7, 4⟩))).memory }
        (resumeExternalCall (dvNvCallState (.init (.scalar ⟨7, 4⟩)))
          (dvNvCallState (.init (.scalar ⟨7, 4⟩))).frame.locals dest 1 unwind) := by
  have hLive := fun (vm : CapturedVirtualMethod) (hKey : vm.dynKey = dvTrKey) =>
    dvDynCheck_ok_of_map
      (r := checkDynVTablePtr (some dvV3ArgCallMir)
        (DynMemView.ofMemory (dvNvCallState (.init (.scalar ⟨7, 4⟩))).memory)
        (layoutPointerBytes emptyLayoutTable) dvMetaTr dvTrKey)
      (f := fun a => (dvSlotIsNonMethod (get? a.1.slots 1), dvSlotIsNonMethod (get? a.1.slots 9),
        dvMethodSlotView (get? a.1.slots 3),
        dvRecvOk (.ref .not) (dvNvCallState (.init (.scalar ⟨7, 4⟩))).frame.locals
          (dvNvCallState (.init (.scalar ⟨7, 4⟩))).memory dvV3ArgCallMir.localDecls
          emptyLayoutTable dvDataTag1 a.1))
      (b := (true, true, some ("dv::<u32 as Tr>::get", 0), true)) (by decide +kernel)
  obtain ⟨⟨entry, vts, dts⟩, hChk, hProj⟩ := hLive
    { methodDefPath := "dv::Tr::get", dynKey := dvTrKey, slotIdx := 3 } rfl
  have hS1 : dvSlotIsNonMethod (get? entry.slots 1) = true := congrArg Prod.fst hProj
  have hS9 : dvSlotIsNonMethod (get? entry.slots 9) = true :=
    congrArg (fun x => x.2.1) hProj
  have hS3 : get? entry.slots 3 = some (.method "dv::<u32 as Tr>::get" []) :=
    dv_method_slot_of_view (congrArg (fun x => x.2.2.1) hProj)
  have hOk : dvRecvOk (.ref .not) (dvNvCallState (.init (.scalar ⟨7, 4⟩))).frame.locals
      (dvNvCallState (.init (.scalar ⟨7, 4⟩))).memory dvV3ArgCallMir.localDecls
      emptyLayoutTable dvDataTag1 entry = true := congrArg (fun x => x.2.2.2) hProj
  obtain ⟨⟨entryD, vtsD, dtsD⟩, hChkD, hProjD⟩ := dvDynCheck_ok_of_map
      (r := checkDynVTablePtr (some dvV3ArgCallMir)
        (DynMemView.ofMemory (dvNvCallState .dead).memory)
        (layoutPointerBytes emptyLayoutTable) dvMetaTr dvTrKey)
      (f := fun a => (dvMethodSlotView (get? a.1.slots 3),
        dvRecvOk (.ref .not) (dvNvCallState .dead).frame.locals
          (dvNvCallState .dead).memory dvV3ArgCallMir.localDecls
          emptyLayoutTable dvDataTag1 a.1))
      (b := (some ("dv::<u32 as Tr>::get", 0), false)) (by decide +kernel)
  have hS3D : get? entryD.slots 3 = some (.method "dv::<u32 as Tr>::get" []) :=
    dv_method_slot_of_view (congrArg Prod.fst hProjD)
  have hBad : dvRecvOk (.ref .not) (dvNvCallState .dead).frame.locals
      (dvNvCallState .dead).memory dvV3ArgCallMir.localDecls
      emptyLayoutTable dvDataTag1 entryD = false := congrArg Prod.snd hProjD
  have hU := fun (vm : CapturedVirtualMethod) (hKey : vm.dynKey = dvTrKey) =>
    dv_v3_evalVirtualCall_slot_universal (dvNvCallState (.init (.scalar ⟨7, 4⟩)))
      (some dvV3ArgCallMir) vm dvV3ArgCallMir.localDecls emptyLayoutTable (.move (dvLoc 1)) restOps
      (.aggregate 0 [dvDataTag1, dvMetaTr]) restVals
      (dvNvCallState (.init (.scalar ⟨7, 4⟩))).frame.locals dest (some 1) unwind
      (dvRefDynTy dvTrKey) (.ref .not) dvTrKey dvDataTag1 dvMetaTr entry vts dts rfl rfl
      (by rw [hKey]; decide +kernel) rfl hChk
  have hUD := dv_v3_evalVirtualCall_slot_universal (dvNvCallState .dead)
      (some dvV3ArgCallMir) { methodDefPath := "dv::Tr::get", dynKey := dvTrKey, slotIdx := 3 }
      dvV3ArgCallMir.localDecls emptyLayoutTable (.move (dvLoc 1)) restOps
      (.aggregate 0 [dvDataTag1, dvMetaTr]) restVals
      (dvNvCallState .dead).frame.locals dest (some 1) unwind
      (dvRefDynTy dvTrKey) (.ref .not) dvTrKey dvDataTag1 dvMetaTr entryD vtsD dtsD rfl rfl
      (by decide +kernel) rfl hChkD
  exact ⟨(hU { methodDefPath := "dv::Tr::hdr", dynKey := dvTrKey, slotIdx := 1 } rfl).1 hS1,
    (hU { methodDefPath := "dv::Tr::oob", dynKey := dvTrKey, slotIdx := 9 } rfl).1 hS9,
    hUD.2.1 _ _ hS3D hBad,
    (hU { methodDefPath := "dv::Tr::get", dynKey := dvTrKey, slotIdx := 3 } rfl).2.2 _ _ 1 hS3 hOk
      (by decide +kernel) rfl⟩

/-! ### Further Trusted `stepMirFn` boundary witnesses (`C1`, `C2`, `C3`) -/

/-- `fn(r: P) -> D { r as D }` unsizing the thin pointer argument `_1 : srcTy`
to `dstTy`, with the pointee as the extra local `_2 : u32`. -/
def dvV1ArgPointeeUnsizeMir (srcTy dstTy : MirAst.Ty) : CapturedMir :=
  dvMkBody "dv::v1_arg_pointee_unsize" [dvDecl dstTy, dvDecl srcTy, dvDecl dvU32Ty] 1
    [dvBb [dvSt (.assign (dvLoc 0) (.cast (.pointerCoercion "Unsize") (.copy (dvLoc 1)) dstTy))]
      .return_]

/-- Initial state for `dvV1ArgPointeeUnsizeMir`: `_1` is the thin pointer with
borrow tag `1` (byte offset `off`), a borrow of local `2` with permission
`perm`, and local `2` holds `slot`. -/
def dvThinPointeeInit (body : CapturedMir) (perm : TreeBorrowPerm) (slot : LocalSlot)
    (off : Nat := 0) : MachineState :=
  let base := dvInitLive body [.ptr { allocId := 1, offsetBytes := off } 8] dvCallees
  { frame := { base.frame with locals := base.frame.locals.set 2 slot },
    memory := { base.memory with
      borrows := [ { tag := 1, targetLocal := 2, targetProjection := [], perm := perm,
                     rangeOffset := 0, rangeLen := 4 } ],
      nextTag := 2 } }

/-- `&u32 -> &dyn Tr` on the argument `_1`. -/
def dvV1RefPointeeUnsizeMir : CapturedMir :=
  dvV1ArgPointeeUnsizeMir dvRefU32Ty (dvRefDynTy dvTrKey)
/-- `*const u32 -> *const dyn Tr` on the argument `_1`. -/
def dvV1RawPointeeUnsizeMir : CapturedMir :=
  dvV1ArgPointeeUnsizeMir dvRawConstU32Ty (dvRawConstDynTy dvTrKey)

/-- **V1 reference-validity gate of `&T -> &dyn Trait`, Trusted `stepMirFn`
(`C2`)**: unsizing a reference requires a valid reference under Tree Borrows
(a `Frozen` tag to a live pointee unsizes; a `Disabled` tag, a dead pointee, and
a misaligned offset are UB), whereas the raw `*const T -> *const dyn Trait`
coercion accepts the `Disabled` tag, the dead pointee, and the misaligned
offset. -/
theorem dv_v1_ref_validity_vs_raw_trusted_witness :
    dvRunTrusted dvV1RefPointeeUnsizeMir dvTrustedFuel
      (dvThinPointeeInit dvV1RefPointeeUnsizeMir .frozen (.init (.scalar ⟨7, 4⟩)))
        = .widePtr 1 0 16384 ∧
    dvRunTrusted dvV1RefPointeeUnsizeMir dvTrustedFuel
      (dvThinPointeeInit dvV1RefPointeeUnsizeMir .disabled (.init (.scalar ⟨7, 4⟩))) = .ub ∧
    dvRunTrusted dvV1RefPointeeUnsizeMir dvTrustedFuel
      (dvThinPointeeInit dvV1RefPointeeUnsizeMir .frozen .dead) = .ub ∧
    dvRunTrusted dvV1RefPointeeUnsizeMir dvTrustedFuel
      (dvThinPointeeInit dvV1RefPointeeUnsizeMir .frozen (.init (.scalar ⟨7, 4⟩)) 1) = .ub ∧
    dvRunTrusted dvV1RawPointeeUnsizeMir dvTrustedFuel
      (dvThinPointeeInit dvV1RawPointeeUnsizeMir .disabled (.init (.scalar ⟨7, 4⟩)))
        = .widePtr 1 0 16384 ∧
    dvRunTrusted dvV1RawPointeeUnsizeMir dvTrustedFuel
      (dvThinPointeeInit dvV1RawPointeeUnsizeMir .frozen .dead) = .widePtr 1 0 16384 ∧
    dvRunTrusted dvV1RawPointeeUnsizeMir dvTrustedFuel
      (dvThinPointeeInit dvV1RawPointeeUnsizeMir .frozen (.init (.scalar ⟨7, 4⟩)) 1)
        = .widePtr 1 1 16384 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The `RigidTy.dynamic` key of `dyn Tr + Send`. -/
@[reducible] def dvTrSendKey : String := "dv::Tr + core::marker::Send"

/-- Trait-object descriptors of `dyn Tr` and `dyn Tr + Send` (the same
predicate key; the latter with the auto trait `Send`). -/
def dvAutoDynTypes : List CapturedDynType :=
  [ { dynKey := dvTrKey, predicateKey := dvTrKey, principalTrait? := some dvTrKey },
    { dynKey := dvTrSendKey, predicateKey := dvTrKey, principalTrait? := some dvTrKey,
      autoTraits := ["core::marker::Send"] } ]

/-- `fn(r: &dyn Src) -> &dyn Dst { r as &dyn Dst }` with the `dvAutoDynTypes`
descriptors; local `_2 : u32` is the pointee of the argument. -/
def dvV2AutoMir (src dst : String) : CapturedMir :=
  { dvMkBody "dv::v2_auto"
      [dvDecl (dvRefDynTy dst), dvDecl (dvRefDynTy src), dvDecl dvU32Ty] 1
      [dvBb [dvSt (.assign (dvLoc 0)
               (.cast (.pointerCoercion "Unsize") (.copy (dvLoc 1)) (dvRefDynTy dst)))]
        .return_] with dynTypes := dvAutoDynTypes }

/-- **V2 auto-trait boundary, Trusted `stepMirFn` (`C2`)**: the ill-typed
auto-trait ADDITION `&dyn Tr -> &dyn (Tr + Send)` fails closed
(`.unsupported`, never a value and never `.ub`), while the auto-trait REMOVAL
`&dyn (Tr + Send) -> &dyn Tr` and the NOP coercions keep the wide pointer. -/
theorem dv_v2_autoTrait_boundary_trusted_witness :
    dvRunTrusted (dvV2AutoMir dvTrKey dvTrSendKey) dvTrustedFuel
      (dvPointeeInit (dvV2AutoMir dvTrKey dvTrSendKey) 16384 .frozen (.init (.scalar ⟨7, 4⟩)))
        = .unsupported ∧
    dvRunTrusted (dvV2AutoMir dvTrSendKey dvTrKey) dvTrustedFuel
      (dvPointeeInit (dvV2AutoMir dvTrSendKey dvTrKey) 16384 .frozen (.init (.scalar ⟨7, 4⟩)))
        = .widePtr 1 0 16384 ∧
    dvRunTrusted (dvV2AutoMir dvTrKey dvTrKey) dvTrustedFuel
      (dvPointeeInit (dvV2AutoMir dvTrKey dvTrKey) 16384 .frozen (.init (.scalar ⟨7, 4⟩)))
        = .widePtr 1 0 16384 ∧
    dvRunTrusted (dvV2AutoMir dvTrSendKey dvTrSendKey) dvTrustedFuel
      (dvPointeeInit (dvV2AutoMir dvTrSendKey dvTrSendKey) 16384 .frozen
        (.init (.scalar ⟨7, 4⟩))) = .widePtr 1 0 16384 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- `fn(x: u32) -> u32 { Pin::new(&mut x as &mut dyn Tr).get(5) }`: a virtual
call whose receiver is `Pin<&mut dyn Tr>`. -/
def dvV3PinCallMir : CapturedMir :=
  dvMkBody "dv::v3_pin_call"
    [dvDecl dvU32Ty, dvDecl dvU32Ty, dvDecl dvRefMutU32Ty,
     dvDecl (dvPinTy (.ref .mut (.uint .u32))),
     dvDecl (dvPinTy (.ref .mut (.dynamic dvTrKey)))] 1
    [dvBb [dvSt (.assign (dvLoc 2) (.ref (.mut false) (dvLoc 1))),
           dvSt (.assign (dvLoc 3) (.aggregate (.adt "core::pin::Pin" 0 none) [.move (dvLoc 2)])),
           dvSt (.assign (dvLoc 4)
             (.cast (.pointerCoercion "Unsize") (.move (dvLoc 3))
               (dvPinTy (.ref .mut (.dynamic dvTrKey)))))]
       (.call (dvFnConst "dv::Tr::get" [.dynamic dvTrKey]) [.move (dvLoc 4), dvConstU32 5] (dvLoc 0)
         (some 1) .continue_),
     dvBb [] .return_]

/-- View of the argument list of an external-call step node: `100 + tag` for a
one-field wrapper around a thin pointer with borrow tag `tag` (a re-wrapped
`Pin<&mut T>` receiver), `tag` for a bare thin pointer, `1000 + bits` for a
scalar. -/
def dvExtCallArgView : MirStepNode → Option (List Nat)
  | .vis (.inr (.inr (.call req))) _ =>
    some (req.args.map fun
      | .aggregate 0 [.ptr p 8] => 100 + p.allocId
      | .ptr p 8 => p.allocId
      | .scalar ⟨b, _⟩ => 1000 + b
      | _ => 9999)
  | _ => none

/-- The `dvExtCallArgView` of the step node after `n` steps. -/
def dvTrustedExtCallArgsAfter (body : CapturedMir) (n : Nat) (s : MachineState) :
    Option (List Nat) :=
  match Nat.repeat (dvTrustedRunStep body) n (.running s) with
  | .running s' => dvExtCallArgView (stepMirFn body s')
  | .done _ => none

/-- **V3 `Pin<&mut dyn Tr>` receiver unwrapping and re-wrapping, Trusted
`stepMirFn` (`C3`)**: with the concrete method not linked, the virtual call
through a `Pin<&mut dyn Tr>` receiver unwraps the pin to find the vtable,
selects the slot-`3` method `dv::<u32 as Tr>::get`, and passes the receiver
re-wrapped as `Pin<&mut u32>` around the thin data pointer (borrow tag `1`),
followed by the argument `5`; the plain `&dyn Tr` receiver of `dvV3CallU32Mir`
is passed as the bare thin pointer (the shared reborrow, tag `1`). -/
theorem dv_v3_pin_receiver_rewrap_trusted_witness :
    dvTrustedNodeAfter dvV3PinCallMir 3 (dvInitLive dvV3PinCallMir [.scalar ⟨7, 4⟩])
      = (2, "dv::<u32 as Tr>::get") ∧
    dvTrustedExtCallArgsAfter dvV3PinCallMir 3 (dvInitLive dvV3PinCallMir [.scalar ⟨7, 4⟩])
      = some [101, 1005] ∧
    dvTrustedExtCallArgsAfter dvV3CallU32Mir 2 (dvInitLive dvV3CallU32Mir [.scalar ⟨7, 4⟩])
      = some [1, 1005] :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## §6. Canonical Executable MiniRust Corpus Observation Interface

Directly executes `MiniRustSpec.Interp.{steps, stepsTB}` for all 4 variants
(normal returns, UB faults, and the `Mach` vs. `MachTB` mode sensitivity of the
Crubit `c16` receiver protector) without any shadow evaluator, so
`Anneal.Mir.DynTraitVTableBundle` can wire `MiniRustSpec.Interp` directly into
`DualCorrespondenceBundle`. -/

/-- MiniRust execution mode: `BasicMemory` (`Mach`) versus `TreeBorrowsMemory` (`MachTB`). -/
inductive DynVtMrMode : Type where
  | basicMemory
  | treeBorrows
  deriving DecidableEq, Repr

/-- Raw authority-typed observation produced directly by `MiniRustSpec.Interp`:
the bytes (with provenance) of the return allocation, or the fault class. -/
inductive DynVtMrObs : Type where
  | retBytes (bs : List TBByteOutcome)
  | ub
  | unsupported
  deriving DecidableEq

/-- Run `n` steps of `MiniRustSpec.Interp` in mode `mode` and extract allocation
`allocIdx`'s observable bytes (`projByteTB`), or `.ub` / `.unsupported`. -/
def dvRunMrObs (mode : DynVtMrMode) (n : Nat) (allocIdx : Nat) (m : Mach) : DynVtMrObs :=
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

/-- The MiniRust machine and step count of each `(variant, case)` key. The
result local is always frame allocation `10`.

| key                       | machine                                                              |
|---------------------------|----------------------------------------------------------------------|
| `thinUnsize.okPrimary`    | thin pointer to the live `u32` object, unsized to `&dyn Tr`          |
| `thinUnsize.okSecondary`  | dangling misaligned thin pointer (`641`), unsized to `*const dyn Tr` |
| `thinUnsize.ubFault`      | the same dangling pointer, unsized to `&dyn Tr`                      |
| `thinUnsize.modeCase`     | thin pointer to the live `u64` object, unsized to `&mut dyn Tr`      |
| `dynUpcastAndNop.ok*`     | `&dyn Sub` upcast to `&dyn Super` / `&dyn Side`                      |
| `dynUpcastAndNop.ubFault` | NOP on `&dyn Tr` whose metadata is the `(u32, Alt)` vtable           |
| `dynUpcastAndNop.modeCase`| NOP on a dangling `*const dyn Tr` with the `(u32, Tr)` vtable        |
| `virtual….okPrimary`      | `r.get(5)` on the `u32` receiver                                     |
| `virtual….okSecondary`    | `r.get(5)` on the `u64` receiver                                     |
| `virtual….ubFault`        | `r.get(5)` on a receiver whose metadata is the `(u32, Alt)` vtable   |
| `virtual….modeCase`       | the full Crubit `c16` dispatch `r.poke(p)` with `p` aliasing `*r`    |
| `dynLayout….okPrimary`    | `size_of_val(&dyn Tr)` after the reference's tag was disabled        |
| `dynLayout….okSecondary`  | thin-pointer equality of `*const dyn Tr` and `*const dyn Alt`        |
| `dynLayout….ubFault`      | `size_of_val(&dyn Tr)` on a reference to a dead allocation           |
| `dynLayout….modeCase`     | wide equality of `(u32, Tr)` and `(u64, Tr)` pointers to one address | -/
def dvMrMachine : DynVtVariant → DynVtCase → Nat × Mach
  | .thinUnsize, .okPrimary =>
    (2, dvMrV1Mach (dvRefDynMrTy 0) 0 (dvDataBytes 13) (scalarBytes u32 7) 4)
  | .thinUnsize, .okSecondary =>
    (2, dvMrV1Mach (dvRawDynMrTy 0) 0 dvDanglingBytes (scalarBytes u32 7) 4)
  | .thinUnsize, .ubFault =>
    (2, dvMrV1Mach (dvRefDynMrTy 0) 0 dvDanglingBytes (scalarBytes u32 7) 4)
  | .thinUnsize, .modeCase =>
    (2, dvMrV1Mach (dvMutDynMrTy 0) 1 (dvDataBytes 13) (scalarBytes dvU64It 64) 8)
  | .dynUpcastAndNop, .okPrimary => (2, dvMrV2UpcastMach 3 4)
  | .dynUpcastAndNop, .okSecondary => (2, dvMrV2UpcastMach 4 5)
  | .dynUpcastAndNop, .ubFault =>
    (1, dvMrV2NopMach (dvRefDynMrTy 0) (dvDataBytes 12 ++ dvVtBytes 2))
  | .dynUpcastAndNop, .modeCase =>
    (1, dvMrV2NopMach (dvRawDynMrTy 0) (dvDanglingBytes ++ dvVtBytes 0))
  | .virtualDispatchAndProtector, .okPrimary => (4, dvMrV3Mach 0 (scalarBytes u32 7) 4)
  | .virtualDispatchAndProtector, .okSecondary => (4, dvMrV3Mach 1 (scalarBytes dvU64It 64) 8)
  | .virtualDispatchAndProtector, .ubFault => (4, dvMrV3Mach 2 (scalarBytes u32 7) 4)
  | .virtualDispatchAndProtector, .modeCase => (5, dvMrV3PokeMach)
  | .dynLayoutRawBorrowAndAddrEq, .okPrimary => (5, dvMrV4SizeMach true)
  | .dynLayoutRawBorrowAndAddrEq, .okSecondary => (1, dvMrV4CmpMach true 0 1 0 2)
  | .dynLayoutRawBorrowAndAddrEq, .ubFault => (1, dvMrV4ArgSizeMach false)
  | .dynLayoutRawBorrowAndAddrEq, .modeCase => (1, dvMrV4CmpMach false 0 0 0 1)

/-- Direct `MiniRustSpec.Interp` observation for every `(mode, variant, case)`
key. Every entry executes the actual MiniRust interpreter (`Interp.steps` or
`Interp.stepsTB`) on a concrete `Mach` / `MachTB` machine. -/
def dvMrObserve (mode : DynVtMrMode) (v : DynVtVariant) (c : DynVtCase) : DynVtMrObs :=
  dvRunMrObs mode (dvMrMachine v c).1 10 (dvMrMachine v c).2

/-- The raw observation of a `BasicMemory` byte list. -/
def dvMrBytesObs (bs : List Byte) : DynVtMrObs :=
  .retBytes (bs.map (projByteTB ∘ liftByteTB))

/-- The frozen dictionary of distinct raw MiniRust observations of the corpus.
The class of an observation is its index in this list:

| class | raw observation                                                    |
|------:|--------------------------------------------------------------------|
| 0     | wide pointer: data object (`640`, allocation `13`), vtable `0`     |
| 1     | wide pointer: dangling `641` (no provenance), vtable `0`           |
| 2     | wide pointer: data object (`640`, allocation `13`), vtable `1`     |
| 3     | wide pointer: data object (`640`, allocation `13`), vtable `4`     |
| 4     | wide pointer: data object (`640`, allocation `13`), vtable `5`     |
| 5     | `u32` `2`                                                          |
| 6     | `u32` `69`                                                         |
| 7     | `u32` `77`                                                         |
| 8     | `usize` `4`                                                        |
| 9     | `bool` `true`                                                      |
| 10    | `bool` `false`                                                     |
| 11    | undefined behavior                                                 |
| 12    | unsupported                                                        | -/
def dvMrObsDict : List DynVtMrObs :=
  [ dvMrBytesObs (dvDataBytes 13 ++ dvVtBytes 0),
    dvMrBytesObs (dvDanglingBytes ++ dvVtBytes 0),
    dvMrBytesObs (dvDataBytes 13 ++ dvVtBytes 1),
    dvMrBytesObs (dvDataBytes 13 ++ dvVtBytes 4),
    dvMrBytesObs (dvDataBytes 13 ++ dvVtBytes 5),
    dvMrBytesObs (scalarBytes u32 2),
    dvMrBytesObs (scalarBytes u32 69),
    dvMrBytesObs (scalarBytes u32 77),
    dvMrBytesObs (scalarBytes IntType.usize_ty 4),
    dvMrBytesObs [.Init 1 none],
    dvMrBytesObs [.Init 0 none],
    .ub,
    .unsupported ]

/-- Index of the first entry of `dict` equal to `o`, counting from `i`. -/
def dvMrObsClassAux (o : DynVtMrObs) : List DynVtMrObs → Nat → Option Nat
  | [], _ => none
  | d :: ds, i => if d = o then some i else dvMrObsClassAux o ds (i + 1)

/-- The class of a raw observation: its index in `dvMrObsDict` (`none` for an
observation outside the dictionary, which fails every downstream check). -/
def dvMrObsClass (o : DynVtMrObs) : Option Nat :=
  dvMrObsClassAux o dvMrObsDict 0

/-- The class of the direct `MiniRustSpec.Interp` observation of a key. -/
def dvMrObserveClass (mode : DynVtMrMode) (v : DynVtVariant) (c : DynVtCase) : Option Nat :=
  dvMrObsClass (dvMrObserve mode v c)

/-- Boolean check that `dvMrObsDict` has no duplicate entries and that every
entry's class is its own index. -/
def dvMrObsDictDistinct : Bool :=
  (List.range dvMrObsDict.length).all fun i =>
    decide ((dvMrObsDict[i]?).bind dvMrObsClass = some i) &&
    (List.range dvMrObsDict.length).all fun j =>
      decide (i = j) || decide (dvMrObsDict[i]? ≠ dvMrObsDict[j]?)

/-- **Kernel-checked injectivity of the class dictionary**: distinct classes
are distinct raw byte observations, and classification is exact on the
dictionary. -/
theorem dvMrObsDict_distinct : dvMrObsDictDistinct = true := by
  decide +kernel

/-- The frozen 32-key MiniRust observation-class table. -/
def dvMrExpectedClass (mode : DynVtMrMode) : DynVtVariant → DynVtCase → Nat
  | .thinUnsize, .okPrimary => 0
  | .thinUnsize, .okSecondary => 1
  | .thinUnsize, .ubFault => 11
  | .thinUnsize, .modeCase => 2
  | .dynUpcastAndNop, .okPrimary => 3
  | .dynUpcastAndNop, .okSecondary => 4
  | .dynUpcastAndNop, .ubFault => 11
  | .dynUpcastAndNop, .modeCase => 1
  | .virtualDispatchAndProtector, .okPrimary => 5
  | .virtualDispatchAndProtector, .okSecondary => 6
  | .virtualDispatchAndProtector, .ubFault => 11
  | .virtualDispatchAndProtector, .modeCase =>
    match mode with
    | .basicMemory => 7
    | .treeBorrows => 11
  | .dynLayoutRawBorrowAndAddrEq, .okPrimary => 8
  | .dynLayoutRawBorrowAndAddrEq, .okSecondary => 9
  | .dynLayoutRawBorrowAndAddrEq, .ubFault => 11
  | .dynLayoutRawBorrowAndAddrEq, .modeCase => 10

/-- **Kernel-checked MiniRust table**: on all 32 keys, executing
`MiniRustSpec.Interp.{steps, stepsTB}` yields a raw observation of exactly the
frozen class. -/
theorem dvMrObserveClass_table (mode : DynVtMrMode) (v : DynVtVariant) (c : DynVtCase) :
    dvMrObserveClass mode v c = some (dvMrExpectedClass mode v c) := by
  cases mode <;> cases v <;> cases c <;> decide +kernel

/-- Mode sensitivity certified directly on `dvMrObserve`: the full Crubit `c16`
dispatch returns `77` under `BasicMemory` (`Mach`) and faults `.ub` under
`TreeBorrowsMemory` (`MachTB`). -/
theorem dvMrObserve_c16_mode_sensitivity :
    dvMrObserve .basicMemory .virtualDispatchAndProtector .modeCase =
      .retBytes ((scalarBytes u32 77).map (projByteTB ∘ liftByteTB)) ∧
    dvMrObserve .treeBorrows .virtualDispatchAndProtector .modeCase = .ub :=
  ⟨by decide +kernel, by decide +kernel⟩

/-! ## §7. Exhaustive Axiom, Import-Isolation, & `Classical.choice`-Free Observer Audit -/

section AxiomAudit
open Lean Elab Command

/-- Exhaustively verify that:
1. This module obeys `[IMPORT-ISOLATION]` (zero `Anneal.*`, zero
   `LeanMiriSpec.*`, zero `DeinitBridge`, zero `IntrinsicBoundary` imports).
2. Every declaration defined in `MiniRustSpec.DynTraitVTableMR` depends ONLY on
   standard Lean axioms (`propext`, `Quot.sound`, `Classical.choice`) with zero
   `sorryAx` and zero `Lean.ofReduceBool` / `Lean.trustCompiler`.
3. All executable observers, class codecs, kernel-checked table theorems, and
   the universal Trusted-side laws listed below are strictly
   `Classical.choice`-free.
4. Every universal law and its realizability witness is present. -/
elab "#assert_dyn_trait_vtable_mr_audit" : command => do
  let env ← getEnv
  for modName in env.header.moduleNames do
    if (`Anneal).isPrefixOf modName || (`LeanMiriSpec).isPrefixOf modName ||
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
    throwError "MiniRustSpec.DynTraitVTableMR: 0 declarations found"
  let choiceFree : List Lean.Name := [
    ``dvTrustedValueObs,
    ``dvRunTrusted,
    ``dvTrustedObserve,
    ``dvTrustedObserve_table,
    ``dvRunMrObs,
    ``dvMrObserve,
    ``dvMrObsClass,
    ``dvMrObserveClass,
    ``dvMrObsDict_distinct,
    ``dvMrObserveClass_table,
    ``dvMrObserve_c16_mode_sensitivity,
    ``dv_wfVTableEntry_minirust_valid_layout,
    ``dv_dynSizeAlignOfVal_agrees_computeSizeAlign_M,
    ``dv_dynSizeAlignOfVal_fault_universal,
    ``dv_v1_evalThinToDynUnsize_universal,
    ``dv_v1_raw_wide_ptr_checkPtrM_universal,
    ``dv_dynRefDataValid_scalar_universal,
    ``dv_v3_evalVirtualCall_slot_universal,
    ``dv_v3_evalVirtualCall_slot_universal_nonvacuous,
    ``dv_v3_vtableMethodLookup_universal_M,
    ``dv_v3_c16_callee_entry_matches_corpus_state
  ]
  for c in choiceFree do
    let axs ← liftCoreM <| Lean.collectAxioms c
    if axs.contains ``Classical.choice then
      throwError "MR observer/law {c} unexpectedly depends on Classical.choice"
  let required : List Lean.Name := [
    ``dvVTables_layoutRel,
    ``dv_wfVTableEntry_minirust_valid_layout,
    ``dv_wfVTableEntry_minirust_valid_layout_nonvacuous,
    ``dv_dynSizeAlignOfVal_agrees_computeSizeAlign_M,
    ``dv_dynSizeAlignOfVal_agrees_computeSizeAlign_M_nonvacuous,
    ``dv_dynSizeAlignOfVal_fault_universal,
    ``dv_dynSizeAlignOfVal_fault_universal_nonvacuous,
    ``dv_v1_evalThinToDynUnsize_universal,
    ``dv_v1_evalThinToDynUnsize_universal_nonvacuous,
    ``dv_v1_raw_wide_ptr_checkPtrM_universal,
    ``dv_v1_raw_wide_ptr_checkPtrM_universal_nonvacuous,
    ``dv_dynRefDataValid_scalar_universal,
    ``dv_dynRefDataValid_scalar_universal_nonvacuous,
    ``dv_v1_null_ref_unsize_ub_universal_M,
    ``dv_v1_misaligned_ref_unsize_ub_universal_M,
    ``dv_v1_null_and_misaligned_ref_unsize_ub_universal_M_nonvacuous,
    ``dv_v3_evalVirtualCall_slot_universal,
    ``dv_v3_evalVirtualCall_slot_universal_nonvacuous,
    ``dv_v3_vtableMethodLookup_universal_M,
    ``dv_v3_vtableMethodLookup_universal_M_nonvacuous,
    ``dv_v3_trusted_dispatch_gates_witness,
    ``dv_v3_nonMethod_slot_ub_vs_minirust_specPanic,
    ``dv_v3_c16_callee_entry_matches_corpus_state,
    ``dv_v3_virtualDispatch_three_way_witness,
    ``dv_v1_thinUnsize_three_way_witness,
    ``dv_v1_failClosed_boundary_witness,
    ``dv_v2_resolveUpcastVTable_diamond_witness,
    ``dv_v2_upcast_and_nop_three_way_witness,
    ``dv_v4_dynLayout_three_way_witness,
    ``dv_v4_rawBorrow_trusted_witness,
    ``dv_v4_wideCmp_addrEq_three_way_witness,
    ``dv_v1_ref_validity_vs_raw_trusted_witness,
    ``dv_v2_autoTrait_boundary_trusted_witness,
    ``dv_v3_pin_receiver_rewrap_trusted_witness
  ]
  for c in required do
    match env.find? c with
    | some (.thmInfo _) => pure ()
    | _ => throwError "required theorem {c} is missing"
  logInfo m!"MiniRustSpec.DynTraitVTableMR: verified {checked} declarations (sorry_free=true, import_isolated=true, choice_free={choiceFree.length}, required_theorems={required.length})"

#assert_dyn_trait_vtable_mr_audit

end AxiomAudit

end MiniRustSpec.DynTraitVTableMR
