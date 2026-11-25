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
# `dyn Trait` Unsizing, Upcasting, VTables, Virtual Dispatch & Dynamic Layout

Authority 2 of the `dyn Trait` correspondence: the conservative hook overlay
`annealStepHooksDynTraitVTable` (strictly extending `annealStepHooksNullaryPtr`)
and the executable authority-typed observation `dvLmObserve`, stepping
unmodified vendored `Miri.Interpreter.Step.step` (`runMiriSteps`) on the frozen
`§0` fixtures. Every `dyn` operation runs real vendored code, with leaves
derived from the captured `CapturedMir.vtables` / `virtualMethods` tables:

* `Unsize` to `&dyn` / `&mut dyn` / `*const dyn` and `dyn Sub -> dyn Super`
  (prefix, `TraitVPtr`, diamond) run `Cast.cast -> Cast.unsizeInto ->
  unsizeIntoPointer`, whose `vtableType` / `vtablePointer` leaves are vendored
  `VTable.getPtrVTableType` (with `checkForType` / `sortedPredicates`) and
  `VTable.getPointer` over a `VTableMachine.Registry` built from the table (the
  vtable `AllocId` of record `v` is `v.vtableAllocId = 16384 + v.vtableId`);
  the destination's validity (`validatePlace`) checks the metadata with
  `VTable.getPtrVTableTypeRead` and, for references, dereferenceability for the
  dynamic size (`DynamicLayout.sizeAndAlignFromMeta`, `VTable.getSizeAndAlignRead`);
* virtual calls run `VirtualCalls.resolveVirtual` (receiver unwrapping, vtable
  type check, `entries[slot]` method selection — non-method / out-of-bounds
  slots are UB —, concrete-instance assertion, thin receiver) and push the
  linked concrete callee frame;
* safe `size_of_val` / `align_of_val` run `DynamicLayout.sizeAndAlignFromMeta`
  after the function-entry validity of `&dyn` (no Tree Borrows read: `C5`);
* wide `==` runs vendored `ScalarOps.binary -> ExecutionScalar.pointerBinary`
  (lexicographic `(data, vtable)`), and `core::ptr::addr_eq` runs its linked
  library body (`PtrToPtr` fat-to-thin via vendored `Cast.ptrToPtr`, then thin
  pointer equality);
* in Tree Borrows mode (`treeBorrows = true`) an assignment through a bare
  dereference performs a vendored Tree Borrows write
  (`npApplyTreeBorrowsWriteAt`), which a protected receiver tag turns into UB
  (Crubit `c16`, key `(2, 3)`).

Strict import isolation: this module NEVER imports `MiniRustSpec.*` or
`Anneal.*` (verified by the trailing `#assert_dyn_trait_vtable_lm_audit`).
-/

namespace LeanMiriSpec.DynTraitVTableLM

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

/-! ## §1. VTable Environment Leaves Derived From the Captured Tables -/

/-- Base `TyId` of the synthetic trait-object (`dyn K`) tails produced by the
overlay's `lockstepTails` leaf: `dvDynTailBase + dvKeyIdx vts K`. -/
def dvDynTailBase : Miri.MIR.TyId := 100000
/-- Base `TyId` of the concrete vtable types `T` (`dvConcreteBase + index`). -/
def dvConcreteBase : Miri.MIR.TyId := 200000
/-- Base `DefId` of the concrete trait-method instances listed in vtables. -/
def dvMethodBase : Miri.MIR.DefId := 300000
/-- Base `DefId` of the `InstanceKind::Virtual` method records. -/
def dvVirtualBase : Miri.MIR.DefId := 400000

/-- Trait identifier (compiler `Nat` predicate id) of the trait-object key `k`:
the index of the first captured vtable built for `k` (`vts.length` when no
vtable is captured for `k`). -/
def dvKeyIdx (vts : List CapturedVTable) (k : DefPath) : Nat :=
  (vts.findIdx? (fun v => stringEq v.dynKey k)).getD vts.length

/-- The trait-object key named by trait identifier `i`. -/
def dvKeyOfIdx? (vts : List CapturedVTable) (i : Nat) : Option DefPath :=
  (vts[i]?).map (·.dynKey)

/-- Concrete-type `TyId` of `ty`: `dvConcreteBase` plus the index of the first
captured vtable whose concrete type is `ty` (`rigidTyEq`). -/
def dvConcreteTyId (vts : List CapturedVTable) (ty : RigidTy) : Miri.MIR.TyId :=
  dvConcreteBase + (vts.findIdx? (fun v => rigidTyEq v.concreteTy ty)).getD vts.length

/-- The captured vtable whose index names the concrete-type `TyId` `tyId`. -/
def dvVTableOfConcreteTyId? (vts : List CapturedVTable) (tyId : Miri.MIR.TyId) :
    Option CapturedVTable :=
  if dvConcreteBase ≤ tyId then vts[tyId - dvConcreteBase]? else none

/-- Concrete type named by a concrete-type `TyId`. -/
def dvConcreteOfTyId? (vts : List CapturedVTable) (tyId : Miri.MIR.TyId) : Option RigidTy :=
  (dvVTableOfConcreteTyId? vts tyId).map (·.concreteTy)

/-- Synthetic `dyn K` tail `TyId`. -/
def dvDynTailTyId (vts : List CapturedVTable) (k : DefPath) : Miri.MIR.TyId :=
  dvDynTailBase + dvKeyIdx vts k

/-- Trait identifier carried by a synthetic `dyn` tail `TyId`. -/
def dvDynTailIdx? (tyId : Miri.MIR.TyId) : Option Nat :=
  if dvDynTailBase ≤ tyId ∧ tyId < dvConcreteBase then some (tyId - dvDynTailBase) else none

/-- Every method `DefPath` listed in a vtable slot, in table order. -/
def dvMethodPaths (vts : List CapturedVTable) : List DefPath :=
  vts.flatMap fun v => v.slots.filterMap fun
    | .method p _ => some p
    | _ => none

/-- `DefId` of the concrete method `p`. -/
def dvMethodDefId (vts : List CapturedVTable) (p : DefPath) : Miri.MIR.DefId :=
  dvMethodBase + ((dvMethodPaths vts).findIdx? (fun q => stringEq q p)).getD (dvMethodPaths vts).length

/-- Concrete `InstanceKind::Item` call instance of the method `p`. -/
def dvMethodInstance (vts : List CapturedVTable) (p : DefPath) : Miri.Interpreter.CallInstance :=
  { kind := .Item (dvMethodDefId vts p), args := #[] }

/-- Method `DefPath` of a concrete call instance. -/
def dvMethodOfInstance? (vts : List CapturedVTable) (inst : Miri.Interpreter.CallInstance) :
    Option DefPath :=
  match inst.kind with
  | .Item d => if dvMethodBase ≤ d then (dvMethodPaths vts)[d - dvMethodBase]? else none
  | _ => none

/-- Translate one captured vtable slot to vendored `VTableEntry`. -/
def dvSlotEntry (vts : List CapturedVTable) : CapturedVTableSlot →
    Miri.Interpreter.VTableEntry Miri.Interpreter.CallInstance
  | .dropInPlace _ => .dropInPlace
  | .size => .size
  | .align => .align
  | .vacant => .vacant
  | .method p _ => .method (dvMethodInstance vts p)
  | .traitVPtr vid =>
    .traitVPtr (match lookupVTableById vts vid with
      | some w => dvKeyIdx vts w.dynKey
      | none => vts.length)
  | .unmodeledMethod => .method { kind := .Item 0, args := #[] }

/-- Vendored entry array of a captured vtable. -/
def dvVTableEntries (vts : List CapturedVTable) (v : CapturedVTable) :
    Array (Miri.Interpreter.VTableEntry Miri.Interpreter.CallInstance) :=
  (v.slots.map (dvSlotEntry vts)).toArray

/-- Registry entry of one captured vtable: `(concrete TyId, trait id, salt 0,
vtableAllocId)` (a record whose `vtableAllocId` is `0` is not representable as
an `AllocId` and has no entry). -/
def dvRegistryEntry? (vts : List CapturedVTable) (v : CapturedVTable) :
    Option Miri.Interpreter.VTableMachine.Entry :=
  if h : UInt64.ofNat v.vtableAllocId ≠ 0 then
    some { typeId := dvConcreteTyId vts v.concreteTy, dynamicType := dvKeyIdx vts v.dynKey,
           salt := 0, allocation := ⟨UInt64.ofNat v.vtableAllocId, h⟩ }
  else none

/-- Vendored `VTableMachine.Registry` derived from the captured vtables (one
`dvRegistryEntry?` per record). -/
def dvRegistry (vts : List CapturedVTable) : Miri.Interpreter.VTableMachine.Registry :=
  ⟨(vts.filterMap (dvRegistryEntry? vts)).toArray⟩

/-- Registry lookup of a vtable allocation (the first branch of vendored
`VTableMachine.globalVTable`). -/
def dvRegistryLookup (reg : Miri.Interpreter.VTableMachine.Registry) (aid : Miri.Memory.AllocId) :
    Option (Miri.MIR.TyId × Nat) :=
  (reg.entries.find? (·.allocation == aid)).map fun e => (e.typeId, e.dynamicType)

/-- Registry reservation lookup (the hit branch of vendored `VTableMachine.reserve`). -/
def dvRegistryReserve (reg : Miri.Interpreter.VTableMachine.Registry) (ty : Miri.MIR.TyId)
    (dynType salt : Nat) : Option Miri.Memory.AllocId :=
  (reg.entries.find? (fun e => e.typeId == ty && e.dynamicType == dynType && e.salt.val == salt)).map
    (·.allocation)

/-- Sized layout of the concrete type of vtable `v` (`size_of::<T>()`,
`align_of::<T>()` as captured). -/
def dvConcreteLayout (vts : List CapturedVTable) (v : CapturedVTable) :
    Miri.ABI.TyAndLayout Miri.MIR.TyId :=
  let al := translateAlignBytes v.alignBytes
  { ty := dvConcreteTyId vts v.concreteTy
    layout := { zstLayoutData with
      size := translateSizeBytes v.sizeBytes, align := ⟨al⟩, unadjustedAbiAlign := al,
      uninhabited := v.isUninhabited } }

/-- Unsized layout of the trait-object pointee `dyn K`. -/
def dvDynLayout (tyId : Miri.MIR.TyId) : Miri.ABI.TyAndLayout Miri.MIR.TyId :=
  { ty := tyId, layout := { zstLayoutData with backendRepr := .Memory (sized := false) } }

/-- Resolve a vtable pointer against the machine's base-address table. -/
def dvResolveVtPtr (mach : AnnealMachine) (ptr : Miri.Memory.Pointer (Option AnnealProv)) :
    Except Miri.Interpreter.VTablePointerError (Miri.Memory.AllocId × Miri.ABI.Size) :=
  match ptr.provenance with
  | none => .error .danglingInteger
  | some (.concrete aid _) =>
    match mach.lookupBaseAddr aid with
    | some b =>
      if b ≤ ptr.offset.bytes then .ok (aid, Miri.ABI.Size.ofBytes (ptr.offset.bytes - b))
      else .error (.other (.unsupported "vtable pointer below its allocation base"))
    | none => .error (.other (.unsupported "vtable pointer into an unknown allocation"))
  | some .wildcard => .error (.other (.unsupported "wildcard vtable pointer"))

/-- Vendored symbolic-vtable read hooks over the captured table `vts`. -/
def dvVTableReadHooks (vts : List CapturedVTable) :
    Miri.Interpreter.VTableReadHooks AnnealProv AnnealStepState Unit :=
  { resolvePointer := fun _ ptr => do return dvResolveVtPtr (← get).machine ptr
    globalVTable := fun _ aid => pure (dvRegistryLookup (dvRegistry vts) aid)
    predicates := fun _ n => pure #[{ id := n, stableKey := n, autoTrait := false }]
    normalizePredicate := fun _ p => pure p.stableKey
    layoutOf := fun _ ty =>
      match dvVTableOfConcreteTyId? vts ty with
      | some v => pure (dvConcreteLayout vts v)
      | none => throw (.unsupported "layout of a type without a captured vtable") }

/-- Captured vtable of `(concrete TyId, trait id)`. -/
def dvVTableFor? (vts : List CapturedVTable) (principal : Option Nat) (ty : Miri.MIR.TyId) :
    Option CapturedVTable :=
  match principal, dvConcreteOfTyId? vts ty with
  | some p, some cty =>
    match dvKeyOfIdx? vts p with
    | some k => lookupVTableFor vts cty k
    | none => none
  | _, _ => none

/-- Root pointer of a vtable allocation (cached base address, root tag). -/
def dvVtRootPointer (mach : AnnealMachine) (aid : Miri.Memory.AllocId) :
    Option (Miri.Memory.Pointer (Option AnnealProv)) :=
  (mach.lookupBaseAddr aid).map fun b => ⟨Miri.ABI.Size.ofBytes b, some (.concrete aid .one)⟩

/-- Full vendored `VTableHooks` over the captured table `vts`. -/
def dvVTableHooks (vts : List CapturedVTable) :
    Miri.Interpreter.VTableHooks AnnealProv AnnealStepState Unit Miri.Interpreter.CallInstance
      (Miri.ABI.FnAbi Miri.MIR.TyId) :=
  let rh := dvVTableReadHooks vts
  { target := annealTargetDataLayout
    isDynamic := fun _ ty => pure (dvDynTailIdx? ty).isSome
    memoryOffset := fun _ mp _ _ md => pure { mp with metadata := md }
    resolvePointer := rh.resolvePointer
    globalVTable := rh.globalVTable
    globalFunction := fun _ _ => pure none
    predicates := rh.predicates
    normalizePredicate := rh.normalizePredicate
    layoutOf := rh.layoutOf
    eraseAndAnonymize := fun _ ty d => pure (ty, d)
    ensureMonomorphicType := fun _ _ => pure ()
    ensureMonomorphicDyn := fun _ _ => pure ()
    globalSalt := fun _ => pure 0
    reserveVTable := fun _ ty d salt =>
      match dvRegistryReserve (dvRegistry vts) ty d salt with
      | some aid => pure aid
      | none => throw (.unsupported "uncaptured (concrete type, trait object) vtable")
    globalRootPointer := fun _ aid => do
      match dvVtRootPointer (← get).machine aid with
      | some p => pure p
      | none => throw (.unsupported "vtable allocation without a base address")
    entries := fun _ principal ty =>
      match dvVTableFor? vts principal ty with
      | some v => pure (dvVTableEntries vts v)
      | none => throw (.unsupported "uncaptured vtable entries")
    assertVirtualInstanceMatches := fun _ _ _ _ _ => pure () }

/-- `TraitVPtr` slot of the target trait in the source trait's vtable layout
(`supertrait_vtable_slot`); `none` for a primary-prefix supertrait. -/
def dvSupertraitSlot (vts : List CapturedVTable) (srcTail tgtTail : Miri.MIR.TyId) : Option Nat :=
  match dvDynTailIdx? srcTail, dvDynTailIdx? tgtTail with
  | some si, some ti =>
    match dvKeyOfIdx? vts si, dvKeyOfIdx? vts ti with
    | some sk, some tk =>
      match vts.find? (fun v => stringEq v.dynKey sk) with
      | some v =>
        v.slots.findIdx? fun
          | .traitVPtr vid =>
            match lookupVTableById vts vid with
            | some w => stringEq w.dynKey tk
            | none => false
          | _ => false
      | none => none
    | _, _ => none
  | _, _ => none

/-- Vendored `DynamicLayoutHooks` for trait-object pointees: `dyn K` tails
classify as `.dynamic`, and their size/alignment come from vendored
`VTable.getSizeAndAlignRead`. -/
def dvDynamicLayoutHooks (vts : List CapturedVTable) :
    Miri.Interpreter.DynamicLayoutHooks AnnealProv AnnealStepState Unit :=
  { target := annealTargetDataLayout
    maxSizeOfVal := Miri.ABI.Size.ofBytes (UInt64.ofNat (2 ^ 63 - 1))
    classify := fun _ ty =>
      match dvDynTailIdx? ty with
      | some i => pure (.dynamic i)
      | none => throw (.unsupported "dynamic layout of a non-dyn type")
    field := fun _ _ _ => throw (.unsupported "dynamic layout field")
    packedAlign := fun _ _ => pure none
    vtableSizeAndAlign := fun c ptr exp =>
      Miri.Interpreter.VTable.getSizeAndAlignRead (dvVTableReadHooks vts) c ptr exp }

/-- Validity of a trait-object wide pointer `imm` of type `*dyn K` / `&dyn K`
(trait id `keyIdx`): the metadata must be a vtable for `K` (vendored
`VTable.getPtrVTableTypeRead`); for a safe reference the concrete type must be
inhabited (`kani#5216`), the data pointer must be dereferenceable for the
dynamic size (vendored `DynamicLayout.sizeAndAlignFromMeta` +
`Memory.checkPtrAccess`), non-null and aligned (Miri `check_safe_pointer`).
When `checkTB = true` (reference unsizing and virtual-call entry under Tree
Borrows), a vendored Tree Borrows permission check (`npApplyTreeBorrowsReadAt`
for shared, `npApplyTreeBorrowsWriteAt` for mutable) is also performed; safe
`size_of_val(&dyn)` and `&raw const (*r)` pass `checkTB = false` (`C5`). -/
def dvValidateDynPtr (vts : List CapturedVTable) (isRef : Bool) (keyIdx : Nat)
    (imm : Miri.Interpreter.Immediate AnnealProv) (checkTB : Bool := false)
    (isMut : Bool := false) : Miri.Interpreter.RvalueM AnnealStepState Unit := do
  let .scalarPair dataSc metaSc := imm
    | throw (.undefinedBehavior "invalid wide pointer value for a trait object")
  let vptr ← match metaSc.toPointer annealTargetDataLayout with
    | .ok p => pure p
    | .error e => throw (Miri.Interpreter.ScalarOps.scalarError e)
  let concreteTy ← Miri.Interpreter.VTable.getPtrVTableTypeRead (dvVTableReadHooks vts) () vptr (some keyIdx)
  if isRef then
    let concreteLay ← (dvVTableReadHooks vts).layoutOf () concreteTy
    if concreteLay.layout.uninhabited then
      throw (.undefinedBehavior "uninhabited reference to a trait object")
    let dataPtr ← match dataSc.toPointer annealTargetDataLayout with
      | .ok p => pure p
      | .error e => throw (Miri.Interpreter.ScalarOps.scalarError e)
    let some (size, align) ← Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta
        (dvDynamicLayoutHooks vts) () 4 (.metadata metaSc) (dvDynLayout (dvDynTailBase + keyIdx))
      | throw (.unsupported "extern type behind a trait object")
    let st ← get
    match Miri.Memory.checkPtrAccess annealPointerArithmetic dataPtr size
        (.dereferenceable "pointer") (annealResolvePtr st.machine) (annealLookupAlloc st.machine) with
    | .error _ => throw (.undefinedBehavior "dangling reference to a trait object")
    | .ok () =>
      if dataPtr.offset.bytes == 0 then throw (.undefinedBehavior "null reference to a trait object")
      match dataPtr.offset.isAligned align with
      | .ok true =>
        if checkTB then
          let st' ← get
          let tbRes :=
            if isMut then npApplyTreeBorrowsWriteAt dataPtr.provenance dataPtr.offset.bytes size st'
            else npApplyTreeBorrowsReadAt dataPtr.provenance dataPtr.offset.bytes size st'
          match tbRes with
          | .ok st'' => set st''
          | .error e => throw e
        else pure ()
      | .ok false => throw (.undefinedBehavior "misaligned reference to a trait object")
      | .error _ => throw (.invalidProgram "invalid alignment")

/-! ### Active-statement classification (`dyn` operations) -/

/-- The statement / terminator of `currentBody` at the active location of `st`. -/
def dvActiveSite? (currentBody : CapturedMir) (st : AnnealStepState) :
    Option (Option Statement × Terminator) :=
  match st.stack.currentFrame? with
  | some frame =>
    match frame.location with
    | .mir loc =>
      match get? currentBody.basicBlocks loc.block with
      | some bb => some (get? bb.statements loc.statementIndex, bb.terminator)
      | none => none
    | .unwinding _ => none
  | none => none

/-- Whether `k` is a trait-object type. -/
def dvIsDynTy : RigidTy → Bool
  | .dynamic _ => true
  | _ => false

/-- Whether `k` is a pointer / reference to a trait object. -/
def dvIsDynPtrTy : RigidTy → Bool
  | .ref _ (.dynamic _) | .rawPtr _ (.dynamic _) => true
  | _ => false

/-- Whether the place is `(*p)` (a single dereference) of a `dyn` pointer local. -/
def dvIsDerefOfDynPtr (decls : List LocalDecl) (p : Place) : Bool :=
  match p.projection with
  | [.deref] =>
    match get? decls p.local_ with
    | some d => dvIsDynPtrTy d.ty.kind
    | none => false
  | _ => false

/-- Whether the place is a bare dereference `(*p)`. -/
def dvIsPureDeref (p : Place) : Bool :=
  match p.projection with
  | [.deref] => true
  | _ => false

/-- `dyn` rvalues: `Unsize` coercions to a `dyn` / `Pin<&dyn>` / unmodeled
`CoerceUnsized` target, casts, comparisons and raw borrows of `dyn` pointers. -/
def dvRvalueIsDynOp (decls : List LocalDecl) (layouts : LayoutTable) : Rvalue → Bool
  | .cast (.pointerCoercion ck) _ targetTy =>
    stringEq ck "Unsize" && (dynUnsizeTarget? targetTy.kind).isSome
  | .cast _ op _ =>
    match operandTy decls layouts op with
    | some t => dvIsDynPtrTy t.kind
    | none => false
  | .binaryOp _ a _ =>
    match operandTy decls layouts a with
    | some t => dvIsDynPtrTy t.kind
    | none => false
  | .rawPtr _ p => dvIsDerefOfDynPtr decls p
  | _ => false

/-- `dyn` statements (plus, in Tree Borrows mode, assignments through a bare
dereference, which the receiver call protector observes). -/
def dvStmtIsDynOp (treeBorrows : Bool) (decls : List LocalDecl) (layouts : LayoutTable)
    (s : Statement) : Bool :=
  match s.kind with
  | .assign p rv => dvRvalueIsDynOp decls layouts rv || (treeBorrows && dvIsPureDeref p)
  | _ => false

/-- `dyn` calls: a function item instantiated at a trait-object type argument
(virtual methods, `size_of_val::<dyn _>`, `addr_eq::<dyn _, dyn _>`). -/
def dvTermIsDynOp (decls : List LocalDecl) (layouts : LayoutTable) (t : Terminator) : Bool :=
  match t.kind with
  | .call func _ _ _ _ =>
    match operandTy decls layouts func with
    | some { kind := .fnDef _ tys, .. } => tys.any dvIsDynTy
    | _ => false
  | _ => false

/-- Whether the active statement (or terminator) of `st` is a `dyn` operation. -/
def dvIsDynOpAt (currentBody : CapturedMir) (treeBorrows : Bool) (st : AnnealStepState) : Bool :=
  match dvActiveSite? currentBody st with
  | some (some s, _) => dvStmtIsDynOp treeBorrows currentBody.localDecls currentBody.layouts s
  | some (none, t) => dvTermIsDynOp currentBody.localDecls currentBody.layouts t
  | none => false

/-- The `(source tail, target tail)` of the active `Unsize` coercion: the
operand's pointee (a `dyn` tail or a concrete vtable type) and the target's
`dyn` pointee. -/
def dvActiveUnsizeTails? (currentBody : CapturedMir) (st : AnnealStepState) :
    Option (Miri.MIR.TyId × Miri.MIR.TyId) :=
  let vts := currentBody.vtables
  match dvActiveSite? currentBody st with
  | some (some { kind := .assign _ (.cast (.pointerCoercion _) op targetTy), .. }, _) =>
    let srcPointee? : Option RigidTy :=
      match operandTy currentBody.localDecls currentBody.layouts op with
      | some { kind := .ref _ p, .. } | some { kind := .rawPtr _ p, .. } => some p
      | _ => none
    let tgtKey? : Option DefPath :=
      match targetTy.kind with
      | .ref _ (.dynamic k) | .rawPtr _ (.dynamic k) => some k
      | _ => none
    match srcPointee?, tgtKey? with
    | some (.dynamic sk), some tk => some (dvDynTailTyId vts sk, dvDynTailTyId vts tk)
    | some p, some tk => some (dvConcreteTyId vts p, dvDynTailTyId vts tk)
    | _, _ => none
  | _ => none

/-- The reference-ness, mutability, and trait-object key of the active statement's
destination (`&[mut] dyn K` / `*[const|mut] dyn K` target of a cast). -/
def dvActiveDynTarget? (currentBody : CapturedMir) (st : AnnealStepState) :
    Option (Bool × Bool × DefPath) :=
  match dvActiveSite? currentBody st with
  | some (some { kind := .assign _ (.cast _ _ targetTy), .. }, _) =>
    match targetTy.kind with
    | .ref .not (.dynamic k) => some (true, false, k)
    | .ref .mut (.dynamic k) => some (true, true, k)
    | .rawPtr .not (.dynamic k) => some (false, false, k)
    | .rawPtr .mut (.dynamic k) => some (false, true, k)
    | _ => none
  | _ => none

/-- Whether the active statement is a mutable raw borrow (`&raw mut _`). -/
def dvActiveRawBorrowIsMut (currentBody : CapturedMir) (st : AnnealStepState) : Bool :=
  match dvActiveSite? currentBody st with
  | some (some { kind := .assign _ (.rawPtr .mut _), .. }, _) => true
  | _ => false

/-- The trait-object key of the active cast's `*dyn K` / `&dyn K` operand. -/
def dvActiveCastSrcKey? (currentBody : CapturedMir) (st : AnnealStepState) : Option DefPath :=
  match dvActiveSite? currentBody st with
  | some (some { kind := .assign _ (.cast _ op _), .. }, _) =>
    match operandTy currentBody.localDecls currentBody.layouts op with
    | some { kind := .ref _ (.dynamic k), .. } | some { kind := .rawPtr _ (.dynamic k), .. } => some k
    | _ => none
  | _ => none

/-! ### Cast, rvalue and assignment leaves -/

/-- `CastHooks` overlay extending `annealCastHooksNullaryPtr` with the leaves of
the `dyn` arms of vendored `Cast.unsizeInto` / `unsizeIntoPointer` / `ptrToPtr`. -/
def annealCastHooksDynTraitVTable (currentBody : CapturedMir) (fnPtrs : List FnPtrEntry := .nil)
    (treeBorrows : Bool := false) :
    Miri.Interpreter.CastHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealCastHooksNullaryPtr currentBody fnPtrs treeBorrows
  let vts := currentBody.vtables
  let vh := dvVTableHooks vts
  { base with
    typeInfo := fun c tyId =>
      if tyId == wideRawDynPtrTyId then pure (.rawPointer dynPointeeTyId)
      else if tyId == wideSafeDynRefTyId then pure (.reference dynPointeeTyId)
      else
        match dvDynTailIdx? tyId with
        | some i => pure (.dynamic i)
        | none =>
          match dvConcreteOfTyId? vts tyId with
          | some .never | some (.adt _ _) => pure (.adt 0)
          | some cty => base.typeInfo c (encodeTyIdOverlay { kind := cty, layoutIdx := 0 })
          | none => base.typeInfo c tyId
    lockstepTails := fun _ _ _ => do
      match dvActiveUnsizeTails? currentBody (← get) with
      | some p => pure p
      | none => throw (.unsupported "Unsize outside the modeled dyn fragment")
    vtableType := fun c ptr exp => Miri.Interpreter.VTable.getPtrVTableType vh c ptr exp
    vtablePointer := fun c ty d => Miri.Interpreter.VTable.getPointer vh c ty d
    principal := fun _ n => pure (some n)
    vtableEntries := fun c p ty => vh.entries c p ty
    supertraitSlot := fun _ s t => pure (dvSupertraitSlot vts s t)
    eraseSelfTraitRef := fun _ r => pure r
    normalizePrincipal := fun _ n => pure (some n)
    derefPointer := fun c op => do
      if op.layout.ty == wideRawDynPtrTyId then
        match dvActiveCastSrcKey? currentBody (← get) with
        | some k =>
          let imm ← annealReadImmediateOverlay op
          dvValidateDynPtr vts false (dvKeyIdx vts k) imm.imm
        | none => throw (.unsupported "dyn pointer cast source without a dyn type")
      else base.derefPointer c op
    validatePlace := fun c dest r b => do
      if dest.layout.ty == wideRawDynPtrTyId || dest.layout.ty == wideSafeDynRefTyId then
        let st ← get
        let some (isRef, isMut, k) := dvActiveDynTarget? currentBody st
          | throw (.unsupported "dyn validity outside a dyn cast")
        let some frame := st.stack.currentFrame? | throw (.stack .emptyStack)
        let op : Miri.Interpreter.Operand AnnealProv ←
          match dest.ref with
          | .local _ localId none _ =>
            match frame.getLocalOperand localId with
            | .ok opVal => pure opVal
            | .error (.localExpectedLive _) => throw (.undefinedBehavior "read of dead local")
            | .error e => throw (.stack e)
          | .memory mp => pure (.indirect mp)
          | .local _ _ (some _) _ => throw (.unsupported "projected dyn validity")
        let imm ← annealReadImmediateOverlay ⟨op, dest.layout⟩
        dvValidateDynPtr vts isRef (dvKeyIdx vts k) imm.imm (treeBorrows && isRef) isMut
      else base.validatePlace c dest r b }

/-- `(isRef, isMutSrc, dynKey)` of `(*_k)` when `_k` is a `&[mut] dyn K` or
`*[const|mut] dyn K` local of `currentBody`. -/
def dvDerefDynPlace? (currentBody : CapturedMir) (p : Miri.MIR.Place) :
    Option (Bool × Bool × DefPath) :=
  if p.projection.toList == [.Deref] then
    match get? currentBody.localDecls p.localId with
    | some d =>
      match d.ty.kind with
      | .ref .not (.dynamic k) => some (true, false, k)
      | .ref .mut (.dynamic k) => some (true, true, k)
      | .rawPtr .not (.dynamic k) => some (false, false, k)
      | .rawPtr .mut (.dynamic k) => some (false, true, k)
      | _ => none
    | none => none
  else none

/-- `ScalarOpsHooks` classifying `dyn` wide pointers as pointers, so that
vendored `ScalarOps.binary` dispatches their comparisons to vendored
`ExecutionScalar.pointerBinary` (lexicographic `(data, vtable)` order). -/
def dvScalarOpsHooks (localDecls : List LocalDecl) (layouts : LayoutTable) :
    Miri.Interpreter.ScalarOpsHooks AnnealProv AnnealStepState Unit :=
  let base := annealScalarOpsHooks localDecls layouts
  { base with
    classify := fun c tyId =>
      if tyId == wideRawDynPtrTyId || tyId == wideSafeDynRefTyId then pure .pointer
      else base.classify c tyId }

/-- `RvalueHooks` overlay: `Unsize` and pointer-to-pointer casts of `dyn`
statements run vendored `Cast.cast` over `annealCastHooksDynTraitVTable`. -/
def annealRvalueHooksDynTraitVTable (currentBody : CapturedMir) (fnPtrs : List FnPtrEntry := .nil)
    (treeBorrows : Bool := false) :
    Miri.Interpreter.RvalueHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealRvalueHooksNullaryPtr currentBody fnPtrs treeBorrows
  let vts := currentBody.vtables
  { base with
    evalPlace := fun c p skip => do
      match dvDerefDynPlace? currentBody p with
      | some (isRef, isMutSrc, k) =>
        let st ← get
        if dvActiveRawBorrowIsMut currentBody st && !isMutSrc then
          throw (.unsupported "mutable raw borrow of immutable dyn pointer")
        let some frame := st.stack.currentFrame? | throw (.stack .emptyStack)
        let op ← match frame.getLocalOperand p.localId with
          | .ok o => pure o
          | .error (.localExpectedLive _) => throw (.undefinedBehavior "read of dead local")
          | .error e => throw (.stack e)
        let lay := (lookupLocalDeclLayout currentBody.localDecls currentBody.layouts p.localId).getD
          (translateTyOverlay dvU32Ty)
        let imm ← annealReadImmediateOverlay ⟨op, lay⟩
        if isRef then dvValidateDynPtr vts true (dvKeyIdx vts k) imm.imm false false
        match imm.imm with
        | .scalarPair d m =>
          match d.toPointer annealTargetDataLayout with
          | .ok ptr =>
            pure { ref := .memory ⟨ptr, .metadata m, none⟩, layout := dvDynLayout (dvDynTailTyId vts k) }
          | .error e => throw (Miri.Interpreter.ScalarOps.scalarError e)
        | _ => throw (.undefinedBehavior "invalid trait-object pointer value")
      | none => base.evalPlace c p skip
    binaryOp := fun c op l r =>
      Miri.Interpreter.ScalarOps.binary (dvScalarOpsHooks currentBody.localDecls currentBody.layouts) c op l r
    cast := fun c src kind ty dest =>
      match kind with
      | .PointerCoercion .Unsize _ | .PtrToPtr =>
        Miri.Interpreter.Cast.cast (annealCastHooksDynTraitVTable currentBody fnPtrs treeBorrows)
          c 16 src kind dest.layout.ty dest
      | _ => base.cast c src kind ty dest }

/-- Tree Borrows write through a bare dereference destination `(*p)` (the
access a receiver call protector guards), backed by `npApplyTreeBorrowsWriteAt`
(vendored `Tree.LocationState.performAccess`). -/
def dvTreeBorrowsDerefWrite (currentBody : CapturedMir) (place : Miri.MIR.Place)
    (state : AnnealStepState) : Except Miri.Interpreter.StepError AnnealStepState :=
  match npEvalPlaceNullaryPtr currentBody.localDecls currentBody.layouts place true state with
  | .error _ _ => .ok state
  | .ok rp _ =>
    match rp.ref with
    | .memory mp => npApplyTreeBorrowsWriteAt mp.ptr.provenance mp.ptr.offset.bytes rp.layout.layout.size state
    | _ => .ok state


/-! ### Call leaves: virtual dispatch, `size_of_val` / `align_of_val`, linked instances -/

/-- The callee path, generic type arguments and argument operands of the active
call terminator of `currentBody`. -/
def dvActiveCall? (currentBody : CapturedMir) (st : AnnealStepState) :
    Option (DefPath × List RigidTy × List Operand) :=
  match dvActiveSite? currentBody st with
  | some (none, { kind := .call func args _ _ _, .. }) =>
    match operandTy currentBody.localDecls currentBody.layouts func with
    | some { kind := .fnDef path tys, .. } => some (path, tys, args)
    | _ => none
  | _ => none

/-- The first trait-object type argument. -/
def dvFirstDynKey? : List RigidTy → Option DefPath
  | [] => none
  | .dynamic k :: _ => some k
  | _ :: rest => dvFirstDynKey? rest

/-- The `InstanceKind::Virtual` record of `(path, key)` and its index. -/
def dvVirtualIdx? (vms : List CapturedVirtualMethod) (path key : DefPath) :
    Option (CapturedVirtualMethod × Nat) :=
  match vms.findIdx? (fun m => stringEq m.methodDefPath path && stringEq m.dynKey key) with
  | some i => (vms[i]?).map fun m => (m, i)
  | none => none

/-- Compiler leaves of vendored `VirtualCalls.resolveVirtual` over the captured
tables (`recvIdx` is the trait id of the receiver's `dyn` type argument). -/
def dvVirtualCompilerHooks (vts : List CapturedVTable) (vms : List CapturedVirtualMethod)
    (recvIdx : Nat) : Miri.Interpreter.VirtualCalls.CompilerHooks AnnealStepState Unit :=
  { classifyReceiver := fun ty =>
      pure (if ty == wideSafeDynRefTyId then .reference
        else if ty == wideRawDynPtrTyId then .rawPointer
        else if (dvDynTailIdx? ty).isSome then .dynamic else .other)
    fieldLayout := fun _ _ => throw (.unsupported "DispatchFromDyn receiver field layout")
    structTailForCodegen := fun ty => pure ty
    dynamicData := fun ty => pure ((dvDynTailIdx? ty).map fun i => { predicates := i, principal := some i })
    mutPointerType := fun ty =>
      match dvConcreteOfTyId? vts ty with
      | some cty => pure (encodeTyIdOverlay { kind := .rawPtr .mut cty, layoutIdx := 0 })
      | none => throw (.unsupported "receiver pointer type of an uncaptured concrete type")
    mutReferenceType := fun _ => throw (.unsupported "dyn drop receiver")
    builtinDeref := fun ty =>
      pure (if ty == wideSafeDynRefTyId || ty == wideRawDynPtrTyId then some (dvDynTailBase + recvIdx)
        else none)
    layoutOf := fun ty =>
      match dvDynTailIdx? ty with
      | some _ => pure (dvDynLayout ty)
      | none =>
        match dvVTableOfConcreteTyId? vts ty with
        | some v => pure (dvConcreteLayout vts v)
        | none => pure (layoutOfEncodedTyIdOverlay ty)
    parentTrait := fun d =>
      match (if dvVirtualBase ≤ d then vms[d - dvVirtualBase]? else none) with
      | some m => pure (dvKeyIdx vts m.dynKey)
      | none => throw (.invalidProgram "virtual method without a captured record")
    rebaseVirtualArgs := fun _ _ dynTy => pure #[.Type dynTy]
    expectResolveForVTable := fun _ d args =>
      match (if dvVirtualBase ≤ d then vms[d - dvVirtualBase]? else none), args[0]? with
      | some m, some (Miri.MIR.GenericArg.Type ty) =>
        match dvVTableFor? vts (some (dvKeyIdx vts m.dynKey)) ty with
        | some v =>
          match get? v.slots m.slotIdx with
          | some (.method p _) => pure (dvMethodInstance vts p)
          | _ => throw (.invalidProgram "virtual record slot is not a method")
        | none => throw (.unsupported "uncaptured vtable for the receiver type")
      | _, _ => throw (.invalidProgram "virtual instance without a receiver type")
    resolveDropGlue := fun _ => throw (.unsupported "dyn drop glue")
    requiresCallerLocation := fun _ => pure false
    sourceScope := fun _ _ _ _ => throw (.unsupported "caller location scope")
    unitLayout := pure (translateTyOverlay { kind := .tuple [], layoutIdx := 0 }) }

/-- Vendored `VirtualCalls.Hooks` over the captured tables. -/
def dvVirtualHooks (vts : List CapturedVTable) (vms : List CapturedVirtualMethod) (recvIdx : Nat) :
    Miri.Interpreter.VirtualCalls.Hooks AnnealProv AnnealStepState Unit Unit :=
  let compiler := dvVirtualCompilerHooks vts vms recvIdx
  { debugAssertions := false
    compiler
    target := annealTargetDataLayout
    vtable := dvVTableHooks vts
    getFrame := do
      match (← get).stack.currentFrame? with
      | some f => pure f
      | none => throw (.stack .emptyStack)
    readImmediate := fun _ op => annealReadImmediateOverlay op
    immPtrToMPlace := fun _ v =>
      Miri.Interpreter.VirtualCalls.pointerPlace compiler annealTargetDataLayout (fun _ _ => pure none) v
    projectField := fun _ _ _ => throw (.unsupported "DispatchFromDyn receiver projection") }

/-- Function-entry validity of a thin `&T` argument (`T` sized with layout
`lay`): dereferenceable, non-null, aligned (Miri validates reference arguments
when it initializes the callee frame). -/
def dvValidateThinRef (sc : Miri.Memory.Scalar AnnealProv) (lay : Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState Unit := do
  let ptr ← match sc.toPointer annealTargetDataLayout with
    | .ok p => pure p
    | .error e => throw (Miri.Interpreter.ScalarOps.scalarError e)
  let st ← get
  match Miri.Memory.checkPtrAccess annealPointerArithmetic ptr lay.layout.size
      (.dereferenceable "pointer") (annealResolvePtr st.machine) (annealLookupAlloc st.machine) with
  | .error _ => throw (.undefinedBehavior "dangling reference argument")
  | .ok () =>
    match ptr.offset.isAligned lay.layout.align.abi with
    | .ok true => pure ()
    | .ok false => throw (.undefinedBehavior "misaligned reference argument")
    | .error _ => throw (.invalidProgram "invalid alignment")

/-- Function-entry retag of a receiver reborrow under Tree Borrows: inserts into
the vendored `BorrowTree` a child of `parent` with the fresh tag `child`,
initial permission `perm` (`Frozen` for `&Self`, `ReservedFrz false` for
`&mut Self`) and accessed on every tracked location, under the parent node.
`none` when `parent` is not tracked. -/
def dvRetagChild (tree : Miri.TreeBorrows.BorrowTree) (parent child : Miri.Memory.BorTag)
    (perm : Miri.TreeBorrows.Permission := .Frozen) :
    Option Miri.TreeBorrows.BorrowTree :=
  match tree.tagMapping.get parent with
  | none => none
  | some pIdx =>
    match tree.nodes.get pIdx with
    | none => none
    | some pNode =>
      let cIdx : Miri.TreeBorrows.UniIndex := ⟨UInt32.ofNat tree.nodes.data.size⟩
      let nodes := (tree.nodes.insert pIdx { pNode with children := pNode.children.push cIdx }).insert
        cIdx { tag := child, parent := some pIdx, children := #[],
               defaultInitialPermission := perm, defaultInitialSifa := .None }
      let locations := { tree.locations with
        entries := tree.locations.entries.map fun seg =>
          { seg with data := { seg.data with perms := seg.data.perms.insert cIdx ⟨perm, true, .None⟩ } } }
      some { tree with
        tagMapping := { tree.tagMapping with mapping := tree.tagMapping.mapping.push (child, cIdx) },
        nodes, locations }

/-- Backwards-compatible alias for `dvRetagChild` with `.Frozen`. -/
abbrev dvRetagFrozenChild (tree : Miri.TreeBorrows.BorrowTree) (parent child : Miri.Memory.BorTag) :
    Option Miri.TreeBorrows.BorrowTree :=
  dvRetagChild tree parent child .Frozen

/-- Under Tree Borrows, the callee's function-entry retag of a `&Self` /
`&mut Self` receiver (Miri `FnEntry` retag of a reference argument): a fresh
child tag (`Frozen` for shared, `ReservedFrz false` for mutable) of the
receiver's tag, protected by a `StrongProtector` (the active call protector);
the receiver pointer carries the new tag. Untracked receivers are unchanged. -/
def dvRetagReceiver (sc : Miri.Memory.Scalar AnnealProv) (isMut : Bool := false) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Memory.Scalar AnnealProv) := do
  let st ← get
  match sc.toPointer annealTargetDataLayout with
  | .ok ptr =>
    match ptr.provenance, st.machine.borrowTracker with
    | some (.concrete aid tag), some bt =>
      match st.machine.memory.live.findIdx? (fun e => e.1 == aid) with
      | some lIdx =>
        match st.machine.memory.live[lIdx]? with
        | some (_, la) =>
          match la.allocation.extra with
          | some tree =>
            let fresh : UInt64 :=
              tree.tagMapping.mapping.foldl (fun m e => max m e.1.value) 0 + 1
            if h : fresh ≠ 0 then
              let child : Miri.Memory.BorTag := ⟨fresh, h⟩
              let perm : Miri.TreeBorrows.Permission := if isMut then .ReservedFrz false else .Frozen
              match dvRetagChild tree tag child perm with
              | some tree' =>
                set { st with machine := { (updateAllocMachine st.machine lIdx aid la.kind
                        (la.allocation.setExtra (some tree'))) with
                      borrowTracker := some { bt with global := { bt.global with
                        protectedTags := bt.global.protectedTags.insert child .StrongProtector } } } }
                pure (Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨ptr.offset, .concrete aid child⟩)
              | none => pure sc
            else pure sc
          | none => pure sc
        | none => pure sc
      | none => pure sc
    | _, _ => pure sc
  | .error _ => pure sc

/-- Caller-side `FnAbi` of a call with evaluated arguments `argImms`. -/
def dvCallerAbi (argImms : List (Miri.Interpreter.RvalueImmTy AnnealProv))
    (ret : Miri.Interpreter.LocalLayout) : Miri.ABI.FnAbi Miri.MIR.TyId :=
  { args := (argImms.map fun a => { layout := a.layout, mode := .Direct .new }).toArray
    ret := { layout := ret, mode := .Direct .new }
    cVariadic := false, fixedCount := UInt32.ofNat argImms.length, conv := .Rust, canUnwind := true }

/-- Virtual method call (`InstanceKind::Virtual(def, slot)`): evaluate the
arguments (`kani#5172` uninit check first), resolve the receiver and the
concrete instance through vendored `VirtualCalls.resolveVirtual` (receiver
unwrapping, `VTable.getPtrVTableType` with `checkForType`, `entries[slot]`
method selection, instance assertion, thin receiver), validate safe-reference
receivers (including `kani#5216` inhabitedness and Tree Borrows permissions)
**before** looking up the linked callee (`C3`), and push the linked concrete
callee frame (`annealPushCalleeFrameLM4_1`) with function-entry receiver
protector retag (`C4`). -/
def dvEvalVirtualCall (currentBody : CapturedMir) (callees : List CapturedMir) (treeBorrows : Bool)
    (m : CapturedVirtualMethod) (mIdx : Nat) (recvKey : DefPath) (args : List Operand)
    (dest : Miri.MIR.Place) (target : Option Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction)
    (state : AnnealStepState) : Miri.Interpreter.StepResult AnnealStepState Unit :=
  let vts := currentBody.vtables
  let recvIdx := dvKeyIdx vts recvKey
  let h := dvVirtualHooks vts currentBody.virtualMethods recvIdx
  let action : Miri.Interpreter.CallM AnnealStepState
      (CapturedMir × List (Miri.Interpreter.RvalueImmTy AnnealProv)) := do
    let argImms ← annealEvalCallArgsLM4_1 currentBody.localDecls currentBody.layouts
      (args.map translateOperand)
    let fnArgs : Array (Miri.Interpreter.FnArg AnnealProv) :=
      (argImms.map fun a => Miri.Interpreter.FnArg.Copy ⟨.immediate a.imm, a.layout⟩).toArray
    let retLay := (lookupLocalDeclLayout currentBody.localDecls currentBody.layouts dest.localId).getD
      (translateTyOverlay dvU32Ty)
    let virtInst : Miri.Interpreter.CallInstance :=
      { kind := .Virtual (dvVirtualBase + mIdx) m.slotIdx, args := #[.Type (dvDynTailBase + recvIdx)] }
    let (inst, _, fnArgs') ← Miri.Interpreter.VirtualCalls.resolveVirtual h () 4 virtInst
      (dvVirtualBase + mIdx) m.slotIdx (dvCallerAbi argImms retLay) fnArgs
    let some path := dvMethodOfInstance? vts inst
      | throw (.invalidProgram "virtual dispatch selected a non-method instance")
    -- Pre-lookup safe-reference receiver gate (C3): validate dereferenceability,
    -- alignment, non-null, inhabitedness (`kani#5216`), and Tree Borrows parent
    -- permissions *before* checking whether `calleeBody` is linked.
    match args.head?, argImms.head? with
    | some recvOp, some recvWide =>
      match operandTy currentBody.localDecls currentBody.layouts recvOp with
      | some { kind := .ref mutb (.dynamic _), .. } =>
        let isMutRecv : Bool := match mutb with | .mut => true | .not => false
        dvValidateDynPtr vts true recvIdx recvWide.imm treeBorrows isMutRecv
      | _ => pure ()
    | _, _ => pure ()
    let some calleeBody := findCallee? callees path
      | throw (.unsupported "unlinked concrete virtual callee")
    let some recvArg := fnArgs'[0]? | throw (.invalidProgram "virtual receiver disappeared")
    let recvImm ← annealReadImmediateOverlay recvArg.copyFnArg
    let paramTy? := (get? calleeBody.localDecls 1).map (·.ty)
    let paramLay := match paramTy? with
      | some t => translateTyOverlay t calleeBody.layouts
      | none => recvImm.layout
    let recv ← match (paramTy?.map (·.kind) : Option RigidTy), recvImm.imm with
      | some (RigidTy.ref .not pointee), .scalar sc =>
        dvValidateThinRef sc (translateTyOverlay { kind := pointee, layoutIdx := 0 } calleeBody.layouts)
        if treeBorrows then pure (Miri.Interpreter.Immediate.scalar (← dvRetagReceiver sc false))
        else pure recvImm.imm
      | some (RigidTy.ref .mut pointee), .scalar sc =>
        dvValidateThinRef sc (translateTyOverlay { kind := pointee, layoutIdx := 0 } calleeBody.layouts)
        if treeBorrows then pure (Miri.Interpreter.Immediate.scalar (← dvRetagReceiver sc true))
        else pure recvImm.imm
      | _, _ => pure recvImm.imm
    pure (calleeBody, ⟨recv, paramLay⟩ :: argImms.drop 1)
  match Miri.Interpreter.runRvalue action state with
  | (st, .error e) => (st, .error e)
  | (st, .ok (calleeBody, argImms')) =>
    annealPushCalleeFrameLM4_1 currentBody calleeBody dest target unwind argImms' st

/-- 64-bit `usize` scalar. -/
def dvUsizeScalar (n : Nat) : Miri.Memory.Scalar AnnealProv :=
  match Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 n) (Miri.ABI.Size.ofBytes 8) with
  | .ok s => s
  | .error _ => Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨.ZERO, .wildcard⟩

/-- Dynamic `size_of_val` / `align_of_val` on `&dyn K` (`isRef = true`, safe
`core::mem`: validates reference without Tree Borrows read, `C5`) or
`*const dyn K` (`isRef = false`, raw `core::intrinsics`: validates vtable
metadata only), reading size/alignment through vendored
`DynamicLayout.sizeAndAlignFromMeta` (`VTable.getSizeAndAlignRead`). -/
def dvEvalSizeAlignOfVal (currentBody : CapturedMir) (isAlign : Bool) (recvKey : DefPath)
    (args : List Operand) (dest : Miri.MIR.Place) (target : Option Miri.MIR.BasicBlockId)
    (state : AnnealStepState) (isRef : Bool := true) :
    Miri.Interpreter.StepResult AnnealStepState Unit :=
  let vts := currentBody.vtables
  let action : Miri.Interpreter.RvalueM AnnealStepState Unit := do
    let argImms ← annealEvalCallArgsLM4_1 currentBody.localDecls currentBody.layouts
      (args.map translateOperand)
    let some a := argImms.head? | throw (.invalidProgram "size_of_val without an argument")
    dvValidateDynPtr vts isRef (dvKeyIdx vts recvKey) a.imm false false
    let .scalarPair _ metaSc := a.imm | throw (.invalidProgram "thin size_of_val argument")
    let some (size, align) ← Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta
        (dvDynamicLayoutHooks vts) () 4 (.metadata metaSc) (dvDynLayout (dvDynTailTyId vts recvKey))
      | throw (.unsupported "extern type behind a trait object")
    let v ← if isAlign then
        match align.bytesNat with
        | .ok n => pure n
        | .error _ => throw (.invalidProgram "invalid alignment")
      else pure size.bytes.toNat
    let destPlace ← annealEvalPlaceOverlay currentBody.localDecls currentBody.layouts dest
    annealWriteImmediate (.scalar (dvUsizeScalar v)) destPlace
  match Miri.Interpreter.runRvalue action state with
  | (st, .error e) => (st, .error e)
  | (st, .ok ()) => Miri.Interpreter.ControlFlow.returnToBlock target st

/-- A call of a linked monomorphized instance (its body is linked under the
item path, e.g. `core::ptr::addr_eq::<dyn Tr, dyn Alt>`): evaluate the
arguments and push the callee frame. -/
def dvEvalLinkedInstanceCall (currentBody calleeBody : CapturedMir) (args : List Operand)
    (dest : Miri.MIR.Place) (target : Option Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction)
    (state : AnnealStepState) : Miri.Interpreter.StepResult AnnealStepState Unit :=
  match Miri.Interpreter.runRvalue
      (annealEvalCallArgsLM4_1 currentBody.localDecls currentBody.layouts (args.map translateOperand))
      state with
  | (st, .error e) => (st, .error e)
  | (st, .ok argImms) => annealPushCalleeFrameLM4_1 currentBody calleeBody dest target unwind argImms st

/-- The `dyn` call terminator dispatcher. -/
def dvEvalDynCall (currentBody : CapturedMir) (callees : List CapturedMir) (treeBorrows : Bool)
    (term : Miri.MIR.Terminator) (state : AnnealStepState) :
    Miri.Interpreter.StepResult AnnealStepState Unit :=
  match dvActiveCall? currentBody state, term.kind with
  | some (path, tys, args), .Call _ _ dest target unwind _ _ =>
    match dvFirstDynKey? tys with
    | none => (state, .error (.unsupported "call without a trait-object type argument"))
    | some k =>
      match dvVirtualIdx? currentBody.virtualMethods path k with
      | some (m, i) => dvEvalVirtualCall currentBody callees treeBorrows m i k args dest target unwind state
      | none =>
        if stringEq path "core::mem::size_of_val" then
          dvEvalSizeAlignOfVal currentBody false k args dest target state true
        else if stringEq path "core::mem::align_of_val" then
          dvEvalSizeAlignOfVal currentBody true k args dest target state true
        else if stringEq path "core::intrinsics::size_of_val" then
          dvEvalSizeAlignOfVal currentBody false k args dest target state false
        else if stringEq path "core::intrinsics::align_of_val" ||
            stringEq path "core::intrinsics::min_align_of_val" then
          dvEvalSizeAlignOfVal currentBody true k args dest target state false
        else
          match findCallee? callees path with
          | some cb => dvEvalLinkedInstanceCall currentBody cb args dest target unwind state
          | none => (state, .error (.unsupported "unlinked dyn-instantiated callee"))
  | _, _ => (state, .error (.invalidProgram "dyn call site mismatch"))

/-! ### The conservative step-hook overlay -/

/-- Whether the active statement's rvalue is a `dyn` rvalue. -/
def dvActiveRvalueIsDyn (currentBody : CapturedMir) (st : AnnealStepState) : Bool :=
  match dvActiveSite? currentBody st with
  | some (some { kind := .assign _ rv, .. }, _) =>
    dvRvalueIsDynOp currentBody.localDecls currentBody.layouts rv
  | _ => false

/-- `dyn` assignment: the Tree Borrows write of a bare-dereference destination
(`treeBorrows` mode), then the rvalue through `annealRvalueHooksDynTraitVTable`
(for `dyn` rvalues) or the base overlay. -/
def dvAssign (currentBody : CapturedMir) (treeBorrows : Bool) (fnPtrs : List FnPtrEntry)
    (baseAssign : Unit → Miri.MIR.Place → Miri.MIR.Rvalue → AnnealStepState →
      Miri.Interpreter.StepResult AnnealStepState Unit)
    (choice : Unit) (place : Miri.MIR.Place) (rvalue : Miri.MIR.Rvalue) (state : AnnealStepState) :
    Miri.Interpreter.StepResult AnnealStepState Unit :=
  let pre : Except Miri.Interpreter.StepError AnnealStepState :=
    if treeBorrows && place.projection.toList == [.Deref] then
      dvTreeBorrowsDerefWrite currentBody place state
    else .ok state
  match pre with
  | .error e => (state, .error e)
  | .ok state' =>
    if dvActiveRvalueIsDyn currentBody state then
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace
          (annealRvalueHooksDynTraitVTable currentBody fnPtrs treeBorrows) choice rvalue place)
        state'
    else baseAssign choice place rvalue state'

/-- **Conservative `StepHooks` overlay** extending `annealStepHooksNullaryPtr`:
`assign` and `terminator` are replaced only when the active statement /
terminator of `currentBody` is a `dyn` operation (`dvIsDynOpAt`); every other
hook, statement and terminator is the base overlay's. -/
def annealStepHooksDynTraitVTable (currentBody : CapturedMir)
    (treeBorrows : Bool := false)
    (callees : List CapturedMir := .nil)
    (poppedFrame : Miri.TreeBorrows.FrameState := {})
    (fnPtrs : List FnPtrEntry := .nil) :
    Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealStepHooksNullaryPtr currentBody treeBorrows callees poppedFrame fnPtrs
  { base with
    assign := fun choice place rvalue state =>
      if dvIsDynOpAt currentBody treeBorrows state then
        dvAssign currentBody treeBorrows fnPtrs base.assign choice place rvalue state
      else base.assign choice place rvalue state
    terminator := fun choice term state =>
      if dvIsDynOpAt currentBody treeBorrows state then
        dvEvalDynCall currentBody callees treeBorrows term state
      else base.terminator choice term state }

/-- The `CapturedMir` executing in the top frame: the root body in the root
frame, otherwise the linked callee whose translation is the frame's body. -/
def dvActiveBody (root : CapturedMir) (callees : List CapturedMir) (st : AnnealStepState) :
    CapturedMir :=
  if st.stack.frames.size ≤ 1 then root
  else
    match st.stack.currentFrame? with
    | some f => (callees.find? (fun c => translateBody c == f.body)).getD root
    | none => root

/-- Frame-indexed overlay: every hook delegates to
`annealStepHooksDynTraitVTable (dvActiveBody root callees st)` (the LeanMiri
analogue of `annealStepHooksForState`). -/
def annealStepHooksDynTraitVTableFor (root : CapturedMir) (callees : List CapturedMir)
    (treeBorrows : Bool := false) (fnPtrs : List FnPtrEntry := .nil) :
    Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let H := fun (st : AnnealStepState) =>
    annealStepHooksDynTraitVTable (dvActiveBody root callees st) treeBorrows callees {} fnPtrs
  { assign := fun c p r st => (H st).assign c p r st
    evalPlace := fun c p b st => (H st).evalPlace c p b st
    writeDiscriminant := fun c v p st => (H st).writeDiscriminant c v p st
    storageLive := fun c l st => (H st).storageLive c l st
    storageDead := fun c l st => (H st).storageDead c l st
    intrinsic := fun c i st => (H st).intrinsic c i st
    incrementConstEvalCounter := fun c st => (H st).incrementConstEvalCounter c st
    returnFromCurrentFrame := fun c u st => (H st).returnFromCurrentFrame c u st
    beforeTerminator := fun c st => (H st).beforeTerminator c st
    terminator := fun c t st => (H st).terminator c t st }


/-! ## §2. Universal Laws -/

/-! ### Conservative extension of `annealStepHooksNullaryPtr` -/

/-- The overlay's `assign` is the base overlay's on every state whose active
statement is not a `dyn` operation. -/
theorem dvAssign_conservative (currentBody : CapturedMir) (treeBorrows : Bool)
    (callees : List CapturedMir) (poppedFrame : Miri.TreeBorrows.FrameState)
    (fnPtrs : List FnPtrEntry) (state : AnnealStepState)
    (hfree : dvIsDynOpAt currentBody treeBorrows state = false) (choice : Unit)
    (place : Miri.MIR.Place) (rvalue : Miri.MIR.Rvalue) :
    (annealStepHooksDynTraitVTable currentBody treeBorrows callees poppedFrame fnPtrs).assign
        choice place rvalue state =
      (annealStepHooksNullaryPtr currentBody treeBorrows callees poppedFrame fnPtrs).assign
        choice place rvalue state := by
  simp only [annealStepHooksDynTraitVTable, hfree, Bool.false_eq_true, ↓reduceIte]

/-- The overlay's `terminator` is the base overlay's on every state whose active
terminator is not a `dyn` call. -/
theorem dvTerminator_conservative (currentBody : CapturedMir) (treeBorrows : Bool)
    (callees : List CapturedMir) (poppedFrame : Miri.TreeBorrows.FrameState)
    (fnPtrs : List FnPtrEntry) (state : AnnealStepState)
    (hfree : dvIsDynOpAt currentBody treeBorrows state = false) (choice : Unit)
    (term : Miri.MIR.Terminator) :
    (annealStepHooksDynTraitVTable currentBody treeBorrows callees poppedFrame fnPtrs).terminator
        choice term state =
      (annealStepHooksNullaryPtr currentBody treeBorrows callees poppedFrame fnPtrs).terminator
        choice term state := by
  simp only [annealStepHooksDynTraitVTable, hfree, Bool.false_eq_true, ↓reduceIte]

/-- **Conservative Extension Theorem (`step_dynTraitVTable_overlay_conservative`)**:
for EVERY body, mode, linked-callee list and state whose active statement /
terminator (in `currentBody`) is not a `dyn` operation (`dvIsDynOpAt = false`,
decidable), one vendored `Miri.Interpreter.Step.step` under
`annealStepHooksDynTraitVTable` is **identically equal** to one step under
`annealStepHooksNullaryPtr`. -/
theorem step_dynTraitVTable_overlay_conservative {currentBody : CapturedMir}
    {callees : List CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState}
    {fnPtrs : List FnPtrEntry} (choice : Unit) (treeBorrows : Bool) (state : AnnealStepState)
    (hfree : dvIsDynOpAt currentBody treeBorrows state = false) :
    Miri.Interpreter.Step.step
      (annealStepHooksDynTraitVTable currentBody treeBorrows callees poppedFrame fnPtrs) choice state =
    Miri.Interpreter.Step.step
      (annealStepHooksNullaryPtr currentBody treeBorrows callees poppedFrame fnPtrs) choice state := by
  have hA := dvAssign_conservative currentBody treeBorrows callees poppedFrame fnPtrs state hfree choice
  have hT := dvTerminator_conservative currentBody treeBorrows callees poppedFrame fnPtrs state hfree
    choice
  have hB : (annealStepHooksNullaryPtr currentBody treeBorrows callees poppedFrame fnPtrs).beforeTerminator
      choice state = (state, .ok ()) := rfl
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
        dsimp only
        cases hst : bb.statements[loc.statementIndex]? with
        | some stmt =>
          rcases stmt with ⟨si, kind⟩
          cases kind with
          | Assign place rvalue =>
            have hEval :
                Miri.Interpreter.Step.evalStatement
                  (annealStepHooksDynTraitVTable currentBody treeBorrows callees poppedFrame fnPtrs)
                  choice { sourceInfo := si, kind := .Assign place rvalue } state =
                Miri.Interpreter.Step.evalStatement
                  (annealStepHooksNullaryPtr currentBody treeBorrows callees poppedFrame fnPtrs)
                  choice { sourceInfo := si, kind := .Assign place rvalue } state := by
              unfold Miri.Interpreter.Step.evalStatement
              exact hA place rvalue
            dsimp only
            rw [hEval]
          | SetDiscriminant _ _ | PlaceMention _ | StorageLive _ | StorageDead _
          | Intrinsic _ | ConstEvalCounter | FakeRead _ | AscribeUserType _ _
          | Coverage _ | Nop | BackwardIncompatibleDropHint _ _ => rfl
        | none =>
          have hB' : (annealStepHooksDynTraitVTable currentBody treeBorrows callees poppedFrame
              fnPtrs).beforeTerminator choice state = (state, .ok ()) := hB
          simp only [hB', hB, hT]

/-- The frame-indexed overlay's `assign` / `terminator` /
`returnFromCurrentFrame` are, in every state, exactly those of
`annealStepHooksDynTraitVTable` at the active body `dvActiveBody root callees st`. -/
theorem dvFor_hooks_eq (root : CapturedMir) (callees : List CapturedMir) (treeBorrows : Bool)
    (fnPtrs : List FnPtrEntry) (choice : Unit) (st : AnnealStepState) :
    (∀ p r, (annealStepHooksDynTraitVTableFor root callees treeBorrows fnPtrs).assign choice p r st =
      (annealStepHooksDynTraitVTable (dvActiveBody root callees st) treeBorrows callees {} fnPtrs).assign
        choice p r st) ∧
    (∀ t, (annealStepHooksDynTraitVTableFor root callees treeBorrows fnPtrs).terminator choice t st =
      (annealStepHooksDynTraitVTable (dvActiveBody root callees st) treeBorrows callees {} fnPtrs).terminator
        choice t st) ∧
    (∀ u, (annealStepHooksDynTraitVTableFor root callees treeBorrows fnPtrs).returnFromCurrentFrame
        choice u st =
      (annealStepHooksDynTraitVTable (dvActiveBody root callees st) treeBorrows callees {}
        fnPtrs).returnFromCurrentFrame choice u st) :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- In the root frame the active body is the root body. -/
theorem dvActiveBody_root (root : CapturedMir) (callees : List CapturedMir) (st : AnnealStepState)
    (h : st.stack.frames.size ≤ 1) : dvActiveBody root callees st = root := by
  simp [dvActiveBody, h]

/-! ### Trait-key and slot laws (Trusted `stringEq` / `CapturedVTableSlot` ↔ vendored predicates / `VTableEntry`) -/

/-- `listByteEq` is list equality. -/
theorem dv_listByteEq_iff : ∀ (a b : List UInt8), listByteEq a b = true ↔ a = b
  | [], [] => by simp [listByteEq]
  | [], _ :: _ => by simp [listByteEq]
  | _ :: _, [] => by simp [listByteEq]
  | x :: xs, y :: ys => by
    have ih := dv_listByteEq_iff xs ys
    unfold listByteEq
    cases h : Nat.beq x.toBitVec.toNat y.toBitVec.toNat with
    | true =>
      have hxy : x = y := UInt8.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true h))
      simp [ih, hxy]
    | false =>
      have hxy : x ≠ y := fun e => by subst e; simp at h
      simp [hxy]

/-- `stringEq` is equality of the UTF-8 byte lists (hence an equivalence). -/
theorem dv_stringEq_iff (a b : String) :
    stringEq a b = true ↔ a.toByteArray.data.toList = b.toByteArray.data.toList :=
  dv_listByteEq_iff _ _

/-- **Trait identifiers decide trait-object key equality**: for every captured
table and every vtable `v` of it, the vendored predicate id of `v`'s key equals
that of `k` exactly when Trusted's `stringEq v.dynKey k` holds. -/
theorem dvKeyIdx_eq_iff (vts : List CapturedVTable) (v : CapturedVTable) (hv : v ∈ vts)
    (k : DefPath) : dvKeyIdx vts v.dynKey = dvKeyIdx vts k ↔ stringEq v.dynKey k = true := by
  have hpt : ∀ a b, stringEq a b = true → ∀ w : CapturedVTable,
      stringEq w.dynKey a = stringEq w.dynKey b := by
    intro a b hab w
    rw [dv_stringEq_iff] at hab
    cases h1 : stringEq w.dynKey a <;> cases h2 : stringEq w.dynKey b <;> try rfl
    · rw [dv_stringEq_iff] at h2; rw [← hab] at h2; rw [← dv_stringEq_iff] at h2; simp_all
    · rw [dv_stringEq_iff] at h1; rw [hab] at h1; rw [← dv_stringEq_iff] at h1; simp_all
  constructor
  · intro heq
    unfold dvKeyIdx at heq
    have hsome : (vts.findIdx? (fun w => stringEq w.dynKey v.dynKey)).isSome := by
      rw [List.findIdx?_isSome]
      exact List.any_eq_true.mpr ⟨v, hv, (dv_stringEq_iff _ _).mpr rfl⟩
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hsome
    rw [hi] at heq
    simp only [Option.getD_some] at heq
    have hlt : i < vts.length := (List.findIdx?_eq_some_iff_getElem.mp hi).1
    cases hk : vts.findIdx? (fun w => stringEq w.dynKey k) with
    | none => rw [hk] at heq; simp at heq; omega
    | some j =>
      rw [hk] at heq; simp only [Option.getD_some] at heq; subst heq
      obtain ⟨hl1, h1, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
      obtain ⟨hl2, h2, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hk
      rw [dv_stringEq_iff] at h1 h2 ⊢
      rw [← h1, ← h2]
  · intro hk
    unfold dvKeyIdx
    have : (fun w : CapturedVTable => stringEq w.dynKey v.dynKey) =
        (fun w => stringEq w.dynKey k) := funext (hpt _ _ hk)
    rw [this]

/-- **Slot law** (the `entries[slot]?` lookup of vendored
`VirtualCalls.resolveVirtual` / `VTable.getMethod`): the vendored entry at
index `i` is the translation of the captured slot at `i`; it is a `.method`
exactly at captured `.method` (or unmodeled-method) slots, so every
out-of-bounds, header (`dropInPlace` / `size` / `align`), `vacant` or
`traitVPtr` slot is rejected as UB by the vendored code, as Trusted
`evalVirtualCall` rejects every slot other than `.method`. -/
theorem dvVTableEntries_getElem? (vts : List CapturedVTable) (v : CapturedVTable) (i : Nat) :
    (dvVTableEntries vts v)[i]? = (v.slots[i]?).map (dvSlotEntry vts) := by
  simp [dvVTableEntries]

theorem dvVTableEntries_method_iff (vts : List CapturedVTable) (v : CapturedVTable) (i : Nat)
    (inst : Miri.Interpreter.CallInstance) :
    (dvVTableEntries vts v)[i]? = some (.method inst) ↔
      (∃ p tys, v.slots[i]? = some (.method p tys) ∧ inst = dvMethodInstance vts p) ∨
      (v.slots[i]? = some .unmodeledMethod ∧ inst = { kind := .Item 0, args := #[] }) := by
  rw [dvVTableEntries_getElem?]
  cases h : v.slots[i]? with
  | none => simp
  | some s =>
    cases s <;> simp [dvSlotEntry, eq_comm]

/-- A captured slot that is not a (modeled or unmodeled) method never yields a
vendored `.method` entry. -/
theorem dvVTableEntries_not_method (vts : List CapturedVTable) (v : CapturedVTable) (i : Nat)
    (h : ∀ p tys, v.slots[i]? ≠ some (.method p tys)) (h' : v.slots[i]? ≠ some .unmodeledMethod)
    (inst : Miri.Interpreter.CallInstance) :
    (dvVTableEntries vts v)[i]? ≠ some (.method inst) := by
  intro hm
  rcases (dvVTableEntries_method_iff vts v i inst).mp hm with ⟨p, tys, hs, _⟩ | ⟨hs, _⟩
  · exact h p tys hs
  · exact h' hs

/-! ### Registry, vtable-pointer and layout laws -/

/-- `vtableEnvOk` bounds every captured `vtableAllocId` inside the reserved
vtable range (so it is a non-zero, 64-bit `AllocId`). -/
theorem dv_vtableEnvOk_allocId_bounds (vts : List CapturedVTable) (n : AllocId)
    (g : List CapturedAllocation) (f : List FnPtrEntry) (h : vtableEnvOk 8 vts n g f = true) :
    ∀ v ∈ vts, vtableAllocBase ≤ v.vtableAllocId ∧ v.vtableAllocId < vtableAllocBase + vtableAllocSpan := by
  intro v hv
  unfold vtableEnvOk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨_, _, hall⟩ := h
  have := hall v hv
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
  exact ⟨this.2.2.1, this.2.2.2.1⟩

private theorem dv_nat_beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

private theorem dv_registry_find_aux (vts0 : List CapturedVTable) (aid : Miri.Memory.AllocId) :
    ∀ l : List CapturedVTable, (∀ v ∈ l, v.vtableAllocId < 2 ^ 64) →
      ((l.filterMap (dvRegistryEntry? vts0)).find? (·.allocation == aid)).map
          (fun e => (e.typeId, e.dynamicType)) =
        (lookupVTableByAllocId l aid.value.toNat).map
          (fun v => (dvConcreteTyId vts0 v.concreteTy, dvKeyIdx vts0 v.dynKey))
  | [], _ => rfl
  | v :: l, hb => by
    have ih := dv_registry_find_aux vts0 aid l (fun w hw => hb w (List.mem_cons_of_mem _ hw))
    have hvb : v.vtableAllocId < 2 ^ 64 := hb v List.mem_cons_self
    have hnz : aid.value.toNat ≠ 0 := by
      intro h0; apply aid.nonzero; exact UInt64.toNat_inj.mp (by simpa using h0)
    simp only [List.filterMap_cons, lookupVTableByAllocId]
    by_cases h : UInt64.ofNat v.vtableAllocId ≠ 0
    · simp only [dvRegistryEntry?, h, ne_eq, not_false_eq_true, ↓reduceDIte, List.find?_cons]
      by_cases hid : v.vtableAllocId = aid.value.toNat
      · have hbeq : (⟨UInt64.ofNat v.vtableAllocId, h⟩ == aid) = true := by
          have : UInt64.ofNat v.vtableAllocId = aid.value := by
            rw [hid]; simp
          cases aid; simp_all
        simp [hbeq, hid]
      · have hbeq : (⟨UInt64.ofNat v.vtableAllocId, h⟩ == aid) = false := by
          cases aid with
          | mk val nz =>
            simp only [beq_eq_false_iff_ne, ne_eq]
            intro he
            apply hid
            cases he
            simp [UInt64.toNat_ofNat, Nat.mod_eq_of_lt hvb]
        have hnb : Nat.beq v.vtableAllocId aid.value.toNat = false :=
          dv_nat_beq_false hid
        simp only [hbeq, hnb]
        exact ih
    · have hz : v.vtableAllocId = 0 := by
        have h0 : UInt64.ofNat v.vtableAllocId = 0 := by simpa using h
        have := congrArg UInt64.toNat h0
        simpa [UInt64.toNat_ofNat, Nat.mod_eq_of_lt hvb] using this
      simp only [dvRegistryEntry?, h, ↓reduceDIte]
      have hnb : Nat.beq v.vtableAllocId aid.value.toNat = false := by
        rw [hz]; exact dv_nat_beq_false (Ne.symm hnz)
      simp only [hnb]
      exact ih

/-- **Registry law**: for every captured table whose allocation identifiers fit
in 64 bits (implied by `vtableEnvOk`, `dv_vtableEnvOk_allocId_bounds`), the
vendored `VTableMachine.Registry` lookup of an allocation (the first branch of
`VTableMachine.globalVTable`) is exactly Trusted `lookupVTableByAllocId`,
projected to `(concrete TyId, trait id)`. -/
theorem dvRegistryLookup_eq_lookupVTableByAllocId (vts : List CapturedVTable)
    (aid : Miri.Memory.AllocId) (hb : ∀ v ∈ vts, v.vtableAllocId < 2 ^ 64) :
    dvRegistryLookup (dvRegistry vts) aid =
      (lookupVTableByAllocId vts aid.value.toNat).map
        (fun v => (dvConcreteTyId vts v.concreteTy, dvKeyIdx vts v.dynKey)) := by
  unfold dvRegistryLookup dvRegistry
  rw [List.find?_toArray]
  exact dv_registry_find_aux vts aid vts hb

section DvPrivate
open Lean Elab Tactic

/-- Unfold the private predicate-sorting helpers of vendored
`Miri.Interpreter.VTable` (`sortedPredicates`, `sortPredicates`,
`insertPredicate`, `ub`), referenced by their module-private names. -/
elab "dv_unfold_vtable_private" : tactic => do
  let base := Name.mkNum `_private.Miri.Interpreter.VTable 0
  let i1 := mkIdent (base ++ `Miri.Interpreter.VTable.sortedPredicates)
  let i2 := mkIdent (base ++ `Miri.Interpreter.VTable.sortPredicates)
  let i3 := mkIdent (base ++ `Miri.Interpreter.VTable.insertPredicate)
  evalTactic (← `(tactic| simp only [$i1:ident, $i2:ident, $i3:ident]))

/-- Rewrite every `sortedPredicates #[⟨n, n, false⟩]` (the predicate list of a
single non-auto trait id, as `dvVTableReadHooks.predicates` returns) to the
singleton list, and the private `ub` to its `StepError.undefinedBehavior`
error (definitional unfoldings of the private helpers). -/
elab "dv_vt_pre" : tactic => do
  let base := Name.mkNum `_private.Miri.Interpreter.VTable 0
  let i1 := mkIdent (base ++ `Miri.Interpreter.VTable.sortedPredicates)
  let i4 := mkIdent (base ++ `Miri.Interpreter.VTable.ub)
  let hsp := mkIdent `dv_hsp
  let hub := mkIdent `dv_hub
  evalTactic (← `(tactic| have $hsp : ∀ n : Nat,
      $i1:ident #[({ id := n, stableKey := n, autoTrait := false } : Miri.Interpreter.VTablePredicate)] =
        [({ id := n, stableKey := n, autoTrait := false } : Miri.Interpreter.VTablePredicate)] :=
      fun _ => rfl))
  evalTactic (← `(tactic| have $hub : ∀ (A : Type) (m : String),
      @$i4:ident AnnealStepState A m = fun s => .error (.undefinedBehavior m) s := fun _ _ => rfl))
  evalTactic (← `(tactic| try simp only [$hsp:ident, $hub:ident]))

/-- Rewrite the private `metadataScalar` / `liftResult` helpers of vendored
`Miri.Interpreter.DynamicLayout` on concrete arguments (definitional
unfoldings). -/
elab "dv_dl_pre" : tactic => do
  let base := Name.mkNum `_private.Miri.Interpreter.DynamicLayout 0
  let i1 := mkIdent (base ++ `Miri.Interpreter.DynamicLayout.metadataScalar)
  let i2 := mkIdent (base ++ `Miri.Interpreter.DynamicLayout.liftResult)
  let h1 := mkIdent `dv_hms
  let h2 := mkIdent `dv_hlr
  evalTactic (← `(tactic| have $h1 : ∀ (sc : Miri.Memory.Scalar AnnealProv),
      @$i1:ident AnnealProv AnnealStepState (.metadata sc) = fun s => .ok sc s := fun _ => rfl))
  evalTactic (← `(tactic| have $h2 : ∀ (A : Type) (x : A),
      @$i2:ident A AnnealStepState (.ok x) = fun s => .ok x s := fun _ _ => rfl))
  evalTactic (← `(tactic| try simp only [$h1:ident, $h2:ident]))

/-- `simp` with the private predicate-sorting helpers of `Miri.Interpreter.VTable`
and the `EStateM` / `forIn` reduction set. -/
elab "dv_vt_simp" : tactic => do
  let base := Name.mkNum `_private.Miri.Interpreter.VTable 0
  let i1 := mkIdent (base ++ `Miri.Interpreter.VTable.sortedPredicates)
  let i2 := mkIdent (base ++ `Miri.Interpreter.VTable.sortPredicates)
  let i3 := mkIdent (base ++ `Miri.Interpreter.VTable.insertPredicate)
  evalTactic (← `(tactic| simp [*, $i1:ident, $i2:ident, $i3:ident, bind, EStateM.bind, pure,
    EStateM.pure, List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop, forIn', ForIn'.forIn',
    forIn, ForIn.forIn, List.forIn', List.zip, List.filter_cons, List.filter_nil, Bool.not_false,
    List.zipWith, List.forIn'_cons, List.forIn'_nil, List.forIn'.loop]))

end DvPrivate

theorem dvCheckForTypeRead_eq (vts : List CapturedVTable) (a e : Nat) (st : AnnealStepState) :
    Miri.Interpreter.VTable.checkForTypeRead (dvVTableReadHooks vts) () a e st =
      if a = e then .ok () st else .error (.undefinedBehavior "InvalidVTableTrait") st := by
  unfold Miri.Interpreter.VTable.checkForTypeRead
  simp only [dvVTableReadHooks, pure_bind]
  dv_vt_pre
  by_cases h : a = e
  · subst h; dv_vt_simp
  · dv_vt_simp

theorem dvVTableReadHooks_resolvePointer (vts : List CapturedVTable) (ptr : Miri.Memory.Pointer (Option AnnealProv))
    :
    (dvVTableReadHooks vts).resolvePointer () ptr = fun st => .ok (dvResolveVtPtr st.machine ptr) st :=
  rfl

theorem dvVTableReadHooks_globalVTable (vts : List CapturedVTable) (aid : Miri.Memory.AllocId)
 :
    (dvVTableReadHooks vts).globalVTable () aid =
      fun st => .ok (dvRegistryLookup (dvRegistry vts) aid) st :=
  rfl

/-- **Vendored vtable-pointer check law** (`VTable.getPtrVTableTypeRead` over
`dvVTableReadHooks`): for EVERY captured table, state and vtable pointer with
concrete provenance into an allocation with a cached base address, the vendored
check returns the registry's concrete type exactly when the pointer is at
offset `0`, names a registered vtable, and that vtable's trait id is the
expected one; it is UB (`InvalidVTablePointer` / `InvalidVTableTrait`)
otherwise. -/
theorem dvGetPtrVTableTypeRead_eq (vts : List CapturedVTable) (st : AnnealStepState)
    (aid : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag) (b addr : UInt64) (e : Nat)
    (hb : st.machine.lookupBaseAddr aid = some b) (hle : b ≤ addr) :
    Miri.Interpreter.VTable.getPtrVTableTypeRead (dvVTableReadHooks vts) ()
        ⟨Miri.ABI.Size.ofBytes addr, some (.concrete aid tag)⟩ (some e) st =
      if addr - b = 0 then
        match dvRegistryLookup (dvRegistry vts) aid with
        | some (ty, d) =>
          if d = e then .ok ty st else .error (.undefinedBehavior "InvalidVTableTrait") st
        | none => .error (.undefinedBehavior "InvalidVTablePointer") st
      else .error (.undefinedBehavior "InvalidVTablePointer") st := by
  unfold Miri.Interpreter.VTable.getPtrVTableTypeRead
  have hres : dvResolveVtPtr st.machine ⟨Miri.ABI.Size.ofBytes addr, some (.concrete aid tag)⟩ =
      .ok (aid, Miri.ABI.Size.ofBytes (addr - b)) := by
    simp [dvResolveVtPtr, hb, hle, Miri.ABI.Size.ofBytes]
  have hc := dvCheckForTypeRead_eq vts
  have hz0 : Miri.ABI.Size.ofBytes 0 = Miri.ABI.Size.ZERO := rfl
  dv_vt_pre
  by_cases hz : addr - b = 0
  · have hz' : (Miri.ABI.Size.ofBytes (addr - b) != Miri.ABI.Size.ZERO) = false := by
      simp [hz, Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
    cases hr : dvRegistryLookup (dvRegistry vts) aid with
    | none =>
      simp [dvVTableReadHooks_resolvePointer, dvVTableReadHooks_globalVTable, hres, hz', hr, hz,
        bind, EStateM.bind, pure, EStateM.pure, dv_hub, hz0]
    | some p =>
      obtain ⟨ty, d⟩ := p
      simp [dvVTableReadHooks_resolvePointer, dvVTableReadHooks_globalVTable, hres, hz', hr, hz,
        bind, EStateM.bind, pure, EStateM.pure, dv_hub, hc, hz0]
      by_cases hde : d = e <;> simp [hde]
  · have hz' : (Miri.ABI.Size.ofBytes (addr - b) != Miri.ABI.Size.ZERO) = true := by
      simp [hz, Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
    have hne : Miri.ABI.Size.ofBytes (addr - b) ≠ Miri.ABI.Size.ZERO := by
      intro h; apply hz; simpa [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO] using h
    simp [dvVTableReadHooks_resolvePointer, hres, hne, hz, bind, EStateM.bind, pure, EStateM.pure,
      dv_hub]

theorem dv_lookupVTableByAllocId_mem : ∀ (vts : List CapturedVTable) (a : Nat) (v : CapturedVTable),
    lookupVTableByAllocId vts a = some v → v ∈ vts
  | [], _, _, h => by simp [lookupVTableByAllocId] at h
  | w :: ws, a, v, h => by
    simp only [lookupVTableByAllocId] at h
    cases hb : Nat.beq w.vtableAllocId a with
    | true => rw [hb] at h; cases h; exact List.mem_cons_self
    | false => rw [hb] at h; exact List.mem_cons_of_mem _ (dv_lookupVTableByAllocId_mem ws a v h)

/-- **Vendored vtable check in Trusted terms**: under the 64-bit identifier
bound (`dv_vtableEnvOk_allocId_bounds`), vendored `VTable.getPtrVTableTypeRead`
(expected trait id `dvKeyIdx vts k`) decides on exactly Trusted's data:
`lookupVTableByAllocId` of the pointer's allocation, its offset, and
`stringEq entry.dynKey k`; success yields the concrete type of the found
entry. -/
theorem dvVTablePtrCheck_eq_trusted (vts : List CapturedVTable) (st : AnnealStepState)
    (aid : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag) (b addr : UInt64) (k : DefPath)
    (hb : st.machine.lookupBaseAddr aid = some b) (hle : b ≤ addr)
    (hbound : ∀ v ∈ vts, v.vtableAllocId < 2 ^ 64) :
    Miri.Interpreter.VTable.getPtrVTableTypeRead (dvVTableReadHooks vts) ()
        ⟨Miri.ABI.Size.ofBytes addr, some (.concrete aid tag)⟩ (some (dvKeyIdx vts k)) st =
      match lookupVTableByAllocId vts aid.value.toNat with
      | none => .error (.undefinedBehavior "InvalidVTablePointer") st
      | some v =>
        if addr - b = 0 then
          (if stringEq v.dynKey k = true then .ok (dvConcreteTyId vts v.concreteTy) st
           else .error (.undefinedBehavior "InvalidVTableTrait") st)
        else .error (.undefinedBehavior "InvalidVTablePointer") st := by
  rw [dvGetPtrVTableTypeRead_eq vts st aid tag b addr _ hb hle,
    dvRegistryLookup_eq_lookupVTableByAllocId vts aid hbound]
  cases hl : lookupVTableByAllocId vts aid.value.toNat with
  | none => by_cases hz : addr - b = 0 <;> simp [hz]
  | some v =>
    have hk := dvKeyIdx_eq_iff vts v (dv_lookupVTableByAllocId_mem vts _ v hl) k
    by_cases hz : addr - b = 0
    · by_cases hs : stringEq v.dynKey k = true
      · simp [hz, hs, hk.mpr hs]
      · have : ¬ dvKeyIdx vts v.dynKey = dvKeyIdx vts k := fun h => hs (hk.mp h)
        simp [hz, hs, this]
    · simp [hz]

/-- Trusted `checkDynVTablePtr` on a captured vtable record, in an environment
without trait-object descriptors (`dts = []`, the corpus' tables) and whose
vtable identifiers are not live borrow tags: success exactly at offset `0` with
a `stringEq`-equal key, `.ub` otherwise. -/
theorem dv_checkDynVTablePtr_found (cb : Option CapturedMir) (mv : DynMemView)
    (vts : List CapturedVTable) (vt : ProvenancePtr) (k : DefPath) (entry : CapturedVTable)
    (henv : dynVTableEnv? cb mv 8 = some (vts, []))
    (hnb : lookupBorrow mv.borrows vt.tag = none)
    (hl : lookupVTableByAllocId vts vt.allocId = some entry) :
    checkDynVTablePtr cb mv 8 (.ptr vt 8) k =
      if vt.offsetBytes = 0 then
        (if stringEq entry.dynKey k = true then .ok (entry, vts, []) else .ub)
      else .ub := by
  have h88 : Nat.beq 8 8 = true := rfl
  unfold checkDynVTablePtr
  simp only [h88, henv, hl, hnb]
  by_cases hz : vt.offsetBytes = 0
  · by_cases hs : stringEq entry.dynKey k = true
    · simp [hz, hs, dynTypeModeled, lookupDynType, dynKeysCompatible]
    · simp [hz, hs, dynTypeModeled, lookupDynType, dynKeysCompatible, dynPredicateKeyOf]
  · have : Nat.beq vt.offsetBytes 0 = false := by
      cases hb' : Nat.beq vt.offsetBytes 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb') hz
    simp [hz, this, dynTypeModeled, lookupDynType]

/-- Outcome class of a Trusted `DynCheck` (`0` ok, `1` UB, `2` unsupported). -/
def dvTrustedCheckClass {α : Type} : DynCheck α → Nat
  | .ok _ => 0
  | .ub => 1
  | .unsupported => 2

/-- Outcome class of a vendored `RvalueM` result (`0` ok, `1` UB, `2` other). -/
def dvMiriResultClass {α : Type} : EStateM.Result Miri.Interpreter.StepError AnnealStepState α → Nat
  | .ok _ _ => 0
  | .error (.undefinedBehavior _) _ => 1
  | .error _ _ => 2

/-- **`checkDynVTablePtr` ↔ vendored `VTable.getPtrVTableTypeRead` agreement**
(universal over tables, states, pointers and expected keys): when the Miri
pointer denotes Trusted's metadata pointer `vt` (same allocation id, same
offset) and `vt` names a captured vtable, the vendored check and Trusted's
check have the same outcome class, and on success the vendored concrete type is
the `TyId` of Trusted's entry. Hypotheses: Trusted's environment is the table
(`dynVTableEnv? = some (vts, [])`), the identifier is not a live borrow tag,
and identifiers fit in 64 bits (implied by `vtableEnvOk`). -/
theorem dvVTablePtrCheck_agrees_checkDynVTablePtr (cb : Option CapturedMir) (mv : DynMemView)
    (vts : List CapturedVTable) (vt : ProvenancePtr) (k : DefPath) (entry : CapturedVTable)
    (st : AnnealStepState) (aid : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag) (b addr : UInt64)
    (henv : dynVTableEnv? cb mv 8 = some (vts, []))
    (hnb : lookupBorrow mv.borrows vt.tag = none)
    (hl : lookupVTableByAllocId vts vt.allocId = some entry)
    (hbound : ∀ v ∈ vts, v.vtableAllocId < 2 ^ 64)
    (hb : st.machine.lookupBaseAddr aid = some b) (hle : b ≤ addr)
    (hid : aid.value.toNat = vt.allocId) (hoff : (addr - b).toNat = vt.offsetBytes) :
    dvMiriResultClass (Miri.Interpreter.VTable.getPtrVTableTypeRead (dvVTableReadHooks vts) ()
        ⟨Miri.ABI.Size.ofBytes addr, some (.concrete aid tag)⟩ (some (dvKeyIdx vts k)) st) =
      dvTrustedCheckClass (checkDynVTablePtr cb mv 8 (.ptr vt 8) k) ∧
    (∀ ty st', Miri.Interpreter.VTable.getPtrVTableTypeRead (dvVTableReadHooks vts) ()
        ⟨Miri.ABI.Size.ofBytes addr, some (.concrete aid tag)⟩ (some (dvKeyIdx vts k)) st =
          .ok ty st' → ty = dvConcreteTyId vts entry.concreteTy) := by
  rw [dvVTablePtrCheck_eq_trusted vts st aid tag b addr k hb hle hbound,
    dv_checkDynVTablePtr_found cb mv vts vt k entry henv hnb hl, hid, hl]
  have hz : (addr - b = 0) ↔ vt.offsetBytes = 0 := by
    rw [← hoff]; constructor
    · intro h; rw [h]; rfl
    · intro h; exact UInt64.toNat_inj.mp (by simpa using h)
  by_cases h0 : vt.offsetBytes = 0
  · have h0' : addr - b = 0 := hz.mpr h0
    by_cases hs : stringEq entry.dynKey k = true
    · refine ⟨by simp [h0, h0', hs, dvMiriResultClass, dvTrustedCheckClass], ?_⟩
      intro ty st' h; simp [h0', hs] at h; exact h.1.symm
    · refine ⟨by simp [h0, h0', hs, dvMiriResultClass, dvTrustedCheckClass], ?_⟩
      intro ty st' h; simp [h0', hs] at h
  · have h0' : ¬ addr - b = 0 := fun h => h0 (hz.mp h)
    refine ⟨by simp [h0, h0', dvMiriResultClass, dvTrustedCheckClass], ?_⟩
    intro ty st' h; simp [h0'] at h

/-- Field equations of `dvVTableHooks` / `dvVTableReadHooks` as `RvalueM` actions. -/
theorem dvVTableReadHooks_layoutOf (vts : List CapturedVTable) (ty : Miri.MIR.TyId) :
    (dvVTableReadHooks vts).layoutOf () ty =
      match dvVTableOfConcreteTyId? vts ty with
      | some v => pure (dvConcreteLayout vts v)
      | none => throw (.unsupported "layout of a type without a captured vtable") := rfl

/-- **Vendored dynamic size/alignment law** (`VTable.getSizeAndAlignRead`):
whenever the vendored vtable check yields concrete type `ty`, the vendored
size/alignment is the captured layout of `ty`'s vtable record. -/
theorem dvGetSizeAndAlignRead_eq (vts : List CapturedVTable)
    (ptr : Miri.Memory.Pointer (Option AnnealProv)) (e : Option Nat) (st : AnnealStepState)
    (ty : Miri.MIR.TyId) (v : CapturedVTable)
    (hty : Miri.Interpreter.VTable.getPtrVTableTypeRead (dvVTableReadHooks vts) () ptr e st =
      .ok ty st)
    (hv : dvVTableOfConcreteTyId? vts ty = some v) :
    Miri.Interpreter.VTable.getSizeAndAlignRead (dvVTableReadHooks vts) () ptr e st =
      .ok (translateSizeBytes v.sizeBytes, translateAlignBytes v.alignBytes) st := by
  unfold Miri.Interpreter.VTable.getSizeAndAlignRead
  simp [bind, EStateM.bind, hty, dvVTableReadHooks_layoutOf, hv, pure, EStateM.pure,
    dvConcreteLayout, Miri.ABI.LayoutData.isSized, Miri.ABI.BackendRepr.isSized,
    Miri.ABI.BackendRepr.isUnsized, zstLayoutData]

/-- **Vendored `DynamicLayout.sizeAndAlignFromMeta` law** on a `dyn K` pointee:
the metadata pointer is checked against `K` (vendored `getSizeAndAlignRead`)
and the captured layout of the resolved vtable is returned. -/
theorem dvSizeAndAlignFromMeta_eq (vts : List CapturedVTable) (fuel : Nat)
    (sc : Miri.Memory.Scalar AnnealProv) (ptr : Miri.Memory.Pointer (Option AnnealProv)) (i : Nat)
    (st : AnnealStepState) (ty : Miri.MIR.TyId) (v : CapturedVTable)
    (hi : i < dvConcreteBase - dvDynTailBase)
    (hptr : sc.toPointer annealTargetDataLayout = .ok ptr)
    (hty : Miri.Interpreter.VTable.getPtrVTableTypeRead (dvVTableReadHooks vts) () ptr (some i) st =
      .ok ty st)
    (hv : dvVTableOfConcreteTyId? vts ty = some v) :
    Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta (dvDynamicLayoutHooks vts) () (fuel + 1)
        (.metadata sc) (dvDynLayout (dvDynTailBase + i)) st =
      .ok (some (translateSizeBytes v.sizeBytes, translateAlignBytes v.alignBytes)) st := by
  have hsz := dvGetSizeAndAlignRead_eq vts ptr (some i) st ty v hty hv
  have hidx : dvDynTailIdx? (dvDynTailBase + i) = some i := by
    unfold dvDynTailIdx?
    have hi' : i < 100000 := hi
    have : dvDynTailBase ≤ dvDynTailBase + i ∧ dvDynTailBase + i < dvConcreteBase := by
      show (100000 : Nat) ≤ 100000 + i ∧ 100000 + i < 200000
      omega
    simp [this]
  unfold Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta
  dv_dl_pre
  simp [dv_hms, dv_hlr, Except.mapError, dvDynLayout, Miri.ABI.LayoutData.isSized, Miri.ABI.BackendRepr.isSized,
    Miri.ABI.BackendRepr.isUnsized, bind, EStateM.bind, dvDynamicLayoutHooks, hidx, pure,
    EStateM.pure, Miri.Interpreter.MemPlaceMeta.unwrapMeta, hptr, hsz]

/-- Layout coherence of a captured table (decidable): every record's concrete
type names (via `dvConcreteTyId`) a record with the same size and alignment. -/
def dvLayoutCoherent (vts : List CapturedVTable) : Bool :=
  vts.all fun v =>
    match dvVTableOfConcreteTyId? vts (dvConcreteTyId vts v.concreteTy) with
    | some w => w.sizeBytes == v.sizeBytes && w.alignBytes == v.alignBytes
    | none => false

/-- **`evalDynSizeAlignOfVal` ↔ vendored dynamic layout**: for every coherent
table, whenever the vendored vtable check accepts a metadata pointer (which by
`dvVTablePtrCheck_agrees_checkDynVTablePtr` happens exactly when Trusted's
`checkDynVTablePtr` returns `.ok (entry, ..)`, with `ty` the entry's concrete
`TyId`), the vendored `sizeAndAlignFromMeta` returns Trusted's
`(entry.sizeBytes, entry.alignBytes)` (the values `evalDynSizeAlignOfVal`
writes). -/
theorem dvSizeAlign_agrees_trusted_entry (vts : List CapturedVTable) (fuel : Nat)
    (sc : Miri.Memory.Scalar AnnealProv) (ptr : Miri.Memory.Pointer (Option AnnealProv)) (i : Nat)
    (st : AnnealStepState) (entry : CapturedVTable) (hentry : entry ∈ vts)
    (hcoh : dvLayoutCoherent vts = true)
    (hi : i < dvConcreteBase - dvDynTailBase)
    (hptr : sc.toPointer annealTargetDataLayout = .ok ptr)
    (hty : Miri.Interpreter.VTable.getPtrVTableTypeRead (dvVTableReadHooks vts) () ptr (some i) st =
      .ok (dvConcreteTyId vts entry.concreteTy) st) :
    Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta (dvDynamicLayoutHooks vts) () (fuel + 1)
        (.metadata sc) (dvDynLayout (dvDynTailBase + i)) st =
      .ok (some (translateSizeBytes entry.sizeBytes, translateAlignBytes entry.alignBytes)) st := by
  have hc := List.all_eq_true.mp hcoh entry hentry
  cases hw : dvVTableOfConcreteTyId? vts (dvConcreteTyId vts entry.concreteTy) with
  | none => simp [hw] at hc
  | some w =>
    simp only [hw, Bool.and_eq_true, beq_iff_eq] at hc
    rw [dvSizeAndAlignFromMeta_eq vts fuel sc ptr i st _ w hi hptr hty hw, hc.1, hc.2]

/-- Alignment encoding: every power-of-two alignment up to `2 ^ 29`
(vendored `Align.MAX`, rustc's maximal alignment) is encoded exactly by the
vendored `Align` (`translateAlignBytes`, `Align.bytesNat`). -/
theorem dv_translateAlign_pow2 : ∀ k < 30, (translateAlignBytes (2 ^ k)).bytesNat = .ok (2 ^ k) := by
  decide +kernel

/-- **`wfVTableEntry` ↔ vendored alignment**: for every well-formed captured
vtable whose (power-of-two, `wfVTableEntry`) alignment is at most rustc's
maximal alignment `2 ^ 29`, the vendored `Align` that `getSizeAndAlignRead`
returns (`translateAlignBytes`) encodes exactly `alignBytes`. -/
theorem dv_wfVTableEntry_align (v : CapturedVTable) (hwf : wfVTableEntry 8 v = true)
    (hmax : v.alignBytes ≤ 2 ^ 29) :
    (translateAlignBytes v.alignBytes).bytesNat = .ok v.alignBytes := by
  unfold wfVTableEntry isPowerOfTwoNat at hwf
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq_true_eq] at hwf
  obtain ⟨⟨hnz, hland⟩, _⟩ := hwf
  have hne : v.alignBytes ≠ 0 := by
    intro h0; rw [h0] at hnz; simp at hnz
  have hland' : v.alignBytes &&& v.alignBytes - 1 = 0 := Nat.eq_of_beq_eq_true hland
  have hpow : v.alignBytes.isPowerOfTwo :=
    (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hne).mp hland'
  obtain ⟨k, hk⟩ := hpow
  have hk29 : k < 30 := by
    have : 2 ^ k ≤ 2 ^ 29 := hk ▸ hmax
    have := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp this
    omega
  rw [hk]
  exact dv_translateAlign_pow2 k hk29

/-- Upcast target law: whenever Trusted resolves a `dyn Sub -> dyn Dst` upcast
(`resolveUpcastVTable?`), the resolved vtable is the captured
`(srcEntry.concreteTy, dstKey)` vtable — the vtable vendored
`Cast.unsizeIntoPointer` installs through `vtablePointer ty expected` for the
concrete type `ty` it recovered from the source vtable. -/
theorem dv_resolveUpcastVTable_eq_lookupVTableFor (vts : List CapturedVTable)
    (dts : List CapturedDynType) (srcEntry w : CapturedVTable) (dstKey : DefPath)
    (h : resolveUpcastVTable? vts dts srcEntry dstKey = some w) :
    lookupVTableFor vts srcEntry.concreteTy dstKey = some w := by
  unfold resolveUpcastVTable? at h
  dsimp only at h
  split at h
  · cases h
  · exact h

/-! ### Method selection and vtable reservation laws -/

theorem dvVTableHooks_entries (vts : List CapturedVTable) (principal : Option Nat) (ty : Miri.MIR.TyId) :
    (dvVTableHooks vts).entries () principal ty =
      match dvVTableFor? vts principal ty with
      | some v => pure (dvVTableEntries vts v)
      | none => throw (.unsupported "uncaptured vtable entries") := rfl

theorem dvVTableHooks_assert (vts : List CapturedVTable) (ty : Miri.MIR.TyId) (d : Miri.MIR.DefId)
    (a b : Miri.Interpreter.CallInstance) :
    (dvVTableHooks vts).assertVirtualInstanceMatches () ty d a b = pure () := rfl

/-- **Vendored `VTable.getMethod` law**: for EVERY captured table, slot index,
virtual instance and caller ABI, once the vendored vtable check yields the
concrete type `ty` of the captured record `v` (and the caller-selected ABI
check accepts), the vendored method selection returns the concrete instance of
`v`'s slot exactly when the slot is a method entry, and is UB
(`dyn call trying to call something that is not a method`) otherwise. -/
theorem dvGetMethod_eq (vts : List CapturedVTable)
    (validate : Unit → Miri.Interpreter.CallInstance → Miri.ABI.FnAbi Miri.MIR.TyId →
      Miri.Interpreter.RvalueM AnnealStepState Unit)
    (ptr : Miri.Memory.Pointer (Option AnnealProv)) (e : Nat) (principal : Option Nat) (idx : Nat)
    (defn : Miri.MIR.DefId) (vinst : Miri.Interpreter.CallInstance)
    (abi : Miri.ABI.FnAbi Miri.MIR.TyId) (st : AnnealStepState) (ty : Miri.MIR.TyId)
    (v : CapturedVTable)
    (hty : Miri.Interpreter.VTable.getPtrVTableType (dvVTableHooks vts) () ptr (some e) st = .ok ty st)
    (hv : dvVTableFor? vts principal ty = some v)
    (hval : ∀ f, validate () f abi st = .ok () st) :
    Miri.Interpreter.VTable.getMethod (dvVTableHooks vts) validate () ptr e principal idx defn vinst
        abi st =
      match (dvVTableEntries vts v)[idx]? with
      | some (.method f) => .ok f st
      | _ => .error (.undefinedBehavior "dyn call trying to call something that is not a method") st := by
  unfold Miri.Interpreter.VTable.getMethod
  dv_vt_pre
  cases hidx : (dvVTableEntries vts v)[idx]? with
  | none =>
    simp [bind, EStateM.bind, hty, dvVTableHooks_entries, hv, pure, EStateM.pure, hidx, dv_hub]
  | some en =>
    cases en <;>
      simp [bind, EStateM.bind, hty, dvVTableHooks_entries, hv, pure, EStateM.pure, hidx, dv_hub,
        hval, dvVTableHooks_assert]

/-- **Non-method slots are UB on both authorities**: under the hypotheses of
`dvGetMethod_eq`, whenever the captured slot `v.slots[idx]?` is not a method
(out of bounds, `dropInPlace` / `size` / `align` header, `vacant`, `traitVPtr`;
exactly the slots Trusted `evalVirtualCall` faults `.ub` on), vendored
`VTable.getMethod` is UB. -/
theorem dvGetMethod_nonMethod_ub (vts : List CapturedVTable)
    (validate : Unit → Miri.Interpreter.CallInstance → Miri.ABI.FnAbi Miri.MIR.TyId →
      Miri.Interpreter.RvalueM AnnealStepState Unit)
    (ptr : Miri.Memory.Pointer (Option AnnealProv)) (e : Nat) (principal : Option Nat) (idx : Nat)
    (defn : Miri.MIR.DefId) (vinst : Miri.Interpreter.CallInstance)
    (abi : Miri.ABI.FnAbi Miri.MIR.TyId) (st : AnnealStepState) (ty : Miri.MIR.TyId)
    (v : CapturedVTable)
    (hty : Miri.Interpreter.VTable.getPtrVTableType (dvVTableHooks vts) () ptr (some e) st = .ok ty st)
    (hv : dvVTableFor? vts principal ty = some v)
    (hval : ∀ f, validate () f abi st = .ok () st)
    (hslot : ∀ p tys, v.slots[idx]? ≠ some (.method p tys))
    (hslot' : v.slots[idx]? ≠ some .unmodeledMethod) :
    Miri.Interpreter.VTable.getMethod (dvVTableHooks vts) validate () ptr e principal idx defn vinst
        abi st =
      .error (.undefinedBehavior "dyn call trying to call something that is not a method") st := by
  rw [dvGetMethod_eq vts validate ptr e principal idx defn vinst abi st ty v hty hv hval]
  have hnm := dvVTableEntries_not_method vts v idx hslot hslot'
  cases hidx : (dvVTableEntries vts v)[idx]? with
  | none => rfl
  | some en =>
    cases en with
    | method f => exact absurd hidx (hnm f)
    | _ => rfl

private theorem dv_registry_reserve_aux (vts0 : List CapturedVTable) (cty : RigidTy) (k : DefPath)
    (hcty : ∀ w ∈ vts0, (dvConcreteTyId vts0 w.concreteTy == dvConcreteTyId vts0 cty) =
      rigidTyEq w.concreteTy cty) :
    ∀ l : List CapturedVTable, (∀ w ∈ l, w ∈ vts0) →
      (∀ w ∈ l, 0 < w.vtableAllocId ∧ w.vtableAllocId < 2 ^ 64) →
      ((l.filterMap (dvRegistryEntry? vts0)).find?
          (fun e => e.typeId == dvConcreteTyId vts0 cty && e.dynamicType == dvKeyIdx vts0 k &&
            e.salt.val == 0)).map (·.allocation.value.toNat) =
        (lookupVTableFor l cty k).map (·.vtableAllocId)
  | [], _, _ => rfl
  | w :: l, hsub, hnz => by
    have ih := dv_registry_reserve_aux vts0 cty k hcty l
      (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) (fun x hx => hnz x (List.mem_cons_of_mem _ hx))
    have hw := hsub w List.mem_cons_self
    obtain ⟨hpos, hlt⟩ := hnz w List.mem_cons_self
    have hne : UInt64.ofNat w.vtableAllocId ≠ 0 := by
      intro h0
      have := congrArg UInt64.toNat h0
      have h1 : w.vtableAllocId = 0 := by
        simpa [UInt64.toNat_ofNat, Nat.mod_eq_of_lt hlt, UInt64.toNat_zero] using this
      rw [h1] at hpos
      exact Nat.lt_irrefl 0 hpos
    have hkey : (dvKeyIdx vts0 w.dynKey == dvKeyIdx vts0 k) = stringEq w.dynKey k := by
      have := dvKeyIdx_eq_iff vts0 w hw k
      cases hs : stringEq w.dynKey k
      · simp only [beq_eq_false_iff_ne]; intro h; rw [this.mp h] at hs; cases hs
      · simp only [beq_iff_eq]; exact this.mpr hs
    have hty := hcty w hw
    simp only [List.filterMap_cons, dvRegistryEntry?, hne, ne_eq, not_false_eq_true, ↓reduceDIte,
      List.find?_cons, lookupVTableFor]
    have hsalt : ((0 : Fin 32).val == 0) = true := rfl
    rw [hty, hkey, hsalt, Bool.and_true, Bool.and_comm]
    cases hc : (stringEq w.dynKey k && rigidTyEq w.concreteTy cty)
    · exact ih
    · simp [UInt64.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- **Registry reservation ↔ `lookupVTableFor`**: for every captured table with
non-zero 64-bit identifiers (implied by `vtableEnvOk`) on which the concrete
type `cty`'s `TyId` is faithful to Trusted's `rigidTyEq` (a decidable
condition), the vendored registry reservation (the hit branch of
`VTableMachine.reserve`, used by vendored `VTable.getPointer`) of
`(TyId of cty, trait id of k, salt 0)` names exactly the allocation of Trusted
`lookupVTableFor vts cty k` — the vtable Trusted `evalThinToDynUnsize` installs
(and, through `dv_resolveUpcastVTable_eq_lookupVTableFor`, the vtable
`evalDynToDynUnsize` installs). -/
theorem dvRegistryReserve_eq_lookupVTableFor (vts : List CapturedVTable) (cty : RigidTy) (k : DefPath)
    (hnz : ∀ w ∈ vts, 0 < w.vtableAllocId ∧ w.vtableAllocId < 2 ^ 64)
    (hcty : ∀ w ∈ vts, (dvConcreteTyId vts w.concreteTy == dvConcreteTyId vts cty) =
      rigidTyEq w.concreteTy cty) :
    (dvRegistryReserve (dvRegistry vts) (dvConcreteTyId vts cty) (dvKeyIdx vts k) 0).map
        (·.value.toNat) =
      (lookupVTableFor vts cty k).map (·.vtableAllocId) := by
  unfold dvRegistryReserve dvRegistry
  rw [List.find?_toArray, Option.map_map]
  exact dv_registry_reserve_aux vts cty k hcty vts (fun _ h => h) hnz

/-- **Vendored `VTable.getPointer` law**: the vendored vtable-pointer
construction (erase / monomorphic checks, salt `0`, registry reservation, root
pointer) returns the root pointer of the reserved vtable allocation, and fails
closed (`unsupported`) on an uncaptured `(type, trait)` pair. -/
theorem dvGetPointer_eq (vts : List CapturedVTable) (st : AnnealStepState) (ty : Miri.MIR.TyId)
    (d : Nat) :
    Miri.Interpreter.VTable.getPointer (dvVTableHooks vts) () ty d st =
      match dvRegistryReserve (dvRegistry vts) ty d 0 with
      | some aid =>
        match dvVtRootPointer st.machine aid with
        | some p => .ok p st
        | none => .error (.unsupported "vtable allocation without a base address") st
      | none => .error (.unsupported "uncaptured (concrete type, trait object) vtable") st := by
  unfold Miri.Interpreter.VTable.getPointer
  cases hr : dvRegistryReserve (dvRegistry vts) ty d 0 with
  | none =>
    simp [dvVTableHooks, bind, EStateM.bind, pure, EStateM.pure, hr, throw, throwThe,
      MonadExceptOf.throw, EStateM.throw]
  | some aid =>
    cases hp : dvVtRootPointer st.machine aid <;>
      simp [dvVTableHooks, bind, EStateM.bind, pure, EStateM.pure, hr, hp, throw, throwThe,
        MonadExceptOf.throw, EStateM.throw, get, getThe, MonadStateOf.get, EStateM.get]

/-! ## §3. Shared LeanMiri Execution, State & Observation Helpers -/

/-- Authority-typed LeanMiri observation of one corpus execution. -/
inductive DynVtLmObs : Type where
  | u32Val (bits : Nat)
  | usizeVal (bits : Nat)
  | boolVal (bits : Nat)
  | widePtr (dataId : Nat) (dataOff : Nat) (vtableAllocId : Nat)
  | ub
  | unsupported
  deriving DecidableEq, Repr

/-- Decode an integer scalar by width (`1` / `4` / `8` bytes). -/
def dvDecodeInt (sc : Miri.Memory.Scalar AnnealProv) : DynVtLmObs :=
  match sc.toScalarInt with
  | .ok msc =>
    if msc.size == Miri.ABI.Size.ofBytes 1 then .boolVal msc.data.toNat
    else if msc.size == Miri.ABI.Size.ofBytes 4 then .u32Val msc.data.toNat
    else if msc.size == Miri.ABI.Size.ofBytes 8 then .usizeVal msc.data.toNat
    else .unsupported
  | .error _ => .unsupported

/-- `(allocation id, allocation-relative offset)` of a pointer scalar with
concrete provenance, resolved against the machine's base-address table. -/
def dvDecodePtr (mach : AnnealMachine) (sc : Miri.Memory.Scalar AnnealProv) : Option (Nat × Nat) :=
  match sc.toPointer annealTargetDataLayout with
  | .ok p =>
    match p.provenance with
    | some (.concrete aid _) =>
      match mach.lookupBaseAddr aid with
      | some b => if b ≤ p.offset.bytes then some (aid.value.toNat, (p.offset.bytes - b).toNat) else none
      | none => none
    | _ => none
  | .error _ => none

/-- Decode a `runMiriSteps` result: the returned `_0` (an integer, or a
`(data, vtable)` wide pointer whose vtable pointer is at offset `0`), or the
`StepError` class. -/
def dvToObs (res : Except Miri.Interpreter.StepError
    (AnnealStepState × Option (Miri.Interpreter.LocalValue AnnealProv))) : DynVtLmObs :=
  match res with
  | .ok (_, some (.live (.immediate (.scalar sc)))) => dvDecodeInt sc
  | .ok (st, some (.live (.immediate (.scalarPair d v)))) =>
    match dvDecodePtr st.machine d, dvDecodePtr st.machine v with
    | some (did, doff), some (vid, 0) => .widePtr did doff vid
    | _, _ => .unsupported
  | .ok _ => .unsupported
  | .error (.undefinedBehavior _) => .ub
  | .error _ => .unsupported

/-- One-frame initial state of `body` with the given locals. -/
def dvMkState (body : CapturedMir)
    (locs : Array (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout))
    (mach : AnnealMachine) : AnnealStepState :=
  let retTy := (body.localDecls.head?.map (·.ty)).getD dvU32Ty
  { stack := { frames := #[{
      body := translateBody body,
      bodyIdentity := .ofCanonicalIndex 0,
      functionInstance := { kind := .Item 0, args := #[] },
      extra := (), returnContinuation := .stop false,
      returnPlace := .frameLocal 0 0 none (translateTyOverlay retTy body.layouts) (.ofAllocationToken 0),
      localsIdentity := .ofAllocationToken 0, locals := locs, vaList := #[],
      trackCallerArg := none, location := .mir ⟨0, 0⟩ }] },
    machine := mach }

/-- An uninitialized live local of type `ty`. -/
def dvUninit (ty : Ty) : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
  ⟨.live (.immediate .uninit), some (translateTyOverlay ty emptyLayoutTable)⟩

/-- An immediate live local of type `ty`. -/
def dvImmLocal (imm : Miri.Interpreter.Immediate AnnealProv) (ty : Ty) :
    Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
  ⟨.live (.immediate imm), some (translateTyOverlay ty emptyLayoutTable)⟩

/-- Unsigned integer scalar of `szBytes` bytes. -/
def dvScalarUInt (bits : Nat) (szBytes : UInt64) : Miri.Memory.Scalar AnnealProv :=
  match Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 bits) (Miri.ABI.Size.ofBytes szBytes) with
  | .ok s => s
  | .error _ => Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨.ZERO, .wildcard⟩

/-- Allocation identifiers of the corpus: `1` (the frame local / pointee),
`3` (the `c16` receiver pointee) and `5` (the untracked dangling allocation). -/
def dvAid1 : Miri.Memory.AllocId := ⟨1, by decide⟩
def dvAid3 : Miri.Memory.AllocId := ⟨3, by decide⟩
def dvAid5 : Miri.Memory.AllocId := ⟨5, by decide⟩

/-- Base address of the untracked dangling allocation `5`. -/
def dvBase5 : UInt64 := 1024

/-- Pointer scalar `(aid, absolute address, tag)`. -/
def dvPtrScalar (aid : Miri.Memory.AllocId) (addr : UInt64)
    (tag : Miri.Memory.BorTag := .one) : Miri.Memory.Scalar AnnealProv :=
  Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨Miri.ABI.Size.ofBytes addr, .concrete aid tag⟩

/-- Root pointer scalar of the captured vtable allocation `vtableAllocId`
(cached base address `annealStackBaseAddr`). -/
def dvVtScalar (vtableAllocId : Nat) : Miri.Memory.Scalar AnnealProv :=
  if h : UInt64.ofNat vtableAllocId ≠ 0 then
    dvPtrScalar ⟨UInt64.ofNat vtableAllocId, h⟩ (annealStackBaseAddr ⟨UInt64.ofNat vtableAllocId, h⟩)
  else Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨.ZERO, .wildcard⟩

/-- A `dyn` wide pointer immediate `(data, vtable)`. -/
def dvWideImm (data : Miri.Memory.Scalar AnnealProv) (vtableAllocId : Nat) :
    Miri.Interpreter.Immediate AnnealProv :=
  .scalarPair data (dvVtScalar vtableAllocId)

/-- Base-address entries of the captured vtable allocations. -/
def dvVtAddrEntries (vts : List CapturedVTable) : Array Miri.Memory.AllocAddresses.BaseAddressEntry :=
  (vts.filterMap fun v =>
    if h : UInt64.ofNat v.vtableAllocId ≠ 0 then
      some ⟨⟨UInt64.ofNat v.vtableAllocId, h⟩, annealStackBaseAddr ⟨UInt64.ofNat v.vtableAllocId, h⟩⟩
    else none).toArray

/-- Initial machine: the captured vtables as vendored symbolic `.vtable` global
allocations (size `0`, pointer alignment, `VTableMachine.reserve`'s shape) with
cached base addresses, plus the given live allocations, extra base addresses
and borrow tracker. -/
def dvMachine (vts : List CapturedVTable)
    (live : Array (Miri.Memory.AllocId × Miri.Memory.LocalAllocation AnnealProv
      (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind) := #[])
    (addrs : Array Miri.Memory.AllocAddresses.BaseAddressEntry := #[])
    (bt : Option Miri.Interpreter.MachineHooks.BorrowState := none) : AnnealMachine :=
  let mem0 : AnnealMemory := (dvRegistry vts).entries.foldl
    (fun m e => Miri.Memory.MemoryState.pushGlobal m
      ⟨e.allocation, .vtable, .ZERO, Miri.ABI.Align.EIGHT, .Not, some .vtable⟩)
    AnnealMachine.empty.memory
  { memory := { mem0 with live := live }
    addresses := { AnnealMachine.empty.addresses with baseAddr := addrs ++ dvVtAddrEntries vts }
    borrowTracker := bt }

/-- A `w`-byte (`w ∈ {4, 8}`) little-endian stack allocation holding the
unsigned integer `n`, aligned to `w`, carrying the borrow tree `tree`. -/
def dvUIntAlloc? (n w : Nat) (tree : Option Miri.TreeBorrows.BorrowTree) :
    Option (Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind) :=
  let bytes : Array UInt8 := ((List.range w).map fun i => UInt8.ofNat (n / 256 ^ i)).toArray
  match Miri.Memory.Allocation.fromBytes (Prov := AnnealProv) bytes
      ⟨if w = 8 then 3 else 2⟩ .Mut with
  | .ok al => some ⟨.stack, al.withExtra tree⟩
  | .error _ => none

/-- Live-allocation table holding a `w`-byte integer `n` at `aid`. -/
def dvLiveUInt (aid : Miri.Memory.AllocId) (n w : Nat) (tree : Option Miri.TreeBorrows.BorrowTree) :
    Array (Miri.Memory.AllocId × Miri.Memory.LocalAllocation AnnealProv
      (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind) :=
  match dvUIntAlloc? n w tree with
  | some a => #[(aid, a)]
  | none => #[]

/-- Live-allocation table holding `_k : u32 = n` at `aid`. -/
def dvLiveU32 (aid : Miri.Memory.AllocId) (n : Nat) (tree : Option Miri.TreeBorrows.BorrowTree) :
    Array (Miri.Memory.AllocId × Miri.Memory.LocalAllocation AnnealProv
      (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind) :=
  dvLiveUInt aid n 4 tree

/-- A memory-backed local of type `ty` at the root of allocation `aid`
(cached base address `annealStackBaseAddr aid`). -/
def dvIndirectLocal (aid : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag := .one) (ty : Ty := dvU32Ty) :
    Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
  ⟨.live (.indirect ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr aid), some (.concrete aid tag)⟩, .none, none⟩),
   some (translateTyOverlay ty emptyLayoutTable)⟩


/-! ### Corpus initial states -/

/-- The linked body of `core::ptr::addr_eq::<dyn Tr, dyn Alt>` (library
`core/src/ptr/mod.rs`: `(p as *const ()) == (q as *const ())`), monomorphized at
the corpus call's type arguments. -/
@[reducible] def dvRawUnitTy : Ty := { kind := .rawPtr .not (.tuple []), layoutIdx := 0 }
def dvCoreAddrEqMir : CapturedMir :=
  dvMkBody "core::ptr::addr_eq"
    [dvDecl dvBoolTy, dvDecl (dvRawConstDynTy dvTrKey), dvDecl (dvRawConstDynTy dvAltKey),
     dvDecl dvRawUnitTy, dvDecl dvRawUnitTy] 2
    [dvBb [dvSt (.storageLive 3), dvSt (.storageLive 4),
           dvSt (.assign (dvLoc 3) (.cast .ptrToPtr (.copy (dvLoc 1)) dvRawUnitTy)),
           dvSt (.assign (dvLoc 4) (.cast .ptrToPtr (.copy (dvLoc 2)) dvRawUnitTy)),
           dvSt (.assign (dvLoc 0) (.binaryOp .eq (.copy (dvLoc 3)) (.copy (dvLoc 4)))),
           dvSt (.storageDead 4), dvSt (.storageDead 3)] .return_]
    [dvPtrArg, dvPtrArg]

/-- Machine with the dangling allocation `5`'s base address cached (no live
allocation). -/
def dvMachine5 : AnnealMachine := dvMachine dvVTables #[] #[⟨dvAid5, dvBase5⟩]

/-- `thinUnsize` states: `x = n` (`w` bytes) for the `&x` fixtures, the dangling
misaligned pointer `(5, +1)` for the argument fixtures. -/
def dvStThinLocal (body : CapturedMir) (n w : Nat) (xTy refTy : Ty) : AnnealStepState :=
  dvMkState body #[dvUninit ((body.localDecls.head?.map (·.ty)).getD dvU32Ty),
    dvIndirectLocal dvAid1 .one xTy, dvUninit refTy]
    (dvMachine dvVTables (dvLiveUInt dvAid1 n w none) #[⟨dvAid1, annealStackBaseAddr dvAid1⟩])
def dvStThinArg (body : CapturedMir) (argTy : Ty) : AnnealStepState :=
  dvMkState body #[dvUninit ((body.localDecls.head?.map (·.ty)).getD dvU32Ty),
    dvImmLocal (.scalar (dvPtrScalar dvAid5 (dvBase5 + 1))) argTy] dvMachine5

/-- `dynUpcastAndNop` upcast states: `x = 7u32`. -/
def dvStUpcast (body : CapturedMir) : AnnealStepState :=
  dvMkState body #[dvUninit ((body.localDecls.head?.map (·.ty)).getD dvU32Ty),
    dvIndirectLocal dvAid1, dvUninit dvRefU32Ty, dvUninit (dvRefDynTy dvSubKey)]
    (dvMachine dvVTables (dvLiveU32 dvAid1 7 none) #[⟨dvAid1, annealStackBaseAddr dvAid1⟩])

/-- States whose argument `_1 : &dyn Tr` points to the memory-backed local
`_2 : u32 = 7` (allocation `1`, borrow tag `tag`, borrow tree `tree`), with
metadata `vt`; `live = false` makes `_2` dead (its allocation freed). -/
def dvStPointee (body : CapturedMir) (vt : Nat) (tree : Option Miri.TreeBorrows.BorrowTree := none)
    (tag : Miri.Memory.BorTag := .one) (live : Bool := true)
    (bt : Option Miri.Interpreter.MachineHooks.BorrowState := none) : AnnealStepState :=
  dvMkState body #[dvUninit ((body.localDecls.head?.map (·.ty)).getD dvU32Ty),
    dvImmLocal (dvWideImm (dvPtrScalar dvAid1 (annealStackBaseAddr dvAid1) tag) vt) (dvRefDynTy dvTrKey),
    if live then dvIndirectLocal dvAid1 else ⟨.dead, some (translateTyOverlay dvU32Ty emptyLayoutTable)⟩]
    (dvMachine dvVTables (if live then dvLiveU32 dvAid1 7 tree else #[])
      #[⟨dvAid1, annealStackBaseAddr dvAid1⟩] bt)

/-- `*const dyn` argument states: data pointers into the dangling allocation `5`. -/
def dvStRawDyn (body : CapturedMir) (off : UInt64) (args : List (Nat × String)) : AnnealStepState :=
  dvMkState body (#[dvUninit ((body.localDecls.head?.map (·.ty)).getD dvU32Ty)] ++
    (args.map fun (vt, k) =>
      dvImmLocal (dvWideImm (dvPtrScalar dvAid5 (dvBase5 + off)) vt) (dvRawConstDynTy k)).toArray)
    dvMachine5

/-- `virtualDispatchAndProtector` call states: `x = n` (`w` bytes). -/
def dvStCall (body : CapturedMir) (n w : Nat) (xTy refTy : Ty) : AnnealStepState :=
  dvMkState body #[dvUninit dvU32Ty, dvIndirectLocal dvAid1 .one xTy, dvUninit refTy,
    dvUninit (dvRefDynTy dvTrKey)]
    (dvMachine dvVTables (dvLiveUInt dvAid1 n w none) #[⟨dvAid1, annealStackBaseAddr dvAid1⟩])

/-- Vendored Tree Borrows tree over the 4 bytes of the `c16` receiver pointee:
root `retagParentTag` (`Unique`, the `&mut` / raw alias) with the accessed
`Frozen` child `retagChildTag` (the receiver's function-entry reborrow). -/
def dvRecvTree : Miri.TreeBorrows.BorrowTree :=
  { hooksTwoNodeTree .frozen with
    locations := Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 4) (hooksLocTree .frozen) }

/-- Borrow tracker whose global protected-tag table protects the receiver tag
`retagChildTag` (`StrongProtector`, the active call protector) iff `prot`. -/
def dvRecvBorrowState (prot : Bool) : Miri.Interpreter.MachineHooks.BorrowState :=
  { global := { protectedTags := (hooksForChildProtected prot).protectedTags }, retagMode := .Default }

/-- Callee-entry state of the Crubit `c16` call (`dvV3ProtectedPokeMir`): `_1`
is the receiver (tag `retagChildTag`), `_2` the raw alias (tag
`retagParentTag`), `_3 : u32 = 7` the memory-backed pointee (allocation `3`). -/
def dvStC16 (prot : Bool := true) : AnnealStepState :=
  dvMkState dvV3ProtectedPokeMir #[dvUninit dvU32Ty,
     dvImmLocal (.scalar (dvPtrScalar dvAid3 (annealStackBaseAddr dvAid3) retagChildTag)) dvRefU32Ty,
     dvImmLocal (.scalar (dvPtrScalar dvAid3 (annealStackBaseAddr dvAid3) retagParentTag)) dvRawMutU32Ty,
     dvIndirectLocal dvAid3 retagParentTag]
    (dvMachine dvVTables (dvLiveU32 dvAid3 7 (some dvRecvTree)) #[⟨dvAid3, annealStackBaseAddr dvAid3⟩]
      (some (dvRecvBorrowState prot)))

/-- Root node of a one-node vendored Tree Borrows tree (`retagParentTag`). -/
def dvRootNode : Miri.TreeBorrows.TreeNode :=
  { tag := retagParentTag, parent := none, children := #[],
    defaultInitialPermission := .Disabled, defaultInitialSifa := .None }

/-- One-node vendored Tree Borrows tree over the 4 bytes of `x : u32`: the root
tag `retagParentTag` (`Unique`, accessed). -/
def dvRootTree : Miri.TreeBorrows.BorrowTree :=
  { tagMapping := { mapping := #[(retagParentTag, ⟨0⟩)], deassigned := #[] }
    nodes := ⟨#[some dvRootNode]⟩
    locations := Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 4)
      { perms := ⟨#[some ⟨.Unique, true, .None⟩]⟩, exposedCache := {} }
    roots := #[⟨0⟩] }

/-- Initial state of the full Crubit `c16` caller `dvV3PokeCallerMir`:
`x = 7u32` memory-backed at allocation `1` under the root tag, with a borrow
tracker holding no protector. Under Tree Borrows the virtual call's
function-entry retag (`dvRetagReceiver`) installs the receiver's protected
`Frozen` reborrow. -/
def dvStC16Caller : AnnealStepState :=
  dvMkState dvV3PokeCallerMir #[dvUninit dvU32Ty, dvIndirectLocal dvAid1 retagParentTag,
     dvUninit dvRefMutU32Ty, dvUninit dvRawMutU32Ty, dvUninit dvRefU32Ty, dvUninit (dvRefDynTy dvTrKey)]
    (dvMachine dvVTables (dvLiveU32 dvAid1 7 (some dvRootTree)) #[⟨dvAid1, annealStackBaseAddr dvAid1⟩]
      (some (dvRecvBorrowState false)))

/-- Two-node tree over `_2 : u32` whose reference tag `retagChildTag` is
`Disabled` (a later direct write through the parent disabled it). -/
def dvDisabledTree : Miri.TreeBorrows.BorrowTree :=
  { hooksTwoNodeTree .disabled with
    locations := Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 4) (hooksLocTree .disabled) }

/-! ## §5. Canonical Executable LeanMiri Corpus Observation (`dvLmObserve`) -/

/-- Step budget of every LeanMiri corpus execution. -/
def dvLmFuel : Nat := 24

/-- Run unmodified vendored `Miri.Interpreter.Step.step` (`runMiriSteps`) under
the frame-indexed overlay `annealStepHooksDynTraitVTableFor root callees` and
decode the result. -/
def dvLmRun (root : CapturedMir) (callees : List CapturedMir) (treeBorrows : Bool)
    (st : AnnealStepState) : DynVtLmObs :=
  dvToObs (runMiriSteps (annealStepHooksDynTraitVTableFor root callees treeBorrows) dvLmFuel st)

/-- The `CapturedMir` fixture executed by `dvLmObserve` for each
`(variantIdx, caseIdx)` key (locked per-key against `MiniRustSpec`'s
`dvTrustedFixture` in the cross-root kernel bridge). -/
def dvLmFixture (variantIdx caseIdx : Nat) : CapturedMir :=
  match variantIdx, caseIdx with
  | 0, 0 => dvV1RefUnsizeMir
  | 0, 1 => dvV1RawUnsizeMir
  | 0, 2 => dvV1RefArgUnsizeMir
  | 0, 3 => dvV1MutUnsizeMir
  | 1, 0 => dvV2UpcastSuperMir
  | 1, 1 => dvV2UpcastSideMir
  | 1, 2 => dvV2NopRefMir
  | 1, 3 => dvV2NopRawMir
  | 2, 0 => dvV3CallU32Mir
  | 2, 1 => dvV3CallU64Mir
  | 2, 2 => dvV3ArgCallMir
  | 2, 3 => dvV3PokeCallerMir
  | 3, 0 => dvV4SizeSafeMir
  | 3, 1 => dvV4AddrEqMir
  | 3, 2 => dvV4SizeSafeMir
  | 3, 3 => dvV4WideEqMir
  | _, _ => dvV1RefUnsizeMir

/-- Direct vendored `Miri.Interpreter.Step.step` observation for every
`(treeBorrows, variantIdx, caseIdx)` key (`variantIdx, caseIdx ∈ 0..3`). -/
def dvLmObserve (treeBorrows : Bool) (variantIdx : Nat) (caseIdx : Nat) : DynVtLmObs :=
  match variantIdx, caseIdx with
  -- 0: thinUnsize
  | 0, 0 => dvLmRun dvV1RefUnsizeMir [] treeBorrows
      (dvStThinLocal dvV1RefUnsizeMir 7 4 dvU32Ty dvRefU32Ty)
  | 0, 1 => dvLmRun dvV1RawUnsizeMir [] treeBorrows (dvStThinArg dvV1RawUnsizeMir dvRawConstU32Ty)
  | 0, 2 => dvLmRun dvV1RefArgUnsizeMir [] treeBorrows (dvStThinArg dvV1RefArgUnsizeMir dvRefU32Ty)
  | 0, 3 => dvLmRun dvV1MutUnsizeMir [] treeBorrows
      (dvStThinLocal dvV1MutUnsizeMir 64 8 dvU64Ty dvRefMutU64Ty)
  -- 1: dynUpcastAndNop
  | 1, 0 => dvLmRun dvV2UpcastSuperMir [] treeBorrows (dvStUpcast dvV2UpcastSuperMir)
  | 1, 1 => dvLmRun dvV2UpcastSideMir [] treeBorrows (dvStUpcast dvV2UpcastSideMir)
  | 1, 2 => dvLmRun dvV2NopRefMir [] treeBorrows (dvStPointee dvV2NopRefMir 16386)
  | 1, 3 => dvLmRun dvV2NopRawMir [] treeBorrows (dvStRawDyn dvV2NopRawMir 1 [(16384, dvTrKey)])
  -- 2: virtualDispatchAndProtector
  | 2, 0 => dvLmRun dvV3CallU32Mir dvCallees treeBorrows (dvStCall dvV3CallU32Mir 7 4 dvU32Ty dvRefU32Ty)
  | 2, 1 => dvLmRun dvV3CallU64Mir dvCallees treeBorrows (dvStCall dvV3CallU64Mir 64 8 dvU64Ty dvRefU64Ty)
  | 2, 2 => dvLmRun dvV3ArgCallMir dvCallees treeBorrows (dvStPointee dvV3ArgCallMir 16386)
  | 2, 3 => dvLmRun dvV3PokeCallerMir dvCallees treeBorrows dvStC16Caller
  -- 3: dynLayoutRawBorrowAndAddrEq
  | 3, 0 => dvLmRun dvV4SizeSafeMir [] treeBorrows
      (dvStPointee dvV4SizeSafeMir 16384 (some dvDisabledTree) retagChildTag
        (bt := some (dvRecvBorrowState false)))
  | 3, 1 => dvLmRun dvV4AddrEqMir [dvCoreAddrEqMir] treeBorrows
      (dvStRawDyn dvV4AddrEqMir 0 [(16384, dvTrKey), (16386, dvAltKey)])
  | 3, 2 => dvLmRun dvV4SizeSafeMir [] treeBorrows (dvStPointee dvV4SizeSafeMir 16384 (live := false))
  | 3, 3 => dvLmRun dvV4WideEqMir [] treeBorrows
      (dvStRawDyn dvV4WideEqMir 0 [(16384, dvTrKey), (16385, dvTrKey)])
  | _, _ => .unsupported


theorem dvLmObserve_v1_thinUnsize_table (tb : Bool) :
    dvLmObserve tb 0 0 = .widePtr 1 0 16384 ∧ dvLmObserve tb 0 1 = .widePtr 5 1 16384 ∧
    dvLmObserve tb 0 2 = .ub ∧ dvLmObserve tb 0 3 = .widePtr 1 0 16385 := by
  cases tb <;> exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem dvLmObserve_v2_dynUpcastAndNop_table (tb : Bool) :
    dvLmObserve tb 1 0 = .widePtr 1 0 16388 ∧ dvLmObserve tb 1 1 = .widePtr 1 0 16389 ∧
    dvLmObserve tb 1 2 = .ub ∧ dvLmObserve tb 1 3 = .widePtr 5 1 16384 := by
  cases tb <;> exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem dvLmObserve_v3_virtualDispatchAndProtector_table (tb : Bool) :
    dvLmObserve tb 2 0 = .u32Val 2 ∧ dvLmObserve tb 2 1 = .u32Val 69 ∧
    dvLmObserve tb 2 2 = .ub ∧
    dvLmObserve tb 2 3 = (if tb then DynVtLmObs.ub else DynVtLmObs.u32Val 77) := by
  cases tb <;> exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem dvLmObserve_v4_dynLayoutRawBorrowAndAddrEq_table (tb : Bool) :
    dvLmObserve tb 3 0 = .usizeVal 4 ∧ dvLmObserve tb 3 1 = .boolVal 1 ∧
    dvLmObserve tb 3 2 = .ub ∧ dvLmObserve tb 3 3 = .boolVal 0 := by
  cases tb <;> exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Exhaustive 32-key table**: for BOTH `treeBorrows` modes and all 16
`(variantIdx, caseIdx)` keys, `dvLmObserve` reduces (kernel `decide`) to the
frozen cross-root expectation. The only mode-sensitive key is `(2, 3)`. -/
theorem dvLmObserve_all_32_table (tb : Bool) :
    (dvLmObserve tb 0 0 = .widePtr 1 0 16384 ∧ dvLmObserve tb 0 1 = .widePtr 5 1 16384 ∧
     dvLmObserve tb 0 2 = .ub ∧ dvLmObserve tb 0 3 = .widePtr 1 0 16385) ∧
    (dvLmObserve tb 1 0 = .widePtr 1 0 16388 ∧ dvLmObserve tb 1 1 = .widePtr 1 0 16389 ∧
     dvLmObserve tb 1 2 = .ub ∧ dvLmObserve tb 1 3 = .widePtr 5 1 16384) ∧
    (dvLmObserve tb 2 0 = .u32Val 2 ∧ dvLmObserve tb 2 1 = .u32Val 69 ∧
     dvLmObserve tb 2 2 = .ub ∧
     dvLmObserve tb 2 3 = (if tb then DynVtLmObs.ub else DynVtLmObs.u32Val 77)) ∧
    (dvLmObserve tb 3 0 = .usizeVal 4 ∧ dvLmObserve tb 3 1 = .boolVal 1 ∧
     dvLmObserve tb 3 2 = .ub ∧ dvLmObserve tb 3 3 = .boolVal 0) :=
  ⟨dvLmObserve_v1_thinUnsize_table tb, dvLmObserve_v2_dynUpcastAndNop_table tb,
   dvLmObserve_v3_virtualDispatchAndProtector_table tb,
   dvLmObserve_v4_dynLayoutRawBorrowAndAddrEq_table tb⟩

/-- Mode sensitivity certified directly on `dvLmObserve`: the Crubit `c16` key
`(2, 3)` (aliased raw write while the receiver's `Frozen` reborrow carries the
active call protector) returns `77` without Tree Borrows and faults `.ub` under
Tree Borrows (vendored `Tree.LocationState.performAccess`: foreign write to a
protected `Frozen` tag). -/
theorem dvLmObserve_c16_mode_sensitivity :
    dvLmObserve false 2 3 = .u32Val 77 ∧ dvLmObserve true 2 3 = .ub :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- Outside the 16 corpus keys the observation fails closed. -/
theorem dvLmObserve_out_of_range (tb : Bool) (v c : Nat) (h : 4 ≤ v ∨ 4 ≤ c) :
    dvLmObserve tb v c = .unsupported := by
  rcases h with h | h
  · match v, c, h with
    | v + 4, _, _ => rfl
  · match v, c, h with
    | 0, c + 4, _ => rfl
    | 1, c + 4, _ => rfl
    | 2, c + 4, _ => rfl
    | 3, c + 4, _ => rfl
    | _ + 4, _, _ => rfl


/-! ## §6. Realizability Witnesses & Concrete Witnesses Beyond the Corpus -/

/-- Every decidable hypothesis of the §2 table laws holds on the frozen `dvVTables`
(no vacuous premises): 64-bit non-zero identifiers, `vtableEnvOk`, layout
coherence, well-formedness with alignment `≤ 2 ^ 29`, the `rigidTyEq`
faithfulness of the concrete `TyId`s of `u32` / `u64`, and the vendored
`VTableMachine.Registry.mergePersistent` / one entry per record. -/
theorem dv_table_hypotheses_realizable :
    (∀ v ∈ dvVTables, 0 < v.vtableAllocId ∧ v.vtableAllocId < 2 ^ 64) ∧
    vtableEnvOk 8 dvVTables 1 [] [] = true ∧
    dvLayoutCoherent dvVTables = true ∧
    (∀ v ∈ dvVTables, wfVTableEntry 8 v = true ∧ v.alignBytes ≤ 2 ^ 29) ∧
    (∀ w ∈ dvVTables, (dvConcreteTyId dvVTables w.concreteTy == dvConcreteTyId dvVTables (.uint .u32)) =
      rigidTyEq w.concreteTy (.uint .u32)) ∧
    (∀ w ∈ dvVTables, (dvConcreteTyId dvVTables w.concreteTy == dvConcreteTyId dvVTables (.uint .u64)) =
      rigidTyEq w.concreteTy (.uint .u64)) ∧
    (Miri.Interpreter.VTableMachine.Registry.mergePersistent (dvRegistry dvVTables)
      Miri.Interpreter.VTableMachine.Registry.empty).isOk = true ∧
    (dvRegistry dvVTables).entries.size = dvVTables.length := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Instances of the registry, reservation and upcast laws on the frozen table:
the `(u64, Tr)` vtable is allocation `16385`, and Trusted's diamond upcast
`dyn Sub -> dyn Base` resolves to the `(u32, Base)` vtable `16390`. -/
theorem dv_table_laws_instances :
    (dvRegistryLookup (dvRegistry dvVTables) ⟨16385, by decide⟩).map Prod.snd = some (dvKeyIdx dvVTables dvTrKey) ∧
    (dvRegistryReserve (dvRegistry dvVTables) (dvConcreteTyId dvVTables (.uint .u64))
      (dvKeyIdx dvVTables dvTrKey) 0).map (·.value.toNat) = some 16385 ∧
    ((dvVTables.find? (fun v => v.vtableId == 3)).bind fun src =>
      (resolveUpcastVTable? dvVTables [] src dvBaseKey).map (·.vtableAllocId)) = some 16390 ∧
    ((dvVTables.find? (fun v => v.vtableId == 3)).bind fun src =>
      (resolveUpcastVTable? dvVTables [] src dvAltKey).map (·.vtableAllocId)) = none := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Realizability of `step_dynTraitVTable_overlay_conservative`: its hypothesis
holds on the `c16` callee entry in basic mode (`*p = 99` is not a `dyn`
operation), and the overlay is non-trivial: on the `Unsize` statement of
`dvV1RefUnsizeMir` (a `dyn` operation) the base overlay fails closed while the
overlay commits the wide pointer. -/
theorem dv_conservative_law_realizable :
    dvIsDynOpAt dvV3ProtectedPokeMir false (dvStC16 true) = false ∧
    dvIsDynOpAt dvV3ProtectedPokeMir true (dvStC16 true) = true ∧
    dvIsDynOpAt dvV1RefUnsizeMir false
      (Miri.Interpreter.Step.step (annealStepHooksNullaryPtr dvV1RefUnsizeMir) ()
        (dvStThinLocal dvV1RefUnsizeMir 7 4 dvU32Ty dvRefU32Ty)).1 = true ∧
    (Miri.Interpreter.Step.step (annealStepHooksNullaryPtr dvV1RefUnsizeMir) ()
      (Miri.Interpreter.Step.step (annealStepHooksNullaryPtr dvV1RefUnsizeMir) ()
        (dvStThinLocal dvV1RefUnsizeMir 7 4 dvU32Ty dvRefU32Ty)).1).2 =
      .error (.unsupported "Unsize outside the array-to-slice fragment") ∧
    (Miri.Interpreter.Step.step (annealStepHooksDynTraitVTable dvV1RefUnsizeMir) ()
      (Miri.Interpreter.Step.step (annealStepHooksNullaryPtr dvV1RefUnsizeMir) ()
        (dvStThinLocal dvV1RefUnsizeMir 7 4 dvU32Ty dvRefU32Ty)).1).2 = .ok true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

/-- The Trusted `DynMemView` of the corpus argument-receiver state: no borrows,
no globals, the fixture as the visible body. -/
def dvTrustedView : DynMemView :=
  { borrows := [], globals := [], callerLocals := [], callStack := [], dynBodies := [],
    fnPtrs := [], nextAllocId := 1, activeProtectors := [], nextTag := 1 }

/-- The `(u32, Alt)` vtable record of `dvVTables` (allocation `16386`). -/
def dvAltVTable : CapturedVTable :=
  { vtableId := 2, vtableAllocId := 16386, concreteTy := .uint .u32, dynKey := dvAltKey,
    sizeBytes := 4, alignBytes := 4,
    slots := [.dropInPlace none, .size, .align, .method "dv::<u32 as Alt>::alt" []] }

/-- Realizability of `dvVTablePtrCheck_agrees_checkDynVTablePtr` on the corpus
key `(2, 2)` (receiver metadata `(u32, Alt)` used as `dyn Tr`): every hypothesis
holds, and both authorities report UB for the expected key `Tr` and success
(concrete type `u32`) for `Alt`. -/
theorem dv_vtable_check_agreement_realizable :
    dynVTableEnv? (some dvV3ArgCallMir) dvTrustedView 8 = some (dvVTables, []) ∧
    lookupBorrow dvTrustedView.borrows (⟨16386, 0⟩ : ProvenancePtr).tag = none ∧
    lookupVTableByAllocId dvVTables 16386 = some dvAltVTable ∧
    (dvStPointee dvV3ArgCallMir 16386).machine.lookupBaseAddr ⟨16386, by decide⟩ =
      some (annealStackBaseAddr ⟨16386, by decide⟩) ∧
    dvTrustedCheckClass (checkDynVTablePtr (some dvV3ArgCallMir) dvTrustedView 8
      (.ptr ⟨16386, 0⟩ 8) dvTrKey) = 1 ∧
    dvMiriResultClass (Miri.Interpreter.VTable.getPtrVTableTypeRead (dvVTableReadHooks dvVTables) ()
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr ⟨16386, by decide⟩),
        some (.concrete ⟨16386, by decide⟩ .one)⟩ (some (dvKeyIdx dvVTables dvTrKey))
      (dvStPointee dvV3ArgCallMir 16386)) = 1 ∧
    dvTrustedCheckClass (checkDynVTablePtr (some dvV3ArgCallMir) dvTrustedView 8
      (.ptr ⟨16386, 0⟩ 8) dvAltKey) = 0 ∧
    dvMiriResultClass (Miri.Interpreter.VTable.getPtrVTableTypeRead (dvVTableReadHooks dvVTables) ()
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr ⟨16386, by decide⟩),
        some (.concrete ⟨16386, by decide⟩ .one)⟩ (some (dvKeyIdx dvVTables dvAltKey))
      (dvStPointee dvV3ArgCallMir 16386)) = 0 := by
  refine ⟨rfl, rfl, rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

/-- Realizability of `dvGetMethod_eq` / `dvGetMethod_nonMethod_ub` with
vendored `VTable.getMethod` on the `(u32, Tr)` vtable: slot `3` (`get`) is a
method, while the header slot `1` (`MetadataSize`) and the out-of-bounds slot
`9` are UB. -/
theorem dv_getMethod_realizable :
    let ptr : Miri.Memory.Pointer (Option AnnealProv) :=
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr ⟨16384, by decide⟩),
        some (.concrete ⟨16384, by decide⟩ .one)⟩
    let st := dvStPointee dvV3ArgCallMir 16384
    let gm := fun idx => Miri.Interpreter.VTable.getMethod (dvVTableHooks dvVTables)
      (fun _ _ _ => pure ()) () ptr (dvKeyIdx dvVTables dvTrKey) (some (dvKeyIdx dvVTables dvTrKey))
      idx 0 { kind := .Item 0, args := #[] } (dvCallerAbi [] (translateTyOverlay dvU32Ty)) st
    dvMiriResultClass (gm 3) = 0 ∧ dvMiriResultClass (gm 1) = 1 ∧ dvMiriResultClass (gm 9) = 1 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Concrete witnesses beyond the corpus** (unmodified vendored `Step.step`):
1. diamond upcast `&dyn Sub -> &dyn Base` (primary-prefix chain) yields the
   `(u32, Base)` vtable `16390`;
2. `&dyn Sub -> &dyn Alt` (not a supertrait) fails closed (`.unsupported`, the
   vendored prefix assertion);
3. virtual calls through the out-of-bounds slot `9` and the `MetadataSize`
   header slot `1` are UB (vendored `VirtualCalls.resolveVirtual`);
4. `align_of_val(&dyn Tr)` is `4`;
5. `&raw const (*r)` on a `Disabled`-tagged `&dyn Tr` succeeds in both modes
   (no Tree Borrows access) and faults on a dead pointee;
6. `Box<u32> -> Box<dyn Tr>` fails closed (`.unsupported`, `C1`). -/
theorem dv_extra_witnesses (tb : Bool) :
    dvLmRun dvV2UpcastBaseMir [] tb (dvStUpcast dvV2UpcastBaseMir) = .widePtr 1 0 16390 ∧
    dvLmRun dvV2UpcastAltMir [] tb (dvStUpcast dvV2UpcastAltMir) = .unsupported ∧
    dvLmRun dvV3CallOobMir dvCallees tb (dvStCall dvV3CallOobMir 7 4 dvU32Ty dvRefU32Ty) = .ub ∧
    dvLmRun dvV3CallHdrMir dvCallees tb (dvStCall dvV3CallHdrMir 7 4 dvU32Ty dvRefU32Ty) = .ub ∧
    dvLmRun dvV4AlignSafeMir [] tb (dvStPointee dvV4AlignSafeMir 16384) = .usizeVal 4 ∧
    dvLmRun (dvV4RawBorrowMir .not (dvRefDynTy dvTrKey) (dvRawConstDynTy dvTrKey)) [] tb
      (dvStPointee (dvV4RawBorrowMir .not (dvRefDynTy dvTrKey) (dvRawConstDynTy dvTrKey)) 16384
        (some dvDisabledTree) retagChildTag (bt := some (dvRecvBorrowState false))) =
      .widePtr 1 0 16384 ∧
    dvLmRun (dvV4RawBorrowMir .not (dvRefDynTy dvTrKey) (dvRawConstDynTy dvTrKey)) [] tb
      (dvStPointee (dvV4RawBorrowMir .not (dvRefDynTy dvTrKey) (dvRawConstDynTy dvTrKey)) 16384
        (live := false)) = .ub ∧
    dvLmRun (dvV1ArgUnsizeMir (dvBoxTy (.uint .u32)) (dvBoxTy (.dynamic dvTrKey))) [] tb
      (dvMkState (dvV1ArgUnsizeMir (dvBoxTy (.uint .u32)) (dvBoxTy (.dynamic dvTrKey)))
        #[dvUninit (dvBoxTy (.dynamic dvTrKey)),
          dvImmLocal (.scalar (dvPtrScalar dvAid5 dvBase5)) (dvBoxTy (.uint .u32))] dvMachine5) =
      .unsupported := by
  cases tb <;>
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Crubit `c16` witnesses**: the full caller `dvV3PokeCallerMir` (corpus key
`(2, 3)`: the protector is installed by the virtual call's function-entry
retag) and the callee-entry scenario `dvV3ProtectedPokeMir` from the Trusted
key's state (receiver tag pre-protected) both return `77` without Tree Borrows
and fault under Tree Borrows; without the protector, the same foreign write
merely disables the receiver tag (`77` under Tree Borrows too), so the UB is
caused by the call protector. -/
theorem dv_c16_witnesses :
    dvLmRun dvV3PokeCallerMir dvCallees false dvStC16Caller = .u32Val 77 ∧
    dvLmRun dvV3PokeCallerMir dvCallees true dvStC16Caller = .ub ∧
    dvLmRun dvV3ProtectedPokeMir dvCallees false (dvStC16 true) = .u32Val 77 ∧
    dvLmRun dvV3ProtectedPokeMir dvCallees true (dvStC16 true) = .ub ∧
    dvLmRun dvV3ProtectedPokeMir dvCallees true (dvStC16 false) = .u32Val 77 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

/-! ### B1 Hardening Witnesses: `kani#5216` Uninhabited, `C2` TB Unsize & `&raw mut` Gate, `C3` Pre-Unlinked Gate, Raw Intrinsics, and Vendored `Cast.unsizeInto` `.adt` / `DispatchFromDyn` -/

/-- Uninhabited concrete type (`!`) vtable for `dyn Tr` (`kani#5216`). -/
def dvUninhabitedVTables : List CapturedVTable :=
  [ { vtableId := 0, vtableAllocId := 16384, concreteTy := .never, dynKey := dvTrKey,
      sizeBytes := 0, alignBytes := 1, isUninhabited := true,
      slots := [.dropInPlace none, .size, .align] } ]

/-- `fn(p: P) -> D { p as D }` with the uninhabited `(Never, dyn Tr)` vtable table. -/
def dvNeverUnsizeMir (srcTy dstTy : Ty) : CapturedMir :=
  { dvV1ArgUnsizeMir srcTy dstTy with vtables := dvUninhabitedVTables }

/-- **`kani#5216` uninhabited concrete type behind `&dyn Trait` (LM authority)**:
unsizing a live, aligned `&!` to `&dyn Tr` faults `.ub` in BOTH modes
(`dvValidateDynPtr` rejects `concreteLay.layout.uninhabited = true`), whereas
raw `*const ! -> *const dyn Tr` succeeds in BOTH modes. -/
theorem dv_kani5216_uninhabited_witness (tb : Bool) :
    let refMir := dvNeverUnsizeMir { kind := .ref .not .never, layoutIdx := 0 } (dvRefDynTy dvTrKey)
    let rawMir := dvNeverUnsizeMir { kind := .rawPtr .not .never, layoutIdx := 0 } (dvRawConstDynTy dvTrKey)
    let mach := dvMachine dvUninhabitedVTables (dvLiveU32 dvAid1 7 none)
      #[⟨dvAid1, annealStackBaseAddr dvAid1⟩]
    let stRef := dvMkState refMir #[dvUninit (dvRefDynTy dvTrKey),
      dvImmLocal (.scalar (dvPtrScalar dvAid1 (annealStackBaseAddr dvAid1)))
        { kind := .ref .not .never, layoutIdx := 0 }] mach
    let stRaw := dvMkState rawMir #[dvUninit (dvRawConstDynTy dvTrKey),
      dvImmLocal (.scalar (dvPtrScalar dvAid1 (annealStackBaseAddr dvAid1)))
        { kind := .rawPtr .not .never, layoutIdx := 0 }] mach
    dvLmRun refMir [] tb stRef = .ub ∧
    dvLmRun rawMir [] tb stRaw = .widePtr 1 0 16384 := by
  cases tb <;> exact ⟨by decide +kernel, by decide +kernel⟩

/-- Initial state for unsizing a thin reference/pointer `_1` pointing to live
local `_2 : u32 = 7` under Tree Borrows tree `tree` and tag `tag`. -/
def dvStThinPointeeTb (body : CapturedMir) (srcTy : Ty) (tree : Miri.TreeBorrows.BorrowTree)
    (tag : Miri.Memory.BorTag) : AnnealStepState :=
  dvMkState body
    #[dvUninit ((body.localDecls.head?.map (·.ty)).getD dvU32Ty),
      dvImmLocal (.scalar (dvPtrScalar dvAid1 (annealStackBaseAddr dvAid1) tag)) srcTy,
      dvIndirectLocal dvAid1]
    (dvMachine dvVTables (dvLiveU32 dvAid1 7 (some tree)) #[⟨dvAid1, annealStackBaseAddr dvAid1⟩]
      (some (dvRecvBorrowState false)))

/-- **`C2` Tree Borrows reference-unsizing gate & `&raw mut` mutability gate (LM)**:
1. Under `treeBorrows = true`, unsizing a `Disabled`-tagged `&u32 -> &dyn Tr`
   and a `Frozen`-tagged `&mut u32 -> &mut dyn Tr` both fault `.ub` through
   vendored `Miri.TreeBorrows`, whereas raw `*const u32 -> *const dyn Tr` with
   the same `Disabled` tag succeeds in BOTH modes;
2. `&raw mut (*r)` on an immutable `&dyn Tr` or `*const dyn Tr` fails closed
   (`.unsupported`), while `&raw mut (*r)` on `&mut dyn Tr` succeeds. -/
theorem dv_c2_tb_unsize_and_raw_mut_witness :
    let refMir := dvMkBody "dv::v1_ref_tb" [dvDecl (dvRefDynTy dvTrKey), dvDecl dvRefU32Ty, dvDecl dvU32Ty] 1
      [dvBb [dvSt (.assign (dvLoc 0) (.cast (.pointerCoercion "Unsize") (.copy (dvLoc 1)) (dvRefDynTy dvTrKey)))] .return_]
    let mutMir := dvMkBody "dv::v1_mut_tb" [dvDecl (dvRefMutDynTy dvTrKey), dvDecl dvRefMutU32Ty, dvDecl dvU32Ty] 1
      [dvBb [dvSt (.assign (dvLoc 0) (.cast (.pointerCoercion "Unsize") (.copy (dvLoc 1)) (dvRefMutDynTy dvTrKey)))] .return_]
    let rawMir := dvMkBody "dv::v1_raw_tb" [dvDecl (dvRawConstDynTy dvTrKey), dvDecl dvRawConstU32Ty, dvDecl dvU32Ty] 1
      [dvBb [dvSt (.assign (dvLoc 0) (.cast (.pointerCoercion "Unsize") (.copy (dvLoc 1)) (dvRawConstDynTy dvTrKey)))] .return_]
    let rawMutShared := dvV4RawBorrowMir .mut (dvRefDynTy dvTrKey) (dvRawMutDynTy dvTrKey)
    let rawMutConst := dvV4RawBorrowMir .mut (dvRawConstDynTy dvTrKey) (dvRawMutDynTy dvTrKey)
    let rawMutMut := dvV4RawBorrowMir .mut (dvRefMutDynTy dvTrKey) (dvRawMutDynTy dvTrKey)
    dvLmRun refMir [] true (dvStThinPointeeTb refMir dvRefU32Ty dvDisabledTree retagChildTag) = .ub ∧
    dvLmRun mutMir [] true (dvStThinPointeeTb mutMir dvRefMutU32Ty dvRecvTree retagChildTag) = .ub ∧
    dvLmRun rawMir [] false (dvStThinPointeeTb rawMir dvRawConstU32Ty dvDisabledTree retagChildTag) = .widePtr 1 0 16384 ∧
    dvLmRun rawMir [] true (dvStThinPointeeTb rawMir dvRawConstU32Ty dvDisabledTree retagChildTag) = .widePtr 1 0 16384 ∧
    dvLmRun rawMutShared [] false (dvStPointee rawMutShared 16384) = .unsupported ∧
    dvLmRun rawMutConst [] false (dvStRawDyn rawMutConst 0 [(16384, dvTrKey)]) = .unsupported ∧
    dvLmRun rawMutMut [] false
      (dvMkState rawMutMut #[dvUninit (dvRawMutDynTy dvTrKey),
        dvImmLocal (dvWideImm (dvPtrScalar dvAid1 (annealStackBaseAddr dvAid1)) 16384) (dvRefMutDynTy dvTrKey),
        dvIndirectLocal dvAid1]
        (dvMachine dvVTables (dvLiveU32 dvAid1 7 none) #[⟨dvAid1, annealStackBaseAddr dvAid1⟩])) = .widePtr 1 0 16384 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **`C3` pre-unlinked validity gate, `Disabled` virtual receiver TB gate, &
raw `core::intrinsics::{size_of_val, align_of_val}` (LM)**:
1. With NO callees linked (`callees := []`), a virtual call on a dead/dangling
   `&dyn Tr` receiver faults `.ub` (never `.unsupported`, `C3`), while a live
   receiver fails closed `.unsupported`;
2. Under `treeBorrows = true`, calling `r.get(5)` on a `Disabled`-tagged
   `&dyn Tr` receiver faults `.ub` (parent Tree Borrows read checked before
   retag);
3. Raw `core::intrinsics::{size_of_val, align_of_val}` on `*const dyn Tr`
   return `8` / `8` for `u64` and `4` / `4` for `u32`. -/
theorem dv_c3_and_raw_intrinsics_witness :
    let intrSz64 := dvV4IntrLayoutMir dvU64Ty dvRefU64Ty "core::intrinsics::size_of_val"
    let intrAl64 := dvV4IntrLayoutMir dvU64Ty dvRefU64Ty "core::intrinsics::align_of_val"
    let intrSz32 := dvV4IntrLayoutMir dvU32Ty dvRefU32Ty "core::intrinsics::size_of_val"
    let intrAl32 := dvV4IntrLayoutMir dvU32Ty dvRefU32Ty "core::intrinsics::align_of_val"
    let stIntr64 (b : CapturedMir) := dvMkState b
      #[dvUninit dvUsizeTy, dvIndirectLocal dvAid1 .one dvU64Ty, dvUninit dvRefU64Ty,
        dvUninit (dvRefDynTy dvTrKey), dvUninit (dvRawConstDynTy dvTrKey)]
      (dvMachine dvVTables (dvLiveUInt dvAid1 64 8 none) #[⟨dvAid1, annealStackBaseAddr dvAid1⟩])
    let stIntr32 (b : CapturedMir) := dvMkState b
      #[dvUninit dvUsizeTy, dvIndirectLocal dvAid1 .one dvU32Ty, dvUninit dvRefU32Ty,
        dvUninit (dvRefDynTy dvTrKey), dvUninit (dvRawConstDynTy dvTrKey)]
      (dvMachine dvVTables (dvLiveU32 dvAid1 7 none) #[⟨dvAid1, annealStackBaseAddr dvAid1⟩])
    dvLmRun dvV3ArgCallMir [] false (dvStPointee dvV3ArgCallMir 16384 (live := false)) = .ub ∧
    dvLmRun dvV3ArgCallMir [] false (dvStPointee dvV3ArgCallMir 16384 (live := true)) = .unsupported ∧
    dvLmRun dvV3ArgCallMir dvCallees true
      (dvStPointee dvV3ArgCallMir 16384 (some dvDisabledTree) retagChildTag
        (bt := some (dvRecvBorrowState false))) = .ub ∧
    dvLmRun intrSz64 [] false (stIntr64 intrSz64) = .usizeVal 8 ∧
    dvLmRun intrAl64 [] false (stIntr64 intrAl64) = .usizeVal 8 ∧
    dvLmRun intrSz32 [] false (stIntr32 intrSz32) = .usizeVal 4 ∧
    dvLmRun intrAl32 [] false (stIntr32 intrAl32) = .usizeVal 4 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Synthetic `TyId`s for exercising vendored `Cast.unsizeInto`'s `.adt` structural
field-traversal arm and `VirtualCalls.resolveVirtual`'s `DispatchFromDyn` `.other`
unwrapping arm directly on `Pin<&mut T>` / `Pin<&mut dyn Tr>` and negative ADTs. -/
def dvPinThinTyId : Miri.MIR.TyId := 500001
def dvPinDynTyId : Miri.MIR.TyId := 500002
def dvPairThinTyId : Miri.MIR.TyId := 500003
def dvPairDynTyId : Miri.MIR.TyId := 500004
def dvBoxDynTyId : Miri.MIR.TyId := 500005

def dvThinRefU32Layout : Miri.ABI.TyAndLayout Miri.MIR.TyId :=
  translateTyOverlay dvRefMutU32Ty emptyLayoutTable

def dvWideRefDynLayout : Miri.ABI.TyAndLayout Miri.MIR.TyId :=
  translateTyOverlay (dvRefMutDynTy dvTrKey) emptyLayoutTable

def dvAdtLayout (tyId : Miri.MIR.TyId) (fieldCount : Nat) (sz : UInt64) :
    Miri.ABI.TyAndLayout Miri.MIR.TyId :=
  let offs : Array Miri.ABI.Size :=
    ((List.range fieldCount).map fun i => Miri.ABI.Size.ofBytes (UInt64.ofNat (i * 8))).toArray
  let ord : Array Nat := (List.range fieldCount).toArray
  { ty := tyId
    layout := { zstLayoutData with
      size := Miri.ABI.Size.ofBytes sz, align := ⟨Miri.ABI.Align.EIGHT⟩,
      unadjustedAbiAlign := Miri.ABI.Align.EIGHT,
      fields := .Arbitrary offs ord } }

/-- `CastHooks` extending `annealCastHooksDynTraitVTable` with 1-field `Pin`
(ADT 1), 2-field `Pair` (ADT 2), and mismatched `Box` (ADT 3) layouts to
exercise vendored `Miri.Interpreter.Cast.unsizeInto`'s `.adt` branch directly. -/
def dvAdtUnsizeCastHooks :
    Miri.Interpreter.CastHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealCastHooksDynTraitVTable dvV1RefUnsizeMir
  { base with
    typeInfo := fun c tyId =>
      if tyId == dvPinThinTyId || tyId == dvPinDynTyId then pure (.adt 1)
      else if tyId == dvPairThinTyId || tyId == dvPairDynTyId then pure (.adt 2)
      else if tyId == dvBoxDynTyId then pure (.adt 3)
      else base.typeInfo c tyId
    lockstepTails := fun _ _ _ => pure (dvConcreteTyId dvVTables (.uint .u32), dvDynTailTyId dvVTables dvTrKey)
    fieldLayout := fun _ target _ =>
      if target.ty == dvPinDynTyId || target.ty == dvPairDynTyId then pure dvWideRefDynLayout
      else throw (.invalidProgram "unexpected ADT field layout")
    projectRead := fun _ src _ => pure ⟨src.op, dvThinRefU32Layout⟩
    projectWrite := fun _ dest _ => pure { dest with layout := dvWideRefDynLayout } }

/-- **`Cast.unsizeInto` `.adt` structural unsizing & `VirtualCalls.resolveVirtual`
`DispatchFromDyn` receiver unwrapping witnesses (vendored `Miri.Interpreter`)**:
1. Positive 1-field transparent ADT (`Pin<&mut u32> -> Pin<&mut dyn Tr>`) runs
   vendored `Miri.Interpreter.Cast.unsizeInto`'s `.adt` arm and writes the wide
   pointer `(data, 16384)` into `_0`;
2. Negative 2-field ADT (`Pair<&mut u32, &mut u32> -> Pair<&mut dyn Tr, &mut dyn Tr>`)
   is rejected by vendored `Cast.unsizeInto` with
   `"unsize_into: more than one field to cast"`;
3. Negative mismatched ADT (`Pin<&mut u32> -> Box<dyn Tr>`) is rejected by
   vendored `Cast.unsizeInto` with
   `"unsizing requires identical ADT definitions"`;
4. Positive `DispatchFromDyn` receiver (`Pin<&mut dyn Tr>`) runs vendored
   `Miri.Interpreter.VirtualCalls.resolveVirtual`'s `.other` (`nonOneZstField` +
   `projectField`) arm and resolves `Tr::get` to `dv::<u32 as Tr>::get` with the
   narrowed thin pointer. -/
theorem dv_pin_adt_unsize_and_dispatch_from_dyn_witness :
    let st0 := dvStThinLocal dvV1RefUnsizeMir 7 4 dvU32Ty dvRefU32Ty
    let srcPtr := dvPtrScalar dvAid1 (annealStackBaseAddr dvAid1)
    let destPin : Miri.Interpreter.RuntimePlace AnnealProv :=
      { ref := .local 0 0 none (.ofAllocationToken 0), layout := dvAdtLayout dvPinDynTyId 1 16 }
    let rPin := Miri.Interpreter.Cast.unsizeInto dvAdtUnsizeCastHooks () 4
      ⟨.immediate (.scalar srcPtr), dvAdtLayout dvPinThinTyId 1 8⟩
      (dvAdtLayout dvPinDynTyId 1 16) destPin st0
    let pinOk : Bool := match rPin with
      | .ok () st1 =>
        match st1.stack.currentFrame?.bind (fun f => (f.getLocalOperand 0).toOption) with
        | some (.immediate (.scalarPair d v)) =>
          dvDecodePtr st1.machine d == some (1, 0) && dvDecodePtr st1.machine v == some (16384, 0)
        | _ => false
      | .error _ _ => false
    let rPair := Miri.Interpreter.Cast.unsizeInto dvAdtUnsizeCastHooks () 4
      ⟨.immediate (.scalar srcPtr), dvAdtLayout dvPairThinTyId 2 16⟩
      (dvAdtLayout dvPairDynTyId 2 32)
      { ref := .local 0 0 none (.ofAllocationToken 0), layout := dvAdtLayout dvPairDynTyId 2 32 } st0
    let pairMsg : Option String := match rPair with
      | .error (.invalidProgram msg) _ => some msg
      | _ => none
    let rMismatch := Miri.Interpreter.Cast.unsizeInto dvAdtUnsizeCastHooks () 4
      ⟨.immediate (.scalar srcPtr), dvAdtLayout dvPinThinTyId 1 8⟩
      (dvAdtLayout dvBoxDynTyId 1 16)
      { ref := .local 0 0 none (.ofAllocationToken 0), layout := dvAdtLayout dvBoxDynTyId 1 16 } st0
    let mismatchMsg : Option String := match rMismatch with
      | .error (.invalidProgram msg) _ => some msg
      | _ => none
    let pinWideImm := dvWideImm srcPtr 16384
    let baseVh := dvVirtualHooks dvVTables dvVirtualMethods (dvKeyIdx dvVTables dvTrKey)
    let pinVh : Miri.Interpreter.VirtualCalls.Hooks AnnealProv AnnealStepState Unit Unit :=
      { baseVh with
        compiler := { baseVh.compiler with
          classifyReceiver := fun ty =>
            if ty == dvPinDynTyId then pure .other else baseVh.compiler.classifyReceiver ty
          fieldLayout := fun lay idx =>
            if lay.ty == dvPinDynTyId && idx == 0 then pure dvWideRefDynLayout
            else baseVh.compiler.fieldLayout lay idx }
        projectField := fun _ op idx =>
          if op.layout.ty == dvPinDynTyId && idx == 0 then pure ⟨.immediate pinWideImm, dvWideRefDynLayout⟩
          else throw (.unsupported "unexpected pin projectField") }
    let pinFnArg : Miri.Interpreter.FnArg AnnealProv :=
      .Copy ⟨.immediate pinWideImm, dvAdtLayout dvPinDynTyId 1 16⟩
    let virtInst : Miri.Interpreter.CallInstance :=
      { kind := .Virtual dvVirtualBase 3, args := #[.Type (dvDynTailTyId dvVTables dvTrKey)] }
    let rDisp := Miri.Interpreter.VirtualCalls.resolveVirtual pinVh () 4 virtInst dvVirtualBase 3
      (dvCallerAbi [⟨pinWideImm, dvAdtLayout dvPinDynTyId 1 16⟩] (translateTyOverlay dvU32Ty))
      #[pinFnArg] st0
    let dispOk : Bool := match rDisp with
      | .ok (inst, _, args') _ =>
        dvMethodOfInstance? dvVTables inst == some "dv::<u32 as Tr>::get" && args'.size == 1
      | .error _ _ => false
    pinOk = true ∧
    pairMsg = some "unsize_into: more than one field to cast" ∧
    mismatchMsg = some "unsizing requires identical ADT definitions" ∧
    dispOk = true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## §7. Documented Cross-Authority Divergences & Modeling Notes

Cross-authority divergences of `PROTOTYPE_REPORT.md` §5, as they surface on this
authority:

1. **Non-method / out-of-bounds slot**: vendored `VirtualCalls.resolveVirtual`
   (and `VTable.getMethod`) report UB (`dyn call trying to call something that is
   not a method`), as Trusted `evalVirtualCall` does (`dvGetMethod_nonMethod_ub`,
   `dv_extra_witnesses`); upstream MiniRust instead stops with
   `Stop.specPanic`.
2. **No Tree Borrows read on safe `size_of_val(&dyn)` / `&raw const (*r)`**: the
   function-entry validity of `val : &dyn K` and the safe-reference check of a
   raw borrow (`dvValidateDynPtr ... checkTB := false`, `refDataValidNoTB`) check
   liveness, bounds, non-null, inhabitedness, and alignment only; a `Disabled`
   tag succeeds (keys `(3, 0)`, `dv_extra_witnesses`), whereas reference unsizing
   (`dv_c2_tb_unsize_and_raw_mut_witness`) and virtual-call entry
   (`dv_c3_and_raw_intrinsics_witness`, `dv_c16_witnesses`) enforce vendored
   Tree Borrows permissions (`npApplyTreeBorrowsReadAt` / `npApplyTreeBorrowsWriteAt`)
   and receiver protectors (`dvRetagReceiver`).
3. **`&raw const (*r)` on a dead pointee**: this authority follows the
   `checkSafeRefDerefOk` convention adopted by the TCB (UB, `dv_extra_witnesses`);
   real Miri's place projection does not validate `r` before an access.
4. **Uninhabited concrete types** (`kani#5216`): `dvValidateDynPtr` enforces
   `concreteLay.layout.uninhabited = false` on safe references, rejecting
   `&! -> &dyn Trait` as `.ub` while accepting `*const ! -> *const dyn Trait`
   (`dv_kani5216_uninhabited_witness`).
5. **`Classical.choice`** enters only through vendored
   `Miri.Memory.MemoryState.empty` (the initial machine), never through a law.

Further modeling notes and known gaps of this authority:

* Unknown vtable allocations: vendored `getPtrVTableTypeRead` reports UB for any
  metadata pointer that names no registered vtable; Trusted reports `.ub` only in
  the reserved vtable range and fails closed (`.unsupported`) elsewhere.
* Upcasts / unrelated traits: an ill-typed `dyn Sub -> dyn Alt` fails closed
  through the vendored prefix assertion (`invalidProgram`, observed
  `.unsupported`).
* The virtual receiver's Tree Borrows retag marks the whole receiver
  allocation (the corpus pointee) and its protector is not released on return.
* Direct `Cast.unsizeInto` `.adt` structural unsizing (`Pin<&mut u32> -> Pin<&mut dyn Tr>`,
  negative 2-field `Pair`, negative mismatched `Pin -> Box`) and
  `VirtualCalls.resolveVirtual` `DispatchFromDyn` receiver unwrapping are
  verified directly through vendored `Miri.Interpreter` (`dv_pin_adt_unsize_and_dispatch_from_dyn_witness`);
  full-body `dvV1PinUnsizeMir` does not run through the base translator because
  §0 uses `emptyLayoutTable`.
* The Tree Borrows write of a bare-dereference destination
  (`dvTreeBorrowsDerefWrite`) reuses `npApplyTreeBorrowsWriteAt`, whose UB message
  names `unwrapUnsafeBinder` places; the outcome class is what is observed.
-/
/-! ## §8. Exhaustive Axiom, Non-Triviality, & Import-Isolation Audit -/

section AxiomAudit
open Lean Elab Command

elab "#assert_dyn_trait_vtable_lm_audit" : command => do
  let env ← getEnv
  for modName in env.header.moduleNames do
    if (`MiniRustSpec).isPrefixOf modName || (`Anneal).isPrefixOf modName then
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
    throwError "LeanMiriSpec.DynTraitVTableLM: 0 declarations found"
  logInfo m!"LeanMiriSpec.DynTraitVTableLM: verified {checked} declarations (sorry_free=true, import_isolated=true, 0 trivial, 0 ofReduceBool)"

#assert_dyn_trait_vtable_lm_audit

end AxiomAudit

end LeanMiriSpec.DynTraitVTableLM
