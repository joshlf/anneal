/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Anneal.Prototypes.DynTraitUnsizeProto

/-!
# `dyn Trait` Unsizing & VTable Dispatch Prototype: Campaign #22 Tests

Tests of `Anneal.Prototypes.DynTraitUnsizeProto` (Track P, `PROTOTYPE_NO_MERGE`).

1. **§1 Fixtures.** `Runtime(PostCleanup)`-style MIR of the Campaign #22
   reproducer (`finding_0000/repro.rs:271-341`): the driver
   `__anneal_vt_driver_43543`, the five trait method bodies, and the captured
   vtables.
2. **§2 End-to-end reproducer.** `Trusted`'s `stepMirFn` is UB at
   `&__vt_rec as &dyn __AnnealVtableTrait43543`; with the prototype rules the
   driver returns `30u32` on `(7, 24)` and the outer function returns `20u32`
   (`MIRI_PASS:scalar:20:4`), with sensitivity guards.
3. **§3 Negative canaries (a)-(e).**
4. **§4 Pillar witnesses**: unsizing, dynamic layout, `addr_eq`, MiniRust
   `Mach` / `MachTB`, ranged Tree Borrows receiver protector.
5. **§5 Cross-root kernel bridge** over vendored `Miri.Interpreter.*`.
6. **§6 Axiom and vacuity audit.**

Every evaluation is by the Lean kernel (`decide +kernel` or `rfl`); there is no
`native_decide`.
-/

namespace Anneal.Prototypes.DynTraitUnsizeProtoTests

set_option Elab.async false

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.Prototypes.DynTraitUnsizeProto

/-! ## §1. Campaign #22 fixtures (`finding_0000/repro.rs:271-341`) -/

namespace Fx

/-- Trait and type keys of the reproducer. -/
def traitKey : String := "miri_diff_corpus::__AnnealVtableTrait43543"
def altKey : String := "miri_diff_corpus::__AnnealVtableAlt43543"
def recKey : String := "miri_diff_corpus::__AnnealVtableReceiver43543"
def otherKey : String := "miri_diff_corpus::__AnnealVtableAltReceiver43543"

def u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
def recTy : Ty := { kind := .adt recKey [], layoutIdx := 1 }
def otherTy : Ty := { kind := .adt otherKey [], layoutIdx := 2 }
def refRecTy : Ty := { kind := .ref .not (.adt recKey []), layoutIdx := 3 }
def refOtherTy : Ty := { kind := .ref .not (.adt otherKey []), layoutIdx := 4 }
def refDynTy : Ty := { kind := .ref .not (.dynamic traitKey), layoutIdx := 5 }
def refAltTy : Ty := { kind := .ref .not (.dynamic altKey), layoutIdx := 5 }
def boolTy : Ty := { kind := .bool, layoutIdx := 6 }
def rawDynTy : Ty := { kind := .rawPtr .not (.dynamic traitKey), layoutIdx := 5 }
def rawAltTy : Ty := { kind := .rawPtr .not (.dynamic altKey), layoutIdx := 5 }
def rawUnitTy : Ty := { kind := .rawPtr .not (.tuple []), layoutIdx := 8 }

def u32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 },
    backendRepr := .scalar (.initialized (.int 32 false) { start := 0, end_ := 4294967295 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def ptrLayout (pointee : Nat) : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 8 },
    backendRepr :=
      .scalar (.initialized (.pointer 0) { start := 1, end_ := 18446744073709551615 }),
    fields := .primitive, variants := .single 0, isUninhabited := false,
    fieldLayouts := [pointee] }

def boolLayout : TypeLayout :=
  { size := { bytes := 1 }, align := { bytes := 1 },
    backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 1 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def widePtrLayout : TypeLayout :=
  { size := { bytes := 16 }, align := { bytes := 8 },
    backendRepr :=
      .scalarPair (.initialized (.pointer 0) { start := 1, end_ := 18446744073709551615 })
        (.initialized (.pointer 0) { start := 1, end_ := 18446744073709551615 }),
    fields := .arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1],
    variants := .single 0, isUninhabited := false }

/-- Layout table shared by the reproducer bodies:
`0` `u32`, `1` `Receiver { bias }` (4 bytes, align 4), `2`
`AltReceiver { pad, bias }` (8 bytes, align 4, `bias` at offset 4), `3`
`&Receiver`, `4` `&AltReceiver`, `5` wide pointer, `6` `bool`, `7` zero-sized
`FnDef`, `8` thin raw pointer. -/
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ u32Layout,
        { size := { bytes := 4 }, align := { bytes := 4 },
          backendRepr := .scalar (.initialized (.int 32 false) { start := 0, end_ := 4294967295 }),
          fields := .arbitrary [{ bytes := 0 }] [0], variants := .single 0,
          isUninhabited := false, fieldLayouts := [0] },
        { size := { bytes := 8 }, align := { bytes := 4 },
          backendRepr :=
            .scalarPair (.initialized (.int 32 false) { start := 0, end_ := 4294967295 })
              (.initialized (.int 32 false) { start := 0, end_ := 4294967295 }),
          fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }] [0, 1], variants := .single 0,
          isUninhabited := false, fieldLayouts := [0, 0] },
        ptrLayout 1, ptrLayout 2, widePtrLayout,
        boolLayout,
        { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory,
          fields := .arbitrary [] [], variants := .single 0, isUninhabited := false },
        ptrLayout 7 ] }

def u32Abi : ArgAbi := { layout := u32Layout, mode := .direct }
def ptrAbi : ArgAbi := { layout := ptrLayout 1, mode := .direct }

def cU32 (n : Nat) : Operand :=
  .constant { ty := u32Ty, val := .scalar (.int { bits := n, sizeBytes := 4 }) }
def cp (l : Nat) : Operand := .copy { local_ := l, projection := [] }
def mv (l : Nat) : Operand := .move { local_ := l, projection := [] }
def loc (l : Nat) : Place := { local_ := l, projection := [] }
def asg (l : Nat) (rv : Rvalue) : Statement := { kind := .assign (loc l) rv, span := "<vt>" }
def live (l : Nat) : Statement := { kind := .storageLive l, span := "<vt>" }
def decl (ty : Ty) : LocalDecl := { mutability := .mut, ty := ty, debugName := none }
def term (k : TerminatorKind) : Terminator := { kind := k, span := "<vt>" }
def bb (stmts : List Statement) (k : TerminatorKind) : BasicBlockData :=
  { statements := stmts, terminator := term k, isCleanup := false }

/-- `(*_l).field : u32` read through the receiver reference. -/
def selfField (l field : Nat) : Operand :=
  .copy { local_ := l, projection := [.deref, .field field u32Ty] }

/-- `<Self as Trait>::method` call-site function operand with `Self = dyn Trait`. -/
def virtFn (methodPath dynKey : String) : Operand :=
  .constant { ty := { kind := .fnDef methodPath [.dynamic dynKey], layoutIdx := 7 },
              val := .zeroSized }

def fnOp (path : String) (args : List RigidTy := []) : Operand :=
  .constant { ty := { kind := .fnDef path args, layoutIdx := 7 }, val := .zeroSized }

def unsize (op : Operand) (ty : Ty) : Rvalue := .cast (.pointerCoercion "Unsize") op ty

def evalVtPath : String := "miri_diff_corpus::__AnnealVtableTrait43543::eval_vt"
def tagVtPath : String := "miri_diff_corpus::__AnnealVtableTrait43543::tag_vt"
def evalAltPath : String := "miri_diff_corpus::__AnnealVtableAlt43543::eval_alt"
def addrEqPath : String := "core::ptr::addr_eq"

def recEvalVt : String :=
  "<miri_diff_corpus::__AnnealVtableReceiver43543 as miri_diff_corpus::__AnnealVtableTrait43543>::eval_vt"
def recTagVt : String :=
  "<miri_diff_corpus::__AnnealVtableReceiver43543 as miri_diff_corpus::__AnnealVtableTrait43543>::tag_vt"
def otherEvalVt : String :=
  "<miri_diff_corpus::__AnnealVtableAltReceiver43543 as miri_diff_corpus::__AnnealVtableTrait43543>::eval_vt"
def otherTagVt : String :=
  "<miri_diff_corpus::__AnnealVtableAltReceiver43543 as miri_diff_corpus::__AnnealVtableTrait43543>::tag_vt"
def recEvalAlt : String :=
  "<miri_diff_corpus::__AnnealVtableReceiver43543 as miri_diff_corpus::__AnnealVtableAlt43543>::eval_alt"

/-- Monomorphized method body skeleton: `_0: u32`, `_1: &Self`, then `u32`
argument and temporaries. -/
def methodBody (path : String) (selfTy : Ty) (argCount : Nat) (temps : Nat)
    (stmts : List Statement) : CapturedMir :=
  { defPath := path, phase := .runtimePostCleanup, role := .model, argCount := argCount,
    localDecls :=
      decl u32Ty :: decl selfTy :: List.replicate (argCount - 1 + temps) (decl u32Ty),
    basicBlocks := [bb stmts .return_],
    fnAbi :=
      { args := ptrAbi :: List.replicate (argCount - 1) u32Abi, ret := u32Abi, conv := .rust,
        canUnwind := false },
    layouts := layouts, allocations := [] }

/-- `impl Trait for Receiver { fn eval_vt(&self, x) { (x ^ self.bias) & 0xFFFF } }` -/
def recEvalVtBody : CapturedMir :=
  methodBody recEvalVt refRecTy 2 2
    [ live 3, live 4,
      asg 3 (.use (selfField 1 0)),
      asg 4 (.binaryOp .bitXor (cp 2) (mv 3)),
      asg 0 (.binaryOp .bitAnd (mv 4) (cU32 65535)) ]

/-- `impl Trait for Receiver { fn tag_vt(&self) { (self.bias & 0x3F) ^ 0x15 } }` -/
def recTagVtBody : CapturedMir :=
  methodBody recTagVt refRecTy 1 2
    [ live 2, live 3,
      asg 2 (.use (selfField 1 0)),
      asg 3 (.binaryOp .bitAnd (mv 2) (cU32 63)),
      asg 0 (.binaryOp .bitXor (mv 3) (cU32 21)) ]

/-- `impl Trait for AltReceiver { fn eval_vt(&self, x) { ((x >> 1) ^ self.pad ^ self.bias) & 0xFFFF } }` -/
def otherEvalVtBody : CapturedMir :=
  methodBody otherEvalVt refOtherTy 2 5
    [ live 3, live 4, live 5, live 6, live 7,
      asg 3 (.binaryOp .shr (cp 2) (cU32 1)),
      asg 4 (.use (selfField 1 0)),
      asg 5 (.binaryOp .bitXor (mv 3) (mv 4)),
      asg 6 (.use (selfField 1 1)),
      asg 7 (.binaryOp .bitXor (mv 5) (mv 6)),
      asg 0 (.binaryOp .bitAnd (mv 7) (cU32 65535)) ]

/-- `impl Trait for AltReceiver { fn tag_vt(&self) { ((self.pad ^ self.bias) & 0x3F) ^ 0x2A } }` -/
def otherTagVtBody : CapturedMir :=
  methodBody otherTagVt refOtherTy 1 4
    [ live 2, live 3, live 4, live 5,
      asg 2 (.use (selfField 1 0)),
      asg 3 (.use (selfField 1 1)),
      asg 4 (.binaryOp .bitXor (mv 2) (mv 3)),
      asg 5 (.binaryOp .bitAnd (mv 4) (cU32 63)),
      asg 0 (.binaryOp .bitXor (mv 5) (cU32 42)) ]

/-- `impl Alt for Receiver { fn eval_alt(&self) { self.bias >> 1 } }` -/
def recEvalAltBody : CapturedMir :=
  methodBody recEvalAlt refRecTy 1 1
    [ live 2,
      asg 2 (.use (selfField 1 0)),
      asg 0 (.binaryOp .shr (mv 2) (cU32 1)) ]

def otherEvalAlt : String :=
  "<miri_diff_corpus::__AnnealVtableAltReceiver43543 as miri_diff_corpus::__AnnealVtableAlt43543>::eval_alt"

/-- A second `AltReceiver` method with the signature of `tag_vt`
(`self.bias >> 1`), used only by the slot-substitution sensitivity guard. -/
def otherEvalAltBody : CapturedMir :=
  methodBody otherEvalAlt refOtherTy 1 1
    [ live 2,
      asg 2 (.use (selfField 1 1)),
      asg 0 (.binaryOp .shr (mv 2) (cU32 1)) ]

def refMutDynTy : Ty := { kind := .ref .mut (.dynamic traitKey), layoutIdx := 5 }
def rawMutDynTy : Ty := { kind := .rawPtr .mut (.dynamic traitKey), layoutIdx := 5 }
def rawRecTy : Ty := { kind := .rawPtr .not (.adt recKey []), layoutIdx := 3 }
def refMutRecTy : Ty := { kind := .ref .mut (.adt recKey []), layoutIdx := 3 }

def addrEqMirPath : String := "miri_diff_corpus::addr_eq_mir"

/-- The MIR body of `core::ptr::addr_eq`: `(p as *const ()) == (q as *const
())` with two `PtrToPtr` casts and a thin-pointer `Eq`. Linked under a
monomorphic path so that `Trusted`'s own call, cast, and comparison rules run
it. -/
def addrEqMirBody : CapturedMir :=
  { defPath := addrEqMirPath, phase := .runtimePostCleanup, role := .model, argCount := 2,
    localDecls := [decl boolTy, decl rawDynTy, decl rawDynTy, decl rawUnitTy, decl rawUnitTy],
    basicBlocks :=
      [bb [ live 3, live 4,
            asg 3 (.cast .ptrToPtr (cp 1) rawUnitTy),
            asg 4 (.cast .ptrToPtr (cp 2) rawUnitTy),
            asg 0 (.binaryOp .eq (mv 3) (mv 4)) ] .return_],
    fnAbi :=
      { args := [{ layout := widePtrLayout, mode := .pair }, { layout := widePtrLayout, mode := .pair }],
        ret := { layout := boolLayout, mode := .direct }, conv := .rust, canUnwind := false },
    layouts := layouts, allocations := [] }

/-- Linked method bodies. -/
def methodBodies : List CapturedMir :=
  [recEvalVtBody, recTagVtBody, otherEvalVtBody, otherTagVtBody, recEvalAltBody]

/-- Trait object predicates of the two traits. -/
def traitPred : ProtoTraitPred := { principalTrait? := some traitKey }
def altPred : ProtoTraitPred := { principalTrait? := some altKey }

/-- Captured vtables. Slots `0..2` are the header; `eval_vt` is slot `3`
(method `0`) and `tag_vt` slot `4` (method `1`) of the trait; `eval_alt` is
slot `3` of the alternative trait. -/
def vtRecTrait : ProtoVTableEntry :=
  { vtableId := 0, vtableAllocId := 40000, concreteTyKey := recKey, traitPred := traitPred,
    sizeBytes := 4, alignBytes := 4,
    slots := [.dropInPlace none, .size, .align, .method recEvalVt, .method recTagVt] }
def vtOtherTrait : ProtoVTableEntry :=
  { vtableId := 1, vtableAllocId := 40001, concreteTyKey := otherKey, traitPred := traitPred,
    sizeBytes := 8, alignBytes := 4,
    slots := [.dropInPlace none, .size, .align, .method otherEvalVt, .method otherTagVt] }
def vtRecAlt : ProtoVTableEntry :=
  { vtableId := 2, vtableAllocId := 40002, concreteTyKey := recKey, traitPred := altPred,
    sizeBytes := 4, alignBytes := 4,
    slots := [.dropInPlace none, .size, .align, .method recEvalAlt] }

def vtables : ProtoVTableTable :=
  { entries := [vtRecTrait, vtOtherTrait, vtRecAlt],
    dynTypes := [(traitKey, traitPred), (altKey, altPred)] }

def prog : ProtoDynProgram :=
  { vtables := vtables,
    virtualMethods := [(evalVtPath, 3), (tagVtPath, 4), (evalAltPath, 3)] }

/-- Types of the driver locals `_0 .. _33`. -/
def driverDecls : List LocalDecl :=
  [ decl u32Ty, decl u32Ty, decl u32Ty,                       -- _0, _1 seed, _2 bias
    decl recTy, decl u32Ty,                                   -- _3 __vt_rec, _4
    decl otherTy, decl u32Ty, decl u32Ty, decl u32Ty, decl u32Ty,  -- _5 __vt_other, _6.._9
    decl refDynTy, decl refRecTy,                             -- _10 __vt_rec_dyn, _11
    decl refDynTy, decl refOtherTy,                           -- _12 __vt_other_dyn, _13
    decl refDynTy, decl boolTy, decl u32Ty,                   -- _14 __vt_dyn, _15, _16
    decl refAltTy, decl refRecTy,                             -- _17 __vt_dyn_alt, _18
    decl u32Ty, decl u32Ty, decl u32Ty,                       -- _19 __vt_virtual, _20, _21
    decl u32Ty,                                               -- _22 __vt_alt_bits
    decl u32Ty, decl boolTy, decl rawDynTy, decl rawAltTy,    -- _23 same_obj, _24, _25, _26
    decl u32Ty, decl boolTy, decl rawDynTy, decl rawDynTy,    -- _27 diff_obj, _28, _29, _30
    decl u32Ty, decl u32Ty, decl u32Ty ]                      -- _31, _32, _33

def derefPlace (l : Nat) : Place := { local_ := l, projection := [.deref] }

/-- `__anneal_vt_driver_43543(__vt_seed, __vt_bias)` (`repro.rs:309-341`).
`sameIfTrue` / `sameIfFalse` and `diffIfTrue` / `diffIfFalse` are the constants
of the two `addr_eq` branches (`1 / 0` and `0 / 2` in the reproducer),
`evalMethod` / `tagMethod` name the trait methods of the two virtual calls, and
`addrEq` is the callee of the two `addr_eq` calls (`core::ptr::addr_eq`). -/
def driverBodyWith (sameIfTrue sameIfFalse diffIfTrue diffIfFalse : Nat)
    (evalMethod tagMethod : String) (addrEq : Operand := fnOp addrEqPath
      [.dynamic traitKey, .dynamic altKey]) : CapturedMir :=
  { defPath := "miri_diff_corpus::__anneal_vt_driver_43543",
    phase := .runtimePostCleanup, role := .model, argCount := 2,
    localDecls := driverDecls,
    basicBlocks :=
      [ -- bb0
        bb ((List.range 31).map (fun i => live (i + 3)) ++
            [ asg 4 (.binaryOp .bitXor (cp 2) (cU32 3)),
              asg 3 (.aggregate (.adt recKey 0 none) [mv 4]),
              asg 7 (.binaryOp .bitAnd (cp 1) (cU32 255)),
              asg 6 (.binaryOp .bitXor (mv 7) (cU32 3)),
              asg 9 (.binaryOp .shr (cp 2) (cU32 1)),
              asg 8 (.binaryOp .bitXor (mv 9) (cU32 3)),
              asg 5 (.aggregate (.adt otherKey 0 none) [mv 6, mv 8]),
              asg 11 (.ref .shared (loc 3)),
              asg 10 (unsize (mv 11) refDynTy),
              asg 13 (.ref .shared (loc 5)),
              asg 12 (unsize (mv 13) refDynTy),
              asg 16 (.binaryOp .bitAnd (cp 1) (cU32 1)),
              asg 15 (.binaryOp .eq (mv 16) (cU32 0)) ])
           (.switchInt (mv 15) { branches := [(0, 2)], otherwise := 1 }),
        -- bb1: `(__vt_seed & 1) == 0`
        bb [asg 14 (.use (cp 10))] (.goto 3),
        -- bb2
        bb [asg 14 (.use (cp 12))] (.goto 3),
        -- bb3
        bb [ asg 18 (.ref .shared (loc 3)),
             asg 17 (unsize (mv 18) refAltTy) ]
           (.call (virtFn evalMethod traitKey) [cp 14, cp 1] (loc 20) (some 4) .continue_),
        -- bb4
        bb [] (.call (virtFn tagMethod traitKey) [cp 14] (loc 21) (some 5) .continue_),
        -- bb5
        bb [asg 19 (.binaryOp .bitXor (mv 20) (mv 21))]
           (.call (virtFn evalAltPath altKey) [cp 17] (loc 22) (some 6) .continue_),
        -- bb6
        bb [ asg 25 (.rawPtr .not (derefPlace 10)),
             asg 26 (.rawPtr .not (derefPlace 17)) ]
           (.call addrEq [mv 25, mv 26] (loc 24) (some 7) .continue_),
        -- bb7
        bb [] (.switchInt (mv 24) { branches := [(0, 9)], otherwise := 8 }),
        bb [asg 23 (.use (cU32 sameIfTrue))] (.goto 10),
        bb [asg 23 (.use (cU32 sameIfFalse))] (.goto 10),
        -- bb10
        bb [ asg 29 (.rawPtr .not (derefPlace 10)),
             asg 30 (.rawPtr .not (derefPlace 12)) ]
           (.call addrEq [mv 29, mv 30] (loc 28) (some 11) .continue_),
        -- bb11
        bb [] (.switchInt (mv 28) { branches := [(0, 13)], otherwise := 12 }),
        bb [asg 27 (.use (cU32 diffIfTrue))] (.goto 14),
        bb [asg 27 (.use (cU32 diffIfFalse))] (.goto 14),
        -- bb14
        bb [ asg 32 (.binaryOp .shl (cp 22) (cU32 2)),
             asg 31 (.binaryOp .bitXor (cp 19) (mv 32)),
             asg 33 (.binaryOp .bitXor (mv 31) (cp 23)),
             asg 0 (.binaryOp .bitXor (mv 33) (cp 27)) ]
           .return_ ],
    fnAbi := { args := [u32Abi, u32Abi], ret := u32Abi, conv := .rust, canUnwind := false },
    layouts := layouts, allocations := [] }

/-- The reproducer's driver. -/
def driverBody : CapturedMir := driverBodyWith 1 0 0 2 evalVtPath tagVtPath

/-- Initial state of `driver(seed, bias)` with `callees` linked. -/
def driverStateWith (callees : List CapturedMir) (body : CapturedMir) (seed bias : Nat) :
    MachineState :=
  initMachineStateWithCallees body [.scalar ⟨seed, 4⟩, .scalar ⟨bias, 4⟩] callees

/-- Initial state of `driver(seed, bias)` with the method bodies linked. -/
def driverState (body : CapturedMir) (seed bias : Nat) : MachineState :=
  driverStateWith methodBodies body seed bias

/-- Scalar result of a bounded run. -/
def scalarOf : ProtoRunResult → Option (Nat × Nat)
  | .returned (.scalar sc) _ => some (sc.bits, sc.sizeBytes)
  | _ => none

/-- Verdict tag of a bounded run (`0` returned, `1` panic, `2` abort, `3` UB,
`4` unsupported, `5` out of fuel, `6` external call). -/
def tagOf : ProtoRunResult → Nat
  | .returned _ _ => 0
  | .panic => 1
  | .abort => 2
  | .ub => 3
  | .unsupported => 4
  | .outOfFuel => 5
  | .externalCall _ => 6

end Fx

/-! ### Outer function `pass_option_some_niche_and_single_c_mut__b0_c10`

The captured MIR below is the finding's own (`finding.json`,
`mir_neighborhood`), reformatted only by line breaks. Its call to
`miri_diff_corpus::__anneal_vt_driver_43543` resolves to `Fx.driverBody`. -/

namespace Outer

/-- Layout table of the captured outer function. -/
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries :=
    (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }
    (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 1, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false }
    (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 1, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }
    (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 1, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) }
    (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.multiple (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) 0 (List.cons (FieldsShape.arbitrary List.nil List.nil) (List.cons (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)) List.nil))), isUninhabited := false, fieldLayouts := (List.cons 3 List.nil) }
    (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 2 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.multiple (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 2 }) 0 (List.cons (FieldsShape.arbitrary List.nil List.nil) (List.cons (FieldsShape.arbitrary List.nil List.nil) (List.cons (FieldsShape.arbitrary List.nil List.nil) List.nil)))), isUninhabited := false }
    (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 255, end_ := 2 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.multiple (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 255, end_ := 2 }) 0 (List.cons (FieldsShape.arbitrary List.nil List.nil) (List.cons (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)) List.nil))), isUninhabited := false, fieldLayouts := (List.cons 5 List.nil) }
    (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 255 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }
    (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 true) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }
    (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 0 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.multiple (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 0 }) 0 (List.cons (FieldsShape.arbitrary (List.cons { bytes := 4 } List.nil) (List.cons 0 List.nil)) List.nil)), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) }
    (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false }
    (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 9 List.nil) }
    (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } List.nil))))))))))))) }

/-- Captured `Runtime(PostCleanup)` MIR of
`miri_diff_corpus::pass_option_some_niche_and_single_c_mut__b0_c10`
(`repro.rs:345-375`), verbatim from `finding_0000/finding.json`
(`mir_neighborhood`). -/
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::pass_option_some_niche_and_single_c_mut__b0_c10",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 0,
    localDecls :=
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none }
    (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "core::num::NonZero" (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 3 }, debugName := (Option.some "nz") }
    (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "some_bits") }
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "core::option::Option" (List.cons (RigidTy.adt "core::num::NonZero" (List.cons (RigidTy.uint UintTy.u32) List.nil)) List.nil)), layoutIdx := 4 }, debugName := Option.none }
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "core::num::NonZero" (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 3 }, debugName := Option.none }
    (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "none_bits") }
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "core::option::Option" (List.cons (RigidTy.adt "core::num::NonZero" (List.cons (RigidTy.uint UintTy.u32) List.nil)) List.nil)), layoutIdx := 4 }, debugName := Option.none }
    (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "core::option::Option" (List.cons (RigidTy.adt "miri_diff_corpus::ColorTag" List.nil) List.nil)), layoutIdx := 6 }, debugName := (Option.some "oc") }
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "miri_diff_corpus::ColorTag" List.nil), layoutIdx := 5 }, debugName := Option.none }
    (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "color_val") }
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 7 }, debugName := Option.none }
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.int IntTy.isize), layoutIdx := 8 }, debugName := Option.none }
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "miri_diff_corpus::SingleC" List.nil), layoutIdx := 9 }, debugName := (Option.some "s") }
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none }
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none }
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none }
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none }
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none }
    (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 10 }, debugName := Option.none }
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.adt "miri_diff_corpus::SingleC" List.nil)), layoutIdx := 11 }, debugName := Option.none }
    (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.uint UintTy.u32)), layoutIdx := 12 }, debugName := (Option.some "p") }
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "miri_diff_corpus::SingleC" List.nil), layoutIdx := 9 }, debugName := Option.none }
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none }
    (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "v") }
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none }
    (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__tail___miri_vt_43543") }
    (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "v") }
    (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__miri_vt_43543") }
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none }
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none }
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none }
    (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))))))))))))))))))))))))))),
    basicBlocks :=
    (List.cons { statements :=
                  (List.cons { kind := (StatementKind.storageLive 10), span := "<dummy>" }
                  (List.cons { kind := (StatementKind.storageLive 11), span := "<dummy>" }
                  (List.cons { kind := (StatementKind.storageLive 1), span := "src/lib.rs:346:9: 346:11" }
                  (List.cons { kind := (StatementKind.assign { local_ := 1, projection := List.nil } (Rvalue.cast CastKind.transmute (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 7, sizeBytes := 4 })) }) { kind := (RigidTy.adt "core::num::NonZero" (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 3 })), span := "src/lib.rs:346:35: 346:69" }
                  (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:347:9: 347:18" }
                  (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:347:72: 347:80" }
                  (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:347:77: 347:79" }
                  (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:347:77: 347:79" }
                  (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "core::option::Option" 1 Option.none) (List.cons (Operand.move { local_ := 4, projection := List.nil }) List.nil))), span := "src/lib.rs:347:72: 347:80" }
                  (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:347:79: 347:80" }
                  (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast CastKind.transmute (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 })), span := "src/lib.rs:347:35: 347:81" }
                  (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:347:80: 347:81" }
                  (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:348:9: 348:18" }
                  (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:348:72: 348:76" }
                  (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "core::option::Option" 0 Option.none) List.nil)), span := "src/lib.rs:348:72: 348:76" }
                  (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.cast CastKind.transmute (Operand.move { local_ := 6, projection := List.nil }) { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 })), span := "src/lib.rs:348:35: 348:77" }
                  (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:348:76: 348:77" }
                  (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:349:9: 349:11" }
                  (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:349:37: 349:52" }
                  (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::ColorTag" 1 Option.none) List.nil)), span := "src/lib.rs:349:37: 349:52" }
                  (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "core::option::Option" 1 Option.none) (List.cons (Operand.move { local_ := 8, projection := List.nil }) List.nil))), span := "src/lib.rs:349:32: 349:53" }
                  (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:349:52: 349:53" }
                  (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:350:9: 350:18" }
                  (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.discriminant { local_ := 7, projection := List.nil })), span := "src/lib.rs:350:32: 350:34" } List.nil)))))))))))))))))))))))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 11, projection := List.nil }) { branches := (List.cons (0, 3) (List.cons (1, 2) List.nil)), otherwise := 1 }), span := "src/lib.rs:350:26: 350:34" }, isCleanup := false }
    (List.cons { statements := List.nil, terminator := { kind := TerminatorKind.unreachable, span := "src/lib.rs:350:32: 350:34" }, isCleanup := false }
    (List.cons { statements :=
                  (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.discriminant { local_ := 7, projection := (List.cons (ProjectionElem.downcast (Option.some "Some") 1) (List.cons (ProjectionElem.field 0 { kind := (RigidTy.adt "miri_diff_corpus::ColorTag" List.nil), layoutIdx := 5 }) List.nil)) })), span := "src/lib.rs:350:32: 350:34" } List.nil), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 10, projection := List.nil }) { branches := (List.cons (0, 6) (List.cons (1, 5) (List.cons (2, 4) List.nil))), otherwise := 1 }), span := "src/lib.rs:350:26: 350:34" }, isCleanup := false }
    (List.cons { statements :=
                  (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 4, sizeBytes := 4 })) }))), span := "src/lib.rs:354:17: 354:21" } List.nil), terminator := { kind := (TerminatorKind.goto 7), span := "src/lib.rs:354:17: 354:21" }, isCleanup := false }
    (List.cons { statements :=
                  (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 3, sizeBytes := 4 })) }))), span := "src/lib.rs:353:33: 353:37" } List.nil), terminator := { kind := (TerminatorKind.goto 7), span := "src/lib.rs:353:33: 353:37" }, isCleanup := false }
    (List.cons { statements :=
                  (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }))), span := "src/lib.rs:352:34: 352:38" } List.nil), terminator := { kind := (TerminatorKind.goto 7), span := "src/lib.rs:352:34: 352:38" }, isCleanup := false }
    (List.cons { statements :=
                  (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:351:32: 351:36" } List.nil), terminator := { kind := (TerminatorKind.goto 7), span := "src/lib.rs:351:32: 351:36" }, isCleanup := false }
    (List.cons { statements :=
                  (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:356:9: 356:14" }
                  (List.cons { kind := (StatementKind.storageLive 13), span := "src/lib.rs:356:31: 356:64" }
                  (List.cons { kind := (StatementKind.storageLive 14), span := "src/lib.rs:356:31: 356:52" }
                  (List.cons { kind := (StatementKind.storageLive 15), span := "src/lib.rs:356:31: 356:40" }
                  (List.cons { kind := (StatementKind.assign { local_ := 15, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:356:31: 356:40" }
                  (List.cons { kind := (StatementKind.storageLive 16), span := "src/lib.rs:356:43: 356:52" }
                  (List.cons { kind := (StatementKind.assign { local_ := 16, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 5, projection := List.nil }))), span := "src/lib.rs:356:43: 356:52" }
                  (List.cons { kind := (StatementKind.assign { local_ := 14, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 15, projection := List.nil }) (Operand.move { local_ := 16, projection := List.nil }))), span := "src/lib.rs:356:31: 356:52" }
                  (List.cons { kind := (StatementKind.storageDead 16), span := "src/lib.rs:356:51: 356:52" }
                  (List.cons { kind := (StatementKind.storageDead 15), span := "src/lib.rs:356:51: 356:52" }
                  (List.cons { kind := (StatementKind.storageLive 17), span := "src/lib.rs:356:55: 356:64" }
                  (List.cons { kind := (StatementKind.assign { local_ := 17, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 9, projection := List.nil }))), span := "src/lib.rs:356:55: 356:64" }
                  (List.cons { kind := (StatementKind.assign { local_ := 13, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 14, projection := List.nil }) (Operand.move { local_ := 17, projection := List.nil }))), span := "src/lib.rs:356:31: 356:64" }
                  (List.cons { kind := (StatementKind.storageDead 17), span := "src/lib.rs:356:63: 356:64" }
                  (List.cons { kind := (StatementKind.storageDead 14), span := "src/lib.rs:356:63: 356:64" }
                  (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::SingleC" 0 Option.none) (List.cons (Operand.move { local_ := 13, projection := List.nil }) List.nil))), span := "src/lib.rs:356:17: 356:65" }
                  (List.cons { kind := (StatementKind.storageDead 13), span := "src/lib.rs:356:64: 356:65" }
                  (List.cons { kind := (StatementKind.storageLive 18), span := "src/lib.rs:357:5: 361:6" }
                  (List.cons { kind := (StatementKind.storageLive 19), span := "src/lib.rs:357:11: 357:17" }
                  (List.cons { kind := (StatementKind.assign { local_ := 19, projection := List.nil } (Rvalue.ref (BorrowKind.mut false) { local_ := 12, projection := List.nil })), span := "src/lib.rs:357:11: 357:17" }
                  (List.cons { kind := (StatementKind.storageLive 20), span := "src/lib.rs:358:23: 358:24" }
                  (List.cons { kind := (StatementKind.assign { local_ := 20, projection := List.nil } (Rvalue.ref (BorrowKind.mut false) { local_ := 19, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.downcast (Option.some "Only") 0) (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil))) })), span := "src/lib.rs:358:23: 358:24" }
                  (List.cons { kind := (StatementKind.assign { local_ := 20, projection := (List.cons ProjectionElem.deref List.nil) } (Rvalue.binaryOp BinOp.bitXor (Operand.copy { local_ := 20, projection := (List.cons ProjectionElem.deref List.nil) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 12, sizeBytes := 4 })) }))), span := "src/lib.rs:359:13: 359:24" }
                  (List.cons { kind := (StatementKind.assign { local_ := 18, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 10 }, val := ConstValue.zeroSized }))), span := "src/lib.rs:358:29: 360:10" }
                  (List.cons { kind := (StatementKind.storageDead 20), span := "src/lib.rs:360:9: 360:10" }
                  (List.cons { kind := (StatementKind.storageDead 19), span := "src/lib.rs:361:5: 361:6" }
                  (List.cons { kind := (StatementKind.storageDead 18), span := "src/lib.rs:361:5: 361:6" }
                  (List.cons { kind := (StatementKind.storageLive 21), span := "src/lib.rs:362:9: 366:6" }
                  (List.cons { kind := (StatementKind.storageLive 22), span := "src/lib.rs:363:9: 365:10" }
                  (List.cons { kind := (StatementKind.storageLive 23), span := "src/lib.rs:364:27: 364:28" }
                  (List.cons { kind := (StatementKind.assign { local_ := 23, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 12, projection := (List.cons (ProjectionElem.downcast (Option.some "Only") 0) (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:364:27: 364:28" }
                  (List.cons { kind := (StatementKind.storageLive 24), span := "src/lib.rs:364:33: 364:34" }
                  (List.cons { kind := (StatementKind.assign { local_ := 24, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 23, projection := List.nil }))), span := "src/lib.rs:364:33: 364:34" }
                  (List.cons { kind := (StatementKind.assign { local_ := 22, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 24, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 3, sizeBytes := 4 })) }))), span := "src/lib.rs:364:33: 364:41" }
                  (List.cons { kind := (StatementKind.storageDead 24), span := "src/lib.rs:364:40: 364:41" }
                  (List.cons { kind := (StatementKind.storageDead 23), span := "src/lib.rs:364:40: 364:41" }
                  (List.cons { kind := (StatementKind.assign { local_ := 21, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::SingleC" 0 Option.none) (List.cons (Operand.move { local_ := 22, projection := List.nil }) List.nil))), span := "src/lib.rs:362:9: 366:6" }
                  (List.cons { kind := (StatementKind.storageDead 22), span := "src/lib.rs:366:5: 366:6" }
                  (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.use (Operand.move { local_ := 21, projection := List.nil }))), span := "src/lib.rs:362:5: 366:6" }
                  (List.cons { kind := (StatementKind.storageDead 21), span := "src/lib.rs:366:5: 366:6" }
                  (List.cons { kind := (StatementKind.storageLive 25), span := "src/lib.rs:367:9: 367:31" }
                  (List.cons { kind := (StatementKind.storageLive 26), span := "src/lib.rs:368:23: 368:24" }
                  (List.cons { kind := (StatementKind.assign { local_ := 26, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 12, projection := (List.cons (ProjectionElem.downcast (Option.some "Only") 0) (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:368:23: 368:24" }
                  (List.cons { kind := (StatementKind.assign { local_ := 25, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 26, projection := List.nil }))), span := "src/lib.rs:368:29: 368:30" }
                  (List.cons { kind := (StatementKind.storageDead 26), span := "src/lib.rs:368:29: 368:30" }
                  (List.cons { kind := (StatementKind.storageLive 27), span := "src/lib.rs:370:9: 370:24" }
                  (List.cons { kind := (StatementKind.storageLive 28), span := "src/lib.rs:371:9: 371:39" }
                  (List.cons { kind := (StatementKind.storageLive 29), span := "src/lib.rs:371:9: 371:27" }
                  (List.cons { kind := (StatementKind.assign { local_ := 29, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:371:10: 371:19" }
                  (List.cons { kind := (StatementKind.assign { local_ := 28, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 29, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 65535, sizeBytes := 4 })) }))), span := "src/lib.rs:371:9: 371:39" }
                  (List.cons { kind := (StatementKind.storageDead 29), span := "src/lib.rs:371:38: 371:39" } List.nil))))))))))))))))))))))))))))))))))))))))))))))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__anneal_vt_driver_43543" List.nil), layoutIdx := 10 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 28, projection := List.nil }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 24, sizeBytes := 4 })) }) List.nil)) { local_ := 27, projection := List.nil } (Option.some 8) UnwindAction.continue_), span := "src/lib.rs:370:32: 373:6" }, isCleanup := false }
    (List.cons { statements :=
                  (List.cons { kind := (StatementKind.storageDead 28), span := "src/lib.rs:373:5: 373:6" }
                  (List.cons { kind := (StatementKind.storageLive 30), span := "src/lib.rs:374:5: 374:27" }
                  (List.cons { kind := (StatementKind.assign { local_ := 30, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 25, projection := List.nil }))), span := "src/lib.rs:374:5: 374:27" }
                  (List.cons { kind := (StatementKind.storageLive 31), span := "src/lib.rs:374:30: 374:54" }
                  (List.cons { kind := (StatementKind.assign { local_ := 31, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 27, projection := List.nil }))), span := "src/lib.rs:374:31: 374:46" }
                  (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 30, projection := List.nil }) (Operand.move { local_ := 31, projection := List.nil }))), span := "src/lib.rs:374:5: 374:54" }
                  (List.cons { kind := (StatementKind.storageDead 31), span := "src/lib.rs:374:53: 374:54" }
                  (List.cons { kind := (StatementKind.storageDead 30), span := "src/lib.rs:374:53: 374:54" }
                  (List.cons { kind := (StatementKind.storageDead 27), span := "src/lib.rs:375:1: 375:2" }
                  (List.cons { kind := (StatementKind.storageDead 25), span := "src/lib.rs:375:1: 375:2" }
                  (List.cons { kind := (StatementKind.storageDead 12), span := "src/lib.rs:375:1: 375:2" }
                  (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:375:1: 375:2" }
                  (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:375:1: 375:2" }
                  (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:375:1: 375:2" }
                  (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:375:1: 375:2" }
                  (List.cons { kind := (StatementKind.storageDead 1), span := "src/lib.rs:375:1: 375:2" } List.nil)))))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:375:2: 375:2" }, isCleanup := false } List.nil))))))))),
    fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end Outer

/-! ## §2. Campaign #22 end-to-end reproducer -/

open Fx

/-- Verdict tag of an `RvalueEvalResult` (`0` ok, `3` UB, `4` unsupported). -/
def rvalTag : RvalueEvalResult → Nat
  | .ok _ _ _ => 0
  | .ub => 3
  | .unsupported => 4

/-- `(data allocation, data offset, vtable allocation, vtable offset)` of a
trait-object pointer with provenance in both words. -/
def dynPtrOf : Value → Option (Nat × Nat × Nat × Nat)
  | .aggregate 0 [.ptr d 8, .ptr v 8] => some (d.allocId, d.offsetBytes, v.allocId, v.offsetBytes)
  | _ => none

/-- Wide-pointer value of an `RvalueEvalResult`. -/
def rvalDynPtr : RvalueEvalResult → Option (Nat × Nat × Nat × Nat)
  | .ok v _ _ => dynPtrOf v
  | _ => none

/-- The reproducer's vtable table is well formed, and disjoint from the
allocations of the driver's initial memory. -/
theorem campaign_vtables_wf :
    wfProtoVTableTable 8 vtables = true ∧
    vtableEnvOk 8 vtables (driverState driverBody 7 24).memory = true := by
  decide +kernel

/-- Probe of the state after 39 `stepMirFn` steps of `driver(7, 24)`: block,
statement index, verdict tag of `evalUnsizeCoercion`, and wide pointer returned
by `evalUnsizeCoercionProto`. -/
def unsizeProbe : List Nat × Option (Nat × Nat × Nat × Nat) :=
  match advanceSteps driverBody (stepMirFn driverBody) 39 (driverState driverBody 7 24) with
  | some s =>
    ([s.frame.blockIdx, s.frame.stmtIdx,
      rvalTag (evalUnsizeCoercion s.frame.locals (mv 11) refDynTy s.memory driverDecls layouts)],
     rvalDynPtr
       (evalUnsizeCoercionProto vtables s.frame.locals (mv 11) refDynTy s.memory driverDecls
         layouts))
  | none => ([], none)

/-- **Campaign #22 root cause, on the reproducer.** After 39 steps the driver
is at `_10 = move _11 as &dyn __AnnealVtableTrait43543 (PointerCoercion(Unsize))`
(`repro.rs:317-318`). On that state `Trusted`'s `evalUnsizeCoercion` is `.ub`,
while `evalUnsizeCoercionProto` returns the wide pointer `(&__vt_rec, vtable
40000)` that keeps the borrow tag of `&__vt_rec`. -/
theorem campaign22_trusted_unsize_ub_and_proto_ok :
    unsizeProbe = ([0, 39, 3], some (1, 0, 40000, 0)) := by
  decide +kernel

/-- `Trusted`'s `stepMirFn` alone: the driver, and therefore the whole run, is
UB (the `false_positive_ub` verdict of the finding). -/
theorem campaign22_trusted_run_ub :
    tagOf (runMirTrusted driverBody 128 (driverState driverBody 7 24)) = 3 ∧
    tagOf (runMirTrusted driverBody 128 (driverState driverBody 6 24)) = 3 := by
  decide +kernel

/-- **`__anneal_vt_driver_43543(7, 24) = 30u32`.** Odd seed: `__vt_dyn` is
`__vt_other_dyn`, so both virtual calls dispatch to the `AltReceiver` impls and
read `pad` (offset 0) and `bias` (offset 4) through the narrowed receiver:
`eval_vt = ((7 >> 1) ^ 4 ^ 15) & 0xFFFF = 8`, `tag_vt = ((4 ^ 15) & 0x3F) ^ 0x2A
= 33`, `eval_alt = 27 >> 1 = 13`, and `(8 ^ 33) ^ (13 << 2) ^ 1 ^ 2 = 30`. -/
theorem campaign22_driver_7_24_returns_30 :
    scalarOf (runMirProto prog driverBody 128 (driverState driverBody 7 24)) = some (30, 4) := by
  decide +kernel

/-- **Even seed.** `__anneal_vt_driver_43543(6, 24)` takes the `__vt_rec_dyn`
branch: `eval_vt = (6 ^ 27) & 0xFFFF = 29`, `tag_vt = (27 & 0x3F) ^ 0x15 = 14`,
`eval_alt = 13`, and `(29 ^ 14) ^ (13 << 2) ^ 1 ^ 2 = 19 ^ 52 ^ 1 ^ 2 = 36`.

The brief's expected `38u32` drops the final `^ 2`: `19 ^ 52 = 39`,
`39 ^ 1 = 38`, `38 ^ 2 = 36`. The arithmetic identity is part of the
statement. -/
theorem campaign22_driver_6_24_returns_36 :
    scalarOf (runMirProto prog driverBody 128 (driverState driverBody 6 24)) = some (36, 4) ∧
    ((6 ^^^ 27) &&& 0xFFFF) ^^^ ((27 &&& 0x3F) ^^^ 0x15) ^^^ (13 <<< 2) ^^^ 1 ^^^ 2 = 36 ∧
    ((6 ^^^ 27) &&& 0xFFFF) ^^^ ((27 &&& 0x3F) ^^^ 0x15) ^^^ (13 <<< 2) ^^^ 1 = 38 := by
  decide +kernel

/-- Wide pointer held by `__vt_dyn` (local `_14`) after the `if`, for the
given seed. -/
def selectedDyn (seed : Nat) : Option (Nat × Nat × Nat × Nat) :=
  match advanceSteps driverBody (stepMirFnProto prog driverBody) 47 (driverState driverBody seed 24) with
  | some s =>
    (match get? s.frame.locals 14 with
     | some (.init v) => dynPtrOf v
     | _ => none)
  | none => none

/-- The even and odd seeds take different branches of the `if`: the selected
`__vt_dyn` (local `_14`) carries the vtable of `Receiver` (`40000`) for seed `6`
and of `AltReceiver` (`40001`) for seed `7`, with the data pointer of the
respective local. -/
theorem campaign22_dynamic_selection :
    selectedDyn 6 = some (1, 0, 40000, 0) ∧ selectedDyn 7 = some (2, 0, 40001, 0) := by
  decide +kernel

/-- **Sensitivity guards.** Flipping the positive `addr_eq` branch, flipping
the negative `addr_eq` branch, and replacing the `tag_vt` slot of the
`AltReceiver` vtable by another method of the same signature each change the
returned scalar. Swapping the `eval_vt` and `tag_vt` slots outright is caught
by ABI validation (the argument counts differ), so the call is UB rather than
a silently wrong dispatch. -/
theorem campaign22_sensitivity_guards :
    scalarOf (runMirProto prog (driverBodyWith 0 1 0 2 evalVtPath tagVtPath) 128
      (driverState driverBody 7 24)) = some (31, 4) ∧
    scalarOf (runMirProto prog (driverBodyWith 1 0 2 0 evalVtPath tagVtPath) 128
      (driverState driverBody 7 24)) = some (28, 4) ∧
    scalarOf (runMirProto
      { prog with vtables := { vtables with entries :=
          [vtRecTrait,
           { vtOtherTrait with
             slots := [.dropInPlace none, .size, .align, .method otherEvalVt, .method otherEvalAlt] },
           vtRecAlt] } }
      driverBody 128 (driverStateWith (otherEvalAltBody :: methodBodies) driverBody 7 24)) =
        some (56, 4) ∧
    tagOf (runMirProto
      { prog with vtables := { vtables with entries :=
          [vtRecTrait,
           { vtOtherTrait with
             slots := [.dropInPlace none, .size, .align, .method otherTagVt, .method otherEvalVt] },
           vtRecAlt] } }
      driverBody 128 (driverState driverBody 7 24)) = 3 := by
  decide +kernel

/-- Initial state of the captured outer function with the driver and the
method bodies linked. -/
def outerState : MachineState :=
  initMachineStateWithCallees Outer.body [] (driverBody :: methodBodies)

/-- **`pass_option_some_niche_and_single_c_mut__b0_c10() = 20u32`**, the exact
Miri result `MIRI_PASS:scalar:20:4`. The captured outer MIR (niche transmutes,
`Option<ColorTag>` match, `&mut SingleC` projection) runs on `Trusted`'s own
rules, calls `__anneal_vt_driver_43543(7 & 0xFFFF, 24) = 30`, and returns
`10 ^ 30 = 20` with zero UB. With `Trusted`'s `stepMirFn` alone the same run is
UB (`MirDiffTag.ub`, the finding's verdict). -/
theorem campaign22_outer_returns_20 :
    scalarOf (runMirProto prog Outer.body 512 outerState) = some (20, 4) ∧
    tagOf (runMirTrusted Outer.body 512 outerState) = 3 := by
  decide +kernel

/-! ## §3. Negative falsification canaries -/

namespace C16
open Fx

/-! ### (a) Crubit `cl/1028119410` (`c16`): receiver invalidated under the
virtual-call protector -/

def pokeKey : String := "c16::Poke"
def pokePath : String := "c16::Poke::poke"
def recPoke : String := "<miri_diff_corpus::__AnnealVtableReceiver43543 as c16::Poke>::poke"
def rawU32Ty : Ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 8 }
def refPokeTy : Ty := { kind := .ref .not (.dynamic pokeKey), layoutIdx := 5 }
def rawPokeTy : Ty := { kind := .rawPtr .not (.dynamic pokeKey), layoutIdx := 5 }
def rawRecTy : Ty := { kind := .rawPtr .not (.adt recKey []), layoutIdx := 3 }

/-- `fn poke(self: <receiver>, alias: *mut u32) -> u32 { [*alias = 9;] 7 }`.
With `write`, the method writes the receiver's backing storage through the
alias while the receiver is live. -/
def pokeBody (selfTy : Ty) (write : Bool) : CapturedMir :=
  { defPath := recPoke, phase := .runtimePostCleanup, role := .model, argCount := 2,
    localDecls := [decl u32Ty, decl selfTy, decl rawU32Ty],
    basicBlocks :=
      [bb ((match write with
            | true =>
              [{ kind := .assign { local_ := 2, projection := [.deref] } (.use (cU32 9)),
                 span := "<c16>" }]
            | false => []) ++ [asg 0 (.use (cU32 7))]) .return_],
    fnAbi := { args := [ptrAbi, ptrAbi], ret := u32Abi, conv := .rust, canUnwind := false },
    layouts := layouts, allocations := [] }

def pokePred : ProtoTraitPred := { principalTrait? := some pokeKey }

def pokeProg : ProtoDynProgram :=
  { vtables :=
      { entries :=
          [{ vtableId := 0, vtableAllocId := 40000, concreteTyKey := recKey, traitPred := pokePred,
             sizeBytes := 4, alignBytes := 4,
             slots := [.dropInPlace none, .size, .align, .method recPoke] }],
        dynTypes := [(pokeKey, pokePred)] },
    virtualMethods := [(pokePath, 3)] }

/-- Caller: `let mut rec = Receiver { bias: 1 }; let alias = &raw mut rec.bias;
let d = <receiver of rec> as <pointer to dyn Poke>; let r = d.poke(alias);
[rec = Receiver { bias: 5 };] r`. `refReceiver` selects `&dyn Poke` (protected)
or `*const dyn Poke` (unprotected); `writeAfter` mutates the owner after the
call returned. -/
def callerBody (refReceiver writeAfter : Bool) : CapturedMir :=
  { defPath := "c16::caller", phase := .runtimePostCleanup, role := .model, argCount := 0,
    localDecls :=
      [ decl u32Ty, decl recTy, decl rawU32Ty,
        decl (match refReceiver with | true => refPokeTy | false => rawPokeTy),
        decl (match refReceiver with | true => refRecTy | false => rawRecTy),
        decl u32Ty ],
    basicBlocks :=
      [ bb [ live 1, live 2, live 3, live 4, live 5,
             asg 1 (.aggregate (.adt recKey 0 none) [cU32 1]),
             asg 2 (.rawPtr .mut { local_ := 1, projection := [.field 0 u32Ty] }),
             asg 4 (match refReceiver with
                    | true => .ref .shared (loc 1)
                    | false => .rawPtr .not (loc 1)),
             asg 3 (unsize (mv 4) (match refReceiver with | true => refPokeTy | false => rawPokeTy)) ]
           (.call (virtFn pokePath pokeKey) [cp 3, cp 2] (loc 5) (some 1) .continue_),
        bb ((match writeAfter with
             | true => [asg 1 (.aggregate (.adt recKey 0 none) [cU32 5])]
             | false => []) ++ [asg 0 (.use (cp 5))]) .return_ ],
    fnAbi := { args := [], ret := u32Abi, conv := .rust, canUnwind := false },
    layouts := layouts, allocations := [] }

/-- Run the caller with the method linked. -/
def run (refReceiver writeInCallee writeAfter : Bool) : ProtoRunResult :=
  runMirProto pokeProg (callerBody refReceiver writeAfter) 64
    (initMachineStateWithCallees (callerBody refReceiver writeAfter) []
      [pokeBody (match refReceiver with | true => refRecTy | false => rawRecTy) writeInCallee])

def refMutPokeTy : Ty := { kind := .ref .mut (.dynamic pokeKey), layoutIdx := 5 }

/-- Caller with `&mut dyn Poke` receiver: `let mut rec = Receiver { bias: 1 };
let alias = &raw mut rec.bias; let d: &mut dyn Poke = &mut rec;
let r = d.poke_mut(alias); [rec = Receiver { bias: 5 };] r`. -/
def mutCallerBody (writeAfter : Bool) : CapturedMir :=
  { defPath := "c16::mut_caller", phase := .runtimePostCleanup, role := .model, argCount := 0,
    localDecls :=
      [ decl u32Ty, decl recTy, decl rawU32Ty, decl refMutPokeTy, decl refMutRecTy, decl u32Ty ],
    basicBlocks :=
      [ bb [ live 1, live 2, live 3, live 4, live 5,
             asg 1 (.aggregate (.adt recKey 0 none) [cU32 1]),
             asg 2 (.rawPtr .mut { local_ := 1, projection := [.field 0 u32Ty] }),
             asg 4 (.ref (.mut false) (loc 1)),
             asg 3 (unsize (mv 4) refMutPokeTy) ]
           (.call (virtFn pokePath pokeKey) [cp 3, cp 2] (loc 5) (some 1) .continue_),
        bb ((match writeAfter with
             | true => [asg 1 (.aggregate (.adt recKey 0 none) [cU32 5])]
             | false => []) ++ [asg 0 (.use (cp 5))]) .return_ ],
    fnAbi := { args := [], ret := u32Abi, conv := .rust, canUnwind := false },
    layouts := layouts, allocations := [] }

def runMut (writeInCallee writeAfter : Bool) : ProtoRunResult :=
  runMirProto pokeProg (mutCallerBody writeAfter) 64
    (initMachineStateWithCallees (mutCallerBody writeAfter) []
      [pokeBody refMutRecTy writeInCallee])

/-- **`c16` with `&mut dyn Poke` receiver.** Writing through the alias while
the protected `&mut dyn Poke` receiver is live is UB; without the write it
returns `7`, and mutating the owner after the call returns `7` once the frame
exit releases the protector. -/
theorem canary_a_c16_mut_dyn_receiver_uaf :
    tagOf (runMut true false) = 3 ∧
    scalarOf (runMut false false) = some (7, 4) ∧
    scalarOf (runMut false true) = some (7, 4) := by
  decide +kernel

end C16

namespace C16

/-- **(a) `c16`: receiver UAF under the active virtual-call protector.**
1. `&dyn Poke` receiver, the method writes the receiver's storage through an
   alias: UB (the write disables the protected receiver tag).
2. `&dyn Poke` receiver, no write: the call returns `7`.
3. `&dyn Poke` receiver, the owner is overwritten after the call returned: the
   run returns `7` (the protector is gone with the frame).
4. `*const dyn Poke` receiver, the same write inside the method: the call
   returns `7` (a raw receiver has no protector).
5. `*const dyn Poke` receiver, the owner overwritten after the call: `7`. -/
theorem canary_a_c16_receiver_uaf_under_protector :
    tagOf (run true true false) = 3 ∧
    scalarOf (run true false false) = some (7, 4) ∧
    scalarOf (run true false true) = some (7, 4) ∧
    scalarOf (run false true false) = some (7, 4) ∧
    scalarOf (run false false true) = some (7, 4) := by
  decide +kernel

/-- Protector bookkeeping of a state: the active protectors, and for every
borrow entry `(tag, parent tag + 1 or 0, protector + 1 or 0)`. -/
def protectorView (s : MachineState) : List Nat × List (Nat × Nat × Nat) :=
  (s.memory.activeProtectors,
   s.memory.borrows.map (fun b =>
     (b.tag,
      (match b.parentTag with | some t => t + 1 | none => 0),
      (match b.protector with | some p => p + 1 | none => 0))))

/-- State of the `&dyn Poke` run after `n` steps. -/
def stateAt (refReceiver : Bool) (n : Nat) : Option MachineState :=
  advanceSteps (callerBody refReceiver false)
    (stepMirFnProto pokeProg (callerBody refReceiver false)) n
    (initMachineStateWithCallees (callerBody refReceiver false) []
      [pokeBody (match refReceiver with | true => refRecTy | false => rawRecTy) false])

/-- **The protector is registered in `Memory.activeProtectors` exactly for the
duration of the call.** For the `&dyn Poke` receiver: before the call (9 steps)
there is no protector; inside the callee (10 steps) protector `1` is active and
the callee's receiver is the fresh tag `3`, a child of the caller's `&rec`
(tag `2`) carrying protector `1`; after the return (12 steps) no protector is
active. For the `*const dyn Poke` receiver no protector is ever registered. -/
theorem canary_a_protector_lifetime :
    (stateAt true 9).map protectorView = some ([], [(2, 0, 0), (1, 0, 0)]) ∧
    (stateAt true 10).map protectorView = some ([1], [(3, 3, 2), (2, 0, 0), (1, 0, 0)]) ∧
    ((stateAt true 12).map protectorView).map (·.1) = some [] ∧
    ((stateAt false 10).map protectorView).map (·.1) = some [] := by
  decide +kernel

/-- State of the `&mut dyn Poke` run after `n` steps. -/
def mutStateAt (n : Nat) : Option MachineState :=
  advanceSteps (mutCallerBody false) (stepMirFnProto pokeProg (mutCallerBody false)) n
    (initMachineStateWithCallees (mutCallerBody false) [] [pokeBody refMutRecTy false])

open Anneal.RefFrame in
/-- **`Trusted` protector and ranged Tree Borrows view agree on c16** across
`&dyn Poke` (in-callee step 10 AND post-return step 12), `&mut dyn Poke`
(in-callee step 10 AND post-return step 12), raw `*const dyn Poke` (no view),
tag-`0` parent borrows (no collision with fresh owner tag), 3-level nested
protected borrow chains (grandparent + child protectors both preserved), dead
allocations (`allocDead = true -> none`), and self-cycles (`none`). -/
theorem canary_a_trusted_and_ranged_views_agree :
    -- 1. `&dyn Poke` in-callee (step 10): fresh owner tag `4`, protected tag `3`.
    (match stateAt true 10 with
     | some s =>
       match rangedReceiverOwnerTag s.memory 3, rangedReceiverView s.memory 3 0 4 with
       | some owner, some t =>
         [ [owner], t.protectedTags,
           accessCode (receiverEnter t 3 0 4).status,
           accessCode
             (receiverForeignAccess (receiverEnter t 3 0 4).tree owner 0 4 .Write).status,
           releaseCode (receiverExit (receiverEnter t 3 0 4).tree 3).status,
           accessCode
             (receiverForeignAccess
               (receiverExit (receiverEnter t 3 0 4).tree 3).tree owner 0 4 .Write).status ]
       | _, _ => [[9]]
     | none => [[9]]) = [[4], [3], [0], [2, 0, 4, 3, 2], [0], [0]] ∧
    -- 2. `&dyn Poke` post-return (step 12): `Trusted` cleared `activeProtectors = []`,
    --    so `rangedReceiverView` has `protectedTags = []` and foreign write completes directly.
    (match stateAt true 12 with
     | some s =>
       match rangedReceiverOwnerTag s.memory 3, rangedReceiverView s.memory 3 0 4 with
       | some owner, some t =>
         [ t.protectedTags,
           accessCode (receiverEnter t 3 0 4).status,
           accessCode
             (receiverForeignAccess (receiverEnter t 3 0 4).tree owner 0 4 .Write).status ]
       | _, _ => [[9]]
     | none => [[9]]) = [[], [0], [0]] ∧
    -- 3. `&mut dyn Poke` in-callee (step 10) and post-return (step 12).
    (match mutStateAt 10, mutStateAt 12 with
     | some sIn, some sOut =>
       match rangedReceiverOwnerTag sIn.memory 3, rangedReceiverView sIn.memory 3 0 4,
             rangedReceiverOwnerTag sOut.memory 3, rangedReceiverView sOut.memory 3 0 4 with
       | some oIn, some tIn, some oOut, some tOut =>
         [ tIn.protectedTags,
           accessCode (receiverEnter tIn 3 0 4).status,
           accessCode
             (receiverForeignAccess (receiverEnter tIn 3 0 4).tree oIn 0 4 .Write).status,
           tOut.protectedTags,
           accessCode
             (receiverForeignAccess (receiverEnter tOut 3 0 4).tree oOut 0 4 .Write).status ]
       | _, _, _, _ => [[9]]
     | _, _ => [[9]]) = [[3], [0], [2, 0, 4, 3, 2], [], [0]] ∧
    -- 4. Raw `*const dyn Poke` registers no receiver tag (no view).
    (match stateAt false 10 with
     | some s => (rangedReceiverView s.memory 3 0 4).isNone
     | none => false) = true ∧
    -- 5. Tag `0` parent borrow (zero collision), 3-level nested protected chain,
    --    dead allocation (`allocDead = true`), and self-cycle.
    (let bTag0 : BorrowEntry :=
       { tag := 0, targetLocal := 1, targetProjection := [], perm := .frozen,
         parentTag := none, protector := none }
     let bChild1 : BorrowEntry :=
       { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen,
         parentTag := some 0, protector := some 7 }
     let memTag0 : Memory :=
       { emptyMemory with borrows := [bChild1, bTag0], activeProtectors := [7] }
     let bGrand : BorrowEntry :=
       { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen,
         parentTag := none, protector := some 10 }
     let bMid : BorrowEntry :=
       { tag := 2, targetLocal := 1, targetProjection := [], perm := .frozen,
         parentTag := some 1, protector := none }
     let bLeaf : BorrowEntry :=
       { tag := 3, targetLocal := 1, targetProjection := [], perm := .reservedFrz false,
         parentTag := some 2, protector := some 20 }
     let memNested : Memory :=
       { emptyMemory with borrows := [bLeaf, bMid, bGrand], activeProtectors := [20, 10] }
     let memDead : Memory :=
       { emptyMemory with borrows := [{ bChild1 with allocDead := true }, bTag0], activeProtectors := [7] }
     let memCycle : Memory :=
       { emptyMemory with
         borrows := [{ tag := 5, targetLocal := 1, targetProjection := [], perm := .frozen,
                       parentTag := some 5, protector := some 1 }],
         activeProtectors := [1] }
     let tag0Res :=
       match rangedReceiverOwnerTag memTag0 1, rangedReceiverView memTag0 1 0 4 with
       | some o0, some t0 =>
         [ [o0],
           accessCode (receiverEnter t0 1 0 4).status,
           accessCode (receiverForeignAccess (receiverEnter t0 1 0 4).tree o0 0 4 .Write).status ]
       | _, _ => [[9]]
     let nestedRes :=
       match rangedReceiverOwnerTag memNested 3, rangedReceiverView memNested 3 0 4 with
       | some oN, some tN =>
         let t1 := (receiverEnter tN 3 0 4).tree
         let tExitChild := (receiverExit t1 3).tree
         let tExitGrand := (receiverExit t1 1).tree
         let tExitBoth := (receiverExit tExitChild 1).tree
         [ [oN], tN.protectedTags,
           accessCode (receiverForeignAccess tExitGrand oN 0 4 .Write).status,
           accessCode (receiverForeignAccess tExitChild oN 0 4 .Write).status,
           accessCode (receiverForeignAccess tExitBoth oN 0 4 .Write).status ]
       | _, _ => [[9]]
     (tag0Res, nestedRes, (rangedReceiverView memDead 1 0 4).isNone,
      (rangedReceiverView memCycle 5 0 4).isNone)) =
      ( [[2], [0], [2, 0, 4, 1, 2]],
        [[4], [1, 3], [2, 0, 4, 3, 2], [2, 0, 4, 1, 2], [0]],
        true, true ) := by
  decide +kernel

end C16

namespace Canary
open Fx

/-- `s` with local `idx` holding `v`. -/
def withLocal (s : MachineState) (idx : Nat) (v : Value) : MachineState :=
  { s with
    frame := { s.frame with locals := (set? s.frame.locals idx (.init v)).getD s.frame.locals } }

/-- `s` with local `idx` in storage state `slot`. -/
def withSlot (s : MachineState) (idx : Nat) (slot : LocalSlot) : MachineState :=
  { s with frame := { s.frame with locals := (set? s.frame.locals idx slot).getD s.frame.locals } }

/-- `s` with the permission of borrow tag `tag` replaced by `perm`. -/
def withPerm (s : MachineState) (tag : Nat) (perm : TreeBorrowPerm) : MachineState :=
  { s with
    memory :=
      { s.memory with
        borrows :=
          s.memory.borrows.map (fun b =>
            match Nat.beq b.tag tag with
            | true => { b with perm := perm }
            | false => b) } }

/-- Driver local declarations with the type of `_11` (the unsizing source)
replaced. -/
def declsWith (ty : Ty) : List LocalDecl := (set? driverDecls 11 (decl ty)).getD driverDecls

/-- The driver at `_10 = move _11 as &dyn Trait (Unsize)`: `_11 = &__vt_rec`
with borrow tag `1`. -/
def s39 : Option MachineState :=
  advanceSteps driverBody (stepMirFn driverBody) 39 (driverState driverBody 7 24)

/-- The driver at the first virtual call `__vt_dyn.eval_vt(__vt_seed)`:
`_14 = (&__vt_other, vtable 40001)` with borrow tag `2`. -/
def s49 : Option MachineState :=
  advanceSteps driverBody (stepMirFnProto prog driverBody) 49 (driverState driverBody 7 24)

/-- `[tag, data allocation, data offset, vtable allocation, vtable offset]` of
`evalUnsizeCoercionProto` on the edited state `edit s39`, with source operand
`copy _11` and target type `targetTy` (`[tag]` alone when the result is not a
wide pointer with provenance in both words). -/
def unsizeWith (vt : ProtoVTableTable) (edit : MachineState → MachineState)
    (decls : List LocalDecl) (targetTy : Ty) : List Nat :=
  match s39 with
  | some s =>
    let r :=
      evalUnsizeCoercionProto vt (edit s).frame.locals (cp 11) targetTy (edit s).memory decls
        layouts
    match rvalDynPtr r with
    | some (a, b, c, d) => [rvalTag r, a, b, c, d]
    | none => [rvalTag r]
  | none => [9]

/-- Verdict tag of a virtual call (`0` callee entered, `1` external call, `3`
UB, `4` unsupported). -/
def vcTag : ProtoVirtualCallResult → Nat
  | .enter _ _ _ => 0
  | .externalCall _ _ _ => 1
  | .ub => 3
  | .unsupported => 4

/-- Verdict tag of `evalVirtualCallProto` for `(copy _14).method(copy _1)` on
the edited state `edit s49`. -/
def callWith (vt : ProtoVTableTable) (pred : ProtoTraitPred) (slot : Nat)
    (edit : MachineState → MachineState) : Nat :=
  match s49 with
  | some s =>
    vcTag
      (evalVirtualCallProto vt { traitPred := pred, slotIdx := slot, receiverIsRef := true }
        (edit s) driverBody [cp 14, cp 1] (loc 20) 4 .continue_)
  | none => 9

def wide (d v : Value) : Value := .aggregate 0 [d, v]
def ptrV (a o : Nat) : Value := .ptr { allocId := a, offsetBytes := o } 8
def scV (n : Nat) : Value := .scalar ⟨n, 8⟩

/-- Non-self supertrait entry for `AltReceiver` used in `vtablesWithNonMethodSlots`. -/
def vtOtherAlt : ProtoVTableEntry :=
  { vtableId := 3, vtableAllocId := 40003, concreteTyKey := otherKey, traitPred := altPred,
    sizeBytes := 8, alignBytes := 4,
    slots := [.dropInPlace none, .size, .align, .method otherEvalAlt] }

/-- Vtable table whose `AltReceiver` vtable has a vacant slot `3` and a
non-self supertrait slot `4` pointing to `vtOtherAlt` (`vtableId = 3`). -/
def vtablesWithNonMethodSlots : ProtoVTableTable :=
  { vtables with
    entries :=
      [vtRecTrait,
       { vtOtherTrait with slots := [.dropInPlace none, .size, .align, .vacant, .traitVPtr 3] },
       vtRecAlt,
       vtOtherAlt] }

/-- `vtablesWithNonMethodSlots` is genuinely well formed (no self-loop). -/
theorem vtablesWithNonMethodSlots_wf :
    wfProtoVTableTable 8 vtablesWithNonMethodSlots = true := by
  decide +kernel

/-- **(b) Mutability and borrow-state violations.** On the reproducer's
unsizing state:
* the baseline `&T -> &dyn Trait` succeeds and keeps the borrow tag;
* `&T -> &mut dyn Trait`, `*const T -> *mut dyn Trait`, and `*const T ->
  &dyn Trait` are UB;
* a `.disabled` tag, a misaligned pointer, an out-of-bounds referent, an
  uninhabited concrete type, a null pointer, and a `.frozen` tag unsized to
  `&mut dyn Trait` are UB for a reference;
* a `&mut T` with a `.unique` tag unsizes to `&mut dyn Trait`. -/
theorem canary_b_mutability_and_borrow_state :
    unsizeWith vtables id driverDecls refDynTy = [0, 1, 0, 40000, 0] ∧
    unsizeWith vtables id driverDecls refMutDynTy = [3] ∧
    unsizeWith vtables id (declsWith rawRecTy) rawMutDynTy = [3] ∧
    unsizeWith vtables id (declsWith rawRecTy) refDynTy = [3] ∧
    unsizeWith vtables (fun s => withPerm s 1 .disabled) driverDecls refDynTy = [3] ∧
    unsizeWith vtables (fun s => withLocal s 11 (ptrV 1 2)) driverDecls refDynTy = [3] ∧
    unsizeWith vtables (fun s => withLocal s 11 (ptrV 1 4)) driverDecls refDynTy = [3] ∧
    unsizeWith
      { vtables with
        entries :=
          [{ vtRecTrait with isUninhabited := true }, vtOtherTrait,
           { vtRecAlt with isUninhabited := true }] }
      id driverDecls refDynTy = [3] ∧
    unsizeWith vtables (fun s => withLocal s 11 (ptrV 0 0)) driverDecls refDynTy = [3] ∧
    unsizeWith vtables (fun s => withLocal s 11 (scV 0)) driverDecls refDynTy = [3] ∧
    unsizeWith vtables (fun s => withPerm s 1 .frozen) (declsWith refMutRecTy) refMutDynTy =
      [3] ∧
    unsizeWith vtables (fun s => withPerm s 1 .unique) (declsWith refMutRecTy) refMutDynTy =
      [0, 1, 0, 40000, 0] := by
  decide +kernel

/-- **Raw side of the raw-versus-reference distinction, on the reproducer.**
The inputs that are UB for a reference in (b) unsize fine as raw pointers:
`*const T -> *const dyn Trait` with a `.disabled` tag, a misaligned pointer, a
dangling misaligned pointer into no allocation, and a provenance-less null
pointer. The data word is preserved exactly. -/
theorem raw_unsize_requires_no_validity :
    unsizeWith vtables id (declsWith rawRecTy) rawDynTy = [0, 1, 0, 40000, 0] ∧
    unsizeWith vtables (fun s => withPerm s 1 .disabled) (declsWith rawRecTy) rawDynTy =
      [0, 1, 0, 40000, 0] ∧
    unsizeWith vtables (fun s => withLocal s 11 (ptrV 1 2)) (declsWith rawRecTy) rawDynTy =
      [0, 1, 2, 40000, 0] ∧
    unsizeWith vtables (fun s => withLocal s 11 (ptrV 777 3)) (declsWith rawRecTy) rawDynTy =
      [0, 777, 3, 40000, 0] ∧
    (unsizeWith vtables (fun s => withLocal s 11 (scV 0)) (declsWith rawRecTy) rawDynTy) = [0] := by
  decide +kernel

/-- **(c) Invalid vtable and slot violations (`lean-miri#75/#79/#82`,
`kani#5216`).** The baseline call enters the callee. A null vtable pointer, a
dangling integer vtable pointer, a non-zero offset into a vtable allocation, a
data allocation and a function allocation used as the vtable, the vtable of
another trait, a thin receiver, an out-of-range slot, the three header slots,
a vacant slot, and a supertrait slot are all UB. -/
theorem canary_c_invalid_vtable_and_slot :
    callWith vtables Fx.traitPred 3 id = 0 ∧
    [ callWith vtables Fx.traitPred 3 (fun s => withLocal s 14 (wide (ptrV 2 0) (ptrV 0 0))),
      callWith vtables Fx.traitPred 3 (fun s => withLocal s 14 (wide (ptrV 2 0) (scV 4096))),
      callWith vtables Fx.traitPred 3 (fun s => withLocal s 14 (wide (ptrV 2 0) (ptrV 40001 8))),
      callWith vtables Fx.traitPred 3 (fun s => withLocal s 14 (wide (ptrV 2 0) (ptrV 2 0))),
      callWith vtables Fx.traitPred 3 (fun s => withLocal s 14 (wide (ptrV 2 0) (ptrV 65536 0))),
      callWith vtables Fx.traitPred 3 (fun s => withLocal s 14 (wide (ptrV 1 0) (ptrV 40002 0))),
      callWith vtables Fx.traitPred 3 (fun s => withLocal s 14 (ptrV 2 0)),
      callWith vtables Fx.traitPred 9 id,
      callWith vtables Fx.traitPred 0 id,
      callWith vtables Fx.traitPred 1 id,
      callWith vtables Fx.traitPred 2 id,
      callWith vtablesWithNonMethodSlots Fx.traitPred 3 id,
      callWith vtablesWithNonMethodSlots Fx.traitPred 4 id ] =
      [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] := by
  decide +kernel

/-- **(d) Unresolved existential binder (`charon#1640`) and supertrait
outlives (`zerocopy:reference` `407e0bf7692a`), on the reproducer**: unsizing
and the virtual call are `.unsupported` (tag `4`), and an uncaptured vtable is
`.unsupported` as well. -/
theorem canary_d_fail_closed_on_reproducer :
    unsizeWith
      { vtables with
        dynTypes :=
          [(traitKey, { Fx.traitPred with hasUnresolvedExistentialBinder := true }),
           (altKey, altPred)] }
      id driverDecls refDynTy = [4] ∧
    unsizeWith
      { vtables with
        dynTypes :=
          [(traitKey, { Fx.traitPred with supertraitOutlivesOk := false }), (altKey, altPred)] }
      id driverDecls refDynTy = [4] ∧
    unsizeWith { vtables with entries := [vtOtherTrait, vtRecAlt] } id driverDecls refDynTy =
      [4] ∧
    callWith vtables { Fx.traitPred with hasUnresolvedExistentialBinder := true } 3 id = 4 ∧
    callWith vtables { Fx.traitPred with supertraitOutlivesOk := false } 3 id = 4 := by
  decide +kernel

/-- **(d), universally.** For every vtable table, operand, and state: when the
target predicate has an unresolved existential binder or undischarged outlives
obligations, unsizing is not UB and not `.ok` (it is `.unsupported`). -/
theorem canary_d_fail_closed_universal
    (vt : ProtoVTableTable) (dstKind : ProtoPtrKind) (dstMut : Bool) (traitKey : String)
    (locals : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (pred : ProtoTraitPred)
    (hLook : lookupDynPred vt.dynTypes traitKey = some pred)
    (hFail : pred.hasUnresolvedExistentialBinder = true ∨ pred.supertraitOutlivesOk = false) :
    evalUnsizeDynProto vt dstKind dstMut traitKey locals op mem localDecls layouts ≠ .ub ∧
    ∀ v locals' mem',
      evalUnsizeDynProto vt dstKind dstMut traitKey locals op mem localDecls layouts ≠
        .ok v locals' mem' := by
  have hF : pred.failsClosed = true := by
    unfold ProtoTraitPred.failsClosed
    rcases hFail with h | h <;> simp [h]
  rw [evalUnsizeDynProto_failsClosed vt dstKind dstMut traitKey locals op mem localDecls layouts
    pred hLook hF]
  refine ⟨?_, ?_⟩
  · intro h
    cases h
  · intro _ _ _ h
    cases h

/-- **(e) Uninitialized virtual-call argument (`kani#5172`).** An
uninitialized or dead trailing argument, an uninitialized receiver, and an
argument value containing `uninit` are UB. The gate comes first: the call is UB
with an uninitialized argument even where it would otherwise be `.unsupported`
(unresolved predicate, ill-formed vtable table) or an external call (callee
not linked). -/
theorem canary_e_uninit_argument :
    [ callWith vtables Fx.traitPred 3 (fun s => withSlot s 1 .uninit),
      callWith vtables Fx.traitPred 3 (fun s => withSlot s 1 .dead),
      callWith vtables Fx.traitPred 3 (fun s => withSlot s 14 .uninit),
      callWith vtables Fx.traitPred 3 (fun s => withLocal s 1 (.aggregate 0 [.uninit])) ] =
      [3, 3, 3, 3] ∧
    callWith vtables { Fx.traitPred with hasUnresolvedExistentialBinder := true } 3 id = 4 ∧
    callWith vtables { Fx.traitPred with hasUnresolvedExistentialBinder := true } 3
      (fun s => withSlot s 1 .uninit) = 3 ∧
    callWith { vtables with entries := [vtRecTrait, vtRecTrait] } Fx.traitPred 3 id = 4 ∧
    callWith { vtables with entries := [vtRecTrait, vtRecTrait] } Fx.traitPred 3
      (fun s => withSlot s 14 .uninit) = 3 ∧
    callWith vtables Fx.traitPred 3
      (fun s => { s with memory := { s.memory with callees := [] } }) = 1 ∧
    callWith vtables Fx.traitPred 3
      (fun s => withSlot { s with memory := { s.memory with callees := [] } } 1 .uninit) = 3 := by
  decide +kernel

end Canary

/-! ## §4. Pillar witnesses on the reproducer -/

namespace Pillar
open Fx Canary

/-- The even-seed driver at the first virtual call: `_10 = &__vt_rec as &dyn
Trait`, `_12 = &__vt_other as &dyn Trait`, `_14 = _10`, and `_17 = &__vt_rec
as &dyn Alt` are initialized. -/
def s49 : Option MachineState :=
  advanceSteps driverBody (stepMirFnProto prog driverBody) 49 (driverState driverBody 6 24)

/-- Value of the driver local `idx` in `s49`. -/
def localVal (idx : Nat) : Value :=
  match s49 with
  | some s =>
    (match get? s.frame.locals idx with
     | some (.init v) => v
     | _ => .unit)
  | none => .unit

/-- `(tag, value)` of a `ProtoRes Nat`. -/
def resCode : ProtoRes Nat → Nat × Nat
  | .ok n => (0, n)
  | .ub => (3, 0)
  | .unsupported => (4, 0)

/-- `(tag, scalar bits)` of an `RvalueEvalResult`. -/
def rvalBool : RvalueEvalResult → Nat × Nat
  | .ok (.scalar sc) _ _ => (0, sc.bits)
  | .ok _ _ _ => (0, 99)
  | .ub => (3, 0)
  | .unsupported => (4, 0)

/-- `core::ptr::addr_eq(p, q)` in `s49`. -/
def addrEq (p q : Value) : Nat × Nat :=
  match s49 with
  | some s => rvalBool (evalWideAddrEqProto p q s.frame.locals s.memory driverDecls layouts)
  | none => (9, 0)

/-- Wide `p == q` in `s49`. -/
def wideEq (p q : Value) : Nat × Nat :=
  match s49 with
  | some s => rvalBool (evalWidePtrEqProto p q s.frame.locals s.memory driverDecls layouts)
  | none => (9, 0)

/-- The three unsizing coercions of the driver: each wide pointer keeps the
borrow tag and offset of its source reference and carries the vtable of the
concrete type for the target trait. `&__vt_rec` is borrowed twice (tags `1` and
`3`) for the two traits. -/
theorem driver_unsize_results :
    [dynPtrOf (localVal 10), dynPtrOf (localVal 12), dynPtrOf (localVal 14),
     dynPtrOf (localVal 17)] =
      [some (1, 0, 40000, 0), some (2, 0, 40001, 0), some (1, 0, 40000, 0),
       some (3, 0, 40002, 0)] := by
  decide +kernel

/-- **Dynamic layout on the reproducer.** `size_of_val` / `align_of_val` read
`(4, 4)` for `Receiver` and `(8, 4)` for `AltReceiver` from the vtable. The
data word is not inspected: a null or dangling data word with a valid vtable
pointer still yields the size. A vtable of another trait, a thin pointer, a
slice length or dangling integer in the metadata word, a non-zero vtable
offset, a data allocation as vtable, `uninit`, and a pointer of the wrong width
are UB; an unresolved existential binder is unsupported. -/
theorem dyn_layout_on_reproducer :
    [ resCode (dynSizeOfValProto vtables 8 Fx.traitPred (localVal 10)),
      resCode (dynAlignOfValProto vtables 8 Fx.traitPred (localVal 10)),
      resCode (dynSizeOfValProto vtables 8 Fx.traitPred (localVal 12)),
      resCode (dynAlignOfValProto vtables 8 Fx.traitPred (localVal 12)),
      resCode (dynSizeOfValProto vtables 8 altPred (localVal 17)),
      resCode (dynSizeOfValProto vtables 8 Fx.traitPred (wide (scV 0) (ptrV 40001 0))),
      resCode (dynSizeOfValProto vtables 8 Fx.traitPred (wide (ptrV 999 7) (ptrV 40001 0))) ] =
      [(0, 4), (0, 4), (0, 8), (0, 4), (0, 4), (0, 8), (0, 8)] ∧
    [ resCode (dynSizeOfValProto vtables 8 Fx.traitPred (localVal 17)),
      resCode (dynSizeOfValProto vtables 8 Fx.traitPred (ptrV 1 0)),
      resCode (dynSizeOfValProto vtables 8 Fx.traitPred (wide (ptrV 1 0) (scV 4))),
      resCode (dynSizeOfValProto vtables 8 Fx.traitPred (wide (ptrV 1 0) (ptrV 40000 8))),
      resCode (dynSizeOfValProto vtables 8 Fx.traitPred (wide (ptrV 1 0) (ptrV 1 0))),
      resCode (dynSizeOfValProto vtables 8 Fx.traitPred .uninit),
      resCode (dynSizeOfValProto vtables 4 Fx.traitPred (localVal 10)) ] =
      [(3, 0), (3, 0), (3, 0), (3, 0), (3, 0), (3, 0), (3, 0)] ∧
    resCode
      (dynSizeOfValProto vtables 8 { Fx.traitPred with hasUnresolvedExistentialBinder := true }
        (localVal 10)) = (4, 0) := by
  decide +kernel

/-- **`addr_eq` ignores all metadata; wide `==` does not** (`rust#166144`), on
the reproducer's values.
* `addr_eq(&rec as &dyn Trait, &rec as &dyn Alt)` is `true` although the borrow
  tags and the vtables differ; `addr_eq(&rec as &dyn Trait, &other as &dyn
  Trait)` is `false`.
* `addr_eq(&rec as &dyn Trait, &rec as *const ())`, two slice pointers of
  lengths `2` and `4` at the same address, and a slice pointer against a
  trait-object pointer are all `true`.
* an `uninit` operand, or an operand containing `uninit`, is UB.
* wide `==` on `&rec as &dyn Trait` and `&rec as &dyn Alt` is `false` (same
  data address, different vtable pointers), and `false` on the slice pointers of
  different length. -/
theorem addr_eq_versus_wide_eq_on_reproducer :
    [ addrEq (localVal 10) (localVal 17), addrEq (localVal 10) (localVal 12),
      addrEq (localVal 10) (ptrV 1 0),
      addrEq (wide (ptrV 1 0) (scV 2)) (wide (ptrV 1 0) (scV 4)),
      addrEq (wide (ptrV 1 0) (scV 2)) (localVal 10),
      addrEq (scV 4096) (wide (scV 4096) (ptrV 40000 0)), addrEq (scV 4096) (scV 4097) ] =
      [(0, 1), (0, 0), (0, 1), (0, 1), (0, 1), (0, 1), (0, 0)] ∧
    [ addrEq (localVal 10) .uninit, addrEq .uninit (localVal 10),
      addrEq (wide .uninit (scV 2)) (localVal 10) ] = [(3, 0), (3, 0), (3, 0)] ∧
    [ wideEq (localVal 10) (localVal 17), wideEq (localVal 10) (localVal 10),
      wideEq (localVal 10) (localVal 12),
      wideEq (wide (ptrV 1 0) (scV 2)) (wide (ptrV 1 0) (scV 4)),
      wideEq (wide (ptrV 1 0) (scV 2)) (wide (ptrV 1 0) (scV 2)) ] =
      [(0, 0), (0, 1), (0, 0), (0, 0), (0, 1)] := by
  decide +kernel

/-- **`addr_eq` is its MIR lowering, end to end.** Replacing the two
`core::ptr::addr_eq` calls of the driver by calls to the linked MIR body
`(p as *const ()) == (q as *const ())` (two `PtrToPtr` casts and a thin `Eq`,
run by `Trusted`'s own call, `evalCastPtrToPtr`, and `BinOp.eq` rules) returns
the same `30` and `36`. -/
theorem addr_eq_mir_lowering_end_to_end :
    scalarOf (runMirProto prog (driverBodyWith 1 0 0 2 evalVtPath tagVtPath (fnOp addrEqMirPath))
      160 (driverStateWith (addrEqMirBody :: methodBodies) driverBody 7 24)) = some (30, 4) ∧
    scalarOf (runMirProto prog (driverBodyWith 1 0 0 2 evalVtPath tagVtPath (fnOp addrEqMirPath))
      160 (driverStateWith (addrEqMirBody :: methodBodies) driverBody 6 24)) = some (36, 4) := by
  decide +kernel

open Anneal.RefFrame in
/-- Ranged tree of the `&dyn Trait` receiver `&__vt_rec` (`Receiver`, bytes
`[0, 4)`): owner tag `1`, caller reference tag `2` (`Frozen`), callee receiver
tag `3`. -/
def recTree (isProtected : Bool) : RangedBorrowTree :=
  receiverTree 1 2 3 0 4 .Frozen (receiverChildPerm false) isProtected

open Anneal.RefFrame in
/-- Ranged tree of a `&mut dyn Trait` receiver to the field at bytes `[4, 8)`
of `AltReceiver`: caller reference `Unique`, callee receiver `ReservedFrz`. -/
def mutFieldTree : RangedBorrowTree :=
  receiverTree 1 2 3 4 4 .Unique (receiverChildPerm true) true

open Anneal.RefFrame in
/-- **Ranged Tree Borrows receiver protector (`c16`).**
1. The function-entry reborrow read through the receiver tag completes.
2. During the call, a foreign write by the owner of the storage is a
   transition error at the receiver tag `3` over `[0, 4)`:
   `ProtectedDisabled`. A foreign read is allowed.
3. `exitFrameWithProtectors` releases the protector, and the same foreign write
   then completes.
4. With no protector (raw-pointer receiver) the write completes during the
   call.
5. A `&mut dyn Trait` receiver over a field range `[4, 8)` behaves the same:
   `ProtectedDisabled` on a foreign write during the call, completed after the
   frame exit. -/
theorem receiver_protector_ranged_tree :
    accessCode (receiverEnter (recTree true) 3 0 4).status = [0] ∧
    accessCode
      (receiverForeignAccess (receiverEnter (recTree true) 3 0 4).tree 1 0 4 .Write).status =
        [2, 0, 4, 3, 2] ∧
    accessCode
      (receiverForeignAccess (receiverEnter (recTree true) 3 0 4).tree 1 0 4 .Read).status =
        [0] ∧
    releaseCode (receiverExit (receiverEnter (recTree true) 3 0 4).tree 3).status = [0] ∧
    accessCode
      (receiverForeignAccess
        (receiverExit (receiverEnter (recTree true) 3 0 4).tree 3).tree 1 0 4 .Write).status =
        [0] ∧
    accessCode
      (receiverForeignAccess (receiverEnter (recTree false) 3 0 4).tree 1 0 4 .Write).status =
        [0] ∧
    accessCode
      (receiverForeignAccess (receiverEnter mutFieldTree 3 4 4).tree 1 4 4 .Write).status =
        [2, 4, 4, 3, 2] ∧
    accessCode
      (receiverForeignAccess
        (receiverExit (receiverEnter mutFieldTree 3 4 4).tree 3).tree 1 4 4 .Write).status =
        [0] := by
  decide +kernel

end Pillar

/-! ### MiniRust `Mach` and `MachTB` on the reproducer's vtables -/

namespace MrTest
open Fx Pillar
open MiniRustSpec MiniRustSpec.Interp
open Anneal.Prototypes.DynTraitUnsizeProto.MR

/-- MiniRust trait numbering: `0` for the reproducer's trait, `1` otherwise. -/
def traitOf (p : ProtoTraitPred) : Nat :=
  match traitPredEq p Fx.traitPred with
  | true => 0
  | false => 1
/-- MiniRust function numbering of the concrete methods (order of first appearance in the vtables). -/
def fnOf (path : String) : Nat := Lm.fnIdOf vtables path

/-- Vtable table with an extra zero-sized concrete type. -/
def vtZst : ProtoVTableEntry :=
  { vtableId := 3, vtableAllocId := 40003, concreteTyKey := "()", traitPred := Fx.traitPred,
    sizeBytes := 0, alignBytes := 1, slots := [.dropInPlace none, .size, .align, .vacant, .vacant] }
/-- The reproducer's vtables plus the zero-sized entry. -/
def vt : ProtoVTableTable := { vtables with entries := vtables.entries ++ [vtZst] }

/-- `Mach` layout. -/
def bmL : DynLayout BM := bmLayout traitOf fnOf
/-- `MachTB` layout. -/
def tbL : DynLayout TBM := tbLayout traitOf fnOf

/-- Little-endian bytes of a small `u32`. -/
def u32Bytes (n : Nat) : List Byte :=
  [.Init (UInt8.ofNat (n % 256)) none, .Init 0 none, .Init 0 none, .Init 0 none]

/-- Allocations `1` (`Receiver`, 4 bytes at `65536`) and `2` (`AltReceiver`, 8 bytes at `131072`). -/
def bmAllocs : List Gen.Allocation :=
  [ { addr := 16, data := [], align := ⟨1⟩, kind := .Stack, live := true, extra := () },
    { addr := 65536, data := u32Bytes 27, align := ⟨4⟩, kind := .Stack, live := true, extra := () },
    { addr := 131072, data := u32Bytes 4 ++ u32Bytes 15, align := ⟨4⟩, kind := .Stack, live := true,
      extra := () } ]

/-- Function pointers of the five methods on `Mach`: method `i` at address `4096 * (i + 1)`. -/
def fnPtrsBM : List (Gen.FnName × Ptr) :=
  (List.range 5).map (fun i => (⟨⟨i⟩⟩, { addr := 4096 * (i + 1), provenance := some (⟨100 + i⟩, ()) }))

/-- `Mach` with the vtables installed. -/
def mach : Mach := installVTables bmL vt (baseMach bmAllocs fnPtrsBM)

/-- Tree Borrows allocation: a `Unique` root and one child node with permission `childPerm`. -/
def tbAlloc (addr : Int) (data : List Byte) (align : Nat) (childPerm : Gen.PermissionUnprot) :
    Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra :=
  { data := data.map (fun b => match b with | .Uninit => .Uninit | .Init v _ => .Init v none)
    addr := addr, align := ⟨align⟩, kind := .Stack, live := true
    extra :=
      { root :=
          { children :=
              [{ children := [], permissions := List.replicate data.length (.Unprot childPerm),
                 «protected» := .No }]
            permissions := List.replicate data.length (.Unprot .Unique)
            «protected» := .No } } }

/-- The data allocations on `MachTB`. -/
def tbAllocs (childPerm : Gen.PermissionUnprot) :
    List (Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) :=
  [ tbAlloc 16 [] 1 childPerm, tbAlloc 65536 (u32Bytes 27) 4 childPerm,
    tbAlloc 131072 (u32Bytes 4 ++ u32Bytes 15) 4 childPerm ]

/-- Function pointers of the five methods on `MachTB`. -/
def fnPtrsTB : List (Gen.FnName × Gen.ThinPointer Gen.TreeBorrowsProvenance) :=
  (List.range 5).map (fun i =>
    (⟨⟨i⟩⟩, { addr := 4096 * (i + 1), provenance := some (⟨100 + i⟩, []) }))

/-- `MachTB` with the vtables installed. -/
def machTB (childPerm : Gen.PermissionUnprot) : MachTB :=
  installVTables tbL vt (baseMachTB (tbAllocs childPerm) fnPtrsTB)

/-- Pointee information of `dyn Trait`. -/
def dynInfo (inhabited : Bool) : Gen.PointeeInfo :=
  { layout := .TraitObject (traitName bmL Fx.traitPred), inhabited := inhabited,
    unsafe_cells := .TraitObject, freeze := true, unpin := true }

/-- `(3, i)` UB with message `msgs[i]` (`i = msgs.length` for another
message), `(4, 0)` unsupported, `(5, 0)` spec panic, `(6, 0)` other. -/
def stopCode (msgs : List String) : Stop → Nat × Nat
  | .ub m => (3, Lm.strIndex m msgs)
  | .unsupported _ => (4, 0)
  | .specPanic _ => (5, 0)
  | _ => (6, 0)
/-- `(0, 0)` on success, otherwise `stopCode`. -/
def interpCode {α : Type} (msgs : List String) : Interp α → Nat × Nat
  | .ok _ => (0, 0)
  | .error e => stopCode msgs e

/-- UB messages of `check_ptr` and `vtable_from_ptr`, by index. -/
def msgs : List String :=
  [ "Value::Ptr: invalid vtable in metadata", "invalid pointer for vtable lookup",
    "Value::Ptr: unaligned safe pointer", "Value::Ptr: safe pointer to uninhabited type",
    "Value::Ptr: non-dereferenceable safe pointer", "Value::Ptr: null safe pointer",
    "Value::Ptr: invalid metadata" ]

/-- `Mach` trait-object pointer to offset `dataOff` of data allocation `dataAlloc` with the vtable of `e`. -/
def bmWide (dataAlloc dataOff : Nat) (e : ProtoVTableEntry) : Gen.Pointer Prov :=
  { thin_pointer := ptrAt bmL dataAlloc dataOff, metadata := some (.VTablePointer (vtPtr bmL e)) }
/-- `MachTB` trait-object pointer whose data provenance is the node at `path`. -/
def tbWide (path : Gen.Path) (dataAlloc dataOff : Nat) (e : ProtoVTableEntry) :
    Gen.Pointer Gen.TreeBorrowsProvenance :=
  { thin_pointer := { addr := (dataAlloc : Int) * 65536 + dataOff, provenance := some (⟨dataAlloc⟩, path) },
    metadata := some (.VTablePointer (vtPtr tbL e)) }

/-- `&dyn Trait`. -/
def refTy (inhabited : Bool := true) : Gen.PtrType := .Ref .Immutable (dynInfo inhabited)
/-- `*const dyn Trait`. -/
def rawTy : Gen.PtrType := .Raw (.VTablePointer (traitName bmL Fx.traitPred))


/-- Code of a `Mach` value: `[0, n]` integer, `[1, addr, alloc, hasMeta]`
pointer (`alloc = -1` without provenance). Results add `[3]` UB, `[4]`
unsupported, `[5]` spec panic. -/
def valCode : Gen.Value BM → List Int
  | .Int n => [0, n]
  | .Ptr p =>
    [1, p.thin_pointer.addr,
     (match p.thin_pointer.provenance with | some (id, _) => id._0 | none => -1),
     (match p.metadata with | some _ => 1 | none => 0)]
  | _ => [2]

/-- Code of a `MachTB` value: as `valCode`. -/
def valCodeTB : Gen.Value TBM → List Int
  | .Int n => [0, n]
  | .Ptr p =>
    [1, p.thin_pointer.addr,
     (match p.thin_pointer.provenance with | some (id, _) => id._0 | none => -1),
     (match p.metadata with | some _ => 1 | none => 0)]
  | _ => [2]

/-- Code of a `Mach` unary-operator result. -/
def unopCode (r : Interp (Val × Gen.Type)) : List Int :=
  match r with
  | .ok (v, _) => valCode v
  | .error (.ub _) => [3]
  | .error (.unsupported _) => [4]
  | .error (.specPanic _) => [5]
  | .error _ => [6]

/-- Code of a `MachTB` unary-operator result. -/
def unopCodeTB (r : Interp (Gen.Value TBM × Gen.Type)) : List Int :=
  match r with
  | .ok (v, _) => valCodeTB v
  | .error (.ub _) => [3]
  | .error (.unsupported _) => [4]
  | .error (.specPanic _) => [5]
  | .error _ => [6]

/-- MiniRust name of the reproducer's trait. -/
def tn : Gen.TraitName := traitName bmL Fx.traitPred
/-- Stand-alone vtable pointer value of `e` on `Mach`. -/
def vtVal (e : ProtoVTableEntry) : Val × Gen.Type :=
  (.Ptr { thin_pointer := vtPtr bmL e, metadata := none }, .Ptr (.VTablePtr tn))
/-- Stand-alone vtable pointer value of `e` on `MachTB`. -/
def vtValTB (e : ProtoVTableEntry) : Gen.Value TBM × Gen.Type :=
  (.Ptr { thin_pointer := vtPtr tbL e, metadata := none }, .Ptr (.VTablePtr tn))


/-- The table with the zero-sized entry is well formed, and every reproducer
vtable resolves by its allocation. -/
theorem mr_table_wf :
    wfProtoVTableTable 8 vt = true ∧
    (lookupVTableByAlloc vt.entries 40000).isSome = true ∧
    (lookupVTableByAlloc vt.entries 40001).isSome = true := by
  decide +kernel

/-- **`check_ptr` on `Mach` (`PtrType::Ref` and `PtrType::Raw` to
`Type::TraitObject`).**
* A `&dyn Trait` to `Receiver` or `AltReceiver` with its own vtable is
  accepted; a zero-sized concrete type is accepted at a dangling address.
* Trait mismatch (the `Alt` vtable), an unaligned data pointer, an uninhabited
  concrete type, an out-of-bounds referent, a referent smaller than the vtable
  size, a null pointer, and a dangling pointer without provenance are UB, each
  with MiniRust's own message.
* A raw `*const dyn Trait` with a dangling data pointer is accepted (only the
  metadata is checked); a raw pointer whose vtable pointer has an offset or is
  a data allocation is `ub "invalid pointer for vtable lookup"`; slice-length
  or missing metadata is `ub "Value::Ptr: invalid metadata"`. -/
theorem mr_checkPtr_mach :
    [ interpCode msgs (checkPtr (bmWide 1 0 vtRecTrait) refTy (some mach)),
      interpCode msgs (checkPtr (bmWide 2 0 vtOtherTrait) refTy (some mach)),
      interpCode msgs
        (checkPtr
          { thin_pointer := { addr := 4097, provenance := none },
            metadata := some (.VTablePointer (vtPtr bmL vtZst)) } refTy (some mach)) ] =
      [(0, 0), (0, 0), (0, 0)] ∧
    [ interpCode msgs (checkPtr (bmWide 1 0 vtRecAlt) refTy (some mach)),
      interpCode msgs (checkPtr (bmWide 1 1 vtRecTrait) refTy (some mach)),
      interpCode msgs (checkPtr (bmWide 1 0 vtRecTrait) (refTy false) (some mach)),
      interpCode msgs (checkPtr (bmWide 1 4 vtRecTrait) refTy (some mach)),
      interpCode msgs (checkPtr (bmWide 1 0 vtOtherTrait) refTy (some mach)),
      interpCode msgs
        (checkPtr
          { thin_pointer := { addr := 0, provenance := none },
            metadata := some (.VTablePointer (vtPtr bmL vtRecTrait)) } refTy (some mach)),
      interpCode msgs
        (checkPtr
          { thin_pointer := { addr := 4096, provenance := none },
            metadata := some (.VTablePointer (vtPtr bmL vtRecTrait)) } refTy (some mach)) ] =
      [(3, 0), (3, 2), (3, 3), (3, 4), (3, 4), (3, 5), (3, 4)] ∧
    [ interpCode msgs
        (checkPtr
          { thin_pointer := { addr := 4097, provenance := none },
            metadata := some (.VTablePointer (vtPtr bmL vtRecTrait)) } rawTy (some mach)),
      interpCode msgs
        (checkPtr
          { thin_pointer := { addr := 4097, provenance := none },
            metadata := some (.VTablePointer (ptrAt bmL 40000 8)) } rawTy (some mach)),
      interpCode msgs
        (checkPtr
          { thin_pointer := { addr := 4097, provenance := none },
            metadata := some (.VTablePointer (ptrAt bmL 1 0)) } rawTy (some mach)),
      interpCode msgs
        (checkPtr
          { thin_pointer := { addr := 4097, provenance := none },
            metadata := some (.ElementCount 3) } rawTy (some mach)),
      interpCode msgs
        (checkPtr
          { thin_pointer := { addr := 4097, provenance := none }, metadata := none } rawTy
          (some mach)) ] =
      [(0, 0), (3, 1), (3, 1), (3, 6), (3, 6)] := by
  decide +kernel

/-- **`check_ptr` on `MachTB`, and Tree Borrows mode sensitivity.**
`checkPtrM` on `MachTB` gives the `Mach` verdicts (accepted, trait mismatch,
unaligned, uninhabited, out of bounds); it does not consult the borrow tree, so
a reference whose node is `Frozen` or `Disabled` passes it. The tree is
enforced by the access the reborrow performs: through a `Frozen` node a load
succeeds and a store is UB; through a `Disabled` node a load is UB. On `Mach`
(no borrow tracking) the same load and store succeed. This is the prototype's
split: `.disabled` is UB for a reference, `.frozen` is UB for a mutable one. -/
theorem mr_checkPtr_machTB_and_tb_mode_sensitivity :
    [ interpCode msgs (checkPtrM (tbWide [] 1 0 vtRecTrait) refTy (some (machTB .Frozen))),
      interpCode msgs (checkPtrM (tbWide [0] 1 0 vtRecTrait) refTy (some (machTB .Frozen))),
      interpCode msgs (checkPtrM (tbWide [0] 1 0 vtRecTrait) refTy (some (machTB .Disabled))),
      interpCode msgs (checkPtrM (tbWide [] 1 0 vtRecAlt) refTy (some (machTB .Frozen))),
      interpCode msgs (checkPtrM (tbWide [] 1 1 vtRecTrait) refTy (some (machTB .Frozen))),
      interpCode msgs (checkPtrM (tbWide [] 1 0 vtRecTrait) (refTy false) (some (machTB .Frozen))),
      interpCode msgs (checkPtrM (tbWide [] 1 4 vtRecTrait) refTy (some (machTB .Frozen))) ] =
      [(0, 0), (0, 0), (0, 0), (3, 0), (3, 2), (3, 3), (3, 4)] ∧
    [ (interpCode msgs
        (MemoryOps.load (machTB .Frozen).mem.memory
          ({ addr := 65536, provenance := some (⟨1⟩, [0]) } :
            Gen.ThinPointer Gen.TreeBorrowsProvenance) ⟨4⟩ ⟨4⟩)).1,
      (interpCode msgs
        (MemoryOps.store (machTB .Frozen).mem.memory
          ({ addr := 65536, provenance := some (⟨1⟩, [0]) } :
            Gen.ThinPointer Gen.TreeBorrowsProvenance)
          [.Init 1 none, .Init 0 none, .Init 0 none, .Init 0 none] ⟨4⟩)).1,
      (interpCode msgs
        (MemoryOps.load (machTB .Disabled).mem.memory
          ({ addr := 65536, provenance := some (⟨1⟩, [0]) } :
            Gen.ThinPointer Gen.TreeBorrowsProvenance) ⟨4⟩ ⟨4⟩)).1,
      (interpCode msgs
        (MemoryOps.load mach.mem.memory
          ({ addr := 65536, provenance := some (⟨1⟩, ()) } : Ptr) ⟨4⟩ ⟨4⟩)).1,
      (interpCode msgs
        (MemoryOps.store mach.mem.memory
          ({ addr := 65536, provenance := some (⟨1⟩, ()) } : Ptr) (u32Bytes 1) ⟨4⟩)).1 ] =
      [0, 3, 3, 0, 0] := by
  decide +kernel

/-- **`evalUnOp` / `evalUnOpM` agree with the prototype.**
* `GetMetadata` on a trait-object pointer returns the vtable pointer (address
  `40000 * 65536`, the canonical `Trusted` address of vtable allocation
  `40000`).
* `ComputeSize` / `ComputeAlign` return `4`, `8`, and `4`, the values of
  `dynSizeOfValProto` / `dynAlignOfValProto`.
* `VTableMethodLookup` at slots `3` and `4` returns the function pointer of
  method `k` at address `4096 * (k + 1)`, where `k` is the method
  `evalVirtualCallProto` resolves for the same vtable and slot
  (`Lm.virtualCallObs`).
* A header or out-of-range slot is a MiniRust spec panic (`[5]`: the program is
  ill formed), where the prototype and Miri report UB.
All of it on `Mach` and on `MachTB`. -/
theorem mr_evalUnOp_agrees_with_proto :
    [ unopCode (evalUnOp .GetMetadata (.Ptr (bmWide 1 0 vtRecTrait), .Ptr refTy) (some mach)),
      unopCode (evalUnOp .GetMetadata (.Ptr (bmWide 2 0 vtOtherTrait), .Ptr rawTy) (some mach)),
      unopCode (evalUnOp (.ComputeSize (.TraitObject tn)) (vtVal vtRecTrait) (some mach)),
      unopCode (evalUnOp (.ComputeSize (.TraitObject tn)) (vtVal vtOtherTrait) (some mach)),
      unopCode (evalUnOp (.ComputeAlign (.TraitObject tn)) (vtVal vtOtherTrait) (some mach)),
      unopCode (evalUnOp (.VTableMethodLookup ⟨⟨3⟩⟩) (vtVal vtRecTrait) (some mach)),
      unopCode (evalUnOp (.VTableMethodLookup ⟨⟨4⟩⟩) (vtVal vtRecTrait) (some mach)),
      unopCode (evalUnOp (.VTableMethodLookup ⟨⟨3⟩⟩) (vtVal vtOtherTrait) (some mach)),
      unopCode (evalUnOp (.VTableMethodLookup ⟨⟨2⟩⟩) (vtVal vtRecTrait) (some mach)),
      unopCode (evalUnOp (.VTableMethodLookup ⟨⟨9⟩⟩) (vtVal vtRecTrait) (some mach)) ] =
      [ [1, 2621440000, 40000, 0], [1, 2621505536, 40001, 0], [0, 4], [0, 8], [0, 4],
        [1, 4096, 100, 0], [1, 8192, 101, 0], [1, 12288, 102, 0], [5], [5] ] ∧
    [ unopCodeTB
        (evalUnOpM .GetMetadata (.Ptr (tbWide [] 1 0 vtRecTrait), .Ptr refTy)
          (some (machTB .Frozen))),
      unopCodeTB
        (evalUnOpM (.ComputeSize (.TraitObject tn)) (vtValTB vtOtherTrait) (some (machTB .Frozen))),
      unopCodeTB
        (evalUnOpM (.ComputeAlign (.TraitObject tn)) (vtValTB vtOtherTrait)
          (some (machTB .Frozen))),
      unopCodeTB
        (evalUnOpM (.VTableMethodLookup ⟨⟨3⟩⟩) (vtValTB vtRecTrait) (some (machTB .Frozen))),
      unopCodeTB
        (evalUnOpM (.VTableMethodLookup ⟨⟨4⟩⟩) (vtValTB vtOtherTrait) (some (machTB .Frozen))) ] =
      [[1, 2621440000, 40000, 0], [0, 8], [0, 4], [1, 4096, 100, 0], [1, 16384, 103, 0]] ∧
    [ Lm.virtualCallObs vt Fx.traitPred 3 (.prov 1 0) (.prov 40000 0),
      Lm.virtualCallObs vt Fx.traitPred 4 (.prov 1 0) (.prov 40000 0),
      Lm.virtualCallObs vt Fx.traitPred 3 (.prov 2 0) (.prov 40001 0),
      Lm.virtualCallObs vt Fx.traitPred 4 (.prov 2 0) (.prov 40001 0),
      Lm.virtualCallObs vt Fx.traitPred 2 (.prov 1 0) (.prov 40000 0) ] =
      [ .method 0 (.prov 1 0), .method 1 (.prov 1 0), .method 2 (.prov 2 0),
        .method 3 (.prov 2 0), .err .notAMethod ] ∧
    [ resCode (dynSizeOfValProto vt 8 Fx.traitPred (Canary.wide (Canary.ptrV 1 0) (Canary.ptrV 40000 0))),
      resCode (dynSizeOfValProto vt 8 Fx.traitPred (Canary.wide (Canary.ptrV 2 0) (Canary.ptrV 40001 0))),
      resCode (dynAlignOfValProto vt 8 Fx.traitPred (Canary.wide (Canary.ptrV 2 0) (Canary.ptrV 40001 0))) ] =
      [(0, 4), (0, 8), (0, 4)] := by
  decide +kernel

/-- **Universal `Mach` / `MachTB` correspondence, instantiated.** The universal
theorem `MR.mach_and_machTB_vtable_correspondence` at the reproducer's
`AltReceiver` vtable, for every base `Mach` and `MachTB`. -/
theorem mr_universal_correspondence_instance (m : Mach) (mTB : MachTB) (d : ProtoDataWord) :
    (vtableFromPtr (installVTables bmL vt m) (vtPtr bmL vtOtherTrait) =
        .ok (vtableOf bmL vtOtherTrait) ∧
      computeSize (installVTables bmL vt m) (.TraitObject tn)
        (some (.VTablePointer (vtPtr bmL vtOtherTrait))) = .ok ⟨8⟩ ∧
      computeAlign (installVTables bmL vt m) (.TraitObject tn)
        (some (.VTablePointer (vtPtr bmL vtOtherTrait))) = .ok ⟨4⟩) ∧
    (vtableFromPtrM (installVTables tbL vt mTB) (vtPtr tbL vtOtherTrait) =
        .ok (vtableOf tbL vtOtherTrait) ∧
      computeSizeM (installVTables tbL vt mTB) (.TraitObject tn)
        (some (.VTablePointer (vtPtr tbL vtOtherTrait))) = .ok ⟨8⟩ ∧
      computeAlignM (installVTables tbL vt mTB) (.TraitObject tn)
        (some (.VTablePointer (vtPtr tbL vtOtherTrait))) = .ok ⟨4⟩) ∧
    dynSizeOfValProto vt 8 Fx.traitPred (mkDynPtr 8 d vtOtherTrait) = .ok 8 ∧
    dynAlignOfValProto vt 8 Fx.traitPred (mkDynPtr 8 d vtOtherTrait) = .ok 4 :=
  mach_and_machTB_vtable_correspondence traitOf fnOf vt 8 vtOtherTrait d tn m mTB
    (by decide +kernel) (by decide +kernel) rfl

/-- **Universal MiniRust `checkPtrMetadataM`, `checkPtrM` (raw & ref, both
positive acceptance and non-dereferenceable/null UB), and `evalUnOpM`
correspondence, instantiated on `Mach` and `MachTB`.** -/
theorem mr_universal_checkPtr_and_evalUnOp_instances
    (m : Mach) (mTB : MachTB) (dataPtr fnThin : Ptr) (dataPtrTB fnThinTB : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (hDataB : inBounds dataPtr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hDataBTB : inBounds dataPtrTB.addr .Unsigned x86_64.PTR_SIZE = true)
    (hFn : mapGet m.fn_ptrs ⟨⟨fnOf otherEvalVt⟩⟩ = some fnThin)
    (hFnTB : mapGet mTB.fn_ptrs ⟨⟨fnOf otherEvalVt⟩⟩ = some fnThinTB) :
    checkPtrM { thin_pointer := dataPtr, metadata := some (.VTablePointer (vtPtr bmL vtOtherTrait)) }
        (.Raw (.VTablePointer tn)) (some (installVTables bmL vt m)) = .ok () ∧
    checkPtrM { thin_pointer := dataPtrTB, metadata := some (.VTablePointer (vtPtr tbL vtOtherTrait)) }
        (.Raw (.VTablePointer tn)) (some (installVTables tbL vt mTB)) = .ok () ∧
    checkPtrM
        { thin_pointer := { addr := 0, provenance := none },
          metadata := some (.VTablePointer (vtPtr bmL vtOtherTrait)) }
        (.Ref .Immutable (dynInfo true)) (some (installVTables bmL vt m)) =
      ub "Value::Ptr: null safe pointer" ∧
    (dataPtr.addr ≠ 0 → Align.is_aligned ⟨4⟩ dataPtr.addr = true →
      ConcurrentMemory.dereferenceable m.mem dataPtr ⟨8⟩ = .ok () →
      checkPtrM { thin_pointer := dataPtr, metadata := some (.VTablePointer (vtPtr bmL vtOtherTrait)) }
          (.Ref .Immutable (dynInfo true)) (some (installVTables bmL vt m)) = .ok ()) ∧
    (dataPtrTB.addr ≠ 0 → Align.is_aligned ⟨4⟩ dataPtrTB.addr = true →
      ∀ msg, ConcurrentMemory.dereferenceable mTB.mem dataPtrTB ⟨8⟩ = .error (.ub msg) →
      checkPtrM { thin_pointer := dataPtrTB, metadata := some (.VTablePointer (vtPtr tbL vtOtherTrait)) }
          (.Ref .Immutable (dynInfo true)) (some (installVTables tbL vt mTB)) =
        ub "Value::Ptr: non-dereferenceable safe pointer") ∧
    evalUnOpM (.VTableMethodLookup ⟨⟨3⟩⟩) (vtVal vtOtherTrait) (some (installVTables bmL vt m)) =
      .ok (.Ptr (ThinPointer.widen fnThin none), .Ptr .FnPtr) ∧
    evalUnOpM (.VTableMethodLookup ⟨⟨3⟩⟩) (vtValTB vtOtherTrait) (some (installVTables tbL vt mTB)) =
      .ok (.Ptr (ThinPointer.widen fnThinTB none), .Ptr .FnPtr) := by
  have hWf : wfProtoVTableTable 8 vt = true := by decide +kernel
  have hLook : lookupVTableByAlloc vt.entries vtOtherTrait.vtableAllocId = some vtOtherTrait := rfl
  have hVtB : inBounds (vtPtr bmL vtOtherTrait).addr .Unsigned x86_64.PTR_SIZE = true := by
    decide +kernel
  have hVtBTB : inBounds (vtPtr tbL vtOtherTrait).addr .Unsigned x86_64.PTR_SIZE = true := by
    decide +kernel
  have hSzB : inBounds (vtOtherTrait.sizeBytes : Int) .Signed x86_64.PTR_SIZE = true := by
    decide +kernel
  have hRawBM := checkPtrM_raw_dyn_unchecked bmL vt m 8 vtOtherTrait dataPtr
    (bmLayout_provOf_inj _ _) hWf hLook hDataB hVtB
  have hRawTB := checkPtrM_raw_dyn_unchecked tbL vt mTB 8 vtOtherTrait dataPtrTB
    (tbLayout_provOf_inj _ _) hWf hLook hDataBTB hVtBTB
  have hNullBM := (checkPtrM_ref_dyn_rejects_invalid bmL vt m 8 vtOtherTrait .Immutable true true
    (bmLayout_provOf_inj _ _) hWf hLook hVtB hSzB).1 none
  have hUnOpBM := (evalUnOpM_dyn_correspondence bmL vt m 8 3 vtOtherTrait otherEvalVt
    dataPtr fnThin rawTy (bmLayout_provOf_inj _ _) hWf hLook hVtB rfl rfl hFn).2.2.2
  have hUnOpTB := (evalUnOpM_dyn_correspondence tbL vt mTB 8 3 vtOtherTrait otherEvalVt
    dataPtrTB fnThinTB rawTy (tbLayout_provOf_inj _ _) hWf hLook hVtBTB rfl rfl hFnTB).2.2.2
  refine ⟨hRawBM, hRawTB, hNullBM, ?_, ?_, hUnOpBM, hUnOpTB⟩
  · intro hNz hAl hDeref
    exact (checkPtrM_ref_dyn_ok_and_nonderef bmL vt m 8 vtOtherTrait .Immutable true true dataPtr
      (bmLayout_provOf_inj _ _) hWf hLook hVtB hSzB hDataB hNz hAl).1 hDeref
  · intro hNz hAl msg hDeref
    exact (checkPtrM_ref_dyn_ok_and_nonderef tbL vt mTB 8 vtOtherTrait .Immutable true true dataPtrTB
      (tbLayout_provOf_inj _ _) hWf hLook hVtBTB hSzB hDataBTB hNz hAl).2 msg hDeref

/-- **Universal dispatch-vs-`VTableMethodLookup` theorem, instantiated.** A raw
`*const dyn Trait` virtual call on the reproducer's `Receiver` vtable at slot
`3` dispatches externally to `eval_vt`, and the universal theorem then yields
MiniRust's `VTableMethodLookup` returning `eval_vt`'s function pointer
(address `4096`) on `Mach`. -/
theorem mr_virtual_dispatch_agrees_instance :
    ∃ (vtPtr' : ProvenancePtr) (e : ProtoVTableEntry),
      resolveVTablePtr vt Fx.traitPred vtPtr' = .ok e ∧
      get? e.slots 3 = some (.method recEvalVt) ∧
      evalUnOpM (.VTableMethodLookup ⟨⟨3⟩⟩)
          (.Ptr (ThinPointer.widen (vtPtr bmL e) none), .Ptr (.VTablePtr (traitName bmL e.traitPred)))
          (some (installVTables bmL vt (baseMach bmAllocs fnPtrsBM))) =
        .ok (.Ptr (ThinPointer.widen { addr := 4096, provenance := some (⟨100⟩, ()) } none),
          .Ptr .FnPtr) :=
  virtualCall_agrees_with_vtableMethodLookup bmL vt (baseMach bmAllocs fnPtrsBM) 8
    { traitPred := Fx.traitPred, slotIdx := 3, receiverIsRef := false }
    (Lm.queryCallState (Lm.widePtrValue (.prov 1 0) (.prov 40000 0))) Lm.queryCallerBody
    [.copy { local_ := 0, projection := [] }] { local_ := 0, projection := [] } (some 0) .continue_
    recEvalVt [.ptr { allocId := 1, offsetBytes := 0 } 8]
    [.init (Lm.widePtrValue (.prov 1 0) (.prov 40000 0))]
    { addr := 4096, provenance := some (⟨100⟩, ()) }
    (bmLayout_provOf_inj _ _) (by decide +kernel)
    (fun e he => List.all_eq_true.mp
      (by decide +kernel :
        vt.entries.all (fun e => inBounds (vtPtr bmL e).addr .Unsigned x86_64.PTR_SIZE) = true)
      e he)
    rfl rfl

/-- `Pin` unsizing sources: only `Pin<&[mut] T>` lowers (`Pin<*const T>` and
`Pin<Box<T>>` fail closed instead of reaching `unsizeDynValue`'s kind check as
UB). -/
theorem a3_pin_source_is_reference_only :
    (V06.lowerPinPtrSource? (.adt "core::pin::Pin" [.ref .mut (.adt recKey [])])).isSome = true ∧
    V06.lowerPinPtrSource? (.adt "core::pin::Pin" [.rawPtr .not (.adt recKey [])]) = none ∧
    V06.lowerPinPtrSource? (.adt "core::pin::Pin" [.adt "alloc::boxed::Box" [.adt recKey []]]) =
      none := by
  decide +kernel

end MrTest

/-! ## §4b. Adversarial B1 hardening & falsification suite -/

namespace B1Hardening
open Fx Canary Pillar

/-- Helper: call `evalVirtualCallProto` with explicit `receiverIsRef` and
`receiverIsMut` on the edited state `edit s49`. -/
def callWithFlags (vt : ProtoVTableTable) (pred : ProtoTraitPred) (slot : Nat)
    (isRef isMut : Bool) (edit : MachineState → MachineState) : Nat :=
  match Canary.s49 with
  | some s =>
    vcTag
      (evalVirtualCallProto vt
        { traitPred := pred, slotIdx := slot, receiverIsRef := isRef, receiverIsMut := isMut }
        (edit s) driverBody [cp 14, cp 1] (loc 20) 4 .continue_)
  | none => 9

/-- **1. `&mut dyn Trait` virtual call mutability, unlinked-callee validity
ordering, Tree Borrows strict-ancestor chain, and valid dangling ZST `.ptr`.**
* `&mut dyn Trait` (`receiverIsMut = true`) on a `.frozen` borrow tag is UB
  (tag `3`), EVEN when `callees = []` (never `.externalCall` = `1`)!
* `&mut dyn Trait` on a `.unique` borrow tag enters the callee (`0`).
* `&mut dyn Trait` on an immutable global allocation is UB (`3`), whereas
  `&dyn Trait` on the same immutable global enters the callee (`0`).
* `&dyn Trait` with a `.disabled` tag or misaligned offset when `callees = []`
  is UB (`3`), never `.externalCall` (`1`).
* A `.frozen` child borrow tag whose strict parent tag is `.disabled` is
  rejected by `refDataValid` (`false`).
* A valid dangling ZST `.ptr { allocId := 0, offsetBytes := 4 }` is accepted by
  `refDataValid` (`true`), while `.ptr { allocId := 0, offsetBytes := 0 }` is
  rejected (`false`). -/
theorem b1_mut_dyn_virtual_call_and_ancestor_and_zst :
    callWithFlags vtables Fx.traitPred 3 true true id = 3 ∧
    callWithFlags vtables Fx.traitPred 3 true true
      (fun s => { s with memory := { s.memory with callees := [] } }) = 3 ∧
    callWithFlags vtables Fx.traitPred 3 true true (fun s => withPerm s 2 .unique) = 0 ∧
    callWithFlags vtables Fx.traitPred 3 true false
      (fun s => { withPerm s 2 .disabled with memory := { (withPerm s 2 .disabled).memory with callees := [] } }) = 3 ∧
    callWithFlags vtables Fx.traitPred 3 true false
      (fun s => { withLocal s 14 (wide (ptrV 2 1) (ptrV 40001 0)) with
                  memory := { s.memory with callees := [] } }) = 3 ∧
    (match Canary.s49 with
     | some s =>
       let gAlloc : CapturedAllocation :=
         { allocId := 90, bytes := List.replicate 8 (some 0), relocations := [],
           align := { bytes := 4 }, mutability := .not }
       let sImm :=
         { withLocal s 14 (wide (ptrV 90 0) (ptrV 40001 0)) with
           memory := { s.memory with globals := gAlloc :: s.memory.globals } }
       (vcTag (evalVirtualCallProto vtables
          { traitPred := Fx.traitPred, slotIdx := 3, receiverIsRef := true, receiverIsMut := true }
          sImm driverBody [cp 14, cp 1] (loc 20) 4 .continue_),
        vcTag (evalVirtualCallProto vtables
          { traitPred := Fx.traitPred, slotIdx := 3, receiverIsRef := true, receiverIsMut := false }
          sImm driverBody [cp 14, cp 1] (loc 20) 4 .continue_))
     | none => (9, 9)) = (3, 0) ∧
    (match Canary.s49 with
     | some s =>
       let bParent : BorrowEntry :=
         { tag := 50, targetLocal := 5, targetProjection := [], perm := .disabled,
           parentTag := none, protector := none }
       let bChild : BorrowEntry :=
         { tag := 51, targetLocal := 5, targetProjection := [], perm := .frozen,
           parentTag := some 50, protector := none }
       let memChain := { s.memory with borrows := bChild :: bParent :: s.memory.borrows }
       let vtZst4 : ProtoVTableEntry := { vtRecTrait with sizeBytes := 0, alignBytes := 4 }
       (refDataValid 8 vtOtherTrait false { allocId := 51, offsetBytes := 0 }
          s.frame.locals memChain driverDecls layouts,
        refDataValid 8 vtZst4 false { allocId := 0, offsetBytes := 4 }
          s.frame.locals s.memory driverDecls layouts,
        refDataValid 8 vtZst4 false { allocId := 0, offsetBytes := 0 }
          s.frame.locals s.memory driverDecls layouts)
     | none => (true, false, true)) = (false, true, false) := by
  decide +kernel

/-- **2. Auto-trait fabrication, unrelated 0-method marker-trait upcast, and
inconsistent same-type layout across vtables are rejected.**
* `dyn TraitA -> dyn TraitA + Send` (`unsizeDynToDyn` with `autoTraits` growing)
  is ill-typed MIR and fails closed (`4`, never `.ok` and never UB: vendored Miri
  runs it without UB), while `dyn TraitA + Send -> dyn TraitA` succeeds (`0`).
* `upcastVTable?` rejects `dyn Sub -> dyn Marker` (unrelated 0-method trait
  whose 3-slot header is trivially a prefix of every vtable) and `unsizeDynToDyn`
  returns `.unsupported` (`4`), while `dyn Sub -> dyn Super` (`.traitVPtr`)
  and `dyn Sub2 -> dyn Super` (`primarySuperVTable? := some 3`) succeed.
* `wfProtoVTableTable` rejects tables where two vtables for the same
  `concreteTyKey` disagree on `sizeBytes`, `alignBytes`, or `isUninhabited`. -/
theorem b1_auto_trait_fabrication_and_unrelated_marker_upcast :
    let eSub := lookupVTableById Lm.corpusTable.entries 4
    let eSub2 := lookupVTableById Lm.corpusTable.entries 5
    (match eSub, eSub2 with
     | some s1, some s2 =>
       ( (upcastVTable? Lm.corpusTable.entries s1 Lm.predMarker).isNone,
         (upcastVTable? Lm.corpusTable.entries s1 Lm.predSuper).map (·.vtableId),
         (upcastVTable? Lm.corpusTable.entries s2 Lm.predSuper).map (·.vtableId) )
     | _, _ => (false, none, none)) = (true, some 3, some 3) ∧
    wfProtoVTableTable 8
      { vtables with entries := [{ vtRecTrait with isUninhabited := true }, vtOtherTrait, vtRecAlt] } =
      false ∧
    wfProtoVTableTable 8
      { vtables with entries := [{ vtRecTrait with sizeBytes := 8 }, vtOtherTrait, vtRecAlt] } =
      false ∧
    (match Canary.s39 with
     | some s =>
       let pSub : Value := wide (ptrV 1 0) (ptrV 40004 0)
       let pA : Value := wide (ptrV 1 0) (ptrV 40000 0)
       let predASend : ProtoTraitPred := { Lm.predA with autoTraits := ["Send"] }
       ( rvalTag (unsizeDynToDyn Lm.corpusTable 8 .raw false Lm.predA predASend
           pA s.frame.locals s.memory driverDecls layouts),
         rvalTag (unsizeDynToDyn Lm.corpusTable 8 .raw false predASend Lm.predA
           pA s.frame.locals s.memory driverDecls layouts),
         rvalTag (unsizeDynToDyn Lm.corpusTable 8 .raw false Lm.predSub Lm.predMarker
           pSub s.frame.locals s.memory driverDecls layouts) )
     | none => (9, 9, 9)) = (4, 0, 4) := by
  decide +kernel

/-- **3. 32-bit target (`ptrBytes = 4`) layout overflow bounds, stack-page
aliasing (`stackLocalAddrPageBase 4 = 32768`), and ZST wrapped-null UB.** -/
def vt32Ok : ProtoVTableEntry :=
  { vtableId := 0, vtableAllocId := 20000, concreteTyKey := recKey, traitPred := Fx.traitPred,
    sizeBytes := 4, alignBytes := 4,
    slots := [.dropInPlace none, .size, .align, .method recEvalVt, .method recTagVt] }

def vt32Zst : ProtoVTableEntry :=
  { vtableId := 1, vtableAllocId := 20001, concreteTyKey := "()", traitPred := altPred,
    sizeBytes := 0, alignBytes := 4,
    slots := [.dropInPlace none, .size, .align, .vacant] }

def table32 : ProtoVTableTable :=
  { entries := [vt32Ok, vt32Zst],
    dynTypes := [(traitKey, Fx.traitPred), (altKey, altPred)] }

def layouts32 : LayoutTable := { layouts with pointerBits := 32 }

theorem b1_32bit_target_and_overflow_bounds :
    entryLayoutOk 4 { vt32Ok with sizeBytes := 0, alignBytes := 2 ^ 31 } = false ∧
    entryLayoutOk 4 { vt32Ok with sizeBytes := 0, alignBytes := 2 ^ 100 } = false ∧
    entryLayoutOk 4 { vt32Ok with sizeBytes := 2 ^ 31 - 4, alignBytes := 8 } = false ∧
    entryLayoutOk 4 vt32Ok = true ∧
    wfProtoVTableTable 4 table32 = true ∧
    vtableAllocDisjoint 4 (driverState driverBody 7 24).memory 32768 = false ∧
    vtableAllocDisjoint 4 (driverState driverBody 7 24).memory 40000 = false ∧
    vtableAllocDisjoint 4 (driverState driverBody 7 24).memory 20000 = true ∧
    vtableEnvOk 4 table32 (driverState driverBody 7 24).memory = true ∧
    resCode (dynSizeOfValProto table32 4 Fx.traitPred
      (mkDynPtr 4 (.prov { allocId := 1, offsetBytes := 0 }) vt32Ok)) = (0, 4) ∧
    resCode (dynAlignOfValProto table32 4 Fx.traitPred
      (mkDynPtr 4 (.prov { allocId := 1, offsetBytes := 0 }) vt32Ok)) = (0, 4) ∧
    (match Canary.s39 with
     | some s =>
       ( rvalTag (unsizeDynToDyn table32 4 .ref false altPred altPred
           (mkDynPtr 4 (.addr (2 ^ 32)) vt32Zst) s.frame.locals s.memory driverDecls layouts32),
         rvalTag (unsizeDynToDyn table32 4 .ref false altPred altPred
           (mkDynPtr 4 (.addr 4) vt32Zst) s.frame.locals s.memory driverDecls layouts32) )
     | none => (9, 9)) = (3, 0) := by
  decide +kernel

/-- **4. Non-zero receiver field `offsetBytes = 4` end-to-end MIR execution.**
`OuterPair { lead: u32, inner: Receiver }` puts `inner` at byte offset `4`.
Borrowing `&outer.inner` yields a pointer with `offsetBytes = 4`, unsizing to
`&dyn Trait` preserves `offsetBytes = 4`, and virtual dispatch to
`Receiver::eval_vt(&self, 10)` narrows the receiver keeping `offsetBytes = 4`
so it reads `inner.bias` (`25`, giving `10 ^ 25 = 19`) rather than `outer.lead`
(`99`, which would give `10 ^ 99 = 105`). -/
def outerPairKey : String := "b1::OuterPair"

def layoutsWithOuterPair : LayoutTable :=
  { layouts with
    entries :=
      layouts.entries ++
        [{ size := { bytes := 8 }, align := { bytes := 4 },
           backendRepr :=
             .scalarPair (.initialized (.int 32 false) { start := 0, end_ := 4294967295 })
               (.initialized (.int 32 false) { start := 0, end_ := 4294967295 }),
           fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }] [0, 1],
           variants := .single 0, isUninhabited := false, fieldLayouts := [0, 1] }] }

def outerPairTy : Ty := { kind := .adt outerPairKey [], layoutIdx := 9 }

def fieldOffsetCallerBody (lead bias : Nat) : CapturedMir :=
  { defPath := "b1::field_offset_caller", phase := .runtimePostCleanup, role := .model,
    argCount := 0,
    localDecls := [decl u32Ty, decl outerPairTy, decl recTy, decl refRecTy, decl refDynTy],
    basicBlocks :=
      [ bb [ live 1, live 2, live 3, live 4,
             asg 2 (.aggregate (.adt recKey 0 none) [cU32 bias]),
             asg 1 (.aggregate (.adt outerPairKey 0 none) [cU32 lead, mv 2]),
             asg 3 (.ref .shared { local_ := 1, projection := [.field 1 recTy] }),
             asg 4 (unsize (mv 3) refDynTy) ]
           (.call (virtFn evalVtPath traitKey) [cp 4, cU32 10] (loc 0) (some 1) .continue_),
        bb [] .return_ ],
    fnAbi := { args := [], ret := u32Abi, conv := .rust, canUnwind := false },
    layouts := layoutsWithOuterPair, allocations := [] }

theorem b1_nonzero_receiver_offset_mir_execution :
    scalarOf (runMirProto prog (fieldOffsetCallerBody 99 25) 64
      (initMachineStateWithCallees (fieldOffsetCallerBody 99 25) [] methodBodies)) =
        some (19, 4) ∧
    scalarOf (runMirProto prog (fieldOffsetCallerBody 99 42) 64
      (initMachineStateWithCallees (fieldOffsetCallerBody 99 42) [] methodBodies)) =
        some (32, 4) ∧
    scalarOf (runMirProto prog (fieldOffsetCallerBody 7 25) 64
      (initMachineStateWithCallees (fieldOffsetCallerBody 7 25) [] methodBodies)) =
        some (19, 4) := by
  decide +kernel

/-- **5. `stepMirFnProto` dynamic-layout intrinsics (`size_of_val` /
`align_of_val`), `&raw mut (*shared_dyn)` failing closed (ill-typed MIR,
`rustc` E0596), diverging virtual call, and
`evalWidePtrEqProto` `.uninit` / heterogeneous metadata UB.** -/
def usizeLayout : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 8 },
    backendRepr := .scalar (.initialized (.int 64 false) { start := 0, end_ := 18446744073709551615 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def layoutsWithUsize : LayoutTable := { layouts with entries := layouts.entries ++ [usizeLayout] }
def usizeTy : Ty := { kind := .uint .usize, layoutIdx := 9 }

def dynLayoutIntrinsicCallerBody (useOther : Bool) (isAlign : Bool) : CapturedMir :=
  let intrinsicPath :=
    match isAlign with
    | false => "core::intrinsics::size_of_val"
    | true => "core::intrinsics::align_of_val"
  { defPath := "b1::dyn_layout_intrinsic_caller", phase := .runtimePostCleanup, role := .model,
    argCount := 0,
    localDecls :=
      [ decl usizeTy,
        decl (match useOther with | false => recTy | true => otherTy),
        decl (match useOther with | false => refRecTy | true => refOtherTy),
        decl refDynTy ],
    basicBlocks :=
      [ bb [ live 1, live 2, live 3,
             asg 1 (match useOther with
                    | false => .aggregate (.adt recKey 0 none) [cU32 1]
                    | true => .aggregate (.adt otherKey 0 none) [cU32 1, cU32 2]),
             asg 2 (.ref .shared (loc 1)),
             asg 3 (unsize (mv 2) refDynTy) ]
           (.call (fnOp intrinsicPath [.dynamic traitKey]) [cp 3] (loc 0) (some 1) .continue_),
        bb [] .return_ ],
    fnAbi :=
      { args := [], ret := { layout := usizeLayout, mode := .direct },
        conv := .rust, canUnwind := false },
    layouts := layoutsWithUsize, allocations := [] }

def sharedToRawMutDynBody : CapturedMir :=
  { defPath := "b1::shared_to_raw_mut_dyn", phase := .runtimePostCleanup, role := .model,
    argCount := 0,
    localDecls := [decl u32Ty, decl recTy, decl refRecTy, decl refDynTy, decl rawMutDynTy],
    basicBlocks :=
      [ bb [ live 1, live 2, live 3, live 4,
             asg 1 (.aggregate (.adt recKey 0 none) [cU32 1]),
             asg 2 (.ref .shared (loc 1)),
             asg 3 (unsize (mv 2) refDynTy),
             asg 4 (.rawPtr .mut (derefPlace 3)),
             asg 0 (.use (cU32 0)) ] .return_ ],
    fnAbi := { args := [], ret := u32Abi, conv := .rust, canUnwind := false },
    layouts := layouts, allocations := [] }

def divergeMethodPath : String := "b1::Diverge::boom"
def recDivergePath : String := "<miri_diff_corpus::__AnnealVtableReceiver43543 as b1::Diverge>::boom"

def recDivergeBody : CapturedMir :=
  { defPath := recDivergePath, phase := .runtimePostCleanup, role := .model, argCount := 1,
    localDecls := [decl u32Ty, decl refRecTy],
    basicBlocks := [bb [] .unreachable],
    fnAbi := { args := [ptrAbi], ret := u32Abi, conv := .rust, canUnwind := false },
    layouts := layouts, allocations := [] }

def divergeProg : ProtoDynProgram :=
  { vtables :=
      { entries :=
          [{ vtableId := 0, vtableAllocId := 40000, concreteTyKey := recKey,
             traitPred := { principalTrait? := some "b1::Diverge" },
             sizeBytes := 4, alignBytes := 4,
             slots := [.dropInPlace none, .size, .align, .method recDivergePath] }],
        dynTypes := [("b1::Diverge", { principalTrait? := some "b1::Diverge" })] },
    virtualMethods := [(divergeMethodPath, 3)] }

def divergeCallerBody : CapturedMir :=
  let refDivTy : Ty := { kind := .ref .not (.dynamic "b1::Diverge"), layoutIdx := 5 }
  { defPath := "b1::diverge_caller", phase := .runtimePostCleanup, role := .model, argCount := 0,
    localDecls := [decl u32Ty, decl recTy, decl refRecTy, decl refDivTy],
    basicBlocks :=
      [ bb [ live 1, live 2, live 3,
             asg 1 (.aggregate (.adt recKey 0 none) [cU32 1]),
             asg 2 (.ref .shared (loc 1)),
             asg 3 (unsize (mv 2) refDivTy) ]
           (.call (virtFn divergeMethodPath "b1::Diverge") [cp 3] (loc 0) none .continue_) ],
    fnAbi := { args := [], ret := u32Abi, conv := .rust, canUnwind := false },
    layouts := layouts, allocations := [] }

theorem b1_intrinsics_raw_mut_diverge_and_wide_eq_ub :
    scalarOf (runMirProto prog (dynLayoutIntrinsicCallerBody false false) 32
      (initMachineStateWithCallees (dynLayoutIntrinsicCallerBody false false) [] [])) =
        some (4, 8) ∧
    scalarOf (runMirProto prog (dynLayoutIntrinsicCallerBody true false) 32
      (initMachineStateWithCallees (dynLayoutIntrinsicCallerBody true false) [] [])) =
        some (8, 8) ∧
    scalarOf (runMirProto prog (dynLayoutIntrinsicCallerBody true true) 32
      (initMachineStateWithCallees (dynLayoutIntrinsicCallerBody true true) [] [])) =
        some (4, 8) ∧
    tagOf (runMirProto prog sharedToRawMutDynBody 32
      (initMachineStateWithCallees sharedToRawMutDynBody [] [])) = 4 ∧
    (advanceSteps divergeCallerBody (stepMirFnProto divergeProg divergeCallerBody) 7
      (initMachineStateWithCallees divergeCallerBody [] [recDivergeBody])).map
        (fun s => s.memory.activeCallee.map (·.defPath)) = some (some recDivergePath) ∧
    wideEq .uninit (localVal 10) = (3, 0) ∧
    wideEq (wide (ptrV 1 0) (scV 2)) (localVal 10) = (3, 0) := by
  decide +kernel


/-! ### A1 regressions -/

/-- `&raw const (*r)` through a trait-object reference `r` whose borrow tag is
`.disabled`: creating a raw pointer performs no access, so the end-to-end run
does not fault at the raw borrow. The body disables `&rec` by writing `rec`
directly, then takes `&raw const *r` and returns `0`. -/
def rawBorrowAfterDisableBody : CapturedMir :=
  { defPath := "a1::raw_borrow_after_disable", phase := .runtimePostCleanup, role := .model,
    argCount := 0,
    localDecls := [decl u32Ty, decl recTy, decl refRecTy, decl refDynTy, decl rawDynTy],
    basicBlocks :=
      [ bb [ live 1, live 2, live 3, live 4,
             asg 1 (.aggregate (.adt recKey 0 none) [cU32 1]),
             asg 2 (.ref .shared (loc 1)),
             asg 3 (unsize (mv 2) refDynTy),
             asg 1 (.aggregate (.adt recKey 0 none) [cU32 5]),
             asg 4 (.rawPtr .not (derefPlace 3)),
             asg 0 (.use (cU32 0)) ] .return_ ],
    fnAbi := { args := [], ret := u32Abi, conv := .rust, canUnwind := false },
    layouts := layouts, allocations := [] }

/-- Virtual-call caller whose receiver has type `recvTy` (a `&dyn Trait`
reference, a `Box<dyn Trait>`, or a `Pin<&mut dyn Trait>`). -/
def wrappedReceiverCaller (recvTy : Ty) : CapturedMir :=
  { defPath := "a1::wrapped_receiver_caller", phase := .runtimePostCleanup, role := .model,
    argCount := 0, localDecls := [decl u32Ty, decl recvTy, decl u32Ty],
    basicBlocks :=
      [bb [] (.call (virtFn evalVtPath traitKey) [cp 1, cp 2] (loc 0) (some 0) .continue_)],
    fnAbi := { args := [], ret := u32Abi, conv := .rust, canUnwind := false },
    layouts := layouts, allocations := [] }

/-- Site classification code: `0` not virtual, `4` unsupported, `[ref, mut]` site. -/
def siteCode : VirtualSiteResolution → List Nat
  | .notVirtual => [0]
  | .unsupported => [4]
  | .site st => [1, (match st.receiverIsRef with | true => 1 | false => 0),
                    (match st.receiverIsMut with | true => 1 | false => 0)]

/-- **A1 regressions.**
1. `&raw const *r` after `r`'s tag was disabled by a direct write to the owner
   runs to completion (`0`): raw borrows are not Tree Borrows accesses.
2. A `Box<dyn Trait>` receiver fails closed (`[4]`) instead of being treated as a
   raw pointer (which skipped receiver validity and the protector);
   `Pin<&mut dyn Trait>` is a mutable reference receiver (`[1, 1, 1]`);
   `&dyn Trait` stays a shared reference receiver (`[1, 1, 0]`) and
   `*const dyn Trait` a raw receiver (`[1, 0, 0]`).
3. Auto-trait fabrication with an *invalid* vtable pointer is still UB: the
   runtime vtable check comes before the type-level fail-closed check. -/
theorem a1_raw_borrow_receiver_class_and_auto_trait_order :
    scalarOf (runMirProto prog rawBorrowAfterDisableBody 32
      (initMachineStateWithCallees rawBorrowAfterDisableBody [] [])) = some (0, 4) ∧
    [ siteCode (virtualCallSite? prog
        (wrappedReceiverCaller
          { kind := .adt "alloc::boxed::Box" [.dynamic traitKey], layoutIdx := 5 })
        (virtFn evalVtPath traitKey) [cp 1, cp 2]),
      siteCode (virtualCallSite? prog
        (wrappedReceiverCaller
          { kind := .adt "core::pin::Pin" [.ref .mut (.dynamic traitKey)], layoutIdx := 5 })
        (virtFn evalVtPath traitKey) [cp 1, cp 2]),
      siteCode (virtualCallSite? prog (wrappedReceiverCaller refDynTy)
        (virtFn evalVtPath traitKey) [cp 1, cp 2]),
      siteCode (virtualCallSite? prog (wrappedReceiverCaller rawDynTy)
        (virtFn evalVtPath traitKey) [cp 1, cp 2]) ] =
      [[4], [1, 1, 1], [1, 1, 0], [1, 0, 0]] ∧
    rvalTag (unsizeDynToDyn Lm.corpusTable 8 .raw false Lm.predA
      { Lm.predA with autoTraits := ["Send"] } (wide (ptrV 1 0) (ptrV 40000 8)) [] emptyMemory []
      layouts) = 3 := by
  decide +kernel

/-! ### B2 regressions (`Pin<&mut dyn>` end-to-end protector, `dynRawBorrowProto?`
safe-reference validity without TB false positives, trailing-arg ABI check,
and `stepDynLayoutIntrinsicProto` environment gate) -/

def pinRefMutDynPokeTy : Ty :=
  { kind := .adt "core::pin::Pin" [.ref .mut (.dynamic C16.pokeKey)], layoutIdx := 5 }
def pinRefDynPokeTy : Ty :=
  { kind := .adt "core::pin::Pin" [.ref .not (.dynamic C16.pokeKey)], layoutIdx := 5 }
def pinRefMutRecTy : Ty :=
  { kind := .adt "core::pin::Pin" [.ref .mut (.adt recKey [])], layoutIdx := 3 }

/-- Concrete `impl Poke for Receiver { fn poke(self: Pin<&mut Receiver>, alias: *mut u32) -> u32 }`
that projects `self.pointer` (`.field 0`), reads `(*self.pointer).bias`, optionally
writes through `alias` while the protected `Pin<&mut Receiver>` is live, and returns
the bias. -/
def pinPokeBody (writeInCallee : Bool) : CapturedMir :=
  { defPath := C16.recPoke, phase := .runtimePostCleanup, role := .model, argCount := 2,
    localDecls := [decl u32Ty, decl pinRefMutRecTy, decl C16.rawU32Ty, decl refMutRecTy, decl u32Ty],
    basicBlocks :=
      [ bb ([ live 3, live 4,
              asg 3 (.use (.copy { local_ := 1, projection := [.field 0 refMutRecTy] })),
              asg 4 (.use (selfField 3 0)) ] ++
            (match writeInCallee with
             | true =>
               [{ kind := .assign { local_ := 2, projection := [.deref] } (.use (cU32 9)),
                  span := "<b2-pin>" }]
             | false => []) ++
            [asg 0 (.use (cp 4))]) .return_ ],
    fnAbi := { args := [ptrAbi, ptrAbi], ret := u32Abi, conv := .rust, canUnwind := false },
    layouts := layouts, allocations := [] }

/-- Caller constructing `Pin { pointer: (&mut rec) as &mut dyn Poke }` (runtime
value `.aggregate 0 [widePtr]`) and invoking `<dyn Poke as Poke>::poke(pin, alias)`. -/
def pinCallerBody (writeAfter : Bool) : CapturedMir :=
  { defPath := "b2::pin_caller", phase := .runtimePostCleanup, role := .model, argCount := 0,
    localDecls :=
      [ decl u32Ty, decl recTy, decl C16.rawU32Ty, decl C16.refMutPokeTy, decl refMutRecTy,
        decl pinRefMutDynPokeTy, decl u32Ty ],
    basicBlocks :=
      [ bb [ live 1, live 2, live 3, live 4, live 5, live 6,
             asg 1 (.aggregate (.adt recKey 0 none) [cU32 17]),
             asg 2 (.rawPtr .mut { local_ := 1, projection := [.field 0 u32Ty] }),
             asg 4 (.ref (.mut false) (loc 1)),
             asg 3 (unsize (mv 4) C16.refMutPokeTy),
             asg 5 (.aggregate (.adt "core::pin::Pin" 0 none) [mv 3]) ]
           (.call (virtFn C16.pokePath C16.pokeKey) [cp 5, cp 2] (loc 6) (some 1) .continue_),
        bb ((match writeAfter with
             | true => [asg 1 (.aggregate (.adt recKey 0 none) [cU32 5])]
             | false => []) ++ [asg 0 (.use (cp 6))]) .return_ ],
    fnAbi := { args := [], ret := u32Abi, conv := .rust, canUnwind := false },
    layouts := layouts, allocations := [] }

def runPin (writeInCallee writeAfter : Bool) : ProtoRunResult :=
  runMirProto C16.pokeProg (pinCallerBody writeAfter) 64
    (initMachineStateWithCallees (pinCallerBody writeAfter) [] [pinPokeBody writeInCallee])

def pinStateAfterCall : Option MachineState :=
  advanceSteps (pinCallerBody false) (stepMirFnProto C16.pokeProg (pinCallerBody false)) 12
    (initMachineStateWithCallees (pinCallerBody false) [] [pinPokeBody false])

/-- **B2-1: End-to-end `Pin<&mut dyn Poke>` virtual dispatch & TB protector.**
1. Clean `Pin<&mut dyn Poke>::poke` unwraps `Pin { pointer: widePtr }`,
   allocates a fresh protected child tag `3` (under caller tag `2`, NOT mutating
   caller tag `2` via `attachOnly`!), re-wraps callee `_1` as `.aggregate 0 [ptr]`,
   projects `self.pointer` (`.field 0`), reads `bias = 17`, and returns `17u32`.
2. Foreign write through `alias` during the `Pin<&mut dyn Poke>` call is UB (`3`).
3. Overwriting `rec` strictly after return succeeds (`17u32`, protector released).
4. `classifyVirtualReceiver` rejects non-`dyn` `Pin<&mut u32>` and `&u32`.
5. `Pin<&dyn Poke>` cannot dispatch to a `Pin<&mut Receiver>` callee (UB `3`). -/
theorem b2_pin_mut_dyn_end_to_end_and_protector :
    scalarOf (runPin false false) = some (17, 4) ∧
    tagOf (runPin true false) = 3 ∧
    scalarOf (runPin false true) = some (17, 4) ∧
    pinStateAfterCall.map C16.protectorView = some ([1], [(3, 3, 2), (2, 0, 0), (1, 0, 0)]) ∧
    [ siteCode (virtualCallSite? prog
        (wrappedReceiverCaller { kind := .adt "core::pin::Pin" [.ref .mut (.uint .u32)], layoutIdx := 5 })
        (virtFn evalVtPath traitKey) [cp 1, cp 2]),
      siteCode (virtualCallSite? prog (wrappedReceiverCaller refRecTy)
        (virtFn evalVtPath traitKey) [cp 1, cp 2]) ] = [[4], [4]] ∧
    (match advanceSteps (pinCallerBody false) (stepMirFnProto C16.pokeProg (pinCallerBody false)) 11
        (initMachineStateWithCallees (pinCallerBody false) [] [pinPokeBody false]) with
     | some s =>
       vcTag (evalVirtualCallProto C16.pokeProg.vtables
         { traitPred := C16.pokePred, slotIdx := 3, receiverIsRef := true,
           receiverIsMut := false, receiverIsPin := true }
         s (pinCallerBody false) [cp 5, cp 2] (loc 6) 1 .continue_)
     | none => 9) = 3 := by
  decide +kernel

/-- `&raw const (*r)` after `StorageDead(rec)` makes `r : &dyn Trait` dangling. -/
def rawBorrowAfterDeadLocalBody : CapturedMir :=
  { defPath := "b2::raw_borrow_after_dead", phase := .runtimePostCleanup, role := .model,
    argCount := 0,
    localDecls := [decl u32Ty, decl recTy, decl refRecTy, decl refDynTy, decl rawDynTy],
    basicBlocks :=
      [ bb [ live 1, live 2, live 3, live 4,
             asg 1 (.aggregate (.adt recKey 0 none) [cU32 1]),
             asg 2 (.ref .shared (loc 1)),
             asg 3 (unsize (mv 2) refDynTy),
             { kind := .storageDead 1, span := "<b2>" },
             asg 4 (.rawPtr .not (derefPlace 3)),
             asg 0 (.use (cU32 0)) ] .return_ ],
    fnAbi := { args := [], ret := u32Abi, conv := .rust, canUnwind := false },
    layouts := layouts, allocations := [] }

/-- **B2-2: Hardened `dynRawBorrowProto?` closes `A1`'s safe-reference hole
while preserving zero false-positive TB UB.**
* `&raw const (*r)` after `StorageDead(rec)` faults UB (`3`).
* `&raw const (*r)` with a null pointer, misaligned pointer, or offset/wrong-trait
  vtable pointer faults UB (`3`).
* `&raw const (*p)` on a raw `*const dyn Trait` with null/dangling data STILL
  returns `.ok` (`0`).
* `&raw const (*r)` with an unresolved existential binder fails closed (`4`). -/
theorem b2_dyn_raw_borrow_ref_validity_without_tb_fp :
    tagOf (runMirProto prog rawBorrowAfterDeadLocalBody 32
      (initMachineStateWithCallees rawBorrowAfterDeadLocalBody [] [])) = 3 ∧
    (match Canary.s49 with
     | some s =>
       let codeOf (r : Option (ProtoRes Value)) : Nat :=
         match r with
         | some (.ok _) => 0
         | some .ub => 3
         | some .unsupported => 4
         | none => 9
       let badDeclsRaw := (set? driverDecls 14 (decl rawDynTy)).getD driverDecls
       let unresolvedVt : ProtoVTableTable :=
         { vtables with
           dynTypes := [(traitKey, { Fx.traitPred with hasUnresolvedExistentialBinder := true }),
                        (altKey, altPred)] }
       [ codeOf (dynRawBorrowProto? vtables 8 .not
           (withLocal s 14 (wide (ptrV 0 0) (ptrV 40001 0))).frame.locals
           s.memory driverDecls layouts (derefPlace 14)),
         codeOf (dynRawBorrowProto? vtables 8 .not
           (withLocal s 14 (wide (ptrV 2 1) (ptrV 40001 0))).frame.locals
           s.memory driverDecls layouts (derefPlace 14)),
         codeOf (dynRawBorrowProto? vtables 8 .not
           (withLocal s 14 (wide (ptrV 2 0) (ptrV 40001 8))).frame.locals
           s.memory driverDecls layouts (derefPlace 14)),
         codeOf (dynRawBorrowProto? vtables 8 .not
           (withLocal s 14 (wide (ptrV 2 0) (ptrV 40002 0))).frame.locals
           s.memory driverDecls layouts (derefPlace 14)),
         codeOf (dynRawBorrowProto? vtables 8 .not
           (withLocal s 14 (wide (scV 0) (ptrV 40001 0))).frame.locals
           s.memory badDeclsRaw layouts (derefPlace 14)),
         codeOf (dynRawBorrowProto? unresolvedVt 8 .not
           s.frame.locals s.memory driverDecls layouts (derefPlace 14)) ]
     | none => [9]) = [3, 3, 3, 3, 0, 4] := by
  decide +kernel

/-- **B2-3 & B2-4: Trailing argument ABI size mismatch, non-pointer concrete
receiver `_1`, `stepDynLayoutIntrinsicProto` `vtableEnvOk` gate, and
`core::mem::{size_of_val_raw, align_of_val_raw}`.** -/
def badTrailingArgCallee : CapturedMir :=
  let u64Abi : ArgAbi := { layout := usizeLayout, mode := .direct }
  { otherEvalVtBody with
    fnAbi := { args := [ptrAbi, u64Abi], ret := u32Abi, conv := .rust, canUnwind := false } }

def nonPtrRecvCallee : CapturedMir :=
  { otherEvalVtBody with
    localDecls := [decl u32Ty, decl usizeTy, decl u32Ty] }

def memRawSizeCallerBody : CapturedMir :=
  { defPath := "b2::mem_raw_size_caller", phase := .runtimePostCleanup, role := .model,
    argCount := 0,
    localDecls := [decl usizeTy, decl otherTy, decl refOtherTy, decl refDynTy],
    basicBlocks :=
      [ bb [ live 1, live 2, live 3,
             asg 1 (.aggregate (.adt otherKey 0 none) [cU32 1, cU32 2]),
             asg 2 (.ref .shared (loc 1)),
             asg 3 (unsize (mv 2) refDynTy) ]
           (.call (fnOp "core::mem::size_of_val_raw" [.dynamic traitKey]) [cp 3] (loc 0)
             (some 1) .continue_),
        bb [] .return_ ],
    fnAbi :=
      { args := [], ret := { layout := usizeLayout, mode := .direct },
        conv := .rust, canUnwind := false },
    layouts := layoutsWithUsize, allocations := [] }

theorem b2_trailing_arg_abi_nonptr_recv_and_intrinsic_env_gate :
    callWithFlags vtables Fx.traitPred 3 true false
      (fun s => { s with memory := { s.memory with callees := [badTrailingArgCallee] } }) = 3 ∧
    callWithFlags vtables Fx.traitPred 3 true false
      (fun s => { s with memory := { s.memory with callees := [nonPtrRecvCallee] } }) = 3 ∧
    scalarOf (runMirProto prog memRawSizeCallerBody 32
      (initMachineStateWithCallees memRawSizeCallerBody [] [])) = some (8, 8) ∧
    (let collidingProg : ProtoDynProgram :=
       { prog with
         vtables :=
           { vtables with
             entries := [{ vtRecTrait with vtableAllocId := 1 }, vtOtherTrait, vtRecAlt] } }
     tagOf (runMirProto collidingProg (dynLayoutIntrinsicCallerBody false false) 32
       (initMachineStateWithCallees (dynLayoutIntrinsicCallerBody false false) [] []))) = 4 := by
  decide +kernel

/-! ### B3 regressions (`CoerceUnsized` `Pin<&mut T> -> Pin<&mut dyn Trait>`
& `Pin` upcast end-to-end, fail-closed `Box<dyn>`/`&Wrapper<dyn>` avoiding
false-positive `.ub`, `Pin` ranged TB agreement, and `V06`/`V08` float/`i128`/
`Pin` dialect symmetry) -/

/-- Caller constructing `Pin::new(&mut rec)` FIRST (type `Pin<&mut Receiver>`),
then coercing `Pin<&mut Receiver> as Pin<&mut dyn Poke> (PointerCoercion(Unsize))`
through `stepMirFnProto`, and dispatching `<dyn Poke as Poke>::poke(pin, alias)`. -/
def pinUnsizeCallerBody (writeAfter : Bool) : CapturedMir :=
  { defPath := "b3::pin_unsize_caller", phase := .runtimePostCleanup, role := .model,
    argCount := 0,
    localDecls :=
      [ decl u32Ty, decl recTy, decl C16.rawU32Ty, decl refMutRecTy, decl pinRefMutRecTy,
        decl pinRefMutDynPokeTy, decl u32Ty ],
    basicBlocks :=
      [ bb [ live 1, live 2, live 3, live 4, live 5, live 6,
             asg 1 (.aggregate (.adt recKey 0 none) [cU32 23]),
             asg 2 (.rawPtr .mut { local_ := 1, projection := [.field 0 u32Ty] }),
             asg 3 (.ref (.mut false) (loc 1)),
             asg 4 (.aggregate (.adt "core::pin::Pin" 0 none) [mv 3]),
             asg 5 (unsize (mv 4) pinRefMutDynPokeTy) ]
           (.call (virtFn C16.pokePath C16.pokeKey) [cp 5, cp 2] (loc 6) (some 1) .continue_),
        bb ((match writeAfter with
             | true => [asg 1 (.aggregate (.adt recKey 0 none) [cU32 5])]
             | false => []) ++ [asg 0 (.use (cp 6))]) .return_ ],
    fnAbi := { args := [], ret := u32Abi, conv := .rust, canUnwind := false },
    layouts := layouts, allocations := [] }

def runPinUnsize (writeInCallee writeAfter : Bool) : ProtoRunResult :=
  runMirProto C16.pokeProg (pinUnsizeCallerBody writeAfter) 64
    (initMachineStateWithCallees (pinUnsizeCallerBody writeAfter) [] [pinPokeBody writeInCallee])

/-- `Pin<&mut dyn Sub> -> Pin<&mut dyn Super>` upcast end-to-end through `stepMirFnProto`. -/
def subKey : String := "b3::Sub"
def supKey : String := "b3::Super"
def supPath : String := "b3::Super::sup"
def recSupPath : String := "<miri_diff_corpus::__AnnealVtableReceiver43543 as b3::Super>::sup"
def subPred : ProtoTraitPred := { principalTrait? := some subKey }
def supPred : ProtoTraitPred := { principalTrait? := some supKey }

def pinSupProg : ProtoDynProgram :=
  { vtables :=
      { entries :=
          [ { vtableId := 0, vtableAllocId := 40000, concreteTyKey := recKey, traitPred := supPred,
              sizeBytes := 4, alignBytes := 4,
              slots := [.dropInPlace none, .size, .align, .method recSupPath] },
            { vtableId := 1, vtableAllocId := 40001, concreteTyKey := recKey, traitPred := subPred,
              sizeBytes := 4, alignBytes := 4,
              slots := [.dropInPlace none, .size, .align, .method recSupPath, .traitVPtr 0] } ],
        dynTypes := [(supKey, supPred), (subKey, subPred)] },
    virtualMethods := [(supPath, 3)] }

def pinSupBody : CapturedMir :=
  { defPath := recSupPath, phase := .runtimePostCleanup, role := .model, argCount := 1,
    localDecls := [decl u32Ty, decl pinRefMutRecTy, decl refMutRecTy],
    basicBlocks :=
      [ bb [ live 2,
             asg 2 (.use (.copy { local_ := 1, projection := [.field 0 refMutRecTy] })),
             asg 0 (.use (selfField 2 0)) ] .return_ ],
    fnAbi := { args := [ptrAbi], ret := u32Abi, conv := .rust, canUnwind := false },
    layouts := layouts, allocations := [] }

def pinUpcastCallerBody : CapturedMir :=
  let pinSubTy : Ty := { kind := .adt "core::pin::Pin" [.ref .mut (.dynamic subKey)], layoutIdx := 5 }
  let pinSupTy : Ty := { kind := .adt "core::pin::Pin" [.ref .mut (.dynamic supKey)], layoutIdx := 5 }
  { defPath := "b3::pin_upcast_caller", phase := .runtimePostCleanup, role := .model, argCount := 0,
    localDecls :=
      [ decl u32Ty, decl recTy, decl refMutRecTy, decl pinRefMutRecTy, decl pinSubTy, decl pinSupTy ],
    basicBlocks :=
      [ bb [ live 1, live 2, live 3, live 4, live 5,
             asg 1 (.aggregate (.adt recKey 0 none) [cU32 41]),
             asg 2 (.ref (.mut false) (loc 1)),
             asg 3 (.aggregate (.adt "core::pin::Pin" 0 none) [mv 2]),
             asg 4 (unsize (mv 3) pinSubTy),
             asg 5 (unsize (mv 4) pinSupTy) ]
           (.call (virtFn supPath supKey) [cp 5] (loc 0) (some 1) .continue_),
        bb [] .return_ ],
    fnAbi := { args := [], ret := u32Abi, conv := .rust, canUnwind := false },
    layouts := layouts, allocations := [] }

/-- Unsupported `CoerceUnsized` ADT unsizing target (`Box<dyn>`, `Pin<Box<dyn>>`,
`&Wrapper<dyn>`): MUST fail closed with `.unsupported` (`4`), NEVER false-positive
`.ub` (`3`) from `Trusted`'s slice-only `evalUnsizeCoercion`. -/
def unsupportedDynAdtUnsizeBody (srcTy targetTy : Ty) : CapturedMir :=
  { defPath := "b3::unsupported_dyn_adt_unsize", phase := .runtimePostCleanup, role := .model,
    argCount := 0,
    localDecls := [decl u32Ty, decl recTy, decl refRecTy, decl srcTy, decl targetTy],
    basicBlocks :=
      [ bb [ live 1, live 2, live 3, live 4,
             asg 1 (.aggregate (.adt recKey 0 none) [cU32 1]),
             asg 2 (.ref .shared (loc 1)),
             asg 3 (.aggregate (.adt "wrapper" 0 none) [mv 2]),
             asg 4 (unsize (mv 3) targetTy),
             asg 0 (.use (cU32 0)) ] .return_ ],
    fnAbi := { args := [], ret := u32Abi, conv := .rust, canUnwind := false },
    layouts := layouts, allocations := [] }

open Anneal.RefFrame in
/-- **B3 regressions.**
1. `Pin<&mut Receiver> as Pin<&mut dyn Poke> (PointerCoercion(Unsize))` runs
   end-to-end through `stepMirFnProto` and virtual dispatch (`23u32`), enforces
   the `c16` protector inside the callee (UB `3`), releases it on return (`23u32`),
   and agrees with `rangedReceiverView` both in-callee and post-return.
2. `Pin<&mut Receiver> -> Pin<&mut dyn Sub> -> Pin<&mut dyn Super>` upcast via
   `stepMirFnProto` resolves the supertrait vtable and returns `41u32`.
3. `Box<dyn Trait>`, `Pin<Box<dyn Trait>>`, and `&Wrapper<dyn Trait>` unsizing
   casts fail closed (`4`), NEVER faulting false-positive `.ub` (`3`).
4. `V06` and `V08` adapters agree on `u128`/`i128`/`f16`/`f32`/`f64`/`f128` and
   `Pin<&[mut] dyn Trait>`. -/
theorem b3_pin_unsize_box_fail_closed_and_dialect_symmetry :
    scalarOf (runPinUnsize false false) = some (23, 4) ∧
    tagOf (runPinUnsize true false) = 3 ∧
    scalarOf (runPinUnsize false true) = some (23, 4) ∧
    (match advanceSteps (pinUnsizeCallerBody false)
        (stepMirFnProto C16.pokeProg (pinUnsizeCallerBody false)) 12
        (initMachineStateWithCallees (pinUnsizeCallerBody false) [] [pinPokeBody false]),
      advanceSteps (pinUnsizeCallerBody false)
        (stepMirFnProto C16.pokeProg (pinUnsizeCallerBody false)) 18
        (initMachineStateWithCallees (pinUnsizeCallerBody false) [] [pinPokeBody false]) with
     | some sIn, some sOut =>
       match rangedReceiverOwnerTag sIn.memory 3, rangedReceiverView sIn.memory 3 0 4,
             rangedReceiverOwnerTag sOut.memory 3, rangedReceiverView sOut.memory 3 0 4 with
       | some oIn, some tIn, some oOut, some tOut =>
         [ tIn.protectedTags,
           accessCode (receiverForeignAccess (receiverEnter tIn 3 0 4).tree oIn 0 4 .Write).status,
           tOut.protectedTags,
           accessCode (receiverForeignAccess (receiverEnter tOut 3 0 4).tree oOut 0 4 .Write).status ]
       | _, _, _, _ => [[9]]
     | _, _ => [[9]]) = [[3], [2, 0, 4, 3, 2], [], [0]] ∧
    scalarOf (runMirProto pinSupProg pinUpcastCallerBody 64
      (initMachineStateWithCallees pinUpcastCallerBody [] [pinSupBody])) = some (41, 4) ∧
    (let boxSrc : Ty := { kind := .adt "alloc::boxed::Box" [.adt recKey []], layoutIdx := 3 }
     let boxDst : Ty := { kind := .adt "alloc::boxed::Box" [.dynamic traitKey], layoutIdx := 5 }
     let pinBoxSrc : Ty := { kind := .adt "core::pin::Pin" [.adt "alloc::boxed::Box" [.adt recKey []]], layoutIdx := 3 }
     let pinBoxDst : Ty := { kind := .adt "core::pin::Pin" [.adt "alloc::boxed::Box" [.dynamic traitKey]], layoutIdx := 5 }
     let wrapSrc : Ty := { kind := .ref .not (.adt "Wrapper" [.adt recKey []]), layoutIdx := 3 }
     let wrapDst : Ty := { kind := .ref .not (.adt "Wrapper" [.dynamic traitKey]), layoutIdx := 5 }
     [ tagOf (runMirProto prog (unsupportedDynAdtUnsizeBody boxSrc boxDst) 32
         (initMachineStateWithCallees (unsupportedDynAdtUnsizeBody boxSrc boxDst) [] [])),
       tagOf (runMirProto prog (unsupportedDynAdtUnsizeBody pinBoxSrc pinBoxDst) 32
         (initMachineStateWithCallees (unsupportedDynAdtUnsizeBody pinBoxSrc pinBoxDst) [] [])),
       tagOf (runMirProto prog (unsupportedDynAdtUnsizeBody wrapSrc wrapDst) 32
         (initMachineStateWithCallees (unsupportedDynAdtUnsizeBody wrapSrc wrapDst) [] [])) ]) =
      [4, 4, 4] ∧
    [ V06.tyKey? (.uint .u128), V08.tyKey? (.uint .u128),
      V06.tyKey? (.int .i128), V08.tyKey? (.int .i128),
      V06.tyKey? (.float .f16), V08.tyKey? (.float .f16),
      V06.tyKey? (.float .f32), V08.tyKey? (.float .f32),
      V06.tyKey? (.float .f64), V08.tyKey? (.float .f64),
      V06.tyKey? (.float .f128), V08.tyKey? (.float .f128) ] =
      [ some "u128", some "u128", some "i128", some "i128",
        some "f16", some "f16", some "f32", some "f32",
        some "f64", some "f64", some "f128", some "f128" ] ∧
    V06.lowerVirtualReceiver (.adt "core::pin::Pin" [.ref .mut (.dynamic traitKey)]) =
      some (true, true, true) ∧
    V08.lowerVirtualReceiver (.adt "core::pin::Pin" [.ref .mut (.dynamic traitKey)]) =
      some (true, true, true) ∧
    V06.lowerPinDynTarget? (.adt "core::pin::Pin" [.ref .not (.dynamic traitKey)]) =
      some (false, traitKey) ∧
    V08.lowerPinDynTarget? (.adt "core::pin::Pin" [.ref .not (.dynamic traitKey)]) =
      some (false, traitKey) := by
  decide +kernel

end B1Hardening

/-! ## §5. Cross-root dual-authority kernel bridge (vendored `Miri.Interpreter.*`)

The `run_cmd` below loads `Anneal.Prototypes.DynTraitUnsizeProto` (root
package) together with vendored `Miri.Interpreter.{VTable, VTableMachine,
VirtualCalls, DynamicLayout, Cast}` (`examples/` package) into a fresh
environment, elaborates the hook instantiation `bridgeSource` in it (every
declaration goes through the kernel), and then:
1. checks that `miriAuthority_check : lmAuthorityCheck miriAuthority = true`
   (kernel `decide`) and `miriContract : LmDynContract miriAuthority` exist;
2. adds closed per-law projections and `Eq.refl` certificates that run the
   vendored functions, via `addDecl`;
3. confirms that the kernel rejects forged certificates on scratch copies;
4. audits axioms and non-triviality of every bridge declaration, self-tests the
   auditor, and checks that the capstone transitively reaches both MiniRust's
   `vtableFromPtr` / `computeSize` / `computeAlign` and the vendored
   `VTable.getPtrVTableTypeRead` / `getSizeAndAlignRead` / `getMethod`,
   `VirtualCalls.resolveVirtual`, `DynamicLayout.sizeAndAlignFromMeta`,
   `Cast.unsizeIntoPointer`, and `Cast.ptrToPtr`. -/

/-- Lean source of the `lean-miri` hook instantiation, elaborated in the
cross-root environment. -/
def bridgeSource : String := r##"
namespace Anneal.Prototypes.DynTraitUnsizeProtoTests.CrossRoot

open Anneal.Prototypes.DynTraitUnsizeProto
open Anneal.Prototypes.DynTraitUnsizeProto.Lm
open Miri.ABI Miri.Memory Miri.Interpreter
open Trusted.Sequence (get?)

/-- Provenance, state (the immediate written by a cast), and choice of the
hook instantiation. -/
abbrev LmP := AllocId
abbrev LmS := Option (Immediate AllocId)
abbrev LmC := Unit

/-- 64-bit little-endian target. -/
def lmTarget : TargetDataLayout := ⟨.little, .w64⟩

/-- Type identities: concrete types are `tyIdOf` (`< 1000`), the trait object
type `dynTypes[i]` is `1000 + i`, the wide raw pointer is `2000`, the thin raw
pointer `2001`, and a raw pointer to `dynTypes[i]` is `4000 + i`. Trait
identities: `dynTypes[i]` is `i`, the trait of the vtable with identifier `v`
is `3000 + v`. -/
def dynTyId (i : Nat) : Nat := 1000 + i

/-- Structural `⌊log₂ n⌋` with fuel. -/
def pow2Of : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n =>
    match Nat.ble n 1 with
    | true => 0
    | false => pow2Of fuel (n / 2) + 1

/-- Index of `k` in `ks` (the length when absent). -/
def keyIndex (k : List Nat) : List (List Nat) → Nat
  | [] => 0
  | x :: xs =>
    match natListEq x k with
    | true => 0
    | false => keyIndex k xs + 1

/-- Every non-auto predicate key of the table. -/
def allKeys (vt : ProtoVTableTable) : List (List Nat) :=
  vt.dynTypes.flatMap (fun p => p.2.nonAutoKeys) ++ vt.entries.flatMap (fun e => e.traitPred.nonAutoKeys)

/-- Trait object type with trait identity `t`. -/
def predOfTrait (vt : ProtoVTableTable) (t : Nat) : Option ProtoTraitPred :=
  match Nat.ble 3000 t with
  | true =>
    match lookupVTableById vt.entries (t - 3000) with
    | some e => some e.traitPred
    | none => none
  | false => nthPred vt t

/-- Compiler predicate list of a trait object type: one predicate per non-auto
key (stable key = id = index of the key), one auto-trait predicate per auto
trait. -/
def predicatesOf (vt : ProtoVTableTable) (p : ProtoTraitPred) : Array VTablePredicate :=
  (p.nonAutoKeys.map (fun k => (⟨keyIndex k (allKeys vt), keyIndex k (allKeys vt), false⟩ :
      VTablePredicate)) ++
    p.autoTraits.map (fun _ => (⟨100000, 100000, true⟩ : VTablePredicate))).toArray

/-- Index in `dynTypes` of the trait object type equal to `p`. -/
def dynIndexOf (vt : ProtoVTableTable) (p : ProtoTraitPred) : Nat :=
  let rec go : List (String × ProtoTraitPred) → Nat
    | [] => 0
    | (_, q) :: rest =>
      match traitPredEq q p with
      | true => 0
      | false => go rest + 1
  go vt.dynTypes

/-- Captured vtable of the concrete type `ty` for the trait object type with
trait identity `t`. -/
def vtableFor (vt : ProtoVTableTable) (ty t : Nat) : Option ProtoVTableEntry :=
  match get? (tyKeys vt) ty, predOfTrait vt t with
  | some key, some pred => findVTableFor vt.entries key pred
  | _, _ => none

/-- `VTableEntry` of a slot. -/
def slotEntry (vt : ProtoVTableTable) : ProtoVTableSlot → VTableEntry CallInstance
  | .dropInPlace _ => .dropInPlace
  | .size => .size
  | .align => .align
  | .vacant => .vacant
  | .method p => .method ⟨.Item (fnIdOf vt p), #[]⟩
  | .traitVPtr sup =>
    match lookupVTableById vt.entries sup with
    | some s => .traitVPtr (dynIndexOf vt s.traitPred)
    | none => .vacant

/-- Sized layout of `size` bytes aligned to `align` bytes. -/
def sizedLayout (size align : Nat) : LayoutData :=
  { fields := .Primitive, variants := .Single 0, backendRepr := .Memory (sized := true),
    largestNiche := none, uninhabited := false,
    align := ⟨⟨pow2Of 64 align⟩⟩, size := ⟨UInt64.ofNat size⟩, maxReprAlign := none,
    unadjustedAbiAlign := ⟨pow2Of 64 align⟩, reprC := false, randomizationSeed := 0 }

/-- Unsized layout of a trait object. -/
def dynLayoutData : LayoutData :=
  { sizedLayout 0 1 with backendRepr := .Memory (sized := false) }

/-- Layout of a `DispatchFromDyn` wrapper `((), *const dyn T, ())` with two
1-ZST fields and a single non-1-ZST wide-pointer field at index `1`. -/
def wrappedDynLayout : LayoutData :=
  { sizedLayout 16 8 with
    fields := .Arbitrary #[Size.ZERO, Size.ZERO, Size.ofBytes 16] #[0, 1, 2] }

/-- Layout of a single-field `Pin<*const T>` ADT (`fields.count = 1`, field 0
at offset 0) exercised by `Cast.unsizeInto`. -/
def pinThinLayout : LayoutData :=
  { sizedLayout 8 8 with fields := .Arbitrary #[Size.ZERO] #[0] }

/-- Layout of a single-field `Pin<*const dyn Trait>` ADT (`fields.count = 1`,
field 0 at offset 0) exercised by `Cast.unsizeInto`. -/
def pinWideLayout : LayoutData :=
  { sizedLayout 16 8 with fields := .Arbitrary #[Size.ZERO] #[0] }

private def unused {S A : Type} (what : String) : EStateM StepError S A :=
  throw (.unsupported s!"unused hook {what}")

/-- Layout of a type identity. -/
def lmLayoutOf (vt : ProtoVTableTable) (ty : Nat) : EStateM StepError LmS (TyAndLayout Nat) :=
  match Nat.blt ty 1000 with
  | true =>
    match get? (tyKeys vt) ty with
    | some key =>
      match vt.entries.find? (fun (e : ProtoVTableEntry) => strEq e.concreteTyKey key) with
      | some e => pure ⟨ty, sizedLayout e.sizeBytes e.alignBytes⟩
      | none => unused "layoutOf"
    | none => unused "layoutOf"
  | false =>
    match Nat.blt ty 2000 with
    | true => pure ⟨ty, dynLayoutData⟩
    | false =>
      match Nat.beq ty 2001 || (Nat.ble 3000 ty && Nat.blt ty 4000) with
      | true => pure ⟨ty, sizedLayout 8 8⟩
      | false =>
        match Nat.ble 6000 ty && Nat.blt ty 7000 with
        | true => pure ⟨ty, pinThinLayout⟩
        | false =>
          match Nat.ble 7000 ty && Nat.blt ty 8000 with
          | true => pure ⟨ty, pinWideLayout⟩
          | false => pure ⟨ty, sizedLayout 16 8⟩

/-- Genuine `VTableHooks` over the table: symbolic vtable allocations, the
compiler's predicate lists, layouts, and vtable entries. -/
def lmVTableHooks (vt : ProtoVTableTable) :
    VTableHooks LmP LmS LmC CallInstance (FnAbi Nat) where
  target := lmTarget
  isDynamic := fun _ ty => pure (Nat.ble 1000 ty && Nat.blt ty 2000)
  memoryOffset := fun _ _ _ _ _ => unused "memoryOffset"
  resolvePointer := fun _ ptr =>
    match ptr.provenance with
    | some id => pure (.ok (id, ptr.offset))
    | none => pure (.error .danglingInteger)
  globalVTable := fun _ id =>
    match lookupVTableByAlloc vt.entries id.value.toNat with
    | some e => pure (some (tyIdOf vt e.concreteTyKey, 3000 + e.vtableId))
    | none => pure none
  globalFunction := fun _ _ => pure none
  predicates := fun _ t =>
    match predOfTrait vt t with
    | some p => pure (predicatesOf vt p)
    | none => unused "predicates"
  normalizePredicate := fun _ p => pure p.stableKey
  layoutOf := fun _ ty => lmLayoutOf vt ty
  eraseAndAnonymize := fun _ _ _ => unused "eraseAndAnonymize"
  ensureMonomorphicType := fun _ _ => pure ()
  ensureMonomorphicDyn := fun _ _ => pure ()
  globalSalt := fun _ => pure 0
  reserveVTable := fun _ _ _ _ => unused "reserveVTable"
  globalRootPointer := fun _ _ => unused "globalRootPointer"
  entries := fun _ principal ty =>
    match principal with
    | some t =>
      match vtableFor vt ty t with
      | some e => pure (e.slots.map (slotEntry vt)).toArray
      | none => unused "entries"
    | none => unused "entries"
  assertVirtualInstanceMatches := fun _ _ _ _ _ => pure ()

/-- Pointer of a query pointer. -/
def lmPointer : LmPtr → Pointer (Option AllocId)
  | .prov a off => ⟨Size.ofBytes (UInt64.ofNat off), AllocId.ofUInt64 (UInt64.ofNat a)⟩
  | .int addr => Pointer.withoutProvenance (UInt64.ofNat addr)

/-- Query pointer of a pointer. -/
def lmPtrOfPointer (p : Pointer (Option AllocId)) : LmPtr :=
  match p.provenance with
  | some id => .prov id.value.toNat p.offset.bytes.toNat
  | none => .int p.offset.bytes.toNat

/-- Query pointer of a pointer-sized scalar. -/
def lmPtrOfScalar (s : Scalar AllocId) : Option LmPtr :=
  match s.toPointer lmTarget with
  | .ok p => some (lmPtrOfPointer p)
  | .error _ => none

/-- Scalar of a query pointer. -/
def lmScalar (p : LmPtr) : Option (Scalar AllocId) :=
  match Scalar.fromMaybePointer lmTarget (lmPointer p) with
  | .ok s => some s
  | .error _ => none

/-- Error class of a step error. -/
def lmErrOf : StepError → LmErr
  | .undefinedBehavior r =>
    match strEq r "InvalidVTablePointer" with
    | true => .invalidVTablePointer
    | false =>
      match strEq r "InvalidVTableTrait" with
      | true => .invalidVTableTrait
      | false =>
        match strEq r "dyn call trying to call something that is not a method" with
        | true => .notAMethod
        | false =>
          match strEq r "InvalidUninitBytes" with
          | true => .uninitBytes
          | false => .otherUb
  | .unsupported _ => .unsupported
  | _ => .other

/-- Run a hook computation from the empty state. -/
def lmRunM {α : Type} (m : EStateM StepError LmS α) (k : α → LmS → LmObs) : LmObs :=
  match m.run none with
  | .ok a s => k a s
  | .error e _ => .err (lmErrOf e)

/-- Observation of the immediate a cast wrote. -/
def lmWrittenObs : LmS → LmObs
  | some (.scalarPair a b) =>
    match lmPtrOfScalar a, lmPtrOfScalar b with
    | some pa, some pb => .wide pa pb
    | _, _ => .err .other
  | _ => .err .other

/-- Slot of the supertrait vtable pointer of `dyn src` that targets `dyn dst`
(`supertrait_vtable_slot`, from the captured vtables of `dyn src`). -/
def supertraitSlotOf (vt : ProtoVTableTable) (src dst : Nat) : Option Nat :=
  match predOfTrait vt src, predOfTrait vt dst with
  | some sp, some dp =>
    let rec scan (i : Nat) : List ProtoVTableSlot → Option Nat
      | [] => none
      | .traitVPtr sup :: rest =>
        match lookupVTableById vt.entries sup with
        | some s =>
          match traitPredEq s.traitPred dp with
          | true => some i
          | false => scan (i + 1) rest
        | none => scan (i + 1) rest
      | _ :: rest => scan (i + 1) rest
    match vt.entries.find? (fun e => traitPredEq e.traitPred sp) with
    | some e => scan 0 e.slots
    | none => none
  | _, _ => none

/-- Genuine `CastHooks`: the type, layout, field-projection, vtable, and
immediate leaves that `Cast.unsizeInto`, `Cast.unsizeIntoPointer`, and
`Cast.ptrToPtr` consult. -/
def lmCastHooks (vt : ProtoVTableTable) : CastHooks LmP LmS LmC Unit where
  target := lmTarget
  typeInfo := fun _ ty =>
    match Nat.blt ty 1000 with
    | true => pure (.adt ty)
    | false =>
      match Nat.blt ty 2000 with
      | true => pure (.dynamic (ty - 1000))
      | false =>
        match Nat.blt ty 3000 with
        | true => pure (.rawPointer 0)
        | false =>
          match Nat.blt ty 4000 with
          | true => pure (.rawPointer (ty - 3000))
          | false =>
            match Nat.blt ty 5000 with
            | true => pure (.rawPointer (dynTyId (ty - 4000)))
            | false =>
              match Nat.ble 6000 ty && Nat.blt ty 8000 with
              | true => pure (.adt 99)
              | false => pure (.rawPointer 0)
  layoutOf := fun _ ty => lmLayoutOf vt ty
  destLayout := fun _ => ⟨2001, sizedLayout 8 8⟩
  readImmediate := fun _ op =>
    match op.op with
    | .immediate imm => pure ⟨imm, op.layout⟩
    | .indirect _ => unused "readImmediate"
  writeImmediate := fun _ imm _ => set (some imm)
  writePointer := fun _ _ _ => unused "writePointer"
  enforceValidity := fun _ _ => pure false
  enforceValidityRecursively := fun _ _ => pure false
  validatePlace := fun _ _ _ _ => pure ()
  derefPointer := fun _ _ => pure ()
  checkFunctionPointer := fun _ _ => pure ()
  exposeProvenance := fun _ _ => pure ()
  pointerFromExposedAddress := fun _ _ => unused "pointerFromExposedAddress"
  usizeLayout := fun _ => unused "usizeLayout"
  floatOps :=
    { integerKindOf := fun _ _ => unused "integerKindOf"
      formatOf := fun _ _ => unused "formatOf"
      boolLayout := fun _ => unused "boolLayout"
      floatNondeterministic := false
      chooseNaN := fun _ _ => pure 0 }
  ensureMonomorphic := fun _ _ => pure ()
  requireNoBoundVars := fun _ _ => pure ()
  resolveFunction := fun _ _ _ => pure none
  resolveClosureFnOnce := fun _ _ _ => unused "resolveClosureFnOnce"
  functionPointer := fun _ _ => unused "functionPointer"
  builtinDeref := fun _ _ _ => pure none
  boxLayout := fun _ _ => unused "boxLayout"
  validateImmediateABI := fun _ _ => .ok ()
  copyAllowTransmute := fun _ _ _ => unused "copyAllowTransmute"
  copyNoValidate := fun _ src _ _ =>
    match src.op with
    | .immediate imm => set (some imm)
    | .indirect _ => unused "copyNoValidate"
  projectRead := fun _ src idx =>
    match Nat.beq idx 0 with
    | false => unused "projectRead"
    | true =>
      match Nat.ble 6000 src.layout.ty && Nat.blt src.layout.ty 7000 with
      | true => pure ⟨src.op, ⟨3000 + (src.layout.ty - 6000), sizedLayout 8 8⟩⟩
      | false =>
        match Nat.ble 7000 src.layout.ty && Nat.blt src.layout.ty 8000 with
        | true => pure ⟨src.op, ⟨4000 + (src.layout.ty - 7000), sizedLayout 16 8⟩⟩
        | false => unused "projectRead"
  projectWrite := fun _ _ idx =>
    match Nat.beq idx 0 with
    | true => pure ()
    | false => unused "projectWrite"
  fieldLayout := fun _ target idx =>
    match Nat.beq idx 0 with
    | false => unused "fieldLayout"
    | true =>
      match Nat.ble 7000 target.ty && Nat.blt target.ty 8000 with
      | true => pure ⟨4000 + (target.ty - 7000), sizedLayout 16 8⟩
      | false => unused "fieldLayout"
  lockstepTails := fun _ a b => pure (a, b)
  vtableType := fun c ptr expected =>
    VTable.getPtrVTableTypeRead (lmVTableHooks vt).readHooks c ptr expected
  vtablePointer := fun _ ty t =>
    match vtableFor vt ty t with
    | some e => pure (lmPointer (.prov e.vtableAllocId 0))
    | none => throw (.unsupported "vtable not captured")
  principal := fun _ t => pure (some t)
  vtableEntries := fun _ principal ty =>
    match principal with
    | some t =>
      match vtableFor vt ty t with
      | some e => pure (e.slots.map (slotEntry vt)).toArray
      | none => unused "vtableEntries"
    | none => unused "vtableEntries"
  supertraitSlot := fun _ src dst => pure (supertraitSlotOf vt (src - 1000) (dst - 1000))
  eraseSelfTraitRef := fun _ r => pure r
  normalizePrincipal := fun _ t => pure (some t)

/-- Genuine `DynamicLayoutHooks`: a trait object classifies as `.dynamic`, and
its size and alignment come from `VTable.getSizeAndAlignRead`. -/
def lmDynLayoutHooks (vt : ProtoVTableTable) : DynamicLayoutHooks LmP LmS LmC where
  target := lmTarget
  maxSizeOfVal := ⟨9223372036854775807⟩
  classify := fun _ ty =>
    match Nat.ble 1000 ty && Nat.blt ty 2000 with
    | true => pure (.dynamic (ty - 1000))
    | false => unused "classify"
  field := fun _ _ _ => unused "field"
  packedAlign := fun _ _ => pure none
  vtableSizeAndAlign := fun c ptr expected =>
    VTable.getSizeAndAlignRead (lmVTableHooks vt).readHooks c ptr expected

/-- Trait and slot of a virtual method definition (`100 * trait + slot`). -/
def lmDefOf (t slot : Nat) : Nat := 100 * t + slot

/-- Genuine `VirtualCalls.CompilerHooks`: receiver classification (direct raw
pointers `4000 + t` and `DispatchFromDyn` wrappers `5000 + t`), dyn tail data,
and the compiler's resolution of the concrete instance. -/
def lmCompilerHooks (vt : ProtoVTableTable) : VirtualCalls.CompilerHooks LmS LmC where
  classifyReceiver := fun ty =>
    match Nat.ble 4000 ty && Nat.blt ty 5000 with
    | true => pure .rawPointer
    | false => pure .other
  fieldLayout := fun layout idx =>
    match Nat.ble 5000 layout.ty with
    | true =>
      match idx with
      | 1 => pure ⟨4000 + (layout.ty - 5000), sizedLayout 16 8⟩
      | _ => pure ⟨2002, sizedLayout 0 1⟩
    | false => unused "fieldLayout"
  structTailForCodegen := fun ty => pure ty
  dynamicData := fun ty =>
    match Nat.ble 1000 ty && Nat.blt ty 2000 with
    | true => pure (some { predicates := ty - 1000, principal := some (ty - 1000) })
    | false => pure none
  mutPointerType := fun _ => pure 2001
  mutReferenceType := fun _ => unused "mutReferenceType"
  builtinDeref := fun ty =>
    match Nat.ble 4000 ty && Nat.blt ty 5000 with
    | true => pure (some (dynTyId (ty - 4000)))
    | false => pure none
  layoutOf := fun ty =>
    match Nat.ble 5000 ty with
    | true => pure ⟨ty, wrappedDynLayout⟩
    | false =>
      match Nat.ble 4000 ty with
      | true => pure ⟨ty, sizedLayout 16 8⟩
      | false => lmLayoutOf vt ty
  parentTrait := fun d => pure d
  rebaseVirtualArgs := fun _ _ ty => pure #[.Type ty]
  expectResolveForVTable := fun _ d args =>
    match args[0]? with
    | some (Miri.MIR.GenericArg.Type ty) =>
      match vtableFor vt ty (d / 100) with
      | some e =>
        match get? e.slots (d % 100) with
        | some (.method p) => pure ⟨.Item (fnIdOf vt p), #[]⟩
        | _ => throw (.invalidProgram "no concrete instance")
      | none => throw (.invalidProgram "no vtable")
    | _ => throw (.invalidProgram "no type argument")
  resolveDropGlue := fun _ => unused "resolveDropGlue"
  requiresCallerLocation := fun _ => pure false
  sourceScope := fun _ _ _ _ => unused "sourceScope"
  unitLayout := unused "unitLayout"

/-- Genuine `VirtualCalls.Hooks`: receiver unwrapping through
`VirtualCalls.pointerPlace` and `VirtualCalls.nonOneZstField` + `projectField`
for `DispatchFromDyn` wrappers (no dereference, no misalignment check). -/
def lmVirtualHooks (vt : ProtoVTableTable) : VirtualCalls.Hooks LmP LmS LmC Unit where
  debugAssertions := false
  compiler := lmCompilerHooks vt
  target := lmTarget
  vtable := lmVTableHooks vt
  getFrame := unused "getFrame"
  readImmediate := fun _ op =>
    match op.op with
    | .immediate imm => pure ⟨imm, op.layout⟩
    | .indirect _ => unused "readImmediate"
  immPtrToMPlace := fun _ v =>
    VirtualCalls.pointerPlace (lmCompilerHooks vt) lmTarget (fun _ _ => pure none) v
  projectField := fun _ receiver idx =>
    match Nat.ble 5000 receiver.layout.ty && Nat.beq idx 1 with
    | true => pure ⟨receiver.op, ⟨4000 + (receiver.layout.ty - 5000), sizedLayout 16 8⟩⟩
    | false => unused "projectField"

/-- Caller ABI of a one-argument virtual call. -/
def lmCallerAbi (t : Nat) : FnAbi Nat :=
  { args := #[⟨⟨4000 + t, sizedLayout 16 8⟩, .Ignore⟩]
    ret := ⟨⟨2001, sizedLayout 0 1⟩, .Ignore⟩
    cVariadic := false, fixedCount := 1, conv := .Rust, canUnwind := false }

/-- Caller ABI of a one-argument virtual call with a `DispatchFromDyn` wrapper receiver. -/
def lmCallerAbiWrapped (t : Nat) : FnAbi Nat :=
  { args := #[⟨⟨5000 + t, wrappedDynLayout⟩, .Ignore⟩]
    ret := ⟨⟨2001, sizedLayout 0 1⟩, .Ignore⟩
    cVariadic := false, fixedCount := 1, conv := .Rust, canUnwind := false }

/-- Observation of a resolved virtual call. -/
def lmMethodObs (inst : CallInstance) (recv : LmPtr) : LmObs :=
  match inst.kind with
  | .Item f => .method f recv
  | _ => .err .other

/-- **The vendored `lean-miri` interpreter as an authority.** Each query runs
the genuine vendored function on the hook instantiation above. -/
def miriRun (vt : ProtoVTableTable) : LmQuery → LmObs
  | .vtableType vtp expected? =>
    lmRunM (VTable.getPtrVTableTypeRead (lmVTableHooks vt).readHooks () (lmPointer vtp) expected?)
      (fun ty _ => .tyOk ty)
  | .sizeAlign vtp t =>
    lmRunM (VTable.getSizeAndAlignRead (lmVTableHooks vt).readHooks () (lmPointer vtp) (some t))
      (fun sa _ => .sizeAlign sa.1.bytes.toNat (2 ^ sa.2.pow2))
  | .dynLayout vtp t =>
    match lmScalar vtp with
    | none => .err .other
    | some s =>
      lmRunM
        (DynamicLayout.sizeAndAlignFromMeta (lmDynLayoutHooks vt) () 4 (.metadata s)
          ⟨dynTyId t, dynLayoutData⟩)
        (fun r _ =>
          match r with
          | some sa => .sizeAlign sa.1.bytes.toNat (2 ^ sa.2.pow2)
          | none => .err .other)
  | .unsize tyIdx traitIdx data =>
    match lmScalar data with
    | none => .err .other
    | some s =>
      lmRunM
        (Cast.unsizeIntoPointer (lmCastHooks vt) () ⟨.immediate (.scalar s), ⟨2001, sizedLayout 8 8⟩⟩
          () tyIdx (dynTyId traitIdx))
        (fun _ st => lmWrittenObs st)
  | .unsizePin tyIdx traitIdx data =>
    match lmScalar data with
    | none => .err .other
    | some s =>
      lmRunM
        (Cast.unsizeInto (lmCastHooks vt) () 4
          ⟨.immediate (.scalar s), ⟨6000 + tyIdx, pinThinLayout⟩⟩
          ⟨7000 + traitIdx, pinWideLayout⟩ ())
        (fun _ st => lmWrittenObs st)
  | .upcast srcTrait dstTrait data vtp =>
    match lmScalar data, lmScalar vtp with
    | some sd, some sv =>
      lmRunM
        (Cast.unsizeIntoPointer (lmCastHooks vt) ()
          ⟨.immediate (.scalarPair sd sv), ⟨4000 + srcTrait, sizedLayout 16 8⟩⟩ ()
          (dynTyId srcTrait) (dynTyId dstTrait))
        (fun _ st => lmWrittenObs st)
    | _, _ => .err .other
  | .upcastPin srcTrait dstTrait data vtp =>
    match lmScalar data, lmScalar vtp with
    | some sd, some sv =>
      lmRunM
        (Cast.unsizeInto (lmCastHooks vt) () 4
          ⟨.immediate (.scalarPair sd sv), ⟨7000 + srcTrait, pinWideLayout⟩⟩
          ⟨7000 + dstTrait, pinWideLayout⟩ ())
        (fun _ st => lmWrittenObs st)
    | _, _ => .err .other
  | .ptrToPtr data ptrMeta =>
    match lmScalar data, lmScalar ptrMeta with
    | some sd, some sm =>
      lmRunM
        (Cast.ptrToPtr (lmCastHooks vt) () ⟨.scalarPair sd sm, ⟨2000, sizedLayout 16 8⟩⟩
          ⟨2001, sizedLayout 8 8⟩)
        (fun r _ =>
          match r.imm with
          | .scalar s =>
            match lmPtrOfScalar s with
            | some p => .thin p
            | none => .err .other
          | _ => .err .other)
    | _, _ => .err .other
  | .ptrToPtrUninit =>
    lmRunM
      (Cast.ptrToPtr (lmCastHooks vt) () ⟨.uninit, ⟨2000, sizedLayout 16 8⟩⟩
        ⟨2001, sizedLayout 8 8⟩)
      (fun _ _ => .err .other)
  | .virtualCall t slot data vtp =>
    match lmScalar data, lmScalar vtp with
    | some sd, some sv =>
      lmRunM
        (VirtualCalls.resolveVirtual (lmVirtualHooks vt) () 4 ⟨.Virtual (lmDefOf t slot) slot, #[]⟩
          (lmDefOf t slot) slot (lmCallerAbi t)
          #[.Copy ⟨.immediate (.scalarPair sd sv), ⟨4000 + t, sizedLayout 16 8⟩⟩])
        (fun r _ =>
          match r.2.2[0]? with
          | some (FnArg.Copy op) =>
            match op.op with
            | .immediate (.scalar s) =>
              match lmPtrOfScalar s with
              | some p => lmMethodObs r.1 p
              | none => .err .other
            | _ => .err .other
          | _ => .err .other)
    | _, _ => .err .other
  | .virtualCallWrapped t slot data vtp =>
    match lmScalar data, lmScalar vtp with
    | some sd, some sv =>
      lmRunM
        (VirtualCalls.resolveVirtual (lmVirtualHooks vt) () 4 ⟨.Virtual (lmDefOf t slot) slot, #[]⟩
          (lmDefOf t slot) slot (lmCallerAbiWrapped t)
          #[.Copy ⟨.immediate (.scalarPair sd sv), ⟨5000 + t, wrappedDynLayout⟩⟩])
        (fun r _ =>
          match r.2.2[0]? with
          | some (FnArg.Copy op) =>
            match op.op with
            | .immediate (.scalar s) =>
              match lmPtrOfScalar s with
              | some p => lmMethodObs r.1 p
              | none => .err .other
            | _ => .err .other
          | _ => .err .other)
    | _, _ => .err .other
  | .getMethod t slot vtp =>
    lmRunM
      (VTable.getMethod (lmVTableHooks vt) (fun _ _ _ => pure ()) () (lmPointer vtp) t (some t)
        slot (lmDefOf t slot) ⟨.Virtual (lmDefOf t slot) slot, #[]⟩ (lmCallerAbi t))
      (fun inst _ => lmMethodObs inst (.int 0))

/-- The vendored interpreter as an `LmDynAuthority`. -/
def miriAuthority : LmDynAuthority := ⟨miriRun⟩

/-- **Kernel-checked certificate**: the vendored interpreter agrees with the
prototype on every test vector. -/
theorem miriAuthority_check : lmAuthorityCheck miriAuthority = true := by decide +kernel

/-- **The `lean-miri` correspondence contract over the vendored interpreter.** -/
theorem miriContract : LmDynContract miriAuthority :=
  lmDynContractOfCheck miriAuthority miriAuthority_check

/-- Real-state `VTableMachine` harness exercising `VTableMachine.reserve`,
`VTableMachine.globalVTable`, `VTableMachine.hooks`,
`VTableMachine.Registry.mergePersistent`, and
`VTableMachine.Registry.ensureDisjointFromFunctions`. -/
abbrev VtmUser := FunctionPointers.Registry Unit × VTableMachine.Registry
abbrev VtmState := MachineHooks.State Unit VtmUser

def vtmSeedRegistry : VTableMachine.Registry :=
  ⟨#[⟨0, 0, ⟨0, by decide⟩, ⟨40000, by decide⟩⟩,
     ⟨1, 0, ⟨0, by decide⟩, ⟨40001, by decide⟩⟩,
     ⟨0, 1, ⟨0, by decide⟩, ⟨40002, by decide⟩⟩]⟩

def vtmInitState : VtmState :=
  { stack := Stack.empty
    machine :=
      { memory := { MemoryState.empty with sourceAllocIdWorldActive := true }
        borrowTracker := none
        dataRace := none
        threads := Miri.Concurrency.ThreadManager.initial true
        raceAllocations := #[]
        allocationSpans := #[]
        user := (FunctionPointers.Registry.empty, vtmSeedRegistry) } }

def vtmFnHooks : FunctionPointers.Hooks Unit VtmUser Unit :=
  { registry := Prod.fst
    putRegistry := fun u r => (r, u.2)
    crossCrateInlineAlways := false
    inlineNever := fun _ => pure false
    chooseSalt := pure ⟨0, by decide⟩
    ptrGetAlloc := fun _ => pure none
    adjustRootPointer := fun id tag =>
      pure ⟨Size.ZERO, Provenance.concrete id tag⟩
    importedFunction := fun _ => pure none }

def vtmHooks : VTableMachine.Hooks Unit VtmUser Unit :=
  { functions := vtmFnHooks
    registry := Prod.snd
    putRegistry := fun u r => (u.1, r)
    target := { RuntimeTargetDataLayout.default with base := lmTarget }
    importedVTable := fun _ => pure none }

def vtmBaseVTableHooks :
    VTableHooks Provenance VtmState Unit CallInstance (FnAbi Nat) :=
  { target := lmTarget
    isDynamic := fun _ _ => pure false
    memoryOffset := fun _ _ _ _ _ => unused "memoryOffset"
    resolvePointer := fun _ _ => unused "resolvePointer"
    globalVTable := fun _ _ => pure none
    globalFunction := fun _ _ => pure none
    predicates := fun _ _ => pure #[]
    normalizePredicate := fun _ p => pure p.stableKey
    layoutOf := fun _ ty => pure ⟨ty, sizedLayout 4 4⟩
    eraseAndAnonymize := fun _ ty d => pure (ty, d)
    ensureMonomorphicType := fun _ _ => pure ()
    ensureMonomorphicDyn := fun _ _ => pure ()
    globalSalt := fun _ => pure 0
    reserveVTable := fun _ _ _ _ => unused "reserveVTable"
    globalRootPointer := fun _ _ => unused "globalRootPointer"
    entries := fun _ _ _ => pure #[]
    assertVirtualInstanceMatches := fun _ _ _ _ _ => pure () }

def vtmInstalledHooks :
    VTableHooks Provenance VtmState Unit CallInstance (FnAbi Nat) :=
  VTableMachine.hooks vtmHooks vtmBaseVTableHooks

/-- Pure, choice-free `VTableMachine.Registry` check (zero `MemoryState` /
`Std.HashMap` dependence): `mergePersistent` merges consistent registries and
rejects conflicting `AllocId`s for the same key or one `AllocId` reused on two
keys, and `ensureDisjointFromFunctions` accepts disjoint registries and rejects
an `AllocId` shared with `FunctionPointers.Registry`. -/
def vtmRegistryCheck : Bool :=
  let id0 : AllocId := ⟨40000, by decide⟩
  let id1 : AllocId := ⟨40001, by decide⟩
  let reg := vtmSeedRegistry
  let mergeSelfOk :=
    match VTableMachine.Registry.mergePersistent reg reg with
    | .ok r => r.entries.size == 3
    | .error _ => false
  let conflictKey : VTableMachine.Registry := ⟨#[⟨0, 0, ⟨0, by decide⟩, id1⟩]⟩
  let mergeConflictKeyRej :=
    match VTableMachine.Registry.mergePersistent reg conflictKey with
    | .ok _ => false
    | .error _ => true
  let conflictAlloc : VTableMachine.Registry := ⟨#[⟨9, 9, ⟨0, by decide⟩, id0⟩]⟩
  let mergeConflictAllocRej :=
    match VTableMachine.Registry.mergePersistent reg conflictAlloc with
    | .ok _ => false
    | .error _ => true
  let fnDisjointOk :=
    match VTableMachine.Registry.ensureDisjointFromFunctions reg
        (FunctionPointers.Registry.empty : FunctionPointers.Registry Unit) with
    | .ok () => true
    | .error _ => false
  let fnColliding : FunctionPointers.Registry Unit :=
    ⟨#[⟨⟨.Item 0, #[]⟩, ⟨0, by decide⟩, id0⟩], #[]⟩
  let fnCollideRej :=
    match VTableMachine.Registry.ensureDisjointFromFunctions reg fnColliding with
    | .ok () => false
    | .error _ => true
  mergeSelfOk && mergeConflictKeyRej && mergeConflictAllocRej && fnDisjointOk && fnCollideRej

theorem vtmRegistryCheck_ok : vtmRegistryCheck = true := by decide +kernel

/-- Exercises stateful `Miri.Interpreter.VTableMachine` (`reserve`,
`globalVTable`, `hooks`) over `MemoryState.empty` inside the Lean kernel
(`decide +kernel`):
1. `VTableMachine.reserve` deduplicates captured `(ty, dynType, salt)` keys and
   returns the exact prepared `AllocId` (`40000`, `40001`, `40002`);
2. uncaptured salt (`salt = 1`) or uncaptured `(ty, dynType)` fails closed with
   `.unsupported` under `sourceAllocIdWorldActive = true`;
3. `VTableMachine.hooks` routes `reserveVTable` / `globalVTable` and rejects
   out-of-range salt (`32`);
4. `VTableMachine.globalVTable` recovers `(ty, dynType)` for each reserved id. -/
def vtmMachineCheck : Bool :=
  let prog : MachineHooks.M Unit VtmUser Bool := do
    let id0 ← VTableMachine.reserve vtmHooks 0 0 ⟨0, by decide⟩
    let id1 ← VTableMachine.reserve vtmHooks 1 0 ⟨0, by decide⟩
    let id2 ← VTableMachine.reserve vtmHooks 0 1 ⟨0, by decide⟩
    let id0ViaHooks ← vtmInstalledHooks.reserveVTable () 0 0 0
    let uncapturedSaltRejected ←
      try
        let _ ← VTableMachine.reserve vtmHooks 0 0 ⟨1, by decide⟩
        pure false
      catch e =>
        match e with
        | .unsupported _ => pure true
        | _ => pure false
    let uncapturedKeyRejected ←
      try
        let _ ← VTableMachine.reserve vtmHooks 1 1 ⟨0, by decide⟩
        pure false
      catch e =>
        match e with
        | .unsupported _ => pure true
        | _ => pure false
    let badSaltRejected ←
      try
        let _ ← vtmInstalledHooks.reserveVTable () 0 0 32
        pure false
      catch _ => pure true
    let g0 ← VTableMachine.globalVTable vtmHooks id0
    let g1 ← vtmInstalledHooks.globalVTable () id1
    let g2 ← VTableMachine.globalVTable vtmHooks id2
    pure (id0.value == 40000 && id1.value == 40001 && id2.value == 40002 &&
      id0 == id0ViaHooks && id0 != id1 && id0 != id2 && id1 != id2 &&
      uncapturedSaltRejected && uncapturedKeyRejected && badSaltRejected &&
      g0 == some (0, 0) && g1 == some (1, 0) && g2 == some (0, 1))
  match prog.run vtmInitState with
  | .ok ok _ => ok
  | .error _ _ => false

theorem vtmMachineCheck_ok : vtmMachineCheck = true := by decide +kernel

/-- Forged authority: virtual calls resolve the next slot. -/
def forgedNextSlot : LmDynAuthority :=
  ⟨fun vt q =>
    match q with
    | .virtualCall t s d v => miriRun vt (.virtualCall t (s + 1) d v)
    | q => miriRun vt q⟩

/-- Forged authority: the vtable trait check is skipped. -/
def forgedNoTraitCheck : LmDynAuthority :=
  ⟨fun vt q =>
    match q with
    | .vtableType v (some _) => miriRun vt (.vtableType v none)
    | q => miriRun vt q⟩

/-- Forged authority: the fat-to-thin cast keeps the metadata word. -/
def forgedKeepsMetadata : LmDynAuthority :=
  ⟨fun vt q =>
    match q with
    | .ptrToPtr d m => .wide d m
    | q => miriRun vt q⟩

/-- MiniRust `checkPtrMetadataM` / `checkPtrM` / `evalUnOpM` correspondence on
the corpus table (`Mach`), reaching the universal §8 theorems. -/
theorem corpus_minirust_checkPtr_evalUnOp
    (m : MiniRustSpec.Interp.Mach)
    (dataPtr fnThin : MiniRustSpec.Interp.Ptr)
    (hDataB : MiniRustSpec.Interp.inBounds dataPtr.addr .Unsigned MiniRustSpec.Interp.x86_64.PTR_SIZE = true)
    (hFn : MiniRustSpec.Interp.mapGet m.fn_ptrs ⟨⟨fnIdOf corpusTable "other::eval"⟩⟩ = some fnThin) :
    let e : ProtoVTableEntry :=
      { vtableId := 1, vtableAllocId := 40001, concreteTyKey := "AltReceiver",
        traitPred := predA, sizeBytes := 8, alignBytes := 4,
        slots := [.dropInPlace none, .size, .align, .method "other::eval", .method "other::tag"] }
    let L := MR.bmLayout corpusTraitOf (fnIdOf corpusTable)
    MiniRustSpec.Interp.checkPtrM
        { thin_pointer := dataPtr, metadata := some (.VTablePointer (MR.vtPtr L e)) }
        (.Raw (.VTablePointer (MR.traitName L e.traitPred)))
        (some (MR.installVTables L corpusTable m)) = .ok () ∧
    MiniRustSpec.Interp.evalUnOpM (.VTableMethodLookup ⟨⟨3⟩⟩)
        (.Ptr (MiniRustSpec.Interp.ThinPointer.widen (MR.vtPtr L e) none),
         .Ptr (.VTablePtr (MR.traitName L e.traitPred)))
        (some (MR.installVTables L corpusTable m)) =
      .ok (.Ptr (MiniRustSpec.Interp.ThinPointer.widen fnThin none), .Ptr .FnPtr) := by
  intro e L
  have hLook : lookupVTableByAlloc corpusTable.entries e.vtableAllocId = some e := rfl
  have hVtB : MiniRustSpec.Interp.inBounds (MR.vtPtr L e).addr .Unsigned
      MiniRustSpec.Interp.x86_64.PTR_SIZE = true := by decide +kernel
  refine ⟨MR.checkPtrM_raw_dyn_unchecked L corpusTable m 8 e dataPtr
      (MR.bmLayout_provOf_inj _ _) corpusTable_wf hLook hDataB hVtB,
    (MR.evalUnOpM_dyn_correspondence L corpusTable m 8 3 e "other::eval" dataPtr fnThin
      (.Raw (.VTablePointer (MR.traitName L e.traitPred)))
      (MR.bmLayout_provOf_inj _ _) corpusTable_wf hLook hVtB rfl rfl hFn).2.2.2⟩

/-- **Dual-authority capstone.** The vendored `lean-miri` interpreter satisfies
`LmDynContract` (including multi-predicate assoc-type sorting/dedup and
`DispatchFromDyn` wrapper receivers) and `VTableMachine` reservation/merge/
disjointness checks, and MiniRust's `vtable_from_ptr` / `compute_size` /
`compute_align` / `check_ptr` / `eval_un_op` agree with the prototype on the
same corpus table (`Mach` and `MachTB`). -/
theorem dyn_dual_authority_capstone :
    LmDynContract miriAuthority ∧
    vtmRegistryCheck = true ∧
    vtmMachineCheck = true ∧
    (∀ (m : MiniRustSpec.Interp.Mach) (mTB : MiniRustSpec.Interp.MachTB) (d : ProtoDataWord),
      type_of% (corpus_minirust_instance m mTB d)) ∧
    (∀ (m : MiniRustSpec.Interp.Mach) (dataPtr fnThin : MiniRustSpec.Interp.Ptr)
      (hDataB : MiniRustSpec.Interp.inBounds dataPtr.addr .Unsigned MiniRustSpec.Interp.x86_64.PTR_SIZE = true)
      (hFn : MiniRustSpec.Interp.mapGet m.fn_ptrs ⟨⟨fnIdOf corpusTable "other::eval"⟩⟩ = some fnThin),
      type_of% (corpus_minirust_checkPtr_evalUnOp m dataPtr fnThin hDataB hFn)) :=
  ⟨miriContract, vtmRegistryCheck_ok, vtmMachineCheck_ok, corpus_minirust_instance,
   corpus_minirust_checkPtr_evalUnOp⟩

end Anneal.Prototypes.DynTraitUnsizeProtoTests.CrossRoot
"##

open Lean Elab Command Meta in
run_cmd do
  let opts := (← getOptions).setBool `Elab.async false
  -- The vendored interpreter lives in the `examples/` Lake package; build it on demand.
  let vendored := ["VTable", "VTableMachine", "VirtualCalls", "DynamicLayout", "Cast"]
  let mut missing : Bool := false
  for m in vendored do
    unless ← System.FilePath.pathExists s!"examples/.lake/build/lib/lean/Miri/Interpreter/{m}.olean" do
      missing := true
  if missing then
    let out ← IO.Process.output
      { cmd := "lake",
        args := #["--dir", "examples", "build", "Miri.Interpreter.VTable",
                  "Miri.Interpreter.VirtualCalls", "Miri.Interpreter.DynamicLayout",
                  "Miri.Interpreter.Cast", "Miri.Interpreter.VTableMachine"] }
    unless out.exitCode == 0 do
      throwError "cross-root: building vendored Miri.Interpreter failed:\n{out.stdout}\n{out.stderr}"
  let sp : SearchPath := [System.FilePath.mk ".lake/build/lib/lean",
                          System.FilePath.mk "examples/.lake/build/lib/lean"]
  initSearchPath (← findSysroot) sp
  -- Elaborating source in the imported environment needs its extensions
  -- (parser tables, namespaces, instances), hence `loadExts := true`.
  enableInitializersExecution
  let baseEnv ← importModules
    #[{ module := `Anneal.Prototypes.DynTraitUnsizeProto },
      { module := `Miri.Interpreter.VTable },
      { module := `Miri.Interpreter.VTableMachine },
      { module := `Miri.Interpreter.VirtualCalls },
      { module := `Miri.Interpreter.DynamicLayout },
      { module := `Miri.Interpreter.Cast }]
    {} 0 (loadExts := true)
  -- Elaborate the hook instantiation in the cross-root environment.
  let inputCtx := Parser.mkInputContext bridgeSource "<dyn-trait-cross-root>"
  let fstate ← IO.processCommands inputCtx {} (Command.mkState baseEnv {} opts)
  let msgs := fstate.commandState.messages
  if msgs.hasErrors then
    let mut errs : Array String := #[]
    for msg in msgs.toList do
      if msg.severity == .error then
        errs := errs.push (← msg.toString)
    throwError "cross-root: bridge source failed to elaborate:\n{errs}"
  let bridgeEnv := fstate.commandState.env
  let ns := `Anneal.Prototypes.DynTraitUnsizeProtoTests.CrossRoot
  let lmNs := `Anneal.Prototypes.DynTraitUnsizeProto.Lm
  let act : CoreM (Nat × Nat × Array Lean.Name) := do
    let addThm (name : Lean.Name) (ty pf : Expr) : CoreM Unit := do
      addDecl <| .thmDecl { name, levelParams := [], type := ty, value := pf }
    let boolTy := mkConst ``Bool
    let natTy := mkConst ``Nat
    let obsTy := mkConst (lmNs ++ `LmObs)
    let tableC := mkConst (lmNs ++ `corpusTable)
    let miriRunC := mkConst (ns ++ `miriRun)
    let protoRunC := mkConst (lmNs ++ `protoLmRun)
    let nat (n : Nat) : Expr := mkNatLit n
    let prov (a o : Nat) : Expr := mkApp2 (mkConst (lmNs ++ `LmPtr.prov)) (nat a) (nat o)
    let intP (a : Nat) : Expr := mkApp (mkConst (lmNs ++ `LmPtr.int)) (nat a)
    let qVirtual (t s : Nat) (d v : Expr) : Expr :=
      mkApp4 (mkConst (lmNs ++ `LmQuery.virtualCall)) (nat t) (nat s) d v
    let qVirtualWrapped (t s : Nat) (d v : Expr) : Expr :=
      mkApp4 (mkConst (lmNs ++ `LmQuery.virtualCallWrapped)) (nat t) (nat s) d v
    let qVtableType (v : Expr) (t : Nat) : Expr :=
      mkApp2 (mkConst (lmNs ++ `LmQuery.vtableType)) v
        (mkApp2 (mkConst ``Option.some [0]) natTy (nat t))
    let qSizeAlign (v : Expr) (t : Nat) : Expr :=
      mkApp2 (mkConst (lmNs ++ `LmQuery.sizeAlign)) v (nat t)
    let qUnsize (ty t : Nat) (d : Expr) : Expr :=
      mkApp3 (mkConst (lmNs ++ `LmQuery.unsize)) (nat ty) (nat t) d
    let qUnsizePin (ty t : Nat) (d : Expr) : Expr :=
      mkApp3 (mkConst (lmNs ++ `LmQuery.unsizePin)) (nat ty) (nat t) d
    let qUpcast (s t : Nat) (d v : Expr) : Expr :=
      mkApp4 (mkConst (lmNs ++ `LmQuery.upcast)) (nat s) (nat t) d v
    let qUpcastPin (s t : Nat) (d v : Expr) : Expr :=
      mkApp4 (mkConst (lmNs ++ `LmQuery.upcastPin)) (nat s) (nat t) d v
    let qPtrToPtr (d m : Expr) : Expr := mkApp2 (mkConst (lmNs ++ `LmQuery.ptrToPtr)) d m
    let oTyOk (ty : Nat) : Expr := mkApp (mkConst (lmNs ++ `LmObs.tyOk)) (nat ty)
    let oMethod (f : Nat) (r : Expr) : Expr := mkApp2 (mkConst (lmNs ++ `LmObs.method)) (nat f) r
    let oSizeAlign (s a : Nat) : Expr := mkApp2 (mkConst (lmNs ++ `LmObs.sizeAlign)) (nat s) (nat a)
    let oWide (d v : Expr) : Expr := mkApp2 (mkConst (lmNs ++ `LmObs.wide)) d v
    let oThin (d : Expr) : Expr := mkApp (mkConst (lmNs ++ `LmObs.thin)) d
    let oErr (e : Lean.Name) : Expr := mkApp (mkConst (lmNs ++ `LmObs.err)) (mkConst (lmNs ++ `LmErr ++ e))
    let eqObs (l r : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) obsTy l r
    let reflObs (r : Expr) : Expr := mkApp2 (mkConst ``Eq.refl [1]) obsTy r
    let miriAt (q : Expr) : Expr := mkApp2 miriRunC tableC q
    let protoAt (q : Expr) : Expr := mkApp2 protoRunC tableC q
    let eqTrue (e : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) boolTy e (mkConst ``Bool.true)
    let eqFalse (e : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) boolTy e (mkConst ``Bool.false)

    -- 1. The elaborated certificate, contract, VTableMachine checks, and capstone.
    let env0 ← getEnv
    let checkName := ns ++ `miriAuthority_check
    let contractName := ns ++ `miriContract
    let vtmRegCheckName := ns ++ `vtmRegistryCheck_ok
    let vtmCheckName := ns ++ `vtmMachineCheck_ok
    let capstoneName := ns ++ `dyn_dual_authority_capstone
    for n in [checkName, contractName, vtmRegCheckName, vtmCheckName, capstoneName] do
      let some (.thmInfo _) := env0.find? n | throwError "cross-root: theorem {n} missing"
    let some (.thmInfo checkInfo) := env0.find? checkName | throwError "unreachable"
    unless checkInfo.type == eqTrue (mkApp (mkConst (lmNs ++ `lmAuthorityCheck))
        (mkConst (ns ++ `miriAuthority))) do
      throwError "cross-root: {checkName} has an unexpected statement"
    let some (.thmInfo vtmRegInfo) := env0.find? vtmRegCheckName | throwError "unreachable"
    unless vtmRegInfo.type == eqTrue (mkConst (ns ++ `vtmRegistryCheck)) do
      throwError "cross-root: {vtmRegCheckName} has an unexpected statement"
    let some (.thmInfo vtmInfo) := env0.find? vtmCheckName | throwError "unreachable"
    unless vtmInfo.type == eqTrue (mkConst (ns ++ `vtmMachineCheck)) do
      throwError "cross-root: {vtmCheckName} has an unexpected statement"
    let contractC := mkConst contractName

    -- 2. Closed per-law projections of the contract over the vendored interpreter.
    let mut added : Array Lean.Name := #[checkName, contractName, vtmRegCheckName, vtmCheckName, capstoneName]
    for law in [`agreement, `unsize_pairs_data_with_vtable, `upcast_selects_super_vtable,
                `layout_from_vtable, `trait_check_ignores_auto_traits,
                `invalid_vtable_pointer_ub, `invalid_vtable_trait_ub,
                `virtual_call_resolves_and_narrows, `non_method_slot_ub,
                `ptr_to_ptr_erases_metadata] do
      let val := mkApp2 (mkConst (lmNs ++ `LmDynContract ++ law)) (mkConst (ns ++ `miriAuthority))
        contractC
      let ty ← MetaM.run' <| inferType val
      let outName := ns ++ `law ++ law
      addThm outName ty val
      added := added.push outName

    -- 3. `Eq.refl` certificates: the kernel runs the vendored functions.
    let certs : List (Lean.Name × Expr × Expr) :=
      [ (`cert.resolveVirtual_eval_vt, qVirtual 0 3 (prov 3 0) (prov 40000 0), oMethod 0 (prov 3 0)),
        (`cert.resolveVirtual_field_receiver, qVirtual 0 3 (prov 5 4) (prov 40001 0),
          oMethod 2 (prov 5 4)),
        (`cert.resolveVirtual_wrapped_dispatch_from_dyn,
          qVirtualWrapped 0 3 (prov 5 4) (prov 40001 0), oMethod 2 (prov 5 4)),
        (`cert.resolveVirtual_wrapped_header_ub,
          qVirtualWrapped 0 1 (prov 3 0) (prov 40000 0), oErr `notAMethod),
        (`cert.resolveVirtual_header_slot_ub, qVirtual 0 1 (prov 3 0) (prov 40000 0),
          oErr `notAMethod),
        (`cert.resolveVirtual_dangling_vtable_ub, qVirtual 0 3 (prov 3 0) (intP 8),
          oErr `invalidVTablePointer),
        (`cert.vtableType_assoc_perm_dup_auto, qVtableType (prov 40007 0) 9, oTyOk 0),
        (`cert.vtableType_assoc_mismatch_ub, qVtableType (prov 40007 0) 10,
          oErr `invalidVTableTrait),
        (`cert.getSizeAndAlign_alt_receiver, qSizeAlign (prov 40001 0) 0, oSizeAlign 8 4),
        (`cert.getSizeAndAlign_wrong_trait_ub, qSizeAlign (prov 40002 0) 0,
          oErr `invalidVTableTrait),
        (`cert.unsizeIntoPointer_sized, qUnsize 1 0 (prov 5 4), oWide (prov 5 4) (prov 40001 0)),
        (`cert.unsizeIntoPointer_null_raw, qUnsize 0 0 (intP 0), oWide (intP 0) (prov 40000 0)),
        (`cert.unsizeInto_pin_sized, qUnsizePin 1 0 (prov 5 4), oWide (prov 5 4) (prov 40001 0)),
        (`cert.unsizeInto_pin_upcast_traitVPtr, qUpcastPin 3 2 (prov 3 0) (prov 40004 0),
          oWide (prov 3 0) (prov 40003 0)),
        (`cert.unsizeInto_pin_upcast_prefix, qUpcastPin 4 2 (prov 3 0) (prov 40005 0),
          oWide (prov 3 0) (prov 40003 0)),
        (`cert.unsizeInto_pin_identity, qUpcastPin 3 3 (prov 3 0) (prov 40004 0),
          oWide (prov 3 0) (prov 40004 0)),
        (`cert.unsizeIntoPointer_upcast_traitVPtr, qUpcast 3 2 (prov 3 0) (prov 40004 0),
          oWide (prov 3 0) (prov 40003 0)),
        (`cert.unsizeIntoPointer_upcast_prefix, qUpcast 4 2 (prov 3 0) (prov 40005 0),
          oWide (prov 3 0) (prov 40003 0)),
        (`cert.ptrToPtr_erases_vtable, qPtrToPtr (prov 5 4) (prov 40001 0), oThin (prov 5 4)) ]
    for (n, q, o) in certs do
      addThm (ns ++ n) (eqObs (miriAt q) o) (reflObs o)
      added := added.push (ns ++ n)
    -- Pointwise agreement certificates `miriRun q = protoLmRun q`.
    let agreeQs : List (Lean.Name × Expr) :=
      [ (`agree.virtualCall, qVirtual 0 4 (prov 3 0) (prov 40000 0)),
        (`agree.virtualCallWrapped, qVirtualWrapped 0 3 (prov 5 4) (prov 40001 0)),
        (`agree.vtableTypeAssocPermDup, qVtableType (prov 40007 0) 9),
        (`agree.unsizePin, qUnsizePin 0 0 (prov 3 0)),
        (`agree.upcastPin, qUpcastPin 3 2 (prov 3 0) (prov 40004 0)),
        (`agree.upcast, qUpcast 3 2 (prov 3 0) (prov 40004 0)),
        (`agree.sizeAlign, qSizeAlign (prov 40000 0) 0) ]
    for (n, q) in agreeQs do
      addThm (ns ++ n) (eqObs (miriAt q) (protoAt q)) (reflObs (miriAt q))
      added := added.push (ns ++ n)

    -- 4. Negative controls on scratch copies: the kernel must reject every forgery.
    let saved ← getEnv
    let rejects (d : Declaration) : CoreM Bool := do
      let r ← try addDecl d; pure false catch _ => pure true
      setEnv saved
      return r
    let forgedCheck (auth : Lean.Name) : Declaration :=
      .thmDecl { name := ns ++ `forged ++ auth, levelParams := [],
                 type := eqTrue (mkApp (mkConst (lmNs ++ `lmAuthorityCheck)) (mkConst (ns ++ auth))),
                 value := mkApp2 (mkConst ``Eq.refl [1]) boolTy (mkConst ``Bool.true) }
    let forgedObs (n : Lean.Name) (q o : Expr) : Declaration :=
      .thmDecl { name := ns ++ `forged ++ n, levelParams := [], type := eqObs (miriAt q) o,
                 value := reflObs o }
    let forged : List (String × Declaration) :=
      [ ("negated lmAuthorityCheck miriAuthority (= false)", .thmDecl {
          name := ns ++ `forged.checkFalse, levelParams := [],
          type := eqFalse (mkApp (mkConst (lmNs ++ `lmAuthorityCheck)) (mkConst (ns ++ `miriAuthority))),
          value := mkApp2 (mkConst ``Eq.refl [1]) boolTy (mkConst ``Bool.false) }),
        ("negated vtmRegistryCheck (= false)", .thmDecl {
          name := ns ++ `forged.vtmRegFalse, levelParams := [],
          type := eqFalse (mkConst (ns ++ `vtmRegistryCheck)),
          value := mkApp2 (mkConst ``Eq.refl [1]) boolTy (mkConst ``Bool.false) }),
        ("negated vtmMachineCheck (= false)", .thmDecl {
          name := ns ++ `forged.vtmFalse, levelParams := [],
          type := eqFalse (mkConst (ns ++ `vtmMachineCheck)),
          value := mkApp2 (mkConst ``Eq.refl [1]) boolTy (mkConst ``Bool.false) }),
        ("authority resolving the next slot", forgedCheck `forgedNextSlot),
        ("authority skipping the vtable trait check", forgedCheck `forgedNoTraitCheck),
        ("authority keeping metadata on fat-to-thin", forgedCheck `forgedKeepsMetadata),
        ("header slot forged as a method", forgedObs `headerSlotMethod
          (qVirtual 0 1 (prov 3 0) (prov 40000 0)) (oMethod 0 (prov 3 0))),
        ("AltReceiver size forged as 4", forgedObs `altSize4
          (qSizeAlign (prov 40001 0) 0) (oSizeAlign 4 4)),
        ("wrong-trait vtable forged as accepted", forgedObs `wrongTraitAccepted
          (qSizeAlign (prov 40002 0) 0) (oSizeAlign 4 4)),
        ("mismatched assoc-type vtable forged as accepted", forgedObs `assocMismatchAccepted
          (qVtableType (prov 40007 0) 10) (oTyOk 0)),
        ("receiver offset forged as 0", forgedObs `receiverOffset0
          (qVirtual 0 3 (prov 5 4) (prov 40001 0)) (oMethod 2 (prov 5 0))),
        ("wrapped receiver offset forged as 0", forgedObs `wrappedReceiverOffset0
          (qVirtualWrapped 0 3 (prov 5 4) (prov 40001 0)) (oMethod 2 (prov 5 0))),
        ("upcast forged to keep the Sub vtable", forgedObs `upcastKeepsSub
          (qUpcast 3 2 (prov 3 0) (prov 40004 0)) (oWide (prov 3 0) (prov 40004 0))),
        ("Pin unsize forged with wrong vtable", forgedObs `pinUnsizeWrongVt
          (qUnsizePin 1 0 (prov 5 4)) (oWide (prov 5 4) (prov 40000 0))),
        ("Pin upcast forged to keep the Sub vtable", forgedObs `pinUpcastKeepsSub
          (qUpcastPin 3 2 (prov 3 0) (prov 40004 0)) (oWide (prov 3 0) (prov 40004 0))),
        ("fat-to-thin forged to return the vtable", forgedObs `thinIsVtable
          (qPtrToPtr (prov 5 4) (prov 40001 0)) (oThin (prov 40001 0))),
        ("ill-typed 0 = 1", .thmDecl {
          name := ns ++ `forged.zeroEqOne, levelParams := [],
          type := mkApp3 (mkConst ``Eq [1]) natTy (nat 0) (nat 1),
          value := mkApp2 (mkConst ``Eq.refl [1]) natTy (nat 0) }) ]
    let mut rejected : Nat := 0
    for (what, d) in forged do
      unless ← rejects d do
        throwError "cross-root negative control FAILED: kernel accepted {what}"
      rejected := rejected + 1

    -- 5. Axiom, safety, and non-triviality audit; auditor self-tests; reachability.
    let env ← getEnv
    let isStdAx (a : Lean.Name) : Bool :=
      a == ``propext || a == ``Classical.choice || a == ``Quot.sound
    let rec isTrivialProp : Expr → Bool
      | .forallE _ _ body _ => isTrivialProp body
      | e =>
        if e.isConstOf ``True then true
        else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
        else false
    let mut crAxioms : NameSet := {}
    let mut choiceFreeBridge : Nat := 0
    -- Stateful `VTableMachine.{reserve, globalVTable, hooks}` transitively uses
    -- vendored `Miri.Memory.MemoryState.empty` (`KeyedArray` / `Std.HashMap`),
    -- which is the sole source of `Classical.choice` in the cross-root bridge.
    -- Every other bridge declaration (including `miriAuthority_check`,
    -- `miriContract`, all 10 law projections, all `cert.*`/`agree.*`,
    -- `vtmRegistryCheck_ok`, and `corpus_minirust_checkPtr_evalUnOp`) MUST be
    -- strictly choice-free (`⊆ [propext, Quot.sound]`).
    let statefulChoiceDecls : List Lean.Name :=
      [vtmCheckName, capstoneName, ns ++ `vtmHooks, ns ++ `vtmInstalledHooks, ns ++ `vtmMachineCheck]
    let bridgeDefs := [`miriRun, `miriAuthority, `lmVTableHooks, `lmCastHooks,
                       `lmDynLayoutHooks, `lmCompilerHooks, `lmVirtualHooks,
                       `vtmRegistryCheck, `vtmHooks, `vtmInstalledHooks, `vtmMachineCheck]
    for n in added ++ (bridgeDefs.map (ns ++ ·)).toArray do
      let some ci := env.find? n | throwError "cross-root: {n} missing"
      match ci with
      | .defnInfo v => if v.safety != .safe then throwError "cross-root: {n} is not safe"
      | .thmInfo v => if isTrivialProp v.type then throwError "cross-root: {n} is trivial"
      | _ => throwError "cross-root: {n} is not a defn or thm"
      let axs ← collectAxioms n
      for a in axs do
        if a == ``sorryAx || a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
          throwError "cross-root: {n} depends on forbidden axiom {a}"
        unless isStdAx a do throwError "cross-root: {n} depends on non-standard axiom {a}"
        crAxioms := crAxioms.insert a
      if !statefulChoiceDecls.contains n then
        for a in axs do
          if a == ``Classical.choice then
            throwError "cross-root constructive audit failure: {n} unexpectedly uses Classical.choice"
        choiceFreeBridge := choiceFreeBridge + 1
    unless choiceFreeBridge ≥ 46 do
      throwError "cross-root constructive audit vacuous: only {choiceFreeBridge} choice-free decls"
    unless !(← collectAxioms ``sorryAx).all isStdAx do
      throwError "cross-root self-test: sorryAx was not detected"
    unless !(← collectAxioms ``Lean.ofReduceBool).all isStdAx do
      throwError "cross-root self-test: Lean.ofReduceBool was not detected"
    unless isTrivialProp (mkConst ``True) &&
        isTrivialProp (mkApp3 (mkConst ``Eq [1]) natTy (nat 1) (nat 1)) &&
        !isTrivialProp (mkApp3 (mkConst ``Eq [1]) natTy (nat 1) (nat 2)) do
      throwError "cross-root self-test: trivial theorem detector failed"
    let mut reach : NameSet := {}
    let mut todo : Array Lean.Name := #[capstoneName]
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if reach.contains n then continue
      reach := reach.insert n
      if let some ci := env.find? n then
        for d in ci.getUsedConstantsAsSet do
          if !reach.contains d then todo := todo.push d
    let requiredReach : List Lean.Name :=
      [ contractName, checkName, vtmRegCheckName, vtmCheckName,
        lmNs ++ `lmDynContractOfCheck, lmNs ++ `protoLmRun,
        `Anneal.Prototypes.DynTraitUnsizeProto.evalVirtualCallProto,
        `Anneal.Prototypes.DynTraitUnsizeProto.dynLayoutOfValProto,
        `Anneal.Prototypes.DynTraitUnsizeProto.unsizeDynToDyn,
        `MiniRustSpec.Interp.vtableFromPtr, `MiniRustSpec.Interp.computeSize,
        `MiniRustSpec.Interp.computeAlign,
        `MiniRustSpec.Interp.checkPtrMetadataM,
        `MiniRustSpec.Interp.checkPtrM,
        `MiniRustSpec.Interp.evalUnOpM,
        `Miri.Interpreter.VTable.getPtrVTableTypeRead,
        `Miri.Interpreter.VTable.getSizeAndAlignRead,
        `Miri.Interpreter.VTable.getMethod,
        `Miri.Interpreter.VTableMachine.reserve,
        `Miri.Interpreter.VTableMachine.globalVTable,
        `Miri.Interpreter.VTableMachine.Registry.mergePersistent,
        `Miri.Interpreter.VTableMachine.Registry.ensureDisjointFromFunctions,
        `Miri.Interpreter.VTableMachine.hooks,
        `Miri.Interpreter.VirtualCalls.resolveVirtual,
        `Miri.Interpreter.VirtualCalls.pointerPlace,
        `Miri.Interpreter.VirtualCalls.nonOneZstField,
        `Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta,
        `Miri.Interpreter.Cast.unsizeInto,
        `Miri.Interpreter.Cast.unsizeIntoPointer,
        `Miri.Interpreter.Cast.ptrToPtr ]
    for req in requiredReach do
      unless reach.contains req do
        throwError "cross-root reachability failure: capstone does not reach {req}"
    return (added.size, rejected, crAxioms.toArray)

  let ctx : Core.Context :=
    { fileName := "<dyn-trait-cross-root>", fileMap := default, options := opts, maxHeartbeats := 0 }
  let ((addedCount, rejectedCount, crAxioms), _) ← liftCoreM <| act.toIO ctx { env := bridgeEnv }
  unless addedCount = 41 && rejectedCount = 17 do
    throwError "cross-root: unexpected counts (added={addedCount}, rejected={rejectedCount})"
  logInfo m!"dyn-trait cross-root kernel bridge: {addedCount} declarations over vendored Miri.Interpreter (incl. choice-free Cast.unsizeInto + VTableMachine.Registry + stateful VTableMachine + DispatchFromDyn), rejected {rejectedCount} forged controls, reached MiniRust + Miri, axioms {crAxioms}"

/-! ## §6. Axiom and vacuity audit of the prototype and the tests -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let protoMod := `Anneal.Prototypes.DynTraitUnsizeProto
  let some protoIdx := env.getModuleIdx? protoMod
    | throwError "audit: module {protoMod} is not imported"
  let testNs := `Anneal.Prototypes.DynTraitUnsizeProtoTests
  let isStdAx (a : Lean.Name) : Bool :=
    a == ``propext || a == ``Classical.choice || a == ``Quot.sound
  let rec isTrivialProp : Expr → Bool
    | .forallE _ _ body _ => isTrivialProp body
    | e =>
      if e.isConstOf ``True then true
      else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
      else false
  -- Auditor self-tests: injected `sorryAx` / `Lean.ofReduceBool` are caught.
  unless (← liftCoreM <| Lean.collectAxioms ``sorryAx).contains ``sorryAx do
    throwError "audit self-test: sorryAx not detected"
  unless (← liftCoreM <| Lean.collectAxioms ``Lean.ofReduceBool).contains ``Lean.ofReduceBool do
    throwError "audit self-test: Lean.ofReduceBool not detected"
  unless isTrivialProp (mkConst ``True) do
    throwError "audit self-test: True-typed theorem not detected"
  let audit (c : Lean.Name) (info : ConstantInfo) : CommandElabM Bool := do
    for a in ← liftCoreM <| Lean.collectAxioms c do
      if a == ``sorryAx || a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
        throwError "audit failure: {c} uses {a}"
      unless isStdAx a do throwError "audit failure: {c} uses non-standard axiom {a}"
    match info with
    | .thmInfo v =>
      -- Internal auxiliaries (`_proof_`, `match_`, ...) are not authored theorems.
      if c.isInternal then return false
      if isTrivialProp v.type then throwError "audit failure: {c} is a trivial theorem"
      return true
    | .axiomInfo _ => throwError "audit failure: {c} is an axiom"
    | .defnInfo v =>
      if v.safety != .safe then throwError "audit failure: {c} is not safe"
      return false
    | _ => return false
  -- `f._unsafe_rec` are the compiler's executable auxiliaries of recursive
  -- definitions: never referenced by a safe declaration (the kernel rejects
  -- that), so they cannot reach a theorem. Every other declaration is audited.
  let isCompilerAux (c : Lean.Name) : Bool :=
    match c with
    | .str _ s => s == "_unsafe_rec"
    | _ => false
  let mut protoDecls : Nat := 0
  let mut protoThms : Nat := 0
  for (c, info) in env.constants.map₁.toList do
    if env.getModuleIdxFor? c == some protoIdx && !isCompilerAux c then
      protoDecls := protoDecls + 1
      if ← audit c info then protoThms := protoThms + 1
  let mut testThms : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    if testNs.isPrefixOf c && !isCompilerAux c then
      if ← audit c info then testThms := testThms + 1
  unless protoThms ≥ 100 && testThms ≥ 20 do
    throwError "audit is vacuous: {protoThms} prototype and {testThms} test theorems"
  -- Core prototype laws are constructive: no `Classical.choice`.
  let constructive : List Lean.Name :=
    [ ``Anneal.Prototypes.DynTraitUnsizeProto.decodeWidePtr?_encodeWidePtr,
      ``Anneal.Prototypes.DynTraitUnsizeProto.encodeWidePtr_of_decodeWidePtr?,
      ``Anneal.Prototypes.DynTraitUnsizeProto.traitPredEq_symm,
      ``Anneal.Prototypes.DynTraitUnsizeProto.traitPredEq_trans,
      ``Anneal.Prototypes.DynTraitUnsizeProto.traitPredEq_assocBindings_swap,
      ``Anneal.Prototypes.DynTraitUnsizeProto.traitPredEq_assocBindings_dup,
      ``Anneal.Prototypes.DynTraitUnsizeProto.Hom.lowerPtrTy_hom,
      ``Anneal.Prototypes.DynTraitUnsizeProto.Hom.lowerCastKind_hom,
      ``Anneal.Prototypes.DynTraitUnsizeProto.Hom.lowerVirtualReceiver_hom,
      ``Anneal.Prototypes.DynTraitUnsizeProto.Hom.lowerPinDynTarget?_hom,
      ``Anneal.Prototypes.DynTraitUnsizeProto.evalUnsizeCoercionProto_conservative,
      ``Anneal.Prototypes.DynTraitUnsizeProto.evalUnsizeCoercionProto_slice_conservative,
      ``Anneal.Prototypes.DynTraitUnsizeProto.evalUnsizeCoercion_dyn_target_never_ok,
      ``Anneal.Prototypes.DynTraitUnsizeProto.evalUnsizeDynProto_failsClosed,
      ``Anneal.Prototypes.DynTraitUnsizeProto.evalUnsizePinDynProto_failsClosed,
      ``Anneal.Prototypes.DynTraitUnsizeProto.classifyDynUnsizeTarget?_box_and_slice,
      ``Anneal.Prototypes.DynTraitUnsizeProto.refDataValid_ancestor_ub,
      ``Anneal.Prototypes.DynTraitUnsizeProto.refDataValid_zst_dangling_ptr,
      ``Anneal.Prototypes.DynTraitUnsizeProto.refDataValidNoTB_of_refDataValid,
      ``Anneal.Prototypes.DynTraitUnsizeProto.classifyVirtualReceiver_fail_closed,
      ``Anneal.Prototypes.DynTraitUnsizeProto.dynRawBorrowProto?_raw_source,
      ``Anneal.Prototypes.DynTraitUnsizeProto.dynRawBorrowProto?_ignores_borrow_state,
      ``Anneal.Prototypes.DynTraitUnsizeProto.dynRawBorrowProto?_invalid_ref_ub,
      ``Anneal.Prototypes.DynTraitUnsizeProto.rangedReceiverView_allocDead_none,
      ``Anneal.Prototypes.DynTraitUnsizeProto.borrowAncestorChain_self_cycle_none,
      ``Anneal.Prototypes.DynTraitUnsizeProto.rangedReceiverView_fresh_owner_gt,
      ``Anneal.Prototypes.DynTraitUnsizeProto.rangedReceiverView_protectedTags_mem_iff,
      ``Anneal.Prototypes.DynTraitUnsizeProto.rangedReceiverView_empty_protectors,
      ``Anneal.Prototypes.DynTraitUnsizeProto.unsizeSizedToDyn_raw_ptr_unchecked,
      ``Anneal.Prototypes.DynTraitUnsizeProto.unsizeSizedToDyn_ref_ptr_iff_valid,
      ``Anneal.Prototypes.DynTraitUnsizeProto.upcastVTable?_rejects_unrelated_marker,
      ``Anneal.Prototypes.DynTraitUnsizeProto.unsizeDynToDyn_invalid_vtable_ub,
      ``Anneal.Prototypes.DynTraitUnsizeProto.unsizeDynToDyn_forbids_auto_trait_fabrication,
      ``Anneal.Prototypes.DynTraitUnsizeProto.unsizeDynToDyn_zst_wrapped_null_ub,
      ``Anneal.Prototypes.DynTraitUnsizeProto.dynLayoutOfValProto_ok,
      ``Anneal.Prototypes.DynTraitUnsizeProto.dynLayoutOfValProto_data_independent,
      ``Anneal.Prototypes.DynTraitUnsizeProto.evalVirtualCallProto_uninit_arg_ub,
      ``Anneal.Prototypes.DynTraitUnsizeProto.evalVirtualCallProto_invalid_ref_before_callee_ub,
      ``Anneal.Prototypes.DynTraitUnsizeProto.evalVirtualCallProto_non_method_slot_ub,
      ``Anneal.Prototypes.DynTraitUnsizeProto.evalVirtualCallProto_narrows_receiver,
      ``Anneal.Prototypes.DynTraitUnsizeProto.evalWideAddrEqProto_ignores_metadata,
      ``Anneal.Prototypes.DynTraitUnsizeProto.evalWideAddrEqProto_eq_thin_ptr_binop_eq,
      ``Anneal.Prototypes.DynTraitUnsizeProto.evalWideAddrEqProto_eq_thin_binop_eq_all_words,
      ``Anneal.Prototypes.DynTraitUnsizeProto.evalWidePtrEqProto_heterogeneous_meta_ub,
      ``Anneal.Prototypes.DynTraitUnsizeProto.runSteps_eq_plain,
      ``Anneal.Prototypes.DynTraitUnsizeProto.Lm.lmDynContractOfCheck,
      ``Anneal.Prototypes.DynTraitUnsizeProto.MR.vtableFromPtrM_install_ok,
      ``Anneal.Prototypes.DynTraitUnsizeProto.MR.vtableFromPtrM_install_iff,
      ``Anneal.Prototypes.DynTraitUnsizeProto.MR.checkPtrMetadataM_install_correspondence,
      ``Anneal.Prototypes.DynTraitUnsizeProto.MR.checkPtrM_raw_dyn_unchecked,
      ``Anneal.Prototypes.DynTraitUnsizeProto.MR.checkPtrM_ref_dyn_rejects_invalid,
      ``Anneal.Prototypes.DynTraitUnsizeProto.MR.checkPtrM_ref_dyn_ok_and_nonderef,
      ``Anneal.Prototypes.DynTraitUnsizeProto.MR.evalUnOpM_dyn_correspondence,
      ``Anneal.Prototypes.DynTraitUnsizeProto.MR.computeSizeAlignM_eq_dynLayoutProto ]
  let mut choiceFree : Nat := 0
  for d in constructive do
    for a in ← liftCoreM <| Lean.collectAxioms d do
      unless a == ``propext || a == ``Quot.sound do
        throwError "constructive audit failure: {d} uses {a}"
    choiceFree := choiceFree + 1
  logInfo m!"dyn-trait audit: {protoDecls} prototype declarations ({protoThms} theorems) and {testThms} test theorems with standard axioms only (0 sorryAx, 0 ofReduceBool, 0 trustCompiler, 0 trivial theorems); {choiceFree} core laws choice-free"

/-! ## §7. Campaign #22 capstone -/

open Fx in
/-- **Campaign #22 capstone.** With the prototype rules the reproducer's outer
function returns Miri's `20u32` and the driver `30u32`, where `Trusted`'s
`stepMirFn` alone is UB. -/
theorem campaign22_capstone :
    scalarOf (runMirProto prog Outer.body 512 outerState) = some (20, 4) ∧
    tagOf (runMirTrusted Outer.body 512 outerState) = 3 ∧
    scalarOf (runMirProto prog driverBody 128 (driverState driverBody 7 24)) = some (30, 4) :=
  ⟨campaign22_outer_returns_20.1, campaign22_outer_returns_20.2,
   campaign22_driver_7_24_returns_30⟩

end Anneal.Prototypes.DynTraitUnsizeProtoTests
