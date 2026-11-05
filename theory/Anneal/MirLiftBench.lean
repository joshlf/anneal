-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted
import Anneal.MirFuelFree
import Anneal.PureMirExec
import Anneal.MirLiftCore

set_option linter.unusedVariables false

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.MirLiftCore
open Anneal.PureMirExec

def makeEmptyBlock (bb : BasicBlockIdx) (next : BasicBlockIdx) : BasicBlockData :=
  { statements := [], terminator := { kind := .goto next, span := "bench" }, isCleanup := false }

def benchBody : CapturedMir :=
  { pureAdtMultiBlockBody with
    basicBlocks := [
      makeEmptyBlock 0 1,
      makeEmptyBlock 1 2,
      makeEmptyBlock 2 3,
      makeEmptyBlock 3 4,
      makeEmptyBlock 4 5,
      makeEmptyBlock 5 6,
      makeEmptyBlock 6 7,
      makeEmptyBlock 7 8,
      makeEmptyBlock 8 9,
      makeEmptyBlock 9 10,
      { statements := [], terminator := { kind := .return_, span := "bench" }, isCleanup := false }
    ],
    argCount := 0
  }

theorem bench_converges : ∃ fuel, LiftBlock benchBody 0 [ .init (.scalar { bits := 0, sizeBytes := 4 }) ] (fun v => v = (.scalar { bits := 0, sizeBytes := 4 })) fuel :=
  ⟨11, by
    apply LiftBlock.of_lookup (by rfl)
    apply LiftStmtsTerminator.term_goto (by rfl) (by exact Or.inl rfl) (by rfl)
    apply LiftBlock.of_lookup (by rfl)
    apply LiftStmtsTerminator.term_goto (by rfl) (by exact Or.inl rfl) (by rfl)
    apply LiftBlock.of_lookup (by rfl)
    apply LiftStmtsTerminator.term_goto (by rfl) (by exact Or.inl rfl) (by rfl)
    apply LiftBlock.of_lookup (by rfl)
    apply LiftStmtsTerminator.term_goto (by rfl) (by exact Or.inl rfl) (by rfl)
    apply LiftBlock.of_lookup (by rfl)
    apply LiftStmtsTerminator.term_goto (by rfl) (by exact Or.inl rfl) (by rfl)
    apply LiftBlock.of_lookup (by rfl)
    apply LiftStmtsTerminator.term_goto (by rfl) (by exact Or.inl rfl) (by rfl)
    apply LiftBlock.of_lookup (by rfl)
    apply LiftStmtsTerminator.term_goto (by rfl) (by exact Or.inl rfl) (by rfl)
    apply LiftBlock.of_lookup (by rfl)
    apply LiftStmtsTerminator.term_goto (by rfl) (by exact Or.inl rfl) (by rfl)
    apply LiftBlock.of_lookup (by rfl)
    apply LiftStmtsTerminator.term_goto (by rfl) (by exact Or.inl rfl) (by rfl)
    apply LiftBlock.of_lookup (by rfl)
    apply LiftStmtsTerminator.term_goto (by rfl) (by exact Or.inl rfl) (by rfl)
    apply LiftBlock.of_lookup (by rfl)
    apply LiftStmtsTerminator.term_return (by rfl) (by exact Or.inl rfl) (by rfl)
    · rfl
    · rfl⟩

/-!
## Polymorphic indirect-call benchmark (`FF-3.3`)

`liftIndirectCallerMir` is the MIR of

```rust
fn lift_poly_id<T>(x: T) -> T { x }

fn indirect_caller() -> u32 {
    let f: fn(u32) -> u32 = lift_poly_id::<u32>;
    f(7)
}
```

Lifting it exercises every new rule: `LiftStmtMem.reifyFnPointer` interns
`lift_poly_id::<u32>` in `Memory.fnPtrs`; `LiftTerminator.callIndirect`
resolves `move _1(const 7_u32)` through that table and instantiates the
generic callee for `T = u32` (`lookupCallee`, which recomputes the callee's
layouts from the caller's layout table); the callee frame runs with
`Memory.activeCallee = some (instantiated callee)`; and
`LiftTerminator.returnToCaller` writes `_0` back into the caller before the
root `return`.
-/

section IndirectCallBenchmark

open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.MirLoops
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-- `u32` at layout index `0`. -/
def liftU32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }

/-- The generic parameter `T` of `lift_poly_id`. -/
def liftParamTTy : Ty := { kind := .param 0 "T", layoutIdx := 0 }

/-- `fn(u32) -> u32`. -/
def liftU32FnPtrKind : RigidTy := .fnPtr [.uint .u32] (.uint .u32) .safe .rust

/-- `fn(u32) -> u32` at layout index `0`. -/
def liftU32FnPtrTy : Ty := { kind := liftU32FnPtrKind, layoutIdx := 0 }

/-- Placeholder layout for the unconstrained generic parameter `T`. -/
def liftParamTLayout : TypeLayout :=
  { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- `fn lift_poly_id<T>(x: T) -> T { x }` (`typeParamCount = 1`). -/
def liftPolyIdMir : CapturedMir := {
  mkMirBody "ff33::lift_poly_id" 1
    [ { mutability := .mut, ty := liftParamTTy, debugName := some "_0" }
    , { mutability := .not, ty := liftParamTTy, debugName := some "x" } ]
    [ { statements :=
          [ { kind := .assign { local_ := 0, projection := [] }
                (.use (.move { local_ := 1, projection := [] })), span := "id" } ]
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false } ] with
  typeParamCount := 1
  genericParams := [{ idx := 0, name := "T" }]
  layouts := { pointerBits := 64, isLittleEndian := true, entries := [liftParamTLayout] }
}

/--
`indirect_caller`: reify `lift_poly_id::<u32>` into `_1 : fn(u32) -> u32`, call
`move _1(const 7_u32)` indirectly, and return the result.
-/
def liftIndirectCallerMir : CapturedMir :=
  mkMirBody "ff33::indirect_caller" 0
    [ { mutability := .mut, ty := liftU32Ty, debugName := some "_0" }
    , { mutability := .mut, ty := liftU32FnPtrTy, debugName := some "f" } ]
    [ { statements :=
          [ { kind := .storageLive 1, span := "live f" }
          , { kind := .assign { local_ := 1, projection := [] }
                (.cast (.pointerCoercion "ReifyFnPointer")
                  (.constant
                    { ty := { kind := .fnDef "ff33::lift_poly_id" [.uint .u32], layoutIdx := 0 }
                      val := .zeroSized })
                  liftU32FnPtrTy), span := "reify" } ]
        terminator :=
          { kind := .call (.move { local_ := 1, projection := [] })
              [.constant { ty := liftU32Ty, val := .scalar (.int ⟨7, 4⟩) }]
              { local_ := 0, projection := [] } (some 1) .continue_
            span := "call f" }
        isCleanup := false }
    , { statements := [ { kind := .storageDead 1, span := "dead f" } ]
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false } ]

/--
`direct_caller`: call `lift_poly_id::<u32>(7)` directly through its
function-item constant, exercising `LiftTerminator.callDirect` with generic
`typeArgs`.
-/
def liftDirectCallerMir : CapturedMir :=
  mkMirBody "ff33::direct_caller" 0
    [ { mutability := .mut, ty := liftU32Ty, debugName := some "_0" } ]
    [ { statements := []
        terminator :=
          { kind := .call
              (.constant
                { ty := { kind := .fnDef "ff33::lift_poly_id" [.uint .u32], layoutIdx := 0 }
                  val := .zeroSized })
              [.constant { ty := liftU32Ty, val := .scalar (.int ⟨7, 4⟩) }]
              { local_ := 0, projection := [] } (some 1) .continue_
            span := "call lift_poly_id::<u32>" }
        isCleanup := false }
    , { statements := []
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false } ]

/--
Frame-lifted execution of `indirect_caller`: seven steps from the callee-aware
initial frame to the root return of `7_u32`. Each step names the rule it
applies; every premise is an evaluation fact checked by `rfl`.
-/
theorem liftIndirectCaller_lift :
    LiftFrame liftIndirectCallerMir 0 0 (initPureEnv liftIndirectCallerMir [])
      (initMachineStateWithCallees liftIndirectCallerMir [] [liftPolyIdMir]).memory
      (fun v => v = .scalar ⟨7, 4⟩) 7 := by
  -- bb0[0]: `StorageLive(_1)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  -- bb0[1]: `_1 = lift_poly_id::<u32> as fn(u32) -> u32 (ReifyFnPointer)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftStmtMem.reifyFnPointer (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl)
  -- bb0 terminator: `_0 = move _1(const 7_u32) -> bb1`, through `fnPtrs`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftTerminator.callIndirect (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues]
  -- Callee (`lift_poly_id` instantiated at `T = u32`) bb0[0]: `_0 = move _1`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  -- Callee bb0 terminator: `return` into the caller's `_0`, resuming at bb1.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues]
  -- bb1[0]: `StorageDead(_1)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  -- bb1 terminator: root `return` of `_0 = 7_u32`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftTerminator.return_ (by rfl) (by rfl)
  rfl

/--
The indirect call returns `7_u32` with no undefined behavior, panic, or abort,
from the trusted callee-aware initial state.
-/
theorem liftIndirectCaller_wpConverges :
    MirWpConverges liftIndirectCallerMir
      (initMachineStateWithCallees liftIndirectCallerMir [] [liftPolyIdMir])
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨7, 4⟩)) :=
  LiftFrame.mirWpConverges_withCallees liftIndirectCaller_lift

/-- Frame-lifted execution of `direct_caller`: a generic direct call. -/
theorem liftDirectCaller_lift :
    LiftFrame liftDirectCallerMir 0 0 (initPureEnv liftDirectCallerMir [])
      (initMachineStateWithCallees liftDirectCallerMir [] [liftPolyIdMir]).memory
      (fun v => v = .scalar ⟨7, 4⟩) 5 := by
  -- bb0 terminator: `_0 = lift_poly_id::<u32>(const 7_u32) -> bb1`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftTerminator.callDirect (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues]
  -- Callee bb0[0]: `_0 = move _1`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  -- Callee bb0 terminator: `return` into the caller's `_0`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues]
  -- bb1 terminator: root `return`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftTerminator.return_ (by rfl) (by rfl)
  rfl

/-- The direct generic call returns `7_u32`. -/
theorem liftDirectCaller_wpConverges :
    MirWpConverges liftDirectCallerMir
      (initMachineStateWithCallees liftDirectCallerMir [] [liftPolyIdMir])
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨7, 4⟩)) :=
  LiftFrame.mirWpConverges_withCallees liftDirectCaller_lift

/-- Stateless claim for `indirect_caller` with `lift_poly_id` linked. -/
def liftIndirectCallerClaim : Claim where
  body := liftIndirectCallerMir
  callees := [liftPolyIdMir]
  pre args := args = []
  post _ ret := ret = .scalar ⟨7, 4⟩

/-- The precondition of `liftIndirectCallerClaim` is satisfiable. -/
theorem liftIndirectCallerClaim_nonVacuous :
    ∃ args, liftIndirectCallerClaim.pre args :=
  ⟨[], rfl⟩

/--
Trusted verification certificate for `liftIndirectCallerClaim`, discharged by
frame lifting through the reified function pointer.
-/
theorem liftIndirectCaller_verified :
    VerificationResult liftIndirectCallerClaim :=
  LiftFrame.verificationResult liftIndirectCallerClaim [] (fun _ h => h)
    liftIndirectCaller_lift

/-- Compound parametric wrapper type `Wrapper<T>` at layout index `1`. -/
def liftWrapperTTy : Ty :=
  { kind := .adt "ff33::Wrapper" [.param 0 "T"], layoutIdx := 1 }

/--
`u32` at layout index `2` (distinct from `T` at `0` and `Wrapper<T>` at
`1`).
-/
def liftU32At2Ty : Ty := { kind := .uint .u32, layoutIdx := 2 }

/-- Concrete 4-byte scalar layout for `u32`. -/
def liftU32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 },
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/--
`fn lift_poly_wrapper_transmute<T>(x: T) -> u32 { unsafe { transmute(Wrapper(x)) } }`.

In the uninstantiated generic MIR body, both `T` (`layoutIdx = 0`) and the
compound ADT `Wrapper<T>` (`layoutIdx = 1`) carry placeholder 0-byte layouts
(`liftParamTLayout`), so `evalByteCast` (`CastKind.transmute`) fails on the
uninstantiated body (`liftPolyWrapperTransmute_uninstantiated_fails`). When
`lookupCallee` instantiates the body for `T = u32`,
`LayoutTable.instantiateForBody` substitutes `T` at `layoutIdx = 0` and
recomputes the compound layout of `Wrapper<T>` at `layoutIdx = 1` (`4` bytes,
field `0` at offset `0`), enabling `evalByteCast` to succeed.
-/
def liftPolyWrapperTransmuteMir : CapturedMir := {
  mkMirBody "ff33::lift_poly_wrapper_transmute" 1
    [ { mutability := .mut, ty := liftU32At2Ty, debugName := some "_0" }
    , { mutability := .not, ty := liftParamTTy, debugName := some "x" }
    , { mutability := .mut, ty := liftWrapperTTy, debugName := some "w" } ]
    [ { statements :=
          [ { kind := .storageLive 2, span := "live w" }
          , { kind := .assign { local_ := 2, projection := [] }
                (.aggregate (.adt "ff33::Wrapper" 0 none)
                  [.move { local_ := 1, projection := [] }])
              span := "wrap" }
          , { kind := .assign { local_ := 0, projection := [] }
                (.cast .transmute (.move { local_ := 2, projection := [] })
                  liftU32At2Ty)
              span := "transmute" } ]
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false } ] with
  typeParamCount := 1
  genericParams := [{ idx := 0, name := "T" }]
  layouts :=
    { pointerBits := 64
      isLittleEndian := true
      entries := [liftParamTLayout, liftParamTLayout, liftU32Layout] }
}

/--
Without polymorphic layout recomputation (`LayoutTable.instantiateForBody`),
the byte-level `CastKind.transmute` in `liftPolyWrapperTransmuteMir` sees the
0-byte placeholder layout for `Wrapper<T>` at `layoutIdx = 1` and fails.
-/
theorem liftPolyWrapperTransmute_uninstantiated_fails :
    evalPureStmt liftPolyWrapperTransmuteMir 0 2
      [.uninit, .uninit, .init (.aggregate 0 [.scalar ⟨7, 4⟩])]
      { kind := .assign { local_ := 0, projection := [] }
          (.cast .transmute (.move { local_ := 2, projection := [] })
            liftU32At2Ty)
        span := "transmute" } = none :=
  rfl

/-- `fn(T) -> T` at layout index `1`. -/
def liftParamTFnPtrTy : Ty :=
  { kind := .fnPtr [.param 0 "T"] (.param 0 "T") .safe .rust, layoutIdx := 1 }

/-- `unsafe fn(T) -> T` at layout index `1`. -/
def liftParamTUnsafeFnPtrTy : Ty :=
  { kind := .fnPtr [.param 0 "T"] (.param 0 "T") .unsafe_ .rust, layoutIdx := 1 }

/--
`fn lift_poly_tail_apply<T>(x: T) -> T`: reifies `lift_poly_id::<T>` into a
safe function pointer `_2 : fn(T) -> T`, coerces `_2` into an unsafe function
pointer `_3 : unsafe fn(T) -> T` via `PointerCoercion("UnsafeFnPointer")`
(`LiftStmtMem.unsafeFnPointer`), and tail-calls `move _3(move _1)` indirectly
via `TerminatorKind.tailCall` (`LiftTerminator.tailCallIndirect`).
-/
def liftPolyTailApplyMir : CapturedMir := {
  mkMirBody "ff33::lift_poly_tail_apply" 1
    [ { mutability := .mut, ty := liftParamTTy, debugName := some "_0" }
    , { mutability := .not, ty := liftParamTTy, debugName := some "x" }
    , { mutability := .mut, ty := liftParamTFnPtrTy, debugName := some "f_safe" }
    , { mutability := .mut, ty := liftParamTUnsafeFnPtrTy, debugName := some "f_unsafe" } ]
    [ { statements :=
          [ { kind := .storageLive 2, span := "live f_safe" }
          , { kind := .storageLive 3, span := "live f_unsafe" }
          , { kind := .assign { local_ := 2, projection := [] }
                (.cast (.pointerCoercion "ReifyFnPointer")
                  (.constant
                    { ty := { kind := .fnDef "ff33::lift_poly_id" [.param 0 "T"], layoutIdx := 2 }
                      val := .zeroSized })
                  liftParamTFnPtrTy)
              span := "reify id" }
          , { kind := .assign { local_ := 3, projection := [] }
                (.cast (.pointerCoercion "UnsafeFnPointer")
                  (.copy { local_ := 2, projection := [] })
                  liftParamTUnsafeFnPtrTy)
              span := "unsafe coerce" } ]
        terminator :=
          { kind := .tailCall (.move { local_ := 3, projection := [] })
              [.move { local_ := 1, projection := [] }]
            span := "tailcall f_unsafe" }
        isCleanup := false } ] with
  typeParamCount := 1
  genericParams := [{ idx := 0, name := "T" }]
  layouts :=
    { pointerBits := 64
      isLittleEndian := true
      entries := [liftParamTLayout, liftParamTLayout, liftParamTLayout] }
}

/-- `*const ()` at layout index `0`. -/
def liftRawUnitPtrTy : Ty :=
  { kind := .rawPtr .not (.tuple []), layoutIdx := 0 }

/-- `()` at layout index `0`. -/
def liftUnitTy : Ty :=
  { kind := .tuple [], layoutIdx := 0 }

/-- Tuple `(fn(u32) -> u32, *const ())` at layout index `0`. -/
def liftFnPtrSlotTy : Ty :=
  { kind := .tuple [liftU32FnPtrKind, .rawPtr .not (.tuple [])], layoutIdx := 0 }

/-- Function-item type `FnDef("ff33::lift_poly_wrapper_transmute", [u32])`. -/
def liftWrapperTransmuteFnDefTy : Ty :=
  { kind := .fnDef "ff33::lift_poly_wrapper_transmute" [.uint .u32], layoutIdx := 0 }

/--
`poly_layout_caller`: comprehensive benchmark exercising:
1. Projected function-pointer reification (`LiftStmtMem.reifyFnPointerPlace`)
   into `_1.0 : fn(u32) -> u32` for `lift_poly_tail_apply::<u32>`.
2. Function-pointer to raw-pointer cast (`LiftStmtMem.fnPtrToPtr`) into
   `_1.1 : *const ()`.
3. Indirect call through projected operand `copy _1.0(const 7_u32)`
   (`LiftTerminator.callIndirect`) into `lift_poly_tail_apply::<u32>`, which in
   turn exercises polymorphic `ReifyFnPointer`, `UnsafeFnPointer`
   (`LiftStmtMem.unsafeFnPointer`), and indirect `TerminatorKind.tailCall`
   (`LiftTerminator.tailCallIndirect`) to `lift_poly_id::<u32>`.
4. Projected drop (`LiftTerminator.dropProjected`) of `_1.0`.
5. Local function-item call (`LiftTerminator.callFnItem`) through
   `_3 : FnDef("ff33::lift_poly_wrapper_transmute", [u32])`, which exercises
   polymorphic compound layout recomputation (`LayoutTable.instantiateForBody`)
   on `Wrapper<T>` during `CastKind.transmute`.
-/
def liftPolyLayoutCallerMir : CapturedMir :=
  mkMirBody "ff33::poly_layout_caller" 0
    [ { mutability := .mut, ty := liftU32Ty, debugName := some "_0" }
    , { mutability := .mut, ty := liftFnPtrSlotTy, debugName := some "slot" }
    , { mutability := .mut, ty := liftU32Ty, debugName := some "tmp" }
    , { mutability := .mut, ty := liftWrapperTransmuteFnDefTy, debugName := some "g_item" } ]
    [ { statements :=
          [ { kind := .storageLive 1, span := "live slot" }
          , { kind := .storageLive 2, span := "live tmp" }
          , { kind := .assign { local_ := 1, projection := [] }
                (.aggregate .tuple
                  [ .constant { ty := liftUnitTy, val := .zeroSized }
                  , .constant { ty := liftUnitTy, val := .zeroSized } ])
              span := "init slot" }
          , { kind := .assign
                { local_ := 1, projection := [.field 0 liftU32FnPtrTy] }
                (.cast (.pointerCoercion "ReifyFnPointer")
                  (.constant
                    { ty := { kind := .fnDef "ff33::lift_poly_tail_apply" [.uint .u32], layoutIdx := 0 }
                      val := .zeroSized })
                  liftU32FnPtrTy)
              span := "reify into _1.0" }
          , { kind := .assign
                { local_ := 1, projection := [.field 1 liftRawUnitPtrTy] }
                (.cast .fnPtrToPtr
                  (.copy { local_ := 1, projection := [.field 0 liftU32FnPtrTy] })
                  liftRawUnitPtrTy)
              span := "cast _1.0 as *const ()" } ]
        terminator :=
          { kind := .call
              (.copy { local_ := 1, projection := [.field 0 liftU32FnPtrTy] })
              [.constant { ty := liftU32Ty, val := .scalar (.int ⟨7, 4⟩) }]
              { local_ := 2, projection := [] } (some 1) .continue_
            span := "call _1.0(7)" }
        isCleanup := false }
    , { statements := []
        terminator :=
          { kind := .drop
              { local_ := 1, projection := [.field 0 liftU32FnPtrTy] }
              2 .continue_
            span := "drop _1.0" }
        isCleanup := false }
    , { statements :=
          [ { kind := .storageLive 3, span := "live g_item" }
          , { kind := .assign { local_ := 3, projection := [] }
                (.use (.constant { ty := liftWrapperTransmuteFnDefTy, val := .zeroSized }))
              span := "assign fn item _3" } ]
        terminator :=
          { kind := .call
              (.move { local_ := 3, projection := [] })
              [.move { local_ := 2, projection := [] }]
              { local_ := 0, projection := [] } (some 3) .continue_
            span := "call local fn item _3(_2)" }
        isCleanup := false }
    , { statements := []
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false } ]

/-- Linked callees for `liftPolyLayoutCallerMir`. -/
def liftPolyLayoutCallees : List CapturedMir :=
  [liftPolyTailApplyMir, liftPolyIdMir, liftPolyWrapperTransmuteMir]

/--
Explicit audited frame-lifting derivation for `liftPolyLayoutCallerMir` across
all 22 steps.
-/
theorem liftPolyLayoutCaller_lift :
    LiftFrame liftPolyLayoutCallerMir 0 0 (initPureEnv liftPolyLayoutCallerMir [])
      (initMachineStateWithCallees liftPolyLayoutCallerMir [] liftPolyLayoutCallees).memory
      (fun v => v = .scalar ⟨7, 4⟩) 22 := by
  -- bb0[0]: `StorageLive(_1)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  -- bb0[1]: `StorageLive(_2)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  -- bb0[2]: initialize tuple `_1`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  -- bb0[3]: reify `lift_poly_tail_apply::<u32>` into projected field `_1.0`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftStmtMem.reifyFnPointerPlace (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  -- bb0[4]: cast `_1.0` to `*const ()` in `_1.1` via `CastKind.fnPtrToPtr`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftStmtMem.fnPtrToPtr (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl)
  -- bb0 terminator: indirect call `_2 = copy _1.0(const 7_u32) -> bb1`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftTerminator.callIndirect (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues]
  -- `lift_poly_tail_apply::<u32>` bb0[0]: `StorageLive(_2)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  -- `lift_poly_tail_apply::<u32>` bb0[1]: `StorageLive(_3)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  -- `lift_poly_tail_apply::<u32>` bb0[2]: reify `lift_poly_id::<u32>` into
  -- `_2`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftStmtMem.reifyFnPointer (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl)
  -- `lift_poly_tail_apply::<u32>` bb0[3]: coerce `_2` to
  -- `unsafe fn(u32) -> u32`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftStmtMem.unsafeFnPointer (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl)
  -- `lift_poly_tail_apply::<u32>` bb0 terminator: indirect `tailCall` to
  -- `lift_poly_id::<u32>`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftTerminator.tailCallIndirect (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues]
  -- `lift_poly_id::<u32>` bb0[0]: `_0 = move _1`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  -- `lift_poly_id::<u32>` bb0 terminator: return `7_u32` to
  -- `poly_layout_caller` at bb1.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues]
  -- bb1 terminator: projected drop of `_1.0 -> bb2`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftTerminator.dropProjected (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues]
  -- bb2[0]: `StorageLive(_3)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  -- bb2[1]: `_3 = const FnDef("ff33::lift_poly_wrapper_transmute", [u32])`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  -- bb2 terminator: local function-item call `_0 = move _3(move _2) -> bb3`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftTerminator.callFnItem (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl)
  dsimp only [FrameStep.Continues]
  -- `lift_poly_wrapper_transmute::<u32>` bb0[0]: `StorageLive(_2)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  -- `lift_poly_wrapper_transmute::<u32>` bb0[1]:
  -- `_2 = Wrapper::<u32>(move _1)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  -- `lift_poly_wrapper_transmute::<u32>` bb0[2]:
  -- `_0 = move _2 as u32 (Transmute)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  -- `lift_poly_wrapper_transmute::<u32>` bb0 terminator: return `7_u32` into
  -- `_0` at bb3.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues]
  -- bb3 terminator: root return of `7_u32`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl)
  apply LiftTerminator.return_ (by rfl) (by rfl)
  rfl

/--
Convergence of `liftPolyLayoutCallerMir` from the callee-aware initial state.
-/
theorem liftPolyLayoutCaller_wpConverges :
    MirWpConverges liftPolyLayoutCallerMir
      (initMachineStateWithCallees liftPolyLayoutCallerMir [] liftPolyLayoutCallees)
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨7, 4⟩)) :=
  LiftFrame.mirWpConverges_withCallees liftPolyLayoutCaller_lift

/-- Stateless claim for `liftPolyLayoutCallerMir`. -/
def liftPolyLayoutCallerClaim : Claim where
  body := liftPolyLayoutCallerMir
  callees := liftPolyLayoutCallees
  pre args := args = []
  post _ ret := ret = .scalar ⟨7, 4⟩

/-- Non-vacuity of `liftPolyLayoutCallerClaim`. -/
theorem liftPolyLayoutCallerClaim_nonVacuous :
    ∃ args, liftPolyLayoutCallerClaim.pre args :=
  ⟨[], rfl⟩

/-- Trusted verification certificate for `liftPolyLayoutCallerClaim`. -/
theorem liftPolyLayoutCaller_verified :
    VerificationResult liftPolyLayoutCallerClaim :=
  LiftFrame.verificationResult liftPolyLayoutCallerClaim [] (fun _ h => h)
    liftPolyLayoutCaller_lift

/-! ### Signature mismatches are undefined behavior and do not lift -/

/-- `u8` at layout index `0`. -/
def liftU8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }

/-- `fn(u8) -> u8` at layout index `0`. -/
def liftU8FnPtrTy : Ty :=
  { kind := .fnPtr [.uint .u8] (.uint .u8) .safe .rust, layoutIdx := 0 }

/--
`lift_poly_id::<u32>` reified at the wrong pointer type `fn(u8) -> u8`:
`checkCalleeSig` compares the instantiated callee's `u32` locals with the
`u8` signature, so `evalReifyFnPointer` faults.
-/
def liftBadReifySigMir : CapturedMir :=
  mkMirBody "ff33::bad_reify_sig" 0
    [ { mutability := .mut, ty := liftU8Ty, debugName := some "_0" }
    , { mutability := .mut, ty := liftU8FnPtrTy, debugName := some "f" } ]
    [ { statements :=
          [ { kind := .storageLive 1, span := "live f" }
          , { kind := .assign { local_ := 1, projection := [] }
                (.cast (.pointerCoercion "ReifyFnPointer")
                  (.constant
                    { ty := { kind := .fnDef "ff33::lift_poly_id" [.uint .u32], layoutIdx := 0 }
                      val := .zeroSized })
                  liftU8FnPtrTy), span := "reify at fn(u8) -> u8" } ]
        terminator :=
          { kind := .call (.move { local_ := 1, projection := [] })
              [.constant { ty := liftU8Ty, val := .scalar (.int ⟨7, 1⟩) }]
              { local_ := 0, projection := [] } (some 1) .continue_
            span := "call f" }
        isCleanup := false }
    , { statements := []
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false } ]

/-- The mis-typed reification faults at its second step. -/
theorem liftBadReifySig_not_converges (post : MirOutcome → Prop) :
    ¬ MirWpConverges liftBadReifySigMir
      (initMachineStateWithCallees liftBadReifySigMir [] [liftPolyIdMir]) post := by
  rintro ⟨fuel, h⟩
  rcases fuel with _ | _ | fuel <;> exact h

/--
A correctly reified `fn(u32) -> u32` stored in a local declared as
`fn(u8) -> u8`: the call site's operand type disagrees with the interned
signature, so `fnEntryCompatibleWithCallSite` rejects the indirect call.
-/
def liftBadCallSigMir : CapturedMir :=
  mkMirBody "ff33::bad_call_sig" 0
    [ { mutability := .mut, ty := liftU32Ty, debugName := some "_0" }
    , { mutability := .mut, ty := liftU8FnPtrTy, debugName := some "f" } ]
    [ { statements :=
          [ { kind := .storageLive 1, span := "live f" }
          , { kind := .assign { local_ := 1, projection := [] }
                (.cast (.pointerCoercion "ReifyFnPointer")
                  (.constant
                    { ty := { kind := .fnDef "ff33::lift_poly_id" [.uint .u32], layoutIdx := 0 }
                      val := .zeroSized })
                  liftU32FnPtrTy), span := "reify at fn(u32) -> u32" } ]
        terminator :=
          { kind := .call (.move { local_ := 1, projection := [] })
              [.constant { ty := liftU32Ty, val := .scalar (.int ⟨7, 4⟩) }]
              { local_ := 0, projection := [] } (some 1) .continue_
            span := "call f as fn(u8) -> u8" }
        isCleanup := false }
    , { statements := []
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false } ]

/-- The mis-typed indirect call faults at its third step. -/
theorem liftBadCallSig_not_converges (post : MirOutcome → Prop) :
    ¬ MirWpConverges liftBadCallSigMir
      (initMachineStateWithCallees liftBadCallSigMir [] [liftPolyIdMir]) post := by
  rintro ⟨fuel, h⟩
  rcases fuel with _ | _ | _ | fuel <;> exact h

end IndirectCallBenchmark
