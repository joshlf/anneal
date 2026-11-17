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
`direct_caller`: call `lift_poly_id::<u32>(7)` directly into `_1` through its
function-item constant (`LiftTerminator.callDirect` with generic `typeArgs`),
then tail-call `lift_poly_id::<u32>(move _1)` (`LiftTerminator.tailCallDirect`).
-/
def liftDirectCallerMir : CapturedMir :=
  mkMirBody "ff33::direct_caller" 0
    [ { mutability := .mut, ty := liftU32Ty, debugName := some "_0" }
    , { mutability := .mut, ty := liftU32Ty, debugName := some "tmp" } ]
    [ { statements := [ { kind := .storageLive 1, span := "live tmp" } ]
        terminator :=
          { kind := .call
              (.constant
                { ty := { kind := .fnDef "ff33::lift_poly_id" [.uint .u32], layoutIdx := 0 }
                  val := .zeroSized })
              [.constant { ty := liftU32Ty, val := .scalar (.int ⟨7, 4⟩) }]
              { local_ := 1, projection := [] } (some 1) .continue_
            span := "call lift_poly_id::<u32>" }
        isCleanup := false }
    , { statements := []
        terminator :=
          { kind := .tailCall
              (.constant
                { ty := { kind := .fnDef "ff33::lift_poly_id" [.uint .u32], layoutIdx := 0 }
                  val := .zeroSized })
              [.move { local_ := 1, projection := [] }]
            span := "tailcall lift_poly_id::<u32>" }
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
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  -- bb0[1]: `_1 = lift_poly_id::<u32> as fn(u32) -> u32 (ReifyFnPointer)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.reifyFnPointer (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl)
  -- bb0 terminator: `_0 = move _1(const 7_u32) -> bb1`, through `fnPtrs`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.callIndirect (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues]
  -- Callee (`lift_poly_id` instantiated at `T = u32`) bb0[0]: `_0 = move _1`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  -- Callee bb0 terminator: `return` into the caller's `_0`, resuming at bb1.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues]
  -- bb1[0]: `StorageDead(_1)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  -- bb1 terminator: root `return` of `_0 = 7_u32`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.return_ (by rfl) (by rfl) (by rfl)
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

/--
Frame-lifted execution of `direct_caller`: a generic direct call
(`LiftTerminator.callDirect`) followed by a generic direct tail call
(`LiftTerminator.tailCallDirect`).
-/
theorem liftDirectCaller_lift :
    LiftFrame liftDirectCallerMir 0 0 (initPureEnv liftDirectCallerMir [])
      (initMachineStateWithCallees liftDirectCallerMir [] [liftPolyIdMir]).memory
      (fun v => v = .scalar ⟨7, 4⟩) 7 := by
  -- bb0[0]: `StorageLive(_1)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- bb0 terminator: `_1 = lift_poly_id::<u32>(const 7_u32) -> bb1`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.callDirect (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, callFrameMem, Option.getD]
  -- Callee bb0[0]: `_0 = move _1`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- Callee bb0 terminator: `return` into the caller's `_1` at bb1.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, returnFrameMem, restoreCallerProtectors]
  -- bb1 terminator: `tailCall lift_poly_id::<u32>(move _1)`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.tailCallDirect (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, tailCallFrameMem, disableFrameBorrows, Option.getD]
  -- Tail callee bb0[0]: `_0 = move _1`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- Tail callee bb0 terminator: root `return` of `7_u32`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.return_ (by rfl) (by rfl) (by rfl)
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
`fn lift_poly_wrapper_transmute<T>(x: T) -> u32`, whose body is
`unsafe { transmute(Wrapper(x)) }`.

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
   `_1.1 : *const ()`, followed by a byte-level `CastKind.transmute`
   round-trip of `_1.1 : *const ()` back into `_1.0 : fn(u32) -> u32`
   (preserving `ProvenancePtr` across `AbstractByte` encoding/decoding).
3. Indirect call through the round-tripped projected operand
   `copy _1.0(const 7_u32)` (`LiftTerminator.callIndirect`) into
   `lift_poly_tail_apply::<u32>`, which in turn exercises polymorphic
   `ReifyFnPointer`, `UnsafeFnPointer` (`LiftStmtMem.unsafeFnPointer`), and
   indirect `TerminatorKind.tailCall` (`LiftTerminator.tailCallIndirect`) to
   `lift_poly_id::<u32>`.
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
              span := "cast _1.0 as *const ()" }
          , { kind := .assign
                { local_ := 1, projection := [.field 0 liftU32FnPtrTy] }
                (.cast .transmute
                  (.copy { local_ := 1, projection := [.field 1 liftRawUnitPtrTy] })
                  liftU32FnPtrTy)
              span := "transmute _1.1 back to fn(u32) -> u32" } ]
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
all 23 steps.
-/
theorem liftPolyLayoutCaller_lift :
    LiftFrame liftPolyLayoutCallerMir 0 0 (initPureEnv liftPolyLayoutCallerMir [])
      (initMachineStateWithCallees liftPolyLayoutCallerMir [] liftPolyLayoutCallees).memory
      (fun v => v = .scalar ⟨7, 4⟩) 23 := by
  -- bb0[0]: `StorageLive(_1)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- bb0[1]: `StorageLive(_2)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- bb0[2]: initialize tuple `_1`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- bb0[3]: reify `lift_poly_tail_apply::<u32>` into projected field `_1.0`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.reifyFnPointerPlace (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  -- bb0[4]: cast `_1.0` to `*const ()` in `_1.1` via `CastKind.fnPtrToPtr`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.fnPtrToPtr (by rfl) (by rfl) (by rfl)
  -- bb0[5]: transmute `_1.1 : *const ()` back into `_1.0 : fn(u32) -> u32`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- bb0 terminator: indirect call `_2 = copy _1.0(const 7_u32) -> bb1`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.callIndirect (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, callFrameMem, Option.getD]
  -- `lift_poly_tail_apply::<u32>` bb0[0]: `StorageLive(_2)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- `lift_poly_tail_apply::<u32>` bb0[1]: `StorageLive(_3)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- `lift_poly_tail_apply::<u32>` bb0[2]: reify `lift_poly_id::<u32>` into
  -- `_2`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.reifyFnPointer (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl)
  -- `lift_poly_tail_apply::<u32>` bb0[3]: coerce `_2` to
  -- `unsafe fn(u32) -> u32`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.unsafeFnPointer (by rfl) (by rfl) (by rfl) (by rfl)
  -- `lift_poly_tail_apply::<u32>` bb0 terminator: indirect `tailCall` to
  -- `lift_poly_id::<u32>`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.tailCallIndirect (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, tailCallFrameMem, disableFrameBorrows, Option.getD]
  -- `lift_poly_id::<u32>` bb0[0]: `_0 = move _1`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- `lift_poly_id::<u32>` bb0 terminator: return `7_u32` to
  -- `poly_layout_caller` at bb1.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, returnFrameMem, restoreCallerProtectors]
  -- bb1 terminator: projected drop of `_1.0 -> bb2`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.dropProjected (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues]
  -- bb2[0]: `StorageLive(_3)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- bb2[1]: `_3 = const FnDef("ff33::lift_poly_wrapper_transmute", [u32])`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- bb2 terminator: local function-item call `_0 = move _3(move _2) -> bb3`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.callFnItem (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl)
  dsimp only [FrameStep.Continues, callFrameMem, Option.getD]
  -- `lift_poly_wrapper_transmute::<u32>` bb0[0]: `StorageLive(_2)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- `lift_poly_wrapper_transmute::<u32>` bb0[1]:
  -- `_2 = Wrapper::<u32>(move _1)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- `lift_poly_wrapper_transmute::<u32>` bb0[2]:
  -- `_0 = move _2 as u32 (Transmute)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- `lift_poly_wrapper_transmute::<u32>` bb0 terminator: return `7_u32` into
  -- `_0` at bb3.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, returnFrameMem, restoreCallerProtectors]
  -- bb3 terminator: root return of `7_u32`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.return_ (by rfl) (by rfl) (by rfl)
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

/-! ### Diverging calls (`target = none`)

`LiftTerminator` has no rule for diverging calls. In MIR that rustc emits, a
diverging callee either faults by returning or unwinds through cleanup blocks,
which cannot return, so execution never reaches a normal root return. The two
bodies below exercise both outcomes.
-/

/-- `!` at layout index `0`. -/
def liftNeverTy : Ty := { kind := .never, layoutIdx := 0 }

/-- `fn() -> !` at layout index `0`. -/
def liftDivergingFnPtrTy : Ty :=
  { kind := .fnPtr [] .never .safe .rust, layoutIdx := 0 }

/-- `bool` at layout index `0`. -/
def liftBoolTy : Ty := { kind := .bool, layoutIdx := 0 }

/--
A diverging call (`target = none`) to a callee (`lift_poly_id::<u32>`) that
actually executes `TerminatorKind.return_`: `caller.isDiverging = true` makes
normal return from a diverging call immediate undefined behavior.
-/
def liftBadDivergingReturnMir : CapturedMir :=
  mkMirBody "ff33::bad_diverging_return" 0
    [ { mutability := .mut, ty := liftU32Ty, debugName := some "_0" } ]
    [ { statements := []
        terminator :=
          { kind := .call
              (.constant
                { ty := { kind := .fnDef "ff33::lift_poly_id" [.uint .u32], layoutIdx := 0 }
                  val := .zeroSized })
              [.constant { ty := liftU32Ty, val := .scalar (.int ⟨7, 4⟩) }]
              { local_ := 0, projection := [] } none .continue_
            span := "diverging call to returning callee" }
        isCleanup := false } ]

/-- Returning normally from a diverging call (`target = none`) is UB. -/
theorem liftBadDivergingReturn_not_converges (post : MirOutcome → Prop) :
    ¬ MirWpConverges liftBadDivergingReturnMir
      (initMachineStateWithCallees liftBadDivergingReturnMir []
        [liftPolyIdMir]) post := by
  rintro ⟨fuel, h⟩
  rcases fuel with _ | _ | _ | fuel <;> exact h

/--
`fn assert_panic() -> !`: an assertion that always fails, whose unwind edge
(`.continue_`) unwinds into the caller, as a failed overflow or bounds check
does.
-/
def liftAssertPanicMir : CapturedMir :=
  mkMirBody "ff33::assert_panic" 0
    [ { mutability := .mut, ty := liftNeverTy, debugName := some "_0" } ]
    [ { statements := []
        terminator :=
          { kind := .assert
              (.constant { ty := liftBoolTy, val := .scalar (.int ⟨0, 1⟩) })
              true 1 .continue_
            span := "assert false" }
        isCleanup := false }
    , { statements := []
        terminator := { kind := .unreachable, span := "unreachable" }
        isCleanup := false } ]

/--
`diverging_panic_caller`: reifies `assert_panic` into `_1 : fn() -> !` and
calls `move _1()` as a diverging call (`target = none`) whose unwind edge enters
the cleanup block `bb1`. rustc's MIR validator forbids a cleanup block from
returning, so `bb1` ends in `UnwindResume`; the unwind reaches the root frame
and the program panics.
-/
def liftDivergingPanicCallerMir : CapturedMir :=
  mkMirBody "ff33::diverging_panic_caller" 0
    [ { mutability := .mut, ty := liftU32Ty, debugName := some "_0" }
    , { mutability := .mut, ty := liftDivergingFnPtrTy, debugName := some "f" }
    , { mutability := .mut, ty := liftNeverTy, debugName := some "never_dst" } ]
    [ { statements :=
          [ { kind := .storageLive 1, span := "live f" }
          , { kind := .assign { local_ := 1, projection := [] }
                (.cast (.pointerCoercion "ReifyFnPointer")
                  (.constant
                    { ty := { kind := .fnDef "ff33::assert_panic" [], layoutIdx := 0 }
                      val := .zeroSized })
                  liftDivergingFnPtrTy)
              span := "reify assert_panic" } ]
        terminator :=
          { kind := .call (.move { local_ := 1, projection := [] })
              [] { local_ := 2, projection := [] } none (.cleanup 1)
            span := "diverging call f" }
        isCleanup := false }
    , { statements := []
        terminator := { kind := .unwindResume, span := "resume" }
        isCleanup := true } ]

/--
`liftDivergingPanicCallerMir` panics at its fifth step (the cleanup block's
`UnwindResume` at the root), so no normal-return postcondition holds.
-/
theorem liftDivergingPanic_not_converges (Q : Value → Memory → Prop) :
    ¬ MirWpConverges liftDivergingPanicCallerMir
      (initMachineStateWithCallees liftDivergingPanicCallerMir []
        [liftAssertPanicMir]) (mirNormalPost Q) := by
  rintro ⟨fuel, h⟩
  rcases fuel with _ | _ | _ | _ | _ | fuel <;> exact h

/-- `usize` at layout index `0`. -/
def liftUsizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }

/--
Transmuting a null integer (`0_usize`) to `fn(u32) -> u32`: in Rust a function
pointer is non-null, so `decodeValueFromBytes` rejects `sv.bits = 0` without
provenance as immediate undefined behavior.
-/
def liftBadNullFnPtrTransmuteMir : CapturedMir :=
  mkMirBody "ff33::bad_null_fn_ptr_transmute" 0
    [ { mutability := .mut, ty := liftU32FnPtrTy, debugName := some "_0" } ]
    [ { statements :=
          [ { kind := .assign { local_ := 0, projection := [] }
                (.cast .transmute
                  (.constant { ty := liftUsizeTy, val := .scalar (.int ⟨0, 8⟩) })
                  liftU32FnPtrTy)
              span := "transmute 0_usize as fn(u32) -> u32" } ]
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false } ]

/-- Transmuting `0_usize` to `fn(u32) -> u32` faults at its first step. -/
theorem liftBadNullFnPtrTransmute_not_converges (post : MirOutcome → Prop) :
    ¬ MirWpConverges liftBadNullFnPtrTransmuteMir
      (initMachineStateWithCallees liftBadNullFnPtrTransmuteMir [] []) post := by
  rintro ⟨fuel, h⟩
  rcases fuel with _ | fuel <;> exact h

/--
Function-item type `FnDef("core::intrinsics::exact_div", [u32])` for the inline
`exact_div` intrinsic.
-/
def liftExactDivU32FnDefTy : Ty :=
  { kind := .fnDef "core::intrinsics::exact_div" [.uint .u32], layoutIdx := 0 }

/--
Calling `core::intrinsics::exact_div::<u32>(7_u32, 2_u32)` with a non-zero
remainder (`7 % 2 != 0`): `evalExactDiv` returns `none`, so the call branch of
`evalTerminator` faults with `.ub`.
-/
def liftBadExactDivMir : CapturedMir :=
  mkMirBody "ff33::bad_exact_div" 0
    [ { mutability := .mut, ty := liftU32Ty, debugName := some "_0" } ]
    [ { statements := []
        terminator :=
          { kind := .call
              (.constant { ty := liftExactDivU32FnDefTy, val := .zeroSized })
              [ .constant { ty := liftU32Ty, val := .scalar (.int ⟨7, 4⟩) }
              , .constant { ty := liftU32Ty, val := .scalar (.int ⟨2, 4⟩) } ]
              { local_ := 0, projection := [] } (some 1) .continue_
            span := "exact_div(7, 2)" }
        isCleanup := false }
    , { statements := []
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false } ]

/-- Non-exact `core::intrinsics::exact_div` faults at its first step. -/
theorem liftBadExactDiv_not_converges (post : MirOutcome → Prop) :
    ¬ MirWpConverges liftBadExactDivMir
      (initMachineStateWithCallees liftBadExactDivMir [] []) post := by
  rintro ⟨fuel, h⟩
  rcases fuel with _ | fuel <;> exact h

/--
Ill-formed MIR body whose entry block is marked `isCleanup := true` and
executes `Return`. Even though `stepMirFn` does not inspect `blk.isCleanup`,
`LiftFrame.stmt` and `LiftFrame.term` require `blk.isCleanup = false`, so this
body cannot be lifted.
-/
def liftBadCleanupReturnMir : CapturedMir :=
  mkMirBody "ff33::bad_cleanup_return" 0
    [ { mutability := .mut, ty := liftU32Ty, debugName := some "_0" } ]
    [ { statements :=
          [ { kind := .assign { local_ := 0, projection := [] }
                (.use (.constant { ty := liftU32Ty, val := .scalar (.int ⟨7, 4⟩) }))
              span := "assign in cleanup" } ]
        terminator := { kind := .return_, span := "return from cleanup" }
        isCleanup := true } ]

/-! ### Non-capturing `ClosureFnPointer`, `TraitImplEntry`, and `exact_div` -/

/-- Non-capturing closure type `RigidTy.closure "ff33::closure_id" []`. -/
def liftClosureIdTy : Ty :=
  { kind := .closure "ff33::closure_id" [], layoutIdx := 0 }

/--
Trait method function-item type `FnDef("ff33::ApplyTrait::apply", [u32])`.
-/
def liftApplyTraitFnDefTy : Ty :=
  { kind := .fnDef "ff33::ApplyTrait::apply" [.uint .u32], layoutIdx := 0 }

/--
Blanket trait implementation entry mapping `<T as ApplyTrait>::apply` to
`ff33::lift_poly_id`.
-/
def liftApplyTraitImpl : TraitImplEntry where
  traitRef := { defPath := "ff33::ApplyTrait::apply", args := [.param 0 "T"] }
  implPath := "ff33::lift_poly_id"

/-- Function-item type `FnDef("ff33::lift_poly_id", [u32])`. -/
def liftPolyIdU32FnDefTy : Ty :=
  { kind := .fnDef "ff33::lift_poly_id" [.uint .u32], layoutIdx := 0 }

/--
Non-capturing closure body `|x: u32| -> u32 { lift_poly_id(x) }`
(`ff33::closure_id`), which stores the function item `lift_poly_id::<u32>` in a
local `_2` and tail-calls `move _2(move _1)` via
`LiftTerminator.tailCallFnItem`.
-/
def liftClosureIdMir : CapturedMir :=
  mkMirBody "ff33::closure_id" 1
    [ { mutability := .mut, ty := liftU32Ty, debugName := some "_0" }
    , { mutability := .not, ty := liftU32Ty, debugName := some "x" }
    , { mutability := .mut, ty := liftPolyIdU32FnDefTy, debugName := some "id_item" } ]
    [ { statements :=
          [ { kind := .storageLive 2, span := "live id_item" }
          , { kind := .assign { local_ := 2, projection := [] }
                (.use (.constant { ty := liftPolyIdU32FnDefTy, val := .zeroSized }))
              span := "assign id_item" } ]
        terminator :=
          { kind := .tailCall
              (.move { local_ := 2, projection := [] })
              [.move { local_ := 1, projection := [] }]
            span := "tailcall id_item(x)" }
        isCleanup := false } ]

/--
`closure_and_trait_caller`:
1. Coerces a non-capturing closure (`RigidTy.closure "ff33::closure_id" []`) to
   `_1 : fn(u32) -> u32` via `PointerCoercion("ClosureFnPointer")`.
2. Reifies a generic trait method (`FnDef("ff33::ApplyTrait::apply", [u32])`)
   to `_2 : fn(u32) -> u32`, resolving `"ff33::ApplyTrait::apply"` through
   `mem.traitImpls` (`liftApplyTraitImpl`) to `lift_poly_id::<u32>` during both
   `checkCalleeSig` and `lookupCallee`.
3. Calls both function pointers indirectly (`_3 = move _1(14)`, which tail-calls
   a local function item via `LiftTerminator.tailCallFnItem`, and
   `_4 = move _2(_3)`), then divides `_4` by `2` via the inline compiler
   intrinsic `core::intrinsics::exact_div::<u32>`
   (`LiftTerminator.callExactDiv`) and exercises `LiftTerminator.drop`,
   `LiftTerminator.assert`, `LiftTerminator.switchInt`, and
   `LiftTerminator.goto` before returning `7_u32`.
-/
def liftClosureAndTraitCallerMir : CapturedMir := {
  mkMirBody "ff33::closure_and_trait_caller" 0
    [ { mutability := .mut, ty := liftU32Ty, debugName := some "_0" }
    , { mutability := .mut, ty := liftU32FnPtrTy, debugName := some "f_clos" }
    , { mutability := .mut, ty := liftU32FnPtrTy, debugName := some "f_trait" }
    , { mutability := .mut, ty := liftU32Ty, debugName := some "tmp1" }
    , { mutability := .mut, ty := liftU32Ty, debugName := some "tmp2" } ]
    [ { statements :=
          [ { kind := .storageLive 1, span := "live f_clos" }
          , { kind := .storageLive 2, span := "live f_trait" }
          , { kind := .storageLive 3, span := "live tmp1" }
          , { kind := .storageLive 4, span := "live tmp2" }
          , { kind := .assign { local_ := 1, projection := [] }
                (.cast (.pointerCoercion "ClosureFnPointer")
                  (.constant { ty := liftClosureIdTy, val := .zeroSized })
                  liftU32FnPtrTy)
              span := "reify closure" }
          , { kind := .assign { local_ := 2, projection := [] }
                (.cast (.pointerCoercion "ReifyFnPointer")
                  (.constant { ty := liftApplyTraitFnDefTy, val := .zeroSized })
                  liftU32FnPtrTy)
              span := "reify trait method" } ]
        terminator :=
          { kind := .call (.move { local_ := 1, projection := [] })
              [.constant { ty := liftU32Ty, val := .scalar (.int ⟨14, 4⟩) }]
              { local_ := 3, projection := [] } (some 1) .continue_
            span := "call closure fn ptr" }
        isCleanup := false }
    , { statements := []
        terminator :=
          { kind := .call (.move { local_ := 2, projection := [] })
              [.move { local_ := 3, projection := [] }]
              { local_ := 4, projection := [] } (some 2) .continue_
            span := "call trait fn ptr" }
        isCleanup := false }
    , { statements := []
        terminator :=
          { kind := .call
              (.constant { ty := liftExactDivU32FnDefTy, val := .zeroSized })
              [ .move { local_ := 4, projection := [] }
              , .constant { ty := liftU32Ty, val := .scalar (.int ⟨2, 4⟩) } ]
              { local_ := 0, projection := [] } (some 3) .continue_
            span := "call exact_div(_4, 2)" }
        isCleanup := false }
    , { statements := []
        terminator :=
          { kind := .drop { local_ := 2, projection := [] } 4 .continue_
            span := "drop _2" }
        isCleanup := false }
    , { statements := []
        terminator :=
          { kind := .assert
              (.constant { ty := liftBoolTy, val := .scalar (.int ⟨1, 1⟩) })
              true 5 .continue_
            span := "assert true" }
        isCleanup := false }
    , { statements := []
        terminator :=
          { kind := .switchInt (.copy { local_ := 0, projection := [] })
              { branches := [(7, 6)], otherwise := 0 }
            span := "switch _0" }
        isCleanup := false }
    , { statements := []
        terminator := { kind := .goto 7, span := "goto ret" }
        isCleanup := false }
    , { statements := []
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false } ] with
  traitImpls := [liftApplyTraitImpl]
}

/-- Linked callees for `liftClosureAndTraitCallerMir`. -/
def liftClosureAndTraitCallees : List CapturedMir :=
  [liftClosureIdMir, liftPolyIdMir]

/--
Frame-lifted execution of `closure_and_trait_caller` across
`ClosureFnPointer` reification, `tailCallFnItem`, `TraitImplEntry` polymorphic
trait-method dispatch, inline `core::intrinsics::exact_div`, `drop`, `assert`,
`switchInt`, and `goto`.
-/
theorem liftClosureAndTraitCaller_lift :
    LiftFrame liftClosureAndTraitCallerMir 0 0
      (initPureEnv liftClosureAndTraitCallerMir [])
      (initMachineStateWithCallees liftClosureAndTraitCallerMir []
        liftClosureAndTraitCallees).memory
      (fun v => v = .scalar ⟨7, 4⟩) 21 := by
  -- bb0[0]: `StorageLive(_1)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- bb0[1]: `StorageLive(_2)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- bb0[2]: `StorageLive(_3)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- bb0[3]: `StorageLive(_4)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- bb0[4]: `_1 = closure_id as fn(u32) -> u32 (ClosureFnPointer)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.reifyFnPointer (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl)
  -- bb0[5]: `_2 = ApplyTrait::apply::<u32> as fn(u32) -> u32 (ReifyFnPointer)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.reifyFnPointer (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl)
  -- bb0 terminator: `_3 = move _1(const 14_u32) -> bb1`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.callIndirect (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, callFrameMem, Option.getD]
  -- `closure_id` bb0[0]: `StorageLive(_2)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- `closure_id` bb0[1]: `_2 = const FnDef("ff33::lift_poly_id", [u32])`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- `closure_id` bb0 terminator: `tailCall move _2(move _1)`
  -- (`tailCallFnItem`).
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.tailCallFnItem (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, tailCallFrameMem, disableFrameBorrows, Option.getD]
  -- `lift_poly_id::<u32>` bb0[0]: `_0 = move _1`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- `lift_poly_id::<u32>` bb0 terminator: return `14_u32` into `_3` at bb1.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, returnFrameMem, restoreCallerProtectors]
  -- bb1 terminator: `_4 = move _2(move _3) -> bb2` (trait method via `fnPtrs`).
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.callIndirect (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, callFrameMem, Option.getD]
  -- `lift_poly_id::<u32>` bb0[0]: `_0 = move _1`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- `lift_poly_id::<u32>` bb0 terminator: return `14_u32` into `_4` at bb2.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, returnFrameMem, restoreCallerProtectors]
  -- bb2 terminator: `_0 = exact_div::<u32>(move _4, const 2_u32) -> bb3`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.callExactDiv (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, List.set]
  -- bb3 terminator: `drop(_2) -> bb4`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.drop (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, List.set]
  -- bb4 terminator: `assert(true) -> bb5`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.assert (by rfl) (by rfl)
  dsimp only [FrameStep.Continues]
  -- bb5 terminator: `switchInt(copy _0) [7 -> bb6, otherwise -> bb0]`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.switchInt (by rfl)
  dsimp only [FrameStep.Continues, lookupSwitchTarget]
  -- bb6 terminator: `goto -> bb7`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.goto
  dsimp only [FrameStep.Continues]
  -- bb7 terminator: root return of `7_u32`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.return_ (by rfl) (by rfl) (by rfl)
  rfl

/-- Convergence of `liftClosureAndTraitCallerMir`. -/
theorem liftClosureAndTraitCaller_wpConverges :
    MirWpConverges liftClosureAndTraitCallerMir
      (initMachineStateWithCallees liftClosureAndTraitCallerMir []
        liftClosureAndTraitCallees)
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨7, 4⟩)) :=
  LiftFrame.mirWpConverges_withCallees liftClosureAndTraitCaller_lift

/-- Stateless claim for `liftClosureAndTraitCallerMir`. -/
def liftClosureAndTraitCallerClaim : Claim where
  body := liftClosureAndTraitCallerMir
  callees := liftClosureAndTraitCallees
  pre args := args = []
  post _ ret := ret = .scalar ⟨7, 4⟩

/-- Non-vacuity of `liftClosureAndTraitCallerClaim`. -/
theorem liftClosureAndTraitCallerClaim_nonVacuous :
    ∃ args, liftClosureAndTraitCallerClaim.pre args :=
  ⟨[], rfl⟩

/-- Trusted verification certificate for `liftClosureAndTraitCallerClaim`. -/
theorem liftClosureAndTraitCaller_verified :
    VerificationResult liftClosureAndTraitCallerClaim :=
  LiftFrame.verificationResult liftClosureAndTraitCallerClaim [] (fun _ h => h)
    liftClosureAndTraitCaller_lift

/-! ### Higher-order polymorphic indirect calls

The function pointer is created in one frame and called in another: the caller
passes reified `lift_poly_id::<u32>` and `lift_poly_id::<u8>` to the generic
`lift_poly_apply::<u32>` and `lift_poly_apply::<u8>`, which call their
`f : fn(T) -> T` parameter, and writes the returned values into projected
fields `_2.0 : u32` and `_2.1 : u8` of a tuple local `_2 : (u32, u8)`. This
exercises `Memory.fnPtrs` entries surviving across frames, call-site
compatibility against the instantiated parameter type
(`CapturedMir.instantiate` rewrites `fn(T) -> T` to `fn(u32) -> u32` or
`fn(u8) -> u8`), one generic callee instantiated at two layouts in a single
execution, `LiftTerminator.returnToCaller` with a non-empty remaining call
stack (two frames deep), and `LiftTerminator.returnToCaller` writing into
projected `caller.destination` places.
-/

/-- Tuple `(u32, u8)` at layout index `0`. -/
def liftU32U8PairTy : Ty :=
  { kind := .tuple [.uint .u32, .uint .u8], layoutIdx := 0 }

/--
`fn lift_poly_apply<T>(f: fn(T) -> T, x: T) -> T { f(x) }`: calls its
function-pointer parameter indirectly.
-/
def liftPolyApplyMir : CapturedMir := {
  mkMirBody "ff33::lift_poly_apply" 2
    [ { mutability := .mut, ty := liftParamTTy, debugName := some "_0" }
    , { mutability := .not, ty := liftParamTFnPtrTy, debugName := some "f" }
    , { mutability := .not, ty := liftParamTTy, debugName := some "x" } ]
    [ { statements := []
        terminator :=
          { kind := .call (.copy { local_ := 1, projection := [] })
              [.move { local_ := 2, projection := [] }]
              { local_ := 0, projection := [] } (some 1) .continue_
            span := "call f" }
        isCleanup := false }
    , { statements := []
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false } ] with
  typeParamCount := 1
  genericParams := [{ idx := 0, name := "T" }]
  layouts :=
    { pointerBits := 64
      isLittleEndian := true
      entries := [liftParamTLayout, liftParamTLayout] }
}

/--
`poly_apply_caller`: computes
`lift_poly_apply::<u32>(lift_poly_id::<u32>, 3) +
(lift_poly_apply::<u8>(lift_poly_id::<u8>, 4) as u32)` into projected tuple
fields `_2.0 : u32` and `_2.1 : u8` and returns `7_u32`.
-/
def liftPolyApplyCallerMir : CapturedMir :=
  mkMirBody "ff33::poly_apply_caller" 0
    [ { mutability := .mut, ty := liftU32Ty, debugName := some "_0" }
    , { mutability := .mut, ty := liftU32FnPtrTy, debugName := some "f32" }
    , { mutability := .mut, ty := liftU32U8PairTy, debugName := some "pair" }
    , { mutability := .mut, ty := liftU8FnPtrTy, debugName := some "f8" }
    , { mutability := .mut, ty := liftU32Ty, debugName := some "b32" } ]
    [ { statements :=
          [ { kind := .storageLive 1, span := "live f32" }
          , { kind := .assign { local_ := 1, projection := [] }
                (.cast (.pointerCoercion "ReifyFnPointer")
                  (.constant
                    { ty := { kind := .fnDef "ff33::lift_poly_id" [.uint .u32], layoutIdx := 0 }
                      val := .zeroSized })
                  liftU32FnPtrTy)
              span := "reify id::<u32>" }
          , { kind := .storageLive 2, span := "live pair" }
          , { kind := .assign { local_ := 2, projection := [] }
                (.aggregate .tuple
                  [ .constant { ty := liftU32Ty, val := .scalar (.int ⟨0, 4⟩) }
                  , .constant { ty := liftU8Ty, val := .scalar (.int ⟨0, 1⟩) } ])
              span := "init pair" } ]
        terminator :=
          { kind := .call
              (.constant
                { ty := { kind := .fnDef "ff33::lift_poly_apply" [.uint .u32], layoutIdx := 0 }
                  val := .zeroSized })
              [ .move { local_ := 1, projection := [] }
              , .constant { ty := liftU32Ty, val := .scalar (.int ⟨3, 4⟩) } ]
              { local_ := 2, projection := [.field 0 liftU32Ty] } (some 1) .continue_
            span := "_2.0 = apply::<u32>(f32, 3)" }
        isCleanup := false }
    , { statements :=
          [ { kind := .storageLive 3, span := "live f8" }
          , { kind := .assign { local_ := 3, projection := [] }
                (.cast (.pointerCoercion "ReifyFnPointer")
                  (.constant
                    { ty := { kind := .fnDef "ff33::lift_poly_id" [.uint .u8], layoutIdx := 0 }
                      val := .zeroSized })
                  liftU8FnPtrTy)
              span := "reify id::<u8>" } ]
        terminator :=
          { kind := .call
              (.constant
                { ty := { kind := .fnDef "ff33::lift_poly_apply" [.uint .u8], layoutIdx := 0 }
                  val := .zeroSized })
              [ .move { local_ := 3, projection := [] }
              , .constant { ty := liftU8Ty, val := .scalar (.int ⟨4, 1⟩) } ]
              { local_ := 2, projection := [.field 1 liftU8Ty] } (some 2) .continue_
            span := "_2.1 = apply::<u8>(f8, 4)" }
        isCleanup := false }
    , { statements :=
          [ { kind := .storageLive 4, span := "live b32" }
          , { kind := .assign { local_ := 4, projection := [] }
                (.cast .intToInt
                  (.copy { local_ := 2, projection := [.field 1 liftU8Ty] })
                  liftU32Ty)
              span := "_2.1 as u32" }
          , { kind := .assign { local_ := 0, projection := [] }
                (.binaryOp .add
                  (.copy { local_ := 2, projection := [.field 0 liftU32Ty] })
                  (.move { local_ := 4, projection := [] }))
              span := "_2.0 + b32" } ]
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false } ]

/-- Linked callees for `liftPolyApplyCallerMir`. -/
def liftPolyApplyCallees : List CapturedMir := [liftPolyApplyMir, liftPolyIdMir]

/--
Explicit audited frame-lifting derivation for `liftPolyApplyCallerMir` across
all 20 steps.
-/
theorem liftPolyApplyCaller_lift :
    LiftFrame liftPolyApplyCallerMir 0 0 (initPureEnv liftPolyApplyCallerMir [])
      (initMachineStateWithCallees liftPolyApplyCallerMir []
        liftPolyApplyCallees).memory
      (fun v => v = .scalar ⟨7, 4⟩) 20 := by
  -- bb0[0]: `StorageLive(_1)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- bb0[1]: `_1 = lift_poly_id::<u32> as fn(u32) -> u32 (ReifyFnPointer)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.reifyFnPointer (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl)
  -- bb0[2]: `StorageLive(_2)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- bb0[3]: initialize tuple `_2 = (0_u32, 0_u8)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- bb0 terminator: `_2.0 = lift_poly_apply::<u32>(move _1, const 3_u32) ->`
  -- `bb1`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.callDirect (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, callFrameMem, Option.getD]
  -- `lift_poly_apply::<u32>` bb0 terminator: `_0 = copy _1(move _2) -> bb1`
  -- through the function-pointer parameter `_1 : fn(u32) -> u32`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.callIndirect (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, callFrameMem, Option.getD]
  -- `lift_poly_id::<u32>` bb0[0]: `_0 = move _1`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- `lift_poly_id::<u32>` bb0 terminator: return `3_u32` into
  -- `lift_poly_apply::<u32>`'s `_0` at bb1 (two frames deep).
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, returnFrameMem, restoreCallerProtectors]
  -- `lift_poly_apply::<u32>` bb1 terminator: return `3_u32` into projected
  -- destination `_2.0` at bb1.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, returnFrameMem, restoreCallerProtectors]
  -- bb1[0]: `StorageLive(_3)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- bb1[1]: `_3 = lift_poly_id::<u8> as fn(u8) -> u8 (ReifyFnPointer)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.reifyFnPointer (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl)
  -- bb1 terminator: `_2.1 = lift_poly_apply::<u8>(move _3, const 4_u8) -> bb2`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.callDirect (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, callFrameMem, Option.getD]
  -- `lift_poly_apply::<u8>` bb0 terminator: `_0 = copy _1(move _2) -> bb1`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.callIndirect (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, callFrameMem, Option.getD]
  -- `lift_poly_id::<u8>` bb0[0]: `_0 = move _1`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- `lift_poly_id::<u8>` bb0 terminator: return `4_u8` into
  -- `lift_poly_apply::<u8>`'s `_0` at bb1.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, returnFrameMem, restoreCallerProtectors]
  -- `lift_poly_apply::<u8>` bb1 terminator: return `4_u8` into projected
  -- destination `_2.1` at bb2.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, returnFrameMem, restoreCallerProtectors]
  -- bb2[0]: `StorageLive(_4)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- bb2[1]: `_4 = copy _2.1 as u32 (IntToInt)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- bb2[2]: `_0 = Add(copy _2.0, move _4)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- bb2 terminator: root return of `3 + 4 = 7_u32`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.return_ (by rfl) (by rfl) (by rfl)
  rfl

/-- Convergence of `liftPolyApplyCallerMir`. -/
theorem liftPolyApplyCaller_wpConverges :
    MirWpConverges liftPolyApplyCallerMir
      (initMachineStateWithCallees liftPolyApplyCallerMir [] liftPolyApplyCallees)
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨7, 4⟩)) :=
  LiftFrame.mirWpConverges_withCallees liftPolyApplyCaller_lift

/-- Stateless claim for `liftPolyApplyCallerMir`. -/
def liftPolyApplyCallerClaim : Claim where
  body := liftPolyApplyCallerMir
  callees := liftPolyApplyCallees
  pre args := args = []
  post _ ret := ret = .scalar ⟨7, 4⟩

/-- Non-vacuity of `liftPolyApplyCallerClaim`. -/
theorem liftPolyApplyCallerClaim_nonVacuous :
    ∃ args, liftPolyApplyCallerClaim.pre args :=
  ⟨[], rfl⟩

/-- Trusted verification certificate for `liftPolyApplyCallerClaim`. -/
theorem liftPolyApplyCaller_verified :
    VerificationResult liftPolyApplyCallerClaim :=
  LiftFrame.verificationResult liftPolyApplyCallerClaim [] (fun _ h => h)
    liftPolyApplyCaller_lift

/--
Passing `lift_poly_id::<u8>` (`fn(u8) -> u8`) where `lift_poly_apply::<u32>`
expects `fn(u32) -> u32`, as `transmute` could: the indirect call inside
`lift_poly_apply::<u32>` checks the pointer's signature against the instantiated
parameter type and faults.
-/
def liftBadPolyApplySigMir : CapturedMir :=
  mkMirBody "ff33::bad_poly_apply_sig" 0
    [ { mutability := .mut, ty := liftU32Ty, debugName := some "_0" }
    , { mutability := .mut, ty := liftU8FnPtrTy, debugName := some "f8" } ]
    [ { statements :=
          [ { kind := .storageLive 1, span := "live f8" }
          , { kind := .assign { local_ := 1, projection := [] }
                (.cast (.pointerCoercion "ReifyFnPointer")
                  (.constant
                    { ty := { kind := .fnDef "ff33::lift_poly_id" [.uint .u8], layoutIdx := 0 }
                      val := .zeroSized })
                  liftU8FnPtrTy)
              span := "reify id::<u8>" } ]
        terminator :=
          { kind := .call
              (.constant
                { ty := { kind := .fnDef "ff33::lift_poly_apply" [.uint .u32], layoutIdx := 0 }
                  val := .zeroSized })
              [ .move { local_ := 1, projection := [] }
              , .constant { ty := liftU32Ty, val := .scalar (.int ⟨3, 4⟩) } ]
              { local_ := 0, projection := [] } (some 1) .continue_
            span := "apply::<u32>(f8, 3)" }
        isCleanup := false }
    , { statements := []
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false } ]

/--
The mis-typed function-pointer argument faults at the fourth step, the indirect
call inside `lift_poly_apply::<u32>`.
-/
theorem liftBadPolyApplySig_not_converges (post : MirOutcome → Prop) :
    ¬ MirWpConverges liftBadPolyApplySigMir
      (initMachineStateWithCallees liftBadPolyApplySigMir []
        liftPolyApplyCallees) post := by
  rintro ⟨fuel, h⟩
  rcases fuel with _ | _ | _ | _ | fuel <;> exact h

end IndirectCallBenchmark

namespace Anneal.PureMirExec

set_option maxRecDepth 2048

open Trusted.Effect
open Trusted.Sequence
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.EffectWP
open Anneal.ITreeWP
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.MirFuelFree
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-!
## 10. Concrete Multi-Callee, Polymorphic, Intrinsic, & `#[external_spec]`
Witnesses
-/

/-- Generic parameter `T` (`idx := 0`, dedicated layout slot `0`). -/
def polyParamTTy : Ty :=
  { kind := .param 0 "T", layoutIdx := 0 }

/-- Generic tuple `(T, T)` (dedicated compound layout slot `1`). -/
def polyPairTTy : Ty :=
  { kind := .tuple [.param 0 "T", .param 0 "T"], layoutIdx := 1 }

/-- `u64` type (`8` bytes). -/
def pureU64Ty : Ty :=
  { kind := .uint .u64, layoutIdx := 0 }

/-- Concrete `64`-bit layout for `(u32, u32)`. -/
def pairU32Layout : TypeLayout :=
  Option.getD
    (RigidTy.computeLayout 64 [u32Layout] [] none (.tuple [.uint .u32, .uint .u32]))
    u32Layout

/-- Concrete `64`-bit layout for `u64`. -/
def u64Layout : TypeLayout :=
  Option.getD (RigidTy.computeLayout 64 [] [] none (.uint .u64)) u32Layout

/-- Concrete `64`-bit layout for `(u64, u64)`. -/
def pairU64Layout : TypeLayout :=
  Option.getD
    (RigidTy.computeLayout 64 [u64Layout] [] none (.tuple [.uint .u64, .uint .u64]))
    u64Layout

/-- Zero-sized function-item constant `Operand` for `(defPath, typeArgs)`. -/
def fnItemOperand (defPath : DefPath) (typeArgs : List RigidTy := []) : Operand :=
  .constant
    { ty := { kind := .fnDef defPath typeArgs, layoutIdx := 0 }
      val := .zeroSized }

/-- Compile-time `u32` scalar constant `Operand`. -/
def u32ConstOperand (n : Nat) : Operand :=
  .constant
    { ty := pureU32Ty
      val := .scalar (.int { bits := n, sizeBytes := 4 }) }

/--
Polymorphic helper `demo::poly_swap_pair<T>` (`typeParamCount := 1`,
`genericParams := [{ idx := 0, name := "T" }]`, `argCount := 1`):
takes `_1 : (T, T)` and returns `(_1.1, _1.0) : (T, T)`.
Slot `0` holds the placeholder for `T` and slot `1` holds `(T, T)` so
`CapturedMir.instantiate` substitutes `T`'s layout and recomputes `(T, T)`'s
compound layout cleanly at any concrete scalar type `T`.
-/
def polySwapPairBody : CapturedMir where
  defPath := "demo::poly_swap_pair"
  phase := .runtimePostCleanup
  role := .subject
  typeParamCount := 1
  genericParams := [{ idx := 0, name := "T" }]
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := polyPairTTy, debugName := some "_0" },
    { mutability := .not, ty := polyPairTTy, debugName := some "pair" }
  ]
  basicBlocks := [
    { statements := [
        { kind := .assign
            { local_ := 0, projection := [] }
            (.aggregate .tuple [
              .copy { local_ := 1, projection := [.field 1 polyParamTTy] },
              .copy { local_ := 1, projection := [.field 0 polyParamTTy] }
            ])
          span := pureAdtSpan }
      ]
      terminator := { kind := .return_, span := pureAdtSpan }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [{ layout := pairU32Layout, mode := .direct }]
    ret := { layout := pairU32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := {
    pointerBits := 64
    isLittleEndian := true
    entries := [u32Layout, pairU32Layout]
  }
  allocations := []

/--
Caller layout table shared by `u32`-pair callers (`[u32Layout, pairU32Layout]`).
-/
def demoCallerLayouts : LayoutTable where
  pointerBits := 64
  isLittleEndian := true
  entries := [u32Layout, pairU32Layout]

/--
Monomorphized `demo::poly_swap_pair::<u32>` body produced by
`CapturedMir.instantiate`.
-/
def polySwapPairU32Body : CapturedMir :=
  polySwapPairBody.instantiate [(.uint .u32, u32Layout)]

/--
Monomorphized `demo::poly_swap_pair::<u64>` body produced by
`CapturedMir.instantiate`.
-/
def polySwapPairU64Body : CapturedMir :=
  polySwapPairBody.instantiate [(.uint .u64, u64Layout)]

/--
Polymorphic `(defPath, typeArgs)` resolution at `T = u32` via `lookupCallee`
instantiates `polySwapPairBody` to `polySwapPairU32Body`.
-/
theorem lookupCallee_polySwapPair_u32 :
    lookupCallee [polySwapPairBody] demoCallerLayouts
      "demo::poly_swap_pair" [.uint .u32] [] =
      some polySwapPairU32Body := rfl

/--
Polymorphic `(defPath, typeArgs)` resolution at `T = u64` via `lookupCallee`
instantiates `polySwapPairBody` to `polySwapPairU64Body` with recomputed
`u64` / `(u64, u64)` layouts.
-/
theorem lookupCallee_polySwapPair_u64 :
    lookupCallee [polySwapPairBody] demoCallerLayouts
      "demo::poly_swap_pair" [.uint .u64] [] =
      some polySwapPairU64Body := rfl

/-- `checkPureMir` holds on monomorphized `polySwapPairU32Body`. -/
theorem checkPureMir_polySwapPairU32Body :
    checkPureMir polySwapPairU32Body = true := by
  decide

/-- `checkPureMir` holds on monomorphized `polySwapPairU64Body`. -/
theorem checkPureMir_polySwapPairU64Body :
    checkPureMir polySwapPairU64Body = true := by
  decide

/--
Call-free `PureMirConverges` summary for `polySwapPairU32Body` (`T = u32`),
swapping `(a, b)` to `(b, a)`.
-/
theorem polySwapPairU32_pureConverges (a b : Value) :
    PureMirConverges polySwapPairU32Body
      (initPureState polySwapPairU32Body [.aggregate 0 [a, b]])
      (· = .aggregate 0 [b, a]) :=
  ⟨4, rfl⟩

/--
Call-free `PureMirConverges` summary for `polySwapPairU64Body` (`T = u64`),
swapping `(a, b)` to `(b, a)`.
-/
theorem polySwapPairU64_pureConverges (a b : Value) :
    PureMirConverges polySwapPairU64Body
      (initPureState polySwapPairU64Body [.aggregate 0 [a, b]])
      (· = .aggregate 0 [b, a]) :=
  ⟨4, rfl⟩

/--
Intermediate helper `demo::scale_swap_and_div` (`argCount := 1`):
- Input `_1 : (u32, u32) = (x, y)` (with `x < 2^31`).
- `bb0`: calls polymorphic `demo::poly_swap_pair::<u32>(_1)` -> `_2 = (y, x)`,
  jumping to `bb1`.
- `bb1`: computes `_3 = _2.1 * 2` (`BinOp.mul`), then calls inline intrinsic
  `core::intrinsics::exact_div::<u32>(_3, 2)` -> `_4 = x`, jumping to `bb2`.
- `bb2`: computes `_5 = _2.0 + 1` (`BinOp.add`), writes `_0 = (_5, _4)`, and
  returns `((y + 1) % 2^32, x)`.
-/
def scaleSwapAndDivBody : CapturedMir where
  defPath := "demo::scale_swap_and_div"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "_0" },
    { mutability := .not, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "pair" },
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "swapped" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "doubled_x" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "halved_x" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "inc_y" }
  ]
  basicBlocks := [
    -- bb0: StorageLive(_2); _2 = demo::poly_swap_pair::<u32>(_1) -> bb1
    { statements := [
        { kind := .storageLive 2, span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "demo::poly_swap_pair" [.uint .u32])
          [.copy { local_ := 1, projection := [] }]
          { local_ := 2, projection := [] }
          (.some 1)
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb1: StorageLive(_3, _4); _3 = _2.1 * 2; _4 = exact_div::<u32>(_3, 2) ->
    -- bb2
    { statements := [
        { kind := .storageLive 3, span := pureAdtSpan },
        { kind := .storageLive 4, span := pureAdtSpan },
        { kind := .assign
            { local_ := 3, projection := [] }
            (.binaryOp .mul
              (.copy { local_ := 2, projection := [.field 1 pureU32Ty] })
              (u32ConstOperand 2))
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "core::intrinsics::exact_div" [.uint .u32])
          [.copy { local_ := 3, projection := [] }, u32ConstOperand 2]
          { local_ := 4, projection := [] }
          (.some 2)
          .unreachable
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb2: StorageLive(_5); _5 = _2.0 + 1; _0 = (_5, _4); return
    { statements := [
        { kind := .storageLive 5, span := pureAdtSpan },
        { kind := .assign
            { local_ := 5, projection := [] }
            (.binaryOp .add
              (.copy { local_ := 2, projection := [.field 0 pureU32Ty] })
              (u32ConstOperand 1))
          span := pureAdtSpan },
        { kind := .assign
            { local_ := 0, projection := [] }
            (.aggregate .tuple [
              .copy { local_ := 5, projection := [] },
              .copy { local_ := 4, projection := [] }
            ])
          span := pureAdtSpan }
      ]
      terminator := { kind := .return_, span := pureAdtSpan }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [{ layout := pairU32Layout, mode := .direct }]
    ret := { layout := pairU32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := demoCallerLayouts
  allocations := []

/--
Outer caller `demo::caller_two_nested` (`argCount := 1`) invoking 2 nested
helper functions in `demoCallees := [polySwapPairBody, scaleSwapAndDivBody]`:
- `bb0`: `StorageLive(_2)`; calls `demo::scale_swap_and_div(_1)` (which
  internally invokes polymorphic `demo::poly_swap_pair::<u32>` and inline
  `core::intrinsics::exact_div::<u32>`), writing `_2 = ((y + 1) % 2^32, x)`.
- `bb1`: calls polymorphic `demo::poly_swap_pair::<u32>(_2)`, writing
  `_0 = (x, (y + 1) % 2^32)`.
- `bb2`: `return`.
-/
def nestedMultiCalleeCallerBody : CapturedMir where
  defPath := "demo::caller_two_nested"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "_0" },
    { mutability := .not, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "pair" },
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "mid" }
  ]
  basicBlocks := [
    -- bb0: StorageLive(_2); _2 = demo::scale_swap_and_div(_1) -> bb1
    { statements := [
        { kind := .storageLive 2, span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "demo::scale_swap_and_div" [])
          [.copy { local_ := 1, projection := [] }]
          { local_ := 2, projection := [] }
          (.some 1)
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb1: _0 = demo::poly_swap_pair::<u32>(_2) -> bb2
    { statements := []
      terminator := {
        kind := .call
          (fnItemOperand "demo::poly_swap_pair" [.uint .u32])
          [.copy { local_ := 2, projection := [] }]
          { local_ := 0, projection := [] }
          (.some 2)
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb2: return
    { statements := []
      terminator := { kind := .return_, span := pureAdtSpan }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [{ layout := pairU32Layout, mode := .direct }]
    ret := { layout := pairU32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := demoCallerLayouts
  allocations := []

/-- Linked callee table with 2 nested pure helper functions. -/
def demoCallees : List CapturedMir :=
  [polySwapPairBody, scaleSwapAndDivBody]

/--
Expected pair output `(x, (y + 1) % 2^32)` of `nestedMultiCalleeCallerBody`.
-/
def nestedCallerExpected (x y : Nat) : Value :=
  .aggregate 0 [
    .scalar { bits := x, sizeBytes := 4 },
    .scalar { bits := wrapScalarBits (Nat.add y 1) (scalarModulus 4), sizeBytes := 4 }
  ]

private theorem wrapScalarBits_lt {val modulus : Nat} (h : val < modulus) :
    wrapScalarBits val modulus = val := by
  unfold wrapScalarBits
  have h_ble : Nat.ble modulus val = false := by
    cases hb : Nat.ble modulus val with
    | false => rfl
    | true =>
      have h_le : modulus ≤ val := Nat.le_of_ble_eq_true hb
      omega
  rw [h_ble]

private theorem evalExactDiv_double_u32 {x : Nat} (hx : x < 2147483648) :
    evalExactDiv ⟨wrapScalarBits (Nat.mul x 2) (scalarModulus 4), 4⟩ ⟨2, 4⟩ false =
      some ⟨x, 4⟩ := by
  have hm : scalarModulus 4 = 4294967296 := rfl
  have h_mul : Nat.mul x 2 = x * 2 := rfl
  have h_w1 : wrapScalarBits (Nat.mul x 2) (scalarModulus 4) = x * 2 := by
    rw [hm, h_mul]
    exact wrapScalarBits_lt (by omega)
  have h_w2 : wrapScalarBits (x * 2) (scalarModulus 4) = x * 2 := by
    rw [hm]
    exact wrapScalarBits_lt (by omega)
  have h_b2 : wrapScalarBits 2 (scalarModulus 4) = 2 := rfl
  have h_mod : Nat.beq (Nat.mod (x * 2) 2) 0 = true := by
    rw [Nat.beq_eq]
    change (x * 2) % 2 = 0
    omega
  have h_div : Nat.div (x * 2) 2 = x := by
    change (x * 2) / 2 = x
    omega
  dsimp only [evalExactDiv]
  rw [h_w1, h_w2, h_b2]
  dsimp only
  rw [h_mod]
  dsimp only
  rw [h_div]
  rfl

/-!
### 10A. Proof Path A — Compositional 1-Step Callee Summaries
(`PureMirConverges.call_summary`)
-/

/--
Compositional summary for `scaleSwapAndDivBody`: resolves polymorphic
`demo::poly_swap_pair::<u32>` in 1 compositional step via
`PureMirConverges.call_leaf_summary` and inline `core::intrinsics::exact_div`
in 1 step via `PureMirConvergesWithCallees.call_exact_div`.
-/
theorem scaleSwapAndDiv_compositional
    (x y : Nat) (hx : x < 2147483648) :
    PureMirConvergesWithCallees scaleSwapAndDivBody demoCallees
      (initPureState scaleSwapAndDivBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ])
      (· = .aggregate 0 [
        .scalar { bits := wrapScalarBits (Nat.add y 1) (scalarModulus 4), sizeBytes := 4 },
        .scalar { bits := x, sizeBytes := 4 }
      ])
      [] := by
  -- bb0 stmt 0 (StorageLive(_2)), then 1-step compositional call to
  -- poly_swap_pair::<u32>
  have h_init :
      initPureState scaleSwapAndDivBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ] = {
        bb := 0
        stmtIdx := 0
        env := [
          .uninit,
          .init (.aggregate 0 [
            .scalar { bits := x, sizeBytes := 4 },
            .scalar { bits := y, sizeBytes := 4 }
          ]),
          .dead, .dead, .dead, .dead
        ]
      } := rfl
  rw [h_init]
  refine PureMirConvergesWithCallees.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirConverges.call_leaf_summary
    (maxCallDepth := 64)
    (calleeBody := polySwapPairU32Body)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl
    checkPureMir_polySwapPairU32Body
    (polySwapPairU32_pureConverges
      (.scalar { bits := x, sizeBytes := 4 })
      (.scalar { bits := y, sizeBytes := 4 }))
    ?_
  rintro _ rfl
  refine ⟨_, rfl, ?_⟩
  -- bb1 stmts (StorageLive(_3), StorageLive(_4), _3 = _2.1 * 2)
  refine PureMirConvergesWithCallees.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirConvergesWithCallees.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirConvergesWithCallees.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  -- bb1 terminator: 1-step inline core::intrinsics::exact_div(_3, 2)
  refine PureMirConvergesWithCallees.call_exact_div
    (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl
    (evalExactDiv_double_u32 hx) rfl ?_
  -- bb2 stmts (StorageLive(_5), _5 = _2.0 + 1, _0 = (_5, _4)) and return_
  refine PureMirConvergesWithCallees.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirConvergesWithCallees.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirConvergesWithCallees.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  exact PureMirConvergesWithCallees.step ⟨Or.inl rfl, rfl⟩

/--
Headline compositional 2-nested-callee proof (`FF-2.2` Section 4):
proves `nestedMultiCalleeCallerBody` using **2 compositional `call_summary`
steps**
(1 step for `demo::scale_swap_and_div`, reusing `scaleSwapAndDiv_compositional`
without re-stepping any of its basic blocks or guessing fuel, and 1 step for
polymorphic `demo::poly_swap_pair::<u32>`) plus `StorageLive(_2)` and `return_`.
-/
theorem nestedMultiCalleeCaller_compositional
    (x y : Nat) (hx : x < 2147483648) :
    PureMirConvergesWithCallees nestedMultiCalleeCallerBody demoCallees
      (initPureState nestedMultiCalleeCallerBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ])
      (· = nestedCallerExpected x y)
      [] := by
  -- bb0: StorageLive(_2), then 1 compositional step for
  -- demo::scale_swap_and_div
  refine PureMirConvergesWithCallees.step ⟨rfl, ?_⟩
  refine PureMirConverges.call_summary
    (maxCallDepth := 64)
    (calleeBody := scaleSwapAndDivBody)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl
    (scaleSwapAndDiv_compositional x y hx)
    ?_
  rintro _ rfl
  refine ⟨_, rfl, ?_⟩
  -- bb1: 1 compositional step for polymorphic demo::poly_swap_pair::<u32>
  refine PureMirConverges.call_leaf_summary
    (maxCallDepth := 64)
    (calleeBody := polySwapPairU32Body)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl
    checkPureMir_polySwapPairU32Body
    (polySwapPairU32_pureConverges
      (.scalar { bits := wrapScalarBits (Nat.add y 1) (scalarModulus 4), sizeBytes := 4 })
      (.scalar { bits := x, sizeBytes := 4 }))
    ?_
  rintro _ rfl
  refine ⟨_, rfl, ?_⟩
  -- bb2: return_
  exact PureMirConvergesWithCallees.step ⟨Or.inl rfl, rfl⟩

/--
`checkPureMirWithCallees` succeeds on `nestedMultiCalleeCallerBody` at exact
call depth `maxCallDepth = 2` (`caller -> scale_swap_and_div ->
poly_swap_pair`).
-/
theorem checkPureMirWithCallees_nestedCaller_depth2 :
    checkPureMirWithCallees demoCallees nestedMultiCalleeCallerBody 2 [] = true := by
  decide

/--
Tightness of `maxCallDepth` in `checkPureMirWithCallees`: depth `1` rejects
`nestedMultiCalleeCallerBody` because `scale_swap_and_div` makes a nested call
at depth `2`.
-/
theorem checkPureMirWithCallees_nestedCaller_depth1_false :
    checkPureMirWithCallees demoCallees nestedMultiCalleeCallerBody 1 [] = false := by
  decide

/--
Transport the compositional 1-step-per-call
`nestedMultiCalleeCaller_compositional`
proof directly to `MirWpConverges` on `initMachineStateWithCallees`.
-/
theorem nestedMultiCalleeCaller_wpConverges_compositional
    (x y : Nat) (hx : x < 2147483648) :
    MirWpConverges nestedMultiCalleeCallerBody
      (initMachineStateWithCallees nestedMultiCalleeCallerBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ] demoCallees)
      (mirNormalPost
        (fun retVal mem' =>
          ActiveRootMemory nestedMultiCalleeCallerBody
            (initMachineStateWithCallees nestedMultiCalleeCallerBody [
              .aggregate 0 [
                .scalar { bits := x, sizeBytes := 4 },
                .scalar { bits := y, sizeBytes := 4 }
              ]
            ] demoCallees).memory mem' ∧
          retVal = nestedCallerExpected x y)) :=
  mirWpConverges_of_pureExecWithCallees_init
    checkPureMirWithCallees_nestedCaller_depth2
    (nestedMultiCalleeCaller_compositional x y hx)

/-!
### 10B. Proof Path B — Inline `checkPureMirWithCallees` Execution & Trusted
Certificates
-/

private def runPureTauSteps : Nat → CapturedMir → MachineState → Option MachineState
  | 0, _, s => some s
  | n + 1, body, s =>
    match stepMirFn body s with
    | .tau (.running s') => runPureTauSteps n body s'
    | _ => none

private theorem wpMirExecNoCallSym_of_runPureTauSteps
    {n fuel : Nat} {body : CapturedMir} {s s' : MachineState}
    {post : _ → Prop}
    (h_run : runPureTauSteps n body s = some s')
    (h_rest : wpMirExecNoCallSym fuel body (.running s') post) :
    wpMirExecNoCallSym (n + fuel) body (.running s) post := by
  induction n generalizing s with
  | zero =>
    injection h_run with h_eq
    subst h_eq
    simpa only [Nat.zero_add] using h_rest
  | succ k ih =>
    dsimp only [runPureTauSteps] at h_run
    cases h_sf : stepMirFn body s with
    | ret _ => rw [h_sf] at h_run; nomatch h_run
    | vis _ _ => rw [h_sf] at h_run; nomatch h_run
    | tau st =>
      rw [h_sf] at h_run
      cases st with
      | halted _ => nomatch h_run
      | faulted _ => nomatch h_run
      | running nxt =>
        have h_sub := ih h_run
        rw [Nat.succ_add]
        unfold wpMirExecNoCallSym
        rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval]
        dsimp only [stepMirState]
        rw [h_sf]
        exact h_sub

private theorem wpMirExecNoCallSym_of_step_eq
    {fuel : Nat} {body : CapturedMir} {s s' : MachineState}
    {post : _ → Prop}
    (h_step : stepMirFn body s = .tau (.running s'))
    (h_rest : wpMirExecNoCallSym fuel body (.running s') post) :
    wpMirExecNoCallSym (fuel + 1) body (.running s) post := by
  unfold wpMirExecNoCallSym
  rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval]
  dsimp only [stepMirState]
  rw [h_step]
  exact h_rest

private theorem wpMirExecNoCallSym_of_retNormal
    {body : CapturedMir} {s : MachineState} {retVal : Value} {memOut : Memory}
    {post : _ → Prop}
    (h_step : stepMirFn body s = .ret (.normal (retVal, memOut)))
    (h_post : post (.normal (retVal, memOut))) :
    wpMirExecNoCallSym 1 body (.running s) post := by
  unfold wpMirExecNoCallSym
  rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval]
  dsimp only [stepMirState]
  rw [h_step]
  exact h_post

/--
Inline multi-frame `PureMirConvergesWithCallees` proof for
`nestedMultiCalleeCallerBody` (`FF-2.2` Section 4), executing directly across
`pushCalleeFrame`, 2-deep `callStack`, polymorphic `poly_swap_pair::<u32>`,
inline `exact_div`, and `activeCallee` restoration in
`wpPureMirExecWithCallees`.
-/
theorem nestedMultiCalleeCaller_inline
    (x y : Nat) (hx : x < 2147483648) :
    PureMirConvergesWithCallees nestedMultiCalleeCallerBody demoCallees
      (initPureState nestedMultiCalleeCallerBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ])
      (· = nestedCallerExpected x y)
      [] := by
  let pairXY : Value :=
    .aggregate 0 [
      .scalar { bits := x, sizeBytes := 4 },
      .scalar { bits := y, sizeBytes := 4 }
    ]
  let pairYX : Value :=
    .aggregate 0 [
      .scalar { bits := y, sizeBytes := 4 },
      .scalar { bits := x, sizeBytes := 4 }
    ]
  let baseMem := pureCalleeMemory demoCallees []
  let s0 := (initPureState nestedMultiCalleeCallerBody [pairXY]).toMachineState baseMem
  let callerSaved : SavedCallerFrame := {
    callerBody := nestedMultiCalleeCallerBody
    frame := {
      blockIdx := 0
      stmtIdx := 1
      locals := [.uninit, .init pairXY, .uninit]
    }
    destination := { local_ := 2, projection := [] }
    returnTarget := 1
    calleeProtectors := []
    returnUnwind := .continue_
    isDiverging := false
  }
  let s9 : MachineState := {
    frame := {
      blockIdx := 1
      stmtIdx := 3
      locals := [
        .uninit,
        .init pairXY,
        .init pairYX,
        .init (.scalar { bits := wrapScalarBits (Nat.mul x 2) (scalarModulus 4), sizeBytes := 4 }),
        .uninit,
        .dead
      ]
    }
    memory := {
      baseMem with
      callStack := [callerSaved]
      activeCallee := some scaleSwapAndDivBody
    }
  }
  let s10 : MachineState := {
    frame := {
      blockIdx := 2
      stmtIdx := 0
      locals := [
        .uninit,
        .init pairXY,
        .init pairYX,
        .init (.scalar { bits := wrapScalarBits (Nat.mul x 2) (scalarModulus 4), sizeBytes := 4 }),
        .init (.scalar { bits := x, sizeBytes := 4 }),
        .dead
      ]
    }
    memory := s9.memory
  }
  let midPair : Value :=
    .aggregate 0 [
      .scalar { bits := wrapScalarBits (Nat.add y 1) (scalarModulus 4), sizeBytes := 4 },
      .scalar { bits := x, sizeBytes := 4 }
    ]
  let s17 : MachineState := {
    frame := {
      blockIdx := 2
      stmtIdx := 0
      locals := [.init (nestedCallerExpected x y), .init pairXY, .init midPair]
    }
    memory := {
      baseMem with
      activeCallee := some nestedMultiCalleeCallerBody
    }
  }
  have h_step10 : stepMirFn nestedMultiCalleeCallerBody s9 = .tau (.running s10) := by
    change
      (match evalExactDiv ⟨wrapScalarBits (Nat.mul x 2) (scalarModulus 4), 4⟩ ⟨2, 4⟩ false with
       | some retScalar =>
         match writePlaceValue s9.frame.locals s9.memory.borrows
             { local_ := 4, projection := [] } (.scalar retScalar) with
         | .ok updatedLocals =>
           MirStepNode.step {
             frame := { s9.frame with blockIdx := 2, stmtIdx := 0, locals := updatedLocals }
             memory := s9.memory
           }
         | .ub => MirStepNode.fail .ub
         | .unsupported => MirStepNode.unsupported
       | none => MirStepNode.fail .ub) = .tau (.running s10)
    rw [evalExactDiv_double_u32 hx]
    rfl
  have h_run9 : runPureTauSteps 9 nestedMultiCalleeCallerBody s0 = some s9 := rfl
  have h_run7 : runPureTauSteps 7 nestedMultiCalleeCallerBody s10 = some s17 := rfl
  have h_ret17 :
      stepMirFn nestedMultiCalleeCallerBody s17 =
        .ret (.normal (nestedCallerExpected x y, s17.memory)) := rfl
  refine ⟨18, ?_⟩
  unfold wpPureMirExecWithCallees
  exact wpMirExecNoCallSym_of_runPureTauSteps (n := 9) (fuel := 9) h_run9
    (wpMirExecNoCallSym_of_step_eq (fuel := 8) h_step10
      (wpMirExecNoCallSym_of_runPureTauSteps (n := 7) (fuel := 1) h_run7
        (wpMirExecNoCallSym_of_retNormal h_ret17 ⟨Or.inr ⟨_, rfl⟩, rfl⟩)))

/-- Stateless `Claim` for `nestedMultiCalleeCallerBody` with `demoCallees`. -/
def nestedMultiCalleeStatelessClaim : Claim where
  body := nestedMultiCalleeCallerBody
  callees := demoCallees
  pre args :=
    ∃ (x y : Nat),
      x < 2147483648 ∧
      args = [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ]
  post args retVal :=
    ∀ (x y : Nat),
      args = [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ] →
      retVal = nestedCallerExpected x y

/-- Non-vacuity witness for `nestedMultiCalleeStatelessClaim.pre`. -/
theorem nestedMultiCalleeStatelessClaim_nonVacuous :
    NonVacuousPre nestedMultiCalleeStatelessClaim.pre :=
  ⟨[.aggregate 0 [.scalar { bits := 21, sizeBytes := 4 }, .scalar { bits := 99, sizeBytes := 4 }]],
   21, 99, by decide, rfl⟩

private theorem pairU32Args_inj
    {x y x' y' : Nat}
    (h :
      ([Value.aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]] : List Value) =
      [Value.aggregate 0 [
          .scalar { bits := x', sizeBytes := 4 },
          .scalar { bits := y', sizeBytes := 4 }
        ]]) :
    x = x' ∧ y = y' := by
  injection h with h_hd _
  injection h_hd with _ h_flds
  injection h_flds with h_x h_tl
  injection h_tl with h_y _
  injection h_x with h_sx
  injection h_y with h_sy
  injection h_sx with hx_eq _
  injection h_sy with hy_eq _
  exact ⟨hx_eq, hy_eq⟩

/--
Stateless `VerificationResult` for `nestedMultiCalleeStatelessClaim`, discharged
via `verifyMirNoPanic_of_pureExecWithCallees` and
`nestedMultiCalleeCaller_inline`.
-/
theorem verify_nestedMultiCalleeStatelessClaim :
    VerificationResult nestedMultiCalleeStatelessClaim := by
  refine verifyMirNoPanic_of_pureExecWithCallees
    nestedMultiCalleeStatelessClaim
    checkPureMirWithCallees_nestedCaller_depth2
    (fun args h_pre => ?_)
  rcases h_pre with ⟨x, y, hx, rfl⟩
  refine PureMirConvergesWithCallees.mono ?_ (nestedMultiCalleeCaller_inline x y hx)
  intro retVal h_ret x' y' h_eq
  rcases pairU32Args_inj h_eq with ⟨rfl, rfl⟩
  exact h_ret

/--
Stateful `StatefulClaim` for `nestedMultiCalleeCallerBody` requiring full
`ActiveRootMemory` preservation (`allocs`, `borrows`, `provenanceMap`,
`globals`,
`fnPtrs`, `callees`, `traitImpls`, `callStack = []`) across arbitrary heap
state.
-/
def nestedMultiCalleeStatefulClaim : StatefulClaim where
  body := nestedMultiCalleeCallerBody
  callees := demoCallees
  pre args mem₀ :=
    (∃ (x y : Nat),
      x < 2147483648 ∧
      args = [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ]) ∧
    RootActiveMemory mem₀
  post args mem₀ retVal mem' :=
    ActiveRootMemory nestedMultiCalleeCallerBody
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        nestedMultiCalleeCallerBody args mem₀ demoCallees).memory mem' ∧
    ∀ (x y : Nat),
      args = [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ] →
      retVal = nestedCallerExpected x y

/-- Non-vacuity witness for `nestedMultiCalleeStatefulClaim.pre`. -/
theorem nestedMultiCalleeStatefulClaim_nonVacuous :
    NonVacuousStatefulPre nestedMultiCalleeStatefulClaim.pre :=
  ⟨[.aggregate 0 [.scalar { bits := 21, sizeBytes := 4 }, .scalar { bits := 99, sizeBytes := 4 }]],
   emptyMemory,
   ⟨21, 99, by decide, rfl⟩,
   rootActiveMemory_emptyMemory⟩

/--
Stateful `StatefulVerificationResult` for `nestedMultiCalleeStatefulClaim`,
discharged via `verifyStatefulMirNoPanic_of_pureExecWithCallees`.
-/
theorem verify_nestedMultiCalleeStatefulClaim :
    StatefulVerificationResult nestedMultiCalleeStatefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExecWithCallees
    nestedMultiCalleeStatefulClaim
    checkPureMirWithCallees_nestedCaller_depth2
    (by decide)
    (fun _ _ h_pre => h_pre.2)
    (fun args _ h_pre => ?_)
  rcases h_pre.1 with ⟨x, y, hx, rfl⟩
  refine PureMirConvergesWithCallees.mono ?_ (nestedMultiCalleeCaller_compositional x y hx)
  intro retVal h_ret mem' h_act
  refine ⟨h_act, fun x' y' h_eq => ?_⟩
  rcases pairU32Args_inj h_eq with ⟨rfl, rfl⟩
  exact h_ret

/--
Total-correctness `TotalClaim` for `nestedMultiCalleeCallerBody`
(`demoCallees`).
-/
def nestedMultiCalleeTotalClaim : TotalClaim where
  body := nestedMultiCalleeCallerBody
  callees := demoCallees
  pre := nestedMultiCalleeStatefulClaim.pre
  post := nestedMultiCalleeStatefulClaim.post

/-- Non-vacuity witness for `nestedMultiCalleeTotalClaim.pre`. -/
theorem nestedMultiCalleeTotalClaim_nonVacuous :
    NonVacuousStatefulPre nestedMultiCalleeTotalClaim.pre :=
  nestedMultiCalleeStatefulClaim_nonVacuous

/--
Total-correctness `TotalVerificationResult` (`TreeSafe`, `Productive`,
`¬ MayDiverge`, no panic/abort) for `nestedMultiCalleeTotalClaim`.
-/
theorem verify_nestedMultiCalleeTotalClaim :
    TotalVerificationResult nestedMultiCalleeTotalClaim := by
  refine verifyTotalMir_of_pureExecWithCallees
    nestedMultiCalleeTotalClaim
    checkPureMirWithCallees_nestedCaller_depth2
    (by decide)
    (fun _ _ h_pre => h_pre.2)
    (fun args _ h_pre => ?_)
  rcases h_pre.1 with ⟨x, y, hx, rfl⟩
  refine PureMirConvergesWithCallees.mono ?_ (nestedMultiCalleeCaller_compositional x y hx)
  intro retVal h_ret mem' h_act
  refine ⟨h_act, fun x' y' h_eq => ?_⟩
  rcases pairU32Args_inj h_eq with ⟨rfl, rfl⟩
  exact h_ret

/-! ### 10C. Pure `CallConv.rustIntrinsic` & UB-Rejection Witnesses -/

/--
`ctlz::<u8>(0) = 8`, whereas `ctlz_nonzero::<u8>(0) = none` (UB rejected).
-/
theorem evalPureScalarIntrinsic_ctlz_and_nonzero_ub :
    evalPureScalarIntrinsic .ctlz [.uint .u8] [.scalar ⟨0, 1⟩] =
      some (.scalar ⟨8, 4⟩) ∧
    evalPureScalarIntrinsic .ctlzNonzero [.uint .u8] [.scalar ⟨0x10, 1⟩] =
      some (.scalar ⟨3, 4⟩) ∧
    evalPureScalarIntrinsic .ctlzNonzero [.uint .u8] [.scalar ⟨0, 1⟩] = none :=
  ⟨rfl, rfl, rfl⟩

/--
`cttz::<u8>(0) = 8`, whereas `cttz_nonzero::<u8>(0) = none` (UB rejected).
-/
theorem evalPureScalarIntrinsic_cttz_and_nonzero_ub :
    evalPureScalarIntrinsic .cttz [.uint .u8] [.scalar ⟨0, 1⟩] =
      some (.scalar ⟨8, 4⟩) ∧
    evalPureScalarIntrinsic .cttzNonzero [.uint .u8] [.scalar ⟨0x18, 1⟩] =
      some (.scalar ⟨3, 4⟩) ∧
    evalPureScalarIntrinsic .cttzNonzero [.uint .u8] [.scalar ⟨0, 1⟩] = none :=
  ⟨rfl, rfl, rfl⟩

/-- `ctpop`, `bswap`, and `bitreverse` pure evaluation witnesses. -/
theorem evalPureScalarIntrinsic_bitops :
    evalPureScalarIntrinsic .ctpop [.uint .u32] [.scalar ⟨0x10101, 4⟩] =
      some (.scalar ⟨3, 4⟩) ∧
    evalPureScalarIntrinsic .bswap [.uint .u32] [.scalar ⟨0x12345678, 4⟩] =
      some (.scalar ⟨0x78563412, 4⟩) ∧
    evalPureScalarIntrinsic .bitreverse [.uint .u8] [.scalar ⟨0x81, 1⟩] =
      some (.scalar ⟨0x81, 1⟩) :=
  ⟨rfl, rfl, rfl⟩

/--
`wrapping_add/sub/mul` and unsigned/signed `saturating_add/sub` witnesses.
-/
theorem evalPureScalarIntrinsic_wrapping_and_saturating :
    evalPureScalarIntrinsic .wrappingAdd [.uint .u8]
      [.scalar ⟨250, 1⟩, .scalar ⟨10, 1⟩] = some (.scalar ⟨4, 1⟩) ∧
    evalPureScalarIntrinsic .wrappingSub [.uint .u8]
      [.scalar ⟨3, 1⟩, .scalar ⟨5, 1⟩] = some (.scalar ⟨254, 1⟩) ∧
    evalPureScalarIntrinsic .wrappingMul [.uint .u8]
      [.scalar ⟨16, 1⟩, .scalar ⟨16, 1⟩] = some (.scalar ⟨0, 1⟩) ∧
    evalPureScalarIntrinsic .saturatingAdd [.uint .u8]
      [.scalar ⟨250, 1⟩, .scalar ⟨10, 1⟩] = some (.scalar ⟨255, 1⟩) ∧
    evalPureScalarIntrinsic .saturatingAdd [.int .i8]
      [.scalar ⟨120, 1⟩, .scalar ⟨20, 1⟩] = some (.scalar ⟨127, 1⟩) ∧
    evalPureScalarIntrinsic .saturatingSub [.int .i8]
      [.scalar ⟨136, 1⟩, .scalar ⟨20, 1⟩] = some (.scalar ⟨128, 1⟩) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
UB-guarded `unchecked_add`, `unchecked_shl`, and `exact_div` witnesses:
valid inputs evaluate to `some`, while overflow (`250 + 10` on `u8`),
out-of-range
shift (`1 << 8` on `u8`), non-exact division (`7 / 2`), and signed `i8::MIN ÷
-1`
(`128 ÷ 255` on `i8`) evaluate to `none`.
-/
theorem evalPureScalarIntrinsic_ub_guards :
    evalPureScalarIntrinsic .uncheckedAdd [.uint .u8]
      [.scalar ⟨200, 1⟩, .scalar ⟨50, 1⟩] = some (.scalar ⟨250, 1⟩) ∧
    evalPureScalarIntrinsic .uncheckedAdd [.uint .u8]
      [.scalar ⟨250, 1⟩, .scalar ⟨10, 1⟩] = none ∧
    evalPureScalarIntrinsic .uncheckedShl [.uint .u8, .uint .u32]
      [.scalar ⟨3, 1⟩, .scalar ⟨2, 4⟩] = some (.scalar ⟨12, 1⟩) ∧
    evalPureScalarIntrinsic .uncheckedShl [.uint .u8, .uint .u32]
      [.scalar ⟨3, 1⟩, .scalar ⟨8, 4⟩] = none ∧
    evalPureScalarIntrinsic .exactDiv [.uint .u8]
      [.scalar ⟨7, 1⟩, .scalar ⟨2, 1⟩] = none ∧
    evalPureScalarIntrinsic .exactDiv [.int .i8]
      [.scalar ⟨128, 1⟩, .scalar ⟨255, 1⟩] = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `three_way_compare`, `ub_checks`, and `const_eval_select` witnesses. -/
theorem evalPureRustIntrinsic_misc_and_constEvalSelect :
    evalPureScalarIntrinsic .threeWayCompare [.int .i8]
      [.scalar ⟨255, 1⟩, .scalar ⟨1, 1⟩] = some (.scalar ⟨255, 1⟩) ∧
    evalPureScalarIntrinsic .ubChecks [] [] 8 false = some (.scalar ⟨0, 1⟩) ∧
    evalPureRustIntrinsicWithRuntime
      (fun dp targs unpacked =>
        if dp == "demo::rt_add" then
          match targs, unpacked with
          | [.uint .u32], [.scalar a, .scalar b] =>
            some (.scalar ⟨a.bits + b.bits, 4⟩)
          | _, _ => none
        else none)
      .constEvalSelect
      [.tuple [.uint .u32, .uint .u32],
       .fnDef "demo::ct_add" [.uint .u32],
       .fnDef "demo::rt_add" [.uint .u32],
       .uint .u32]
      [.aggregate 0 [.scalar ⟨19, 4⟩, .scalar ⟨23, 4⟩], .unit, .unit] =
      some (.scalar ⟨42, 4⟩) :=
  ⟨rfl, rfl, rfl⟩

/-!
### 10D. Modular `CallConv.rustIntrinsic` & `#[external_spec]` Caller
Witnesses
-/

/--
Caller `demo::intrinsic_bswap_pop` invoking two `CallConv.rustIntrinsic`
operations (`core::intrinsics::bswap::<u32>` followed by
`core::intrinsics::ctpop::<u32>`) on `_1 : u32`.
-/
def pureIntrinsicCallerBody : CapturedMir where
  defPath := "demo::intrinsic_bswap_pop"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := pureU32Ty, debugName := some "_0" },
    { mutability := .not, ty := pureU32Ty, debugName := some "x" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "swapped" }
  ]
  basicBlocks := [
    -- bb0: StorageLive(_2); _2 = core::intrinsics::bswap::<u32>(_1) -> bb1
    { statements := [
        { kind := .storageLive 2, span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "core::intrinsics::bswap" [.uint .u32])
          [.copy { local_ := 1, projection := [] }]
          { local_ := 2, projection := [] }
          (.some 1)
          .unreachable
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb1: _0 = core::intrinsics::ctpop::<u32>(_2) -> bb2
    { statements := []
      terminator := {
        kind := .call
          (fnItemOperand "core::intrinsics::ctpop" [.uint .u32])
          [.copy { local_ := 2, projection := [] }]
          { local_ := 0, projection := [] }
          (.some 2)
          .unreachable
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb2: return
    { statements := []
      terminator := { kind := .return_, span := pureAdtSpan }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [{ layout := u32Layout, mode := .direct }]
    ret := { layout := u32Layout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := demoCallerLayouts
  allocations := []

/--
Default 64-bit runtime `pureRustIntrinsicContract` instance (`pointerBytes =
8`).
-/
abbrev defaultPureRustIntrinsicContract : MirCallContract :=
  pureRustIntrinsicContract 8 true (fun _ _ _ => none)

/--
Expected return value `ctpop::<u32>(bswap::<u32>(x))` of
`pureIntrinsicCallerBody`.
-/
@[irreducible]
def expectedBswapPopU32 (x : Nat) : Value :=
  .scalar ⟨pureCtpopLoop 32 (pureBswapLoop 4 x 0), 4⟩

private theorem expectedBswapPopU32_def (x : Nat) :
    (Value.scalar ⟨pureCtpopLoop 32 (pureBswapLoop 4 x 0), 4⟩) =
      expectedBswapPopU32 x := by
  unfold expectedBswapPopU32
  rfl

private theorem isCanonicalScalarOfSize_four {v : Nat} (hv : v < 4294967296) :
    isCanonicalScalarOfSize { bits := v, sizeBytes := 4 } 4 = true := by
  change decide (v < 4294967296) = true
  exact decide_eq_true hv

/--
Compositional modular convergence for `pureIntrinsicCallerBody` under
`defaultPureRustIntrinsicContract` on any canonical `x < 2^32` and arbitrary
`traitImpls`.
-/
theorem pureIntrinsicCaller_modularConverges
    (x : Nat) (hx : x < 4294967296)
    (traitImpls : List TraitImplEntry := []) :
    PureMirModularConverges
      defaultPureRustIntrinsicContract
      pureIntrinsicCallerBody []
      (initPureState pureIntrinsicCallerBody [.scalar { bits := x, sizeBytes := 4 }])
      (· = expectedBswapPopU32 x)
      traitImpls := by
  have h_canon_x :
      isCanonicalScalarOfSize { bits := x, sizeBytes := 4 } 4 = true :=
    isCanonicalScalarOfSize_four hx
  have h_step (v a bound : Nat) (ha : a < bound) :
      a * 256 + Nat.mod v 256 < bound * 256 := by
    have hm : Nat.mod v 256 < 256 := Nat.mod_lt v (by decide)
    omega
  have h_bswap_lt : pureBswapLoop 4 x 0 < 4294967296 := by
    dsimp only [pureBswapLoop]
    have h1 := h_step x 0 1 (by decide)
    have h2 := h_step (Nat.div x 256) _ 256 h1
    have h3 := h_step (Nat.div (Nat.div x 256) 256) _ 65536 h2
    exact h_step (Nat.div (Nat.div (Nat.div x 256) 256) 256) _ 16777216 h3
  have h_canon_bs :
      isCanonicalScalarOfSize
        { bits := pureBswapLoop 4 x 0, sizeBytes := 4 } 4 = true :=
    isCanonicalScalarOfSize_four h_bswap_lt
  -- bb0: StorageLive(_2), then 1-step inline intrinsic bswap::<u32>(_1)
  refine PureMirModularConverges.step_stmt
    (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  refine PureMirModularConverges.call_inline_intrinsic
    (retVal := .scalar ⟨pureBswapLoop 4 x 0, 4⟩)
    (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl
    (lookupCallee_nil _ _ _ _) (by decide)
    (fun _ _ => evalDirectRustIntrinsic_bswap_u32 _ _ _ _ _ _ _ _ _ _ hx)
    rfl ?_
  -- bb1: 1-step inline intrinsic ctpop::<u32>(_2)
  refine PureMirModularConverges.call_inline_intrinsic
    (retVal := expectedBswapPopU32 x)
    (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl
    (lookupCallee_nil _ _ _ _) (by decide)
    (fun _ _ => by
      rw [← expectedBswapPopU32_def x]
      exact evalDirectRustIntrinsic_ctpop_u32 _ _ _ _ _ _ _ _ _ _ h_bswap_lt)
    rfl ?_
  exact PureMirModularConverges.return_ (fun _ h => nomatch h) rfl rfl rfl rfl rfl

/-- Modular precondition for `pureIntrinsicCallerBody`. -/
def pureIntrinsicCallerPre (args : List Value) (mem : Memory) : Prop :=
  (∃ x : Nat, x < 4294967296 ∧ args = [.scalar { bits := x, sizeBytes := 4 }]) ∧
  mem.callees = [] ∧
  mem.callStack = [] ∧
  (mem.activeCallee = none ∨ mem.activeCallee = some pureIntrinsicCallerBody) ∧
  mem.activeProtectors = []

/-- Modular postcondition for `pureIntrinsicCallerBody`. -/
def pureIntrinsicCallerPost
    (args : List Value) (_ : Memory) (retVal : Value) (_ : Memory) : Prop :=
  ∀ x : Nat,
    args = [.scalar { bits := x, sizeBytes := 4 }] →
    retVal = expectedBswapPopU32 x

/-- Non-vacuity witness for `pureIntrinsicCallerBody`'s modular precondition. -/
theorem pureIntrinsicCaller_modularPre_nonVacuous :
    NonVacuousStatefulPre pureIntrinsicCallerPre :=
  ⟨[.scalar { bits := 0x12345678, sizeBytes := 4 }],
   emptyMemory,
   ⟨0x12345678, by decide, rfl⟩,
   rfl, rfl, Or.inl rfl, rfl⟩

/--
Audited `ModularVerificationResult` for `pureIntrinsicCallerBody` against
`defaultPureRustIntrinsicContract.holdsOn`.
-/
theorem verify_pureIntrinsicCallerModular :
    ModularVerificationResult
      { body := pureIntrinsicCallerBody
        envAssumed := defaultPureRustIntrinsicContract.holdsOn
        pre := pureIntrinsicCallerPre
        post := pureIntrinsicCallerPost } := by
  refine verifyModularMir_of_pureModularExec
    defaultPureRustIntrinsicContract
    pureIntrinsicCallerBody
    pureIntrinsicCallerPre
    pureIntrinsicCallerPost
    (fun _ _ h_pre => h_pre.2)
    (fun args mem h_pre => ?_)
  rcases h_pre.1 with ⟨x, hx, rfl⟩
  refine PureMirModularConverges.mono ?_
    (pureIntrinsicCaller_modularConverges x hx mem.traitImpls)
  intro retVal h_ret _ x' h_eq
  injection h_eq with h_hd _
  injection h_hd with h_sc
  injection h_sc with hx_eq _
  subst hx_eq
  exact h_ret

/--
Sidecar stub body for a polymorphic `#[external_spec]` target
`ext::checked_inc<T>(x: u32) -> u32` (monomorphized at `T = u32`).
-/
def extCheckedIncSidecarBody : CapturedMir where
  defPath := "ext::checked_inc_spec"
  phase := .runtimePostCleanup
  role := .externalSpec "ext::checked_inc"
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := pureU32Ty, debugName := some "_0" },
    { mutability := .not, ty := pureU32Ty, debugName := some "x" }
  ]
  basicBlocks := [
    { statements := []
      terminator := { kind := .return_, span := pureAdtSpan }
      isCleanup := false }
  ]
  fnAbi := {
    args := [{ layout := u32Layout, mode := .direct }]
    ret := { layout := u32Layout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := demoCallerLayouts
  allocations := []

/--
Polymorphic `#[external_spec]` contract for `ext::checked_inc::<u32>`:
requires `x < 2^32 - 1` and returns `x + 1`.
-/
def extCheckedIncContract : MirCallContract :=
  polyExternalSpecCallContract
    "ext::checked_inc"
    [.uint .u32]
    extCheckedIncSidecarBody
    (fun args => ∃ x : Nat, x < 4294967295 ∧ args = [.scalar { bits := x, sizeBytes := 4 }])
    (fun args retVal =>
      ∀ x : Nat,
        args = [.scalar { bits := x, sizeBytes := 4 }] →
        retVal = .scalar { bits := x + 1, sizeBytes := 4 })

/--
Hybrid caller `demo::external_spec_and_poly_callee` (`argCount := 1`,
input `_1 : (u32, u32) = (x, y)` with `x < 2^32 - 1`):
- `bb0`: `StorageLive(_2, _3)`; calls `#[external_spec]` target
  `ext::checked_inc::<u32>(_1.0)` -> `_2 = x + 1`.
- `bb1`: constructs `_3 = (_2, _1.1) = (x + 1, y)`, then calls linked
  polymorphic
  callee `demo::poly_swap_pair::<u32>(_3)` in `demoCallees` -> `_0 = (y, x +
  1)`.
- `bb2`: `return`.
-/
def externalSpecAndPolyCalleeCallerBody : CapturedMir where
  defPath := "demo::external_spec_and_poly_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "_0" },
    { mutability := .not, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "pair" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "inc_x" },
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "tmp_pair" }
  ]
  basicBlocks := [
    -- bb0: StorageLive(_2, _3); _2 = ext::checked_inc::<u32>(_1.0) -> bb1
    { statements := [
        { kind := .storageLive 2, span := pureAdtSpan },
        { kind := .storageLive 3, span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "ext::checked_inc" [.uint .u32])
          [.copy { local_ := 1, projection := [.field 0 pureU32Ty] }]
          { local_ := 2, projection := [] }
          (.some 1)
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb1: _3 = (_2, _1.1); _0 = demo::poly_swap_pair::<u32>(_3) -> bb2
    { statements := [
        { kind := .assign
            { local_ := 3, projection := [] }
            (.aggregate .tuple [
              .copy { local_ := 2, projection := [] },
              .copy { local_ := 1, projection := [.field 1 pureU32Ty] }
            ])
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "demo::poly_swap_pair" [.uint .u32])
          [.copy { local_ := 3, projection := [] }]
          { local_ := 0, projection := [] }
          (.some 2)
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb2: return
    { statements := []
      terminator := { kind := .return_, span := pureAdtSpan }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [{ layout := pairU32Layout, mode := .direct }]
    ret := { layout := pairU32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := demoCallerLayouts
  allocations := []

/--
Compositional modular proof combining a 1-step `#[external_spec]` call
(`PureMirModularConverges.call_poly_external_spec`) with a 1-step linked
polymorphic callee summary (`PureMirModularConverges.call_summary`), even after
the external call may have mutated `m.borrows` or `m.globals`.
-/
theorem externalSpecAndPolyCallee_modularConverges
    (x y : Nat) (hx : x < 4294967295) :
    PureMirModularConverges
      extCheckedIncContract
      externalSpecAndPolyCalleeCallerBody
      [polySwapPairBody]
      (initPureState externalSpecAndPolyCalleeCallerBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ])
      (· = .aggregate 0 [
        .scalar { bits := y, sizeBytes := 4 },
        .scalar { bits := x + 1, sizeBytes := 4 }
      ])
      [] := by
  -- bb0: StorageLive(_2), StorageLive(_3), then 1-step #[external_spec] call
  refine PureMirModularConverges.step_stmt
    (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  refine PureMirModularConverges.step_stmt
    (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  refine PureMirModularConverges.call_poly_external_spec
    (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) rfl
    ⟨⟨x, by dsimp [scalarModulus]; omega, rfl⟩, trivial⟩
    ⟨x, hx, rfl⟩
    (Or.inl rfl)
    ?_
  rintro retVal ⟨_, h_ext_post⟩
  have h_rv : retVal = .scalar { bits := x + 1, sizeBytes := 4 } :=
    h_ext_post x rfl
  subst h_rv
  refine ⟨_, rfl, ?_⟩
  -- bb1 stmt 0: _3 = (_2, _1.1)
  refine PureMirModularConverges.step_stmt
    (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  -- bb1 terminator: 1-step linked polymorphic callee summary
  -- demo::poly_swap_pair::<u32>
  refine PureMirModularConverges.call_summary
    (maxCallDepth := 1)
    (calleeBody := polySwapPairU32Body)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl rfl
    (by decide)
    (PureMirConvergesWithCallees.of_pureMirConverges
      checkPureMir_polySwapPairU32Body
      (polySwapPairU32_pureConverges
        (.scalar { bits := x + 1, sizeBytes := 4 })
        (.scalar { bits := y, sizeBytes := 4 })))
    ?_
  rintro _ rfl
  refine ⟨_, rfl, ?_⟩
  -- bb2: return_
  exact PureMirModularConverges.return_ (fun _ h => nomatch h) rfl rfl rfl rfl rfl

/--
Non-vacuity witness for `externalSpecAndPolyCalleeCallerBody`'s precondition.
-/
theorem externalSpecAndPolyCallee_modularPre_nonVacuous :
    NonVacuousStatefulPre
      (fun args mem =>
        (∃ (x y : Nat),
          x < 4294967295 ∧
          args = [
            .aggregate 0 [
              .scalar { bits := x, sizeBytes := 4 },
              .scalar { bits := y, sizeBytes := 4 }
            ]
          ]) ∧
        mem.callStack = [] ∧
        (mem.activeCallee = none ∨
         mem.activeCallee = some externalSpecAndPolyCalleeCallerBody) ∧
        mem.activeProtectors = []) :=
  ⟨[.aggregate 0 [.scalar { bits := 41, sizeBytes := 4 }, .scalar { bits := 7, sizeBytes := 4 }]],
   emptyMemory,
   ⟨41, 7, by decide, rfl⟩,
   rfl, Or.inl rfl, rfl⟩

/--
Audited `ModularVerificationResult` for `externalSpecAndPolyCalleeCallerBody`
with linked `[polySwapPairBody]` and external `extCheckedIncContract.holdsOn`.
-/
theorem verify_externalSpecAndPolyCalleeModular :
    ModularVerificationResult
      { body := externalSpecAndPolyCalleeCallerBody
        callees := [polySwapPairBody]
        envAssumed := extCheckedIncContract.holdsOn
        pre := fun args mem =>
          (∃ (x y : Nat),
            x < 4294967295 ∧
            args = [
              .aggregate 0 [
                .scalar { bits := x, sizeBytes := 4 },
                .scalar { bits := y, sizeBytes := 4 }
              ]
            ]) ∧
          mem.callStack = [] ∧
          (mem.activeCallee = none ∨
           mem.activeCallee = some externalSpecAndPolyCalleeCallerBody) ∧
          mem.activeProtectors = []
        post := fun args _ retVal _ =>
          ∀ (x y : Nat),
            args = [
              .aggregate 0 [
                .scalar { bits := x, sizeBytes := 4 },
                .scalar { bits := y, sizeBytes := 4 }
              ]
            ] →
            retVal = .aggregate 0 [
              .scalar { bits := y, sizeBytes := 4 },
              .scalar { bits := x + 1, sizeBytes := 4 }
            ] } := by
  refine verifyModularMirWithCallees_of_pureModularExec
    extCheckedIncContract
    externalSpecAndPolyCalleeCallerBody
    [polySwapPairBody]
    _ _
    (by decide)
    (fun _ _ h_pre => h_pre.2)
    (fun args _ h_pre => ?_)
  rcases h_pre.1 with ⟨x, y, hx, rfl⟩
  refine PureMirModularConverges.mono ?_
    (externalSpecAndPolyCallee_modularConverges x y hx)
  intro retVal h_ret _ x' y' h_eq
  rcases pairU32Args_inj h_eq with ⟨rfl, rfl⟩
  exact h_ret

/-!
### 10E. Combined Modular Pipeline Witness — `combineMirCallContracts`
(`#[external_spec]` + `bswap` + `const_eval_select(ctpop)` + `assert` +
`exact_div` + Linked Polymorphic `tailCall`)
-/

/--
Combined rely contract pairing `defaultPureRustIntrinsicContract` and
`extCheckedIncContract` via `combineMirCallContracts`.
-/
def combinedIntrinsicAndExtContract : MirCallContract :=
  combineMirCallContracts defaultPureRustIntrinsicContract extCheckedIncContract

/--
Combined modular caller `demo::combined_modular_pipeline` (`argCount := 1`,
input `_1 : (u32, u32) = (x, y)` with `x < 2^31`):
- `bb0`: `StorageLive(_2.._9)`; calls `#[external_spec]` target
  `ext::checked_inc::<u32>(_1.0)` -> `_2 = x + 1`.
- `bb1`: calls `core::intrinsics::bswap::<u32>(_2)` -> `_3`.
- `bb2`: packs `_5 = (_3,)` and calls `core::intrinsics::const_eval_select`
  selecting `core::intrinsics::ctpop::<u32>` at runtime -> `_4 =
  ctpop::<u32>(bswap::<u32>(x + 1))`.
- `bb3`: computes `_6 = (_2 == _2)` and executes `TerminatorKind.assert` ->
  `bb4`.
- `bb4`: computes `_7 = _1.0 * 2` and calls inline
  `core::intrinsics::exact_div::<u32>(_7, 2)` -> `_8 = x`.
- `bb5`: constructs `_9 = (_4, _8)` and executes `TerminatorKind.tailCall` to
  linked polymorphic `demo::poly_swap_pair::<u32>(_9)` -> `(x,
  ctpop::<u32>(bswap::<u32>(x + 1)))`.
-/
def combinedModularPipelineBody : CapturedMir where
  defPath := "demo::combined_modular_pipeline"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "_0" },
    { mutability := .not, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "pair" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "inc_x" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "bswap_inc" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "pop_val" },
    { mutability := .mut, ty := { kind := .tuple [.uint .u32], layoutIdx := 0 }, debugName := some "arg_tup" },
    { mutability := .mut, ty := { kind := .bool, layoutIdx := 0 }, debugName := some "cond" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "doubled_x" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "halved_x" },
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "final_pair" }
  ]
  basicBlocks := [
    -- bb0: StorageLive(_2.._9); _2 = ext::checked_inc::<u32>(_1.0) -> bb1
    { statements := [
        { kind := .storageLive 2, span := pureAdtSpan },
        { kind := .storageLive 3, span := pureAdtSpan },
        { kind := .storageLive 4, span := pureAdtSpan },
        { kind := .storageLive 5, span := pureAdtSpan },
        { kind := .storageLive 6, span := pureAdtSpan },
        { kind := .storageLive 7, span := pureAdtSpan },
        { kind := .storageLive 8, span := pureAdtSpan },
        { kind := .storageLive 9, span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "ext::checked_inc" [.uint .u32])
          [.copy { local_ := 1, projection := [.field 0 pureU32Ty] }]
          { local_ := 2, projection := [] }
          (.some 1)
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb1: _3 = core::intrinsics::bswap::<u32>(_2) -> bb2
    { statements := []
      terminator := {
        kind := .call
          (fnItemOperand "core::intrinsics::bswap" [.uint .u32])
          [.copy { local_ := 2, projection := [] }]
          { local_ := 3, projection := [] }
          (.some 2)
          .unreachable
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb2: _5 = (_3,); _4 = const_eval_select((_3,), ctpop::<u32>,
    -- ctpop::<u32>) -> bb3
    { statements := [
        { kind := .assign
            { local_ := 5, projection := [] }
            (.aggregate .tuple [.copy { local_ := 3, projection := [] }])
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "core::intrinsics::const_eval_select" [
            .tuple [.uint .u32],
            .fnDef "core::intrinsics::ctpop" [.uint .u32],
            .fnDef "core::intrinsics::ctpop" [.uint .u32],
            .uint .u32
          ])
          [ .copy { local_ := 5, projection := [] },
            fnItemOperand "core::intrinsics::ctpop" [.uint .u32],
            fnItemOperand "core::intrinsics::ctpop" [.uint .u32] ]
          { local_ := 4, projection := [] }
          (.some 3)
          .unreachable
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb3: _6 = (_2 == _2); assert(_6 == true) -> bb4
    { statements := [
        { kind := .assign
            { local_ := 6, projection := [] }
            (.binaryOp .eq
              (.copy { local_ := 2, projection := [] })
              (.copy { local_ := 2, projection := [] }))
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .assert
          (.copy { local_ := 6, projection := [] })
          true
          4
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb4: _7 = _1.0 * 2; _8 = core::intrinsics::exact_div::<u32>(_7, 2) -> bb5
    { statements := [
        { kind := .assign
            { local_ := 7, projection := [] }
            (.binaryOp .mul
              (.copy { local_ := 1, projection := [.field 0 pureU32Ty] })
              (u32ConstOperand 2))
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "core::intrinsics::exact_div" [.uint .u32])
          [.copy { local_ := 7, projection := [] }, u32ConstOperand 2]
          { local_ := 8, projection := [] }
          (.some 5)
          .unreachable
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb5: _9 = (_4, _8); tailCall demo::poly_swap_pair::<u32>(_9)
    { statements := [
        { kind := .assign
            { local_ := 9, projection := [] }
            (.aggregate .tuple [
              .copy { local_ := 4, projection := [] },
              .copy { local_ := 8, projection := [] }
            ])
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .tailCall
          (fnItemOperand "demo::poly_swap_pair" [.uint .u32])
          [.copy { local_ := 9, projection := [] }]
        span := pureAdtSpan
      }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [{ layout := pairU32Layout, mode := .direct }]
    ret := { layout := pairU32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := demoCallerLayouts
  allocations := []

@[irreducible]
private def bswapScalarU32 (v : Nat) : ScalarInt :=
  ⟨pureBswapLoop 4 v 0, 4⟩

private theorem bswapScalarU32_def (v : Nat) :
    ({ bits := pureBswapLoop 4 v 0, sizeBytes := 4 } : ScalarInt) =
      bswapScalarU32 v := by
  unfold bswapScalarU32
  rfl

private theorem evalConstEvalSelect_ctpop_u32 (v : ScalarInt)
    (hv : isCanonicalScalarOfSize v 4 = true) :
    evalPureRustIntrinsicWithRuntime (fun _ _ _ => none) .constEvalSelect
      [.tuple [.uint .u32],
       .fnDef "core::intrinsics::ctpop" [.uint .u32],
       .fnDef "core::intrinsics::ctpop" [.uint .u32],
       .uint .u32]
      [.aggregate 0 [.scalar v], .unit, .unit] 8 true =
      some (.scalar ⟨pureCtpopLoop 32 v.bits, 4⟩) := by
  have h_unp :
      unpackConstEvalSelectWithElemTys?
        [.tuple [.uint .u32],
         .fnDef "core::intrinsics::ctpop" [.uint .u32],
         .fnDef "core::intrinsics::ctpop" [.uint .u32],
         .uint .u32]
        [.aggregate 0 [.scalar v], .unit, .unit] =
      some ([.uint .u32], "core::intrinsics::ctpop", [.uint .u32], [.scalar v]) := rfl
  have h_cls : classifyPureRustIntrinsic? "core::intrinsics::ctpop" = some .ctpop := rfl
  dsimp only [evalPureRustIntrinsicWithRuntime]
  rw [h_unp]
  dsimp only
  rw [h_cls]
  change (if isCanonicalScalarOfSize v 4 then some (Value.scalar ⟨pureCtpopLoop 32 v.bits, 4⟩) else none) = _
  rw [hv]
  rfl

private theorem pureBswapLoop_four_lt (v : Nat) :
    pureBswapLoop 4 v 0 < 4294967296 := by
  have h_step (u a bound : Nat) (ha : a < bound) :
      a * 256 + Nat.mod u 256 < bound * 256 := by
    have hm : Nat.mod u 256 < 256 := Nat.mod_lt u (by decide)
    omega
  dsimp only [pureBswapLoop]
  have h1 := h_step v 0 1 (by decide)
  have h2 := h_step (Nat.div v 256) _ 256 h1
  have h3 := h_step (Nat.div (Nat.div v 256) 256) _ 65536 h2
  exact h_step (Nat.div (Nat.div (Nat.div v 256) 256) 256) _ 16777216 h3

private theorem checkPureMirWithCallees_polySwapPairU32 :
    checkPureMirWithCallees [polySwapPairBody] polySwapPairU32Body 1 [] = true := by
  decide

private theorem combinedModularPipeline_from_bb3
    (x y : Nat) (hx : x < 2147483648) :
    PureMirModularConverges
      combinedIntrinsicAndExtContract
      combinedModularPipelineBody
      [polySwapPairBody]
      { bb := 3
        stmtIdx := 0
        env := [
          .uninit,
          .init (.aggregate 0 [
            .scalar { bits := x, sizeBytes := 4 },
            .scalar { bits := y, sizeBytes := 4 }
          ]),
          .init (.scalar { bits := x + 1, sizeBytes := 4 }),
          .init (.scalar (bswapScalarU32 (x + 1))),
          .init (expectedBswapPopU32 (x + 1)),
          .init (.aggregate 0 [.scalar (bswapScalarU32 (x + 1))]),
          .uninit,
          .uninit,
          .uninit,
          .uninit
        ] }
      (· = .aggregate 0 [
        .scalar { bits := x, sizeBytes := 4 },
        expectedBswapPopU32 (x + 1)
      ])
      [] := by
  -- bb3 stmt 0: _6 = (_2 == _2) (evaluates to bool true = 1)
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  -- bb3 terminator: assert(_6 == true) -> bb4
  refine PureMirModularConverges.step_assert
    (fun _ h => nomatch h) rfl rfl rfl rfl rfl
    (fun _ => ?_)
    (fun _ => Or.inl rfl)
  -- bb4 stmt 0: _7 = _1.0 * 2
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  -- bb4 terminator: inline core::intrinsics::exact_div::<u32>(_7, 2) -> bb5
  refine PureMirModularConverges.call_exact_div
    (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl
    (evalExactDiv_double_u32 hx) rfl ?_
  -- bb5 stmt 0: _9 = (_4, _8)
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  -- bb5 terminator: linked polymorphic tailCall demo::poly_swap_pair::<u32>(_9)
  refine PureMirModularConverges.tailCall_summary
    (maxCallDepth := 1)
    (calleeBody := polySwapPairU32Body)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl
    checkPureMirWithCallees_polySwapPairU32
    (PureMirConvergesWithCallees.of_pureMirConverges
      checkPureMir_polySwapPairU32Body
      (polySwapPairU32_pureConverges
        (expectedBswapPopU32 (x + 1))
        (.scalar { bits := x, sizeBytes := 4 })))
    (fun _ h => h)

private theorem combinedModularPipeline_from_bb2
    (x y : Nat) (hx : x < 2147483648) :
    PureMirModularConverges
      combinedIntrinsicAndExtContract
      combinedModularPipelineBody
      [polySwapPairBody]
      { bb := 2
        stmtIdx := 0
        env := [
          .uninit,
          .init (.aggregate 0 [
            .scalar { bits := x, sizeBytes := 4 },
            .scalar { bits := y, sizeBytes := 4 }
          ]),
          .init (.scalar { bits := x + 1, sizeBytes := 4 }),
          .init (.scalar (bswapScalarU32 (x + 1))),
          .uninit,
          .uninit,
          .uninit,
          .uninit,
          .uninit,
          .uninit
        ] }
      (· = .aggregate 0 [
        .scalar { bits := x, sizeBytes := 4 },
        expectedBswapPopU32 (x + 1)
      ])
      [] := by
  -- bb2 stmt 0: _5 = (_3,)
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  -- bb2 terminator: const_eval_select((_3,), ctpop::<u32>, ctpop::<u32>)
  refine PureMirModularConverges.call_inline_intrinsic
    (retVal := expectedBswapPopU32 (x + 1))
    (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
    (fun m hm => by
      have h_sz_bs : (bswapScalarU32 (x + 1)).sizeBytes = 4 := by
        rw [← bswapScalarU32_def]
      have h_bits_bs : (bswapScalarU32 (x + 1)).bits = pureBswapLoop 4 (x + 1) 0 := by
        rw [← bswapScalarU32_def]
      have h_lt_bs : (bswapScalarU32 (x + 1)).bits < 4294967296 := by
        rw [h_bits_bs]
        exact pureBswapLoop_four_lt (x + 1)
      rw [← expectedBswapPopU32_def (x + 1), ← h_bits_bs]
      exact evalDirectRustIntrinsic_constEvalSelect_ctpop_u32
        _ _ _ _ _ _ _ _ _ _ _ rfl rfl
        (by dsimp only [PureState.toMachineState]; rw [hm.1, hm.2.1]; rfl)
        h_sz_bs h_lt_bs)
    rfl
    (combinedModularPipeline_from_bb3 x y hx)

/--
Compositional modular proof for `combinedModularPipelineBody`, combining
`call_poly_external_spec_sub`, `call_inline_intrinsic` (`bswap` +
`const_eval_select(ctpop)`), `step_assert`, `call_exact_div`, and
`tailCall_summary` in a single caller under `combinedIntrinsicAndExtContract`.
-/
theorem combinedModularPipeline_modularConverges
    (x y : Nat) (hx : x < 2147483648) :
    PureMirModularConverges
      combinedIntrinsicAndExtContract
      combinedModularPipelineBody
      [polySwapPairBody]
      (initPureState combinedModularPipelineBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ])
      (· = .aggregate 0 [
        .scalar { bits := x, sizeBytes := 4 },
        expectedBswapPopU32 (x + 1)
      ])
      [] := by
  have hx1_lt : x + 1 < 4294967296 :=
    Nat.lt_trans (Nat.succ_lt_succ hx) (by decide)
  -- bb0: StorageLive(_2.._9)
  have h_init :
      initPureState combinedModularPipelineBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ] = {
        bb := 0
        stmtIdx := 0
        env := [
          .uninit,
          .init (.aggregate 0 [
            .scalar { bits := x, sizeBytes := 4 },
            .scalar { bits := y, sizeBytes := 4 }
          ]),
          .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead
        ]
      } := rfl
  rw [h_init]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  -- bb0 terminator: ext::checked_inc::<u32>(_1.0) via call_poly_external_spec_sub
  refine PureMirModularConverges.call_poly_external_spec_sub
    (targetDefPath := "ext::checked_inc")
    (expectedTypeArgs := [.uint .u32])
    (sidecarBody := extCheckedIncSidecarBody)
    (extraPre := fun args =>
      ∃ x : Nat, x < 4294967295 ∧ args = [.scalar { bits := x, sizeBytes := 4 }])
    (extraPost := fun args retVal =>
      ∀ x : Nat,
        args = [.scalar { bits := x, sizeBytes := 4 }] →
        retVal = .scalar { bits := x + 1, sizeBytes := 4 })
    (MirCallContract.Subsumes.combine_right
      defaultPureRustIntrinsicContract extCheckedIncContract)
    (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    ⟨⟨x, Nat.lt_trans hx (by decide), rfl⟩, trivial⟩
    ⟨x, Nat.lt_trans hx (by decide), rfl⟩
    (Or.inl rfl)
    ?_
    rfl
  rintro retVal ⟨_, h_ext_post⟩
  have h_rv : retVal = .scalar { bits := x + 1, sizeBytes := 4 } :=
    h_ext_post x rfl
  subst h_rv
  refine ⟨_, rfl, ?_⟩
  -- bb1: core::intrinsics::bswap::<u32>(_2) via call_inline_intrinsic
  refine PureMirModularConverges.call_inline_intrinsic
    (retVal := .scalar (bswapScalarU32 (x + 1)))
    (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl rfl rfl
    ?_
    rfl
    (combinedModularPipeline_from_bb2 x y hx)
  intro _ _
  rw [← bswapScalarU32_def]
  exact evalDirectRustIntrinsic_bswap_u32 _ _ _ _ _ _ _ _ _ _ hx1_lt

/-- Non-vacuity witness for `combinedModularPipelineBody`'s precondition. -/
theorem combinedModularPipeline_modularPre_nonVacuous :
    NonVacuousStatefulPre
      (fun args mem =>
        (∃ (x y : Nat),
          x < 2147483648 ∧
          args = [
            .aggregate 0 [
              .scalar { bits := x, sizeBytes := 4 },
              .scalar { bits := y, sizeBytes := 4 }
            ]
          ]) ∧
        mem.callStack = [] ∧
        (mem.activeCallee = none ∨
         mem.activeCallee = some combinedModularPipelineBody) ∧
        mem.activeProtectors = []) :=
  ⟨[.aggregate 0 [.scalar { bits := 19, sizeBytes := 4 }, .scalar { bits := 3, sizeBytes := 4 }]],
   emptyMemory,
   ⟨19, 3, by decide, rfl⟩,
   rfl, Or.inl rfl, rfl⟩

/--
Audited `ModularVerificationResult` for `combinedModularPipelineBody` against
`combinedIntrinsicAndExtContract.holdsOn`.
-/
theorem verify_combinedModularPipeline :
    ModularVerificationResult
      { body := combinedModularPipelineBody
        callees := [polySwapPairBody]
        envAssumed := combinedIntrinsicAndExtContract.holdsOn
        pre := fun args mem =>
          (∃ (x y : Nat),
            x < 2147483648 ∧
            args = [
              .aggregate 0 [
                .scalar { bits := x, sizeBytes := 4 },
                .scalar { bits := y, sizeBytes := 4 }
              ]
            ]) ∧
          mem.callStack = [] ∧
          (mem.activeCallee = none ∨
           mem.activeCallee = some combinedModularPipelineBody) ∧
          mem.activeProtectors = []
        post := fun args _ retVal _ =>
          ∀ (x y : Nat),
            args = [
              .aggregate 0 [
                .scalar { bits := x, sizeBytes := 4 },
                .scalar { bits := y, sizeBytes := 4 }
              ]
            ] →
            retVal = .aggregate 0 [
              .scalar { bits := x, sizeBytes := 4 },
              expectedBswapPopU32 (x + 1)
            ] } := by
  refine verifyModularMirWithCallees_of_pureModularExec
    combinedIntrinsicAndExtContract
    combinedModularPipelineBody
    [polySwapPairBody]
    _ _
    (by decide)
    (fun _ _ h_pre => h_pre.2)
    (fun args _ h_pre => ?_)
  rcases h_pre.1 with ⟨x, y, hx, rfl⟩
  refine PureMirModularConverges.mono ?_
    (combinedModularPipeline_modularConverges x y hx)
  intro retVal h_ret _ x' y' h_eq
  rcases pairU32Args_inj h_eq with ⟨rfl, rfl⟩
  exact h_ret

/-!
### 10F. `TraitImplEntry` Dispatch, Multi-Monomorphization (`u32` + `u64`),
Linked `tailCall`, & Computable `evalPureMirWithCallees` Witness
-/

/--
Concrete `u32` trait-method implementation body `demo::u32_step_impl`
(`<u32 as demo::StepTrait>::step`), returning `_1 + 1` (wrapping modulo `2^32`).
-/
def u32StepImplBody : CapturedMir where
  defPath := "demo::u32_step_impl"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := pureU32Ty, debugName := some "_0" },
    { mutability := .not, ty := pureU32Ty, debugName := some "x" }
  ]
  basicBlocks := [
    { statements := [
        { kind := .assign
            { local_ := 0, projection := [] }
            (.binaryOp .add
              (.copy { local_ := 1, projection := [] })
              (u32ConstOperand 1))
          span := pureAdtSpan }
      ]
      terminator := { kind := .return_, span := pureAdtSpan }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [{ layout := u32Layout, mode := .direct }]
    ret := { layout := u32Layout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := demoCallerLayouts
  allocations := []

/--
Registered `TraitImplEntry` associating `<u32 as demo::StepTrait>::step` with
`demo::u32_step_impl`.
-/
def demoStepTraitImpl : TraitImplEntry where
  traitRef := { defPath := "demo::StepTrait::step", args := [.uint .u32] }
  implPath := "demo::u32_step_impl"

theorem checkPureMir_u32StepImplBody : checkPureMir u32StepImplBody = true := by
  decide

theorem u32StepImpl_pureConverges (x : Nat) :
    PureMirConverges u32StepImplBody
      (initPureState u32StepImplBody [.scalar { bits := x, sizeBytes := 4 }])
      (· = .scalar { bits := wrapScalarBits (Nat.add x 1) (scalarModulus 4), sizeBytes := 4 }) :=
  ⟨4, rfl⟩

/--
Layout table supporting both `(u32, u32)` and `(u64, u64)` pairs in a single
caller (`[u32Layout, pairU32Layout, u64Layout, pairU64Layout]`).
-/
def multiMonoCallerLayouts : LayoutTable where
  pointerBits := 64
  isLittleEndian := true
  entries := [u32Layout, pairU32Layout, u64Layout, pairU64Layout]

/--
Caller `demo::trait_and_tail_multi_mono_caller` (`argCount := 2`,
`_1 : (u32, u32) = (x, y)`, `_2 : (u64, u64) = (z, w)`, with
`traitImpls := [demoStepTraitImpl]`):
- `bb0`: calls `demo::poly_swap_pair::<u32>(_1)` -> `_3 = (y, x)`.
- `bb1`: calls `demo::poly_swap_pair::<u64>(_2)` -> `_4 = (w, z)` (second
  monomorphization of `polySwapPairBody` in the same caller!).
- `bb2`: dispatches trait method `demo::StepTrait::step::<u32>(_3.1)` via
  `TraitImplEntry` (`demoStepTraitImpl` -> `demo::u32_step_impl`) -> `_5 =
  (x + 1) % 2^32`.
- `bb3`: executes `TerminatorKind.tailCall` to trait method
  `demo::StepTrait::step::<u32>(_5)` -> `((x + 1) % 2^32 + 1) % 2^32`.
-/
def traitAndTailMultiMonoCallerBody : CapturedMir where
  defPath := "demo::trait_and_tail_multi_mono_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [
    { mutability := .mut, ty := pureU32Ty, debugName := some "_0" },
    { mutability := .not, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "pair32" },
    { mutability := .not, ty := { kind := .tuple [.uint .u64, .uint .u64], layoutIdx := 3 }, debugName := some "pair64" },
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "sw32" },
    { mutability := .mut, ty := { kind := .tuple [.uint .u64, .uint .u64], layoutIdx := 3 }, debugName := some "sw64" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "step1" }
  ]
  basicBlocks := [
    -- bb0: StorageLive(_3, _4, _5); _3 = demo::poly_swap_pair::<u32>(_1) -> bb1
    { statements := [
        { kind := .storageLive 3, span := pureAdtSpan },
        { kind := .storageLive 4, span := pureAdtSpan },
        { kind := .storageLive 5, span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "demo::poly_swap_pair" [.uint .u32])
          [.copy { local_ := 1, projection := [] }]
          { local_ := 3, projection := [] }
          (.some 1)
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb1: _4 = demo::poly_swap_pair::<u64>(_2) -> bb2
    { statements := []
      terminator := {
        kind := .call
          (fnItemOperand "demo::poly_swap_pair" [.uint .u64])
          [.copy { local_ := 2, projection := [] }]
          { local_ := 4, projection := [] }
          (.some 2)
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb2: _5 = <u32 as demo::StepTrait>::step(_3.1) -> bb3
    { statements := []
      terminator := {
        kind := .call
          (fnItemOperand "demo::StepTrait::step" [.uint .u32])
          [.copy { local_ := 3, projection := [.field 1 pureU32Ty] }]
          { local_ := 5, projection := [] }
          (.some 3)
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb3: tailCall <u32 as demo::StepTrait>::step(_5)
    { statements := []
      terminator := {
        kind := .tailCall
          (fnItemOperand "demo::StepTrait::step" [.uint .u32])
          [.copy { local_ := 5, projection := [] }]
        span := pureAdtSpan
      }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [
      { layout := pairU32Layout, mode := .direct },
      { layout := pairU64Layout, mode := .direct }
    ]
    ret := { layout := u32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := multiMonoCallerLayouts
  allocations := []
  traitImpls := [demoStepTraitImpl]

def traitMultiMonoCallees : List CapturedMir :=
  [polySwapPairBody, u32StepImplBody]

theorem checkPureMirWithCallees_traitAndTailMultiMono :
    checkPureMirWithCallees traitMultiMonoCallees
      traitAndTailMultiMonoCallerBody 2 [demoStepTraitImpl] = true := by
  decide

/--
Compositional 4-step proof of `traitAndTailMultiMonoCallerBody` exercising
`u32` + `u64` multi-monomorphization of `polySwapPairBody`, `TraitImplEntry`
dispatch (`<u32 as demo::StepTrait>::step -> demo::u32_step_impl`), and
`PureMirConverges.tailCall_leaf_summary`.
-/
theorem traitAndTailMultiMonoCaller_compositional (x y z w : Nat) :
    PureMirConvergesWithCallees traitAndTailMultiMonoCallerBody
      traitMultiMonoCallees
      (initPureState traitAndTailMultiMonoCallerBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ],
        .aggregate 0 [
          .scalar { bits := z, sizeBytes := 8 },
          .scalar { bits := w, sizeBytes := 8 }
        ]
      ])
      (· = .scalar {
        bits := wrapScalarBits
          (Nat.add (wrapScalarBits (Nat.add x 1) (scalarModulus 4)) 1)
          (scalarModulus 4)
        sizeBytes := 4
      })
      [demoStepTraitImpl] := by
  refine PureMirConvergesWithCallees.step ⟨rfl, ?_⟩
  refine PureMirConvergesWithCallees.step ⟨rfl, ?_⟩
  refine PureMirConvergesWithCallees.step ⟨rfl, ?_⟩
  -- 1. demo::poly_swap_pair::<u32>(_1)
  refine PureMirConverges.call_leaf_summary
    (maxCallDepth := 2)
    (calleeBody := polySwapPairU32Body)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl
    checkPureMir_polySwapPairU32Body
    (polySwapPairU32_pureConverges
      (.scalar { bits := x, sizeBytes := 4 })
      (.scalar { bits := y, sizeBytes := 4 }))
    ?_
  rintro _ rfl
  refine ⟨_, rfl, ?_⟩
  -- 2. demo::poly_swap_pair::<u64>(_2)
  refine PureMirConverges.call_leaf_summary
    (maxCallDepth := 2)
    (calleeBody := polySwapPairU64Body)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl
    checkPureMir_polySwapPairU64Body
    (polySwapPairU64_pureConverges
      (.scalar { bits := z, sizeBytes := 8 })
      (.scalar { bits := w, sizeBytes := 8 }))
    ?_
  rintro _ rfl
  refine ⟨_, rfl, ?_⟩
  -- 3. TraitImplEntry dispatch <u32 as demo::StepTrait>::step(_3.1)
  refine PureMirConverges.call_leaf_summary
    (maxCallDepth := 2)
    (calleeBody := u32StepImplBody)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl
    checkPureMir_u32StepImplBody
    (u32StepImpl_pureConverges x)
    ?_
  rintro _ rfl
  refine ⟨_, rfl, ?_⟩
  -- 4. TraitImplEntry tailCall <u32 as demo::StepTrait>::step(_5)
  exact PureMirConverges.tailCall_leaf_summary
    (maxCallDepth := 2)
    (calleeBody := u32StepImplBody)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl
    checkPureMir_u32StepImplBody
    (u32StepImpl_pureConverges (wrapScalarBits (Nat.add x 1) (scalarModulus 4)))
    (fun _ h => h)

/--
Zero-step computable evaluation witness for `traitAndTailMultiMonoCallerBody`
via `pureMirConvergesWithCallees_of_evalPureMirWithCallees` (`x = 40` -> `42`).
-/
theorem traitAndTailMultiMonoCaller_evalConcrete :
    PureMirConvergesWithCallees traitAndTailMultiMonoCallerBody
      traitMultiMonoCallees
      (initPureState traitAndTailMultiMonoCallerBody [
        .aggregate 0 [
          .scalar { bits := 40, sizeBytes := 4 },
          .scalar { bits := 7, sizeBytes := 4 }
        ],
        .aggregate 0 [
          .scalar { bits := 100, sizeBytes := 8 },
          .scalar { bits := 200, sizeBytes := 8 }
        ]
      ])
      (· = .scalar { bits := 42, sizeBytes := 4 })
      [demoStepTraitImpl] :=
  pureMirConvergesWithCallees_of_evalPureMirWithCallees
    checkPureMirWithCallees_traitAndTailMultiMono
    (fuel := 32)
    rfl

/-!
### 10G. Higher-Order Local Zero-Sized Function-Item & Callee-Backed
`const_eval_select` + Diverging Panic + External Intrinsic `tailCall` Witnesses
-/

/-- Zero-sized layout (`0` bytes) for function-item types (`RigidTy.fnDef`). -/
def zstFnItemLayout : TypeLayout :=
  Option.getD
    (RigidTy.computeLayout 64 [] [] none (.fnDef "demo::poly_swap_pair" [.uint .u32]))
    u32Layout

/-- Function-item `Ty` for `demo::poly_swap_pair::<u32>` at layout slot `2`. -/
def polySwapU32FnItemTy : Ty :=
  { kind := .fnDef "demo::poly_swap_pair" [.uint .u32], layoutIdx := 2 }

/--
Caller layout table `[u32Layout, pairU32Layout, zstFnItemLayout]` supporting
`u32`, `(u32, u32)`, and zero-sized `fnDef` local variables.
-/
def higherOrderCallerLayouts : LayoutTable where
  pointerBits := 64
  isLittleEndian := true
  entries := [u32Layout, pairU32Layout, zstFnItemLayout]

/--
Higher-order caller `demo::higher_order_fn_item_caller` (`argCount := 2`):
- `_1` has zero-sized function-item type `RigidTy.fnDef "demo::poly_swap_pair"
  [.uint .u32]` (`Value.unit`),
- `_2` has type `(u32, u32)`,
- `bb0` copies `_1` into local `_3` and invokes `TerminatorKind.call` via
  `Operand.move _3` (`extractCalleeDefPath? = none`!), writing `_4 = (y, x)`,
- `bb1` invokes `TerminatorKind.tailCall` via `Operand.copy _1`
  (`extractCalleeDefPath? = none`!), returning `(x, y)`.
-/
def higherOrderFnItemCallerBody : CapturedMir where
  defPath := "demo::higher_order_fn_item_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "_0" },
    { mutability := .not, ty := polySwapU32FnItemTy, debugName := some "f" },
    { mutability := .not, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "pair" },
    { mutability := .mut, ty := polySwapU32FnItemTy, debugName := some "f_local" },
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "swapped" }
  ]
  basicBlocks := [
    -- bb0: StorageLive(_3); StorageLive(_4); _3 = Copy(_1);
    --      _4 = (Move(_3))(_2) -> bb1
    { statements := [
        { kind := .storageLive 3, span := pureAdtSpan },
        { kind := .storageLive 4, span := pureAdtSpan },
        { kind := .assign
            { local_ := 3, projection := [] }
            (.use (.copy { local_ := 1, projection := [] }))
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (.move { local_ := 3, projection := [] })
          [.copy { local_ := 2, projection := [] }]
          { local_ := 4, projection := [] }
          (.some 1)
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb1: tailcall (Copy(_1))(_4)
    { statements := []
      terminator := {
        kind := .tailCall
          (.copy { local_ := 1, projection := [] })
          [.copy { local_ := 4, projection := [] }]
        span := pureAdtSpan
      }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [
      { layout := zstFnItemLayout, mode := .ignore },
      { layout := pairU32Layout, mode := .direct }
    ]
    ret := { layout := pairU32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := higherOrderCallerLayouts
  allocations := []

/--
`checkPureMirWithCallees` accepts `higherOrderFnItemCallerBody` at `maxCallDepth =
2` even though both `call` and `tailCall` invoke local `Operand.move` /
`Operand.copy` function-item slots (`extractCalleeDefPath? = none`).
-/
theorem checkPureMirWithCallees_higherOrderFnItemCaller :
    checkPureMirWithCallees [polySwapPairBody] higherOrderFnItemCallerBody 2 [] =
      true := by
  decide

/--
Symbolic compositional proof for `higherOrderFnItemCallerBody` across all
`x y : Nat`, discharging the `Operand.move _3` call via
`PureMirConverges.call_leaf_summary` and the `Operand.copy _1` tail call via
`PureMirConverges.tailCall_leaf_summary`.
-/
theorem higherOrderFnItemCaller_compositional (x y : Nat) :
    PureMirConvergesWithCallees higherOrderFnItemCallerBody [polySwapPairBody]
      (initPureState higherOrderFnItemCallerBody [
        .unit,
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ])
      (· = .aggregate 0 [
        .scalar { bits := x, sizeBytes := 4 },
        .scalar { bits := y, sizeBytes := 4 }
      ])
      [] := by
  -- bb0: StorageLive(_3), StorageLive(_4), _3 = Copy(_1)
  refine PureMirConvergesWithCallees.step ⟨rfl, ?_⟩
  refine PureMirConvergesWithCallees.step ⟨rfl, ?_⟩
  refine PureMirConvergesWithCallees.step ⟨rfl, ?_⟩
  -- bb0 terminator: (Move(_3))(_2) -> polySwapPairU32Body
  refine PureMirConverges.call_leaf_summary
    (maxCallDepth := 2)
    (calleeBody := polySwapPairU32Body)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl
    checkPureMir_polySwapPairU32Body
    (polySwapPairU32_pureConverges
      (.scalar { bits := x, sizeBytes := 4 })
      (.scalar { bits := y, sizeBytes := 4 }))
    ?_
  rintro _ rfl
  refine ⟨_, rfl, ?_⟩
  -- bb1 terminator: tailCall (Copy(_1))(_4) -> polySwapPairU32Body
  exact PureMirConverges.tailCall_leaf_summary
    (maxCallDepth := 2)
    (calleeBody := polySwapPairU32Body)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl
    checkPureMir_polySwapPairU32Body
    (polySwapPairU32_pureConverges
      (.scalar { bits := y, sizeBytes := 4 })
      (.scalar { bits := x, sizeBytes := 4 }))
    (fun _ h => h)

/--
Operational `MirWpConverges` witness on `initMachineStateWithCallees` for
`higherOrderFnItemCallerBody`.
-/
theorem higherOrderFnItemCaller_mirWpConverges (x y : Nat) :
    MirWpConverges higherOrderFnItemCallerBody
      (initMachineStateWithCallees higherOrderFnItemCallerBody [
        .unit,
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ] [polySwapPairBody])
      (mirNormalPost
        (fun retVal mem' =>
          ActiveRootMemory higherOrderFnItemCallerBody
            (initMachineStateWithCallees higherOrderFnItemCallerBody [
              .unit,
              .aggregate 0 [
                .scalar { bits := x, sizeBytes := 4 },
                .scalar { bits := y, sizeBytes := 4 }
              ]
            ] [polySwapPairBody]).memory mem' ∧
          retVal = .aggregate 0 [
            .scalar { bits := x, sizeBytes := 4 },
            .scalar { bits := y, sizeBytes := 4 }
          ])) :=
  mirWpConverges_of_pureExecWithCallees_init
    checkPureMirWithCallees_higherOrderFnItemCaller
    (higherOrderFnItemCaller_compositional x y)

/--
Zero-step concrete evaluation witness for `higherOrderFnItemCallerBody` via
`pureMirConvergesWithCallees_of_evalPureMirWithCallees`.
-/
theorem higherOrderFnItemCaller_evalConcrete :
    PureMirConvergesWithCallees higherOrderFnItemCallerBody [polySwapPairBody]
      (initPureState higherOrderFnItemCallerBody [
        .unit,
        .aggregate 0 [
          .scalar { bits := 17, sizeBytes := 4 },
          .scalar { bits := 99, sizeBytes := 4 }
        ]
      ])
      (· = .aggregate 0 [
        .scalar { bits := 17, sizeBytes := 4 },
        .scalar { bits := 99, sizeBytes := 4 }
      ])
      [] :=
  pureMirConvergesWithCallees_of_evalPureMirWithCallees
    checkPureMirWithCallees_higherOrderFnItemCaller
    (fuel := 16)
    rfl

/--
Modular caller `demo::callee_const_eval_and_intrinsic_tail` (`argCount := 1`):
- Input `_1 : (u32, u32) = (x, y)`.
- `bb0`: invokes `core::intrinsics::const_eval_select` selecting polymorphic
  Rust helper `demo::poly_swap_pair::<u32>` on `(_1,)` (unpacked via `((u32,
  u32),)` 1-tuple), evaluated through `calleeRuntimeEval` -> `_3 = (y, x)`.
- `bb1`: `switchInt(_3.0)` (testing whether `y == 0`):
  - `y == 0` (`bb2`): invokes diverging `core::panicking::panic` (`target =
    .none`, `unwind = .continue_`), discharged via `call_diverging_panic`.
  - `y != 0` (`bb3`): invokes external `TerminatorKind.tailCall` to
    `core::intrinsics::ctpop::<u32>(_3.0)`, discharged via
    `tailCall_intrinsic_sub`.
-/
def calleeBackedConstEvalAndIntrinsicTailBody : CapturedMir where
  defPath := "demo::callee_const_eval_and_intrinsic_tail"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := pureU32Ty, debugName := some "_0" },
    { mutability := .not, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "pair" },
    { mutability := .mut, ty := { kind := .tuple [.tuple [.uint .u32, .uint .u32]], layoutIdx := 1 }, debugName := some "arg_tup" },
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "swapped" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "first" },
    { mutability := .mut, ty := { kind := .never, layoutIdx := 2 }, debugName := some "never_dst" }
  ]
  basicBlocks := [
    -- bb0: _2 = (_1,); _3 = const_eval_select(_2, poly_swap_pair::<u32>,
    --      poly_swap_pair::<u32>) -> bb1
    { statements := [
        { kind := .storageLive 2, span := pureAdtSpan },
        { kind := .storageLive 3, span := pureAdtSpan },
        { kind := .assign
            { local_ := 2, projection := [] }
            (.aggregate .tuple [.copy { local_ := 1, projection := [] }])
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "core::intrinsics::const_eval_select" [
            .tuple [.tuple [.uint .u32, .uint .u32]],
            .fnDef "demo::poly_swap_pair" [.uint .u32],
            .fnDef "demo::poly_swap_pair" [.uint .u32],
            .tuple [.uint .u32, .uint .u32]
          ])
          [
            .copy { local_ := 2, projection := [] },
            fnItemOperand "demo::poly_swap_pair" [.uint .u32],
            fnItemOperand "demo::poly_swap_pair" [.uint .u32]
          ]
          { local_ := 3, projection := [] }
          (.some 1)
          .unreachable
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb1: _4 = Copy(_3.0); switchInt(_4) [0 -> bb2, otherwise -> bb3]
    { statements := [
        { kind := .storageLive 4, span := pureAdtSpan },
        { kind := .assign
            { local_ := 4, projection := [] }
            (.use (.copy { local_ := 3, projection := [.field 0 pureU32Ty] }))
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .switchInt
          (.copy { local_ := 4, projection := [] })
          { branches := [(0, 2)], otherwise := 3 }
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb2: diverging panic guard core::panicking::panic() -> !
    { statements := [
        { kind := .storageLive 5, span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "core::panicking::panic" [])
          []
          { local_ := 5, projection := [] }
          .none
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb3: external intrinsic tailCall core::intrinsics::ctpop::<u32>(_4)
    { statements := []
      terminator := {
        kind := .tailCall
          (fnItemOperand "core::intrinsics::ctpop" [.uint .u32])
          [.copy { local_ := 4, projection := [] }]
        span := pureAdtSpan
      }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [{ layout := pairU32Layout, mode := .direct }]
    ret := { layout := u32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := higherOrderCallerLayouts
  allocations := []

/--
Combined modular contract pairing `calleeRuntimeEval` over `[polySwapPairBody]`
inside `pureRustIntrinsicContract` with `extCheckedIncContract`.
-/
def calleeBackedModularContract : MirCallContract :=
  combineMirCallContracts
    (pureRustIntrinsicContract 8 true
      (calleeRuntimeEval 16 [polySwapPairBody] higherOrderCallerLayouts [] 2))
    extCheckedIncContract

/--
Precondition for `calleeBackedConstEvalAndIntrinsicTailBody` on concrete pair
`(7, 0x0F0F0005)` (where swapped first element `y = 0x0F0F0005` has popcount
`10`), plus arbitrary `(x, 0)` exercising the diverging `panic` branch.
-/
def calleeBackedModularPre (args : List Value) (mem : Memory) : Prop :=
  mem.callStack = [] ∧
  (mem.activeCallee = none ∨
    mem.activeCallee = some calleeBackedConstEvalAndIntrinsicTailBody) ∧
  mem.activeProtectors = [] ∧
  ((args = [.aggregate 0 [
      .scalar { bits := 7, sizeBytes := 4 },
      .scalar { bits := 0x0F0F0005, sizeBytes := 4 }
    ]]) ∨
   (args = [.aggregate 0 [
      .scalar { bits := 7, sizeBytes := 4 },
      .scalar { bits := 0, sizeBytes := 4 }
    ]]))

/-- Non-vacuity witness for `calleeBackedModularPre`. -/
theorem calleeBackedConstEval_modularPre_nonVacuous :
    NonVacuousStatefulPre calleeBackedModularPre :=
  ⟨[.aggregate 0 [
      .scalar { bits := 7, sizeBytes := 4 },
      .scalar { bits := 0x0F0F0005, sizeBytes := 4 }
    ]],
   emptyMemory,
   ⟨rfl, Or.inl rfl, rfl, Or.inl rfl⟩⟩

/--
End-to-end audited `ModularVerificationResult` certificate via
`verifyModularMir_of_pureModularExec_any` exercising:
1. `calleeRuntimeEval` inside `const_eval_select` resolving polymorphic
   `demo::poly_swap_pair::<u32>`,
2. `PureMirModularConverges.step_switchInt`,
3. `PureMirModularConverges.call_diverging_panic` on the `y = 0` guard branch,
4. `PureMirModularConverges.tailCall_intrinsic_sub` (`ctpop::<u32>`) on the
   `y = 0x0F0F0005` branch (returning popcount `10`).
-/
theorem verify_calleeBackedConstEvalAndIntrinsicTail :
    ModularVerificationResult
      { body := calleeBackedConstEvalAndIntrinsicTailBody
        envAssumed := calleeBackedModularContract.holdsOn
        pre := calleeBackedModularPre
        post := fun args _ retVal _ =>
          args = [.aggregate 0 [
            .scalar { bits := 7, sizeBytes := 4 },
            .scalar { bits := 0x0F0F0005, sizeBytes := 4 }
          ]] →
          retVal = .scalar { bits := 10, sizeBytes := 4 }
        callees := [polySwapPairBody] } := by
  refine verifyModularMir_of_pureModularExec_any
    calleeBackedModularContract _ rfl (Or.inl (by decide))
    (fun _ _ hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)
    (fun args _ hp => ?_)
  simp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte]
  rcases hp.2.2.2 with rfl | rfl
  · -- Case 1: y = 0x0F0F0005 -> const_eval_select -> switchInt -> tailCall ctpop = 10
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    refine PureMirModularConverges.call_const_eval_select_summary
      (maxCallDepth := 1)
      (calleeBody := polySwapPairU32Body)
      (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl (by decide)
      rfl rfl rfl (fun _ _ => rfl) rfl rfl (by decide)
      (PureMirConvergesWithCallees.of_pureMirConverges
        checkPureMir_polySwapPairU32Body
        (polySwapPairU32_pureConverges
          (.scalar { bits := 7, sizeBytes := 4 })
          (.scalar { bits := 0x0F0F0005, sizeBytes := 4 })))
      ?_
    rintro _ rfl
    refine ⟨_, rfl, ?_⟩
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    refine PureMirModularConverges.step_switchInt
      (fun _ h => nomatch h) rfl rfl rfl rfl rfl ?_
    exact PureMirModularConverges.tailCall_intrinsic_sub
      (MirCallContract.Subsumes.combine_left _ _)
      (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun _ _ => rfl)
  · -- Case 2: y = 0 -> const_eval_select -> switchInt -> diverging panic guard
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    refine PureMirModularConverges.call_const_eval_select_summary
      (maxCallDepth := 1)
      (calleeBody := polySwapPairU32Body)
      (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl (by decide)
      rfl rfl rfl (fun _ _ => rfl) rfl rfl (by decide)
      (PureMirConvergesWithCallees.of_pureMirConverges
        checkPureMir_polySwapPairU32Body
        (polySwapPairU32_pureConverges
          (.scalar { bits := 7, sizeBytes := 4 })
          (.scalar { bits := 0, sizeBytes := 4 })))
      ?_
    rintro _ rfl
    refine ⟨_, rfl, ?_⟩
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    refine PureMirModularConverges.step_switchInt
      (fun _ h => nomatch h) rfl rfl rfl rfl rfl ?_
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    exact PureMirModularConverges.call_diverging_panic
      (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl rfl
      (Or.inr ⟨rfl, Or.inl rfl⟩)

/-!
### 10H. Capture-Free Closure & Arity-Validated `const_eval_select` +
Higher-Order Modular `fnDef` & `.cleanup` Unwind Landing-Pad Witnesses
-/

/--
Capture-free closure body `demo::closure_first` (`|x: u32, _y: u32| -> u32 { x }`,
`argCount := 3`):
- `_1` is the zero-sized closure environment `RigidTy.closure "demo::closure_first" []`
  (`Value.unit`),
- `_2` is parameter `x : u32`,
- `_3` is parameter `y : u32`,
- `bb0` returns `Copy(_2)` (`x`), distinguishing exact `(.unit :: unpackedArgs)`
  closure frame layout from off-by-one `unpackedArgs` misalignment.
-/
def captureFreeFirstClosureBody : CapturedMir where
  defPath := "demo::closure_first"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 3
  localDecls := [
    { mutability := .mut, ty := pureU32Ty, debugName := some "_0" },
    { mutability := .not,
      ty := { kind := .closure "demo::closure_first" [], layoutIdx := 2 },
      debugName := some "_env" },
    { mutability := .not, ty := pureU32Ty, debugName := some "x" },
    { mutability := .not, ty := pureU32Ty, debugName := some "y" }
  ]
  basicBlocks := [
    { statements := [
        { kind := .assign
            { local_ := 0, projection := [] }
            (.use (.copy { local_ := 2, projection := [] }))
          span := pureAdtSpan }
      ]
      terminator := { kind := .return_, span := pureAdtSpan }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [
      { layout := zstFnItemLayout, mode := .ignore },
      { layout := u32Layout, mode := .direct },
      { layout := u32Layout, mode := .direct }
    ]
    ret := { layout := u32Layout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := higherOrderCallerLayouts
  allocations := []

/--
Kernel-checked regression witnesses for `const_eval_select` + `calleeRuntimeEval`:
1. Invoking capture-free closure `captureFreeFirstClosureBody` on `(10, 99)`
   prepends `Value.unit` for `_1` and returns `10` (`_2`), not `99` (`_3`).
2. Capturing closures (`upvars ≠ []`) are rejected (`none`) by
   `extractZeroSizedCallableTy?` ( both as `rtFnTy` and as `constFnTy`).
3. Arity-mismatched `const_eval_select` calls (e.g., passing a 2-element tuple
   to 1-parameter `u32StepImplBody`) fail closed (`none`) instead of corrupting
   temporary locals.
-/
theorem constEvalSelect_closure_and_arity_witnesses :
    evalPureRustIntrinsicWithRuntime
      (calleeRuntimeEval 8 [captureFreeFirstClosureBody] higherOrderCallerLayouts [] 1)
      .constEvalSelect
      [.tuple [.uint .u32, .uint .u32],
       .fnDef "demo::ct_first" [],
       .closure "demo::closure_first" [],
       .uint .u32]
      [.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨99, 4⟩], .unit, .unit] =
      some (.scalar ⟨10, 4⟩) ∧
    evalPureRustIntrinsicWithRuntime
      (calleeRuntimeEval 8 [captureFreeFirstClosureBody] higherOrderCallerLayouts [] 1)
      .constEvalSelect
      [.tuple [.uint .u32, .uint .u32],
       .fnDef "demo::ct_first" [],
       .closure "demo::closure_first" [.uint .u32],
       .uint .u32]
      [.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨99, 4⟩], .unit, .unit] = none ∧
    evalPureRustIntrinsicWithRuntime
      (calleeRuntimeEval 8 [captureFreeFirstClosureBody] higherOrderCallerLayouts [] 1)
      .constEvalSelect
      [.tuple [.uint .u32, .uint .u32],
       .tuple [],
       .closure "demo::closure_first" [],
       .uint .u32]
      [.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨99, 4⟩], .unit, .unit] = none ∧
    calleeRuntimeEval 8 [u32StepImplBody] demoCallerLayouts [] 1
      "demo::u32_step_impl" [] [.scalar ⟨10, 4⟩, .scalar ⟨99, 4⟩] = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/--
Operational `MirWpConverges` soundness certificate for `calleeRuntimeEval` on
capture-free closure `captureFreeFirstClosureBody` via `calleeRuntimeEval_sound`.
-/
theorem captureFreeFirstClosure_calleeRuntimeEval_sound :
    ∃ (calleeBody : CapturedMir) (callArgs : List Value),
      lookupCallee [captureFreeFirstClosureBody] higherOrderCallerLayouts
        "demo::closure_first" [] [] = some calleeBody ∧
      effectiveConstEvalCalleeArgs? calleeBody
        [.scalar ⟨10, 4⟩, .scalar ⟨99, 4⟩] = some callArgs ∧
      MirWpConverges calleeBody
        (initMachineStateWithMemory calleeBody callArgs
          (pureCalleeMemory [captureFreeFirstClosureBody] []))
        (mirNormalPost
          (fun rv mem' =>
            ActiveRootMemory calleeBody
              (pureCalleeMemory [captureFreeFirstClosureBody] []) mem' ∧
            rv = .scalar ⟨10, 4⟩)) :=
  calleeRuntimeEval_sound (fuel := 8) (maxCallDepth := 1)
    (mem₀ := pureCalleeMemory [captureFreeFirstClosureBody] []) rfl

/--
Unwinding `#[external_spec]` sidecar stub `ext::unwinding_inc<T>(x: u32) -> u32`
with `fnAbi.canUnwind := true` (`sidecarTargetCanUnwind = true`), so callers
passing `unwind = .cleanup cleanupBb` must genuinely prove cleanup landing-pad
convergence.
-/
def extUnwindingIncSidecarBody : CapturedMir where
  defPath := "ext::unwinding_inc_spec"
  phase := .runtimePostCleanup
  role := .externalSpec "ext::unwinding_inc"
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := pureU32Ty, debugName := some "_0" },
    { mutability := .not, ty := pureU32Ty, debugName := some "x" }
  ]
  basicBlocks := [
    { statements := []
      terminator := { kind := .return_, span := pureAdtSpan }
      isCleanup := false }
  ]
  fnAbi := {
    args := [{ layout := u32Layout, mode := .direct }]
    ret := { layout := u32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := demoCallerLayouts
  allocations := []

/--
Polymorphic unwinding `#[external_spec]` contract for `ext::unwinding_inc::<u32>`:
requires `x < 2^32 - 1` and returns `x + 1` on normal return, while permitting
frame-preserving panics (`sidecarTargetCanUnwind = true`).
-/
def extUnwindingIncContract : MirCallContract :=
  polyExternalSpecCallContract
    "ext::unwinding_inc"
    [.uint .u32]
    extUnwindingIncSidecarBody
    (fun args => ∃ x : Nat, x < 4294967295 ∧ args = [.scalar { bits := x, sizeBytes := 4 }])
    (fun args retVal =>
      ∀ x : Nat,
        args = [.scalar { bits := x, sizeBytes := 4 }] →
        retVal = .scalar { bits := x + 1, sizeBytes := 4 })

/-- Zero-sized function-item `Ty` for `ext::unwinding_inc::<u32>`. -/
def extUnwindingIncU32FnTy : Ty :=
  { kind := .fnDef "ext::unwinding_inc" [.uint .u32], layoutIdx := 2 }

/-- Zero-sized function-item `Ty` for `core::intrinsics::ctpop::<u32>`. -/
def ctpopU32FnTy : Ty :=
  { kind := .fnDef "core::intrinsics::ctpop" [.uint .u32], layoutIdx := 2 }

/--
Combined modular contract pairing `defaultPureRustIntrinsicContract` with
unwinding `extUnwindingIncContract`.
-/
def localFnItemAndCleanupContract : MirCallContract :=
  combineMirCallContracts
    defaultPureRustIntrinsicContract
    extUnwindingIncContract

/--
Higher-order modular caller `demo::local_fn_item_and_cleanup_modular`
(`argCount := 3`, `_1 : u32`, `_2 : fnDef("ext::unwinding_inc", [u32])`,
`_3 : fnDef("core::intrinsics::ctpop", [u32])`):
- `bb0`: copies `_1` into `_4` and calls `(Move(_2))(_4)` (`Operand.move` local
  `fnDef` slot!) with `unwind := .cleanup 2`.
- `bb1`: on normal return `_5 = x + 1`, tail-calls `(Copy(_3))(_5)`
  (`Operand.copy` local intrinsic `fnDef` slot!), returning `ctpop::<u32>(x + 1)`.
- `bb2` (`isCleanup := true`): on unwind from `ext::unwinding_inc`, runs
  `StorageDead(_5)` and `drop(_4) -> bb3`.
- `bb3` (`isCleanup := true`): runs `StorageDead(_4)` and `unwindResume`.
-/
def localFnItemAndCleanupModularBody : CapturedMir where
  defPath := "demo::local_fn_item_and_cleanup_modular"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 3
  localDecls := [
    { mutability := .mut, ty := pureU32Ty, debugName := some "_0" },
    { mutability := .not, ty := pureU32Ty, debugName := some "x" },
    { mutability := .mut, ty := extUnwindingIncU32FnTy, debugName := some "ext_f" },
    { mutability := .not, ty := ctpopU32FnTy, debugName := some "intr_f" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "guard_tmp" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "inc_out" }
  ]
  basicBlocks := [
    -- bb0: StorageLive(_4, _5); _4 = Copy(_1);
    --      _5 = (Move(_2))(_4) -> [return: bb1, unwind: cleanup(bb2)]
    { statements := [
        { kind := .storageLive 4, span := pureAdtSpan },
        { kind := .storageLive 5, span := pureAdtSpan },
        { kind := .assign
            { local_ := 4, projection := [] }
            (.use (.copy { local_ := 1, projection := [] }))
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (.move { local_ := 2, projection := [] })
          [.copy { local_ := 4, projection := [] }]
          { local_ := 5, projection := [] }
          (.some 1)
          (.cleanup 2)
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb1: tailcall (Copy(_3))(_5)
    { statements := []
      terminator := {
        kind := .tailCall
          (.copy { local_ := 3, projection := [] })
          [.copy { local_ := 5, projection := [] }]
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb2 (cleanup): StorageDead(_5); drop(_4) -> [return: bb3, unwind: terminate]
    { statements := [
        { kind := .storageDead 5, span := pureAdtSpan }
      ]
      terminator := {
        kind := .drop
          { local_ := 4, projection := [] }
          3
          .terminate
        span := pureAdtSpan
      }
      isCleanup := true
    },
    -- bb3 (cleanup): StorageDead(_4); unwindResume
    { statements := [
        { kind := .storageDead 4, span := pureAdtSpan }
      ]
      terminator := {
        kind := .unwindResume
        span := pureAdtSpan
      }
      isCleanup := true
    }
  ]
  fnAbi := {
    args := [
      { layout := u32Layout, mode := .direct },
      { layout := zstFnItemLayout, mode := .ignore },
      { layout := zstFnItemLayout, mode := .ignore }
    ]
    ret := { layout := u32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := higherOrderCallerLayouts
  allocations := []

/--
Precondition for `localFnItemAndCleanupModularBody` over all `x < 2^32 - 1` and
unconstrained `mem.traitImpls` (with `mem.callees = []`).
-/
def localFnItemAndCleanupPre (args : List Value) (mem : Memory) : Prop :=
  (∃ x : Nat,
    x < 4294967295 ∧
    args = [.scalar { bits := x, sizeBytes := 4 }, .unit, .unit]) ∧
  mem.callees = [] ∧
  mem.callStack = [] ∧
  (mem.activeCallee = none ∨
    mem.activeCallee = some localFnItemAndCleanupModularBody) ∧
  mem.activeProtectors = []

/-- Non-vacuity witness for `localFnItemAndCleanupPre`. -/
theorem localFnItemAndCleanup_modularPre_nonVacuous :
    NonVacuousStatefulPre localFnItemAndCleanupPre :=
  ⟨[.scalar { bits := 41, sizeBytes := 4 }, .unit, .unit],
   emptyMemory,
   ⟨41, by decide, rfl⟩,
   rfl, rfl, Or.inl rfl, rfl⟩

@[irreducible]
def expectedCtpopU32 (v : Nat) : Value := .scalar ⟨pureCtpopLoop 32 v, 4⟩

private theorem expectedCtpopU32_def (v : Nat) :
    (Value.scalar ⟨pureCtpopLoop 32 v, 4⟩) = expectedCtpopU32 v := by
  unfold expectedCtpopU32
  rfl

/--
Symbolic modular convergence across all `x < 2^32 - 1` and arbitrary
`traitImpls` for `localFnItemAndCleanupModularBody`, exercising:
1. `PureMirModularConverges.call_poly_external_spec_pureTarget` on `Operand.move
   _2` (`_2` becomes `.uninit`) with `unwind = .cleanup 2`,
2. Cleanup landing-pad recovery in `bb2 -> bb3` via `step_stmt` + `step_drop` +
   `step_unwindResume`,
3. `PureMirModularConverges.tailCall_intrinsic_pureTarget` on `Operand.copy _3`
   (`ctpop::<u32>(x + 1)`).
-/
theorem localFnItemAndCleanup_modularConverges
    (x : Nat) (hx : x < 4294967295)
    (traitImpls : List TraitImplEntry := []) :
    PureMirModularConverges
      localFnItemAndCleanupContract
      localFnItemAndCleanupModularBody
      []
      (initPureState localFnItemAndCleanupModularBody
        [.scalar { bits := x, sizeBytes := 4 }, .unit, .unit])
      (· = expectedCtpopU32 (x + 1))
      traitImpls := by
  have hx1_lt : x + 1 < 4294967296 := Nat.succ_lt_succ hx
  have h_canon_x1 :
      isCanonicalScalarOfSize { bits := x + 1, sizeBytes := 4 } 4 = true :=
    isCanonicalScalarOfSize_four hx1_lt
  -- bb0: StorageLive(_4), StorageLive(_5), _4 = Copy(_1)
  have h_init :
      initPureState localFnItemAndCleanupModularBody
        [.scalar { bits := x, sizeBytes := 4 }, .unit, .unit] =
        { bb := 0
          stmtIdx := 0
          env := [.uninit, .init (.scalar { bits := x, sizeBytes := 4 }),
            .init .unit, .init .unit, .dead, .dead] } := rfl
  rw [h_init]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  -- bb0 terminator: (Move(_2))(_4) -> [return: bb1, unwind: cleanup(bb2)]
  refine PureMirModularConverges.call_poly_external_spec_pureTarget
    (targetDefPath := "ext::unwinding_inc")
    (expectedTypeArgs := [.uint .u32])
    (sidecarBody := extUnwindingIncSidecarBody)
    (extraPre := fun args =>
      ∃ x : Nat, x < 4294967295 ∧ args = [.scalar { bits := x, sizeBytes := 4 }])
    (extraPost := fun args retVal =>
      ∀ x : Nat,
        args = [.scalar { bits := x, sizeBytes := 4 }] →
        retVal = .scalar { bits := x + 1, sizeBytes := 4 })
    (MirCallContract.Subsumes.combine_right
      defaultPureRustIntrinsicContract extUnwindingIncContract)
    (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl rfl
    (lookupCallee_nil _ _ _ _)
    rfl rfl
    ⟨⟨x, Nat.lt_trans hx (by decide), rfl⟩, trivial⟩
    ⟨x, hx, rfl⟩
    (Or.inr (Or.inr (Or.inr ⟨2, rfl, ?_⟩)))
    ?_
    rfl
  · -- Cleanup landing pad bb2 -> bb3: StorageDead(_5), drop(_4), StorageDead(_4), unwindResume
    refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set]
    refine PureMirModularConverges.step_drop (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set]
    exact PureMirModularConverges.step_unwindResume
      (fun _ h => nomatch h) rfl rfl rfl
  · -- Normal return path bb1: tailCall (Copy(_3))(_5) -> ctpop::<u32>(x + 1)
    rintro retVal ⟨_, h_ext_post⟩
    have h_rv : retVal = .scalar { bits := x + 1, sizeBytes := 4 } :=
      h_ext_post x rfl
    subst h_rv
    refine ⟨_, rfl, ?_⟩
    refine PureMirModularConverges.tailCall_intrinsic_pureTarget
      (pointerBytes := 8)
      (ubChecksEnabled := true)
      (rtEval := fun _ _ _ => none)
      (kind := .ctpop)
      (retVal := expectedCtpopU32 (x + 1))
      (MirCallContract.Subsumes.combine_left
        defaultPureRustIntrinsicContract extUnwindingIncContract)
      (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl
      (lookupCallee_nil _ _ _ _)
      rfl
      ?_
      rfl
    dsimp only [evalPureRustIntrinsicWithRuntime, evalPureScalarIntrinsic,
      intrinsicScalarTyInfo?]
    rw [h_canon_x1]
    exact congrArg some (expectedCtpopU32_def (x + 1))

/--
Audited `ModularVerificationResult` for `localFnItemAndCleanupModularBody` via
`verifyModularMir_of_pureModularExec_any` with `callees = []` and unconstrained
`mem.traitImpls`.
-/
theorem verify_localFnItemAndCleanupModular :
    ModularVerificationResult
      { body := localFnItemAndCleanupModularBody
        envAssumed := localFnItemAndCleanupContract.holdsOn
        pre := localFnItemAndCleanupPre
        post := fun args _ retVal _ =>
          ∀ x : Nat,
            args = [.scalar { bits := x, sizeBytes := 4 }, .unit, .unit] →
            retVal = expectedCtpopU32 (x + 1)
        callees := [] } := by
  refine verifyModularMir_of_pureModularExec_any
    localFnItemAndCleanupContract _ rfl
    (Or.inr (fun _ _ hp => hp.2.1))
    (fun _ _ hp => hp.2.2)
    (fun args mem hp => ?_)
  rcases hp.1 with ⟨x, hx, rfl⟩
  refine PureMirModularConverges.mono ?_
    (localFnItemAndCleanup_modularConverges x hx mem.traitImpls)
  intro retVal h_ret _ x' h_eq
  injection h_eq with h_hd _
  injection h_hd with h_sc
  injection h_sc with hx_eq _
  subst hx_eq
  exact h_ret

end Anneal.PureMirExec
