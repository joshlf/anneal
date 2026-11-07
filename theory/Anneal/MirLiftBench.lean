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
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues]
  -- bb1[0]: `StorageDead(_1)`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  -- bb1 terminator: root `return` of `_0 = 7_u32`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
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
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, returnFrameMem, restoreCallerProtectors]
  -- bb1 terminator: `tailCall lift_poly_id::<u32>(move _1)`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.tailCallDirect (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, tailCallFrameMem, Option.getD]
  -- Tail callee bb0[0]: `_0 = move _1`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- Tail callee bb0 terminator: root `return` of `7_u32`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
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
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, tailCallFrameMem, Option.getD]
  -- `lift_poly_id::<u32>` bb0[0]: `_0 = move _1`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- `lift_poly_id::<u32>` bb0 terminator: return `7_u32` to
  -- `poly_layout_caller` at bb1.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl)
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
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, returnFrameMem, restoreCallerProtectors]
  -- bb3 terminator: root return of `7_u32`.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
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
    (by rfl)
  dsimp only [FrameStep.Continues, tailCallFrameMem, Option.getD]
  -- `lift_poly_id::<u32>` bb0[0]: `_0 = move _1`.
  apply LiftFrame.stmt (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
  dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add]
  -- `lift_poly_id::<u32>` bb0 terminator: return `14_u32` into `_3` at bb1.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl)
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
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl)
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
  apply LiftTerminator.return_ (by rfl) (by rfl)
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
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, returnFrameMem, restoreCallerProtectors]
  -- `lift_poly_apply::<u32>` bb1 terminator: return `3_u32` into projected
  -- destination `_2.0` at bb1.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl)
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
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl)
  dsimp only [FrameStep.Continues, returnFrameMem, restoreCallerProtectors]
  -- `lift_poly_apply::<u8>` bb1 terminator: return `4_u8` into projected
  -- destination `_2.1` at bb2.
  apply LiftFrame.term (by rfl) (Or.inl rfl) (by rfl) (by rfl) (by rfl)
  apply LiftTerminator.returnToCaller (by rfl) (by rfl) (by rfl) (by rfl)
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
  apply LiftTerminator.return_ (by rfl) (by rfl)
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
