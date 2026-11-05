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

end IndirectCallBenchmark
