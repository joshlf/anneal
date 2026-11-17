-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import Anneal
import Anneal.OpaqueCalleeTable
import Anneal.CompilerQueryEnv

/-!
# End-to-end tests: opaque callee table and demand-time compiler queries

The import header is itself the **co-import gate**: `Anneal.OpaqueCalleeTable` and
`Anneal.CompilerQueryEnv` elaborate next to the entire `Anneal` umbrella (including
`Anneal.Rustc.V2026_06_01.TraceCheck`, which derives `DecidableEq` for the nine
V2026_06_01 enumeration types), so any duplicate global constant (an orphan
`Trusted.….ofNat`) or conflicting instance would fail this file at import time.

Contents (every claim is checked by the kernel when this file is elaborated):

* concrete `CapturedMir` canaries over the real trusted machine for the opaque table
  (`O(1)` certificates, exact literal pruning, demanded-key cone narrowing, specificity and
  default-method trait dispatch, the naive-narrowing counterexample);
* the **unconditional trusted frame lemma** in use (decide-free trusted agreement, calls
  outside `MirLiftCore.StepConeSafe`, non-vacuity, necessity of the linked-table hypothesis);
* the **`Anneal.MirLiftCore` bridge** (`AgreesOn` from raw certificates, `calleesAgreeOn`,
  opaque evaluation → `runCfgWithCallees` → narrowed table, `wpMirExecSym` transfer, the
  `CalleeInitWf` forms down to the empty table and their necessity, and polymorphic
  `CallConeClosedPoly` narrowing of a generic callee);
* Part B query canaries and the **receiver-driven `charon#1611` dispatch** canaries, including
  the explicit trait-method binding (`expectedTraitMethod?`) for compiler-generated shims versus
  the fail-closed `implementsCalledMethod` fallback;
* the `BEq`-shadowing demonstration (`ShadowingDemo`);
* the `run_meta` **opacity witness** on all five sealed `OpaqueCalleeTable` operations;
* the in-file **heartbeat regression gate** (`M = 4` vs. `M = 32` callees);
* `#guard_msgs` axiom pins on headline theorems and the bottom-of-file `run_cmd`
  **axiom & namespace audit** over every constant of both library modules.
-/

namespace Anneal.CompilerQueryAndOpaqueCalleeTests

open Trusted.Effect (FailureKind Outcome)
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.OpaqueCalleeTable
open Anneal.CompilerQueryEnv

/-! ## `DecidableEq RigidTy` evaluates under `decide` -/

/-- `decide` evaluates `DecidableEq RigidTy` both on and off the constructor
diagonal (including at top level). -/
theorem rigidTy_decide_canary :
    RigidTy.bool ≠ RigidTy.uint .u32 ∧
      RigidTy.fnPtr [] .bool .safe .rust ≠ RigidTy.fnPtr [] (.uint .u32) .safe .rust ∧
      RigidTy.adt "a::B" [.bool, .array (.uint .u32) 3] = RigidTy.adt "a::B" [.bool, .array (.uint .u32) 3] ∧
      RigidTy.ref .not (.param 0 "T") ≠ RigidTy.ref .mut (.param 0 "T") := by
  decide

/-- The V2026_08_01 `RigidTy` instance (`Anneal.CompilerQueryEnv`) evaluates under `decide`
too, and the lossless dialect bridge round-trips concrete types. -/
theorem rigidTyV08_decide_canary :
    Trusted.Rustc.V2026_08_01.MirAst.RigidTy.bool ≠ Trusted.Rustc.V2026_08_01.MirAst.RigidTy.uint .u32 ∧
      bridgeRigidTyV06ToV08 (.ref .mut (.array (.int .i64) 4)) =
        Trusted.Rustc.V2026_08_01.MirAst.RigidTy.ref .mut (.array (.int .i64) 4) ∧
      bridgeRigidTyV08ToV06 (bridgeRigidTyV06ToV08 (.fnPtr [.bool] .str .unsafe_ .c)) =
        RigidTy.fnPtr [.bool] .str .unsafe_ .c := by
  decide

/-- V2026_08_01 `Value`, `TreeBorrowPerm`, enumeration (`UnOp`, `BinOp`, `RetagKind`), and
reverse `V08 → V06 → V08` `RigidTy` round-trip canary (`bridgeRigidTy_roundtrip_v08`). -/
theorem v08_machine_and_roundtrip_canary :
    let v08Ty : Trusted.Rustc.V2026_08_01.MirAst.RigidTy :=
      .fnPtr [.bool, .dynamic "fx::Area"] (.ref .mut (.slice (.uint .u32))) .unsafe_ .c
    bridgeRigidTyV06ToV08 (bridgeRigidTyV08ToV06 v08Ty) = v08Ty ∧
      (Trusted.Rustc.V2026_08_01.MirSemantics.Value.aggregate 0 [.scalar ⟨3, 4⟩, .ptr ⟨7, 0⟩ 0] ≠
        Trusted.Rustc.V2026_08_01.MirSemantics.Value.aggregate 0 [.scalar ⟨4, 4⟩, .ptr ⟨7, 0⟩ 0]) ∧
      (Trusted.Rustc.V2026_08_01.MirSemantics.TreeBorrowPerm.reservedFrz true ≠
        Trusted.Rustc.V2026_08_01.MirSemantics.TreeBorrowPerm.reservedFrz false) ∧
      (Trusted.Rustc.V2026_08_01.MirAst.UnOp.ptrMetadata ≠ .neg) ∧
      (Trusted.Rustc.V2026_08_01.MirAst.BinOp.offset ≠ .add) ∧
      (Trusted.Rustc.V2026_08_01.MirAst.RetagKind.twoPhase ≠ .raw) :=
  ⟨bridgeRigidTy_roundtrip_v08 _, by decide, by decide, by decide, by decide, by decide⟩

/-! ## Opaque callee table: concrete captured MIR -/

/-- `()` layout. -/
def fxUnitLayout : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory, fields := .arbitrary [] [],
    variants := .single 0, isUninhabited := false }

/-- `bool` layout. -/
def fxBoolLayout : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- `u32` layout (as computed by `RigidTy.computeLayout`). -/
def fxU32Layout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- Shared x86_64 layout table: `0 ↦ ()`, `1 ↦ bool`, `2 ↦ u32`. -/
def fxLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [fxUnitLayout, fxBoolLayout, fxU32Layout] }

/-- `bool` at layout index `1`. -/
def fxBoolTy : Ty := ⟨.bool, 1⟩

/-- `u32` at layout index `2`. -/
def fxU32Ty : Ty := ⟨.uint .u32, 2⟩

/-- `extern "Rust" fn() -> u32`. -/
def fxRetU32Abi : FnAbi :=
  { args := [], ret := ⟨fxU32Layout, .direct⟩, conv := .rust, canUnwind := true }

/-- `const v_u32`. -/
def fxU32Const (v : Nat) : Operand := .constant ⟨fxU32Ty, .scalar (.int ⟨v, 4⟩)⟩

/-- Literal `bool` constant operand. -/
def fxBoolConst (b : Bool) : Operand :=
  .constant ⟨fxBoolTy, .scalar (.int ⟨if b then 1 else 0, 1⟩)⟩

/-- Function-item operand `p::<tys>`. -/
def fxFnItem (p : DefPath) (tys : List RigidTy) : Operand :=
  .constant ⟨⟨.fnDef p tys, 0⟩, .zeroSized⟩

/-- Return place `_0`. -/
def fxRetPlace : Place := ⟨0, []⟩

/-- Captured leaf callee `fn() -> u32 { _0 = const v; return }`, generic over
`typeParams` (unused) type parameters and carrying `traitImpls`. -/
def fxLeaf (p : DefPath) (v : Nat) (typeParams : Nat) (traitImpls : List TraitImplEntry) :
    CapturedMir :=
  { defPath := p, phase := .runtimePostCleanup, role := .subject, argCount := 0,
    localDecls := [⟨.mut, fxU32Ty, some "_0"⟩],
    basicBlocks :=
      [⟨[⟨.assign fxRetPlace (.use (fxU32Const v)), "leaf:0"⟩], ⟨.return_, "leaf:1"⟩, false⟩],
    fnAbi := fxRetU32Abi, layouts := fxLayouts, allocations := [],
    typeParamCount := typeParams,
    genericParams := if typeParams = 0 then [] else [⟨0, "T"⟩],
    traitImpls := traitImpls }

/-- Call block `_0 = p::<tys>() -> target`. -/
def fxCallBlock (p : DefPath) (tys : List RigidTy) (target : BasicBlockIdx) : BasicBlockData :=
  ⟨[], ⟨.call (fxFnItem p tys) [] fxRetPlace (some target) .continue_, "call"⟩, false⟩

/-- Panicking callee `g_dead`: `fn() -> u32 { core::panicking::panic() }`. -/
def fxGDead : CapturedMir :=
  { defPath := "fx::g_dead", phase := .runtimePostCleanup, role := .subject, argCount := 0,
    localDecls := [⟨.mut, fxU32Ty, some "_0"⟩],
    basicBlocks :=
      [⟨[], ⟨.call (fxFnItem "core::panicking::panic" []) [] fxRetPlace none .continue_,
        "g_dead:0"⟩, false⟩],
    fnAbi := fxRetU32Abi, layouts := fxLayouts, allocations := [] }

/-- Live monomorphic callee. -/
def fxLiveF : CapturedMir := fxLeaf "fx::live_f" 7 0 []

/-- Unrelated captured callees padding the full table. -/
def fxFillerA : CapturedMir := fxLeaf "fx::filler_a" 1 0 []

/-- Unrelated captured callee padding the full table. -/
def fxFillerB : CapturedMir := fxLeaf "fx::filler_b" 2 0 []

/-- Root `fn() -> u32 { if LIT { _0 = live() } else { _0 = dead() } }`:
`bb0: switchInt(const LIT) -> [0: bb2, otherwise: bb1]`, `bb1: _0 = live() -> bb3`,
`bb2: _0 = dead() -> bb3`, `bb3: return`. -/
def fxLitIfRoot (lit : Bool) (liveP : DefPath) (liveTys : List RigidTy) (deadP : DefPath) :
    CapturedMir :=
  { defPath := "fx::root", phase := .runtimePostCleanup, role := .subject, argCount := 0,
    localDecls := [⟨.mut, fxU32Ty, some "_0"⟩],
    basicBlocks := [
      ⟨[], ⟨.switchInt (fxBoolConst lit) ⟨[(0, 2)], 1⟩, "root:if"⟩, false⟩,
      fxCallBlock liveP liveTys 3,
      fxCallBlock deadP [] 3,
      ⟨[], ⟨.return_, "root:ret"⟩, false⟩ ],
    fnAbi := fxRetU32Abi, layouts := fxLayouts, allocations := [] }

/-- Dead-arm canary root: `if true { live_f() } else { g_dead() }`. -/
def canaryRoot : CapturedMir := fxLitIfRoot true "fx::live_f" [] "fx::g_dead"

/-- Initial machine state of `canaryRoot`. -/
def canaryInit : MachineState := initMachineState canaryRoot []

/-- Full table (fillers, the panicking `g_dead`, and `live_f`). -/
def canaryFullTbl : OpaqueCalleeTable :=
  .ofList [fxFillerA, fxGDead, fxLiveF, fxFillerB]

/-- Narrowed table: `g_dead` (dead arm only) and fillers excluded. -/
def canaryNarrowTbl : OpaqueCalleeTable := .ofList [fxLiveF]

/-- Broken table: the live callee is missing. -/
def canaryBrokenTbl : OpaqueCalleeTable := .ofList [fxFillerA, fxGDead, fxFillerB]

/-- Key of the live call. -/
def canaryLiveKey : CalleeKey := ⟨fxLayouts, "fx::live_f", [], []⟩

/-- Only the live call is demanded: the dead arm's `g_dead` never is. -/
theorem canary_deadArm_demandedKeys :
    demandedKeys canaryFullTbl.lookup canaryRoot 8 canaryInit = [canaryLiveKey] := by
  decide +kernel

/-- Non-vacuity: the tables genuinely differ on `g_dead`. -/
theorem canary_deadArm_tables_differ :
    canaryFullTbl.lookup fxLayouts "fx::g_dead" [] [] = some fxGDead ∧
      canaryNarrowTbl.lookup fxLayouts "fx::g_dead" [] [] = none := by
  refine ⟨lookupCallee_hit_mono ?_ rfl, lookupCallee_miss_direct ?_⟩
  · unfold canaryFullTbl
    rw [lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  · unfold canaryNarrowTbl
    rw [lookupRaw_ofList_cons_miss (by decide), OpaqueCalleeTable.lookupRaw_eq,
      OpaqueCalleeTable.toList_ofList]
    rfl

/-- `live_f` resolves identically in both tables (`O(1)` `lookupKey_hit_mono` certificates,
zero `lookupKey_eq` unfolding). -/
theorem canary_liveKey_agrees :
    canaryNarrowTbl.lookupKey canaryLiveKey = canaryFullTbl.lookupKey canaryLiveKey := by
  have hrawN : canaryNarrowTbl.lookupRaw "fx::live_f" = some fxLiveF :=
    lookupRaw_ofList_cons_hit rfl
  rw [lookupKey_hit_mono (c := fxLiveF) hrawN rfl rfl,
    lookupKey_hit_mono (c := fxLiveF) ?_ rfl rfl]
  unfold canaryFullTbl
  rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide)]
  exact lookupRaw_ofList_cons_hit rfl

/-- **Dead-arm cone canary**: dropping the panicking dead-arm callee `g_dead`
(and unrelated callees) leaves the run unchanged. -/
theorem canary_deadArm_cone_narrow :
    evalWithOpaqueCallees canaryNarrowTbl canaryRoot 8 canaryInit =
      evalWithOpaqueCallees canaryFullTbl canaryRoot 8 canaryInit := by
  apply evalWithOpaqueCallees_cone_narrow
  rw [canary_deadArm_demandedKeys]
  intro k hk
  simp only [List.mem_singleton] at hk
  subst hk
  exact canary_liveKey_agrees

/-- The canary genuinely executes: one branch event, then `live_f` returns `7`. -/
theorem canary_deadArm_halts :
    (evalWithOpaqueCallees canaryFullTbl canaryRoot 8 canaryInit).summary =
      ⟨.halted, [.event 1], some 7, none⟩ := by
  decide +kernel

/-- Initial state of `canaryRoot` with `canaryFullTbl.toList` linked in
`memory.callees` (`initMachineStateWithCallees`). -/
def canaryInitWithCallees : MachineState :=
  initMachineStateWithCallees canaryRoot [] canaryFullTbl.toList

/-- **Concrete instantiation of `evalWithOpaqueCallees_eq_trusted`**: when the
initial state links `canaryFullTbl.toList` in `memory.callees`, every visited
state along the run preserves `s'.memory.callees = canaryFullTbl.toList`, and
`evalWithOpaqueCallees` is *identical* to the iterated trusted `stepMirFn`. -/
theorem canary_evalWithOpaqueCallees_eq_trusted :
    evalWithOpaqueCallees canaryFullTbl canaryRoot 8 canaryInitWithCallees =
      runSteps (stepMirFn canaryRoot) 8 canaryInitWithCallees [] := by
  apply evalWithOpaqueCallees_eq_trusted
  decide +kernel

/-- Contrast: on `canaryInit` (`initMachineState`, where `memory.callees = []`),
the trusted `stepMirFn` halts at an external call to `fx::live_f`, whereas on
`canaryInitWithCallees` it halts normally returning `7`. -/
theorem canary_trusted_stepMirFn_requires_linked_callees :
    (runSteps (stepMirFn canaryRoot) 8 canaryInit []).summary =
      ⟨.external, [.event 1], none, some "fx::live_f"⟩ ∧
    (runSteps (stepMirFn canaryRoot) 8 canaryInitWithCallees []).summary =
      ⟨.halted, [.event 1], some 7, none⟩ := by
  decide +kernel

/-- Negative canary: dropping the *live* callee changes the outcome (the cone
hypothesis is necessary). -/
theorem canary_liveArm_required :
    (evalWithOpaqueCallees canaryBrokenTbl canaryRoot 8 canaryInit).summary =
      ⟨.external, [.event 1], none, some "fx::live_f"⟩ := by
  decide +kernel

/-! #### Multi-callee canary: polymorphic instantiation + `TraitImplEntry` dispatch -/

/-- `Self` type of the trait-dispatch canary. -/
def fxCircleTy : RigidTy := .adt "fx::Circle" []

/-- `impl Area for Circle` override entry for trait method `fx::Area::area`. -/
def fxAreaEntry : TraitImplEntry :=
  ⟨⟨"fx::Area::area", [fxCircleTy]⟩, "fx::<impl Area for Circle>::area"⟩

/-- Generic callee `fn poly<T>() -> u32` (instantiated via `CapturedMir.instantiate`). -/
def fxPoly : CapturedMir := fxLeaf "fx::poly" 9 1 []

/-- Override body `<Circle as Area>::area`. -/
def fxCircleArea : CapturedMir := fxLeaf "fx::<impl Area for Circle>::area" 31 0 []

/-- Captured `impl Area for Circle` block body carrying the `TraitImplEntry`; it is
never called, yet trait resolution reads its entry through `flatMapTraitImpls`. -/
def fxAreaImplHolder : CapturedMir := fxLeaf "fx::<impl Area for Circle>" 0 0 [fxAreaEntry]

/-- `if false { g_dead() } else { _0 = poly::<u32>(); _0 = <Circle as Area>::area() }`:
`bb0: switchInt(const false) -> [0: bb1, otherwise: bb4]`, `bb1: poly::<u32>() -> bb2`,
`bb2: Area::area::<Circle>() -> bb3`, `bb3: return`, `bb4: g_dead() -> bb3`. -/
def multiRoot : CapturedMir :=
  { defPath := "fx::root2", phase := .runtimePostCleanup, role := .subject, argCount := 0,
    localDecls := [⟨.mut, fxU32Ty, some "_0"⟩],
    basicBlocks := [
      ⟨[], ⟨.switchInt (fxBoolConst false) ⟨[(0, 1)], 4⟩, "root2:if"⟩, false⟩,
      fxCallBlock "fx::poly" [.uint .u32] 2,
      fxCallBlock "fx::Area::area" [fxCircleTy] 3,
      ⟨[], ⟨.return_, "root2:ret"⟩, false⟩,
      fxCallBlock "fx::g_dead" [] 3 ],
    fnAbi := fxRetU32Abi, layouts := fxLayouts, allocations := [] }

/-- Initial state of `multiRoot`. -/
def multiInit : MachineState := initMachineState multiRoot []

/-- Full table. -/
def multiFullTbl : OpaqueCalleeTable :=
  .ofList [fxFillerA, fxGDead, fxPoly, fxAreaImplHolder, fxFillerB, fxCircleArea]

/-- Demanded-key narrowing: keeps the `impl` block carrying the `TraitImplEntry`. -/
def multiNarrowTbl : OpaqueCalleeTable := .ofList [fxPoly, fxAreaImplHolder, fxCircleArea]

/-- Naive "executed `DefPath`s only" narrowing: drops the never-called `impl` block. -/
def multiNaiveTbl : OpaqueCalleeTable := .ofList [fxPoly, fxCircleArea]

/-- Key of the polymorphic call. -/
def multiPolyKey : CalleeKey := ⟨fxLayouts, "fx::poly", [.uint .u32], []⟩

/-- Key of the trait-method call. -/
def multiAreaKey : CalleeKey := ⟨fxLayouts, "fx::Area::area", [fxCircleTy], []⟩

/-- Exactly the polymorphic and trait-dispatch calls are demanded (not `g_dead`). -/
theorem canary_multi_demandedKeys :
    demandedKeys multiFullTbl.lookup multiRoot 12 multiInit = [multiPolyKey, multiAreaKey] := by
  decide +kernel

/-- The multi-callee run executes both live calls and returns `31`. -/
theorem canary_multi_halts :
    (evalWithOpaqueCallees multiFullTbl multiRoot 12 multiInit).summary =
      ⟨.halted, [.event 0], some 31, none⟩ := by
  decide +kernel

/-- `u32` instantiation layout certificate. -/
theorem canary_u32_instantiationLayouts :
    instantiationLayouts? fxLayouts [.uint .u32] = some [fxU32Layout] := by
  decide

/-- Polymorphic resolution certificate in a table. -/
theorem canary_poly_resolve (tbl : List CapturedMir)
    (h : resolveCalleeBodyAndArgs? tbl "fx::poly" [.uint .u32] [] = some (fxPoly, [.uint .u32])) :
    (OpaqueCalleeTable.ofList tbl).lookupKey multiPolyKey =
      some (fxPoly.instantiate ([RigidTy.uint .u32].zip [fxU32Layout])) := by
  rw [OpaqueCalleeTable.lookupKey_eq]
  exact lookupCallee_hit (by rw [OpaqueCalleeTable.toList_ofList]; exact h) rfl rfl
    canary_u32_instantiationLayouts

/-- One-time per-table `traitImpls` certificate for `multiNarrowTbl`. -/
theorem multiNarrowTbl_traitImpls : multiNarrowTbl.traitImpls = [fxAreaEntry] := by
  unfold multiNarrowTbl
  rw [traitImpls_ofList]
  rfl

/-- One-time per-table `traitImpls` certificate for `multiFullTbl`: emitted once
for the table and reused across all free-generic and trait-method call sites without
ever unfolding `multiFullTbl.toList` again. -/
theorem multiFullTbl_traitImpls : multiFullTbl.traitImpls = [fxAreaEntry] := by
  unfold multiFullTbl
  rw [traitImpls_ofList]
  rfl

/-- The polymorphic key agrees across the full and narrowed tables (`O(1)`
`lookupKey_hit_free_poly_opaque` certificates over `lookupRaw` and sealed `traitImpls`,
with zero `tbl.toList` unfolding). -/
theorem canary_multi_polyKey_agrees :
    multiNarrowTbl.lookupKey multiPolyKey = multiFullTbl.lookupKey multiPolyKey := by
  have hno : hasTraitImplForDefPath ([] ++ [fxAreaEntry]) "fx::poly" = false := by decide
  have hrawN : multiNarrowTbl.lookupRaw "fx::poly" = some fxPoly :=
    lookupRaw_ofList_cons_hit rfl
  have hrawF : multiFullTbl.lookupRaw "fx::poly" = some fxPoly := by
    unfold multiFullTbl
    rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  rw [lookupKey_hit_free_poly_opaque rfl multiNarrowTbl_traitImpls hno hrawN rfl
      canary_u32_instantiationLayouts,
    lookupKey_hit_free_poly_opaque rfl multiFullTbl_traitImpls hno hrawF rfl
      canary_u32_instantiationLayouts]

/-- `impl Area for Circle` is the unique most-specific override in both tables. -/
theorem canary_area_winner_narrow :
    filterMostSpecificTraitImpls (traitMatches multiNarrowTbl [] "fx::Area::area" [fxCircleTy])
      (traitMatches multiNarrowTbl [] "fx::Area::area" [fxCircleTy]) =
        [(fxAreaEntry, some [])] := by
  decide +kernel

/-- Same winner in the full table. -/
theorem canary_area_winner_full :
    filterMostSpecificTraitImpls (traitMatches multiFullTbl [] "fx::Area::area" [fxCircleTy])
      (traitMatches multiFullTbl [] "fx::Area::area" [fxCircleTy]) =
        [(fxAreaEntry, some [])] := by
  decide +kernel

/-- The trait-dispatch key agrees across the full and narrowed tables (`O(1)`
`lookupKey_trait_hit_cert` + `collectMatchingTraitImplsWith_cons_hit_mono` certificates,
with zero `tbl.toList` unfolding). -/
theorem canary_multi_areaKey_agrees :
    multiNarrowTbl.lookupKey multiAreaKey = multiFullTbl.lookupKey multiAreaKey := by
  have himplN : multiNarrowTbl.lookupRaw "fx::<impl Area for Circle>::area" =
      some fxCircleArea := by
    unfold multiNarrowTbl
    rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  have himplF : multiFullTbl.lookupRaw "fx::<impl Area for Circle>::area" =
      some fxCircleArea := by
    unfold multiFullTbl
    rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide),
      lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide),
      lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  have hcolN :
      collectMatchingTraitImplsWith multiNarrowTbl.lookupRaw ([] ++ [fxAreaEntry])
        "fx::Area::area" [fxCircleTy] [] = [(fxAreaEntry, some [])] := by
    rw [List.nil_append,
      collectMatchingTraitImplsWith_cons_hit_mono (c := fxCircleArea)
        (by decide) rfl (by decide) himplN (by decide) rfl]
    rfl
  have hcolF :
      collectMatchingTraitImplsWith multiFullTbl.lookupRaw ([] ++ [fxAreaEntry])
        "fx::Area::area" [fxCircleTy] [] = [(fxAreaEntry, some [])] := by
    rw [List.nil_append,
      collectMatchingTraitImplsWith_cons_hit_mono (c := fxCircleArea)
        (by decide) rfl (by decide) himplF (by decide) rfl]
    rfl
  rw [lookupKey_trait_hit_cert (winner := fxAreaEntry) rfl (by decide) multiNarrowTbl_traitImpls
      hcolN (by decide) himplN (by decide) rfl,
    lookupKey_trait_hit_cert (winner := fxAreaEntry) rfl (by decide) multiFullTbl_traitImpls
      hcolF (by decide) himplF (by decide) rfl]

/-- **Multi-callee cone canary** (polymorphic + trait dispatch, dead-arm `g_dead`
excluded). -/
theorem canary_multi_cone_narrow :
    evalWithOpaqueCallees multiNarrowTbl multiRoot 12 multiInit =
      evalWithOpaqueCallees multiFullTbl multiRoot 12 multiInit := by
  apply evalWithOpaqueCallees_cone_narrow
  rw [canary_multi_demandedKeys]
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact canary_multi_polyKey_agrees
  · exact canary_multi_areaKey_agrees

/-- **Soundness corner case**: narrowing to the *executed* `DefPath`s (every body
that runs is kept) still breaks trait dispatch, because the dropped, never-called
`impl` block contributed the `TraitImplEntry` via `flatMapTraitImpls`. Cone
narrowing must preserve demanded lookup *results*, not reachable `DefPath`s. -/
theorem canary_naiveNarrow_breaks_trait_dispatch :
    (evalWithOpaqueCallees multiNaiveTbl multiRoot 12 multiInit).summary =
      ⟨.external, [.event 0], none, some "fx::Area::area"⟩ := by
  decide +kernel

/-- Generic `impl<T> Area for Wrapper<T>` entry (`traitRef.args = [Wrapper<T>]`). -/
def fxWrapperGenericEntry : TraitImplEntry :=
  ⟨⟨"fx::Area::area", [.adt "fx::Wrapper" [.param 0 "T"]]⟩,
    "fx::<impl<T> Area for Wrapper<T>>::area"⟩

/-- Specialized `impl Area for Wrapper<u32>` entry (`traitRef.args = [Wrapper<u32>]`). -/
def fxWrapperU32Entry : TraitImplEntry :=
  ⟨⟨"fx::Area::area", [.adt "fx::Wrapper" [.uint .u32]]⟩,
    "fx::<impl Area for Wrapper<u32>>::area"⟩

/-- Explicit default-method inheritance entry `impl Area for Square` (`implPath = defPath`). -/
def fxSquareDefaultEntry : TraitImplEntry :=
  ⟨⟨"fx::Area::area", [.adt "fx::Square" []]⟩, "fx::Area::area"⟩

/-- Default trait method body `fn Area::area<Self>() -> u32 { 11 }` (`typeParamCount = 1`). -/
def fxDefaultArea : CapturedMir := fxLeaf "fx::Area::area" 11 1 []

/-- Generic override body `fn <impl<T> Area for Wrapper<T>>::area<T>() -> u32 { 22 }`. -/
def fxWrapperGenericArea : CapturedMir :=
  fxLeaf "fx::<impl<T> Area for Wrapper<T>>::area" 22 1 []

/-- Specialized monomorphic override body `fn <impl Area for Wrapper<u32>>::area() -> u32 { 33 }`. -/
def fxWrapperU32Area : CapturedMir :=
  fxLeaf "fx::<impl Area for Wrapper<u32>>::area" 33 0 []

/-- Opaque callee table with default trait method, generic override, and specialized override. -/
def fxSpecTbl : OpaqueCalleeTable :=
  .ofList [fxDefaultArea, fxWrapperGenericArea, fxWrapperU32Area]

/-- Registered `TraitImplEntry` records exercising specificity and default inheritance. -/
def fxSpecExtra : List TraitImplEntry :=
  [fxWrapperGenericEntry, fxWrapperU32Entry, fxSquareDefaultEntry]

/-- **Specificity, polymorphic override, and default-method inheritance canary**:
1. On `Wrapper<u32>`, both `impl<T> Area for Wrapper<T>` and `impl Area for Wrapper<u32>`
   match `traitMatches` (2 candidates), and `filterMostSpecificTraitImpls` selects the
   strictly more specific `Wrapper<u32>` override (`lookupCallee_trait_hit`).
2. On `Wrapper<bool>`, the generic `impl<T> Area for Wrapper<T>` wins and is instantiated
   at `T = bool` (`lookupCallee_trait_hit_poly`).
3. On `Square`, `fxSquareDefaultEntry` (`implPath = "fx::Area::area"`) inherits the
   default trait method body `fxDefaultArea` and instantiates `Self = Square`
   (`lookupCallee_trait_default_hit`). -/
theorem canary_trait_specificity_and_default_inheritance :
    (traitMatches fxSpecTbl fxSpecExtra "fx::Area::area"
        [.adt "fx::Wrapper" [.uint .u32]]).length = 2 ∧
    fxSpecTbl.lookup fxLayouts "fx::Area::area"
        [.adt "fx::Wrapper" [.uint .u32]] fxSpecExtra =
      some fxWrapperU32Area ∧
    fxSpecTbl.lookup fxLayouts "fx::Area::area"
        [.adt "fx::Wrapper" [.bool]] fxSpecExtra =
      some (fxWrapperGenericArea.instantiate [(.bool, fxBoolLayout)]) ∧
    fxSpecTbl.lookup fxLayouts "fx::Area::area"
        [.adt "fx::Square" []] fxSpecExtra =
      some (fxDefaultArea.instantiate [(.adt "fx::Square" [], fxUnitLayout)]) := by
  refine ⟨by decide +kernel, ?_, ?_, ?_⟩
  · apply lookupCallee_trait_hit (winner := fxWrapperU32Entry) (by decide) (by decide +kernel)
      ?_ (by decide) rfl
    unfold fxSpecTbl
    rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  · apply lookupCallee_trait_hit_poly (winner := fxWrapperGenericEntry) (implArgs := [.bool])
      (argLayouts := [fxBoolLayout]) (by decide) (by decide +kernel) ?_ (by decide) rfl rfl
      (by decide)
    unfold fxSpecTbl
    rw [lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  · apply lookupCallee_trait_default_hit (winner := fxSquareDefaultEntry) (implArgs := [.adt "fx::Square" []])
      (argLayouts := [fxUnitLayout]) (by decide) (by decide +kernel) rfl ?_ rfl (by decide)
    unfold fxSpecTbl
    exact lookupRaw_ofList_cons_hit rfl

/-- **Free generic certificate canary**: `fx::poly` has no `TraitImplEntry` in
`multiFullTbl` (which does register `impl Area for Circle`), so *one* per-`defPath`
certificate (`hno`) plus one raw certificate resolve both the concrete
instantiation `poly::<u32>` and a still-generic caller's `poly::<T>`
(`.param 0 "T"`, outside `lookupCallee_hit_poly`) to the instantiated body. -/
theorem canary_free_poly_param_and_concrete :
    multiFullTbl.lookup fxLayouts "fx::poly" [.uint .u32] [] =
      some (fxPoly.instantiate [(.uint .u32, fxU32Layout)]) ∧
    multiFullTbl.lookup fxLayouts "fx::poly" [.param 0 "T"] [] =
      some (fxPoly.instantiate [(.param 0 "T", fxUnitLayout)]) := by
  have hno : hasTraitImplForDefPath ([] ++ flatMapTraitImpls multiFullTbl.toList)
      "fx::poly" = false := by
    decide +kernel
  have hraw : multiFullTbl.lookupRaw "fx::poly" = some fxPoly := by
    unfold multiFullTbl
    rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  have hlayP : instantiationLayouts? fxLayouts [.param 0 "T"] = some [fxUnitLayout] := by
    decide
  exact ⟨lookupCallee_hit_free_poly hno hraw rfl canary_u32_instantiationLayouts,
    lookupCallee_hit_free_poly hno hraw rfl hlayP⟩

/-- **`tbl.toList`-free free-generic certificate canary**: reuses the per-table
`multiFullTbl_traitImpls` certificate (`multiFullTbl.traitImpls = [fxAreaEntry]`)
so `hno` checks only the 1-entry `TraitImplEntry` list `[fxAreaEntry]`
without ever unfolding `multiFullTbl.toList`. -/
theorem canary_free_poly_opaque_cert :
    multiFullTbl.lookup fxLayouts "fx::poly" [.uint .u32] [] =
      some (fxPoly.instantiate [(.uint .u32, fxU32Layout)]) ∧
    multiFullTbl.lookup fxLayouts "fx::poly" [.param 0 "T"] [] =
      some (fxPoly.instantiate [(.param 0 "T", fxUnitLayout)]) := by
  have hno : hasTraitImplForDefPath ([] ++ [fxAreaEntry]) "fx::poly" = false := by
    decide
  have hraw : multiFullTbl.lookupRaw "fx::poly" = some fxPoly := by
    unfold multiFullTbl
    rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  have hlayP : instantiationLayouts? fxLayouts [.param 0 "T"] = some [fxUnitLayout] := by
    decide
  exact ⟨lookupCallee_hit_free_poly_opaque multiFullTbl_traitImpls hno hraw rfl
      canary_u32_instantiationLayouts,
    lookupCallee_hit_free_poly_opaque multiFullTbl_traitImpls hno hraw rfl hlayP⟩

/-- **`tbl.toList`-free trait-dispatch certificate canary**: resolves
`<Circle as Area>::area` on `multiFullTbl` using *only* the one-time table
certificate `multiFullTbl_traitImpls`, `collectMatchingTraitImplsWith_cons_hit_mono`,
and the `O(1)` `lookupRaw` certificate for `fxCircleArea` — zero `tbl.toList`
unfolding and zero `decide +kernel` over the callee list. -/
theorem canary_trait_cert_no_toList :
    multiFullTbl.lookup fxLayouts "fx::Area::area" [fxCircleTy] [] =
      some fxCircleArea := by
  have himpl : multiFullTbl.lookupRaw "fx::<impl Area for Circle>::area" =
      some fxCircleArea := by
    unfold multiFullTbl
    rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide),
      lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide),
      lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  have hcollect :
      collectMatchingTraitImplsWith multiFullTbl.lookupRaw ([] ++ [fxAreaEntry])
        "fx::Area::area" [fxCircleTy] [] = [(fxAreaEntry, some [])] := by
    rw [List.nil_append,
      collectMatchingTraitImplsWith_cons_hit_mono (c := fxCircleArea)
        (by decide) rfl (by decide) himpl (by decide) rfl]
    rfl
  exact lookupCallee_trait_hit_cert (winner := fxAreaEntry) (by decide)
    multiFullTbl_traitImpls hcollect (by decide) himpl (by decide) rfl

/-- One-time `traitImpls` certificate for `fxSpecTbl`. -/
theorem fxSpecTbl_traitImpls : fxSpecTbl.traitImpls = [] := by
  unfold fxSpecTbl
  rw [traitImpls_ofList]
  rfl

/-- **`tbl.toList`-free polymorphic & default-method trait-dispatch certificate canary**:
resolves both `<Wrapper<bool> as Area>::area` (polymorphic `TraitImplEntry` override)
and `<Square as Area>::area` (default trait method inheritance) on `fxSpecTbl`
using `lookupCallee_trait_hit_poly_cert`, `lookupCallee_trait_default_hit_cert`,
`collectMatchingTraitImplsWith_cons_hit_poly`,
`collectMatchingTraitImplsWith_cons_hit_default`, and `collectMatchingTraitImplsWith_cons_ne_args`
without ever unfolding `fxSpecTbl.toList`. -/
theorem canary_trait_poly_and_default_cert_no_toList :
    fxSpecTbl.lookup fxLayouts "fx::Area::area"
        [.adt "fx::Wrapper" [.bool]] fxSpecExtra =
      some (fxWrapperGenericArea.instantiate [(.bool, fxBoolLayout)]) ∧
    fxSpecTbl.lookup fxLayouts "fx::Area::area"
        [.adt "fx::Square" []] fxSpecExtra =
      some (fxDefaultArea.instantiate [(.adt "fx::Square" [], fxUnitLayout)]) := by
  have hdefRaw : fxSpecTbl.lookupRaw "fx::Area::area" = some fxDefaultArea := by
    unfold fxSpecTbl
    exact lookupRaw_ofList_cons_hit rfl
  have hgenRaw : fxSpecTbl.lookupRaw "fx::<impl<T> Area for Wrapper<T>>::area" =
      some fxWrapperGenericArea := by
    unfold fxSpecTbl
    rw [lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  have hcollectPoly :
      collectMatchingTraitImplsWith fxSpecTbl.lookupRaw (fxSpecExtra ++ [])
        "fx::Area::area" [.adt "fx::Wrapper" [.bool]] [] =
          [(fxWrapperGenericEntry, some [.bool])] := by
    unfold fxSpecExtra
    rw [List.append_nil,
      collectMatchingTraitImplsWith_cons_hit_poly (c := fxWrapperGenericArea)
        (subst := [(0, .bool)]) (methodTypeArgs := []) (implHeaderArgs := [.bool])
        (by decide) rfl (by decide) (by decide) hgenRaw (by decide) (by decide),
      collectMatchingTraitImplsWith_cons_ne_args (by decide) (by decide),
      collectMatchingTraitImplsWith_cons_ne_args (by decide) (by decide)]
    rfl
  have hcollectDef :
      collectMatchingTraitImplsWith fxSpecTbl.lookupRaw (fxSpecExtra ++ [])
        "fx::Area::area" [.adt "fx::Square" []] [] =
          [(fxSquareDefaultEntry, some [.adt "fx::Square" []])] := by
    unfold fxSpecExtra
    rw [List.append_nil,
      collectMatchingTraitImplsWith_cons_ne_args (by decide) (by decide),
      collectMatchingTraitImplsWith_cons_ne_args (by decide) (by decide),
      collectMatchingTraitImplsWith_cons_hit_default (c := fxDefaultArea)
        (subst := []) (methodTypeArgs := []) (implHeaderArgs := [])
        (by decide) rfl (by decide) (by decide) hdefRaw (by decide) (by decide)]
    rfl
  refine ⟨?_, ?_⟩
  · exact lookupCallee_trait_hit_poly_cert (winner := fxWrapperGenericEntry)
      (implArgs := [.bool]) (argLayouts := [fxBoolLayout])
      (by decide) fxSpecTbl_traitImpls hcollectPoly (by decide) hgenRaw
      (by decide) rfl rfl (by decide)
  · exact lookupCallee_trait_default_hit_cert (winner := fxSquareDefaultEntry)
      (implArgs := [.adt "fx::Square" []]) (argLayouts := [fxUnitLayout])
      (by decide) fxSpecTbl_traitImpls hcollectDef (by decide) rfl hdefRaw
      rfl (by decide)


/-! ## Unconditional trusted frame lemma in use -/

/-- **Decide-free trusted agreement**: `evalWithOpaqueCallees_eq_trusted_initWithCallees`
discharges the `memory.callees` / `memory.traitImpls` frame condition that
`canary_evalWithOpaqueCallees_eq_trusted` checks by kernel evaluation of the whole run. -/
theorem canary_evalWithOpaqueCallees_eq_trusted_unconditional :
    evalWithOpaqueCallees canaryFullTbl canaryRoot 8 canaryInitWithCallees =
      runSteps (stepMirFn canaryRoot) 8 canaryInitWithCallees [] :=
  evalWithOpaqueCallees_eq_trusted_initWithCallees canaryFullTbl canaryRoot [] 8

/-- Entry state of `multiRoot` linking `multiFullTbl` in `memory.callees`. -/
def multiInitWithCallees : MachineState :=
  initMachineStateWithCallees multiRoot [] multiFullTbl.toList

/-- **The frame lemma covers calls outside `MirLiftCore.StepConeSafe`**: `multiRoot` makes a
polymorphic call (`poly::<u32>`) and a trait-dispatched call (`<Circle as Area>::area`), which
`MirLiftCore.directCallInCone` rejects (`typeArgs ≠ []`), yet the opaque run from the linked
entry state is the trusted run by the unconditional theorem alone, and it halts returning
`31`. -/
theorem canary_frame_poly_trait_unconditional :
    evalWithOpaqueCallees multiFullTbl multiRoot 12 multiInitWithCallees =
      runSteps (stepMirFn multiRoot) 12 multiInitWithCallees [] ∧
    (runSteps (stepMirFn multiRoot) 12 multiInitWithCallees []).summary =
      ⟨.halted, [.event 0], some 31, none⟩ ∧
    MirLiftCore.directCallInCone ["fx::poly", "fx::Area::area"]
      (fxFnItem "fx::poly" [.uint .u32]) = false ∧
    MirLiftCore.directCallInCone ["fx::poly", "fx::Area::area"]
      (fxFnItem "fx::Area::area" [fxCircleTy]) = false :=
  ⟨evalWithOpaqueCallees_eq_trusted_initWithCallees multiFullTbl multiRoot [] 12,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Non-vacuity of the frame lemma**: along the `multiRoot` run the active callee changes
(frames are pushed and popped), while `memory.callees` and `memory.traitImpls` stay fixed at
*every* visited state — by `trusted_runVisited_frames`, with no per-state check. -/
theorem canary_frame_nonvacuous :
    (runVisited (stepMirFn multiRoot) 12 multiInitWithCallees).any
        (fun s => s.memory.activeCallee.isSome) = true ∧
      ∀ s' ∈ runVisited (stepMirFn multiRoot) 12 multiInitWithCallees,
        s'.memory.callees = multiFullTbl.toList ∧ s'.memory.traitImpls = multiRoot.traitImpls := by
  refine ⟨by decide +kernel, fun s' hs' => ?_⟩
  have h := trusted_runVisited_frames multiRoot 12 multiInitWithCallees s' hs'
  exact ⟨h.1.trans (initMachineStateWithCallees_callees _ _ _),
    h.2.trans (initMachineStateWithCallees_traitImpls _ _ _)⟩

/-- **The linked-table hypothesis is necessary**: from `canaryInit` (`memory.callees = []`)
the opaque evaluator over `canaryFullTbl` and the trusted machine disagree (the opaque run
halts with `live_f`'s `7`, the trusted run stops at an external call). -/
theorem canary_unconditional_requires_linked_table :
    evalWithOpaqueCallees canaryFullTbl canaryRoot 8 canaryInit ≠
      runSteps (stepMirFn canaryRoot) 8 canaryInit [] := by
  decide +kernel

/-- Every key demanded along a pruned run carries the start state's trait impls
(`demandedKeys_extraTraitImpls`), here on the polymorphic + trait-dispatch run. -/
theorem canary_demandedKeys_extraTraitImpls :
    ∀ k ∈ demandedKeys multiFullTbl.lookup multiRoot 12 multiInit,
      k.extraTraitImpls = multiInit.memory.traitImpls :=
  demandedKeys_extraTraitImpls multiFullTbl.lookup multiRoot 12 multiInit

/-! ## Bridge to `Anneal.MirLiftCore` -/

/-- Call cone of `canaryRoot`'s live run. -/
def canaryCone : List DefPath := ["fx::live_f"]

/-- `live_f`'s raw certificate in the full table. -/
theorem canaryFullTbl_lookupRaw_live :
    canaryFullTbl.lookupRaw "fx::live_f" = some fxLiveF := by
  unfold canaryFullTbl
  rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide)]
  exact lookupRaw_ofList_cons_hit rfl

/-- **`AgreesOn` from `O(1)` raw certificates** (no `toList` unfolding) and its
`MirLiftCore.calleesAgreeOn` form on the sealed lists. -/
theorem canary_agreesOn_live :
    OpaqueCalleeTable.AgreesOn canaryCone canaryNarrowTbl canaryFullTbl ∧
      MirLiftCore.calleesAgreeOn canaryCone canaryNarrowTbl.toList canaryFullTbl.toList := by
  have h : OpaqueCalleeTable.AgreesOn canaryCone canaryNarrowTbl canaryFullTbl := by
    intro dp hdp
    simp only [canaryCone, List.mem_singleton] at hdp
    subst hdp
    rw [canaryFullTbl_lookupRaw_live]
    exact lookupRaw_ofList_cons_hit rfl
  exact ⟨h, calleesAgreeOn_of_agreesOn h⟩

/-- **Opaque cone narrowing from `calleesAgreeOn`**: the only demanded key is the monomorphic
live call, inside `canaryCone`, so agreement on the cone alone narrows the run
(`evalWithOpaqueCallees_cone_narrow_of_agreesOn`, no per-key lookup certificate). -/
theorem canary_cone_narrow_of_agreesOn :
    evalWithOpaqueCallees canaryNarrowTbl canaryRoot 8 canaryInit =
      evalWithOpaqueCallees canaryFullTbl canaryRoot 8 canaryInit := by
  apply evalWithOpaqueCallees_cone_narrow_of_agreesOn canaryCone _ _ _ _ _ canary_agreesOn_live.1
  rw [canary_deadArm_demandedKeys]
  intro k hk
  simp only [List.mem_singleton] at hk
  subst hk
  exact ⟨List.Mem.head _, rfl⟩

/-- Syntactic call cone of `canaryRoot` over `canaryFullTbl`: both arms and the panic. -/
def canaryClosedCone : List DefPath := ["fx::live_f", "fx::g_dead", "core::panicking::panic"]

/-- The canonical narrowing of `canaryFullTbl` to `canaryClosedCone` (fillers dropped). -/
def canaryClosedTbl : OpaqueCalleeTable := canaryFullTbl.narrowToCone canaryClosedCone

/-- `MirLiftCore.CallConeClosed` holds for `canaryRoot` over the full table (one-time
decidable check). -/
theorem canary_callConeClosed :
    MirLiftCore.CallConeClosed canaryClosedCone canaryRoot canaryFullTbl.toList = true := by
  decide +kernel

theorem canaryFullTbl_toList_ne_nil : canaryFullTbl.toList ≠ [] :=
  toList_ne_nil_of_lookupRaw canaryFullTbl_lookupRaw_live

theorem canaryClosedTbl_toList_ne_nil : canaryClosedTbl.toList ≠ [] :=
  toList_ne_nil_of_lookupRaw
    ((lookupRaw_narrowToCone canaryFullTbl (List.Mem.head _)).trans canaryFullTbl_lookupRaw_live)

/-- A halted run summary comes from a halted run. -/
theorem RunResult.halted_of_summary {r : RunResult} (h : r.summary.tag = .halted) :
    ∃ out tr, r = .halted out tr := by
  cases r with
  | halted out tr => exact ⟨out, tr, rfl⟩
  | faulted _ _ => nomatch h
  | external _ _ => nomatch h
  | outOfFuel _ _ => nomatch h

/-- **Opaque evaluation → `MirLiftCore.runCfgWithCallees` → narrowed table**: the opaque run
from the multi-callee entry state halts, so `runCfgWithCallees` with the sealed list returns the
same outcome (`runCfgWithCallees_of_evalWithOpaqueCallees_halted`), and with the canonical cone
narrowing it returns its `withCallees` image (`runCfgWithCallees_cone_narrow_of_agreesOn_closed`),
with agreement stated over `lookupRaw` only. -/
theorem canary_runCfgWithCallees_bridge :
    ∃ out, MirLiftCore.runCfgWithCallees 9 canaryRoot [] emptyMemory canaryFullTbl.toList =
        some out ∧
      MirLiftCore.runCfgWithCallees 9 canaryRoot [] emptyMemory canaryClosedTbl.toList =
        some (MirLiftCore.MirOutcome.mapMem
          (MirLiftCore.Memory.withCallees canaryClosedTbl.toList) out) := by
  have hhalt : (evalWithOpaqueCallees canaryFullTbl canaryRoot 8
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees canaryRoot [] emptyMemory
        canaryFullTbl.toList)).summary.tag = .halted := by
    decide +kernel
  obtain ⟨out, tr, hrun⟩ := RunResult.halted_of_summary hhalt
  have h₁ := runCfgWithCallees_of_evalWithOpaqueCallees_halted canaryFullTbl canaryRoot []
    emptyMemory 8 out tr canaryFullTbl_toList_ne_nil hrun
  refine ⟨out, h₁, ?_⟩
  rw [runCfgWithCallees_cone_narrow_of_agreesOn_closed canaryClosedCone 9 canaryRoot []
    emptyMemory canaryFullTbl_toList_ne_nil canaryClosedTbl_toList_ne_nil
    (agreesOn_narrowToCone canaryClosedCone canaryFullTbl) canary_callConeClosed rfl rfl, h₁]
  rfl

/-- **`wpMirExecSym` transfer between opaque tables**: every callee-insensitive postcondition
transfers between the entry states of `canaryFullTbl` and its cone narrowing. -/
theorem canary_wpMirExecSym_bridge (post : MirOutcome → Prop)
    (h_post : ∀ out, post (MirLiftCore.MirOutcome.mapMem
      (MirLiftCore.Memory.withCallees canaryClosedTbl.toList) out) ↔ post out) :
    Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym 9 canaryRoot
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees canaryRoot []
          emptyMemory canaryClosedTbl.toList)) post ↔
      Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym 9 canaryRoot
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees canaryRoot []
          emptyMemory canaryFullTbl.toList)) post :=
  wpMirExecSym_cone_narrow_of_agreesOn canaryClosedCone 9 canaryRoot [] emptyMemory
    canaryFullTbl_toList_ne_nil canaryClosedTbl_toList_ne_nil
    (agreesOn_narrowToCone canaryClosedCone canaryFullTbl) post h_post
    (MirLiftCore.coneReach_of_closedInv canary_callConeClosed 9 _
      (MirLiftCore.closedInv_init canaryClosedCone canaryRoot [] emptyMemory
        canaryFullTbl_toList_ne_nil rfl rfl))

/-- **`CalleeInitWf` agreement down to the empty table**: over the clean `emptyMemory`
(`callees = []`, `traitImpls = canaryRoot.traitImpls`) the empty sealed table satisfies
`MirLiftCore.CalleeInitWf`, so the opaque evaluator over it is the trusted machine. -/
theorem canary_initWithMemory_empty_of_wf :
    evalWithOpaqueCallees (OpaqueCalleeTable.ofList []) canaryRoot 8
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees canaryRoot [] emptyMemory
          (OpaqueCalleeTable.ofList []).toList) =
      runSteps (stepMirFn canaryRoot) 8
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees canaryRoot [] emptyMemory
          (OpaqueCalleeTable.ofList []).toList) [] :=
  evalWithOpaqueCallees_eq_trusted_initWithMemoryAndCallees_of_wf _ _ _ _ _ (Or.inr ⟨rfl, rfl⟩)

/-- An entry memory whose own callee list already links `live_f`. -/
def linkedMemory : Memory := { emptyMemory with callees := [fxLiveF] }

/-- **`CalleeInitWf` is necessary**: the empty table over `linkedMemory` leaves
`memory.callees = [live_f]` in place, so the trusted machine resolves the live call while the
opaque evaluator over the empty table stops at an external call. -/
theorem canary_initWithMemory_requires_wf :
    ¬ MirLiftCore.CalleeInitWf canaryRoot linkedMemory (OpaqueCalleeTable.ofList []).toList ∧
      evalWithOpaqueCallees (OpaqueCalleeTable.ofList []) canaryRoot 8
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees canaryRoot []
            linkedMemory (OpaqueCalleeTable.ofList []).toList) ≠
        runSteps (stepMirFn canaryRoot) 8
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees canaryRoot []
            linkedMemory (OpaqueCalleeTable.ofList []).toList) [] := by
  refine ⟨?_, by decide +kernel⟩
  rintro (h | ⟨h, _⟩)
  · exact h (OpaqueCalleeTable.toList_ofList [])
  · nomatch h

/-- **Syntactic narrowing all the way down to the empty table** (`_closed_wf`): the leaf
`live_f` makes no calls, so over the clean `emptyMemory` its empty call cone narrows the full
table to the empty one, and the run halts on both sides. -/
theorem canary_runCfgWithCallees_narrow_to_empty :
    MirLiftCore.runCfgWithCallees 4 fxLiveF [] emptyMemory
        (OpaqueCalleeTable.ofList []).toList =
      (MirLiftCore.runCfgWithCallees 4 fxLiveF [] emptyMemory canaryFullTbl.toList).map
        (MirLiftCore.MirOutcome.mapMem
          (MirLiftCore.Memory.withCallees (OpaqueCalleeTable.ofList []).toList)) ∧
      (MirLiftCore.runCfgWithCallees 4 fxLiveF [] emptyMemory canaryFullTbl.toList).isSome =
        true :=
  ⟨runCfgWithCallees_cone_narrow_of_agreesOn_closed_wf [] 4 fxLiveF [] emptyMemory
      (Or.inl canaryFullTbl_toList_ne_nil) (Or.inr ⟨rfl, rfl⟩) (fun _ h => nomatch h)
      (by decide +kernel) rfl rfl,
    by decide +kernel⟩

/-- Root whose live arm calls the generic `poly::<u32>` (dead arm: `g_dead`). -/
def polyRoot : CapturedMir := fxLitIfRoot true "fx::poly" [.uint .u32] "fx::g_dead"

/-- Fillers and an unrelated trait-impl holder around `poly` and `g_dead`. -/
def polyFullTbl : OpaqueCalleeTable :=
  .ofList [fxFillerA, fxPoly, fxGDead, fxAreaImplHolder, fxFillerB]

/-- Syntactic call cone of `polyRoot`. -/
def polyCone : List DefPath := ["fx::poly", "fx::g_dead", "core::panicking::panic"]

theorem polyFullTbl_lookupRaw_poly : polyFullTbl.lookupRaw "fx::poly" = some fxPoly := by
  unfold polyFullTbl
  rw [lookupRaw_ofList_cons_miss (by decide)]
  exact lookupRaw_ofList_cons_hit rfl

/-- The monomorphic closure check rejects the generic call; the polymorphic one accepts it. -/
theorem canary_polyCone_closed :
    MirLiftCore.CallConeClosed polyCone polyRoot polyFullTbl.toList = false ∧
      MirLiftCore.CallConeClosedPoly polyCone polyRoot polyFullTbl.toList polyRoot.traitImpls =
        true := by
  decide +kernel

/-- **Polymorphic syntactic narrowing between opaque tables** (`_closed_poly_wf`): the generic
callee is monomorphized by `CapturedMir.instantiate` along the run, and the narrowed table's
trait-impl side condition is checked over its sealed `traitImpls`. -/
theorem canary_runCfgWithCallees_poly_bridge :
    ∃ out, MirLiftCore.runCfgWithCallees 9 polyRoot [] emptyMemory polyFullTbl.toList =
        some out ∧
      MirLiftCore.runCfgWithCallees 9 polyRoot [] emptyMemory
          (polyFullTbl.narrowToCone polyCone).toList =
        some (MirLiftCore.MirOutcome.mapMem
          (MirLiftCore.Memory.withCallees (polyFullTbl.narrowToCone polyCone).toList) out) := by
  have hwf₁ : MirLiftCore.CalleeInitWf polyRoot emptyMemory polyFullTbl.toList :=
    calleeInitWf_of_lookupRaw polyRoot emptyMemory polyFullTbl_lookupRaw_poly
  have hwf₂ : MirLiftCore.CalleeInitWf polyRoot emptyMemory
      (polyFullTbl.narrowToCone polyCone).toList :=
    calleeInitWf_of_lookupRaw polyRoot emptyMemory
      ((lookupRaw_narrowToCone (cone := polyCone) polyFullTbl (List.Mem.head _)).trans
        polyFullTbl_lookupRaw_poly)
  have hhalt : (evalWithOpaqueCallees polyFullTbl polyRoot 8
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees polyRoot [] emptyMemory
        polyFullTbl.toList)).summary.tag = .halted := by
    decide +kernel
  obtain ⟨out, tr, hrun⟩ := RunResult.halted_of_summary hhalt
  have h₁ := runCfgWithCallees_of_evalWithOpaqueCallees_halted_of_wf polyFullTbl polyRoot []
    emptyMemory 8 out tr hwf₁ hrun
  refine ⟨out, h₁, ?_⟩
  rw [runCfgWithCallees_cone_narrow_of_agreesOn_closed_poly_wf polyCone 9 polyRoot []
    emptyMemory hwf₁ hwf₂ (agreesOn_narrowToCone polyCone polyFullTbl)
    canary_polyCone_closed.2 (by decide +kernel) rfl rfl, h₁]
  rfl

/-- Shadowed duplicate of `fx::live_f` whose unreachable body calls `"fx::outside_cone"`.
When placed *after* `fxLiveF` in a callee table, `findCallee?` / `lookupRaw` never selects it,
yet `MirLiftCore.CallConeClosed` scans every list element with `defPath ∈ cone` and falsely
rejects the table (`false`). -/
def fxLiveFShadowed : CapturedMir :=
  { defPath := "fx::live_f", phase := .runtimePostCleanup, role := .subject, argCount := 0,
    localDecls := [⟨.mut, fxU32Ty, some "_0"⟩],
    basicBlocks := [
      fxCallBlock "fx::outside_cone" [] 1,
      ⟨[], ⟨.return_, "shadow:ret"⟩, false⟩ ],
    fnAbi := fxRetU32Abi, layouts := fxLayouts, allocations := [] }

/-- Table where `fxLiveFShadowed` is shadowed by `fxLiveF`. -/
def canaryShadowedTbl : OpaqueCalleeTable :=
  .ofList [fxFillerA, fxLiveF, fxGDead, fxLiveFShadowed]

/-- **`tbl.toList`-free `OpaqueCalleeTable.callConeClosed` & shadowed-duplicate canary**:
1. `canaryFullTbl.callConeClosed canaryClosedCone canaryRoot = true` is proved purely from
   `O(1)` `lookupRaw` certificates on the 3 cone paths (zero `canaryFullTbl.toList` unfolding!).
2. On `canaryShadowedTbl`, `MirLiftCore.CallConeClosed` falsely returns `false` (tripped by the
   shadowed `fxLiveFShadowed`), whereas `OpaqueCalleeTable.callConeClosed` queries `lookupRaw`
   (first-match) and returns `true`, enabling `runCfgWithCallees_cone_narrow_of_callConeClosed_wf`!
3. `polyFullTbl.callConeClosedPoly` narrows `polyRoot` via
   `runCfgWithCallees_cone_narrow_of_callConeClosedPoly_wf` without unfolding `polyFullTbl.toList`. -/
theorem canary_callConeClosed_no_toList_and_shadowed_dup :
    canaryFullTbl.callConeClosed canaryClosedCone canaryRoot = true ∧
    MirLiftCore.CallConeClosed canaryClosedCone canaryRoot canaryShadowedTbl.toList = false ∧
    canaryShadowedTbl.callConeClosed canaryClosedCone canaryRoot = true ∧
    MirLiftCore.runCfgWithCallees 9 canaryRoot [] emptyMemory
        (canaryShadowedTbl.narrowToCone canaryClosedCone).toList =
      (MirLiftCore.runCfgWithCallees 9 canaryRoot [] emptyMemory canaryShadowedTbl.toList).map
        (MirLiftCore.MirOutcome.mapMem
          (MirLiftCore.Memory.withCallees
            (canaryShadowedTbl.narrowToCone canaryClosedCone).toList)) ∧
    MirLiftCore.runCfgWithCallees 9 polyRoot [] emptyMemory
        (polyFullTbl.narrowToCone polyCone).toList =
      (MirLiftCore.runCfgWithCallees 9 polyRoot [] emptyMemory polyFullTbl.toList).map
        (MirLiftCore.MirOutcome.mapMem
          (MirLiftCore.Memory.withCallees (polyFullTbl.narrowToCone polyCone).toList)) := by
  have hgdead : canaryFullTbl.lookupRaw "fx::g_dead" = some fxGDead := by
    unfold canaryFullTbl
    rw [lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  have hpanic : canaryFullTbl.lookupRaw "core::panicking::panic" = none := by
    unfold canaryFullTbl
    rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide),
      lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide),
      OpaqueCalleeTable.lookupRaw_eq, OpaqueCalleeTable.toList_ofList]
    rfl
  have hclosedNoToList : canaryFullTbl.callConeClosed canaryClosedCone canaryRoot = true := by
    simp only [OpaqueCalleeTable.callConeClosed, canaryClosedCone, List.all_cons, List.all_nil,
      canaryFullTbl_lookupRaw_live, hgdead, hpanic]
    decide
  have hshadowLive : canaryShadowedTbl.lookupRaw "fx::live_f" = some fxLiveF := by
    unfold canaryShadowedTbl
    rw [lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  have hwfS₁ : MirLiftCore.CalleeInitWf canaryRoot emptyMemory canaryShadowedTbl.toList :=
    calleeInitWf_of_lookupRaw canaryRoot emptyMemory hshadowLive
  have hwfS₂ : MirLiftCore.CalleeInitWf canaryRoot emptyMemory
      (canaryShadowedTbl.narrowToCone canaryClosedCone).toList :=
    calleeInitWf_of_lookupRaw canaryRoot emptyMemory
      ((lookupRaw_narrowToCone (cone := canaryClosedCone) canaryShadowedTbl
        (List.Mem.head _)).trans hshadowLive)
  have hwfP₁ : MirLiftCore.CalleeInitWf polyRoot emptyMemory polyFullTbl.toList :=
    calleeInitWf_of_lookupRaw polyRoot emptyMemory polyFullTbl_lookupRaw_poly
  have hwfP₂ : MirLiftCore.CalleeInitWf polyRoot emptyMemory
      (polyFullTbl.narrowToCone polyCone).toList :=
    calleeInitWf_of_lookupRaw polyRoot emptyMemory
      ((lookupRaw_narrowToCone (cone := polyCone) polyFullTbl (List.Mem.head _)).trans
        polyFullTbl_lookupRaw_poly)
  refine ⟨hclosedNoToList, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · exact runCfgWithCallees_cone_narrow_of_callConeClosed_wf canaryClosedCone 9 canaryRoot []
      emptyMemory hwfS₁ hwfS₂ (agreesOn_narrowToCone canaryClosedCone canaryShadowedTbl)
      (by decide +kernel) rfl rfl
  · exact runCfgWithCallees_cone_narrow_of_callConeClosedPoly_wf polyCone 9 polyRoot []
      emptyMemory hwfP₁ hwfP₂ (agreesOn_narrowToCone polyCone polyFullTbl)
      (callConeClosedPoly_of_mirLiftCore canary_polyCone_closed.2)
      (by decide +kernel) rfl rfl


/-! ## Demand-time compiler queries -/


/-- **Negative coherence canary**: if a decoder populates an incoherent V2026_08_01
`LayoutTable` (`pointerBits = 32` while `layoutsV06.pointerBits = 64`),
`isLayoutCoherent` is `false` and `.v2026_08_01` `layoutOf` disagrees with
`.v2026_06_01` `layoutOf` on `&u32` (`4` bytes vs. `8` bytes). -/
theorem incoherence_breaks_dialect_agreement_canary :
    let badEnv : CompilerQueryEnv :=
      { schema := .v2026_08_01
        layoutsV06 := fxLayouts
        layoutsV08 := some { bridgeLayoutV06ToV08 fxLayouts with pointerBits := 32 }
        fnAbis := [], cfiTags := none, syncRegions := none, vtables := none }
    let refU32 : Ty := ⟨.ref .not (.uint .u32), 0⟩
    badEnv.isLayoutCoherent = false ∧
      evalCompilerQuery badEnv (.layoutOf .v2026_06_01 refU32) ≠
        evalCompilerQuery badEnv (.layoutOf .v2026_08_01 refU32) ∧
      (badEnv.withBridgedV08Layouts .v2026_08_01).isLayoutCoherent = true ∧
      evalCompilerQuery (badEnv.withBridgedV08Layouts .v2026_08_01) (.layoutOf .v2026_06_01 refU32) =
        evalCompilerQuery (badEnv.withBridgedV08Layouts .v2026_08_01) (.layoutOf .v2026_08_01 refU32) := by
  decide

/-- **Negative `EnvExtends` coherence canary**: when `env₁` is a `v2026_06_01`
environment (`env₁.v08Layouts? = none`, so `env₁.isLayoutCoherent = true` vacuously),
plain `EnvExtends env₁ env₂` only requires `OptionExtends none env₂.v08Layouts?`
(`True`) and therefore allows upgrading `env₁` to an *incoherent* `v2026_08_01`
environment `env₂` (`env₂.isLayoutCoherent = false`) whose V08 `layoutOf` answer
disagrees with `env₁`'s V06 `layoutOf` answer. -/
theorem envExtends_allows_incoherent_v08_upgrade_canary :
    let env₁ : CompilerQueryEnv :=
      { schema := .v2026_06_01
        layoutsV06 := fxLayouts
        layoutsV08 := none
        fnAbis := [], cfiTags := none, syncRegions := none, vtables := none }
    let env₂ : CompilerQueryEnv :=
      { schema := .v2026_08_01
        layoutsV06 := fxLayouts
        layoutsV08 := some { bridgeLayoutV06ToV08 fxLayouts with pointerBits := 32 }
        fnAbis := [], cfiTags := none, syncRegions := none, vtables := none }
    let refU32 : Ty := ⟨.ref .not (.uint .u32), 0⟩
    env₁.isLayoutCoherent = true ∧
      EnvExtends env₁ env₂ ∧
      env₂.isLayoutCoherent = false ∧
      evalCompilerQuery env₂ (.layoutOf .v2026_08_01 refU32) ≠
        evalCompilerQuery env₁ (.layoutOf .v2026_06_01 refU32) := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  exact ⟨by decide, rfl, (fun _ h => nomatch h), rfl, (fun _ h => nomatch h),
    (fun _ h => nomatch h), (fun _ h => nomatch h)⟩

/-- The alternative "schema-triggered" CFI semantics (CFI auto-checked whenever
`env.schema = .schema13`, even if the query did not request it). -/
def evalAbiAutoCfi (env : CompilerQueryEnv) (callerAbi : FnAbi) (callee : DefPath)
    (cfiCallSite : Option RigidTy) : QueryResult QueryAnswer :=
  match cfiCallSite, env.schema.hasSchema13 with
  | none, false => abiCore env callerAbi callee
  | site, _ =>
    match env.cfiEvidence? with
    | none => .unsupported .missingCfiEvidence
    | some spec =>
      match lookupDefPathAssoc spec.calleeTypeIds callee,
          lookupTyAssoc spec.callSiteTypeIds (site.getD (.fnPtr [] (.uint .u32) .safe .rust)) with
      | some a, some b => if a = b then abiCore env callerAbi callee else .err .cfiTypeIdMismatch
      | none, _ => .err (.cfiCalleeUntagged callee)
      | _, none => .err .cfiCallSiteUntagged

/-- Design-rationale environment (Schema 12). -/
def autoCfiEnv₁ : CompilerQueryEnv :=
  { schema := .v2026_06_01, layoutsV06 := fxLayouts, layoutsV08 := none,
    fnAbis := [("fx::f", fxRetU32Abi)], cfiTags := none, syncRegions := none,
    vtables := none }

/-- Its Schema-13 extension with CFI evidence that does not tag `fx::f`. -/
def autoCfiEnv₂ : CompilerQueryEnv :=
  { autoCfiEnv₁ with schema := .schema13, cfiTags := some ⟨[], []⟩ }

/-- **Why the CFI demand is part of the query key**: schema-triggered CFI checking
breaks monotonicity (a supported Schema-12 answer changes after a sound
upgrade), while `evalAbiCompatible` (CFI only when requested) satisfies
`query_mono_schema`. -/
theorem autoCfi_breaks_mono :
    EnvExtends autoCfiEnv₁ autoCfiEnv₂ ∧
      evalAbiAutoCfi autoCfiEnv₁ fxRetU32Abi "fx::f" none = .ok .abiOk ∧
      evalAbiAutoCfi autoCfiEnv₂ fxRetU32Abi "fx::f" none =
        .err (.cfiCalleeUntagged "fx::f") ∧
      evalCompilerQuery autoCfiEnv₂ (.abiCompatible fxRetU32Abi "fx::f" none) =
        evalCompilerQuery autoCfiEnv₁ (.abiCompatible fxRetU32Abi "fx::f" none) := by
  refine ⟨⟨by decide, rfl, OptionExtends.refl _, rfl, (fun _ h => nomatch h),
    OptionExtends.refl _, OptionExtends.refl _⟩, by decide, by decide, by decide⟩

/-! ### Part B canaries -/

/-- Schema-V2026_08_01 environment whose V08 material is the bridged V06 table. -/
def bridgeEnv : CompilerQueryEnv :=
  { schema := .v2026_08_01, layoutsV06 := fxLayouts,
    layoutsV08 := some (bridgeLayoutV06ToV08 fxLayouts), fnAbis := [], cfiTags := none,
    syncRegions := none, vtables := none }

/-- Cross-dialect agreement: V2026_06_01 and (bridged) V2026_08_01
`RigidTy.computeLayout` agree on scalar, aggregate, array, and pointer types. -/
theorem layoutOf_dialects_agree_canary :
    [fxU32Ty, fxBoolTy, (⟨.tuple [.bool, .uint .u32], 0⟩ : Ty), ⟨.array (.uint .u32) 3, 0⟩,
        ⟨.ref .not (.uint .u32), 0⟩, ⟨.ref .mut .str, 0⟩, ⟨.int .i64, 0⟩, ⟨.float .f64, 0⟩].all
      (fun ty => evalCompilerQuery bridgeEnv (.layoutOf .v2026_06_01 ty) ==
        evalCompilerQuery bridgeEnv (.layoutOf .v2026_08_01 ty)) = true := by
  decide

/-- `(bool, u32)` has size 8 / align 4 with fields at offsets 0 and 4; a V08
`layoutOf` under a V2026_06_01 producer fails closed. -/
theorem layoutOf_canary :
    (match evalCompilerQuery bridgeEnv (.layoutOf .v2026_06_01 ⟨.tuple [.bool, .uint .u32], 0⟩) with
      | .ok (.layout l) => some (l.size.bytes, l.align.bytes, l.fields)
      | _ => none) = some (8, 4, .arbitrary [⟨0⟩, ⟨4⟩] [0, 1]) ∧
    evalCompilerQuery { bridgeEnv with schema := .v2026_06_01 } (.layoutOf .v2026_08_01 fxU32Ty) =
      .unsupported .missingV08LayoutDialect ∧
    evalCompilerQuery bridgeEnv (.layoutOf .v2026_06_01 ⟨.str, 7⟩) = .err .layoutUncomputable := by
  decide

/-- ABI mismatch canaries (each a schema-independent `.err`). -/
theorem abiCompatible_canary :
    evalCompilerQuery autoCfiEnv₁ (.abiCompatible fxRetU32Abi "fx::f" none) = .ok .abiOk ∧
    evalCompilerQuery autoCfiEnv₁ (.abiCompatible { fxRetU32Abi with conv := .c } "fx::f" none) =
      .err .callConvMismatch ∧
    evalCompilerQuery autoCfiEnv₁
        (.abiCompatible { fxRetU32Abi with args := [⟨fxU32Layout, .direct⟩] } "fx::f" none) =
      .err .argCountMismatch ∧
    evalCompilerQuery autoCfiEnv₁
        (.abiCompatible { fxRetU32Abi with ret := ⟨fxBoolLayout, .direct⟩ } "fx::f" none) =
      .err .retAbiMismatch ∧
    evalCompilerQuery autoCfiEnv₁
        (.abiCompatible { fxRetU32Abi with canUnwind := false } "fx::f" none) =
      .err .unwindMismatch ∧
    evalCompilerQuery autoCfiEnv₁ (.abiCompatible fxRetU32Abi "fx::nope" none) =
      .err (.unknownCalleeAbi "fx::nope") := by
  decide

/-- Schema-13 environment with CFI type ids. -/
def cfiEnv : CompilerQueryEnv :=
  { autoCfiEnv₁ with
    schema := .schema13
    cfiTags := some ⟨[("fx::f", 42)], [(.fnPtr [] (.uint .u32) .safe .rust, 42),
      (.fnPtr [.bool] (.uint .u32) .safe .rust, 7)]⟩ }

/-- CFI canaries: matching type ids pass, mismatches are the CFI trap, and Schema
12 fails closed. -/
theorem cfi_canary :
    evalCompilerQuery cfiEnv (.abiCompatible fxRetU32Abi "fx::f"
      (some (.fnPtr [] (.uint .u32) .safe .rust))) = .ok .abiOk ∧
    evalCompilerQuery cfiEnv (.abiCompatible fxRetU32Abi "fx::f"
      (some (.fnPtr [.bool] (.uint .u32) .safe .rust))) = .err .cfiTypeIdMismatch ∧
    evalCompilerQuery cfiEnv (.abiCompatible fxRetU32Abi "fx::f"
      (some (.fnPtr [] .bool .safe .rust))) = .err .cfiCallSiteUntagged ∧
    evalCompilerQuery autoCfiEnv₁ (.abiCompatible fxRetU32Abi "fx::f"
      (some (.fnPtr [] (.uint .u32) .safe .rust))) = .unsupported .missingCfiEvidence := by
  decide


/-! ### End-to-end canary -/

/-- `Area` trait reference with `Self = dyn Area`. -/
def dynTraitRef : TraitRef := ⟨"fx::Area", [.dynamic "fx::Area"]⟩

/-- `*const ()` (receiver vtable pointers; layout index `0`). -/
def fxVtPtrTy : Ty := ⟨.rawPtr .not (.tuple []), 0⟩

/-- The `dyn Area` call site (receiver vtable pointer in local `_1`, slot `0`, not
CFI-instrumented). -/
def dynSite : DynCallSite :=
  { vtableLocal := 1, lookupOp := ⟨dynTraitRef, 0, [], none⟩, callerAbi := fxRetU32Abi,
    cfiCallSite := none, dynKey := ("fx::Area::area", [.dynamic "fx::Area"]) }

/-- `fn(vt: *const ()) -> u32 { if true { <dyn Area>::area() } else { g_dead() } }`. -/
def dynRoot : CapturedMir :=
  { fxLitIfRoot true "fx::Area::area" [.dynamic "fx::Area"] "fx::g_dead" with
    argCount := 1, localDecls := [⟨.mut, fxU32Ty, some "_0"⟩, ⟨.not, fxVtPtrTy, some "vt"⟩] }

/-- Initial state of `dynRoot`, called with a `Circle` receiver (vtable `7`). -/
def dynInit : MachineState := initMachineState dynRoot [.ptr ⟨7, 0⟩ 0]

/-- State at the live `dyn` call (after the literal switch). -/
def dynAtCall : MachineState :=
  { dynInit with frame := { blockIdx := 1, stmtIdx := 0, locals := dynInit.frame.locals } }

/-- `dynAtCall` is not hand-made: it is exactly the state the pruned literal
switch reaches from `dynInit` (after emitting branch event `1`), under any
resolver. -/
theorem dynAtCall_reached (r : CalleeResolver) :
    viewStepNode (stepBranchPruned r dynRoot dynInit) = .cont (some (.event 1)) (.running dynAtCall) :=
  rfl

/-- The receiver's vtable pointer at the call is read from the frame: vtable `7`. -/
theorem dyn_vtablePtr_atCall : dynSite.vtablePtr? dynAtCall = some ⟨7, 0⟩ := rfl

/-- `dynSite` is well formed: its call key `<dyn Area as Area>::area` is a virtual
call on `Area`, the trait of the receiver's vtable. -/
theorem dynSite_wellFormed : dynSite.wellFormed = true := by decide

/-- Schema-12 environment (no vtable evidence). -/
def dynEnv12 : CompilerQueryEnv :=
  { schema := .v2026_08_01, layoutsV06 := fxLayouts,
    layoutsV08 := some (bridgeLayoutV06ToV08 fxLayouts),
    fnAbis := [("fx::<impl Area for Circle>::area", fxRetU32Abi),
      ("fx::<impl Area for Square>::area", fxRetU32Abi)],
    cfiTags := none, syncRegions := none, vtables := none }

/-- Schema-13 extension with vtable evidence (`7 ↦ Circle`, `9 ↦ Square`). -/
def dynEnv13 : CompilerQueryEnv :=
  { dynEnv12 with
    schema := .schema13
    vtables := some [⟨7, dynTraitRef, [("fx::<impl Area for Circle>::area", [])], [], []⟩,
      ⟨9, dynTraitRef, [("fx::<impl Area for Square>::area", [])], [], []⟩] }

/-- A further extension populating sync-storage regions. -/
def dynEnv13Sync : CompilerQueryEnv := { dynEnv13 with syncRegions := some [⟨3, 4, 8⟩] }

/-- `impl Area for Square { fn area() -> u32 { 44 } }`. -/
def fxSquareArea : CapturedMir := fxLeaf "fx::<impl Area for Square>::area" 44 0 []

/-- Full and narrowed tables for the `dyn` canary. -/
def dynFullTbl : OpaqueCalleeTable :=
  .ofList [fxFillerA, fxGDead, fxCircleArea, fxSquareArea, fxFillerB]

/-- Narrowed `dyn` table. -/
def dynNarrowTbl : OpaqueCalleeTable := .ofList [fxCircleArea]

/-- Schema 12 fails closed on the `dyn` call. -/
theorem dyn_schema12_unsupported :
    resolveDynTarget dynEnv12 dynSite ⟨7, 0⟩ = .unsupported .missingVTableEvidence := by decide

/-- Schema 13 dispatches the `Circle` receiver to `<Circle as Area>::area`. -/
theorem dyn_schema13_resolves :
    resolveDynTarget dynEnv13 dynSite ⟨7, 0⟩ = .ok ("fx::<impl Area for Circle>::area", []) := by
  decide

theorem dyn_envExtends_12_13 : EnvExtends dynEnv12 dynEnv13 :=
  ⟨by decide, rfl, OptionExtends.refl _, rfl, OptionExtends.refl _, OptionExtends.refl _,
    (fun _ h => nomatch h)⟩

theorem dyn_envExtends_13_sync : EnvExtends dynEnv13 dynEnv13Sync :=
  ⟨by decide, rfl, OptionExtends.refl _, rfl, OptionExtends.refl _, (fun _ h => nomatch h),
    OptionExtends.refl _⟩

/-- The Schema-13 dynamic-dispatch step enters `<Circle as Area>::area`. -/
theorem dyn_step_enters_impl :
    (viewStepNode (dynDispatchStep dynEnv13 dynFullTbl dynSite dynRoot dynAtCall)).activeCalleePath? =
      some "fx::<impl Area for Circle>::area" := by
  decide +kernel

/-- The Schema-12 dynamic-dispatch step is the fail-closed `unsupported` node. -/
theorem dyn_step_schema12_fails_closed :
    dynDispatchStep dynEnv12 dynFullTbl dynSite dynRoot dynAtCall = MirStepNode.unsupported := by
  simp only [dynDispatchStep, dynSite_wellFormed, ite_true, dyn_vtablePtr_atCall,
    dyn_schema12_unsupported]

/-- A `dyn` call whose receiver local holds no pointer is UB (fail-closed: no
vtable lookup, no call). -/
theorem dyn_step_missing_receiver_ub :
    dynDispatchStep dynEnv13 dynFullTbl { dynSite with vtableLocal := 0 } dynRoot dynAtCall =
      MirStepNode.fail .ub :=
  rfl

/-- The live `dyn` call is the only demanded key at the call state. -/
theorem dyn_demandedKey :
    demandedKey? dynRoot dynAtCall =
      some ⟨fxLayouts, "fx::Area::area", [.dynamic "fx::Area"], []⟩ := by
  decide +kernel

/-- **End-to-end canary**: the Schema-13 dynamic-dispatch step is preserved when the
environment is further extended (sync regions) *and* the callee table is narrowed
to the dispatched method (dropping the dead-arm `g_dead`, `Square`, and fillers). -/
theorem dyn_step_preserved :
    dynDispatchStep dynEnv13Sync dynNarrowTbl dynSite dynRoot dynAtCall =
      dynDispatchStep dynEnv13 dynFullTbl dynSite dynRoot dynAtCall := by
  apply dynDispatchStep_preserved dyn_envExtends_13_sync
  · intro _ vt hvt
    rw [dyn_vtablePtr_atCall] at hvt
    cases hvt
    rw [dyn_schema13_resolves]
    exact fun _ h => nomatch h
  · intro _ vt target hvt ht _ k hk
    rw [dyn_vtablePtr_atCall] at hvt
    cases hvt
    rw [dyn_schema13_resolves] at ht
    cases ht
    rw [dyn_demandedKey] at hk
    cases hk
    have hrawN : dynNarrowTbl.lookupRaw "fx::<impl Area for Circle>::area" = some fxCircleArea :=
      lookupRaw_ofList_cons_hit rfl
    rw [redirectResolver_apply_hit dynNarrowTbl dynSite.dynKey
        ("fx::<impl Area for Circle>::area", []) rfl,
      redirectResolver_apply_hit dynFullTbl dynSite.dynKey
        ("fx::<impl Area for Circle>::area", []) rfl,
      lookupKey_hit_mono (c := fxCircleArea) hrawN rfl rfl,
      lookupKey_hit_mono (c := fxCircleArea) ?_ rfl rfl]
    unfold dynFullTbl
    rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl

/-- Monotonicity canary: Schema-13-only answers appear after the upgrade, while
supported Schema-12 answers are unchanged; vtable errors are exact. -/
theorem query_mono_canary :
    evalCompilerQuery dynEnv12 (.vtableMethodLookup 7 dynTraitRef 0 none) =
      .unsupported .missingVTableEvidence ∧
    evalCompilerQuery dynEnv13 (.vtableMethodLookup 7 dynTraitRef 0 none) =
      .ok (.method "fx::<impl Area for Circle>::area" []) ∧
    evalCompilerQuery dynEnv13
        (.abiCompatible fxRetU32Abi "fx::<impl Area for Circle>::area" none) =
      evalCompilerQuery dynEnv12
        (.abiCompatible fxRetU32Abi "fx::<impl Area for Circle>::area" none) ∧
    evalCompilerQuery dynEnv13 (.vtableMethodLookup 7 dynTraitRef 1 none) =
      .err (.vtableSlotOutOfBounds 1) ∧
    evalCompilerQuery dynEnv13 (.vtableMethodLookup 7 ⟨"fx::Other", []⟩ 0 none) =
      .err .vtableTraitMismatch ∧
    evalCompilerQuery dynEnv13 (.vtableMethodLookup 8 dynTraitRef 0 none) = .err (.vtableNotFound 8) := by
  decide

/-- Sync-storage guard canaries over region `[4, 12)` of allocation `3` (plus a
zero-byte region `[6, 6)` at offset `6`, which never blocks a spanning access). -/
theorem syncStorageGuard_canary :
    evalCompilerQuery dynEnv13Sync (.syncStorageGuard 3 6 1) =
      .err (.syncStorageOverlap ⟨3, 4, 8⟩) ∧
    evalCompilerQuery dynEnv13Sync (.syncStorageGuard 3 2 4) =
      .err (.syncStorageOverlap ⟨3, 4, 8⟩) ∧
    evalCompilerQuery dynEnv13Sync (.syncStorageGuard 3 0 4) = .ok .syncPermit ∧
    evalCompilerQuery dynEnv13Sync (.syncStorageGuard 3 12 4) = .ok .syncPermit ∧
    evalCompilerQuery dynEnv13Sync (.syncStorageGuard 4 6 1) = .ok .syncPermit ∧
    evalCompilerQuery { dynEnv13 with syncRegions := some [⟨3, 6, 0⟩] }
        (.syncStorageGuard 3 0 12) = .ok .syncPermit ∧
    evalCompilerQuery dynEnv13 (.syncStorageGuard 3 6 1) = .unsupported .missingSyncStorage := by
  decide

/-- Schema-gated `EnvExtends` canary: a Schema-12 environment whose raw `vtables`
field holds ignored garbage still extends cleanly to `dynEnv13` (`EnvExtends`),
and `query_mono_schema` preserves its supported answers. -/
theorem envExtends_schema12_ignored_fields_canary :
    let noisy12 : CompilerQueryEnv :=
      { dynEnv12 with vtables := some [⟨999, ⟨"fx::Noise", []⟩, [], [], []⟩] }
    EnvExtends noisy12 dynEnv13 ∧
      evalCompilerQuery noisy12 (.vtableMethodLookup 7 dynTraitRef 0 none) =
        .unsupported .missingVTableEvidence ∧
      evalCompilerQuery dynEnv13
          (.abiCompatible fxRetU32Abi "fx::<impl Area for Circle>::area" none) =
        evalCompilerQuery noisy12
          (.abiCompatible fxRetU32Abi "fx::<impl Area for Circle>::area" none) := by
  refine ⟨⟨by decide, rfl, OptionExtends.refl _, rfl, OptionExtends.refl _, OptionExtends.refl _,
    (fun _ h => nomatch h)⟩, by decide, by decide⟩

/-- A CFI-instrumented `dyn` call whose call-site type id mismatches is the
defined CFI trap (`abort`), not UB and not a call. -/
theorem dyn_cfi_trap :
    dynDispatchStep { dynEnv13 with cfiTags := some ⟨[("fx::<impl Area for Circle>::area", 1)],
        [(.fnPtr [] (.uint .u32) .safe .rust, 2)]⟩ } dynFullTbl
      { dynSite with cfiCallSite := some (.fnPtr [] (.uint .u32) .safe .rust) } dynRoot dynAtCall =
      MirStepNode.retOutcome .abort := by
  rfl


/-- **Full multi-step end-to-end dynamic-dispatch canary (Schema 13)**: starting
from `dynInit` (`bb0: if true { <dyn Area>::area() } else { g_dead() }`),
`evalDynWithOpaqueCallees` prunes the dead branch `g_dead`, reads the receiver's
vtable pointer, resolves `UnOp.vtableMethodLookup` + `abiCompatible` on demand at
`bb1`, enters `<Circle as Area>::area` in the narrowed opaque table, and halts
returning `31`; the narrowed/extended run equals the full run by the narrow-run
multi-step theorem (`runVisited` steps only `dynNarrowTbl`). -/
theorem canary_dyn_e2e_full_run_schema13 :
    (evalDynWithOpaqueCallees dynEnv13 dynNarrowTbl dynSite dynRoot 12 dynInit).summary =
      ⟨.halted, [.event 1], some 31, none⟩ ∧
    evalDynWithOpaqueCallees dynEnv13Sync dynNarrowTbl dynSite dynRoot 12 dynInit =
      evalDynWithOpaqueCallees dynEnv13 dynFullTbl dynSite dynRoot 12 dynInit :=
  ⟨by decide +kernel,
    evalDynWithOpaqueCallees_preserved_of_narrow_check dyn_envExtends_13_sync 12 dynInit
      (by decide +kernel)⟩

/-- `if false { <dyn Area>::area() } else { live_f() }`: the `dyn Area` call is on
the dead literal-`false` branch, while the live branch calls `live_f`. -/
def dynDeadBranchRoot : CapturedMir :=
  { defPath := "fx::dyn_dead_root", phase := .runtimePostCleanup, role := .subject, argCount := 0,
    localDecls := [⟨.mut, fxU32Ty, some "_0"⟩],
    basicBlocks := [
      ⟨[], ⟨.switchInt (fxBoolConst false) ⟨[(0, 2)], 1⟩, "root:if"⟩, false⟩,
      fxCallBlock "fx::Area::area" [.dynamic "fx::Area"] 3,
      fxCallBlock "fx::live_f" [] 3,
      ⟨[], ⟨.return_, "root:ret"⟩, false⟩ ],
    fnAbi := fxRetU32Abi, layouts := fxLayouts, allocations := [] }

/-- Initial state of `dynDeadBranchRoot`. -/
def dynDeadBranchInit : MachineState := initMachineState dynDeadBranchRoot []

/-- **Synergy canary (Dead-Branch Pruning + Demand-Time Schema-12 Queries)**:
when `<dyn Area>::area()` lies in the dead arm of `if false`, `evalDynWithOpaqueCallees`
under Schema 12 (`dynEnv12`, which lacks Schema-13 vtable evidence!) never
demands `vtableMethodLookup` and executes the live branch `live_f()` to `.halted 7`
on the narrowed `[fxLiveF]` table; preservation across `dynEnv12 → dynEnv13` and
`canaryNarrowTbl ↔ canaryFullTbl` is proved through
`evalDynWithOpaqueCallees_preserved_of_narrow_check`. -/
theorem canary_dyn_deadBranch_schema12_succeeds :
    (evalDynWithOpaqueCallees dynEnv12 canaryNarrowTbl dynSite
        dynDeadBranchRoot 12 dynDeadBranchInit).summary =
      ⟨.halted, [.event 0], some 7, none⟩ ∧
    evalDynWithOpaqueCallees dynEnv12 canaryNarrowTbl dynSite
        dynDeadBranchRoot 12 dynDeadBranchInit =
      evalDynWithOpaqueCallees dynEnv13 canaryFullTbl dynSite
        dynDeadBranchRoot 12 dynDeadBranchInit := by
  refine ⟨by decide +kernel, ?_⟩
  have h1 :
      evalDynWithOpaqueCallees dynEnv13 canaryNarrowTbl dynSite
          dynDeadBranchRoot 12 dynDeadBranchInit =
        evalDynWithOpaqueCallees dynEnv12 canaryNarrowTbl dynSite
          dynDeadBranchRoot 12 dynDeadBranchInit :=
    evalDynWithOpaqueCallees_preserved_of_narrow_check
      dyn_envExtends_12_13 12 dynDeadBranchInit (by decide +kernel)
  have h2 :
      evalDynWithOpaqueCallees dynEnv13 canaryNarrowTbl dynSite
          dynDeadBranchRoot 12 dynDeadBranchInit =
        evalDynWithOpaqueCallees dynEnv13 canaryFullTbl dynSite
          dynDeadBranchRoot 12 dynDeadBranchInit :=
    evalDynWithOpaqueCallees_preserved_of_narrow_check
      (EnvExtends.refl dynEnv13) 12 dynDeadBranchInit (by decide +kernel)
  exact h1.symm.trans h2

/-! ### Receiver-driven dispatch: one call key, two receivers -/

/-- `fn(vt_circle, vt_square: *const ()) -> u32`: the *same* `dyn Area` call key is
reached twice with different receivers in one run
(`bb0: StorageLive(vt); vt = copy vt_circle; _0 = <dyn Area>::area() -> bb1`,
`bb1: vt = copy vt_square; _0 = <dyn Area>::area() -> bb2`, `bb2: return`). -/
def dyn2Root : CapturedMir :=
  { defPath := "fx::dyn_two_receivers", phase := .runtimePostCleanup, role := .subject,
    argCount := 2,
    localDecls := [⟨.mut, fxU32Ty, some "_0"⟩, ⟨.not, fxVtPtrTy, some "vt_circle"⟩,
      ⟨.not, fxVtPtrTy, some "vt_square"⟩, ⟨.mut, fxVtPtrTy, some "vt"⟩],
    basicBlocks := [
      ⟨[⟨.storageLive 3, "dyn2:live"⟩, ⟨.assign ⟨3, []⟩ (.use (.copy ⟨1, []⟩)), "dyn2:vt0"⟩],
        ⟨.call (fxFnItem "fx::Area::area" [.dynamic "fx::Area"]) [] fxRetPlace
          (some 1) .continue_, "dyn2:call0"⟩, false⟩,
      ⟨[⟨.assign ⟨3, []⟩ (.use (.copy ⟨2, []⟩)), "dyn2:vt1"⟩],
        ⟨.call (fxFnItem "fx::Area::area" [.dynamic "fx::Area"]) [] fxRetPlace
          (some 2) .continue_, "dyn2:call1"⟩, false⟩,
      ⟨[], ⟨.return_, "dyn2:ret"⟩, false⟩ ],
    fnAbi := fxRetU32Abi, layouts := fxLayouts, allocations := [] }

/-- `dyn2Root` called with a `Circle` receiver (vtable `7`) and a `Square` receiver
(vtable `9`). -/
def dyn2Init : MachineState := initMachineState dyn2Root [.ptr ⟨7, 0⟩ 0, .ptr ⟨9, 0⟩ 0]

/-- The two-receiver call site reads the receiver vtable pointer from local `vt` (`_3`). -/
def dyn2Site : DynCallSite := { dynSite with vtableLocal := 3 }

/-- Narrowed table holding exactly the two dispatched `impl` bodies. -/
def dyn2NarrowTbl : OpaqueCalleeTable := .ofList [fxCircleArea, fxSquareArea]

/-- **Receiver-driven dispatch canary**: in one Schema-13 run the same `dyn Area`
call key is reached with a `Circle` receiver and then a `Square` receiver; the
vtable pointer read from the frame at each call dispatches to the right `impl`, so
the run returns `44` (`Square`'s area, from the last call). Reading a fixed
receiver (`vtableLocal := 1`, as a receiver-independent site would) wrongly sends
both calls to `Circle` (`31`), and Schema 12 fails closed at the first `dyn` call. -/
theorem canary_dyn_two_receivers :
    (evalDynWithOpaqueCallees dynEnv13 dynFullTbl dyn2Site dyn2Root 16 dyn2Init).summary =
      ⟨.halted, [], some 44, none⟩ ∧
    (evalDynWithOpaqueCallees dynEnv13 dynFullTbl { dyn2Site with vtableLocal := 1 } dyn2Root 16
        dyn2Init).summary = ⟨.halted, [], some 31, none⟩ ∧
    evalDynWithOpaqueCallees dynEnv12 dynFullTbl dyn2Site dyn2Root 16 dyn2Init =
      .faulted .unsupported [] := by
  decide +kernel

/-- **Multi-step preservation on the two-receiver run**: the whole run under the
further-extended environment and the two-`impl` narrowed table equals the full
run, by `evalDynWithOpaqueCallees_preserved_of_narrow_check` (`runVisited` steps
only `dyn2NarrowTbl`). -/
theorem canary_dyn_two_receivers_preserved :
    evalDynWithOpaqueCallees dynEnv13Sync dyn2NarrowTbl dyn2Site dyn2Root 16 dyn2Init =
      evalDynWithOpaqueCallees dynEnv13 dynFullTbl dyn2Site dyn2Root 16 dyn2Init :=
  evalDynWithOpaqueCallees_preserved_of_narrow_check dyn_envExtends_13_sync 16 dyn2Init
    (by decide +kernel)

/-! ### Chained supertrait vtable lookup (`charon#1611`) -/

/-- Subtrait `SubArea : Area` with `Self = dyn SubArea`. -/
def dynSubTraitRef : TraitRef := ⟨"fx::SubArea", [.dynamic "fx::SubArea"]⟩

/-- Schema-13 environment where vtable `11` (`dyn SubArea` for `Circle`) links its
supertrait `Area` to vtable `7` (`dyn Area` for `Circle`). -/
def dynSubEnv13 : CompilerQueryEnv :=
  { dynEnv13 with
    vtables := some [
      ⟨7, dynTraitRef, [("fx::<impl Area for Circle>::area", [])], [], []⟩,
      ⟨9, dynTraitRef, [("fx::<impl Area for Square>::area", [])], [], []⟩,
      ⟨11, dynSubTraitRef, [], [(dynTraitRef, 7)], []⟩ ] }

/-- `fn(vt: *const ()) -> u32 { if true { <dyn SubArea as Area>::area() } else { g_dead() } }`:
the supertrait method `Area::area` called on a `dyn SubArea` receiver (call key
`(Area::area, [dyn SubArea])`, as rustc emits it). -/
def dynSubRoot : CapturedMir :=
  { fxLitIfRoot true "fx::Area::area" [.dynamic "fx::SubArea"] "fx::g_dead" with
    argCount := 1, localDecls := [⟨.mut, fxU32Ty, some "_0"⟩, ⟨.not, fxVtPtrTy, some "vt"⟩] }

/-- Call site of `dynSubRoot`'s virtual call: the receiver's `dyn SubArea` vtable is
read first, chaining `SubArea → Area` before looking up `Area::area` at slot `0`. -/
def dynSubSite : DynCallSite :=
  { dynSite with
    lookupOp := ⟨dynTraitRef, 0, [dynSubTraitRef], none⟩
    dynKey := ("fx::Area::area", [.dynamic "fx::SubArea"]) }

/-- `dynSubSite` is well formed: the call's receiver type `dyn SubArea` names the
trait of the first vtable the chain reads. -/
theorem dynSubSite_wellFormed : dynSubSite.wellFormed = true := by decide

/-- Initial state of `dynSubRoot` called with a `dyn SubArea` receiver (vtable `11`). -/
def dynSubInit : MachineState := initMachineState dynSubRoot [.ptr ⟨11, 0⟩ 0]

/-- **Chained supertrait vtable canary (`charon#1611`)**:
1. `UnOpExt.query?` on `dynSubSite` issues `.vtableSupertraitLookup 11 dynSubTraitRef dynTraitRef`
   as its initial query (the first hop of `resolveVTableChain`), resolving to
   `.ok (.supertraitVTable 7)`.
2. `resolveDynTarget` chains `11 (SubArea) → 7 (Area) → <Circle as Area>::area`.
3. Schema 12 (`dynEnv12`) fails closed with `.unsupported .missingVTableEvidence`.
4. A hop from a vtable without the requested supertrait link (vtable `7` of `Area`
   has `supertraits = []`) is `.err (.vtableSupertraitNotFound 7 dynSubTraitRef)`.
5. `evalDynWithOpaqueCallees` on `dynSubInit` halts returning `31` on the narrowed
   table `dynNarrowTbl`, and equals the full-table run by
   `evalDynWithOpaqueCallees_preserved_of_narrow_check`. -/
theorem canary_dyn_supertrait_chain :
    (UnOpExt.vtableMethodLookup dynSubSite.lookupOp).query? ⟨11, 0⟩ =
      some (.vtableSupertraitLookup 11 dynSubTraitRef dynTraitRef) ∧
    evalCompilerQuery dynSubEnv13 (.vtableSupertraitLookup 11 dynSubTraitRef dynTraitRef) =
      .ok (.supertraitVTable 7) ∧
    resolveDynTarget dynSubEnv13 dynSubSite ⟨11, 0⟩ =
      .ok ("fx::<impl Area for Circle>::area", []) ∧
    resolveDynTarget dynEnv12 dynSubSite ⟨11, 0⟩ =
      .unsupported .missingVTableEvidence ∧
    evalCompilerQuery dynSubEnv13 (.vtableSupertraitLookup 7 dynTraitRef dynSubTraitRef) =
      .err (.vtableSupertraitNotFound 7 dynSubTraitRef) ∧
    (evalDynWithOpaqueCallees dynSubEnv13 dynNarrowTbl dynSubSite dynSubRoot 12 dynSubInit).summary =
      ⟨.halted, [.event 1], some 31, none⟩ ∧
    evalDynWithOpaqueCallees { dynSubEnv13 with syncRegions := some [⟨3, 4, 8⟩] }
        dynNarrowTbl dynSubSite dynSubRoot 12 dynSubInit =
      evalDynWithOpaqueCallees dynSubEnv13 dynFullTbl dynSubSite dynSubRoot 12 dynSubInit := by
  have hExt : EnvExtends dynSubEnv13 { dynSubEnv13 with syncRegions := some [⟨3, 4, 8⟩] } :=
    ⟨by decide, rfl, OptionExtends.refl _, rfl, OptionExtends.refl _, (fun _ h => nomatch h),
      OptionExtends.refl _⟩
  refine ⟨rfl, by decide, by decide, by decide, by decide, by decide +kernel,
    evalDynWithOpaqueCallees_preserved_of_narrow_check hExt 12 dynSubInit (by decide +kernel)⟩

/-- A mismatched site: a `<dyn Area as Area>::area` call key paired with a lookup that starts
at the receiver's `dyn SubArea` vtable. -/
def dynMismatchSite : DynCallSite := { dynSite with lookupOp := ⟨dynTraitRef, 0, [dynSubTraitRef], none⟩ }

/-- **Ill-formed site canary**: the vtable chain alone would happily resolve
`dynMismatchSite` (a `dyn Area` call dispatched through a `dyn SubArea` vtable
chain), but the site's call key does not name the trait of the receiver's vtable,
so it is ill formed and the run fails closed at the virtual call. -/
theorem canary_dyn_site_mismatch_fails_closed :
    dynMismatchSite.wellFormed = false ∧
    resolveDynTarget dynSubEnv13 dynMismatchSite ⟨11, 0⟩ =
      .ok ("fx::<impl Area for Circle>::area", []) ∧
    (evalDynWithOpaqueCallees dynSubEnv13 dynFullTbl dynMismatchSite dynRoot 12
        (initMachineState dynRoot [.ptr ⟨11, 0⟩ 0])).summary =
      ⟨.faulted, [.event 1], none, none⟩ := by
  decide +kernel

/-- A site for an unrelated virtual call (`<dyn Shape as Shape>::perimeter`). -/
def dynOtherSite : DynCallSite :=
  { dynSite with
    lookupOp := ⟨⟨"fx::Shape", [.dynamic "fx::Shape"]⟩, 0, [], none⟩
    dynKey := ("fx::Shape::perimeter", [.dynamic "fx::Shape"]) }

/-- **Unregistered virtual calls fail closed**: without vtable dispatch, the trusted
static resolver turns `<dyn Area as Area>::area` into an unlinked external call to
the trait method's `DefPath` (`dyn Area` has no layout, so no body instantiates).
`evalDynWithOpaqueCallees` with a site for a *different* virtual call refuses it
(`.unsupported`) instead. -/
theorem canary_unregistered_dyn_fails_closed :
    (evalWithOpaqueCallees dynFullTbl dynRoot 12 dynInit).summary =
      ⟨.external, [.event 1], none, some "fx::Area::area"⟩ ∧
    (evalDynWithOpaqueCallees dynEnv13 dynFullTbl dynOtherSite dynRoot 12 dynInit).summary =
      ⟨.faulted, [.event 1], none, none⟩ := by
  decide +kernel

/-- Root calling `<dyn Area as Area<u32>>::area` (`typeArgs = [dyn Area, u32]`). -/
def dynArgMismatchRoot : CapturedMir :=
  { fxLitIfRoot true "fx::Area::area" [.dynamic "fx::Area", .uint .u32] "fx::g_dead" with
    argCount := 1, localDecls := [⟨.mut, fxU32Ty, some "_0"⟩, ⟨.not, fxVtPtrTy, some "vt"⟩] }

/-- Site whose `dynKey` has generic trait arguments `[dyn Area, u32]` while its
vtable lookup targets `⟨"fx::Area", [dyn Area]⟩`: `firstTrait.defPath` matches
`"fx::Area"` (so a `.defPath`-only well-formedness check would accept it),
but `dynKey.2 ≠ firstTrait.args`. -/
def dynArgMismatchSite : DynCallSite :=
  { dynSite with dynKey := ("fx::Area::area", [.dynamic "fx::Area", .uint .u32]) }

/-- **Generic trait-argument mismatch canary**: `dynArgMismatchSite` has matching
trait `DefPath` `"fx::Area"` and resolves at the raw vtable level, but its generic
argument list `[dyn Area, u32]` does not match the vtable's `[dyn Area]`, so the
generic-argument check of `DynCallSite.wellFormed` rejects it (`false`) and execution fails closed
(`.faulted` via `MirStepNode.unsupported`). -/
theorem canary_dyn_trait_arg_mismatch_fails_closed :
    decide ((dynSelfTrait? dynArgMismatchSite.dynKey) =
      some (dynArgMismatchSite.lookupOp.supertraitChain.headD
        dynArgMismatchSite.lookupOp.traitRef).defPath) = true ∧
    dynArgMismatchSite.wellFormed = false ∧
    resolveDynTarget dynEnv13 dynArgMismatchSite ⟨7, 0⟩ =
      .ok ("fx::<impl Area for Circle>::area", []) ∧
    (evalDynWithOpaqueCallees dynEnv13 dynFullTbl dynArgMismatchSite dynArgMismatchRoot 12
        (initMachineState dynArgMismatchRoot [.ptr ⟨7, 0⟩ 0])).summary =
      ⟨.faulted, [.event 1], none, none⟩ := by
  decide +kernel


/-- `<impl SubArea for Circle>::bonus() -> u32 { 10 }`. -/
def fxCircleBonus : CapturedMir :=
  fxLeaf "fx::<impl SubArea for Circle>::bonus" 10 0
    [⟨⟨"fx::SubArea::bonus", [fxCircleTy]⟩, "fx::<impl SubArea for Circle>::bonus"⟩]

/-- Schema-13 environment where vtable `11` (`dyn SubArea` for `Circle`) has its own
method `<impl SubArea for Circle>::bonus` at slot `0` *and* links supertrait `Area`
to vtable `7` (`dyn Area` for `Circle`). -/
def dynMultiSiteEnv13 : CompilerQueryEnv :=
  { dynSubEnv13 with
    fnAbis := [
      ("fx::<impl Area for Circle>::area", fxRetU32Abi),
      ("fx::<impl Area for Square>::area", fxRetU32Abi),
      ("fx::<impl SubArea for Circle>::bonus", fxRetU32Abi) ],
    vtables := some [
      ⟨7, dynTraitRef, [("fx::<impl Area for Circle>::area", [])], [], []⟩,
      ⟨9, dynTraitRef, [("fx::<impl Area for Square>::area", [])], [], []⟩,
      ⟨11, dynSubTraitRef, [("fx::<impl SubArea for Circle>::bonus", [])],
        [(dynTraitRef, 7)], []⟩ ] }

/-- Call site for the subtrait's own virtual method `<dyn SubArea as SubArea>::bonus`
(direct vtable `11` slot `0`, no supertrait hop). -/
def dynSubBonusSite : DynCallSite :=
  { vtableLocal := 1
    lookupOp := ⟨dynSubTraitRef, 0, [], none⟩
    callerAbi := fxRetU32Abi
    cfiCallSite := none
    dynKey := ("fx::SubArea::bonus", [.dynamic "fx::SubArea"]) }

/-- Two-site registry covering both `<dyn SubArea as SubArea>::bonus` (direct) and
`<dyn SubArea as Area>::area` (supertrait hop `SubArea → Area`). -/
def dynTwoSiteRegistry : DynCallRegistry := [dynSubBonusSite, dynSubSite]

/-- Program making *two distinct virtual calls* in one execution:
`bb0` calls `<dyn SubArea as SubArea>::bonus` (jumping to `bb1`) and `bb1` calls
`<dyn SubArea as Area>::area` (jumping to `bb2: return`). -/
def dynMultiSiteRoot : CapturedMir :=
  { defPath := "fx::dyn_multi_site_root", phase := .runtimePostCleanup, role := .subject,
    argCount := 1,
    localDecls := [⟨.mut, fxU32Ty, some "_0"⟩, ⟨.not, fxVtPtrTy, some "vt"⟩],
    basicBlocks := [
      fxCallBlock "fx::SubArea::bonus" [.dynamic "fx::SubArea"] 1,
      fxCallBlock "fx::Area::area" [.dynamic "fx::SubArea"] 2,
      ⟨[], ⟨.return_, "multi:ret"⟩, false⟩ ],
    fnAbi := fxRetU32Abi, layouts := fxLayouts, allocations := [] }

/-- Initial state of `dynMultiSiteRoot` with a `dyn SubArea` receiver (vtable `11`). -/
def dynMultiSiteInit : MachineState := initMachineState dynMultiSiteRoot [.ptr ⟨11, 0⟩ 0]

/-- Narrowed callee table for `dynMultiSiteRoot` (holding `fxCircleBonus` and `fxCircleArea`). -/
def dynMultiSiteNarrowTbl : OpaqueCalleeTable := .ofList [fxCircleBonus, fxCircleArea]

/-- Full callee table for `dynMultiSiteRoot` (adding unused callees `fxLiveF`, `fxGDead`, `fxSquareArea`). -/
def dynMultiSiteFullTbl : OpaqueCalleeTable :=
  .ofList [fxLiveF, fxGDead, fxCircleBonus, fxCircleArea, fxSquareArea]

/-- **Multi-site dynamic-dispatch registry canary**:
1. `dynTwoSiteRegistry` is well formed (`true`).
2. `evalDynRegistryWithOpaqueCallees` executes *both* virtual call keys
   (`<dyn SubArea as SubArea>::bonus` via direct vtable `11` and
   `<dyn SubArea as Area>::area` via supertrait chain `11 → 7`) and halts returning `31`.
3. Single-site `evalDynWithOpaqueCallees` with only `dynSubBonusSite` or only
   `dynSubSite` fails closed (`.faulted`) at whichever virtual call key is unregistered.
4. The multi-site run is preserved under `EnvExtends` and call-cone narrowing
   (`dynMultiSiteNarrowTbl` vs. `dynMultiSiteFullTbl`) via
   `evalDynRegistryWithOpaqueCallees_preserved_of_narrow_check`. -/
theorem canary_dyn_multi_site_registry :
    dynTwoSiteRegistry.wellFormed = true ∧
    (evalDynRegistryWithOpaqueCallees dynMultiSiteEnv13 dynMultiSiteNarrowTbl
        dynTwoSiteRegistry dynMultiSiteRoot 16 dynMultiSiteInit).summary =
      ⟨.halted, [], some 31, none⟩ ∧
    (evalDynWithOpaqueCallees dynMultiSiteEnv13 dynMultiSiteFullTbl
        dynSubBonusSite dynMultiSiteRoot 16 dynMultiSiteInit).summary =
      ⟨.faulted, [], none, none⟩ ∧
    (evalDynWithOpaqueCallees dynMultiSiteEnv13 dynMultiSiteFullTbl
        dynSubSite dynMultiSiteRoot 16 dynMultiSiteInit).summary =
      ⟨.faulted, [], none, none⟩ ∧
    evalDynRegistryWithOpaqueCallees
        { dynMultiSiteEnv13 with syncRegions := some [⟨3, 4, 8⟩] }
        dynMultiSiteNarrowTbl dynTwoSiteRegistry dynMultiSiteRoot 16 dynMultiSiteInit =
      evalDynRegistryWithOpaqueCallees
        dynMultiSiteEnv13 dynMultiSiteFullTbl dynTwoSiteRegistry dynMultiSiteRoot 16
        dynMultiSiteInit := by
  have hExt : EnvExtends dynMultiSiteEnv13
      { dynMultiSiteEnv13 with syncRegions := some [⟨3, 4, 8⟩] } :=
    ⟨by decide, rfl, OptionExtends.refl _, rfl, OptionExtends.refl _, (fun _ h => nomatch h),
      OptionExtends.refl _⟩
  refine ⟨by decide, by decide +kernel, by decide +kernel, by decide +kernel,
    evalDynRegistryWithOpaqueCallees_preserved_of_narrow_check hExt 16 dynMultiSiteInit
      (by decide +kernel)⟩

/-- Root calling `<dyn Area as Area>::perimeter`. -/
def dynPerimeterRoot : CapturedMir :=
  { fxLitIfRoot true "fx::Area::perimeter" [.dynamic "fx::Area"] "fx::g_dead" with
    argCount := 1, localDecls := [⟨.mut, fxU32Ty, some "_0"⟩, ⟨.not, fxVtPtrTy, some "vt"⟩] }

/-- A well-formed site for `<dyn Area as Area>::perimeter` whose lookup reads slot `0`
of the `Area` vtable, which holds `area`'s implementation. -/
def dynSlotMismatchSite : DynCallSite :=
  { dynSite with dynKey := ("fx::Area::perimeter", [.dynamic "fx::Area"]) }

/-- **Slot/method mismatch canary**: `dynSlotMismatchSite` passes
`DynCallSite.wellFormed` (right trait, right arguments) and its slot resolves, but
the slot holds `<impl Area for Circle>::area`, not a `perimeter` implementation.
An unguarded step would run it anyway — the redirected pruned step halts returning `31`,
`area`'s value, for a `perimeter` call — while the guarded step fails closed. -/
theorem canary_dyn_slot_method_mismatch_fails_closed :
    dynSlotMismatchSite.wellFormed = true ∧
    resolveDynTarget dynEnv13 dynSlotMismatchSite ⟨7, 0⟩ =
      .ok ("fx::<impl Area for Circle>::area", []) ∧
    implementsCalledMethod "fx::Area::perimeter" "fx::<impl Area for Circle>::area" = false ∧
    implementsCalledMethod "fx::Area::area" "fx::<impl Area for Circle>::area" = true ∧
    implementsCalledMethod "fx::SubArea::bonus" "fx::<impl SubArea for Circle>::bonus" = true ∧
    (runSteps (stepBranchPruned (redirectResolver dynFullTbl dynSlotMismatchSite.dynKey
        ("fx::<impl Area for Circle>::area", [])) dynPerimeterRoot) 12
        (initMachineState dynPerimeterRoot [.ptr ⟨7, 0⟩ 0]) []).summary =
      ⟨.halted, [.event 1], some 31, none⟩ ∧
    (evalDynWithOpaqueCallees dynEnv13 dynFullTbl dynSlotMismatchSite dynPerimeterRoot 12
        (initMachineState dynPerimeterRoot [.ptr ⟨7, 0⟩ 0])).summary =
      ⟨.faulted, [.event 1], none, none⟩ := by
  decide +kernel

/-- A second site registered for `dynSite`'s call key (pointing at slot `1`). -/
def dynDuplicateSite : DynCallSite := { dynSite with lookupOp := ⟨dynTraitRef, 1, [], none⟩ }

/-- **Registry ambiguity canary**: with two sites registered for the same call key,
a first-match lookup would silently dispatch through whichever came first; the
registry is ill formed (`wellFormed = false`, duplicate key), the key has no
site, and the virtual call fails closed. The unambiguous registry still runs. -/
theorem canary_dyn_registry_ambiguity_fails_closed :
    DynCallRegistry.wellFormed [dynSite, dynDuplicateSite] = false ∧
    DynCallRegistry.findSite? [dynSite, dynDuplicateSite] dynSite.dynKey = none ∧
    (evalDynRegistryWithOpaqueCallees dynEnv13 dynFullTbl [dynSite, dynDuplicateSite]
        dynRoot 12 dynInit).summary = ⟨.faulted, [.event 1], none, none⟩ ∧
    DynCallRegistry.wellFormed [dynSite] = true ∧
    (evalDynRegistryWithOpaqueCallees dynEnv13 dynFullTbl [dynSite] dynRoot 12 dynInit).summary =
      ⟨.halted, [.event 1], some 31, none⟩ := by
  decide +kernel

/-- Root calling `<dyn Area as OtherTrait>::area`: same method suffix `::area` as
`Area::area`, but on a *different* trait `fx::OtherTrait`. -/
def dynWrongTraitPrefixRoot : CapturedMir :=
  { fxLitIfRoot true "fx::OtherTrait::area" [.dynamic "fx::Area"] "fx::g_dead" with
    argCount := 1, localDecls := [⟨.mut, fxU32Ty, some "_0"⟩, ⟨.not, fxVtPtrTy, some "vt"⟩] }

/-- Site for `<dyn Area as OtherTrait>::area` reading `Area`'s vtable slot `0`
(`"fx::<impl Area for Circle>::area"`). It passes `implementsCalledMethod`
(both paths end in `::area`!) and the receiver-trait checks `d = firstTrait.defPath` /
`dynKey.2 = .dynamic d :: traitRef.args.tail`, so without `methodMatchesTrait` it would
dispatch `OtherTrait::area` to `<impl Area for Circle>::area`! -/
def dynWrongTraitPrefixSite : DynCallSite :=
  { dynSite with dynKey := ("fx::OtherTrait::area", [.dynamic "fx::Area"]) }

/-- **Cross-trait method-suffix collision canary**: `dynWrongTraitPrefixSite` calls
`"fx::OtherTrait::area"` while reading `Area`'s vtable slot `0`. Both paths end
in `::area`, so `implementsCalledMethod` is `true` and `resolveDynTarget` succeeds,
but `methodMatchesTrait "fx::OtherTrait::area" "fx::Area"` is `false`, so
`DynCallSite.wellFormed` rejects the site (`false`) and execution fails closed. -/
theorem canary_dyn_wrong_trait_prefix_fails_closed :
    implementsCalledMethod dynWrongTraitPrefixSite.dynKey.1
      "fx::<impl Area for Circle>::area" = true ∧
    methodMatchesTrait dynWrongTraitPrefixSite.dynKey.1
      dynWrongTraitPrefixSite.lookupOp.traitRef.defPath = false ∧
    dynWrongTraitPrefixSite.wellFormed = false ∧
    resolveDynTarget dynEnv13 dynWrongTraitPrefixSite ⟨7, 0⟩ =
      .ok ("fx::<impl Area for Circle>::area", []) ∧
    (evalDynWithOpaqueCallees dynEnv13 dynFullTbl dynWrongTraitPrefixSite
        dynWrongTraitPrefixRoot 12
        (initMachineState dynWrongTraitPrefixRoot [.ptr ⟨7, 0⟩ 0])).summary =
      ⟨.faulted, [.event 1], none, none⟩ := by
  decide +kernel

/-- Generic supertrait `Conv<u32>` with `Self = dyn Conv` (`args = [dyn Conv, u32]`). -/
def dynConvU32TraitRef : TraitRef :=
  ⟨"fx::Conv", [.dynamic "fx::Conv", .uint .u32]⟩

/-- `<impl Conv<u32> for Circle>::conv() -> u32 { 55 }`. -/
def fxCircleConvU32 : CapturedMir :=
  fxLeaf "fx::<impl Conv<u32> for Circle>::conv" 55 0
    [⟨⟨"fx::Conv::conv", [fxCircleTy, .uint .u32]⟩,
      "fx::<impl Conv<u32> for Circle>::conv"⟩]

/-- Schema-13 environment where vtable `11` (`dyn SubArea` for `Circle`) links
generic supertrait `Conv<u32>` to vtable `13`. -/
def dynGenSuperEnv13 : CompilerQueryEnv :=
  { dynSubEnv13 with
    fnAbis := [
      ("fx::<impl Area for Circle>::area", fxRetU32Abi),
      ("fx::<impl Area for Square>::area", fxRetU32Abi),
      ("fx::<impl Conv<u32> for Circle>::conv", fxRetU32Abi) ],
    vtables := some [
      ⟨7, dynTraitRef, [("fx::<impl Area for Circle>::area", [])], [], []⟩,
      ⟨11, dynSubTraitRef, [], [(dynTraitRef, 7), (dynConvU32TraitRef, 13)], []⟩,
      ⟨13, dynConvU32TraitRef, [("fx::<impl Conv<u32> for Circle>::conv", [])], [], []⟩ ] }

/-- Root calling the generic supertrait method `<dyn SubArea as Conv<u32>>::conv`
(call key `("fx::Conv::conv", [dyn SubArea, u32])`). -/
def dynGenSuperRoot : CapturedMir :=
  { fxLitIfRoot true "fx::Conv::conv" [.dynamic "fx::SubArea", .uint .u32] "fx::g_dead" with
    argCount := 1, localDecls := [⟨.mut, fxU32Ty, some "_0"⟩, ⟨.not, fxVtPtrTy, some "vt"⟩] }

/-- Call site for `<dyn SubArea as Conv<u32>>::conv` chaining `SubArea → Conv<u32>`. -/
def dynGenSuperSite : DynCallSite :=
  { vtableLocal := 1
    lookupOp := ⟨dynConvU32TraitRef, 0, [dynSubTraitRef], none⟩
    callerAbi := fxRetU32Abi
    cfiCallSite := none
    dynKey := ("fx::Conv::conv", [.dynamic "fx::SubArea", .uint .u32]) }

/-- Mismatched generic supertrait site `<dyn SubArea as Conv<u64>>::conv` paired with
the `Conv<u32>` vtable chain. -/
def dynGenSuperBadSite : DynCallSite :=
  { dynGenSuperSite with
    dynKey := ("fx::Conv::conv", [.dynamic "fx::SubArea", .uint .u64]) }

/-- Narrowed and full tables for `dynGenSuperRoot`. -/
def dynGenSuperNarrowTbl : OpaqueCalleeTable := .ofList [fxCircleConvU32]
def dynGenSuperFullTbl : OpaqueCalleeTable :=
  .ofList [fxLiveF, fxGDead, fxCircleArea, fxCircleConvU32]

/-- **Generic supertrait vtable chain canary**:
1. `dynGenSuperSite` (`<dyn SubArea as Conv<u32>>::conv`, where `firstTrait = SubArea`
   has args `[dyn SubArea]` while the supertrait `Conv<u32>` has args `[dyn Conv, u32]`)
   would be rejected by the naive rule `dynKey.2 = firstTrait.args`, but is accepted
   (`wellFormed = true`) by `dynKey.2 = .dynamic d :: traitRef.args.tail`.
2. `evalDynWithOpaqueCallees` chains `11 (SubArea) → 13 (Conv<u32>) → <impl Conv<u32> for Circle>::conv`
   and halts returning `55` on `dynGenSuperNarrowTbl` (and equals the full-table run via
   `evalDynWithOpaqueCallees_preserved_of_narrow_check`).
3. Mismatched supertrait type arguments (`dynGenSuperBadSite`: `Conv<u64>` vs. `Conv<u32>`)
   have `wellFormed = false`. -/
theorem canary_dyn_generic_supertrait_chain :
    decide (dynGenSuperSite.dynKey.2 =
      (dynGenSuperSite.lookupOp.supertraitChain.headD
        dynGenSuperSite.lookupOp.traitRef).args) = false ∧
    dynGenSuperSite.wellFormed = true ∧
    dynGenSuperBadSite.wellFormed = false ∧
    (evalDynWithOpaqueCallees dynGenSuperEnv13 dynGenSuperNarrowTbl dynGenSuperSite
        dynGenSuperRoot 12 (initMachineState dynGenSuperRoot [.ptr ⟨11, 0⟩ 0])).summary =
      ⟨.halted, [.event 1], some 55, none⟩ ∧
    evalDynWithOpaqueCallees { dynGenSuperEnv13 with syncRegions := some [⟨3, 4, 8⟩] }
        dynGenSuperNarrowTbl dynGenSuperSite dynGenSuperRoot 12
        (initMachineState dynGenSuperRoot [.ptr ⟨11, 0⟩ 0]) =
      evalDynWithOpaqueCallees dynGenSuperEnv13 dynGenSuperFullTbl dynGenSuperSite
        dynGenSuperRoot 12 (initMachineState dynGenSuperRoot [.ptr ⟨11, 0⟩ 0]) := by
  have hExt : EnvExtends dynGenSuperEnv13
      { dynGenSuperEnv13 with syncRegions := some [⟨3, 4, 8⟩] } :=
    ⟨by decide, rfl, OptionExtends.refl _, rfl, OptionExtends.refl _, (fun _ h => nomatch h),
      OptionExtends.refl _⟩
  refine ⟨by decide, by decide, by decide, by decide +kernel,
    evalDynWithOpaqueCallees_preserved_of_narrow_check hExt 12
      (initMachineState dynGenSuperRoot [.ptr ⟨11, 0⟩ 0]) (by decide +kernel)⟩


/-! ### Explicit trait-method binding (`expectedTraitMethod?`) vs. the item-name fallback -/

/-- Compiler-generated vtable shim for `<Circle as Area>::area`: its impl path does *not* end in
the method name `area`. -/
def fxCircleAreaShim : CapturedMir :=
  fxLeaf "fx::<Circle as Area>::area::{{vtable.shim}}" 77 0 []

/-- Schema-13 environment whose vtable `7` (`dyn Area` for `Circle`) holds the shim in slot `0`,
with the explicit slot bindings `binding` (`VTableMethodEntry.slotTraitMethods`). -/
def shimEnv13 (binding : List DefPath) : CompilerQueryEnv :=
  { dynEnv13 with
    fnAbis := [("fx::<Circle as Area>::area::{{vtable.shim}}", fxRetU32Abi)]
    vtables := some
      [⟨7, dynTraitRef, [("fx::<Circle as Area>::area::{{vtable.shim}}", [])], [], binding⟩] }

/-- Callee table holding the shim body. -/
def shimTbl : OpaqueCalleeTable := .ofList [fxFillerA, fxCircleAreaShim]

/-- The `dyn Area` call site carrying `charon#1611`'s explicit trait-method `DefPath`. -/
def dynShimSite : DynCallSite :=
  { dynSite with lookupOp := ⟨dynTraitRef, 0, [], some "fx::Area::area"⟩ }

/-- **Shim dispatch through the explicit trait-method binding**:
1. the shim's path fails the byte-level item-name check (`implementsCalledMethod = false`);
2. with the binding (`expectedTraitMethod? = some "fx::Area::area"`, slot `0` bound to
   `fx::Area::area`), the site is well formed and the run dispatches to the shim, halting
   with `77`;
3. without it (`dynSite`), the fail-closed item-name fallback refuses the shim
   (`.faulted .unsupported`);
4. a slot bound to another trait method, or an unbound slot, is a
   `.vtableSlotMethodMismatch` and fails closed;
5. a binding naming another method than the call key is ill formed. -/
theorem canary_shim_dispatch_with_expected_trait_method :
    implementsCalledMethod "fx::Area::area"
      "fx::<Circle as Area>::area::{{vtable.shim}}" = false ∧
    dynShimSite.wellFormed = true ∧
    (evalDynWithOpaqueCallees (shimEnv13 ["fx::Area::area"]) shimTbl dynShimSite dynRoot 12
        dynInit).summary = ⟨.halted, [.event 1], some 77, none⟩ ∧
    evalDynWithOpaqueCallees (shimEnv13 ["fx::Area::area"]) shimTbl dynSite dynRoot 12
        dynInit = .faulted .unsupported [.event 1] ∧
    evalCompilerQuery (shimEnv13 ["fx::Area::perimeter"])
        (.vtableMethodLookup 7 dynTraitRef 0 (some "fx::Area::area")) =
      .err (.vtableSlotMethodMismatch 0) ∧
    evalDynWithOpaqueCallees (shimEnv13 ["fx::Area::perimeter"]) shimTbl dynShimSite dynRoot
        12 dynInit = .faulted .unsupported [.event 1] ∧
    evalDynWithOpaqueCallees (shimEnv13 []) shimTbl dynShimSite dynRoot 12 dynInit =
      .faulted .unsupported [.event 1] ∧
    ({ dynSite with lookupOp := ⟨dynTraitRef, 0, [], some "fx::Area::perimeter"⟩ } :
        DynCallSite).wellFormed = false := by
  decide +kernel

/-- The binding is checked at the *terminal* method read of a supertrait chain: a
`<dyn SubArea as Area>::area` call carrying `expectedTraitMethod? = some "fx::Area::area"`
dispatches through `11 (SubArea) → 7 (Area)` when slot `0` of vtable `7` is bound to
`fx::Area::area` (halting with `31`), and fails closed when vtable `7` carries no binding. -/
theorem canary_expected_trait_method_supertrait_chain :
    (evalDynWithOpaqueCallees
        { dynSubEnv13 with
          vtables := some [
            ⟨7, dynTraitRef, [("fx::<impl Area for Circle>::area", [])], [],
              ["fx::Area::area"]⟩,
            ⟨11, dynSubTraitRef, [], [(dynTraitRef, 7)], []⟩ ] }
        dynNarrowTbl { dynSubSite with lookupOp := ⟨dynTraitRef, 0, [dynSubTraitRef],
          some "fx::Area::area"⟩ } dynSubRoot 12 dynSubInit).summary =
      ⟨.halted, [.event 1], some 31, none⟩ ∧
    evalDynWithOpaqueCallees dynSubEnv13 dynNarrowTbl
        { dynSubSite with lookupOp := ⟨dynTraitRef, 0, [dynSubTraitRef],
          some "fx::Area::area"⟩ } dynSubRoot 12 dynSubInit =
      .faulted .unsupported [.event 1] := by
  decide +kernel

/-- `slotMethodAgrees` is the item-name check without a binding, and accepts every non-empty
target with a binding that names the called method. -/
theorem canary_slotMethodAgrees :
    slotMethodAgrees dynSite "fx::<Circle as Area>::area::{{vtable.shim}}" = false ∧
      slotMethodAgrees dynShimSite "fx::<Circle as Area>::area::{{vtable.shim}}" = true :=
  ⟨by rw [slotMethodAgrees_of_none _ rfl]; decide,
    slotMethodAgrees_of_some _ rfl rfl (by decide)⟩

/-- **Symmetric `CoherentEnvExtends` layout invariance (`evalLayoutOf_any_dialect_of_coherentExtends`)**:
upgrading a Schema-12 environment via `withBridgedV08Layouts` produces a `CoherentEnvExtends` pair
(`coherent₁` holds as well), and `evalLayoutOf` agrees across *any* pair of layout dialects
(when supported in `env₁` or `d₁ = .v2026_06_01`). -/
theorem canary_coherentExtends_any_dialect :
    let env₁ := autoCfiEnv₁
    let env₂ := env₁.withBridgedV08Layouts .schema13
    let tupTy : Ty := ⟨.tuple [.bool, .uint .u32], 0⟩
    CoherentEnvExtends env₁ env₂ ∧
      env₁.isLayoutCoherent = true ∧
      evalCompilerQuery env₂ (.layoutOf .v2026_08_01 tupTy) =
        evalCompilerQuery env₁ (.layoutOf .v2026_06_01 tupTy) ∧
      evalCompilerQuery env₂ (.layoutOf .v2026_06_01 tupTy) =
        evalCompilerQuery env₂ (.layoutOf .v2026_08_01 tupTy) := by
  have hcoh : CoherentEnvExtends autoCfiEnv₁ (autoCfiEnv₁.withBridgedV08Layouts .schema13) :=
    withBridgedV08Layouts_coherentExtends autoCfiEnv₁ .schema13 (by decide)
      (isLayoutCoherent_of_schema_v06 autoCfiEnv₁ rfl)
  exact ⟨hcoh, hcoh.coherent₁,
    evalLayoutOf_any_dialect_of_coherentExtends hcoh .v2026_06_01 .v2026_08_01 _
      (fun _ h => nomatch h) (fun _ h => nomatch h),
    evalLayoutOf_any_dialect_of_coherentExtends (CoherentEnvExtends.refl _ hcoh.coherent₂)
      .v2026_08_01 .v2026_06_01 _ (fun _ h => nomatch h) (fun _ h => nomatch h)⟩

/-- Ill-formed supertrait-chain site whose terminal `traitRef` carries a non-`dyn` `Self`
(`⟨"fx::Area", [u32]⟩`, `args.tail = []`). Checking only `firstTrait.args.head? = some (dyn d)`
and `!traitRef.args.isEmpty` would falsely accept it, whereas `DynCallSite.wellFormed` validates
`tr.args.head? = some (.dynamic tr.defPath)` on every hop including the terminal `traitRef`. -/
def dynBadTermNonDynSite : DynCallSite :=
  { dynSubSite with
    lookupOp := ⟨⟨"fx::Area", [.uint .u32]⟩, 0, [dynSubTraitRef], none⟩ }

/-- Ill-formed supertrait-chain site whose terminal `traitRef` carries a mismatched `dyn` `Self`
(`⟨"fx::Area", [dyn Other]⟩`). -/
def dynBadTermOtherDynSite : DynCallSite :=
  { dynSubSite with
    lookupOp := ⟨⟨"fx::Area", [.dynamic "fx::Other"]⟩, 0, [dynSubTraitRef], none⟩ }

/-- **Terminal/intermediate `TraitRef` `Self`-validation canary**: both `dynBadTermNonDynSite`
and `dynBadTermOtherDynSite` satisfy `firstTrait.args.head? = some (.dynamic "fx::SubArea")`,
`!traitRef.args.isEmpty`, `dynKey.2 = .dynamic "fx::SubArea" :: traitRef.args.tail`, and
`methodMatchesTrait`, yet `DynCallSite.wellFormed` rejects both (`false`) and execution fails
closed (`.faulted .unsupported`). -/
theorem canary_dyn_terminal_trait_self_mismatch_fails_closed :
    (!dynBadTermNonDynSite.lookupOp.traitRef.args.isEmpty) = true ∧
    decide (dynBadTermNonDynSite.dynKey.2 =
      .dynamic "fx::SubArea" :: dynBadTermNonDynSite.lookupOp.traitRef.args.tail) = true ∧
    dynBadTermNonDynSite.wellFormed = false ∧
    dynBadTermOtherDynSite.wellFormed = false ∧
    evalDynWithOpaqueCallees dynSubEnv13 dynFullTbl dynBadTermNonDynSite dynSubRoot 12 dynSubInit =
      .faulted .unsupported [.event 1] ∧
    evalDynWithOpaqueCallees dynSubEnv13 dynFullTbl dynBadTermOtherDynSite dynSubRoot 12 dynSubInit =
      .faulted .unsupported [.event 1] := by
  decide +kernel

/-- Broken Schema-13 environment where vtable `7` slot `0` mistakenly stores the uninstantiated
virtual key `("fx::Area::area", [dyn Area])` instead of a concrete `impl` method. -/
def brokenVirtualVTableEnv13 : CompilerQueryEnv :=
  { dynEnv13 with
    fnAbis := [("fx::Area::area", fxRetU32Abi)]
    vtables := some [⟨7, dynTraitRef, [("fx::Area::area", [.dynamic "fx::Area"])], [], []⟩] }

/-- **Unresolved `dyn` vtable target & empty item-name fail-closed canary**:
1. In `brokenVirtualVTableEnv13`, `resolveDynTarget` returns `.ok ("fx::Area::area", [dyn Area])`
   and `slotMethodAgrees` is `true` (both paths end in `::area`), so without `vtableTargetAgrees`
   the redirected step leaks into `stepBranchPruned` and produces an unlinked `.external` call!
2. `vtableTargetAgrees` rejects `(dynSelfTrait? target).isSome` (`false`), so `dynDispatchStep`
   and `evalDynWithOpaqueCallees` fail closed with `.faulted .unsupported`
   (`dynDispatchStep_of_dyn_target`).
3. Empty item segments (`""` or trailing `"::"`) are rejected by both `implementsCalledMethod`
   and `slotMethodAgrees` even when `expectedTraitMethod? = some ""`. -/
theorem canary_dyn_unresolved_vtable_target_and_empty_item_fails_closed :
    resolveDynTarget brokenVirtualVTableEnv13 dynSite ⟨7, 0⟩ =
      .ok ("fx::Area::area", [.dynamic "fx::Area"]) ∧
    slotMethodAgrees dynSite "fx::Area::area" = true ∧
    vtableTargetAgrees dynSite ("fx::Area::area", [.dynamic "fx::Area"]) = false ∧
    (runSteps (stepBranchPruned (redirectResolver dynFullTbl dynSite.dynKey
        ("fx::Area::area", [.dynamic "fx::Area"])) dynRoot) 12 dynInit []).summary =
      ⟨.external, [.event 1], none, some "fx::Area::area"⟩ ∧
    dynDispatchStep brokenVirtualVTableEnv13 dynFullTbl dynSite dynRoot dynAtCall =
      MirStepNode.unsupported ∧
    evalDynWithOpaqueCallees brokenVirtualVTableEnv13 dynFullTbl dynSite dynRoot 12 dynInit =
      .faulted .unsupported [.event 1] ∧
    implementsCalledMethod "" "" = false ∧
    implementsCalledMethod "fx::Area::" "fx::Impl::" = false ∧
    slotMethodAgrees
      ({ dynSite with
        dynKey := ("", [.dynamic "fx::Area"])
        lookupOp := ⟨dynTraitRef, 0, [], some ""⟩ }) "" = false :=
  ⟨by decide, by decide, by decide, by decide +kernel,
    dynDispatchStep_of_dyn_target (target := ("fx::Area::area", [.dynamic "fx::Area"]))
      brokenVirtualVTableEnv13 dynFullTbl dynRoot dynAtCall
      dynSite_wellFormed dyn_vtablePtr_atCall (by decide) rfl,
    by decide +kernel, by decide, by decide, by decide⟩

/-- **`DynCallRegistry` well-formedness theorems & unconditional non-`dyn` trusted agreement**:
1. Every member of `dynTwoSiteRegistry` is uniquely returned by `findSite?`
   (`DynCallRegistry.findSite?_eq_some_of_wellFormed`).
2. Duplicate keys fail `wellFormed` and yield `findSite? = none` at arbitrary positions
   (`DynCallRegistry.findSite?_eq_none_of_duplicate`).
3. On `dynDeadBranchRoot` with `canaryFullTbl.toList` linked in `memory.callees`, both
   `evalDynWithOpaqueCallees` and `evalDynRegistryWithOpaqueCallees` equal the iterated trusted
   `stepMirFn` unconditionally (`evalDynWithOpaqueCallees_eq_trusted_of_no_dyn_unconditional`,
   `evalDynRegistryWithOpaqueCallees_eq_trusted_of_no_dyn_unconditional`). -/
theorem canary_dyn_registry_theorems_and_unconditional_frames :
    (dynTwoSiteRegistry.findSite? dynSubSite.dynKey = some dynSubSite ∧
      dynSubSite.wellFormed = true) ∧
    (DynCallRegistry.wellFormed ([dynSubBonusSite] ++ dynSite :: [] ++ dynDuplicateSite :: []) = false ∧
      DynCallRegistry.findSite? ([dynSubBonusSite] ++ dynSite :: [] ++ dynDuplicateSite :: [])
        dynSite.dynKey = none) ∧
    evalDynWithOpaqueCallees dynEnv12 canaryFullTbl dynSite dynDeadBranchRoot 12
        (initMachineStateWithCallees dynDeadBranchRoot [] canaryFullTbl.toList) =
      runSteps (stepMirFn dynDeadBranchRoot) 12
        (initMachineStateWithCallees dynDeadBranchRoot [] canaryFullTbl.toList) [] ∧
    evalDynRegistryWithOpaqueCallees dynEnv12 canaryFullTbl [dynSite] dynDeadBranchRoot 12
        (initMachineStateWithCallees dynDeadBranchRoot [] canaryFullTbl.toList) =
      runSteps (stepMirFn dynDeadBranchRoot) 12
        (initMachineStateWithCallees dynDeadBranchRoot [] canaryFullTbl.toList) [] :=
  ⟨DynCallRegistry.findSite?_eq_some_of_wellFormed (by decide) (by simp [dynTwoSiteRegistry]),
    DynCallRegistry.findSite?_eq_none_of_duplicate [dynSubBonusSite] [] [] rfl rfl,
    evalDynWithOpaqueCallees_eq_trusted_of_no_dyn_unconditional dynEnv12 canaryFullTbl dynSite
      dynDeadBranchRoot 12 _ (initMachineStateWithCallees_callees _ _ _) (by decide +kernel),
    evalDynRegistryWithOpaqueCallees_eq_trusted_of_no_dyn_unconditional dynEnv12 canaryFullTbl
      [dynSite] dynDeadBranchRoot 12 _ (initMachineStateWithCallees_callees _ _ _)
      (by decide +kernel)⟩


/-! ## Part C: worked `BEq`-shadowing demonstration (`tholenst` cl/1022563952) -/

namespace ShadowingDemo

/-- A key type that, like every key type of the two modules, derives only `DecidableEq`. -/
inductive DemoKey : Type where
  | unit
  | idx (n : Nat)
  deriving DecidableEq

/-- Non-shadowed: `==` on `DemoKey` is `instBEqOfDecidableEq`, i.e. `decide`. -/
theorem demoKey_beq_eq_decide (a b : DemoKey) : (a == b) = decide (a = b) := rfl

/-- Non-shadowed: `beq_iff_eq` fires under `simp` via the core `instLawfulBEq`. -/
theorem demoKey_beq_iff (a b : DemoKey) : (a == b) = true ↔ a = b := by simp

/-- The structural `BEq` that a redundant `BEq` derivation next to `DecidableEq`
would install. -/
@[instance_reducible]
def structuralBEq : BEq DemoKey :=
  ⟨fun a b =>
    match a, b with
    | .unit, .unit => true
    | .idx m, .idx n => Nat.beq m n
    | _, _ => false⟩

-- Without the redundant instance, `LawfulBEq DemoKey` is the core `instLawfulBEq`.
/-- info: instLawfulBEq -/
#guard_msgs in
#synth LawfulBEq DemoKey

section Shadowed
attribute [local instance] structuralBEq

/-- With the redundant instance in scope, `==` elaborates to the structural `BEq`
(no longer `decide (· = ·)`). -/
theorem shadowed_beq_is_structural (m n : Nat) :
    (DemoKey.idx m == DemoKey.idx n) = Nat.beq m n := rfl

-- ...and `LawfulBEq DemoKey` can no longer be synthesized, so `beq_iff_eq`
-- (and every `LawfulBEq`-keyed `List`/`Option` lemma) silently stops applying.
/--
error: failed to synthesize
  LawfulBEq DemoKey

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs (whitespace := lax) in
#synth LawfulBEq DemoKey

end Shadowed

/-- Real `Trusted` type audit connection (`theory/Correspondence/V2026_06_01/L4_TreeBorrows.lean:80`):
with `DecidableEq TreeBorrowPerm` alone, `LawfulBEq TreeBorrowPerm` is synthesized
via `instLawfulBEq` and `beq_iff_eq` holds. -/
theorem treeBorrowPerm_beq_iff_eq_by_simp (a b : TreeBorrowPerm) : (a == b) = true ↔ a = b := by
  simp

/-- Co-import check: the library lemma `Anneal.OpaqueCalleeTable.treeBorrowPerm_beq_iff_eq`
(stated against `instBEqOfDecidableEq`) applies verbatim inside the full `Anneal` closure, so no
imported module installs a competing global `BEq TreeBorrowPerm`. -/
example (a b : TreeBorrowPerm) : (a == b) = true ↔ a = b :=
  Anneal.OpaqueCalleeTable.treeBorrowPerm_beq_iff_eq

/-- info: instLawfulBEq -/
#guard_msgs in
#synth LawfulBEq TreeBorrowPerm

/-- The redundant structural `BEq TreeBorrowPerm` derived at
`theory/Correspondence/V2026_06_01/L4_TreeBorrows.lean:80`. -/
@[instance_reducible]
def structuralBEqTreeBorrowPerm : BEq TreeBorrowPerm :=
  ⟨fun a b =>
    match a, b with
    | .cell, .cell => true
    | .reservedFrz true, .reservedFrz true => true
    | .reservedFrz false, .reservedFrz false => true
    | .reservedIM, .reservedIM => true
    | .unique, .unique => true
    | .frozen, .frozen => true
    | .disabled, .disabled => true
    | _, _ => false⟩

section ShadowedTreeBorrowPerm
attribute [local instance] structuralBEqTreeBorrowPerm

-- Installing the redundant `BEq TreeBorrowPerm` shadows `instBEqOfDecidableEq`
-- and breaks `LawfulBEq TreeBorrowPerm` synthesis.
/--
error: failed to synthesize
  LawfulBEq TreeBorrowPerm

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs (whitespace := lax) in
#synth LawfulBEq TreeBorrowPerm

end ShadowedTreeBorrowPerm

/-- V2026_08_01 `TreeBorrowPerm` co-import check (`theory/Correspondence/V2026_08_01/L4_TreeBorrows.lean:61`):
with `DecidableEq` alone in `Anneal.CompilerQueryEnv`, `LawfulBEq` synthesizes via `instLawfulBEq`
and `treeBorrowPermV08_beq_iff_eq` applies directly. -/
example (a b : Trusted.Rustc.V2026_08_01.MirSemantics.TreeBorrowPerm) : (a == b) = true ↔ a = b :=
  Anneal.CompilerQueryEnv.treeBorrowPermV08_beq_iff_eq

/-- info: instLawfulBEq -/
#guard_msgs in
#synth LawfulBEq Trusted.Rustc.V2026_08_01.MirSemantics.TreeBorrowPerm

end ShadowingDemo

/-! ## `@[irreducible]` opacity witness on all five sealed operations

At default transparency `whnf` leaves `OpaqueCalleeTable.ofList` (the sealed table literal),
`toList`, `lookupRaw`, `traitImpls`, and `lookup` stuck — no `O(|callees|)` `findCallee?` /
`lookupCallee` / `flatMapTraitImpls` unfolding — and the carrier type itself is sealed; only an
explicit `.all` transparency sees through the seal (self-test). -/

open Lean Meta in
run_meta do
  let tbl := mkConst ``canaryFullTbl
  let raw := mkApp2 (mkConst ``OpaqueCalleeTable.lookupRaw) tbl (mkStrLit "fx::live_f")
  let full := mkApp5 (mkConst ``OpaqueCalleeTable.lookup) tbl
    (mkConst ``fxLayouts) (mkStrLit "fx::live_f")
    (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``RigidTy))
    (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``TraitImplEntry))
  let impls := mkApp (mkConst ``OpaqueCalleeTable.traitImpls) tbl
  let asList := mkApp (mkConst ``OpaqueCalleeTable.toList) tbl
  for (e, head) in [(tbl, ``OpaqueCalleeTable.ofList), (raw, ``OpaqueCalleeTable.lookupRaw),
      (full, ``OpaqueCalleeTable.lookup), (impls, ``OpaqueCalleeTable.traitImpls),
      (asList, ``OpaqueCalleeTable.toList)] do
    let r ← whnf e
    unless r.isAppOf head do
      throwError "opacity witness failed: whnf unfolded {head} to {r}"
    let r' ← withTransparency .all (whnf e)
    if r'.isAppOf head then
      throwError "opacity witness self-test failed: `.all` transparency did not unfold {e}"
  let carrier := mkConst ``OpaqueCalleeTable
  unless (← whnf carrier).isConstOf ``OpaqueCalleeTable do
    throwError "opacity witness failed: the carrier type `OpaqueCalleeTable` unfolded"
  if (← withTransparency .all (whnf carrier)).isConstOf ``OpaqueCalleeTable then
    throwError "opacity witness self-test failed: `.all` did not unfold the carrier type"

/-! ## Heartbeat regression gate (`M = 4` vs. `M = 32` callees)

The gated obligation is the client pattern the opaque table exists for: a branch-pruned
multi-step run over an `M`-callee table (`M` fillers, the dead-arm `g_dead`, and the live
`live_f`) equals the run over the one-element narrowed table, proved by demanded-key cone
narrowing over the narrowed run's keys (`canary_narrow_demandedKeys`, computed once; the
dead arm demands nothing) and one `O(1)` key certificate per demanded key
(`lookupKey_hit_mono`). The raw certificate is a hypothesis (a capture tool emits it once
per table), so neither the elaborator nor the kernel ever inspects the table: the cost of
elaborating *and kernel-checking* the proof must not depend on `M`. The gate measures
`IO.getNumHeartbeats` around synchronous elaboration (`Elab.async false`, kernel check
included) after a warm-up and requires `Hb(M = 32) ≤ 1.25 × Hb(M = 4)`.

Sensitivity self-test: the same obligation proved with a definitional `show` from
`lookupKey` to `lookup` type-checks in the elaborator without touching the seal, but the
kernel (which ignores `@[irreducible]`) unfolds the differently-headed sealed operations
into the `M`-element list scan; the gate requires that variant to grow by at least 40% from
`M = 4` to `M = 32`, so a regression that makes the certificate path leak `tbl.toList`
unfolding — in the elaborator or in the kernel — fails this file. -/

/-- `m` unrelated captured callees padding a gate table. -/
def gateFillers (m : Nat) : List CapturedMir :=
  (List.range m).map fun i => fxLeaf ("fx::gate_filler_" ++ toString i) i 0 []

/-- Gate table: `m` fillers, the dead-arm `g_dead`, and the live `live_f` last. -/
def gateTbl (m : Nat) : OpaqueCalleeTable := .ofList (gateFillers m ++ [fxGDead, fxLiveF])

/-- `live_f`'s raw certificate in the one-element narrowed table. -/
theorem canaryNarrowTbl_lookupRaw_live :
    canaryNarrowTbl.lookupRaw "fx::live_f" = some fxLiveF :=
  lookupRaw_ofList_cons_hit rfl

/-- The narrowed run's demanded keys (one-time, over the one-element table): only the live
call; the dead arm's `g_dead` is never demanded. -/
theorem canary_narrow_demandedKeys :
    demandedKeys canaryNarrowTbl.lookup canaryRoot 8 canaryInit = [canaryLiveKey] := by
  decide +kernel

/-- Multi-callee gate table (`m` fillers + dead `g_dead` + generic `poly` + `Area` impl holder +
`Circle::area` override). -/
def multiGateTbl (m : Nat) : OpaqueCalleeTable :=
  .ofList (gateFillers m ++ [fxGDead, fxPoly, fxAreaImplHolder, fxCircleArea])

/-- Narrowed demanded keys of `multiRoot` (computed once over the 3-entry narrowed table). -/
theorem canary_multi_narrow_demandedKeys :
    demandedKeys multiNarrowTbl.lookup multiRoot 12 multiInit = [multiPolyKey, multiAreaKey] := by
  decide +kernel

/-- Pre-proved narrow lookup certificate for `multiPolyKey`. -/
theorem multiNarrow_polyKey_cert :
    multiNarrowTbl.lookupKey multiPolyKey =
      some (fxPoly.instantiate ([RigidTy.uint .u32].zip [fxU32Layout])) := by
  have hrawN : multiNarrowTbl.lookupRaw "fx::poly" = some fxPoly :=
    lookupRaw_ofList_cons_hit rfl
  exact lookupKey_hit_free_poly_opaque rfl multiNarrowTbl_traitImpls (by decide)
    hrawN rfl canary_u32_instantiationLayouts

/-- Pre-proved narrow lookup certificate for `multiAreaKey`. -/
theorem multiNarrow_areaKey_cert :
    multiNarrowTbl.lookupKey multiAreaKey = some fxCircleArea := by
  have himplN : multiNarrowTbl.lookupRaw "fx::<impl Area for Circle>::area" =
      some fxCircleArea := by
    unfold multiNarrowTbl
    rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  have hcolN :
      collectMatchingTraitImplsWith multiNarrowTbl.lookupRaw ([] ++ [fxAreaEntry])
        "fx::Area::area" [fxCircleTy] [] = [(fxAreaEntry, some [])] := by
    rw [List.nil_append,
      collectMatchingTraitImplsWith_cons_hit_mono (c := fxCircleArea)
        (by decide) rfl (by decide) himplN (by decide) rfl]
    rfl
  exact lookupKey_trait_hit_cert (winner := fxAreaEntry) rfl (by decide) multiNarrowTbl_traitImpls
    hcolN (by decide) himplN (by decide) rfl

open Lean Elab Command in
run_cmd do
  let o1 : Nat → CommandElabM (TSyntax `command) := fun m => do
    let mLit := Syntax.mkNumLit (toString m)
    `(command|
      set_option Elab.async false in
      example (hraw : (gateTbl $mLit).lookupRaw "fx::live_f" = some fxLiveF) :
          evalWithOpaqueCallees canaryNarrowTbl canaryRoot 8 canaryInit =
            evalWithOpaqueCallees (gateTbl $mLit) canaryRoot 8 canaryInit := by
        apply evalWithOpaqueCallees_cone_narrow_of_narrow
        rw [canary_narrow_demandedKeys]
        intro k hk
        simp only [List.mem_singleton] at hk
        subst hk
        rw [lookupKey_hit_mono canaryNarrowTbl_lookupRaw_live rfl rfl,
          lookupKey_hit_mono hraw rfl rfl])
  let o1PolyTrait : Nat → CommandElabM (TSyntax `command) := fun m => do
    let mLit := Syntax.mkNumLit (toString m)
    `(command|
      set_option Elab.async false in
      example
          (htraits : (multiGateTbl $mLit).traitImpls = [fxAreaEntry])
          (hpoly : (multiGateTbl $mLit).lookupRaw "fx::poly" = some fxPoly)
          (harea : (multiGateTbl $mLit).lookupRaw "fx::<impl Area for Circle>::area" =
            some fxCircleArea) :
          evalWithOpaqueCallees multiNarrowTbl multiRoot 12 multiInit =
            evalWithOpaqueCallees (multiGateTbl $mLit) multiRoot 12 multiInit := by
        apply evalWithOpaqueCallees_cone_narrow_of_narrow
        rw [canary_multi_narrow_demandedKeys]
        intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with h | h
        · subst h
          rw [multiNarrow_polyKey_cert,
            lookupKey_hit_free_poly_opaque rfl htraits (by decide) hpoly rfl
              canary_u32_instantiationLayouts]
        · subst h
          have hcol :
              collectMatchingTraitImplsWith (multiGateTbl $mLit).lookupRaw ([] ++ [fxAreaEntry])
                "fx::Area::area" [fxCircleTy] [] = [(fxAreaEntry, some [])] := by
            rw [List.nil_append,
              collectMatchingTraitImplsWith_cons_hit_mono (c := fxCircleArea)
                (by decide) rfl (by decide) harea (by decide) rfl]
            rfl
          rw [multiNarrow_areaKey_cert,
            lookupKey_trait_hit_cert (winner := fxAreaEntry) rfl (by decide) htraits
              hcol (by decide) harea (by decide) rfl])
  let leaky : Nat → CommandElabM (TSyntax `command) := fun m => do
    let mLit := Syntax.mkNumLit (toString m)
    `(command|
      set_option Elab.async false in
      example (hraw : (gateTbl $mLit).lookupRaw "fx::live_f" = some fxLiveF) :
          evalWithOpaqueCallees canaryNarrowTbl canaryRoot 8 canaryInit =
            evalWithOpaqueCallees (gateTbl $mLit) canaryRoot 8 canaryInit := by
        apply evalWithOpaqueCallees_cone_narrow_of_narrow
        rw [canary_narrow_demandedKeys]
        intro k hk
        simp only [List.mem_singleton] at hk
        subst hk
        show canaryNarrowTbl.lookup fxLayouts "fx::live_f" [] [] =
          (gateTbl $mLit).lookup fxLayouts "fx::live_f" [] []
        rw [lookupCallee_hit_mono canaryNarrowTbl_lookupRaw_live rfl,
          lookupCallee_hit_mono hraw rfl])
  let measure : TSyntax `command → CommandElabM Nat := fun cmd => do
    let h₀ ← IO.getNumHeartbeats
    elabCommand cmd
    let h₁ ← IO.getNumHeartbeats
    return h₁ - h₀
  -- Warm-up (one-time equation lemmas, instance and simp caches).
  discard <| measure (← o1 2)
  discard <| measure (← o1PolyTrait 2)
  discard <| measure (← leaky 2)
  let hb4 ← measure (← o1 4)
  let hb32 ← measure (← o1 32)
  let hbPT4 ← measure (← o1PolyTrait 4)
  let hbPT32 ← measure (← o1PolyTrait 32)
  let lk4 ← measure (← leaky 4)
  let lk32 ← measure (← leaky 32)
  unless 0 < hb4 && 0 < hbPT4 do
    throwError "heartbeat gate: no heartbeats measured for M = 4"
  unless hb32 * 4 ≤ hb4 * 5 do
    throwError "heartbeat regression gate (mono) failed: Hb(M = 32) = {hb32} > 1.25 × Hb(M = 4) = {hb4}"
  unless hbPT32 * 4 ≤ hbPT4 * 5 do
    throwError "heartbeat regression gate (poly+trait) failed: Hb(M = 32) = {hbPT32} > 1.25 × Hb(M = 4) = {hbPT4}"
  unless lk4 * 7 ≤ lk32 * 5 do
    throwError "heartbeat gate self-test failed: the kernel-unfolding variant did not scale \
      (Hb(M = 4) = {lk4}, Hb(M = 32) = {lk32})"

/-! ## `#guard_msgs` axiom pins on headline theorems

Every headline library theorem (and the key canaries of this file) is pinned to its exact
transitive axiom set. Any drift (a new `propext`/`Quot.sound` dependency where there was none,
or anything outside `{propext, Quot.sound}`) changes the `#print axioms` message and fails the
corresponding `#guard_msgs`. The module-wide `run_cmd` audit below covers every remaining
constant. -/

/-- info: 'Anneal.OpaqueCalleeTable.opaqueCalleeTable_lookup_eq_trusted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.opaqueCalleeTable_lookup_eq_trusted

/-- info: 'Anneal.OpaqueCalleeTable.decEqOfCtorIdx' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.decEqOfCtorIdx

/-- info: 'Anneal.OpaqueCalleeTable.instDecidableEqBinOp' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.instDecidableEqBinOp

/-- info: 'Anneal.OpaqueCalleeTable.rigidTyStructEq_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.rigidTyStructEq_iff

/-- info: 'Anneal.OpaqueCalleeTable.valueStructEq_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.valueStructEq_iff

/-- info: 'Anneal.OpaqueCalleeTable.rigidTy_beq_iff_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.rigidTy_beq_iff_eq

/-- info: 'Anneal.OpaqueCalleeTable.capturedMir_beq_iff_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.capturedMir_beq_iff_eq

/-- info: 'Anneal.OpaqueCalleeTable.machineState_beq_iff_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.machineState_beq_iff_eq

/-- info: 'Anneal.OpaqueCalleeTable.treeBorrowPerm_beq_iff_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.treeBorrowPerm_beq_iff_eq

/-- info: 'Anneal.OpaqueCalleeTable.stringEq_eq_true_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.stringEq_eq_true_iff

/-- info: 'Anneal.OpaqueCalleeTable.traitImpls_ofList' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.traitImpls_ofList

/-- info: 'Anneal.OpaqueCalleeTable.lookupRaw_ofList_append_cons_of_skips' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupRaw_ofList_append_cons_of_skips

/-- info: 'Anneal.OpaqueCalleeTable.lookupRaw_ofList_of_mem_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupRaw_ofList_of_mem_nodup

/-- info: 'Anneal.OpaqueCalleeTable.lookupCallee_hit_mono' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupCallee_hit_mono

/-- info: 'Anneal.OpaqueCalleeTable.lookupKey_hit_mono' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupKey_hit_mono

/-- info: 'Anneal.OpaqueCalleeTable.lookupCallee_hit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupCallee_hit

/-- info: 'Anneal.OpaqueCalleeTable.lookupCallee_hit_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupCallee_hit_poly

/-- info: 'Anneal.OpaqueCalleeTable.lookupCallee_hit_free_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupCallee_hit_free_poly

/-- info: 'Anneal.OpaqueCalleeTable.lookupCallee_hit_free_poly_opaque' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupCallee_hit_free_poly_opaque

/-- info: 'Anneal.OpaqueCalleeTable.lookupCallee_trait_hit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupCallee_trait_hit

/-- info: 'Anneal.OpaqueCalleeTable.lookupCallee_trait_hit_cert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupCallee_trait_hit_cert

/-- info: 'Anneal.OpaqueCalleeTable.lookupCallee_trait_hit_poly_cert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupCallee_trait_hit_poly_cert

/-- info: 'Anneal.OpaqueCalleeTable.lookupCallee_trait_default_hit_cert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupCallee_trait_default_hit_cert

/-- info: 'Anneal.OpaqueCalleeTable.lookupCallee_miss' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupCallee_miss

/-- info: 'Anneal.OpaqueCalleeTable.lookupCallee_miss_direct' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupCallee_miss_direct

/-- info: 'Anneal.OpaqueCalleeTable.stepTerminatorWith_prune_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.stepTerminatorWith_prune_exact

/-- info: 'Anneal.OpaqueCalleeTable.stepBranchPruned_eq_trusted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.stepBranchPruned_eq_trusted

/-- info: 'Anneal.OpaqueCalleeTable.evalWithOpaqueCallees_eq_evalWithListCallees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.evalWithOpaqueCallees_eq_evalWithListCallees

/-- info: 'Anneal.OpaqueCalleeTable.evalWithOpaqueCallees_eq_trusted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.evalWithOpaqueCallees_eq_trusted

/-- info: 'Anneal.OpaqueCalleeTable.evalWithOpaqueCallees_cone_narrow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.evalWithOpaqueCallees_cone_narrow

/-- info: 'Anneal.OpaqueCalleeTable.evalWithOpaqueCallees_cone_narrow_of_narrow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.evalWithOpaqueCallees_cone_narrow_of_narrow

/-- info: 'Anneal.OpaqueCalleeTable.evalRvalue_keepsCtx' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.evalRvalue_keepsCtx

/-- info: 'Anneal.OpaqueCalleeTable.evalStmt_frames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.evalStmt_frames

/-- info: 'Anneal.OpaqueCalleeTable.evalDirectRustIntrinsic?_frames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.evalDirectRustIntrinsic?_frames

/-- info: 'Anneal.OpaqueCalleeTable.stepTerminatorWith_frames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.stepTerminatorWith_frames

/-- info: 'Anneal.OpaqueCalleeTable.stepBranchPruned_frames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.stepBranchPruned_frames

/-- info: 'Anneal.OpaqueCalleeTable.stepMirFn_frames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.stepMirFn_frames

/-- info: 'Anneal.OpaqueCalleeTable.runVisited_frames' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.runVisited_frames

/-- info: 'Anneal.OpaqueCalleeTable.trusted_runVisited_frames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.trusted_runVisited_frames

/-- info: 'Anneal.OpaqueCalleeTable.opaqueRunFramed_of_init' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.opaqueRunFramed_of_init

/-- info: 'Anneal.OpaqueCalleeTable.evalWithOpaqueCallees_eq_trusted_unconditional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.evalWithOpaqueCallees_eq_trusted_unconditional

/-- info: 'Anneal.OpaqueCalleeTable.evalWithOpaqueCallees_eq_trusted_initWithCallees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.evalWithOpaqueCallees_eq_trusted_initWithCallees

/-- info: 'Anneal.OpaqueCalleeTable.evalWithOpaqueCallees_eq_trusted_initWithMemoryAndCallees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.evalWithOpaqueCallees_eq_trusted_initWithMemoryAndCallees

/-- info: 'Anneal.OpaqueCalleeTable.evalWithOpaqueCallees_eq_trusted_initWithMemoryAndCallees_of_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.evalWithOpaqueCallees_eq_trusted_initWithMemoryAndCallees_of_wf

/-- info: 'Anneal.OpaqueCalleeTable.demandedKeys_extraTraitImpls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.demandedKeys_extraTraitImpls

/-- info: 'Anneal.OpaqueCalleeTable.calleesAgreeOn_toList_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.calleesAgreeOn_toList_iff

/-- info: 'Anneal.OpaqueCalleeTable.lookupKey_eq_of_agreesOn_mono' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupKey_eq_of_agreesOn_mono

/-- info: 'Anneal.OpaqueCalleeTable.lookupKey_eq_of_agreesOn_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupKey_eq_of_agreesOn_free

/-- info: 'Anneal.OpaqueCalleeTable.evalWithOpaqueCallees_cone_narrow_of_agreesOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.evalWithOpaqueCallees_cone_narrow_of_agreesOn

/-- info: 'Anneal.OpaqueCalleeTable.runMirExecBounded_of_runSteps_halted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.runMirExecBounded_of_runSteps_halted

/-- info: 'Anneal.OpaqueCalleeTable.runCfgWithCallees_of_evalWithOpaqueCallees_halted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.runCfgWithCallees_of_evalWithOpaqueCallees_halted

/-- info: 'Anneal.OpaqueCalleeTable.runCfgWithCallees_of_evalWithOpaqueCallees_halted_of_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.runCfgWithCallees_of_evalWithOpaqueCallees_halted_of_wf

/-- info: 'Anneal.OpaqueCalleeTable.runCfgWithCallees_cone_narrow_of_agreesOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.runCfgWithCallees_cone_narrow_of_agreesOn

/-- info: 'Anneal.OpaqueCalleeTable.runCfgWithCallees_cone_narrow_of_agreesOn_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.runCfgWithCallees_cone_narrow_of_agreesOn_closed

/-- info: 'Anneal.OpaqueCalleeTable.wpMirExecSym_cone_narrow_of_agreesOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.wpMirExecSym_cone_narrow_of_agreesOn

/-- info: 'Anneal.OpaqueCalleeTable.mirWpConverges_cone_narrow_of_agreesOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.mirWpConverges_cone_narrow_of_agreesOn

/-- info: 'Anneal.OpaqueCalleeTable.runCfgWithCallees_cone_narrow_of_agreesOn_closed_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.runCfgWithCallees_cone_narrow_of_agreesOn_closed_wf

/-- info: 'Anneal.OpaqueCalleeTable.wpMirExecSym_cone_narrow_of_agreesOn_closed_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.wpMirExecSym_cone_narrow_of_agreesOn_closed_wf

/-- info: 'Anneal.OpaqueCalleeTable.mirWpConverges_cone_narrow_of_agreesOn_closed_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.mirWpConverges_cone_narrow_of_agreesOn_closed_wf

/-- info: 'Anneal.OpaqueCalleeTable.runCfgWithCallees_cone_narrow_of_agreesOn_closed_poly_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.runCfgWithCallees_cone_narrow_of_agreesOn_closed_poly_wf

/-- info: 'Anneal.OpaqueCalleeTable.wpMirExecSym_cone_narrow_of_agreesOn_closed_poly_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.wpMirExecSym_cone_narrow_of_agreesOn_closed_poly_wf

/-- info: 'Anneal.OpaqueCalleeTable.mirWpConverges_cone_narrow_of_agreesOn_closed_poly_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.mirWpConverges_cone_narrow_of_agreesOn_closed_poly_wf

/-- info: 'Anneal.CompilerQueryEnv.instDecidableEqUintTyV08' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.instDecidableEqUintTyV08

/-- info: 'Anneal.CompilerQueryEnv.rigidTyV08StructEq_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.rigidTyV08StructEq_iff

/-- info: 'Anneal.CompilerQueryEnv.SchemaLe.antisymm' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.SchemaLe.antisymm

/-- info: 'Anneal.CompilerQueryEnv.bridgeTypeLayout_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.bridgeTypeLayout_roundtrip

/-- info: 'Anneal.CompilerQueryEnv.bridgeLayout_roundtrip_v08' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.bridgeLayout_roundtrip_v08

/-- info: 'Anneal.CompilerQueryEnv.bridgeRigidTy_roundtrip' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.bridgeRigidTy_roundtrip

/-- info: 'Anneal.CompilerQueryEnv.computeLayout_bridge_commutes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.computeLayout_bridge_commutes

/-- info: 'Anneal.CompilerQueryEnv.computeLayoutV08Bridged_eq_computeLayoutV06_bridge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.computeLayoutV08Bridged_eq_computeLayoutV06_bridge

/-- info: 'Anneal.CompilerQueryEnv.evalLayoutOf_v08_eq_v06' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.evalLayoutOf_v08_eq_v06

/-- info: 'Anneal.CompilerQueryEnv.evalLayoutOf_v08_eq_v06_of_coherent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.evalLayoutOf_v08_eq_v06_of_coherent

/-- info: 'Anneal.CompilerQueryEnv.withBridgedV08Layouts_extends' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.withBridgedV08Layouts_extends

/-- info: 'Anneal.CompilerQueryEnv.evalLayoutOf_dialect_invariant_of_coherentExtends' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.evalLayoutOf_dialect_invariant_of_coherentExtends

/-- info: 'Anneal.CompilerQueryEnv.EnvExtends.of_raw' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.EnvExtends.of_raw

/-- info: 'Anneal.CompilerQueryEnv.query_schema12_unsupported_fallback' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.query_schema12_unsupported_fallback

/-- info: 'Anneal.CompilerQueryEnv.query_schema12_never_ok' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.query_schema12_never_ok

/-- info: 'Anneal.CompilerQueryEnv.query_mono_schema' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.query_mono_schema

/-- info: 'Anneal.CompilerQueryEnv.layoutOf_agrees_with_eager' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.layoutOf_agrees_with_eager

/-- info: 'Anneal.CompilerQueryEnv.memoLookup_memoize' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.memoLookup_memoize

/-- info: 'Anneal.CompilerQueryEnv.syncStorageRegion_blocks_iff_overlap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.syncStorageRegion_blocks_iff_overlap

/-- info: 'Anneal.CompilerQueryEnv.syncStorageRegion_blocks_zero_size' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.syncStorageRegion_blocks_zero_size

/-- info: 'Anneal.CompilerQueryEnv.fnAbiMismatch?_eq_none_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.fnAbiMismatch?_eq_none_iff

/-- info: 'Anneal.CompilerQueryEnv.abiCore_ok_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.abiCore_ok_iff

/-- info: 'Anneal.CompilerQueryEnv.evalLayoutOf_v06_ok_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.evalLayoutOf_v06_ok_iff

/-- info: 'Anneal.CompilerQueryEnv.evalLayoutOf_v08_ok_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.evalLayoutOf_v08_ok_iff

/-- info: 'Anneal.CompilerQueryEnv.evalAbiCompatible_ok_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.evalAbiCompatible_ok_iff

/-- info: 'Anneal.CompilerQueryEnv.evalSyncStorageGuard_ok_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.evalSyncStorageGuard_ok_iff

/-- info: 'Anneal.CompilerQueryEnv.evalVTableMethodLookup_ok_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.evalVTableMethodLookup_ok_iff

/-- info: 'Anneal.CompilerQueryEnv.evalVTableSupertraitLookup_ok_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.evalVTableSupertraitLookup_ok_iff

/-- info: 'Anneal.CompilerQueryEnv.resolveVTableChain_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.resolveVTableChain_mono

/-- info: 'Anneal.CompilerQueryEnv.resolveDynTarget_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.resolveDynTarget_mono

/-- info: 'Anneal.CompilerQueryEnv.implementsCalledMethod' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.implementsCalledMethod

/-- info: 'Anneal.CompilerQueryEnv.methodMatchesTrait' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.methodMatchesTrait

/-- info: 'Anneal.CompilerQueryEnv.slotMethodAgrees_of_none' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.slotMethodAgrees_of_none

/-- info: 'Anneal.CompilerQueryEnv.slotMethodAgrees_of_some' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.slotMethodAgrees_of_some

/-- info: 'Anneal.CompilerQueryEnv.dynDispatchStep_of_not_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.dynDispatchStep_of_not_wellFormed

/-- info: 'Anneal.CompilerQueryEnv.dynDispatchStep_of_method_mismatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.dynDispatchStep_of_method_mismatch

/-- info: 'Anneal.CompilerQueryEnv.dynDispatchStep_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.dynDispatchStep_preserved

/-- info: 'Anneal.CompilerQueryEnv.dynDemandStep_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.dynDemandStep_preserved

/-- info: 'Anneal.CompilerQueryEnv.dynDemandStep_eq_dynDispatchStep_of_resolved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.dynDemandStep_eq_dynDispatchStep_of_resolved

/-- info: 'Anneal.CompilerQueryEnv.dynDemandStep_eq_trusted_of_not_demanded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.dynDemandStep_eq_trusted_of_not_demanded

/-- info: 'Anneal.CompilerQueryEnv.dynDemandStep_of_unregistered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.dynDemandStep_of_unregistered

/-- info: 'Anneal.CompilerQueryEnv.evalDynWithOpaqueCallees_preserved_of_narrow_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.evalDynWithOpaqueCallees_preserved_of_narrow_check

/-- info: 'Anneal.CompilerQueryEnv.dynRegistryStep_singleton' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.dynRegistryStep_singleton

/-- info: 'Anneal.CompilerQueryEnv.dynRegistryStep_eq_trusted_of_no_dyn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.dynRegistryStep_eq_trusted_of_no_dyn

/-- info: 'Anneal.CompilerQueryEnv.evalDynRegistryWithOpaqueCallees_preserved_of_narrow_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.evalDynRegistryWithOpaqueCallees_preserved_of_narrow_check

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_deadArm_cone_narrow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_deadArm_cone_narrow

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_deadArm_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_deadArm_halts

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_liveArm_required' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_liveArm_required

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_multi_cone_narrow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_multi_cone_narrow

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_naiveNarrow_breaks_trait_dispatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_naiveNarrow_breaks_trait_dispatch

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_trait_specificity_and_default_inheritance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_trait_specificity_and_default_inheritance

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_trait_cert_no_toList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_trait_cert_no_toList

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_trait_poly_and_default_cert_no_toList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_trait_poly_and_default_cert_no_toList

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_evalWithOpaqueCallees_eq_trusted_unconditional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_evalWithOpaqueCallees_eq_trusted_unconditional

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_frame_poly_trait_unconditional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_frame_poly_trait_unconditional

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_frame_nonvacuous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_frame_nonvacuous

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_unconditional_requires_linked_table' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_unconditional_requires_linked_table

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_agreesOn_live' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_agreesOn_live

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_cone_narrow_of_agreesOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_cone_narrow_of_agreesOn

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_runCfgWithCallees_bridge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_runCfgWithCallees_bridge

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_wpMirExecSym_bridge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_wpMirExecSym_bridge

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_initWithMemory_empty_of_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_initWithMemory_empty_of_wf

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_initWithMemory_requires_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_initWithMemory_requires_wf

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_runCfgWithCallees_narrow_to_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_runCfgWithCallees_narrow_to_empty

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_polyCone_closed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_polyCone_closed

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_runCfgWithCallees_poly_bridge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_runCfgWithCallees_poly_bridge

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.incoherence_breaks_dialect_agreement_canary' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.incoherence_breaks_dialect_agreement_canary

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.envExtends_allows_incoherent_v08_upgrade_canary' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.envExtends_allows_incoherent_v08_upgrade_canary

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.autoCfi_breaks_mono' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.autoCfi_breaks_mono

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.dyn_step_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.dyn_step_preserved

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_e2e_full_run_schema13' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_e2e_full_run_schema13

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_deadBranch_schema12_succeeds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_deadBranch_schema12_succeeds

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_two_receivers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_two_receivers

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_supertrait_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_supertrait_chain

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_unregistered_dyn_fails_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_unregistered_dyn_fails_closed

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_trait_arg_mismatch_fails_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_trait_arg_mismatch_fails_closed

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_multi_site_registry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_multi_site_registry

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_slot_method_mismatch_fails_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_slot_method_mismatch_fails_closed

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_registry_ambiguity_fails_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_registry_ambiguity_fails_closed

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_wrong_trait_prefix_fails_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_wrong_trait_prefix_fails_closed

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_generic_supertrait_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_generic_supertrait_chain

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_shim_dispatch_with_expected_trait_method' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_shim_dispatch_with_expected_trait_method

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_expected_trait_method_supertrait_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_expected_trait_method_supertrait_chain

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_slotMethodAgrees' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_slotMethodAgrees

/-- info: 'Anneal.OpaqueCalleeTable.lookupKey_miss_direct' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupKey_miss_direct

/-- info: 'Anneal.OpaqueCalleeTable.lookupKey_hit_free_poly_opaque' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupKey_hit_free_poly_opaque

/-- info: 'Anneal.OpaqueCalleeTable.lookupKey_trait_hit_cert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupKey_trait_hit_cert

/-- info: 'Anneal.OpaqueCalleeTable.lookupKey_trait_hit_poly_cert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupKey_trait_hit_poly_cert

/-- info: 'Anneal.OpaqueCalleeTable.lookupKey_trait_default_hit_cert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.lookupKey_trait_default_hit_cert

/-- info: 'Anneal.OpaqueCalleeTable.runCfgWithCallees_cone_narrow_of_callConeClosed_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.runCfgWithCallees_cone_narrow_of_callConeClosed_wf

/-- info: 'Anneal.OpaqueCalleeTable.runCfgWithCallees_cone_narrow_of_callConeClosedPoly_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.OpaqueCalleeTable.runCfgWithCallees_cone_narrow_of_callConeClosedPoly_wf

/-- info: 'Anneal.CompilerQueryEnv.instDecidableEqBinOpV08' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.instDecidableEqBinOpV08

/-- info: 'Anneal.CompilerQueryEnv.valueV08StructEq_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.valueV08StructEq_iff

/-- info: 'Anneal.CompilerQueryEnv.treeBorrowPermV08_beq_iff_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.treeBorrowPermV08_beq_iff_eq

/-- info: 'Anneal.CompilerQueryEnv.bridgeRigidTy_roundtrip_v08' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.bridgeRigidTy_roundtrip_v08

/-- info: 'Anneal.CompilerQueryEnv.evalLayoutOf_any_dialect_of_coherentExtends' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.evalLayoutOf_any_dialect_of_coherentExtends

/-- info: 'Anneal.CompilerQueryEnv.dynDispatchStep_of_dyn_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.dynDispatchStep_of_dyn_target

/-- info: 'Anneal.CompilerQueryEnv.dynDispatchStep_frames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.dynDispatchStep_frames

/-- info: 'Anneal.CompilerQueryEnv.dynRegistryStep_frames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.dynRegistryStep_frames

/-- info: 'Anneal.CompilerQueryEnv.DynCallRegistry.findSite?_eq_some_of_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.DynCallRegistry.findSite?_eq_some_of_wellFormed

/-- info: 'Anneal.CompilerQueryEnv.DynCallRegistry.findSite?_eq_none_of_duplicate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.DynCallRegistry.findSite?_eq_none_of_duplicate

/-- info: 'Anneal.CompilerQueryEnv.evalDynWithOpaqueCallees_eq_trusted_of_no_dyn_unconditional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.evalDynWithOpaqueCallees_eq_trusted_of_no_dyn_unconditional

/-- info: 'Anneal.CompilerQueryEnv.evalDynRegistryWithOpaqueCallees_eq_trusted_of_no_dyn_unconditional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryEnv.evalDynRegistryWithOpaqueCallees_eq_trusted_of_no_dyn_unconditional

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_callConeClosed_no_toList_and_shadowed_dup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_callConeClosed_no_toList_and_shadowed_dup

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_terminal_trait_self_mismatch_fails_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_terminal_trait_self_mismatch_fails_closed

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_unresolved_vtable_target_and_empty_item_fails_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_unresolved_vtable_target_and_empty_item_fails_closed

/-- info: 'Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_registry_theorems_and_unconditional_frames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.CompilerQueryAndOpaqueCalleeTests.canary_dyn_registry_theorems_and_unconditional_frames

end Anneal.CompilerQueryAndOpaqueCalleeTests

/-! ## Module-wide axiom and namespace audit

Traverses **every** constant each library module adds to the environment (its `.olean`
`constNames`: declarations, `deriving` / structure / matcher auxiliaries, and realized
equation lemmas) and fails elaboration unless

1. its transitive axioms are within `{propext, Quot.sound}` (no `Classical.choice`, no
   `sorryAx`, no `Lean.ofReduceBool`), and
2. it lies in the module's own namespace (`Anneal.OpaqueCalleeTable.*` /
   `Anneal.CompilerQueryEnv.*`, after private-name normalization). The only admitted foreign
   names are Lean's realized equation lemmas of foreign definitions (`eq_<n>`, `eq_def`,
   `eq_unfold`, `splitter`, `else_eq`, `_sparseCasesOn_<n>`), which are deterministic,
   statement-identical across modules, and deduplicated at import. An orphan enumeration
   `deriving instance DecidableEq` (a global `Trusted.….ofNat`) fails here.

The test file's own declarations (canaries, fixtures, the shadowing demo) are audited for
axioms as well. Non-vacuity: the auditor must flag `Classical.choice` (via `Classical.em`),
`sorryAx`, and `Lean.ofReduceBool`, and must cover a minimum number of constants and
theorems per module. -/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Quot.sound]
  let forbiddenOf (n : Name) : Elab.Command.CommandElabM (Array Name) := do
    return (← Lean.collectAxioms n).filter (fun ax => !allowed.contains ax)
  for (probe, ax) in [(``Classical.em, ``Classical.choice), (``sorryAx, ``sorryAx),
      (``Lean.ofReduceBool, ``Lean.ofReduceBool)] do
    unless (← forbiddenOf probe).contains ax do
      throwError "axiom audit self-test failed: {probe} not flagged for {ax}"
  let isRealizedEq (n : Name) : Bool :=
    match n.eraseMacroScopes with
    | .str _ last =>
      last == "eq_def" || last == "eq_unfold" || last == "splitter" || last == "else_eq" ||
        last.startsWith "eq_" || last.startsWith "_sparseCasesOn_"
    | _ => false
  for (mod, minConsts, minThms) in
      [(`Anneal.OpaqueCalleeTable, 1500, 1000), (`Anneal.CompilerQueryEnv, 1350, 700)] do
    let some idx := env.getModuleIdx? mod
      | throwError "audit: module {mod} is not imported"
    let names := env.header.moduleData[idx]!.constNames
    let mut inNamespace : Nat := 0
    let mut theorems : Nat := 0
    let mut leaked : Array Name := #[]
    let mut bad : Array (Name × Array Name) := #[]
    for n in names do
      let un := (Lean.privateToUserName? n).getD n
      if mod.isPrefixOf un then
        inNamespace := inNamespace + 1
      else
        unless un.hasMacroScopes || isRealizedEq un do
          leaked := leaked.push un
      if let some (.thmInfo _) := env.find? n then
        theorems := theorems + 1
      let f ← forbiddenOf n
      unless f.isEmpty do
        bad := bad.push (n, f)
    unless bad.isEmpty do
      throwError "axiom audit ({mod}): forbidden axioms {bad}"
    unless leaked.isEmpty do
      throwError "namespace audit ({mod}): constants declared outside {mod}: {leaked}"
    unless inNamespace ≥ minConsts && theorems ≥ minThms do
      throwError "audit coverage too low for {mod}: {names.size} constants \
        ({inNamespace} in namespace), {theorems} theorems"
  let mut localBad : Array (Name × Array Name) := #[]
  let mut localCount : Nat := 0
  for (n, _) in env.constants.map₂.toList do
    localCount := localCount + 1
    let f ← forbiddenOf n
    unless f.isEmpty do
      localBad := localBad.push (n, f)
  unless localBad.isEmpty do
    throwError "axiom audit (test file): forbidden axioms {localBad}"
  unless localCount ≥ 300 do
    throwError "axiom audit (test file): coverage too low ({localCount} constants)"
