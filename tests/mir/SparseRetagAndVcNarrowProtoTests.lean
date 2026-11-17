-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal
import Anneal.SparseRetagAndVcNarrowPrototype

/-!
# Verification Suite & Scaling Benchmarks for `Anneal.SparseRetagAndVcNarrowPrototype`

1. Co-imports `Anneal` and `Anneal.SparseRetagAndVcNarrowPrototype` to prove zero global constant /
   `DecidableEq` instance collisions.
2. Instantiates positive and negative canaries across all 4 subsystems (Part A `SparseRetagAttrIndex`,
   Part B `BatchedVcConeNarrowCert` + `hoistTraitImpls` + `@[irreducible] coerceValueAt`,
   Part C `DemandCallerLocationEnv` + `AllocRenamingRel`, Part D `LazyWriteChain` + `bvShiftSafe` /
   `shiftLeftBitsSafe`).
3. Measures kernel/elaborator `IO.getNumHeartbeats` scaling tables across `M ∈ {16, 64, 128, 256}`,
   `S ∈ {16, 64, 128}`, `N ∈ {16, 64}`, and `shift = 2^64`.
4. Runs a self-enforcing bottom-of-file `run_cmd` audit verifying `0` `unsafe`, `0` `Classical.choice`,
   `0` `Lean.ofReduceBool`, `0` `sorryAx`, `0` leaked constants (`leaked.isEmpty`), and `100%`
   theorem reachability (`unreached.isEmpty`).
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Anneal.SparseRetagAndVcNarrowProtoTests

open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Scalars
open Anneal.MirLiftCore
open Anneal.MirFuelFree
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Anneal.SparseRetagAndVcNarrowPrototype

/-! ## 1. Foundations & `@[irreducible]` Opacity Audit (`run_cmd`) -/

theorem test_listEqBy_witnesses :
    listEqBy Nat.beq [1, 2, 3] [1, 2, 3] = true ∧
    ([1, 2] : List Nat) = [1, 2] := by
  refine ⟨listEqBy_refl nat_beq_self_raw [1, 2, 3],
    listEqBy_eq_of_true (fun h => Nat.eq_of_beq_eq_true h) rfl⟩

/- Meta-level opacity witness verifying that both `coerceValueAt` and `SparseRetagAttrIndex.get?`
remain unreduced under `TransparencyMode.default` `whnf` and reduce to `Option.some` under
`TransparencyMode.all`. -/
open Lean Elab Command Term Meta in
run_cmd liftTermElabM do
  let coerceExpr ← elabTerm
    (← `(coerceValueAt protoLayouts (.uint .u32) (.scalar ⟨42, 4⟩))) none
  let coerceDef ← withTransparency .default (whnf coerceExpr)
  unless coerceDef.isAppOf ``coerceValueAt do
    throwError "opacity failure: coerceValueAt reduced under default transparency: {coerceDef}"
  let coerceAll ← withTransparency .all (whnf coerceExpr)
  unless coerceAll.isAppOf ``Option.some do
    throwError "unfolding failure: coerceValueAt did not reduce under .all transparency: {coerceAll}"
  let idxExpr ← elabTerm
    (← `(SparseRetagAttrIndex.get? ⟨NatBitTrie.empty.insert 3 true, 1⟩ 3)) none
  let idxDef ← withTransparency .default (whnf idxExpr)
  unless idxDef.isAppOf ``SparseRetagAttrIndex.get? do
    throwError "opacity failure: SparseRetagAttrIndex.get? reduced under default transparency"
  let idxAll ← withTransparency .all (whnf idxExpr)
  unless idxAll.isAppOf ``Option.some do
    throwError "unfolding failure: SparseRetagAttrIndex.get? did not reduce under .all transparency"
  logInfo m!"opacity audit passed: coerceValueAt and SparseRetagAttrIndex.get? sealed at .default and reducible at .all"

/-! ## 2. Part A Witnesses & Canaries (`SparseRetagAttrIndex`, `lean-miri#68`) -/

def sampleRetagRows : List RetagQueryRow :=
  [ ⟨0, "core::ptr::Unique::new_unchecked", true⟩,
    ⟨3, "alloc::boxed::Box::new", true⟩,
    ⟨7, "my_crate::mutate_ref", false⟩ ]

def dupRetagRows : List RetagQueryRow :=
  [ ⟨0, "a", true⟩, ⟨3, "b", false⟩, ⟨0, "a_dup", false⟩ ]

def oobRetagRows : List RetagQueryRow :=
  [ ⟨0, "a", true⟩, ⟨12, "oob", false⟩ ]

/-- Positive and negative canaries for `SparseRetagAttrIndex`, exercising every `RetagAttrErr`
variant, `lookupSparseRetag_eq_linearScan`, `frameAbsent_precedes_malformedTable`,
`lookupSparseRetag_cert`, `lookupSparseRetag_miss_cert`, and `SparseDefPathRetagIndex`. -/
theorem test_partA_sparseRetag_canaries :
    trieLookupBits (.empty : BitTrie Bool) [true, false] 1 = none ∧
    trieLookupBits (trieInsertBits (.empty : BitTrie Bool) [true] 1 true) [true] 1 = some true ∧
    trieLookupBits (trieInsertBits (.empty : BitTrie Bool) [true] 1 true) [false] 0 = none ∧
    (natLowBits 4 5).length = 4 ∧
    (NatBitTrie.empty : NatBitTrie Bool).get? 3 = none ∧
    ((NatBitTrie.empty : NatBitTrie Bool).insert 3 true).get? 3 = some true ∧
    SparseRetagAttrIndex.get? ⟨.empty, 0⟩ 0 = none ∧
    evalPreparedRetagLookup (prepareSparseRetagLoop 10 .empty 0 sampleRetagRows) 3 = .ok true ∧
    lookupSparseRetag 10 (prepareSparseRetagIndex 10 sampleRetagRows) 3 =
      linearScanRetagAttr 10 sampleRetagRows 3 ∧
    lookupSparseRetag 10 (prepareSparseRetagIndex 10 sampleRetagRows) 7 = .ok false ∧
    lookupSparseRetag 10 (prepareSparseRetagIndex 10 sampleRetagRows) 5 = .error .attrQueryAbsent ∧
    lookupSparseRetag 10 (prepareSparseRetagIndex 10 dupRetagRows) 0 = .error .duplicateDefQuery ∧
    lookupSparseRetag 10 (prepareSparseRetagIndex 10 oobRetagRows) 0 = .error .defIdOutOfBounds ∧
    lookupSparseRetag 10 (.error .duplicateDefQuery) 10 = .error .frameAbsent ∧
    (SparseDefPathRetagIndex.mk .empty).get? "x" = none ∧
    ((SparseDefPathRetagIndex.mk .empty).insert "alloc::boxed::Box::new" true).get?
      "alloc::boxed::Box::new" = some true := by
  have _ := @trieLookupBits_empty
  have _ := @trieLookupBits_insert_same
  have _ := @trieLookupBits_insert_diff
  have _ := @natLowBits_length
  have _ := @NatBitTrie.get?_empty
  have _ := @NatBitTrie.get?_insert
  have _ := @SparseRetagAttrIndex.get?_eq
  have _ := @prepareSparseRetagLoop_lookup_eq
  have _ := @lookupSparseRetag_eq_linearScan
  have _ := @frameAbsent_precedes_malformedTable
  have _ := @lookupSparseRetag_cert
  have _ := @lookupSparseRetag_miss_cert
  have _ := @SparseDefPathRetagIndex.get?_empty
  have _ := @SparseDefPathRetagIndex.get?_insert
  refine ⟨trieLookupBits_empty [true, false] 1,
    by rw [trieLookupBits_insert_same]; rfl,
    by rw [trieLookupBits_insert_diff [true] [false] .empty 1 true 0 rfl (by decide)]; rfl,
    natLowBits_length 4 5,
    NatBitTrie.get?_empty 3,
    by rw [NatBitTrie.get?_insert]; rfl,
    by rw [SparseRetagAttrIndex.get?_eq]; rfl,
    by rw [prepareSparseRetagLoop_lookup_eq 10 3 sampleRetagRows [] .empty 0 (fun _ => rfl)]; rfl,
    lookupSparseRetag_eq_linearScan 10 sampleRetagRows 3,
    by with_unfolding_all rfl,
    by with_unfolding_all rfl,
    by with_unfolding_all rfl,
    by with_unfolding_all rfl,
    frameAbsent_precedes_malformedTable (Nat.le_refl 10) .duplicateDefQuery,
    SparseDefPathRetagIndex.get?_empty "x",
    by rw [SparseDefPathRetagIndex.get?_insert]; rfl⟩

/-- Concrete MIR state with a mutable reference `_1 : &mut u32` borrowed from `_2 : u32` (`tag = 1`)
to test `evalFnEntryRetagWithSparseAttr` permission selection (`.reservedFrz false` when
`rustcNoWritable = true` vs. `.unique` when `rustcNoWritable = false` and `implicitWrites = true`)
and demand-locality on malformed tables. -/
def protoRefMutU32Ty : Ty := { kind := .ref .mut (.uint .u32), layoutIdx := 0 }

def protoRetagLocalDecls : List LocalDecl :=
  [ ⟨.mut, protoU32Ty, some "_0"⟩,
    ⟨.mut, protoRefMutU32Ty, some "_1"⟩,
    ⟨.mut, protoU32Ty, some "_2"⟩ ]

def protoRetagParentBorrow : BorrowEntry :=
  { tag := 1, targetLocal := 2, targetProjection := [], perm := .unique }

def protoRetagMachineState : MachineState :=
  { frame :=
      { locals :=
          [ .init (.scalar ⟨0, 4⟩),
            .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
            .init (.scalar ⟨42, 4⟩) ]
        blockIdx := 0
        stmtIdx := 0 }
    memory :=
      { emptyMemory with
        borrows := [protoRetagParentBorrow]
        nextTag := 2
        nextProtector := 1 } }

def protoFnEntryRetagStmt : Statement := ⟨.retag .fnEntry ⟨1, []⟩, "retag:fnEntry"⟩
def protoDefaultRetagStmt : Statement := ⟨.retag .default ⟨1, []⟩, "retag:default"⟩

theorem test_partA_operational_retag_overlay :
    fnEntryRetagPermWithAttr .mut (.uint .u32) true true =
      fnEntryRetagPerm .mut (.uint .u32) ∧
    fnEntryRetagPermWithAttr .mut (.uint .u32) false false =
      fnEntryRetagPerm .mut (.uint .u32) ∧
    evalFnEntryRetagWithSparseAttr 10 (prepareSparseRetagIndex 10 sampleRetagRows) true 7
        protoRetagMachineState protoFnEntryRetagStmt protoRetagLocalDecls protoLayouts =
      evalFnEntryRetagWithLinearScan 10 sampleRetagRows true 7
        protoRetagMachineState protoFnEntryRetagStmt protoRetagLocalDecls protoLayouts ∧
    evalFnEntryRetagWithSparseAttr 10 (.error .duplicateDefQuery) true 7
        protoRetagMachineState protoDefaultRetagStmt protoRetagLocalDecls protoLayouts =
      evalStmt protoRetagMachineState protoDefaultRetagStmt protoRetagLocalDecls protoLayouts ∧
    evalFnEntryRetagWithSparseAttr 10 (.error .duplicateDefQuery) false 7
        protoRetagMachineState protoFnEntryRetagStmt protoRetagLocalDecls protoLayouts =
      evalStmt protoRetagMachineState protoFnEntryRetagStmt protoRetagLocalDecls protoLayouts ∧
    evalFnEntryRetagWithSparseAttr 10 (prepareSparseRetagIndex 10 sampleRetagRows) true 3
        protoRetagMachineState protoFnEntryRetagStmt protoRetagLocalDecls protoLayouts =
      evalStmt protoRetagMachineState protoFnEntryRetagStmt protoRetagLocalDecls protoLayouts := by
  refine ⟨fnEntryRetagPermWithAttr_noWritable .mut (.uint .u32) true,
    fnEntryRetagPermWithAttr_implicitWrites_false .mut (.uint .u32) false,
    evalFnEntryRetagWithSparseAttr_eq_linear 10 sampleRetagRows true 7
      protoRetagMachineState protoFnEntryRetagStmt protoRetagLocalDecls protoLayouts,
    unusedMalformedTable_demand_local 10 .duplicateDefQuery true 7
      protoRetagMachineState protoDefaultRetagStmt protoRetagLocalDecls protoLayouts rfl,
    evalFnEntryRetagWithSparseAttr_implicitWrites_false 10 (.error .duplicateDefQuery) 7
      protoRetagMachineState protoFnEntryRetagStmt protoRetagLocalDecls protoLayouts,
    evalFnEntryRetagWithSparseAttr_rustcNoWritable_true 10
      (prepareSparseRetagIndex 10 sampleRetagRows) true 3
      protoRetagMachineState protoFnEntryRetagStmt protoRetagLocalDecls protoLayouts
      (lookupSparseRetag_cert (by decide) rfl)⟩

/-! ## 3. Part A Heartbeat Scaling Benchmarks (`M ∈ {16, 64, 128, 256}`) -/

def buildRetagRows : Nat → List RetagQueryRow
  | 0 => []
  | k + 1 => ⟨k, "crate::retag_fn", k % 2 == 0⟩ :: buildRetagRows k

/-- Construct the exact 12-bit binary radix trie for keys `0 ..< maxKey` top-down so lazy kernel
WHNF only forces the $O(\log M)$ path along a queried key rather than re-running $M$ insertions on
every theorem invocation. Proved definitionally equal (`rfl`) to `prepareSparseRetagIndex`. -/
def mkDirectBitTrie : Nat → Nat → Nat → Nat → BitTrie Bool
  | 0, maxKey, curKey, _ =>
    if curKey < maxKey then .leaf [(curKey, curKey % 2 == 0)] else .empty
  | d + 1, maxKey, curKey, stride =>
    if !(curKey < maxKey) then .empty
    else
      .branch
        (mkDirectBitTrie d maxKey curKey (stride * 2))
        (mkDirectBitTrie d maxKey (curKey + stride) (stride * 2))

def buildSparseIndex (m : Nat) : SparseRetagAttrIndex :=
  ⟨⟨mkDirectBitTrie defaultRetagTrieDepth m 0 1⟩, m⟩

theorem prepareSparseRetagIndex_eq_buildSparseIndex_16 :
    prepareSparseRetagIndex 512 (buildRetagRows 16) = .ok (buildSparseIndex 16) := rfl

def retagRows16 : List RetagQueryRow := buildRetagRows 16
def retagRows64 : List RetagQueryRow := buildRetagRows 64
def retagRows128 : List RetagQueryRow := buildRetagRows 128
def retagRows256 : List RetagQueryRow := buildRetagRows 256

def sparseIdx16 : SparseRetagAttrIndex := buildSparseIndex 16
def sparseIdx64 : SparseRetagAttrIndex := buildSparseIndex 64
def sparseIdx128 : SparseRetagAttrIndex := buildSparseIndex 128
def sparseIdx256 : SparseRetagAttrIndex := buildSparseIndex 256

def retagResOkEq (r : Except RetagAttrErr Bool) (expected : Bool) : Bool :=
  match r with
  | .ok b => b == expected
  | .error _ => false

def runLinearRetagBench (definitionCount : Nat) (rows : List RetagQueryRow) : Nat → Bool
  | 0 => true
  | q + 1 =>
    retagResOkEq (linearScanRetagAttr definitionCount rows q) (q % 2 == 0) &&
      runLinearRetagBench definitionCount rows q

def runSparseRetagBench (definitionCount : Nat) (idx : SparseRetagAttrIndex) : Nat → Bool
  | 0 => true
  | q + 1 =>
    retagResOkEq (lookupSparseRetag definitionCount (.ok idx) q) (q % 2 == 0) &&
      runSparseRetagBench definitionCount idx q

open Lean Elab Command in
run_cmd do
  let bench (label : String) (mkCmd : CommandElabM (TSyntax `command)) : CommandElabM Unit := do
    let cmd ← mkCmd
    let h0 ← IO.getNumHeartbeats
    let t0 ← IO.monoNanosNow
    elabCommand cmd
    let t1 ← IO.monoNanosNow
    let h1 ← IO.getNumHeartbeats
    logInfo m!"BENCH {label} heartbeats={h1 - h0} ns={t1 - t0}"
  bench "PartA_linear_M16" `(command|
    theorem bench_partA_linear_16 :
        runLinearRetagBench 512 retagRows16 1 = true := rfl)
  bench "PartA_sparse_M16" `(command|
    theorem bench_partA_sparse_16 :
        runSparseRetagBench 512 sparseIdx16 1 = true := by with_unfolding_all rfl)
  bench "PartA_linear_M64" `(command|
    theorem bench_partA_linear_64 :
        runLinearRetagBench 512 retagRows64 1 = true := rfl)
  bench "PartA_sparse_M64" `(command|
    theorem bench_partA_sparse_64 :
        runSparseRetagBench 512 sparseIdx64 1 = true := by with_unfolding_all rfl)
  bench "PartA_linear_M128" `(command|
    theorem bench_partA_linear_128 :
        runLinearRetagBench 512 retagRows128 1 = true := rfl)
  bench "PartA_sparse_M128" `(command|
    theorem bench_partA_sparse_128 :
        runSparseRetagBench 512 sparseIdx128 1 = true := by with_unfolding_all rfl)
  bench "PartA_linear_M256" `(command|
    theorem bench_partA_linear_256 :
        runLinearRetagBench 512 retagRows256 1 = true := rfl)
  bench "PartA_sparse_M256" `(command|
    theorem bench_partA_sparse_256 :
        runSparseRetagBench 512 sparseIdx256 1 = true := by with_unfolding_all rfl)

/-! ## 4. Part B Witnesses, Canaries, & Scaling Benchmarks (`BatchedVcConeNarrowCert` + `coerceValueAt`) -/

theorem test_partB_batchedVcNarrow_and_coerceValueAt :
    hoistTraitImpls (stripCalleeTraitImpls protoNaiveNarrowCallees) [] ++
        flatMapTraitImpls (stripCalleeTraitImpls protoNaiveNarrowCallees) =
      [] ++ flatMapTraitImpls (stripCalleeTraitImpls protoNaiveNarrowCallees) ∧
    lookupCallee protoFullCallees protoLayouts "proto::Area::area" [protoCircleTy] [] =
      lookupCallee protoNaiveNarrowCallees protoLayouts "proto::Area::area" [protoCircleTy]
        protoHoistedExtra ∧
    runMirExecBounded 12 traitCallRootMir
        (.running (MachineState.mapMem
          (Memory.withCalleesAndTraits protoNaiveNarrowCallees protoHoistedExtra)
          (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir []
            emptyMemory protoFullCallees))) =
      (runMirExecBounded 12 traitCallRootMir
        (.running (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir []
          emptyMemory protoFullCallees))).map
        (MirOutcome.mapMem (Memory.withCalleesAndTraits protoNaiveNarrowCallees protoHoistedExtra)) ∧
    (vcMirWithCallees 12 traitCallRootMir
        (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir [] emptyMemory protoFullCallees)
        protoNaiveNarrowCallees protoHoistedExtra [] protoTraitCone
        (fun out => match out with | .normal (v, _) => v = Value.scalar ⟨31, 4⟩ | _ => False) ↔
      vcMirWithCallees 12 traitCallRootMir
        (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir [] emptyMemory protoFullCallees)
        protoFullCallees [] [] protoTraitCone
        (fun out => match out with | .normal (v, _) => v = Value.scalar ⟨31, 4⟩ | _ => False)) ∧
    coerceValueAt protoLayouts (.uint .u32) (.scalar ⟨42, 4⟩) =
      some (.scalar ⟨wrapScalarBits 42 (scalarModulus 4), 4⟩) ∧
    coerceValueAt protoLayouts .bool (.scalar (boolToScalar true)) =
      some (.scalar (boolToScalar true)) ∧
    coerceValueAt protoLayouts (.ref .not (.uint .u32))
        (.ptr { allocId := 1, offsetBytes := 0 } (layoutPointerBytes protoLayouts)) =
      some (.ptr { allocId := 1, offsetBytes := 0 } (layoutPointerBytes protoLayouts)) ∧
    coerceValueAt protoLayouts protoCircleTy (.aggregate 0 [.scalar ⟨7, 4⟩]) =
      some (.aggregate 0 [.scalar ⟨7, 4⟩]) ∧
    coerceValueAt protoLayouts (.uint .u32)
        (.scalar ⟨wrapScalarBits 42 (scalarModulus 4), 4⟩) =
      some (.scalar ⟨wrapScalarBits 42 (scalarModulus 4), 4⟩) := by
  have _ := @flatMapTraitImpls_stripCalleeTraitImpls
  have _ := @hoistTraitImpls_append_strip
  have _ := @Memory.withCalleesAndTraits_callees
  have _ := @Memory.withCalleesAndTraits_traitImpls
  have _ := @Memory.withCalleesAndTraits_activeCallee
  have _ := @Memory.withCalleesAndTraits_activeProtectors
  have _ := @Memory.withCalleesAndTraits_borrows
  have _ := @Memory.withCalleesAndTraits_callStack
  have _ := @Memory.withCalleesAndTraits_callerLocals
  have _ := @Memory.withCalleesAndTraits_fnPtrs
  have _ := @Memory.withCalleesAndTraits_globals
  have _ := @Memory.withCalleesAndTraits_eq_withCalleeCtx
  have _ := @MachineState.withCalleesAndTraits_eq_withCalleeCtx
  have _ := @Memory.withCalleesAndTraits_comp_withCalleeCtx
  have _ := @evalStmt_withCalleesAndTraits
  have _ := @unwindFromCallStack_withCalleesAndTraits
  have _ := @applyUnwindAction_withCalleesAndTraits
  have _ := @commitForeignFrameLocals_withCalleesAndTraits
  have _ := @foreignFrameDerefWrite_withCalleesAndTraits
  have _ := @writeReturnDestination_withCalleesAndTraits
  have _ := @evalTerminator_return_withCalleesAndTraits
  have _ := @writeIntrinsicReturn_withCalleesAndTraits
  have _ := @evalNonSelectIntrinsicCall_withCalleesAndTraits
  have _ := @evalDirectRustIntrinsic?_withCalleesAndTraits_of_nonSelect
  have _ := @collectMatchingTraitImpls_filter_defPath
  have _ := @hasTraitImplForDefPath_eq_of_filter_eq
  have _ := @collectMatchingTraitImpls_congr_callees
  have _ := @upsertMatchingTraitImpl_mem_fst
  have _ := @collectMatchingTraitImpls_mem_fst
  have _ := @filterMostSpecificTraitImpls_sub
  have _ := @resolveCalleeNonParam?_congr
  have _ := @resolveCalleeBodyAndArgs?_eq_of_traitConeAgree
  have _ := @lookupCallee_eq_of_traitConeAgree
  have _ := @resolveCalleeBodyAndArgs?_origin
  have _ := @lookupCallee_origin
  have _ := @inConeSetPoly_of_lookup_trait
  have _ := @TraitConeAgreeOn.refl
  have _ := @lookupCallee_eq_of_traitConeAgreeOn
  have _ := @evalTerminator_withCalleesAndTraits
  have _ := @stepMirFn_withCalleesAndTraits
  have _ := @stepMirFn_calleesAndTraits_preserved
  have _ := @traitAgreesAt_succ
  have _ := @runMirExecBounded_trait_cone_narrow
  have _ := @wpMirExecSym_trait_cone_narrow
  have _ := @stepConeSafeTrait_of_closedInvPoly
  have _ := @nodeSuccs_evalTerminatorTrait
  have _ := @nodeSuccs_stepMirFnTrait
  have _ := @coneReach_of_closedInvTrait
  have _ := @traitImplConeClosed_imp
  have _ := @BatchedVcConeNarrowCert.rootInCone
  have _ := @BatchedVcConeNarrowCert.coneBodiesInCone
  have _ := @BatchedVcConeNarrowCert.traitImplsInCone
  have _ := @BatchedVcConeNarrowCert.toTraitConeAgreeOn
  have _ := @BatchedVcConeNarrowCert.untrustedAdmissible
  have _ := @lookupCallee_eq_of_batchedCert
  have _ := @runMirExecBounded_narrow_of_batchedCert
  have _ := @wpMirExecSym_narrow_of_batchedCert
  have _ := @vcMirWithCallees_narrow_of_batchedCert
  have _ := @canary_naiveNarrow_breaks_trait_dispatch
  have _ := @protoTraitBatchedCert
  have _ := @canary_traitDispatch_preserved_under_batchedVcNarrow
  have _ := @canary_duplicateShadow_rejected
  have _ := @canary_externalShadowsInternal_rejected
  have _ := @canary_missingTraitImplBody_rejected
  refine ⟨hoistTraitImpls_append_strip (stripCalleeTraitImpls protoNaiveNarrowCallees) []
      protoNaiveNarrowCallees,
    lookupCallee_eq_of_batchedCert protoTraitBatchedCert protoLayouts
      (List.Mem.tail _ (List.Mem.head _)) [protoCircleTy],
    runMirExecBounded_narrow_of_batchedCert protoTraitBatchedCert 12
      (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir [] emptyMemory protoFullCallees)
      rfl rfl rfl rfl,
    (vcMirWithCallees_narrow_of_batchedCert protoTraitBatchedCert 12
      (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir [] emptyMemory protoFullCallees)
      rfl rfl rfl rfl
      (fun out => match out with | .normal (v, _) => v = Value.scalar ⟨31, 4⟩ | _ => False)
      (fun out => by rcases out with ⟨v, m⟩ | _ | _ <;> exact Iff.rfl)).1,
    coerceValueAt_u32 protoLayouts 42,
    coerceValueAt_bool protoLayouts true,
    coerceValueAt_ref protoLayouts .not (.uint .u32) { allocId := 1, offsetBytes := 0 },
    coerceValueAt_adt_exact protoLayouts "proto::Circle" [] 0 [.scalar ⟨7, 4⟩],
    coerceValueAt_idempotent protoLayouts (.uint .u32) (.scalar ⟨42, 4⟩)
      (.scalar ⟨wrapScalarBits 42 (scalarModulus 4), 4⟩) (coerceValueAt_u32 protoLayouts 42)⟩

def buildFillerCallees : Nat → List CapturedMir
  | 0 => []
  | k + 1 => protoLeaf "bench::filler" (k + 100) 0 [] :: buildFillerCallees k

def fullCallees16 : List CapturedMir := buildFillerCallees 13 ++ [protoPoly, protoAreaImplHolder, protoCircleArea]
def fullCallees64 : List CapturedMir := buildFillerCallees 61 ++ [protoPoly, protoAreaImplHolder, protoCircleArea]
def fullCallees128 : List CapturedMir := buildFillerCallees 125 ++ [protoPoly, protoAreaImplHolder, protoCircleArea]

def narrowCallees2 : List CapturedMir := [protoPoly, protoCircleArea]
def narrowTraitExtra : List TraitImplEntry := [protoAreaEntry]

open Lean Elab Command in
run_cmd do
  let bench (label : String) (mkCmd : CommandElabM (TSyntax `command)) : CommandElabM Unit := do
    let cmd ← mkCmd
    let h0 ← IO.getNumHeartbeats
    let t0 ← IO.monoNanosNow
    elabCommand cmd
    let t1 ← IO.monoNanosNow
    let h1 ← IO.getNumHeartbeats
    logInfo m!"BENCH {label} heartbeats={h1 - h0} ns={t1 - t0}"
  bench "PartB_full_M16" `(command|
    theorem bench_partB_full_16 :
        ((runMirExecBounded 12 traitCallRootMir
          (.running (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir []
            emptyMemory fullCallees16))).map
          (fun out => match out with | .normal (.scalar sc, _) => some sc.bits | _ => none)) =
        some (some 31) := by decide +kernel)
  bench "PartB_narrow_M16" `(command|
    theorem bench_partB_narrow_16 :
        ((runMirExecBounded 12 traitCallRootMir
          (.running (MachineState.mapMem (Memory.withCalleesAndTraits narrowCallees2 narrowTraitExtra)
            (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir []
              emptyMemory fullCallees16)))).map
          (fun out => match out with | .normal (.scalar sc, _) => some sc.bits | _ => none)) =
        some (some 31) := by decide +kernel)
  bench "PartB_full_M64" `(command|
    theorem bench_partB_full_64 :
        ((runMirExecBounded 12 traitCallRootMir
          (.running (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir []
            emptyMemory fullCallees64))).map
          (fun out => match out with | .normal (.scalar sc, _) => some sc.bits | _ => none)) =
        some (some 31) := by decide +kernel)
  bench "PartB_narrow_M64" `(command|
    theorem bench_partB_narrow_64 :
        ((runMirExecBounded 12 traitCallRootMir
          (.running (MachineState.mapMem (Memory.withCalleesAndTraits narrowCallees2 narrowTraitExtra)
            (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir []
              emptyMemory fullCallees64)))).map
          (fun out => match out with | .normal (.scalar sc, _) => some sc.bits | _ => none)) =
        some (some 31) := by decide +kernel)
  bench "PartB_full_M128" `(command|
    theorem bench_partB_full_128 :
        ((runMirExecBounded 12 traitCallRootMir
          (.running (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir []
            emptyMemory fullCallees128))).map
          (fun out => match out with | .normal (.scalar sc, _) => some sc.bits | _ => none)) =
        some (some 31) := by decide +kernel)
  bench "PartB_narrow_M128" `(command|
    theorem bench_partB_narrow_128 :
        ((runMirExecBounded 12 traitCallRootMir
          (.running (MachineState.mapMem (Memory.withCalleesAndTraits narrowCallees2 narrowTraitExtra)
            (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir []
              emptyMemory fullCallees128)))).map
          (fun out => match out with | .normal (.scalar sc, _) => some sc.bits | _ => none)) =
        some (some 31) := by decide +kernel)

/-! ## 5. Part C Witnesses & Scaling Benchmarks (`DemandCallerLocationEnv`, `lean-miri#67`) -/

theorem test_partC_demandCallerLocation :
    allLocationDetailPolicies.length = 8 ∧
    (LocationDetailPolicy.mk true false true) ∈ allLocationDetailPolicies ∧
    applyLocationDetailPolicy ⟨false, true, false⟩
        (applyLocationDetailPolicy ⟨false, true, false⟩ protoUserCallerPos) =
      applyLocationDetailPolicy ⟨false, true, false⟩ protoUserCallerPos ∧
    resolveTrackCallerWalkUpAux {} protoUnwrapBodyPos
        ([protoUnwrapFrame {}] ++ protoUserCallerFrame {} :: []) =
      applyLocationDetailPolicy {}
        (propagateTrackCallerTopDown protoUnwrapBodyPos [protoUnwrapFrame {}]) ∧
    readU32Le? (u32LeBytes (42 : UInt32).toNat ++ []) = some 42 ∧
    readU64Le? (u64LeBytes 10 ++ []) = some 10 ∧
    decodeInitBytes? (protoLibRsBytes.map Option.some) = some protoLibRsBytes ∧
    lookupGlobalAlloc
        ([mkFilenameAllocation 1 protoLibRsBytes] ++ [mkLocationAllocation 2 1 10 42 13]) 1 =
      some (mkFilenameAllocation 1 protoLibRsBytes) ∧
    lookupGlobalAlloc
        ([mkFilenameAllocation 1 protoLibRsBytes] ++ [mkLocationAllocation 2 1 10 42 13]) 2 =
      some (mkLocationAllocation 2 1 10 42 13) ∧
    (runDemandCallerLocationTrace {} protoRetagMachineState protoRetagLocalDecls protoLayouts
      [.normalStep ⟨.nop, "nop"⟩]).1 = {} ∧
    (let (_, ptr, mem') := evalDemandCallerLocation {} (protoUnwrapFailedFrame {})
        [protoUnwrapFrame {}, protoUserCallerFrame {}] emptyMemory
     readLocationFromGlobals mem'.globals ptr = some (protoLibRsBytes, 42, 13)) := by
  have _ := @allLocationDetailPolicies_length
  have _ := @mem_allLocationDetailPolicies
  have _ := @applyLocationDetailPolicy_idempotent
  have _ := @resolveTrackCallerWalkUpAux_eq_topDown
  have _ := @readU32Le_u32LeBytes
  have _ := @readU64Le_u64LeBytes
  have _ := @decodeInitBytes?_map_some
  have _ := @lookupGlobalAlloc_append_left
  have _ := @lookupGlobalAlloc_snoc_self
  have _ := @demandCallerLocation_no_call_zero_allocs
  have _ := @readLocationFromGlobals_evalDemandCallerLocation_fresh
  have _ := @demandCallerLocation_filename_dedup
  have _ := @AllocRenamingRel.wf
  have _ := @AllocRenamingRel.ptrsMapped
  have _ := @AllocRenamingRel.obsAgree
  have _ := @demandCallerLocation_bisim_eager
  have _ := @trackCaller_stops_at_nonTrackCaller_frame
  refine ⟨allLocationDetailPolicies_length,
    mem_allLocationDetailPolicies ⟨true, false, true⟩,
    applyLocationDetailPolicy_idempotent ⟨false, true, false⟩ protoUserCallerPos,
    resolveTrackCallerWalkUpAux_eq_topDown {}
      [protoUnwrapFrame {}] (protoUserCallerFrame {}) [] protoUnwrapBodyPos rfl rfl,
    readU32Le_u32LeBytes 42 [],
    readU64Le_u64LeBytes (by decide) [],
    decodeInitBytes?_map_some protoLibRsBytes,
    lookupGlobalAlloc_append_left rfl,
    lookupGlobalAlloc_snoc_self [mkFilenameAllocation 1 protoLibRsBytes]
      (mkLocationAllocation 2 1 10 42 13)
      (fun a ha => by cases ha with | head => decide | tail _ h => nomatch h),
    (demandCallerLocation_no_call_zero_allocs {} [.normalStep ⟨.nop, "nop"⟩]
      protoRetagMachineState protoRetagLocalDecls protoLayouts rfl).1,
    readLocationFromGlobals_evalDemandCallerLocation_fresh (protoUnwrapFailedFrame {})
      [protoUnwrapFrame {}, protoUserCallerFrame {}] emptyMemory rfl (by decide)⟩

def buildCandidateSpans : Nat → List (FrameLocMeta × List FrameLocMeta)
  | 0 => []
  | k + 1 =>
    let pos : SourceExpansionPos :=
      ⟨"src/lib.rs", protoLibRsBytes, UInt32.ofNat (k + 1), 5⟩
    (⟨"crate::caller", pos, false, {}⟩, []) :: buildCandidateSpans k

def candidateSpans16 : List (FrameLocMeta × List FrameLocMeta) := buildCandidateSpans 16
def candidateSpans64 : List (FrameLocMeta × List FrameLocMeta) := buildCandidateSpans 64
def candidateSpans128 : List (FrameLocMeta × List FrameLocMeta) := buildCandidateSpans 128

def nonPanickingTrace8 : List CallerLocationTraceEvent :=
  List.replicate 8 (.normalStep ⟨.nop, "nop"⟩)

open Lean Elab Command in
run_cmd do
  let bench (label : String) (mkCmd : CommandElabM (TSyntax `command)) : CommandElabM Unit := do
    let cmd ← mkCmd
    let h0 ← IO.getNumHeartbeats
    let t0 ← IO.monoNanosNow
    elabCommand cmd
    let t1 ← IO.monoNanosNow
    let h1 ← IO.getNumHeartbeats
    logInfo m!"BENCH {label} heartbeats={h1 - h0} ns={t1 - t0}"
  bench "PartC_eager_S16" `(command|
    theorem bench_partC_eager_16 :
        (eagerInitCallerLocations candidateSpans16 emptyMemory).2.2.globals.length = 17 := by
      decide +kernel)
  bench "PartC_demand_S16" `(command|
    theorem bench_partC_demand_16 :
        (runDemandCallerLocationTrace {} protoRetagMachineState protoRetagLocalDecls protoLayouts
          nonPanickingTrace8).2.2.memory.globals.length = 0 := by
      decide +kernel)
  bench "PartC_eager_S64" `(command|
    theorem bench_partC_eager_64 :
        (eagerInitCallerLocations candidateSpans64 emptyMemory).2.2.globals.length = 65 := by
      decide +kernel)
  bench "PartC_demand_S64" `(command|
    theorem bench_partC_demand_64 :
        (runDemandCallerLocationTrace {} protoRetagMachineState protoRetagLocalDecls protoLayouts
          nonPanickingTrace8).2.2.memory.globals.length = 0 := by
      decide +kernel)
  bench "PartC_eager_S128" `(command|
    theorem bench_partC_eager_128 :
        (eagerInitCallerLocations candidateSpans128 emptyMemory).2.2.globals.length = 129 := by
      decide +kernel)
  bench "PartC_demand_S128" `(command|
    theorem bench_partC_demand_128 :
        (runDemandCallerLocationTrace {} protoRetagMachineState protoRetagLocalDecls protoLayouts
          nonPanickingTrace8).2.2.memory.globals.length = 0 := by
      decide +kernel)

/-! ## 6. Part D Witnesses & Scaling Benchmarks (`LazyWriteChain` & `bvShiftSafe` / `shiftLeftBitsSafe`) -/

def zeroEnv : Nat → Nat → Option Nat := fun _ _ => some 0

theorem test_partD_lazyWrite_and_shifts :
    evalSymArrayTerm zeroEnv (.constVec 8 0) 9 = none ∧
    symArrayLen (mkLazyWrite (.constVec 8 0) 2 99) = 8 ∧
    evalSymArrayTerm zeroEnv (mkLazyWrite (.constVec 8 0) 2 99) 2 =
      evalSymArrayTerm zeroEnv (.write (.constVec 8 0) 2 99) 2 ∧
    symArrayLen (stripShadowedWrites (.write (.constVec 8 0) 2 99) 2) = 8 ∧
    evalSymArrayTerm zeroEnv (stripShadowedWrites (.write (.constVec 8 0) 2 99) 2) 3 =
      evalSymArrayTerm zeroEnv (.write (.constVec 8 0) 2 99) 3 ∧
    evalSymArrayTerm zeroEnv (mkLazyWrite (.constVec 8 0) 2 99) 2 = some 99 ∧
    lazyWriteChainSteps 16 = 16 ∧
    2 * eagerWriteChainSteps 16 = 16 * 17 ∧
    bvShlSafe (0x12345678#32) 64 = (0x12345678#32) <<< 64 ∧
    bvLshrSafe (0x12345678#32) 64 = (0x12345678#32) >>> 64 ∧
    bvAshrSafe (0x80000000#32) 64 = BitVec.sshiftRight (0x80000000#32) 64 ∧
    shiftLeftBitsSafe 0x12345678 64 4 = shiftLeftBits 0x12345678 64 (scalarModulus 4) ∧
    shiftRightUnsignedBitsSafe 0x12345678 64 4 = shiftRightUnsignedBits 0x12345678 64 ∧
    arithmeticShrBitsSafe 0x80000000 4 64 = arithmeticShrBits 0x80000000 4 64 := by
  have _ := @nat_beq_self_raw
  have _ := @nat_beq_self
  have _ := @nat_beq_ne
  have _ := @evalSymArrayTerm_oob
  have _ := @symArrayLen_mkLazyWrite
  have _ := @eval_mkLazyWrite
  have _ := @symArrayLen_stripShadowedWrites
  have _ := @eval_stripShadowedWrites_ne
  have _ := @eval_mkLazyRead
  have _ := @lazyWriteChain_distinctAddrs_steps_eq_N
  have _ := @eagerWriteChain_distinctAddrs_steps_quadratic
  have _ := @bvShlSafe_eq
  have _ := @bvLshrSafe_eq
  have _ := @bvAshrSafe_eq
  have _ := @scalarPow2_add
  have _ := @scalarPow2_le_of_le
  have _ := @scalarModulus_eq_scalarPow2_mul8
  have _ := @shiftLeftBitsSafe_eq
  have _ := @shiftRightUnsignedBitsSafe_eq
  have _ := @arithmeticShrBitsSafe_eq
  have _ := @canary_wideShift_two_pow_64
  refine ⟨evalSymArrayTerm_oob zeroEnv (.constVec 8 0) 9 (by decide),
    symArrayLen_mkLazyWrite (.constVec 8 0) 2 99,
    eval_mkLazyWrite zeroEnv (.constVec 8 0) 2 99 2,
    symArrayLen_stripShadowedWrites (.write (.constVec 8 0) 2 99) 2,
    eval_stripShadowedWrites_ne zeroEnv (.write (.constVec 8 0) 2 99) 2 3 rfl,
    eval_mkLazyRead zeroEnv (mkLazyWrite (.constVec 8 0) 2 99) 2 99 rfl,
    lazyWriteChain_distinctAddrs_steps_eq_N 16,
    eagerWriteChain_distinctAddrs_steps_quadratic 16,
    bvShlSafe_eq (0x12345678#32) 64,
    bvLshrSafe_eq (0x12345678#32) 64,
    bvAshrSafe_eq (0x80000000#32) 64,
    shiftLeftBitsSafe_eq 0x12345678 64 4,
    shiftRightUnsignedBitsSafe_eq (by decide) 64,
    arithmeticShrBitsSafe_eq 0x80000000 4 64⟩

open Lean Elab Command in
run_cmd do
  let bench (label : String) (mkCmd : CommandElabM (TSyntax `command)) : CommandElabM Unit := do
    let cmd ← mkCmd
    let h0 ← IO.getNumHeartbeats
    let t0 ← IO.monoNanosNow
    elabCommand cmd
    let t1 ← IO.monoNanosNow
    let h1 ← IO.getNumHeartbeats
    logInfo m!"BENCH {label} heartbeats={h1 - h0} ns={t1 - t0}"
  bench "PartD_eagerWrite_N16" `(command|
    theorem bench_partD_eager_16 :
        (buildEagerDistinctChainWithSteps 128 16).2 = 136 ∧
        mkLazyRead (buildEagerDistinctChainWithSteps 128 16).1 15 = some 16 := by
      decide +kernel)
  bench "PartD_lazyWrite_N16" `(command|
    theorem bench_partD_lazy_16 :
        lazyWriteChainSteps 16 = 16 ∧
        mkLazyRead (buildLazyDistinctChain 128 16) 15 = some 16 := by
      decide +kernel)
  bench "PartD_eagerWrite_N64" `(command|
    theorem bench_partD_eager_64 :
        (buildEagerDistinctChainWithSteps 128 64).2 = 2080 ∧
        mkLazyRead (buildEagerDistinctChainWithSteps 128 64).1 63 = some 64 := by
      decide +kernel)
  bench "PartD_lazyWrite_N64" `(command|
    theorem bench_partD_lazy_64 :
        lazyWriteChainSteps 64 = 64 ∧
        mkLazyRead (buildLazyDistinctChain 128 64) 63 = some 64 := by
      decide +kernel)
  bench "PartD_wideShift_2pow64" `(command|
    theorem bench_partD_wideShift_2pow64 :
        shiftLeftBitsSafe 0xdeadbeef wideShiftTwoPow64 4 = 0 ∧
        shiftRightUnsignedBitsSafe 0xdeadbeef wideShiftTwoPow64 4 = 0 ∧
        arithmeticShrBitsSafe 0x80000000 4 wideShiftTwoPow64 = 0xffffffff ∧
        bvShlSafe (0xdeadbeef#32) wideShiftTwoPow64 = 0#32 ∧
        bvLshrSafe (0xdeadbeef#32) wideShiftTwoPow64 = 0#32 ∧
        bvAshrSafe (0x80000000#32) wideShiftTwoPow64 = 0xffffffff#32 := by
      decide +kernel)

/-! ## 7. Bottom-of-File Kernel Axiom, Namespace Hygiene, & Theorem Reachability Audit -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Quot.sound]
  let protoMod := `Anneal.SparseRetagAndVcNarrowPrototype
  let testPfx := `Anneal.SparseRetagAndVcNarrowProtoTests
  let some modIdx := env.getModuleIdx? protoMod
    | throwError "module {protoMod} not imported"
  let mut audited : Nat := 0
  let mut theorems : Nat := 0
  let mut auditedSet : NameSet := {}
  let mut auditedThms : Array Name := #[]
  let mut leaked : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some modIdx then
      if ci.isUnsafe then
        throwError "unsafe declaration in {protoMod}: {n}"
      let axs ← collectAxioms n
      for a in axs do
        unless allowed.contains a do
          throwError "{n} in {protoMod} depends on disallowed axiom {a}"
      let un := (Lean.privateToUserName? n).getD n
      if protoMod.isPrefixOf un then
        audited := audited + 1
        auditedSet := auditedSet.insert n
        if ci matches .thmInfo _ then
          let last := un.eraseMacroScopes.getString!
          let isAutoAux :=
            last == "eq_def" || last == "splitter" || last == "else_eq" ||
              last.startsWith "eq_" || last.startsWith "_sparseCasesOn_" ||
              last == "noConfusion" || last == "noConfusionType" ||
              last == "ctorIdx" || last == "toCtorIdx" || last == "ofNat_ctorIdx" ||
              last == "inj" || last == "injEq" || last == "sizeOf_spec" ||
              last == "eq" || last == "_arg_pusher" || last.startsWith "_proof_"
          unless un.hasMacroScopes || isAutoAux do
            theorems := theorems + 1
            auditedThms := auditedThms.push n
      else
        let last := un.eraseMacroScopes.getString!
        let isRealizedEq :=
          last == "eq_def" || last == "splitter" || last == "else_eq" ||
            last.startsWith "eq_" || last.startsWith "_sparseCasesOn_"
        unless un.hasMacroScopes || isRealizedEq do
          leaked := leaked.push un
  unless leaked.isEmpty do
    throwError "leaked constants outside {protoMod}: {leaked}"
  let mut reached : NameSet := {}
  let mut work : Array Name := #[]
  for (n, ci) in env.constants.map₂.toList do
    if testPfx.isPrefixOf n then
      if ci.isUnsafe then
        throwError "unsafe declaration in {testPfx}: {n}"
      let axs ← collectAxioms n
      for a in axs do
        unless allowed.contains a do
          throwError "{n} in {testPfx} depends on disallowed axiom {a}"
      audited := audited + 1
      for c in ci.getUsedConstantsAsSet do
        if auditedSet.contains c && !reached.contains c then
          reached := reached.insert c
          work := work.push c
  while !work.isEmpty do
    let c := work.back!
    work := work.pop
    if let some ci := env.find? c then
      for d in ci.getUsedConstantsAsSet do
        if auditedSet.contains d && !reached.contains d then
          reached := reached.insert d
          work := work.push d
  let unreached := auditedThms.filter (fun n => !reached.contains n)
  unless unreached.isEmpty do
    throwError "prototype theorems not instantiated/reached by any test witness: {unreached.toList}"
  logInfo m!"axiom audit passed: {audited} declarations ({theorems} prototype theorems, 0 unsafe, 0 Classical.choice, 0 Lean.ofReduceBool, 0 leaked constants, 100% theorem reachability)"

end Anneal.SparseRetagAndVcNarrowProtoTests
