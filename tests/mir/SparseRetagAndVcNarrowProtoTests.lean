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
2. Instantiates positive and negative canaries across all 4 subsystems with concrete arguments
   (no `have _ := @thm` placeholders: the bottom-of-file audit rejects any test proof that binds a
   prototype theorem without using it).
3. Measures kernel `IO.getNumHeartbeats` / wall-clock scaling with ONE evaluation mechanism
   (`decide +kernel`) for both arms of every comparison, including one-time preparation /
   certificate costs in the optimized arm.
4. Runs a self-enforcing bottom-of-file `run_cmd` audit verifying `0` `unsafe`, `0`
   `Classical.choice`, `0` `Lean.ofReduceBool`, `0` `sorryAx`, `0` leaked constants
   (`leaked.isEmpty`), `0` placeholder-only theorem uses, and `100%` theorem reachability
   (`unreached.isEmpty`).
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

/-- The prepared index of `sampleRetagRows` (extracted from the `Except`). -/
def sampleIdx : SparseRetagAttrIndex :=
  match prepareSparseRetagIndex 10 sampleRetagRows with
  | .ok idx => idx
  | .error _ => ⟨.empty, 0⟩

theorem sampleIdx_prepared : prepareSparseRetagIndex 10 sampleRetagRows = .ok sampleIdx := rfl

/-- Positive and negative canaries for `SparseRetagAttrIndex`, exercising every `RetagAttrErr`
variant, `lookupSparseRetag_eq_linearScan`, `frameAbsent_precedes_malformedTable`, the hit/miss
certificates on the *actual* prepared index, and `SparseDefPathRetagIndex`. -/
theorem test_partA_sparseRetag_canaries :
    trieLookupBits (.empty : BitTrie Bool) [true, false] 1 = none ∧
    trieLookupBits (trieInsertBits (.empty : BitTrie Bool) [true] 1 true) [true] 1 = some true ∧
    trieLookupBits (trieInsertBits (.empty : BitTrie Bool) [true] 1 true) [false] 0 = none ∧
    (natLowBits 4 5).length = 4 ∧
    (NatBitTrie.empty : NatBitTrie Bool).get? 3 = none ∧
    ((NatBitTrie.empty : NatBitTrie Bool).insert 3 true).get? 3 = some true ∧
    SparseRetagAttrIndex.get? ⟨.empty, 0⟩ 0 = none ∧
    evalPreparedRetagLookup (prepareSparseRetagLoop 10 .empty 0 sampleRetagRows) 3 =
      linearScanLoop 10 3 [] ((NatBitTrie.empty : NatBitTrie Bool).get? 3) sampleRetagRows ∧
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
  refine ⟨trieLookupBits_empty [true, false] 1,
    by rw [trieLookupBits_insert_same]; rfl,
    by rw [trieLookupBits_insert_diff [true] [false] .empty 1 true 0 rfl (by decide)]; rfl,
    natLowBits_length 4 5,
    NatBitTrie.get?_empty 3,
    by rw [NatBitTrie.get?_insert]; rfl,
    by rw [SparseRetagAttrIndex.get?_eq]; rfl,
    prepareSparseRetagLoop_lookup_eq 10 3 sampleRetagRows [] .empty 0 (fun _ => rfl),
    lookupSparseRetag_eq_linearScan 10 sampleRetagRows 3,
    by rw [sampleIdx_prepared]; exact lookupSparseRetag_cert (by decide) rfl,
    by rw [sampleIdx_prepared]; exact lookupSparseRetag_miss_cert (by decide) rfl,
    by rw [lookupSparseRetag_eq_linearScan]; rfl,
    by rw [lookupSparseRetag_eq_linearScan]; rfl,
    frameAbsent_precedes_malformedTable (Nat.le_refl 10) .duplicateDefQuery,
    SparseDefPathRetagIndex.get?_empty "x",
    by rw [SparseDefPathRetagIndex.get?_insert]; rfl⟩

/-- Largest leaf bucket of a `BitTrie` (measurement helper). -/
def bitTrieMaxBucket {α : Type} : BitTrie α → Nat
  | .empty => 0
  | .leaf bucket => bucket.length
  | .branch l r => max (bitTrieMaxBucket l) (bitTrieMaxBucket r)

/-- A `definitionCount = 5000 > 4096` table whose keys `7` and `4103 = 7 + 4096` share their low
12 bits. -/
def bigRetagRows : List RetagQueryRow := [⟨7, "crate::a", true⟩, ⟨4103, "crate::b", false⟩]

def preparedMaxBucket (prepared : Except RetagAttrErr SparseRetagAttrIndex) : Nat :=
  match prepared with
  | .ok idx => bitTrieMaxBucket idx.trie.root
  | .error _ => 0

/-- Adaptive trie depth, exercised where it matters: at the fixed 12-bit depth keys `7` and
`4103` share a path and a 2-entry leaf bucket; at `adaptiveRetagTrieDepth 5000` their paths differ
(by `adaptiveRetagTrieDepth_bitPath_injective`) and every leaf of the prepared index holds one key. -/
theorem test_partA_adaptive_depth :
    natLowBits 12 7 = natLowBits 12 4103 ∧
    natLowBits (adaptiveRetagTrieDepth 5000) 7 ≠ natLowBits (adaptiveRetagTrieDepth 5000) 4103 ∧
    preparedMaxBucket (prepareSparseRetagLoop 5000 (NatBitTrie.empty 12) 0 bigRetagRows) = 2 ∧
    preparedMaxBucket (prepareSparseRetagIndex 5000 bigRetagRows) = 1 ∧
    lookupSparseRetag 5000 (prepareSparseRetagIndex 5000 bigRetagRows) 4103 = .ok false ∧
    lookupSparseRetag 5000 (prepareSparseRetagIndex 5000 bigRetagRows) 7 = .ok true :=
  ⟨by decide,
    fun h => absurd (adaptiveRetagTrieDepth_bitPath_injective (by decide) (by decide) h) (by decide),
    by decide +kernel,
    by decide +kernel,
    by rw [lookupSparseRetag_eq_linearScan]; rfl,
    by rw [lookupSparseRetag_eq_linearScan]; rfl⟩

/-- Concrete MIR state with a mutable reference `_1 : &mut u32` borrowed from `_2 : u32`
(`tag = 1`). -/
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

/-- Zero-sized `_1 : &mut ()` (non-null dangling scalar) with an unrelated live borrow entry at
the head of `borrows`: its fn-entry retag creates no child tag in `Trusted` semantics. -/
def protoZstRefTy : Ty := { kind := .ref .mut (.tuple []), layoutIdx := 0 }

def protoZstLocalDecls : List LocalDecl :=
  [ ⟨.mut, protoU32Ty, some "_0"⟩, ⟨.mut, protoZstRefTy, some "_1"⟩ ]

def protoZstMachineState : MachineState :=
  { frame :=
      { locals := [ .init (.scalar ⟨0, 4⟩), .init (.scalar ⟨1, 8⟩) ]
        blockIdx := 0
        stmtIdx := 0 }
    memory :=
      { emptyMemory with
        borrows := [{ tag := 1, targetLocal := 0, targetProjection := [], perm := .reservedFrz false }]
        nextTag := 2
        nextProtector := 1 } }

/-- `some true` iff the head borrow entry of the successor state is `.unique`. -/
def headPermIsUnique (node : MirStepNode) : Option Bool :=
  match node with
  | .tau (.running s') =>
    match s'.memory.borrows with
    | head :: _ => some (match head.perm with | .unique => true | _ => false)
    | [] => none
  | _ => none

/-- The `[adv A0]` overlay (kept verbatim here only as a regression witness): it rewrote the
head borrow entry whatever it was. -/
def applyImplicitWriteUpgradeLegacyA0 (node : MirStepNode) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (place : Place) (implicitWrites rustcNoWritable : Bool) :
    MirStepNode :=
  match implicitWrites && !rustcNoWritable with
  | false => node
  | true =>
    match placeTy localDecls layouts place with
    | some { kind := .ref .mut _, .. } =>
      match node with
      | .tau (.running s') =>
        match s'.memory.borrows with
        | head :: tail =>
          MirStepNode.step
            { s' with memory := { s'.memory with borrows := { head with perm := .unique } :: tail } }
        | [] => node
      | _ => node
    | _ => node

/-- Successor state of the ZST fn-entry retag. -/
def protoZstAfter : MachineState :=
  match evalStmt protoZstMachineState protoFnEntryRetagStmt protoZstLocalDecls protoLayouts with
  | .tau (.running s') => s'
  | _ => protoZstMachineState

theorem protoZst_step :
    evalStmt protoZstMachineState protoFnEntryRetagStmt protoZstLocalDecls protoLayouts =
      .tau (.running protoZstAfter) := rfl

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
      evalStmt protoRetagMachineState protoFnEntryRetagStmt protoRetagLocalDecls protoLayouts ∧
    headPermIsUnique (evalFnEntryRetagWithSparseAttr 10 (prepareSparseRetagIndex 10 sampleRetagRows)
      true 7 protoRetagMachineState protoFnEntryRetagStmt protoRetagLocalDecls protoLayouts) = some true ∧
    headPermIsUnique (evalFnEntryRetagWithSparseAttr 10 (prepareSparseRetagIndex 10 sampleRetagRows)
      true 3 protoRetagMachineState protoFnEntryRetagStmt protoRetagLocalDecls protoLayouts) = some false ∧
    evalFnEntryRetagWithSparseAttr 10 (prepareSparseRetagIndex 10 sampleRetagRows) true 7
        protoZstMachineState protoFnEntryRetagStmt protoZstLocalDecls protoLayouts =
      evalStmt protoZstMachineState protoFnEntryRetagStmt protoZstLocalDecls protoLayouts ∧
    headPermIsUnique (evalStmt protoZstMachineState protoFnEntryRetagStmt protoZstLocalDecls
      protoLayouts) = some false ∧
    headPermIsUnique (applyImplicitWriteUpgradeLegacyA0
      (evalStmt protoZstMachineState protoFnEntryRetagStmt protoZstLocalDecls protoLayouts)
      protoZstLocalDecls protoLayouts ⟨1, []⟩ true false) = some true ∧
    fnEntryRetagPerm .mut protoCircleTy = .reservedFrz false ∧
    (match applyImplicitWriteUpgrade 2
        (.tau (.running { protoZstMachineState with
          memory := { emptyMemory with
            borrows :=
              [ { tag := 2, targetLocal := 0, targetProjection := [], perm := .reservedFrz false,
                  parentTag := some 1, rangeLen := 4 },
                { tag := 1, targetLocal := 0, targetProjection := [], perm := .frozen, rangeLen := 4 } ],
            nextTag := 3 } }))
        [⟨.mut, { kind := .uint .u32, layoutIdx := 0 }, some "_0"⟩,
         ⟨.mut, { kind := .ref .mut (.uint .u32), layoutIdx := 0 }, some "_1"⟩]
        { pointerBits := 64, isLittleEndian := true, entries := [] } ⟨1, []⟩ true false with
      | .vis (.inl (.fail .ub)) _ => true
      | _ => false) = true := by
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
      (by rw [sampleIdx_prepared]; exact lookupSparseRetag_cert (by decide) rfl),
    by decide +kernel, by decide +kernel, ?_, by decide +kernel, by decide +kernel,
    fnEntryRetagPerm_mut protoCircleTy,
    canary_implicitWrite_treeBorrows_full.2.1⟩
  have hq : lookupSparseRetag 10 (prepareSparseRetagIndex 10 sampleRetagRows) 7 = .ok false := by
    rw [sampleIdx_prepared]
    exact lookupSparseRetag_cert (by decide) rfl
  unfold evalFnEntryRetagWithSparseAttr evalStmtWithRetagAttrOracle
  show (match lookupSparseRetag 10 (prepareSparseRetagIndex 10 sampleRetagRows) 7 with
      | .error _ => MirStepNode.unsupported
      | .ok noWritable =>
        applyImplicitWriteUpgrade protoZstMachineState.memory.nextTag
          (evalStmt protoZstMachineState protoFnEntryRetagStmt protoZstLocalDecls protoLayouts)
          protoZstLocalDecls protoLayouts ⟨1, []⟩ true noWritable) = _
  rw [hq]
  show applyImplicitWriteUpgrade protoZstMachineState.memory.nextTag
      (evalStmt protoZstMachineState protoFnEntryRetagStmt protoZstLocalDecls protoLayouts)
      protoZstLocalDecls protoLayouts ⟨1, []⟩ true false = _
  rw [protoZst_step]
  exact applyImplicitWriteUpgrade_of_no_fresh_child _ protoZstAfter _ _ _ _ _ rfl

/-! ## 3. Part A Heartbeat Scaling (`M ∈ {16, 64, 128, 256}`)

Both arms are evaluated by `decide +kernel`. The sparse arm *includes* the one-time
`prepareSparseRetagIndex` table preparation (`M` trie insertions with `O(log D)` duplicate
checks); the linear arm is the reference oracle, which re-validates the whole table (with its
list-based duplicate scan) on every query, exactly like `lean-miri`'s pre-#68 `rustcNoWritable`. -/

def buildRetagRows : Nat → List RetagQueryRow
  | 0 => []
  | k + 1 => ⟨k, "crate::retag_fn", k % 2 == 0⟩ :: buildRetagRows k

def retagResOkEq (r : Except RetagAttrErr Bool) (expected : Bool) : Bool :=
  match r with
  | .ok b => b == expected
  | .error _ => false

/-- `q` linear-oracle queries for ids `0 ..< q`. -/
def runLinearRetagBench (definitionCount : Nat) (rows : List RetagQueryRow) : Nat → Bool
  | 0 => true
  | q + 1 =>
    retagResOkEq (linearScanRetagAttr definitionCount rows q) (q % 2 == 0) &&
      runLinearRetagBench definitionCount rows q

/-- `q` sparse queries for ids `0 ..< q` against one prepared index. -/
def runSparseQueries (definitionCount : Nat) (prepared : Except RetagAttrErr SparseRetagAttrIndex) :
    Nat → Bool
  | 0 => true
  | q + 1 =>
    retagResOkEq (lookupSparseRetag definitionCount prepared q) (q % 2 == 0) &&
      runSparseQueries definitionCount prepared q

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
  bench "PartA_linear_q1_M16" `(command|
    theorem bench_partA_linear_q1_16 :
        runLinearRetagBench 512 (buildRetagRows 16) 1 = true := by decide +kernel)
  bench "PartA_sparse_prep_q1_M16" `(command|
    theorem bench_partA_sparse_q1_16 :
        runSparseQueries 512 (prepareSparseRetagIndex 512 (buildRetagRows 16)) 1 = true := by
      decide +kernel)
  bench "PartA_sparse_prep_qM_M16" `(command|
    theorem bench_partA_sparse_qM_16 :
        runSparseQueries 512 (prepareSparseRetagIndex 512 (buildRetagRows 16)) 16 = true := by
      decide +kernel)
  bench "PartA_linear_q1_M64" `(command|
    theorem bench_partA_linear_q1_64 :
        runLinearRetagBench 512 (buildRetagRows 64) 1 = true := by decide +kernel)
  bench "PartA_sparse_prep_q1_M64" `(command|
    theorem bench_partA_sparse_q1_64 :
        runSparseQueries 512 (prepareSparseRetagIndex 512 (buildRetagRows 64)) 1 = true := by
      decide +kernel)
  bench "PartA_sparse_prep_qM_M64" `(command|
    theorem bench_partA_sparse_qM_64 :
        runSparseQueries 512 (prepareSparseRetagIndex 512 (buildRetagRows 64)) 64 = true := by
      decide +kernel)
  bench "PartA_linear_q1_M128" `(command|
    theorem bench_partA_linear_q1_128 :
        runLinearRetagBench 512 (buildRetagRows 128) 1 = true := by decide +kernel)
  bench "PartA_sparse_prep_q1_M128" `(command|
    theorem bench_partA_sparse_q1_128 :
        runSparseQueries 512 (prepareSparseRetagIndex 512 (buildRetagRows 128)) 1 = true := by
      decide +kernel)
  bench "PartA_sparse_prep_qM_M128" `(command|
    theorem bench_partA_sparse_qM_128 :
        runSparseQueries 512 (prepareSparseRetagIndex 512 (buildRetagRows 128)) 128 = true := by
      decide +kernel)
  bench "PartA_linear_q1_M256" `(command|
    theorem bench_partA_linear_q1_256 :
        runLinearRetagBench 512 (buildRetagRows 256) 1 = true := by decide +kernel)
  bench "PartA_sparse_prep_q1_M256" `(command|
    theorem bench_partA_sparse_q1_256 :
        runSparseQueries 512 (prepareSparseRetagIndex 512 (buildRetagRows 256)) 1 = true := by
      decide +kernel)
  bench "PartA_sparse_prep_qM_M256" `(command|
    theorem bench_partA_sparse_qM_256 :
        runSparseQueries 512 (prepareSparseRetagIndex 512 (buildRetagRows 256)) 256 = true := by
      decide +kernel)

/-! ## 4. Part B Witnesses, Canaries, & Scaling (`BatchedVcConeNarrowCert` + `coerceValueAt`) -/

/-- The `[adv A0]` callee-agreement "check" (metadata only: `defPath`, `argCount`,
`typeParamCount`, block count), kept here as a regression witness: it ACCEPTS the same-shape
shadowing narrowing that `checkMaskKeepsFirstMatch` rejects, although the exposed body differs. -/
def checkCalleesAgreeOnLegacyA0 (cone : List DefPath) (c₁ c₂ : List CapturedMir) : Bool :=
  cone.all (fun dp =>
    match findCallee? c₁ dp, findCallee? c₂ dp with
    | none, none => true
    | some b₁, some b₂ =>
      stringEq b₁.defPath b₂.defPath &&
        decide (b₁.argCount = b₂.argCount) &&
        decide (b₁.typeParamCount = b₂.typeParamCount) &&
        decide (b₁.basicBlocks.length = b₂.basicBlocks.length)
    | _, _ => false)

/-- Leaf result extractor. -/
def leafBits (out : MirOutcome) : Option Nat :=
  match out with
  | .normal (.scalar sc, _) => some sc.bits
  | _ => none

theorem test_partB_batchedVcNarrow_and_coerceValueAt :
    hoistTraitImpls (stripCalleeTraitImpls protoNaiveNarrowCallees) [] ++
        flatMapTraitImpls (stripCalleeTraitImpls protoNaiveNarrowCallees) =
      [] ++ flatMapTraitImpls (stripCalleeTraitImpls protoNaiveNarrowCallees) ∧
    (Memory.withCalleesAndTraits protoNaiveNarrowCallees protoHoistedExtra emptyMemory).callees =
      protoNaiveNarrowCallees ∧
    (Memory.withCalleesAndTraits protoNaiveNarrowCallees protoHoistedExtra emptyMemory).traitImpls =
      protoHoistedExtra ∧
    lookupCallee protoFullCallees protoLayouts "proto::Area::area" [protoCircleTy] [] =
      lookupCallee protoNaiveNarrowCallees protoLayouts "proto::Area::area" [protoCircleTy]
        protoHoistedExtra ∧
    runMirExecBounded 12 traitCallRootMir
        (.running (MachineState.mapMem
          (Memory.withCalleesAndTraits protoNaiveNarrowCallees protoHoistedExtra)
          protoTraitInitState)) =
      (runMirExecBounded 12 traitCallRootMir (.running protoTraitInitState)).map
        (MirOutcome.mapMem (Memory.withCalleesAndTraits protoNaiveNarrowCallees protoHoistedExtra)) ∧
    (vcMirWithCallees (fun _ _ _ => True) 12 traitCallRootMir protoTraitInitState
        protoNaiveNarrowCallees protoHoistedExtra [] protoTraitCone
        (fun out => match out with | .normal (v, _) => v = Value.scalar ⟨31, 4⟩ | _ => False) ↔
      vcMirWithCallees (fun _ _ _ => True) 12 traitCallRootMir protoTraitInitState
        protoFullCallees [] [] protoTraitCone
        (fun out => match out with | .normal (v, _) => v = Value.scalar ⟨31, 4⟩ | _ => False)) ∧
    (wpMirExecExt (fun _ _ _ => True) protoTraitCone [] 12 traitCallRootMir
        (.running protoTraitInitState)
        (fun out => match out with | .normal (v, _) => v = Value.scalar ⟨31, 4⟩ | _ => False) ↔
      wpMirExecSym 12 traitCallRootMir (.running protoTraitInitState)
        (fun out => match out with | .normal (v, _) => v = Value.scalar ⟨31, 4⟩ | _ => False)) ∧
    checkCalleesAgreeOnLegacyA0 protoTraitCone protoShadowFullCallees
      (selectByMask protoShadowFullCallees protoShadowBadMask) = true ∧
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
  refine ⟨hoistTraitImpls_append_strip (stripCalleeTraitImpls protoNaiveNarrowCallees) []
      protoNaiveNarrowCallees,
    Memory.withCalleesAndTraits_callees _ _ _,
    Memory.withCalleesAndTraits_traitImpls _ _ _,
    lookupCallee_eq_of_batchedCert protoTraitBatchedCert protoLayouts
      (List.Mem.tail _ (List.Mem.head _)) [protoCircleTy],
    runMirExecBounded_narrow_of_batchedCert protoTraitBatchedCert 12 protoTraitInitState
      rfl rfl rfl rfl,
    vcMirWithCallees_narrow_of_batchedCert protoTraitBatchedCert (fun _ _ _ => True) 12
      protoTraitInitState rfl rfl rfl rfl
      (fun out => match out with | .normal (v, _) => v = Value.scalar ⟨31, 4⟩ | _ => False)
      (fun out => by rcases out with ⟨v, m⟩ | _ | _ <;> exact Iff.rfl)
      (fun _ _ _ => Iff.rfl),
    wpMirExecExt_nil_iff (fun _ _ _ => True) protoTraitCone traitCallRootMir _ 12 _,
    by decide +kernel,
    coerceValueAt_u32 protoLayouts 42,
    coerceValueAt_bool protoLayouts true,
    coerceValueAt_ref protoLayouts .not (.uint .u32) { allocId := 1, offsetBytes := 0 },
    coerceValueAt_adt_exact protoLayouts "proto::Circle" [] 0 [.scalar ⟨7, 4⟩],
    coerceValueAt_idempotent protoLayouts (.uint .u32) (.scalar ⟨42, 4⟩)
      (.scalar ⟨wrapScalarBits 42 (scalarModulus 4), 4⟩) (coerceValueAt_u32 protoLayouts 42)⟩

/-- Postcondition "returned `31 : u32`". -/
def post31 (out : MirOutcome) : Prop :=
  match out with
  | .normal (v, _) => v = Value.scalar ⟨31, 4⟩
  | _ => False

/-- The full trait-dispatch run returns `31`, so the havoc WP holds (via `wpMirExecExt_of_run` and
`wpMirExecExt_nil_iff`), and therefore so does the contract-aware VC with summaries (summaries only
weaken obligations, `wpMirExecExt_of_wpMirExecSym`). No hypotheses are assumed. -/
theorem test_partB_summary_weakening :
    wpMirExecSym 12 traitCallRootMir (.running protoTraitInitState) post31 ∧
    wpMirExecExt protoExtContracts protoTraitCone [⟨"proto::poly", 7⟩] 12 traitCallRootMir
      (.running protoTraitInitState) post31 := by
  have hrun : (runMirExecBounded 12 traitCallRootMir (.running protoTraitInitState)).map
      (fun out => match out with | .normal (v, _) => some v | _ => none) =
      some (some (Value.scalar ⟨31, 4⟩)) := rfl
  obtain ⟨out, hout, hv⟩ := Option.map_eq_some_iff.mp hrun
  have hpost : post31 out := by
    rcases out with ⟨v, m⟩ | _ | _
    · exact Option.some.inj hv
    · nomatch hv
    · nomatch hv
  have hsym : wpMirExecSym 12 traitCallRootMir (.running protoTraitInitState) post31 :=
    (wpMirExecExt_nil_iff protoExtContracts protoTraitCone traitCallRootMir post31 12
      (.running protoTraitInitState)).mp
      (wpMirExecExt_of_run protoExtContracts protoTraitCone [] traitCallRootMir post31 12
        (.running protoTraitInitState) out hout hpost)
  exact ⟨hsym, wpMirExecExt_of_wpMirExecSym protoExtContracts protoTraitCone [⟨"proto::poly", 7⟩]
    traitCallRootMir post31 12 (.running protoTraitInitState) hsym⟩

/-- Memory-frame simp lemmas of `Memory.withCalleesAndTraits`, instantiated concretely. -/
theorem test_partB_memory_frame_lemmas :
    (Memory.withCalleesAndTraits protoNaiveNarrowCallees protoHoistedExtra emptyMemory).borrows =
      emptyMemory.borrows ∧
    (Memory.withCalleesAndTraits protoNaiveNarrowCallees protoHoistedExtra emptyMemory).globals =
      emptyMemory.globals ∧
    (Memory.withCalleesAndTraits protoNaiveNarrowCallees protoHoistedExtra emptyMemory).callerLocals =
      emptyMemory.callerLocals ∧
    (Memory.withCalleesAndTraits protoNaiveNarrowCallees protoHoistedExtra emptyMemory).fnPtrs =
      emptyMemory.fnPtrs ∧
    (Memory.withCalleesAndTraits protoNaiveNarrowCallees protoHoistedExtra emptyMemory).callStack =
      emptyMemory.callStack ∧
    (Memory.withCalleesAndTraits protoNaiveNarrowCallees protoHoistedExtra emptyMemory).activeCallee =
      emptyMemory.activeCallee ∧
    (Memory.withCalleesAndTraits protoNaiveNarrowCallees protoHoistedExtra emptyMemory).activeProtectors =
      emptyMemory.activeProtectors ∧
    Memory.withCalleesAndTraits protoNaiveNarrowCallees protoHoistedExtra emptyMemory =
      Memory.withCalleeCtx protoNaiveNarrowCallees emptyMemory.activeCallee protoHoistedExtra
        emptyMemory :=
  ⟨Memory.withCalleesAndTraits_borrows _ _ _, Memory.withCalleesAndTraits_globals _ _ _,
    Memory.withCalleesAndTraits_callerLocals _ _ _, Memory.withCalleesAndTraits_fnPtrs _ _ _,
    Memory.withCalleesAndTraits_callStack _ _ _, Memory.withCalleesAndTraits_activeCallee _ _ _,
    Memory.withCalleesAndTraits_activeProtectors _ _ _,
    Memory.withCalleesAndTraits_eq_withCalleeCtx _ _ _⟩

/-- The theory-file canaries, re-exported conjunct by conjunct (each is *used*, not merely
named): naive narrowing breaks trait dispatch, the certified narrowing preserves the exact result,
every negative certificate is rejected, and the external summary is load-bearing in the VC. -/
theorem test_partB_canaries :
    lookupCallee protoNaiveNarrowCallees protoLayouts "proto::Area::area" [protoCircleTy] [] = none ∧
    CallConeClosedPoly protoTraitCone traitCallRootMir protoFullCallees [] = false ∧
    ((runMirExecBounded 12 traitCallRootMir
        (.running (MachineState.mapMem
          (Memory.withCalleesAndTraits protoNaiveNarrowCallees protoHoistedExtra)
          protoTraitInitState))).map
      (fun out => match out with | .normal (v, _) => some v | _ => none)) =
      some (some (Value.scalar ⟨31, 4⟩)) ∧
    checkBatchedVcConeNarrowCert protoTraitCone traitCallRootMir protoShadowFullCallees
      protoShadowBadMask [] [] [] = false ∧
    checkBatchedVcConeNarrowCert protoTraitCone traitCallRootMir protoFullCallees protoTraitMask []
      [⟨"proto::poly", 1⟩] [⟨"proto::poly", 1⟩] = false ∧
    checkBatchedVcConeNarrowCert protoTraitCone traitCallRootMir protoFullCallees
      [false, false, true, false, false, false] [] [] [] = false ∧
    vcMirWithCallees protoExtContracts 3 protoExtCallRootMir protoExtInitState [] []
      [⟨"ext::rand", 7⟩] protoExtCone protoExtPost ∧
    ¬ vcMirWithCallees protoExtContracts 3 protoExtCallRootMir protoExtInitState [] []
      [] protoExtCone protoExtPost ∧
    (∀ ext ∈ ([] : ExternalSummaryEnv), findCallee? protoFullCallees ext.defPath = none) ∧
    checkBatchedVcConeNarrowCertMask protoTraitCone traitCallRootMir
      protoRustcStyleCallees protoRustcStyleMask [] [] [] = true ∧
    vcMirWithCallees protoCoercedExtContracts 3 protoExtCallRootMir protoExtInitState [] []
      [⟨"ext::rand", 8⟩] protoExtCone protoExtPost ∧
    (([] : List TraitImplEntry) ++ flatMapTraitImpls protoFullCallees).filter
        (fun e => stringEq e.traitRef.defPath "proto::Area::area") =
      (hoistMaskTraitImpls protoFullCallees protoTraitMask [] ++
        flatMapTraitImpls (selectByMask protoFullCallees protoTraitMask)).filter
        (fun e => stringEq e.traitRef.defPath "proto::Area::area") :=
  ⟨canary_naiveNarrow_breaks_trait_dispatch.2.1,
    canary_naiveNarrow_breaks_trait_dispatch.2.2.2.2,
    canary_traitDispatch_preserved_under_batchedVcNarrow.1,
    canary_duplicateShadow_rejected.1,
    canary_externalShadowsInternal_rejected.1,
    canary_missingTraitImplBody_rejected.1,
    canary_externalSummary_vc.2.1,
    canary_externalSummary_vc.2.2,
    protoTraitBatchedCert.untrustedAdmissible,
    canary_keptBodyWithTraitImpl_accepted.2.1,
    canary_coercedExternalSummary_vc,
    traitFilter_hoistMask_eq (cone := protoTraitCone) (extra := []) rfl
      (List.Mem.tail _ (List.Mem.head _))⟩

/-- The mask-aware certificate for the `rustc-capture` layout (a kept impl body carrying its own
`TraitImplEntry`) is load-bearing: through `runMirExecBounded_narrow_of_batchedCert` the narrowed
execution returns exactly the full execution's `31`. -/
theorem test_partB_rustcStyle_narrow_run :
    hoistMaskTraitImpls protoRustcStyleCallees protoRustcStyleMask [] =
      hoistTraitImpls [protoFillerA, protoFillerB] [] ∧
    lookupCallee protoRustcStyleCallees protoLayouts "proto::Area::area" [protoCircleTy] [] =
      lookupCallee (selectByMask protoRustcStyleCallees protoRustcStyleMask) protoLayouts
        "proto::Area::area" [protoCircleTy]
        (hoistMaskTraitImpls protoRustcStyleCallees protoRustcStyleMask []) ∧
    (runMirExecBounded 12 traitCallRootMir
        (.running (MachineState.mapMem
          (Memory.withCalleesAndTraits (selectByMask protoRustcStyleCallees protoRustcStyleMask)
            (hoistMaskTraitImpls protoRustcStyleCallees protoRustcStyleMask []))
          (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir [] emptyMemory
            protoRustcStyleCallees)))).map leafBits = some (some 31) := by
  refine ⟨hoistMaskTraitImpls_eq_hoistTraitImpls _ _ _,
    lookupCallee_eq_of_traitConeAgree protoLayouts [protoCircleTy] rfl
      (traitFilter_hoistMask_eq (cone := protoTraitCone) (extra := []) rfl
        (List.Mem.tail _ (List.Mem.head _)))
      (fun e he _ => by
        change e ∈ [protoAreaEntry] at he
        rcases he with _ | ⟨_, h⟩
        · rfl
        · nomatch h),
    ?_⟩
  rw [runMirExecBounded_narrow_of_batchedCert canary_keptBodyWithTraitImpl_accepted.2.2.2 12 _
    rfl rfl rfl rfl, Option.map_map]
  have hfun : (leafBits ∘ MirOutcome.mapMem (Memory.withCalleesAndTraits
      (selectByMask protoRustcStyleCallees protoRustcStyleMask)
      (hoistMaskTraitImpls protoRustcStyleCallees protoRustcStyleMask []))) = leafBits := by
    funext out
    rcases out with ⟨v, m⟩ | _ | _
    · cases v <;> rfl
    · rfl
    · rfl
  rw [hfun]
  rfl

/-- The entry state of `protoExtCallRootMir` is cone-safe (discharged, not assumed). -/
theorem protoExtInitState_coneSafe :
    StepConeSafeTrait protoExtCone protoExtCallRootMir protoExtInitState :=
  stepConeSafeTrait_of_closedInvPoly (c₁ := []) (ti₁ := []) (by decide +kernel) rfl
    (closedInvPoly_entry rfl rfl rfl rfl)

/-- The real external call emitted by `protoExtCallRootMir` stays in the cone, so the cone-filtered
summary lookup agrees with the unfiltered one at that call. -/
theorem test_partB_extCallInCone :
    NodeExtCallInCone protoExtCone (stepMirFn protoExtCallRootMir protoExtInitState) ∧
    coneSummary? protoExtCone [⟨"ext::rand", 7⟩] protoExtReq.defPath =
      findExternalSummary? [⟨"ext::rand", 7⟩] protoExtReq.defPath ∧
    findExternalSummary? [⟨"ext::rand", 7⟩] protoExtReq.defPath = some ⟨"ext::rand", 7⟩ :=
  ⟨stepMirFn_extCallInCone protoExtCone protoExtCallRootMir protoExtInitState
      protoExtInitState_coneSafe,
    coneSummary?_eq_of_stepMirFn_extCall [⟨"ext::rand", 7⟩] protoExtInitState_coneSafe
      protoExtStep_eq,
    by decide +kernel⟩

/-- Mixed-partition trait-impl hoisting: when `"proto::Area::area"` has `protoAreaEntry` on a kept
body (`protoCircleAreaWithTrait`) and `protoSquareAreaEntry` on a dropped carrier
(`protoSquareAreaHolder`), both `checkKeptCarryNoConeTraitImpls` and `checkMaskTraitPartition`
return `false`, while `checkBatchedVcConeNarrowCertGeneral` + `BatchedVcConeNarrowCert.ofCheckGeneral`
certify narrowing (via `upsertMatchingTraitImpl` deduplication) and preserve the execution outcome. -/
theorem test_partB_mixed_trait_partition :
    checkKeptCarryNoConeTraitImpls protoMixedTraitCone
      (selectByMask protoMixedTraitCallees protoMixedTraitMask) = false ∧
    checkMaskTraitPartition protoMixedTraitCone protoMixedTraitCallees protoMixedTraitMask = false ∧
    checkBatchedVcConeNarrowCertGeneral protoMixedTraitCone traitCallRootMir
      protoMixedTraitCallees protoMixedTraitMask [] [] [] = true ∧
    lookupCallee protoMixedTraitCallees protoLayouts "proto::Area::area" [protoCircleTy] [] =
      lookupCallee (selectByMask protoMixedTraitCallees protoMixedTraitMask) protoLayouts
        "proto::Area::area" [protoCircleTy] (hoistTraitImpls protoMixedTraitCallees []) ∧
    ((runMirExecBounded 12 traitCallRootMir
        (.running (MachineState.mapMem
          (Memory.withCalleesAndTraits
            (selectByMask protoMixedTraitCallees protoMixedTraitMask)
            (hoistTraitImpls protoMixedTraitCallees []))
          (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir []
            emptyMemory protoMixedTraitCallees)))).map
      (fun out => match out with | .normal (v, _) => some v | _ => none)) =
      some (some (Value.scalar ⟨31, 4⟩)) :=
  ⟨canary_mixedTraitPartition_accepted.1,
   canary_mixedTraitPartition_accepted.2.1,
   canary_mixedTraitPartition_accepted.2.2.1,
   lookupCallee_eq_of_batchedCert canary_mixedTraitPartition_accepted.2.2.2.1 protoLayouts
     (List.Mem.tail _ (List.Mem.head _)) [protoCircleTy],
   canary_mixedTraitPartition_accepted.2.2.2.2⟩

/-- Multi-call external summary preservation (`closedInvPoly_resumeExternalCall` +
`canary_twoExternalCalls_vc`): after resuming from the first external call (`ext::seed`), the
resumed state in `bb1` stays cone-safe (`StepConeSafeTrait`), `coneSummary?_eq_of_stepMirFn_extCall`
applies to the second external call (`ext::add_twenty`), and the 2-call VC holds with both summaries
and fails when the second summary is dropped. -/
theorem test_partB_two_external_calls :
    StepConeSafeTrait protoTwoExtCone protoTwoExtCallsRootMir protoTwoExtStateAfterSeed ∧
    NodeExtCallInCone protoTwoExtCone
      (stepMirFn protoTwoExtCallsRootMir protoTwoExtStateAfterSeed) ∧
    coneSummary? protoTwoExtCone protoTwoExtSummaries protoTwoExtReq2.defPath =
      findExternalSummary? protoTwoExtSummaries protoTwoExtReq2.defPath ∧
    vcMirWithCallees protoTwoExtContracts 4 protoTwoExtCallsRootMir protoTwoExtInitState [] []
      protoTwoExtSummaries protoTwoExtCone protoTwoExtPost ∧
    ¬ vcMirWithCallees protoTwoExtContracts 4 protoTwoExtCallsRootMir protoTwoExtInitState [] []
      [⟨"ext::seed", 10⟩] protoTwoExtCone protoTwoExtPost :=
  ⟨canary_twoExternalCalls_vc.1,
   stepMirFn_extCallInCone protoTwoExtCone protoTwoExtCallsRootMir protoTwoExtStateAfterSeed
     canary_twoExternalCalls_vc.1,
   coneSummary?_eq_of_stepMirFn_extCall protoTwoExtSummaries canary_twoExternalCalls_vc.1
     protoTwoExtStep2_eq,
   canary_twoExternalCalls_vc.2.2.1,
   canary_twoExternalCalls_vc.2.2.2⟩

/-- Genuine universally quantified symbolic VC (`∀ x : Nat`) where `x % 1000` flows through
polymorphic `sym_poly::<u32>(_1)` (`AddUnchecked(_1, 7)`) and trait-dispatched
`<Circle as Area>::area(_0)` (`AddUnchecked(_1, 24)`) to return `(x % 1000) + 31 : u32`. -/
theorem test_partB_symbolic_trait_vc (x : Nat) :
    symTraitInitState (x % 1000) protoSymFullCallees =
      MirFuelFree.initMachineStateWithMemoryAndCallees symTraitRootMir [.scalar ⟨x % 1000, 4⟩]
        emptyMemory protoSymFullCallees ∧
    computeBatchedVcNarrowCert 4 symTraitRootMir protoSymFullCallees [] [] =
      (protoSymCone, protoSymMask, []) ∧
    vcMirWithCallees protoSymContracts 8 symTraitRootMir
      (symTraitInitState (x % 1000) protoSymFullCallees)
      protoSymNarrowCallees protoSymHoistedExtra [] protoSymCone (symTraitPost (x % 1000)) ∧
    vcMirWithCallees protoSymContracts 8 symTraitRootMir
      (symTraitInitState (x % 1000) protoSymFullCallees)
      protoSymFullCallees [] [] protoSymCone (symTraitPost (x % 1000)) :=
  ⟨symTraitInitState_eq_initMachineState (x % 1000),
   protoSymBatchedCert_check.1, (symTrait_vc_narrow x).1, (symTrait_vc_narrow x).2⟩

/-- The symbolic VC on the whole non-overflowing `u32` range (`symTrait_vc_narrow_of_lt` at the
largest admissible input `4294967264 = 2^32 - 32`) and the overflow canary
(`symTrait_vc_overflow_fails`: at `4294967290` the first `AddUnchecked` is UB and the VC is false on
the narrowed and on the full callee table). -/
theorem test_partB_symbolic_vc_range :
    vcMirWithCallees protoSymContracts 8 symTraitRootMir
      (symTraitInitState 4294967264 protoSymFullCallees)
      protoSymFullCallees [] [] protoSymCone (symTraitPost 4294967264) ∧
    ¬ vcMirWithCallees protoSymContracts 8 symTraitRootMir
        (symTraitInitState 4294967290 protoSymFullCallees)
        protoSymNarrowCallees protoSymHoistedExtra [] protoSymCone (symTraitPost 4294967290) ∧
    ¬ vcMirWithCallees protoSymContracts 8 symTraitRootMir
        (symTraitInitState 4294967290 protoSymFullCallees)
        protoSymFullCallees [] [] protoSymCone (symTraitPost 4294967290) :=
  ⟨(symTrait_vc_narrow_of_lt 4294967264 (by decide)).2,
   symTrait_vc_overflow_fails.1, symTrait_vc_overflow_fails.2⟩

/-- Cone filtering is conservative (`wpMirExecExt_mono_cone`): the 2-call VC proved with summaries
trusted on `protoTwoExtCone` still holds when summaries are trusted on a larger cone. -/
theorem test_partB_cone_filter_conservative :
    vcMirWithCallees protoTwoExtContracts 4 protoTwoExtCallsRootMir protoTwoExtInitState [] []
      protoTwoExtSummaries ("proto::two_ext_root" :: protoTwoExtCone) protoTwoExtPost :=
  wpMirExecExt_mono_cone protoTwoExtContracts protoTwoExtSummaries protoTwoExtCallsRootMir
    protoTwoExtPost (fun _ h => inCone_iff.mpr (List.mem_cons_of_mem _ (inCone_iff.mp h))) 4 _
    canary_twoExternalCalls_vc.2.2.1

/-- Diverging external call (`canary_divergingExternalCall_coneSafe`): the call `ext::diverge` is
emitted from a cone-safe entry state and targets the cone; after a panicked answer the cleanup-pad
state is cone-safe again (`stepConeSafeTrait_of_resumeExternalDivergingCall`); a normal return from
the diverging call is UB. -/
theorem test_partB_diverging_external_call :
    stepMirState protoDivergingExtRootMir (.running protoDivergingInitState) =
      .vis (.inr (.inr (.call protoDivergingReq))) protoDivergingCont ∧
    NodeExtCallInCone protoDivergingCone
      (stepMirFn protoDivergingExtRootMir protoDivergingInitState) ∧
    StepConeSafeTrait protoDivergingCone protoDivergingExtRootMir protoDivergingStateAfterPanic ∧
    protoDivergingCont (.panicked protoDivergingReq.memory) =
      .running protoDivergingStateAfterPanic ∧
    protoDivergingCont (.returned (.scalar ⟨0, 4⟩) protoDivergingReq.memory) = .faulted .ub :=
  ⟨protoDivergingStep_eq,
   stepMirFn_extCallInCone protoDivergingCone protoDivergingExtRootMir protoDivergingInitState
     (stepConeSafeTrait_of_closedInvPoly (c₁ := []) (ti₁ := []) (by decide +kernel)
       (by decide +kernel) (closedInvPoly_entry rfl rfl rfl rfl)),
   canary_divergingExternalCall_coneSafe.2.2.2.1,
   canary_divergingExternalCall_coneSafe.2.1,
   canary_divergingExternalCall_coneSafe.2.2.2.2⟩

/- Meta-level non-reducibility audit confirming that `rfl` / `isDefEq` CANNOT discharge the symbolic
VC `symTrait_vc_narrow` because `Nat.ble 4294967296 ((x % 1000) + 7)` and
`Nat.ble 4294967296 (((x % 1000) + 7) + 24)` are not definitionally equal to `false`, and
`evalScalarBinOp .addUnchecked ⟨x % 1000, 4⟩ ⟨7, 4⟩ [] emptyMemory false` is not definitionally
equal to `.ok (.scalar ⟨(x % 1000) + 7, 4⟩) [] emptyMemory` for a symbolic free variable `x : Nat`. -/
open Lean Elab Command Term Meta in
run_cmd liftTermElabM do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let falseExpr := toExpr false
    let ble1Stx ← `(term| Nat.ble 4294967296 (Nat.add ($(← exprToSyntax x) % 1000) 7))
    let ble1Expr ← elabTerm ble1Stx none
    if ← isDefEq ble1Expr falseExpr then
      throwError "symbolic VC audit failed: first Nat.ble overflow check unexpectedly reduced by isDefEq!"
    let ble2Stx ← `(term| Nat.ble 4294967296 (Nat.add (Nat.add ($(← exprToSyntax x) % 1000) 7) 24))
    let ble2Expr ← elabTerm ble2Stx none
    if ← isDefEq ble2Expr falseExpr then
      throwError "symbolic VC audit failed: second Nat.ble overflow check unexpectedly reduced by isDefEq!"
    let binLhsStx ← `(term| evalScalarBinOp .addUnchecked ⟨$(← exprToSyntax x) % 1000, 4⟩ ⟨7, 4⟩ [] emptyMemory false)
    let binRhsStx ← `(term| RvalueEvalResult.ok (.scalar ⟨Nat.add ($(← exprToSyntax x) % 1000) 7, 4⟩) [] emptyMemory)
    let binLhsExpr ← elabTerm binLhsStx none
    let binRhsExpr ← elabTerm binRhsStx none
    if ← isDefEq binLhsExpr binRhsExpr then
      throwError "symbolic VC audit failed: evalScalarBinOp .addUnchecked unexpectedly reduced by isDefEq!"
    logInfo m!"symbolic VC audit passed: the AddUnchecked overflow guards of symTrait_vc_narrow do not reduce by isDefEq on a free input"

/-- Part C / Part D theory canaries and the projections of `AllocRenamingRel`, used concretely. -/
theorem test_partCD_canaries :
    (evalDemandCallerLocation (evalDemandCallerLocation {} (protoPanicSite {} {}) emptyMemory).1
        (protoDirectSite {}) (evalDemandCallerLocation {} (protoPanicSite {} {}) emptyMemory).2.2).2.2.globals.length = 3 ∧
    (protoPanicSite ⟨false, false, false⟩ {}).resolve = protoUserCallerPos ∧
    CallerLocationSite.resolve
        ⟨protoUnwrapFailedPos, [protoUnwrapFailedFrame {},
          ⟨"my_crate::non_track_helper", some protoOtherCallPos, false, {}⟩, protoUserCallerFrame {}]⟩ =
      protoUnwrapBodyPos ∧
    (evalDemandCallerLocation {} (protoDirectSite {})
      { emptyMemory with
        borrows := [{ tag := 1, targetLocal := 2, targetProjection := [], perm := .unique }],
        nextTag := 2, nextAllocId := 0 }).2.1.allocId = 3 ∧
    lookupBorrow ([] : List BorrowEntry) 5 = none ∧
    readLocationBorrowAware
        (evalDemandCallerLocation {} (protoDirectSite {}) emptyMemory).2.2
        (evalDemandCallerLocation {} (protoDirectSite {}) emptyMemory).2.1 =
      some (protoLibRsBytes, 108, 7) ∧
    shiftLeftBitsSafe 0xdeadbeef wideShiftTwoPow64 4 = 0 ∧
    symArrayLen (buildEagerDistinctChain 16 16) = 16 ∧
    (lazyDistinctChainCounted 16 16).1 = buildLazyDistinctChain 16 16 ∧
    (mkLazyReadCounted 8 (.constVec 8 0) 2).1 = mkLazyRead 8 (.constVec 8 0) 2 ∧
    mkLazyReadCounted 8 (.write (.constVec 8 0) 2 99) 2 = (some 99, 1) :=
  ⟨demandCallerLocation_filename_dedup.1,
    trackCaller_span_owner_policy.1,
    trackCaller_stops_at_nonTrackCaller_frame,
    canary_demandLocation_borrowTag_disjoint.2.1,
    lookupBorrow_eq_none_of_lt (borrows := []) (id := 5)
      (fun _ (h : _ ∈ ([] : List BorrowEntry)) => nomatch h),
    (evalDemandCallerLocation_borrowAware_spec {} (protoDirectSite {}) emptyMemory
      (⟨(fun _ (h : _ ∈ ([] : List CapturedAllocation)) => nomatch h),
        (fun _ _ (h : _ ∈ ([] : List (List UInt8 × AllocId))) => nomatch h)⟩ :
        DemandLocInv {} emptyMemory)
      (fun _ (h : _ ∈ ([] : List BorrowEntry)) => nomatch h : BorrowsFresh emptyMemory)
      (by decide)).2.1,
    canary_wideShift_two_pow_64.2.1,
    symArrayLen_buildEagerDistinctChain 16 16,
    lazyDistinctChainCounted_fst 16 16,
    mkLazyReadCounted_fst 8 (.constVec 8 0) 2,
    mkLazyReadCounted_hit_top (.constVec 8 0) 99 (by decide)⟩

/-- The actual successor of a `nop` on a frame-free state. -/
def protoNopAfter : MachineState :=
  match evalStmt { protoRetagMachineState with memory := emptyMemory } ⟨.nop, "nop"⟩
      protoRetagLocalDecls protoLayouts with
  | .tau (.running ns) => ns
  | _ => { protoRetagMachineState with memory := emptyMemory }

theorem protoNop_step :
    evalStmt { protoRetagMachineState with memory := emptyMemory } ⟨.nop, "nop"⟩
      protoRetagLocalDecls protoLayouts = .tau (.running protoNopAfter) := rfl

/-- Direct (closed) witness for `evalStmt_pure_memory_eq` and `normalStmtStep_eq_raw_of_pure`. -/
theorem test_partC_stmt_pure_memory :
    protoNopAfter.memory = emptyMemory ∧
    normalStmtStep { protoRetagMachineState with memory := emptyMemory }
        ⟨.nop, "nop"⟩ protoRetagLocalDecls protoLayouts = protoNopAfter :=
  ⟨evalStmt_pure_memory_eq rfl rfl rfl protoNop_step,
    by rw [normalStmtStep_eq_raw_of_pure _ _ _ _ rfl rfl rfl, protoNop_step]⟩

theorem test_partC_renaming_witness :
    AllocRenamingRel [(1, 4)] emptyMemory emptyMemory [⟨1, 0⟩] [⟨4, 0⟩] :=
  ⟨by decide, rfl, fun _ hp => by cases hp with | head => rfl | tail _ h => nomatch h⟩

/-- The three projections of a concrete (proved) `AllocRenamingRel`. -/
theorem test_partC_renaming_projections :
    AllocRenamingWf [(1, 4)] = true ∧
    [(⟨4, 0⟩ : ProvenancePtr)] = [(⟨1, 0⟩ : ProvenancePtr)].map (relocatePtr [(1, 4)]) ∧
    LocationPtrObsEq emptyMemory.globals ⟨1, 0⟩ emptyMemory.globals (relocatePtr [(1, 4)] ⟨1, 0⟩) :=
  ⟨test_partC_renaming_witness.wf, test_partC_renaming_witness.ptrsMapped,
    test_partC_renaming_witness.obsAgree ⟨1, 0⟩ (List.Mem.head _)⟩

/-- Part B runs with the narrowed table cached as a literal (steady state after the one-time
certificate + narrowing), proved equal to the computed narrowing. -/
def cachedNarrowState (full : List CapturedMir) : MachineState :=
  MachineState.mapMem (Memory.withCalleesAndTraits [protoPoly, protoCircleArea] [protoAreaEntry])
    (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir [] emptyMemory full)

def buildFillerCallees : Nat → List CapturedMir
  | 0 => []
  | k + 1 => protoLeaf "bench::filler" (k + 100) 0 [] :: buildFillerCallees k

def fullCallees16 : List CapturedMir := buildFillerCallees 13 ++ [protoPoly, protoAreaImplHolder, protoCircleArea]
def fullCallees64 : List CapturedMir := buildFillerCallees 61 ++ [protoPoly, protoAreaImplHolder, protoCircleArea]
def fullCallees128 : List CapturedMir := buildFillerCallees 125 ++ [protoPoly, protoAreaImplHolder, protoCircleArea]

theorem cachedNarrow_eq_computed_16 :
    selectByMask fullCallees16 (fullCallees16.map (fun b => inCone protoTraitCone b.defPath)) =
      [protoPoly, protoCircleArea] ∧ hoistTraitImpls fullCallees16 [] = [protoAreaEntry] :=
  ⟨rfl, rfl⟩
theorem cachedNarrow_eq_computed_64 :
    selectByMask fullCallees64 (fullCallees64.map (fun b => inCone protoTraitCone b.defPath)) =
      [protoPoly, protoCircleArea] ∧ hoistTraitImpls fullCallees64 [] = [protoAreaEntry] :=
  ⟨rfl, rfl⟩
theorem cachedNarrow_eq_computed_128 :
    selectByMask fullCallees128 (fullCallees128.map (fun b => inCone protoTraitCone b.defPath)) =
      [protoPoly, protoCircleArea] ∧ hoistTraitImpls fullCallees128 [] = [protoAreaEntry] :=
  ⟨rfl, rfl⟩

/-- Narrowed state computed from the certificate data (mask + hoisting) of a full table. -/
def narrowedTraitState (full : List CapturedMir) : MachineState :=
  MachineState.mapMem
    (Memory.withCalleesAndTraits
      (selectByMask full (full.map (fun b => inCone protoTraitCone b.defPath)))
      (hoistTraitImpls full []))
    (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir [] emptyMemory full)

/-- Reducible (unsealed) copy of `coerceValueAt`, used only as the coercion baseline. -/
def coerceValueAtUnsealed (layouts : LayoutTable) (ty : RigidTy) (v : Value) : Option Value :=
  match ty with
  | .uint ut =>
    match v with
    | .scalar sc =>
      let w := uintTyByteWidth layouts ut
      match Nat.beq sc.sizeBytes w with
      | true => some (.scalar ⟨wrapScalarBits sc.bits (scalarModulus w), w⟩)
      | false => none
    | _ => none
  | _ => none

/-- Iterated `K`-step coercion chain using `@[irreducible] coerceValueAt`. -/
def chainCoerceSealed : Nat → Value → Option Value
  | 0, v => some v
  | k + 1, v =>
    match coerceValueAt protoLayouts (.uint .u32) v with
    | some v' => chainCoerceSealed k v'
    | none => none

/-- Iterated `K`-step coercion chain using reducible `coerceValueAtUnsealed`. -/
def chainCoerceUnsealed : Nat → Value → Option Value
  | 0, v => some v
  | k + 1, v =>
    match coerceValueAtUnsealed protoLayouts (.uint .u32) v with
    | some v' => chainCoerceUnsealed k v'
    | none => none

theorem chainCoerceSealed_idempotent (v v' : Value)
    (h : coerceValueAt protoLayouts (.uint .u32) v = some v') :
    ∀ k : Nat, chainCoerceSealed (k + 1) v = some v'
  | 0 => by
    unfold chainCoerceSealed
    rw [h]
    rfl
  | k + 1 => by
    unfold chainCoerceSealed
    rw [h]
    dsimp only
    exact chainCoerceSealed_idempotent v' v' (coerceValueAt_idempotent protoLayouts (.uint .u32) v v' h) k

/-- Closed instance of `chainCoerceSealed_idempotent` (16 sealed coercions of `5 : u32`). -/
theorem test_partB_chain_idempotent :
    chainCoerceSealed 16 (.scalar ⟨5, 4⟩) = some (.scalar ⟨wrapScalarBits 5 (scalarModulus 4), 4⟩) :=
  chainCoerceSealed_idempotent _ _ (coerceValueAt_u32 protoLayouts 5) 15

def symFullCallees128 : List CapturedMir :=
  buildFillerCallees 125 ++ [protoSymPoly, protoAreaImplHolder, protoSymCircleArea]

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
        (runMirExecBounded 12 traitCallRootMir
          (.running (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir []
            emptyMemory fullCallees16))).map leafBits = some (some 31) := by decide +kernel)
  bench "PartB_cert_M16" `(command|
    theorem bench_partB_cert_16 :
        (computeBatchedVcNarrowCert 4 traitCallRootMir fullCallees16 [] []).1 = protoTraitCone ∧
        checkBatchedVcConeNarrowCert protoTraitCone traitCallRootMir fullCallees16
          (fullCallees16.map (fun b => inCone protoTraitCone b.defPath)) [] [] [] = true := by
      decide +kernel)
  bench "PartB_narrow_M16" `(command|
    theorem bench_partB_narrow_16 :
        (runMirExecBounded 12 traitCallRootMir (.running (narrowedTraitState fullCallees16))).map
          leafBits = some (some 31) := by decide +kernel)
  bench "PartB_narrowCached_M16" `(command|
    theorem bench_partB_narrowCached_16 :
        (runMirExecBounded 12 traitCallRootMir (.running (cachedNarrowState fullCallees16))).map
          leafBits = some (some 31) := by decide +kernel)
  bench "PartB_full_M64" `(command|
    theorem bench_partB_full_64 :
        (runMirExecBounded 12 traitCallRootMir
          (.running (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir []
            emptyMemory fullCallees64))).map leafBits = some (some 31) := by decide +kernel)
  bench "PartB_cert_M64" `(command|
    theorem bench_partB_cert_64 :
        (computeBatchedVcNarrowCert 4 traitCallRootMir fullCallees64 [] []).1 = protoTraitCone ∧
        checkBatchedVcConeNarrowCert protoTraitCone traitCallRootMir fullCallees64
          (fullCallees64.map (fun b => inCone protoTraitCone b.defPath)) [] [] [] = true := by
      decide +kernel)
  bench "PartB_narrow_M64" `(command|
    theorem bench_partB_narrow_64 :
        (runMirExecBounded 12 traitCallRootMir (.running (narrowedTraitState fullCallees64))).map
          leafBits = some (some 31) := by decide +kernel)
  bench "PartB_narrowCached_M64" `(command|
    theorem bench_partB_narrowCached_64 :
        (runMirExecBounded 12 traitCallRootMir (.running (cachedNarrowState fullCallees64))).map
          leafBits = some (some 31) := by decide +kernel)
  bench "PartB_full_M128" `(command|
    theorem bench_partB_full_128 :
        (runMirExecBounded 12 traitCallRootMir
          (.running (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir []
            emptyMemory fullCallees128))).map leafBits = some (some 31) := by decide +kernel)
  bench "PartB_cert_M128" `(command|
    theorem bench_partB_cert_128 :
        (computeBatchedVcNarrowCert 4 traitCallRootMir fullCallees128 [] []).1 = protoTraitCone ∧
        checkBatchedVcConeNarrowCert protoTraitCone traitCallRootMir fullCallees128
          (fullCallees128.map (fun b => inCone protoTraitCone b.defPath)) [] [] [] = true := by
      decide +kernel)
  bench "PartB_narrow_M128" `(command|
    theorem bench_partB_narrow_128 :
        (runMirExecBounded 12 traitCallRootMir (.running (narrowedTraitState fullCallees128))).map
          leafBits = some (some 31) := by decide +kernel)
  bench "PartB_narrowCached_M128" `(command|
    theorem bench_partB_narrowCached_128 :
        (runMirExecBounded 12 traitCallRootMir (.running (cachedNarrowState fullCallees128))).map
          leafBits = some (some 31) := by decide +kernel)
  bench "PartB_rflVC_full_M128" `(command|
    theorem bench_partB_rflVC_full_128 :
        vcMirWithCallees (fun _ _ _ => True) 12 traitCallRootMir
          (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir [] emptyMemory
            fullCallees128)
          fullCallees128 [] [] protoTraitCone
          (fun out => match out with | .normal (v, _) => v = Value.scalar ⟨31, 4⟩ | _ => False) :=
      rfl)
  bench "PartB_rflVC_narrowCached_M128" `(command|
    theorem bench_partB_rflVC_narrowCached_128 :
        vcMirWithCallees (fun _ _ _ => True) 12 traitCallRootMir
          (MirFuelFree.initMachineStateWithMemoryAndCallees traitCallRootMir [] emptyMemory
            fullCallees128)
          [protoPoly, protoCircleArea] [protoAreaEntry] [] protoTraitCone
          (fun out => match out with | .normal (v, _) => v = Value.scalar ⟨31, 4⟩ | _ => False) :=
      rfl)
  bench "PartB_symVC_full_M128" `(command|
    theorem bench_partB_symVC_full_128 (x : Nat) :
        vcMirWithCallees protoSymContracts 8 symTraitRootMir
          (symTraitInitState (x % 1000) symFullCallees128)
          symFullCallees128 [] [] protoSymCone (symTraitPost (x % 1000)) := by
      have h_ovf1 : Nat.ble 4294967296 (Nat.add (x % 1000) 7) = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.ble_eq]; change ¬(4294967296 ≤ (x % 1000) + 7); omega
      have h_ovf2 : Nat.ble 4294967296 (Nat.add (Nat.add (x % 1000) 7) 24) = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.ble_eq]; change ¬(4294967296 ≤ ((x % 1000) + 7) + 24); omega
      unfold vcMirWithCallees
      refine wpMirExecExt_step_tau rfl ?_
      refine wpMirExecExt_step_tau
        (stepMirState_assign_local _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl
          (evalRvalue_addUnchecked_u32 _ _ _ rfl h_ovf1) rfl rfl rfl) ?_
      refine wpMirExecExt_step_tau rfl ?_
      refine wpMirExecExt_step_tau rfl ?_
      refine wpMirExecExt_step_tau
        (stepMirState_assign_local _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl
          (evalRvalue_addUnchecked_u32 _ _ _ rfl h_ovf2) rfl rfl rfl) ?_
      refine wpMirExecExt_step_tau rfl ?_
      refine wpMirExecExt_step_ret rfl ?_
      exact congrArg (fun n => Value.scalar ⟨n, 4⟩)
        (by change ((x % 1000) + 7) + 24 = (x % 1000) + 31; omega))
  bench "PartB_symVC_narrowCached_M128" `(command|
    theorem $(mkIdent `bench_partB_symVC_narrowCached_128) (x : Nat) :
        vcMirWithCallees protoSymContracts 8 symTraitRootMir
          (symTraitInitState (x % 1000) symFullCallees128)
          [protoSymPoly, protoSymCircleArea] [protoAreaEntry] [] protoSymCone
          (symTraitPost (x % 1000)) := by
      have h_ovf1 : Nat.ble 4294967296 (Nat.add (x % 1000) 7) = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.ble_eq]; change ¬(4294967296 ≤ (x % 1000) + 7); omega
      have h_ovf2 : Nat.ble 4294967296 (Nat.add (Nat.add (x % 1000) 7) 24) = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.ble_eq]; change ¬(4294967296 ≤ ((x % 1000) + 7) + 24); omega
      unfold vcMirWithCallees
      refine wpMirExecExt_step_tau rfl ?_
      refine wpMirExecExt_step_tau
        (stepMirState_assign_local _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl
          (evalRvalue_addUnchecked_u32 _ _ _ rfl h_ovf1) rfl rfl rfl) ?_
      refine wpMirExecExt_step_tau rfl ?_
      refine wpMirExecExt_step_tau rfl ?_
      refine wpMirExecExt_step_tau
        (stepMirState_assign_local _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl
          (evalRvalue_addUnchecked_u32 _ _ _ rfl h_ovf2) rfl rfl rfl) ?_
      refine wpMirExecExt_step_tau rfl ?_
      refine wpMirExecExt_step_ret rfl ?_
      exact congrArg (fun n => Value.scalar ⟨n, 4⟩)
        (by change ((x % 1000) + 7) + 24 = (x % 1000) + 31; omega))
  bench "PartB_symVC_cert_M128" `(command|
    theorem $(mkIdent `bench_partB_symVC_cert_128) :
        (computeBatchedVcNarrowCert 4 symTraitRootMir symFullCallees128 [] []).1 = protoSymCone ∧
        checkBatchedVcConeNarrowCert protoSymCone symTraitRootMir symFullCallees128
          (symFullCallees128.map (fun b => inCone protoSymCone b.defPath)) [] [] [] = true := by
      decide +kernel)
  bench "PartB_coerce_sealed_simp" `(command|
    theorem bench_partB_coerce_sealed :
        ∀ bits : Nat, chainCoerceSealed 16 (.scalar ⟨bits, 4⟩) =
          some (.scalar ⟨wrapScalarBits bits (scalarModulus 4), 4⟩) := by
      intro bits
      simp only [chainCoerceSealed, coerceValueAt_u32, wrapScalarBits_eq_mod_modulus, Nat.mod_mod])
  bench "PartB_coerce_unsealed_simp" `(command|
    theorem bench_partB_coerce_unsealed :
        ∀ bits : Nat, chainCoerceUnsealed 16 (.scalar ⟨bits, 4⟩) =
          some (.scalar ⟨wrapScalarBits bits (scalarModulus 4), 4⟩) := by
      intro bits
      dsimp only [chainCoerceUnsealed, coerceValueAtUnsealed, uintTyByteWidth, protoLayouts,
        layoutPointerBytes]
      simp only [wrapScalarBits_eq_mod_modulus, Nat.mod_mod])

/-- The symbolic benchmark's cached narrowed table is the certified narrowing of
`symFullCallees128` (mask selection + hoisting), as for `cachedNarrow_eq_computed_*`. -/
theorem symCachedNarrow_eq_computed_128 :
    selectByMask symFullCallees128 (symFullCallees128.map (fun b => inCone protoSymCone b.defPath)) =
      [protoSymPoly, protoSymCircleArea] ∧ hoistTraitImpls symFullCallees128 [] = [protoAreaEntry] :=
  ⟨rfl, rfl⟩

/-- End-to-end symbolic narrowing at `M = 128`: the VC proved on the cached narrowed table
(`bench_partB_symVC_narrowCached_128`) plus the one-time certificate (`bench_partB_symVC_cert_128`)
yields the VC on the *full* 128-entry callee table via `vcMirWithCallees_narrow_of_batchedCert`. -/
theorem test_partB_symVC_transfer_128 (x : Nat) :
    vcMirWithCallees protoSymContracts 8 symTraitRootMir
      (symTraitInitState (x % 1000) symFullCallees128)
      symFullCallees128 [] [] protoSymCone (symTraitPost (x % 1000)) := by
  have hcert := BatchedVcConeNarrowCert.ofCheck bench_partB_symVC_cert_128.2
  rw [symCachedNarrow_eq_computed_128.1, symCachedNarrow_eq_computed_128.2] at hcert
  exact (vcMirWithCallees_narrow_of_batchedCert hcert protoSymContracts 8
    (symTraitInitState (x % 1000) symFullCallees128) rfl rfl rfl rfl
    (symTraitPost (x % 1000))
    (fun out => by rcases out with ⟨v, m⟩ | _ | _ <;> exact Iff.rfl)
    (fun _ _ _ => Iff.rfl)).mp (bench_partB_symVC_narrowCached_128 x)

/-! ## 5. Part C Witnesses & Scaling (`DemandCallerLocationEnv`, `lean-miri#67`) -/

/-- A demand-world initial state with fresh (empty) globals. -/
def protoLocState : MachineState := { protoRetagMachineState with memory := emptyMemory }

theorem protoLocState_fresh : GlobalsFresh protoLocState.memory := fun _ h => nomatch h

/-- Panicking trace: two normal steps, the 3-frame chain twice (repeated site), and the direct
site once. -/
def protoPanicTrace : List CallerLocationTraceEvent :=
  [ .normalStep ⟨.nop, "nop"⟩, .invokeCallerLocation 2, .normalStep ⟨.nop, "nop"⟩,
    .invokeCallerLocation 2, .invokeCallerLocation 0, .invokeCallerLocation 7 ]

/-- Trace invoking two *distinct* sites (renaming is injective). -/
def protoDistinctTrace : List CallerLocationTraceEvent :=
  [ .invokeCallerLocation 2, .normalStep ⟨.nop, "nop"⟩, .invokeCallerLocation 0 ]

/-- Demand / eager observations agree for ALL 8 redaction policies (general theorem
instantiated per policy) and equal the resolved location of every invoked site. -/
theorem test_partC_bisim_all_policies :
    ∀ pol ∈ allLocationDetailPolicies,
      readLocations
          (runDemandCallerLocationTrace (protoSites pol pol) {} protoLocState protoRetagLocalDecls
            protoLayouts protoPanicTrace).2.2.memory.globals
          (runDemandCallerLocationTrace (protoSites pol pol) {} protoLocState protoRetagLocalDecls
            protoLayouts protoPanicTrace).2.1 =
        readLocations
          (runEagerCallerLocationWorld (protoSites pol pol) protoLocState protoRetagLocalDecls
            protoLayouts protoPanicTrace).2.memory.globals
          (runEagerCallerLocationWorld (protoSites pol pol) protoLocState protoRetagLocalDecls
            protoLayouts protoPanicTrace).1 := by
  intro pol _
  exact (demandCallerLocation_bisim_eager (protoSites pol pol) protoLocState protoRetagLocalDecls
    protoLayouts protoPanicTrace protoLocState_fresh (protoSites_fileLenOk pol pol)).1

theorem test_partC_demandCallerLocation :
    allLocationDetailPolicies.length = 8 ∧
    (LocationDetailPolicy.mk true false true) ∈ allLocationDetailPolicies ∧
    applyLocationDetailPolicy ⟨false, true, false⟩
        (applyLocationDetailPolicy ⟨false, true, false⟩ protoUserCallerPos) =
      applyLocationDetailPolicy ⟨false, true, false⟩ protoUserCallerPos ∧
    resolveCallerLocationAux {} protoUnwrapFailedPos
        ([protoUnwrapFailedFrame {}, protoUnwrapFrame {}] ++ protoUserCallerFrame {} :: []) =
      applyLocationDetailPolicy {}
        (propagateTrackCallerTopDown protoUnwrapFailedPos [protoUnwrapFailedFrame {}, protoUnwrapFrame {}]) ∧
    readU32Le? (u32LeBytes (42 : UInt32).toNat ++ []) = some 42 ∧
    readU64Le? (u64LeBytes 10 ++ []) = some 10 ∧
    decodeInitBytes? (protoLibRsBytes.map Option.some) = some protoLibRsBytes ∧
    lookupGlobalAlloc
        ([mkFilenameAllocation 1 protoLibRsBytes] ++ [mkLocationAllocation 2 1 10 42 13]) 1 =
      some (mkFilenameAllocation 1 protoLibRsBytes) ∧
    lookupGlobalAlloc
        ([mkFilenameAllocation 1 protoLibRsBytes] ++ [mkLocationAllocation 2 1 10 42 13]) 2 =
      some (mkLocationAllocation 2 1 10 42 13) ∧
    readLocationFromGlobals
        ([mkFilenameAllocation 1 protoLibRsBytes] ++ [mkLocationAllocation 2 1 10 42 13])
        { allocId := 2, offsetBytes := 0 } = some (protoLibRsBytes, 42, 13) ∧
    readLocations
        (runDemandCallerLocationTrace (protoSites {} {}) {} protoLocState protoRetagLocalDecls
          protoLayouts protoPanicTrace).2.2.memory.globals
        (runDemandCallerLocationTrace (protoSites {} {}) {} protoLocState protoRetagLocalDecls
          protoLayouts protoPanicTrace).2.1 =
      [ some (protoLibRsBytes, 42, 13), some (protoLibRsBytes, 42, 13),
        some (protoLibRsBytes, 108, 7) ] ∧
    runDemandCallerLocationTrace (protoSites {} {}) {} protoLocState protoRetagLocalDecls
        protoLayouts [.normalStep ⟨.nop, "nop"⟩, .normalStep ⟨.nop, "nop"⟩] =
      ({}, [], runPlainTrace protoLocState protoRetagLocalDecls protoLayouts
        [.normalStep ⟨.nop, "nop"⟩, .normalStep ⟨.nop, "nop"⟩]) ∧
    (runEagerCallerLocationWorld (protoSites {} {}) protoLocState protoRetagLocalDecls protoLayouts
        [.normalStep ⟨.nop, "nop"⟩]).2.memory.globals.length =
      0 + 3 + (eagerInitCallerLocations (protoSites {} {}) protoLocState.memory).1.fileCache.length ∧
    AllocRenamingRel
      (renamingOfPtrs
        (runDemandCallerLocationTrace (protoSites {} {}) {} protoLocState protoRetagLocalDecls
          protoLayouts protoDistinctTrace).2.1
        (runEagerCallerLocationWorld (protoSites {} {}) protoLocState protoRetagLocalDecls
          protoLayouts protoDistinctTrace).1)
      (runDemandCallerLocationTrace (protoSites {} {}) {} protoLocState protoRetagLocalDecls
        protoLayouts protoDistinctTrace).2.2.memory
      (runEagerCallerLocationWorld (protoSites {} {}) protoLocState protoRetagLocalDecls
        protoLayouts protoDistinctTrace).2.memory
      (runDemandCallerLocationTrace (protoSites {} {}) {} protoLocState protoRetagLocalDecls
        protoLayouts protoDistinctTrace).2.1
      (runEagerCallerLocationWorld (protoSites {} {}) protoLocState protoRetagLocalDecls
        protoLayouts protoDistinctTrace).1 := by
  have h_bisim := demandCallerLocation_bisim_eager (protoSites {} {}) protoLocState
    protoRetagLocalDecls protoLayouts protoPanicTrace protoLocState_fresh (protoSites_fileLenOk {} {})
  have h_dist := demandCallerLocation_bisim_eager (protoSites {} {}) protoLocState
    protoRetagLocalDecls protoLayouts protoDistinctTrace protoLocState_fresh (protoSites_fileLenOk {} {})
  refine ⟨allLocationDetailPolicies_length,
    mem_allLocationDetailPolicies ⟨true, false, true⟩,
    applyLocationDetailPolicy_idempotent ⟨false, true, false⟩ protoUserCallerPos,
    resolveCallerLocationAux_eq_topDown [protoUnwrapFailedFrame {}, protoUnwrapFrame {}]
      (protoUserCallerFrame {}) [] {} protoUnwrapFailedPos rfl rfl,
    readU32Le_u32LeBytes 42 [],
    readU64Le_u64LeBytes (by decide) [],
    decodeInitBytes?_map_some protoLibRsBytes,
    lookupGlobalAlloc_append_left rfl,
    lookupGlobalAlloc_snoc_self [mkFilenameAllocation 1 protoLibRsBytes]
      (mkLocationAllocation 2 1 10 42 13)
      (fun a ha => by cases ha with | head => decide | tail _ h => nomatch h),
    readLocationFromGlobals_of_lookups (fileId := 1) rfl rfl (by decide),
    ?_,
    (demandCallerLocation_no_call_zero_allocs (protoSites {} {}) {} protoRetagLocalDecls protoLayouts
      [.normalStep ⟨.nop, "nop"⟩, .normalStep ⟨.nop, "nop"⟩] protoLocState rfl).1,
    (eagerCallerLocation_clutter (protoSites {} {}) protoLocState protoRetagLocalDecls protoLayouts
      [.normalStep ⟨.nop, "nop"⟩] rfl).2,
    allocRenamingRel_of_readLocations h_dist.1 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)⟩
  rw [h_bisim.2]
  decide +kernel

theorem protoLocState_borrowsFresh : BorrowsFresh protoLocState.memory := fun _ h => nomatch h

/-- Realistic borrow-monotone trace that interleaves `StorageLive`, scalar assignment, `&mut _2`
stack reference creation (`Rvalue.ref`), `Retag([fn entry] _1)` (minting a protected child borrow
tag before `caller_location`), `.invokeCallerLocation 2`, `Retag([default] _1)` (minting a fresh
stack borrow tag *after* `caller_location`), and `.invokeCallerLocation 0`. -/
def protoBorrowMonotoneTrace : List CallerLocationTraceEvent :=
  [ .normalStep ⟨.storageLive 2, "sl2"⟩,
    .normalStep ⟨.assign ⟨2, []⟩ (.use (protoU32Const 42)), "init2"⟩,
    .normalStep ⟨.assign ⟨1, []⟩ (.ref (.mut false) ⟨2, []⟩), "ref1"⟩,
    .normalStep protoFnEntryRetagStmt,
    .invokeCallerLocation 2,
    .normalStep protoDefaultRetagStmt,
    .invokeCallerLocation 0 ]

/-- Successor of `protoRetagMachineState` (which has a live stack borrow `tag = 1`) after
`protoFnEntryRetagStmt`. -/
def protoFnEntryRetagAfter : MachineState :=
  match evalStmt protoRetagMachineState protoFnEntryRetagStmt protoRetagLocalDecls protoLayouts with
  | .tau (.running ns) => ns
  | _ => protoRetagMachineState

/-- Plain state just before the first `caller_location` of `protoBorrowMonotoneTrace` (after
`StorageLive`, `_2 = 42`, `_1 = &mut _2`, and the fn-entry retag). -/
def protoBorrowTraceBeforeInvoke : MachineState :=
  runPlainTrace protoLocState protoRetagLocalDecls protoLayouts (protoBorrowMonotoneTrace.take 4)

/-- Why borrow-aware ids matter on `protoBorrowMonotoneTrace`: before the first `caller_location`,
`nextAllocId = 0` while the borrow tags `2, 1` minted by `&mut _2` and the retag are live. An
allocator drawing the filename and `Location` ids from `nextAllocId` alone would hand the `Location`
the id `1`, which `lookupBorrow` resolves to the live `&mut _2` borrow. `evalDemandCallerLocation`
draws from `max nextAllocId nextTag = 3` instead. -/
theorem test_partC_borrowAware_needed :
    protoBorrowTraceBeforeInvoke.memory.nextAllocId = 0 ∧
    protoBorrowTraceBeforeInvoke.memory.nextTag = 3 ∧
    protoBorrowTraceBeforeInvoke.memory.borrows.map BorrowEntry.tag = [2, 1] ∧
    (lookupBorrow protoBorrowTraceBeforeInvoke.memory.borrows
      (protoBorrowTraceBeforeInvoke.memory.nextAllocId + 1)).isSome = true ∧
    nextFreshGlobalAndTagId protoBorrowTraceBeforeInvoke.memory = 3 := by
  decide +kernel

/-- Closed witness for `evalStmt_borrowMonotone_frame`, `normalStmtStep_eq_raw_of_borrowMonotone`,
`runDemandCallerLocationTrace_borrowAware_spec`, and `demandCallerLocation_bisim_eager_borrowAware`
across all 8 `LocationDetailPolicy` combinations on `protoBorrowMonotoneTrace`. -/
theorem test_partC_borrowMonotone_and_trace_borrowAware :
    normalStmtStep protoRetagMachineState protoFnEntryRetagStmt protoRetagLocalDecls protoLayouts =
      protoFnEntryRetagAfter ∧
    readLocationsBorrowAware
        (runDemandCallerLocationTrace (protoSites {} {}) {} protoLocState protoRetagLocalDecls
          protoLayouts protoBorrowMonotoneTrace).2.2.memory
        (runDemandCallerLocationTrace (protoSites {} {}) {} protoLocState protoRetagLocalDecls
          protoLayouts protoBorrowMonotoneTrace).2.1 =
      [ some (protoLibRsBytes, 42, 13), some (protoLibRsBytes, 108, 7) ] ∧
    (∀ pol ∈ allLocationDetailPolicies,
      readLocationsBorrowAware
          (runDemandCallerLocationTrace (protoSites pol pol) {} protoLocState protoRetagLocalDecls
            protoLayouts protoBorrowMonotoneTrace).2.2.memory
          (runDemandCallerLocationTrace (protoSites pol pol) {} protoLocState protoRetagLocalDecls
            protoLayouts protoBorrowMonotoneTrace).2.1 =
        readLocationsBorrowAware
          (runEagerCallerLocationWorld (protoSites pol pol) protoLocState protoRetagLocalDecls
            protoLayouts protoBorrowMonotoneTrace).2.memory
          (runEagerCallerLocationWorld (protoSites pol pol) protoLocState protoRetagLocalDecls
            protoLayouts protoBorrowMonotoneTrace).1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [normalStmtStep_eq_raw_of_borrowMonotone _ _ _ _ rfl]
    rfl
  · have h_ba := (demandCallerLocation_bisim_eager_borrowAware (protoSites {} {}) protoLocState
      protoRetagLocalDecls protoLayouts protoBorrowMonotoneTrace (by decide +kernel)
      protoLocState_fresh protoLocState_borrowsFresh (protoSites_fileLenOk {} {})).2
    rw [h_ba]
    decide +kernel
  · intro pol _
    exact (demandCallerLocation_bisim_eager_borrowAware (protoSites pol pol) protoLocState
      protoRetagLocalDecls protoLayouts protoBorrowMonotoneTrace (by decide +kernel)
      protoLocState_fresh protoLocState_borrowsFresh (protoSites_fileLenOk pol pol)).1

def buildCandidateSites : Nat → List CallerLocationSite
  | 0 => []
  | k + 1 =>
    let pos : SourceExpansionPos := ⟨"src/lib.rs", protoLibRsBytes, UInt32.ofNat (k + 1), 5⟩
    ⟨pos, [protoUserCallerFrame {}]⟩ :: buildCandidateSites k

def candidateSites16 : List CallerLocationSite := buildCandidateSites 16
def candidateSites64 : List CallerLocationSite := buildCandidateSites 64
def candidateSites128 : List CallerLocationSite := buildCandidateSites 128

def nonPanickingTrace8 : List CallerLocationTraceEvent :=
  List.replicate 8 (.normalStep ⟨.nop, "nop"⟩)

def panickingTrace9 : List CallerLocationTraceEvent :=
  nonPanickingTrace8 ++ [.invokeCallerLocation 0]

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
  bench "PartC_eager_noPanic_S16" `(command|
    theorem bench_partC_eager_np_16 :
        (runEagerCallerLocationWorld candidateSites16 protoLocState protoRetagLocalDecls protoLayouts
          nonPanickingTrace8).2.memory.globals.length = 17 := by decide +kernel)
  bench "PartC_demand_noPanic_S16" `(command|
    theorem bench_partC_demand_np_16 :
        (runDemandCallerLocationTrace candidateSites16 {} protoLocState protoRetagLocalDecls
          protoLayouts nonPanickingTrace8).2.2.memory.globals.length = 0 := by decide +kernel)
  bench "PartC_eager_panic_S16" `(command|
    theorem bench_partC_eager_p_16 :
        (fun r => readLocations r.2.memory.globals r.1)
          (runEagerCallerLocationWorld candidateSites16 protoLocState protoRetagLocalDecls
            protoLayouts panickingTrace9) = [some (protoLibRsBytes, 16, 5)] := by decide +kernel)
  bench "PartC_demand_panic_S16" `(command|
    theorem bench_partC_demand_p_16 :
        (fun r => readLocations r.2.2.memory.globals r.2.1)
          (runDemandCallerLocationTrace candidateSites16 {} protoLocState protoRetagLocalDecls
            protoLayouts panickingTrace9) = [some (protoLibRsBytes, 16, 5)] := by decide +kernel)
  bench "PartC_eager_noPanic_S64" `(command|
    theorem bench_partC_eager_np_64 :
        (runEagerCallerLocationWorld candidateSites64 protoLocState protoRetagLocalDecls protoLayouts
          nonPanickingTrace8).2.memory.globals.length = 65 := by decide +kernel)
  bench "PartC_demand_noPanic_S64" `(command|
    theorem bench_partC_demand_np_64 :
        (runDemandCallerLocationTrace candidateSites64 {} protoLocState protoRetagLocalDecls
          protoLayouts nonPanickingTrace8).2.2.memory.globals.length = 0 := by decide +kernel)
  bench "PartC_eager_panic_S64" `(command|
    theorem bench_partC_eager_p_64 :
        (fun r => readLocations r.2.memory.globals r.1)
          (runEagerCallerLocationWorld candidateSites64 protoLocState protoRetagLocalDecls
            protoLayouts panickingTrace9) = [some (protoLibRsBytes, 64, 5)] := by decide +kernel)
  bench "PartC_demand_panic_S64" `(command|
    theorem bench_partC_demand_p_64 :
        (fun r => readLocations r.2.2.memory.globals r.2.1)
          (runDemandCallerLocationTrace candidateSites64 {} protoLocState protoRetagLocalDecls
            protoLayouts panickingTrace9) = [some (protoLibRsBytes, 64, 5)] := by decide +kernel)
  bench "PartC_eager_noPanic_S128" `(command|
    theorem bench_partC_eager_np_128 :
        (runEagerCallerLocationWorld candidateSites128 protoLocState protoRetagLocalDecls protoLayouts
          nonPanickingTrace8).2.memory.globals.length = 129 := by decide +kernel)
  bench "PartC_demand_noPanic_S128" `(command|
    theorem bench_partC_demand_np_128 :
        (runDemandCallerLocationTrace candidateSites128 {} protoLocState protoRetagLocalDecls
          protoLayouts nonPanickingTrace8).2.2.memory.globals.length = 0 := by decide +kernel)
  bench "PartC_eager_panic_S128" `(command|
    theorem bench_partC_eager_p_128 :
        (fun r => readLocations r.2.memory.globals r.1)
          (runEagerCallerLocationWorld candidateSites128 protoLocState protoRetagLocalDecls
            protoLayouts panickingTrace9) = [some (protoLibRsBytes, 128, 5)] := by decide +kernel)
  bench "PartC_demand_panic_S128" `(command|
    theorem bench_partC_demand_p_128 :
        (fun r => readLocations r.2.2.memory.globals r.2.1)
          (runDemandCallerLocationTrace candidateSites128 {} protoLocState protoRetagLocalDecls
            protoLayouts panickingTrace9) = [some (protoLibRsBytes, 128, 5)] := by decide +kernel)

/-! ## 6. Part D Witnesses & Scaling (`LazyWriteChain` & `bvShiftSafe` / `shiftLeftBitsSafe`) -/

def zeroEnv : Nat → Nat → Option Nat := fun _ _ => some 0

theorem test_partD_lazyWrite_and_shifts :
    evalSymArrayTerm zeroEnv (.constVec 8 0) 9 = none ∧
    symArrayLen (mkLazyWrite 8 (.constVec 8 0) 2 99) = 8 ∧
    evalSymArrayTerm zeroEnv (mkLazyWrite 8 (.constVec 8 0) 2 99) 3 =
      evalSymArrayTerm zeroEnv (.write (.constVec 8 0) 2 99) 3 ∧
    evalSymArrayTerm zeroEnv (mkEagerWrite 8 (.write (.constVec 8 0) 2 99) 2 7) 2 =
      evalSymArrayTerm zeroEnv (.write (.write (.constVec 8 0) 2 99) 2 7) 2 ∧
    evalSymArrayTerm zeroEnv (.write (.constVec 8 0) 9 5) 3 =
      evalSymArrayTerm zeroEnv (.constVec 8 0) 3 ∧
    symArrayLen (stripShadowedWrites (.write (.constVec 8 0) 2 99) 2) = 8 ∧
    evalSymArrayTerm zeroEnv (stripShadowedWrites (.write (.constVec 8 0) 2 99) 2) 3 =
      evalSymArrayTerm zeroEnv (.write (.constVec 8 0) 2 99) 3 ∧
    evalSymArrayTerm zeroEnv (mkLazyWrite 8 (.constVec 8 0) 2 99) 2 = some 99 ∧
    (mkLazyWriteCounted 8 (.constVec 8 0) 2 99).1 = mkLazyWrite 8 (.constVec 8 0) 2 99 ∧
    (stripShadowedWritesCounted (.write (.write (.constVec 8 0) 1 5) 2 6) 3).2 = 3 ∧
    (eagerDistinctChainCounted 16 16).1 = buildEagerDistinctChain 16 16 ∧
    (lazyDistinctChainCounted 16 16).2 = 16 ∧
    2 * (eagerDistinctChainCounted 16 16).2 = 16 * 17 ∧
    buildLazyDistinctChain 16 16 = buildEagerDistinctChain 16 16 ∧
    symArrayLen (buildLazyDistinctChain 16 16) = 16 ∧
    bvShlSafe (0x12345678#32) 64 = (0x12345678#32) <<< 64 ∧
    bvLshrSafe (0x12345678#32) 64 = (0x12345678#32) >>> 64 ∧
    bvAshrSafe (0x80000000#32) 64 = BitVec.sshiftRight (0x80000000#32) 64 ∧
    shiftLeftBitsSafe 0x12345678 64 4 = shiftLeftBits 0x12345678 64 (scalarModulus 4) ∧
    shiftRightUnsignedBitsSafe 0x12345678 64 4 = shiftRightUnsignedBits 0x12345678 64 ∧
    arithmeticShrBitsSafe 0x80000000 4 64 = arithmeticShrBits 0x80000000 4 64 := by
  refine ⟨evalSymArrayTerm_oob zeroEnv (.constVec 8 0) 9 (by decide),
    symArrayLen_mkLazyWrite 8 (.constVec 8 0) 2 99,
    eval_mkLazyWrite zeroEnv (.constVec 8 0) rfl 2 99 3,
    eval_mkEagerWrite zeroEnv (.write (.constVec 8 0) 2 99) rfl 2 7 2,
    eval_write_oob zeroEnv (.constVec 8 0) 9 5 3 (by decide),
    symArrayLen_stripShadowedWrites (.write (.constVec 8 0) 2 99) 2,
    eval_stripShadowedWrites_ne zeroEnv (.write (.constVec 8 0) 2 99) 2 3 rfl,
    eval_mkLazyRead zeroEnv (mkLazyWrite 8 (.constVec 8 0) 2 99) rfl 2 99 rfl,
    mkLazyWriteCounted_fst 8 (.constVec 8 0) 2 99,
    by rw [stripShadowedWritesCounted_snd]; rfl,
    eagerDistinctChainCounted_fst 16 16,
    lazyWriteChain_distinctAddrs_steps_eq_N (Nat.le_refl 16),
    eagerWriteChain_distinctAddrs_steps_quadratic (Nat.le_refl 16),
    buildLazyDistinctChain_eq_eager (Nat.le_refl 16),
    symArrayLen_buildLazyDistinctChain 16 16,
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
        (eagerDistinctChainCounted 128 16).2 = 136 ∧
        mkLazyRead 128 (eagerDistinctChainCounted 128 16).1 15 = some 16 := by decide +kernel)
  bench "PartD_lazyWrite_N16" `(command|
    theorem bench_partD_lazy_16 :
        (lazyDistinctChainCounted 128 16).2 = 16 ∧
        mkLazyRead 128 (lazyDistinctChainCounted 128 16).1 15 = some 16 := by decide +kernel)
  bench "PartD_eagerWrite_N64" `(command|
    theorem bench_partD_eager_64 :
        (eagerDistinctChainCounted 128 64).2 = 2080 ∧
        mkLazyRead 128 (eagerDistinctChainCounted 128 64).1 63 = some 64 := by decide +kernel)
  bench "PartD_lazyWrite_N64" `(command|
    theorem bench_partD_lazy_64 :
        (lazyDistinctChainCounted 128 64).2 = 64 ∧
        mkLazyRead 128 (lazyDistinctChainCounted 128 64).1 63 = some 64 := by decide +kernel)
  bench "PartD_eagerWrite_N128" `(command|
    theorem bench_partD_eager_128 :
        (eagerDistinctChainCounted 128 128).2 = 8256 ∧
        mkLazyRead 128 (eagerDistinctChainCounted 128 128).1 127 = some 128 := by decide +kernel)
  bench "PartD_lazyWrite_N128" `(command|
    theorem bench_partD_lazy_128 :
        (lazyDistinctChainCounted 128 128).2 = 128 ∧
        mkLazyRead 128 (lazyDistinctChainCounted 128 128).1 127 = some 128 := by decide +kernel)
  bench "PartD_wideShift_2pow64" `(command|
    theorem bench_partD_wideShift_2pow64 :
        shiftLeftBitsSafe 0xdeadbeef wideShiftTwoPow64 4 = 0 ∧
        shiftRightUnsignedBitsSafe 0xdeadbeef wideShiftTwoPow64 4 = 0 ∧
        arithmeticShrBitsSafe 0x80000000 4 wideShiftTwoPow64 = 0xffffffff ∧
        bvShlSafe (0xdeadbeef#32) wideShiftTwoPow64 = 0#32 ∧
        bvLshrSafe (0xdeadbeef#32) wideShiftTwoPow64 = 0#32 ∧
        bvAshrSafe (0x80000000#32) wideShiftTwoPow64 = 0xffffffff#32 := by
      decide +kernel)

/-! ## 7. Bottom-of-File Kernel Axiom, Namespace Hygiene, Placeholder, & Reachability Audit -/

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
  let mut auditedThmSet : NameSet := {}
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
              last == "eq" || last == "_arg_pusher" || last.startsWith "_proof_" ||
              last.startsWith "_simp_"
          unless un.hasMacroScopes || isAutoAux do
            theorems := theorems + 1
            auditedThms := auditedThms.push n
            auditedThmSet := auditedThmSet.insert n
      else
        let last := un.eraseMacroScopes.getString!
        let isRealizedEq :=
          last == "eq_def" || last == "splitter" || last == "else_eq" ||
            last.startsWith "eq_" || last.startsWith "_sparseCasesOn_"
        unless un.hasMacroScopes || isRealizedEq do
          leaked := leaked.push un
  unless leaked.isEmpty do
    throwError "leaked constants outside {protoMod}: {leaked}"
  -- Placeholder detector: a `have _ := @thm` (elaborated as `let`/`letFun`) whose value is a bare
  -- prototype theorem and whose body never uses the bound variable instantiates nothing.
  let isPlaceholder (e : Expr) : Bool :=
    match e with
    | .letE _ _ v b _ =>
      (match v.getAppFn.constName? with
        | some c => auditedThmSet.contains c && !b.hasLooseBVar 0
        | none => false)
    | _ =>
      if e.isAppOfArity ``letFun 4 then
        let v := e.getArg! 2
        let f := e.getArg! 3
        match v.getAppFn.constName?, f with
        | some c, .lam _ _ b _ => auditedThmSet.contains c && !b.hasLooseBVar 0
        | _, _ => false
      else
        false
  -- Detector self-test: an elaborated `have _ := @thm` placeholder must be caught.
  let probe ← liftTermElabM do
    let stx ← `(term| (by
      have _ := @$(mkIdent ``Anneal.SparseRetagAndVcNarrowPrototype.nat_beq_self)
      exact True.intro : True))
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  unless (probe.find? isPlaceholder).isSome do
    throwError "placeholder detector self-test failed on {probe}"
  -- Conditional-test detector: a test theorem whose statement assumes a Prop hypothesis (other than
  -- a bounded-quantifier membership `x ∈ l`) may instantiate prototype theorems vacuously, so such
  -- theorems only count toward reachability if a closed test witness applies them.
  let isConditionalThm (ci : ConstantInfo) : CommandElabM Bool := do
    match ci with
    | .thmInfo _ =>
      liftTermElabM <| Meta.forallTelescope ci.type fun xs _ => do
        let mut cond := false
        for x in xs do
          let ty ← Meta.inferType x
          if (← Meta.isProp ty) && !ty.isAppOf ``Membership.mem then
            cond := true
        return cond
    | _ => return false
  let probeCond ← liftTermElabM do
    let stx ← `(term| ∀ (n : Nat), n = 3 → n + 1 = 4)
    let ty ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    Meta.forallTelescope ty fun xs _ => xs.anyM fun x => do
      let t ← Meta.inferType x
      return (← Meta.isProp t) && !t.isAppOf ``Membership.mem
  unless probeCond do
    throwError "conditional-test detector self-test failed"
  let mut testSet : NameSet := {}
  for (n, _) in env.constants.map₂.toList do
    if testPfx.isPrefixOf n then
      testSet := testSet.insert n
  let mut placeholders : Array Name := #[]
  let mut conditionals : Array Name := #[]
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
      if let some v := ci.value? then
        if (v.find? isPlaceholder).isSome then
          placeholders := placeholders.push n
      if ← isConditionalThm ci then
        conditionals := conditionals.push n
      else
        -- closed test witnesses (and test definitions) are the reachability roots
        for c in ci.getUsedConstantsAsSet do
          if (auditedSet.contains c || testSet.contains c) && !reached.contains c then
            reached := reached.insert c
            work := work.push c
  unless placeholders.isEmpty do
    throwError "placeholder-only prototype theorem uses (`have _ := @thm`) in: {placeholders.toList}"
  while !work.isEmpty do
    let c := work.back!
    work := work.pop
    if let some ci := env.find? c then
      for d in ci.getUsedConstantsAsSet do
        if (auditedSet.contains d || testSet.contains d) && !reached.contains d then
          reached := reached.insert d
          work := work.push d
  let undischarged := conditionals.filter (fun n => !reached.contains n)
  unless undischarged.isEmpty do
    throwError "conditional test theorems never applied by a closed test witness: {undischarged.toList}"
  let unreached := auditedThms.filter (fun n => !reached.contains n)
  unless unreached.isEmpty do
    throwError "prototype theorems not instantiated/reached by any closed test witness: {unreached.toList}"
  logInfo m!"axiom audit passed: {audited} declarations ({theorems} prototype theorems, 0 unsafe, 0 Classical.choice, 0 Lean.ofReduceBool, 0 leaked constants, 0 placeholder uses, {conditionals.size} conditional test lemmas all discharged, 100% theorem reachability from closed test witnesses)"

end Anneal.SparseRetagAndVcNarrowProtoTests
