/-
Copyright 2026 The Fuchsia Authors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Lean
import Anneal.ExactWpAndSmartCtors
import Anneal.MiriTreeBorrowsV2026
import LeanMiriSpec.MemoryLemmas
import LeanMiriSpec.ExactWpAndMemoryFrameLM
import LeanMiriSpec.Correspondence.Translate
import Miri.Interpreter.CallDispatchMachine
import Miri.Interpreter.PlaceMachine
import Miri.Interpreter.MemoryErrors
import Miri.Memory.AllocAddresses.GlobalState

/-!
# Episode 1 LeanMiri Bridge: Initial-State Tree Borrows, Instruction, Call-Dispatch & Memory-Observation `ExactWP` (`LeanMiriSpec.InitialStateTreeBorrowsWpLM`)

Extends `LeanMiriSpec.ExactWpAndMemoryFrameLM` with `Std.Do`-free compositional initial-state
weakest preconditions mirroring `proofs-rs/lean-miri#94` (`miri_tree_range_wp`,
`miri_instruction_wp`, `miri_call_dispatch_wp`, `miri_observe_memory`) over unmodified vendored
`Miri.*`, bridged directly to `Anneal.MiriTreeBorrowsV2026`, `Trusted.Rustc.V2026_06_01.MirSemantics`,
and `LeanMiriSpec.Correspondence.translateBody`-lowered `CapturedMir` bodies — with ZERO
`MiniRustSpec.*` imports and ZERO `Std.Do` / `Std.Tactic.Do` / `Std.WP` usage:

1. **§1 (Compositional Initial-State Tree Borrows Range WP — `miriTreeRangeExactWP_iff`)**:
   - Exact bidirectional `↔` `AnnealExactWP` for `BorrowTree.newChild` (`miriTreeNewChildExactWP_iff`),
     multi-child initial-state setup from `BorrowTree.new` (`miriTreeInitialSetupExactWP_iff`),
     multi-location `BorrowTree.performBorrowAccessRange` (`miriTreeRangeExactWP_iff`,
     `miriTreeInitAndRangeExactWP_iff`, `miriTreeRangeSymbolicExactWP_iff`), sequencing / chaining
     (`miriTreeRangeSeqExactWP_iff`, `miriTreeRangeChainExactWP_iff`), and protector release +
     `ProtectedTags` teardown (`miriTreeRangeThenReleaseExactWP_iff`).
   - Topology framing (`miriTreeRange_preserves_topology`), missing-tag framing, disjoint
     `ProtectedTags` framing (`miriProtectedTags_insert_ne`, `miriProtectedTags_remove_ne`,
     `miriEndCall_preserves_unlisted_protector`), plus concrete disjoint-range frame preservation
     and committed-prefix error witnesses.
2. **§2 (Initial-State Instruction & Call-Dispatch WP — `miriInstructionExactWP_iff`,
   `miriCallDispatchExactWP_iff`)**:
   - Exact bidirectional `↔` `AnnealExactWP` for `Miri.Interpreter.Step.evalStatement` across all
     MIR statement kinds (`.Assign`, `.SetDiscriminant`, `.StorageLive`, `.StorageDead`,
     `.Intrinsic`, `.PlaceMention`, `.ConstEvalCounter`, `.Nop`/no-ops), plus `Step.step`
     statement-advance framing (`miriStepStmtExactWP_iff`).
   - Exact bidirectional `↔` `AnnealExactWP` for `Miri.Interpreter.CallDispatchMachine.findMirOrEvalFn`
     (`miriCallDispatchExactWP_iff`), `CallDispatchMachine.callExtra` (`miriCallExtraExactWP_iff`),
     and `ControlFlow.evalTerminator` / `Step.step` `.Call` terminator dispatch
     (`miriCallTerminatorExactWP_iff`, `miriStepCallTerminatorExactWP_iff`).
3. **§3 (Initial-State Read-Only Memory Observation WP — `miriObserveMemoryExactWP_iff`)**:
   - Exact bidirectional `↔` `AnnealExactWP` for read-only scalar (`Allocation.readScalar`),
     provenance-stripping byte (`Allocation.getBytesStripProvenance`), raw byte
     (`Allocation.getBytesUnchecked`), and full machine+borrow-tree observation
     (`MiriObservedState`), proving strict state immutability (`s' = s` on both `.ok` and `.error`)
     and clean composition with `miriTreeRangeExactWP_iff`, `miriInstructionExactWP_iff`, and
     `miriCallDispatchExactWP_iff`.
4. **§4 (Cross-Layer Correspondence `Anneal.MiriTreeBorrowsV2026` ↔ Vendored `Miri.TreeBorrows`
   ↔ `V2026_06_01` ↔ `translateBody`-Lowered `CapturedMir` + Positive & Negative `↔` Witnesses)**:
   - Exact 6-state bijection, 56-cell transition correspondence, `associatedAccess` / SIFA /
     `permissionLE` / `skipIfKnownNoop` / `LocationState.performAccess` / deallocation-guard
     correspondence, and full 3-way triangle `MiriTreeBorrowsV2026 ↔ V2026_06_01 ↔ Miri.TreeBorrows`.
   - Concrete positive executions AND bidirectional `↔` negative UB refutations across
     `translateBody`-lowered `CapturedMir`, `BorrowTree`, `Allocation`, and `CallDispatchMachine`.
   - §4.2: Tree Borrows UB (protected two-phase conflict write, frozen local write) on REAL
     `V2026_06_01` `CapturedMir` bodies reached by real `stepMirFn` steps from a concrete initial
     state, with exact per-cell agreement `treeBorrowNodeAccess` ↔ `miriPerformLocAccess` ↔
     vendored `Miri.TreeBorrows.performAccess`.
5. **§5 (Capstone & Silent Import-Isolation / Bridge-Reality / 3-Axiom Audit)**.

**Precise import-isolation guarantee (checked by the §5 `run_cmd`).** On toolchain
`v4.34.1`, the Lean/Std toolchain libraries themselves load `Std.Do.*` / `Std.Tactic.Do.*`
(`Std` imports `Std.Do`; `Lean.Meta.Sym.Pattern` / `Lean.Parser.Tactic` import
`Std.Do.Triple.Basic` / `Std.Tactic.Do.Syntax`), and unmodified vendored `Miri.*` imports `Std`
and `Lean` (e.g. `Miri.ABI.Size`, `Miri.DataStructures.DedupRangeMap`). A module importing vendored
`Miri.*` therefore CANNOT avoid having `Std.Do` modules in its environment header. The §5 audit
enforces the strongest achievable form of isolation instead:
- (a) this module directly imports no `Std.Do` / `Std.Tactic.Do` / `Std.WP` / `MiniRustSpec` module,
  and no `MiniRustSpec.*` module is loaded transitively at all;
- (b) toolchain containment: EVERY loaded module that directly imports a `Std.Do` / `Std.Tactic.Do` /
  `Std.WP` module is itself a toolchain module (`Init.*` / `Std.*` / `Lean.*`) — no project, vendored,
  or third-party module bridges into `Std.Do`;
- (c) `Anneal.MiriTreeBorrowsV2026`'s full transitive import closure contains ZERO `Std.Do`, `Lean`,
  `Miri`, `LeanMiriSpec`, or `MiniRustSpec` modules;
- (d) the full transitive CONSTANT-dependency closure (types AND values, through vendored `Miri.*`,
  `Trusted.*`, and the core library) of every declaration of this module contains ZERO `Std.Do.*`,
  `Std.Tactic.Do.*`, `Std.WP.*`, or `MiniRustSpec.*` constants.
-/

namespace LeanMiriSpec.InitialStateTreeBorrowsWpLM

set_option Elab.async false
set_option autoImplicit false

open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.DataStructures Miri.Interpreter
open Anneal.ExactWpAndSmartCtors
open Anneal.MiriTreeBorrowsV2026
open LeanMiriSpec.ExactWpAndMemoryFrameLM
open LeanMiriSpec.Correspondence
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics (emptyLayoutTable)

/-! ## §0. Kernel Definitional Reduction Helper (Zero `native_decide`) -/

/-- Close an equality goal via kernel definitional reduction (zero `Lean.ofReduceBool`). -/
local elab "kernel_rfl" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let tgt ← Lean.MVarId.getType' mvarId
  let some (ty, lhs, _) := tgt.eq?
    | Lean.Meta.throwTacticEx `kernel_rfl mvarId "expected equality goal"
  let u ← Lean.Meta.getLevel ty
  mvarId.assign (Lean.mkApp2 (Lean.mkConst ``Eq.refl [u]) ty lhs)
  Lean.Elab.Tactic.replaceMainGoal []

/-- Definitionally unfold private helper lemmas in `Miri.TreeBorrows.MachineMemoryHooks`
(purely definitional `replaceTargetDefEq`; zero extra axioms). -/
local elab "unfold_mmh" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let tgt ← g.getType
  let tgt' ← Lean.Meta.deltaExpand tgt (fun n =>
    n.toString.startsWith "_private.Miri.TreeBorrows.MachineMemoryHooks.")
  let g' ← g.replaceTargetDefEq tgt'
  Lean.Elab.Tactic.replaceMainGoal [g']

/-- Definitionally unfold private helper lemmas in vendored `PlaceMachine`, `MachineHooks`,
and `Rvalue` (excluding compiler `.match_` auxiliaries; zero extra axioms). -/
local elab "unfold_pm" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let tgt ← g.getType
  let tgt' ← Lean.Meta.deltaExpand tgt (fun n =>
    let s := n.toString
    !n.components.any (fun c => c.toString.startsWith "match_") &&
    (s.startsWith "_private.Miri.Interpreter.PlaceMachine." ||
     s.startsWith "_private.Miri.Interpreter.MachineHooks." ||
     s.startsWith "_private.Miri.Interpreter.Rvalue."))
  let g' ← g.replaceTargetDefEq tgt'
  Lean.Elab.Tactic.replaceMainGoal [g']

/-- Definitionally unfold private helper `AllocationAccess.getPtrAllocation` only
(excluding compiler `.match_` auxiliaries). -/
local elab "unfold_aa" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let tgt ← g.getType
  let tgt' ← Lean.Meta.deltaExpand tgt (fun n =>
    !n.components.any (fun c => c.toString.startsWith "match_") &&
    n.toString.startsWith "_private.Miri.Memory.AllocationAccess.")
  let g' ← g.replaceTargetDefEq tgt'
  Lean.Elab.Tactic.replaceMainGoal [g']

/-- Definitionally unfold private helpers in `Miri.Interpreter.MemoryOperand` only
(excluding compiler `.match_` auxiliaries). -/
local elab "unfold_mo" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let tgt ← g.getType
  let tgt' ← Lean.Meta.deltaExpand tgt (fun n =>
    !n.components.any (fun c => c.toString.startsWith "match_") &&
    n.toString.startsWith "_private.Miri.Interpreter.MemoryOperand.")
  let g' ← g.replaceTargetDefEq tgt'
  Lean.Elab.Tactic.replaceMainGoal [g']

/-- Definitionally unfold private helpers in `Miri.Interpreter.MachineHooks` only
(excluding compiler `.match_` auxiliaries). -/
local elab "unfold_mh" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let tgt ← g.getType
  let tgt' ← Lean.Meta.deltaExpand tgt (fun n =>
    !n.components.any (fun c => c.toString.startsWith "match_") &&
    n.toString.startsWith "_private.Miri.Interpreter.MachineHooks.")
  let g' ← g.replaceTargetDefEq tgt'
  Lean.Elab.Tactic.replaceMainGoal [g']

/-- Definitionally unfold private helpers in `Miri.Interpreter.Place` only
(excluding compiler `.match_` auxiliaries). -/
local elab "unfold_pl" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let tgt ← g.getType
  let tgt' ← Lean.Meta.deltaExpand tgt (fun n =>
    !n.components.any (fun c => c.toString.startsWith "match_") &&
    n.toString.startsWith "_private.Miri.Interpreter.Place.")
  let g' ← g.replaceTargetDefEq tgt'
  Lean.Elab.Tactic.replaceMainGoal [g']

/-! ## §1. Compositional Initial-State Tree Borrows Range WP (`miriTreeRangeExactWP_iff`) -/

section InitialStateTreeRangeWP

/-- Child insertion specification for building initial `BorrowTree` states from `BorrowTree.new`. -/
structure MiriChildInitSpec : Type where
  baseOffset : Size
  parentProvenance : ProvenanceExtra
  newTag : BorTag
  insidePermissions : DedupRangeMap Tree.LocationState
  outsidePermission : Permission
  isProtected : Bool

/-- State-retaining `ExactAction` wrapping unmodified `Miri.TreeBorrows.BorrowTree.newChild`
(retaining `result.tree` on BOTH `.ok ()` and `.error err`). -/
def miriTreeNewChildAction (spec : MiriChildInitSpec) :
    ExactAction BorrowTree BorrowTree.ChildInsertError Unit :=
  fun tree =>
    let res := tree.newChild spec.baseOffset spec.parentProvenance spec.newTag
      spec.insidePermissions spec.outsidePermission spec.isProtected
    match res.outcome with
    | .ok () => .ok () res.tree
    | .error err => .error err res.tree

/-- Exact symbolic precondition for `BorrowTree.newChild`. -/
def miriTreeNewChildPre (spec : MiriChildInitSpec)
    (post : Unit → BorrowTree → Prop)
    (onError : BorrowTree.ChildInsertError → BorrowTree → Prop)
    (tree : BorrowTree) : Prop :=
  let res := tree.newChild spec.baseOffset spec.parentProvenance spec.newTag
    spec.insidePermissions spec.outsidePermission spec.isProtected
  match res.outcome with
  | .ok () => post () res.tree
  | .error err => onError err res.tree

/-- **Exact bidirectional `↔` theorem `miriTreeNewChildExactWP_iff`** for unmodified
`Miri.TreeBorrows.BorrowTree.newChild`. -/
theorem miriTreeNewChildExactWP_iff (spec : MiriChildInitSpec)
    (post : Unit → BorrowTree → Prop)
    (onError : BorrowTree.ChildInsertError → BorrowTree → Prop)
    (tree : BorrowTree) :
    AnnealExactWP (miriTreeNewChildAction spec) post onError tree ↔
      miriTreeNewChildPre spec post onError tree := by
  unfold AnnealExactWP miriTreeNewChildAction miriTreeNewChildPre
  dsimp only
  cases (tree.newChild spec.baseOffset spec.parentProvenance spec.newTag
    spec.insidePermissions spec.outsidePermission spec.isProtected).outcome with
  | ok u => cases u; rfl
  | error e => rfl

/-- Multi-child initial-state tree setup `ExactAction` threading `BorrowTree.newChild` across a
list of `MiriChildInitSpec`s. -/
def miriTreeInitialSetupAction (children : List MiriChildInitSpec) :
    ExactAction BorrowTree BorrowTree.ChildInsertError Unit :=
  ExactAction.foldl (fun _ spec => miriTreeNewChildAction spec) () children

/-- **Exact bidirectional `↔` theorem `miriTreeInitialSetupExactWP_iff`**: characterizes
constructing a multi-child `BorrowTree` starting from `BorrowTree.new rootTag size`! -/
theorem miriTreeInitialSetupExactWP_iff (rootTag : BorTag) (size : Size)
    (children : List MiriChildInitSpec)
    (post : Unit → BorrowTree → Prop)
    (onError : BorrowTree.ChildInsertError → BorrowTree → Prop) :
    AnnealExactWP (miriTreeInitialSetupAction children) post onError (BorrowTree.new rootTag size) ↔
      exactFoldWP (fun _ spec => miriTreeNewChildAction spec) post onError () children
        (BorrowTree.new rootTag size) :=
  exactWP_foldl (fun _ spec => miriTreeNewChildAction spec) post onError () children
    (BorrowTree.new rootTag size)

/-- Error sum for combined initial-state setup + ranged access + protector release pipelines. -/
inductive MiriTreePipelineError : Type where
  | childInsert (err : BorrowTree.ChildInsertError) : MiriTreePipelineError
  | access (status : BorrowTree.BorrowTreeAccessStatus)
      (visited : Array BorrowTree.BorrowTreeLocationResult) : MiriTreePipelineError
  | protectorRelease (status : BorrowTree.ProtectorReleaseStatus) : MiriTreePipelineError
  deriving DecidableEq, Repr

/-- Lift an `ExactAction` error type via `f : E₁ → E₂`. -/
def mapExactActionErr {S E₁ E₂ A : Type} (f : E₁ → E₂) (act : ExactAction S E₁ A) :
    ExactAction S E₂ A :=
  fun s =>
    match act s with
    | .ok a s' => .ok a s'
    | .error e s' => .error (f e) s'

theorem exactWP_mapErr {S E₁ E₂ A : Type} (f : E₁ → E₂) (act : ExactAction S E₁ A)
    (post : A → S → Prop) (onError : E₂ → S → Prop) (s : S) :
    AnnealExactWP (mapExactActionErr f act) post onError s ↔
      AnnealExactWP act post (fun e s' => onError (f e) s') s := by
  unfold AnnealExactWP mapExactActionErr
  cases act s <;> rfl

/-- Initial-state Tree Borrows range access `ExactAction` wrapping unmodified
`Miri.TreeBorrows.BorrowTree.performBorrowAccessRange` (mirroring `lean-miri#94`
`miri_tree_range_wp`). -/
abbrev miriTreeRangeAction (provenance : ProvenanceExtra) (offset length : Size)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) :
    ExactAction BorrowTree
      (BorrowTree.BorrowTreeAccessStatus × Array BorrowTree.BorrowTreeLocationResult)
      (Array BorrowTree.BorrowTreeLocationResult) :=
  tbAccessAction provenance offset length kind tags mode

/-- **Exact bidirectional `↔` theorem `miriTreeRangeExactWP_iff`** (mirroring `lean-miri#94`'s
`miri_tree_range_wp`): exact two-continuation WP for multi-location
`Miri.TreeBorrows.BorrowTree.performBorrowAccessRange` from any initial `BorrowTree`, exposing both
the exact committed post-tree `result.tree` and diagnostic `result.locations` on `.Completed` and
on error! -/
theorem miriTreeRangeExactWP_iff (provenance : ProvenanceExtra) (offset length : Size)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (post : Array BorrowTree.BorrowTreeLocationResult → BorrowTree → Prop)
    (onError : (BorrowTree.BorrowTreeAccessStatus × Array BorrowTree.BorrowTreeLocationResult) →
      BorrowTree → Prop)
    (tree : BorrowTree) :
    AnnealExactWP (miriTreeRangeAction provenance offset length kind tags mode) post onError tree ↔
      tbAccessPre tree provenance offset length kind tags mode post onError :=
  tbAccessExactWP_iff provenance offset length kind tags mode post onError tree

/-- Unconditional per-cursor symbolic `↔` refinement of `miriTreeRangeExactWP_iff` over
`List.range' 0 prepared.positions.size`. -/
theorem miriTreeRangeSymbolicExactWP_iff (provenance : ProvenanceExtra) (offset length : Size)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (post : Array BorrowTree.BorrowTreeLocationResult → BorrowTree → Prop)
    (onError : (BorrowTree.BorrowTreeAccessStatus × Array BorrowTree.BorrowTreeLocationResult) →
      BorrowTree → Prop)
    (tree : BorrowTree) :
    AnnealExactWP (miriTreeRangeAction provenance offset length kind tags mode) post onError tree ↔
      tbAccessSymbolicPre provenance offset length kind tags mode post onError tree :=
  tbAccessSymbolicPre_iff provenance offset length kind tags mode post onError tree

/-- **Compositional initial-state setup + ranged access WP (`miriTreeInitAndRangeExactWP_iff`)**:
starting from fresh `BorrowTree.new rootTag size`, inserts `children` via `BorrowTree.newChild`
and then performs `BorrowTree.performBorrowAccessRange`! -/
theorem miriTreeInitAndRangeExactWP_iff (rootTag : BorTag) (size : Size)
    (children : List MiriChildInitSpec)
    (provenance : ProvenanceExtra) (offset length : Size)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (post : Array BorrowTree.BorrowTreeLocationResult → BorrowTree → Prop)
    (onError : MiriTreePipelineError → BorrowTree → Prop) :
    AnnealExactWP
      (ExactAction.seq
        (mapExactActionErr MiriTreePipelineError.childInsert (miriTreeInitialSetupAction children))
        (mapExactActionErr (fun p => MiriTreePipelineError.access p.1 p.2)
          (miriTreeRangeAction provenance offset length kind tags mode)))
      post onError (BorrowTree.new rootTag size) ↔
      exactFoldWP (fun _ spec => miriTreeNewChildAction spec)
        (fun _ builtTree =>
          tbAccessSymbolicPre provenance offset length kind tags mode post
            (fun errPair t' => onError (.access errPair.1 errPair.2) t') builtTree)
        (fun err t' => onError (.childInsert err) t') () children
        (BorrowTree.new rootTag size) := by
  rw [exactWP_seq, exactWP_mapErr, miriTreeInitialSetupExactWP_iff]
  have hCongr :
      ∀ (cs : List MiriChildInitSpec) (t : BorrowTree),
        exactFoldWP (fun _ spec => miriTreeNewChildAction spec)
          (fun _ builtTree =>
            AnnealExactWP
              (mapExactActionErr (fun p => MiriTreePipelineError.access p.1 p.2)
                (miriTreeRangeAction provenance offset length kind tags mode))
              post onError builtTree)
          (fun err t' => onError (.childInsert err) t') () cs t ↔
        exactFoldWP (fun _ spec => miriTreeNewChildAction spec)
          (fun _ builtTree =>
            tbAccessSymbolicPre provenance offset length kind tags mode post
              (fun errPair t' => onError (.access errPair.1 errPair.2) t') builtTree)
          (fun err t' => onError (.childInsert err) t') () cs t := by
    intro cs
    induction cs with
    | nil =>
      intro t
      unfold exactFoldWP
      rw [exactWP_mapErr, miriTreeRangeSymbolicExactWP_iff]
    | cons c cs ih =>
      intro t
      unfold exactFoldWP
      constructor
      · exact exactWP_consequence (fun u t' h => by cases u; exact (ih t').mp h) (fun _ _ h => h)
      · exact exactWP_consequence (fun u t' h => by cases u; exact (ih t').mpr h) (fun _ _ h => h)
  exact hCongr children (BorrowTree.new rootTag size)

/-- **Compositional two-access sequencing law (`miriTreeRangeSeqExactWP_iff`)**:
chaining two `BorrowTree.performBorrowAccessRange` calls via `ExactAction.bind` is exact (`↔`)! -/
theorem miriTreeRangeSeqExactWP_iff
    (prov₁ : ProvenanceExtra) (off₁ len₁ : Size) (kind₁ : AccessKind)
    (tags₁ : ProtectedTags) (mode₁ : Tree.ChildrenVisitMode)
    (prov₂ : ProvenanceExtra) (off₂ len₂ : Size) (kind₂ : AccessKind)
    (tags₂ : ProtectedTags) (mode₂ : Tree.ChildrenVisitMode)
    (post : Array BorrowTree.BorrowTreeLocationResult →
      Array BorrowTree.BorrowTreeLocationResult → BorrowTree → Prop)
    (onError : (BorrowTree.BorrowTreeAccessStatus × Array BorrowTree.BorrowTreeLocationResult) →
      BorrowTree → Prop)
    (tree : BorrowTree) :
    AnnealExactWP
      (ExactAction.bind (miriTreeRangeAction prov₁ off₁ len₁ kind₁ tags₁ mode₁)
        (fun locs₁ =>
          ExactAction.map (fun locs₂ => (locs₁, locs₂))
            (miriTreeRangeAction prov₂ off₂ len₂ kind₂ tags₂ mode₂)))
      (fun pair t' => post pair.1 pair.2 t') onError tree ↔
      tbAccessPre tree prov₁ off₁ len₁ kind₁ tags₁ mode₁
        (fun locs₁ midTree =>
          tbAccessPre midTree prov₂ off₂ len₂ kind₂ tags₂ mode₂
            (fun locs₂ finalTree => post locs₁ locs₂ finalTree) onError)
        onError := by
  rw [exactWP_bind, miriTreeRangeExactWP_iff]
  unfold tbAccessPre
  dsimp only
  generalize tree.performBorrowAccessRange prov₁ off₁ len₁ kind₁ tags₁ mode₁ = res₁
  cases res₁.status with
  | Completed =>
    dsimp only
    rw [exactWP_map, miriTreeRangeExactWP_iff]
    exact Iff.rfl
  | _ => exact Iff.rfl

/-- **Multi-access chain WP (`miriTreeRangeChainExactWP_iff`)**:
arbitrary lists of ranged accesses compose cleanly via `Anneal.ExactWpAndSmartCtors.TreeBorrowsFrameWP`! -/
theorem miriTreeRangeChainExactWP_iff
    (steps : List (ProvenanceExtra × Size × Size × AccessKind × ProtectedTags × Tree.ChildrenVisitMode))
    (post : List (Array BorrowTree.BorrowTreeLocationResult) → BorrowTree → Prop)
    (onError : (BorrowTree.BorrowTreeAccessStatus × Array BorrowTree.BorrowTreeLocationResult) →
      BorrowTree → Prop)
    (tree : BorrowTree) :
    TreeBorrowsFrameWP
        (fun s => miriTreeRangeAction s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2)
        steps post onError tree ↔
      AnnealExactWP
        (treeBorrowsFrameAction
          (fun s => miriTreeRangeAction s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2)
          steps)
        post onError tree :=
  treeBorrowsFrameWP_iff _ steps post onError tree

/-- **Compositional ranged access + protector release + `ProtectedTags` removal WP
(`miriTreeRangeThenReleaseExactWP_iff`)**: pairs `(BorrowTree × ProtectedTags)` so releasing
`relTag` runs `BorrowTree.releaseProtector` while `relTag` is STILL in `ProtectedTags` and removes
`relTag` from `ProtectedTags` ONLY upon `.Released`! -/
def miriTreeWithProtRangeAction (prov : ProvenanceExtra) (off len : Size)
    (kind : AccessKind) (mode : Tree.ChildrenVisitMode) :
    ExactAction (BorrowTree × ProtectedTags) MiriTreePipelineError
      (Array BorrowTree.BorrowTreeLocationResult) :=
  fun ⟨tree, prot⟩ =>
    let res := tree.performBorrowAccessRange prov off len kind prot mode
    match res.status with
    | .Completed => .ok res.locations (res.tree, prot)
    | st => .error (.access st res.locations) (res.tree, prot)

/-- Protector release + `ProtectedTags.remove` over `(BorrowTree × ProtectedTags)`. -/
def miriTreeWithProtReleaseAction (relTag : BorTag) :
    ExactAction (BorrowTree × ProtectedTags) MiriTreePipelineError Unit :=
  fun ⟨tree, prot⟩ =>
    let res := tree.releaseProtector relTag prot
    match res.status with
    | .Released => .ok () (res.tree, prot.remove relTag)
    | st => .error (.protectorRelease st) (res.tree, prot)

theorem miriTreeRangeThenReleaseExactWP_iff
    (prov : ProvenanceExtra) (off len : Size) (kind : AccessKind)
    (mode : Tree.ChildrenVisitMode) (relTag : BorTag)
    (post : Unit → BorrowTree × ProtectedTags → Prop)
    (onError : MiriTreePipelineError → BorrowTree × ProtectedTags → Prop)
    (tree : BorrowTree) (prot : ProtectedTags) :
    AnnealExactWP
      (ExactAction.seq (miriTreeWithProtRangeAction prov off len kind mode)
        (miriTreeWithProtReleaseAction relTag))
      post onError (tree, prot) ↔
      tbAccessPre tree prov off len kind prot mode
        (fun _ midTree =>
          protectorReleaseSymbolicPre relTag prot
            (fun _ finalTree => post () (finalTree, prot.remove relTag))
            (fun st errTree => onError (.protectorRelease st) (errTree, prot))
            midTree)
        (fun errPair errTree => onError (.access errPair.1 errPair.2) (errTree, prot)) := by
  rw [exactWP_seq]
  have h1 :
      ∀ (P : Array BorrowTree.BorrowTreeLocationResult → BorrowTree × ProtectedTags → Prop),
        AnnealExactWP (miriTreeWithProtRangeAction prov off len kind mode) P onError (tree, prot) ↔
          tbAccessPre tree prov off len kind prot mode
            (fun locs t' => P locs (t', prot))
            (fun errPair t' => onError (.access errPair.1 errPair.2) (t', prot)) := by
    intro P
    unfold AnnealExactWP miriTreeWithProtRangeAction tbAccessPre
    dsimp only
    cases (tree.performBorrowAccessRange prov off len kind prot mode).status <;> rfl
  rw [h1]
  have h2 :
      ∀ midTree,
        AnnealExactWP (miriTreeWithProtReleaseAction relTag) post onError (midTree, prot) ↔
          protectorReleaseSymbolicPre relTag prot
            (fun _ finalTree => post () (finalTree, prot.remove relTag))
            (fun st errTree => onError (.protectorRelease st) (errTree, prot))
            midTree := by
    intro midTree
    rw [← protectorReleaseSymbolicPre_iff]
    unfold AnnealExactWP miriTreeWithProtReleaseAction ExactWpAndMemoryFrameLM.protectorReleaseAction
    dsimp only
    cases (midTree.releaseProtector relTag prot).status <;> rfl
  unfold tbAccessPre
  dsimp only
  generalize tree.performBorrowAccessRange prov off len kind prot mode = res
  cases res.status with
  | Completed => exact h2 res.tree
  | _ => exact Iff.rfl

/-! ### §1.1. Topology Framing, Missing-Tag Framing & Disjoint `ProtectedTags` Framing -/

/-- `BorrowTree.performBorrowAccessRange` NEVER modifies `tagMapping`, `nodes`, or `roots`
(even when segments split or an access fails!). -/
theorem miriTreeRange_preserves_topology (tree : BorrowTree)
    (prov : ProvenanceExtra) (off len : Size) (kind : AccessKind)
    (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) :
    let res := tree.performBorrowAccessRange prov off len kind tags mode
    res.tree.tagMapping = tree.tagMapping ∧
    res.tree.nodes = tree.nodes ∧
    res.tree.roots = tree.roots := by
  unfold BorrowTree.performBorrowAccessRange
  simp only [Id.run]
  cases prov with
  | concrete tag =>
    dsimp only
    cases (tree.indexOfTag tag).isNone with
    | true => simp only [↓reduceIte, pure, Pure.pure, and_self]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, bind, Bind.bind, pure, Pure.pure]
      cases (tree.locations.iterMut off len).outcome with
      | error _ => exact ⟨rfl, rfl, rfl⟩
      | ok _ => exact ⟨rfl, rfl, rfl⟩
  | wildcard =>
    simp only [bind, Bind.bind, pure, Pure.pure]
    cases (tree.locations.iterMut off len).outcome with
    | error _ => exact ⟨rfl, rfl, rfl⟩
    | ok _ => exact ⟨rfl, rfl, rfl⟩

/-- Accessing a concrete tag absent from `tree` fails closed with `.MissingTag tag` leaving
`tree` identically unchanged! -/
theorem miriTreeRange_missingTag_frame_exactWP (tag : BorTag) (off len : Size)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (post : Array BorrowTree.BorrowTreeLocationResult → BorrowTree → Prop)
    (onError : (BorrowTree.BorrowTreeAccessStatus × Array BorrowTree.BorrowTreeLocationResult) →
      BorrowTree → Prop)
    (tree : BorrowTree) (hMiss : tree.indexOfTag tag = none) :
    AnnealExactWP (miriTreeRangeAction (.concrete tag) off len kind tags mode) post onError tree ↔
      onError (.MissingTag tag, #[]) tree := by
  rw [miriTreeRangeSymbolicExactWP_iff]
  unfold tbAccessSymbolicPre
  simp only [hMiss, Option.isNone_none, ↓reduceIte]

private theorem array_find?_filter_of_pred_true {α : Type} (p q : α → Bool) (xs : Array α)
    (hImp : ∀ x, q x = true → p x = true) :
    (xs.filter p).find? q = xs.find? q := by
  rw [← Array.find?_toList, ← Array.find?_toList, Array.toList_filter]
  induction xs.toList with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter, List.find?]
    cases hq : q hd with
    | true =>
      have hp : p hd = true := hImp hd hq
      simp [hp, hq]
    | false =>
      cases p hd <;> simp [hq, ih]

/-- Removing a disjoint tag `t₁ ≠ t₂` from `ProtectedTags` preserves `ProtectedTags.get t₂` and
`ProtectedTags.contains t₂`. -/
theorem miriProtectedTags_remove_ne (prot : ProtectedTags) (t₁ t₂ : BorTag) (hNe : t₁ ≠ t₂) :
    (prot.remove t₁).get t₂ = prot.get t₂ ∧
    (prot.remove t₁).contains t₂ = prot.contains t₂ := by
  have hGet : (prot.remove t₁).get t₂ = prot.get t₂ := by
    unfold ProtectedTags.get ProtectedTags.remove
    congr 1
    apply array_find?_filter_of_pred_true
    intro x hx
    have hEq : x.1 = t₂ := beq_iff_eq.mp hx
    have hNe' : x.1 ≠ t₁ := fun h => hNe (h.symm.trans hEq)
    exact bne_iff_ne.mpr hNe'
  exact ⟨hGet, by unfold ProtectedTags.contains; rw [hGet]⟩

/-- Inserting a disjoint tag `t₁ ≠ t₂` into `ProtectedTags` preserves `ProtectedTags.get t₂`. -/
theorem miriProtectedTags_insert_ne (prot : ProtectedTags) (t₁ t₂ : BorTag)
    (kind : ProtectorKind) (hNe : t₁ ≠ t₂) :
    (prot.insert t₁ kind).get t₂ = prot.get t₂ := by
  unfold ProtectedTags.get ProtectedTags.insert
  have hNotEq : (t₁ == t₂) = false := beq_false_of_ne hNe
  have hFindPush :
      ((prot.entries.filter fun e => e.1 != t₁).push (t₁, kind)).find? (fun e => e.1 == t₂) =
        (prot.entries.filter fun e => e.1 != t₁).find? (fun e => e.1 == t₂) := by
    rw [Array.find?_push]
    cases hF : (prot.entries.filter fun e => e.1 != t₁).find? (fun e => e.1 == t₂) with
    | some v => rfl
    | none => simp [hNotEq]
  rw [hFindPush]
  have hRem := (miriProtectedTags_remove_ne prot t₁ t₂ hNe).1
  unfold ProtectedTags.get ProtectedTags.remove at hRem
  exact hRem

/-- `GlobalState.endCall` preserves every protected tag `t` not registered in the exiting frame! -/
theorem miriEndCall_preserves_unlisted_protector (gs : GlobalState) (frame : FrameState)
    (t : BorTag) (hNotIn : ∀ p ∈ frame.protectedTags.toList, p.2 ≠ t) :
    (gs.endCall frame).protectedTags.get t = gs.protectedTags.get t := by
  unfold GlobalState.endCall
  dsimp only
  rw [← Array.foldl_toList]
  generalize frame.protectedTags.toList = ps at hNotIn ⊢
  generalize gs.protectedTags = pt
  induction ps generalizing pt with
  | nil => rfl
  | cons p rest ih =>
    dsimp only [List.foldl]
    have hp : p.2 ≠ t := hNotIn p List.mem_cons_self
    rw [ih (fun q hq => hNotIn q (List.mem_cons_of_mem p hq)) (pt.remove p.2)]
    exact (miriProtectedTags_remove_ne pt p.2 t hp).1

/-! ### §1.2. Real Vendored `Miri.TreeBorrows.MachineMemoryHooks.{beforeMemoryRead, beforeMemoryWrite}` Exact WP -/

/-- State-retaining `ExactAction` wrapping unmodified
`Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryRead` over
`(MemoryState Provenance BorrowTree K × MachineMemoryHooks.Context S Obj)`. -/
def miriBeforeMemoryReadAction {S Obj K : Type} [DecidableEq K]
    (hooks : MachineMemoryHooks.Hooks S Obj K)
    (allocation : Allocation Provenance BorrowTree)
    (pointer : Pointer (Option Provenance)) (allocId : Miri.Memory.AllocId)
    (provenance : ProvenanceExtra) (range : AllocRange) :
    ExactAction (MemoryState Provenance BorrowTree K × MachineMemoryHooks.Context S Obj)
      String Unit :=
  fun ⟨mem, ctx⟩ =>
    let res := MachineMemoryHooks.beforeMemoryRead mem ctx hooks allocation pointer allocId
      provenance range
    match res.outcome with
    | .ok () => .ok () (res.memory, res.context)
    | .error msg => .error msg (res.memory, res.context)

/-- State-retaining `ExactAction` wrapping unmodified
`Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryWrite` over
`(MemoryState Provenance BorrowTree K × MachineMemoryHooks.Context S Obj)`. -/
def miriBeforeMemoryWriteAction {S Obj K : Type} [DecidableEq K]
    (hooks : MachineMemoryHooks.Hooks S Obj K)
    (allocation : Allocation Provenance BorrowTree)
    (pointer : Pointer (Option Provenance)) (allocId : Miri.Memory.AllocId)
    (provenance : ProvenanceExtra) (range : AllocRange) :
    ExactAction (MemoryState Provenance BorrowTree K × MachineMemoryHooks.Context S Obj)
      String Unit :=
  fun ⟨mem, ctx⟩ =>
    let res := MachineMemoryHooks.beforeMemoryWrite mem ctx hooks allocation pointer allocId
      provenance range
    match res.outcome with
    | .ok () => .ok () (res.memory, res.context)
    | .error msg => .error msg (res.memory, res.context)

/-- **Exact bidirectional `↔` theorem `miriBeforeMemoryReadExactWP_iff`**: when allocation
diagnostics are disabled, `dataRaceRead` succeeds without altering `ctx.state`, sync objects are
empty, and `setLiveAllocation` commits the updated `BorrowTree` extra back to `mem`, unmodified
vendored `Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryRead` reduces EXACTLY to
`tbAccessPre` (`BorrowTree.performBorrowAccessRange ... .Read hooks.protectedTags .VisitChildrenOfAccessed`),
retaining the committed `BorrowTree` in `mem'` on BOTH `.Completed` and Tree Borrows error! -/
theorem miriBeforeMemoryReadExactWP_iff {S Obj K : Type} [DecidableEq K]
    (hooks : MachineMemoryHooks.Hooks S Obj K)
    (allocation : Allocation Provenance BorrowTree)
    (pointer : Pointer (Option Provenance)) (allocId : Miri.Memory.AllocId)
    (provenance : ProvenanceExtra) (range : AllocRange) (endOff : Size)
    (mem mem' : MemoryState Provenance BorrowTree K)
    (ctx : MachineMemoryHooks.Context S Obj)
    (post : Unit → MemoryState Provenance BorrowTree K × MachineMemoryHooks.Context S Obj → Prop)
    (onError : String → MemoryState Provenance BorrowTree K × MachineMemoryHooks.Context S Obj → Prop)
    (hNoDiag : ctx.trackAllocAccesses = false)
    (hRace : hooks.dataRaceRead ctx.state pointer allocId range = ⟨ctx.state, .ok ()⟩)
    (hNoSync : ctx.syncObjects.get allocId = .empty)
    (hRangeOk : range.endExclusive = .ok endOff)
    (hSetMem :
      mem.setLiveAllocation allocId
        (allocation.setExtra
          (allocation.extra.performBorrowAccessRange provenance range.start range.size
            .Read hooks.protectedTags .VisitChildrenOfAccessed).tree) = .ok mem') :
    AnnealExactWP
      (miriBeforeMemoryReadAction hooks allocation pointer allocId provenance range)
      post onError (mem, ctx) ↔
      tbAccessPre allocation.extra provenance range.start range.size .Read
        hooks.protectedTags .VisitChildrenOfAccessed
        (fun _ _ => post () (mem', ctx))
        (fun errPair _ => onError s!"Tree Borrows read failed: {reprStr errPair.1}" (mem', ctx)) := by
  rcases ctx with ⟨ctxSt, ctxSync, ctxTrack, ctxIds⟩
  dsimp only at hNoDiag hRace hNoSync ⊢
  subst hNoDiag
  have hRes :
      MachineMemoryHooks.beforeMemoryRead mem ⟨ctxSt, ctxSync, false, ctxIds⟩ hooks
          allocation pointer allocId provenance range =
        let res := allocation.extra.performBorrowAccessRange provenance range.start range.size
          .Read hooks.protectedTags .VisitChildrenOfAccessed
        match res.status with
        | .Completed => ⟨mem', ⟨ctxSt, ctxSync, false, ctxIds⟩, .ok ()⟩
        | st => ⟨mem', ⟨ctxSt, ctxSync, false, ctxIds⟩,
            .error s!"Tree Borrows read failed: {reprStr st}"⟩ := by
    unfold MachineMemoryHooks.beforeMemoryRead
    simp only [Id.run, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hRace, pure, Pure.pure,
      bind, Bind.bind]
    unfold_mmh
    simp only [hSetMem, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
    generalize allocation.extra.performBorrowAccessRange provenance range.start range.size
        .Read hooks.protectedTags .VisitChildrenOfAccessed = res
    cases res.status with
    | Completed =>
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hNoSync,
        MachineMemoryHooks.SyncObjectMap.inRange, MachineMemoryHooks.SyncObjectMap.empty,
        hRangeOk, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure,
        Array.filter_empty]
      rfl
    | _ =>
      simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte]
  unfold AnnealExactWP miriBeforeMemoryReadAction tbAccessPre
  dsimp only
  rw [hRes]
  dsimp only
  generalize allocation.extra.performBorrowAccessRange provenance range.start range.size
      .Read hooks.protectedTags .VisitChildrenOfAccessed = res
  cases res.status <;> rfl

/-- **Exact bidirectional `↔` theorem `miriBeforeMemoryWriteExactWP_iff`**: exact two-continuation
WP characterization of unmodified vendored `Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryWrite`
reducing directly to `tbAccessPre` (`.Write`) with committed post-tree retention on error! -/
theorem miriBeforeMemoryWriteExactWP_iff {S Obj K : Type} [DecidableEq K]
    (hooks : MachineMemoryHooks.Hooks S Obj K)
    (allocation : Allocation Provenance BorrowTree)
    (pointer : Pointer (Option Provenance)) (allocId : Miri.Memory.AllocId)
    (provenance : ProvenanceExtra) (range : AllocRange) (endOff : Size)
    (mem mem' : MemoryState Provenance BorrowTree K)
    (ctx : MachineMemoryHooks.Context S Obj)
    (post : Unit → MemoryState Provenance BorrowTree K × MachineMemoryHooks.Context S Obj → Prop)
    (onError : String → MemoryState Provenance BorrowTree K × MachineMemoryHooks.Context S Obj → Prop)
    (hNoDiag : ctx.trackAllocAccesses = false)
    (hRace : hooks.dataRaceWrite ctx.state pointer allocId range = ⟨ctx.state, .ok ()⟩)
    (hNoSync : ctx.syncObjects.get allocId = .empty)
    (hRangeOk : range.endExclusive = .ok endOff)
    (hSetMem :
      mem.setLiveAllocation allocId
        (allocation.setExtra
          (allocation.extra.performBorrowAccessRange provenance range.start range.size
            .Write hooks.protectedTags .VisitChildrenOfAccessed).tree) = .ok mem') :
    AnnealExactWP
      (miriBeforeMemoryWriteAction hooks allocation pointer allocId provenance range)
      post onError (mem, ctx) ↔
      tbAccessPre allocation.extra provenance range.start range.size .Write
        hooks.protectedTags .VisitChildrenOfAccessed
        (fun _ _ =>
          post () (mem', { ctx with syncObjects := ctx.syncObjects.set allocId .empty }))
        (fun errPair _ => onError s!"Tree Borrows write failed: {reprStr errPair.1}" (mem', ctx)) := by
  rcases ctx with ⟨ctxSt, ctxSync, ctxTrack, ctxIds⟩
  dsimp only at hNoDiag hRace hNoSync ⊢
  subst hNoDiag
  have hRes :
      MachineMemoryHooks.beforeMemoryWrite mem ⟨ctxSt, ctxSync, false, ctxIds⟩ hooks
          allocation pointer allocId provenance range =
        let res := allocation.extra.performBorrowAccessRange provenance range.start range.size
          .Write hooks.protectedTags .VisitChildrenOfAccessed
        match res.status with
        | .Completed =>
          ⟨mem', ⟨ctxSt, ctxSync.set allocId .empty, false, ctxIds⟩, .ok ()⟩
        | st => ⟨mem', ⟨ctxSt, ctxSync, false, ctxIds⟩,
            .error s!"Tree Borrows write failed: {reprStr st}"⟩ := by
    unfold MachineMemoryHooks.beforeMemoryWrite
    simp only [Id.run, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hRace, pure, Pure.pure,
      bind, Bind.bind]
    unfold_mmh
    simp only [hSetMem, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
    generalize allocation.extra.performBorrowAccessRange provenance range.start range.size
        .Write hooks.protectedTags .VisitChildrenOfAccessed = res
    cases res.status with
    | Completed =>
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hNoSync,
        MachineMemoryHooks.SyncObjectMap.inRange, MachineMemoryHooks.SyncObjectMap.empty,
        hRangeOk, bind, Bind.bind, Except.bind, pure, Pure.pure,
        Except.pure, Array.filter_empty]
      change MachineMemoryHooks.AccessResult.mk mem'
               (MachineMemoryHooks.Context.mk ctxSt
                 (ctxSync.set allocId (ctxSync.get allocId)) false ctxIds)
               (Except.ok ()) = _
      rw [hNoSync]
      rfl
    | _ =>
      simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte]
  unfold AnnealExactWP miriBeforeMemoryWriteAction tbAccessPre
  dsimp only
  rw [hRes]
  dsimp only
  generalize allocation.extra.performBorrowAccessRange provenance range.start range.size
      .Write hooks.protectedTags .VisitChildrenOfAccessed = res
  cases res.status <;> rfl

/-! ### §1.3. Real Vendored `Miri.Interpreter.PlaceMachine.{memoryAccess, writeMemory, readImmediate}` Exact WP -/

/-- Exact public mirror of vendored `PlaceMachine.treeError` (`PlaceMachine.lean:38-44`) classifying
Tree Borrows transition errors as `.undefinedBehavior` and invariant errors as `.invalidProgram`. -/
def placeMachineTreeError (status : BorrowTree.BorrowTreeAccessStatus) : StepError :=
  match status with
  | .AccessFailure _ (.TransitionError ..)
  | .WildcardFailure _ (.TransitionError ..)
  | .WildcardFailure _ (.NoValidExposedReferences ..) =>
    .undefinedBehavior s!"Tree Borrows: {reprStr status}"
  | _ => .invalidProgram s!"Tree Borrows invariant: {reprStr status}"

/-- State-retaining `ExactAction` wrapping unmodified vendored `Miri.Interpreter.PlaceMachine.memoryAccess`
over `(PlaceMachine.AccessState K User × BorrowTree)`, preserving BOTH `AccessState` (including
`pendingError`) AND the committed `BorrowTree` on `.ok` and `.error`! -/
def miriPlaceMachineMemoryAccessAction {K User : Type}
    (config : PlaceMachine.AccessConfig K User) (write : Bool)
    (allocId : Miri.Memory.AllocId) (provenance : ProvenanceExtra) (range : AllocRange) :
    ExactAction (PlaceMachine.AccessState K User × BorrowTree) String Unit :=
  fun ⟨st, tree⟩ =>
    let res := PlaceMachine.memoryAccess config write st tree allocId provenance range
    match res.outcome with
    | .ok () => .ok () (res.state, res.extra)
    | .error msg => .error msg (res.state, res.extra)

/-- **Exact bidirectional `↔` theorem `miriPlaceMachineMemoryAccessExactWP_iff`**: characterizes
unmodified vendored `Miri.Interpreter.PlaceMachine.memoryAccess` (the actual callback installed by
`PlaceMachine.accessHooks` for `beforeMemoryRead` and `beforeMemoryWrite`) directly in terms of
`tbAccessPre` (`BorrowTree.performBorrowAccessRange`), retaining the committed `BorrowTree` AND
stashing `placeMachineTreeError status` in `pendingError` on Tree Borrows UB! -/
theorem miriPlaceMachineMemoryAccessExactWP_iff {K User : Type}
    (config : PlaceMachine.AccessConfig K User) (write : Bool)
    (allocId : Miri.Memory.AllocId) (provenance : ProvenanceExtra) (range : AllocRange)
    (state : PlaceMachine.AccessState K User) (tree : BorrowTree)
    (tracker : MachineHooks.BorrowState)
    (post : Unit → PlaceMachine.AccessState K User × BorrowTree → Prop)
    (onError : String → PlaceMachine.AccessState K User × BorrowTree → Prop)
    (hNoRace : state.machine.dataRace = none)
    (hTracker : state.machine.borrowTracker = some tracker)
    (hDiag : config.diagnostic write allocId range state.machine = .ok () state.machine)
    (hWeak : write = true → config.weakMemoryWrite allocId range state.machine = .ok () state.machine)
    (hSync : config.syncAccess write allocId range state.machine = .ok () state.machine) :
    AnnealExactWP
      (miriPlaceMachineMemoryAccessAction config write allocId provenance range)
      post onError (state, tree) ↔
      tbAccessPre tree provenance range.start range.size
        (if write then .Write else .Read) tracker.global.protectedTags .VisitChildrenOfAccessed
        (fun _ tree' => post () (state, tree'))
        (fun errPair tree' =>
          let err := placeMachineTreeError errPair.1
          onError (reprStr err) ({ state with pendingError := some err }, tree')) := by
  rcases state with ⟨mach, pend⟩
  dsimp only at hNoRace hTracker hDiag hWeak hSync ⊢
  have hRes :
      PlaceMachine.memoryAccess config write ⟨mach, pend⟩ tree allocId provenance range =
        let accessed := tree.performBorrowAccessRange provenance range.start range.size
          (if write then .Write else .Read) tracker.global.protectedTags .VisitChildrenOfAccessed
        match accessed.status with
        | .Completed => ⟨⟨mach, pend⟩, accessed.tree, .ok ()⟩
        | st =>
          let err := placeMachineTreeError st
          ⟨⟨mach, some err⟩, accessed.tree, .error (reprStr err)⟩ := by
    unfold PlaceMachine.memoryAccess
    cases write with
    | false =>
      simp only [Id.run, Bool.false_eq_true, ↓reduceIte]
      unfold_pm
      rw [hDiag]
      simp only [MachineHooks.memoryRaceAccess, hNoRace, Id.run, pure, Pure.pure, hTracker]
      generalize tree.performBorrowAccessRange provenance range.start range.size .Read
          tracker.global.protectedTags .VisitChildrenOfAccessed = accessed
      rcases accessed with ⟨accTree, accLocs, accStatus⟩
      cases accStatus with
      | Completed =>
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hSync]
      | AccessFailure r st =>
        simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte,
          placeMachineTreeError]
        cases st <;> rfl
      | WildcardFailure r st =>
        simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte,
          placeMachineTreeError]
        cases st <;> rfl
      | _ =>
        simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte,
          placeMachineTreeError]
    | true =>
      have hW := hWeak rfl
      simp only [Id.run, ↓reduceIte]
      unfold_pm
      rw [hDiag]
      simp only [MachineHooks.memoryRaceAccess, hNoRace, Id.run, pure, Pure.pure, hW, hTracker]
      generalize tree.performBorrowAccessRange provenance range.start range.size .Write
          tracker.global.protectedTags .VisitChildrenOfAccessed = accessed
      rcases accessed with ⟨accTree, accLocs, accStatus⟩
      cases accStatus with
      | Completed =>
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hSync]
      | AccessFailure r st =>
        simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte,
          placeMachineTreeError]
        cases st <;> rfl
      | WildcardFailure r st =>
        simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte,
          placeMachineTreeError]
        cases st <;> rfl
      | _ =>
        simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte,
          placeMachineTreeError]
  unfold AnnealExactWP miriPlaceMachineMemoryAccessAction tbAccessPre
  dsimp only
  rw [hRes]
  dsimp only
  generalize tree.performBorrowAccessRange provenance range.start range.size
      (if write then .Write else .Read) tracker.global.protectedTags .VisitChildrenOfAccessed =
    accessed
  cases accessed.status <;> rfl

/-- Lift unmodified vendored `Miri.Interpreter.PlaceMachine.writeMemory` (which routes through
`PlaceMachine.accessHooks` → `AllocationAccess.getPtrAllocMut` → `PlaceMachine.memoryAccess`) into
`ExactAction`. -/
def miriPlaceMachineWriteMemoryAction {K User : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K User)
    (willValidate : MemoryOperandLayout → Bool)
    (value : Immediate Provenance) (place : MPlaceTy Provenance) :
    ExactAction (PlaceMachine.State K User) StepError Unit :=
  ExactAction.ofEStateM (PlaceMachine.writeMemory config willValidate value place)

/-- **Exact bidirectional `↔` theorem `miriPlaceMachineWriteMemoryExactWP_iff`**: decomposes
unmodified vendored `Miri.Interpreter.PlaceMachine.writeMemory` into
`writeImmediateToMplaceNoValidate ... (PlaceMachine.accessHooks config)`, memory/touched-ref
commit (`retainTouched`), and `pendingError` recovery on error! -/
theorem miriPlaceMachineWriteMemoryExactWP_iff {K User : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K User)
    (willValidate : MemoryOperandLayout → Bool)
    (value : Immediate Provenance) (place : MPlaceTy Provenance)
    (post : Unit → PlaceMachine.State K User → Prop)
    (onError : StepError → PlaceMachine.State K User → Prop)
    (state : PlaceMachine.State K User) :
    AnnealExactWP (miriPlaceMachineWriteMemoryAction config willValidate value place)
        post onError state ↔
      let result := writeImmediateToMplaceNoValidate state.machine.memory ⟨state.machine, none⟩
        value ⟨place.mplace, localMemoryLayout place.layout⟩ config.runtime config.ghostMode
        config.globalKind config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout
        willValidate
      let afterState : PlaceMachine.State K User :=
        { state with
          machine := config.retainTouched { result.hooks.machine with memory := result.memory }
            result.touched }
      match result.outcome with
      | .ok () => post () afterState
      | .error err => onError (result.hooks.pendingError.getD (config.memoryError err)) afterState := by
  unfold AnnealExactWP miriPlaceMachineWriteMemoryAction ExactAction.ofEStateM PlaceMachine.writeMemory
  unfold_pm
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, pure, Pure.pure,
    throw, MonadExcept.throw, throwThe, MonadExceptOf.throw]
  generalize writeImmediateToMplaceNoValidate state.machine.memory ⟨state.machine, none⟩
      value ⟨place.mplace, localMemoryLayout place.layout⟩ config.runtime config.ghostMode
      config.globalKind config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout
      willValidate = result
  cases result.outcome with
  | ok u => cases u; rfl
  | error err => rfl

/-- Lift unmodified vendored `Miri.Interpreter.PlaceMachine.readImmediate` (which routes through
`PlaceMachine.accessHooks` → `AllocationAccess.getPtrAlloc` → `PlaceMachine.memoryAccess`) into
`ExactAction`. -/
def miriPlaceMachineReadImmediateAction {K User : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K User) (operand : OpTy Provenance) :
    ExactAction (PlaceMachine.State K User) StepError (RvalueImmTy Provenance) :=
  ExactAction.ofEStateM (PlaceMachine.readImmediate config operand)

/-- **Exact bidirectional `↔` theorem `miriPlaceMachineReadImmediateExactWP_iff`**: decomposes
unmodified vendored `Miri.Interpreter.PlaceMachine.readImmediate` into
`Miri.Interpreter.readImmediate ... (PlaceMachine.accessHooks config)`, memory/touched-ref commit,
and `pendingError` recovery on error! -/
theorem miriPlaceMachineReadImmediateExactWP_iff {K User : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K User) (operand : OpTy Provenance)
    (post : RvalueImmTy Provenance → PlaceMachine.State K User → Prop)
    (onError : StepError → PlaceMachine.State K User → Prop)
    (state : PlaceMachine.State K User) :
    AnnealExactWP (miriPlaceMachineReadImmediateAction config operand) post onError state ↔
      let result := Miri.Interpreter.readImmediate state.machine.memory ⟨state.machine, none⟩
        operand.op (localMemoryLayout operand.layout) config.runtime config.ghostMode
        config.globalKind config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout
      let afterState : PlaceMachine.State K User :=
        { state with
          machine := config.retainTouched { result.hooks.machine with memory := result.memory }
            result.touched }
      match result.outcome with
      | .ok val => post ⟨val.value, operand.layout⟩ afterState
      | .error err => onError (result.hooks.pendingError.getD (config.memoryError err)) afterState := by
  unfold AnnealExactWP miriPlaceMachineReadImmediateAction ExactAction.ofEStateM
    PlaceMachine.readImmediate
  unfold_pm
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, pure, Pure.pure, EStateM.pure,
    throw, MonadExcept.throw, throwThe, MonadExceptOf.throw]
  generalize Miri.Interpreter.readImmediate state.machine.memory ⟨state.machine, none⟩
      operand.op (localMemoryLayout operand.layout) config.runtime config.ghostMode
      config.globalKind config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout =
    result
  cases result.outcome <;> rfl

end InitialStateTreeRangeWP

/-! ## §2. Initial-State Instruction & Call-Dispatch WP (`miriInstructionExactWP_iff`, `miriCallDispatchExactWP_iff`) -/

section InstructionAndCallDispatchWP

variable {P L E M C V : Type}

/-- Lift unmodified `Miri.Interpreter.Step.evalStatement` into `ExactAction`, retaining post-state
on BOTH `.ok ()` and `.error err`. -/
def miriInstructionAction (hooks : StepHooks P L E M C V) (choice : C)
    (stmt : Miri.MIR.Statement) : ExactAction (StepState P L E M) StepError Unit :=
  fun state =>
    match Step.evalStatement hooks choice stmt state with
    | (after, .ok ()) => .ok () after
    | (after, .error err) => .error err after

/-- Exact symbolic per-statement-kind precondition mirroring `lean-miri#94` `miri_instruction_wp`
over unmodified `Miri.Interpreter.Step.evalStatement`. -/
def miriInstructionPre (hooks : StepHooks P L E M C V) (choice : C)
    (stmt : Miri.MIR.Statement)
    (post : Unit → StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state : StepState P L E M) : Prop :=
  match stmt.kind with
  | .Assign place value =>
    match hooks.assign choice place value state with
    | (after, .ok ()) => post () after
    | (after, .error err) => onError err after
  | .SetDiscriminant place variant =>
    match hooks.evalPlace choice place false state with
    | (s1, .error err) => onError err s1
    | (s1, .ok placeVal) =>
      match hooks.writeDiscriminant choice variant placeVal s1 with
      | (s2, .ok ()) => post () s2
      | (s2, .error err) => onError err s2
  | .StorageLive localId =>
    match hooks.storageLive choice localId state with
    | (after, .ok ()) => post () after
    | (after, .error err) => onError err after
  | .StorageDead localId =>
    match hooks.storageDead choice localId state with
    | (after, .ok ()) => post () after
    | (after, .error err) => onError err after
  | .Intrinsic intr =>
    match hooks.intrinsic choice intr state with
    | (after, .ok ()) => post () after
    | (after, .error err) => onError err after
  | .PlaceMention place =>
    match hooks.evalPlace choice place false state with
    | (after, .ok _) => post () after
    | (after, .error err) => onError err after
  | .ConstEvalCounter =>
    match hooks.incrementConstEvalCounter choice state with
    | (after, .ok ()) => post () after
    | (after, .error err) => onError err after
  | .FakeRead .. | .AscribeUserType .. | .Coverage .. | .Nop
  | .BackwardIncompatibleDropHint .. =>
    post () state

/-- **Exact bidirectional `↔` theorem `miriInstructionExactWP_iff`** (mirroring `lean-miri#94`'s
`miri_instruction_wp`): characterizes EVERY MIR statement constructor of unmodified
`Miri.Interpreter.Step.evalStatement`! -/
theorem miriInstructionExactWP_iff (hooks : StepHooks P L E M C V) (choice : C)
    (stmt : Miri.MIR.Statement)
    (post : Unit → StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state : StepState P L E M) :
    AnnealExactWP (miriInstructionAction hooks choice stmt) post onError state ↔
      miriInstructionPre hooks choice stmt post onError state := by
  unfold AnnealExactWP miriInstructionAction miriInstructionPre Step.evalStatement
  cases stmt.kind with
  | Assign place value =>
    dsimp only
    cases hooks.assign choice place value state with
    | mk after res => cases res with | ok u => cases u; rfl | error _ => rfl
  | SetDiscriminant place variant =>
    dsimp only
    cases hEv : hooks.evalPlace choice place false state with
    | mk s1 res1 =>
      simp only [hEv]
      cases res1 with
      | error _ => rfl
      | ok pv =>
        dsimp only
        cases hooks.writeDiscriminant choice variant pv s1 with
        | mk s2 res2 => cases res2 with | ok u => cases u; rfl | error _ => rfl
  | StorageLive localId =>
    dsimp only
    cases hooks.storageLive choice localId state with
    | mk after res => cases res with | ok u => cases u; rfl | error _ => rfl
  | StorageDead localId =>
    dsimp only
    cases hooks.storageDead choice localId state with
    | mk after res => cases res with | ok u => cases u; rfl | error _ => rfl
  | Intrinsic intr =>
    dsimp only
    cases hooks.intrinsic choice intr state with
    | mk after res => cases res with | ok u => cases u; rfl | error _ => rfl
  | PlaceMention place =>
    dsimp only
    cases hEval : hooks.evalPlace choice place false state with
    | mk after res =>
      simp only [hEval, Except.map]
      cases res <;> rfl
  | ConstEvalCounter =>
    dsimp only
    cases hooks.incrementConstEvalCounter choice state with
    | mk after res => cases res with | ok u => cases u; rfl | error _ => rfl
  | FakeRead _ _ => rfl
  | AscribeUserType _ _ _ => rfl
  | Coverage _ => rfl
  | Nop => rfl
  | BackwardIncompatibleDropHint _ _ => rfl

/-- Exact no-op / metadata statement framing law: `.Nop`, `.FakeRead`, `.AscribeUserType`,
`.Coverage`, and `.BackwardIncompatibleDropHint` leave the ENTIRE `StepState` untouched! -/
theorem miriInstructionExactWP_nop_frame (hooks : StepHooks P L E M C V) (choice : C)
    (sourceInfo : Miri.MIR.SourceInfo)
    (post : Unit → StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state : StepState P L E M) :
    AnnealExactWP (miriInstructionAction hooks choice ⟨sourceInfo, .Nop⟩) post onError state ↔
      post () state :=
  miriInstructionExactWP_iff hooks choice ⟨sourceInfo, .Nop⟩ post onError state

/-- **Unified metadata/no-op framing law (`miriInstructionExactWP_meta_frame`)**: ALL FIVE MIR
no-op/metadata statement constructors (`.Nop`, `.FakeRead`, `.AscribeUserType`, `.Coverage`,
`.BackwardIncompatibleDropHint`) leave the ENTIRE `StepState` identically untouched and frame
ANY state invariant `Inv`! -/
theorem miriInstructionExactWP_meta_frame (hooks : StepHooks P L E M C V) (choice : C)
    (stmt : Miri.MIR.Statement)
    (hMeta : match stmt.kind with
      | .FakeRead .. | .AscribeUserType .. | .Coverage .. | .Nop
      | .BackwardIncompatibleDropHint .. => True
      | _ => False)
    (Inv : StepState P L E M → Prop)
    (post : Unit → StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state : StepState P L E M) :
    AnnealExactWP (miriInstructionAction hooks choice stmt)
        (fun u s' => post u s' ∧ Inv s') onError state ↔
      post () state ∧ Inv state := by
  rw [miriInstructionExactWP_iff]
  unfold miriInstructionPre
  cases hk : stmt.kind <;> rw [hk] at hMeta <;> first | exact False.elim hMeta | exact Iff.rfl

/-- **Concrete `annealStepHooks` fail-closed `StorageDead 0` law
(`annealInstruction_storageDead_returnPlace_err_exactWP`)**: executing `StorageDead 0` on ANY
non-empty active stack frame with `annealStepHooks` ALWAYS faults with
`StepError.stack .cannotMakeReturnPlaceDead` (rustc MIR forbids killing return place `_0`), and
via `↔` refutes pure safety! -/
theorem annealInstruction_storageDead_returnPlace_err_exactWP
    (localDecls : List LocalDecl) (layouts : AnnealLayoutTable)
    (sourceInfo : Miri.MIR.SourceInfo)
    (post : Unit → AnnealStepState → Prop)
    (onError : StepError → AnnealStepState → Prop)
    (state : AnnealStepState) (frame : Frame AnnealProv LocalLayout Unit)
    (hFrame : state.stack.currentFrame? = some frame) :
    AnnealExactWP
      (miriInstructionAction (annealStepHooks localDecls layouts) () ⟨sourceInfo, .StorageDead 0⟩)
      post onError state ↔
      onError (.stack .cannotMakeReturnPlaceDead)
        { stack :=
            { frames := state.stack.frames.set (state.stack.frames.size - 1) frame
                (by
                  unfold Stack.currentFrame? at hFrame
                  cases hSz : state.stack.frames.size with
                  | zero => simp [Array.back?, hSz] at hFrame
                  | succ k => omega) }
          machine := state.machine } := by
  rw [miriInstructionExactWP_iff]
  unfold miriInstructionPre
  dsimp only [annealStepHooks, annealRunFrameStorage, Frame.storageDead]
  rw [hFrame]
  have hLt : state.stack.frames.size - 1 < state.stack.frames.size := by
    unfold Stack.currentFrame? at hFrame
    cases hSz : state.stack.frames.size with
    | zero => simp [Array.back?, hSz] at hFrame
    | succ k => omega
  simp only [Id.run, pure, Pure.pure, beq_self_eq_true, ↓reduceIte, hLt, ↓reduceDIte]

/-- Exact `.SetDiscriminant` compositional two-stage law: evaluates `place` first (committing
its state on error) and then writes `variant`. -/
theorem miriInstructionExactWP_setDiscriminant_iff (hooks : StepHooks P L E M C V) (choice : C)
    (place : Miri.MIR.Place) (variant : Miri.MIR.VariantIndex)
    (sourceInfo : Miri.MIR.SourceInfo)
    (post : Unit → StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state : StepState P L E M) :
    AnnealExactWP (miriInstructionAction hooks choice ⟨sourceInfo, .SetDiscriminant place variant⟩)
        post onError state ↔
      match hooks.evalPlace choice place false state with
      | (s1, .error err) => onError err s1
      | (s1, .ok pv) =>
        match hooks.writeDiscriminant choice variant pv s1 with
        | (s2, .ok ()) => post () s2
        | (s2, .error err) => onError err s2 :=
  miriInstructionExactWP_iff hooks choice ⟨sourceInfo, .SetDiscriminant place variant⟩ post onError state

/-! ### §2.0a. Deep Semantic Decomposition of `.Assign` (`Miri.Interpreter.evalRvalueIntoPlace`) -/

/-- Lift unmodified `Miri.Interpreter.evalRvalueIntoPlace` into `ExactAction`. -/
def miriEvalRvalueAction {S : Type} (rh : RvalueHooks P S C V) (choice : C)
    (rvalue : Miri.MIR.Rvalue) (place : Miri.MIR.Place) : ExactAction S StepError Unit :=
  ExactAction.ofEStateM (Miri.Interpreter.evalRvalueIntoPlace rh choice rvalue place)

/-- Exact symbolic per-`Rvalue` precondition decomposing unmodified
`Miri.Interpreter.evalRvalueIntoPlace`: destination place evaluation ALWAYS runs first
(`skip_validity_for_simple_deref = true`), followed by the exact operational sub-stages of all 13
MIR `Rvalue` constructors (including `.CopyForDeref` fail-closed error, `.Use` `RetagMode` scoping,
`.BinaryOp`/`.UnaryOp` homogeneity & layout assertion, `.Ref` `TwoPhase`/`Default` retag, and
`.RawPtr` `.Raw` retag)! -/
def miriEvalRvaluePre {S : Type} (rh : RvalueHooks P S C V) (choice : C)
    (rvalue : Miri.MIR.Rvalue) (place : Miri.MIR.Place)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) (state : S) : Prop :=
  AnnealExactWP (ExactAction.ofEStateM (rh.evalPlace choice place true))
    (fun dest s1 =>
      let layout := rh.placeLayout dest
      match rvalue with
      | .ThreadLocalRef definition =>
        AnnealExactWP (ExactAction.ofEStateM (rh.threadLocalPointer choice definition))
          (fun ptr s2 => AnnealExactWP (ExactAction.ofEStateM (rh.writePointer choice ptr dest)) post onError s2)
          onError s1
      | .Use operand retag =>
        AnnealExactWP
          (ExactAction.ofEStateM
            (rh.evalOperandAt choice (OperandPath.rvalue "operand") operand (some layout)))
          (fun op s2 =>
            AnnealExactWP
              (ExactAction.ofEStateM
                (rh.withRetagMode choice (if retag == .Yes then .Default else .None)
                  (rh.copyOp choice op dest)))
              post onError s2)
          onError s1
      | .CopyForDeref _ =>
        onError (.invalidProgram "CopyForDeref in runtime MIR") s1
      | .BinaryOp operator left right =>
        AnnealExactWP
          (ExactAction.ofEStateM
            (rh.evalOperandAt choice (OperandPath.rvalue "left") left
              (if operator.leftHomogeneous then some layout else none)))
          (fun lOp s2 =>
            AnnealExactWP (ExactAction.ofEStateM (rh.readImmediate choice lOp))
              (fun lVal s3 =>
                AnnealExactWP
                  (ExactAction.ofEStateM
                    (rh.evalOperandAt choice (OperandPath.rvalue "right") right
                      (if operator.rightHomogeneous then some lVal.layout else none)))
                  (fun rOp s4 =>
                    AnnealExactWP (ExactAction.ofEStateM (rh.readImmediate choice rOp))
                      (fun rVal s5 =>
                        AnnealExactWP (ExactAction.ofEStateM (rh.binaryOp choice operator lVal rVal))
                          (fun res s6 =>
                            if res.layout == layout then
                              AnnealExactWP (ExactAction.ofEStateM (rh.writeImmediate choice res.imm dest))
                                post onError s6
                            else
                              onError (.invalidProgram "rvalue result layout mismatch") s6)
                          onError s5)
                      onError s4)
                  onError s3)
              onError s2)
          onError s1
      | .UnaryOp operator operand =>
        AnnealExactWP
          (ExactAction.ofEStateM
            (rh.evalOperandAt choice (OperandPath.rvalue "operand") operand
              (if operator.homogeneous then some layout else none)))
          (fun op s2 =>
            AnnealExactWP (ExactAction.ofEStateM (rh.readImmediate choice op))
              (fun val s3 =>
                AnnealExactWP (ExactAction.ofEStateM (rh.unaryOp choice operator val))
                  (fun res s4 =>
                    if res.layout == layout then
                      AnnealExactWP (ExactAction.ofEStateM (rh.writeImmediate choice res.imm dest))
                        post onError s4
                    else
                      onError (.invalidProgram "rvalue result layout mismatch") s4)
                  onError s3)
              onError s2)
          onError s1
      | .Aggregate kind operands =>
        AnnealExactWP (ExactAction.ofEStateM (rh.writeAggregate choice kind operands dest)) post onError s1
      | .Repeat operand _ =>
        AnnealExactWP (ExactAction.ofEStateM (rh.writeRepeat choice operand dest)) post onError s1
      | .Ref _ borrow src =>
        AnnealExactWP (ExactAction.ofEStateM (rh.evalPlace choice src true))
          (fun srcV s2 =>
            AnnealExactWP (ExactAction.ofEStateM (rh.forceAllocation choice srcV))
              (fun srcMp s3 =>
                AnnealExactWP (ExactAction.ofEStateM (rh.toRef choice srcMp))
                  (fun imm s4 =>
                    let val : RvalueImmTy P := ⟨imm, layout⟩
                    let mode :=
                      if borrow == .Mut .TwoPhaseBorrow then
                        Miri.TreeBorrows.RetagPolicy.RetagMode.TwoPhase
                      else .Default
                    AnnealExactWP
                      (ExactAction.ofEStateM
                        (rh.withRetagMode choice mode do
                          let mut val := val
                          if !(← rh.enforceValidity choice val.layout) then
                            if let some newVal ← rh.retagPtrValue choice val val.layout.ty then
                              val := newVal
                          rh.writeImmediate choice val.imm dest))
                      post onError s4)
                  onError s3)
              onError s2)
          onError s1
      | .Reborrow _ mutability src =>
        AnnealExactWP (ExactAction.ofEStateM (rh.evalPlaceToOp choice src none))
          (fun op s2 =>
            if mutability == .Not then
              AnnealExactWP (ExactAction.ofEStateM (rh.copyOpAllowTransmute choice op dest)) post onError s2
            else
              AnnealExactWP (ExactAction.ofEStateM (rh.copyOp choice op dest)) post onError s2)
          onError s1
      | .RawPtr kind src =>
        AnnealExactWP (ExactAction.ofEStateM (rh.placeBaseRaw choice src))
          (fun baseRaw s2 =>
            AnnealExactWP (ExactAction.ofEStateM (rh.evalPlace choice src false))
              (fun srcV s3 =>
                AnnealExactWP (ExactAction.ofEStateM (rh.forceAllocation choice srcV))
                  (fun srcMp s4 =>
                    AnnealExactWP (ExactAction.ofEStateM (rh.toRef choice srcMp))
                      (fun imm s5 =>
                        let val : RvalueImmTy P := ⟨imm, layout⟩
                        if !baseRaw && kind != .FakeForPtrMetadata then
                          AnnealExactWP
                            (ExactAction.ofEStateM
                              (rh.withRetagMode choice .Raw do
                                return (← rh.retagPtrValue choice val val.layout.ty).getD val))
                            (fun val' s6 =>
                              AnnealExactWP (ExactAction.ofEStateM (rh.writeImmediate choice val'.imm dest))
                                post onError s6)
                            onError s5
                        else
                          AnnealExactWP (ExactAction.ofEStateM (rh.writeImmediate choice val.imm dest))
                            post onError s5)
                      onError s4)
                  onError s3)
              onError s2)
          onError s1
      | .Cast kind operand ty =>
        AnnealExactWP
          (ExactAction.ofEStateM (rh.evalOperandAt choice (OperandPath.rvalue "operand") operand none))
          (fun src s2 =>
            AnnealExactWP (ExactAction.ofEStateM (rh.normalize choice ty))
              (fun ty' s3 =>
                AnnealExactWP (ExactAction.ofEStateM (rh.cast choice src kind ty' dest)) post onError s3)
              onError s2)
          onError s1
      | .Discriminant src =>
        AnnealExactWP (ExactAction.ofEStateM (rh.evalPlaceToOp choice src none))
          (fun op s2 =>
            AnnealExactWP (ExactAction.ofEStateM (rh.readDiscriminant choice op))
              (fun variant s3 =>
                AnnealExactWP (ExactAction.ofEStateM (rh.discriminantForVariant choice op.layout.ty variant))
                  (fun discr s4 =>
                    AnnealExactWP (ExactAction.ofEStateM (rh.writeImmediate choice discr.imm dest))
                      post onError s4)
                  onError s3)
              onError s2)
          onError s1
      | .WrapUnsafeBinder operand _ =>
        AnnealExactWP
          (ExactAction.ofEStateM (rh.evalOperandAt choice (OperandPath.rvalue "operand") operand none))
          (fun op s2 =>
            AnnealExactWP (ExactAction.ofEStateM (rh.copyOpAllowTransmute choice op dest)) post onError s2)
          onError s1)
    onError state

/-- **Exact bidirectional `↔` theorem `miriEvalRvalueIntoPlaceExactWP_iff`**: decomposes unmodified
`Miri.Interpreter.evalRvalueIntoPlace` across ALL 13 MIR `Rvalue` constructors! -/
theorem miriEvalRvalueIntoPlaceExactWP_iff {S : Type} (rh : RvalueHooks P S C V) (choice : C)
    (rvalue : Miri.MIR.Rvalue) (place : Miri.MIR.Place)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) (state : S) :
    AnnealExactWP (miriEvalRvalueAction rh choice rvalue place) post onError state ↔
      miriEvalRvaluePre rh choice rvalue place post onError state := by
  unfold miriEvalRvalueAction miriEvalRvaluePre Miri.Interpreter.evalRvalueIntoPlace
  unfold_pm
  simp only [AnnealExactWP, ExactAction.ofEStateM, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, throw, MonadExcept.throw, throwThe, MonadExceptOf.throw]
  cases rh.evalPlace choice place true state with
  | error err s1 => rfl
  | ok dest s1 =>
    dsimp only
    cases rvalue with
    | ThreadLocalRef definition =>
      dsimp only [EStateM.bind]
      cases rh.threadLocalPointer choice definition s1 <;> rfl
    | Use operand retag =>
      dsimp only [EStateM.bind]
      cases rh.evalOperandAt choice (OperandPath.rvalue "operand") operand (some (rh.placeLayout dest)) s1 <;> rfl
    | CopyForDeref _ => rfl
    | BinaryOp operator left right =>
      dsimp only [EStateM.bind]
      cases rh.evalOperandAt choice (OperandPath.rvalue "left") left
          (if operator.leftHomogeneous then some (rh.placeLayout dest) else none) s1 with
      | error _ _ => rfl
      | ok lOp s2 =>
        dsimp only [EStateM.bind]
        cases rh.readImmediate choice lOp s2 with
        | error _ _ => rfl
        | ok lVal s3 =>
          dsimp only [EStateM.bind]
          cases rh.evalOperandAt choice (OperandPath.rvalue "right") right
              (if operator.rightHomogeneous then some lVal.layout else none) s3 with
          | error _ _ => rfl
          | ok rOp s4 =>
            dsimp only [EStateM.bind]
            cases rh.readImmediate choice rOp s4 with
            | error _ _ => rfl
            | ok rVal s5 =>
              dsimp only [EStateM.bind]
              cases rh.binaryOp choice operator lVal rVal s5 with
              | error _ _ => rfl
              | ok res s6 =>
                dsimp only [EStateM.bind]
                by_cases hEq : (res.layout == rh.placeLayout dest) = true <;>
                  simp only [hEq, Bool.false_eq_true, ↓reduceIte, EStateM.pure, EStateM.throw]
    | UnaryOp operator operand =>
      dsimp only [EStateM.bind]
      cases rh.evalOperandAt choice (OperandPath.rvalue "operand") operand
          (if operator.homogeneous then some (rh.placeLayout dest) else none) s1 with
      | error _ _ => rfl
      | ok op s2 =>
        dsimp only [EStateM.bind]
        cases rh.readImmediate choice op s2 with
        | error _ _ => rfl
        | ok val s3 =>
          dsimp only [EStateM.bind]
          cases rh.unaryOp choice operator val s3 with
          | error _ _ => rfl
          | ok res s4 =>
            dsimp only [EStateM.bind]
            by_cases hEq : (res.layout == rh.placeLayout dest) = true <;>
              simp only [hEq, Bool.false_eq_true, ↓reduceIte, EStateM.pure, EStateM.throw]
    | Aggregate kind operands => rfl
    | Repeat operand _ => rfl
    | Ref _ borrow src =>
      dsimp only [EStateM.bind]
      cases rh.evalPlace choice src true s1 with
      | error _ _ => rfl
      | ok srcV s2 =>
        dsimp only [EStateM.bind]
        cases rh.forceAllocation choice srcV s2 with
        | error _ _ => rfl
        | ok srcMp s3 =>
          dsimp only [EStateM.bind]
          cases rh.toRef choice srcMp s3 <;> rfl
    | Reborrow _ mutability src =>
      dsimp only [EStateM.bind]
      cases rh.evalPlaceToOp choice src none s1 with
      | error _ _ => rfl
      | ok op s2 =>
        dsimp only
        by_cases hMut : (mutability == .Not) = true <;>
          simp only [hMut, Bool.false_eq_true, ↓reduceIte]
    | RawPtr kind src =>
      dsimp only [EStateM.bind]
      cases rh.placeBaseRaw choice src s1 with
      | error _ _ => rfl
      | ok baseRaw s2 =>
        dsimp only [EStateM.bind]
        cases rh.evalPlace choice src false s2 with
        | error _ _ => rfl
        | ok srcV s3 =>
          dsimp only [EStateM.bind]
          cases rh.forceAllocation choice srcV s3 with
          | error _ _ => rfl
          | ok srcMp s4 =>
            dsimp only [EStateM.bind]
            cases rh.toRef choice srcMp s4 with
            | error _ _ => rfl
            | ok imm s5 =>
              dsimp only [EStateM.bind]
              by_cases hRaw : (!baseRaw && kind != .FakeForPtrMetadata) = true
              · simp only [hRaw, ↓reduceIte, EStateM.bind]
                cases rh.withRetagMode choice .Raw
                    (do return (← rh.retagPtrValue choice ⟨imm, rh.placeLayout dest⟩
                      (rh.placeLayout dest).ty).getD ⟨imm, rh.placeLayout dest⟩) s5 <;> rfl
              · simp only [hRaw, Bool.false_eq_true, ↓reduceIte]
    | Cast kind operand ty =>
      dsimp only [EStateM.bind]
      cases rh.evalOperandAt choice (OperandPath.rvalue "operand") operand none s1 with
      | error _ _ => rfl
      | ok src s2 =>
        dsimp only [EStateM.bind]
        cases rh.normalize choice ty s2 <;> rfl
    | Discriminant src =>
      dsimp only [EStateM.bind]
      cases rh.evalPlaceToOp choice src none s1 with
      | error _ _ => rfl
      | ok op s2 =>
        dsimp only [EStateM.bind]
        cases rh.readDiscriminant choice op s2 with
        | error _ _ => rfl
        | ok variant s3 =>
          dsimp only [EStateM.bind]
          cases rh.discriminantForVariant choice op.layout.ty variant s3 <;> rfl
    | WrapUnsafeBinder operand _ =>
      dsimp only [EStateM.bind]
      cases rh.evalOperandAt choice (OperandPath.rvalue "operand") operand none s1 <;> rfl

/-- **Compositional `.Assign` instruction decomposition (`miriInstructionAssignRvalueExactWP_iff`)**:
whenever a `StepHooks.assign` delegates to unmodified `Miri.Interpreter.runRvalue (evalRvalueIntoPlace rh ...)`,
`miriInstructionAction` on `.Assign place rvalue` reduces EXACTLY to `miriEvalRvaluePre`! -/
theorem miriInstructionAssignRvalueExactWP_iff
    (hooks : StepHooks P L E M C V) (rh : RvalueHooks P (StepState P L E M) C V) (choice : C)
    (hAssign : hooks.assign = fun c p rv s => Miri.Interpreter.runRvalue (Miri.Interpreter.evalRvalueIntoPlace rh c rv p) s)
    (sourceInfo : Miri.MIR.SourceInfo) (place : Miri.MIR.Place) (rvalue : Miri.MIR.Rvalue)
    (post : Unit → StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state : StepState P L E M) :
    AnnealExactWP (miriInstructionAction hooks choice ⟨sourceInfo, .Assign place rvalue⟩)
        post onError state ↔
      miriEvalRvaluePre rh choice rvalue place post onError state := by
  rw [miriInstructionExactWP_iff]
  unfold miriInstructionPre
  dsimp only
  rw [hAssign]
  rw [← miriEvalRvalueIntoPlaceExactWP_iff]
  unfold AnnealExactWP miriEvalRvalueAction ExactAction.ofEStateM Miri.Interpreter.runRvalue
  dsimp only
  cases Miri.Interpreter.evalRvalueIntoPlace rh choice rvalue place state with
  | ok u s' => cases u; rfl
  | error err s' => rfl

/-- Fail-closed `.CopyForDeref` corollary: `.Assign place (.CopyForDeref src)` ALWAYS faults with
`.invalidProgram "CopyForDeref in runtime MIR"` once destination `place` evaluates cleanly! -/
theorem miriInstructionAssign_copyForDeref_err_exactWP
    (hooks : StepHooks P L E M C V) (rh : RvalueHooks P (StepState P L E M) C V) (choice : C)
    (hAssign : hooks.assign = fun c p rv s => Miri.Interpreter.runRvalue (Miri.Interpreter.evalRvalueIntoPlace rh c rv p) s)
    (sourceInfo : Miri.MIR.SourceInfo) (place src : Miri.MIR.Place)
    (post : Unit → StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state s1 : StepState P L E M) (dest : V)
    (hDest : rh.evalPlace choice place true state = .ok dest s1) :
    AnnealExactWP (miriInstructionAction hooks choice ⟨sourceInfo, .Assign place (.CopyForDeref src)⟩)
        post onError state ↔
      onError (.invalidProgram "CopyForDeref in runtime MIR") s1 := by
  rw [miriInstructionAssignRvalueExactWP_iff hooks rh choice hAssign]
  unfold miriEvalRvaluePre AnnealExactWP ExactAction.ofEStateM
  rw [hDest]

/-- Specialized `.Use` 3-stage decomposition corollary: evaluates destination place, evaluates source
operand with destination layout, then runs `copyOp` under `RetagMode.Default` / `RetagMode.None`! -/
theorem miriInstructionAssign_use_exactWP_iff
    (hooks : StepHooks P L E M C V) (rh : RvalueHooks P (StepState P L E M) C V) (choice : C)
    (hAssign : hooks.assign = fun c p rv s => Miri.Interpreter.runRvalue (Miri.Interpreter.evalRvalueIntoPlace rh c rv p) s)
    (sourceInfo : Miri.MIR.SourceInfo) (place : Miri.MIR.Place) (operand : Miri.MIR.Operand)
    (retag : Miri.MIR.WithRetag)
    (post : Unit → StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state s1 s2 : StepState P L E M) (dest : V) (op : Miri.Interpreter.OpTy P)
    (hDest : rh.evalPlace choice place true state = .ok dest s1)
    (hOp : rh.evalOperandAt choice (OperandPath.rvalue "operand") operand
      (some (rh.placeLayout dest)) s1 = .ok op s2) :
    AnnealExactWP (miriInstructionAction hooks choice ⟨sourceInfo, .Assign place (.Use operand retag)⟩)
        post onError state ↔
      AnnealExactWP
        (ExactAction.ofEStateM
          (rh.withRetagMode choice (if retag == .Yes then .Default else .None)
            (rh.copyOp choice op dest)))
        post onError s2 := by
  rw [miriInstructionAssignRvalueExactWP_iff hooks rh choice hAssign]
  unfold miriEvalRvaluePre
  simp only [AnnealExactWP, ExactAction.ofEStateM, hDest, hOp]

/-! ### §2.0b. Deep Semantic Decomposition of Vendored `MachineHooks.storageDead` -/

/-- Lift unmodified vendored `Miri.Interpreter.MachineHooks.storageDead` into `ExactAction`. -/
def miriMachineStorageDeadAction {K User : Type}
    (sh : MachineHooks.StorageHooks K User) (localId : Miri.MIR.LocalId) :
    ExactAction (PlaceMachine.State K User) StepError Unit :=
  ExactAction.ofEStateM (MachineHooks.storageDead sh localId)

/-- **Exact bidirectional `↔` theorem `miriMachineStorageDeadExactWP_iff`**: decomposes unmodified
vendored `Miri.Interpreter.MachineHooks.storageDead` across return-place guard (`localId == 0`),
active-frame lookup, local-slot lookup, local replacement with `.dead`, and indirect-storage
deallocation (`deallocateStack` iff `.live (.indirect place)`)! -/
theorem miriMachineStorageDeadExactWP_iff {K User : Type}
    (sh : MachineHooks.StorageHooks K User) (localId : Miri.MIR.LocalId)
    (post : Unit → PlaceMachine.State K User → Prop)
    (onError : StepError → PlaceMachine.State K User → Prop)
    (state : PlaceMachine.State K User) :
    AnnealExactWP (miriMachineStorageDeadAction sh localId) post onError state ↔
      if localId == 0 then
        onError (.stack .cannotMakeReturnPlaceDead) state
      else
        match state.stack.currentFrame? with
        | none => onError (.stack .emptyStack) state
        | some frame =>
          match frame.getLocal localId with
          | .error e => onError (.stack e) state
          | .ok oldSlot =>
            match frame.replaceLocalValue localId .dead with
            | .error e => onError (.stack e) state
            | .ok updatedFrame =>
              if state.stack.frames.isEmpty then
                onError (.stack .emptyStack) state
              else
                let stAfterSet : PlaceMachine.State K User :=
                  { state with stack := ⟨state.stack.frames.pop.push updatedFrame⟩ }
                match oldSlot.value with
                | .live (.indirect place) =>
                  AnnealExactWP (ExactAction.ofEStateM (sh.deallocateStack place.ptr))
                    post onError stAfterSet
                | _ => post () stAfterSet := by
  unfold miriMachineStorageDeadAction MachineHooks.storageDead MachineHooks.currentFrame
    MachineHooks.setCurrentFrame
  unfold_pm
  simp only [AnnealExactWP, ExactAction.ofEStateM, get, getThe, MonadStateOf.get,
    set, MonadStateOf.set, bind, Bind.bind, pure, Pure.pure,
    throw, MonadExcept.throw, throwThe, MonadExceptOf.throw]
  by_cases hZero : (localId == 0) = true
  · simp only [hZero, ↓reduceIte, EStateM.bind, EStateM.throw]
  · simp only [hZero, Bool.false_eq_true, ↓reduceIte, EStateM.bind, EStateM.get]
    cases hFr : state.stack.currentFrame? with
    | none => simp only [EStateM.throw]
    | some frame =>
      dsimp only [EStateM.pure]
      cases hGet : frame.getLocal localId with
      | error e => simp only [EStateM.throw]
      | ok oldSlot =>
        dsimp only [EStateM.pure]
        cases hRep : frame.replaceLocalValue localId .dead with
        | error e => simp only [EStateM.throw]
        | ok updatedFrame =>
          dsimp only [EStateM.pure, EStateM.get]
          by_cases hEmp : state.stack.frames.isEmpty = true
          · simp only [hEmp, ↓reduceIte, EStateM.bind, EStateM.throw]
          · simp only [hEmp, Bool.false_eq_true, ↓reduceIte, EStateM.set]
            cases oldSlot.value with
            | dead => simp only [EStateM.pure]
            | live op =>
              cases op with
              | immediate _ => simp only [EStateM.pure]
              | indirect _ => rfl

/-- **Machine & sibling-local frame law for `MachineHooks.storageDead`**: killing any non-return
immediate or dead local (`localId ≠ 0`) updates ONLY slot `localId` of the top frame, preserving
EVERY other local `j ≠ localId`, EVERY suspended caller frame, and the ENTIRE `state.machine`
(all memory bytes, `BorrowTree`s, `borrowTracker`, and `dataRace`) identically! -/
theorem miriMachineStorageDead_imm_frame_otherLocals {K User : Type}
    (sh : MachineHooks.StorageHooks K User) (localId : Miri.MIR.LocalId)
    (hNonZero : localId ≠ 0)
    (state : PlaceMachine.State K User)
    (frame updatedFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (oldSlot : LocalState Provenance LocalLayout)
    (hFrame : state.stack.currentFrame? = some frame)
    (hGet : frame.getLocal localId = .ok oldSlot)
    (hNotIndirect : ∀ mp, oldSlot.value ≠ .live (.indirect mp))
    (hRep : frame.replaceLocalValue localId .dead = .ok updatedFrame)
    (post : Unit → PlaceMachine.State K User → Prop)
    (onError : StepError → PlaceMachine.State K User → Prop) :
    let stAfter : PlaceMachine.State K User :=
      { state with stack := ⟨state.stack.frames.pop.push updatedFrame⟩ }
    stAfter.machine = state.machine ∧
    (∀ i, i < state.stack.frames.size - 1 →
      stAfter.stack.frames[i]? = state.stack.frames[i]?) ∧
    (AnnealExactWP (miriMachineStorageDeadAction sh localId) post onError state ↔
      post () stAfter) := by
  have hNonEmpty : state.stack.frames.isEmpty = false := by
    unfold Stack.currentFrame? at hFrame
    cases hSz : state.stack.frames.size with
    | zero => simp [Array.back?, hSz] at hFrame
    | succ k => simp [Array.isEmpty, hSz]
  have hZeroF : (localId == 0) = false := beq_false_of_ne hNonZero
  refine ⟨rfl, ?_, ?_⟩
  · intro i hi
    dsimp only
    have hPopSz : state.stack.frames.pop.size = state.stack.frames.size - 1 := Array.size_pop
    have hiPop : i < state.stack.frames.pop.size := by omega
    have hiOrig : i < state.stack.frames.size := by omega
    simp only [Array.getElem?_push_lt hiPop,
      Array.getElem?_eq_getElem hiOrig, Array.getElem_pop]
  · cases hV : oldSlot.value with
    | dead =>
      rw [miriMachineStorageDeadExactWP_iff]
      simp only [hZeroF, Bool.false_eq_true, ↓reduceIte, hFrame, hGet, hRep, hNonEmpty, hV]
    | live op =>
      cases op with
      | immediate _ =>
        rw [miriMachineStorageDeadExactWP_iff]
        simp only [hZeroF, Bool.false_eq_true, ↓reduceIte, hFrame, hGet, hRep, hNonEmpty, hV]
      | indirect mp => exact False.elim (hNotIndirect mp hV)

/-- **Exact bidirectional `↔` `Step.step` statement-position law (`miriStepStmtExactWP_iff`)**:
when the active frame is at a valid statement `block.statements[loc.statementIndex]? = some stmt`,
unmodified `Miri.Interpreter.Step.step` executes `miriInstructionAction hooks choice stmt`,
verifies frame index stability, checks the `.mir` location, and advances `statementIndex + 1`
while framing all caller frames (`i < frames.size - 1`) untouched! -/
theorem miriStepStmtExactWP_iff (hooks : StepHooks P L E M C V) (choice : C)
    (post : Bool → StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state : StepState P L E M) (frame : Frame P L E)
    (loc : Miri.MIR.Location) (bb : Miri.MIR.BasicBlock) (stmt : Miri.MIR.Statement)
    (hFrame : state.stack.currentFrame? = some frame)
    (hLoc : frame.location = .mir loc)
    (hBlock : frame.body.basicBlocks[loc.block]? = some bb)
    (hStmt : bb.statements[loc.statementIndex]? = some stmt) :
    AnnealExactWP (miriStepAction hooks choice) post onError state ↔
      AnnealExactWP (miriInstructionAction hooks choice stmt)
        (fun _ after =>
          let oldIndex := state.stack.frames.size - 1
          let newIndex := after.stack.frames.size - 1
          if oldIndex != newIndex then
            onError (.frameIndexChanged oldIndex newIndex) after
          else
            match after.stack.currentFrame? with
            | none => onError (.stack .emptyStack) after
            | some current =>
              match current.location with
              | .unwinding _ => onError .expectedMirLocation after
              | .mir currentLoc =>
                let next := { currentLoc with statementIndex := currentLoc.statementIndex + 1 }
                if h : newIndex < after.stack.frames.size then
                  post true
                    { after with
                      stack :=
                        { frames := after.stack.frames.set newIndex
                            { current with location := .mir next } h } }
                else
                  onError (.stack .emptyStack) after)
        onError state := by
  rw [miriStepExactWP_iff]
  unfold miriStepPre Step.step AnnealExactWP miriInstructionAction
  simp only [Id.run, hFrame, hLoc, hBlock, hStmt, pure, Pure.pure]
  cases Step.evalStatement hooks choice stmt state with
  | mk after res =>
    dsimp only
    cases res with
    | error err => rfl
    | ok u =>
      cases u
      dsimp only
      cases ((state.stack.frames.size - 1 != after.stack.frames.size - 1)) with
      | true => simp only [↓reduceIte]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases after.stack.currentFrame? with
        | none => rfl
        | some current =>
          dsimp only
          cases current.location with
          | unwinding _ => rfl
          | mir currentLoc =>
            dsimp only
            by_cases hLt : after.stack.frames.size - 1 < after.stack.frames.size <;>
              simp only [hLt, ↓reduceDIte]

/-- Frame-preservation corollary for `Step.step` statement advancement: updating the top frame's
program counter (`frames.set (frames.size - 1) ...`) leaves EVERY suspended caller frame
`i < frames.size - 1` identically untouched! -/
theorem miriStepStmt_callerFrames_preserved (frames : Array (Frame P L E))
    (updatedTop : Frame P L E) (hTop : frames.size - 1 < frames.size)
    (i : Nat) (hi : i < frames.size - 1) :
    (frames.set (frames.size - 1) updatedTop hTop)[i]? = frames[i]? := by
  have hNe : frames.size - 1 ≠ i := by omega
  simp [hNe]

/-- **Compositional caller-stack frame law (`miriStepStmt_frame_callerStack`)**: if a statement
executes cleanly to `after` without altering stack depth or any suspended caller frame
(`i < frames.size - 1`), then `Step.step` advances ONLY the top frame's `statementIndex` and
frames EVERY suspended caller frame identically! -/
theorem miriStepStmt_frame_callerStack (hooks : StepHooks P L E M C V) (choice : C)
    (post : Bool → StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state after : StepState P L E M) (frame current : Frame P L E)
    (loc currentLoc : Miri.MIR.Location) (bb : Miri.MIR.BasicBlock) (stmt : Miri.MIR.Statement)
    (hFrame : state.stack.currentFrame? = some frame)
    (hLoc : frame.location = .mir loc)
    (hBlock : frame.body.basicBlocks[loc.block]? = some bb)
    (hStmt : bb.statements[loc.statementIndex]? = some stmt)
    (hEval : Step.evalStatement hooks choice stmt state = (after, .ok ()))
    (hSameDepth : after.stack.frames.size = state.stack.frames.size)
    (hAfterTop : after.stack.currentFrame? = some current)
    (hAfterLoc : current.location = .mir currentLoc)
    (hCallerFrames : ∀ i, i < state.stack.frames.size - 1 →
      after.stack.frames[i]? = state.stack.frames[i]?) :
    ∃ hTop : after.stack.frames.size - 1 < after.stack.frames.size,
      let nextState : StepState P L E M :=
        { after with
          stack :=
            { frames := after.stack.frames.set (after.stack.frames.size - 1)
                { current with location := .mir { currentLoc with statementIndex := currentLoc.statementIndex + 1 } }
                hTop } }
      (∀ i, i < state.stack.frames.size - 1 → nextState.stack.frames[i]? = state.stack.frames[i]?) ∧
      (AnnealExactWP (miriStepAction hooks choice) post onError state ↔ post true nextState) := by
  have hTop : after.stack.frames.size - 1 < after.stack.frames.size := by
    unfold Stack.currentFrame? at hAfterTop
    cases hSz : after.stack.frames.size with
    | zero => simp [Array.back?, hSz] at hAfterTop
    | succ k => omega
  refine ⟨hTop, ?_, ?_⟩
  · intro i hi
    have hi' : i < after.stack.frames.size - 1 := by omega
    rw [miriStepStmt_callerFrames_preserved after.stack.frames _ hTop i hi']
    exact hCallerFrames i hi
  · rw [miriStepStmtExactWP_iff hooks choice post onError state frame loc bb stmt
      hFrame hLoc hBlock hStmt]
    unfold AnnealExactWP miriInstructionAction
    rw [hEval]
    dsimp only
    simp only [hSameDepth, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      hAfterTop, hAfterLoc]
    have hTop' : state.stack.frames.size - 1 < state.stack.frames.size := by omega
    simp only [hTop', ↓reduceDIte]

/-! ### §2.1. Call-Dispatch WP (`CallDispatchMachine.findMirOrEvalFn` & `callExtra` & `.Call` Terminator) -/

section CallDispatchWP

variable {S Other : Type}

/-- Lift unmodified `Miri.Interpreter.CallDispatchMachine.findMirOrEvalFn` into `ExactAction`. -/
def miriCallDispatchAction (h : CallDispatchMachine.Hooks S C Other) (choice : C)
    (callee : CallInstance) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (FnArg Provenance)) (destination : RuntimeStackPlace Provenance)
    (ret : Option Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction) :
    ExactAction S StepError (Option (LoadedBody × CallInstance)) :=
  ExactAction.ofEStateM
    (CallDispatchMachine.findMirOrEvalFn h choice callee abi args destination ret unwind)

/-- Exact symbolic precondition mirroring `lean-miri#94` `miri_call_dispatch_wp` over unmodified
`Miri.Interpreter.CallDispatchMachine.findMirOrEvalFn`: explicitly distinguishes foreign-item
emulation, missing-foreign failure, backend-selection error, and MIR body loading! -/
def miriCallDispatchPre (h : CallDispatchMachine.Hooks S C Other) (choice : C)
    (callee : CallInstance) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (FnArg Provenance)) (destination : RuntimeStackPlace Provenance)
    (ret : Option Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction)
    (post : Option (LoadedBody × CallInstance) → S → Prop)
    (onError : StepError → S → Prop)
    (state : S) : Prop :=
  match h.isForeignItem callee state with
  | .error err s1 => onError err s1
  | .ok true s1 =>
    match h.symbolName callee s1 with
    | .error err s2 => onError err s2
    | .ok name s2 =>
      match h.foreign with
      | none =>
        onError (.unsupported s!"foreign call requires complete source platform input: {name}") s2
      | some foreignAction =>
        AnnealExactWP
          (ExactAction.ofEStateM
            (h.foreignScope (do
              let foreign ← foreignAction
              ForeignItems.emulate foreign name abi (args.map FnArg.copyFnArg)
                destination.toRuntimePlace ret unwind)))
          post onError s2
  | .ok false s1 =>
    match h.backend.selection s1 with
    | .error err => onError err s1
    | .ok _ =>
      match h.loadMir choice callee s1 with
      | .error err s2 => onError err s2
      | .ok body s2 => post (some (body, callee)) s2

/-- **Exact bidirectional `↔` theorem `miriCallDispatchExactWP_iff`** (mirroring `lean-miri#94`'s
`miri_call_dispatch_wp`) directly over unmodified `Miri.Interpreter.CallDispatchMachine.findMirOrEvalFn`! -/
theorem miriCallDispatchExactWP_iff (h : CallDispatchMachine.Hooks S C Other) (choice : C)
    (callee : CallInstance) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (FnArg Provenance)) (destination : RuntimeStackPlace Provenance)
    (ret : Option Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction)
    (post : Option (LoadedBody × CallInstance) → S → Prop)
    (onError : StepError → S → Prop)
    (state : S) :
    AnnealExactWP (miriCallDispatchAction h choice callee abi args destination ret unwind)
        post onError state ↔
      miriCallDispatchPre h choice callee abi args destination ret unwind post onError state := by
  unfold AnnealExactWP miriCallDispatchAction miriCallDispatchPre ExactAction.ofEStateM
    CallDispatchMachine.findMirOrEvalFn
  simp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure,
    get, MonadState.get, throw, MonadExcept.throw]
  cases hIsF : h.isForeignItem callee state with
  | error err s1 => rfl
  | ok isForeign s1 =>
    dsimp only
    cases isForeign with
    | true =>
      simp only [↓reduceIte, EStateM.bind]
      cases hSym : h.symbolName callee s1 with
      | error err s2 => rfl
      | ok name s2 =>
        dsimp only
        cases hFor : h.foreign with
        | none =>
          simp only [throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind]
        | some foreignAction =>
          unfold AnnealExactWP
          rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, EStateM.bind, getThe, MonadStateOf.get, EStateM.get]
      cases hBack : h.backend.selection s1 with
      | error err =>
        simp only [throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind]
      | ok selected =>
        simp only [EStateM.pure, EStateM.bind]
        cases h.loadMir choice callee s1 <;> rfl

/-- Specialized branch corollary: missing foreign hooks (`h.foreign = none`) on a foreign item
faults with `.unsupported "foreign call requires complete source platform input: ..."`! -/
theorem miriCallDispatch_missingForeign_exactWP (h : CallDispatchMachine.Hooks S C Other)
    (choice : C) (callee : CallInstance) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (FnArg Provenance)) (destination : RuntimeStackPlace Provenance)
    (ret : Option Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction)
    (post : Option (LoadedBody × CallInstance) → S → Prop)
    (onError : StepError → S → Prop)
    (state s1 s2 : S) (name : String)
    (hIsF : h.isForeignItem callee state = .ok true s1)
    (hSym : h.symbolName callee s1 = .ok name s2)
    (hNone : h.foreign = none) :
    AnnealExactWP (miriCallDispatchAction h choice callee abi args destination ret unwind)
        post onError state ↔
      onError (.unsupported s!"foreign call requires complete source platform input: {name}") s2 := by
  rw [miriCallDispatchExactWP_iff]
  unfold miriCallDispatchPre
  rw [hIsF]; dsimp only
  rw [hSym]; dsimp only
  rw [hNone]

/-- Specialized branch corollary: non-foreign call with backend selection error faults with that
exact backend error! -/
theorem miriCallDispatch_backendError_exactWP (h : CallDispatchMachine.Hooks S C Other)
    (choice : C) (callee : CallInstance) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (FnArg Provenance)) (destination : RuntimeStackPlace Provenance)
    (ret : Option Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction)
    (post : Option (LoadedBody × CallInstance) → S → Prop)
    (onError : StepError → S → Prop)
    (state s1 : S) (err : StepError)
    (hNotF : h.isForeignItem callee state = .ok false s1)
    (hBackErr : h.backend.selection s1 = .error err) :
    AnnealExactWP (miriCallDispatchAction h choice callee abi args destination ret unwind)
        post onError state ↔
      onError err s1 := by
  rw [miriCallDispatchExactWP_iff]
  unfold miriCallDispatchPre
  rw [hNotF]; dsimp only
  rw [hBackErr]

/-- Specialized branch corollary: non-foreign call with valid backend loads MIR body via `loadMir`. -/
theorem miriCallDispatch_loadMir_exactWP (h : CallDispatchMachine.Hooks S C Other)
    (choice : C) (callee : CallInstance) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (FnArg Provenance)) (destination : RuntimeStackPlace Provenance)
    (ret : Option Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction)
    (post : Option (LoadedBody × CallInstance) → S → Prop)
    (onError : StepError → S → Prop)
    (state s1 s2 : S) (selected : IntrinsicBackend.Kind) (body : LoadedBody)
    (hNotF : h.isForeignItem callee state = .ok false s1)
    (hBackOk : h.backend.selection s1 = .ok selected)
    (hLoadOk : h.loadMir choice callee s1 = .ok body s2) :
    AnnealExactWP (miriCallDispatchAction h choice callee abi args destination ret unwind)
        post onError state ↔
      post (some (body, callee)) s2 := by
  rw [miriCallDispatchExactWP_iff]
  unfold miriCallDispatchPre
  rw [hNotF]; dsimp only
  rw [hBackOk]; dsimp only
  rw [hLoadOk]

/-- Specialized branch corollary: foreign item with configured `h.foreign = some foreignAction`
routes directly into unmodified vendored `Miri.Interpreter.ForeignItems.emulate`! -/
theorem miriCallDispatch_foreignEmulate_exactWP (h : CallDispatchMachine.Hooks S C Other)
    (choice : C) (callee : CallInstance) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (FnArg Provenance)) (destination : RuntimeStackPlace Provenance)
    (ret : Option Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction)
    (post : Option (LoadedBody × CallInstance) → S → Prop)
    (onError : StepError → S → Prop)
    (state s1 s2 : S) (name : String)
    (foreignAction : CallDispatchMachine.M S
      (ForeignItems.Hooks Provenance S (RuntimePlace Provenance) (RuntimePlace Provenance)
        (Pointer (Option Provenance)) LoadedBody CallInstance))
    (hIsF : h.isForeignItem callee state = .ok true s1)
    (hSym : h.symbolName callee s1 = .ok name s2)
    (hFor : h.foreign = some foreignAction) :
    AnnealExactWP (miriCallDispatchAction h choice callee abi args destination ret unwind)
        post onError state ↔
      AnnealExactWP
        (ExactAction.ofEStateM
          (h.foreignScope (do
            let foreign ← foreignAction
            ForeignItems.emulate foreign name abi (args.map FnArg.copyFnArg)
              destination.toRuntimePlace ret unwind)))
        post onError s2 := by
  rw [miriCallDispatchExactWP_iff]
  unfold miriCallDispatchPre
  rw [hIsF]; dsimp only
  rw [hSym]; dsimp only
  rw [hFor]

/-- Lift unmodified `Miri.Interpreter.CallDispatchMachine.callExtra` into `ExactAction`. -/
def miriCallExtraAction (h : CallDispatchMachine.Hooks S C Other) (choice : C)
    (symbol : Other) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (FnArg Provenance)) (destination : RuntimeStackPlace Provenance)
    (ret : Option Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction) :
    ExactAction S StepError Unit :=
  ExactAction.ofEStateM
    (CallDispatchMachine.callExtra h choice symbol abi args destination ret unwind)

/-- **Exact bidirectional `↔` theorem `miriCallExtraExactWP_iff`** for unmodified
`Miri.Interpreter.CallDispatchMachine.callExtra`! -/
theorem miriCallExtraExactWP_iff (h : CallDispatchMachine.Hooks S C Other) (choice : C)
    (symbol : Other) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (FnArg Provenance)) (destination : RuntimeStackPlace Provenance)
    (ret : Option Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) (state : S) :
    AnnealExactWP (miriCallExtraAction h choice symbol abi args destination ret unwind)
        post onError state ↔
      match h.foreign with
      | none =>
        onError (.unsupported "dynamic foreign call requires complete source platform input") state
      | some foreignAction =>
        AnnealExactWP
          (ExactAction.ofEStateM
            (h.foreignScope (do
              let foreign ← foreignAction
              ForeignItems.emulateDynSym foreign (h.dynSymName symbol) abi
                (args.map FnArg.copyFnArg) destination.toRuntimePlace ret unwind)))
          post onError state := by
  unfold AnnealExactWP miriCallExtraAction ExactAction.ofEStateM CallDispatchMachine.callExtra
  cases hFor : h.foreign with
  | none =>
    simp only [throw, MonadExcept.throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  | some foreignAction =>
    dsimp only
    cases h.foreignScope
        (do
          let foreign ← foreignAction
          ForeignItems.emulateDynSym foreign (h.dynSymName symbol) abi
            (args.map FnArg.copyFnArg) destination.toRuntimePlace ret unwind) state <;> rfl

/-! ### §2.1a. Symbolic Decomposition of Unmodified `Miri.Interpreter.ForeignItems.emulate` -/

/-- Lift unmodified vendored `Miri.Interpreter.ForeignItems.emulate` into `ExactAction`. -/
def miriForeignEmulateAction {P S D MD Ptr B I : Type}
    (fh : ForeignItems.Hooks P S D MD Ptr B I) (name : String) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (Miri.Interpreter.OpTy P)) (dest : D)
    (ret : Option Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction) :
    ExactAction S StepError (Option (B × I)) :=
  ExactAction.ofEStateM (ForeignItems.emulate fh name abi args dest ret unwind)

/-- **Symbolic `ForeignItems.emulate` `"abort"` law (`miriForeignEmulate_abort_exactWP`)**:
under standard non-native, non-allocator configuration with valid C void ABI, calling foreign
`"abort"` ALWAYS faults with `.machineStop "the program aborted execution"` (and via `↔` refutes
pure safety)! -/
theorem miriForeignEmulate_abort_exactWP {P S D MD Ptr B I : Type}
    (fh : ForeignItems.Hooks P S D MD Ptr B I) (abi : FnAbi Miri.MIR.TyId)
    (dest : D) (mdest : MD) (ret : Option Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction)
    (post : Option (B × I) → S → Prop) (onError : StepError → S → Prop) (state s1 s2 s3 : S)
    (hAlloc : fh.allocatorSymbol "abort" state = .ok none s1)
    (hForce : fh.forceAllocation dest s1 = .ok mdest s2)
    (hNoNative : fh.nativeEnabled = false)
    (hNoShim : fh.noAllocShimSymbol ≠ "abort")
    (hSig : ForeignItems.checkSignature fh "abort" ⟨.C, #[], .unit⟩ abi #[] s2 = .ok #[] s3) :
    AnnealExactWP (miriForeignEmulateAction fh "abort" abi #[] dest ret unwind)
        post onError state ↔
      onError (.machineStop "the program aborted execution") s3 := by
  unfold miriForeignEmulateAction ForeignItems.emulate ForeignItems.inner
  have hShimF : ("abort" == fh.noAllocShimSymbol) = false := beq_false_of_ne hNoShim.symm
  have hMalloc : (("abort" == "malloc") || ("abort" == "calloc") ||
      ("abort" == "realloc") || ("abort" == "free")) = false := rfl
  have hExit : ("abort" == "exit") = false := rfl
  have hAbort : ("abort" == "abort") = true := rfl
  simp only [AnnealExactWP, ExactAction.ofEStateM, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, throw, MonadExcept.throw, throwThe, MonadExceptOf.throw,
    hAlloc, hForce, hNoNative, hShimF, hMalloc, hExit, hAbort, Bool.false_eq_true, ↓reduceIte,
    hSig, EStateM.throw]

/-- **Symbolic `ForeignItems.emulate` `noAllocShimSymbol` law (`miriForeignEmulate_noAllocShim_exactWP`)**:
calling `fh.noAllocShimSymbol` (e.g. `"__rust_no_alloc_shim_is_unstable_v2"`) with valid Rust void ABI
ALWAYS invokes `fh.returnToBlock ret` and returns `.ok none`! -/
theorem miriForeignEmulate_noAllocShim_exactWP {P S D MD Ptr B I : Type}
    (fh : ForeignItems.Hooks P S D MD Ptr B I) (abi : FnAbi Miri.MIR.TyId)
    (dest : D) (mdest : MD) (ret : Option Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction)
    (post : Option (B × I) → S → Prop) (onError : StepError → S → Prop) (state s1 s2 s3 : S)
    (hAlloc : fh.allocatorSymbol fh.noAllocShimSymbol state = .ok none s1)
    (hForce : fh.forceAllocation dest s1 = .ok mdest s2)
    (hNoNative : fh.nativeEnabled = false)
    (hSig : ForeignItems.checkSignature fh fh.noAllocShimSymbol ⟨.Rust, #[], .unit⟩ abi #[] s2 =
      .ok #[] s3) :
    AnnealExactWP (miriForeignEmulateAction fh fh.noAllocShimSymbol abi #[] dest ret unwind)
        post onError state ↔
      AnnealExactWP (ExactAction.ofEStateM (fh.returnToBlock ret))
        (fun _ s4 => post none s4) onError s3 := by
  unfold miriForeignEmulateAction ForeignItems.emulate ForeignItems.inner
  simp only [AnnealExactWP, ExactAction.ofEStateM, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, hAlloc, hForce, hNoNative, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte,
    hSig, EStateM.pure]
  cases fh.returnToBlock ret s3 with
  | ok u s4 => cases u; rfl
  | error err s4 => rfl

end CallDispatchWP

/-- Lift unmodified `Miri.Interpreter.ControlFlow.evalTerminator` into `ExactAction`. -/
def miriEvalTerminatorAction {Op Imm : Type}
    (hooks : TerminatorHooks P L E M C Op Imm) (choice : C) (term : Miri.MIR.Terminator) :
    ExactAction (StepState P L E M) StepError Unit :=
  fun state =>
    match ControlFlow.evalTerminator hooks choice term state with
    | (after, .ok ()) => .ok () after
    | (after, .error err) => .error err after

/-- **Exact bidirectional `↔` `.Call` terminator dispatch WP (`miriCallTerminatorExactWP_iff`)**:
characterizes `ControlFlow.evalTerminator` on `.Call`, including both `hooks.call` errors AND
rustc's no-progress guard (`.invalidProgram "evaluating this call made no progress"`)! -/
theorem miriCallTerminatorExactWP_iff {Op Imm : Type}
    (hooks : TerminatorHooks P L E M C Op Imm) (choice : C)
    (func : Miri.MIR.Operand) (args : Array Miri.MIR.SpannedOperand) (dest : Miri.MIR.Place)
    (target : Option Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction)
    (callSource : Miri.MIR.CallSource) (fnSpan : Miri.MIR.SpanRef)
    (sourceInfo : Miri.MIR.SourceInfo)
    (post : Unit → StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state : StepState P L E M) :
    let term : Miri.MIR.Terminator :=
      ⟨sourceInfo, .Call func args dest target unwind callSource fnSpan⟩
    AnnealExactWP (miriEvalTerminatorAction hooks choice term) post onError state ↔
      let oldIndex := state.stack.frames.size
      let oldLoc := state.stack.currentFrame?.map (·.location)
      match hooks.call choice term state with
      | (after, .error err) => onError err after
      | (after, .ok ()) =>
        if target.isSome && after.stack.frames.size == oldIndex &&
            after.stack.currentFrame?.map (·.location) == oldLoc then
          onError (.invalidProgram "evaluating this call made no progress") after
        else
          post () after := by
  dsimp only
  unfold AnnealExactWP miriEvalTerminatorAction ControlFlow.evalTerminator
  simp only [Id.run, pure, Pure.pure]
  cases hCall : hooks.call choice ⟨sourceInfo, .Call func args dest target unwind callSource fnSpan⟩ state with
  | mk after res =>
    simp only [hCall]
    cases res with
    | error err => rfl
    | ok u =>
      cases u
      dsimp only
      by_cases hProg :
          (target.isSome && (after.stack.frames.size == state.stack.frames.size) &&
            (after.stack.currentFrame?.map (·.location) == state.stack.currentFrame?.map (·.location))) = true <;>
        simp only [hProg, Bool.false_eq_true, ↓reduceIte]

/-- **Exact bidirectional `↔` `Step.step` `.Call` terminator dispatch theorem
(`miriStepCallTerminatorExactWP_iff`)**: connects `Step.step` at the end of a basic block whose
terminator is `.Call` directly through `beforeTerminator`, `termHooks.call`, and rustc's
no-progress guard! -/
theorem miriStepCallTerminatorExactWP_iff {Op Imm : Type}
    (stepHooks : StepHooks P L E M C V) (termHooks : TerminatorHooks P L E M C Op Imm)
    (choice : C)
    (hTermEq : stepHooks.terminator = ControlFlow.evalTerminator termHooks)
    (post : Bool → StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state : StepState P L E M) (frame : Frame P L E)
    (loc : Miri.MIR.Location) (bb : Miri.MIR.BasicBlock)
    (func : Miri.MIR.Operand) (args : Array Miri.MIR.SpannedOperand) (dest : Miri.MIR.Place)
    (target : Option Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction)
    (callSource : Miri.MIR.CallSource) (fnSpan : Miri.MIR.SpanRef)
    (sourceInfo : Miri.MIR.SourceInfo)
    (hFrame : state.stack.currentFrame? = some frame)
    (hLoc : frame.location = .mir loc)
    (hBlock : frame.body.basicBlocks[loc.block]? = some bb)
    (hEnd : bb.statements[loc.statementIndex]? = none)
    (hCallTerm : bb.terminator = ⟨sourceInfo, .Call func args dest target unwind callSource fnSpan⟩) :
    let term : Miri.MIR.Terminator :=
      ⟨sourceInfo, .Call func args dest target unwind callSource fnSpan⟩
    AnnealExactWP (miriStepAction stepHooks choice) post onError state ↔
      match stepHooks.beforeTerminator choice state with
      | (s1, .error err) => onError err s1
      | (s1, .ok ()) =>
        let oldIndex := s1.stack.frames.size
        let oldLoc := s1.stack.currentFrame?.map (·.location)
        match termHooks.call choice term s1 with
        | (after, .error err) => onError err after
        | (after, .ok ()) =>
          if target.isSome && after.stack.frames.size == oldIndex &&
              after.stack.currentFrame?.map (·.location) == oldLoc then
            onError (.invalidProgram "evaluating this call made no progress") after
          else
            post true after := by
  dsimp only
  rw [miriStepExactWP_terminator stepHooks choice post onError state frame loc bb
    hFrame hLoc hBlock hEnd, hTermEq, hCallTerm]
  cases stepHooks.beforeTerminator choice state with
  | mk s1 r1 =>
    cases r1 with
    | error err => rfl
    | ok u =>
      cases u
      dsimp only
      have hCall := miriCallTerminatorExactWP_iff termHooks choice func args dest target unwind
        callSource fnSpan sourceInfo (fun _ s2 => post true s2) onError s1
      dsimp only at hCall
      rw [← hCall]
      unfold AnnealExactWP miriEvalTerminatorAction
      cases ControlFlow.evalTerminator termHooks choice
        ⟨sourceInfo, .Call func args dest target unwind callSource fnSpan⟩ s1 with
      | mk s2 r2 => cases r2 with | ok u' => cases u'; rfl | error _ => rfl

/-- **Unified `ControlFlow.evalTerminator` Exact WP (`miriTerminatorExactWP_iff`)**:
genuinely decomposes unmodified `Miri.Interpreter.ControlFlow.evalTerminator` across `.Goto`
(`goToBlock`), `.Return`/`.UnwindResume` (`returnFromCurrentFrame`), `.UnwindTerminate`,
`.Unreachable` (always `.undefinedBehavior "Unreachable"`), `.InlineAsm` (always `.unsupported`),
eliminated MIR terminators (`.FalseEdge`/`.FalseUnwind`/`.Yield`/`.CoroutineDrop`), `.TailCall`
(frame-index-changed guard), `.Drop` (async-drop rejection), and `.Assert` (optional overflow check
guard)! -/
theorem miriTerminatorExactWP_iff {Op Imm : Type}
    (hooks : TerminatorHooks P L E M C Op Imm) (choice : C)
    (term : Miri.MIR.Terminator)
    (post : Unit → StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state : StepState P L E M) :
    AnnealExactWP (miriEvalTerminatorAction hooks choice term) post onError state ↔
      match term.kind with
      | .Goto target _ =>
        match state.stack.currentFrame? with
        | none => onError (.stack .emptyStack) state
        | some frame =>
          post ()
            { state with
              stack := ⟨state.stack.frames.pop.push { frame with location := .mir ⟨target, 0⟩ }⟩ }
      | .Return =>
        match ControlFlow.returnFromCurrentFrame hooks.toControlHooks choice false state with
        | (after, .ok ()) => post () after
        | (after, .error err) => onError err after
      | .UnwindResume =>
        match ControlFlow.returnFromCurrentFrame hooks.toControlHooks choice true state with
        | (after, .ok ()) => post () after
        | (after, .error err) => onError err after
      | .UnwindTerminate reason =>
        match hooks.unwindTerminate choice reason state with
        | (after, .ok ()) => post () after
        | (after, .error err) => onError err after
      | .Unreachable => onError (.undefinedBehavior "Unreachable") state
      | .InlineAsm _ => onError (.unsupported "inline assembly") state
      | .FalseEdge .. | .FalseUnwind .. | .Yield .. | .CoroutineDrop =>
        onError (.invalidProgram "terminator should have been eliminated by MIR pass") state
      | .SwitchInt .. =>
        match ControlFlow.evalTerminator hooks choice term state with
        | (after, .ok ()) => post () after
        | (after, .error err) => onError err after
      | .Call _ _ _ target .. =>
        let oldIndex := state.stack.frames.size
        let oldLoc := state.stack.currentFrame?.map (·.location)
        match hooks.call choice term state with
        | (after, .error err) => onError err after
        | (after, .ok ()) =>
          if target.isSome && after.stack.frames.size == oldIndex &&
              after.stack.currentFrame?.map (·.location) == oldLoc then
            onError (.invalidProgram "evaluating this call made no progress") after
          else
            post () after
      | .TailCall .. =>
        let oldIndex := state.stack.frames.size
        match hooks.tailCall choice term state with
        | (after, .error err) => onError err after
        | (after, .ok ()) =>
          if after.stack.frames.size != oldIndex then
            onError (.invalidProgram "tail call changed frame index") after
          else
            post () after
      | .Drop place target unwind _ asyncDrop =>
        if asyncDrop.isSome then
          onError (.invalidProgram "Async Drop must be expanded or reset to sync") state
        else
          match hooks.drop choice place target unwind state with
          | (after, .ok ()) => post () after
          | (after, .error err) => onError err after
      | .Assert condition expected message target unwind =>
        let ignored := hooks.ignoreOptionalOverflowChecks state &&
          ControlFlow.isOptionalOverflowCheck message
        match hooks.readAssertCondition choice condition state with
        | (s1, .error err) => onError err s1
        | (s1, .ok value) =>
          if ignored || expected == value then
            match s1.stack.currentFrame? with
            | none => onError (.stack .emptyStack) s1
            | some frame =>
              post ()
                { s1 with
                  stack := ⟨s1.stack.frames.pop.push { frame with location := .mir ⟨target, 0⟩ }⟩ }
          else
            match hooks.assertPanic choice message unwind s1 with
            | (after, .ok ()) => post () after
            | (after, .error err) => onError err after := by
  rcases term with ⟨sourceInfo, kind⟩
  cases kind with
  | Goto target _ =>
    unfold AnnealExactWP miriEvalTerminatorAction ControlFlow.evalTerminator
      ControlFlow.goToBlock ControlFlow.setLocation
    dsimp only [Id.run]
    cases state.stack.currentFrame? <;> rfl
  | Return =>
    unfold AnnealExactWP miriEvalTerminatorAction ControlFlow.evalTerminator
    dsimp only [Id.run]
    cases ControlFlow.returnFromCurrentFrame hooks.toControlHooks choice false state with
    | mk after res => cases res with | ok u => cases u; rfl | error _ => rfl
  | UnwindResume =>
    unfold AnnealExactWP miriEvalTerminatorAction ControlFlow.evalTerminator
    dsimp only [Id.run]
    cases ControlFlow.returnFromCurrentFrame hooks.toControlHooks choice true state with
    | mk after res => cases res with | ok u => cases u; rfl | error _ => rfl
  | UnwindTerminate reason =>
    unfold AnnealExactWP miriEvalTerminatorAction ControlFlow.evalTerminator
    dsimp only [Id.run]
    cases hooks.unwindTerminate choice reason state with
    | mk after res => cases res with | ok u => cases u; rfl | error _ => rfl
  | Unreachable => rfl
  | InlineAsm _ => rfl
  | FalseEdge _ _ => rfl
  | FalseUnwind _ _ => rfl
  | Yield _ _ _ _ => rfl
  | CoroutineDrop => rfl
  | SwitchInt discr targets =>
    unfold AnnealExactWP miriEvalTerminatorAction
    cases ControlFlow.evalTerminator hooks choice ⟨sourceInfo, .SwitchInt discr targets⟩ state with
    | mk after res => cases res with | ok u => cases u; rfl | error _ => rfl
  | Call func args dest target unwind callSource fnSpan =>
    exact miriCallTerminatorExactWP_iff hooks choice func args dest target unwind
      callSource fnSpan sourceInfo post onError state
  | TailCall func args fnSpan =>
    unfold AnnealExactWP miriEvalTerminatorAction ControlFlow.evalTerminator
    simp only [Id.run, pure, Pure.pure]
    cases hTC : hooks.tailCall choice ⟨sourceInfo, .TailCall func args fnSpan⟩ state with
    | mk after res =>
      simp only [hTC]
      cases res with
      | error _ => rfl
      | ok u =>
        cases u
        dsimp only
        by_cases hNe : (after.stack.frames.size != state.stack.frames.size) = true <;>
          simp only [hNe, Bool.false_eq_true, ↓reduceIte]
  | Drop place target unwind replace asyncDrop =>
    unfold AnnealExactWP miriEvalTerminatorAction ControlFlow.evalTerminator
    simp only [Id.run, pure, Pure.pure]
    by_cases hAsync : asyncDrop.isSome = true
    · simp only [hAsync, ↓reduceIte]
    · simp only [hAsync, Bool.false_eq_true, ↓reduceIte]
      cases hooks.drop choice place target unwind state with
      | mk after res => cases res with | ok u => cases u; rfl | error _ => rfl
  | Assert condition expected message target unwind =>
    unfold AnnealExactWP miriEvalTerminatorAction ControlFlow.evalTerminator
    simp only [Id.run, pure, Pure.pure]
    cases hRead : hooks.readAssertCondition choice condition state with
    | mk s1 res =>
      simp only [hRead]
      cases res with
      | error _ => rfl
      | ok val =>
        dsimp only
        by_cases hPass : ((hooks.ignoreOptionalOverflowChecks state &&
            ControlFlow.isOptionalOverflowCheck message) || (expected == val)) = true
        · simp only [hPass, ↓reduceIte, ControlFlow.goToBlock, ControlFlow.setLocation]
          cases s1.stack.currentFrame? <;> rfl
        · simp only [hPass, Bool.false_eq_true, ↓reduceIte]
          cases hooks.assertPanic choice message unwind s1 with
          | mk after r2 => cases r2 with | ok u => cases u; rfl | error _ => rfl

/-- `ExactAction` wrapping unmodified vendored `Miri.Interpreter.MachineHooks.beforeStackPopWithEnsure`
(retaining all committed Tree Borrows release mutations on both success and failure). -/
def miriBeforeStackPopAction {K User : Type} [DecidableEq K]
    (ensureTreeExtra : Miri.Memory.AllocId → MachineHooks.M K User Unit) :
    ExactAction (MachineHooks.State K User) StepError Unit :=
  fun state =>
    match MachineHooks.run (MachineHooks.beforeStackPopWithEnsure ensureTreeExtra) state with
    | (after, .ok u) => .ok u after
    | (after, .error err) => .error err after

/-- **Exact bidirectional `↔` WP for `MachineHooks.beforeStackPopWithEnsure` when Tree Borrows is
disabled (`borrowTracker = none`)**: guaranteed state-preserving no-op! -/
theorem miriBeforeStackPopWithEnsure_disabled_exactWP_iff {K User : Type} [DecidableEq K]
    (ensureTreeExtra : Miri.Memory.AllocId → MachineHooks.M K User Unit)
    (post : Unit → MachineHooks.State K User → Prop)
    (onError : StepError → MachineHooks.State K User → Prop)
    (state : MachineHooks.State K User)
    (hDisabled : state.machine.borrowTracker = none) :
    AnnealExactWP (miriBeforeStackPopAction ensureTreeExtra) post onError state ↔
      post () state := by
  unfold AnnealExactWP miriBeforeStackPopAction MachineHooks.run Call.run
    MachineHooks.beforeStackPopWithEnsure
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure, hDisabled, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

/-- **Exact bidirectional `↔` WP for `MachineHooks.beforeStackPopWithEnsure` on a single-protector
live allocation frame**: characterizes unmodified vendored `BorrowTree.releaseProtector` +
`MemoryState.setLiveAllocation` + `GlobalState.endCall` (on `.Released`) and committed-tree
`placeMachineTreeError` UB (on `.AccessFailure`)! -/
theorem miriBeforeStackPopWithEnsure_singleLive_exactWP_iff {K User : Type} [DecidableEq K]
    (ensureTreeExtra : Miri.Memory.AllocId → MachineHooks.M K User Unit)
    (post : Unit → MachineHooks.State K User → Prop)
    (onError : StepError → MachineHooks.State K User → Prop)
    (state : MachineHooks.State K User)
    (tracker : MachineHooks.BorrowState)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (allocId : Miri.Memory.AllocId) (tag : BorTag) (kind : MemoryKind K)
    (alloc : Allocation Provenance BorrowTree)
    (hBt : state.machine.borrowTracker = some tracker)
    (hCur : state.stack.currentFrame? = some frame)
    (hFrameBt : frame.extra.borrowTracker = some { protectedTags := #[(allocId, tag)] })
    (hFind : state.machine.memory.live.find? (fun e => e.1 == allocId) =
      some (allocId, LocalAllocation.mk kind alloc))
    (hEnsure : ensureTreeExtra allocId state = .ok () state) :
    let released := alloc.extra.releaseProtector tag tracker.global.protectedTags
    let mem' : MemoryState Provenance BorrowTree K :=
      { state.machine.memory with
        live := (state.machine.memory.live.filter fun r => r.1 != allocId).push
          (allocId, LocalAllocation.mk kind (alloc.setExtra released.tree)) }
    let stateRel : MachineHooks.State K User :=
      { state with machine := { state.machine with memory := mem' } }
    AnnealExactWP (miriBeforeStackPopAction ensureTreeExtra) post onError state ↔
      match released.status with
      | .Released =>
        post ()
          { stateRel with
            machine :=
              { stateRel.machine with
                borrowTracker :=
                  some { tracker with global := tracker.global.endCall { protectedTags := #[(allocId, tag)] } } } }
      | .AccessFailure _ status =>
        onError (placeMachineTreeError status) stateRel
      | other =>
        onError (.invalidProgram s!"protector release invariant: {reprStr other}") stateRel := by
  dsimp only
  have hInfo : state.machine.memory.getAllocInfo allocId =
      .ok ⟨alloc.byteSize, alloc.align, .liveData, alloc.mutability⟩ := by
    unfold MemoryState.getAllocInfo
    simp only [hFind, pure, Pure.pure, Except.pure]
  have hSet :
      state.machine.memory.setLiveAllocation allocId
        (alloc.setExtra (alloc.extra.releaseProtector tag tracker.global.protectedTags).tree) =
      .ok { state.machine.memory with
            live := (state.machine.memory.live.filter fun r => r.1 != allocId).push
              (allocId, LocalAllocation.mk kind
                (alloc.setExtra (alloc.extra.releaseProtector tag tracker.global.protectedTags).tree)) } :=
    MemoryState.setLiveAllocation_of_find state.machine.memory allocId
      (LocalAllocation.mk kind alloc) _ hFind
  unfold AnnealExactWP miriBeforeStackPopAction MachineHooks.run Call.run
    MachineHooks.beforeStackPopWithEnsure MachineHooks.currentFrame
  simp only [get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set,
    modify, modifyGet, MonadStateOf.modifyGet,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    hBt, Option.isSome_some, ↓reduceIte, hCur, hFrameBt]
  simp only [← Array.forIn_toList, List.forIn_cons, List.forIn_nil,
    EStateM.get, EStateM.modifyGet, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    hInfo, beq_self_eq_true, ↓reduceIte, hEnsure, hFind, hSet, hBt]
  generalize alloc.extra.releaseProtector tag tracker.global.protectedTags = rel
  rcases rel with ⟨relTree, relStatus⟩
  cases relStatus with
  | Released =>
    simp only [EStateM.bind, EStateM.pure, EStateM.set]
  | AccessFailure r status =>
    unfold_mh
    simp only [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, placeMachineTreeError]
    cases status <;> rfl
  | MissingTag =>
    simp only [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind]
  | _ =>
    simp only [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind]

end InstructionAndCallDispatchWP

/-! ## §3. Initial-State Read-Only Memory Observation WP (`miriObserveMemoryExactWP_iff`) -/

section ObserveMemoryWP

variable {P E : Type}

/-- Read-only scalar observation `ExactAction` over unmodified `Miri.Memory.Allocation.readScalar`. -/
abbrev miriObserveScalarAction [DecidableEq P] [PointerProvenance P]
    (layout : TargetDataLayout) (range : AllocRange) (readProvenance : Bool) :
    ExactAction (Allocation P E) AllocError (Miri.Memory.Scalar P) :=
  allocReadScalarAction layout range readProvenance

/-- Read-only provenance-stripped byte observation `ExactAction` over unmodified
`Miri.Memory.Allocation.getBytesStripProvenance` (the byte-read primitive of
`RawMemoryMachine.readBytes` and `ValidityMemory.readBytes`). -/
def miriObserveBytesAction [PointerProvenance P]
    (layout : TargetDataLayout) (range : AllocRange) :
    ExactAction (Allocation P E) AllocError (Array UInt8) :=
  fun allocation =>
    match allocation.getBytesStripProvenance layout range with
    | .ok bs => .ok bs allocation
    | .error err => .error err allocation

/-- Read-only raw byte-slice observation `ExactAction` over unmodified
`Miri.Memory.Allocation.getBytesUnchecked`. -/
def miriObserveRawBytesAction (range : AllocRange) :
    ExactAction (Allocation P E) AllocError (Array UInt8) :=
  fun allocation =>
    match allocation.getBytesUnchecked range with
    | .ok bs => .ok bs allocation
    | .error err => .error err allocation

/-- Exact bidirectional `↔` scalar observation WP. -/
theorem miriObserveScalarExactWP_iff [DecidableEq P] [PointerProvenance P]
    (layout : TargetDataLayout) (range : AllocRange) (readProvenance : Bool)
    (post : Miri.Memory.Scalar P → Allocation P E → Prop)
    (onError : AllocError → Allocation P E → Prop)
    (allocation : Allocation P E) :
    AnnealExactWP (miriObserveScalarAction layout range readProvenance) post onError allocation ↔
      match allocation.readScalar layout range readProvenance with
      | .ok sc => post sc allocation
      | .error err => onError err allocation :=
  allocReadScalarExactWP_iff layout range readProvenance post onError allocation

/-- Exact bidirectional `↔` provenance-stripped byte observation WP. -/
theorem miriObserveBytesExactWP_iff [PointerProvenance P]
    (layout : TargetDataLayout) (range : AllocRange)
    (post : Array UInt8 → Allocation P E → Prop)
    (onError : AllocError → Allocation P E → Prop)
    (allocation : Allocation P E) :
    AnnealExactWP (miriObserveBytesAction layout range) post onError allocation ↔
      match allocation.getBytesStripProvenance layout range with
      | .ok bs => post bs allocation
      | .error err => onError err allocation := by
  unfold AnnealExactWP miriObserveBytesAction
  cases allocation.getBytesStripProvenance layout range <;> rfl

/-- Exact bidirectional `↔` raw byte observation WP. -/
theorem miriObserveRawBytesExactWP_iff (range : AllocRange)
    (post : Array UInt8 → Allocation P E → Prop)
    (onError : AllocError → Allocation P E → Prop)
    (allocation : Allocation P E) :
    AnnealExactWP (miriObserveRawBytesAction range) post onError allocation ↔
      match allocation.getBytesUnchecked range with
      | .ok bs => post bs allocation
      | .error err => onError err allocation := by
  unfold AnnealExactWP miriObserveRawBytesAction
  cases allocation.getBytesUnchecked range <;> rfl

/-- Uninitialized byte range observation faults with `.invalidUninitBytes` (`MemoryLemmas` bridge). -/
theorem miriObserveBytes_uninit_err_exactWP [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout) (range bad : AllocRange)
    (post : Array UInt8 → Allocation P E → Prop)
    (onError : AllocError → Allocation P E → Prop)
    (hUninit : allocation.initializationMask.isRangeInitialized range = .ok (.error bad)) :
    AnnealExactWP (miriObserveBytesAction layout range) post onError allocation ↔
      onError (.invalidUninitBytes (some ⟨range, bad⟩)) allocation := by
  rw [miriObserveBytesExactWP_iff,
    Allocation.getBytesStripProvenance_uninit_err allocation layout range bad hUninit]

/-- Initialized provenance-clean byte observation agrees with `getBytesUnchecked` (`MemoryLemmas` bridge). -/
theorem miriObserveBytes_ok_exactWP [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout) (range : AllocRange)
    (post : Array UInt8 → Allocation P E → Prop)
    (onError : AllocError → Allocation P E → Prop)
    (hInit : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (hProv : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true) :
    AnnealExactWP (miriObserveBytesAction layout range) post onError allocation ↔
      AnnealExactWP (miriObserveRawBytesAction range) post onError allocation := by
  rw [miriObserveBytesExactWP_iff, miriObserveRawBytesExactWP_iff,
    Allocation.getBytesStripProvenance_ok allocation layout range hInit hProv]

/-- **Strict state immutability of scalar observation**: `miriObserveScalarAction` NEVER modifies
`allocation` (bytes, initMask, provenance, or extra/`BorrowTree`) on EITHER `.ok` or `.error`! -/
theorem miriObserveScalar_state_immutable [DecidableEq P] [PointerProvenance P]
    (layout : TargetDataLayout) (range : AllocRange) (readProvenance : Bool)
    (allocation : Allocation P E) :
    (∀ sc a', miriObserveScalarAction layout range readProvenance allocation = .ok sc a' →
      a' = allocation) ∧
    (∀ err a', miriObserveScalarAction layout range readProvenance allocation = .error err a' →
      a' = allocation) := by
  unfold miriObserveScalarAction allocReadScalarAction
  cases allocation.readScalar layout range readProvenance with
  | ok sc =>
    constructor
    · intro _ _ h; cases h; rfl
    · intro _ _ h; cases h
  | error err =>
    constructor
    · intro _ _ h; cases h
    · intro _ _ h; cases h; rfl

/-- **Strict state immutability of byte observation**: `miriObserveBytesAction` NEVER modifies
`allocation` on EITHER `.ok` or `.error`! -/
theorem miriObserveBytes_state_immutable [PointerProvenance P]
    (layout : TargetDataLayout) (range : AllocRange) (allocation : Allocation P E) :
    (∀ bs a', miriObserveBytesAction layout range allocation = .ok bs a' → a' = allocation) ∧
    (∀ err a', miriObserveBytesAction layout range allocation = .error err a' → a' = allocation) := by
  unfold miriObserveBytesAction
  cases allocation.getBytesStripProvenance layout range with
  | ok bs =>
    constructor
    · intro _ _ h; cases h; rfl
    · intro _ _ h; cases h
  | error err =>
    constructor
    · intro _ _ h; cases h
    · intro _ _ h; cases h; rfl

/-- Composite machine + borrow-tree memory observation state pairing unmodified
`Miri.Memory.MemoryState P BorrowTree Unit` with unmodified `Miri.TreeBorrows.ProtectedTags`. -/
structure MiriObservedState (P : Type) : Type where
  memory : MemoryState P BorrowTree Unit
  protectedTags : ProtectedTags

/-- Read-only memory observation request (scalar or byte slice). -/
inductive MiriObserveQuery : Type where
  | scalar (range : AllocRange) (readProvenance : Bool) : MiriObserveQuery
  | bytes (range : AllocRange) : MiriObserveQuery
  deriving DecidableEq, Repr

/-- Read-only memory observation result payload. -/
inductive MiriObservedValue (P : Type) : Type where
  | scalar (val : Miri.Memory.Scalar P) : MiriObservedValue P
  | bytes (val : Array UInt8) : MiriObservedValue P
  deriving DecidableEq, Repr

/-- Read-only memory observation error (missing allocation vs. allocation read fault). -/
inductive MiriObserveError : Type where
  | missingAlloc (allocId : Miri.Memory.AllocId) : MiriObserveError
  | allocError (err : AllocError) : MiriObserveError
  deriving DecidableEq, Repr

/-- Look up a live `Allocation P BorrowTree` in `MiriObservedState P`. -/
def lookupLiveAlloc (st : MiriObservedState P) (allocId : Miri.Memory.AllocId) :
    Option (Allocation P BorrowTree) :=
  (st.memory.live.find? (fun entry => entry.1 == allocId)).map (fun entry => entry.2.allocation)

/-- **Read-only memory observation `ExactAction` (`miriObserveMemoryAction`)** mirroring
`lean-miri#94` `miri_observe_memory`: looks up `allocId` in `st.memory.live` and executes
unmodified `Allocation.readScalar` or `Allocation.getBytesStripProvenance`, returning `st`
strictly unmodified on EVERY branch! -/
def miriObserveMemoryAction [DecidableEq P] [PointerProvenance P]
    (layout : TargetDataLayout) (allocId : Miri.Memory.AllocId) (query : MiriObserveQuery) :
    ExactAction (MiriObservedState P) MiriObserveError (MiriObservedValue P) :=
  fun st =>
    match lookupLiveAlloc st allocId with
    | none => .error (.missingAlloc allocId) st
    | some alloc =>
      match query with
      | .scalar range readProv =>
        match alloc.readScalar layout range readProv with
        | .ok sc => .ok (.scalar sc) st
        | .error err => .error (.allocError err) st
      | .bytes range =>
        match alloc.getBytesStripProvenance layout range with
        | .ok bs => .ok (.bytes bs) st
        | .error err => .error (.allocError err) st

/-- Exact symbolic precondition for `miriObserveMemoryAction` (mirroring `miri_observe_memory`). -/
def miriObserveMemoryPre [DecidableEq P] [PointerProvenance P]
    (layout : TargetDataLayout) (allocId : Miri.Memory.AllocId) (query : MiriObserveQuery)
    (post : MiriObservedValue P → MiriObservedState P → Prop)
    (onError : MiriObserveError → MiriObservedState P → Prop)
    (st : MiriObservedState P) : Prop :=
  match lookupLiveAlloc st allocId with
  | none => onError (.missingAlloc allocId) st
  | some alloc =>
    match query with
    | .scalar range readProv =>
      match alloc.readScalar layout range readProv with
      | .ok sc => post (.scalar sc) st
      | .error err => onError (.allocError err) st
    | .bytes range =>
      match alloc.getBytesStripProvenance layout range with
      | .ok bs => post (.bytes bs) st
      | .error err => onError (.allocError err) st

/-- **Exact bidirectional `↔` theorem `miriObserveMemoryExactWP_iff`** (mirroring `lean-miri#94`'s
`miri_observe_memory`) over unmodified `Miri.Memory.Allocation.{readScalar, getBytesStripProvenance}`
and `MiriObservedState`! -/
theorem miriObserveMemoryExactWP_iff [DecidableEq P] [PointerProvenance P]
    (layout : TargetDataLayout) (allocId : Miri.Memory.AllocId) (query : MiriObserveQuery)
    (post : MiriObservedValue P → MiriObservedState P → Prop)
    (onError : MiriObserveError → MiriObservedState P → Prop)
    (st : MiriObservedState P) :
    AnnealExactWP (miriObserveMemoryAction layout allocId query) post onError st ↔
      miriObserveMemoryPre layout allocId query post onError st := by
  unfold AnnealExactWP miriObserveMemoryAction miriObserveMemoryPre
  cases lookupLiveAlloc st allocId with
  | none => rfl
  | some alloc =>
    dsimp only
    cases query with
    | scalar range readProv => dsimp only; cases alloc.readScalar layout range readProv <;> rfl
    | bytes range => dsimp only; cases alloc.getBytesStripProvenance layout range <;> rfl

/-- **Strict whole-state immutability (`miriObserveMemory_state_immutable`)**: observing memory
NEVER modifies ANY field of `MiriObservedState` — allocation bytes, initialization mask,
provenance map, `BorrowTree`, or `ProtectedTags` are strictly identical (`st' = st`) on BOTH
`.ok` and `.error`! -/
theorem miriObserveMemory_state_immutable [DecidableEq P] [PointerProvenance P]
    (layout : TargetDataLayout) (allocId : Miri.Memory.AllocId) (query : MiriObserveQuery)
    (st : MiriObservedState P) :
    (∀ val st', miriObserveMemoryAction layout allocId query st = .ok val st' → st' = st) ∧
    (∀ err st', miriObserveMemoryAction layout allocId query st = .error err st' → st' = st) := by
  unfold miriObserveMemoryAction
  cases lookupLiveAlloc st allocId with
  | none =>
    constructor
    · intro _ _ h; cases h
    · intro _ _ h; cases h; rfl
  | some alloc =>
    dsimp only
    cases query with
    | scalar range readProv =>
      dsimp only
      cases alloc.readScalar layout range readProv with
      | ok _ =>
        constructor
        · intro _ _ h; cases h; rfl
        · intro _ _ h; cases h
      | error _ =>
        constructor
        · intro _ _ h; cases h
        · intro _ _ h; cases h; rfl
    | bytes range =>
      dsimp only
      cases alloc.getBytesStripProvenance layout range with
      | ok _ =>
        constructor
        · intro _ _ h; cases h; rfl
        · intro _ _ h; cases h
      | error _ =>
        constructor
        · intro _ _ h; cases h
        · intro _ _ h; cases h; rfl

/-- **Bridge to real vendored Miri `get_alloc_raw` (`MemoryLifecycle.getAllocRaw`)**:
`lookupLiveAlloc` is EXACTLY the live-map hit branch of unmodified
`Miri.Memory.MemoryLifecycle.getAllocRaw`. Whenever `lookupLiveAlloc` finds `alloc`, the real Miri
lookup returns `.ok alloc` for EVERY hook state, global machine kind, and
`GlobalAllocationHooks`, leaves `MemoryState` IDENTICALLY unchanged, and only re-synchronizes the
hook state — so `miriObserveMemoryAction` observes precisely the allocation real Miri reads. -/
theorem lookupLiveAlloc_eq_getAllocRaw_live [DecidableEq P] [PointerProvenance P]
    {HookState : Type}
    (st : MiriObservedState P) (allocId : Miri.Memory.AllocId) (alloc : Allocation P BorrowTree)
    (hooksState : HookState) (globalKind : Option Unit)
    (hooks : GlobalAllocationHooks P BorrowTree Unit HookState)
    (hLive : lookupLiveAlloc st allocId = some alloc) :
    MemoryLifecycle.getAllocRaw st.memory hooksState allocId globalKind hooks =
      ⟨st.memory, hooks.synchronizeMemory st.memory hooksState, .ok alloc⟩ := by
  unfold lookupLiveAlloc at hLive
  unfold MemoryLifecycle.getAllocRaw
  cases hF : st.memory.live.find? (fun old => old.1 == allocId) with
  | none => rw [hF] at hLive; cases hLive
  | some entry =>
    rw [hF] at hLive
    cases hLive
    simp only [Id.run]
    rfl

/-- **Observation through real Miri `getAllocRaw` (`miriObserveMemory_agrees_getAllocRaw`)**: on a
live allocation, `miriObserveMemoryAction` returns EXACTLY the unmodified
`Allocation.readScalar` / `Allocation.getBytesStripProvenance` result on the allocation returned
by real `MemoryLifecycle.getAllocRaw`, whose memory component equals the input memory. -/
theorem miriObserveMemory_agrees_getAllocRaw [DecidableEq P] [PointerProvenance P]
    {HookState : Type}
    (layout : TargetDataLayout) (allocId : Miri.Memory.AllocId) (query : MiriObserveQuery)
    (st : MiriObservedState P) (alloc : Allocation P BorrowTree)
    (hooksState : HookState) (globalKind : Option Unit)
    (hooks : GlobalAllocationHooks P BorrowTree Unit HookState)
    (hLive : lookupLiveAlloc st allocId = some alloc) :
    let r := MemoryLifecycle.getAllocRaw st.memory hooksState allocId globalKind hooks
    r.memory = st.memory ∧ r.outcome = .ok alloc ∧
    miriObserveMemoryAction layout allocId query st =
      (match query with
       | .scalar range readProv =>
         match alloc.readScalar layout range readProv with
         | .ok sc => .ok (.scalar sc) st
         | .error err => .error (.allocError err) st
       | .bytes range =>
         match alloc.getBytesStripProvenance layout range with
         | .ok bs => .ok (.bytes bs) st
         | .error err => .error (.allocError err) st) := by
  dsimp only
  rw [lookupLiveAlloc_eq_getAllocRaw_live st allocId alloc hooksState globalKind hooks hLive]
  refine ⟨rfl, rfl, ?_⟩
  unfold miriObserveMemoryAction
  rw [hLive]

/-- **Universal invariant-framing WP law (`miriObserveMemory_frame_invariant_iff`)**: because
`miriObserveMemoryAction` is strictly state-immutable on BOTH `.ok` and `.error`, ANY state
invariant `Inv : MiriObservedState P → Prop` factors cleanly out of BOTH postcondition and error
continuation! -/
theorem miriObserveMemory_frame_invariant_iff [DecidableEq P] [PointerProvenance P]
    (layout : TargetDataLayout) (allocId : Miri.Memory.AllocId) (query : MiriObserveQuery)
    (Inv : MiriObservedState P → Prop)
    (post : MiriObservedValue P → MiriObservedState P → Prop)
    (onError : MiriObserveError → MiriObservedState P → Prop)
    (st : MiriObservedState P) :
    AnnealExactWP (miriObserveMemoryAction layout allocId query)
        (fun val st' => post val st' ∧ Inv st')
        (fun err st' => onError err st' ∧ Inv st') st ↔
      Inv st ∧ AnnealExactWP (miriObserveMemoryAction layout allocId query) post onError st := by
  have ⟨hOkImm, hErrImm⟩ := miriObserveMemory_state_immutable layout allocId query st
  unfold AnnealExactWP
  cases hAct : miriObserveMemoryAction layout allocId query st with
  | ok val st' =>
    have hEq : st' = st := hOkImm val st' hAct
    subst hEq
    exact ⟨fun ⟨hp, hi⟩ => ⟨hi, hp⟩, fun ⟨hi, hp⟩ => ⟨hp, hi⟩⟩
  | error err st' =>
    have hEq : st' = st := hErrImm err st' hAct
    subst hEq
    exact ⟨fun ⟨he, hi⟩ => ⟨hi, he⟩, fun ⟨hi, he⟩ => ⟨he, hi⟩⟩

/-- **Miss / dangling-allocation bridge to real vendored `MemoryLifecycle.getAllocRaw`**:
whenever `lookupLiveAlloc st allocId = none` and global-allocation fallback fails with `gErr`
(e.g., `.unavailable` or `.dangling`), real `MemoryLifecycle.getAllocRaw` faults with
`.error (.globalAccess gErr)` — matching `miriObserveMemoryAction`'s `.error (.missingAlloc allocId)`! -/
theorem lookupLiveAlloc_none_agrees_getAllocRaw_error [DecidableEq P] [PointerProvenance P]
    {HookState : Type}
    (st : MiriObservedState P) (allocId : Miri.Memory.AllocId)
    (hooksState : HookState) (globalKind : Option Unit)
    (hooks : GlobalAllocationHooks P BorrowTree Unit HookState)
    (gMem : MemoryState P BorrowTree Unit) (gHooks : HookState)
    (gErr : GlobalAccessError)
    (hMiss : lookupLiveAlloc st allocId = none)
    (hGlobErr : MemoryLifecycle.getGlobalAlloc st.memory hooksState allocId false hooks =
      ⟨gMem, gHooks, .error gErr⟩) :
    (MemoryLifecycle.getAllocRaw st.memory hooksState allocId globalKind hooks).outcome =
      .error (.globalAccess gErr) ∧
    ∀ layout query,
      miriObserveMemoryAction layout allocId query st = .error (.missingAlloc allocId) st := by
  unfold lookupLiveAlloc at hMiss
  cases hF : st.memory.live.find? (fun old => old.1 == allocId) with
  | some entry => rw [hF] at hMiss; cases hMiss
  | none =>
    constructor
    · unfold MemoryLifecycle.getAllocRaw
      simp only [Id.run, hF, hGlobErr, pure, Pure.pure]
    · intro layout query
      unfold miriObserveMemoryAction lookupLiveAlloc
      rw [hF]
      rfl

/-- Lift unmodified vendored `Miri.Interpreter.RawMemoryMachine.readBytes` into `ExactAction`. -/
def miriRawMemoryReadBytesAction {K User : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K User)
    (arithmetic : PointerArithmetic) (pointer : Pointer (Option Provenance)) (length : UInt64) :
    ExactAction (MachineHooks.State K User) StepError ByteArray :=
  ExactAction.ofEStateM (RawMemoryMachine.readBytes config arithmetic pointer length)

/-- **Exact bidirectional `↔` bridge to real vendored `Miri.Interpreter.RawMemoryMachine.readBytes`**:
once `RawMemoryMachine.reference` resolves `some ref` in post-state `s1`, unmodified
`RawMemoryMachine.readBytes` evaluates `ref.allocation.getBytesStripProvenance config.runtime.base ref.range`
— directly connecting real Miri's raw-memory byte reader to `miriObserveBytesExactWP_iff`! -/
theorem miriRawMemoryReadBytesExactWP_iff {K User : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K User)
    (arithmetic : PointerArithmetic) (pointer : Pointer (Option Provenance)) (length : UInt64)
    (post : ByteArray → MachineHooks.State K User → Prop)
    (onError : StepError → MachineHooks.State K User → Prop)
    (state s1 : MachineHooks.State K User)
    (ref : AllocationAccessRef Provenance BorrowTree)
    (hRef : RawMemoryMachine.reference config arithmetic false pointer (Size.ofBytes length) state =
      .ok (some ref) s1) :
    AnnealExactWP (miriRawMemoryReadBytesAction config arithmetic pointer length) post onError state ↔
      AnnealExactWP (miriObserveBytesAction config.runtime.base ref.range)
        (fun bs _ => post ⟨bs⟩ s1)
        (fun err _ => onError (config.memoryError (.allocation err)) s1)
        ref.allocation := by
  rw [miriObserveBytesExactWP_iff]
  unfold AnnealExactWP miriRawMemoryReadBytesAction ExactAction.ofEStateM RawMemoryMachine.readBytes
  simp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, hRef]
  dsimp only [Except.mapError]
  cases ref.allocation.getBytesStripProvenance config.runtime.base ref.range <;> rfl

/-! ### §3.1. Composing `miriObserveMemoryExactWP_iff` with Tree Borrows Range, Instruction & Call-Dispatch WP -/

/-- Lift a single-allocation `BorrowTree.performBorrowAccessRange` onto `MiriObservedState P`
updating ONLY `alloc.extra` via `setExtra` / `setLiveAllocation`. -/
inductive MiriObsAndRangeError : Type where
  | observe (err : MiriObserveError) : MiriObsAndRangeError
  | missingAlloc (allocId : Miri.Memory.AllocId) : MiriObsAndRangeError
  | memUpdate (err : AllocationLookupError) : MiriObsAndRangeError
  | treeRange (status : BorrowTree.BorrowTreeAccessStatus)
      (visited : Array BorrowTree.BorrowTreeLocationResult) : MiriObsAndRangeError
  deriving DecidableEq, Repr

def miriObservedTreeRangeAction (allocId : Miri.Memory.AllocId)
    (prov : ProvenanceExtra) (off len : Size) (kind : AccessKind)
    (mode : Tree.ChildrenVisitMode) :
    ExactAction (MiriObservedState P) MiriObsAndRangeError
      (Array BorrowTree.BorrowTreeLocationResult) :=
  fun st =>
    match lookupLiveAlloc st allocId with
    | none => .error (.missingAlloc allocId) st
    | some alloc =>
      let res := alloc.extra.performBorrowAccessRange prov off len kind st.protectedTags mode
      let alloc' := alloc.setExtra res.tree
      match st.memory.setLiveAllocation allocId alloc' with
      | .error uErr => .error (.memUpdate uErr) st
      | .ok mem' =>
        let st' : MiriObservedState P := { st with memory := mem' }
        match res.status with
        | .Completed => .ok res.locations st'
        | status => .error (.treeRange status res.locations) st'

/-- **Composition Law 1 (`miriObserveMemory_then_treeRange_exactWP_iff`)**:
sequencing read-only memory observation BEFORE a Tree Borrows range access leaves the state
strictly unchanged for `miriTreeRangeExactWP_iff`! -/
theorem miriObserveMemory_then_treeRange_exactWP_iff [DecidableEq P] [PointerProvenance P]
    (layout : TargetDataLayout) (obsAllocId tbAllocId : Miri.Memory.AllocId)
    (query : MiriObserveQuery)
    (prov : ProvenanceExtra) (off len : Size) (kind : AccessKind)
    (mode : Tree.ChildrenVisitMode)
    (post : MiriObservedValue P → Array BorrowTree.BorrowTreeLocationResult →
      MiriObservedState P → Prop)
    (onError : MiriObsAndRangeError → MiriObservedState P → Prop)
    (st : MiriObservedState P) :
    AnnealExactWP
      (ExactAction.bind
        (mapExactActionErr MiriObsAndRangeError.observe
          (miriObserveMemoryAction layout obsAllocId query))
        (fun val =>
          ExactAction.map (fun locs => (val, locs))
            (miriObservedTreeRangeAction tbAllocId prov off len kind mode)))
      (fun pair st' => post pair.1 pair.2 st') onError st ↔
      miriObserveMemoryPre layout obsAllocId query
        (fun val _ =>
          AnnealExactWP (miriObservedTreeRangeAction tbAllocId prov off len kind mode)
            (fun locs st' => post val locs st') onError st)
        (fun err st' => onError (.observe err) st') st := by
  rw [exactWP_bind, exactWP_mapErr, miriObserveMemoryExactWP_iff]
  unfold miriObserveMemoryPre
  cases lookupLiveAlloc st obsAllocId with
  | none => rfl
  | some alloc =>
    dsimp only
    cases query with
    | scalar range readProv =>
      dsimp only
      cases alloc.readScalar layout range readProv with
      | error _ => rfl
      | ok sc => dsimp only; rw [exactWP_map]
    | bytes range =>
      dsimp only
      cases alloc.getBytesStripProvenance layout range with
      | error _ => rfl
      | ok bs => dsimp only; rw [exactWP_map]

/-- **Composition Law 2 (`miriTreeRange_preserves_allocObservation`)**:
updating an allocation's `BorrowTree` via `Allocation.setExtra` (as `miriObservedTreeRangeAction`
does) NEVER changes `Allocation.readScalar` or `Allocation.getBytesStripProvenance`! -/
theorem miriTreeRange_preserves_allocObservation [DecidableEq P] [PointerProvenance P]
    (alloc : Allocation P BorrowTree) (layout : TargetDataLayout) (range : AllocRange)
    (readProv : Bool)
    (prov : ProvenanceExtra) (off len : Size) (kind : AccessKind)
    (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) :
    let nextTree := (alloc.extra.performBorrowAccessRange prov off len kind tags mode).tree
    (alloc.setExtra nextTree).readScalar layout range readProv =
      alloc.readScalar layout range readProv ∧
    (alloc.setExtra nextTree).getBytesStripProvenance layout range =
      alloc.getBytesStripProvenance layout range :=
  ⟨Allocation.readScalar_mapExtra alloc (fun _ => _) layout range readProv,
   Allocation.getBytesStripProvenance_mapExtra alloc (fun _ => _) layout range⟩

/-- Generic read-only observation lens lifting `miriObserveMemoryAction` onto ANY state `S`
carrying a projection `view : S → MiriObservedState P`! -/
def miriObserveInStateAction [DecidableEq P] [PointerProvenance P] {S Err : Type}
    (view : S → MiriObservedState P) (liftErr : MiriObserveError → Err)
    (layout : TargetDataLayout) (allocId : Miri.Memory.AllocId) (query : MiriObserveQuery) :
    ExactAction S Err (MiriObservedValue P) :=
  fun s =>
    match miriObserveMemoryAction layout allocId query (view s) with
    | .ok val _ => .ok val s
    | .error err _ => .error (liftErr err) s

/-- **Composition Law 3 (`miriObserveMemory_then_instruction_exactWP_iff`)**:
sequencing read-only memory observation before `miriInstructionAction` (`Step.evalStatement`)
leaves the full `StepState` strictly untouched for `miriInstructionExactWP_iff`! -/
theorem miriObserveMemory_then_instruction_exactWP_iff [DecidableEq P] [PointerProvenance P]
    {L E M C V : Type}
    (view : StepState P L E M → MiriObservedState P)
    (liftErr : MiriObserveError → StepError)
    (layout : TargetDataLayout) (allocId : Miri.Memory.AllocId) (query : MiriObserveQuery)
    (hooks : StepHooks P L E M C V) (choice : C) (stmt : Miri.MIR.Statement)
    (post : MiriObservedValue P → StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state : StepState P L E M) :
    AnnealExactWP
      (ExactAction.bind (miriObserveInStateAction view liftErr layout allocId query)
        (fun val => ExactAction.map (fun _ => val) (miriInstructionAction hooks choice stmt)))
      post onError state ↔
      miriObserveMemoryPre layout allocId query
        (fun val _ =>
          miriInstructionPre hooks choice stmt (fun _ after => post val after) onError state)
        (fun err _ => onError (liftErr err) state) (view state) := by
  rw [exactWP_bind]
  have hObs :
      ∀ (P : MiriObservedValue P → StepState P L E M → Prop),
        AnnealExactWP (miriObserveInStateAction view liftErr layout allocId query) P onError state ↔
          miriObserveMemoryPre layout allocId query
            (fun val _ => P val state) (fun err _ => onError (liftErr err) state) (view state) := by
    intro P
    rw [← miriObserveMemoryExactWP_iff]
    unfold AnnealExactWP miriObserveInStateAction
    cases miriObserveMemoryAction layout allocId query (view state) <;> rfl
  rw [hObs]
  have hStmt :
      ∀ val,
        AnnealExactWP (ExactAction.map (fun _ => val) (miriInstructionAction hooks choice stmt))
          post onError state ↔
        miriInstructionPre hooks choice stmt (fun _ after => post val after) onError state := by
    intro val
    rw [exactWP_map, miriInstructionExactWP_iff]
  unfold miriObserveMemoryPre
  cases lookupLiveAlloc (view state) allocId with
  | none => rfl
  | some alloc =>
    dsimp only
    cases query with
    | scalar range readProv =>
      dsimp only
      cases alloc.readScalar layout range readProv with
      | error _ => rfl
      | ok sc => dsimp only; exact hStmt (.scalar sc)
    | bytes range =>
      dsimp only
      cases alloc.getBytesStripProvenance layout range with
      | error _ => rfl
      | ok bs => dsimp only; exact hStmt (.bytes bs)

/-- **Composition Law 4 (`miriObserveMemory_then_callDispatch_exactWP_iff`)**:
sequencing read-only memory observation before `miriCallDispatchAction`
(`CallDispatchMachine.findMirOrEvalFn`) leaves the caller state strictly untouched for
`miriCallDispatchExactWP_iff`! -/
theorem miriObserveMemory_then_callDispatch_exactWP_iff [DecidableEq P] [PointerProvenance P]
    {S C Other : Type}
    (view : S → MiriObservedState P) (liftErr : MiriObserveError → StepError)
    (layout : TargetDataLayout) (allocId : Miri.Memory.AllocId) (query : MiriObserveQuery)
    (h : CallDispatchMachine.Hooks S C Other) (choice : C)
    (callee : CallInstance) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (FnArg Provenance)) (destination : RuntimeStackPlace Provenance)
    (ret : Option Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction)
    (post : MiriObservedValue P → Option (LoadedBody × CallInstance) → S → Prop)
    (onError : StepError → S → Prop)
    (state : S) :
    AnnealExactWP
      (ExactAction.bind (miriObserveInStateAction view liftErr layout allocId query)
        (fun val =>
          ExactAction.map (fun res => (val, res))
            (miriCallDispatchAction h choice callee abi args destination ret unwind)))
      (fun pair s' => post pair.1 pair.2 s') onError state ↔
      miriObserveMemoryPre layout allocId query
        (fun val _ =>
          miriCallDispatchPre h choice callee abi args destination ret unwind
            (fun res s' => post val res s') onError state)
        (fun err _ => onError (liftErr err) state) (view state) := by
  rw [exactWP_bind]
  have hObs :
      ∀ (P : MiriObservedValue P → S → Prop),
        AnnealExactWP (miriObserveInStateAction view liftErr layout allocId query) P onError state ↔
          miriObserveMemoryPre layout allocId query
            (fun val _ => P val state) (fun err _ => onError (liftErr err) state) (view state) := by
    intro P
    rw [← miriObserveMemoryExactWP_iff]
    unfold AnnealExactWP miriObserveInStateAction
    cases miriObserveMemoryAction layout allocId query (view state) <;> rfl
  rw [hObs]
  have hCall :
      ∀ val,
        AnnealExactWP
          (ExactAction.map (fun res => (val, res))
            (miriCallDispatchAction h choice callee abi args destination ret unwind))
          (fun pair s' => post pair.1 pair.2 s') onError state ↔
        miriCallDispatchPre h choice callee abi args destination ret unwind
          (fun res s' => post val res s') onError state := by
    intro val
    rw [exactWP_map, miriCallDispatchExactWP_iff]
  unfold miriObserveMemoryPre
  cases lookupLiveAlloc (view state) allocId with
  | none => rfl
  | some alloc =>
    dsimp only
    cases query with
    | scalar range readProv =>
      dsimp only
      cases alloc.readScalar layout range readProv with
      | error _ => rfl
      | ok sc => dsimp only; exact hCall (.scalar sc)
    | bytes range =>
      dsimp only
      cases alloc.getBytesStripProvenance layout range with
      | error _ => rfl
      | ok bs => dsimp only; exact hCall (.bytes bs)

end ObserveMemoryWP

/-! ## §4. Cross-Layer Correspondence (`Anneal.MiriTreeBorrowsV2026` ↔ Vendored `Miri.TreeBorrows` ↔ `V2026_06_01` ↔ `translateBody`) -/

section CrossLayerCorrespondence

/-- Exact bijection: `Anneal.MiriTreeBorrowsV2026.MiriPerm → Miri.TreeBorrows.Permission`. -/
def miriV2026PermToVendored : MiriPerm → Miri.TreeBorrows.Permission
  | .cell => .Cell
  | .reservedFrz c => .ReservedFrz c
  | .reservedIM => .ReservedIM
  | .unique => .Unique
  | .frozen => .Frozen
  | .disabled => .Disabled

/-- Exact inverse bijection: `Miri.TreeBorrows.Permission → Anneal.MiriTreeBorrowsV2026.MiriPerm`. -/
def vendoredPermToMiriV2026 : Miri.TreeBorrows.Permission → MiriPerm
  | .Cell => .cell
  | .ReservedFrz c => .reservedFrz c
  | .ReservedIM => .reservedIM
  | .Unique => .unique
  | .Frozen => .frozen
  | .Disabled => .disabled

theorem vendoredPermToMiriV2026_miriV2026PermToVendored (p : MiriPerm) :
    vendoredPermToMiriV2026 (miriV2026PermToVendored p) = p := by
  cases p <;> rfl

theorem miriV2026PermToVendored_vendoredPermToMiriV2026 (p : Miri.TreeBorrows.Permission) :
    miriV2026PermToVendored (vendoredPermToMiriV2026 p) = p := by
  cases p <;> rfl

def miriV2026AccessKindToVendored : MiriAccessKind → Miri.TreeBorrows.AccessKind
  | .read => .Read
  | .write => .Write

def miriV2026RelToVendored : MiriRelatedness → Miri.TreeBorrows.AccessRelatedness
  | .localAccess => .LocalAccess
  | .foreignAccess => .ForeignAccess

def miriV2026SifaToVendored : MiriSifa → Miri.TreeBorrows.IdempotentForeignAccess
  | .none => .None
  | .read => .Read
  | .write => .Write

def miriV2026OutcomeToVendored : MiriPermOutcome → Miri.TreeBorrows.AccessOutcome
  | .transition next => .Transition (miriV2026PermToVendored next)
  | .undefinedBehavior => .UndefinedBehavior
  | .impossibleProtectedReservedIM => .ImpossibleProtectedReservedIM

def miriV2026LocStateToVendored (st : MiriLocState) : Miri.TreeBorrows.Tree.LocationState :=
  ⟨miriV2026PermToVendored st.perm, st.accessed, miriV2026SifaToVendored st.sifa⟩

/-- **Exact 56-cell correspondence** between `Anneal.MiriTreeBorrowsV2026.miriPerformPermAccess` and
unmodified vendored `Miri.TreeBorrows.performAccess`! -/
theorem miriV2026_performPermAccess_eq_vendored_performAccess
    (kind : MiriAccessKind) (rel : MiriRelatedness) (perm : MiriPerm) (isProtected : Bool) :
    miriV2026OutcomeToVendored (miriPerformPermAccess kind rel perm isProtected) =
      Miri.TreeBorrows.performAccess
        (miriV2026AccessKindToVendored kind)
        (miriV2026RelToVendored rel)
        (miriV2026PermToVendored perm)
        isProtected := by
  rcases perm with _ | (_ | _) | _ | _ | _ | _ <;> cases kind <;> cases rel <;>
    cases isProtected <;> rfl

/-- Exact `associatedAccess` agreement between `Anneal.MiriTreeBorrowsV2026` and vendored `Miri.TreeBorrows`. -/
theorem miriV2026_associatedAccess_eq_vendored (perm : MiriPerm) :
    (miriAssociatedAccess perm).map miriV2026AccessKindToVendored =
      (miriV2026PermToVendored perm).associatedAccess := by
  cases perm <;> rfl

/-- Exact `strongestIdempotentForeignAccess` agreement. -/
theorem miriV2026_strongestSifa_eq_vendored (perm : MiriPerm) (isProtected : Bool) :
    (match miriStrongestSifa perm isProtected with
     | some s => Miri.TreeBorrows.Permission.IdempotentAccessResult.Access (miriV2026SifaToVendored s)
     | none => .ImpossibleProtectedReservedIM) =
      (miriV2026PermToVendored perm).strongestIdempotentForeignAccess isProtected := by
  rcases perm with _ | (_ | _) | _ | _ | _ | _ <;> cases isProtected <;> rfl

/-- Exact permission reachability partial-order agreement (`miriPermLE = permissionLE`). -/
theorem miriV2026_permLE_eq_vendored (p q : MiriPerm) :
    miriPermLE p q = Miri.TreeBorrows.permissionLE
      (miriV2026PermToVendored p) (miriV2026PermToVendored q) := by
  rcases p with _ | (_ | _) | _ | _ | _ | _ <;>
  rcases q with _ | (_ | _) | _ | _ | _ | _ <;> rfl

/-- Exact `skipIfKnownNoop` agreement between `Anneal.MiriTreeBorrowsV2026` and vendored
`Miri.TreeBorrows.Tree.LocationState.skipIfKnownNoop`. -/
theorem miriV2026_skipIfKnownNoop_eq_vendored (st : MiriLocState)
    (kind : MiriAccessKind) (rel : MiriRelatedness) :
    (if miriSkipIfKnownNoop st kind rel then Tree.ContinueTraversal.SkipSelfAndChildren
     else .Recurse) =
      Tree.LocationState.skipIfKnownNoop (miriV2026LocStateToVendored st)
        (miriV2026AccessKindToVendored kind) (miriV2026RelToVendored rel) := by
  rcases st with ⟨p, acc, sifa⟩
  rcases p with _ | (_ | _) | _ | _ | _ | _ <;> cases sifa <;> cases kind <;> cases rel <;> rfl

/-- Exact per-location transition correspondence: for every non-skipped, possible (`accessed || !isUnique`)
`MiriLocState`, `Anneal.MiriTreeBorrowsV2026.miriPerformLocAccess` matches vendored
`Tree.LocationState.recordNewAccess` followed by `Tree.LocationState.performAccess` on every
transition, `.ChildAccessForbidden`, `.ProtectedDisabled`, and `.PermissionInvariantFailure`! -/
theorem miriV2026_performLocAccess_eq_vendored_locationState
    (tag : Nat) (st : MiriLocState) (kind : MiriAccessKind) (rel : MiriRelatedness)
    (isProtected : Bool)
    (hPossible : (miriV2026LocStateToVendored st).possible = true)
    (hNotSkipped : miriSkipIfKnownNoop st kind rel = false) :
    ∃ recState,
      Tree.LocationState.recordNewAccess (miriV2026LocStateToVendored st)
          (miriV2026AccessKindToVendored kind) (miriV2026RelToVendored rel) =
        .Recorded recState ∧
      match miriPerformLocAccess tag st kind rel isProtected with
      | .ok nextLoc =>
        ∃ tr,
          Tree.LocationState.performAccess recState
              (miriV2026AccessKindToVendored kind) (miriV2026RelToVendored rel) isProtected =
            .Success (miriV2026LocStateToVendored nextLoc) tr
      | .err nextLoc (.childAccessForbidden _ p) =>
        Tree.LocationState.performAccess recState
            (miriV2026AccessKindToVendored kind) (miriV2026RelToVendored rel) isProtected =
          .Error (miriV2026LocStateToVendored nextLoc)
            (.ChildAccessForbidden (miriV2026PermToVendored p))
      | .err nextLoc (.protectedDisabled _ p) =>
        Tree.LocationState.performAccess recState
            (miriV2026AccessKindToVendored kind) (miriV2026RelToVendored rel) isProtected =
          .Error (miriV2026LocStateToVendored nextLoc)
            (.ProtectedDisabled (miriV2026PermToVendored p))
      | .err nextLoc (.impossibleProtectedReservedIM _) =>
        Tree.LocationState.performAccess recState
            (miriV2026AccessKindToVendored kind) (miriV2026RelToVendored rel) isProtected =
          .PermissionInvariantFailure (miriV2026LocStateToVendored nextLoc)
      | .err _ _ => False := by
  rcases st with ⟨p, acc, sifa⟩
  rcases p with _ | (_ | _) | _ | _ | _ | _ <;>
    cases acc <;> cases sifa <;> cases kind <;> cases rel <;> cases isProtected <;>
    first
    | exact absurd hPossible (by decide)
    | exact absurd hNotSkipped (by decide)
    | exact ⟨_, rfl, ⟨_, rfl⟩⟩
    | exact ⟨_, rfl, rfl⟩

/-- **Exact deallocation-protection correspondence (`miriV2026_preventsDealloc_eq_vendored_deallocGuard`)**:
`Anneal.MiriTreeBorrowsV2026.miriPermPreventsDealloc p` equals BOTH
`Trusted.Rustc.V2026_06_01.MirSemantics.preventsDeallocation (miriPermToV2026 p)` AND vendored
`!(miriV2026PermToVendored p).isCell && !(miriV2026PermToVendored p).isDisabled` (which is the exact
deallocation guard enforced by `BorrowTree.deallocateBorrowRange`: write-pass skips `.Disabled` and
the strong-protector check skips `.Cell`)! -/
theorem miriV2026_preventsDealloc_eq_vendored_deallocGuard (p : MiriPerm) :
    miriPermPreventsDealloc p =
      Trusted.Rustc.V2026_06_01.MirSemantics.preventsDeallocation (miriPermToV2026 p) ∧
    miriPermPreventsDealloc p =
      (!(miriV2026PermToVendored p).isCell && !(miriV2026PermToVendored p).isDisabled) := by
  cases p <;> exact ⟨rfl, rfl⟩

/-- Map `Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowPerm` directly to vendored
`Miri.TreeBorrows.Permission`. -/
def v2026PermToVendored :
    Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowPerm → Miri.TreeBorrows.Permission
  | .cell => .Cell
  | .reservedFrz c => .ReservedFrz c
  | .reservedIM => .ReservedIM
  | .unique => .Unique
  | .frozen => .Frozen
  | .disabled => .Disabled

/-- Map `Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowTransition` directly to vendored
`Miri.TreeBorrows.AccessOutcome`. -/
def v2026TransitionToVendored :
    Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowTransition → Miri.TreeBorrows.AccessOutcome
  | .transition q => .Transition (v2026PermToVendored q)
  | .ub => .UndefinedBehavior
  | .protectedReservedIM => .ImpossibleProtectedReservedIM

/-- **3-way commuting triangle (`Anneal.MiriTreeBorrowsV2026` ↔ `V2026_06_01.MirSemantics` ↔
vendored `Miri.TreeBorrows`)**: the bijection `miriPermToV2026` followed by `v2026PermToVendored`
equals `miriV2026PermToVendored`, and all three 56-cell transition tables agree identically! -/
theorem miriV2026_v2026_vendored_triangle
    (kind : MiriAccessKind) (rel : MiriRelatedness) (perm : MiriPerm) (isProtected : Bool) :
    v2026PermToVendored (miriPermToV2026 perm) = miriV2026PermToVendored perm ∧
    v2026TransitionToVendored
      (Trusted.Rustc.V2026_06_01.MirSemantics.treeBorrowPermTransition
        (miriAccessKindToV2026 kind) (miriRelToV2026 rel)
        (miriPermToV2026 perm) isProtected) =
      miriV2026OutcomeToVendored (miriPerformPermAccess kind rel perm isProtected) ∧
    miriV2026OutcomeToVendored (miriPerformPermAccess kind rel perm isProtected) =
      Miri.TreeBorrows.performAccess
        (miriV2026AccessKindToVendored kind) (miriV2026RelToVendored rel)
        (miriV2026PermToVendored perm) isProtected := by
  refine ⟨?_, ?_, miriV2026_performPermAccess_eq_vendored_performAccess kind rel perm isProtected⟩
  · cases perm <;> rfl
  · rw [← miriPerformPermAccess_eq_v2026_treeBorrowPermTransition]
    cases miriPerformPermAccess kind rel perm isProtected with
    | transition q => cases q <;> rfl
    | undefinedBehavior => rfl
    | impossibleProtectedReservedIM => rfl

/-! ### §4.1. End-to-End Positive & Bidirectional `↔` Negative UB Refutation Witnesses -/

private def ep1Tag1 : BorTag := ⟨1, by decide⟩
private def ep1Tag2 : BorTag := ⟨2, by decide⟩
private def ep1Tag3 : BorTag := ⟨3, by decide⟩
private def ep1AllocId : Miri.Memory.AllocId := ⟨1, by decide⟩

private def ep1LayoutLE64 : TargetDataLayout :=
  { endian := .little, pointerWidth := .w64 }

private def ep1ExtractOk {ε α : Type} : (r : Except ε α) → (match r with | .ok _ => true | .error _ => false) = true → α
  | .ok a, _ => a

private def ep1BaseBytes16 : Array UInt8 :=
  #[0x2A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x77, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

private def ep1BaseAlloc16 : Allocation Provenance Unit :=
  match h : Allocation.fromBytes (Prov := Provenance) ep1BaseBytes16 Align.ONE .Mut with
  | .ok a => a
  | .error _ => False.elim (by cases h)

private theorem ep1BaseAlloc16_fromBytes :
    Allocation.fromBytes (Prov := Provenance) ep1BaseBytes16 Align.ONE .Mut = .ok ep1BaseAlloc16 := by
  unfold ep1BaseAlloc16
  split
  · rename_i a ha; exact ha
  · rename_i _ ha; cases ha

private def ep1Child2Spec : MiriChildInitSpec :=
  { baseOffset := Size.ZERO
    parentProvenance := .concrete ep1Tag1
    newTag := ep1Tag2
    insidePermissions := DedupRangeMap.new (Size.ofBytes 8) ⟨Permission.newFrozen, true, .Read⟩
    outsidePermission := Permission.newCell
    isProtected := true }

private def ep1Child3Spec : MiriChildInitSpec :=
  { baseOffset := Size.ofBytes 8
    parentProvenance := .concrete ep1Tag1
    newTag := ep1Tag3
    insidePermissions := DedupRangeMap.new (Size.ofBytes 8) ⟨Permission.newUnique, true, .None⟩
    outsidePermission := Permission.newCell
    isProtected := true }

private noncomputable def ep1DisjointTwoChildTree : BorrowTree :=
  let t0 := BorrowTree.new ep1Tag1 (Size.ofBytes 16)
  let t1 := (newChildLMU t0 ep1Child2Spec.baseOffset ep1Child2Spec.parentProvenance
    ep1Child2Spec.newTag ep1Child2Spec.insidePermissions ep1Child2Spec.outsidePermission
    ep1Child2Spec.isProtected).tree
  (newChildLMU t1 ep1Child3Spec.baseOffset ep1Child3Spec.parentProvenance
    ep1Child3Spec.newTag ep1Child3Spec.insidePermissions ep1Child3Spec.outsidePermission
    ep1Child3Spec.isProtected).tree

private def ep1Prot23 : ProtectedTags :=
  ({} : ProtectedTags)
    |>.insert ep1Tag2 .StrongProtector
    |>.insert ep1Tag3 .StrongProtector

private def ep1Prot3Only : ProtectedTags :=
  ({} : ProtectedTags)
    |>.insert ep1Tag3 .StrongProtector

private def ep1SegPerm (tree : BorrowTree) (segIdx : Nat) (tag : BorTag) : Option Permission :=
  match tree.locations.index segIdx, tree.indexOfTag tag with
  | .ok seg, some idx => (seg.data.perms.get idx).map (·.permission)
  | _, _ => none

private noncomputable def ep1ObsState : MiriObservedState Provenance :=
  { memory :=
      { (MemoryState.empty : MemoryState Provenance BorrowTree Unit) with
        nextAllocId := 2
        live := #[(ep1AllocId, { kind := .stack, allocation := ep1BaseAlloc16.withExtra ep1DisjointTwoChildTree })] }
    protectedTags := ep1Prot23 }

/-- **Positive Witness 1 (Initial-State `BorrowTree.new` → `newChild` via `miriTreeInitAndRangeExactWP_iff`
→ Disjoint Ranged Write → Read-Only Memory Observation (`.bytes` & `.scalar`) → Clean Protector Release)**:
Starting literally from `BorrowTree.new ep1Tag1 (Size.ofBytes 16)`:
1. `miriTreeInitAndRangeExactWP_iff` constructs both disjoint children (`tag 2` `Frozen` on `[0..8)`,
   `tag 3` `Unique` on `[8..16)`) and executes a write via `tag 3` on `[8..16)` cleanly!
2. Writing via `tag 3` on `[8..16)` succeeds (`.Completed`) AND frames disjoint segment 0 (`[0..8)`),
   leaving `tag 2` `Frozen`, followed by clean protector release (`.Released`) removing `tag 3`
   while preserving `tag 2`'s strong protector!
3. Observing `[0..4)` via `miriObserveMemoryAction` (both `.bytes` and `.scalar`) returns exact
   `#[0x2A, 0, 0, 0]` / `mkMiriU32Scalar 42` while leaving the ENTIRE `MiriObservedState`
   strictly immutable! -/
theorem witness_positive_initial_tree_range_observe_and_release :
    let initTree := ep1DisjointTwoChildTree
    let obsState := ep1ObsState
    let r0 : AllocRange := allocRange Size.ZERO (Size.ofBytes 4)
    AnnealExactWP
      (ExactAction.seq
        (mapExactActionErr MiriTreePipelineError.childInsert
          (miriTreeInitialSetupAction [ep1Child2Spec, ep1Child3Spec]))
        (mapExactActionErr (fun p => MiriTreePipelineError.access p.1 p.2)
          (miriTreeRangeAction (.concrete ep1Tag3) (Size.ofBytes 8) (Size.ofBytes 8)
            .Write ep1Prot23 .VisitChildrenOfAccessed)))
      (fun _ finalTree =>
        ep1SegPerm finalTree 0 ep1Tag2 = some Permission.newFrozen ∧
        ep1SegPerm finalTree 1 ep1Tag3 = some Permission.newUnique)
      (fun _ _ => False) (BorrowTree.new ep1Tag1 (Size.ofBytes 16)) ∧
    AnnealExactWP
      (ExactAction.seq
        (miriTreeWithProtRangeAction (.concrete ep1Tag3) (Size.ofBytes 8) (Size.ofBytes 8)
          .Write .VisitChildrenOfAccessed)
        (miriTreeWithProtReleaseAction ep1Tag3))
      (fun _ finalPair =>
        ep1SegPerm finalPair.1 0 ep1Tag2 = some Permission.newFrozen ∧
        ep1SegPerm finalPair.1 1 ep1Tag3 = some Permission.newUnique ∧
        finalPair.2.get ep1Tag3 = none ∧
        finalPair.2.get ep1Tag2 = some .StrongProtector)
      (fun _ _ => False) (initTree, ep1Prot23) ∧
    AnnealExactWP (miriObserveMemoryAction ep1LayoutLE64 ep1AllocId (.bytes r0))
      (fun val st' => val = .bytes #[0x2A, 0x00, 0x00, 0x00] ∧ st' = obsState)
      (fun _ _ => False) obsState ∧
    AnnealExactWP (miriObserveMemoryAction ep1LayoutLE64 ep1AllocId (.scalar r0 false))
      (fun val st' => val = .scalar (mkMiriU32Scalar 42) ∧ st' = obsState)
      (fun _ _ => False) obsState := by
  let r0 : AllocRange := allocRange Size.ZERO (Size.ofBytes 4)
  obtain ⟨_, _, _, _, _, hProv, hMask, _, hFullBytes⟩ :=
    Allocation.fromBytes_spec ep1BaseBytes16 Align.ONE .Mut ep1BaseAlloc16 ep1BaseAlloc16_fromBytes
  have hInitR0 : ep1BaseAlloc16.initializationMask.isRangeInitialized r0 = .ok (.ok ()) := by
    rw [hMask]; decide
  have hProvR0 :
      ep1BaseAlloc16.provenanceMap.rangeEmpty r0 (Size.fromBits ep1LayoutLE64.pointerWidth.bits) =
        .ok true := by
    rw [hProv]; decide
  have hRawR0 : ep1BaseAlloc16.getBytesUnchecked r0 = .ok #[0x2A, 0x00, 0x00, 0x00] :=
    (hFullBytes r0 (Size.ofBytes 4) (by decide) (by decide) (by decide)).trans (by decide)
  have hStripR0 :
      (ep1BaseAlloc16.withExtra ep1DisjointTwoChildTree).getBytesStripProvenance ep1LayoutLE64 r0 =
        .ok #[0x2A, 0x00, 0x00, 0x00] := by
    change (ep1BaseAlloc16.mapExtra (fun _ => ep1DisjointTwoChildTree)).getBytesStripProvenance
      ep1LayoutLE64 r0 = .ok #[0x2A, 0x00, 0x00, 0x00]
    rw [Allocation.getBytesStripProvenance_mapExtra]
    rw [Allocation.getBytesStripProvenance_ok ep1BaseAlloc16 ep1LayoutLE64 r0 hInitR0 (Or.inr hProvR0)]
    exact hRawR0
  have hScalarR0 :
      (ep1BaseAlloc16.withExtra ep1DisjointTwoChildTree).readScalar ep1LayoutLE64 r0 false =
        .ok (mkMiriU32Scalar 42) := by
    change (ep1BaseAlloc16.mapExtra (fun _ => ep1DisjointTwoChildTree)).readScalar
      ep1LayoutLE64 r0 false = .ok (mkMiriU32Scalar 42)
    rw [Allocation.readScalar_mapExtra]
    rw [Allocation.readScalar_int_of_bytes ep1BaseAlloc16 ep1LayoutLE64 r0
      #[0x2A, 0x00, 0x00, 0x00] hInitR0 hRawR0 (by decide) (Or.inr hProvR0)]
    decide
  have hLookupObs : lookupLiveAlloc ep1ObsState ep1AllocId =
      some (ep1BaseAlloc16.withExtra ep1DisjointTwoChildTree) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [miriTreeInitAndRangeExactWP_iff]
    dsimp only [exactFoldWP]
    rw [miriTreeNewChildExactWP_iff]
    unfold miriTreeNewChildPre
    dsimp only
    rw [newChildLMU.eq_src]
    have hC2 :
        (newChildLMU (BorrowTree.new ep1Tag1 (Size.ofBytes 16))
          ep1Child2Spec.baseOffset ep1Child2Spec.parentProvenance ep1Child2Spec.newTag
          ep1Child2Spec.insidePermissions ep1Child2Spec.outsidePermission
          ep1Child2Spec.isProtected).outcome = .ok () := by kernel_rfl
    rw [hC2]
    dsimp only [exactFoldWP]
    rw [miriTreeNewChildExactWP_iff]
    unfold miriTreeNewChildPre
    dsimp only
    rw [newChildLMU.eq_src]
    have hC3 :
        (newChildLMU
          (newChildLMU (BorrowTree.new ep1Tag1 (Size.ofBytes 16))
            ep1Child2Spec.baseOffset ep1Child2Spec.parentProvenance ep1Child2Spec.newTag
            ep1Child2Spec.insidePermissions ep1Child2Spec.outsidePermission
            ep1Child2Spec.isProtected).tree
          ep1Child3Spec.baseOffset ep1Child3Spec.parentProvenance ep1Child3Spec.newTag
          ep1Child3Spec.insidePermissions ep1Child3Spec.outsidePermission
          ep1Child3Spec.isProtected).outcome = .ok () := by kernel_rfl
    rw [hC3]
    dsimp only [exactFoldWP]
    rw [← miriTreeRangeSymbolicExactWP_iff, miriTreeRangeExactWP_iff]
    unfold tbAccessPre
    dsimp only
    change match (ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag3)
        (Size.ofBytes 8) (Size.ofBytes 8) .Write ep1Prot23 .VisitChildrenOfAccessed).status with
      | .Completed => _ | _ => False
    rw [performBorrowAccessRangeLMU.eq_src]
    have hStatus :
        (performBorrowAccessRangeLMU ep1DisjointTwoChildTree (.concrete ep1Tag3)
          (Size.ofBytes 8) (Size.ofBytes 8) .Write ep1Prot23 .VisitChildrenOfAccessed).status =
        .Completed := by kernel_rfl
    rw [hStatus]
    exact ⟨by kernel_rfl, by kernel_rfl⟩
  · rw [miriTreeRangeThenReleaseExactWP_iff]
    unfold tbAccessPre
    dsimp only
    rw [performBorrowAccessRangeLMU.eq_src]
    have hStatus :
        (performBorrowAccessRangeLMU ep1DisjointTwoChildTree (.concrete ep1Tag3)
          (Size.ofBytes 8) (Size.ofBytes 8) .Write ep1Prot23 .VisitChildrenOfAccessed).status =
        .Completed := by kernel_rfl
    rw [hStatus]
    dsimp only
    rw [← protectorReleaseSymbolicPre_iff]
    unfold AnnealExactWP ExactWpAndMemoryFrameLM.protectorReleaseAction
    dsimp only
    rw [releaseProtectorLMU.eq_src]
    have hRelStatus :
        (releaseProtectorLMU
          (performBorrowAccessRangeLMU ep1DisjointTwoChildTree (.concrete ep1Tag3)
            (Size.ofBytes 8) (Size.ofBytes 8) .Write ep1Prot23 .VisitChildrenOfAccessed).tree
          ep1Tag3 ep1Prot23).status = .Released := by kernel_rfl
    rw [hRelStatus]
    refine ⟨by kernel_rfl, by kernel_rfl, by decide, by decide⟩
  · rw [miriObserveMemoryExactWP_iff]
    unfold miriObserveMemoryPre
    rw [hLookupObs]
    dsimp only
    rw [hStripR0]
    exact ⟨rfl, rfl⟩
  · rw [miriObserveMemoryExactWP_iff]
    unfold miriObserveMemoryPre
    rw [hLookupObs]
    dsimp only
    rw [hScalarR0]
    exact ⟨rfl, rfl⟩

/-- **Negative UB Refutation Witness 1 & 2 + Committed-Prefix Retention on Error**:
1. **Protected Foreign Write UB**: writing through root `tag 1` on `[0..8)` disables protected
   `tag 2` (`Frozen`), faulting with `.AccessFailure ⟨0, 8⟩ (.TransitionError 1 (.ProtectedDisabled .Frozen))`,
   so `¬ AnnealExactWP (miriTreeRangeAction ...) (fun _ _ => True) (fun _ _ => False)`!
2. **Frozen Local Write UB**: writing through `tag 2` (`Frozen`) on `[0..8)` faults with
   `.AccessFailure ⟨0, 8⟩ (.TransitionError 1 (.ChildAccessForbidden .Frozen))`, so
   `¬ AnnealExactWP (miriTreeRangeAction ...) (fun _ _ => True) (fun _ _ => False)`!
3. **Multi-Segment Committed-Prefix Retention on Error**: writing through root `tag 1` across
   `[0..16)` when ONLY `tag 3` (`[8..16)`) is protected (`ep1Prot3Only`) commits segment 0
   (`tag 2` transitions `.Frozen → .Disabled` on `[0..8)`) before faulting on segment 1
   (`.ProtectedDisabled .Unique`), AND `AnnealExactWP`'s `onError` branch exposes the committed
   post-tree with `ep1SegPerm errTree 0 ep1Tag2 = some .Disabled`! -/
theorem witness_negative_tree_protected_foreign_and_frozen_local_write_ub :
    AnnealExactWP
      (miriTreeRangeAction (.concrete ep1Tag1) Size.ZERO (Size.ofBytes 8) .Write
        ep1Prot23 .VisitChildrenOfAccessed)
      (fun _ _ => False)
      (fun errPair _ =>
        errPair.1 = .AccessFailure ⟨0, 8⟩ (.TransitionError 1 (.ProtectedDisabled .Frozen)))
      ep1DisjointTwoChildTree ∧
    ¬ AnnealExactWP
      (miriTreeRangeAction (.concrete ep1Tag1) Size.ZERO (Size.ofBytes 8) .Write
        ep1Prot23 .VisitChildrenOfAccessed)
      (fun _ _ => True) (fun _ _ => False) ep1DisjointTwoChildTree ∧
    AnnealExactWP
      (miriTreeRangeAction (.concrete ep1Tag2) Size.ZERO (Size.ofBytes 8) .Write
        ep1Prot23 .VisitChildrenOfAccessed)
      (fun _ _ => False)
      (fun errPair _ =>
        errPair.1 = .AccessFailure ⟨0, 8⟩ (.TransitionError 1 (.ChildAccessForbidden .Frozen)))
      ep1DisjointTwoChildTree ∧
    ¬ AnnealExactWP
      (miriTreeRangeAction (.concrete ep1Tag2) Size.ZERO (Size.ofBytes 8) .Write
        ep1Prot23 .VisitChildrenOfAccessed)
      (fun _ _ => True) (fun _ _ => False) ep1DisjointTwoChildTree ∧
    AnnealExactWP
      (miriTreeRangeAction (.concrete ep1Tag1) Size.ZERO (Size.ofBytes 16) .Write
        ep1Prot3Only .VisitChildrenOfAccessed)
      (fun _ _ => False)
      (fun errPair errTree =>
        errPair.1 = .AccessFailure ⟨8, 16⟩ (.TransitionError 2 (.ProtectedDisabled .Unique)) ∧
        ep1SegPerm errTree 0 ep1Tag2 = some .Disabled)
      ep1DisjointTwoChildTree ∧
    ¬ AnnealExactWP
      (miriTreeRangeAction (.concrete ep1Tag1) Size.ZERO (Size.ofBytes 16) .Write
        ep1Prot3Only .VisitChildrenOfAccessed)
      (fun _ _ => True) (fun _ _ => False) ep1DisjointTwoChildTree := by
  have hProt :
      (performBorrowAccessRangeLMU ep1DisjointTwoChildTree (.concrete ep1Tag1)
        Size.ZERO (Size.ofBytes 8) .Write ep1Prot23 .VisitChildrenOfAccessed).status =
      .AccessFailure ⟨0, 8⟩ (.TransitionError 1 (.ProtectedDisabled .Frozen)) := by kernel_rfl
  have hFroz :
      (performBorrowAccessRangeLMU ep1DisjointTwoChildTree (.concrete ep1Tag2)
        Size.ZERO (Size.ofBytes 8) .Write ep1Prot23 .VisitChildrenOfAccessed).status =
      .AccessFailure ⟨0, 8⟩ (.TransitionError 1 (.ChildAccessForbidden .Frozen)) := by kernel_rfl
  have hPrefix :
      (performBorrowAccessRangeLMU ep1DisjointTwoChildTree (.concrete ep1Tag1)
        Size.ZERO (Size.ofBytes 16) .Write ep1Prot3Only .VisitChildrenOfAccessed).status =
      .AccessFailure ⟨8, 16⟩ (.TransitionError 2 (.ProtectedDisabled .Unique)) := by kernel_rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [miriTreeRangeExactWP_iff]; unfold tbAccessPre; dsimp only
    rw [performBorrowAccessRangeLMU.eq_src, hProt]
  · intro hSafe
    rw [miriTreeRangeExactWP_iff] at hSafe
    unfold tbAccessPre at hSafe; dsimp only at hSafe
    rw [performBorrowAccessRangeLMU.eq_src, hProt] at hSafe
    exact hSafe
  · rw [miriTreeRangeExactWP_iff]; unfold tbAccessPre; dsimp only
    rw [performBorrowAccessRangeLMU.eq_src, hFroz]
  · intro hSafe
    rw [miriTreeRangeExactWP_iff] at hSafe
    unfold tbAccessPre at hSafe; dsimp only at hSafe
    rw [performBorrowAccessRangeLMU.eq_src, hFroz] at hSafe
    exact hSafe
  · rw [miriTreeRangeExactWP_iff]; unfold tbAccessPre; dsimp only
    rw [performBorrowAccessRangeLMU.eq_src, hPrefix]
    exact ⟨rfl, by kernel_rfl⟩
  · intro hSafe
    rw [miriTreeRangeExactWP_iff] at hSafe
    unfold tbAccessPre at hSafe; dsimp only at hSafe
    rw [performBorrowAccessRangeLMU.eq_src, hPrefix] at hSafe
    exact hSafe

/-- **Negative UB Refutation Witness 3 (Uninit Memory Observation Error via `↔` + Immutability)**:
On a fresh uninitialized 8-byte `Allocation.tryNew ... .Uninit`:
1. Both `miriObserveScalarAction` and `miriObserveBytesAction` fault with `.invalidUninitBytes`
   leaving `alloc` strictly unmodified;
2. Via `↔`, pure-safety `AnnealExactWP ... (fun _ _ => True) (fun _ _ => False)` is REFUTED! -/
theorem witness_negative_uninit_memory_observation_refutation :
    let r0 : AllocRange := allocRange Size.ZERO (Size.ofBytes 4)
    ∃ alloc : Allocation Provenance Unit,
      Allocation.tryNew (Prov := Provenance) (Size.ofBytes 8) Align.ONE .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok alloc ∧
      AnnealExactWP (miriObserveScalarAction ep1LayoutLE64 r0 false)
        (fun _ _ => False)
        (fun err a' => (match err with | .invalidUninitBytes _ => True | _ => False) ∧ a' = alloc)
        alloc ∧
      ¬ AnnealExactWP (miriObserveScalarAction ep1LayoutLE64 r0 false)
        (fun _ _ => True) (fun _ _ => False) alloc ∧
      AnnealExactWP (miriObserveBytesAction ep1LayoutLE64 r0)
        (fun _ _ => False)
        (fun err a' => (match err with | .invalidUninitBytes _ => True | _ => False) ∧ a' = alloc)
        alloc ∧
      ¬ AnnealExactWP (miriObserveBytesAction ep1LayoutLE64 r0)
        (fun _ _ => True) (fun _ _ => False) alloc := by
  let r0 : AllocRange := allocRange Size.ZERO (Size.ofBytes 4)
  obtain ⟨alloc, hCreated, _⟩ :=
    Allocation.tryNew_exists (P := Provenance) (Size.ofBytes 8) Align.ONE 1 .Uninit
      (by decide) (by decide)
  obtain ⟨_, _, _, _, _, _, hMaskUninit, _, _, _⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 8) Align.ONE .Uninit alloc hCreated
  have hUninit : alloc.initializationMask.isRangeInitialized r0 = .ok (.error r0) := by
    rw [hMaskUninit rfl]; decide
  refine ⟨alloc, hCreated, ?_, ?_, ?_, ?_⟩
  · rw [allocReadScalar_uninit_exactWP alloc ep1LayoutLE64 r0 r0 false _ _ hUninit]
    exact ⟨trivial, rfl⟩
  · intro hSafe
    rw [allocReadScalar_uninit_exactWP alloc ep1LayoutLE64 r0 r0 false _ _ hUninit] at hSafe
    exact hSafe
  · rw [miriObserveBytes_uninit_err_exactWP alloc ep1LayoutLE64 r0 r0 _ _ hUninit]
    exact ⟨trivial, rfl⟩
  · intro hSafe
    rw [miriObserveBytes_uninit_err_exactWP alloc ep1LayoutLE64 r0 r0 _ _ hUninit] at hSafe
    exact hSafe

private def ep1SampleFnAbi : FnAbi Miri.MIR.TyId :=
  { conv := .Rust
    args := #[]
    ret := { layout := { ty := 0, layout := zstLayoutData }, mode := .Ignore }
    cVariadic := false
    fixedCount := 0
    canUnwind := true }

private def ep1SampleDest : RuntimeStackPlace Provenance :=
  .frameLocal 0 0 none { ty := 0, layout := zstLayoutData } (LocalsIdentity.ofAllocationToken 0)

private def ep1SampleBody : LoadedBody :=
  { identity := BodyIdentity.ofCanonicalIndex 0
    body :=
      { phase := .Built
        argumentCount := 0
        spreadArgument := none
        locals := #[]
        basicBlocks := #[] } }

private def ep1SampleCallee : CallInstance :=
  { kind := .Item 1, args := #[] }

private def ep1CallHooks (isFor : Bool) (backendRes : Except StepError IntrinsicBackend.Kind) :
    CallDispatchMachine.Hooks Nat Unit String :=
  { foreign := none
    returnToBlock := fun _ => pure ()
    isForeignItem := fun _ => pure isFor
    symbolName := fun _ => pure "extern_missing_sym"
    loadMir := fun _ _ => pure ep1SampleBody
    backend := { selection := fun _ => backendRes }
    dynSymName := id
    foreignScope := id }

/-- **Positive & Negative Call-Dispatch Witness (`miriCallDispatchExactWP_iff` & `miriCallExtraExactWP_iff`)**:
1. Positive: non-foreign MIR call with `.none` backend succeeds returning `some (ep1SampleBody, ep1SampleCallee)`
   and framing caller state `7`;
2. Negative #1 (Missing Foreign Call Error + `↔` Refutation): foreign item with `foreign := none`
   faults with `.unsupported "foreign call requires complete source platform input: extern_missing_sym"`;
3. Negative #2 (Backend Selection Error + `↔` Refutation): non-foreign item with failing backend
   faults with `.unsupported "backend unavailable"`;
4. Negative #3 (`callExtra` Missing Foreign Error + `↔` Refutation): dynamic foreign call with
   `foreign := none` faults with `.unsupported "dynamic foreign call requires complete source platform input"`. -/
theorem witness_call_dispatch_positive_and_negative_refutations :
    AnnealExactWP
      (miriCallDispatchAction (ep1CallHooks false (.ok .none)) () ep1SampleCallee
        ep1SampleFnAbi #[] ep1SampleDest (some 1) .Continue)
      (fun res s' => res = some (ep1SampleBody, ep1SampleCallee) ∧ s' = 7)
      (fun _ _ => False) 7 ∧
    AnnealExactWP
      (miriCallDispatchAction (ep1CallHooks true (.ok .none)) () ep1SampleCallee
        ep1SampleFnAbi #[] ep1SampleDest (some 1) .Continue)
      (fun _ _ => False)
      (fun err s' =>
        err = .unsupported "foreign call requires complete source platform input: extern_missing_sym" ∧
        s' = 7) 7 ∧
    ¬ AnnealExactWP
      (miriCallDispatchAction (ep1CallHooks true (.ok .none)) () ep1SampleCallee
        ep1SampleFnAbi #[] ep1SampleDest (some 1) .Continue)
      (fun _ _ => True) (fun _ _ => False) 7 ∧
    AnnealExactWP
      (miriCallDispatchAction (ep1CallHooks false (.error (.unsupported "backend unavailable"))) ()
        ep1SampleCallee ep1SampleFnAbi #[] ep1SampleDest (some 1) .Continue)
      (fun _ _ => False)
      (fun err s' => err = .unsupported "backend unavailable" ∧ s' = 7) 7 ∧
    ¬ AnnealExactWP
      (miriCallDispatchAction (ep1CallHooks false (.error (.unsupported "backend unavailable"))) ()
        ep1SampleCallee ep1SampleFnAbi #[] ep1SampleDest (some 1) .Continue)
      (fun _ _ => True) (fun _ _ => False) 7 ∧
    AnnealExactWP
      (miriCallExtraAction (ep1CallHooks true (.ok .none)) () "dyn_sym"
        ep1SampleFnAbi #[] ep1SampleDest (some 1) .Continue)
      (fun _ _ => False)
      (fun err s' =>
        err = .unsupported "dynamic foreign call requires complete source platform input" ∧
        s' = 7) 7 ∧
    ¬ AnnealExactWP
      (miriCallExtraAction (ep1CallHooks true (.ok .none)) () "dyn_sym"
        ep1SampleFnAbi #[] ep1SampleDest (some 1) .Continue)
      (fun _ _ => True) (fun _ _ => False) 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [miriCallDispatch_loadMir_exactWP (ep1CallHooks false (.ok .none)) () ep1SampleCallee
      ep1SampleFnAbi #[] ep1SampleDest (some 1) .Continue _ _ 7 7 7 .none ep1SampleBody rfl rfl rfl]
    exact ⟨rfl, rfl⟩
  · rw [miriCallDispatch_missingForeign_exactWP (ep1CallHooks true (.ok .none)) () ep1SampleCallee
      ep1SampleFnAbi #[] ep1SampleDest (some 1) .Continue _ _ 7 7 7 "extern_missing_sym" rfl rfl rfl]
    exact ⟨rfl, rfl⟩
  · intro hSafe
    rw [miriCallDispatch_missingForeign_exactWP (ep1CallHooks true (.ok .none)) () ep1SampleCallee
      ep1SampleFnAbi #[] ep1SampleDest (some 1) .Continue _ _ 7 7 7 "extern_missing_sym" rfl rfl rfl]
      at hSafe
    exact hSafe
  · rw [miriCallDispatch_backendError_exactWP
      (ep1CallHooks false (.error (.unsupported "backend unavailable"))) () ep1SampleCallee
      ep1SampleFnAbi #[] ep1SampleDest (some 1) .Continue _ _ 7 7 (.unsupported "backend unavailable")
      rfl rfl]
    exact ⟨rfl, rfl⟩
  · intro hSafe
    rw [miriCallDispatch_backendError_exactWP
      (ep1CallHooks false (.error (.unsupported "backend unavailable"))) () ep1SampleCallee
      ep1SampleFnAbi #[] ep1SampleDest (some 1) .Continue _ _ 7 7 (.unsupported "backend unavailable")
      rfl rfl] at hSafe
    exact hSafe
  · rw [miriCallExtraExactWP_iff]; exact ⟨rfl, rfl⟩
  · intro hSafe; rw [miriCallExtraExactWP_iff] at hSafe; exact hSafe

private def ep1ForeignHooks (retLog : Option Miri.MIR.BasicBlockId → Nat → Nat) :
    ForeignItems.Hooks Provenance Nat (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance :=
  { family := .unix
    os := "linux"
    arch := "x86_64"
    maximumSize := 1024
    noAllocShimSymbol := "__rust_no_alloc_shim_is_unstable_v2"
    allocatorSymbol := fun _ => pure none
    lookupFunction := fun _ => pure none
    forceAllocation := fun d => pure d
    returnToBlock := fun ret s => .ok () (retLog ret s)
    unwindToBlock := fun _ => pure ()
    nativeEnabled := false
    callNative := fun _ _ _ => pure false
    expectedAbi := fun sig => pure { ep1SampleFnAbi with conv := sig.conv }
    argumentCompat := fun _ _ => pure true
    checkSymbolClash := fun _ => pure ()
    transmute := fun op _ => pure op
    readUsize := fun _ => pure 0
    readPointer := fun _ => pure ⟨Size.ZERO, none⟩
    readI32 := fun _ => pure 0
    isNull := fun _ => pure true
    allocate := fun _ _ _ _ => pure ⟨Size.ZERO, none⟩
    deallocate := fun _ _ _ => pure ()
    reallocate := fun _ _ _ _ _ => pure ⟨Size.ZERO, none⟩
    writePointer := fun _ _ => pure ()
    writeNull := fun _ => pure ()
    setEnomem := pure ()
    startExit := fun _ => pure ()
    specialDestination := fun d => pure d
    math := fun _ _ _ _ => pure .NotSupported
    unix := fun _ _ _ _ => pure .NotSupported
    windows := fun _ _ _ _ => pure .NotSupported
    otherPortable := fun _ _ _ _ => pure none }

private def ep1CallHooksWithForeign (sym : String) :
    CallDispatchMachine.Hooks Nat Unit String :=
  { ep1CallHooks true (.ok .none) with
    symbolName := fun _ => pure sym
    foreign := some (pure (ep1ForeignHooks (fun ret s => (ret.getD 0) + s))) }

private def ep1NoProgressCallBody : Miri.MIR.Body :=
  { phase := .Built
    argumentCount := 0
    spreadArgument := none
    locals := #[]
    basicBlocks :=
      #[{ statements := #[]
          terminator :=
            ⟨⟨defaultSpanRef, 0⟩,
             .Call (.Copy ⟨0, #[]⟩) #[] ⟨0, #[]⟩ (some 0) .Continue .Normal defaultSpanRef⟩
          cleanup := false }] }

private def ep1NoProgressState : AnnealStepState :=
  let frame : Frame AnnealProv LocalLayout Unit :=
    { body := ep1NoProgressCallBody
      bodyIdentity := BodyIdentity.ofCanonicalIndex 0
      functionInstance := ⟨.Item 0, #[]⟩
      extra := ()
      returnContinuation := .stop false
      returnPlace := .frameLocal 0 0 none { ty := 0, layout := zstLayoutData }
        (LocalsIdentity.ofAllocationToken 0)
      localsIdentity := LocalsIdentity.ofAllocationToken 0
      locals := #[]
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 0⟩ }
  { stack := { frames := #[frame] }, machine := AnnealMachine.empty }

private def ep1NoProgressTermHooks :
    TerminatorHooks AnnealProv LocalLayout Unit AnnealMachine Unit
      (Miri.Interpreter.Operand AnnealProv) (RvalueImmTy AnnealProv) :=
  { annealTerminatorHooks [] emptyLayoutTable with
    call := fun _ _ st => (st, .ok ()) }

private def ep1NoProgressStepHooks :
    StepHooks AnnealProv LocalLayout Unit AnnealMachine Unit (RuntimePlace AnnealProv) :=
  { annealStepHooks [] emptyLayoutTable with
    terminator := ControlFlow.evalTerminator ep1NoProgressTermHooks }

/-- **Real `ForeignItems.emulate` Positive & Negative Dispatch + `.Call` Terminator No-Progress
Guard Witness**:
1. Positive (`ForeignItems.emulate`): calling foreign shim `"__rust_no_alloc_shim_is_unstable_v2"`
   through real `CallDispatchMachine.findMirOrEvalFn` → `ForeignItems.emulate` checks the Rust ABI
   via `ForeignItems.checkSignature`, invokes `returnToBlock (some 5)` (`7 ↦ 12`), and returns `none`!
2. Negative #1 (`ForeignItems.emulate` `"abort"` + `↔` refutation): calling `"abort"` with C ABI
   faults with `.machineStop "the program aborted execution"`, refuting pure safety via `↔`!
3. Negative #2 (`miriStepCallTerminatorExactWP_iff` no-progress guard + `↔` refutation): a `.Call`
   terminator with `target = some 0` whose `hooks.call` leaves frame count and location unchanged
   triggers rustc's real no-progress guard `.invalidProgram "evaluating this call made no progress"`,
   refuting pure safety via `↔`! -/
theorem witness_call_dispatch_foreign_emulate_and_call_terminator :
    let abiC : FnAbi Miri.MIR.TyId := { ep1SampleFnAbi with conv := .C }
    AnnealExactWP
      (miriCallDispatchAction (ep1CallHooksWithForeign "__rust_no_alloc_shim_is_unstable_v2") ()
        ep1SampleCallee ep1SampleFnAbi #[] ep1SampleDest (some 5) .Continue)
      (fun res s' => res = none ∧ s' = 12)
      (fun _ _ => False) 7 ∧
    AnnealExactWP
      (miriCallDispatchAction (ep1CallHooksWithForeign "abort") ()
        ep1SampleCallee abiC #[] ep1SampleDest (some 5) .Continue)
      (fun _ _ => False)
      (fun err s' => err = .machineStop "the program aborted execution" ∧ s' = 7) 7 ∧
    ¬ AnnealExactWP
      (miriCallDispatchAction (ep1CallHooksWithForeign "abort") ()
        ep1SampleCallee abiC #[] ep1SampleDest (some 5) .Continue)
      (fun _ _ => True) (fun _ _ => False) 7 ∧
    AnnealExactWP (miriStepAction ep1NoProgressStepHooks ())
      (fun _ _ => False)
      (fun err s' =>
        err = .invalidProgram "evaluating this call made no progress" ∧
        s' = ep1NoProgressState)
      ep1NoProgressState ∧
    ¬ AnnealExactWP (miriStepAction ep1NoProgressStepHooks ())
      (fun _ _ => True) (fun _ _ => False) ep1NoProgressState := by
  let abiC : FnAbi Miri.MIR.TyId := { ep1SampleFnAbi with conv := .C }
  have hNoProg :
      ∀ (post : Bool → AnnealStepState → Prop) (onError : StepError → AnnealStepState → Prop),
        AnnealExactWP (miriStepAction ep1NoProgressStepHooks ()) post onError ep1NoProgressState ↔
          onError (.invalidProgram "evaluating this call made no progress") ep1NoProgressState := by
    intro post onError
    have hStep := miriStepCallTerminatorExactWP_iff ep1NoProgressStepHooks ep1NoProgressTermHooks () rfl
      post onError ep1NoProgressState (ep1NoProgressState.stack.frames[0]'(by decide))
      ⟨0, 0⟩ (ep1NoProgressCallBody.basicBlocks[0]'(by decide))
      (.Copy ⟨0, #[]⟩) #[] ⟨0, #[]⟩ (some 0) .Continue .Normal defaultSpanRef ⟨defaultSpanRef, 0⟩
      rfl rfl rfl rfl rfl
    dsimp only at hStep
    rw [hStep]
    rfl
  have hNoAllocEval :
      ((ep1CallHooksWithForeign "__rust_no_alloc_shim_is_unstable_v2").foreignScope (do
        let foreign ← pure (ep1ForeignHooks (fun ret s => (ret.getD 0) + s))
        ForeignItems.emulate foreign "__rust_no_alloc_shim_is_unstable_v2" ep1SampleFnAbi
          (#[].map FnArg.copyFnArg) ep1SampleDest.toRuntimePlace (some 5) .Continue)) 7 =
      .ok none 12 := by kernel_rfl
  have hAbortEval :
      ((ep1CallHooksWithForeign "abort").foreignScope (do
        let foreign ← pure (ep1ForeignHooks (fun ret s => (ret.getD 0) + s))
        ForeignItems.emulate foreign "abort" abiC
          (#[].map FnArg.copyFnArg) ep1SampleDest.toRuntimePlace (some 5) .Continue)) 7 =
      .error (.machineStop "the program aborted execution") 7 := by kernel_rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [miriCallDispatch_foreignEmulate_exactWP
      (ep1CallHooksWithForeign "__rust_no_alloc_shim_is_unstable_v2") ()
      ep1SampleCallee ep1SampleFnAbi #[] ep1SampleDest (some 5) .Continue _ _ 7 7 7
      "__rust_no_alloc_shim_is_unstable_v2" _ rfl rfl rfl]
    unfold AnnealExactWP ExactAction.ofEStateM
    rw [hNoAllocEval]
    exact ⟨rfl, rfl⟩
  · rw [miriCallDispatch_foreignEmulate_exactWP
      (ep1CallHooksWithForeign "abort") ()
      ep1SampleCallee abiC #[] ep1SampleDest (some 5) .Continue _ _ 7 7 7
      "abort" _ rfl rfl rfl]
    unfold AnnealExactWP ExactAction.ofEStateM
    rw [hAbortEval]
    exact ⟨rfl, rfl⟩
  · intro hSafe
    rw [miriCallDispatch_foreignEmulate_exactWP
      (ep1CallHooksWithForeign "abort") ()
      ep1SampleCallee abiC #[] ep1SampleDest (some 5) .Continue _ _ 7 7 7
      "abort" _ rfl rfl rfl] at hSafe
    unfold AnnealExactWP ExactAction.ofEStateM at hSafe
    rw [hAbortEval] at hSafe
    exact hSafe
  · rw [hNoProg]; exact ⟨rfl, rfl⟩
  · intro hSafe; rw [hNoProg] at hSafe; exact hSafe

private def ep1U32Ty : Trusted.Rustc.V2026_06_01.MirAst.Ty := ⟨.uint .u32, 0⟩
private def ep1U32Decl : LocalDecl := ⟨.mut, ep1U32Ty, some "ret"⟩
private def ep1TmpDecl : LocalDecl := ⟨.mut, ep1U32Ty, some "tmp"⟩

private def ep1UnitLayout : Trusted.Rustc.V2026_06_01.Layout.TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }

private def mkEp1Body (name : String) (decls : List LocalDecl) (blocks : List BasicBlockData) :
    CapturedMir :=
  { defPath := name
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls := decls
    basicBlocks := blocks
    fnAbi := { args := [], ret := { layout := ep1UnitLayout, mode := .direct },
               conv := .rust, canUnwind := true }
    layouts := emptyLayoutTable
    allocations := [] }

/-- Real `V2026_06_01` `CapturedMir` body exercising `StorageLive`, `Assign`, `PlaceMention`,
`Nop`, `StorageDead`, and `Return` through `LeanMiriSpec.Correspondence.translateBody`. -/
def ep1BodyMultiStmtPositive : CapturedMir :=
  mkEp1Body "ep1::multi_stmt_positive" [ep1U32Decl, ep1TmpDecl]
    [ { statements :=
          [ { kind := .storageLive 1, span := "s0" },
            { kind := .assign ⟨1, []⟩ (.use (.constant ⟨ep1U32Ty, .scalar (.int ⟨42, 4⟩)⟩)),
              span := "s1" },
            { kind := .placeMention ⟨1, []⟩, span := "s2" },
            { kind := .nop, span := "s3" },
            { kind := .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩)), span := "s4" },
            { kind := .storageDead 1, span := "s5" } ],
        terminator := { kind := .return_, span := "t0" },
        isCleanup := false } ]

/-- Real `V2026_06_01` `CapturedMir` negative UB body #1: marks `_1` `StorageDead` and then reads
`_1` (`_0 = copy _1`), faulting with `.undefinedBehavior "read of dead local"`! -/
def ep1BodyDeadLocalReadUB : CapturedMir :=
  mkEp1Body "ep1::dead_local_read_ub" [ep1U32Decl, ep1TmpDecl]
    [ { statements :=
          [ { kind := .storageDead 1, span := "s0" },
            { kind := .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩)), span := "s1" } ],
        terminator := { kind := .return_, span := "t0" },
        isCleanup := false } ]

/-- Real `V2026_06_01` `CapturedMir` negative UB body #2: executes `Return` while `_0` is still
uninitialized, faulting with `.undefinedBehavior "return with uninitialized or dead _0"`! -/
def ep1BodyUninitReturnUB : CapturedMir :=
  mkEp1Body "ep1::uninit_return_ub" [ep1U32Decl]
    [ { statements := [],
        terminator := { kind := .return_, span := "t0" },
        isCleanup := false } ]

/-- **End-to-End `translateBody`-Lowered `CapturedMir` Initial-State WP Witness (Positive + 2 Negative `↔` UBs)**:
1. Positive (`ep1BodyMultiStmtPositive`):
   - After the first 5 statements (`StorageLive 1`, `_1 = 42`, `PlaceMention _1`, `Nop`, `_0 = copy _1`),
     `activeLocal0Bits mid = some 42`;
   - Full 9-step `miriBodySafetyVC` / `miriRunFuelAction` completes cleanly with empty stack and zero errors;
2. Negative #1 (`ep1BodyDeadLocalReadUB`):
   - Executes `StorageDead 1` followed by `_0 = copy _1`, faulting with
     `.undefinedBehavior "read of dead local"`, AND via `↔` (`miriBodyExactWP_negation_refutation`)
     refutes `¬ AnnealExactWP ... (fun _ _ => True) (fun _ _ => False)`!
3. Negative #2 (`ep1BodyUninitReturnUB`):
   - Executes `Return` on uninitialized `_0`, faulting with
     `.undefinedBehavior "return with uninitialized or dead _0"`, AND via `↔` refutes safety! -/
theorem witness_translateBody_positive_multiStmt_and_negative_deadReturn_ub :
    let hooksPos := annealStepHooks ep1BodyMultiStmtPositive.localDecls emptyLayoutTable
    let initPos := initMiriStateForBody ep1BodyMultiStmtPositive emptyLayoutTable
    let hooksDead := annealStepHooks ep1BodyDeadLocalReadUB.localDecls emptyLayoutTable
    let initDead := initMiriStateForBody ep1BodyDeadLocalReadUB emptyLayoutTable
    let hooksUninit := annealStepHooks ep1BodyUninitReturnUB.localDecls emptyLayoutTable
    let initUninit := initMiriStateForBody ep1BodyUninitReturnUB emptyLayoutTable
    AnnealExactWP
      (ExactAction.seq (miriStepAction hooksPos ())
        (ExactAction.seq (miriStepAction hooksPos ())
          (ExactAction.seq (miriStepAction hooksPos ())
            (ExactAction.seq (miriStepAction hooksPos ())
              (miriStepAction hooksPos ())))))
      (fun more mid => more = true ∧ activeLocal0Bits mid = some 42)
      (fun _ _ => False) initPos ∧
    AnnealExactWP (miriRunFuelAction hooksPos () 9)
      (fun _ final => final.stack.frames = #[])
      (fun _ _ => False) initPos ∧
    AnnealExactWP (miriRunFuelAction hooksDead () 4)
      (fun _ _ => False)
      (fun err _ => err = .undefinedBehavior "read of dead local") initDead ∧
    ¬ AnnealExactWP (miriRunFuelAction hooksDead () 4)
      (fun _ _ => True) (fun _ _ => False) initDead ∧
    AnnealExactWP (miriRunFuelAction hooksUninit () 4)
      (fun _ _ => False)
      (fun err _ => err = .undefinedBehavior "return with uninitialized or dead _0") initUninit ∧
    ¬ AnnealExactWP (miriRunFuelAction hooksUninit () 4)
      (fun _ _ => True) (fun _ _ => False) initUninit := by
  refine ⟨⟨rfl, rfl⟩, rfl, rfl, ?_, rfl, ?_⟩
  · apply miriBodyExactWP_negation_refutation
    intro hFalse
    exact hFalse
  · apply miriBodyExactWP_negation_refutation
    intro hFalse
    exact hFalse

/-! ### §4.2. Real `V2026_06_01` `CapturedMir` Tree Borrows UB ↔ `Anneal.MiriTreeBorrowsV2026` ↔ Vendored `Miri.TreeBorrows` -/

section V2026CapturedMirTreeBorrowsUB

open Trusted.Rustc.V2026_06_01.MirSemantics
  (stepMirFn MachineState MirStepNode treeBorrowNodeAccess emptyMemory)

private def tbStmt (k : Trusted.Rustc.V2026_06_01.MirAst.StatementKind) :
    Trusted.Rustc.V2026_06_01.MirAst.Statement :=
  { kind := k, span := "ep1-tb" }
private def tbLoc (i : Nat) : Trusted.Rustc.V2026_06_01.MirAst.Place :=
  { local_ := i, projection := [] }
private def tbDeref (i : Nat) : Trusted.Rustc.V2026_06_01.MirAst.Place :=
  { local_ := i, projection := [.deref] }
private def tbU64 : Trusted.Rustc.V2026_06_01.MirAst.Ty := { kind := .uint .u64, layoutIdx := 0 }
private def tbDecl (ty : Trusted.Rustc.V2026_06_01.MirAst.Ty) : LocalDecl :=
  { mutability := .mut, ty := ty, debugName := none }
private def tbConstU64 (n : Nat) : Trusted.Rustc.V2026_06_01.MirAst.Operand :=
  .constant { ty := tbU64, val := .scalar (.int ⟨n, 8⟩) }
private def tbU64Layout : Trusted.Rustc.V2026_06_01.Layout.TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := .memory,
    fields := .primitive, variants := .single 0, isUninhabited := false }
private def tbBody (name : String) (decls : List LocalDecl)
    (stmts : List Trusted.Rustc.V2026_06_01.MirAst.Statement) : CapturedMir :=
  { defPath := name
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls := decls
    basicBlocks :=
      [{ statements := stmts, terminator := { kind := .return_, span := "ep1-tb" },
         isCleanup := false }]
    fnAbi := { args := [], ret := { layout := tbU64Layout, mode := .direct },
               conv := .rust, canUnwind := false }
    layouts := emptyLayoutTable
    allocations := [] }

/-- Satisfiable concrete initial `V2026_06_01` machine state: `_1 = 5_u64`, empty borrow table. -/
private def tbInit : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0,
               locals := [.uninit, .init (.scalar ⟨5, 8⟩), .uninit, .uninit] }
    memory := emptyMemory }

private def tbNext (b : CapturedMir) (s : MachineState) : MachineState :=
  match stepMirFn b s with
  | .step s' => s'
  | _ => s

/-- Real `V2026_06_01` `CapturedMir` (protected two-phase conflict UB):
```text
bb0: _2 = &mut _1;           // tag 1, ReservedFrz false
     Retag([fn entry] _2);   // tag 2, PROTECTED ReservedFrz false (protector 1)
     _3 = &_1;               // tag 3, Frozen
     _0 = copy (*_3);        // foreign read for tag 2: conflicted latch set
     (*_2) = const 9;        // child write through protected conflicted tag 2: UB
     return
``` -/
def ep1BodyProtectedConflictUB : CapturedMir :=
  tbBody "ep1::protected_conflict_ub"
    [tbDecl tbU64, tbDecl tbU64,
     tbDecl { kind := .ref .mut (.uint .u64), layoutIdx := 0 },
     tbDecl { kind := .ref .not (.uint .u64), layoutIdx := 0 }]
    [tbStmt (.assign (tbLoc 2) (.ref (.mut false) (tbLoc 1))),
     tbStmt (.retag .fnEntry (tbLoc 2)),
     tbStmt (.assign (tbLoc 3) (.ref .shared (tbLoc 1))),
     tbStmt (.assign (tbLoc 0) (.use (.copy (tbDeref 3)))),
     tbStmt (.assign (tbDeref 2) (.use (tbConstU64 9)))]

/-- Real `V2026_06_01` `CapturedMir` (frozen local write UB through a `&T`-derived `*mut T`):
```text
bb0: _2 = &_1;               // tag 1, Frozen
     _3 = &raw mut (*_2);    // raw pointer inherits tag 1
     (*_3) = const 9;        // local write through Frozen tag 1: UB
     return
``` -/
def ep1BodyFrozenWriteUB : CapturedMir :=
  tbBody "ep1::frozen_write_ub"
    [tbDecl tbU64, tbDecl tbU64,
     tbDecl { kind := .ref .not (.uint .u64), layoutIdx := 0 },
     tbDecl { kind := .rawPtr .mut (.uint .u64), layoutIdx := 0 }]
    [tbStmt (.assign (tbLoc 2) (.ref .shared (tbLoc 1))),
     tbStmt (.assign (tbLoc 3) (.rawPtr .mut (tbDeref 2))),
     tbStmt (.assign (tbDeref 3) (.use (tbConstU64 9)))]

/-- **End-to-end Tree Borrows UB witnesses on REAL `V2026_06_01` `CapturedMir` bodies, with exact
3-way cell agreement (`V2026_06_01.MirSemantics` ↔ `Anneal.MiriTreeBorrowsV2026` ↔ vendored
`Miri.TreeBorrows`)**. Every faulting state is REACHED by real `stepMirFn` steps from the concrete,
satisfiable initial state `tbInit` (no hypotheses):
1. Protected two-phase conflict: four real steps build borrow table
   `[3 ↦ Frozen, 2 ↦ ReservedFrz true (protector 1), 1 ↦ ReservedFrz false]` with protector `1`
   active, then the child write through tag `2` faults with `.fail .ub`.
2. Frozen local write: two real steps build `[1 ↦ Frozen]`, then the write through the
   `&T`-derived `*mut T` (tag `1`) faults with `.fail .ub`.
3. For both faulting cells, unmodified V2026 `treeBorrowNodeAccess` yields `.ub`,
   `Anneal.MiriTreeBorrowsV2026.miriPerformLocAccess` faults with `.childAccessForbidden`, and
   unmodified vendored `Miri.TreeBorrows.performAccess` yields `.UndefinedBehavior`. -/
theorem witness_v2026_capturedMir_tree_borrows_ub_triangle :
    (let b := ep1BodyProtectedConflictUB
     let s1 := tbNext b tbInit
     let s2 := tbNext b s1
     let s3 := tbNext b s2
     let s4 := tbNext b s3
     stepMirFn b tbInit = .step s1 ∧ stepMirFn b s1 = .step s2 ∧
     stepMirFn b s2 = .step s3 ∧ stepMirFn b s3 = .step s4 ∧
     s4.memory.activeProtectors = [1] ∧
     s4.memory.borrows.map (fun e => (e.tag, e.perm, e.protector)) =
       [(3, .frozen, none), (2, .reservedFrz true, some 1), (1, .reservedFrz false, none)] ∧
     stepMirFn b s4 = .fail .ub) ∧
    (let b := ep1BodyFrozenWriteUB
     let s1 := tbNext b tbInit
     let s2 := tbNext b s1
     stepMirFn b tbInit = .step s1 ∧ stepMirFn b s1 = .step s2 ∧
     s2.memory.borrows.map (fun e => (e.tag, e.perm, e.protector)) = [(1, .frozen, none)] ∧
     stepMirFn b s2 = .fail .ub) ∧
    treeBorrowNodeAccess .write .localAccess (.reservedFrz true) true = .ub ∧
    miriPerformLocAccess 2 ⟨v2026PermToMiri (.reservedFrz true), true, .none⟩ .write
        .localAccess true =
      .err ⟨.reservedFrz true, true, .none⟩ (.childAccessForbidden 2 (.reservedFrz true)) ∧
    Miri.TreeBorrows.performAccess .Write .LocalAccess (.ReservedFrz true) true =
      .UndefinedBehavior ∧
    treeBorrowNodeAccess .write .localAccess .frozen false = .ub ∧
    miriPerformLocAccess 1 ⟨v2026PermToMiri .frozen, true, .none⟩ .write .localAccess false =
      .err ⟨.frozen, true, .none⟩ (.childAccessForbidden 1 .frozen) ∧
    Miri.TreeBorrows.performAccess .Write .LocalAccess .Frozen false = .UndefinedBehavior :=
  ⟨⟨by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl,
    by kernel_rfl⟩,
   ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl⟩

end V2026CapturedMirTreeBorrowsUB

/-! ### §4.3. Tree-Borrows-Enabled Miri-Side (`borrowTracker := some`) `Step.step` + `translateBody` Execution & `↔` UB Refutation -/

section TbEnabledTranslateBodyMiriExecution

/-- Total, kernel-reducible diagnostic label for `BorrowTree.BorrowTreeAccessStatus` (avoids
`Std.Format.pretty` partial functions during kernel-checked proofs). -/
def formatTbAccessStatus : BorrowTree.BorrowTreeAccessStatus → String
  | .Completed => "Completed"
  | .MissingTag _ => "MissingTag"
  | .RangeMapFailure _ => "RangeMapFailure"
  | .LocationMapFailure _ _ => "LocationMapFailure"
  | .AccessFailure _ (.TransitionError _ (.ProtectedDisabled .Frozen)) =>
      "Tree Borrows UB: ProtectedDisabled Frozen"
  | .AccessFailure _ (.TransitionError _ (.ProtectedDisabled .Unique)) =>
      "Tree Borrows UB: ProtectedDisabled Unique"
  | .AccessFailure _ (.TransitionError _ (.ChildAccessForbidden .Frozen)) =>
      "Tree Borrows UB: ChildAccessForbidden Frozen"
  | .AccessFailure _ (.TransitionError _ (.ChildAccessForbidden _)) =>
      "Tree Borrows UB: ChildAccessForbidden"
  | .AccessFailure _ (.TransitionError _ (.ProtectedDisabled _)) =>
      "Tree Borrows UB: ProtectedDisabled"
  | .AccessFailure _ (.TransitionError _ .ProtectedDealloc) =>
      "Tree Borrows UB: ProtectedDealloc"
  | .AccessFailure _ _ => "Tree Borrows UB: AccessFailure"
  | .WildcardFailure _ _ => "Tree Borrows UB: WildcardFailure"
  | .MultipleRoots _ => "Tree Borrows UB: MultipleRoots"
  | .CacheFailure _ _ => "Tree Borrows UB: CacheFailure"

/-- Run unmodified vendored `Miri.TreeBorrows.BorrowTree.performBorrowAccessRange` on the live
`Allocation AnnealProv (Option BorrowTree)` targeted by `mplace` whenever `st.machine.borrowTracker`
is active (`some bs`), committing the updated `BorrowTree` back into `st.machine.memory.live` on
BOTH `.Completed` and Tree Borrows error (mirroring `MachineMemoryHooks.commitTreeAccess`)! -/
def annealTbCheckMemAccess (mplace : Miri.Interpreter.MemPlace AnnealProv)
    (size : Size) (kind : AccessKind) :
    Miri.Interpreter.RvalueM AnnealStepState Unit := do
  let st ← get
  let some bs := st.machine.borrowTracker | return ()
  -- Resolve through the project's CHECKED `annealResolvePtr` (fail closed on provenance-free,
  -- wildcard, base-less, or below-base pointers instead of wrapping `UInt64` subtraction).
  let some resolved := (annealResolvePtr st.machine mplace.ptr (Int.ofNat size.bytes.toNat)).toOption
    | throw (.undefinedBehavior "Tree Borrows access through unresolvable pointer")
  match st.machine.memory.live.find? (fun row => row.1 == resolved.allocId) with
  | none => throw (.undefinedBehavior "Tree Borrows access on dangling allocation")
  | some (_, ⟨_, alloc⟩) =>
    match alloc.extra with
    -- With the borrow tracker active, EVERY live allocation must carry a `BorrowTree` (as in
    -- vendored Miri, whose allocation extra is non-optional): fail closed, never skip the check.
    | none => throw (.invalidProgram "Tree Borrows enabled but allocation has no borrow tree")
    | some tree =>
      let allocId := resolved.allocId
      let res := tree.performBorrowAccessRange (.concrete resolved.extra) resolved.offset size kind
        bs.global.protectedTags .VisitChildrenOfAccessed
      let alloc' := alloc.setExtra (some res.tree)
      match st.machine.memory.setLiveAllocation allocId alloc' with
      | .error _ => throw (.undefinedBehavior "Tree Borrows allocation update failed")
      | .ok mem' =>
        set { st with machine := { st.machine with memory := mem' } }
        match res.status with
        | .Completed => return ()
        | errStatus =>
          throw (.undefinedBehavior (formatTbAccessStatus errStatus))

/-- Tree-Borrows-enforcing `StepHooks` extending unmodified `annealStepHooks`: before any dereference
memory write (`*p = rvalue`) or dereference memory read (`_d = copy/move (*p)`), enforces real
vendored `Miri.TreeBorrows.BorrowTree.performBorrowAccessRange` against
`state.machine.borrowTracker.global.protectedTags` and live allocation `BorrowTree`s, then executes
unmodified `annealStepHooks.assign`!

**Scope / honesty note.** `Miri.Interpreter.Step.step` itself is unmodified; this is an
*instantiation* of its `StepHooks` parameter. The pre-existing correspondence instantiation
(`annealMemoryCopyHooks`, `Correspondence/Translate.lean`) deliberately tracks NO borrow state, so
these hooks are Anneal-authored instrumentation, NOT vendored Miri's own TB-enabled machine
(`PlaceMachine.memoryAccess` / `MachineMemoryHooks`). Consequently:
- the instrumentation only intercepts `Use (Copy/Move *p)` reads and `*p = _` writes, so a
  successful run under `annealTbStepHooks` is NOT a general Tree Borrows soundness claim;
- its per-access TB verdicts on the §4.3 witness accesses are cross-validated against unmodified
  vendored `MachineMemoryHooks.beforeMemoryWrite` / `beforeMemoryRead` by
  `witness_tb_hooks_agree_vendored_machineMemoryHooks`. -/
def annealTbStepHooks (localDecls : List LocalDecl := .nil)
    (layouts : AnnealLayoutTable := emptyLayoutTable) :
    StepHooks AnnealProv LocalLayout Unit AnnealMachine Unit (RuntimePlace AnnealProv) :=
  { annealStepHooks localDecls layouts with
    assign := fun choice place rvalue state =>
      Miri.Interpreter.runRvalue (do
        match rvalue with
        | .Use (.Copy srcPlace) _ | .Use (.Move srcPlace) _ =>
          if !srcPlace.projection.isEmpty then
            let srcRt ← annealEvalPlace localDecls layouts srcPlace
            match srcRt.ref with
            | .memory mp => annealTbCheckMemAccess mp srcRt.layout.layout.size .Read
            | _ => pure ()
        | _ => pure ()
        if !place.projection.isEmpty then
          let dstRt ← annealEvalPlace localDecls layouts place
          match dstRt.ref with
          | .memory mp => annealTbCheckMemAccess mp dstRt.layout.layout.size .Write
          | _ => pure ()
        Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks localDecls layouts) choice rvalue place)
        state }

private def ep1MutPtrU32Ty : Trusted.Rustc.V2026_06_01.MirAst.Ty := ⟨.rawPtr .mut (.uint .u32), 0⟩
private def ep1Ptr1Decl : LocalDecl := ⟨.mut, ep1MutPtrU32Ty, some "p_write"⟩
private def ep1Ptr2Decl : LocalDecl := ⟨.mut, ep1MutPtrU32Ty, some "p_read"⟩

/-- Real `V2026_06_01` `CapturedMir` body lowered through `LeanMiriSpec.Correspondence.translateBody`:
`bb0: (*_1) = const 99u32; _0 = copy (*_2); return`. -/
def ep1BodyTbDerefWriteAndRead : CapturedMir :=
  mkEp1Body "ep1::tb_deref_write_and_read" [ep1U32Decl, ep1Ptr1Decl, ep1Ptr2Decl]
    [ { statements :=
          [ { kind := .assign ⟨1, [.deref]⟩ (.use (.constant ⟨ep1U32Ty, .scalar (.int ⟨99, 4⟩)⟩)),
              span := "s0" },
            { kind := .assign ⟨0, []⟩ (.use (.copy ⟨2, [.deref]⟩)),
              span := "s1" } ],
        terminator := { kind := .return_, span := "t0" },
        isCleanup := false } ]

private def ep1TbBaseAddr : UInt64 := 0x1000

private def ep1PtrScalar (tag : BorTag) (off : UInt64) : Miri.Memory.Scalar AnnealProv :=
  Miri.Memory.Scalar.fromPointer annealTargetDataLayout
    ⟨Size.ofBytes (ep1TbBaseAddr + off), Provenance.concrete ep1AllocId tag⟩

private noncomputable def ep1InitTbMiriState (writeTag : BorTag) (writeOff : UInt64) :
    AnnealStepState :=
  let base := initMiriStateForBody ep1BodyTbDerefWriteAndRead emptyLayoutTable
  let allocWithTree : Allocation AnnealProv (Option BorrowTree) :=
    ep1BaseAlloc16.withExtra (some ep1DisjointTwoChildTree)
  let mem : AnnealMemory :=
    { (MemoryState.empty : AnnealMemory) with
      nextAllocId := 2
      live := #[(ep1AllocId, { kind := .stack, allocation := allocWithTree })] }
  let addrs : AllocAddresses.GlobalAddressState :=
    { provenanceMode := .default
      addressMode := .managed
      generation := none
      baseAddr := #[⟨ep1AllocId, ep1TbBaseAddr⟩] }
  let bt : MachineHooks.BorrowState :=
    { global := { GlobalState.new with protectedTags := ep1Prot23 }
      retagMode := .Default }
  let pLay := some (translateTy ep1MutPtrU32Ty emptyLayoutTable)
  let u32Lay := some (translateTy ep1U32Ty emptyLayoutTable)
  let locals : Array (LocalState AnnealProv LocalLayout) :=
    #[ { value := .live (.immediate .uninit), layout := u32Lay },
       { value := .live (.immediate (.scalar (ep1PtrScalar writeTag writeOff))), layout := pLay },
       { value := .live (.immediate (.scalar (ep1PtrScalar ep1Tag2 0))), layout := pLay } ]
  let frame' : Frame AnnealProv LocalLayout Unit :=
    match base.stack.frames[0]? with
    | some fr => { fr with locals := locals }
    | none =>
      { body := translateBody ep1BodyTbDerefWriteAndRead
        bodyIdentity := BodyIdentity.ofCanonicalIndex 0
        functionInstance := ⟨.Item 0, #[]⟩
        extra := ()
        returnContinuation := .stop false
        returnPlace := .frameLocal 0 0 none (translateTy ep1U32Ty emptyLayoutTable)
          (LocalsIdentity.ofAllocationToken 0)
        localsIdentity := LocalsIdentity.ofAllocationToken 0
        locals := locals
        vaList := #[]
        trackCallerArg := none
        location := .mir ⟨0, 0⟩ }
  { stack := { frames := #[frame'] }
    machine := { memory := mem, addresses := addrs, borrowTracker := some bt } }

private noncomputable def annealTbCheckMemAccessLMU (mplace : Miri.Interpreter.MemPlace AnnealProv)
    (size : Size) (kind : AccessKind) :
    Miri.Interpreter.RvalueM AnnealStepState Unit := do
  let st ← get
  let some bs := st.machine.borrowTracker | return ()
  -- Resolve through the project's CHECKED `annealResolvePtr` (fail closed on provenance-free,
  -- wildcard, base-less, or below-base pointers instead of wrapping `UInt64` subtraction).
  let some resolved := (annealResolvePtr st.machine mplace.ptr (Int.ofNat size.bytes.toNat)).toOption
    | throw (.undefinedBehavior "Tree Borrows access through unresolvable pointer")
  match st.machine.memory.live.find? (fun row => row.1 == resolved.allocId) with
  | none => throw (.undefinedBehavior "Tree Borrows access on dangling allocation")
  | some (_, ⟨_, alloc⟩) =>
    match alloc.extra with
    -- With the borrow tracker active, EVERY live allocation must carry a `BorrowTree` (as in
    -- vendored Miri, whose allocation extra is non-optional): fail closed, never skip the check.
    | none => throw (.invalidProgram "Tree Borrows enabled but allocation has no borrow tree")
    | some tree =>
      let allocId := resolved.allocId
      let res := performBorrowAccessRangeLMU tree (.concrete resolved.extra) resolved.offset size kind
        bs.global.protectedTags .VisitChildrenOfAccessed
      let alloc' := alloc.setExtra (some res.tree)
      match st.machine.memory.setLiveAllocation allocId alloc' with
      | .error _ => throw (.undefinedBehavior "Tree Borrows allocation update failed")
      | .ok mem' =>
        set { st with machine := { st.machine with memory := mem' } }
        match res.status with
        | .Completed => return ()
        | errStatus =>
          throw (.undefinedBehavior (formatTbAccessStatus errStatus))

private noncomputable def annealTbStepHooksLMU (localDecls : List LocalDecl := .nil)
    (layouts : AnnealLayoutTable := emptyLayoutTable) :
    StepHooks AnnealProv LocalLayout Unit AnnealMachine Unit (RuntimePlace AnnealProv) :=
  { annealStepHooks localDecls layouts with
    assign := fun choice place rvalue state =>
      Miri.Interpreter.runRvalue (do
        match rvalue with
        | .Use (.Copy srcPlace) _ | .Use (.Move srcPlace) _ =>
          if !srcPlace.projection.isEmpty then
            let srcRt ← annealEvalPlace localDecls layouts srcPlace
            match srcRt.ref with
            | .memory mp => annealTbCheckMemAccessLMU mp srcRt.layout.layout.size .Read
            | _ => pure ()
        | _ => pure ()
        if !place.projection.isEmpty then
          let dstRt ← annealEvalPlace localDecls layouts place
          match dstRt.ref with
          | .memory mp => annealTbCheckMemAccessLMU mp dstRt.layout.layout.size .Write
          | _ => pure ()
        Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks localDecls layouts) choice rvalue place)
        state }

private theorem annealTbCheckMemAccess_eq_LMU :
    @annealTbCheckMemAccess = @annealTbCheckMemAccessLMU := by
  funext mp sz kind
  unfold annealTbCheckMemAccess annealTbCheckMemAccessLMU
  rw [performBorrowAccessRangeLMU.eq_src]

private theorem annealTbStepHooks_eq_LMU (localDecls : List LocalDecl) (layouts : AnnealLayoutTable) :
    annealTbStepHooks localDecls layouts = annealTbStepHooksLMU localDecls layouts := by
  unfold annealTbStepHooks annealTbStepHooksLMU
  rw [annealTbCheckMemAccess_eq_LMU]

/-- **End-to-End Tree-Borrows-Enabled (`borrowTracker := some`) Miri-Side `translateBody` +
`Step.step` + `AnnealExactWP` Witness (Positive + 2 Bidirectional `↔` Negative UB Refutations)**:
Runs real `LeanMiriSpec.Correspondence.translateBody ep1BodyTbDerefWriteAndRead` through unmodified
`Miri.Interpreter.Step.step` (`miriRunFuelAction`) with live `Allocation AnnealProv (Option BorrowTree)`
and `borrowTracker := some { protectedTags := ep1Prot23 }`:
1. **Positive**: `_1` carries `tag 3` (`Unique` on `[8..16)`) at offset `8` and `_2` carries
   `tag 2` (`Frozen` on `[0..8)`) at offset `0`. Executing `(*_1) = 99u32; _0 = copy (*_2); return`:
   - passes real `BorrowTree.performBorrowAccessRange` for BOTH the write and the read,
   - writes `99u32` at `[8..12)` while preserving `42u32` at `[0..4)` (`activeLocal0Bits mid = some 42`),
   - terminates cleanly with empty stack (`final.stack.frames = #[]`)!
2. **Negative #1 (Protected Foreign Write UB + `↔` Refutation)**: `_1` carries root `tag 1` at
   offset `0` — step 1 faults in real `BorrowTree.performBorrowAccessRange` with
   `.ProtectedDisabled .Frozen` AND via `↔` refutes `¬ AnnealExactWP ... (fun _ _ => True) (fun _ _ => False)`!
3. **Negative #2 (Frozen Local Write UB + `↔` Refutation)**: `_1` carries `tag 2` (`Frozen`) at
   offset `0` — step 1 faults in real `BorrowTree.performBorrowAccessRange` with
   `.ChildAccessForbidden .Frozen` AND via `↔` refutes `¬ AnnealExactWP ... (fun _ _ => True) (fun _ _ => False)`! -/
theorem witness_tb_enabled_translateBody_positive_and_negative_ub_refutations :
    let hooks := annealTbStepHooks ep1BodyTbDerefWriteAndRead.localDecls emptyLayoutTable
    let initOk := ep1InitTbMiriState ep1Tag3 8
    let initProtUB := ep1InitTbMiriState ep1Tag1 0
    let initFrozUB := ep1InitTbMiriState ep1Tag2 0
    AnnealExactWP
      (ExactAction.seq (miriStepAction hooks ()) (miriStepAction hooks ()))
      (fun more mid => more = true ∧ activeLocal0Bits mid = some 42)
      (fun _ _ => False) initOk ∧
    AnnealExactWP (miriRunFuelAction hooks () 6)
      (fun _ final => final.stack.frames = #[])
      (fun _ _ => False) initOk ∧
    AnnealExactWP (miriRunFuelAction hooks () 4)
      (fun _ _ => False)
      (fun err _ => err = .undefinedBehavior "Tree Borrows UB: ProtectedDisabled Frozen")
      initProtUB ∧
    ¬ AnnealExactWP (miriRunFuelAction hooks () 4)
      (fun _ _ => True) (fun _ _ => False) initProtUB ∧
    AnnealExactWP (miriRunFuelAction hooks () 4)
      (fun _ _ => False)
      (fun err _ => err = .undefinedBehavior "Tree Borrows UB: ChildAccessForbidden Frozen")
      initFrozUB ∧
    ¬ AnnealExactWP (miriRunFuelAction hooks () 4)
      (fun _ _ => True) (fun _ _ => False) initFrozUB := by
  let hooksLMU := annealTbStepHooksLMU ep1BodyTbDerefWriteAndRead.localDecls emptyLayoutTable
  let initOk := ep1InitTbMiriState ep1Tag3 8
  let initProtUB := ep1InitTbMiriState ep1Tag1 0
  let initFrozUB := ep1InitTbMiriState ep1Tag2 0
  have hHooksEq :
      annealTbStepHooks ep1BodyTbDerefWriteAndRead.localDecls emptyLayoutTable = hooksLMU :=
    annealTbStepHooks_eq_LMU ep1BodyTbDerefWriteAndRead.localDecls emptyLayoutTable
  have hStep2 :
      (match ExactAction.seq (miriStepAction hooksLMU ()) (miriStepAction hooksLMU ()) initOk with
       | .ok more mid => more == true && activeLocal0Bits mid == some 42
       | .error _ _ => false) = true := by kernel_rfl
  have hOkRun :
      (match miriRunFuelAction hooksLMU () 6 initOk with
       | .ok () final => final.stack.frames.isEmpty
       | .error _ _ => false) = true := by kernel_rfl
  have hProtRun :
      (match miriRunFuelAction hooksLMU () 4 initProtUB with
       | .ok _ _ => false
       | .error err _ => err == .undefinedBehavior "Tree Borrows UB: ProtectedDisabled Frozen") =
        true := by kernel_rfl
  have hFrozRun :
      (match miriRunFuelAction hooksLMU () 4 initFrozUB with
       | .ok _ _ => false
       | .error err _ => err == .undefinedBehavior "Tree Borrows UB: ChildAccessForbidden Frozen") =
        true := by kernel_rfl
  dsimp only
  rw [hHooksEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold AnnealExactWP
    cases hR : ExactAction.seq (miriStepAction hooksLMU ()) (miriStepAction hooksLMU ()) initOk with
    | error _ _ => rw [hR] at hStep2; cases hStep2
    | ok more mid =>
      rw [hR] at hStep2
      simp only [Bool.and_eq_true, beq_iff_eq] at hStep2
      exact hStep2
  · unfold AnnealExactWP
    cases hR : miriRunFuelAction hooksLMU () 6 initOk with
    | error _ _ => rw [hR] at hOkRun; cases hOkRun
    | ok u final =>
      rw [hR] at hOkRun
      exact Array.isEmpty_iff.mp hOkRun
  · unfold AnnealExactWP
    cases hR : miriRunFuelAction hooksLMU () 4 initProtUB with
    | ok _ _ => rw [hR] at hProtRun; cases hProtRun
    | error err _ =>
      rw [hR] at hProtRun
      exact beq_iff_eq.mp hProtRun
  · intro hSafe
    unfold AnnealExactWP at hSafe
    cases hR : miriRunFuelAction hooksLMU () 4 initProtUB with
    | ok _ _ => rw [hR] at hProtRun; cases hProtRun
    | error _ _ => rw [hR] at hSafe; exact hSafe
  · unfold AnnealExactWP
    cases hR : miriRunFuelAction hooksLMU () 4 initFrozUB with
    | ok _ _ => rw [hR] at hFrozRun; cases hFrozRun
    | error err _ =>
      rw [hR] at hFrozRun
      exact beq_iff_eq.mp hFrozRun
  · intro hSafe
    unfold AnnealExactWP at hSafe
    cases hR : miriRunFuelAction hooksLMU () 4 initFrozUB with
    | ok _ _ => rw [hR] at hFrozRun; cases hFrozRun
    | error _ _ => rw [hR] at hSafe; exact hSafe

/-- Trivial (single-threaded, no data race, no sync objects) vendored `MachineMemoryHooks.Hooks`
with the SAME protector set `ep1Prot23` as the §4.3 borrow tracker. -/
private def ep1TrivialMMHooks : MachineMemoryHooks.Hooks Unit Unit Unit :=
  { protectedTags := ep1Prot23
    emitDiagnostic := fun s _ _ => s
    dataRaceRead := fun s _ _ _ => ⟨s, .ok ()⟩
    dataRaceWrite := fun s _ _ _ => ⟨s, .ok ()⟩
    dataRaceDeallocate := fun s _ _ _ _ => ⟨s, .ok ()⟩
    syncOnAccess := fun s _ _ => ⟨s, .ok ()⟩
    deleteOnWrite := fun _ => false
    recordDeallocatedSpan := fun s _ => s
    freeAllocId := fun s _ _ _ _ => s }

private def ep1TrivialMMCtx : MachineMemoryHooks.Context Unit Unit :=
  { state := (), syncObjects := .empty }

private noncomputable def ep1VendoredTbAlloc : Allocation Provenance BorrowTree :=
  ep1BaseAlloc16.withExtra ep1DisjointTwoChildTree

private def ep1VendoredTbPtr (tag : BorTag) (off : UInt64) : Pointer (Option Provenance) :=
  ⟨Size.ofBytes (0x1000 + off), some (.concrete ep1AllocId tag)⟩

/-- Real vendored `MachineMemoryHooks` verdict for a 4-byte access through `tag` at `off`, reduced
to `tbAccessPre` via `miriBeforeMemoryWriteExactWP_iff` / `miriBeforeMemoryReadExactWP_iff`. -/
private theorem ep1VendoredSetLive (t : BorrowTree) :
    ep1ObsState.memory.setLiveAllocation ep1AllocId (ep1VendoredTbAlloc.setExtra t) =
      .ok { ep1ObsState.memory with
            live := ((ep1ObsState.memory.live.filter fun row => row.1 != ep1AllocId).push
              (ep1AllocId, { kind := .stack, allocation := ep1VendoredTbAlloc.setExtra t })) } :=
  MemoryState.setLiveAllocation_of_find ep1ObsState.memory ep1AllocId
    { kind := .stack, allocation := ep1VendoredTbAlloc } _ rfl

/-- Helper looking up a live allocation directly in a `MemoryState`. -/
def lookupLiveAllocMem {P E K : Type} (mem : MemoryState P E K)
    (allocId : Miri.Memory.AllocId) : Option (Allocation P E) :=
  (mem.live.find? (fun entry => entry.1 == allocId)).map (fun entry => entry.2.allocation)

/-- **Cross-validation of the §4.3 instrumentation against UNMODIFIED vendored
`Miri.TreeBorrows.MachineMemoryHooks` (`witness_tb_hooks_agree_vendored_machineMemoryHooks`)**:
on the same allocation (`ep1BaseAlloc16` + `ep1DisjointTwoChildTree`), the same protector set
(`ep1Prot23`), and the same 4-byte accesses that `witness_tb_enabled_translateBody_*` performs,
vendored `beforeMemoryWrite` / `beforeMemoryRead` (pinned `MiriMachine::before_memory_{write,read}`)
return EXACTLY the verdicts `annealTbStepHooks` reports — WITH exact error messages, committed
post-error memory states, bidirectional `↔` safety refutations, AND sequential post-write chaining:
1. write through root `tag 1` at `[0, 4)`: vendored hook FAULTS with exact error string
   `s!"Tree Borrows write failed: {reprStr ...ProtectedDisabled .Frozen}"`, retains the committed
   updated `BorrowTree` in `mem'`, AND refutes `¬ AnnealExactWP ... (fun _ _ => True) (fun _ _ => False)`;
2. write through `tag 2` (`Frozen`) at `[0, 4)`: vendored hook FAULTS with exact error string
   `s!"Tree Borrows write failed: {reprStr ...ChildAccessForbidden .Frozen}"`, retains committed
   `mem'`, AND refutes `¬ AnnealExactWP ... (fun _ _ => True) (fun _ _ => False)`;
3. **sequential positive composition**: write through `tag 3` (`Unique`) at `[8, 12)` commits
   post-write `mem₁` / `alloc₁`, AND THEN read through `tag 2` (`Frozen`) at `[0, 4)` executes on
   THAT committed post-write `(mem₁, alloc₁)` and succeeds! -/
theorem witness_tb_hooks_agree_vendored_machineMemoryHooks :
    let stW1 := BorrowTree.BorrowTreeAccessStatus.AccessFailure ⟨0, 4⟩
      (.TransitionError 1 (.ProtectedDisabled .Frozen))
    let stW2 := BorrowTree.BorrowTreeAccessStatus.AccessFailure ⟨0, 4⟩
      (.TransitionError 1 (.ChildAccessForbidden .Frozen))
    let tW1 := (ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag1) Size.ZERO
      (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).tree
    let tW2 := (ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag2) Size.ZERO
      (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).tree
    let tW3 := (ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag3)
      (Size.ofBytes 8) (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).tree
    let allocAfterW3 : Allocation Provenance BorrowTree := ep1VendoredTbAlloc.setExtra tW3
    let ctxAfterW3 : MachineMemoryHooks.Context Unit Unit :=
      { ep1TrivialMMCtx with syncObjects := ep1TrivialMMCtx.syncObjects.set ep1AllocId .empty }
    AnnealExactWP
      (miriBeforeMemoryWriteAction ep1TrivialMMHooks ep1VendoredTbAlloc (ep1VendoredTbPtr ep1Tag1 0)
        ep1AllocId (.concrete ep1Tag1) (allocRange Size.ZERO (Size.ofBytes 4)))
      (fun _ _ => False)
      (fun msg pair =>
        msg = s!"Tree Borrows write failed: {reprStr stW1}" ∧
        lookupLiveAllocMem pair.1 ep1AllocId = some (ep1VendoredTbAlloc.setExtra tW1))
      (ep1ObsState.memory, ep1TrivialMMCtx) ∧
    ¬ AnnealExactWP
      (miriBeforeMemoryWriteAction ep1TrivialMMHooks ep1VendoredTbAlloc (ep1VendoredTbPtr ep1Tag1 0)
        ep1AllocId (.concrete ep1Tag1) (allocRange Size.ZERO (Size.ofBytes 4)))
      (fun _ _ => True) (fun _ _ => False) (ep1ObsState.memory, ep1TrivialMMCtx) ∧
    formatTbAccessStatus
      (ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag1) Size.ZERO
        (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).status =
      "Tree Borrows UB: ProtectedDisabled Frozen" ∧
    AnnealExactWP
      (miriBeforeMemoryWriteAction ep1TrivialMMHooks ep1VendoredTbAlloc (ep1VendoredTbPtr ep1Tag2 0)
        ep1AllocId (.concrete ep1Tag2) (allocRange Size.ZERO (Size.ofBytes 4)))
      (fun _ _ => False)
      (fun msg pair =>
        msg = s!"Tree Borrows write failed: {reprStr stW2}" ∧
        lookupLiveAllocMem pair.1 ep1AllocId = some (ep1VendoredTbAlloc.setExtra tW2))
      (ep1ObsState.memory, ep1TrivialMMCtx) ∧
    ¬ AnnealExactWP
      (miriBeforeMemoryWriteAction ep1TrivialMMHooks ep1VendoredTbAlloc (ep1VendoredTbPtr ep1Tag2 0)
        ep1AllocId (.concrete ep1Tag2) (allocRange Size.ZERO (Size.ofBytes 4)))
      (fun _ _ => True) (fun _ _ => False) (ep1ObsState.memory, ep1TrivialMMCtx) ∧
    formatTbAccessStatus
      (ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag2) Size.ZERO
        (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).status =
      "Tree Borrows UB: ChildAccessForbidden Frozen" ∧
    AnnealExactWP
      (ExactAction.seq
        (miriBeforeMemoryWriteAction ep1TrivialMMHooks ep1VendoredTbAlloc (ep1VendoredTbPtr ep1Tag3 8)
          ep1AllocId (.concrete ep1Tag3) (allocRange (Size.ofBytes 8) (Size.ofBytes 4)))
        (miriBeforeMemoryReadAction ep1TrivialMMHooks allocAfterW3 (ep1VendoredTbPtr ep1Tag2 0)
          ep1AllocId (.concrete ep1Tag2) (allocRange Size.ZERO (Size.ofBytes 4))))
      (fun _ pair =>
        pair.2 = ctxAfterW3 ∧
        lookupLiveAllocMem pair.1 ep1AllocId =
          some (allocAfterW3.setExtra
            (tW3.performBorrowAccessRange (.concrete ep1Tag2) Size.ZERO (Size.ofBytes 4) .Read
              ep1Prot23 .VisitChildrenOfAccessed).tree))
      (fun _ _ => False) (ep1ObsState.memory, ep1TrivialMMCtx) := by
  have hW1 :
      (performBorrowAccessRangeLMU ep1DisjointTwoChildTree (.concrete ep1Tag1) Size.ZERO
        (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).status =
      .AccessFailure ⟨0, 4⟩ (.TransitionError 1 (.ProtectedDisabled .Frozen)) := by kernel_rfl
  have hW2 :
      (performBorrowAccessRangeLMU ep1DisjointTwoChildTree (.concrete ep1Tag2) Size.ZERO
        (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).status =
      .AccessFailure ⟨0, 4⟩ (.TransitionError 1 (.ChildAccessForbidden .Frozen)) := by kernel_rfl
  have hW3 :
      (performBorrowAccessRangeLMU ep1DisjointTwoChildTree (.concrete ep1Tag3) (Size.ofBytes 8)
        (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).status = .Completed := by
    kernel_rfl
  have hR2AfterW3 :
      (performBorrowAccessRangeLMU
        (performBorrowAccessRangeLMU ep1DisjointTwoChildTree (.concrete ep1Tag3) (Size.ofBytes 8)
          (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).tree
        (.concrete ep1Tag2) Size.ZERO (Size.ofBytes 4) .Read ep1Prot23
        .VisitChildrenOfAccessed).status = .Completed := by
    kernel_rfl
  dsimp only
  have hFindPost :
      ∀ (t : BorrowTree),
        lookupLiveAllocMem
          ({ ep1ObsState.memory with
             live := (ep1ObsState.memory.live.filter fun row => row.1 != ep1AllocId).push
               (ep1AllocId, { kind := .stack, allocation := ep1VendoredTbAlloc.setExtra t }) } :
            MemoryState Provenance BorrowTree Unit)
          ep1AllocId = some (ep1VendoredTbAlloc.setExtra t) := by
    intro t
    unfold lookupLiveAllocMem
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [miriBeforeMemoryWriteExactWP_iff ep1TrivialMMHooks ep1VendoredTbAlloc _ ep1AllocId _ _
      (Size.ofBytes 4) _ _ ep1TrivialMMCtx _ _ rfl rfl rfl (by kernel_rfl) (ep1VendoredSetLive _)]
    unfold tbAccessPre
    dsimp only [ep1VendoredTbAlloc, Allocation.withExtra, allocRange, ep1TrivialMMHooks]
    rw [performBorrowAccessRangeLMU.eq_src]
    generalize hRes : performBorrowAccessRangeLMU ep1DisjointTwoChildTree (.concrete ep1Tag1)
        Size.ZERO (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed = res
    rw [hRes] at hW1
    rw [hW1]
    exact ⟨rfl, hFindPost _⟩
  · rw [miriBeforeMemoryWriteExactWP_iff ep1TrivialMMHooks ep1VendoredTbAlloc _ ep1AllocId _ _
      (Size.ofBytes 4) _ _ ep1TrivialMMCtx _ _ rfl rfl rfl (by kernel_rfl) (ep1VendoredSetLive _)]
    unfold tbAccessPre
    dsimp only [ep1VendoredTbAlloc, Allocation.withExtra, allocRange, ep1TrivialMMHooks]
    rw [performBorrowAccessRangeLMU.eq_src, hW1]
    intro hF; exact hF
  · rw [performBorrowAccessRangeLMU.eq_src, hW1]; rfl
  · rw [miriBeforeMemoryWriteExactWP_iff ep1TrivialMMHooks ep1VendoredTbAlloc _ ep1AllocId _ _
      (Size.ofBytes 4) _ _ ep1TrivialMMCtx _ _ rfl rfl rfl (by kernel_rfl) (ep1VendoredSetLive _)]
    unfold tbAccessPre
    dsimp only [ep1VendoredTbAlloc, Allocation.withExtra, allocRange, ep1TrivialMMHooks]
    rw [performBorrowAccessRangeLMU.eq_src]
    generalize hRes : performBorrowAccessRangeLMU ep1DisjointTwoChildTree (.concrete ep1Tag2)
        Size.ZERO (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed = res
    rw [hRes] at hW2
    rw [hW2]
    exact ⟨rfl, hFindPost _⟩
  · rw [miriBeforeMemoryWriteExactWP_iff ep1TrivialMMHooks ep1VendoredTbAlloc _ ep1AllocId _ _
      (Size.ofBytes 4) _ _ ep1TrivialMMCtx _ _ rfl rfl rfl (by kernel_rfl) (ep1VendoredSetLive _)]
    unfold tbAccessPre
    dsimp only [ep1VendoredTbAlloc, Allocation.withExtra, allocRange, ep1TrivialMMHooks]
    rw [performBorrowAccessRangeLMU.eq_src, hW2]
    intro hF; exact hF
  · rw [performBorrowAccessRangeLMU.eq_src, hW2]; rfl
  · rw [exactWP_seq]
    rw [miriBeforeMemoryWriteExactWP_iff ep1TrivialMMHooks ep1VendoredTbAlloc _ ep1AllocId _ _
      (Size.ofBytes 12) _ _ ep1TrivialMMCtx _ _ rfl rfl rfl (by kernel_rfl) (ep1VendoredSetLive _)]
    unfold tbAccessPre
    dsimp only [allocRange]
    have hW3' :
        (ep1VendoredTbAlloc.extra.performBorrowAccessRange (.concrete ep1Tag3) (Size.ofBytes 8)
          (Size.ofBytes 4) .Write ep1TrivialMMHooks.protectedTags .VisitChildrenOfAccessed).status =
        .Completed := by
      dsimp only [ep1VendoredTbAlloc, Allocation.withExtra, ep1TrivialMMHooks]
      rw [performBorrowAccessRangeLMU.eq_src]; exact hW3
    rw [hW3']
    dsimp only
    let ctxW3 : MachineMemoryHooks.Context Unit Unit :=
      { ep1TrivialMMCtx with
        syncObjects := ep1TrivialMMCtx.syncObjects.set ep1AllocId .empty }
    have hNoSyncPost : ctxW3.syncObjects.get ep1AllocId = .empty := rfl
    let tW3 := (ep1VendoredTbAlloc.extra.performBorrowAccessRange (.concrete ep1Tag3)
      (Size.ofBytes 8) (Size.ofBytes 4) .Write ep1TrivialMMHooks.protectedTags
      .VisitChildrenOfAccessed).tree
    let memW3 : MemoryState Provenance BorrowTree Unit :=
      { ep1ObsState.memory with
        live := (ep1ObsState.memory.live.filter fun row => row.1 != ep1AllocId).push
          (ep1AllocId, LocalAllocation.mk .stack (ep1VendoredTbAlloc.setExtra tW3)) }
    have hSetPost :
        ∀ (t : BorrowTree),
          memW3.setLiveAllocation ep1AllocId ((ep1VendoredTbAlloc.setExtra tW3).setExtra t) =
          .ok { memW3 with
                live := (memW3.live.filter fun row => row.1 != ep1AllocId).push
                  (ep1AllocId, LocalAllocation.mk .stack
                    ((ep1VendoredTbAlloc.setExtra tW3).setExtra t)) } := by
      intro t
      exact MemoryState.setLiveAllocation_of_find memW3 ep1AllocId
        (LocalAllocation.mk .stack (ep1VendoredTbAlloc.setExtra tW3)) _ rfl
    change AnnealExactWP
      (miriBeforeMemoryReadAction ep1TrivialMMHooks (ep1VendoredTbAlloc.setExtra tW3)
        ⟨Size.ofBytes ep1TbBaseAddr, some (.concrete ep1AllocId ep1Tag2)⟩
        ep1AllocId (.concrete ep1Tag2) (allocRange Size.ZERO (Size.ofBytes 4)))
      _ _ (memW3, ctxW3)
    rw [miriBeforeMemoryReadExactWP_iff ep1TrivialMMHooks (ep1VendoredTbAlloc.setExtra tW3) _
      ep1AllocId _ _ (Size.ofBytes 4) memW3 _ ctxW3 _ _ rfl rfl hNoSyncPost (by kernel_rfl)
      (hSetPost _)]
    unfold tbAccessPre
    dsimp only [Allocation.setExtra, Allocation.mapExtra, allocRange]
    have hR2' :
        (tW3.performBorrowAccessRange (.concrete ep1Tag2) Size.ZERO (Size.ofBytes 4) .Read
          ep1TrivialMMHooks.protectedTags .VisitChildrenOfAccessed).status = .Completed := by
      dsimp only [tW3, ep1VendoredTbAlloc, Allocation.withExtra, ep1TrivialMMHooks]
      rw [performBorrowAccessRangeLMU.eq_src]
      exact hR2AfterW3
    rw [hR2']
    exact ⟨rfl, rfl⟩

end TbEnabledTranslateBodyMiriExecution

/-! ### §4.4. Vendored-Native `PlaceMachine.accessHooks` + `Step.step` + `translateBody` Execution & `↔` UB Refutations -/

section VendoredNativePlaceMachineTbExecution

/-- Concrete unmodified vendored `Miri.Memory.AllocAddresses.GlobalAddressState` registering
`ep1AllocId` at `ep1TbBaseAddr` under strict provenance mode (so concrete provenance resolves via
vendored `GlobalAddressState.ptrGetAlloc`, while wildcard provenance fails closed with
`.strictAddressLookup`). -/
def ep1GlobalAddressState : Miri.Memory.AllocAddresses.GlobalAddressState :=
  { intToPtrMap := #[⟨ep1TbBaseAddr, ep1AllocId⟩]
    baseAddr := #[⟨ep1AllocId, ep1TbBaseAddr⟩]
    exposed := #[]
    provenanceMode := .strict
    addressMode := .managed
    generation := none }

/-- Under `.strict` provenance mode, unmodified vendored `GlobalAddressState.ptrGetAlloc` rejects
wildcard pointers fail-closed with `.strictAddressLookup`! -/
theorem ep1GlobalAddressState_ptrGetAlloc_wildcard_strict (addr : UInt64) (sz : Int64)
    (hooks : Miri.Memory.AllocAddresses.AddressLookupHooks) :
    ep1GlobalAddressState.ptrGetAlloc
      ⟨Size.ofBytes addr, .wildcard⟩ sz hooks
      { pointerSize := Size.ofBytes 8 } =
    .error .strictAddressLookup := by
  rfl

/-- Vendored `PlaceMachine.AccessConfig Unit Unit` backed by **unmodified vendored
`Miri.Memory.AllocAddresses.GlobalAddressState.ptrGetAlloc`** (`ep1GlobalAddressState`, returning
`.ok (.error addr)` → `.danglingIntegerPointer` for provenance-free, strict-wildcard, or uncached
pointers), `ghostMode := false`, and unmodified `MemoryErrors.operand`. ALL Tree Borrows checks run
inside unmodified vendored `PlaceMachine.accessHooks` → `AllocationAccess.getPtrAlloc{Mut}` →
`PlaceMachine.memoryAccess` → `BorrowTree.performBorrowAccessRange`! -/
def ep1PlaceAccessConfig : PlaceMachine.AccessConfig Unit Unit :=
  { runtime := annealRuntimeDataLayout
    ghostMode := false
    globalKind := none
    globalHooks :=
      { synchronizeMemory := fun _ hs => hs
        evaluateStaticInitializer := fun mem hs _ =>
          ⟨mem, hs, .error "ep1 vendored witness has no static initializers"⟩
        beforeAccessGlobal := fun mem hs _ _ _ _ => ⟨mem, hs, .ok ()⟩
        adjustGlobalAllocation := fun mem hs _ _ =>
          ⟨mem, hs, .error "ep1 vendored witness has no global allocations"⟩ }
    dynamicLayout := fun mem hs _ => ⟨mem, hs, .ok none⟩
    resolvePointer := fun mem ptr sz mach =>
      match ptr.provenance with
      | none => .ok (.error ptr.offset.bytes) mach
      | some prov =>
        let lookup : Miri.Memory.AllocAddresses.AddressLookupHooks :=
          { sizeOf := fun id => (mem.getAllocInfo id).toOption.map (·.size)
            isLive := fun id => some (mem.isAllocLive id) }
        let cx : Miri.Memory.PointerArithmetic := { pointerSize := Size.ofBytes 8 }
        match ep1GlobalAddressState.ptrGetAlloc ⟨ptr.offset, prov⟩ (Int64.ofInt sz) lookup cx with
        | .ok (some (aid, relOff)) =>
          let provExtra : ProvenanceExtra := match prov with
            | .concrete _ tag => .concrete tag
            | .wildcard => .wildcard
          .ok (.ok ⟨aid, relOff, provExtra⟩) mach
        | .ok none | .error _ => .ok (.error ptr.offset.bytes) mach
    beforeAllocationAccess := fun _ => pure ()
    diagnostic := fun _ _ _ => pure ()
    weakMemoryWrite := fun _ _ => pure ()
    syncAccess := fun _ _ _ => pure ()
    retainTouched := fun m _ => m
    memoryError := MemoryErrors.operand }

private def ep1PlaceAllocConfig : PlaceMachine.AllocationConfig Unit Unit :=
  { maximumObjectSize := Size.ofBytes 0x100000
    zeroedStorage := fun _ _ => none
    diagnostic := fun _ _ _ => pure ()
    allocationTail := fun _ _ _ => pure ()
    adjustRootAddress := fun _ _ => throw (.unsupported "ep1 stack alloc unused") }

private def ep1PlaceCompilerHooks : PlaceMachine.CompilerHooks Unit Unit Unit :=
  { debugAssertions := false
    layout := fun _ _ => throw (.unsupported "ep1 uncached local layout unused")
    validationInProgress := pure false
    projection := fun _ => throw (.unsupported "ep1 non-deref projection unused")
    deref := fun _ base _ => do
      match base.ref with
      | .local _ localId none _ =>
        let op ← PlaceMachine.localToOpCore
          (fun id => do
            let slot ← match (← MachineHooks.currentFrame).getLocal id with
              | .ok s => pure s | .error e => throw (.stack e)
            match slot.layout with
            | some lay => pure lay
            | none => throw (.unsupported "ep1 uncached local layout"))
          (pure false) localId
        let sc ← match op.op with
          | .immediate (.scalar sc) => pure sc
          | _ => throw (.invalidProgram "expected pointer scalar local for deref")
        let ptr ← match sc.toPointer annealTargetDataLayout with
          | .ok ptr => pure ptr
          | .error e => throw (MemoryErrors.allocation (.scalar e))
        return ⟨.memory ⟨ptr, .none, none⟩, translateTy ep1U32Ty emptyLayoutTable⟩
      | _ => throw (.unsupported "ep1 deref only supports whole pointer locals")
    checkPlaceType := fun _ _ _ => pure ()
    memoryOffset := fun _ _ _ _ _ => throw (.unsupported "ep1 memoryOffset unused")
    debugAbiCheck := fun _ _ => pure ()
    localSpan := fun _ _ => pure defaultSpanRef
    enforceValidity := fun _ _ => pure false
    validate := fun _ _ => pure ()
    willValidateMemory := fun _ => false }

/-- Unmodified vendored `PlaceMachine.placeHooks` instantiated with `ep1PlaceAccessConfig`
(backed by vendored `GlobalAddressState.ptrGetAlloc`). -/
def ep1VendoredPlaceHooks :
    PlaceHooks Provenance (PlaceMachine.State Unit Unit) Unit MachineHooks.FrameExtra :=
  PlaceMachine.placeHooks ep1PlaceAccessConfig ep1PlaceAllocConfig ep1PlaceCompilerHooks

private def ep1PlaceStorageHooks : MachineHooks.StorageHooks Unit Unit :=
  { veryTriviallySized := fun _ => .ok true
    layout := fun id => do
      let slot ← match (← MachineHooks.currentFrame).getLocal id with
        | .ok s => pure s
        | .error e => throw (.stack e)
      match slot.layout with
      | some lay => pure lay
      | none => throw (.unsupported "ep1 uncached local layout")
    allocateDyn := fun _ _ => throw (.unsupported "ep1 dynamic stack alloc unused")
    deallocateStack := fun _ => throw (.unsupported "ep1 stack dealloc unused") }

private def ep1VendoredControlHooks :
    ControlHooks Provenance LocalLayout MachineHooks.FrameExtra (PlaceMachine.Machine Unit Unit)
      Unit (Immediate Provenance) :=
  { bodySpan := fun _ => .ok defaultSpanRef
    -- Return value: the ACTUAL `_0` immediate via vendored `Frame.getLocalOperand` (fail closed on
    -- dead / missing / non-immediate `_0`), not a constant placeholder.
    returnOperand := fun _ st =>
      match st.stack.currentFrame? with
      | none => (st, .error (.stack .emptyStack))
      | some fr =>
        match fr.getLocalOperand 0 with
        | .error e => (st, .error (.stack e))
        | .ok (.immediate imm) => (st, .ok imm)
        | .ok _ => (st, .error (.invalidProgram "ep1 witness: non-immediate return local"))
    -- Frame pop: vendored `MachineHooks.beforeStackPopWithEnsure` (Tree Borrows protector release
    -- + `GlobalState.endCall`) BEFORE vendored `Stack.popFrame`, matching Miri's `on_stack_pop`.
    popFrame := fun _ st =>
      match MachineHooks.run (MachineHooks.beforeStackPopWithEnsure (fun _ => pure ())) st with
      | (st', .error e) => (st', .error e)
      | (st', .ok ()) =>
        match st'.stack.popFrame with
        | .error e => (st', .error (.stack e))
        | .ok (stk, fr) => ({ st' with stack := stk }, .ok fr)
    copyReturn := fun _ _ _ st => (st, .ok ())
    cleanupFrame := fun _ _ _ st => (st, .ok .normal)
    unwindTerminate := fun _ _ st => (st, .error (.machineStop "unwind terminate")) }

private def ep1VendoredTermHooks :
    TerminatorHooks Provenance LocalLayout MachineHooks.FrameExtra (PlaceMachine.Machine Unit Unit)
      Unit (Immediate Provenance) (Immediate Provenance) :=
  { ep1VendoredControlHooks with
    evalDiscriminant := fun _ _ st => (st, .error (.unsupported "switch unused"))
    compareSwitchCase := fun _ _ _ st => (st, .error (.unsupported "switch unused"))
    call := fun _ _ st => (st, .error (.unsupported "call unused"))
    tailCall := fun _ _ st => (st, .error (.unsupported "tailCall unused"))
    drop := fun _ _ _ _ st => (st, .error (.unsupported "drop unused"))
    ignoreOptionalOverflowChecks := fun _ => false
    readAssertCondition := fun _ _ st => (st, .error (.unsupported "assert unused"))
    assertPanic := fun _ _ _ st => (st, .error (.unsupported "assert unused")) }

/-- **Vendored-Native Tree-Borrows `StepHooks` (`ep1VendoredPlaceStepHooks`)**:
operates directly on vendored `PlaceMachine.State Unit Unit` (`MemoryState Provenance BorrowTree Unit`
with NON-OPTIONAL `BorrowTree` extras) and delegates:
- place evaluation, dereference local reads, operand conversion, and destination writes directly to
  **unmodified vendored `Miri.Interpreter.{evalPlace, placeToOp, writePlaceImmediate}`** via
  **`PlaceMachine.placeHooks`** (`PlaceMachine.{localToOpCore, writeMemory, readImmediate}`,
  `placeWriteLocalImmediate`, `MachineHooks.{afterLocalRead, afterLocalWrite}`);
- pointer address resolution directly to **unmodified vendored
  `Miri.Memory.AllocAddresses.GlobalAddressState.ptrGetAlloc`** (`ep1GlobalAddressState`);
- memory accesses directly to **unmodified vendored `PlaceMachine.accessHooks` →
  `AllocationAccess.getPtrAlloc{Mut}` → `PlaceMachine.memoryAccess` →
  `BorrowTree.performBorrowAccessRange` → `Allocation.{writeScalar, readScalar}`**;
- `StorageDead` directly to **unmodified vendored `MachineHooks.storageDead`**;
- terminators, returns, and `FnEntry` protector release directly to **unmodified vendored
  `ControlFlow.{evalTerminator, returnFromCurrentFrame}` → `Frame.getLocalOperand 0` →
  `MachineHooks.beforeStackPopWithEnsure` (`BorrowTree.releaseProtector` + `GlobalState.endCall`) →
  `Stack.popFrame`**.
ZERO custom TB-check instrumentation (`annealTbCheckMemAccess`) is used anywhere in this path!

**Precise trust boundary (what is vendored vs. witness-local).** Vendored and unmodified:
`Step.step`, `ControlFlow.{evalTerminator, returnFromCurrentFrame}`,
`PlaceMachine.{placeHooks, writeMemory, readImmediate, accessHooks, memoryAccess, localToOpCore}`,
`Miri.Interpreter.{evalPlace, placeToOp, writePlaceImmediate, placeWriteLocalImmediate}`,
`AllocationAccess.getPtrAlloc{,Mut}`, `AllocAddresses.GlobalAddressState.ptrGetAlloc`,
`BorrowTree.{performBorrowAccessRange, releaseProtector}`, `GlobalState.endCall`,
`MachineHooks.{beforeStackPopWithEnsure, storageDead, afterLocalRead, afterLocalWrite}`,
`Frame.{getLocalOperand, setLocalOperand}`, `Stack.popFrame`.
Witness-local (authored, scoped to `ep1BodyTbDerefWriteAndRead`):
- the 2-arm `assign` rvalue dispatcher (`.Use (.Constant (.Val (.Scalar (.Int ...))))` and
  `.Use (.Copy/.Move srcPlace)`; every other rvalue shape fails closed with `.unsupported`);
- `ep1PlaceCompilerHooks.deref` (resolves whole-local pointer dereferences via vendored
  `PlaceMachine.localToOpCore` with fixed `u32` pointee layout; non-deref projections fail closed);
- `ep1PlaceStorageHooks` reads each local's actual cached frame layout via `Frame.getLocal`
  (failing closed on uncached/missing locals or dynamic stack allocation/deallocation, with
  `veryTriviallySized := fun _ => .ok true` for sized scalar/pointer locals);
- `ep1VendoredControlHooks.copyReturn` is a no-op because the root `.stop` frame has no caller
  return destination (`returnOperand` still reads `_0` via vendored `Frame.getLocalOperand 0` and
  `popFrame` runs vendored `MachineHooks.beforeStackPopWithEnsure` before `Stack.popFrame`).
Hence these witnesses certify vendored PlaceHooks, GlobalAddressState, Tree Borrows, memory, and
protector-release semantics on the exercised accesses, not a full vendored `ExecutionControl.hooks`
machine. -/
def ep1VendoredPlaceStepHooks :
    StepHooks Provenance LocalLayout MachineHooks.FrameExtra (PlaceMachine.Machine Unit Unit)
      Unit (RuntimePlace Provenance) :=
  { assign := fun _ place rvalue state =>
      Miri.Interpreter.runRvalue (do
        let rtDest ← Miri.Interpreter.evalPlace ep1VendoredPlaceHooks () place false
        match rvalue with
        | .Use (.Constant c) _ =>
          match c.value with
          | .Val (.Scalar (.Int bits szBytes)) _ =>
            let sc ← match Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 bits)
                (Size.ofBytes szBytes.toUInt64) with
              | .ok sc => pure sc
              | .error e => throw (MemoryErrors.allocation (.scalar e))
            Miri.Interpreter.writePlaceImmediate ep1VendoredPlaceHooks () (.scalar sc) rtDest
          | _ => throw (.unsupported "non-int constant in ep1 vendored PlaceMachine witness")
        | .Use (.Copy srcPlace) _ | .Use (.Move srcPlace) _ =>
          let rtSrc ← Miri.Interpreter.evalPlace ep1VendoredPlaceHooks () srcPlace false
          let opSrc ← Miri.Interpreter.placeToOp ep1VendoredPlaceHooks () rtSrc
          let readVal ← PlaceMachine.readImmediate ep1PlaceAccessConfig opSrc
          Miri.Interpreter.writePlaceImmediate ep1VendoredPlaceHooks () readVal.imm rtDest
        | _ => throw (.unsupported "rvalue shape outside ep1 vendored PlaceMachine witness"))
        state
    evalPlace := fun _ _ _ st => (st, .error (.unsupported "evalPlace unused"))
    writeDiscriminant := fun _ _ _ st => (st, .error (.unsupported "writeDiscriminant unused"))
    storageLive := fun _ _ st => (st, .error (.unsupported "storageLive unused"))
    storageDead := fun _ lid st =>
      Miri.Interpreter.runRvalue (MachineHooks.storageDead ep1PlaceStorageHooks lid) st
    intrinsic := fun _ _ st => (st, .error (.unsupported "intrinsic unused"))
    incrementConstEvalCounter := fun _ st => (st, .ok ())
    returnFromCurrentFrame := ControlFlow.returnFromCurrentFrame ep1VendoredControlHooks
    beforeTerminator := fun _ st => (st, .ok ())
    terminator := ControlFlow.evalTerminator ep1VendoredTermHooks }

private def ep1VendoredPtrScalar (prov : Option Provenance) (off : UInt64) :
    Miri.Memory.Scalar Provenance :=
  match prov with
  | some p => Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨Size.ofBytes (ep1TbBaseAddr + off), p⟩
  | none =>
    match Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 (ep1TbBaseAddr + off).toNat) (Size.ofBytes 8) with
    | .ok sc => sc
    | .error _ => Miri.Memory.Scalar.fromPointer annealTargetDataLayout
        ⟨Size.ofBytes (ep1TbBaseAddr + off), .concrete ep1AllocId ep1Tag1⟩

/-- Active `FnEntry` frame protectors (`ep1Tag2` and `ep1Tag3` on `ep1AllocId`), released by
unmodified vendored `MachineHooks.beforeStackPopWithEnsure` when the frame returns. -/
private def ep1FrameBorrowState : Miri.TreeBorrows.FrameState :=
  { protectedTags := #[(ep1AllocId, ep1Tag2), (ep1AllocId, ep1Tag3)] }

/-- Initial vendored `PlaceMachine.State Unit Unit` loaded with
`LeanMiriSpec.Correspondence.translateBody ep1BodyTbDerefWriteAndRead`, live `ep1VendoredTbAlloc`
(`Allocation Provenance BorrowTree` at `ep1AllocId`), `FnEntry` frame protectors
`ep1FrameBorrowState`, and global `borrowTracker := some` with `ep1Prot23`. -/
noncomputable def ep1InitVendoredPlaceState (writeProv : Option Provenance) (writeOff : UInt64) :
    PlaceMachine.State Unit Unit :=
  let pLay := some (translateTy ep1MutPtrU32Ty emptyLayoutTable)
  let u32Lay := some (translateTy ep1U32Ty emptyLayoutTable)
  let locals : Array (LocalState Provenance LocalLayout) :=
    #[ { value := .live (.immediate .uninit), layout := u32Lay },
       { value := .live (.immediate (.scalar (ep1VendoredPtrScalar writeProv writeOff))), layout := pLay },
       { value := .live (.immediate (.scalar (ep1VendoredPtrScalar (some (.concrete ep1AllocId ep1Tag2)) 0))),
         layout := pLay } ]
  let frame : Frame Provenance LocalLayout MachineHooks.FrameExtra :=
    { body := translateBody ep1BodyTbDerefWriteAndRead
      bodyIdentity := BodyIdentity.ofCanonicalIndex 0
      functionInstance := ⟨.Item 0, #[]⟩
      extra := { borrowTracker := some ep1FrameBorrowState, catchUnwind := none,
                 userRelevance := 0, dataRace := none }
      returnContinuation := .stop false
      returnPlace := .frameLocal 0 0 none (translateTy ep1U32Ty emptyLayoutTable)
        (LocalsIdentity.ofAllocationToken 0)
      localsIdentity := LocalsIdentity.ofAllocationToken 0
      locals := locals
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 0⟩ }
  let mach : PlaceMachine.Machine Unit Unit :=
    { memory := ep1ObsState.memory
      borrowTracker := some { global := { GlobalState.new with protectedTags := ep1Prot23 },
                              retagMode := .Default }
      dataRace := none
      threads := Miri.Concurrency.ThreadManager.initial true
      raceAllocations := #[]
      allocationSpans := #[]
      user := () }
  { stack := { frames := #[frame] }, machine := mach }

/-- Modular Stage 1: exact reduction of unmodified `PlaceMachine.memoryAccess ep1PlaceAccessConfig`. -/
private theorem ep1PlaceMemoryAccess_eq
    (write : Bool) (mach : PlaceMachine.Machine Unit Unit) (tree : BorrowTree)
    (tag : BorTag) (off : UInt64) (bt : MachineHooks.BorrowState)
    (hNoRace : mach.dataRace = none)
    (hBt : mach.borrowTracker = some bt) :
    PlaceMachine.memoryAccess ep1PlaceAccessConfig write ⟨mach, none⟩ tree ep1AllocId
        (.concrete tag) (allocRange (Size.ofBytes off) (Size.ofBytes 4)) =
      let accessed := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes off)
        (Size.ofBytes 4) (if write then .Write else .Read) bt.global.protectedTags
        .VisitChildrenOfAccessed
      match accessed.status with
      | .Completed => ⟨⟨mach, none⟩, accessed.tree, .ok ()⟩
      | st =>
        let err := placeMachineTreeError st
        ⟨⟨mach, some err⟩, accessed.tree, .error (reprStr err)⟩ := by
  unfold PlaceMachine.memoryAccess ep1PlaceAccessConfig
  cases write with
  | false =>
    simp only [Id.run, Bool.false_eq_true, ↓reduceIte, allocRange]
    unfold_pm
    simp only [Id.run, MachineHooks.memoryRaceAccess, hNoRace, hBt, pure, Pure.pure, EStateM.pure]
    generalize tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes off) (Size.ofBytes 4)
        .Read bt.global.protectedTags .VisitChildrenOfAccessed = accessed
    rcases accessed with ⟨accTree, accLocs, accStatus⟩
    cases accStatus with
    | Completed => simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    | AccessFailure r s =>
      simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte, placeMachineTreeError]
      cases s <;> rfl
    | WildcardFailure r s =>
      simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte, placeMachineTreeError]
      cases s <;> rfl
    | _ =>
      simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte, placeMachineTreeError]
  | true =>
    simp only [Id.run, ↓reduceIte, allocRange]
    unfold_pm
    simp only [Id.run, MachineHooks.memoryRaceAccess, hNoRace, hBt, pure, Pure.pure, EStateM.pure]
    generalize tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes off) (Size.ofBytes 4)
        .Write bt.global.protectedTags .VisitChildrenOfAccessed = accessed
    rcases accessed with ⟨accTree, accLocs, accStatus⟩
    cases accStatus with
    | Completed => simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    | AccessFailure r s =>
      simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte, placeMachineTreeError]
      cases s <;> rfl
    | WildcardFailure r s =>
      simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte, placeMachineTreeError]
      cases s <;> rfl
    | _ =>
      simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte, placeMachineTreeError]

/-- Modular Stage 2 (write): exact reduction of unmodified `AllocationAccess.getPtrAllocMut`
under `PlaceMachine.accessHooks ep1PlaceAccessConfig`. -/
private theorem ep1GetPtrAllocMut_eq
    (mach : PlaceMachine.Machine Unit Unit) (alloc : Allocation Provenance BorrowTree)
    (tag : BorTag) (off : UInt64) (bt : MachineHooks.BorrowState)
    (hNoRace : mach.dataRace = none)
    (hBt : mach.borrowTracker = some bt)
    (hFind : mach.memory.live.find? (fun row => row.1 == ep1AllocId) =
      some (ep1AllocId, LocalAllocation.mk .stack alloc))
    (hAny : mach.memory.live.any (fun row => row.1 == ep1AllocId) = true)
    (hMut : alloc.mutability = .Mut)
    (hByteSz : alloc.byteSize = Size.ofBytes 16)
    (hOffBounds : (ep1TbBaseAddr + off).toNat ≥ ep1TbBaseAddr.toNat ∧
      (ep1TbBaseAddr + off - ep1TbBaseAddr) = off ∧
      off.toNat + 4 ≤ 16 ∧
      checkedBounds ⟨Size.ofBytes 8⟩ ep1AllocId (Size.ofBytes 16) (Size.ofBytes off) 4 .memoryAccess =
        .ok ())
    (hPtrGetAlloc : ∀ (hooks : Miri.Memory.AllocAddresses.AddressLookupHooks),
      ep1GlobalAddressState.ptrGetAlloc
        ⟨Size.ofBytes (ep1TbBaseAddr + off), .concrete ep1AllocId tag⟩ (Int64.ofInt 4) hooks
        { pointerSize := Size.ofBytes 8 } =
      .ok (some (ep1AllocId, Size.ofBytes off))) :
    let ptr : Pointer (Option Provenance) :=
      ⟨Size.ofBytes (ep1TbBaseAddr + off), some (.concrete ep1AllocId tag)⟩
    let accessed := alloc.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes off)
      (Size.ofBytes 4) .Write bt.global.protectedTags .VisitChildrenOfAccessed
    let allocTB := alloc.setExtra accessed.tree
    let memTB : MemoryState Provenance BorrowTree Unit :=
      { mach.memory with
        live := (mach.memory.live.filter fun row => row.1 != ep1AllocId).push
          (ep1AllocId, LocalAllocation.mk .stack allocTB) }
    let refTB : AllocationAccessRef Provenance BorrowTree :=
      ⟨ep1AllocId, allocRange (Size.ofBytes off) (Size.ofBytes 4), allocTB⟩
    AllocationAccess.getPtrAllocMut mach.memory ⟨mach, none⟩ ⟨Size.ofBytes 8⟩ ptr (Size.ofBytes 4)
        false none ep1PlaceAccessConfig.globalHooks (PlaceMachine.accessHooks ep1PlaceAccessConfig) =
      match accessed.status with
      | .Completed => ⟨memTB, ⟨mach, none⟩, some refTB, .ok (some refTB)⟩
      | errStatus =>
        let err := placeMachineTreeError errStatus
        ⟨memTB, ⟨mach, some err⟩, some refTB,
          .error (.hookFailure "beforeMemoryWrite" (reprStr err))⟩ := by
  dsimp only
  have hSize4 : sizeAsI64 (Size.ofBytes 4) = .ok 4 := by decide
  have hResPtr :
      (PlaceMachine.accessHooks ep1PlaceAccessConfig).resolvePointer mach.memory ⟨mach, none⟩
        ⟨Size.ofBytes (ep1TbBaseAddr + off), some (.concrete ep1AllocId tag)⟩ 4 =
      ⟨⟨mach, none⟩, .ok (.ok ⟨ep1AllocId, Size.ofBytes off, .concrete tag⟩)⟩ := by
    unfold PlaceMachine.accessHooks ep1PlaceAccessConfig
    unfold_pm
    dsimp only
    rw [hPtrGetAlloc]
  have hRaw :
      MemoryLifecycle.getAllocRawMut mach.memory ⟨mach, none⟩ ep1AllocId none
        ep1PlaceAccessConfig.globalHooks = ⟨mach.memory, ⟨mach, none⟩, .ok alloc⟩ := by
    simp [MemoryLifecycle.getAllocRawMut, ep1PlaceAccessConfig, hFind, hMut]
  have hBefore :
      (PlaceMachine.accessHooks ep1PlaceAccessConfig).beforeAllocationAccess ⟨mach, none⟩ ep1AllocId =
        ⟨⟨mach, none⟩, .ok ()⟩ := by
    unfold PlaceMachine.accessHooks ep1PlaceAccessConfig; unfold_pm; rfl
  have hFourNeZero : ((4 : Int) != 0) = true := by decide
  have hBeforeWrite :
      (PlaceMachine.accessHooks ep1PlaceAccessConfig).beforeMemoryWrite ⟨mach, none⟩ alloc.extra
        ⟨Size.ofBytes (ep1TbBaseAddr + off), some (.concrete ep1AllocId tag)⟩ ep1AllocId
        (.concrete tag) (allocRange (Size.ofBytes off) (Size.ofBytes 4)) =
      PlaceMachine.memoryAccess ep1PlaceAccessConfig true ⟨mach, none⟩ alloc.extra ep1AllocId
        (.concrete tag) (allocRange (Size.ofBytes off) (Size.ofBytes 4)) := rfl
  have hMemAcc := ep1PlaceMemoryAccess_eq true mach alloc.extra tag off bt hNoRace hBt
  have hSetTB :
      ∀ (t : BorrowTree),
        mach.memory.setLiveAllocation ep1AllocId (alloc.setExtra t) =
        .ok { mach.memory with
              live := (mach.memory.live.filter fun row => row.1 != ep1AllocId).push
                (ep1AllocId, LocalAllocation.mk .stack (alloc.setExtra t)) } := fun t =>
    MemoryState.setLiveAllocation_of_find mach.memory ep1AllocId (LocalAllocation.mk .stack alloc) _ hFind
  unfold AllocationAccess.getPtrAllocMut
  unfold_aa
  dsimp only [Id.run]
  rw [hSize4]
  simp only [bind, Bind.bind, pure, Pure.pure, hFourNeZero, ↓reduceIte, hResPtr, hRaw, hByteSz,
    hOffBounds.2.2.2, Bool.not_false, Option.map_some, hBefore, hBeforeWrite, hMemAcc]
  generalize alloc.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes off) (Size.ofBytes 4)
      .Write bt.global.protectedTags .VisitChildrenOfAccessed = accessed
  rcases accessed with ⟨accTree, accLocs, accStatus⟩
  cases accStatus with
  | Completed =>
    simp only [hAny, ↓reduceIte, hSetTB accTree]
  | _ =>
    simp only [hAny, ↓reduceIte, hSetTB accTree]

/-- Exact symbolic reduction of unmodified vendored `PlaceMachine.writeMemory ep1PlaceAccessConfig`
on a concrete-provenance `u32` pointer into `ep1AllocId`: routes through unmodified
`PlaceMachine.accessHooks` → `AllocationAccess.getPtrAllocMut` → `PlaceMachine.memoryAccess` →
`BorrowTree.performBorrowAccessRange`! -/
private theorem ep1PlaceWriteMemory_u32_concrete_eq
    (st : PlaceMachine.State Unit Unit) (alloc : Allocation Provenance BorrowTree)
    (tag : BorTag) (off : UInt64) (val : Miri.Memory.Scalar Provenance)
    (bt : MachineHooks.BorrowState)
    (hNoRace : st.machine.dataRace = none)
    (hBt : st.machine.borrowTracker = some bt)
    (hFind : st.machine.memory.live.find? (fun row => row.1 == ep1AllocId) =
      some (ep1AllocId, LocalAllocation.mk .stack alloc))
    (hAny : st.machine.memory.live.any (fun row => row.1 == ep1AllocId) = true)
    (hMut : alloc.mutability = .Mut)
    (hByteSz : alloc.byteSize = Size.ofBytes 16)
    (hOffBounds : (ep1TbBaseAddr + off).toNat ≥ ep1TbBaseAddr.toNat ∧
      (ep1TbBaseAddr + off - ep1TbBaseAddr) = off ∧
      off.toNat + 4 ≤ 16 ∧
      checkedBounds ⟨Size.ofBytes 8⟩ ep1AllocId (Size.ofBytes 16) (Size.ofBytes off) 4 .memoryAccess =
        .ok ())
    (hPtrGetAlloc : ∀ (hooks : Miri.Memory.AllocAddresses.AddressLookupHooks),
      ep1GlobalAddressState.ptrGetAlloc
        ⟨Size.ofBytes (ep1TbBaseAddr + off), .concrete ep1AllocId tag⟩ (Int64.ofInt 4) hooks
        { pointerSize := Size.ofBytes 8 } =
      .ok (some (ep1AllocId, Size.ofBytes off)))
    (hSub4 : (allocRange (Size.ofBytes off) (Size.ofBytes 4)).subrange
      (allocRange Size.ZERO (Size.ofBytes 4)) =
      .ok (allocRange (Size.ofBytes off) (Size.ofBytes 4)))
    (hValSz : val.size = Size.ofBytes 4)
    (hValInt : val.isPointer = false) :
    let mp : MPlaceTy Provenance :=
      ⟨⟨⟨Size.ofBytes (ep1TbBaseAddr + off), some (.concrete ep1AllocId tag)⟩, .none, none⟩,
       translateTy ep1U32Ty emptyLayoutTable⟩
    let accessed := alloc.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes off)
      (Size.ofBytes 4) .Write bt.global.protectedTags .VisitChildrenOfAccessed
    let allocTB := alloc.setExtra accessed.tree
    let memTB : MemoryState Provenance BorrowTree Unit :=
      { st.machine.memory with
        live := (st.machine.memory.live.filter fun row => row.1 != ep1AllocId).push
          (ep1AllocId, LocalAllocation.mk .stack allocTB) }
    PlaceMachine.writeMemory ep1PlaceAccessConfig (fun _ => false) (.scalar val) mp st =
      match accessed.status with
      | .Completed =>
        let mutRes := Allocation.writeScalar annealTargetDataLayout
          (allocRange (Size.ofBytes off) (Size.ofBytes 4)) val allocTB
        let updatedAlloc := match mutRes with | .ok _ a | .error _ a => a
        let memW : MemoryState Provenance BorrowTree Unit :=
          { memTB with
            live := (memTB.live.filter fun row => row.1 != ep1AllocId).push
              (ep1AllocId, LocalAllocation.mk .stack updatedAlloc) }
        match mutRes with
        | .ok () _ => .ok () { st with machine := { st.machine with memory := memW } }
        | .error e _ => .error (MemoryErrors.operand (.allocation e))
            { st with machine := { st.machine with memory := memW } }
      | errStatus =>
        .error (placeMachineTreeError errStatus)
          { st with machine := { st.machine with memory := memTB } } := by
  dsimp only
  have hFindTB :
      ∀ (t : BorrowTree),
        ({ st.machine.memory with
           live := (st.machine.memory.live.filter fun row => row.1 != ep1AllocId).push
             (ep1AllocId, LocalAllocation.mk .stack (alloc.setExtra t)) } :
            MemoryState Provenance BorrowTree Unit).live.find? (fun row => row.1 == ep1AllocId) =
          some (ep1AllocId, LocalAllocation.mk .stack (alloc.setExtra t)) := by
    intro t
    have hFilterNone :
        (st.machine.memory.live.filter fun row => row.1 != ep1AllocId).find?
          (fun row => row.1 == ep1AllocId) = none := by
      rw [← Array.find?_toList, List.find?_eq_none]
      intro x hx
      rw [Array.mem_toList_iff] at hx
      have hMem := (Array.mem_filter.mp hx).2
      simp only [bne_iff_ne, ne_eq] at hMem
      simp [beq_false_of_ne hMem]
    rw [Array.find?_push, hFilterNone]
    simp
  have hGetPtr := ep1GetPtrAllocMut_eq st.machine alloc tag off bt hNoRace hBt hFind hAny hMut
    hByteSz hOffBounds hPtrGetAlloc
  dsimp only at hGetPtr
  have hGhost : ep1PlaceAccessConfig.ghostMode = false := rfl
  have hGlobKind : ep1PlaceAccessConfig.globalKind = none := rfl
  have hGetPlace :
      getPlaceAllocMut st.machine.memory ⟨st.machine, none⟩
        ⟨⟨⟨Size.ofBytes (ep1TbBaseAddr + off), some (.concrete ep1AllocId tag)⟩, .none, none⟩,
         localMemoryLayout (translateTy ep1U32Ty emptyLayoutTable)⟩
        ep1PlaceAccessConfig.runtime ep1PlaceAccessConfig.ghostMode ep1PlaceAccessConfig.globalKind
        ep1PlaceAccessConfig.globalHooks (PlaceMachine.accessHooks ep1PlaceAccessConfig)
        ep1PlaceAccessConfig.dynamicLayout =
      let accessed := alloc.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes off)
        (Size.ofBytes 4) .Write bt.global.protectedTags .VisitChildrenOfAccessed
      let allocTB := alloc.setExtra accessed.tree
      let memTB : MemoryState Provenance BorrowTree Unit :=
        { st.machine.memory with
          live := (st.machine.memory.live.filter fun row => row.1 != ep1AllocId).push
            (ep1AllocId, LocalAllocation.mk .stack allocTB) }
      let refTB : AllocationAccessRef Provenance BorrowTree :=
        ⟨ep1AllocId, allocRange (Size.ofBytes off) (Size.ofBytes 4), allocTB⟩
      match accessed.status with
      | .Completed => ⟨memTB, ⟨st.machine, none⟩, some refTB, .ok (some refTB)⟩
      | errStatus =>
        let err := placeMachineTreeError errStatus
        ⟨memTB, ⟨st.machine, some err⟩, some refTB,
          .error (.pointerAccess (.hookFailure "beforeMemoryWrite" (reprStr err)))⟩ := by
    unfold getPlaceAllocMut
    unfold_mo
    have hPtrSz : ep1PlaceAccessConfig.runtime.pointerSizeIn
        ep1PlaceAccessConfig.runtime.defaultAddressSpace = .ok (Size.ofBytes 8) := by decide
    have hLaySz : (localMemoryLayout (translateTy ep1U32Ty emptyLayoutTable)).size =
        Size.ofBytes 4 := by decide
    have hUnsized : (localMemoryLayout (translateTy ep1U32Ty emptyLayoutTable)).backendRepr.isUnsized =
        false := by decide
    simp only [Id.run, hUnsized, Bool.false_eq_true, ↓reduceIte, hPtrSz, Except.mapError,
      Except.bind, Except.pure, bind, Bind.bind, pure, Pure.pure, hLaySz, hGhost, hGlobKind, hGetPtr]
    generalize alloc.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes off) (Size.ofBytes 4)
        .Write bt.global.protectedTags .VisitChildrenOfAccessed = accessed
    rcases accessed with ⟨accTree, accLocs, accStatus⟩
    cases accStatus <;> rfl
  dsimp only at hGetPlace
  have hWriteOp :
      writeImmediateToMplaceNoValidate st.machine.memory ⟨st.machine, none⟩ (.scalar val)
        ⟨⟨⟨Size.ofBytes (ep1TbBaseAddr + off), some (.concrete ep1AllocId tag)⟩, .none, none⟩,
         localMemoryLayout (translateTy ep1U32Ty emptyLayoutTable)⟩
        ep1PlaceAccessConfig.runtime ep1PlaceAccessConfig.ghostMode ep1PlaceAccessConfig.globalKind
        ep1PlaceAccessConfig.globalHooks (PlaceMachine.accessHooks ep1PlaceAccessConfig)
        ep1PlaceAccessConfig.dynamicLayout (fun _ => false) =
      let accessed := alloc.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes off)
        (Size.ofBytes 4) .Write bt.global.protectedTags .VisitChildrenOfAccessed
      let allocTB := alloc.setExtra accessed.tree
      let memTB : MemoryState Provenance BorrowTree Unit :=
        { st.machine.memory with
          live := (st.machine.memory.live.filter fun row => row.1 != ep1AllocId).push
            (ep1AllocId, LocalAllocation.mk .stack allocTB) }
      let refTB : AllocationAccessRef Provenance BorrowTree :=
        ⟨ep1AllocId, allocRange (Size.ofBytes off) (Size.ofBytes 4), allocTB⟩
      match accessed.status with
      | .Completed =>
        let mutRes := Allocation.writeScalar annealTargetDataLayout
          (allocRange (Size.ofBytes off) (Size.ofBytes 4)) val allocTB
        let updatedAlloc := match mutRes with | .ok _ a | .error _ a => a
        let memW : MemoryState Provenance BorrowTree Unit :=
          { memTB with
            live := (memTB.live.filter fun row => row.1 != ep1AllocId).push
              (ep1AllocId, LocalAllocation.mk .stack updatedAlloc) }
        match mutRes with
        | .ok () _ => ⟨memW, ⟨st.machine, none⟩, some { refTB with allocation := updatedAlloc }, .ok ()⟩
        | .error e _ =>
          ⟨memW, ⟨st.machine, none⟩, some { refTB with allocation := updatedAlloc }, .error (.allocation e)⟩
      | errStatus =>
        let err := placeMachineTreeError errStatus
        ⟨memTB, ⟨st.machine, some err⟩, some refTB,
          .error (.pointerAccess (.hookFailure "beforeMemoryWrite" (reprStr err)))⟩ := by
    unfold writeImmediateToMplaceNoValidate
    unfold_mo
    have hRepr : (localMemoryLayout (translateTy ep1U32Ty emptyLayoutTable)).backendRepr =
        .Scalar (.Initialized (value := .Int .I32 false)
          (validRange := ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 (2 ^ 32 - 1)⟩)) := by decide
    have hPrimSz : Miri.ABI.Primitive.size (.Int .I32 false) ep1PlaceAccessConfig.runtime =
        .ok (Size.ofBytes 4) := by decide
    simp only [Id.run, hRepr, Miri.ABI.BackendRepr.isUnsized, Bool.false_eq_true, ↓reduceIte,
      Miri.ABI.Scalar.primitive, hPrimSz, Except.mapError, bind, Bind.bind, Except.bind,
      hValSz, bne_self_eq_false, hValInt, pure, Pure.pure, Except.pure, hGetPlace]
    generalize alloc.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes off) (Size.ofBytes 4)
        .Write bt.global.protectedTags .VisitChildrenOfAccessed = accessed
    rcases accessed with ⟨accTree, accLocs, accStatus⟩
    cases accStatus with
    | Completed =>
      simp only [hSub4, ep1PlaceAccessConfig, annealRuntimeDataLayout]
      let memCur : MemoryState Provenance BorrowTree Unit :=
        { st.machine.memory with
          live := (st.machine.memory.live.filter fun row => row.1 != ep1AllocId).push
            (ep1AllocId, LocalAllocation.mk .stack (alloc.setExtra accTree)) }
      have hSetW :
          ∀ (a' : Allocation Provenance BorrowTree),
            memCur.setLiveAllocation ep1AllocId a' =
            .ok { memCur with
                  live := (memCur.live.filter fun row => row.1 != ep1AllocId).push
                    (ep1AllocId, LocalAllocation.mk .stack a') } := fun a' =>
        MemoryState.setLiveAllocation_of_find memCur ep1AllocId
          (LocalAllocation.mk .stack (alloc.setExtra accTree)) _ (hFindTB accTree)
      dsimp only [memCur] at hSetW
      cases Allocation.writeScalar annealTargetDataLayout
          (allocRange (Size.ofBytes off) (Size.ofBytes 4)) val (alloc.setExtra accTree) with
      | ok u updatedAlloc =>
        cases u; rw [hSetW updatedAlloc]
      | error e updatedAlloc =>
        rw [hSetW updatedAlloc]
    | _ => rfl
  unfold PlaceMachine.writeMemory
  unfold_pm
  simp only [get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, hWriteOp]
  dsimp only [ep1PlaceAccessConfig]
  generalize alloc.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes off) (Size.ofBytes 4)
      .Write bt.global.protectedTags .VisitChildrenOfAccessed = accessed
  rcases accessed with ⟨accTree, accLocs, accStatus⟩
  cases accStatus with
  | Completed =>
    cases Allocation.writeScalar annealTargetDataLayout
        (allocRange (Size.ofBytes off) (Size.ofBytes 4)) val (alloc.setExtra accTree) with
    | ok u _ => cases u; rfl
    | error e _ => rfl
  | _ => rfl

/-- Modular Stage 2 (read): exact reduction of unmodified `AllocationAccess.getPtrAlloc`
under `PlaceMachine.accessHooks ep1PlaceAccessConfig`. -/
private theorem ep1GetPtrAlloc_eq
    (mach : PlaceMachine.Machine Unit Unit) (alloc : Allocation Provenance BorrowTree)
    (tag : BorTag) (off : UInt64) (bt : MachineHooks.BorrowState)
    (hNoRace : mach.dataRace = none)
    (hBt : mach.borrowTracker = some bt)
    (hFind : mach.memory.live.find? (fun row => row.1 == ep1AllocId) =
      some (ep1AllocId, LocalAllocation.mk .stack alloc))
    (hAny : mach.memory.live.any (fun row => row.1 == ep1AllocId) = true)
    (hByteSz : alloc.byteSize = Size.ofBytes 16)
    (hOffBounds : (ep1TbBaseAddr + off).toNat ≥ ep1TbBaseAddr.toNat ∧
      (ep1TbBaseAddr + off - ep1TbBaseAddr) = off ∧
      off.toNat + 4 ≤ 16 ∧
      checkedBounds ⟨Size.ofBytes 8⟩ ep1AllocId (Size.ofBytes 16) (Size.ofBytes off) 4 .memoryAccess =
        .ok ())
    (hPtrGetAlloc : ∀ (hooks : Miri.Memory.AllocAddresses.AddressLookupHooks),
      ep1GlobalAddressState.ptrGetAlloc
        ⟨Size.ofBytes (ep1TbBaseAddr + off), .concrete ep1AllocId tag⟩ (Int64.ofInt 4) hooks
        { pointerSize := Size.ofBytes 8 } =
      .ok (some (ep1AllocId, Size.ofBytes off))) :
    let ptr : Pointer (Option Provenance) :=
      ⟨Size.ofBytes (ep1TbBaseAddr + off), some (.concrete ep1AllocId tag)⟩
    let accessed := alloc.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes off)
      (Size.ofBytes 4) .Read bt.global.protectedTags .VisitChildrenOfAccessed
    let allocTB := alloc.setExtra accessed.tree
    let memTB : MemoryState Provenance BorrowTree Unit :=
      { mach.memory with
        live := (mach.memory.live.filter fun row => row.1 != ep1AllocId).push
          (ep1AllocId, LocalAllocation.mk .stack allocTB) }
    let refTB : AllocationAccessRef Provenance BorrowTree :=
      ⟨ep1AllocId, allocRange (Size.ofBytes off) (Size.ofBytes 4), allocTB⟩
    AllocationAccess.getPtrAlloc mach.memory ⟨mach, none⟩ ⟨Size.ofBytes 8⟩ ptr (Size.ofBytes 4)
        false none ep1PlaceAccessConfig.globalHooks (PlaceMachine.accessHooks ep1PlaceAccessConfig) =
      match accessed.status with
      | .Completed => ⟨memTB, ⟨mach, none⟩, some refTB, .ok (some refTB)⟩
      | errStatus =>
        let err := placeMachineTreeError errStatus
        ⟨memTB, ⟨mach, some err⟩, some refTB,
          .error (.hookFailure "beforeMemoryRead" (reprStr err))⟩ := by
  dsimp only
  have hSize4 : sizeAsI64 (Size.ofBytes 4) = .ok 4 := by decide
  have hResPtr :
      (PlaceMachine.accessHooks ep1PlaceAccessConfig).resolvePointer mach.memory ⟨mach, none⟩
        ⟨Size.ofBytes (ep1TbBaseAddr + off), some (.concrete ep1AllocId tag)⟩ 4 =
      ⟨⟨mach, none⟩, .ok (.ok ⟨ep1AllocId, Size.ofBytes off, .concrete tag⟩)⟩ := by
    unfold PlaceMachine.accessHooks ep1PlaceAccessConfig
    unfold_pm
    dsimp only
    rw [hPtrGetAlloc]
  have hRaw :
      MemoryLifecycle.getAllocRaw mach.memory ⟨mach, none⟩ ep1AllocId none
        ep1PlaceAccessConfig.globalHooks = ⟨mach.memory, ⟨mach, none⟩, .ok alloc⟩ := by
    simp [MemoryLifecycle.getAllocRaw, ep1PlaceAccessConfig, hFind]
  have hBefore :
      (PlaceMachine.accessHooks ep1PlaceAccessConfig).beforeAllocationAccess ⟨mach, none⟩ ep1AllocId =
        ⟨⟨mach, none⟩, .ok ()⟩ := by
    unfold PlaceMachine.accessHooks ep1PlaceAccessConfig; unfold_pm; rfl
  have hFourNeZero : ((4 : Int) != 0) = true := by decide
  have hBeforeRead :
      (PlaceMachine.accessHooks ep1PlaceAccessConfig).beforeMemoryRead ⟨mach, none⟩ alloc.extra
        ⟨Size.ofBytes (ep1TbBaseAddr + off), some (.concrete ep1AllocId tag)⟩ ep1AllocId
        (.concrete tag) (allocRange (Size.ofBytes off) (Size.ofBytes 4)) =
      PlaceMachine.memoryAccess ep1PlaceAccessConfig false ⟨mach, none⟩ alloc.extra ep1AllocId
        (.concrete tag) (allocRange (Size.ofBytes off) (Size.ofBytes 4)) := rfl
  have hMemAcc := ep1PlaceMemoryAccess_eq false mach alloc.extra tag off bt hNoRace hBt
  have hSetTB :
      ∀ (t : BorrowTree),
        mach.memory.setLiveAllocation ep1AllocId (alloc.setExtra t) =
        .ok { mach.memory with
              live := (mach.memory.live.filter fun row => row.1 != ep1AllocId).push
                (ep1AllocId, LocalAllocation.mk .stack (alloc.setExtra t)) } := fun t =>
    MemoryState.setLiveAllocation_of_find mach.memory ep1AllocId (LocalAllocation.mk .stack alloc) _ hFind
  unfold AllocationAccess.getPtrAlloc
  unfold_aa
  dsimp only [Id.run]
  rw [hSize4]
  simp only [bind, Bind.bind, pure, Pure.pure, hFourNeZero, ↓reduceIte, hResPtr, hRaw, hByteSz,
    hOffBounds.2.2.2, Bool.not_false, Bool.false_eq_true, hBefore, hBeforeRead, hMemAcc]
  generalize alloc.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes off) (Size.ofBytes 4)
      .Read bt.global.protectedTags .VisitChildrenOfAccessed = accessed
  rcases accessed with ⟨accTree, accLocs, accStatus⟩
  cases accStatus with
  | Completed =>
    simp only [hAny, ↓reduceIte, hSetTB accTree, Option.map_some]
  | _ =>
    simp only [hAny, ↓reduceIte, hSetTB accTree]

/-- Exact symbolic reduction of unmodified vendored `PlaceMachine.readImmediate ep1PlaceAccessConfig`
on a concrete-provenance `u32` indirect pointer into `ep1AllocId`: routes through unmodified
`PlaceMachine.accessHooks` → `AllocationAccess.getPtrAlloc` → `PlaceMachine.memoryAccess` →
`BorrowTree.performBorrowAccessRange` → `Allocation.readScalar`! -/
private theorem ep1PlaceReadImmediate_u32_concrete_eq
    (st : PlaceMachine.State Unit Unit) (alloc : Allocation Provenance BorrowTree)
    (tag : BorTag) (off : UInt64) (bt : MachineHooks.BorrowState)
    (hNoRace : st.machine.dataRace = none)
    (hBt : st.machine.borrowTracker = some bt)
    (hFind : st.machine.memory.live.find? (fun row => row.1 == ep1AllocId) =
      some (ep1AllocId, LocalAllocation.mk .stack alloc))
    (hAny : st.machine.memory.live.any (fun row => row.1 == ep1AllocId) = true)
    (hByteSz : alloc.byteSize = Size.ofBytes 16)
    (hOffBounds : (ep1TbBaseAddr + off).toNat ≥ ep1TbBaseAddr.toNat ∧
      (ep1TbBaseAddr + off - ep1TbBaseAddr) = off ∧
      off.toNat + 4 ≤ 16 ∧
      checkedBounds ⟨Size.ofBytes 8⟩ ep1AllocId (Size.ofBytes 16) (Size.ofBytes off) 4 .memoryAccess =
        .ok ())
    (hPtrGetAlloc : ∀ (hooks : Miri.Memory.AllocAddresses.AddressLookupHooks),
      ep1GlobalAddressState.ptrGetAlloc
        ⟨Size.ofBytes (ep1TbBaseAddr + off), .concrete ep1AllocId tag⟩ (Int64.ofInt 4) hooks
        { pointerSize := Size.ofBytes 8 } =
      .ok (some (ep1AllocId, Size.ofBytes off)))
    (hSub4 : (allocRange (Size.ofBytes off) (Size.ofBytes 4)).subrange
      (allocRange Size.ZERO (Size.ofBytes 4)) =
      .ok (allocRange (Size.ofBytes off) (Size.ofBytes 4))) :
    let u32Lay := translateTy ep1U32Ty emptyLayoutTable
    let op : OpTy Provenance :=
      ⟨.indirect ⟨⟨Size.ofBytes (ep1TbBaseAddr + off), some (.concrete ep1AllocId tag)⟩, .none, none⟩,
       u32Lay⟩
    let accessed := alloc.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes off)
      (Size.ofBytes 4) .Read bt.global.protectedTags .VisitChildrenOfAccessed
    let allocTB := alloc.setExtra accessed.tree
    let memTB : MemoryState Provenance BorrowTree Unit :=
      { st.machine.memory with
        live := (st.machine.memory.live.filter fun row => row.1 != ep1AllocId).push
          (ep1AllocId, LocalAllocation.mk .stack allocTB) }
    PlaceMachine.readImmediate ep1PlaceAccessConfig op st =
      match accessed.status with
      | .Completed =>
        match allocTB.readScalar annealTargetDataLayout
            (allocRange (Size.ofBytes off) (Size.ofBytes 4)) false with
        | .ok sc => .ok ⟨.scalar sc, u32Lay⟩ { st with machine := { st.machine with memory := memTB } }
        | .error e => .error (MemoryErrors.operand (.allocation e))
            { st with machine := { st.machine with memory := memTB } }
      | errStatus =>
        .error (placeMachineTreeError errStatus)
          { st with machine := { st.machine with memory := memTB } } := by
  dsimp only
  have hGetPtr := ep1GetPtrAlloc_eq st.machine alloc tag off bt hNoRace hBt hFind hAny hByteSz
    hOffBounds hPtrGetAlloc
  dsimp only at hGetPtr
  have hGhost : ep1PlaceAccessConfig.ghostMode = false := rfl
  have hGlobKind : ep1PlaceAccessConfig.globalKind = none := rfl
  have hGetPlace :
      getPlaceAlloc st.machine.memory ⟨st.machine, none⟩
        ⟨⟨⟨Size.ofBytes (ep1TbBaseAddr + off), some (.concrete ep1AllocId tag)⟩, .none, none⟩,
         localMemoryLayout (translateTy ep1U32Ty emptyLayoutTable)⟩
        ep1PlaceAccessConfig.runtime ep1PlaceAccessConfig.ghostMode ep1PlaceAccessConfig.globalKind
        ep1PlaceAccessConfig.globalHooks (PlaceMachine.accessHooks ep1PlaceAccessConfig)
        ep1PlaceAccessConfig.dynamicLayout =
      let accessed := alloc.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes off)
        (Size.ofBytes 4) .Read bt.global.protectedTags .VisitChildrenOfAccessed
      let allocTB := alloc.setExtra accessed.tree
      let memTB : MemoryState Provenance BorrowTree Unit :=
        { st.machine.memory with
          live := (st.machine.memory.live.filter fun row => row.1 != ep1AllocId).push
            (ep1AllocId, LocalAllocation.mk .stack allocTB) }
      let refTB : AllocationAccessRef Provenance BorrowTree :=
        ⟨ep1AllocId, allocRange (Size.ofBytes off) (Size.ofBytes 4), allocTB⟩
      match accessed.status with
      | .Completed => ⟨memTB, ⟨st.machine, none⟩, some refTB, .ok (some refTB)⟩
      | errStatus =>
        let err := placeMachineTreeError errStatus
        ⟨memTB, ⟨st.machine, some err⟩, some refTB,
          .error (.pointerAccess (.hookFailure "beforeMemoryRead" (reprStr err)))⟩ := by
    unfold getPlaceAlloc
    unfold_mo
    have hPtrSz : ep1PlaceAccessConfig.runtime.pointerSizeIn
        ep1PlaceAccessConfig.runtime.defaultAddressSpace = .ok (Size.ofBytes 8) := by decide
    have hLaySz : (localMemoryLayout (translateTy ep1U32Ty emptyLayoutTable)).size =
        Size.ofBytes 4 := by decide
    have hUnsized : (localMemoryLayout (translateTy ep1U32Ty emptyLayoutTable)).backendRepr.isUnsized =
        false := by decide
    simp only [Id.run, hUnsized, Bool.false_eq_true, ↓reduceIte, hPtrSz, Except.mapError,
      Except.bind, Except.pure, bind, Bind.bind, pure, Pure.pure, hLaySz, hGhost, hGlobKind, hGetPtr]
    generalize alloc.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes off) (Size.ofBytes 4)
        .Read bt.global.protectedTags .VisitChildrenOfAccessed = accessed
    rcases accessed with ⟨accTree, accLocs, accStatus⟩
    cases accStatus <;> rfl
  dsimp only at hGetPlace
  have hReadOp :
      Miri.Interpreter.readImmediate st.machine.memory ⟨st.machine, none⟩
        (.indirect ⟨⟨Size.ofBytes (ep1TbBaseAddr + off), some (.concrete ep1AllocId tag)⟩, .none, none⟩)
        (localMemoryLayout (translateTy ep1U32Ty emptyLayoutTable))
        ep1PlaceAccessConfig.runtime ep1PlaceAccessConfig.ghostMode ep1PlaceAccessConfig.globalKind
        ep1PlaceAccessConfig.globalHooks (PlaceMachine.accessHooks ep1PlaceAccessConfig)
        ep1PlaceAccessConfig.dynamicLayout =
      let accessed := alloc.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes off)
        (Size.ofBytes 4) .Read bt.global.protectedTags .VisitChildrenOfAccessed
      let allocTB := alloc.setExtra accessed.tree
      let memTB : MemoryState Provenance BorrowTree Unit :=
        { st.machine.memory with
          live := (st.machine.memory.live.filter fun row => row.1 != ep1AllocId).push
            (ep1AllocId, LocalAllocation.mk .stack allocTB) }
      let refTB : AllocationAccessRef Provenance BorrowTree :=
        ⟨ep1AllocId, allocRange (Size.ofBytes off) (Size.ofBytes 4), allocTB⟩
      match accessed.status with
      | .Completed =>
        match allocTB.readScalar annealTargetDataLayout
            (allocRange (Size.ofBytes off) (Size.ofBytes 4)) false with
        | .ok sc => ⟨memTB, ⟨st.machine, none⟩, some refTB,
            .ok ⟨.scalar sc, localMemoryLayout (translateTy ep1U32Ty emptyLayoutTable)⟩⟩
        | .error e => ⟨memTB, ⟨st.machine, none⟩, some refTB, .error (.allocation e)⟩
      | errStatus =>
        let err := placeMachineTreeError errStatus
        ⟨memTB, ⟨st.machine, some err⟩, some refTB,
          .error (.pointerAccess (.hookFailure "beforeMemoryRead" (reprStr err)))⟩ := by
    unfold Miri.Interpreter.readImmediate Miri.Interpreter.readImmediateRaw
      Miri.Interpreter.readImmediateFromMplaceRaw
    unfold_mo
    have hRepr : (localMemoryLayout (translateTy ep1U32Ty emptyLayoutTable)).backendRepr =
        .Scalar (.Initialized (value := .Int .I32 false)
          (validRange := ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 (2 ^ 32 - 1)⟩)) := by decide
    have hPrimSz : Miri.ABI.Primitive.size (.Int .I32 false) ep1PlaceAccessConfig.runtime =
        .ok (Size.ofBytes 4) := by decide
    have hLaySz : (localMemoryLayout (translateTy ep1U32Ty emptyLayoutTable)).size =
        Size.ofBytes 4 := by decide
    simp only [Id.run, hRepr, Miri.ABI.BackendRepr.isUnsized, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, hGetPlace]
    generalize alloc.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes off) (Size.ofBytes 4)
        .Read bt.global.protectedTags .VisitChildrenOfAccessed = accessed
    rcases accessed with ⟨accTree, accLocs, accStatus⟩
    cases accStatus with
    | Completed =>
      simp only [hPrimSz, hLaySz, Except.mapError, Except.bind, Except.pure,
        bind, Bind.bind, pure, Pure.pure, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        hSub4]
      dsimp only [ep1PlaceAccessConfig, annealRuntimeDataLayout]
      cases (alloc.setExtra accTree).readScalar annealTargetDataLayout
          (allocRange (Size.ofBytes off) (Size.ofBytes 4)) false <;> rfl
    | _ => rfl
  unfold PlaceMachine.readImmediate
  unfold_pm
  simp only [get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, hReadOp]
  dsimp only [ep1PlaceAccessConfig]
  generalize alloc.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes off) (Size.ofBytes 4)
      .Read bt.global.protectedTags .VisitChildrenOfAccessed = accessed
  rcases accessed with ⟨accTree, accLocs, accStatus⟩
  cases accStatus with
  | Completed =>
    cases (alloc.setExtra accTree).readScalar annealTargetDataLayout
        (allocRange (Size.ofBytes off) (Size.ofBytes 4)) false <;> rfl
  | _ => rfl

/-- Modular Stage 2b (dangling integer pointer): exact reduction of unmodified
`PlaceMachine.writeMemory ep1PlaceAccessConfig` on a provenance-free pointer `⟨0x1000, none⟩`. -/
private theorem ep1PlaceWriteMemory_dangling_eq
    (st : PlaceMachine.State Unit Unit) (val : Miri.Memory.Scalar Provenance)
    (hValSz : val.size = Size.ofBytes 4) (hValInt : val.isPointer = false) :
    let mp : MPlaceTy Provenance :=
      ⟨⟨⟨Size.ofBytes ep1TbBaseAddr, none⟩, .none, none⟩, translateTy ep1U32Ty emptyLayoutTable⟩
    PlaceMachine.writeMemory ep1PlaceAccessConfig (fun _ => false) (.scalar val) mp st =
      .error
        (MemoryErrors.operand
          (.pointerAccess (.access (.danglingIntegerPointer ep1TbBaseAddr 4 .memoryAccess))))
        st := by
  dsimp only
  have hGetPtr :
      AllocationAccess.getPtrAllocMut st.machine.memory ⟨st.machine, none⟩ ⟨Size.ofBytes 8⟩
        ⟨Size.ofBytes ep1TbBaseAddr, none⟩ (Size.ofBytes 4) false none
        ep1PlaceAccessConfig.globalHooks (PlaceMachine.accessHooks ep1PlaceAccessConfig) =
      ⟨st.machine.memory, ⟨st.machine, none⟩, none,
        .error (.access (.danglingIntegerPointer ep1TbBaseAddr 4 .memoryAccess))⟩ := by
    have hSize4 : sizeAsI64 (Size.ofBytes 4) = .ok 4 := by decide
    have hRes :
        (PlaceMachine.accessHooks ep1PlaceAccessConfig).resolvePointer st.machine.memory
          ⟨st.machine, none⟩ ⟨Size.ofBytes ep1TbBaseAddr, none⟩ 4 =
        ⟨⟨st.machine, none⟩, .ok (.error ep1TbBaseAddr)⟩ := by
      unfold PlaceMachine.accessHooks ep1PlaceAccessConfig; unfold_pm; rfl
    have hFourNeZero : ((4 : Int) != 0) = true := by decide
    unfold AllocationAccess.getPtrAllocMut
    unfold_aa
    dsimp only [Id.run]
    rw [hSize4]
    simp only [bind, Bind.bind, pure, Pure.pure, hFourNeZero, ↓reduceIte, hRes]
  have hGhost : ep1PlaceAccessConfig.ghostMode = false := rfl
  have hGlobKind : ep1PlaceAccessConfig.globalKind = none := rfl
  have hGetPlace :
      getPlaceAllocMut st.machine.memory ⟨st.machine, none⟩
        ⟨⟨⟨Size.ofBytes ep1TbBaseAddr, none⟩, .none, none⟩,
         localMemoryLayout (translateTy ep1U32Ty emptyLayoutTable)⟩
        ep1PlaceAccessConfig.runtime ep1PlaceAccessConfig.ghostMode ep1PlaceAccessConfig.globalKind
        ep1PlaceAccessConfig.globalHooks (PlaceMachine.accessHooks ep1PlaceAccessConfig)
        ep1PlaceAccessConfig.dynamicLayout =
      ⟨st.machine.memory, ⟨st.machine, none⟩, none,
        .error (.pointerAccess (.access (.danglingIntegerPointer ep1TbBaseAddr 4 .memoryAccess)))⟩ := by
    unfold getPlaceAllocMut
    unfold_mo
    have hPtrSz : ep1PlaceAccessConfig.runtime.pointerSizeIn
        ep1PlaceAccessConfig.runtime.defaultAddressSpace = .ok (Size.ofBytes 8) := by decide
    have hLaySz : (localMemoryLayout (translateTy ep1U32Ty emptyLayoutTable)).size =
        Size.ofBytes 4 := by decide
    have hUnsized : (localMemoryLayout (translateTy ep1U32Ty emptyLayoutTable)).backendRepr.isUnsized =
        false := by decide
    simp only [Id.run, hUnsized, Bool.false_eq_true, ↓reduceIte, hPtrSz, Except.mapError,
      Except.bind, Except.pure, bind, Bind.bind, pure, Pure.pure, hLaySz, hGhost, hGlobKind, hGetPtr]
  have hWriteOp :
      writeImmediateToMplaceNoValidate st.machine.memory ⟨st.machine, none⟩ (.scalar val)
        ⟨⟨⟨Size.ofBytes ep1TbBaseAddr, none⟩, .none, none⟩,
         localMemoryLayout (translateTy ep1U32Ty emptyLayoutTable)⟩
        ep1PlaceAccessConfig.runtime ep1PlaceAccessConfig.ghostMode ep1PlaceAccessConfig.globalKind
        ep1PlaceAccessConfig.globalHooks (PlaceMachine.accessHooks ep1PlaceAccessConfig)
        ep1PlaceAccessConfig.dynamicLayout (fun _ => false) =
      ⟨st.machine.memory, ⟨st.machine, none⟩, none,
        .error (.pointerAccess (.access (.danglingIntegerPointer ep1TbBaseAddr 4 .memoryAccess)))⟩ := by
    unfold writeImmediateToMplaceNoValidate
    unfold_mo
    have hRepr : (localMemoryLayout (translateTy ep1U32Ty emptyLayoutTable)).backendRepr =
        .Scalar (.Initialized (value := .Int .I32 false)
          (validRange := ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 (2 ^ 32 - 1)⟩)) := by decide
    have hPrimSz : Miri.ABI.Primitive.size (.Int .I32 false) ep1PlaceAccessConfig.runtime =
        .ok (Size.ofBytes 4) := by decide
    simp only [Id.run, hRepr, Miri.ABI.BackendRepr.isUnsized, Bool.false_eq_true, ↓reduceIte,
      Miri.ABI.Scalar.primitive, hPrimSz, Except.mapError, bind, Bind.bind, Except.bind,
      hValSz, bne_self_eq_false, hValInt, pure, Pure.pure, Except.pure, hGetPlace]
  unfold PlaceMachine.writeMemory
  unfold_pm
  simp only [get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, hWriteOp]
  rfl

/-- Helper reading local `_0`'s `u32` bits from a vendored `PlaceMachine.State Unit Unit`. -/
private def vendoredActiveLocal0Bits (st : PlaceMachine.State Unit Unit) : Option Nat :=
  match st.stack.currentFrame? with
  | none => none
  | some fr =>
    match fr.locals[0]? with
    | none => none
    | some slot =>
      match slot.value with
      | .live (.immediate (.scalar sc)) =>
        match sc.toBits (Size.ofBytes 4) with
        | .ok bv => some bv.toNat
        | .error _ => none
      | _ => none

/-- Modular helper: exact reduction of unmodified vendored `Miri.Interpreter.evalPlace`
under `ep1VendoredPlaceHooks` (`PlaceMachine.placeHooks`) on a dereferenced pointer local
`(*_lid)`. -/
private theorem ep1EvalPlace_deref_local_eq
    (st : PlaceMachine.State Unit Unit) (fr : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (lid : Miri.MIR.LocalId) (sc : Miri.Memory.Scalar Provenance)
    (ptr : Pointer (Option Provenance)) (lay : LocalLayout)
    (hFrames : st.stack.frames = #[fr])
    (hNoRace : fr.extra.dataRace = none)
    (hGetLocal : fr.getLocal lid = .ok { value := .live (.immediate (.scalar sc)), layout := some lay })
    (hSized : lay.layout.isSized = true)
    (hPtr : sc.toPointer annealTargetDataLayout = .ok ptr) :
    Miri.Interpreter.evalPlace ep1VendoredPlaceHooks () ⟨lid, #[.Deref]⟩ false st =
      .ok ⟨.memory ⟨ptr, .none, none⟩, translateTy ep1U32Ty emptyLayoutTable⟩ st := by
  have hCur : st.stack.currentFrame? = some fr := by
    unfold Stack.currentFrame?; rw [hFrames]; rfl
  have hIdx : st.stack.frameIndex = .ok 0 := by
    unfold Stack.frameIndex; rw [hFrames]; rfl
  have hGetOp : fr.getLocalOperand lid = .ok (.immediate (.scalar sc)) := by
    unfold Frame.getLocalOperand
    simp only [hGetLocal]
    rfl
  unfold Miri.Interpreter.evalPlace Miri.Interpreter.localToPlace Miri.Interpreter.placeLayoutOfLocal
    Miri.Interpreter.projectRuntimePlace ep1VendoredPlaceHooks PlaceMachine.placeHooks
    ep1PlaceCompilerHooks PlaceMachine.localToOpCore MachineHooks.afterLocalRead
  unfold MachineHooks.currentFrame
  unfold_pl
  simp only [get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    Except.mapError, hCur, hGetLocal, hSized, ↓reduceIte, hIdx,
    Bool.false_and, Bool.false_eq_true, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil,
    beq_self_eq_true, hGetOp, Bool.not_true, hNoRace, hPtr]

/-- Modular helper: exact reduction of unmodified vendored `Miri.Interpreter.evalPlace`
under `ep1VendoredPlaceHooks` (`PlaceMachine.placeHooks`) on a whole sized local `⟨lid, #[]⟩`. -/
private theorem ep1EvalPlace_whole_local_eq
    (st : PlaceMachine.State Unit Unit) (fr : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (lid : Miri.MIR.LocalId) (v : LocalValue Provenance) (lay : LocalLayout)
    (hFrames : st.stack.frames = #[fr])
    (hGetLocal : fr.getLocal lid = .ok { value := v, layout := some lay })
    (hSized : lay.layout.isSized = true) :
    Miri.Interpreter.evalPlace ep1VendoredPlaceHooks () ⟨lid, #[]⟩ false st =
      .ok ⟨.local 0 lid none fr.localsIdentity, lay⟩ st := by
  have hCur : st.stack.currentFrame? = some fr := by
    unfold Stack.currentFrame?; rw [hFrames]; rfl
  have hIdx : st.stack.frameIndex = .ok 0 := by
    unfold Stack.frameIndex; rw [hFrames]; rfl
  unfold Miri.Interpreter.evalPlace Miri.Interpreter.localToPlace Miri.Interpreter.placeLayoutOfLocal
    ep1VendoredPlaceHooks PlaceMachine.placeHooks ep1PlaceCompilerHooks MachineHooks.currentFrame
  unfold_pl
  simp only [get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    Except.mapError, hCur, hGetLocal, hSized, ↓reduceIte, hIdx,
    Bool.false_and, Bool.false_eq_true, ← Array.forIn_toList, List.forIn_nil]

/-- Modular helper: exact reduction of unmodified vendored `Miri.Interpreter.writePlaceImmediate`
under `ep1VendoredPlaceHooks` on a sized memory place (delegates directly to
`PlaceMachine.writeMemory ep1PlaceAccessConfig`). -/
private theorem ep1WritePlaceImmediate_memory_eq
    (st : PlaceMachine.State Unit Unit) (val : Immediate Provenance)
    (mp : MemPlace Provenance) (lay : LocalLayout)
    (hSized : lay.layout.isSized = true) :
    Miri.Interpreter.writePlaceImmediate ep1VendoredPlaceHooks () val ⟨.memory mp, lay⟩ st =
      PlaceMachine.writeMemory ep1PlaceAccessConfig (fun _ => false) val ⟨mp, lay⟩ st := by
  unfold Miri.Interpreter.writePlaceImmediate Miri.Interpreter.writePlaceImmediateNoValidate
    Miri.Interpreter.asMplaceOrMutableLocal ep1VendoredPlaceHooks PlaceMachine.placeHooks
    ep1PlaceCompilerHooks
  simp only [hSized, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  cases PlaceMachine.writeMemory ep1PlaceAccessConfig (fun _ => false) val ⟨mp, lay⟩ st with
  | ok u s => cases u; rfl
  | error e s => rfl

/-- Modular helper: exact reduction of unmodified vendored `Miri.Interpreter.writePlaceImmediate`
under `ep1VendoredPlaceHooks` on a whole sized immediate local (delegates directly to
`placeWriteLocalImmediate` → `Frame.setLocalOperand` → `MachineHooks.afterLocalWrite`). -/
private theorem ep1WritePlaceImmediate_local_eq
    (st : PlaceMachine.State Unit Unit) (fr fr' : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (lid : Miri.MIR.LocalId) (oldImm val : Immediate Provenance) (lay : LocalLayout)
    (hFrames : st.stack.frames = #[fr])
    (hNoRace : fr'.extra.dataRace = none)
    (hSized : lay.layout.isSized = true)
    (hGetOp : fr.getLocalOperand lid = .ok (.immediate oldImm))
    (hSetOp : fr.setLocalOperand lid (.immediate val) = .ok fr') :
    Miri.Interpreter.writePlaceImmediate ep1VendoredPlaceHooks () val
        ⟨.local 0 lid none fr.localsIdentity, lay⟩ st =
      .ok () { st with stack := { frames := #[fr'] } } := by
  have hCur : st.stack.currentFrame? = some fr := by
    unfold Stack.currentFrame?; rw [hFrames]; rfl
  have hIdx : st.stack.frameIndex = .ok 0 := by
    unfold Stack.frameIndex; rw [hFrames]; rfl
  have hSetFr :
      MachineHooks.setCurrentFrame fr' st = .ok () { st with stack := { frames := #[fr'] } } := by
    unfold MachineHooks.setCurrentFrame
    simp only [get, getThe, MonadStateOf.get, set, MonadStateOf.set,
      bind, Bind.bind, EStateM.bind, EStateM.get, hFrames]
    rfl
  have hBackFr : #[fr][#[fr].size - 1]? = some fr := rfl
  have hBackFr' : #[fr'][#[fr'].size - 1]? = some fr' := rfl
  unfold Miri.Interpreter.writePlaceImmediate Miri.Interpreter.writePlaceImmediateNoValidate
    Miri.Interpreter.asMplaceOrMutableLocal ep1VendoredPlaceHooks PlaceMachine.placeHooks
    ep1PlaceCompilerHooks
  unfold Miri.Interpreter.placeWriteLocalImmediate MachineHooks.afterLocalWrite
  unfold MachineHooks.currentFrame
  unfold_pl
  simp only [get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    Except.mapError, hSized, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Option.isSome_none, hIdx, bne_self_eq_false, hFrames, hBackFr, hGetOp, hSetOp, hSetFr,
    Stack.currentFrame?, Array.back?, hBackFr', hNoRace]

/-- **Vendored-Native Tree-Borrows `PlaceMachine` + `PlaceHooks` + `GlobalAddressState` +
`beforeStackPopWithEnsure` + `Step.step` + `translateBody` End-to-End Witness
(`witness_vendored_placeMachine_tb_step_positive_and_ub_refutations`)**:
Executes REAL `LeanMiriSpec.Correspondence.translateBody ep1BodyTbDerefWriteAndRead`
(`(*_1) = 99u32; _0 = copy (*_2); return`) through **unmodified `Miri.Interpreter.Step.step`**
with **unmodified vendored `PlaceMachine.placeHooks` / `evalPlace` / `placeToOp` /
`writePlaceImmediate` / `GlobalAddressState.ptrGetAlloc` / `PlaceMachine.{writeMemory,
readImmediate, accessHooks, memoryAccess}` / `MachineHooks.beforeStackPopWithEnsure` /
`ControlFlow.{evalTerminator, returnFromCurrentFrame}` / `Frame.getLocalOperand` /
`Stack.popFrame`** over `PlaceMachine.State Unit Unit` (ZERO custom TB hooks):
1. **Positive (`_1 = tag 3 @ 8`, `_2 = tag 2 @ 0`, active `FnEntry` frame protectors `tag 2`, `tag 3`)**:
   - Step 1 (`(*_1) = 99u32`) evaluates `(*_1)` via `evalPlace` (`PlaceMachine.placeHooks`), resolves
     pointer via `GlobalAddressState.ptrGetAlloc`, passes `PlaceMachine.writeMemory` +
     `PlaceMachine.memoryAccess`, and writes `99u32` into `[8..12)`.
   - Step 2 (`_0 = copy (*_2)`) evaluates `_0` and `(*_2)` via `evalPlace` + `placeToOp`, passes
     `PlaceMachine.readImmediate` + `PlaceMachine.memoryAccess`, and writes `42u32` into `_0` via
     `writePlaceImmediate` (`vendoredActiveLocal0Bits mid = some 42`).
   - Step 3 (`return`) reads `_0` via `Frame.getLocalOperand 0`, releases BOTH `FnEntry` protectors
     (`tag 2`, `tag 3`) via **unmodified `MachineHooks.beforeStackPopWithEnsure`** (`releaseProtector`
     + `GlobalState.endCall`), and pops the frame via `Stack.popFrame` (`final.stack.frames = #[]`).
   - Post-return observations confirm: live bytes `[8..12)` = `99u32` and `[0..4)` = `42u32`,
     `protectedTags` no longer protects `tag 2` or `tag 3`, AND a subsequent foreign write by
     `tag 1 @ [0..4)` via unmodified `BorrowTree.performBorrowAccessRange` NOW SUCCEEDS
     (`.Completed`) — whereas the exact same foreign write before return was `ProtectedDisabled` UB!
2. **Negative #1 (Protected Foreign Write UB + Committed Tree + `↔` Refutation)**:
   `_1 = tag 1 @ 0` faults INSIDE unmodified `PlaceMachine.writeMemory` → `PlaceMachine.accessHooks`
   → `PlaceMachine.memoryAccess` with exact `ProtectedDisabled .Frozen` UB and committed tree.
3. **Negative #2 (Frozen Local Write UB + Committed Tree + `↔` Refutation)**:
   `_1 = tag 2 @ 0` faults INSIDE unmodified `PlaceMachine.writeMemory` → `PlaceMachine.accessHooks`
   → `PlaceMachine.memoryAccess` with exact `ChildAccessForbidden .Frozen` UB and committed tree.
4. **Negative #3 (Provenance-Free Dangling Integer Pointer UB + `↔` Refutation)**:
   `_1 = ⟨0x1000, none⟩` faults INSIDE unmodified `PlaceMachine.writeMemory` →
   `AllocationAccess.getPtrAllocMut` with `danglingIntegerPointer`.
5. **Negative #4 (Dead Return Local `_0` on `return` + `↔` Refutation)**:
   At the `return` terminator with `_0 = .dead`, `Step.step` → `ControlFlow.returnFromCurrentFrame`
   → `Frame.getLocalOperand 0` fails closed with `.stack (.localExpectedLive 0)`. -/
theorem witness_vendored_placeMachine_tb_step_positive_and_ub_refutations :
    let initOk := ep1InitVendoredPlaceState (some (.concrete ep1AllocId ep1Tag3)) 8
    let initProtUB := ep1InitVendoredPlaceState (some (.concrete ep1AllocId ep1Tag1)) 0
    let initFrozUB := ep1InitVendoredPlaceState (some (.concrete ep1AllocId ep1Tag2)) 0
    let initDanglingUB := ep1InitVendoredPlaceState none 0
    let deadRetFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra :=
      { body := translateBody ep1BodyTbDerefWriteAndRead
        bodyIdentity := BodyIdentity.ofCanonicalIndex 0
        functionInstance := ⟨.Item 0, #[]⟩
        extra := { borrowTracker := some ep1FrameBorrowState, catchUnwind := none,
                   userRelevance := 0, dataRace := none }
        returnContinuation := .stop false
        returnPlace := .frameLocal 0 0 none (translateTy ep1U32Ty emptyLayoutTable)
          (LocalsIdentity.ofAllocationToken 0)
        localsIdentity := LocalsIdentity.ofAllocationToken 0
        locals :=
          #[ { value := .dead, layout := some (translateTy ep1U32Ty emptyLayoutTable) },
             { value := .live (.immediate (.scalar (ep1VendoredPtrScalar (some (.concrete ep1AllocId ep1Tag3)) 8))),
               layout := some (translateTy ep1MutPtrU32Ty emptyLayoutTable) },
             { value := .live (.immediate (.scalar (ep1VendoredPtrScalar (some (.concrete ep1AllocId ep1Tag2)) 0))),
               layout := some (translateTy ep1MutPtrU32Ty emptyLayoutTable) } ]
        vaList := #[]
        trackCallerArg := none
        location := .mir ⟨0, 2⟩ }
    let initDeadRetUB : PlaceMachine.State Unit Unit :=
      { initOk with stack := { frames := #[deadRetFrame] } }
    let stProt := BorrowTree.BorrowTreeAccessStatus.AccessFailure ⟨0, 4⟩
      (.TransitionError 1 (.ProtectedDisabled .Frozen))
    let stFroz := BorrowTree.BorrowTreeAccessStatus.AccessFailure ⟨0, 4⟩
      (.TransitionError 1 (.ChildAccessForbidden .Frozen))
    let tProt := (ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag1) Size.ZERO
      (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).tree
    let tFroz := (ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag2) Size.ZERO
      (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).tree
    AnnealExactWP
      (ExactAction.seq (miriStepAction ep1VendoredPlaceStepHooks ())
        (miriStepAction ep1VendoredPlaceStepHooks ()))
      (fun more mid => more = true ∧ vendoredActiveLocal0Bits mid = some 42)
      (fun _ _ => False) initOk ∧
    AnnealExactWP (miriRunFuelAction ep1VendoredPlaceStepHooks () 4)
      (fun _ final =>
        final.stack.frames = #[] ∧
        (∃ bt, final.machine.borrowTracker = some bt ∧
          bt.global.protectedTags.contains ep1Tag2 = false ∧
          bt.global.protectedTags.contains ep1Tag3 = false ∧
          ∃ a, lookupLiveAllocMem final.machine.memory ep1AllocId = some a ∧
            (a.extra.performBorrowAccessRange (.concrete ep1Tag1) Size.ZERO (Size.ofBytes 4)
              .Write bt.global.protectedTags .VisitChildrenOfAccessed).status = .Completed ∧
            AnnealExactWP (miriObserveScalarAction annealTargetDataLayout
                (allocRange (Size.ofBytes 8) (Size.ofBytes 4)) false)
              (fun sc _ => sc.toBits (Size.ofBytes 4) = .ok (BitVec.ofNat 128 99))
              (fun _ _ => False) a ∧
            AnnealExactWP (miriObserveScalarAction annealTargetDataLayout
                (allocRange Size.ZERO (Size.ofBytes 4)) false)
              (fun sc _ => sc.toBits (Size.ofBytes 4) = .ok (BitVec.ofNat 128 42))
              (fun _ _ => False) a))
      (fun _ _ => False) initOk ∧
    AnnealExactWP (miriStepAction ep1VendoredPlaceStepHooks ())
      (fun _ _ => False)
      (fun err after =>
        err = .undefinedBehavior s!"Tree Borrows: {reprStr stProt}" ∧
        lookupLiveAllocMem after.machine.memory ep1AllocId =
          some (ep1VendoredTbAlloc.setExtra tProt))
      initProtUB ∧
    ¬ AnnealExactWP (miriStepAction ep1VendoredPlaceStepHooks ())
      (fun _ _ => True) (fun _ _ => False) initProtUB ∧
    AnnealExactWP (miriStepAction ep1VendoredPlaceStepHooks ())
      (fun _ _ => False)
      (fun err after =>
        err = .undefinedBehavior s!"Tree Borrows: {reprStr stFroz}" ∧
        lookupLiveAllocMem after.machine.memory ep1AllocId =
          some (ep1VendoredTbAlloc.setExtra tFroz))
      initFrozUB ∧
    ¬ AnnealExactWP (miriStepAction ep1VendoredPlaceStepHooks ())
      (fun _ _ => True) (fun _ _ => False) initFrozUB ∧
    AnnealExactWP (miriStepAction ep1VendoredPlaceStepHooks ())
      (fun _ _ => False)
      (fun err _ =>
        err = MemoryErrors.operand
          (.pointerAccess (.access (.danglingIntegerPointer ep1TbBaseAddr 4 .memoryAccess))))
      initDanglingUB ∧
    ¬ AnnealExactWP (miriStepAction ep1VendoredPlaceStepHooks ())
      (fun _ _ => True) (fun _ _ => False) initDanglingUB ∧
    AnnealExactWP (miriStepAction ep1VendoredPlaceStepHooks ())
      (fun _ _ => False)
      (fun err _ => err = .stack (.localExpectedLive 0))
      initDeadRetUB ∧
    ¬ AnnealExactWP (miriStepAction ep1VendoredPlaceStepHooks ())
      (fun _ _ => True) (fun _ _ => False) initDeadRetUB := by
  dsimp only
  have hW1 :
      (ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag1) Size.ZERO
        (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).status =
      .AccessFailure ⟨0, 4⟩ (.TransitionError 1 (.ProtectedDisabled .Frozen)) := by
    rw [performBorrowAccessRangeLMU.eq_src]; kernel_rfl
  have hW2 :
      (ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag2) Size.ZERO
        (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).status =
      .AccessFailure ⟨0, 4⟩ (.TransitionError 1 (.ChildAccessForbidden .Frozen)) := by
    rw [performBorrowAccessRangeLMU.eq_src]; kernel_rfl
  have hW3 :
      (ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag3) (Size.ofBytes 8)
        (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).status = .Completed := by
    rw [performBorrowAccessRangeLMU.eq_src]; kernel_rfl
  have hR2AfterW3 :
      ((ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag3) (Size.ofBytes 8)
          (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).tree.performBorrowAccessRange
        (.concrete ep1Tag2) Size.ZERO (Size.ofBytes 4) .Read ep1Prot23
        .VisitChildrenOfAccessed).status = .Completed := by
    rw [performBorrowAccessRangeLMU.eq_src]; kernel_rfl
  have hRel2StatusClosed :
      (((ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag3) (Size.ofBytes 8)
          (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).tree.performBorrowAccessRange
        (.concrete ep1Tag2) (Size.ofBytes 0) (Size.ofBytes 4) .Read ep1Prot23
        .VisitChildrenOfAccessed).tree.releaseProtector ep1Tag2 ep1Prot23).status = .Released := by
    rw [releaseProtectorLMU.eq_src, performBorrowAccessRangeLMU.eq_src]
    kernel_rfl
  have hRel3StatusClosed :
      ((((ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag3) (Size.ofBytes 8)
          (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).tree.performBorrowAccessRange
        (.concrete ep1Tag2) (Size.ofBytes 0) (Size.ofBytes 4) .Read ep1Prot23
        .VisitChildrenOfAccessed).tree.releaseProtector ep1Tag2 ep1Prot23).tree.releaseProtector
        ep1Tag3 ep1Prot23).status = .Released := by
    rw [releaseProtectorLMU.eq_src, performBorrowAccessRangeLMU.eq_src]
    kernel_rfl
  have hPostRetW1Closed :
      (((((ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag3) (Size.ofBytes 8)
          (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).tree.performBorrowAccessRange
        (.concrete ep1Tag2) (Size.ofBytes 0) (Size.ofBytes 4) .Read ep1Prot23
        .VisitChildrenOfAccessed).tree.releaseProtector ep1Tag2 ep1Prot23).tree.releaseProtector
        ep1Tag3 ep1Prot23).tree.performBorrowAccessRange (.concrete ep1Tag1) Size.ZERO
        (Size.ofBytes 4) .Write ((ep1Prot23.remove ep1Tag2).remove ep1Tag3)
        .VisitChildrenOfAccessed).status = .Completed := by
    rw [performBorrowAccessRangeLMU.eq_src, releaseProtectorLMU.eq_src]
    kernel_rfl
  have hPtrGet0 : ∀ (tag : BorTag) (hooks : Miri.Memory.AllocAddresses.AddressLookupHooks),
      ep1GlobalAddressState.ptrGetAlloc
        ⟨Size.ofBytes (ep1TbBaseAddr + 0), .concrete ep1AllocId tag⟩ (Int64.ofInt 4) hooks
        { pointerSize := Size.ofBytes 8 } =
      .ok (some (ep1AllocId, Size.ofBytes 0)) := fun _ _ => by kernel_rfl
  have hPtrGet8 : ∀ (tag : BorTag) (hooks : Miri.Memory.AllocAddresses.AddressLookupHooks),
      ep1GlobalAddressState.ptrGetAlloc
        ⟨Size.ofBytes (ep1TbBaseAddr + 8), .concrete ep1AllocId tag⟩ (Int64.ofInt 4) hooks
        { pointerSize := Size.ofBytes 8 } =
      .ok (some (ep1AllocId, Size.ofBytes 8)) := fun _ _ => by kernel_rfl
  have hBounds0 :
      (ep1TbBaseAddr + 0).toNat ≥ ep1TbBaseAddr.toNat ∧
      (ep1TbBaseAddr + 0 - ep1TbBaseAddr) = 0 ∧
      (0 : UInt64).toNat + 4 ≤ 16 ∧
      checkedBounds ⟨Size.ofBytes 8⟩ ep1AllocId (Size.ofBytes 16) (Size.ofBytes 0) 4 .memoryAccess =
        .ok () := ⟨by decide, by decide, by decide, by kernel_rfl⟩
  have hBounds8 :
      (ep1TbBaseAddr + 8).toNat ≥ ep1TbBaseAddr.toNat ∧
      (ep1TbBaseAddr + 8 - ep1TbBaseAddr) = 8 ∧
      (8 : UInt64).toNat + 4 ≤ 16 ∧
      checkedBounds ⟨Size.ofBytes 8⟩ ep1AllocId (Size.ofBytes 16) (Size.ofBytes 8) 4 .memoryAccess =
        .ok () := ⟨by decide, by decide, by decide, by kernel_rfl⟩
  have hSc99 :
      Miri.Memory.Scalar.fromUInt (Prov := Provenance) (BitVec.ofNat 128 99) (Size.ofBytes 4) =
      .ok (mkMiriU32Scalar 99) := by kernel_rfl
  have hSc99Sz : (mkMiriU32Scalar 99).size = Size.ofBytes 4 := by kernel_rfl
  have hSc99Int : (mkMiriU32Scalar 99).isPointer = false := by kernel_rfl
  have hPtrLaySized : (translateTy ep1MutPtrU32Ty emptyLayoutTable).layout.isSized = true := by decide
  have hU32LaySized : (translateTy ep1U32Ty emptyLayoutTable).layout.isSized = true := by decide
  have hWrite99OnBase :
      ∃ (alloc99 : Allocation Provenance BorrowTree),
        Allocation.writeScalar annealTargetDataLayout
          (allocRange (Size.ofBytes 8) (Size.ofBytes 4))
          (mkMiriU32Scalar 99)
          (ep1VendoredTbAlloc.setExtra
            (ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag3) (Size.ofBytes 8)
              (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).tree) =
        .ok () alloc99 ∧
        alloc99.byteSize = Size.ofBytes 16 ∧
        alloc99.readScalar annealTargetDataLayout (allocRange Size.ZERO (Size.ofBytes 4)) false =
          .ok (mkMiriU32Scalar 42) ∧
        alloc99.readScalar annealTargetDataLayout (allocRange (Size.ofBytes 8) (Size.ofBytes 4))
          false = .ok (mkMiriU32Scalar 99) ∧
        alloc99.extra =
          (ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag3) (Size.ofBytes 8)
            (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).tree := by
    have hCore :
        ∃ (a0 : Allocation Provenance Unit),
          Allocation.writeScalar annealTargetDataLayout
            (allocRange (Size.ofBytes 8) (Size.ofBytes 4))
            (mkMiriU32Scalar 99) ep1BaseAlloc16 = .ok () a0 ∧
          a0.byteSize = Size.ofBytes 16 ∧
          a0.readScalar annealTargetDataLayout (allocRange Size.ZERO (Size.ofBytes 4)) false =
            .ok (mkMiriU32Scalar 42) ∧
          a0.readScalar annealTargetDataLayout (allocRange (Size.ofBytes 8) (Size.ofBytes 4))
            false = .ok (mkMiriU32Scalar 99) := by
      cases hW : Allocation.writeScalar annealTargetDataLayout
          (allocRange (Size.ofBytes 8) (Size.ofBytes 4))
          (mkMiriU32Scalar 99) ep1BaseAlloc16 with
      | error e _ =>
        have hOk : (match Allocation.writeScalar annealTargetDataLayout
            (allocRange (Size.ofBytes 8) (Size.ofBytes 4))
            (mkMiriU32Scalar 99) ep1BaseAlloc16 with
            | .ok () _ => true | .error _ _ => false) = true := by kernel_rfl
        rw [hW] at hOk; cases hOk
      | ok u a0 =>
        cases u
        refine ⟨a0, rfl, ?_, ?_, ?_⟩
        · have hB : (match Allocation.writeScalar annealTargetDataLayout
              (allocRange (Size.ofBytes 8) (Size.ofBytes 4))
              (mkMiriU32Scalar 99) ep1BaseAlloc16 with
              | .ok () a => a.byteSize == Size.ofBytes 16 | .error _ _ => false) = true := by
            kernel_rfl
          rw [hW] at hB; exact beq_iff_eq.mp hB
        · have hR0 : (match Allocation.writeScalar annealTargetDataLayout
              (allocRange (Size.ofBytes 8) (Size.ofBytes 4))
              (mkMiriU32Scalar 99) ep1BaseAlloc16 with
              | .ok () a => a.readScalar annealTargetDataLayout (allocRange Size.ZERO (Size.ofBytes 4)) false ==
                  .ok (mkMiriU32Scalar 42)
              | .error _ _ => false) = true := by kernel_rfl
          rw [hW] at hR0; exact beq_iff_eq.mp hR0
        · have hR8 : (match Allocation.writeScalar annealTargetDataLayout
              (allocRange (Size.ofBytes 8) (Size.ofBytes 4))
              (mkMiriU32Scalar 99) ep1BaseAlloc16 with
              | .ok () a => a.readScalar annealTargetDataLayout (allocRange (Size.ofBytes 8) (Size.ofBytes 4)) false ==
                  .ok (mkMiriU32Scalar 99)
              | .error _ _ => false) = true := by kernel_rfl
          rw [hW] at hR8; exact beq_iff_eq.mp hR8
    rcases hCore with ⟨a0, hWa0, hSz0, hR0, hR8⟩
    let tW3 := (ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag3) (Size.ofBytes 8)
      (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).tree
    have hWriteExtra :
        Allocation.writeScalar annealTargetDataLayout
          (allocRange (Size.ofBytes 8) (Size.ofBytes 4))
          (mkMiriU32Scalar 99) (ep1BaseAlloc16.withExtra tW3) =
        .ok () (a0.withExtra tW3) := by
      have hDet :
          ∀ (t : BorrowTree),
            Allocation.writeScalar annealTargetDataLayout
              (allocRange (Size.ofBytes 8) (Size.ofBytes 4))
              (mkMiriU32Scalar 99) (ep1BaseAlloc16.withExtra t) =
            .ok () ((match Allocation.writeScalar annealTargetDataLayout
                (allocRange (Size.ofBytes 8) (Size.ofBytes 4))
                (mkMiriU32Scalar 99) ep1BaseAlloc16 with
              | .ok () a => a
              | .error _ a => a).withExtra t) := fun _ => by kernel_rfl
      rw [hDet tW3, hWa0]
    have hReadExtra :
        ∀ (a : Allocation Provenance Unit) (t : BorrowTree) (r : AllocRange),
          (a.withExtra t).readScalar annealTargetDataLayout r false =
            a.readScalar annealTargetDataLayout r false := by
      intro a t r
      cases a; rfl
    refine ⟨a0.withExtra tW3, ?_, ?_, ?_, ?_, rfl⟩
    · exact hWriteExtra
    · simpa [Allocation.withExtra, Allocation.byteSize] using hSz0
    · rw [hReadExtra]; exact hR0
    · rw [hReadExtra]; exact hR8
  rcases hWrite99OnBase with ⟨alloc99, hAlloc99W, hAlloc99Sz, hAlloc99R0, hAlloc99R8, hAlloc99Ex⟩
  have hSub0 :
      (allocRange (Size.ofBytes 0) (Size.ofBytes 4)).subrange
        (allocRange Size.ZERO (Size.ofBytes 4)) =
      .ok (allocRange (Size.ofBytes 0) (Size.ofBytes 4)) := by kernel_rfl
  have hSub8 :
      (allocRange (Size.ofBytes 8) (Size.ofBytes 4)).subrange
        (allocRange Size.ZERO (Size.ofBytes 4)) =
      .ok (allocRange (Size.ofBytes 8) (Size.ofBytes 4)) := by kernel_rfl
  have hBack1 : ∀ {α : Type} (x : α), (#[x] : Array α).back? = some x := fun _ => rfl
  let stmt0 : Miri.MIR.Statement :=
    translateStmt { kind := .assign ⟨1, [.deref]⟩ (.use (.constant ⟨ep1U32Ty, .scalar (.int ⟨99, 4⟩)⟩)),
                    span := "s0" }
  let stmt1 : Miri.MIR.Statement :=
    translateStmt { kind := .assign ⟨0, []⟩ (.use (.copy ⟨2, [.deref]⟩)),
                    span := "s1" }
  let term0 : Miri.MIR.Terminator := translateTerminator { kind := .return_, span := "t0" }
  let bb0 : Miri.MIR.BasicBlock :=
    { statements := #[stmt0, stmt1], terminator := term0, cleanup := false }
  have hBb0 : (translateBody ep1BodyTbDerefWriteAndRead).basicBlocks[0]? = some bb0 := by kernel_rfl
  have hS0 : bb0.statements[0]? = some stmt0 := rfl
  have hS1 : bb0.statements[1]? = some stmt1 := rfl
  have hS2 : bb0.statements[2]? = none := rfl
  have hEx : ep1VendoredTbAlloc.extra = ep1DisjointTwoChildTree := rfl
  have hPtrConcrete0 : ∀ (tag : BorTag),
      (ep1VendoredPtrScalar (some (.concrete ep1AllocId tag)) 0).toPointer annealTargetDataLayout =
        .ok ⟨Size.ofBytes (ep1TbBaseAddr + 0), some (.concrete ep1AllocId tag)⟩ := fun _ => by kernel_rfl
  have hPtrConcrete8 : ∀ (tag : BorTag),
      (ep1VendoredPtrScalar (some (.concrete ep1AllocId tag)) 8).toPointer annealTargetDataLayout =
        .ok ⟨Size.ofBytes (ep1TbBaseAddr + 8), some (.concrete ep1AllocId tag)⟩ := fun _ => by kernel_rfl
  have hInitFr : ∀ (wp : Option Provenance) (wo : UInt64),
      (ep1InitVendoredPlaceState wp wo).stack.currentFrame? =
        some
          { body := translateBody ep1BodyTbDerefWriteAndRead
            bodyIdentity := BodyIdentity.ofCanonicalIndex 0
            functionInstance := ⟨.Item 0, #[]⟩
            extra := { borrowTracker := some ep1FrameBorrowState, catchUnwind := none,
                       userRelevance := 0, dataRace := none }
            returnContinuation := .stop false
            returnPlace := .frameLocal 0 0 none (translateTy ep1U32Ty emptyLayoutTable)
              (LocalsIdentity.ofAllocationToken 0)
            localsIdentity := LocalsIdentity.ofAllocationToken 0
            locals :=
              #[ { value := .live (.immediate .uninit),
                   layout := some (translateTy ep1U32Ty emptyLayoutTable) },
                 { value := .live (.immediate (.scalar (ep1VendoredPtrScalar wp wo))),
                   layout := some (translateTy ep1MutPtrU32Ty emptyLayoutTable) },
                 { value := .live (.immediate (.scalar (ep1VendoredPtrScalar (some (.concrete ep1AllocId ep1Tag2)) 0))),
                   layout := some (translateTy ep1MutPtrU32Ty emptyLayoutTable) } ]
            vaList := #[]
            trackCallerArg := none
            location := .mir ⟨0, 0⟩ } := fun _ _ => rfl
  have hFourU64 : (4 : Nat).toUInt64 = 4 := rfl
  have hStep1Write :
      ∀ (tag : BorTag) (off : UInt64)
        (res : EStateM.Result StepError (PlaceMachine.State Unit Unit) Unit),
        (ep1VendoredPtrScalar (some (.concrete ep1AllocId tag)) off).toPointer annealTargetDataLayout =
          .ok ⟨Size.ofBytes (ep1TbBaseAddr + off), some (.concrete ep1AllocId tag)⟩ →
        PlaceMachine.writeMemory ep1PlaceAccessConfig (fun _ => false)
          (.scalar (mkMiriU32Scalar 99))
          ⟨⟨⟨Size.ofBytes (ep1TbBaseAddr + off), some (.concrete ep1AllocId tag)⟩, .none, none⟩,
           translateTy ep1U32Ty emptyLayoutTable⟩
          (ep1InitVendoredPlaceState (some (.concrete ep1AllocId tag)) off) = res →
        Step.step ep1VendoredPlaceStepHooks ()
          (ep1InitVendoredPlaceState (some (.concrete ep1AllocId tag)) off) =
          match res with
          | .error err after => (after, .error err)
          | .ok () after =>
            if (0 != after.stack.frames.size - 1) then
              (after, .error (.frameIndexChanged 0 (after.stack.frames.size - 1)))
            else
              match after.stack.currentFrame? with
              | some fr =>
                match fr.location with
                | .mir loc =>
                  if hLt : after.stack.frames.size - 1 < after.stack.frames.size then
                    ({ after with
                       stack := ⟨after.stack.frames.set (after.stack.frames.size - 1)
                         { fr with location := .mir { loc with statementIndex := loc.statementIndex + 1 } }
                         hLt⟩ },
                     .ok true)
                  else (after, .error (.stack .emptyStack))
                | .unwinding _ => (after, .error .expectedMirLocation)
              | none => (after, .error (.stack .emptyStack)) := by
    intro tag off res hPtr hPM
    have hEvalDest :
        Miri.Interpreter.evalPlace ep1VendoredPlaceHooks () ⟨1, #[.Deref]⟩ false
          (ep1InitVendoredPlaceState (some (.concrete ep1AllocId tag)) off) =
        .ok ⟨.memory ⟨⟨Size.ofBytes (ep1TbBaseAddr + off), some (.concrete ep1AllocId tag)⟩, .none, none⟩,
             translateTy ep1U32Ty emptyLayoutTable⟩
          (ep1InitVendoredPlaceState (some (.concrete ep1AllocId tag)) off) :=
      ep1EvalPlace_deref_local_eq _ _ 1 _ _ (translateTy ep1MutPtrU32Ty emptyLayoutTable)
        rfl rfl rfl hPtrLaySized hPtr
    have hWriteMem := ep1WritePlaceImmediate_memory_eq
      (ep1InitVendoredPlaceState (some (.concrete ep1AllocId tag)) off)
      (.scalar (mkMiriU32Scalar 99))
      ⟨⟨Size.ofBytes (ep1TbBaseAddr + off), some (.concrete ep1AllocId tag)⟩, .none, none⟩
      (translateTy ep1U32Ty emptyLayoutTable) hU32LaySized
    cases res with
    | error err after =>
      have hAssign :
          Step.evalStatement ep1VendoredPlaceStepHooks () stmt0
            (ep1InitVendoredPlaceState (some (.concrete ep1AllocId tag)) off) =
          (after, .error err) := by
        unfold Step.evalStatement
        dsimp only [stmt0, translateStmt, translateStmtKind, translatePlace, translateProjectionElem,
          translateRvalue, translateOperand, translateConstOperand, translateConstValue,
          translateConstScalar, List.map]
        unfold ep1VendoredPlaceStepHooks
        simp only [Miri.Interpreter.runRvalue, bind, Bind.bind, EStateM.bind,
          pure, Pure.pure, EStateM.pure, hEvalDest, hFourU64, hSc99, hWriteMem, hPM]
      unfold Step.step
      simp only [Id.run, hInitFr, hBb0, hS0, hAssign]
      rfl
    | ok u after =>
      cases u
      have hAssign :
          Step.evalStatement ep1VendoredPlaceStepHooks () stmt0
            (ep1InitVendoredPlaceState (some (.concrete ep1AllocId tag)) off) =
          (after, .ok ()) := by
        unfold Step.evalStatement
        dsimp only [stmt0, translateStmt, translateStmtKind, translatePlace, translateProjectionElem,
          translateRvalue, translateOperand, translateConstOperand, translateConstValue,
          translateConstScalar, List.map]
        unfold ep1VendoredPlaceStepHooks
        simp only [Miri.Interpreter.runRvalue, bind, Bind.bind, EStateM.bind,
          pure, Pure.pure, EStateM.pure, hEvalDest, hFourU64, hSc99, hWriteMem, hPM]
      have hInitSz :
          (ep1InitVendoredPlaceState (some (.concrete ep1AllocId tag)) off).stack.frames.size - 1 = 0 :=
        rfl
      unfold Step.step
      simp only [Id.run, hInitFr, hBb0, hS0, hAssign, hInitSz, pure, Pure.pure]
      by_cases hIdx : (0 != after.stack.frames.size - 1) = true
      · simp only [hIdx, ↓reduceIte]
      · simp only [hIdx, Bool.false_eq_true, ↓reduceIte]
        cases hCur : after.stack.currentFrame? with
        | none => simp only
        | some fr =>
          dsimp only
          cases hLoc : fr.location with
          | unwinding _ => simp only
          | mir _ => simp only
  let initOk := ep1InitVendoredPlaceState (some (.concrete ep1AllocId ep1Tag3)) 8
  let fr1Ok : Frame Provenance LocalLayout MachineHooks.FrameExtra :=
    { body := translateBody ep1BodyTbDerefWriteAndRead
      bodyIdentity := BodyIdentity.ofCanonicalIndex 0
      functionInstance := ⟨.Item 0, #[]⟩
      extra := { borrowTracker := some ep1FrameBorrowState, catchUnwind := none,
                 userRelevance := 0, dataRace := none }
      returnContinuation := .stop false
      returnPlace := .frameLocal 0 0 none (translateTy ep1U32Ty emptyLayoutTable)
        (LocalsIdentity.ofAllocationToken 0)
      localsIdentity := LocalsIdentity.ofAllocationToken 0
      locals :=
        #[ { value := .live (.immediate .uninit),
             layout := some (translateTy ep1U32Ty emptyLayoutTable) },
           { value := .live (.immediate (.scalar (ep1VendoredPtrScalar (some (.concrete ep1AllocId ep1Tag3)) 8))),
             layout := some (translateTy ep1MutPtrU32Ty emptyLayoutTable) },
           { value := .live (.immediate (.scalar (ep1VendoredPtrScalar (some (.concrete ep1AllocId ep1Tag2)) 0))),
             layout := some (translateTy ep1MutPtrU32Ty emptyLayoutTable) } ]
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 1⟩ }
  let stMid1 : PlaceMachine.State Unit Unit :=
    { initOk with
      stack := { frames := #[fr1Ok] }
      machine :=
        { initOk.machine with
          memory :=
            { ep1ObsState.memory with
              live := #[(ep1AllocId, LocalAllocation.mk .stack alloc99)] } } }
  have hAnyObs : ep1ObsState.memory.live.any (fun row => row.1 == ep1AllocId) = true := by
    simp [ep1ObsState]
  have hStep1Ok :
      Step.step ep1VendoredPlaceStepHooks () initOk = (stMid1, .ok true) := by
    have hPM := ep1PlaceWriteMemory_u32_concrete_eq initOk
      ep1VendoredTbAlloc ep1Tag3 8 (mkMiriU32Scalar 99)
      { global := { GlobalState.new with protectedTags := ep1Prot23 }, retagMode := .Default }
      rfl rfl rfl hAnyObs rfl (by kernel_rfl) hBounds8 (hPtrGet8 ep1Tag3) hSub8 hSc99Sz hSc99Int
    dsimp only at hPM
    rw [hEx, hW3] at hPM
    dsimp only at hPM
    rw [hAlloc99W] at hPM
    have hS1 := hStep1Write ep1Tag3 8 _ (hPtrConcrete8 ep1Tag3) hPM
    dsimp only at hS1
    rw [hS1]
    rfl
  let tAfterR2 := (alloc99.extra.performBorrowAccessRange (.concrete ep1Tag2) (Size.ofBytes 0)
    (Size.ofBytes 4) .Read ep1Prot23 .VisitChildrenOfAccessed).tree
  let allocAfterR2 : Allocation Provenance BorrowTree := alloc99.setExtra tAfterR2
  have hR2Status :
      (alloc99.extra.performBorrowAccessRange (.concrete ep1Tag2) (Size.ofBytes 0)
        (Size.ofBytes 4) .Read ep1Prot23 .VisitChildrenOfAccessed).status = .Completed := by
    rw [hAlloc99Ex]; exact hR2AfterW3
  let fr2Ok : Frame Provenance LocalLayout MachineHooks.FrameExtra :=
    { fr1Ok with
      location := .mir ⟨0, 2⟩
      locals :=
        #[ { value := .live (.immediate (.scalar (mkMiriU32Scalar 42))),
             layout := some (translateTy ep1U32Ty emptyLayoutTable) },
           { value := .live (.immediate (.scalar (ep1VendoredPtrScalar (some (.concrete ep1AllocId ep1Tag3)) 8))),
             layout := some (translateTy ep1MutPtrU32Ty emptyLayoutTable) },
           { value := .live (.immediate (.scalar (ep1VendoredPtrScalar (some (.concrete ep1AllocId ep1Tag2)) 0))),
             layout := some (translateTy ep1MutPtrU32Ty emptyLayoutTable) } ] }
  have hStep2Ok :
      ∃ fr2,
        fr2.location = .mir ⟨0, 2⟩ ∧
        fr2.body = translateBody ep1BodyTbDerefWriteAndRead ∧
        fr2.returnContinuation = .stop false ∧
        fr2.extra.borrowTracker = some ep1FrameBorrowState ∧
        fr2.locals[0]? =
          some { value := .live (.immediate (.scalar (mkMiriU32Scalar 42))),
                 layout := some (translateTy ep1U32Ty emptyLayoutTable) } ∧
        Step.step ep1VendoredPlaceStepHooks () stMid1 =
          ({ stMid1 with
             stack := { frames := #[fr2] }
             machine :=
               { stMid1.machine with
                 memory :=
                   { ep1ObsState.memory with
                     live := #[(ep1AllocId, LocalAllocation.mk .stack allocAfterR2)] } } },
           .ok true) := by
    have hPMRead := ep1PlaceReadImmediate_u32_concrete_eq stMid1 alloc99 ep1Tag2 0
      { global := { GlobalState.new with protectedTags := ep1Prot23 }, retagMode := .Default }
      rfl rfl rfl (by simp [stMid1]) hAlloc99Sz hBounds0 (hPtrGet0 ep1Tag2) hSub0
    dsimp only at hPMRead
    rw [hR2Status] at hPMRead
    dsimp only at hPMRead
    have hR0SetExtra :
        allocAfterR2.readScalar annealTargetDataLayout (allocRange (Size.ofBytes 0) (Size.ofBytes 4)) false =
          .ok (mkMiriU32Scalar 42) := by
      have : allocAfterR2.readScalar annealTargetDataLayout (allocRange (Size.ofBytes 0) (Size.ofBytes 4)) false =
          alloc99.readScalar annealTargetDataLayout (allocRange (Size.ofBytes 0) (Size.ofBytes 4)) false := by
        cases alloc99; rfl
      rw [this]; exact hAlloc99R0
    rw [hR0SetExtra] at hPMRead
    have hStMid1Fr : stMid1.stack.currentFrame? = some fr1Ok := rfl
    have hFr1Loc : fr1Ok.location = .mir ⟨0, 1⟩ := rfl
    have hFr1Body : fr1Ok.body = translateBody ep1BodyTbDerefWriteAndRead := rfl
    have hEvalDest0 :
        Miri.Interpreter.evalPlace ep1VendoredPlaceHooks () ⟨0, #[]⟩ false stMid1 =
          .ok ⟨.local 0 0 none (LocalsIdentity.ofAllocationToken 0),
               translateTy ep1U32Ty emptyLayoutTable⟩ stMid1 :=
      ep1EvalPlace_whole_local_eq stMid1 fr1Ok 0 _ (translateTy ep1U32Ty emptyLayoutTable)
        rfl rfl hU32LaySized
    have hEvalSrc2 :
        Miri.Interpreter.evalPlace ep1VendoredPlaceHooks () ⟨2, #[.Deref]⟩ false stMid1 =
          .ok ⟨.memory ⟨⟨Size.ofBytes (ep1TbBaseAddr + 0), some (.concrete ep1AllocId ep1Tag2)⟩, .none, none⟩,
               translateTy ep1U32Ty emptyLayoutTable⟩ stMid1 :=
      ep1EvalPlace_deref_local_eq stMid1 fr1Ok 2 _ _ (translateTy ep1MutPtrU32Ty emptyLayoutTable)
        rfl rfl rfl hPtrLaySized (hPtrConcrete0 ep1Tag2)
    have hPlaceToOp2 :
        Miri.Interpreter.placeToOp ep1VendoredPlaceHooks ()
          ⟨.memory ⟨⟨Size.ofBytes (ep1TbBaseAddr + 0), some (.concrete ep1AllocId ep1Tag2)⟩, .none, none⟩,
           translateTy ep1U32Ty emptyLayoutTable⟩ stMid1 =
        .ok ⟨.indirect ⟨⟨Size.ofBytes (ep1TbBaseAddr + 0), some (.concrete ep1AllocId ep1Tag2)⟩, .none, none⟩,
             translateTy ep1U32Ty emptyLayoutTable⟩ stMid1 := rfl
    let stAfterRead : PlaceMachine.State Unit Unit :=
      { stMid1 with
        machine :=
          { stMid1.machine with
            memory :=
              { ep1ObsState.memory with
                live := #[(ep1AllocId, LocalAllocation.mk .stack allocAfterR2)] } } }
    have hWriteLocal0 :
        Miri.Interpreter.writePlaceImmediate ep1VendoredPlaceHooks () (.scalar (mkMiriU32Scalar 42))
          ⟨.local 0 0 none (LocalsIdentity.ofAllocationToken 0),
           translateTy ep1U32Ty emptyLayoutTable⟩ stAfterRead =
        .ok () { stAfterRead with stack := { frames := #[{ fr2Ok with location := .mir ⟨0, 1⟩ }] } } :=
      ep1WritePlaceImmediate_local_eq stAfterRead fr1Ok { fr2Ok with location := .mir ⟨0, 1⟩ } 0
        .uninit (.scalar (mkMiriU32Scalar 42)) (translateTy ep1U32Ty emptyLayoutTable)
        rfl rfl hU32LaySized rfl rfl
    have hAssign2 :
        Step.evalStatement ep1VendoredPlaceStepHooks () stmt1 stMid1 =
          ({ stAfterRead with stack := { frames := #[{ fr2Ok with location := .mir ⟨0, 1⟩ }] } },
           .ok ()) := by
      unfold Step.evalStatement
      dsimp only [stmt1, translateStmt, translateStmtKind, translatePlace, translateProjectionElem,
        translateRvalue, translateOperand, List.map]
      unfold ep1VendoredPlaceStepHooks
      simp only [Miri.Interpreter.runRvalue, bind, Bind.bind, EStateM.bind,
        hEvalDest0, hEvalSrc2, hPlaceToOp2]
      rw [hPMRead]
      have hStAfterEq :
          ({ stMid1 with
             machine :=
               { stMid1.machine with
                 memory :=
                   { stMid1.machine.memory with
                     live := (stMid1.machine.memory.live.filter fun row => row.1 != ep1AllocId).push
                       (ep1AllocId, LocalAllocation.mk .stack allocAfterR2) } } } :
              PlaceMachine.State Unit Unit) = stAfterRead := rfl
      dsimp only
      rw [hStAfterEq, hWriteLocal0]
    refine ⟨fr2Ok, rfl, rfl, rfl, rfl, rfl, ?_⟩
    unfold Step.step
    simp only [Id.run, hStMid1Fr, hFr1Loc, hFr1Body, hBb0, hS1, hAssign2]
    rfl
  rcases hStep2Ok with ⟨fr2, hFr2Loc, hFr2Body, hFr2Cont, hFr2Bt, hFr2Loc0, hStep2Eq⟩
  let stMid2 : PlaceMachine.State Unit Unit :=
    { stMid1 with
      stack := { frames := #[fr2] }
      machine :=
        { stMid1.machine with
          memory :=
            { ep1ObsState.memory with
              live := #[(ep1AllocId, LocalAllocation.mk .stack allocAfterR2)] } } }
  let tAfterRel2 := (tAfterR2.releaseProtector ep1Tag2 ep1Prot23).tree
  let allocAfterRel2 : Allocation Provenance BorrowTree := allocAfterR2.setExtra tAfterRel2
  let tAfterRel3 := (tAfterRel2.releaseProtector ep1Tag3 ep1Prot23).tree
  let allocAfterRel3 : Allocation Provenance BorrowTree := allocAfterRel2.setExtra tAfterRel3
  let btAfterEndCall : MachineHooks.BorrowState :=
    { global := { GlobalState.new with protectedTags := (ep1Prot23.remove ep1Tag2).remove ep1Tag3 },
      retagMode := .Default }
  let stFinal : PlaceMachine.State Unit Unit :=
    { stMid2 with
      stack := { frames := #[] }
      machine :=
        { stMid2.machine with
          memory :=
            { ep1ObsState.memory with
              live := #[(ep1AllocId, LocalAllocation.mk .stack allocAfterRel3)] }
          borrowTracker := some btAfterEndCall } }
  have hRel2Status : (tAfterR2.releaseProtector ep1Tag2 ep1Prot23).status = .Released := by
    dsimp only [tAfterR2]; rw [hAlloc99Ex]; exact hRel2StatusClosed
  have hRel3Status : (tAfterRel2.releaseProtector ep1Tag3 ep1Prot23).status = .Released := by
    dsimp only [tAfterRel2, tAfterR2]; rw [hAlloc99Ex]; exact hRel3StatusClosed
  have hPostRetW1 :
      (tAfterRel3.performBorrowAccessRange (.concrete ep1Tag1) Size.ZERO (Size.ofBytes 4)
        .Write btAfterEndCall.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    dsimp only [tAfterRel3, tAfterRel2, tAfterR2, btAfterEndCall]
    rw [hAlloc99Ex]; exact hPostRetW1Closed
  have hStep3Ok :
      Step.step ep1VendoredPlaceStepHooks () stMid2 = (stFinal, .ok true) := by
    have hOp0 : fr2.getLocalOperand 0 =
        .ok (.immediate (.scalar (mkMiriU32Scalar 42))) := by
      obtain ⟨hLt, hEq⟩ := Array.getElem?_eq_some_iff.mp hFr2Loc0
      unfold Frame.getLocalOperand Frame.getLocal
      simp only [hLt, ↓reduceDIte, hEq, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
      rfl
    have hFind1 :
        (#[(ep1AllocId, LocalAllocation.mk (MachineKind := Unit) .stack allocAfterR2)]).find?
          (fun entry => entry.1 == ep1AllocId) =
        some (ep1AllocId, LocalAllocation.mk .stack allocAfterR2) := by simp
    have hFind2 :
        (#[(ep1AllocId, LocalAllocation.mk (MachineKind := Unit) .stack allocAfterRel2)]).find?
          (fun entry => entry.1 == ep1AllocId) =
        some (ep1AllocId, LocalAllocation.mk .stack allocAfterRel2) := by simp
    have hInfoRel1 :
        ({ ep1ObsState.memory with
           live := #[(ep1AllocId, LocalAllocation.mk .stack allocAfterR2)] } :
            MemoryState Provenance BorrowTree Unit).getAllocInfo ep1AllocId =
        .ok ⟨allocAfterR2.byteSize, allocAfterR2.align, .liveData, allocAfterR2.mutability⟩ := by
      unfold MemoryState.getAllocInfo
      simp only [hFind1, pure, Pure.pure, Except.pure]
    have hInfoRel2 :
        ({ ep1ObsState.memory with
           live := #[(ep1AllocId, LocalAllocation.mk .stack allocAfterRel2)] } :
            MemoryState Provenance BorrowTree Unit).getAllocInfo ep1AllocId =
        .ok ⟨allocAfterRel2.byteSize, allocAfterRel2.align, .liveData, allocAfterRel2.mutability⟩ := by
      unfold MemoryState.getAllocInfo
      simp only [hFind2, pure, Pure.pure, Except.pure]
    have hSetRel1 :
        ({ ep1ObsState.memory with
           live := #[(ep1AllocId, LocalAllocation.mk .stack allocAfterR2)] } :
            MemoryState Provenance BorrowTree Unit).setLiveAllocation ep1AllocId allocAfterRel2 =
        .ok { ep1ObsState.memory with
              live := #[(ep1AllocId, LocalAllocation.mk .stack allocAfterRel2)] } := by
      have hS := MemoryState.setLiveAllocation_of_find
        ({ ep1ObsState.memory with
           live := #[(ep1AllocId, LocalAllocation.mk .stack allocAfterR2)] })
        ep1AllocId (LocalAllocation.mk .stack allocAfterR2) allocAfterRel2 hFind1
      simpa using hS
    have hSetRel2 :
        ({ ep1ObsState.memory with
           live := #[(ep1AllocId, LocalAllocation.mk .stack allocAfterRel2)] } :
            MemoryState Provenance BorrowTree Unit).setLiveAllocation ep1AllocId allocAfterRel3 =
        .ok { ep1ObsState.memory with
              live := #[(ep1AllocId, LocalAllocation.mk .stack allocAfterRel3)] } := by
      have hS := MemoryState.setLiveAllocation_of_find
        ({ ep1ObsState.memory with
           live := #[(ep1AllocId, LocalAllocation.mk .stack allocAfterRel2)] })
        ep1AllocId (LocalAllocation.mk .stack allocAfterRel2) allocAfterRel3 hFind2
      simpa using hS
    have hBeforePop :
        MachineHooks.run (MachineHooks.beforeStackPopWithEnsure (fun _ => pure ())) stMid2 =
          ({ stFinal with stack := { frames := #[fr2] } }, .ok ()) := by
      unfold MachineHooks.run Call.run MachineHooks.beforeStackPopWithEnsure MachineHooks.currentFrame
      simp only [stMid2, stMid1, initOk, ep1InitVendoredPlaceState,
        get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set,
        modify, modifyGet, MonadStateOf.modifyGet,
        bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
        Option.isSome_some, ↓reduceIte, Stack.currentFrame?, hBack1, hFr2Bt, ep1FrameBorrowState]
      simp only [← Array.forIn_toList, List.forIn_cons, List.forIn_nil,
        EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
        hInfoRel1, beq_self_eq_true, ↓reduceIte, hFind1]
      have hExAfterR2 : allocAfterR2.extra = tAfterR2 := rfl
      rw [hExAfterR2]
      have hSetRel1' :
          ({ ep1ObsState.memory with
             live := #[(ep1AllocId, LocalAllocation.mk .stack allocAfterR2)] } :
              MemoryState Provenance BorrowTree Unit).setLiveAllocation ep1AllocId
              (allocAfterR2.setExtra (tAfterR2.releaseProtector ep1Tag2 ep1Prot23).tree) =
          .ok { ep1ObsState.memory with
                live := #[(ep1AllocId, LocalAllocation.mk .stack allocAfterRel2)] } := hSetRel1
      rw [hSetRel1']
      simp only [EStateM.get, EStateM.modifyGet, EStateM.bind,
        EStateM.pure, hRel2Status, hInfoRel2, beq_self_eq_true, ↓reduceIte, hFind2]
      have hExAfterRel2 : allocAfterRel2.extra = tAfterRel2 := rfl
      rw [hExAfterRel2]
      have hSetRel2' :
          ({ ep1ObsState.memory with
             live := #[(ep1AllocId, LocalAllocation.mk .stack allocAfterRel2)] } :
              MemoryState Provenance BorrowTree Unit).setLiveAllocation ep1AllocId
              (allocAfterRel2.setExtra (tAfterRel2.releaseProtector ep1Tag3 ep1Prot23).tree) =
          .ok { ep1ObsState.memory with
                live := #[(ep1AllocId, LocalAllocation.mk .stack allocAfterRel3)] } := hSetRel2
      rw [hSetRel2']
      simp only [EStateM.modifyGet, EStateM.set, EStateM.bind, EStateM.pure, hRel3Status]
      rfl
    have hStMid2Cur : stMid2.stack.currentFrame? = some fr2 := by
      simp only [stMid2, Stack.currentFrame?, hBack1]
    unfold Step.step ep1VendoredPlaceStepHooks ControlFlow.evalTerminator
      ControlFlow.returnFromCurrentFrame ep1VendoredTermHooks ep1VendoredControlHooks
    simp only [Id.run, hStMid2Cur, hFr2Loc, hFr2Body, hBb0, hS2, hOp0]
    dsimp only [bb0, term0, translateTerminator, translateTerminatorKind]
    rw [hBeforePop]
    simp only [bind, Bind.bind, pure, Pure.pure, bne_self_eq_false, Bool.false_eq_true,
      Bool.false_and, ↓reduceIte, Stack.popFrame, hBack1, Except.pure, hFr2Cont]
    rfl
  have hStep4Done :
      Step.step ep1VendoredPlaceStepHooks () stFinal = (stFinal, .ok false) := rfl
  let tProtTree := (ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag1) Size.ZERO
    (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).tree
  let tFrozTree := (ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag2) Size.ZERO
    (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).tree
  have hStepProtUB :
      Step.step ep1VendoredPlaceStepHooks ()
        (ep1InitVendoredPlaceState (some (.concrete ep1AllocId ep1Tag1)) 0) =
      ({ (ep1InitVendoredPlaceState (some (.concrete ep1AllocId ep1Tag1)) 0) with
         machine :=
           { (ep1InitVendoredPlaceState (some (.concrete ep1AllocId ep1Tag1)) 0).machine with
             memory :=
               { ep1ObsState.memory with
                 live := #[(ep1AllocId,
                   LocalAllocation.mk .stack (ep1VendoredTbAlloc.setExtra tProtTree))] } } },
       .error (.undefinedBehavior s!"Tree Borrows: {reprStr (BorrowTree.BorrowTreeAccessStatus.AccessFailure ⟨0, 4⟩ (.TransitionError 1 (.ProtectedDisabled .Frozen)))}")) := by
    have hPM := ep1PlaceWriteMemory_u32_concrete_eq
      (ep1InitVendoredPlaceState (some (.concrete ep1AllocId ep1Tag1)) 0)
      ep1VendoredTbAlloc ep1Tag1 0 (mkMiriU32Scalar 99)
      { global := { GlobalState.new with protectedTags := ep1Prot23 }, retagMode := .Default }
      rfl rfl rfl hAnyObs rfl (by kernel_rfl) hBounds0 (hPtrGet0 ep1Tag1) hSub0 hSc99Sz hSc99Int
    dsimp only at hPM
    have hW1' :
        (ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag1) (Size.ofBytes 0)
          (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).status =
        .AccessFailure ⟨0, 4⟩ (.TransitionError 1 (.ProtectedDisabled .Frozen)) := hW1
    rw [hEx, hW1'] at hPM
    dsimp only [placeMachineTreeError] at hPM
    have hS1 := hStep1Write ep1Tag1 0 _ (hPtrConcrete0 ep1Tag1) hPM
    dsimp only at hS1
    rw [hS1]
    rfl
  have hStepFrozUB :
      Step.step ep1VendoredPlaceStepHooks ()
        (ep1InitVendoredPlaceState (some (.concrete ep1AllocId ep1Tag2)) 0) =
      ({ (ep1InitVendoredPlaceState (some (.concrete ep1AllocId ep1Tag2)) 0) with
         machine :=
           { (ep1InitVendoredPlaceState (some (.concrete ep1AllocId ep1Tag2)) 0).machine with
             memory :=
               { ep1ObsState.memory with
                 live := #[(ep1AllocId,
                   LocalAllocation.mk .stack (ep1VendoredTbAlloc.setExtra tFrozTree))] } } },
       .error (.undefinedBehavior s!"Tree Borrows: {reprStr (BorrowTree.BorrowTreeAccessStatus.AccessFailure ⟨0, 4⟩ (.TransitionError 1 (.ChildAccessForbidden .Frozen)))}")) := by
    have hPM := ep1PlaceWriteMemory_u32_concrete_eq
      (ep1InitVendoredPlaceState (some (.concrete ep1AllocId ep1Tag2)) 0)
      ep1VendoredTbAlloc ep1Tag2 0 (mkMiriU32Scalar 99)
      { global := { GlobalState.new with protectedTags := ep1Prot23 }, retagMode := .Default }
      rfl rfl rfl hAnyObs rfl (by kernel_rfl) hBounds0 (hPtrGet0 ep1Tag2) hSub0 hSc99Sz hSc99Int
    dsimp only at hPM
    have hW2' :
        (ep1DisjointTwoChildTree.performBorrowAccessRange (.concrete ep1Tag2) (Size.ofBytes 0)
          (Size.ofBytes 4) .Write ep1Prot23 .VisitChildrenOfAccessed).status =
        .AccessFailure ⟨0, 4⟩ (.TransitionError 1 (.ChildAccessForbidden .Frozen)) := hW2
    rw [hEx, hW2'] at hPM
    dsimp only [placeMachineTreeError] at hPM
    have hS1 := hStep1Write ep1Tag2 0 _ (hPtrConcrete0 ep1Tag2) hPM
    dsimp only at hS1
    rw [hS1]
    rfl
  have hStepDangUB :
      Step.step ep1VendoredPlaceStepHooks () (ep1InitVendoredPlaceState none 0) =
      (ep1InitVendoredPlaceState none 0,
       .error (MemoryErrors.operand
         (.pointerAccess (.access (.danglingIntegerPointer ep1TbBaseAddr 4 .memoryAccess))))) := by
    have hPM := ep1PlaceWriteMemory_dangling_eq (ep1InitVendoredPlaceState none 0)
      (mkMiriU32Scalar 99) hSc99Sz hSc99Int
    dsimp only at hPM
    have hPtrNone :
        (ep1VendoredPtrScalar none 0).toPointer annealTargetDataLayout =
          .ok ⟨Size.ofBytes ep1TbBaseAddr, none⟩ := by kernel_rfl
    have hEvalDestDang :
        Miri.Interpreter.evalPlace ep1VendoredPlaceHooks () ⟨1, #[.Deref]⟩ false
          (ep1InitVendoredPlaceState none 0) =
        .ok ⟨.memory ⟨⟨Size.ofBytes ep1TbBaseAddr, none⟩, .none, none⟩,
             translateTy ep1U32Ty emptyLayoutTable⟩
          (ep1InitVendoredPlaceState none 0) :=
      ep1EvalPlace_deref_local_eq _ _ 1 _ _ (translateTy ep1MutPtrU32Ty emptyLayoutTable)
        rfl rfl rfl hPtrLaySized hPtrNone
    have hWriteDang := ep1WritePlaceImmediate_memory_eq
      (ep1InitVendoredPlaceState none 0) (.scalar (mkMiriU32Scalar 99))
      ⟨⟨Size.ofBytes ep1TbBaseAddr, none⟩, .none, none⟩
      (translateTy ep1U32Ty emptyLayoutTable) hU32LaySized
    have hAssignDang :
        Step.evalStatement ep1VendoredPlaceStepHooks () stmt0 (ep1InitVendoredPlaceState none 0) =
          (ep1InitVendoredPlaceState none 0,
           .error (MemoryErrors.operand
             (.pointerAccess (.access (.danglingIntegerPointer ep1TbBaseAddr 4 .memoryAccess))))) := by
      unfold Step.evalStatement
      dsimp only [stmt0, translateStmt, translateStmtKind, translatePlace, translateProjectionElem,
        translateRvalue, translateOperand, translateConstOperand, translateConstValue,
        translateConstScalar, List.map]
      unfold ep1VendoredPlaceStepHooks
      simp only [Miri.Interpreter.runRvalue, bind, Bind.bind, EStateM.bind,
        pure, Pure.pure, EStateM.pure, hEvalDestDang, hFourU64, hSc99, hWriteDang, hPM]
    unfold Step.step
    simp only [Id.run, hInitFr, hBb0, hS0, hAssignDang]
    rfl
  let deadRetFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra :=
    { body := translateBody ep1BodyTbDerefWriteAndRead
      bodyIdentity := BodyIdentity.ofCanonicalIndex 0
      functionInstance := ⟨.Item 0, #[]⟩
      extra := { borrowTracker := some ep1FrameBorrowState, catchUnwind := none,
                 userRelevance := 0, dataRace := none }
      returnContinuation := .stop false
      returnPlace := .frameLocal 0 0 none (translateTy ep1U32Ty emptyLayoutTable)
        (LocalsIdentity.ofAllocationToken 0)
      localsIdentity := LocalsIdentity.ofAllocationToken 0
      locals :=
        #[ { value := .dead, layout := some (translateTy ep1U32Ty emptyLayoutTable) },
           { value := .live (.immediate (.scalar (ep1VendoredPtrScalar (some (.concrete ep1AllocId ep1Tag3)) 8))),
             layout := some (translateTy ep1MutPtrU32Ty emptyLayoutTable) },
           { value := .live (.immediate (.scalar (ep1VendoredPtrScalar (some (.concrete ep1AllocId ep1Tag2)) 0))),
             layout := some (translateTy ep1MutPtrU32Ty emptyLayoutTable) } ]
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 2⟩ }
  let initDeadRetUB : PlaceMachine.State Unit Unit :=
    { initOk with stack := { frames := #[deadRetFrame] } }
  have hStepDeadRetUB :
      Step.step ep1VendoredPlaceStepHooks () initDeadRetUB =
        (initDeadRetUB, .error (.stack (.localExpectedLive 0))) := by
    have hDead0 : deadRetFrame.getLocalOperand 0 = .error (.localExpectedLive 0) := rfl
    unfold Step.step ep1VendoredPlaceStepHooks ControlFlow.evalTerminator
      ControlFlow.returnFromCurrentFrame ep1VendoredTermHooks ep1VendoredControlHooks
    simp only [initDeadRetUB, Id.run, Stack.currentFrame?, hBack1, deadRetFrame, hBb0, hS2, hDead0]
    dsimp only [bb0, term0, translateTerminator, translateTerminatorKind]
    simp only [bind, Bind.bind, pure, Pure.pure, bne_self_eq_false, Bool.false_eq_true,
      Bool.false_and, ↓reduceIte]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exactWP_seq]
    unfold AnnealExactWP miriStepAction
    rw [hStep1Ok]
    dsimp only
    rw [hStep2Eq]
    refine ⟨rfl, ?_⟩
    unfold vendoredActiveLocal0Bits
    simp only [Stack.currentFrame?, hBack1, hFr2Loc0]
    kernel_rfl
  · change AnnealExactWP (miriRunFuelAction ep1VendoredPlaceStepHooks () 4) _ _ initOk
    rw [miriBodyExactWP_iff]
    dsimp only [stMid2] at hStep3Ok hStep4Done
    simp only [miriBodySafetyVC, AnnealExactWP, miriStepAction, hStep1Ok, hStep2Eq, hStep3Ok,
      hStep4Done, ↓reduceIte]
    refine ⟨rfl, btAfterEndCall, rfl, (by decide), (by decide), allocAfterRel3, rfl, hPostRetW1, ?_, ?_⟩
    · unfold miriObserveScalarAction allocReadScalarAction
      have hRead8 :
          allocAfterRel3.readScalar annealTargetDataLayout
            (allocRange (Size.ofBytes 8) (Size.ofBytes 4)) false =
          .ok (mkMiriU32Scalar 99) := by
        have : allocAfterRel3.readScalar annealTargetDataLayout
            (allocRange (Size.ofBytes 8) (Size.ofBytes 4)) false =
          alloc99.readScalar annealTargetDataLayout
            (allocRange (Size.ofBytes 8) (Size.ofBytes 4)) false := by cases alloc99; rfl
        rw [this]; exact hAlloc99R8
      rw [hRead8]; kernel_rfl
    · unfold miriObserveScalarAction allocReadScalarAction
      have hRead0 :
          allocAfterRel3.readScalar annealTargetDataLayout
            (allocRange Size.ZERO (Size.ofBytes 4)) false =
          .ok (mkMiriU32Scalar 42) := by
        have : allocAfterRel3.readScalar annealTargetDataLayout
            (allocRange Size.ZERO (Size.ofBytes 4)) false =
          alloc99.readScalar annealTargetDataLayout
            (allocRange Size.ZERO (Size.ofBytes 4)) false := by cases alloc99; rfl
        rw [this]; exact hAlloc99R0
      rw [hRead0]; kernel_rfl
  · unfold AnnealExactWP miriStepAction
    rw [hStepProtUB]
    exact ⟨rfl, rfl⟩
  · unfold AnnealExactWP miriStepAction
    rw [hStepProtUB]
    intro hF; exact hF
  · unfold AnnealExactWP miriStepAction
    rw [hStepFrozUB]
    exact ⟨rfl, rfl⟩
  · unfold AnnealExactWP miriStepAction
    rw [hStepFrozUB]
    intro hF; exact hF
  · unfold AnnealExactWP miriStepAction
    rw [hStepDangUB]
  · unfold AnnealExactWP miriStepAction
    rw [hStepDangUB]
    intro hF; exact hF
  · unfold AnnealExactWP miriStepAction
    rw [hStepDeadRetUB]
  · unfold AnnealExactWP miriStepAction
    rw [hStepDeadRetUB]
    intro hF; exact hF

end VendoredNativePlaceMachineTbExecution

end CrossLayerCorrespondence

/-! ## §5. Episode 1 Capstone & Silent Import-Isolation / Bridge-Reality / 3-Axiom Audit -/

/-- **Episode 1 Capstone (`LeanMiriSpec.InitialStateTreeBorrowsWpLM`)**:
bundles §1 (`miriTreeRangeExactWP_iff` + initial-state setup/chaining/protector/topology framing),
§2 (`miriInstructionExactWP_iff` + `miriStepStmtExactWP_iff` + `miriCallDispatchExactWP_iff` +
`miriCallExtraExactWP_iff` + `miriCallTerminatorExactWP_iff`),
§3 (`miriObserveMemoryExactWP_iff` + strict state immutability + compositions), and
§4 (3-way `Anneal.MiriTreeBorrowsV2026 ↔ V2026_06_01 ↔ Miri.TreeBorrows` correspondence +
concrete positive and bidirectional `↔` negative UB refutations on `translateBody`-lowered
`CapturedMir`, `BorrowTree`, `Allocation`, and `CallDispatchMachine`). -/
theorem ep1_initial_state_tree_borrows_wp_capstone :
    (type_of% @miriTreeNewChildExactWP_iff) ∧
    (type_of% @miriTreeInitialSetupExactWP_iff) ∧
    (type_of% @miriTreeRangeExactWP_iff) ∧
    (type_of% @miriTreeRangeSymbolicExactWP_iff) ∧
    (type_of% @miriTreeInitAndRangeExactWP_iff) ∧
    (type_of% @miriTreeRangeSeqExactWP_iff) ∧
    (type_of% @miriTreeRangeChainExactWP_iff) ∧
    (type_of% @miriTreeRangeThenReleaseExactWP_iff) ∧
    (type_of% @miriTreeRange_preserves_topology) ∧
    (type_of% @miriTreeRange_missingTag_frame_exactWP) ∧
    (type_of% @miriProtectedTags_remove_ne) ∧
    (type_of% @miriProtectedTags_insert_ne) ∧
    (type_of% @miriEndCall_preserves_unlisted_protector) ∧
    (type_of% @miriBeforeMemoryReadExactWP_iff) ∧
    (type_of% @miriBeforeMemoryWriteExactWP_iff) ∧
    (type_of% @miriPlaceMachineMemoryAccessExactWP_iff) ∧
    (type_of% @miriPlaceMachineWriteMemoryExactWP_iff) ∧
    (type_of% @miriPlaceMachineReadImmediateExactWP_iff) ∧
    (type_of% @miriInstructionExactWP_iff) ∧
    (type_of% @miriInstructionExactWP_nop_frame) ∧
    (type_of% @miriInstructionExactWP_meta_frame) ∧
    (type_of% @annealInstruction_storageDead_returnPlace_err_exactWP) ∧
    (type_of% @miriInstructionExactWP_setDiscriminant_iff) ∧
    (type_of% @miriEvalRvalueIntoPlaceExactWP_iff) ∧
    (type_of% @miriInstructionAssignRvalueExactWP_iff) ∧
    (type_of% @miriInstructionAssign_copyForDeref_err_exactWP) ∧
    (type_of% @miriInstructionAssign_use_exactWP_iff) ∧
    (type_of% @miriMachineStorageDeadExactWP_iff) ∧
    (type_of% @miriMachineStorageDead_imm_frame_otherLocals) ∧
    (type_of% @miriStepStmtExactWP_iff) ∧
    (type_of% @miriStepStmt_callerFrames_preserved) ∧
    (type_of% @miriStepStmt_frame_callerStack) ∧
    (type_of% @miriCallDispatchExactWP_iff) ∧
    (type_of% @miriCallDispatch_missingForeign_exactWP) ∧
    (type_of% @miriCallDispatch_backendError_exactWP) ∧
    (type_of% @miriCallDispatch_loadMir_exactWP) ∧
    (type_of% @miriCallDispatch_foreignEmulate_exactWP) ∧
    (type_of% @miriCallExtraExactWP_iff) ∧
    (type_of% @miriForeignEmulate_abort_exactWP) ∧
    (type_of% @miriForeignEmulate_noAllocShim_exactWP) ∧
    (type_of% @miriCallTerminatorExactWP_iff) ∧
    (type_of% @miriStepCallTerminatorExactWP_iff) ∧
    (type_of% @miriTerminatorExactWP_iff) ∧
    (type_of% @miriBeforeStackPopWithEnsure_disabled_exactWP_iff) ∧
    (type_of% @miriBeforeStackPopWithEnsure_singleLive_exactWP_iff) ∧
    (type_of% @miriObserveScalarExactWP_iff) ∧
    (type_of% @miriObserveBytesExactWP_iff) ∧
    (type_of% @miriObserveRawBytesExactWP_iff) ∧
    (type_of% @miriObserveBytes_uninit_err_exactWP) ∧
    (type_of% @miriObserveBytes_ok_exactWP) ∧
    (type_of% @miriObserveScalar_state_immutable) ∧
    (type_of% @miriObserveBytes_state_immutable) ∧
    (type_of% @miriObserveMemoryExactWP_iff) ∧
    (type_of% @miriObserveMemory_state_immutable) ∧
    (type_of% @lookupLiveAlloc_eq_getAllocRaw_live) ∧
    (type_of% @miriObserveMemory_agrees_getAllocRaw) ∧
    (type_of% @miriObserveMemory_frame_invariant_iff) ∧
    (type_of% @lookupLiveAlloc_none_agrees_getAllocRaw_error) ∧
    (type_of% @miriRawMemoryReadBytesExactWP_iff) ∧
    (type_of% @miriObserveMemory_then_treeRange_exactWP_iff) ∧
    (type_of% @miriTreeRange_preserves_allocObservation) ∧
    (type_of% @miriObserveMemory_then_instruction_exactWP_iff) ∧
    (type_of% @miriObserveMemory_then_callDispatch_exactWP_iff) ∧
    (type_of% @miriV2026_performPermAccess_eq_vendored_performAccess) ∧
    (type_of% @miriV2026_associatedAccess_eq_vendored) ∧
    (type_of% @miriV2026_strongestSifa_eq_vendored) ∧
    (type_of% @miriV2026_permLE_eq_vendored) ∧
    (type_of% @miriV2026_skipIfKnownNoop_eq_vendored) ∧
    (type_of% @miriV2026_performLocAccess_eq_vendored_locationState) ∧
    (type_of% @miriV2026_preventsDealloc_eq_vendored_deallocGuard) ∧
    (type_of% @miriV2026_v2026_vendored_triangle) ∧
    (type_of% @witness_positive_initial_tree_range_observe_and_release) ∧
    (type_of% @witness_negative_tree_protected_foreign_and_frozen_local_write_ub) ∧
    (type_of% @witness_negative_uninit_memory_observation_refutation) ∧
    (type_of% @witness_call_dispatch_positive_and_negative_refutations) ∧
    (type_of% @witness_call_dispatch_foreign_emulate_and_call_terminator) ∧
    (type_of% @witness_translateBody_positive_multiStmt_and_negative_deadReturn_ub) ∧
    (type_of% @witness_v2026_capturedMir_tree_borrows_ub_triangle) ∧
    (type_of% @witness_tb_enabled_translateBody_positive_and_negative_ub_refutations) ∧
    (type_of% @witness_tb_hooks_agree_vendored_machineMemoryHooks) ∧
    (type_of% @ep1GlobalAddressState_ptrGetAlloc_wildcard_strict) ∧
    (type_of% @witness_vendored_placeMachine_tb_step_positive_and_ub_refutations) :=
  ⟨@miriTreeNewChildExactWP_iff, @miriTreeInitialSetupExactWP_iff, @miriTreeRangeExactWP_iff,
   @miriTreeRangeSymbolicExactWP_iff, @miriTreeInitAndRangeExactWP_iff,
   @miriTreeRangeSeqExactWP_iff, @miriTreeRangeChainExactWP_iff,
   @miriTreeRangeThenReleaseExactWP_iff, @miriTreeRange_preserves_topology,
   @miriTreeRange_missingTag_frame_exactWP, @miriProtectedTags_remove_ne,
   @miriProtectedTags_insert_ne, @miriEndCall_preserves_unlisted_protector,
   @miriBeforeMemoryReadExactWP_iff, @miriBeforeMemoryWriteExactWP_iff,
   @miriPlaceMachineMemoryAccessExactWP_iff, @miriPlaceMachineWriteMemoryExactWP_iff,
   @miriPlaceMachineReadImmediateExactWP_iff,
   @miriInstructionExactWP_iff, @miriInstructionExactWP_nop_frame,
   @miriInstructionExactWP_meta_frame,
   @annealInstruction_storageDead_returnPlace_err_exactWP,
   @miriInstructionExactWP_setDiscriminant_iff,
   @miriEvalRvalueIntoPlaceExactWP_iff, @miriInstructionAssignRvalueExactWP_iff,
   @miriInstructionAssign_copyForDeref_err_exactWP, @miriInstructionAssign_use_exactWP_iff,
   @miriMachineStorageDeadExactWP_iff, @miriMachineStorageDead_imm_frame_otherLocals,
   @miriStepStmtExactWP_iff,
   @miriStepStmt_callerFrames_preserved, @miriStepStmt_frame_callerStack,
   @miriCallDispatchExactWP_iff,
   @miriCallDispatch_missingForeign_exactWP, @miriCallDispatch_backendError_exactWP,
   @miriCallDispatch_loadMir_exactWP, @miriCallDispatch_foreignEmulate_exactWP,
   @miriCallExtraExactWP_iff,
   @miriForeignEmulate_abort_exactWP, @miriForeignEmulate_noAllocShim_exactWP,
   @miriCallTerminatorExactWP_iff, @miriStepCallTerminatorExactWP_iff,
   @miriTerminatorExactWP_iff,
   @miriBeforeStackPopWithEnsure_disabled_exactWP_iff,
   @miriBeforeStackPopWithEnsure_singleLive_exactWP_iff,
   @miriObserveScalarExactWP_iff, @miriObserveBytesExactWP_iff, @miriObserveRawBytesExactWP_iff,
   @miriObserveBytes_uninit_err_exactWP, @miriObserveBytes_ok_exactWP,
   @miriObserveScalar_state_immutable, @miriObserveBytes_state_immutable,
   @miriObserveMemoryExactWP_iff, @miriObserveMemory_state_immutable,
   @lookupLiveAlloc_eq_getAllocRaw_live, @miriObserveMemory_agrees_getAllocRaw,
   @miriObserveMemory_frame_invariant_iff, @lookupLiveAlloc_none_agrees_getAllocRaw_error,
   @miriRawMemoryReadBytesExactWP_iff,
   @miriObserveMemory_then_treeRange_exactWP_iff, @miriTreeRange_preserves_allocObservation,
   @miriObserveMemory_then_instruction_exactWP_iff,
   @miriObserveMemory_then_callDispatch_exactWP_iff,
   @miriV2026_performPermAccess_eq_vendored_performAccess,
   @miriV2026_associatedAccess_eq_vendored, @miriV2026_strongestSifa_eq_vendored,
   @miriV2026_permLE_eq_vendored, @miriV2026_skipIfKnownNoop_eq_vendored,
   @miriV2026_performLocAccess_eq_vendored_locationState,
   @miriV2026_preventsDealloc_eq_vendored_deallocGuard,
   @miriV2026_v2026_vendored_triangle,
   @witness_positive_initial_tree_range_observe_and_release,
   @witness_negative_tree_protected_foreign_and_frozen_local_write_ub,
   @witness_negative_uninit_memory_observation_refutation,
   @witness_call_dispatch_positive_and_negative_refutations,
   @witness_call_dispatch_foreign_emulate_and_call_terminator,
   @witness_translateBody_positive_multiStmt_and_negative_deadReturn_ub,
   @witness_v2026_capturedMir_tree_borrows_ub_triangle,
   @witness_tb_enabled_translateBody_positive_and_negative_ub_refutations,
   @witness_tb_hooks_agree_vendored_machineMemoryHooks,
   @ep1GlobalAddressState_ptrGetAlloc_wildcard_strict,
   @witness_vendored_placeMachine_tb_step_positive_and_ub_refutations⟩

section AxiomAndIsolationAudit
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let isDoName : Lean.Name → Bool := fun u =>
    (`Std.Do).isPrefixOf u || (`Std.Tactic.Do).isPrefixOf u || (`Std.WP).isPrefixOf u
  let isToolchain : Lean.Name → Bool := fun m =>
    (`Init).isPrefixOf m || (`Std).isPrefixOf m || (`Lean).isPrefixOf m
  let ns := `LeanMiriSpec.InitialStateTreeBorrowsWpLM
  -- 1. (a) Strict transitive MiniRustSpec exclusion across ALL loaded modules.
  for modName in env.header.moduleNames do
    if (`MiniRustSpec).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported"
  -- 2. (a) Zero direct Std.Do / Std.Tactic.Do / Std.WP imports by this module.
  for imp in env.header.imports do
    if isDoName imp.module then
      throwError "Std.Do isolation violation: direct import {imp.module} is forbidden"
  -- 2. (b) Toolchain containment: EVERY loaded module that directly imports a Std.Do module is
  --        itself a toolchain module (Init.* / Std.* / Lean.*): no project, vendored, or
  --        third-party module bridges into Std.Do.
  let mut idx : Lean.NameMap Nat := {}
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    idx := idx.insert modName i
    unless isToolchain modName do
      if h : i < env.header.moduleData.size then
        for imp in env.header.moduleData[i].imports do
          if isDoName imp.module then
            throwError "Std.Do containment violation: non-toolchain module {modName} imports {imp.module}"
  -- 2. (c) `Anneal.MiriTreeBorrowsV2026`'s full transitive import closure is Std.Do-, Lean-,
  --        Miri-, LeanMiriSpec-, and MiniRustSpec-free.
  let mut seenM : Lean.NameSet := {}
  let mut todoM : Array Lean.Name := #[`Anneal.MiriTreeBorrowsV2026]
  while !todoM.isEmpty do
    let m := todoM.back!
    todoM := todoM.pop
    if seenM.contains m then continue
    seenM := seenM.insert m
    if isDoName m || (`Lean).isPrefixOf m || (`MiniRustSpec).isPrefixOf m ||
        (`Miri).isPrefixOf m || (`LeanMiriSpec).isPrefixOf m then
      throwError "Anneal.MiriTreeBorrowsV2026 import-closure violation: reaches {m}"
    if let some i := idx.find? m then
      if h : i < env.header.moduleData.size then
        for imp in env.header.moduleData[i].imports do
          todoM := todoM.push imp.module
  unless seenM.contains `Trusted.Rustc.V2026_06_01.MirSemantics.Statements do
    throwError "Anneal.MiriTreeBorrowsV2026 import-closure audit vacuous"
  -- 2. (d) The full transitive CONSTANT-dependency closure (types AND values) of EVERY declaration
  --        defined in this module (both public AND private `_private.*` helpers in `map₂`)
  --        contains ZERO Std.Do / Std.Tactic.Do / Std.WP / MiniRustSpec constants.
  let mut seenC : Lean.NameSet := {}
  let mut todoC : Array Lean.Name := #[]
  for (c, _) in env.constants.map₂.toList do
    todoC := todoC.push c
  while !todoC.isEmpty do
    let n := todoC.back!
    todoC := todoC.pop
    if seenC.contains n then continue
    seenC := seenC.insert n
    if isDoName n || (`MiniRustSpec).isPrefixOf n then
      throwError "constant-closure isolation violation: {ns} transitively depends on {n}"
    if let some ci := env.find? n then
      for u in ci.type.getUsedConstants do
        unless seenC.contains u do todoC := todoC.push u
      if let some v := ci.value? (allowOpaque := true) then
        for u in v.getUsedConstants do
          unless seenC.contains u do todoC := todoC.push u
  unless seenC.contains `Miri.TreeBorrows.BorrowTree.performBorrowAccessRange &&
      seenC.contains `Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryRead &&
      seenC.contains `Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryWrite &&
      seenC.contains `Miri.Interpreter.PlaceMachine.memoryAccess &&
      seenC.contains `Miri.Interpreter.PlaceMachine.accessHooks &&
      seenC.contains `Miri.Interpreter.PlaceMachine.writeMemory &&
      seenC.contains `Miri.Interpreter.PlaceMachine.readImmediate &&
      seenC.contains `Miri.Interpreter.PlaceMachine.placeHooks &&
      seenC.contains `Miri.Interpreter.evalPlace &&
      seenC.contains `Miri.Interpreter.placeToOp &&
      seenC.contains `Miri.Interpreter.writePlaceImmediate &&
      seenC.contains `Miri.Memory.AllocAddresses.GlobalAddressState.ptrGetAlloc &&
      seenC.contains `Miri.Interpreter.MachineHooks.beforeStackPopWithEnsure &&
      seenC.contains `Miri.Interpreter.evalRvalueIntoPlace &&
      seenC.contains `Miri.Interpreter.MachineHooks.storageDead &&
      seenC.contains `Miri.Interpreter.Step.step &&
      seenC.contains `Miri.Interpreter.ForeignItems.emulate &&
      seenC.contains `Miri.Interpreter.RawMemoryMachine.readBytes &&
      seenC.contains `Miri.Memory.MemoryLifecycle.getAllocRaw do
    throwError "constant-closure isolation audit vacuous"
  -- 2. (e) `Anneal.MiriTreeBorrowsV2026` header guarantee, enforced (that module cannot import
  --        `Lean`, so it is checked here): EVERY theorem AND definition it declares (INCLUDING
  --        `private` ones) depends strictly on axioms `⊆ {propext}`.
  let some tbIdx := env.getModuleIdx? `Anneal.MiriTreeBorrowsV2026
    | throwError "Anneal.MiriTreeBorrowsV2026 is not loaded"
  let mut tbThms : Nat := 0
  let mut tbDefs : Nat := 0
  for (c, info) in env.constants.map₁.toList do
    if env.getModuleIdxFor? c == some tbIdx then
      match info with
      | .thmInfo _ =>
        tbThms := tbThms + 1
        for a in ← liftCoreM <| Lean.collectAxioms c do
          unless a == ``propext do
            throwError "Anneal.MiriTreeBorrowsV2026 axiom-purity violation: theorem {c} depends on {a}"
      | .defnInfo _ =>
        tbDefs := tbDefs + 1
        for a in ← liftCoreM <| Lean.collectAxioms c do
          unless a == ``propext do
            throwError "Anneal.MiriTreeBorrowsV2026 axiom-purity violation: def {c} depends on {a}"
      | _ => pure ()
  if tbThms < 150 || tbDefs < 30 then
    throwError "Anneal.MiriTreeBorrowsV2026 axiom-purity audit vacuous: only {tbThms} theorems, {tbDefs} defs"
  -- 3. Bridge-reality audit: confirm our theorems genuinely reach REAL vendored Miri,
  --    Anneal.MiriTreeBorrowsV2026, AnnealExactWP, and translateBody.
  let bridgeReq : List (Lean.Name × Lean.Name) :=
    [ (ns ++ `miriTreeNewChildExactWP_iff, `Miri.TreeBorrows.BorrowTree.newChild),
      (ns ++ `miriTreeInitialSetupExactWP_iff, `Miri.TreeBorrows.BorrowTree.new),
      (ns ++ `miriTreeRangeExactWP_iff, `Miri.TreeBorrows.BorrowTree.performBorrowAccessRange),
      (ns ++ `miriTreeRangeThenReleaseExactWP_iff, `Miri.TreeBorrows.BorrowTree.releaseProtector),
      (ns ++ `miriBeforeMemoryReadExactWP_iff, `Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryRead),
      (ns ++ `miriBeforeMemoryWriteExactWP_iff, `Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryWrite),
      (ns ++ `miriPlaceMachineMemoryAccessExactWP_iff, `Miri.Interpreter.PlaceMachine.memoryAccess),
      (ns ++ `miriPlaceMachineWriteMemoryExactWP_iff, `Miri.Interpreter.PlaceMachine.writeMemory),
      (ns ++ `miriPlaceMachineReadImmediateExactWP_iff, `Miri.Interpreter.PlaceMachine.readImmediate),
      (ns ++ `miriInstructionExactWP_iff, `Miri.Interpreter.Step.evalStatement),
      (ns ++ `miriEvalRvalueIntoPlaceExactWP_iff, `Miri.Interpreter.evalRvalueIntoPlace),
      (ns ++ `miriMachineStorageDeadExactWP_iff, `Miri.Interpreter.MachineHooks.storageDead),
      (ns ++ `miriStepStmtExactWP_iff, `Miri.Interpreter.Step.step),
      (ns ++ `miriCallDispatchExactWP_iff, `Miri.Interpreter.CallDispatchMachine.findMirOrEvalFn),
      (ns ++ `miriCallDispatch_foreignEmulate_exactWP, `Miri.Interpreter.ForeignItems.emulate),
      (ns ++ `miriForeignEmulate_abort_exactWP, `Miri.Interpreter.ForeignItems.emulate),
      (ns ++ `miriForeignEmulate_noAllocShim_exactWP, `Miri.Interpreter.ForeignItems.emulate),
      (ns ++ `miriCallExtraExactWP_iff, `Miri.Interpreter.CallDispatchMachine.callExtra),
      (ns ++ `miriCallTerminatorExactWP_iff, `Miri.Interpreter.ControlFlow.evalTerminator),
      (ns ++ `miriTerminatorExactWP_iff, `Miri.Interpreter.ControlFlow.evalTerminator),
      (ns ++ `miriObserveScalarExactWP_iff, `Miri.Memory.Allocation.readScalar),
      (ns ++ `miriObserveBytesExactWP_iff, `Miri.Memory.Allocation.getBytesStripProvenance),
      (ns ++ `miriObserveMemoryExactWP_iff, `Miri.Memory.Allocation.readScalar),
      (ns ++ `lookupLiveAlloc_eq_getAllocRaw_live, `Miri.Memory.MemoryLifecycle.getAllocRaw),
      (ns ++ `lookupLiveAlloc_none_agrees_getAllocRaw_error, `Miri.Memory.MemoryLifecycle.getAllocRaw),
      (ns ++ `miriObserveMemory_agrees_getAllocRaw, `Miri.Memory.MemoryLifecycle.getAllocRaw),
      (ns ++ `miriRawMemoryReadBytesExactWP_iff, `Miri.Interpreter.RawMemoryMachine.readBytes),
      (ns ++ `miriV2026_performPermAccess_eq_vendored_performAccess,
        `Anneal.MiriTreeBorrowsV2026.miriPerformPermAccess),
      (ns ++ `miriV2026_performPermAccess_eq_vendored_performAccess,
        `Miri.TreeBorrows.performAccess),
      (ns ++ `miriV2026_v2026_vendored_triangle,
        `Trusted.Rustc.V2026_06_01.MirSemantics.treeBorrowPermTransition),
      (ns ++ `witness_translateBody_positive_multiStmt_and_negative_deadReturn_ub,
        `LeanMiriSpec.Correspondence.translateBody),
      (ns ++ `witness_v2026_capturedMir_tree_borrows_ub_triangle,
        `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn),
      (ns ++ `witness_v2026_capturedMir_tree_borrows_ub_triangle,
        `Anneal.MiriTreeBorrowsV2026.miriPerformLocAccess),
      (ns ++ `witness_v2026_capturedMir_tree_borrows_ub_triangle,
        `Miri.TreeBorrows.performAccess),
      (ns ++ `witness_tb_hooks_agree_vendored_machineMemoryHooks,
        `Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryWrite),
      (ns ++ `witness_tb_hooks_agree_vendored_machineMemoryHooks,
        `Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryRead),
      (ns ++ `witness_tb_enabled_translateBody_positive_and_negative_ub_refutations,
        `LeanMiriSpec.Correspondence.translateBody),
      (ns ++ `witness_tb_enabled_translateBody_positive_and_negative_ub_refutations,
        `Miri.Interpreter.Step.step),
      (ns ++ `witness_tb_enabled_translateBody_positive_and_negative_ub_refutations,
        `Miri.TreeBorrows.BorrowTree.performBorrowAccessRange),
      (ns ++ `witness_vendored_placeMachine_tb_step_positive_and_ub_refutations,
        `LeanMiriSpec.Correspondence.translateBody),
      (ns ++ `witness_vendored_placeMachine_tb_step_positive_and_ub_refutations,
        `Miri.Interpreter.Step.step),
      (ns ++ `witness_vendored_placeMachine_tb_step_positive_and_ub_refutations,
        `Miri.Interpreter.PlaceMachine.readImmediate),
      (ns ++ `witness_vendored_placeMachine_tb_step_positive_and_ub_refutations,
        `Miri.Interpreter.MachineHooks.storageDead),
      (ns ++ `witness_vendored_placeMachine_tb_step_positive_and_ub_refutations,
        `Miri.Interpreter.ControlFlow.evalTerminator),
      (ns ++ `witness_vendored_placeMachine_tb_step_positive_and_ub_refutations,
        `Miri.Memory.AllocAddresses.GlobalAddressState.ptrGetAlloc),
      (ns ++ `witness_vendored_placeMachine_tb_step_positive_and_ub_refutations,
        `Miri.Interpreter.MachineHooks.beforeStackPopWithEnsure),
      (ns ++ `witness_vendored_placeMachine_tb_step_positive_and_ub_refutations,
        `Miri.Interpreter.PlaceMachine.placeHooks),
      (ns ++ `witness_vendored_placeMachine_tb_step_positive_and_ub_refutations,
        `Miri.Interpreter.evalPlace),
      (ns ++ `witness_vendored_placeMachine_tb_step_positive_and_ub_refutations,
        `Miri.Interpreter.writePlaceImmediate),
      (ns ++ `miriBeforeStackPopWithEnsure_singleLive_exactWP_iff,
        `Miri.Interpreter.MachineHooks.beforeStackPopWithEnsure),
      (ns ++ `ep1GlobalAddressState_ptrGetAlloc_wildcard_strict,
        `Miri.Memory.AllocAddresses.GlobalAddressState.ptrGetAlloc),
      (ns ++ `miriTreeRangeExactWP_iff, `Anneal.ExactWpAndSmartCtors.AnnealExactWP) ]
  for (thm, req) in bridgeReq do
    let some ci := env.find? thm | throwError "bridge audit: {thm} missing"
    let mut seen : NameSet := {}
    let mut todo : Array Lean.Name := ci.type.getUsedConstants
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      if n == req then break
      if env.constants.map₂.contains n ||
          ns.isPrefixOf n || (`LeanMiriSpec.ExactWpAndMemoryFrameLM).isPrefixOf n then
        if let some (.defnInfo v) := env.find? n then
          todo := todo ++ v.value.getUsedConstants
    unless seen.contains req do
      throwError "shadow-evaluator audit: {thm} does not reach real {req}"
  -- 4. Standard-3-axiom purity audit across ALL declarations in env.constants.map₂.
  let mut theorems : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    for a in ← liftCoreM <| Lean.collectAxioms c do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      if a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
        throwError "{c} depends on forbidden axiom {a}"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    if ns.isPrefixOf c && !c.isInternal then
      if let .thmInfo _ := info then theorems := theorems + 1
  if theorems < 30 then
    throwError "axiom audit vacuous: only {theorems} theorems seen"

end AxiomAndIsolationAudit

end LeanMiriSpec.InitialStateTreeBorrowsWpLM
