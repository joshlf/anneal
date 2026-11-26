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
  let some (.concrete allocId tag) := mplace.ptr.provenance | return ()
  let some base := st.machine.lookupBaseAddr allocId
    | throw (.undefinedBehavior "Tree Borrows access on allocation without base address")
  let offset := Size.ofBytes (mplace.ptr.offset.bytes - base)
  match st.machine.memory.live.find? (fun row => row.1 == allocId) with
  | none => throw (.undefinedBehavior "Tree Borrows access on dangling allocation")
  | some (_, ⟨_, alloc⟩) =>
    match alloc.extra with
    | none => return ()
    | some tree =>
      let res := tree.performBorrowAccessRange (.concrete tag) offset size kind
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
unmodified `annealStepHooks.assign`! -/
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
  let some (.concrete allocId tag) := mplace.ptr.provenance | return ()
  let some base := st.machine.lookupBaseAddr allocId
    | throw (.undefinedBehavior "Tree Borrows access on allocation without base address")
  let offset := Size.ofBytes (mplace.ptr.offset.bytes - base)
  match st.machine.memory.live.find? (fun row => row.1 == allocId) with
  | none => throw (.undefinedBehavior "Tree Borrows access on dangling allocation")
  | some (_, ⟨_, alloc⟩) =>
    match alloc.extra with
    | none => return ()
    | some tree =>
      let res := performBorrowAccessRangeLMU tree (.concrete tag) offset size kind
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

end TbEnabledTranslateBodyMiriExecution

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
    (type_of% @miriInstructionExactWP_iff) ∧
    (type_of% @miriInstructionExactWP_nop_frame) ∧
    (type_of% @miriInstructionExactWP_meta_frame) ∧
    (type_of% @annealInstruction_storageDead_returnPlace_err_exactWP) ∧
    (type_of% @miriInstructionExactWP_setDiscriminant_iff) ∧
    (type_of% @miriStepStmtExactWP_iff) ∧
    (type_of% @miriStepStmt_callerFrames_preserved) ∧
    (type_of% @miriStepStmt_frame_callerStack) ∧
    (type_of% @miriCallDispatchExactWP_iff) ∧
    (type_of% @miriCallDispatch_missingForeign_exactWP) ∧
    (type_of% @miriCallDispatch_backendError_exactWP) ∧
    (type_of% @miriCallDispatch_loadMir_exactWP) ∧
    (type_of% @miriCallDispatch_foreignEmulate_exactWP) ∧
    (type_of% @miriCallExtraExactWP_iff) ∧
    (type_of% @miriCallTerminatorExactWP_iff) ∧
    (type_of% @miriStepCallTerminatorExactWP_iff) ∧
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
    (type_of% @witness_tb_enabled_translateBody_positive_and_negative_ub_refutations) :=
  ⟨@miriTreeNewChildExactWP_iff, @miriTreeInitialSetupExactWP_iff, @miriTreeRangeExactWP_iff,
   @miriTreeRangeSymbolicExactWP_iff, @miriTreeInitAndRangeExactWP_iff,
   @miriTreeRangeSeqExactWP_iff, @miriTreeRangeChainExactWP_iff,
   @miriTreeRangeThenReleaseExactWP_iff, @miriTreeRange_preserves_topology,
   @miriTreeRange_missingTag_frame_exactWP, @miriProtectedTags_remove_ne,
   @miriProtectedTags_insert_ne, @miriEndCall_preserves_unlisted_protector,
   @miriBeforeMemoryReadExactWP_iff, @miriBeforeMemoryWriteExactWP_iff,
   @miriInstructionExactWP_iff, @miriInstructionExactWP_nop_frame,
   @miriInstructionExactWP_meta_frame,
   @annealInstruction_storageDead_returnPlace_err_exactWP,
   @miriInstructionExactWP_setDiscriminant_iff, @miriStepStmtExactWP_iff,
   @miriStepStmt_callerFrames_preserved, @miriStepStmt_frame_callerStack,
   @miriCallDispatchExactWP_iff,
   @miriCallDispatch_missingForeign_exactWP, @miriCallDispatch_backendError_exactWP,
   @miriCallDispatch_loadMir_exactWP, @miriCallDispatch_foreignEmulate_exactWP,
   @miriCallExtraExactWP_iff,
   @miriCallTerminatorExactWP_iff, @miriStepCallTerminatorExactWP_iff,
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
   @witness_tb_enabled_translateBody_positive_and_negative_ub_refutations⟩

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
      seenC.contains `Miri.Interpreter.Step.step &&
      seenC.contains `Miri.Interpreter.ForeignItems.emulate &&
      seenC.contains `Miri.Interpreter.RawMemoryMachine.readBytes &&
      seenC.contains `Miri.Memory.MemoryLifecycle.getAllocRaw do
    throwError "constant-closure isolation audit vacuous"
  -- 3. Bridge-reality audit: confirm our theorems genuinely reach REAL vendored Miri,
  --    Anneal.MiriTreeBorrowsV2026, AnnealExactWP, and translateBody.
  let bridgeReq : List (Lean.Name × Lean.Name) :=
    [ (ns ++ `miriTreeNewChildExactWP_iff, `Miri.TreeBorrows.BorrowTree.newChild),
      (ns ++ `miriTreeInitialSetupExactWP_iff, `Miri.TreeBorrows.BorrowTree.new),
      (ns ++ `miriTreeRangeExactWP_iff, `Miri.TreeBorrows.BorrowTree.performBorrowAccessRange),
      (ns ++ `miriTreeRangeThenReleaseExactWP_iff, `Miri.TreeBorrows.BorrowTree.releaseProtector),
      (ns ++ `miriBeforeMemoryReadExactWP_iff, `Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryRead),
      (ns ++ `miriBeforeMemoryWriteExactWP_iff, `Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryWrite),
      (ns ++ `miriInstructionExactWP_iff, `Miri.Interpreter.Step.evalStatement),
      (ns ++ `miriStepStmtExactWP_iff, `Miri.Interpreter.Step.step),
      (ns ++ `miriCallDispatchExactWP_iff, `Miri.Interpreter.CallDispatchMachine.findMirOrEvalFn),
      (ns ++ `miriCallDispatch_foreignEmulate_exactWP, `Miri.Interpreter.ForeignItems.emulate),
      (ns ++ `miriCallExtraExactWP_iff, `Miri.Interpreter.CallDispatchMachine.callExtra),
      (ns ++ `miriCallTerminatorExactWP_iff, `Miri.Interpreter.ControlFlow.evalTerminator),
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
      (ns ++ `witness_tb_enabled_translateBody_positive_and_negative_ub_refutations,
        `LeanMiriSpec.Correspondence.translateBody),
      (ns ++ `witness_tb_enabled_translateBody_positive_and_negative_ub_refutations,
        `Miri.Interpreter.Step.step),
      (ns ++ `witness_tb_enabled_translateBody_positive_and_negative_ub_refutations,
        `Miri.TreeBorrows.BorrowTree.performBorrowAccessRange),
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
