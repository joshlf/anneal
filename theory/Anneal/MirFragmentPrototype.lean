-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted
import Anneal.PureMirExec

namespace Anneal.MirFragmentPrototype

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec

/-!
# Track P Prototype: 5-Element `MirFragment` Lattice (`Anneal.MirFragmentPrototype`)

Converges Anneal's MIR verification pipeline with Zircon 2.1's declared fragment
lattice (`Zircon/IR/Fragment.lean` & `Zircon/Specs/FragmentSpec.lean`),
replacing implicit tactic preconditions and ad-hoc boolean flags on
`MirLiftingProfile` with a kernel-checked 5-element bounded lattice over real
`Trusted.Rustc.V2026_06_01.MirAst.CapturedMir` bodies:

1. **`MirFragment.pureLoopFree`** (`0`):
   Syntactically pure MIR (`Anneal.PureMirExec.checkPureMir`) with no CFG
   back-edges (`hasCfgBackedge body = false`). Discharged in a single pass by
   `#mir_lift` / `LiftBlock` / `LiftStmtsTerminator`.
2. **`MirFragment.pureBoundedLoop`** (`1`):
   Syntactically pure MIR (`checkBodyFragment .pureBoundedLoop body =
   Anneal.PureMirExec.checkPureMir body`) permitting arbitrary pure `goto` /
   `switchInt` / `assert` / `drop` control-flow loops. Discharged via
   `Anneal.MirLoops` (`forRangeUp`, `mirWpConverges_whileRank`, `runCfgToBlock`).
3. **`MirFragment.treeBorrowsLocal`** (`2`):
   Extends `.pureBoundedLoop` with local references (`Rvalue.ref`), raw pointers
   (`Rvalue.rawPtr`), pointer dereferences (`ProjectionElem.deref`), unsafe
   binder projections (`ProjectionElem.unwrapUnsafeBinder`), deref copies
   (`Rvalue.copyForDeref`), in-bounds pointer offsets (`BinOp.offset`), local
   pointer casts (`CastKind.pointerCoercion`, `CastKind.ptrToPtr`), and Tree
   Borrows retags (`StatementKind.retag`). Discharged via
   `Anneal.SepLogicLenses` (`verifyStatefulMir_of_sepLenses`) or stateful
   `runCfgToBlock`.
4. **`MirFragment.intrinsicCopy`** (`3`):
   Extends `.treeBorrowsLocal` with non-overlapping bulk memory copies
   (`StatementKind.intrinsic (.copyNonOverlapping src dst count)`) and global
   constant allocations (`ConstValue.indirect`, `ConstValue.slice (.ptr ..)`),
   while still excluding interprocedural calls and inline assembly. Discharged
   via `evalCopyNonOverlappingPermOk` and stateful memory framing.
5. **`MirFragment.fullMir`** (`4`):
   The complete `CapturedMir` grammar, admitting interprocedural calls
   (`TerminatorKind.call`, `TerminatorKind.tailCall`), inline assembly
   (`TerminatorKind.inlineAsm`), `CastKind.fnPtrToPtr`,
   `Rvalue.threadLocalRef`, `Rvalue.shallowInitBox`, and
   `StatementKind.backwardIncompatibleDropHint`. Discharged via modular call
   contracts (`PureMirModularConverges`), linked callee tables
   (`checkPureMirWithCallees`), or `#[spec(trusted)]` / Miri boundaries.
-/

/-! ## 1. The 5-Element Bounded Lattice (`MirFragment`) -/

/--
5-element total bounded lattice of Rust `Runtime(PostCleanup)` MIR sub-grammars
ordered by syntactic and semantic expressiveness.
-/
inductive MirFragment : Type where
  /-- Loop-free alias-free pure MIR (`#mir_lift` / `PureMirExec` + DAG CFG). -/
  | pureLoopFree : MirFragment
  /-- Alias-free pure MIR with arbitrary control-flow loops (`PureMirExec` + `MirLoops`). -/
  | pureBoundedLoop : MirFragment
  /-- Intraprocedural Tree Borrows local reference/pointer/retag MIR (`SepLogicLenses`). -/
  | treeBorrowsLocal : MirFragment
  /-- Intraprocedural MIR with `copy_nonoverlapping` and global memory constants. -/
  | intrinsicCopy : MirFragment
  /-- Full `Runtime(PostCleanup)` MIR including calls and inline assembly. -/
  | fullMir : MirFragment
  deriving DecidableEq, Repr

/--
Fail-closed default: an unclassified body is only claimed to be in `.fullMir`
(matching `MirFragment::default()` in `crates/cargo-anneal/src/scaffold.rs`).
-/
instance : Inhabited MirFragment := ⟨.fullMir⟩

namespace MirFragment

/-- Canonical snake_case identifier matching `crates/cargo-anneal/src/scaffold.rs`
and `.anneal/spec-lock.json` (`mir_fragment`). -/
@[simp]
def asStr : MirFragment → String
  | .pureLoopFree => "pure_loop_free"
  | .pureBoundedLoop => "pure_bounded_loop"
  | .treeBorrowsLocal => "tree_borrows_local"
  | .intrinsicCopy => "intrinsic_copy"
  | .fullMir => "full_mir"

/-- Canonical qualified Lean constructor name emitted by `cargo-anneal`. -/
@[simp]
def leanCtor : MirFragment → String
  | .pureLoopFree => "MirFragment.pureLoopFree"
  | .pureBoundedLoop => "MirFragment.pureBoundedLoop"
  | .treeBorrowsLocal => "MirFragment.treeBorrowsLocal"
  | .intrinsicCopy => "MirFragment.intrinsicCopy"
  | .fullMir => "MirFragment.fullMir"

/-- Parse a `MirFragment` from its snake_case or Lean constructor string. -/
def fromStr? : String → Option MirFragment
  | "pure_loop_free" | "MirFragment.pureLoopFree" | "pureLoopFree" => some .pureLoopFree
  | "pure_bounded_loop" | "MirFragment.pureBoundedLoop" | "pureBoundedLoop" => some .pureBoundedLoop
  | "tree_borrows_local" | "MirFragment.treeBorrowsLocal" | "treeBorrowsLocal" =>
    some .treeBorrowsLocal
  | "intrinsic_copy" | "MirFragment.intrinsicCopy" | "intrinsicCopy" => some .intrinsicCopy
  | "full_mir" | "MirFragment.fullMir" | "fullMir" => some .fullMir
  | _ => none

instance : ToString MirFragment where
  toString := asStr

@[simp]
theorem fromStr?_asStr (f : MirFragment) : fromStr? f.asStr = some f := by
  cases f <;> rfl

@[simp]
theorem fromStr?_leanCtor (f : MirFragment) : fromStr? f.leanCtor = some f := by
  cases f <;> rfl

/-- Numeric rank in `0..=4` inducing the linear lattice order on `MirFragment`. -/
@[simp]
def toRank : MirFragment → Nat
  | .pureLoopFree => 0
  | .pureBoundedLoop => 1
  | .treeBorrowsLocal => 2
  | .intrinsicCopy => 3
  | .fullMir => 4

/-- Reconstruct a `MirFragment` from its numeric rank `0..=4`. -/
@[simp]
def ofRank? : Nat → Option MirFragment
  | 0 => some .pureLoopFree
  | 1 => some .pureBoundedLoop
  | 2 => some .treeBorrowsLocal
  | 3 => some .intrinsicCopy
  | 4 => some .fullMir
  | _ => none

@[simp]
theorem ofRank?_toRank (f : MirFragment) : ofRank? f.toRank = some f := by
  cases f <;> rfl

theorem toRank_lt_five (f : MirFragment) : f.toRank < 5 := by
  cases f <;> decide

/-- Exhaustive list of all 5 `MirFragment` levels in strictly ascending order. -/
def all : List MirFragment :=
  [.pureLoopFree, .pureBoundedLoop, .treeBorrowsLocal, .intrinsicCopy, .fullMir]

theorem mem_all (f : MirFragment) : f ∈ all := by
  cases f <;> decide

instance : LE MirFragment where
  le a b := a.toRank ≤ b.toRank

instance : LT MirFragment where
  lt a b := a.toRank < b.toRank

instance : DecidableRel (α := MirFragment) (· ≤ ·) :=
  fun a b => Nat.decLe a.toRank b.toRank

instance : DecidableRel (α := MirFragment) (· < ·) :=
  fun a b => Nat.decLt a.toRank b.toRank

/-- Bottom element of the `MirFragment` lattice (`.pureLoopFree`). -/
@[simp]
def bot : MirFragment := .pureLoopFree

/-- Top element of the `MirFragment` lattice (`.fullMir`). -/
@[simp]
def top : MirFragment := .fullMir

/-- Least upper bound (`a ⊔ b`) in the `MirFragment` lattice. -/
@[simp]
def join (a b : MirFragment) : MirFragment :=
  if a ≤ b then b else a

/-- Greatest lower bound (`a ⊓ b`) in the `MirFragment` lattice. -/
@[simp]
def meet (a b : MirFragment) : MirFragment :=
  if a ≤ b then a else b

theorem le_iff_toRank_le (a b : MirFragment) : a ≤ b ↔ a.toRank ≤ b.toRank :=
  Iff.rfl

theorem lt_iff_toRank_lt (a b : MirFragment) : a < b ↔ a.toRank < b.toRank :=
  Iff.rfl

theorem toRank_injective {a b : MirFragment} (h : a.toRank = b.toRank) : a = b := by
  cases a <;> cases b <;> first | rfl | contradiction

theorem le_refl (a : MirFragment) : a ≤ a := by
  cases a <;> decide

theorem le_trans {a b c : MirFragment} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  Nat.le_trans hab hbc

theorem le_antisymm {a b : MirFragment} (hab : a ≤ b) (hba : b ≤ a) : a = b :=
  toRank_injective (Nat.le_antisymm hab hba)

theorem le_total (a b : MirFragment) : a ≤ b ∨ b ≤ a := by
  cases a <;> cases b <;> decide

theorem lt_iff_le_not_le (a b : MirFragment) : a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  cases a <;> cases b <;> decide

theorem bot_le (a : MirFragment) : bot ≤ a := by
  cases a <;> decide

theorem le_top (a : MirFragment) : a ≤ top := by
  cases a <;> decide

theorem le_join_left (a b : MirFragment) : a ≤ a.join b := by
  cases a <;> cases b <;> decide

theorem le_join_right (a b : MirFragment) : b ≤ a.join b := by
  cases a <;> cases b <;> decide

theorem join_le {a b c : MirFragment} (hac : a ≤ c) (hbc : b ≤ c) : a.join b ≤ c := by
  cases a <;> cases b <;> cases c <;> revert hac hbc <;> decide

theorem join_le_iff (a b c : MirFragment) : a.join b ≤ c ↔ a ≤ c ∧ b ≤ c := by
  cases a <;> cases b <;> cases c <;> decide

theorem join_comm (a b : MirFragment) : a.join b = b.join a := by
  cases a <;> cases b <;> rfl

theorem join_assoc (a b c : MirFragment) : (a.join b).join c = a.join (b.join c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem join_idem (a : MirFragment) : a.join a = a := by
  cases a <;> rfl

theorem meet_le_left (a b : MirFragment) : a.meet b ≤ a := by
  cases a <;> cases b <;> decide

theorem meet_le_right (a b : MirFragment) : a.meet b ≤ b := by
  cases a <;> cases b <;> decide

theorem le_meet {a b c : MirFragment} (hca : c ≤ a) (hcb : c ≤ b) : c ≤ a.meet b := by
  cases a <;> cases b <;> cases c <;> revert hca hcb <;> decide

theorem le_meet_iff (a b c : MirFragment) : c ≤ a.meet b ↔ c ≤ a ∧ c ≤ b := by
  cases a <;> cases b <;> cases c <;> decide

theorem meet_comm (a b : MirFragment) : a.meet b = b.meet a := by
  cases a <;> cases b <;> rfl

theorem meet_assoc (a b c : MirFragment) : (a.meet b).meet c = a.meet (b.meet c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem meet_idem (a : MirFragment) : a.meet a = a := by
  cases a <;> rfl

end MirFragment

export MirFragment (
  toRank_injective le_refl le_trans le_antisymm le_total lt_iff_le_not_le
  bot_le le_top
  le_join_left le_join_right join_le join_le_iff join_comm join_assoc join_idem
  meet_le_left meet_le_right le_meet le_meet_iff meet_comm meet_assoc meet_idem
)

/-! ## 2. CFG Successor Extraction, Back-Edge Analysis & DAG Acyclicity -/

/-- Extract control-flow target basic-block index from an `UnwindAction`. -/
def unwindTargets : UnwindAction → List BasicBlockIdx
  | .cleanup cleanupBlock => [cleanupBlock]
  | .unreachable => []
  | .terminate => []
  | .continue_ => []

/--
Extract all outgoing control-flow target basic-block indices from a
`TerminatorKind`, matching `extract_terminator_targets` in
`crates/cargo-anneal/src/scaffold.rs` 1-to-1.
-/
def terminatorTargets : TerminatorKind → List BasicBlockIdx
  | .goto target => [target]
  | .switchInt _ targets => targets.branches.map Prod.snd ++ [targets.otherwise]
  | .unwindResume => []
  | .unwindTerminate => []
  | .return_ => []
  | .unreachable => []
  | .drop _ target unwind => target :: unwindTargets unwind
  | .call _ _ _ target unwind =>
    (match target with | some t => [t] | none => []) ++ unwindTargets unwind
  | .tailCall _ _ => []
  | .assert _ _ target unwind => target :: unwindTargets unwind
  | .inlineAsm _ targets unwind => targets ++ unwindTargets unwind

/-- Outgoing CFG successor basic-block indices of a `BasicBlockData`. -/
def blockTargets (bb : BasicBlockData) : List BasicBlockIdx :=
  terminatorTargets bb.terminator.kind

/--
True iff basic block `bb` at 0-based index `bbIdx` has at least one outgoing
edge to a target `succ ≤ bbIdx` (a self-loop or backward jump in index order).
-/
def hasBlockBackedge (bbIdx : BasicBlockIdx) (bb : BasicBlockData) : Bool :=
  (blockTargets bb).any (fun succ => decide (succ ≤ bbIdx))

/-- Helper scanning a suffix of `body.basicBlocks` starting at 0-based index `bbIdx`. -/
def hasCfgBackedgeAux : BasicBlockIdx → List BasicBlockData → Bool
  | _, [] => false
  | bbIdx, bb :: rest =>
    hasBlockBackedge bbIdx bb || hasCfgBackedgeAux (bbIdx + 1) rest

/--
Computable $O(|B|)$ index-order CFG back-edge detector on `body : CapturedMir`,
matching `detect_blocks_and_back_edges` in `crates/cargo-anneal/src/scaffold.rs`.
-/
def hasCfgBackedge (body : CapturedMir) : Bool :=
  hasCfgBackedgeAux 0 body.basicBlocks

/-- Directed control-flow edge `u → v` in `body.basicBlocks`. -/
def CfgEdge (body : CapturedMir) (u v : BasicBlockIdx) : Prop :=
  ∃ bb, Trusted.Sequence.get? body.basicBlocks u = some bb ∧ v ∈ blockTargets bb

/-- Non-empty directed control-flow path `u →⁺ v` in `body.basicBlocks`. -/
inductive CfgPath (body : CapturedMir) : BasicBlockIdx → BasicBlockIdx → Prop where
  | single {u v : BasicBlockIdx} : CfgEdge body u v → CfgPath body u v
  | step {u v w : BasicBlockIdx} :
      CfgEdge body u v → CfgPath body v w → CfgPath body u w

theorem hasBlockBackedge_false_of_hasCfgBackedgeAux_false
    {start : Nat} {bbs : List BasicBlockData} {offset : Nat} {bb : BasicBlockData}
    (h_no : hasCfgBackedgeAux start bbs = false)
    (h_get : Trusted.Sequence.get? bbs offset = some bb) :
    hasBlockBackedge (start + offset) bb = false := by
  induction bbs generalizing start offset with
  | nil => cases h_get
  | cons hd tl ih =>
    simp only [hasCfgBackedgeAux, Bool.or_eq_false_iff] at h_no
    cases offset with
    | zero =>
      cases h_get
      simp only [Nat.add_zero]
      exact h_no.1
    | succ offset' =>
      have h_step := ih h_no.2 h_get
      have h_arith : start + 1 + offset' = start + (offset' + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 offset', ← Nat.add_assoc]
      rw [← h_arith]
      exact h_step

/--
Every CFG edge `u → v` in a body with `hasCfgBackedge body = false` strictly
increases the basic-block index (`u < v`).
-/
theorem cfgEdge_lt_of_hasCfgBackedge_false
    {body : CapturedMir} {u v : BasicBlockIdx}
    (h_no : hasCfgBackedge body = false)
    (h_edge : CfgEdge body u v) :
    u < v := by
  rcases h_edge with ⟨bb, h_get, h_mem⟩
  have h_blk : hasBlockBackedge u bb = false := by
    have h0 := hasBlockBackedge_false_of_hasCfgBackedgeAux_false h_no h_get
    simpa [Nat.zero_add] using h0
  simp only [hasBlockBackedge, List.any_eq_false] at h_blk
  have h_not_le := h_blk v h_mem
  simp only [decide_eq_true_eq] at h_not_le
  exact Nat.lt_of_not_le h_not_le

/--
Every non-empty directed CFG path `u →⁺ v` in a body with
`hasCfgBackedge body = false` strictly increases the basic-block index (`u < v`).
-/
theorem cfgPath_lt_of_hasCfgBackedge_false
    {body : CapturedMir} {u v : BasicBlockIdx}
    (h_no : hasCfgBackedge body = false)
    (h_path : CfgPath body u v) :
    u < v := by
  induction h_path with
  | single h_edge => exact cfgEdge_lt_of_hasCfgBackedge_false h_no h_edge
  | step h_edge _ ih =>
    exact Nat.lt_trans (cfgEdge_lt_of_hasCfgBackedge_false h_no h_edge) ih

/--
**Soundness of `hasCfgBackedge = false` for General DAG Acyclicity**:
If `hasCfgBackedge body = false`, then `body`'s control-flow graph is strictly
acyclic (`∀ u, ¬ CfgPath body u u`).
-/
theorem no_cfg_cycle_of_hasCfgBackedge_false
    {body : CapturedMir}
    (h_no : hasCfgBackedge body = false)
    (u : BasicBlockIdx) :
    ¬ CfgPath body u u := by
  intro h_cycle
  have h_lt := cfgPath_lt_of_hasCfgBackedge_false h_no h_cycle
  exact Nat.lt_irrefl u h_lt

/-! ### Exact specification of the index-order rule (`hasCfgBackedge`) -/

theorem exists_backedge_of_hasCfgBackedgeAux
    {start : Nat} {bbs : List BasicBlockData}
    (h : hasCfgBackedgeAux start bbs = true) :
    ∃ off bb v, Trusted.Sequence.get? bbs off = some bb ∧
      v ∈ blockTargets bb ∧ v ≤ start + off := by
  induction bbs generalizing start with
  | nil => simp [hasCfgBackedgeAux] at h
  | cons hd tl ih =>
    simp only [hasCfgBackedgeAux, Bool.or_eq_true] at h
    rcases h with h_hd | h_tl
    · simp only [hasBlockBackedge, List.any_eq_true, decide_eq_true_eq] at h_hd
      obtain ⟨v, h_mem, h_le⟩ := h_hd
      exact ⟨0, hd, v, rfl, h_mem, h_le⟩
    · obtain ⟨off, bb, v, h_get, h_mem, h_le⟩ := ih h_tl
      refine ⟨off + 1, bb, v, h_get, h_mem, ?_⟩
      have h_eq : start + 1 + off = start + (off + 1) := by omega
      rw [← h_eq]
      exact h_le

/--
**Exact specification of `hasCfgBackedge`** (the rule `scaffold.rs` mirrors in
`detect_blocks_and_back_edges`): `hasCfgBackedge body = true` iff some CFG edge
`u → v` of `body` satisfies `v ≤ u` (a self-loop or a jump to a block whose
index is not larger).
-/
theorem hasCfgBackedge_eq_true_iff (body : CapturedMir) :
    hasCfgBackedge body = true ↔ ∃ u v, CfgEdge body u v ∧ v ≤ u := by
  constructor
  · intro h
    obtain ⟨off, bb, v, h_get, h_mem, h_le⟩ := exists_backedge_of_hasCfgBackedgeAux h
    rw [Nat.zero_add] at h_le
    exact ⟨off, v, ⟨bb, h_get, h_mem⟩, h_le⟩
  · rintro ⟨u, v, h_edge, h_le⟩
    cases h_b : hasCfgBackedge body
    · exact absurd h_le (Nat.not_le_of_lt (cfgEdge_lt_of_hasCfgBackedge_false h_b h_edge))
    · rfl

/--
**Exact forward-numbering characterization of `hasCfgBackedge = false`**:
`hasCfgBackedge body = false` iff every CFG edge `u → v` of `body` strictly
increases basic-block index (`u < v`).
-/
theorem hasCfgBackedge_eq_false_iff (body : CapturedMir) :
    hasCfgBackedge body = false ↔ ∀ u v, CfgEdge body u v → u < v := by
  constructor
  · intro h u v h_edge
    exact cfgEdge_lt_of_hasCfgBackedge_false h h_edge
  · intro h_lt
    cases h_b : hasCfgBackedge body
    · rfl
    · obtain ⟨u, v, h_edge, h_le⟩ := (hasCfgBackedge_eq_true_iff body).mp h_b
      exact absurd h_le (Nat.not_le_of_lt (h_lt u v h_edge))

/-- The source block of every CFG edge is an in-range block index. -/
theorem lt_length_of_cfgEdge {body : CapturedMir} {u v : BasicBlockIdx}
    (h : CfgEdge body u v) : u < body.basicBlocks.length := by
  rcases h with ⟨bb, h_get, _⟩
  exact (List.getElem?_eq_some_iff.mp h_get).1

/-- The source block of every non-empty CFG path is an in-range block index. -/
theorem lt_length_of_cfgPath {body : CapturedMir} {u v : BasicBlockIdx}
    (h : CfgPath body u v) : u < body.basicBlocks.length := by
  cases h with
  | single h_edge => exact lt_length_of_cfgEdge h_edge
  | step h_edge _ => exact lt_length_of_cfgEdge h_edge

/-!
### General DAG acyclicity via verified rank certificates (`isCfgDag`)

The index-order rule is *sound* for acyclicity (`no_cfg_cycle_of_hasCfgBackedge_false`)
but *not complete*: `rustc`'s captured MIR is not reverse-postorder numbered (the
`ReorderBasicBlocks` pass is off by default), so loop-free bodies routinely contain
index back-edges (e.g. arms of a `match` jumping to a shared return block created
before them; see `witnessRustcSharedReturn`, transcribed from the real captured
`core::cmp::PartialOrd::le`). `isCfgDag` is a general, polynomial ($O(n^2 |E|)$)
acyclicity check whose soundness is independent of how its rank function is
computed: any `rank : Nat → Nat` strictly increasing along every in-range edge
certifies that the CFG has no directed cycle.
-/

/--
True iff block `bb` at index `u` has an in-range edge `u → v` (`v < n`) that
violates `rank` (`rank v ≤ rank u`).
-/
def hasBlockRankViolation (rank : Nat → Nat) (n u : Nat) (bb : BasicBlockData) : Bool :=
  (blockTargets bb).any (fun v => decide (v < n) && decide (rank v ≤ rank u))

/-- Helper scanning a suffix of `body.basicBlocks` starting at 0-based index `u`. -/
def hasRankViolationAux (rank : Nat → Nat) (n : Nat) : Nat → List BasicBlockData → Bool
  | _, [] => false
  | u, bb :: rest => hasBlockRankViolation rank n u bb || hasRankViolationAux rank n (u + 1) rest

/-- True iff some in-range CFG edge `u → v` of `body` has `rank v ≤ rank u`. -/
def hasRankViolation (rank : Nat → Nat) (body : CapturedMir) : Bool :=
  hasRankViolationAux rank body.basicBlocks.length 0 body.basicBlocks

theorem hasBlockRankViolation_false_of_hasRankViolationAux_false
    {rank : Nat → Nat} {n start : Nat} {bbs : List BasicBlockData} {off : Nat}
    {bb : BasicBlockData}
    (h_no : hasRankViolationAux rank n start bbs = false)
    (h_get : Trusted.Sequence.get? bbs off = some bb) :
    hasBlockRankViolation rank n (start + off) bb = false := by
  induction bbs generalizing start off with
  | nil => cases h_get
  | cons hd tl ih =>
    simp only [hasRankViolationAux, Bool.or_eq_false_iff] at h_no
    cases off with
    | zero =>
      cases h_get
      simpa using h_no.1
    | succ off' =>
      have h_step := ih h_no.2 h_get
      have h_arith : start + 1 + off' = start + (off' + 1) := by omega
      rw [← h_arith]
      exact h_step

/-- A violation-free `rank` strictly increases along every in-range CFG edge. -/
theorem cfgEdge_rank_lt_of_hasRankViolation_false
    {rank : Nat → Nat} {body : CapturedMir} {u v : BasicBlockIdx}
    (h_no : hasRankViolation rank body = false)
    (h_edge : CfgEdge body u v) (h_v : v < body.basicBlocks.length) :
    rank u < rank v := by
  rcases h_edge with ⟨bb, h_get, h_mem⟩
  have h_blk := hasBlockRankViolation_false_of_hasRankViolationAux_false (start := 0) h_no h_get
  simp only [Nat.zero_add, hasBlockRankViolation, List.any_eq_false, Bool.and_eq_true,
    decide_eq_true_eq, not_and] at h_blk
  exact Nat.lt_of_not_le (h_blk v h_mem h_v)

/-- A violation-free `rank` strictly increases along every CFG path into an in-range block. -/
theorem cfgPath_rank_lt_of_hasRankViolation_false
    {rank : Nat → Nat} {body : CapturedMir} {u w : BasicBlockIdx}
    (h_no : hasRankViolation rank body = false)
    (h_path : CfgPath body u w) (h_w : w < body.basicBlocks.length) :
    rank u < rank w := by
  induction h_path with
  | single h_edge => exact cfgEdge_rank_lt_of_hasRankViolation_false h_no h_edge h_w
  | step h_edge h_rest ih =>
    exact Nat.lt_trans
      (cfgEdge_rank_lt_of_hasRankViolation_false h_no h_edge (lt_length_of_cfgPath h_rest))
      (ih h_w)

/--
**Rank-certificate soundness**: for ANY `rank : Nat → Nat`, if no in-range CFG
edge violates `rank`, then `body`'s CFG has no directed cycle.
-/
theorem no_cfg_cycle_of_hasRankViolation_false
    {rank : Nat → Nat} {body : CapturedMir}
    (h_no : hasRankViolation rank body = false) (u : BasicBlockIdx) :
    ¬ CfgPath body u u := by
  intro h_cycle
  exact Nat.lt_irrefl _
    (cfgPath_rank_lt_of_hasRankViolation_false h_no h_cycle (lt_length_of_cfgPath h_cycle))

theorem hasRankViolationAux_id_eq_hasCfgBackedgeAux {n : Nat} :
    ∀ (u : Nat) (bbs : List BasicBlockData), u + bbs.length ≤ n →
      hasRankViolationAux (fun i => i) n u bbs = hasCfgBackedgeAux u bbs
  | _, [], _ => rfl
  | u, bb :: rest, h_len => by
    have h_len' : u + 1 + rest.length ≤ n := by
      simp only [List.length_cons] at h_len
      omega
    have h_u : u < n := by omega
    simp only [hasRankViolationAux, hasCfgBackedgeAux,
      hasRankViolationAux_id_eq_hasCfgBackedgeAux (u + 1) rest h_len']
    congr 1
    simp only [hasBlockRankViolation, hasBlockBackedge]
    congr 1
    funext v
    by_cases h : v ≤ u
    · simp [h, Nat.lt_of_le_of_lt h h_u]
    · simp [h]

/--
`hasCfgBackedge` is exactly the identity-rank instance of the general certificate
check (`rank = id`), so `no_cfg_cycle_of_hasCfgBackedge_false` is a special case
of `no_cfg_cycle_of_hasRankViolation_false`.
-/
theorem hasRankViolation_id_eq_hasCfgBackedge (body : CapturedMir) :
    hasRankViolation (fun i => i) body = hasCfgBackedge body :=
  hasRankViolationAux_id_eq_hasCfgBackedgeAux 0 body.basicBlocks (by simp)

/--
Every MIR body without an index-order back-edge (`hasCfgBackedge body = false`)
admits an explicit violation-free rank certificate (`rank = id`).
-/
theorem exists_rank_certificate_of_hasCfgBackedge_false
    {body : CapturedMir} (h : hasCfgBackedge body = false) :
    ∃ rank : Nat → Nat, hasRankViolation rank body = false :=
  ⟨fun i => i, (hasRankViolation_id_eq_hasCfgBackedge body).trans h⟩

/-- In-range CFG edges `(u, v)` (`v < n`) of a suffix of `body.basicBlocks` starting at `u`. -/
def cfgEdgeListAux (n : Nat) : Nat → List BasicBlockData → List (Nat × Nat)
  | _, [] => []
  | u, bb :: rest =>
    ((blockTargets bb).filter (fun v => decide (v < n))).map (fun v => (u, v)) ++
      cfgEdgeListAux n (u + 1) rest

/-- All in-range CFG edges of `body`. -/
def cfgEdgeList (body : CapturedMir) : List (Nat × Nat) :=
  cfgEdgeListAux body.basicBlocks.length 0 body.basicBlocks

/-- One Bellman-Ford longest-path relaxation round over `edges`. -/
def relaxRanks (edges : List (Nat × Nat)) (ranks : List Nat) : List Nat :=
  edges.foldl (fun rs e => rs.set e.2 (max (rs.getD e.2 0) (rs.getD e.1 0 + 1))) ranks

/--
Longest-path ranks after `n = body.basicBlocks.length` relaxation rounds. On an
acyclic CFG these are the exact longest-path depths (strictly increasing along
every edge); on a cyclic CFG some edge of every cycle necessarily violates them.
-/
def dagRanks (body : CapturedMir) : List Nat :=
  Nat.repeat (relaxRanks (cfgEdgeList body)) body.basicBlocks.length
    (List.replicate body.basicBlocks.length 0)

/-- Rank function induced by `dagRanks` (`0` outside the block range). -/
def dagRank (body : CapturedMir) (i : Nat) : Nat :=
  (dagRanks body).getD i 0

/--
Computable general CFG acyclicity check: `true` iff the longest-path ranks of
`body` certify that every in-range edge strictly increases rank.
-/
def isCfgDag (body : CapturedMir) : Bool :=
  !hasRankViolation (dagRank body) body

/-- **Soundness of `isCfgDag`**: `isCfgDag body = true` rules out every directed CFG cycle. -/
theorem no_cfg_cycle_of_isCfgDag {body : CapturedMir}
    (h : isCfgDag body = true) (u : BasicBlockIdx) :
    ¬ CfgPath body u u := by
  have h_no : hasRankViolation (dagRank body) body = false := by
    simpa [isCfgDag] using h
  exact no_cfg_cycle_of_hasRankViolation_false h_no u

/-- Every `isCfgDag body = true` body yields an explicit violation-free rank certificate (`dagRank body`). -/
theorem exists_rank_certificate_of_isCfgDag {body : CapturedMir}
    (h : isCfgDag body = true) :
    ∃ rank : Nat → Nat, hasRankViolation rank body = false := by
  refine ⟨dagRank body, ?_⟩
  simpa [isCfgDag] using h

/-- Existential rank-certificate soundness: any violation-free rank certificate rules out all CFG cycles. -/
theorem no_cfg_cycle_of_exists_rank_certificate {body : CapturedMir}
    (h : ∃ rank : Nat → Nat, hasRankViolation rank body = false) (u : BasicBlockIdx) :
    ¬ CfgPath body u u := by
  rcases h with ⟨rank, h_no⟩
  exact no_cfg_cycle_of_hasRankViolation_false h_no u

/-! ## 3. Per-Construct Structural Fragment Checkers -/

/--
Check whether `cv : ConstValue` belongs to fragment `f`:
- `.zeroSized`, `.scalar _`, `.slice (.int _) _`, and `.unevaluated _` belong to
  all fragments (`.pureLoopFree` and above), matching `isPureConstValue`.
- `.slice (.ptr _ _) _` and `.indirect _ _` reference global memory allocations
  and require at least `.intrinsicCopy`.
-/
def checkConstFragment (f : MirFragment) : ConstValue → Bool
  | .zeroSized => true
  | .scalar _ => true
  | .slice (.int _) _ => true
  | .slice (.ptr _ _) _ => decide (MirFragment.intrinsicCopy ≤ f)
  | .indirect _ _ => decide (MirFragment.intrinsicCopy ≤ f)
  | .unevaluated _ => true

/--
Check whether `pe : ProjectionElem` belongs to fragment `f`:
- Value projections (`.field`, `.index`, `.constantIndex`, `.subslice`,
  `.downcast`, `.opaqueCast`) belong to all fragments (`.pureLoopFree` and
  above), matching `isPureProjElem`.
- Pointer dereference (`.deref`) and unsafe binder unwrapping
  (`.unwrapUnsafeBinder`) require at least `.treeBorrowsLocal`.
-/
def checkProjElemFragment (f : MirFragment) : ProjectionElem → Bool
  | .deref => decide (MirFragment.treeBorrowsLocal ≤ f)
  | .field _ _ => true
  | .index _ => true
  | .constantIndex .. => true
  | .subslice .. => true
  | .downcast _ _ => true
  | .opaqueCast _ => true
  | .unwrapUnsafeBinder _ => decide (MirFragment.treeBorrowsLocal ≤ f)

/-- Check whether every projection element in `p : Place` belongs to fragment `f`. -/
def checkPlaceFragment (f : MirFragment) (p : Place) : Bool :=
  p.projection.all (checkProjElemFragment f)

/-- Check whether `op : Operand` belongs to fragment `f`. -/
def checkOperandFragment (f : MirFragment) : Operand → Bool
  | .copy p => checkPlaceFragment f p
  | .move p => checkPlaceFragment f p
  | .constant c => checkConstFragment f c.val

/--
Check whether `op : BinOp` belongs to fragment `f`:
- `BinOp.offset` (in-bounds pointer arithmetic reading `mem.borrows`) requires
  at least `.treeBorrowsLocal`.
- All 25 scalar arithmetic, bitwise, shift, and comparison operators belong to
  all fragments (`.pureLoopFree` and above), matching `isPureBinOp`.
-/
def checkBinOpFragment (f : MirFragment) : BinOp → Bool
  | .offset => decide (MirFragment.treeBorrowsLocal ≤ f)
  | .add | .addUnchecked | .addWithOverflow
  | .sub | .subUnchecked | .subWithOverflow
  | .mul | .mulUnchecked | .mulWithOverflow
  | .div | .rem
  | .bitXor | .bitAnd | .bitOr
  | .shl | .shlUnchecked | .shr | .shrUnchecked
  | .eq | .lt | .le | .ne | .ge | .gt | .cmp => true

/--
Check whether `ck : CastKind` belongs to fragment `f`:
- `.pointerCoercion _` and `.ptrToPtr` require at least `.treeBorrowsLocal`.
- `.fnPtrToPtr` requires `.fullMir`.
- All other casts (`.intToInt`, `.floatToInt`, `.floatToFloat`, `.intToFloat`,
  `.transmute`, `.subtype`, `.pointerExposeProvenance`,
  `.pointerWithExposedProvenance`) are accepted in `.pureLoopFree` and above,
  preserving exact parity with `Anneal.PureMirExec.isPureRvalue`.
-/
def checkCastFragment (f : MirFragment) : CastKind → Bool
  | .pointerCoercion _ => decide (MirFragment.treeBorrowsLocal ≤ f)
  | .ptrToPtr => decide (MirFragment.treeBorrowsLocal ≤ f)
  | .fnPtrToPtr => decide (MirFragment.fullMir ≤ f)
  | .pointerExposeProvenance
  | .pointerWithExposedProvenance
  | .intToInt
  | .floatToInt
  | .floatToFloat
  | .intToFloat
  | .transmute
  | .subtype => true

/--
Check whether `rv : Rvalue` belongs to fragment `f`:
- Value operations on valid operands/places belong to `.pureLoopFree` and above.
- Local borrow/address creation (`.ref`, `.rawPtr`) and `.copyForDeref` require
  at least `.treeBorrowsLocal`.
- `.threadLocalRef` and `.shallowInitBox` require `.fullMir`.
-/
def checkRvalueFragment (f : MirFragment) : Rvalue → Bool
  | .use op => checkOperandFragment f op
  | .repeat op _ => checkOperandFragment f op
  | .ref _ p => decide (MirFragment.treeBorrowsLocal ≤ f) && checkPlaceFragment f p
  | .rawPtr _ p => decide (MirFragment.treeBorrowsLocal ≤ f) && checkPlaceFragment f p
  | .threadLocalRef _ => decide (MirFragment.fullMir ≤ f)
  | .len p => checkPlaceFragment f p
  | .cast ck op _ => checkCastFragment f ck && checkOperandFragment f op
  | .binaryOp op lhs rhs =>
    checkBinOpFragment f op && (checkOperandFragment f lhs && checkOperandFragment f rhs)
  | .nullaryOp _ _ => true
  | .unaryOp _ op => checkOperandFragment f op
  | .discriminant p => checkPlaceFragment f p
  | .aggregate _ ops => ops.all (checkOperandFragment f)
  | .shallowInitBox op _ => decide (MirFragment.fullMir ≤ f) && checkOperandFragment f op
  | .copyForDeref p => decide (MirFragment.treeBorrowsLocal ≤ f) && checkPlaceFragment f p
  | .wrapUnsafeBinder op _ => checkOperandFragment f op

/--
Check whether `sk : StatementKind` belongs to fragment `f`:
- Standard value statements and `.intrinsic (.assume op)` belong to
  `.pureLoopFree` and above when their places/operands belong to `f`.
- `.retag` requires at least `.treeBorrowsLocal`.
- `.intrinsic (.copyNonOverlapping src dst count)` requires at least
  `.intrinsicCopy`.
- `.backwardIncompatibleDropHint` requires `.fullMir`.
-/
def checkStmtFragment (f : MirFragment) : StatementKind → Bool
  | .assign p r => checkPlaceFragment f p && checkRvalueFragment f r
  | .setDiscriminant p _ => checkPlaceFragment f p
  | .storageLive _ => true
  | .storageDead _ => true
  | .nop => true
  | .coverage => true
  | .constEvalCounter => true
  | .placeMention p => checkPlaceFragment f p
  | .deinit p => checkPlaceFragment f p
  | .intrinsic (.assume op) => checkOperandFragment f op
  | .intrinsic (.copyNonOverlapping src dst count) =>
    decide (MirFragment.intrinsicCopy ≤ f) &&
      checkOperandFragment f src &&
      checkOperandFragment f dst &&
      checkOperandFragment f count
  | .retag _ p => decide (MirFragment.treeBorrowsLocal ≤ f) && checkPlaceFragment f p
  | .backwardIncompatibleDropHint p =>
    decide (MirFragment.fullMir ≤ f) && checkPlaceFragment f p

/--
Check whether `tk : TerminatorKind` belongs to fragment `f`:
- Intra-procedural control-flow terminators (`.goto`, `.switchInt`, `.return_`,
  `.assert`, `.drop`, `.unreachable`, `.unwindResume`, `.unwindTerminate`)
  belong to `.pureLoopFree` and above when their operands/places belong to `f`.
- `.call`, `.tailCall`, and `.inlineAsm` require `.fullMir`.
-/
def checkTerminatorFragment (f : MirFragment) : TerminatorKind → Bool
  | .goto _ => true
  | .switchInt discr _ => checkOperandFragment f discr
  | .return_ => true
  | .assert cond _ _ _ => checkOperandFragment f cond
  | .drop p _ _ => checkPlaceFragment f p
  | .unreachable => true
  | .unwindResume => true
  | .unwindTerminate => true
  | .call func args dest _ _ =>
    decide (MirFragment.fullMir ≤ f) &&
      checkOperandFragment f func &&
      args.all (checkOperandFragment f) &&
      checkPlaceFragment f dest
  | .tailCall func args =>
    decide (MirFragment.fullMir ≤ f) &&
      checkOperandFragment f func &&
      args.all (checkOperandFragment f)
  | .inlineAsm _ _ _ => decide (MirFragment.fullMir ≤ f)

/-- Check whether all statements and the terminator of `bb : BasicBlockData` belong to `f`. -/
def checkBlockFragment (f : MirFragment) (bb : BasicBlockData) : Bool :=
  bb.statements.all (fun stmt => checkStmtFragment f stmt.kind) &&
  checkTerminatorFragment f bb.terminator.kind

/--
Computable $O(|B|)$ structural fragment membership checker on `body : CapturedMir`:
- For `.pureLoopFree`, requires every basic block to satisfy
  `checkBlockFragment .pureLoopFree` AND `hasCfgBackedge body = false`.
- For all `f ≥ .pureBoundedLoop`, requires every basic block to satisfy
  `checkBlockFragment f`.
-/
def checkBodyFragment (f : MirFragment) (body : CapturedMir) : Bool :=
  match f with
  | .pureLoopFree =>
    body.basicBlocks.all (checkBlockFragment .pureLoopFree) && !hasCfgBackedge body
  | .pureBoundedLoop =>
    body.basicBlocks.all (checkBlockFragment .pureBoundedLoop)
  | .treeBorrowsLocal =>
    body.basicBlocks.all (checkBlockFragment .treeBorrowsLocal)
  | .intrinsicCopy =>
    body.basicBlocks.all (checkBlockFragment .intrinsicCopy)
  | .fullMir =>
    body.basicBlocks.all (checkBlockFragment .fullMir)

/--
Computable $O(|B|)$ minimum fragment classifier returning the least `MirFragment`
in the 5-element lattice that accepts `body`.
-/
def inferMinFragment (body : CapturedMir) : MirFragment :=
  if checkBodyFragment .pureLoopFree body then .pureLoopFree
  else if checkBodyFragment .pureBoundedLoop body then .pureBoundedLoop
  else if checkBodyFragment .treeBorrowsLocal body then .treeBorrowsLocal
  else if checkBodyFragment .intrinsicCopy body then .intrinsicCopy
  else .fullMir

/-! ## 4. Monotonicity, Totality & Minimality Theorems -/

theorem list_all_mono {α : Type} {p q : α → Bool}
    (hpq : ∀ x, p x = true → q x = true) :
    ∀ (xs : List α), xs.all p = true → xs.all q = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h ⊢
    exact ⟨hpq x h.1, list_all_mono hpq xs h.2⟩

theorem checkConstFragment_mono {f₁ f₂ : MirFragment} (hle : f₁ ≤ f₂)
    (cv : ConstValue) (h : checkConstFragment f₁ cv = true) :
    checkConstFragment f₂ cv = true := by
  cases cv with
  | zeroSized | scalar _ | unevaluated _ => rfl
  | slice sc _ =>
    cases sc with
    | int _ => rfl
    | ptr _ _ =>
      simp only [checkConstFragment, decide_eq_true_eq] at h ⊢
      exact MirFragment.le_trans h hle
  | indirect _ _ =>
    simp only [checkConstFragment, decide_eq_true_eq] at h ⊢
    exact MirFragment.le_trans h hle

theorem checkProjElemFragment_mono {f₁ f₂ : MirFragment} (hle : f₁ ≤ f₂)
    (pe : ProjectionElem) (h : checkProjElemFragment f₁ pe = true) :
    checkProjElemFragment f₂ pe = true := by
  cases pe <;> simp only [checkProjElemFragment, decide_eq_true_eq] at h ⊢
  all_goals first | trivial | exact MirFragment.le_trans h hle

theorem checkPlaceFragment_mono {f₁ f₂ : MirFragment} (hle : f₁ ≤ f₂)
    (p : Place) (h : checkPlaceFragment f₁ p = true) :
    checkPlaceFragment f₂ p = true :=
  list_all_mono (checkProjElemFragment_mono hle) p.projection h

theorem checkOperandFragment_mono {f₁ f₂ : MirFragment} (hle : f₁ ≤ f₂)
    (op : Operand) (h : checkOperandFragment f₁ op = true) :
    checkOperandFragment f₂ op = true := by
  cases op with
  | copy p | move p => exact checkPlaceFragment_mono hle p h
  | constant c => exact checkConstFragment_mono hle c.val h

theorem checkBinOpFragment_mono {f₁ f₂ : MirFragment} (hle : f₁ ≤ f₂)
    (op : BinOp) (h : checkBinOpFragment f₁ op = true) :
    checkBinOpFragment f₂ op = true := by
  cases op <;> simp only [checkBinOpFragment, decide_eq_true_eq] at h ⊢
  all_goals first | trivial | exact MirFragment.le_trans h hle

theorem checkCastFragment_mono {f₁ f₂ : MirFragment} (hle : f₁ ≤ f₂)
    (ck : CastKind) (h : checkCastFragment f₁ ck = true) :
    checkCastFragment f₂ ck = true := by
  cases ck <;> simp only [checkCastFragment, decide_eq_true_eq] at h ⊢
  all_goals first | trivial | exact MirFragment.le_trans h hle

theorem checkRvalueFragment_mono {f₁ f₂ : MirFragment} (hle : f₁ ≤ f₂)
    (rv : Rvalue) (h : checkRvalueFragment f₁ rv = true) :
    checkRvalueFragment f₂ rv = true := by
  cases rv with
  | use op | «repeat» op _ | unaryOp _ op | wrapUnsafeBinder op _ =>
    exact checkOperandFragment_mono hle op h
  | len p | discriminant p =>
    exact checkPlaceFragment_mono hle p h
  | nullaryOp _ _ => rfl
  | ref _ p | rawPtr _ p | copyForDeref p =>
    simp only [checkRvalueFragment, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨MirFragment.le_trans h.1 hle, checkPlaceFragment_mono hle p h.2⟩
  | threadLocalRef _ =>
    simp only [checkRvalueFragment, decide_eq_true_eq] at h ⊢
    exact MirFragment.le_trans h hle
  | cast ck op _ =>
    simp only [checkRvalueFragment, Bool.and_eq_true] at h ⊢
    exact ⟨checkCastFragment_mono hle ck h.1, checkOperandFragment_mono hle op h.2⟩
  | binaryOp op lhs rhs =>
    simp only [checkRvalueFragment, Bool.and_eq_true] at h ⊢
    exact ⟨checkBinOpFragment_mono hle op h.1,
      checkOperandFragment_mono hle lhs h.2.1,
      checkOperandFragment_mono hle rhs h.2.2⟩
  | aggregate _ ops =>
    exact list_all_mono (checkOperandFragment_mono hle) ops h
  | shallowInitBox op _ =>
    simp only [checkRvalueFragment, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨MirFragment.le_trans h.1 hle, checkOperandFragment_mono hle op h.2⟩

theorem checkStmtFragment_mono {f₁ f₂ : MirFragment} (hle : f₁ ≤ f₂)
    (sk : StatementKind) (h : checkStmtFragment f₁ sk = true) :
    checkStmtFragment f₂ sk = true := by
  cases sk with
  | assign p r =>
    simp only [checkStmtFragment, Bool.and_eq_true] at h ⊢
    exact ⟨checkPlaceFragment_mono hle p h.1, checkRvalueFragment_mono hle r h.2⟩
  | setDiscriminant p _ | placeMention p | deinit p =>
    exact checkPlaceFragment_mono hle p h
  | storageLive _ | storageDead _ | nop | coverage | constEvalCounter => rfl
  | intrinsic intr =>
    cases intr with
    | assume op => exact checkOperandFragment_mono hle op h
    | copyNonOverlapping src dst count =>
      simp only [checkStmtFragment, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact ⟨⟨⟨MirFragment.le_trans h.1.1.1 hle,
        checkOperandFragment_mono hle src h.1.1.2⟩,
        checkOperandFragment_mono hle dst h.1.2⟩,
        checkOperandFragment_mono hle count h.2⟩
  | retag _ p =>
    simp only [checkStmtFragment, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨MirFragment.le_trans h.1 hle, checkPlaceFragment_mono hle p h.2⟩
  | backwardIncompatibleDropHint p =>
    simp only [checkStmtFragment, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨MirFragment.le_trans h.1 hle, checkPlaceFragment_mono hle p h.2⟩

theorem checkTerminatorFragment_mono {f₁ f₂ : MirFragment} (hle : f₁ ≤ f₂)
    (tk : TerminatorKind) (h : checkTerminatorFragment f₁ tk = true) :
    checkTerminatorFragment f₂ tk = true := by
  cases tk with
  | goto _ | return_ | unreachable | unwindResume | unwindTerminate => rfl
  | switchInt discr _ => exact checkOperandFragment_mono hle discr h
  | assert cond _ _ _ => exact checkOperandFragment_mono hle cond h
  | drop p _ _ => exact checkPlaceFragment_mono hle p h
  | call func args dest _ _ =>
    simp only [checkTerminatorFragment, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨⟨⟨MirFragment.le_trans h.1.1.1 hle,
      checkOperandFragment_mono hle func h.1.1.2⟩,
      list_all_mono (checkOperandFragment_mono hle) args h.1.2⟩,
      checkPlaceFragment_mono hle dest h.2⟩
  | tailCall func args =>
    simp only [checkTerminatorFragment, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨⟨MirFragment.le_trans h.1.1 hle,
      checkOperandFragment_mono hle func h.1.2⟩,
      list_all_mono (checkOperandFragment_mono hle) args h.2⟩
  | inlineAsm _ _ _ =>
    simp only [checkTerminatorFragment, decide_eq_true_eq] at h ⊢
    exact MirFragment.le_trans h hle

theorem checkBlockFragment_mono {f₁ f₂ : MirFragment} (hle : f₁ ≤ f₂)
    (bb : BasicBlockData) (h : checkBlockFragment f₁ bb = true) :
    checkBlockFragment f₂ bb = true := by
  simp only [checkBlockFragment, Bool.and_eq_true] at h ⊢
  exact ⟨list_all_mono (fun s hs => checkStmtFragment_mono hle s.kind hs) bb.statements h.1,
    checkTerminatorFragment_mono hle bb.terminator.kind h.2⟩

theorem checkBodyFragment_mono {f₁ f₂ : MirFragment} (hle : f₁ ≤ f₂)
    (body : CapturedMir) (h : checkBodyFragment f₁ body = true) :
    checkBodyFragment f₂ body = true := by
  cases f₁ <;> cases f₂
  all_goals try exact False.elim (by revert hle; decide)
  all_goals try exact h
  all_goals
    simp only [checkBodyFragment, Bool.and_eq_true] at h ⊢
    first
      | exact list_all_mono (checkBlockFragment_mono hle) body.basicBlocks h.1
      | exact list_all_mono (checkBlockFragment_mono hle) body.basicBlocks h

@[simp]
theorem le_fullMir (a : MirFragment) : a ≤ .fullMir :=
  MirFragment.le_top a

@[simp]
theorem checkConstFragment_fullMir (cv : ConstValue) :
    checkConstFragment .fullMir cv = true := by
  cases cv with
  | slice sc _ => cases sc <;> rfl
  | _ => rfl

@[simp]
theorem checkProjElemFragment_fullMir (pe : ProjectionElem) :
    checkProjElemFragment .fullMir pe = true := by
  cases pe <;> rfl

@[simp]
theorem checkPlaceFragment_fullMir (p : Place) :
    checkPlaceFragment .fullMir p = true := by
  simp [checkPlaceFragment]

@[simp]
theorem checkOperandFragment_fullMir (op : Operand) :
    checkOperandFragment .fullMir op = true := by
  cases op <;> simp [checkOperandFragment]

@[simp]
theorem checkBinOpFragment_fullMir (op : BinOp) :
    checkBinOpFragment .fullMir op = true := by
  cases op <;> rfl

@[simp]
theorem checkCastFragment_fullMir (ck : CastKind) :
    checkCastFragment .fullMir ck = true := by
  cases ck <;> rfl

@[simp]
theorem checkRvalueFragment_fullMir (rv : Rvalue) :
    checkRvalueFragment .fullMir rv = true := by
  cases rv <;> simp [checkRvalueFragment]

@[simp]
theorem checkStmtFragment_fullMir (sk : StatementKind) :
    checkStmtFragment .fullMir sk = true := by
  cases sk with
  | intrinsic intr => cases intr <;> simp [checkStmtFragment]
  | _ => simp [checkStmtFragment]

@[simp]
theorem checkTerminatorFragment_fullMir (tk : TerminatorKind) :
    checkTerminatorFragment .fullMir tk = true := by
  cases tk <;> simp [checkTerminatorFragment]

@[simp]
theorem checkBlockFragment_fullMir (bb : BasicBlockData) :
    checkBlockFragment .fullMir bb = true := by
  simp [checkBlockFragment]

/-- Every `CapturedMir` body belongs to `.fullMir`. -/
@[simp]
theorem checkBodyFragment_fullMir (body : CapturedMir) :
    checkBodyFragment .fullMir body = true := by
  simp [checkBodyFragment]

/-- `inferMinFragment body` always satisfies `checkBodyFragment`. -/
theorem checkBodyFragment_inferMinFragment (body : CapturedMir) :
    checkBodyFragment (inferMinFragment body) body = true := by
  unfold inferMinFragment
  split <;> first | assumption | (split <;> first | assumption | (split <;> first | assumption | (split <;> first | assumption | exact checkBodyFragment_fullMir body)))

/-- `inferMinFragment body` is the least fragment accepting `body`. -/
theorem inferMinFragment_minimal (body : CapturedMir) (f : MirFragment)
    (hf : checkBodyFragment f body = true) :
    inferMinFragment body ≤ f := by
  unfold inferMinFragment
  cases f with
  | pureLoopFree =>
    simp only [hf, ↓reduceIte]
    decide
  | pureBoundedLoop =>
    simp only [hf, ↓reduceIte]
    split <;> decide
  | treeBorrowsLocal =>
    simp only [hf, ↓reduceIte]
    split <;> first | decide | (split <;> decide)
  | intrinsicCopy =>
    simp only [hf, ↓reduceIte]
    split <;> first | decide | (split <;> first | decide | (split <;> decide))
  | fullMir =>
    exact MirFragment.le_top _

/--
**Galois / Lower-Adjoint Characterization of `inferMinFragment`**:
A `CapturedMir` body belongs to fragment `f` if and only if
`inferMinFragment body ≤ f`.
-/
theorem checkBodyFragment_iff_inferMinFragment_le (f : MirFragment) (body : CapturedMir) :
    checkBodyFragment f body = true ↔ inferMinFragment body ≤ f := by
  constructor
  · exact inferMinFragment_minimal body f
  · intro hle
    exact checkBodyFragment_mono hle body (checkBodyFragment_inferMinFragment body)

/-- Equivalence of `inferMinFragment` with the head of `MirFragment.all.filter`. -/
theorem inferMinFragment_eq_filter_headD (body : CapturedMir) :
    inferMinFragment body =
      (MirFragment.all.filter (fun f => checkBodyFragment f body)).headD .fullMir := by
  unfold inferMinFragment MirFragment.all
  cases h0 : checkBodyFragment .pureLoopFree body <;>
    cases h1 : checkBodyFragment .pureBoundedLoop body <;>
    cases h2 : checkBodyFragment .treeBorrowsLocal body <;>
    cases h3 : checkBodyFragment .intrinsicCopy body <;>
    cases h4 : checkBodyFragment .fullMir body <;>
    simp [List.filter, h0, h1, h2, h3, h4]

/-! ## 5. Structural Exclusion Theorems -/

/-- A `.pureLoopFree` body has no CFG back-edges (`hasCfgBackedge body = false`). -/
theorem pureLoopFree_has_no_backedges (body : CapturedMir)
    (h : checkBodyFragment .pureLoopFree body = true) :
    hasCfgBackedge body = false := by
  simp only [checkBodyFragment, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.2

/-- A `.pureLoopFree` body has no directed CFG cycles of any length. -/
theorem pureLoopFree_no_cfg_cycle (body : CapturedMir)
    (h : checkBodyFragment .pureLoopFree body = true) (u : BasicBlockIdx) :
    ¬ CfgPath body u u :=
  no_cfg_cycle_of_hasCfgBackedge_false (pureLoopFree_has_no_backedges body h) u

theorem list_all_false_of_mem {α : Type} {p : α → Bool} {xs : List α} {x : α}
    (h_mem : x ∈ xs) (hx : p x = false) :
    xs.all p = false := by
  induction xs with
  | nil => cases h_mem
  | cons hd tl ih =>
    simp only [List.mem_cons] at h_mem
    rcases h_mem with rfl | h_tl
    · simp [hx]
    · simp [ih h_tl]

/-- `ProjectionElem.deref` is excluded from `.pureBoundedLoop` (and `.pureLoopFree`). -/
theorem no_deref_in_pureBoundedLoop :
    checkProjElemFragment .pureBoundedLoop .deref = false ∧
    ∀ (p : Place), .deref ∈ p.projection →
      checkPlaceFragment .pureBoundedLoop p = false := by
  refine ⟨rfl, fun p h_mem => ?_⟩
  exact list_all_false_of_mem h_mem rfl

/-- `StatementKind.retag` is excluded from `.pureBoundedLoop` (and `.pureLoopFree`). -/
theorem no_retag_in_pureBoundedLoop (rk : RetagKind) (p : Place) :
    checkStmtFragment .pureBoundedLoop (.retag rk p) = false :=
  rfl

/-- Any body containing a `StatementKind.retag` statement is rejected by `.pureBoundedLoop`. -/
theorem no_retag_body_in_pureBoundedLoop
    (body : CapturedMir) (bb : BasicBlockData) (stmt : Statement)
    (rk : RetagKind) (p : Place)
    (h_bb : bb ∈ body.basicBlocks) (h_stmt : stmt ∈ bb.statements)
    (h_kind : stmt.kind = .retag rk p) :
    checkBodyFragment .pureBoundedLoop body = false := by
  have h_sf : checkStmtFragment .pureBoundedLoop stmt.kind = false := by
    rw [h_kind]; rfl
  have h_stmts : bb.statements.all (fun s => checkStmtFragment .pureBoundedLoop s.kind) = false :=
    list_all_false_of_mem h_stmt h_sf
  have h_blk : checkBlockFragment .pureBoundedLoop bb = false := by
    simp [checkBlockFragment, h_stmts]
  exact list_all_false_of_mem h_bb h_blk

/-- `NonDivergingIntrinsic.copyNonOverlapping` is excluded from `.treeBorrowsLocal`. -/
theorem no_copyNonOverlapping_in_treeBorrowsLocal (src dst count : Operand) :
    checkStmtFragment .treeBorrowsLocal
      (.intrinsic (.copyNonOverlapping src dst count)) = false :=
  rfl

/-- Any body containing `copyNonOverlapping` is rejected by `.treeBorrowsLocal`. -/
theorem no_copyNonOverlapping_body_in_treeBorrowsLocal
    (body : CapturedMir) (bb : BasicBlockData) (stmt : Statement)
    (src dst count : Operand)
    (h_bb : bb ∈ body.basicBlocks) (h_stmt : stmt ∈ bb.statements)
    (h_kind : stmt.kind = .intrinsic (.copyNonOverlapping src dst count)) :
    checkBodyFragment .treeBorrowsLocal body = false := by
  have h_sf : checkStmtFragment .treeBorrowsLocal stmt.kind = false := by
    rw [h_kind]; rfl
  have h_stmts : bb.statements.all (fun s => checkStmtFragment .treeBorrowsLocal s.kind) = false :=
    list_all_false_of_mem h_stmt h_sf
  have h_blk : checkBlockFragment .treeBorrowsLocal bb = false := by
    simp [checkBlockFragment, h_stmts]
  exact list_all_false_of_mem h_bb h_blk

/-- `TerminatorKind.call` and `TerminatorKind.tailCall` are excluded from `.intrinsicCopy`. -/
theorem no_call_in_intrinsicCopy
    (func : Operand) (args : List Operand) (dest : Place)
    (target : Option BasicBlockIdx) (unwind : UnwindAction) :
    checkTerminatorFragment .intrinsicCopy (.call func args dest target unwind) = false ∧
    checkTerminatorFragment .intrinsicCopy (.tailCall func args) = false :=
  ⟨rfl, rfl⟩

/-- Any body containing a `TerminatorKind.call` terminator is rejected by `.intrinsicCopy`. -/
theorem no_call_body_in_intrinsicCopy
    (body : CapturedMir) (bb : BasicBlockData)
    (func : Operand) (args : List Operand) (dest : Place)
    (target : Option BasicBlockIdx) (unwind : UnwindAction)
    (h_bb : bb ∈ body.basicBlocks)
    (h_term : bb.terminator.kind = .call func args dest target unwind) :
    checkBodyFragment .intrinsicCopy body = false := by
  have h_tf : checkTerminatorFragment .intrinsicCopy bb.terminator.kind = false := by
    rw [h_term]; rfl
  have h_blk : checkBlockFragment .intrinsicCopy bb = false := by
    simp [checkBlockFragment, h_tf]
  exact list_all_false_of_mem h_bb h_blk

/-- `TerminatorKind.inlineAsm` is excluded from `.intrinsicCopy`. -/
theorem no_inlineAsm_in_intrinsicCopy
    (template : String) (targets : List BasicBlockIdx) (unwind : UnwindAction) :
    checkTerminatorFragment .intrinsicCopy (.inlineAsm template targets unwind) = false :=
  rfl

/-- Any body containing `TerminatorKind.inlineAsm` is rejected by `.intrinsicCopy`. -/
theorem no_inlineAsm_body_in_intrinsicCopy
    (body : CapturedMir) (bb : BasicBlockData)
    (template : String) (targets : List BasicBlockIdx) (unwind : UnwindAction)
    (h_bb : bb ∈ body.basicBlocks)
    (h_term : bb.terminator.kind = .inlineAsm template targets unwind) :
    checkBodyFragment .intrinsicCopy body = false := by
  have h_tf : checkTerminatorFragment .intrinsicCopy bb.terminator.kind = false := by
    rw [h_term]; rfl
  have h_blk : checkBlockFragment .intrinsicCopy bb = false := by
    simp [checkBlockFragment, h_tf]
  exact list_all_false_of_mem h_bb h_blk

/-! ### Downward-closed exclusions (every level strictly below each threshold) -/

/-- `ProjectionElem.deref` is rejected at every level `f < .treeBorrowsLocal`. -/
theorem no_deref_below_treeBorrowsLocal (f : MirFragment) (hf : f < .treeBorrowsLocal) :
    checkProjElemFragment f .deref = false := by
  cases f <;> first | rfl | exact absurd hf (by decide)

/-- `StatementKind.retag` is rejected at every level `f < .treeBorrowsLocal`. -/
theorem no_retag_below_treeBorrowsLocal (f : MirFragment) (hf : f < .treeBorrowsLocal)
    (rk : RetagKind) (p : Place) :
    checkStmtFragment f (.retag rk p) = false := by
  cases f <;> first | rfl | exact absurd hf (by decide)

/-- `copyNonOverlapping` is rejected at every level `f < .intrinsicCopy`. -/
theorem no_copyNonOverlapping_below_intrinsicCopy (f : MirFragment) (hf : f < .intrinsicCopy)
    (src dst count : Operand) :
    checkStmtFragment f (.intrinsic (.copyNonOverlapping src dst count)) = false := by
  cases f <;> first | rfl | exact absurd hf (by decide)

/-- `TerminatorKind.call` / `.tailCall` are rejected at every level `f < .fullMir`. -/
theorem no_call_below_fullMir (f : MirFragment) (hf : f < .fullMir)
    (func : Operand) (args : List Operand) (dest : Place)
    (target : Option BasicBlockIdx) (unwind : UnwindAction) :
    checkTerminatorFragment f (.call func args dest target unwind) = false ∧
    checkTerminatorFragment f (.tailCall func args) = false := by
  cases f <;> first | exact ⟨rfl, rfl⟩ | exact absurd hf (by decide)

/-- `TerminatorKind.inlineAsm` is rejected at every level `f < .fullMir`. -/
theorem no_inlineAsm_below_fullMir (f : MirFragment) (hf : f < .fullMir)
    (template : String) (targets : List BasicBlockIdx) (unwind : UnwindAction) :
    checkTerminatorFragment f (.inlineAsm template targets unwind) = false := by
  cases f <;> first | rfl | exact absurd hf (by decide)

/-- `Rvalue.ref` and `Rvalue.rawPtr` are rejected at every level `f < .treeBorrowsLocal`. -/
theorem no_ref_or_rawPtr_below_treeBorrowsLocal (f : MirFragment) (hf : f < .treeBorrowsLocal)
    (bk : BorrowKind) (m : Mutability) (p : Place) :
    checkRvalueFragment f (.ref bk p) = false ∧
    checkRvalueFragment f (.rawPtr m p) = false := by
  cases f <;> first | exact ⟨rfl, rfl⟩ | exact absurd hf (by decide)

/-- `Rvalue.copyForDeref` is rejected at every level `f < .treeBorrowsLocal`. -/
theorem no_copyForDeref_below_treeBorrowsLocal (f : MirFragment) (hf : f < .treeBorrowsLocal)
    (p : Place) :
    checkRvalueFragment f (.copyForDeref p) = false := by
  cases f <;> first | rfl | exact absurd hf (by decide)

/-- `BinOp.offset` is rejected at every level `f < .treeBorrowsLocal`. -/
theorem no_offset_below_treeBorrowsLocal (f : MirFragment) (hf : f < .treeBorrowsLocal) :
    checkBinOpFragment f .offset = false := by
  cases f <;> first | rfl | exact absurd hf (by decide)

/-- `CastKind.pointerCoercion` and `.ptrToPtr` are rejected at every level `f < .treeBorrowsLocal`. -/
theorem no_ptrCast_below_treeBorrowsLocal (f : MirFragment) (hf : f < .treeBorrowsLocal)
    (tag : String) :
    checkCastFragment f (.pointerCoercion tag) = false ∧
    checkCastFragment f .ptrToPtr = false := by
  cases f <;> first | exact ⟨rfl, rfl⟩ | exact absurd hf (by decide)

/-- `ProjectionElem.unwrapUnsafeBinder` is rejected at every level `f < .treeBorrowsLocal`. -/
theorem no_unwrapUnsafeBinder_below_treeBorrowsLocal (f : MirFragment) (hf : f < .treeBorrowsLocal)
    (ty : Ty) :
    checkProjElemFragment f (.unwrapUnsafeBinder ty) = false := by
  cases f <;> first | rfl | exact absurd hf (by decide)

/-- `ConstValue.indirect` and pointer-backed `.slice (.ptr ..)` are rejected at every level `f < .intrinsicCopy`. -/
theorem no_globalAllocConst_below_intrinsicCopy (f : MirFragment) (hf : f < .intrinsicCopy)
    (allocId offset : Nat) (ptr : ProvenancePtr) (sz meta_ : Nat) :
    checkConstFragment f (.indirect allocId offset) = false ∧
    checkConstFragment f (.slice (.ptr ptr sz) meta_) = false := by
  cases f <;> first | exact ⟨rfl, rfl⟩ | exact absurd hf (by decide)

/-- `Rvalue.threadLocalRef`, `Rvalue.shallowInitBox`, `CastKind.fnPtrToPtr`, and `StatementKind.backwardIncompatibleDropHint` are rejected at every level `f < .fullMir`. -/
theorem no_fullMirOnlyConstructs_below_fullMir (f : MirFragment) (hf : f < .fullMir)
    (path : DefPath) (op : Operand) (ty : Ty) (p : Place) :
    checkRvalueFragment f (.threadLocalRef path) = false ∧
    checkRvalueFragment f (.shallowInitBox op ty) = false ∧
    checkCastFragment f .fnPtrToPtr = false ∧
    checkStmtFragment f (.backwardIncompatibleDropHint p) = false := by
  cases f <;> first | exact ⟨rfl, rfl, rfl, rfl⟩ | exact absurd hf (by decide)

/-- Any body containing `StatementKind.retag` is rejected at every level `f < .treeBorrowsLocal`. -/
theorem no_retag_body_below_treeBorrowsLocal
    (f : MirFragment) (hf : f < .treeBorrowsLocal)
    (body : CapturedMir) (bb : BasicBlockData) (stmt : Statement)
    (rk : RetagKind) (p : Place)
    (h_bb : bb ∈ body.basicBlocks) (h_stmt : stmt ∈ bb.statements)
    (h_kind : stmt.kind = .retag rk p) :
    checkBodyFragment f body = false := by
  cases h_chk : checkBodyFragment f body
  · rfl
  · have h_le : checkBodyFragment .pureBoundedLoop body = true := by
      refine checkBodyFragment_mono ?_ body h_chk
      cases f <;> first | decide | exact absurd hf (by decide)
    exact absurd h_le (by rw [no_retag_body_in_pureBoundedLoop body bb stmt rk p h_bb h_stmt h_kind]; decide)

/-- Any body containing `copyNonOverlapping` is rejected at every level `f < .intrinsicCopy`. -/
theorem no_copyNonOverlapping_body_below_intrinsicCopy
    (f : MirFragment) (hf : f < .intrinsicCopy)
    (body : CapturedMir) (bb : BasicBlockData) (stmt : Statement)
    (src dst count : Operand)
    (h_bb : bb ∈ body.basicBlocks) (h_stmt : stmt ∈ bb.statements)
    (h_kind : stmt.kind = .intrinsic (.copyNonOverlapping src dst count)) :
    checkBodyFragment f body = false := by
  cases h_chk : checkBodyFragment f body
  · rfl
  · have h_le : checkBodyFragment .treeBorrowsLocal body = true := by
      refine checkBodyFragment_mono ?_ body h_chk
      cases f <;> first | decide | exact absurd hf (by decide)
    exact absurd h_le (by rw [no_copyNonOverlapping_body_in_treeBorrowsLocal body bb stmt src dst count h_bb h_stmt h_kind]; decide)

/-- Any body containing `TerminatorKind.call` is rejected at every level `f < .fullMir`. -/
theorem no_call_body_below_fullMir
    (f : MirFragment) (hf : f < .fullMir)
    (body : CapturedMir) (bb : BasicBlockData)
    (func : Operand) (args : List Operand) (dest : Place)
    (target : Option BasicBlockIdx) (unwind : UnwindAction)
    (h_bb : bb ∈ body.basicBlocks)
    (h_term : bb.terminator.kind = .call func args dest target unwind) :
    checkBodyFragment f body = false := by
  cases h_chk : checkBodyFragment f body
  · rfl
  · have h_le : checkBodyFragment .intrinsicCopy body = true := by
      refine checkBodyFragment_mono ?_ body h_chk
      cases f <;> first | decide | exact absurd hf (by decide)
    exact absurd h_le (by rw [no_call_body_in_intrinsicCopy body bb func args dest target unwind h_bb h_term]; decide)

/-- Any body containing `TerminatorKind.inlineAsm` is rejected at every level `f < .fullMir`. -/
theorem no_inlineAsm_body_below_fullMir
    (f : MirFragment) (hf : f < .fullMir)
    (body : CapturedMir) (bb : BasicBlockData)
    (template : String) (targets : List BasicBlockIdx) (unwind : UnwindAction)
    (h_bb : bb ∈ body.basicBlocks)
    (h_term : bb.terminator.kind = .inlineAsm template targets unwind) :
    checkBodyFragment f body = false := by
  cases h_chk : checkBodyFragment f body
  · rfl
  · have h_le : checkBodyFragment .intrinsicCopy body = true := by
      refine checkBodyFragment_mono ?_ body h_chk
      cases f <;> first | decide | exact absurd hf (by decide)
    exact absurd h_le (by rw [no_inlineAsm_body_in_intrinsicCopy body bb template targets unwind h_bb h_term]; decide)

/-! ## 6. Exact `Anneal.PureMirExec.checkPureMir` Bridge Theorems -/

@[simp]
theorem checkConstFragment_pureBoundedLoop_eq_isPureConstValue (cv : ConstValue) :
    checkConstFragment .pureBoundedLoop cv = isPureConstValue cv := by
  cases cv with
  | slice sc _ => cases sc <;> rfl
  | _ => rfl

@[simp]
theorem checkProjElemFragment_pureBoundedLoop_eq_isPureProjElem (pe : ProjectionElem) :
    checkProjElemFragment .pureBoundedLoop pe = isPureProjElem pe := by
  cases pe <;> rfl

@[simp]
theorem checkPlaceFragment_pureBoundedLoop_eq_isPurePlace (p : Place) :
    checkPlaceFragment .pureBoundedLoop p = isPurePlace p :=
  congrArg p.projection.all (funext checkProjElemFragment_pureBoundedLoop_eq_isPureProjElem)

@[simp]
theorem checkOperandFragment_pureBoundedLoop_eq_isPureOperand (op : Operand) :
    checkOperandFragment .pureBoundedLoop op = isPureOperand op := by
  cases op with
  | copy p | move p => exact checkPlaceFragment_pureBoundedLoop_eq_isPurePlace p
  | constant c => exact checkConstFragment_pureBoundedLoop_eq_isPureConstValue c.val

@[simp]
theorem checkBinOpFragment_pureBoundedLoop_eq_isPureBinOp (op : BinOp) :
    checkBinOpFragment .pureBoundedLoop op = isPureBinOp op := by
  cases op <;> rfl

@[simp]
theorem checkRvalueFragment_pureBoundedLoop_eq_isPureRvalue (rv : Rvalue) :
    checkRvalueFragment .pureBoundedLoop rv = isPureRvalue rv := by
  cases rv with
  | use op | «repeat» op _ | unaryOp _ op | wrapUnsafeBinder op _ =>
    exact checkOperandFragment_pureBoundedLoop_eq_isPureOperand op
  | ref _ _ | rawPtr _ _ | threadLocalRef _ | shallowInitBox _ _ | copyForDeref _ =>
    rfl
  | len p | discriminant p =>
    exact checkPlaceFragment_pureBoundedLoop_eq_isPurePlace p
  | cast ck op _ =>
    cases ck <;>
      first
        | rfl
        | (dsimp only [checkRvalueFragment, isPureRvalue, checkCastFragment]
           rw [Bool.true_and]
           exact checkOperandFragment_pureBoundedLoop_eq_isPureOperand op)
  | binaryOp op lhs rhs =>
    dsimp only [checkRvalueFragment, isPureRvalue]
    rw [checkBinOpFragment_pureBoundedLoop_eq_isPureBinOp,
      checkOperandFragment_pureBoundedLoop_eq_isPureOperand,
      checkOperandFragment_pureBoundedLoop_eq_isPureOperand]
  | nullaryOp _ _ => rfl
  | aggregate _ ops =>
    exact congrArg ops.all (funext checkOperandFragment_pureBoundedLoop_eq_isPureOperand)

@[simp]
theorem checkStmtFragment_pureBoundedLoop_eq_isPureStatement (sk : StatementKind) :
    checkStmtFragment .pureBoundedLoop sk = isPureStatement sk := by
  cases sk with
  | assign p r =>
    dsimp only [checkStmtFragment, isPureStatement]
    rw [checkPlaceFragment_pureBoundedLoop_eq_isPurePlace,
      checkRvalueFragment_pureBoundedLoop_eq_isPureRvalue]
  | setDiscriminant p _ | placeMention p | deinit p =>
    exact checkPlaceFragment_pureBoundedLoop_eq_isPurePlace p
  | storageLive _ | storageDead _ | nop | coverage | constEvalCounter => rfl
  | intrinsic intr =>
    cases intr with
    | assume op => exact checkOperandFragment_pureBoundedLoop_eq_isPureOperand op
    | copyNonOverlapping _ _ _ => rfl
  | retag _ _ | backwardIncompatibleDropHint _ => rfl

@[simp]
theorem checkTerminatorFragment_pureBoundedLoop_eq_isPureTerminator (tk : TerminatorKind) :
    checkTerminatorFragment .pureBoundedLoop tk = isPureTerminator tk := by
  cases tk with
  | switchInt discr _ => exact checkOperandFragment_pureBoundedLoop_eq_isPureOperand discr
  | assert cond _ _ _ => exact checkOperandFragment_pureBoundedLoop_eq_isPureOperand cond
  | drop p _ _ => exact checkPlaceFragment_pureBoundedLoop_eq_isPurePlace p
  | _ => rfl

/--
**Exact Syntactic Purity Bridge**:
`checkBodyFragment .pureBoundedLoop body` is extensionally identical to
`Anneal.PureMirExec.checkPureMir body` for every `body : CapturedMir`.
-/
@[simp]
theorem checkBodyFragment_pureBoundedLoop_eq_checkPureMir (body : CapturedMir) :
    checkBodyFragment .pureBoundedLoop body = Anneal.PureMirExec.checkPureMir body := by
  refine congrArg body.basicBlocks.all (funext fun bb => ?_)
  dsimp only [checkBlockFragment]
  rw [congrArg bb.statements.all
    (funext fun stmt => checkStmtFragment_pureBoundedLoop_eq_isPureStatement stmt.kind),
    checkTerminatorFragment_pureBoundedLoop_eq_isPureTerminator bb.terminator.kind]

/--
If `inferMinFragment body ≤ .pureBoundedLoop` (i.e., `body` is classified as
`.pureLoopFree` or `.pureBoundedLoop`), then `Anneal.PureMirExec.checkPureMir body = true`.
-/
theorem checkPureMir_of_inferMinFragment_le_pureBoundedLoop
    (body : CapturedMir)
    (h : inferMinFragment body ≤ .pureBoundedLoop) :
    Anneal.PureMirExec.checkPureMir body = true := by
  rw [← checkBodyFragment_pureBoundedLoop_eq_checkPureMir]
  exact (checkBodyFragment_iff_inferMinFragment_le .pureBoundedLoop body).mpr h

/--
Biconditional bridge between `inferMinFragment body ≤ .pureBoundedLoop` and
`Anneal.PureMirExec.checkPureMir body = true`.
-/
theorem inferMinFragment_le_pureBoundedLoop_iff_checkPureMir (body : CapturedMir) :
    inferMinFragment body ≤ .pureBoundedLoop ↔
      Anneal.PureMirExec.checkPureMir body = true := by
  rw [← checkBodyFragment_pureBoundedLoop_eq_checkPureMir]
  exact (checkBodyFragment_iff_inferMinFragment_le .pureBoundedLoop body).symm

/--
Direct verification bridge from `inferMinFragment c.body ≤ .pureBoundedLoop`
to `VerificationResult c` via `Anneal.PureMirExec.verifyMirNoPanic_of_pureExec`.
-/
theorem verifyMirNoPanic_of_inferMinFragment_le_pureBoundedLoop
    (c : Claim)
    (h_frag : inferMinFragment c.body ≤ .pureBoundedLoop)
    (h_exec : ∀ args, c.pre args →
      PureMirConverges c.body (initPureState c.body args) (c.post args)) :
    VerificationResult c :=
  Anneal.PureMirExec.verifyMirNoPanic_of_pureExec c
    (checkPureMir_of_inferMinFragment_le_pureBoundedLoop c.body h_frag)
    h_exec

/--
Direct partial-correctness verification bridge from
`inferMinFragment c.body ≤ .pureBoundedLoop` and `PureMirSafeConverges` to
`VerificationResult c` via `Anneal.PureMirExec.verifyMirSafe_of_pureExec`.
-/
theorem verifyMirSafe_of_inferMinFragment_le_pureBoundedLoop
    (c : Claim)
    (h_frag : inferMinFragment c.body ≤ .pureBoundedLoop)
    (h_exec : ∀ args, c.pre args →
      PureMirSafeConverges c.body (initPureState c.body args) (c.post args)) :
    VerificationResult c :=
  Anneal.PureMirExec.verifyMirSafe_of_pureExec c
    (checkPureMir_of_inferMinFragment_le_pureBoundedLoop c.body h_frag)
    h_exec

/-! ## 7. Polymorphic Instantiation Invariance (`CapturedMir.instantiate`) -/

@[simp]
theorem checkProjElemFragment_instantiate
    (f : MirFragment) (tbl : LayoutTable) (args : TypeSubst) (pe : ProjectionElem) :
    checkProjElemFragment f (pe.instantiate tbl args) = checkProjElemFragment f pe := by
  cases pe <;> rfl

@[simp]
theorem checkPlaceFragment_instantiateList
    (f : MirFragment) (tbl : LayoutTable) (args : TypeSubst) :
    ∀ (pes : List ProjectionElem),
      (ProjectionElem.instantiateList tbl args pes).all (checkProjElemFragment f) =
        pes.all (checkProjElemFragment f)
  | [] => rfl
  | pe :: rest => by
    simp only [ProjectionElem.instantiateList, List.all_cons,
      checkProjElemFragment_instantiate,
      checkPlaceFragment_instantiateList f tbl args rest]

@[simp]
theorem checkPlaceFragment_instantiate
    (f : MirFragment) (tbl : LayoutTable) (args : TypeSubst) (p : Place) :
    checkPlaceFragment f (p.instantiate tbl args) = checkPlaceFragment f p := by
  simp only [checkPlaceFragment, checkPlaceFragment_instantiateList]

@[simp]
theorem checkConstFragment_instantiate
    (f : MirFragment) (tbl : LayoutTable) (args : TypeSubst) (c : ConstOperand) :
    checkConstFragment f (c.instantiate tbl args).val = checkConstFragment f c.val := by
  cases c
  rfl

@[simp]
theorem checkOperandFragment_instantiate
    (f : MirFragment) (tbl : LayoutTable) (args : TypeSubst) (op : Operand) :
    checkOperandFragment f (op.instantiate tbl args) = checkOperandFragment f op := by
  cases op with
  | copy p | move p =>
    simp only [checkOperandFragment, checkPlaceFragment_instantiate]
  | constant c =>
    cases c
    rfl

@[simp]
theorem checkOperandFragment_instantiateList
    (f : MirFragment) (tbl : LayoutTable) (args : TypeSubst) :
    ∀ (ops : List Operand),
      (Operand.instantiateList tbl args ops).all (checkOperandFragment f) =
        ops.all (checkOperandFragment f)
  | [] => rfl
  | op :: rest => by
    have h_hd := checkOperandFragment_instantiate f tbl args op
    have h_tl := checkOperandFragment_instantiateList f tbl args rest
    dsimp only [Operand.instantiateList, List.all_cons]
    rw [h_hd, h_tl]

@[simp]
theorem checkRvalueFragment_instantiate
    (f : MirFragment) (tbl : LayoutTable) (args : TypeSubst) (rv : Rvalue) :
    checkRvalueFragment f (rv.instantiate tbl args) = checkRvalueFragment f rv := by
  cases rv <;>
    simp only [checkRvalueFragment,
      checkOperandFragment_instantiate, checkPlaceFragment_instantiate,
      checkOperandFragment_instantiateList]

@[simp]
theorem checkStmtFragment_instantiate
    (f : MirFragment) (tbl : LayoutTable) (args : TypeSubst) (sk : StatementKind) :
    checkStmtFragment f (sk.instantiate tbl args) = checkStmtFragment f sk := by
  cases sk with
  | intrinsic intr =>
    cases intr <;>
      simp only [checkStmtFragment, checkOperandFragment_instantiate]
  | _ =>
    simp only [checkStmtFragment,
      checkPlaceFragment_instantiate, checkRvalueFragment_instantiate]

@[simp]
theorem checkStmtFragment_instantiateList
    (f : MirFragment) (tbl : LayoutTable) (args : TypeSubst) :
    ∀ (stmts : List Statement),
      (Statement.instantiateList tbl args stmts).all (fun s => checkStmtFragment f s.kind) =
        stmts.all (fun s => checkStmtFragment f s.kind)
  | [] => rfl
  | s :: rest => by
    have h_hd := checkStmtFragment_instantiate f tbl args s.kind
    have h_tl := checkStmtFragment_instantiateList f tbl args rest
    dsimp only [Statement.instantiateList, Statement.instantiate, List.all_cons]
    rw [h_hd, h_tl]

@[simp]
theorem checkTerminatorFragment_instantiate
    (f : MirFragment) (tbl : LayoutTable) (args : TypeSubst) (tk : TerminatorKind) :
    checkTerminatorFragment f (tk.instantiate tbl args) = checkTerminatorFragment f tk := by
  cases tk <;>
    simp only [checkTerminatorFragment,
      checkOperandFragment_instantiate, checkPlaceFragment_instantiate,
      checkOperandFragment_instantiateList]

@[simp]
theorem terminatorTargets_instantiate
    (tbl : LayoutTable) (args : TypeSubst) (tk : TerminatorKind) :
    terminatorTargets (tk.instantiate tbl args) = terminatorTargets tk := by
  cases tk <;> rfl

@[simp]
theorem hasBlockBackedge_instantiate
    (bbIdx : BasicBlockIdx) (tbl : LayoutTable) (args : TypeSubst) (bb : BasicBlockData) :
    hasBlockBackedge bbIdx (bb.instantiate tbl args) = hasBlockBackedge bbIdx bb := by
  dsimp only [BasicBlockData.instantiate, Terminator.instantiate, hasBlockBackedge, blockTargets]
  rw [terminatorTargets_instantiate]

@[simp]
theorem hasCfgBackedgeAux_instantiate
    (tbl : LayoutTable) (args : TypeSubst) :
    ∀ (bbIdx : BasicBlockIdx) (bbs : List BasicBlockData),
      hasCfgBackedgeAux bbIdx (BasicBlockData.instantiateList tbl args bbs) =
        hasCfgBackedgeAux bbIdx bbs
  | _, [] => rfl
  | bbIdx, bb :: rest => by
    have h_hd := hasBlockBackedge_instantiate bbIdx tbl args bb
    have h_tl := hasCfgBackedgeAux_instantiate tbl args (bbIdx + 1) rest
    dsimp only [BasicBlockData.instantiateList, hasCfgBackedgeAux]
    rw [h_hd, h_tl]

@[simp]
theorem checkBlockFragment_instantiate
    (f : MirFragment) (tbl : LayoutTable) (args : TypeSubst) (bb : BasicBlockData) :
    checkBlockFragment f (bb.instantiate tbl args) = checkBlockFragment f bb := by
  dsimp only [BasicBlockData.instantiate, Terminator.instantiate, checkBlockFragment]
  rw [checkStmtFragment_instantiateList, checkTerminatorFragment_instantiate]

@[simp]
theorem checkBlockFragment_instantiateList
    (f : MirFragment) (tbl : LayoutTable) (args : TypeSubst) :
    ∀ (bbs : List BasicBlockData),
      (BasicBlockData.instantiateList tbl args bbs).all (checkBlockFragment f) =
        bbs.all (checkBlockFragment f)
  | [] => rfl
  | bb :: rest => by
    have h_hd := checkBlockFragment_instantiate f tbl args bb
    have h_tl := checkBlockFragment_instantiateList f tbl args rest
    dsimp only [BasicBlockData.instantiateList, List.all_cons]
    rw [h_hd, h_tl]

/--
**Polymorphic Monomorphization Invariance**:
Instantiating generic type parameters via `CapturedMir.instantiate` preserves
`checkBodyFragment` across all 5 `MirFragment` levels.
-/
@[simp]
theorem checkBodyFragment_instantiate
    (f : MirFragment) (body : CapturedMir) (args : TypeSubst) :
    checkBodyFragment f (body.instantiate args) = checkBodyFragment f body := by
  cases f <;>
    simp only [checkBodyFragment, hasCfgBackedge,
      checkBlockFragment_instantiateList, hasCfgBackedgeAux_instantiate]

/--
**Polymorphic Fragment Inference Invariance**:
`inferMinFragment (body.instantiate args) = inferMinFragment body`.
-/
@[simp]
theorem inferMinFragment_instantiate
    (body : CapturedMir) (args : TypeSubst) :
    inferMinFragment (body.instantiate args) = inferMinFragment body := by
  unfold inferMinFragment
  simp only [checkBodyFragment_instantiate]

@[simp]
theorem BasicBlockData.instantiateList_length
    (tbl : LayoutTable) (args : TypeSubst) :
    ∀ (bbs : List BasicBlockData),
      (BasicBlockData.instantiateList tbl args bbs).length = bbs.length
  | [] => rfl
  | _ :: rest => by
    simp only [BasicBlockData.instantiateList, List.length_cons,
      BasicBlockData.instantiateList_length tbl args rest]

@[simp]
theorem hasBlockRankViolation_instantiate
    (rank : Nat → Nat) (n u : Nat) (tbl : LayoutTable) (args : TypeSubst) (bb : BasicBlockData) :
    hasBlockRankViolation rank n u (bb.instantiate tbl args) = hasBlockRankViolation rank n u bb := by
  dsimp only [BasicBlockData.instantiate, Terminator.instantiate, hasBlockRankViolation, blockTargets]
  rw [terminatorTargets_instantiate]

@[simp]
theorem hasRankViolationAux_instantiate
    (rank : Nat → Nat) (n : Nat) (tbl : LayoutTable) (args : TypeSubst) :
    ∀ (u : Nat) (bbs : List BasicBlockData),
      hasRankViolationAux rank n u (BasicBlockData.instantiateList tbl args bbs) =
        hasRankViolationAux rank n u bbs
  | _, [] => rfl
  | u, bb :: rest => by
    have h_hd := hasBlockRankViolation_instantiate rank n u tbl args bb
    have h_tl := hasRankViolationAux_instantiate rank n tbl args (u + 1) rest
    dsimp only [BasicBlockData.instantiateList, hasRankViolationAux]
    rw [h_hd, h_tl]

@[simp]
theorem hasRankViolation_instantiate
    (rank : Nat → Nat) (body : CapturedMir) (args : TypeSubst) :
    hasRankViolation rank (body.instantiate args) = hasRankViolation rank body := by
  dsimp only [CapturedMir.instantiate, hasRankViolation]
  rw [BasicBlockData.instantiateList_length, hasRankViolationAux_instantiate]

@[simp]
theorem cfgEdgeListAux_instantiate
    (n : Nat) (tbl : LayoutTable) (args : TypeSubst) :
    ∀ (u : Nat) (bbs : List BasicBlockData),
      cfgEdgeListAux n u (BasicBlockData.instantiateList tbl args bbs) =
        cfgEdgeListAux n u bbs
  | _, [] => rfl
  | u, bb :: rest => by
    have h_tl := cfgEdgeListAux_instantiate n tbl args (u + 1) rest
    dsimp only [BasicBlockData.instantiateList, cfgEdgeListAux,
      BasicBlockData.instantiate, Terminator.instantiate, blockTargets]
    rw [terminatorTargets_instantiate, h_tl]

@[simp]
theorem cfgEdgeList_instantiate
    (body : CapturedMir) (args : TypeSubst) :
    cfgEdgeList (body.instantiate args) = cfgEdgeList body := by
  dsimp only [CapturedMir.instantiate, cfgEdgeList]
  rw [BasicBlockData.instantiateList_length, cfgEdgeListAux_instantiate]

@[simp]
theorem dagRanks_instantiate
    (body : CapturedMir) (args : TypeSubst) :
    dagRanks (body.instantiate args) = dagRanks body := by
  unfold dagRanks
  rw [cfgEdgeList_instantiate]
  dsimp only [CapturedMir.instantiate]
  rw [BasicBlockData.instantiateList_length]

@[simp]
theorem dagRank_instantiate
    (body : CapturedMir) (args : TypeSubst) (i : Nat) :
    dagRank (body.instantiate args) i = dagRank body i := by
  unfold dagRank
  rw [dagRanks_instantiate]

theorem dagRank_instantiate_fun
    (body : CapturedMir) (args : TypeSubst) :
    dagRank (body.instantiate args) = dagRank body := by
  funext i
  exact dagRank_instantiate body args i

/--
**Polymorphic DAG Acyclicity Invariance**:
Instantiating generic type parameters via `CapturedMir.instantiate` preserves
`isCfgDag` (`isCfgDag (body.instantiate args) = isCfgDag body`).
-/
@[simp]
theorem isCfgDag_instantiate
    (body : CapturedMir) (args : TypeSubst) :
    isCfgDag (body.instantiate args) = isCfgDag body := by
  unfold isCfgDag
  rw [dagRank_instantiate_fun, hasRankViolation_instantiate]

/-! ## 8. Concrete `CapturedMir` Witnesses Across All 5 Lattice Levels -/

private def dummyU32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }

private def dummyU32Layout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 4 }
  backendRepr := .memory
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

private def dummyFnAbi : FnAbi := {
  args := []
  ret := { layout := dummyU32Layout, mode := .direct }
  conv := .rust
  canUnwind := false
}

/--
Shared non-`basicBlocks` fields of the synthetic witness bodies below. Every
witness is written as `{ protoBase with defPath := .., basicBlocks := [..] }`
with a fully inline `basicBlocks` literal (no helper identifiers), so that the
`scaffold.rs` unit test `mir_fragment_rust_classifier_matches_lean_witness_theorems`
can classify the *verbatim* text of each witness and compare it against the
kernel-checked `inferMinFragment` / `hasCfgBackedge` theorems in this section.
-/
private def protoBase : CapturedMir := {
  defPath := "proto::base"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [{ mutability := .mut, ty := dummyU32Ty, debugName := none }]
  basicBlocks := []
  fnAbi := dummyFnAbi
  layouts := emptyLayoutTable
  allocations := []
}

/-- Level 0 witness (`.pureLoopFree`): single-block pure scalar assignment and return. -/
def witnessPureLoopFree : CapturedMir :=
  { protoBase with
    defPath := "proto::witness_pure_loop_free"
    basicBlocks :=
      [{ statements :=
           [{ kind := .assign { local_ := 0, projection := [] }
                (.use (.constant { ty := { kind := .uint .u32, layoutIdx := 0 },
                                   val := .scalar (.int { bits := 0, sizeBytes := 4 }) }))
              span := "proto.rs:1:1" }]
         terminator := { kind := .return_, span := "proto.rs:1:10" }
         isCleanup := false }] }

/-- Level 1 witness (`.pureBoundedLoop`): pure loop with CFG back-edge (`bb1 -> bb1`). -/
def witnessPureBoundedLoop : CapturedMir :=
  { protoBase with
    defPath := "proto::witness_pure_bounded_loop"
    basicBlocks :=
      [{ statements := []
         terminator := { kind := .goto 1, span := "proto.rs:2:1" }
         isCleanup := false },
       { statements := []
         terminator :=
           { kind := .switchInt (.copy { local_ := 0, projection := [] })
               { branches := [(0, 2)], otherwise := 1 }
             span := "proto.rs:2:5" }
         isCleanup := false },
       { statements := []
         terminator := { kind := .return_, span := "proto.rs:2:10" }
         isCleanup := false }] }

/-- Level 2 witness (`.treeBorrowsLocal`): local shared reference and deref read. -/
def witnessTreeBorrowsLocal : CapturedMir :=
  { protoBase with
    defPath := "proto::witness_tree_borrows_local"
    basicBlocks :=
      [{ statements :=
           [{ kind := .assign { local_ := 1, projection := [] }
                (.ref .shared { local_ := 0, projection := [] })
              span := "proto.rs:3:1" },
            { kind := .retag .default { local_ := 1, projection := [] }
              span := "proto.rs:3:5" },
            { kind := .assign { local_ := 0, projection := [] }
                (.use (.copy { local_ := 1, projection := [.deref] }))
              span := "proto.rs:3:9" }]
         terminator := { kind := .return_, span := "proto.rs:3:15" }
         isCleanup := false }] }

/-- Level 3 witness (`.intrinsicCopy`): `NonDivergingIntrinsic.copyNonOverlapping`. -/
def witnessIntrinsicCopy : CapturedMir :=
  { protoBase with
    defPath := "proto::witness_intrinsic_copy"
    basicBlocks :=
      [{ statements :=
           [{ kind := .intrinsic
                (.copyNonOverlapping
                  (.copy { local_ := 1, projection := [] })
                  (.copy { local_ := 2, projection := [] })
                  (.constant { ty := { kind := .uint .usize, layoutIdx := 0 },
                               val := .scalar (.int { bits := 0, sizeBytes := 8 }) }))
              span := "proto.rs:4:1" }]
         terminator := { kind := .return_, span := "proto.rs:4:10" }
         isCleanup := false }] }

/-- Level 4 witness (`.fullMir`): interprocedural `TerminatorKind.call`. -/
def witnessFullMir : CapturedMir :=
  { protoBase with
    defPath := "proto::witness_full_mir"
    basicBlocks :=
      [{ statements := []
         terminator :=
           { kind := .call
               (.constant { ty := { kind := .fnDef "proto::callee" [], layoutIdx := 0 },
                            val := .zeroSized })
               []
               { local_ := 0, projection := [] }
               (some 1)
               .continue_
             span := "proto.rs:5:1" }
         isCleanup := false },
       { statements := []
         terminator := { kind := .return_, span := "proto.rs:5:10" }
         isCleanup := false }] }

/--
3-block non-topologically-numbered DAG (`bb0 -> bb2 -> bb1 -> return`): a loop-free
CFG whose numbering has an index back-edge (`bb2 -> bb1`, `1 ≤ 2`), so
`hasCfgBackedge = true` while `isCfgDag = true` certifies acyclicity.
-/
def nonTopoDagWitness : CapturedMir :=
  { protoBase with
    defPath := "proto::non_topo_dag_witness"
    basicBlocks :=
      [{ statements := []
         terminator := { kind := .goto 2, span := "proto.rs:6:1" }
         isCleanup := false },
       { statements := []
         terminator := { kind := .return_, span := "proto.rs:6:5" }
         isCleanup := false },
       { statements := []
         terminator := { kind := .goto 1, span := "proto.rs:6:9" }
         isCleanup := false }] }

/--
Real-`rustc` index-order witness, transcribed (minus its `partial_cmp` call) from
the captured `Runtime` MIR of `core::cmp::PartialOrd::le`: the shared return block
`bb1` is numbered *before* the `match` arms `bb3` / `bb4` that jump to it. The
body is pure and acyclic (`checkPureMir`, `isCfgDag`), yet the index-order rule
classifies it `.pureBoundedLoop` (sound but conservative).
-/
def witnessRustcSharedReturn : CapturedMir :=
  { protoBase with
    defPath := "proto::witness_rustc_shared_return"
    basicBlocks :=
      [{ statements :=
           [{ kind := .assign { local_ := 4, projection := [] }
                (.discriminant { local_ := 3, projection := [] })
              span := "core/src/cmp.rs:1:1" }]
         terminator :=
           { kind := .switchInt (.move { local_ := 4, projection := [] })
               { branches := [(0, 4), (1, 3)], otherwise := 2 }
             span := "core/src/cmp.rs:1:2" }
         isCleanup := false },
       { statements := []
         terminator := { kind := .return_, span := "core/src/cmp.rs:1:3" }
         isCleanup := false },
       { statements := []
         terminator := { kind := .unreachable, span := "core/src/cmp.rs:1:4" }
         isCleanup := false },
       { statements :=
           [{ kind := .assign { local_ := 0, projection := [] }
                (.binaryOp .le (.move { local_ := 6, projection := [] })
                  (.constant { ty := { kind := .int .i8, layoutIdx := 0 },
                               val := .scalar (.int { bits := 0, sizeBytes := 1 }) }))
              span := "core/src/cmp.rs:1:5" }]
         terminator := { kind := .goto 1, span := "core/src/cmp.rs:1:6" }
         isCleanup := false },
       { statements :=
           [{ kind := .assign { local_ := 0, projection := [] }
                (.use (.constant { ty := { kind := .bool, layoutIdx := 0 },
                                   val := .scalar (.int { bits := 0, sizeBytes := 1 }) }))
              span := "core/src/cmp.rs:1:7" }]
         terminator := { kind := .goto 1, span := "core/src/cmp.rs:1:8" }
         isCleanup := false }] }

/--
Shorthand-syntax `Mutability.mut` witness (`.pureLoopFree`): `*mut` / `&mut` types
in cast targets, field projections and constants, plus a pure
`AggregateKind.rawPtr _ .mut` pointer-from-parts aggregate. None of these is a
`BorrowKind.mut` borrow, so the body stays in `.pureLoopFree` (regression fixture
for the `.mut` token ambiguity between `Mutability.mut` and `BorrowKind.mut`).
-/
def witnessShorthandMutTypes : CapturedMir :=
  { protoBase with
    defPath := "proto::witness_shorthand_mut_types"
    basicBlocks :=
      [{ statements :=
           [{ kind := .assign { local_ := 1, projection := [] }
                (.cast .pointerWithExposedProvenance (.copy { local_ := 2, projection := [] })
                  { kind := .rawPtr .mut (.uint .u8), layoutIdx := 1 })
              span := "proto.rs:7:1" },
            { kind := .assign { local_ := 3, projection := [] }
                (.aggregate (.rawPtr { kind := .uint .u8, layoutIdx := 0 } .mut)
                  [.copy { local_ := 1, projection := [] }, .copy { local_ := 2, projection := [] }])
              span := "proto.rs:7:2" },
            { kind := .assign
                { local_ := 4, projection := [.field 0 { kind := .ref .mut (.uint .u32), layoutIdx := 2 }] }
                (.use (.constant { ty := { kind := .rawPtr .mut .bool, layoutIdx := 3 },
                                   val := .scalar (.int { bits := 0, sizeBytes := 8 }) }))
              span := "proto.rs:7:3" }]
         terminator := { kind := .return_, span := "proto.rs:7:4" }
         isCleanup := false }] }

/--
Fully-qualified `rustc-capture` emitter-syntax witness (`.treeBorrowsLocal`):
`Rvalue.rawPtr Mutability.mut` written with `List.cons` / `List.nil` exactly as
`trusted/rustc-capture/src/lean_emit.rs` renders it.
-/
def witnessQualifiedEmitterRawPtr : CapturedMir :=
  { protoBase with
    defPath := "proto::witness_qualified_emitter_raw_ptr"
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 1, projection := List.nil } (Rvalue.rawPtr Mutability.mut { local_ := 2, projection := List.nil })), span := "src/lib.rs:8:1" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:8:2" }, isCleanup := false } List.nil) }

/-- Global-allocation constant witness (`.intrinsicCopy`) without `copyNonOverlapping`. -/
def witnessIndirectConst : CapturedMir :=
  { protoBase with
    defPath := "proto::witness_indirect_const"
    basicBlocks :=
      [{ statements :=
           [{ kind := .assign { local_ := 0, projection := [] }
                (.use (.constant { ty := { kind := .uint .u32, layoutIdx := 0 }, val := .indirect 0 0 }))
              span := "proto.rs:9:1" }]
         terminator := { kind := .return_, span := "proto.rs:9:2" }
         isCleanup := false }] }

/-- Call-free `.fullMir` witness: `CastKind.fnPtrToPtr` and `Rvalue.threadLocalRef`. -/
def witnessFullMirNoCall : CapturedMir :=
  { protoBase with
    defPath := "proto::witness_full_mir_no_call"
    basicBlocks :=
      [{ statements :=
           [{ kind := .assign { local_ := 0, projection := [] }
                (.cast .fnPtrToPtr (.copy { local_ := 1, projection := [] })
                  { kind := .rawPtr .not .bool, layoutIdx := 0 })
              span := "proto.rs:10:1" },
            { kind := .assign { local_ := 2, projection := [] } (.threadLocalRef "proto::TLS")
              span := "proto.rs:10:2" }]
         terminator := { kind := .return_, span := "proto.rs:10:3" }
         isCleanup := false }] }

/--
Out-of-order record fields & parenthesized span witness (`.pureBoundedLoop`):
`BasicBlockData` writes `isCleanup` before `terminator` and `statements` last;
`Terminator` writes parenthesized `span := ("...")` before `kind :=`; and
`SwitchTargets` writes `otherwise := 0` (back-edge `0 ≤ 0`) before `branches :=`.
-/
def witnessOutOfOrderFieldsAndParenSpan : CapturedMir :=
  { protoBase with
    defPath := "proto::witness_out_of_order_fields_and_paren_span"
    basicBlocks :=
      [{ isCleanup := false
         terminator :=
           { span := ("proto.rs:11:1")
             kind := .switchInt (.copy { projection := [], local_ := 0 })
               { otherwise := 0, branches := [(1, 1)] } }
         statements := [] },
       { isCleanup := false
         terminator := { span := ("proto.rs:11:2"), kind := .return_ }
         statements := [] }] }

/--
Raw-string lexer witness (`.fullMir`): `defPath` is the raw string literal
`r#"proto"::raw"#` (an unescaped `"` inside), and a later `span` string contains
the text `basicBlocks := []`. A lexer that treats `r#"..."#` as an ordinary string
loses string polarity, exposes that `span` text as code, and would classify the
body as an empty pure body; the real body ends in a `TerminatorKind.call`.
-/
def witnessRawStringDefPath : CapturedMir :=
  { protoBase with
    defPath := r#"proto"::raw"#
    basicBlocks :=
      [{ statements := []
         terminator :=
           { kind := .call
               (.constant { ty := { kind := .fnDef "proto::callee" [], layoutIdx := 0 },
                            val := .zeroSized })
               [] { local_ := 0, projection := [] } (some 1) .continue_
             span := " basicBlocks := [] fnAbi := " }
         isCleanup := false },
       { statements := []
         terminator := { kind := .return_, span := "proto.rs:12:2" }
         isCleanup := false }] }

/--
Named-argument witness (`.treeBorrowsLocal`): `.unevaluated (defPath := "..")`
reuses the `CapturedMir` field name `defPath` inside `basicBlocks`; a scanner that
ends the `basicBlocks` value at the first textual `defPath :=` would miss the
later `ProjectionElem.deref` (the block lists `statements` last).
-/
def witnessNamedDefPathArg : CapturedMir :=
  { protoBase with
    defPath := "proto::witness_named_def_path_arg"
    basicBlocks :=
      [{ isCleanup := false
         terminator := { kind := .return_, span := "proto.rs:13:1" }
         statements :=
           [{ kind := .assign { local_ := 0, projection := [] }
                (.use (.constant { ty := { kind := .uint .u32, layoutIdx := 0 },
                                   val := .unevaluated (defPath := "proto::C") }))
              span := "proto.rs:13:2" },
            { kind := .assign { local_ := 1, projection := [] }
                (.use (.copy { local_ := 2, projection := [.deref] }))
              span := "proto.rs:13:3" }] }] }

/--
Column-aligned fields & interpolated-char-literal lexer witness (`.fullMir`):
`defPath` uses an interpolated string `s!"proto::{if '}' == '"' then "a" else "b"}"`
whose `{..}` interpolation contains `'}'` and `'"'` character literals; `basicBlocks`
and `isCleanup` use multi-space column alignment (`basicBlocks  :=`, `isCleanup  :=`);
and `bb0` ends in a `TerminatorKind.call` whose `span` contains `" basicBlocks := [] fnAbi := "`.
-/
def witnessAlignedAndInterpCharDefPath : CapturedMir :=
  { protoBase with
    defPath      := s!"proto::{if '}' == '"' then "a" else "b"}"
    basicBlocks  :=
      [{ statements := []
         terminator :=
           { kind := .call
               (.constant { ty := { kind := .fnDef "proto::callee" [], layoutIdx := 0 },
                            val := .zeroSized })
               [] { local_ := 0, projection := [] } (some 1) .continue_
             span := " basicBlocks := [] fnAbi := " }
         isCleanup  := false },
       { statements := []
         terminator := { kind := .return_, span := "proto.rs:14:2" }
         isCleanup  := false }] }

theorem inferMinFragment_witnessPureLoopFree :
    inferMinFragment witnessPureLoopFree = .pureLoopFree := rfl

theorem inferMinFragment_witnessPureBoundedLoop :
    inferMinFragment witnessPureBoundedLoop = .pureBoundedLoop := rfl

theorem inferMinFragment_witnessTreeBorrowsLocal :
    inferMinFragment witnessTreeBorrowsLocal = .treeBorrowsLocal := rfl

theorem inferMinFragment_witnessIntrinsicCopy :
    inferMinFragment witnessIntrinsicCopy = .intrinsicCopy := rfl

theorem inferMinFragment_witnessFullMir :
    inferMinFragment witnessFullMir = .fullMir := rfl

theorem inferMinFragment_nonTopoDagWitness :
    inferMinFragment nonTopoDagWitness = .pureBoundedLoop := rfl

theorem inferMinFragment_witnessRustcSharedReturn :
    inferMinFragment witnessRustcSharedReturn = .pureBoundedLoop := rfl

theorem inferMinFragment_witnessShorthandMutTypes :
    inferMinFragment witnessShorthandMutTypes = .pureLoopFree := rfl

theorem inferMinFragment_witnessQualifiedEmitterRawPtr :
    inferMinFragment witnessQualifiedEmitterRawPtr = .treeBorrowsLocal := rfl

theorem inferMinFragment_witnessIndirectConst :
    inferMinFragment witnessIndirectConst = .intrinsicCopy := rfl

theorem inferMinFragment_witnessFullMirNoCall :
    inferMinFragment witnessFullMirNoCall = .fullMir := rfl

theorem inferMinFragment_witnessOutOfOrderFieldsAndParenSpan :
    inferMinFragment witnessOutOfOrderFieldsAndParenSpan = .pureBoundedLoop := rfl

theorem inferMinFragment_witnessRawStringDefPath :
    inferMinFragment witnessRawStringDefPath = .fullMir := rfl

theorem inferMinFragment_witnessNamedDefPathArg :
    inferMinFragment witnessNamedDefPathArg = .treeBorrowsLocal := rfl

theorem inferMinFragment_witnessAlignedAndInterpCharDefPath :
    inferMinFragment witnessAlignedAndInterpCharDefPath = .fullMir := rfl

theorem hasCfgBackedge_witnessPureLoopFree : hasCfgBackedge witnessPureLoopFree = false := rfl

theorem hasCfgBackedge_witnessPureBoundedLoop : hasCfgBackedge witnessPureBoundedLoop = true := rfl

theorem hasCfgBackedge_witnessFullMir : hasCfgBackedge witnessFullMir = false := rfl

theorem hasCfgBackedge_nonTopoDagWitness : hasCfgBackedge nonTopoDagWitness = true := rfl

theorem hasCfgBackedge_witnessRustcSharedReturn :
    hasCfgBackedge witnessRustcSharedReturn = true := rfl

theorem hasCfgBackedge_witnessAlignedAndInterpCharDefPath :
    hasCfgBackedge witnessAlignedAndInterpCharDefPath = false := rfl

/--
**Index-order vs. general DAG acyclicity**: `nonTopoDagWitness` has an index
back-edge (`hasCfgBackedge = true`) but is certified acyclic (`isCfgDag = true`),
so it is classified `.pureBoundedLoop` although no loop exists.
-/
theorem nonTopoDagWitness_backedge_vs_dag :
    hasCfgBackedge nonTopoDagWitness = true ∧
    isCfgDag nonTopoDagWitness = true ∧
    inferMinFragment nonTopoDagWitness = .pureBoundedLoop :=
  ⟨rfl, rfl, rfl⟩

/-- `nonTopoDagWitness` has no directed CFG cycle (kernel-checked via `isCfgDag`). -/
theorem nonTopoDagWitness_acyclic (u : BasicBlockIdx) : ¬ CfgPath nonTopoDagWitness u u :=
  no_cfg_cycle_of_isCfgDag rfl u

/--
The real-`rustc` shared-return pattern is pure and acyclic, yet classified
`.pureBoundedLoop` by the (sound, conservative) index-order rule.
-/
theorem witnessRustcSharedReturn_pure_acyclic_but_pureBoundedLoop :
    Anneal.PureMirExec.checkPureMir witnessRustcSharedReturn = true ∧
    hasCfgBackedge witnessRustcSharedReturn = true ∧
    isCfgDag witnessRustcSharedReturn = true ∧
    inferMinFragment witnessRustcSharedReturn = .pureBoundedLoop :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem witnessRustcSharedReturn_acyclic (u : BasicBlockIdx) :
    ¬ CfgPath witnessRustcSharedReturn u u :=
  no_cfg_cycle_of_isCfgDag rfl u

/-- `witnessPureBoundedLoop` has a genuine self-loop `bb1 -> bb1` (and `isCfgDag` rejects it). -/
theorem witnessPureBoundedLoop_cycle :
    CfgPath witnessPureBoundedLoop 1 1 ∧ isCfgDag witnessPureBoundedLoop = false :=
  ⟨.single ⟨_, rfl, by decide⟩, rfl⟩

#guard inferMinFragment witnessPureLoopFree == .pureLoopFree
#guard inferMinFragment witnessPureBoundedLoop == .pureBoundedLoop
#guard inferMinFragment witnessTreeBorrowsLocal == .treeBorrowsLocal
#guard inferMinFragment witnessIntrinsicCopy == .intrinsicCopy
#guard inferMinFragment witnessFullMir == .fullMir
#guard hasCfgBackedge nonTopoDagWitness == true
#guard isCfgDag nonTopoDagWitness == true
#guard isCfgDag witnessPureBoundedLoop == false
#guard MirFragment.fromStr? " pure_loop_free" == none
#guard (default : MirFragment) == .fullMir

/-! ## 9. Single-Pass Bottom-Up Lattice Inference (`inferMinFragmentSinglePass`) -/

/-- Minimum fragment required by a single `ConstValue`. -/
def minConstFragment : ConstValue → MirFragment
  | .zeroSized => .pureLoopFree
  | .scalar _ => .pureLoopFree
  | .slice (.int _) _ => .pureLoopFree
  | .slice (.ptr _ _) _ => .intrinsicCopy
  | .indirect _ _ => .intrinsicCopy
  | .unevaluated _ => .pureLoopFree

/-- Minimum fragment required by a single `ProjectionElem`. -/
def minProjElemFragment : ProjectionElem → MirFragment
  | .deref => .treeBorrowsLocal
  | .field _ _ => .pureLoopFree
  | .index _ => .pureLoopFree
  | .constantIndex .. => .pureLoopFree
  | .subslice .. => .pureLoopFree
  | .downcast _ _ => .pureLoopFree
  | .opaqueCast _ => .pureLoopFree
  | .unwrapUnsafeBinder _ => .treeBorrowsLocal

/-- Join `g x` across all elements of `xs`, starting from `.pureLoopFree`. -/
def joinList {α : Type} (g : α → MirFragment) : List α → MirFragment
  | [] => .pureLoopFree
  | x :: xs => (g x).join (joinList g xs)

/-- Minimum fragment required by a `Place`. -/
def minPlaceFragment (p : Place) : MirFragment :=
  joinList minProjElemFragment p.projection

/-- Minimum fragment required by an `Operand`. -/
def minOperandFragment : Operand → MirFragment
  | .copy p => minPlaceFragment p
  | .move p => minPlaceFragment p
  | .constant c => minConstFragment c.val

/-- Minimum fragment required by a `BinOp`. -/
def minBinOpFragment : BinOp → MirFragment
  | .offset => .treeBorrowsLocal
  | _ => .pureLoopFree

/-- Minimum fragment required by a `CastKind`. -/
def minCastFragment : CastKind → MirFragment
  | .pointerCoercion _ => .treeBorrowsLocal
  | .ptrToPtr => .treeBorrowsLocal
  | .fnPtrToPtr => .fullMir
  | _ => .pureLoopFree

/-- Minimum fragment required by an `Rvalue`. -/
def minRvalueFragment : Rvalue → MirFragment
  | .use op => minOperandFragment op
  | .repeat op _ => minOperandFragment op
  | .ref _ p => MirFragment.treeBorrowsLocal.join (minPlaceFragment p)
  | .rawPtr _ p => MirFragment.treeBorrowsLocal.join (minPlaceFragment p)
  | .threadLocalRef _ => .fullMir
  | .len p => minPlaceFragment p
  | .cast ck op _ => (minCastFragment ck).join (minOperandFragment op)
  | .binaryOp op lhs rhs =>
    (minBinOpFragment op).join ((minOperandFragment lhs).join (minOperandFragment rhs))
  | .nullaryOp _ _ => .pureLoopFree
  | .unaryOp _ op => minOperandFragment op
  | .discriminant p => minPlaceFragment p
  | .aggregate _ ops => joinList minOperandFragment ops
  | .shallowInitBox op _ => MirFragment.fullMir.join (minOperandFragment op)
  | .copyForDeref p => MirFragment.treeBorrowsLocal.join (minPlaceFragment p)
  | .wrapUnsafeBinder op _ => minOperandFragment op

/-- Minimum fragment required by a `StatementKind`. -/
def minStmtFragment : StatementKind → MirFragment
  | .assign p r => (minPlaceFragment p).join (minRvalueFragment r)
  | .setDiscriminant p _ => minPlaceFragment p
  | .storageLive _ => .pureLoopFree
  | .storageDead _ => .pureLoopFree
  | .nop => .pureLoopFree
  | .coverage => .pureLoopFree
  | .constEvalCounter => .pureLoopFree
  | .placeMention p => minPlaceFragment p
  | .deinit p => minPlaceFragment p
  | .intrinsic (.assume op) => minOperandFragment op
  | .intrinsic (.copyNonOverlapping src dst count) =>
    (MirFragment.intrinsicCopy.join (minOperandFragment src)).join
      ((minOperandFragment dst).join (minOperandFragment count))
  | .retag _ p => MirFragment.treeBorrowsLocal.join (minPlaceFragment p)
  | .backwardIncompatibleDropHint p => MirFragment.fullMir.join (minPlaceFragment p)

/-- Minimum fragment required by a `TerminatorKind`. -/
def minTerminatorFragment : TerminatorKind → MirFragment
  | .goto _ => .pureLoopFree
  | .switchInt discr _ => minOperandFragment discr
  | .return_ => .pureLoopFree
  | .assert cond _ _ _ => minOperandFragment cond
  | .drop p _ _ => minPlaceFragment p
  | .unreachable => .pureLoopFree
  | .unwindResume => .pureLoopFree
  | .unwindTerminate => .pureLoopFree
  | .call func args dest _ _ =>
    ((MirFragment.fullMir.join (minOperandFragment func)).join
      (joinList minOperandFragment args)).join
      (minPlaceFragment dest)
  | .tailCall func args =>
    (MirFragment.fullMir.join (minOperandFragment func)).join
      (joinList minOperandFragment args)
  | .inlineAsm _ _ _ => .fullMir

/-- Minimum fragment required by a `BasicBlockData`. -/
def minBlockFragment (bb : BasicBlockData) : MirFragment :=
  (joinList (fun s => minStmtFragment s.kind) bb.statements).join
    (minTerminatorFragment bb.terminator.kind)

/--
Single-pass bottom-up fragment inference over `body : CapturedMir`, directly
mirroring `scan_captured_mir_body` in `crates/cargo-anneal/src/scaffold.rs`.
-/
def inferMinFragmentSinglePass (body : CapturedMir) : MirFragment :=
  let blocksFrag := joinList minBlockFragment body.basicBlocks
  if hasCfgBackedge body then
    blocksFrag.join .pureBoundedLoop
  else
    blocksFrag

theorem decide_join_le (a b f : MirFragment) :
    (decide (a ≤ f) && decide (b ≤ f)) = decide (a.join b ≤ f) := by
  cases a <;> cases b <;> cases f <;> rfl

theorem list_all_decide_le_eq_joinList {α : Type} (g : α → MirFragment) (f : MirFragment) :
    ∀ (xs : List α),
      xs.all (fun x => decide (g x ≤ f)) = decide (joinList g xs ≤ f)
  | [] => by cases f <;> rfl
  | x :: xs => by
    dsimp only [List.all_cons, joinList]
    rw [list_all_decide_le_eq_joinList g f xs, decide_join_le]
    rfl

theorem checkConstFragment_eq_decide (f : MirFragment) (cv : ConstValue) :
    checkConstFragment f cv = decide (minConstFragment cv ≤ f) := by
  cases cv with
  | slice sc _ => cases sc <;> cases f <;> rfl
  | _ => cases f <;> rfl

theorem checkProjElemFragment_eq_decide (f : MirFragment) (pe : ProjectionElem) :
    checkProjElemFragment f pe = decide (minProjElemFragment pe ≤ f) := by
  cases pe <;> cases f <;> rfl

theorem checkPlaceFragment_eq_decide (f : MirFragment) (p : Place) :
    checkPlaceFragment f p = decide (minPlaceFragment p ≤ f) := by
  dsimp only [checkPlaceFragment, minPlaceFragment]
  rw [congrArg p.projection.all (funext (checkProjElemFragment_eq_decide f)),
    list_all_decide_le_eq_joinList]
  rfl

theorem checkOperandFragment_eq_decide (f : MirFragment) (op : Operand) :
    checkOperandFragment f op = decide (minOperandFragment op ≤ f) := by
  cases op with
  | copy p | move p => exact checkPlaceFragment_eq_decide f p
  | constant c => exact checkConstFragment_eq_decide f c.val

theorem checkBinOpFragment_eq_decide (f : MirFragment) (op : BinOp) :
    checkBinOpFragment f op = decide (minBinOpFragment op ≤ f) := by
  cases op <;> cases f <;> rfl

theorem checkCastFragment_eq_decide (f : MirFragment) (ck : CastKind) :
    checkCastFragment f ck = decide (minCastFragment ck ≤ f) := by
  cases ck <;> cases f <;> rfl

theorem checkRvalueFragment_eq_decide (f : MirFragment) (rv : Rvalue) :
    checkRvalueFragment f rv = decide (minRvalueFragment rv ≤ f) := by
  cases rv with
  | use op | «repeat» op _ | unaryOp _ op | wrapUnsafeBinder op _ =>
    exact checkOperandFragment_eq_decide f op
  | len p | discriminant p =>
    exact checkPlaceFragment_eq_decide f p
  | nullaryOp _ _ => cases f <;> rfl
  | threadLocalRef _ => cases f <;> rfl
  | ref _ p | rawPtr _ p | copyForDeref p =>
    dsimp only [checkRvalueFragment, minRvalueFragment]
    rw [checkPlaceFragment_eq_decide, decide_join_le]
    rfl
  | cast ck op _ =>
    dsimp only [checkRvalueFragment, minRvalueFragment]
    rw [checkCastFragment_eq_decide, checkOperandFragment_eq_decide, decide_join_le]
    rfl
  | binaryOp op lhs rhs =>
    dsimp only [checkRvalueFragment, minRvalueFragment]
    rw [checkBinOpFragment_eq_decide, checkOperandFragment_eq_decide,
      checkOperandFragment_eq_decide, decide_join_le, decide_join_le]
    rfl
  | aggregate _ ops =>
    dsimp only [checkRvalueFragment, minRvalueFragment]
    rw [congrArg ops.all (funext (checkOperandFragment_eq_decide f)),
      list_all_decide_le_eq_joinList]
    rfl
  | shallowInitBox op _ =>
    dsimp only [checkRvalueFragment, minRvalueFragment]
    rw [checkOperandFragment_eq_decide, decide_join_le]
    rfl

theorem checkStmtFragment_eq_decide (f : MirFragment) (sk : StatementKind) :
    checkStmtFragment f sk = decide (minStmtFragment sk ≤ f) := by
  cases sk with
  | assign p r =>
    dsimp only [checkStmtFragment, minStmtFragment]
    rw [checkPlaceFragment_eq_decide, checkRvalueFragment_eq_decide, decide_join_le]
    rfl
  | setDiscriminant p _ | placeMention p | deinit p =>
    exact checkPlaceFragment_eq_decide f p
  | storageLive _ | storageDead _ | nop | coverage | constEvalCounter =>
    cases f <;> rfl
  | intrinsic intr =>
    cases intr with
    | assume op => exact checkOperandFragment_eq_decide f op
    | copyNonOverlapping src dst count =>
      dsimp only [checkStmtFragment, minStmtFragment]
      rw [checkOperandFragment_eq_decide, checkOperandFragment_eq_decide,
        checkOperandFragment_eq_decide, Bool.and_assoc, decide_join_le,
        decide_join_le, decide_join_le]
      rfl
  | retag _ p | backwardIncompatibleDropHint p =>
    dsimp only [checkStmtFragment, minStmtFragment]
    rw [checkPlaceFragment_eq_decide, decide_join_le]
    rfl

theorem checkTerminatorFragment_eq_decide (f : MirFragment) (tk : TerminatorKind) :
    checkTerminatorFragment f tk = decide (minTerminatorFragment tk ≤ f) := by
  cases tk with
  | goto _ | return_ | unreachable | unwindResume | unwindTerminate | inlineAsm _ _ _ =>
    cases f <;> rfl
  | switchInt discr _ => exact checkOperandFragment_eq_decide f discr
  | assert cond _ _ _ => exact checkOperandFragment_eq_decide f cond
  | drop p _ _ => exact checkPlaceFragment_eq_decide f p
  | call func args dest _ _ =>
    dsimp only [checkTerminatorFragment, minTerminatorFragment]
    rw [checkOperandFragment_eq_decide,
      congrArg args.all (funext (checkOperandFragment_eq_decide f)),
      list_all_decide_le_eq_joinList, checkPlaceFragment_eq_decide,
      decide_join_le, decide_join_le, decide_join_le]
    rfl
  | tailCall func args =>
    dsimp only [checkTerminatorFragment, minTerminatorFragment]
    rw [checkOperandFragment_eq_decide,
      congrArg args.all (funext (checkOperandFragment_eq_decide f)),
      list_all_decide_le_eq_joinList, decide_join_le, decide_join_le]
    rfl

theorem checkBlockFragment_eq_decide (f : MirFragment) (bb : BasicBlockData) :
    checkBlockFragment f bb = decide (minBlockFragment bb ≤ f) := by
  dsimp only [checkBlockFragment, minBlockFragment]
  rw [congrArg bb.statements.all (funext fun s => checkStmtFragment_eq_decide f s.kind),
    list_all_decide_le_eq_joinList (fun (s : Statement) => minStmtFragment s.kind) f bb.statements,
    checkTerminatorFragment_eq_decide, decide_join_le]
  rfl

theorem checkBodyFragment_eq_decide_singlePass (f : MirFragment) (body : CapturedMir) :
    checkBodyFragment f body = decide (inferMinFragmentSinglePass body ≤ f) := by
  have h_all :
      body.basicBlocks.all (checkBlockFragment f) =
        decide (joinList minBlockFragment body.basicBlocks ≤ f) := by
    rw [congrArg body.basicBlocks.all (funext (checkBlockFragment_eq_decide f)),
      list_all_decide_le_eq_joinList]
  unfold checkBodyFragment inferMinFragmentSinglePass
  cases f <;>
    rw [h_all] <;>
    cases hasCfgBackedge body <;>
    cases joinList minBlockFragment body.basicBlocks <;>
    rfl

/--
**Isomorphism of Top-Down and Single-Pass Bottom-Up Fragment Inference**:
`inferMinFragmentSinglePass body` (single-pass AST fold with `MirFragment.join`)
equals `inferMinFragment body` for every `body : CapturedMir`.
-/
theorem inferMinFragmentSinglePass_eq_inferMinFragment (body : CapturedMir) :
    inferMinFragmentSinglePass body = inferMinFragment body := by
  apply MirFragment.le_antisymm
  · have h_in : checkBodyFragment (inferMinFragment body) body = true :=
      checkBodyFragment_inferMinFragment body
    rw [checkBodyFragment_eq_decide_singlePass, decide_eq_true_eq] at h_in
    exact h_in
  · apply inferMinFragment_minimal
    rw [checkBodyFragment_eq_decide_singlePass, decide_eq_true_eq]
    exact MirFragment.le_refl _

/--
**Polymorphic Single-Pass Fragment Inference Invariance**:
`inferMinFragmentSinglePass (body.instantiate args) = inferMinFragmentSinglePass body`.
-/
@[simp]
theorem inferMinFragmentSinglePass_instantiate
    (body : CapturedMir) (args : TypeSubst) :
    inferMinFragmentSinglePass (body.instantiate args) = inferMinFragmentSinglePass body := by
  rw [inferMinFragmentSinglePass_eq_inferMinFragment,
    inferMinFragmentSinglePass_eq_inferMinFragment,
    inferMinFragment_instantiate]

theorem le_joinList_of_mem {α : Type} (g : α → MirFragment) {x : α} {xs : List α}
    (h_mem : x ∈ xs) : g x ≤ joinList g xs := by
  induction xs with
  | nil => cases h_mem
  | cons hd tl ih =>
    simp only [List.mem_cons] at h_mem
    rcases h_mem with rfl | h_tl
    · exact MirFragment.le_join_left _ _
    · exact MirFragment.le_trans (ih h_tl) (MirFragment.le_join_right _ _)

theorem joinList_minBlockFragment_le_inferMinFragment (body : CapturedMir) :
    joinList minBlockFragment body.basicBlocks ≤ inferMinFragment body := by
  rw [← inferMinFragmentSinglePass_eq_inferMinFragment]
  unfold inferMinFragmentSinglePass
  cases hasCfgBackedge body
  · exact MirFragment.le_refl _
  · exact MirFragment.le_join_left _ _

/--
**Universal Block Lower-Bound Theorem**:
Every basic block `bb ∈ body.basicBlocks` bounds `inferMinFragment body` from below
(`minBlockFragment bb ≤ inferMinFragment body`).
-/
theorem minBlockFragment_le_inferMinFragment_of_mem
    {body : CapturedMir} {bb : BasicBlockData} (h_bb : bb ∈ body.basicBlocks) :
    minBlockFragment bb ≤ inferMinFragment body :=
  MirFragment.le_trans
    (le_joinList_of_mem minBlockFragment h_bb)
    (joinList_minBlockFragment_le_inferMinFragment body)

/--
**Universal Statement Lower-Bound Theorem**:
Every statement `stmt ∈ bb.statements` in any block `bb ∈ body.basicBlocks`
bounds `inferMinFragment body` from below (`minStmtFragment stmt.kind ≤ inferMinFragment body`).
-/
theorem minStmtFragment_le_inferMinFragment_of_mem
    {body : CapturedMir} {bb : BasicBlockData} {stmt : Statement}
    (h_bb : bb ∈ body.basicBlocks) (h_stmt : stmt ∈ bb.statements) :
    minStmtFragment stmt.kind ≤ inferMinFragment body := by
  have h_s : minStmtFragment stmt.kind ≤ minBlockFragment bb :=
    MirFragment.le_trans
      (le_joinList_of_mem (fun (s : Statement) => minStmtFragment s.kind) h_stmt)
      (MirFragment.le_join_left _ _)
  exact MirFragment.le_trans h_s (minBlockFragment_le_inferMinFragment_of_mem h_bb)

/--
**Universal Terminator Lower-Bound Theorem**:
Every block terminator `bb.terminator` in `bb ∈ body.basicBlocks` bounds
`inferMinFragment body` from below (`minTerminatorFragment bb.terminator.kind ≤ inferMinFragment body`).
-/
theorem minTerminatorFragment_le_inferMinFragment_of_mem
    {body : CapturedMir} {bb : BasicBlockData} (h_bb : bb ∈ body.basicBlocks) :
    minTerminatorFragment bb.terminator.kind ≤ inferMinFragment body :=
  MirFragment.le_trans
    (MirFragment.le_join_right _ _)
    (minBlockFragment_le_inferMinFragment_of_mem h_bb)

/--
If `f < inferMinFragment body`, then `checkBodyFragment f body = false`.
-/
theorem checkBodyFragment_false_of_lt_inferMinFragment
    {body : CapturedMir} {f : MirFragment}
    (hf : f < inferMinFragment body) :
    checkBodyFragment f body = false := by
  cases h : checkBodyFragment f body
  · rfl
  · exact absurd (inferMinFragment_minimal body f h) (Nat.not_le_of_lt hf)

/--
**Universal Statement Downward-Closed Exclusion Theorem**:
If `stmt ∈ bb.statements` (`bb ∈ body.basicBlocks`) and `f < minStmtFragment stmt.kind`,
then `checkBodyFragment f body = false`.
-/
theorem checkBodyFragment_false_of_lt_minStmtFragment
    {body : CapturedMir} {bb : BasicBlockData} {stmt : Statement} {f : MirFragment}
    (h_bb : bb ∈ body.basicBlocks) (h_stmt : stmt ∈ bb.statements)
    (hf : f < minStmtFragment stmt.kind) :
    checkBodyFragment f body = false := by
  apply checkBodyFragment_false_of_lt_inferMinFragment
  exact Nat.lt_of_lt_of_le hf (minStmtFragment_le_inferMinFragment_of_mem h_bb h_stmt)

/--
**Universal Terminator Downward-Closed Exclusion Theorem**:
If `bb ∈ body.basicBlocks` and `f < minTerminatorFragment bb.terminator.kind`,
then `checkBodyFragment f body = false`.
-/
theorem checkBodyFragment_false_of_lt_minTerminatorFragment
    {body : CapturedMir} {bb : BasicBlockData} {f : MirFragment}
    (h_bb : bb ∈ body.basicBlocks)
    (hf : f < minTerminatorFragment bb.terminator.kind) :
    checkBodyFragment f body = false := by
  apply checkBodyFragment_false_of_lt_inferMinFragment
  exact Nat.lt_of_lt_of_le hf (minTerminatorFragment_le_inferMinFragment_of_mem h_bb)

/-! ## 10. Rank 1 Is a Pure CFG Property (`.pureLoopFree` Characterization) -/

theorem join_ne_pureBoundedLoop {a b : MirFragment}
    (ha : a ≠ .pureBoundedLoop) (hb : b ≠ .pureBoundedLoop) :
    a.join b ≠ .pureBoundedLoop := by
  cases a <;> cases b <;> first | decide | exact absurd rfl ha | exact absurd rfl hb

theorem joinList_ne_pureBoundedLoop {α : Type} {g : α → MirFragment}
    (hg : ∀ x, g x ≠ .pureBoundedLoop) :
    ∀ xs : List α, joinList g xs ≠ .pureBoundedLoop
  | [] => nofun
  | x :: xs => join_ne_pureBoundedLoop (hg x) (joinList_ne_pureBoundedLoop hg xs)

theorem minConstFragment_ne_pureBoundedLoop (cv : ConstValue) :
    minConstFragment cv ≠ .pureBoundedLoop := by
  cases cv with
  | slice sc _ => cases sc <;> nofun
  | _ => nofun

theorem minProjElemFragment_ne_pureBoundedLoop (pe : ProjectionElem) :
    minProjElemFragment pe ≠ .pureBoundedLoop := by
  cases pe <;> nofun

theorem minPlaceFragment_ne_pureBoundedLoop (p : Place) :
    minPlaceFragment p ≠ .pureBoundedLoop :=
  joinList_ne_pureBoundedLoop minProjElemFragment_ne_pureBoundedLoop p.projection

theorem minOperandFragment_ne_pureBoundedLoop (op : Operand) :
    minOperandFragment op ≠ .pureBoundedLoop := by
  cases op with
  | copy p | move p => exact minPlaceFragment_ne_pureBoundedLoop p
  | constant c => exact minConstFragment_ne_pureBoundedLoop c.val

theorem minBinOpFragment_ne_pureBoundedLoop (op : BinOp) :
    minBinOpFragment op ≠ .pureBoundedLoop := by
  cases op <;> nofun

theorem minCastFragment_ne_pureBoundedLoop (ck : CastKind) :
    minCastFragment ck ≠ .pureBoundedLoop := by
  cases ck <;> nofun

theorem minRvalueFragment_ne_pureBoundedLoop (rv : Rvalue) :
    minRvalueFragment rv ≠ .pureBoundedLoop := by
  cases rv with
  | use op | «repeat» op _ | unaryOp _ op | wrapUnsafeBinder op _ =>
    exact minOperandFragment_ne_pureBoundedLoop op
  | len p | discriminant p => exact minPlaceFragment_ne_pureBoundedLoop p
  | nullaryOp _ _ | threadLocalRef _ => nofun
  | ref _ p | rawPtr _ p | copyForDeref p =>
    exact join_ne_pureBoundedLoop (by decide) (minPlaceFragment_ne_pureBoundedLoop p)
  | cast ck op _ =>
    exact join_ne_pureBoundedLoop (minCastFragment_ne_pureBoundedLoop ck)
      (minOperandFragment_ne_pureBoundedLoop op)
  | binaryOp op lhs rhs =>
    exact join_ne_pureBoundedLoop (minBinOpFragment_ne_pureBoundedLoop op)
      (join_ne_pureBoundedLoop (minOperandFragment_ne_pureBoundedLoop lhs)
        (minOperandFragment_ne_pureBoundedLoop rhs))
  | aggregate _ ops => exact joinList_ne_pureBoundedLoop minOperandFragment_ne_pureBoundedLoop ops
  | shallowInitBox op _ =>
    exact join_ne_pureBoundedLoop (by decide) (minOperandFragment_ne_pureBoundedLoop op)

theorem minStmtFragment_ne_pureBoundedLoop (sk : StatementKind) :
    minStmtFragment sk ≠ .pureBoundedLoop := by
  cases sk with
  | assign p r =>
    exact join_ne_pureBoundedLoop (minPlaceFragment_ne_pureBoundedLoop p)
      (minRvalueFragment_ne_pureBoundedLoop r)
  | setDiscriminant p _ | placeMention p | deinit p => exact minPlaceFragment_ne_pureBoundedLoop p
  | storageLive _ | storageDead _ | nop | coverage | constEvalCounter => nofun
  | intrinsic intr =>
    cases intr with
    | assume op => exact minOperandFragment_ne_pureBoundedLoop op
    | copyNonOverlapping src dst count =>
      exact join_ne_pureBoundedLoop
        (join_ne_pureBoundedLoop (by decide) (minOperandFragment_ne_pureBoundedLoop src))
        (join_ne_pureBoundedLoop (minOperandFragment_ne_pureBoundedLoop dst)
          (minOperandFragment_ne_pureBoundedLoop count))
  | retag _ p | backwardIncompatibleDropHint p =>
    exact join_ne_pureBoundedLoop (by decide) (minPlaceFragment_ne_pureBoundedLoop p)

theorem minTerminatorFragment_ne_pureBoundedLoop (tk : TerminatorKind) :
    minTerminatorFragment tk ≠ .pureBoundedLoop := by
  cases tk with
  | goto _ | return_ | unreachable | unwindResume | unwindTerminate | inlineAsm _ _ _ => nofun
  | switchInt discr _ => exact minOperandFragment_ne_pureBoundedLoop discr
  | assert cond _ _ _ => exact minOperandFragment_ne_pureBoundedLoop cond
  | drop p _ _ => exact minPlaceFragment_ne_pureBoundedLoop p
  | call func args dest _ _ =>
    exact join_ne_pureBoundedLoop
      (join_ne_pureBoundedLoop
        (join_ne_pureBoundedLoop (by decide) (minOperandFragment_ne_pureBoundedLoop func))
        (joinList_ne_pureBoundedLoop minOperandFragment_ne_pureBoundedLoop args))
      (minPlaceFragment_ne_pureBoundedLoop dest)
  | tailCall func args =>
    exact join_ne_pureBoundedLoop
      (join_ne_pureBoundedLoop (by decide) (minOperandFragment_ne_pureBoundedLoop func))
      (joinList_ne_pureBoundedLoop minOperandFragment_ne_pureBoundedLoop args)

/--
**No basic block requires exactly `.pureBoundedLoop`**: rank 1 of the lattice is
a pure CFG property (`hasCfgBackedge`), never a per-construct one.
-/
theorem minBlockFragment_ne_pureBoundedLoop (bb : BasicBlockData) :
    minBlockFragment bb ≠ .pureBoundedLoop :=
  join_ne_pureBoundedLoop
    (joinList_ne_pureBoundedLoop (fun s => minStmtFragment_ne_pureBoundedLoop s.kind) bb.statements)
    (minTerminatorFragment_ne_pureBoundedLoop bb.terminator.kind)

theorem checkBlockFragment_pureLoopFree_eq_pureBoundedLoop (bb : BasicBlockData) :
    checkBlockFragment .pureLoopFree bb = checkBlockFragment .pureBoundedLoop bb := by
  rw [checkBlockFragment_eq_decide, checkBlockFragment_eq_decide]
  have h := minBlockFragment_ne_pureBoundedLoop bb
  generalize minBlockFragment bb = m at h ⊢
  cases m <;> first | rfl | exact absurd rfl h

/--
**Exact characterization of `.pureLoopFree`**: membership is precisely
`checkPureMir body && !hasCfgBackedge body`.
-/
theorem checkBodyFragment_pureLoopFree_eq (body : CapturedMir) :
    checkBodyFragment .pureLoopFree body =
      (checkPureMir body && !hasCfgBackedge body) := by
  rw [← checkBodyFragment_pureBoundedLoop_eq_checkPureMir]
  simp only [checkBodyFragment]
  rw [congrArg body.basicBlocks.all (funext checkBlockFragment_pureLoopFree_eq_pureBoundedLoop)]

/-- `inferMinFragment body = .pureLoopFree` iff `checkPureMir body` and no index back-edge. -/
theorem inferMinFragment_eq_pureLoopFree_iff (body : CapturedMir) :
    inferMinFragment body = .pureLoopFree ↔
      checkPureMir body = true ∧ hasCfgBackedge body = false := by
  have h_iff := checkBodyFragment_iff_inferMinFragment_le .pureLoopFree body
  simp only [checkBodyFragment_pureLoopFree_eq, Bool.and_eq_true, Bool.not_eq_true'] at h_iff
  constructor
  · intro h
    apply h_iff.mpr
    rw [h]
    exact MirFragment.le_refl _
  · intro h
    exact MirFragment.le_antisymm (h_iff.mp h) (MirFragment.bot_le _)

/--
**Exact characterization of `.pureBoundedLoop`**:
`inferMinFragment body = .pureBoundedLoop` iff `checkPureMir body = true` and
`hasCfgBackedge body = true`.
-/
theorem inferMinFragment_eq_pureBoundedLoop_iff (body : CapturedMir) :
    inferMinFragment body = .pureBoundedLoop ↔
      checkPureMir body = true ∧ hasCfgBackedge body = true := by
  constructor
  · intro h
    have h_le : inferMinFragment body ≤ .pureBoundedLoop := by
      rw [h]; exact MirFragment.le_refl _
    have h_pure : checkPureMir body = true :=
      (inferMinFragment_le_pureBoundedLoop_iff_checkPureMir body).mp h_le
    cases h_be : hasCfgBackedge body
    · have h_plf : inferMinFragment body = .pureLoopFree :=
        (inferMinFragment_eq_pureLoopFree_iff body).mpr ⟨h_pure, h_be⟩
      rw [h] at h_plf
      cases h_plf
    · exact ⟨h_pure, rfl⟩
  · rintro ⟨h_pure, h_be⟩
    have h_le : inferMinFragment body ≤ .pureBoundedLoop :=
      (inferMinFragment_le_pureBoundedLoop_iff_checkPureMir body).mpr h_pure
    have h_not_plf : inferMinFragment body ≠ .pureLoopFree := by
      intro h_eq
      have h_be_false := ((inferMinFragment_eq_pureLoopFree_iff body).mp h_eq).2
      rw [h_be] at h_be_false
      cases h_be_false
    generalize inferMinFragment body = m at h_le h_not_plf
    cases m <;> first | rfl | exact absurd rfl h_not_plf | exact absurd h_le (by decide)

end Anneal.MirFragmentPrototype
