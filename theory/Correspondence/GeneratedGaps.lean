import Correspondence.Framework
import Correspondence.DialectInterface

/-!
# `Correspondence.GeneratedGaps` — Schema-Derived Gap Registry & Non-Vacuity Proofs

Mechanically reflects `theory/Correspondence/correspondence_gaps.toml` and
`theory/Correspondence/correspondence_matrix.toml` into kernel-decidable Lean 4
definitions and proves non-vacuity (`allCanonicalFixturesAvoidGaps`) by kernel
`decide`.
-/

namespace Correspondence

/-! ## 1. Registered Gap Identifiers & Metadata -/

/-- Every entry declared in `theory/Correspondence/correspondence_gaps.toml`. -/
inductive GapId : Type where
  /-- `GAP-MR-0001`: `BorrowKind.shared` over `UnsafeCell` freezes permission (`L4_TreeBorrows`). -/
  | GAP_MR_0001
  /-- `GAP-MR-0002`: Union aggregate init / cross-variant field write UB (`L2_BytesAndLayout`). -/
  | GAP_MR_0002
  /-- `GAP-MR-0003`: Dynamic array index borrow after `StorageDead` of index temp (`L3_PlacesAndBasicMem`). -/
  | GAP_MR_0003
  /-- `GAP-MR-0004`: Unmodeled `core::intrinsics::exact_div` call (`L1_Scalars`). -/
  | GAP_MR_0004
  /-- `GAP-EPOCH-0001`: Post-2026-05 `Reserved` interior-mutability read relaxation (`L4_TreeBorrows`). -/
  | GAP_EPOCH_0001
  /-- `GAP-EPOCH-0002`: `V2026_08_01` protected mutable reborrow initial write vs. `S2026_05_Matched` read (`L4_TreeBorrows`). -/
  | GAP_EPOCH_0002
  deriving DecidableEq, Repr

/-- Complete list of all registered gap IDs. -/
@[reducible]
def allGapIds : List GapId :=
  [.GAP_MR_0001, .GAP_MR_0002, .GAP_MR_0003, .GAP_MR_0004, .GAP_EPOCH_0001, .GAP_EPOCH_0002]

/-- Formal 4-way taxonomy class for each `GapId`. -/
@[reducible]
def gapKind : GapId → GapKind
  | .GAP_MR_0001 => .anneal_soundness_bug
  | .GAP_MR_0002 => .anneal_false_positive_ub
  | .GAP_MR_0003 => .anneal_false_positive_ub
  | .GAP_MR_0004 => .anneal_unmodeled_feature
  | .GAP_EPOCH_0001 => .intentional_epoch_divergence
  | .GAP_EPOCH_0002 => .intentional_epoch_divergence

/-- Semantic slice owning each `GapId`. -/
@[reducible]
def gapLayer : GapId → SemanticLayer
  | .GAP_MR_0001 => .L4_TreeBorrows
  | .GAP_MR_0002 => .L2_BytesAndLayout
  | .GAP_MR_0003 => .L3_PlacesAndBasicMem
  | .GAP_MR_0004 => .L1_Scalars
  | .GAP_EPOCH_0001 => .L4_TreeBorrows
  | .GAP_EPOCH_0002 => .L4_TreeBorrows

/-- Cross-reference into `tests/miri-diff/manifest.toml` when applicable. -/
@[reducible]
def gapMiriDiffCrossRef : GapId → Option String
  | .GAP_MR_0001 => some "pass_tb_unsafe_cell_shared_mutation"
  | .GAP_MR_0002 => some "pass_uninit_union_write_then_read"
  | .GAP_MR_0003 => some "pass_ref_array_elem_temp_index"
  | .GAP_MR_0004 => some "pass_exact_div_valid"
  | .GAP_EPOCH_0001 => none
  | .GAP_EPOCH_0002 => none

/-! ## 2. Scoped Active Gap Queries Across `(AnnealVer × MiniRustSnap)` -/

/-- Whether gap `id` is currently open (`false` when `status == "closed"`, `true` when `status == "open"` or `"active"`). -/
@[reducible]
def gapIsOpen : GapId → Bool
  | .GAP_MR_0001 => false
  | .GAP_MR_0002 => false
  | .GAP_MR_0003 => false
  | .GAP_MR_0004 => false
  | .GAP_EPOCH_0001 => true
  | .GAP_EPOCH_0002 => true

/-- Whether gap `id` applies to `(ver, snap)`. -/
@[reducible]
def gapAppliesTo (id : GapId) (ver : AnnealVer) (snap : MiniRustSnap) : Bool :=
  match ver, id with
  | .V2026_06_01, .GAP_MR_0001 => true
  | .V2026_06_01, .GAP_MR_0002 => true
  | .V2026_06_01, .GAP_MR_0003 => true
  | .V2026_06_01, .GAP_MR_0004 => true
  | .V2026_06_01, .GAP_EPOCH_0001 =>
    match snap with
    | .S2026_05_Matched => false
    | .S2026_07_BleedingEdge => true
  | .V2026_06_01, .GAP_EPOCH_0002 => false
  | .V2026_08_01, .GAP_EPOCH_0002 =>
    match snap with
    | .S2026_05_Matched => true
    | .S2026_07_BleedingEdge => false
  | .V2026_08_01, _ => false
  | .V2026_12_01, _ => false

/-- Whether gap `g` is active for `(ver, snap)`. -/
@[reducible]
def isGapActive (ver : AnnealVer) (snap : MiniRustSnap) (g : GapId) : Bool :=
  gapIsOpen g && gapAppliesTo g ver snap

/-- All open bug/feature gaps (`gapIsOpen id && (gapKind id).isAnnealBug`) active for `(ver, snap)`. -/
@[reducible]
def activeBugGaps (ver : AnnealVer) (snap : MiniRustSnap) : List GapId :=
  allGapIds.filter (fun id => gapIsOpen id && (gapKind id).isAnnealBug && gapAppliesTo id ver snap)

/-- All closed remediated bug/feature gaps (`!gapIsOpen id && (gapKind id).isAnnealBug`) for `(ver, snap)`. -/
@[reducible]
def closedBugGaps (ver : AnnealVer) (snap : MiniRustSnap) : List GapId :=
  allGapIds.filter (fun id => !gapIsOpen id && (gapKind id).isAnnealBug && gapAppliesTo id ver snap)

/-- All intentional epoch divergences (`isEpochDivergence = true`) active for `(ver, snap)`. -/
@[reducible]
def activeEpochDivergences (ver : AnnealVer) (snap : MiniRustSnap) : List GapId :=
  allGapIds.filter (fun g => isGapActive ver snap g && (gapKind g).isEpochDivergence)

/-! ## 3. Decidable Guard Predicates & Canonical Non-Vacuity Theorem -/

/-- Decidable guard predicate testing whether `(prog, st)` triggers gap `g`. -/
@[reducible]
def hitsGap (g : GapId) (st : FixtureState) (prog : FixtureProg) : Bool :=
  let _ := st
  match g, prog with
  | .GAP_MR_0001, .sharedUnsafeCellWrite => true
  | .GAP_MR_0002, .unionVariantWriteRead => true
  | .GAP_MR_0003, .dynamicArrayIndexBorrow => true
  | .GAP_MR_0004, .exactDivIntrinsicCall => true
  | .GAP_EPOCH_0001, .reservedImEpochTransition => true
  | .GAP_EPOCH_0002, .reservedImEpochTransition => true
  | _, _ => false

/-- Combined guard predicate testing whether any gap in `gaps` fires on `(st, prog)`. -/
@[reducible]
def hitsAnyGap (gaps : List GapId) (st : FixtureState) (prog : FixtureProg) : Bool :=
  gaps.any (fun g => hitsGap g st prog)

/-- Suite of canonical well-behaved baseline fixtures across all layers `L1`–`L4`. -/
@[reducible]
def canonicalBaselineFixtures : List FixtureProg :=
  [ .canonicalSafeScalarAdd
  , .canonicalSafeByteRoundTrip
  , .canonicalSafeLocalWriteRead
  , .canonicalSafeTreeBorrowMut
  ]

/-- Decidable check verifying that gap `g` never fires on any canonical baseline fixture. -/
@[reducible]
def canonicalFixturesAvoidGap (g : GapId) : Bool :=
  canonicalBaselineFixtures.all (fun prog => !hitsGap g defaultFixtureState prog)

/-- Decidable check verifying that NO registered gap fires on ANY canonical baseline fixture. -/
@[reducible]
def allCanonicalFixturesAvoidAllGaps : Bool :=
  allGapIds.all canonicalFixturesAvoidGap

/--
**Non-Vacuity Theorem (`allCanonicalFixturesAvoidGaps`)**:
Proves by kernel reduction (`decide`) that zero gap guards fire on any canonical
baseline program — preventing an overly broad guard predicate from silently
hollowing out universal correspondence theorems.
-/
theorem allCanonicalFixturesAvoidGaps :
    allCanonicalFixturesAvoidAllGaps = true := by
  decide

/--
Against `S2026_05_Matched`, `V2026_06_01` has ZERO epoch divergences (`[]`),
 whereas against `S2026_07_BleedingEdge` it has exactly `[.GAP_EPOCH_0001]`.
-/
theorem matched_snapshot_has_zero_epoch_divergences :
    activeEpochDivergences .V2026_06_01 .S2026_05_Matched = [] ∧
    activeEpochDivergences .V2026_06_01 .S2026_07_BleedingEdge = [.GAP_EPOCH_0001] := by
  decide

/--
Monotonic ratchet ceiling check: active open bugs on `V2026_06_01` have been
ratcheted down to `0`, with all `4` historical bug gaps closed.
-/
theorem active_bug_count_within_ratchet_ceiling :
    activeBugGaps .V2026_06_01 .S2026_05_Matched = [] ∧
    (activeBugGaps .V2026_06_01 .S2026_05_Matched).length ≤ 0 ∧
    (closedBugGaps .V2026_06_01 .S2026_05_Matched).length = 4 := by
  decide

end Correspondence
