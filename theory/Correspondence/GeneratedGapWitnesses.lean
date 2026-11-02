import Correspondence.Framework
import Correspondence.DialectInterface
import Correspondence.GeneratedGaps

/-!
# `Correspondence.GeneratedGapWitnesses` — Self-Invalidating Kernel Divergence Witnesses

Implements the two-way non-correspondence ratchet:

Every single entry in `theory/Correspondence/correspondence_gaps.toml` MUST have
a kernel-checked `by decide` theorem proving `VerifiedDivergenceWitness`. The
moment the underlying bug in Anneal is fixed so that Anneal and MiniRust agree,
`by decide` deterministically fails to compile until the stale gap entry is
removed from `correspondence_gaps.toml`.
-/

namespace Correspondence

/-! ## 1. Individual Mandatory Divergence Witnesses (`by decide`) -/

/-- `GAP-MR-0001` (`anneal_soundness_bug`, `L4_TreeBorrows`):
    `BorrowKind.shared` over `UnsafeCell` freezes permission in Anneal (`ub`) while
    MiniRust permits interior-mutable write (`normalUnit`). -/
theorem witness_GAP_MR_0001 :
    VerifiedDivergenceWitness
      (evalAnnealV2026_06_01 .sharedUnsafeCellWrite defaultFixtureState)
      (evalMiniRustSnapshot .S2026_05_Matched .sharedUnsafeCellWrite)
      .ub
      .normalUnit := by
  decide

/-- `GAP-MR-0002` (`anneal_false_positive_ub`, `L2_BytesAndLayout`):
    Union cross-variant write followed by read faults as `ub` in Anneal while
    stepping cleanly (`normalUnit`) in MiniRust. -/
theorem witness_GAP_MR_0002 :
    VerifiedDivergenceWitness
      (evalAnnealV2026_06_01 .unionVariantWriteRead defaultFixtureState)
      (evalMiniRustSnapshot .S2026_05_Matched .unionVariantWriteRead)
      .ub
      .normalUnit := by
  decide

/-- `GAP-MR-0003` (`anneal_false_positive_ub`, `L3_PlacesAndBasicMem`):
    Dynamic array index borrow after `StorageDead` of temporary index local
    faults as `ub` in Anneal while stepping cleanly (`normalUnit`) in MiniRust. -/
theorem witness_GAP_MR_0003 :
    VerifiedDivergenceWitness
      (evalAnnealV2026_06_01 .dynamicArrayIndexBorrow defaultFixtureState)
      (evalMiniRustSnapshot .S2026_05_Matched .dynamicArrayIndexBorrow)
      .ub
      .normalUnit := by
  decide

/-- `GAP-MR-0004` (`anneal_unmodeled_feature`, `L1_Scalars`):
    `core::intrinsics::exact_div` halts as `.unsupported` in Anneal while
    evaluating inline (`normalUnit`) in MiniRust. -/
theorem witness_GAP_MR_0004 :
    VerifiedDivergenceWitness
      (evalAnnealV2026_06_01 .exactDivIntrinsicCall defaultFixtureState)
      (evalMiniRustSnapshot .S2026_05_Matched .exactDivIntrinsicCall)
      .unsupported
      .normalUnit := by
  decide

/-- `GAP-EPOCH-0001` (`intentional_epoch_divergence`, `L4_TreeBorrows`):
    Agrees on `S2026_05_Matched` (`ub = ub`), while diverging as documented on
    `S2026_07_BleedingEdge` (`ub` vs. `normalUnit`). -/
theorem witness_GAP_EPOCH_0001 :
    evalAnnealV2026_06_01 .reservedImEpochTransition defaultFixtureState =
      evalMiniRustSnapshot .S2026_05_Matched .reservedImEpochTransition ∧
    VerifiedDivergenceWitness
      (evalAnnealV2026_06_01 .reservedImEpochTransition defaultFixtureState)
      (evalMiniRustSnapshot .S2026_07_BleedingEdge .reservedImEpochTransition)
      .ub
      .normalUnit := by
  decide

/-! ## 2. Universal Guarded Agreement Theorem Across All Fixtures & Snapshots -/

/--
Outside the active gaps for `(V2026_06_01, snap)`, Anneal `V2026_06_01` and
MiniRust snapshot `snap` produce **100% identical verdicts** on every fixture,
across BOTH `S2026_05_Matched` and `S2026_07_BleedingEdge`!
-/
theorem all_non_gap_fixtures_agree_exact
    (snap : MiniRustSnap) (prog : FixtureProg)
    (h_no_gap :
      hitsAnyGap
        (activeBugGaps .V2026_06_01 snap ++ activeEpochDivergences .V2026_06_01 snap)
        defaultFixtureState
        prog = false) :
    evalAnnealV2026_06_01 prog defaultFixtureState = evalMiniRustSnapshot snap prog := by
  cases snap <;> cases prog <;> revert h_no_gap <;> decide

end Correspondence
