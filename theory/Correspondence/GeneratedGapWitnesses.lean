import Correspondence.Framework
import Correspondence.DialectInterface
import Correspondence.GeneratedGaps

/-!
# `Correspondence.GeneratedGapWitnesses` — Kernel Divergence & Remediation Witnesses

Implements the two-way non-correspondence and remediation ratchet:

- Every open or active entry in `theory/Correspondence/correspondence_gaps.toml`
  carries a kernel-checked `by decide` theorem proving `VerifiedDivergenceWitness`.
- Every closed remediated entry (`status = "closed"`) carries a kernel-checked
  `by decide` theorem proving `VerifiedRemediationWitness`, certifying that Anneal
  and MiniRust now agree on the remediated verdict.
-/

namespace Correspondence

/--
Decidable predicate asserting that Anneal and MiniRust both evaluate to the
remediated `expectedVerdict` and agree with each other.
-/
@[reducible]
def VerifiedRemediationWitness (annealEval minirustEval expectedVerdict : Verdict) : Prop :=
  annealEval = expectedVerdict ∧ minirustEval = expectedVerdict ∧ annealEval = minirustEval

instance instDecidableVerifiedRemediationWitness
    (a m ev : Verdict) : Decidable (VerifiedRemediationWitness a m ev) :=
  inferInstanceAs (Decidable (a = ev ∧ m = ev ∧ a = m))

/-! ## 1. Individual Mandatory Remediation & Divergence Witnesses (`by decide`) -/

/-- `GAP-MR-0001` (`anneal_soundness_bug`, `L4_TreeBorrows`, `status = "closed"`):
    `BorrowKind.shared` over `UnsafeCell` initializes `TreeBorrowPerm.reserved` in Anneal
    so both Anneal and MiniRust permit interior-mutable write (`normalUnit`). -/
theorem witness_GAP_MR_0001 :
    VerifiedRemediationWitness
      (evalAnnealV2026_06_01 .sharedUnsafeCellWrite defaultFixtureState)
      (evalMiniRustSnapshot .S2026_05_Matched .sharedUnsafeCellWrite)
      .normalUnit := by
  decide

/-- `GAP-MR-0002` (`anneal_false_positive_ub`, `L2_BytesAndLayout`, `status = "closed"`):
    Union cross-variant write followed by read steps cleanly (`normalUnit`) in both
    Anneal and MiniRust. -/
theorem witness_GAP_MR_0002 :
    VerifiedRemediationWitness
      (evalAnnealV2026_06_01 .unionVariantWriteRead defaultFixtureState)
      (evalMiniRustSnapshot .S2026_05_Matched .unionVariantWriteRead)
      .normalUnit := by
  decide

/-- `GAP-MR-0003` (`anneal_false_positive_ub`, `L3_PlacesAndBasicMem`, `status = "closed"`):
    Dynamic array index borrow resolves `.index` at borrow creation time so dereferencing
    after `StorageDead` of the temporary index local steps cleanly (`normalUnit`) in both
    Anneal and MiniRust. -/
theorem witness_GAP_MR_0003 :
    VerifiedRemediationWitness
      (evalAnnealV2026_06_01 .dynamicArrayIndexBorrow defaultFixtureState)
      (evalMiniRustSnapshot .S2026_05_Matched .dynamicArrayIndexBorrow)
      .normalUnit := by
  decide

/-- `GAP-MR-0004` (`anneal_unmodeled_feature`, `L1_Scalars`, `status = "closed"`):
    `core::intrinsics::exact_div` evaluates inline via `evalExactDiv` (`normalUnit`) in both
    Anneal and MiniRust. -/
theorem witness_GAP_MR_0004 :
    VerifiedRemediationWitness
      (evalAnnealV2026_06_01 .exactDivIntrinsicCall defaultFixtureState)
      (evalMiniRustSnapshot .S2026_05_Matched .exactDivIntrinsicCall)
      .normalUnit := by
  decide

/-- `GAP-EPOCH-0001` (`intentional_epoch_divergence`, `L4_TreeBorrows`, `status = "active"`):
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

/-- `GAP-EPOCH-0002` (`intentional_epoch_divergence`, `L4_TreeBorrows`):
    `V2026_08_01` agrees unconditionally on `S2026_07_BleedingEdge` (`normalUnit = normalUnit`),
    while diverging as documented against historical snapshot `S2026_05_Matched` (`normalUnit` vs. `ub`). -/
theorem witness_GAP_EPOCH_0002 :
    evalAnnealV2026_08_01 .reservedImEpochTransition defaultFixtureState =
      evalMiniRustSnapshot .S2026_07_BleedingEdge .reservedImEpochTransition ∧
    VerifiedDivergenceWitness
      (evalAnnealV2026_08_01 .reservedImEpochTransition defaultFixtureState)
      (evalMiniRustSnapshot .S2026_05_Matched .reservedImEpochTransition)
      .normalUnit
      .ub := by
  decide

/-! ## 2. Universal Unconditional Matched Agreement & Guarded Multi-Snapshot Agreement -/

/--
On `S2026_05_Matched`, Anneal `V2026_06_01` and MiniRust `S2026_05_Matched` produce
**100% identical verdicts unconditionally** across EVERY `prog : FixtureProg`!
-/
theorem all_matched_fixtures_agree_unconditionally (prog : FixtureProg) :
    evalAnnealV2026_06_01 prog defaultFixtureState =
      evalMiniRustSnapshot .S2026_05_Matched prog := by
  cases prog <;> decide

/--
Outside the active gaps for `(V2026_06_01, snap)` (which is `[]` on `S2026_05_Matched`
and `[.GAP_EPOCH_0001]` on `S2026_07_BleedingEdge`), Anneal `V2026_06_01` and
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

/--
Against `S2026_07_BleedingEdge`, Anneal `V2026_08_01` agrees **unconditionally**
on **100% of fixtures** (`L1`–`L6`, including all 4 closed `GAP-MR-*` fixtures and
`.reservedImEpochTransition`), with zero active bug gaps and zero epoch divergences!
-/
theorem all_v2026_08_01_s2026_07_fixtures_agree_unconditional
    (prog : FixtureProg) :
    evalAnnealV2026_08_01 prog defaultFixtureState =
      evalMiniRustSnapshot .S2026_07_BleedingEdge prog := by
  cases prog <;> decide

/--
Outside the active gaps for `(V2026_08_01, snap)` (which is `[]` on `S2026_07_BleedingEdge`
and `[.GAP_EPOCH_0002]` on `S2026_05_Matched`), Anneal `V2026_08_01` and MiniRust
snapshot `snap` produce **100% identical verdicts** on every fixture!
-/
theorem all_v2026_08_01_non_gap_fixtures_agree_exact
    (snap : MiniRustSnap) (prog : FixtureProg)
    (h_no_gap :
      hitsAnyGap
        (activeBugGaps .V2026_08_01 snap ++ activeEpochDivergences .V2026_08_01 snap)
        defaultFixtureState
        prog = false) :
    evalAnnealV2026_08_01 prog defaultFixtureState = evalMiniRustSnapshot snap prog := by
  cases snap <;> cases prog <;> revert h_no_gap <;> decide

end Correspondence
