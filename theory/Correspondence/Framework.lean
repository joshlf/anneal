import Trusted.Refinement
import MiniRust.LibSpecr

/-!
# `Correspondence.Framework` — Multi-Version Refinement & Non-Correspondence Taxonomy

Connects MiniRust's dual-mode computation trees (`MiniRust.LibSpecr.NdComp`) to
Anneal's Layer 1A Smyth refinement lattice (`Trusted.Refinement.Partial`), and
defines:

1. The four mutually exclusive non-correspondence classes (`GapKind`):
   - `anneal_soundness_bug`
   - `anneal_false_positive_ub`
   - `anneal_unmodeled_feature`
   - `intentional_epoch_divergence`
2. Version and snapshot coordinates (`AnnealVer`, `MiniRustSnap`, `SemanticLayer`,
   `ExpectedTier`) across the `(AnnealVersion × MiniRustSnapshot × Layer)` matrix.
3. Observable execution verdicts (`Verdict`) shared across kernel-checked
   divergence witnesses (`VerifiedDivergenceWitness`).
-/

namespace Correspondence

open Trusted.Refinement
open MiniRust.LibSpecr

/-! ## 1. Version, Snapshot, Layer, and Formal Tier Identifiers -/

/-- Versioned Anneal MIR dialects under `Trusted.Rustc.V*`. -/
inductive AnnealVer : Type where
  /-- Pinned `rustc 1.98.0-nightly (14210df0e 2026-05-31)` MIR model. -/
  | V2026_06_01
  /-- Planned follow-up MIR model absorbing post-2026-05 Tree Borrows relaxations. -/
  | V2026_12_01
  deriving DecidableEq, BEq, Repr

/-- Mechanically ingested upstream MiniRust snapshots. -/
inductive MiniRustSnap : Type where
  /-- Upstream MiniRust snapshot epoch-matched to `V2026_06_01` (`2026-05-31`). -/
  | S2026_05_Matched
  /-- Upstream MiniRust bleeding-edge snapshot tracking `master` HEAD. -/
  | S2026_07_BleedingEdge
  deriving DecidableEq, BEq, Repr

/-- Horizontal semantic slices of the correspondence proof architecture. -/
inductive SemanticLayer : Type where
  | L1_Scalars
  | L2_BytesAndLayout
  | L3_PlacesAndBasicMem
  | L4_TreeBorrows
  | L5_ControlAndCalls
  | L6_WholeMachine
  deriving DecidableEq, BEq, Repr

/-- Formal correspondence expectation tiers in `correspondence_matrix.toml`. -/
inductive ExpectedTier : Type where
  /-- Zero bug gaps and zero epoch divergences permitted. -/
  | ExactUnconditional
  /-- Zero bug gaps; only explicitly cited `intentional_epoch_divergence` entries permitted. -/
  | EpochDeltaOnly
  /-- Bounded bug ratchet (`activeBugGaps.length ≤ maxOpenBugs`) with kernel witnesses. -/
  | GuardedRatchet
  deriving DecidableEq, BEq, Repr

/-! ## 2. Four-Way Formal Non-Correspondence Taxonomy -/

/--
Mutually exclusive classification of every documented discrepancy between an
Anneal MIR dialect and an upstream MiniRust snapshot.
-/
inductive GapKind : Type where
  /-- Anneal admits normal/panic execution where MiniRust raises UB or computes a distinct value. -/
  | anneal_soundness_bug
  /-- Anneal conservatively emits `.fail .ub` (`Partial.ub`) where MiniRust steps cleanly. -/
  | anneal_false_positive_ub
  /-- Anneal emits `.fail .unsupported` or external call for an unmodeled feature. -/
  | anneal_unmodeled_feature
  /-- Intentional semantic evolution between pinned `rustc` and a newer MiniRust snapshot. -/
  | intentional_epoch_divergence
  deriving DecidableEq, Repr

namespace GapKind

/-- Whether this class counts against the open Anneal bug ceiling (`max_open_bugs`). -/
@[reducible]
def isBug : GapKind → Bool
  | .anneal_soundness_bug => true
  | .anneal_false_positive_ub => true
  | .anneal_unmodeled_feature => true
  | .intentional_epoch_divergence => false

/-- Alias for `GapKind.isBug` used by generated gap ratchet queries. -/
@[reducible]
def isAnnealBug : GapKind → Bool :=
  isBug

/-- Whether this class blocks a declaration from carrying `@[vetted]`. -/
@[reducible]
def blocksVetted : GapKind → Bool
  | .anneal_soundness_bug => true
  | _ => false

/-- Whether this class represents intentional cross-epoch version skew. -/
@[reducible]
def isEpochDivergence : GapKind → Bool
  | .intentional_epoch_divergence => true
  | _ => false

end GapKind

/-! ## 3. Observable Verdict Domain & Kernel Divergence Predicate -/

/-- Normalized observable verdict used in cross-semantics equivalence & witness checks. -/
inductive Verdict : Type where
  | normalUnit
  | normalScalar (val : Nat)
  | panic
  | ub
  | unsupported
  deriving DecidableEq, Repr

/-- Project a concrete `Verdict` into Layer 1A's `Partial (BehaviorSet Verdict)` lattice. -/
def Verdict.toPartial (v : Verdict) : Partial (BehaviorSet Verdict) :=
  match v with
  | .ub => Partial.ub
  | .unsupported => Partial.ub
  | other => Partial.pure (fun out => out = other)

/--
Both `.ub` and `.unsupported` map to top (`Partial.ub`) in Layer 1A's Smyth order,
so any MiniRust computation `c` refines Anneal whenever Anneal produces `.ub` or
`.unsupported`.
-/
theorem minirust_refines_verdict_top
    (c : NdComp Verdict) (v : Verdict)
    (h_top : v = .ub ∨ v = .unsupported) :
    NdComp.toPartialBehavior c ≤ v.toPartial := by
  cases h_top with
  | inl hub =>
    subst hub
    exact NdComp.top_refines_false_positive_ub c
  | inr hunsup =>
    subst hunsup
    exact NdComp.top_refines_unsupported c

/--
Decidable predicate asserting that Anneal and MiniRust produce the exact recorded
pair of diverging verdicts `(expectedAnneal, expectedMiniRust)` with
`expectedAnneal ≠ expectedMiniRust`.
-/
@[reducible]
def VerifiedDivergenceWitness
    (actualAnneal actualMiniRust expectedAnneal expectedMiniRust : Verdict) : Prop :=
  actualAnneal = expectedAnneal ∧
  actualMiniRust = expectedMiniRust ∧
  expectedAnneal ≠ expectedMiniRust

instance instDecidableVerifiedDivergenceWitness
    (a m ea em : Verdict) : Decidable (VerifiedDivergenceWitness a m ea em) :=
  inferInstanceAs (Decidable (a = ea ∧ m = em ∧ ea ≠ em))

/--
If two verdicts agree (`actualAnneal = actualMiniRust`), no `VerifiedDivergenceWitness`
can ever hold for them — guaranteeing that fixing an Anneal bug immediately invalidates
its stale witness theorem under `by decide`.
-/
theorem witness_invalidated_when_verdicts_agree
    (v expectedAnneal expectedMiniRust : Verdict)
    (h_wit : VerifiedDivergenceWitness v v expectedAnneal expectedMiniRust) :
    False := by
  rcases h_wit with ⟨ha, hm, hne⟩
  rw [← ha, ← hm] at hne
  exact hne rfl

end Correspondence
