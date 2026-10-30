# Untrusted Lean verification library (`theory/`)

This directory holds the `Anneal.*` Lean library: all derived equational laws,
coinductive refinement relations, temporal modalities, observation-projection
pass frameworks, certificate checkers, open-effect Dijkstra predicate
transformers, and separation-logic framing combinators built on top of
[`trusted/lean/`](../trusted/lean/README.md) and Lean 4's `Init` and `Std`
standard libraries ([#100](https://github.com/joshlf/anneal/issues/100),
[#99](https://github.com/joshlf/anneal/issues/99),
[#103](https://github.com/joshlf/anneal/issues/103)).

## Why `theory/` is untrusted ("Lean said it was fine, so it is fine")

Nothing in `theory/` belongs to Anneal's Trusted Computing Base (TCB):

1. **Used only in proof terms (`ci.value?`), never in theorem statements (`ci.type`):**
   [`trusted/audit/`](../trusted/audit/README.md) enforces that the theorem
   statement `ci.type` of every verification certificate (`VerificationResult`,
   `StatefulVerificationResult`, `ModularVerificationResult`,
   `TraceVerificationResult`, `TotalVerificationResult`) has zero transitive
   dependencies on `Anneal.*`. Definitions in `theory/` appear only inside proof
   witnesses (`ci.value?`).
2. **Checked by the Lean kernel under strict zero-custom-axiom containment:**
   Every module in `theory/` compiles under the strict zero-custom-axiom policy
   using only Lean's standard axioms (`{propext, Quot.sound, Classical.choice}`)
   with zero `sorryAx`, `unsafe`, `partial`, or compiler overrides. A bug in
   `theory/` can cause a proof to fail typechecking, but it can never allow a
   false verification certificate to pass.

## Standard-library foundations

Rather than reinventing core algebra, monads, fixpoints, or predicate-transformer
interfaces from `Init.Core`, `theory/` builds directly on Lean 4.34.1's `Init`
and `Std`:

- **Order algebra (`Std.IsPreorder`, `Std.IsPartialOrder`):** Refinement lattices
  (`BehaviorSet`, `Partial`, `WeakRef`, `TotalWeakRef`, `WeakObsRef`) instantiate
  standard `LE` and `Std` order typeclasses directly.
- **Lattice-theoretic fixpoints (`coinductive_fixpoint`, `inductive_fixpoint`):**
  Coinductive relations and greatest/least predicate transformers (`StrongBisim`,
  `Eutt`, `WeakRef`, `TotalWeakRef`, `WeakSim`, `WeakCSim`, `CoAlways`,
  `Eventually`, `InfinitelyOften`, `FollowsStream`, `DWLP`, `DWP`) use Lean's
  `Order.PartialFixpoint` machinery rather than hand-rolled dual inductive
  encodings.
- **Monad laws and `Std.Do` Hoare triples (`Monad`, `LawfulMonad`, `Std.Do.WP`, `Std.Do.WPMonad`, `Std.Do.Triple`):**
  `ITree E` instantiates `LawfulMonad`, enabling `do`-notation and `simp` monad
  normalization; `DWLP` instantiates `Std.Do.WP (ITree E) .pure` and
  `Std.Do.WPMonad (ITree E) .pure`, connecting `⦃P⦄ t ⦃Q⦄` Hoare triples
  directly to `DWLP` adequacy (`Triple.toDWLP`).
- **List combinators, well-founded recursion, and arithmetic automation (`List.filterMap`, `List.IsPrefix`, `Acc`, `omega`, `simp`):**
  Observation projection filters raw `List (Event E)` traces with
  `List.filterMap` and prefix closure `<+:` (`List.IsPrefix`); total loop rules
  use Lean's `Acc r init`; arithmetic and byte-offset proofs discharge via
  `omega` and `simp` without a custom `LeanCompat` layer.

## Module architecture under `theory/Anneal/`

The library progresses from abstract refinement and open interaction trees to
concrete Rust MIR verification across 15 modules:

- **Y-diagram composition, partial behaviors, and pass contracts (`Anneal/Refinement.lean`, Layer 1A):**
  `GuardedRefines.trans` (`y_diagram_sound`, `anneal_is_correct`),
  `VerifierPass` / `CompilerPass` / `BugFinderPass` / `SanitizerPass` /
  `ExactPass` pass specializations, query-indexed `Language` composition
  (`Compiles.comp`, `Abstracts.comp`, `y_diagram_language_sound`),
  `Partial.map_monotone`, and `BehaviorSet.map_monotone`
  ([#100](https://github.com/joshlf/anneal/issues/100) §3–§4).
- **Open effect algebra and constructive non-vacuity (`Anneal/Effect.lean`):**
  Identity, composition, and `SumE` lifting laws for `Subeffect` and
  `LawfulSubeffect`, natural transformations (`EffectHom`, `LawfulEffectHom`),
  and typeclass-driven `InhabitedDemonic` synthesis across arbitrary `SumE`
  signatures (`FailE`, `ObsE`, `PickE`, `WitnessE`, `CallE`, `StateE`).
- **Coinductive interaction-tree equational theory, Smyth tree refinement, and temporal modalities (`Anneal/ITree.lean`):**
  - Strong bisimulation (`StrongBisim`) via `coinductive_fixpoint` with
    quotient-soundness extensionality (`StrongBisim t u ↔ t = u`),
    `LawfulMonad (ITree E)`, and the unfolding/congruence laws for `iter`,
    `interp`, and `interpState`.
  - Equivalence up to finite silent `.tau` steps (`Eutt`: reflexivity, symmetry,
    transitivity, `bind` and `interp` congruence, and `Eutt.toWeakRef`).
  - The 2×2 coinductive refinement lattice: Smyth-oriented partial-correctness
    refinement (`WeakRef`, placing `ITree.fail` at `⊤` and `ITree.stuck` at `⊥`
    with `Std.IsPreorder`), termination-preserving refinement (`TotalWeakRef`),
    and explicit separation from naive similarity (`WeakSim`) and complete
    similarity (`WeakCSim`).
  - Prefix-preserving UB-closed trace sets (`UBClosedPrefixes`, modeling Vellvm
    `model_UB` and CompCert `Goes_wrong tr₀`), adequacy bridges
    (`WeakRef.toPartial_le`, `WeakRef.toPrefixPartial_le`,
    `WeakRef.ubClosedPrefixes_le`), foreign/ISA `BridgeContract` / `bridgeTree`
    refinement (`bridgeTree_refines_of_contract`,
    [#102](https://github.com/joshlf/anneal/issues/102)), and the Skolemized
    environment-strategy equivalence (`EnvStrategy`, `ReachesWithStrategy`,
    `reaches_iff_exists_strategy`).
  - Coinductive and mixed inductive-coinductive modalities beyond finite
    prefixes: `Productive`, `CoAlways` ($\Box P$), choice-aware `Eventually`
    ($\Diamond P$), Büchi `InfinitelyOften` ($\Box\Diamond P$), and
    `FollowsStream` connecting `ObsE` trees to `CoStream`.
- **`ITreeMachine` observation projections, CFG pass frameworks, and certificate checkers (`Anneal/Pass.lean`, Layer 1B & Layer 2):**
  `VerifiedVerifierChecker` / `VerifiedCompilerChecker` / `VerifiedExactChecker`
  validators, coalgebraic `ITreeMachine` with `List.filterMap`-based
  `EffectObs` / `ObsPrefix` / `UBClosedObsPrefixes` / `MachineSemantics` and
  depth-indexed `ITreeMachine.toLanguage` bridges, cross-effect `WeakObsRef`
  simulation yielding both `CompilerPass` and `Compiles`, `exactPass_of_eutt`,
  resolved-label `CFGSystem` (`PureJumpLaw`, `TargetLabelIndependenceLaw`,
  `PCDispatchLaw`, `eliminateForwarder_exactPass`), and `.tau`-erasing
  `TauCFGSystem` (`TauForwarderLaw`, `eliminateTauForwarder_eutt`,
  `eliminateTauForwarder_exactPass`)
  ([#99](https://github.com/joshlf/anneal/issues/99) §7–§9,
  [#100](https://github.com/joshlf/anneal/issues/100) §5–§6).
- **Open-effect Dijkstra predicate transformers and `Std.Do` integration (`Anneal/EffectWP.lean`, `Anneal/ITreeWP.lean`):**
  - `StateEffectWP S E` and pure `PureEffectWP E` (`S = PUnit`) with modular
    healthiness classes (`Conjunctive`, `ExcludedMiracle`, `Disjunctive`),
    `StateEffectWP.sum` preserving healthiness across `SumE E₁ E₂`,
    trace-accumulating `StateEffectWP.withTrace`, and concrete effect
    transformers (`failWP`, `obsIgnoreWP`, `obsAccumWP`, `pickWP`, `witnessWP`,
    `callContractWP`, `unconstrainedCallWP`, `stateEffectWP`).
  - Coinductive partial-correctness weakest liberal precondition (`DWLP`) and
    inductive total-correctness weakest precondition (`DWP`) via
    `coinductive_fixpoint` / `inductive_fixpoint`, loop rules
    (`DWLP.iter_invariant`, `DWP.iter_acc` over `Acc r init`, and
    `DWP.iter_measure`), computable fuel-bounded coalgebra stepping
    (`wpCoalBounded`, `dwp_cofix_of_wpCoalBounded`,
    `dwlp_cofix_of_wpCoalBounded`), semantic adequacy theorems (`DWLP.treeSafe`,
    `dwlp_pure_adequacy`, `dwlp_withTrace_adequacy`, `DWP.not_mayDiverge`,
    `dwp_pure_adequacy`), handler-linking theorems (`DWLP.interp`, `DWP.interp`,
    `DWLP.interpState`, `DWP.interpState`), and `Std.Do.WP` / `Std.Do.WPMonad` /
    `Triple.toDWLP`.
- **Scalars, memory, bit validity, unsafe obligations, and unified `PartialHeap` separation logic (`Anneal/Scalars.lean`, `Anneal/Memory.lean`, `Anneal/BitValidity.lean`, `Anneal/UnsafeObligations.lean`, `Anneal/SepLogic.lean`):**
  Fixed-width integer bounds (`Anneal/Scalars.lean`), abstract byte and Tree
  Borrows helpers (`Anneal/Memory.lean`), `ZerocopyTrait` layout certificate
  checkers (`checkUnaligned_sound`, `checkFromZeros_sound`,
  `checkFromBytes_sound`, `checkIntoBytes_sound` in `Anneal/BitValidity.lean`),
  raw-pointer alignment, provenance, and slice-splitting obligations
  (`Anneal/UnsafeObligations.lean`), and unified `PartialHeap` separation logic
  (`PartialHeap`, `SepProp`, `PointsToSep`, `BorrowTokenSep`,
  `LocalEffectFootprint`, `dwlp_frame_disjoint`, `dwp_frame_disjoint`, and
  `statefulVerificationResult_frame_disjoint` in `Anneal/SepLogic.lean`)
  ([#88](https://github.com/joshlf/anneal/issues/88),
  [#101](https://github.com/joshlf/anneal/issues/101)).
- **MIR predicate-transformer instantiation and horizontal caller–callee linking (`Anneal/Rustc/V2026_06_01/Lower.lean`):**
  Instantiations of `StateEffectWP` for `MirEffect` (`mirClosedWP`,
  `mirNoCallWP`, `mirDefaultWP`, `mirTraceWP`, `mirModularWP contract`),
  computable fuel-bounded stepping (`wpMirBounded`, `wpMirTraceBounded`,
  `wpMirTotalBounded`), adequacy bridges discharging all five trusted
  verification gates (`verifyMirByDWLP`, `verifyMirBounded`,
  `verifyStatefulMirByDWLP`, `verifyStatefulMirBounded`, `verifyTraceMirByDWLP`,
  `verifyTraceMirBounded`, `verifyTotalMirByDWP`, `verifyTotalMirBounded`,
  `verifyModularMirByDWLP`, `verifyModularMirBounded`,
  `mirBoolPredicateHolds_of_dwlp`, `mirBoolPredicateHolds_of_bounded`),
  program-to-program refinement and equivalence adequacy, and
  horizontal caller–callee linking via `ITree.interp` (`linkCalleeHandler`,
  `linkVerifiedMirCallee`).
- **Single-pass symbolic MIR evaluation and UB refutation (`Anneal/Rustc/V2026_06_01/SymbolicEval.lean`):**
  Fast continuation-based symbolic stepping over `V2026_06_01` `CapturedMir`,
  `#[spec]` `MirBoolPredicateHolds` discharge combinators, non-vacuity witness
  helpers, and bounded UB counterexample refutation (`¬ claim.holds`).
- **Plan-guided functional translation (`Anneal/FunctionalTranslation.lean`):**
  Spine-preserving symbolic values (`SymVal`, `zipSymVal`), forward/backward
  lenses for `&mut` references, input-indexed `TransPlan` / `SymPlan` CFG and
  `while`-loop translation, and pure-model relational equivalence bridges
  ([#109](https://github.com/joshlf/anneal/issues/109)).
