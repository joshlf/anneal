# Trusted Lean definitions (`trusted/lean/`)

This directory holds the `Trusted.*` Lean source root: the minimal set of
primitive semantic commitments and top-level claim gates required to state
verification certificates ([#100](https://github.com/joshlf/anneal/issues/100),
[#103](https://github.com/joshlf/anneal/issues/103)).

## What belongs in `trusted/lean/`

Only definitions that must appear in (or unfold inside) the **statement
(`ci.type`)** of a verification certificate belong here, built directly on Lean
4's `Init` and `Std` abstractions rather than duplicating standard algebra,
monads, or list operations:

- **`Trusted/Refinement.lean` (Layer 1A):** Refinement over standard `LE` (`≤`),
  `Std.IsPreorder`, and `Std.IsPartialOrder` (`Refines`, `Semantics`,
  downward-closed `Spec`, `Monotone`, `Spec.pullback`), canonical `BehaviorSet`
  predicates (`BehaviorSet.allSpec`, `BehaviorSet.forbidSpec`,
  `BehaviorSet.twoSafetySpec`), constructive Smyth `Partial` behaviors
  (`Partial.pure`, `Partial.ub`, `Partial.contract`, `Std.IsPartialOrder`),
  query-indexed `Language` contracts (`Language.WellFormedOn`,
  `Language.WellFormed`, `Language.ContractSpec`, `Compiles`, `Abstracts`), and
  `GuardedRefines` ([#100](https://github.com/joshlf/anneal/issues/100) §3–§4).
- **`Trusted/CoInd.lean` (Constructive Coinduction):** Indexed M-types
  (`CoInd A B` constructed via `PathTree` and `Quot` without `partial` or
  `unsafe`), `CoInd.cofix`, `CoInd.unfold_cofix`, `CoInd.ext`, and infinite
  streams (`CoStream`).
- **`Trusted/Effect.lean` (Open Effect Signatures):** The indexed interaction
  signature `Effect.{u}` (`I : Type u`, `O : I → Type u`), `Event E`,
  operational fault classification (`FaultEffect`), structural combinators
  (`EmptyE`, `SumE`, `Subeffect`, `LawfulSubeffect`), standard effect building
  blocks (`FailE`, `ObsE`, `PickE`/`DemonicE`, `WitnessE`/`AngelicE`, `CallE`,
  `StateE`), and constructive demonic non-vacuity (`InhabitedDemonic`).
- **`Trusted/ITree.lean` (Fundamental Coinductive Interaction Trees):**
  `ITreeF E R X` (`ret | tau | vis`), coinductive `ITree E R` (inheriting
  propositional extensionality from `CoInd.ext`), `Monad (ITree E)` enabling
  standard Lean `do`-notation and `>>=`, core combinators (`ITree.cofix`,
  `ITree.bind`, `ITree.iter`, `ITree.trigger`, `ITree.triggerSub`,
  `ITree.interp`, `ITree.interpState`, `ITree.spin`, `ITree.fail`, `ITree.emit`,
  `ITree.pick`, `ITree.stuck`, `ITree.witness`), trace reachability (`TauStar`,
  `Reaches`, `FaultNow`, `TreeSafe`), divergence predicates (`Diverges` defined
  via `coinductive_fixpoint` and `MayDiverge`), and Smyth `Partial` projections
  (`ITree.toPartial`, `ITree.toPrefixPartial`) placing undefined behavior at top
  (`defined := TreeSafe t`) and miraculous empty demonic choices at bottom.
- **`Trusted/Sequence.lean`:** Thin wrappers (`get?`, `set?`, `slice?`,
  `writeSlice?`) over Lean's standard `List` (`xs[idx]?`, `xs.set`, `xs.take`,
  `xs.drop`).
- **`Trusted/Rustc/V2026_06_01/Layout.lean` (re-exported by `Trusted/Layout.lean`):**
  Compiler layout and ABI types (`Size`, `Align`, `WrappingRange`,
  `PrimitiveKind`, `ScalarLayout`, `FieldsShape`, `VariantsShape`,
  `BackendRepr`, `TypeLayout`, `LayoutTable`, `AbiPassMode`, `ArgAbi`,
  `CallConv`, `FnAbi`) with derived `DecidableEq`/`Repr` instances and verbatim
  `rustc_abi` and Rust Reference citations
  ([#88](https://github.com/joshlf/anneal/issues/88)).
- **`Trusted/Rustc/V2026_06_01/MirAst/{Types,Places,Rvalues,Statements,Terminators,Body}.lean` (re-exported by `Trusted/MirAst.lean`):**
  Sharded `Runtime(PostCleanup)` MIR syntax (`Ty`, `Place`, `ProjectionElem`,
  `Operand`, `Rvalue`, `Statement`, `Terminator`, `CapturedAllocation`,
  `ContractRole`, and `CapturedMir`) backed by verbatim `rustc_middle::mir` and
  Rust Reference citations ([#99](https://github.com/joshlf/anneal/issues/99)).
- **`Trusted/Rustc/V2026_06_01/MirSemantics/{State,Scalars,Places,Statements,Terminators,Eval,Machine}.lean` (re-exported by `Trusted/MirSemantics.lean`):**
  Coalgebraic MIR operational semantics producing `ITree MirEffect MirOutcome`
  (`mirTree`, `mirStatefulTree`) over the open effect sum
  `MirEffect := SumE MirFailE (SumE MirObsE MirCallE)`. Unresolved external and
  FFI calls suspend on `MirCallE` carrying `(defPath, args, memory)` and receive
  `MirCallAns` carrying updated `Memory` (or unwind/abort), so external calls
  are impure and nondeterministic by default rather than pure mathematical
  functions. Unmodeled constructs emit `MirFailE` (`.unsupported`), keeping
  `TreeSafe` fail-closed ([#100](https://github.com/joshlf/anneal/issues/100),
  [#101](https://github.com/joshlf/anneal/issues/101)).
- **`Trusted/VerificationResult.lean`:** `ArtifactIdentity`,
  `MirBoolPredicateHolds`, and five top-level claim and certificate gates over
  `mirStatefulTree`:
  - `Claim` and `VerificationResult` (stateless value contracts),
  - `StatefulClaim` and `StatefulVerificationResult` (memory and Tree Borrows
    contracts),
  - `ModularClaim` and `ModularVerificationResult` (handler-interpreted external
    calls via `ExternalCallHandler` and `mirHandledTree`),
  - `TraceClaim` and `TraceVerificationResult` (explicit `MirObs` observation
    trace contracts), and
  - `TotalClaim` and `TotalVerificationResult` (divergence-forbidding total
    correctness requiring `¬ MayDiverge` and reachable normal return),
  alongside program-to-program behavioral refinement and equivalence gates
  (`RefinesStatefulMir`, `StatefulEquivVerificationResult`), non-vacuity
  precondition witnesses (`NonVacuousPre`, `NonVacuousStatefulPre`), and
  whole-crate verification rollup (`CrateVerificationEntry`, `CrateTheorem`).
- **`foundation-lock.json` and `locks/foundation-lock-v4.34.1.json`:**
  Cryptographic SHA-256 digests of the pinned Lean 4.34.1 toolchain binary and
  locked foundation artifacts verified by `trusted/audit/check_trusted.py`.

## Why equational theory and Dijkstra predicate transformers stay outside `trusted/lean/`

Every claim gate in `Trusted/VerificationResult.lean` states its `TreeSafe`
safety obligation and postcondition directly over `mirStatefulTree` (or
`mirHandledTree`) using only definitions in `trusted/lean/`.

Coinductive simulation and refinement relations (`StrongBisim`, `Eutt`,
`WeakRef`, `TotalWeakRef`), `LawfulMonad (ITree E)`, open-effect Dijkstra
predicate transformers (`StateEffectWP`, `EffectWP`, `DWLP`, `DWP`, and their
`Std.Do.WP` / `Std.Do.WPMonad` instances), computable fuel-bounded stepping
(`wpCoalBounded`, `wpMirBounded`), `ITreeMachine` observation projections and
CFG pass theorems (`CFGSystem`, `TauCFGSystem`), and separation-logic framing
(`SepLogic`) appear **only inside proof terms (`ci.value?`)**. They therefore
live entirely in [`theory/`](../../theory/README.md) outside the TCB.

## Authoring rules

1. Every module imports only `trusted/lean/` modules and the pinned Lean 4.34.1
   standard library (`Init.*`, `Std.*`), enforced by
   `trusted/audit/check_trusted.py`.
2. Zero custom `axiom`, `sorry`, `unsafe`, `partial`, `native_decide`,
   `implemented_by`, `csimp`, or `extern` declarations are permitted, and all
   `trusted/lean/` declarations must replay cleanly in `base.toKernelEnv.replay`.
3. Every declaration that models a Rust guarantee must include an adjacent
   documentation comment with verbatim quotations and versioned citations
   following [`agent_docs/trusted-rust.md`](../../agent_docs/trusted-rust.md).
