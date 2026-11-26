import Anneal.Rustc.V2026_06_01.SymbolicEval.CoreEvalAndDischarge
import Anneal.Rustc.V2026_06_01.SymbolicEval.PinnedSpecEquivAndCalls
import Anneal.Rustc.V2026_06_01.SymbolicEval.DiffTestingAndSigTests
import Anneal.Rustc.V2026_06_01.SymbolicEval.SymTableGvnAndCanonState
import Anneal.Rustc.V2026_06_01.SymbolicEval.MirCfgAndJoinPruning
import Anneal.Rustc.V2026_06_01.SymbolicEval.CfgGvnDriverAndBenchmarks
import Anneal.Rustc.V2026_06_01.SymbolicEval.MirSemanticsBridges
import Anneal.Rustc.V2026_06_01.SymbolicEval.MirJoinDiamondWitness

/-!
# `Anneal.Rustc.V2026_06_01.SymbolicEval`

Umbrella module re-exporting every `Anneal.Rustc.V2026_06_01.SymbolicEval.*` submodule; all
declarations live in namespace `Anneal.Rustc.V2026_06_01.SymbolicEval`. The submodule split keeps
each file within `3,500` lines so it elaborates and kernel-replays under `-j1 -M2048`.

- `SymbolicEval.CoreEvalAndDischarge`: Core single-pass CPS symbolic MIR evaluator, `@[simp]` collapsing lemmas, fast-path checkers, certificate discharge combinators, and pinned `#[spec]` combinators (sections 1-7).
- `SymbolicEval.PinnedSpecEquivAndCalls`: Bounded UB refutation, call-free program equivalence, scoped-UB / modular call-contract evaluators, and `O(1)` block / callee lookup context lemmas (sections 8, 9, 14, 15).
- `SymbolicEval.DiffTestingAndSigTests`: Differential-testing outcome classifiers, strict UB / panic refutation combinators, and signature / polymorphic obligation adapter kernel checks (section 10, `SignatureValidationTests`).
- `SymbolicEval.SymTableGvnAndCanonState`: Append-only `SymTable` GVN with monotone evaluation and peepholes, `CanonLocals` / `CanonState` canonical MIR state, and CPS spine forcing.
- `SymbolicEval.MirCfgAndJoinPruning`: Compositional join-point cuts, first-order MIR CFG syntax and concrete semantics, join-point pruning refinement, and compositional diamond joins (sections 3-3.4).
- `SymbolicEval.CfgGvnDriverAndBenchmarks`: Single-continuation symbolic CFG evaluator (`symEvalCfgGvn`) with end-to-end soundness and kernel-checked `k`-diamond multi-block CFG benchmarks (sections 3.5-3.6).
- `SymbolicEval.MirSemanticsBridges`: Width-aware trusted `MirSemantics` operator bridges and production `DWLP mirDefaultWP` diamond / triangle / `switchTable` join-cut combinators with `callerLocals` / full-`Memory` merges.
- `SymbolicEval.MirJoinDiamondWitness`: Concrete diamond / triangle / `switchTable` / caller-`&mut` / full-memory join witnesses, `MirStateLiveEquiv` bridges, `Value.uninit` / `Memory.rootUnwindCeiling` regressions, and the GVN / join-cut axiom policy.
-/
