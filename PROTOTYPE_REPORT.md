# Track P Prototype Report — `ws-proto-mir-fragment-lattice` (`ep1-prototype-mir-fragment-lattice`)

- **Workstream ID**: `ws-proto-mir-fragment-lattice`
- **Episode ID**: `ep1-prototype-mir-fragment-lattice`
- **Track & Merge Policy**: `prototype` (`no_merge_prototype` — isolated off `unstable`)
- **Paired Unstable Workstream**: `ws-mir-fragment-lattice-unstable` (currently held in `PROPOSED_HOLD`)
- **Base `unstable` SHA (`BASE_SHA`)**: `b076d6a34d749f712a42fe700342f2d40140a2b5`
- **Recommendation**: **GO** — Unhold `ws-mir-fragment-lattice-unstable` and boost priority from `P2` to **`P1`**.

---

## 1. Executive Summary

This Track P prototype designs, implements, and kernel-verifies a 5-element decidable MIR fragment lattice (`MirFragment`) across both Lean 4 ([MirFragmentPrototype.lean](file:///home/groupagent-anneal-maxwell-bot/Projects/markdittmer/anneal-worktrees/ws-proto-mir-fragment-lattice/theory/Anneal/MirFragmentPrototype.lean)) and Rust ([scaffold.rs](file:///home/groupagent-anneal-maxwell-bot/Projects/markdittmer/anneal-worktrees/ws-proto-mir-fragment-lattice/crates/cargo-anneal/src/scaffold.rs)), converging Anneal's MIR verification pipeline with Zircon 2.1's declarative fragment lattice (`Zircon/IR/Fragment.lean` & `Zircon/Specs/FragmentSpec.lean`, cl/1016587495 & cl/1016618663).

| Metric | Target | Measured Result |
|---|---|---|
| Lean 4 compiler errors / warnings | `0` / `0` | **`0` errors, `0` warnings** |
| `sorry` / `admit` / `sorryAx` / `Lean.ofReduceBool` (`native_decide`) | `0` | **`0`** (verified via `anneal-lsp audit-preview`) |
| `lake env lean theory/Anneal/MirFragmentPrototype.lean` wall time | `< 10s` | **`4.96s`** (`user 10.66s`, `sys 0.91s` with `W = 1`, including Section 9 single-pass isomorphism) |
| Warm `anneal-lsp diagnostics` latency | `< 2s` | **`0.87s`** (`872.4 ms`) |
| `cargo test -p cargo-anneal --lib --bins` suite | All pass | **`63 / 63` passed** (`0` failed; note `tests/end_to_end_demo_journeys.rs` has a pre-existing `b076d6a3` `disableLocalBorrows` `dsimp only` regression in `examples/wireframe-demo`) |

---

## 2. The 5-Element `MirFragment` Lattice Architecture

Ordered strictly by syntactic and semantic expressiveness (`0..=4`):

$$\texttt{pureLoopFree} \; (0) \;<\; \texttt{pureBoundedLoop} \; (1) \;<\; \texttt{treeBorrowsLocal} \; (2) \;<\; \texttt{intrinsicCopy} \; (3) \;<\; \texttt{fullMir} \; (4)$$

| Rank | Lean Constructor | Rust Variant / `spec-lock.json` Tag | Semantic Scope | Primary Anneal Proof Engine |
|---|---|---|---|---|
| `0` | `MirFragment.pureLoopFree` | `MirFragment::PureLoopFree` (`"pure_loop_free"`) | Alias-free, call-free `PureMirExec` MIR with no CFG back-edges (`hasCfgBackedge body = false`) | `#mir_lift`, `verifyMirNoPanic_of_pureExec`, `LiftBlock`, `LiftStmtsTerminator` |
| `1` | `MirFragment.pureBoundedLoop` | `MirFragment::PureBoundedLoop` (`"pure_bounded_loop"`) | Exact `Anneal.PureMirExec.checkPureMir` (`goto` / `switchInt` / `assert` / `drop` loops over pure values) | `Anneal.MirLoops` (`forRangeUp`, `mirWpConverges_whileRank`, `runCfgToBlock`) |
| `2` | `MirFragment.treeBorrowsLocal` | `MirFragment::TreeBorrowsLocal` (`"tree_borrows_local"`) | Intraprocedural local borrows/pointers: `.deref`, `.unwrapUnsafeBinder`, `Rvalue.ref`, `Rvalue.rawPtr`, `Rvalue.copyForDeref`, `BinOp.offset`, `CastKind.{pointerCoercion,ptrToPtr}`, `StatementKind.retag` | `Anneal.SepLogicLenses` (`verifyStatefulMir_of_sepLenses`, `LiftLensBlock`) or stateful `runCfgToBlock` |
| `3` | `MirFragment.intrinsicCopy` | `MirFragment::IntrinsicCopy` (`"intrinsic_copy"`) | Extends `treeBorrowsLocal` with `NonDivergingIntrinsic.copyNonOverlapping` and global memory constants (`ConstValue.indirect`, `ConstValue.slice (.ptr ..)`) | `Anneal.MirFuelFree` (`evalCopyNonOverlappingPermOk`, `verifyStatefulMirNoPanic_of_wpConverges`) |
| `4` | `MirFragment.fullMir` | `MirFragment::FullMir` (`"full_mir"`) | Full `Runtime(PostCleanup)` MIR: `TerminatorKind.{call,tailCall,inlineAsm}`, `CastKind.fnPtrToPtr`, `Rvalue.{threadLocalRef,shallowInitBox}`, `StatementKind.backwardIncompatibleDropHint` | `PureMirModularConverges` (`verifyModularMir_of_pureModularExec_any`), `checkPureMirWithCallees`, or `#[spec(trusted)]` |

---

## 3. Complete 20-Row Construct-to-Fragment Parity Table (Lean $\leftrightarrow$ Rust)

Both `checkBodyFragment` / `inferMinFragment` in [MirFragmentPrototype.lean](file:///home/groupagent-anneal-maxwell-bot/Projects/markdittmer/anneal-worktrees/ws-proto-mir-fragment-lattice/theory/Anneal/MirFragmentPrototype.lean) and `classify_mir_fragment` in [scaffold.rs](file:///home/groupagent-anneal-maxwell-bot/Projects/markdittmer/anneal-worktrees/ws-proto-mir-fragment-lattice/crates/cargo-anneal/src/scaffold.rs) classify every `Trusted.Rustc.V2026_06_01.MirAst` construct identically:

| # | `MirAst` Construct | Minimum `MirFragment` | Rust Escalation Reason (`escalation_reasons`) | Accepted by `checkPureMir`? |
|---|---|---|---|---|
| 1 | CFG back-edge (`succ ≤ bbIdx` in `terminatorTargets`) | `.pureBoundedLoop` (`1`) | `"CFG back-edge"` | Yes |
| 2 | `ProjectionElem.deref` | `.treeBorrowsLocal` (`2`) | `"ProjectionElem.deref"` | No |
| 3 | `ProjectionElem.unwrapUnsafeBinder` | `.treeBorrowsLocal` (`2`) | `"ProjectionElem.unwrapUnsafeBinder"` | No |
| 4 | `Rvalue.ref` | `.treeBorrowsLocal` (`2`) | `"Rvalue.ref"` | No |
| 5 | `Rvalue.rawPtr` | `.treeBorrowsLocal` (`2`) | `"Rvalue.rawPtr"` | No |
| 6 | `Rvalue.copyForDeref` | `.treeBorrowsLocal` (`2`) | `"Rvalue.copyForDeref"` | No |
| 7 | `BinOp.offset` | `.treeBorrowsLocal` (`2`) | `"BinOp.offset"` | No |
| 8 | `CastKind.pointerCoercion` | `.treeBorrowsLocal` (`2`) | `"CastKind.pointerCoercion"` | No |
| 9 | `CastKind.ptrToPtr` | `.treeBorrowsLocal` (`2`) | `"CastKind.ptrToPtr"` | No |
| 10 | `StatementKind.retag` | `.treeBorrowsLocal` (`2`) | `"StatementKind.retag"` | No |
| 11 | `NonDivergingIntrinsic.copyNonOverlapping` | `.intrinsicCopy` (`3`) | `"NonDivergingIntrinsic.copyNonOverlapping"` | No |
| 12 | `ConstValue.indirect` | `.intrinsicCopy` (`3`) | `"ConstValue.indirect"` | No |
| 13 | `ConstValue.slice (.ptr ..) _` | `.intrinsicCopy` (`3`) | `"ConstValue.slice (ConstScalar.ptr)"` | No |
| 14 | `TerminatorKind.call` | `.fullMir` (`4`) | `"TerminatorKind.call"` | No |
| 15 | `TerminatorKind.tailCall` | `.fullMir` (`4`) | `"TerminatorKind.tailCall"` | No |
| 16 | `TerminatorKind.inlineAsm` | `.fullMir` (`4`) | `"TerminatorKind.inlineAsm"` | No |
| 17 | `CastKind.fnPtrToPtr` | `.fullMir` (`4`) | `"CastKind.fnPtrToPtr"` | No |
| 18 | `Rvalue.threadLocalRef` | `.fullMir` (`4`) | `"Rvalue.threadLocalRef"` | No |
| 19 | `Rvalue.shallowInitBox` | `.fullMir` (`4`) | `"Rvalue.shallowInitBox"` | No |
| 20 | `StatementKind.backwardIncompatibleDropHint` | `.fullMir` (`4`) | `"StatementKind.backwardIncompatibleDropHint"` | No |

All other `MirAst` constructs (`.zeroSized`, `.scalar`, `.slice (.int _)`, `.unevaluated`, `.field`, `.index`, `.constantIndex`, `.subslice`, `.downcast`, `.opaqueCast`, the 25 non-`offset` `BinOp`s, `UnOp`, `NullOp`, `Rvalue.{use,repeat,len,nullaryOp,unaryOp,discriminant,aggregate,wrapUnsafeBinder}`, `StatementKind.{assign,setDiscriminant,storageLive,storageDead,nop,coverage,constEvalCounter,placeMention,deinit}`, `NonDivergingIntrinsic.assume`, and `TerminatorKind.{goto,switchInt,return_,assert,drop,unreachable,unwindResume,unwindTerminate}`) belong to `.pureLoopFree` (`0`) whenever their sub-operands/places belong to `.pureLoopFree`.

---

## 4. Kernel-Checked Theorem Inventory (`theory/Anneal/MirFragmentPrototype.lean`)

1. **Bounded Lattice Laws**:
   - `toRank_injective`, `fromStr?_asStr`, `fromStr?_leanCtor`, `ofRank?_toRank`, `toRank_lt_five`
   - `le_refl`, `le_trans`, `le_antisymm`, `le_total`, `lt_iff_le_not_le`, `bot_le`, `le_top`
   - `le_join_left`, `le_join_right`, `join_le`, `join_le_iff`, `join_comm`, `join_assoc`, `join_idem`
   - `meet_le_left`, `meet_le_right`, `le_meet`, `le_meet_iff`, `meet_comm`, `meet_assoc`, `meet_idem`
2. **CFG Back-Edge & General DAG Acyclicity**:
   - `cfgEdge_lt_of_hasCfgBackedge_false : hasCfgBackedge body = false → CfgEdge body u v → u < v`
   - `cfgPath_lt_of_hasCfgBackedge_false : hasCfgBackedge body = false → CfgPath body u v → u < v`
   - `no_cfg_cycle_of_hasCfgBackedge_false : hasCfgBackedge body = false → ∀ u, ¬ CfgPath body u u`
   - `nonTopoDagWitness_backedge_vs_cycle`: concrete 3-block witness separating index back-edges (`hasCfgBackedge = true`) from general directed cycles (`hasCfgCycle = false`).
3. **Monotonicity, Totality & Galois Lower-Adjoint Minimality**:
   - `checkConstFragment_mono`, `checkProjElemFragment_mono`, `checkPlaceFragment_mono`, `checkOperandFragment_mono`, `checkBinOpFragment_mono`, `checkCastFragment_mono`, `checkRvalueFragment_mono`, `checkStmtFragment_mono`, `checkTerminatorFragment_mono`, `checkBlockFragment_mono`, `checkBodyFragment_mono`
   - `checkBodyFragment_fullMir : ∀ body, checkBodyFragment .fullMir body = true`
   - `checkBodyFragment_inferMinFragment : ∀ body, checkBodyFragment (inferMinFragment body) body = true`
   - `inferMinFragment_minimal : ∀ body f, checkBodyFragment f body = true → inferMinFragment body ≤ f`
   - `checkBodyFragment_iff_inferMinFragment_le : ∀ f body, checkBodyFragment f body = true ↔ inferMinFragment body ≤ f`
   - `inferMinFragment_eq_filter_headD`
4. **Structural Exclusion Theorems**:
   - `pureLoopFree_has_no_backedges`, `pureLoopFree_no_cfg_cycle`
   - `no_deref_in_pureBoundedLoop`, `no_retag_in_pureBoundedLoop`, `no_retag_body_in_pureBoundedLoop`
   - `no_copyNonOverlapping_in_treeBorrowsLocal`, `no_copyNonOverlapping_body_in_treeBorrowsLocal`
   - `no_call_in_intrinsicCopy`, `no_call_body_in_intrinsicCopy`, `no_inlineAsm_in_intrinsicCopy`, `no_inlineAsm_body_in_intrinsicCopy`
5. **Exact `Anneal.PureMirExec` Bridge Theorems**:
   - `checkBodyFragment_pureBoundedLoop_eq_checkPureMir : ∀ body, checkBodyFragment .pureBoundedLoop body = Anneal.PureMirExec.checkPureMir body`
   - `checkPureMir_of_inferMinFragment_le_pureBoundedLoop`
   - `inferMinFragment_le_pureBoundedLoop_iff_checkPureMir`
   - `verifyMirNoPanic_of_inferMinFragment_le_pureBoundedLoop`
6. **Polymorphic Generic Instantiation Invariance (`CapturedMir.instantiate`)**:
   - `checkBodyFragment_instantiate : ∀ f body args, checkBodyFragment f (body.instantiate args) = checkBodyFragment f body`
   - `inferMinFragment_instantiate : ∀ body args, inferMinFragment (body.instantiate args) = inferMinFragment body`
7. **Single-Pass Bottom-Up Lattice Inference Isomorphism (`inferMinFragmentSinglePass`)**:
   - `checkBodyFragment_eq_decide_singlePass : ∀ f body, checkBodyFragment f body = decide (inferMinFragmentSinglePass body ≤ f)`
   - `inferMinFragmentSinglePass_eq_inferMinFragment : ∀ body, inferMinFragmentSinglePass body = inferMinFragment body` (proving that the single-pass `MirFragment.join` fold used by `scaffold.rs` is extensionally identical to the top-down cascade `inferMinFragment`).

---

## 5. Subtle Engineering Findings Discovered During Prototyping

1. **`CastKind` Wildcard Behavior in `Anneal.PureMirExec.isPureRvalue`**:
   - In `theory/Anneal/PureMirExec.lean` (lines 361–367), `isPureRvalue` matches `.cast ck op _` by rejecting `.pointerCoercion _`, `.fnPtrToPtr`, and `.ptrToPtr`, and falling through to `_ => isPureOperand op` for the remaining 8 `CastKind` constructors—including `.pointerExposeProvenance` and `.pointerWithExposedProvenance` (because `evalRvalue` in `MirSemantics.lean` threads `mem` through unchanged on those casts).
   - Because `.pureBoundedLoop` must equal `checkPureMir` AND satisfy `checkBodyFragment_mono` (`pureBoundedLoop ≤ treeBorrowsLocal`), `checkCastFragment` accepts those 8 `CastKind`s from `.pureLoopFree` upward, places `.pointerCoercion` and `.ptrToPtr` in `.treeBorrowsLocal`, and places `.fnPtrToPtr` in `.fullMir`.
   - **Actionable Recommendation for `ws-mir-fragment-lattice-unstable`**: When landing Episode 1 on `unstable`, either keep this exact table (zero churn to existing `PureMirExec` proofs) or explicitly reject `.pointerExposeProvenance` and `.pointerWithExposedProvenance` in `PureMirExec.isPureRvalue` so they live at `.fullMir`.
2. **Index-Order CFG Back-Edge (`hasCfgBackedge`) vs. General Cycle Detection (`hasCfgCycle`)**:
   - `hasCfgBackedge` checks whether block `bbIdx` has a target `succ ≤ bbIdx`. By `no_cfg_cycle_of_hasCfgBackedge_false`, `hasCfgBackedge body = false` strictly implies general DAG acyclicity (`∀ u, ¬ CfgPath body u u`), which is the exact precondition needed by `#mir_lift` / forward block induction.
   - As demonstrated by `nonTopoDagWitness` (`bb0 -> bb2 -> bb1 -> return`), a DAG whose blocks are not topologically ordered has `hasCfgBackedge = true` while `hasCfgCycle = false`. Because `rustc` emits `Runtime(PostCleanup)` MIR basic blocks in reverse postorder (RPO), genuine loop back-edges in `rustc` MIR always satisfy `succ ≤ bbIdx`.
3. **Token-Exact Constructor Scanning & Field-Order Hardening in `scaffold.rs`**:
   - Earlier substring/dot scanning (`has_dotted_ctor` without preceding token boundary and `.contains(tok)`) could false-trigger on identifier substrings (`local_call`, `recall`, `my_retag`) or module paths (`Mir.MyCrate.call`), and `detect_blocks_and_back_edges` used `.or_else` instead of `.min()` when finding the end of a terminator block.
   - `scaffold.rs` now uses whitespace-token-exact `has_ast_ctor(norm_blocks, type_name, ctor_name)`, bounds `basicBlocks :=` and `localDecls :=` slices against all 12 `CapturedMir` record fields in any order, and fails closed to `MirFragment::FullMir` on non-inline alias definitions (`def body : CapturedMir := otherBody`).
4. **Live Confirmation of the Problem Statement on `BASE_SHA` (`b076d6a3`, `ws-lm-div-statements`)**:
   - Commit `b076d6a34d749f712a42fe700342f2d40140a2b5` (`Merge branch 'ws-lm-div-statements' into unstable`) added `disableLocalBorrows` to `StatementKind.storageDead` and `ensureNestedFieldShells` / `uninitFieldWriteShell?` to `finishAssignStmtNode`. While `tests/mir/SymbolicEvalTests.lean` was updated to add `disableLocalBorrows` to its `dsimp only [...]` list, `examples/wireframe-demo/anneal/proofs/Proof/WireframeDemo/{clamp_payload_window,frame_total_len,checksum_frame_safe}.lean` (exercised by `tests/end_to_end_demo_journeys.rs`) still use hardcoded `dsimp only [...]` lists without `disableLocalBorrows`, causing `repeat (dsimp only [...])` to stall at `storageDead`.
   - Notably, `clamp_payload_window` and `frame_total_len` are both classified as `MirFragment.pureLoopFree` (`0`) by `inferMinFragment` / `classify_mir_fragment`—meaning they should be discharged via `Anneal.PureMirExec` / `MirLiftCore` (which encapsulates `evalStmt` / `disableLocalBorrows` behind `evalStmt_pure_eq_withMem`) rather than brittle 40-symbol `dsimp only` lists!

---

## 6. Empirical Fragment Classification Over Real Captured MIR & Worked Fixtures

| Source File / Fixture | Item `defPath` | Basic Blocks | `inferMinFragment` / `classify_mir_fragment` | Escalation Reasons |
|---|---|---|---|---|
| `examples/tutor-ch1/.anneal/generated/Mir/FrameTutor/magic_version.lean` | `frame_tutor::magic_version` | 1 | `pure_loop_free` (`0`) | `[]` |
| `examples/tutor-ch1/.anneal/generated/Mir/FrameTutor/advance_offset.lean` | `frame_tutor::advance_offset` | 2 | `pure_loop_free` (`0`) | `[]` |
| `examples/mir/MirVerification.lean` (`addU32UncheckedMirBody`) | `demo::add_u32_unchecked` | 1 | `pure_loop_free` (`0`) | `[]` |
| `examples/mir/MirVerification.lean` (`eq42BoolSpecMirBody`) | `demo::__anodized_ensures_eq42` | 1 | `pure_loop_free` (`0`) | `[]` |
| `examples/mir/MirVerification.lean` (`branchObsMirBody`) | `demo::branch_obs` | 3 | `pure_loop_free` (`0`) | `[]` |
| `examples/mir/MirVerification.lean` (`polySwapPairMirBody`) | `demo::swap_pair` | 1 | `pure_loop_free` (`0`) | `[]` |
| `examples/mir/MirVerification.lean` (`countdownMirBody`) | `demo::countdown_loop` | 3 | `pure_bounded_loop` (`1`) | `["CFG back-edge"]` |
| `examples/mir/MirVerification.lean` (`infiniteLoopMirBody`) | `demo::infinite_loop` | 1 | `pure_bounded_loop` (`1`) | `["CFG back-edge"]` |
| `examples/mir/MirVerification.lean` (`reborrowWriteMirBody`) | `demo::reborrow_write_ok` | 1 | `tree_borrows_local` (`2`) | `["ProjectionElem.deref", "Rvalue.ref"]` |
| `examples/mir/MirVerification.lean` (`aliasingViolationMirBody`) | `demo::aliasing_violation_ub` | 1 | `tree_borrows_local` (`2`) | `["ProjectionElem.deref", "Rvalue.ref"]` |
| `examples/mir/MirVerification.lean` (`unalignSetMirBody`) | `zerocopy::Unalign::set` | 1 | `tree_borrows_local` (`2`) | `["ProjectionElem.deref"]` |
| `theory/Anneal/MirFragmentPrototype.lean` (`witnessIntrinsicCopy`) | `proto::witness_intrinsic_copy` | 1 | `intrinsic_copy` (`3`) | `["NonDivergingIntrinsic.copyNonOverlapping"]` |
| `examples/mir/MirVerification.lean` (`ffiDoubleCallMirBody`) | `demo::ffi_double_call_assert_eq` | 4 | `full_mir` (`4`) | `["TerminatorKind.call"]` |
| `examples/mir/MirVerification.lean` (`callerAddTwoMirBody`) | `app::add_two_u32` | 2 | `full_mir` (`4`) | `["TerminatorKind.call"]` |

---

## 7. Integration Plan for `ws-mir-fragment-lattice-unstable` (Go / Priority Boost to `P1`)

1. **Episode 1 (`ep1-mir-fragment-lattice-lean` on `unstable`)**:
   - Promote `theory/Anneal/MirFragmentPrototype.lean` to `theory/Anneal/MirFragment.lean` and export `Anneal.MirFragment` in `theory/Anneal.lean`.
   - Connect `checkBodyFragment_pureBoundedLoop_eq_checkPureMir` and `pureLoopFree_has_no_backedges` directly to `Anneal.MirLift` (`#mir_lift` elaborator precondition check) so `#mir_lift` emits an immediate fragment diagnostic using `inferMinFragment` whenever applied to a body exceeding `.pureLoopFree`.
2. **Episode 2 (`ep2-cargo-anneal-fragment-certificates` on `unstable`)**:
   - Wire `MirFragment`, `classify_mir_fragment`, `render_mir_fragment_diagnostic`, and `compute_prototype_fragment_spec_digest` from `crates/cargo-anneal/src/scaffold.rs` into `.anneal/generated/Obligations/<Item>.lean` (`def fragment : MirFragment := ...` + `theorem fragment_sound : checkBodyFragment fragment Mir.<Item>.body = true := by rfl`) and `.anneal/spec-lock.json` (`mir_fragment` + `spec_digest`), mirroring Zircon 2.1 cl/1016618663.
   - Surface `render_mir_fragment_diagnostic` in `cargo anneal agent-context` whenever an item crosses `pure_bounded_loop` so agents and users immediately see which construct triggered stateful/modular escalation and which Anneal proof combinator to use.
