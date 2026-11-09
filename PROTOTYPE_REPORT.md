# Track P Prototype Report — `ws-proto-mir-fragment-lattice` (`ep1-prototype-mir-fragment-lattice`)

- **Workstream ID**: `ws-proto-mir-fragment-lattice`
- **Episode ID**: `ep1-prototype-mir-fragment-lattice`
- **Track & Merge Policy**: `prototype` (`no_merge_prototype` — isolated off `unstable`)
- **Paired Unstable Workstream**: `ws-mir-fragment-lattice-unstable` (currently held in `PROPOSED_HOLD`)
- **Base `unstable` SHA (`BASE_SHA`)**: `b076d6a34d749f712a42fe700342f2d40140a2b5`
- **Adversarial history**: `[adv A0]` initial build → `[adv B1]` cross-family critique & hardening → `[adv A1]` Round 1 critique & fail-closed/theorem hardening (this revision)
- **Recommendation**: **GO (conditional)** — unhold `ws-mir-fragment-lattice-unstable` and boost priority from `P2` to **`P1`**, carrying over the B1 + A1 fail-closed scanner rules and the Lean-witness parity test (Section 7).

---

## 1. Executive Summary

This Track P prototype designs, implements, and kernel-verifies a 5-element decidable MIR fragment lattice (`MirFragment`) across both Lean 4 ([MirFragmentPrototype.lean](file:///home/groupagent-anneal-maxwell-bot/Projects/markdittmer/anneal-worktrees/ws-proto-mir-fragment-lattice/theory/Anneal/MirFragmentPrototype.lean)) and Rust ([scaffold.rs](file:///home/groupagent-anneal-maxwell-bot/Projects/markdittmer/anneal-worktrees/ws-proto-mir-fragment-lattice/crates/cargo-anneal/src/scaffold.rs)), converging Anneal's MIR verification pipeline with Zircon 2.1's declarative fragment lattice (`Zircon/IR/Fragment.lean` & `Zircon/Specs/FragmentSpec.lean`, cl/1016587495 & cl/1016618663).

| Metric | Target | Measured Result (`[adv A1]`) |
|---|---|---|
| Lean 4 compiler errors / warnings | `0` / `0` | **`0` errors, `0` warnings** (`anneal-lsp diagnostics`) |
| `sorry` / `admit` / `sorryAx` / `Lean.ofReduceBool` (`native_decide`) | `0` | **`0`** (`anneal-lsp audit-preview` + per-theorem `#print axioms` over all **203** theorems) |
| Axioms used (all 203 theorems) | standard only | Zero forbidden axioms (`sorryAx` / `Lean.ofReduceBool`); only `verifyMirNoPanic_of_inferMinFragment_le_pureBoundedLoop` and `verifyMirSafe_of_inferMinFragment_le_pureBoundedLoop` inherit `Classical.choice` from upstream `Anneal.PureMirExec` |
| `lake env lean theory/Anneal/MirFragmentPrototype.lean` wall time | `< 10s` | **`4.28s`** (`user 14.41s`, `sys 0.88s`, `W = 1`; 2,694 lines; bash `time -p` — `/usr/bin/time` is absent on this capsule) |
| `cargo test -p cargo-anneal --lib --bins` | All pass | **`65` passed, `0` failed, `1` ignored** (`34.74s`, opt-in parity harness) |
| Full `cargo test -p cargo-anneal` | exit `0` | **exit `101`** (`170.69s`): lib `65` passed / `1` ignored, bins `0`, then `tests/end_to_end_demo_journeys.rs` fails — **identically on `BASE_SHA`** (Section 5, Finding 7) |
| Other integration binaries (run separately with B1, `--no-fail-fast`) | pass | `end_to_end_pipeline` 1/1, `end_to_end_rust_only_adoption` 2/2, `end_to_end_tutor` 4/4, `end_to_end_difftest_oracles` 4/4, `end_to_end_itree_diff` 4/4; `end_to_end_minirust_correspondence` has one failure (`e2e_upstream_md_mutation_changes_generated_ops_and_breaks_lean_proof`, a MiniRust vendor/specr test with no `scaffold.rs` dependency; not investigated in B1); `miri_diff` / `trace_observer` not run |
| Lean ↔ Rust parity, real `rustc`-captured MIR | `0` mismatches | **`0 / 64`** bodies (fragment, back-edge flag, block count) |
| Lean ↔ Rust parity, differential fuzzing | `0` fail-open | **`0 / 1,400`** fail-open; exact agreement on all `1,267` inline bodies (Section 6.3) |

---

## 2. The 5-Element `MirFragment` Lattice Architecture

Ordered strictly by syntactic and semantic expressiveness (`0..=4`):

$$\texttt{pureLoopFree} \; (0) \;<\; \texttt{pureBoundedLoop} \; (1) \;<\; \texttt{treeBorrowsLocal} \; (2) \;<\; \texttt{intrinsicCopy} \; (3) \;<\; \texttt{fullMir} \; (4)$$

| Rank | Lean Constructor | Rust Variant / `spec-lock.json` Tag | Semantic Scope | Primary Anneal Proof Engine |
|---|---|---|---|---|
| `0` | `MirFragment.pureLoopFree` | `MirFragment::PureLoopFree` (`"pure_loop_free"`) | Exactly `checkPureMir body && !hasCfgBackedge body` (`checkBodyFragment_pureLoopFree_eq`) | `#mir_lift`, `verifyMirNoPanic_of_pureExec`, `LiftBlock`, `LiftStmtsTerminator` |
| `1` | `MirFragment.pureBoundedLoop` | `MirFragment::PureBoundedLoop` (`"pure_bounded_loop"`) | Exact `Anneal.PureMirExec.checkPureMir` (`goto` / `switchInt` / `assert` / `drop` loops over pure values) | `Anneal.MirLoops` (`forRangeUp`, `mirWpConverges_whileRank`, `runCfgToBlock`) |
| `2` | `MirFragment.treeBorrowsLocal` | `MirFragment::TreeBorrowsLocal` (`"tree_borrows_local"`) | Intraprocedural borrows/pointers: `.deref`, `.unwrapUnsafeBinder`, `Rvalue.ref`, `Rvalue.rawPtr`, `Rvalue.copyForDeref`, `BinOp.offset`, `CastKind.{pointerCoercion,ptrToPtr}`, `StatementKind.retag` | `Anneal.SepLogicLenses` (`verifyStatefulMir_of_sepLenses`, `LiftLensBlock`) or stateful `runCfgToBlock` |
| `3` | `MirFragment.intrinsicCopy` | `MirFragment::IntrinsicCopy` (`"intrinsic_copy"`) | Adds `NonDivergingIntrinsic.copyNonOverlapping` and global-allocation constants (`ConstValue.indirect`, `ConstValue.slice (.ptr ..)`) | `Anneal.MirFuelFree` (`evalCopyNonOverlappingPermOk`, `verifyStatefulMirNoPanic_of_wpConverges`) |
| `4` | `MirFragment.fullMir` | `MirFragment::FullMir` (`"full_mir"`, fail-closed `Default` / `Inhabited`) | Full `Runtime` MIR: `TerminatorKind.{call,tailCall,inlineAsm}`, `CastKind.fnPtrToPtr`, `Rvalue.{threadLocalRef,shallowInitBox}`, `StatementKind.backwardIncompatibleDropHint` | `PureMirModularConverges` (`verifyModularMir_of_pureModularExec_any`), `checkPureMirWithCallees`, or `#[spec(trusted)]` |

Rank `1` is a **pure CFG property**: `minBlockFragment_ne_pureBoundedLoop` proves that no basic block (hence no single MIR construct) requires exactly `.pureBoundedLoop`; only `hasCfgBackedge` separates ranks `0` and `1`.

---

## 3. Construct-to-Fragment Parity Table (Lean $\leftrightarrow$ Rust)

Both `checkBodyFragment` / `inferMinFragment` in [MirFragmentPrototype.lean](file:///home/groupagent-anneal-maxwell-bot/Projects/markdittmer/anneal-worktrees/ws-proto-mir-fragment-lattice/theory/Anneal/MirFragmentPrototype.lean) and `classify_mir_fragment` in [scaffold.rs](file:///home/groupagent-anneal-maxwell-bot/Projects/markdittmer/anneal-worktrees/ws-proto-mir-fragment-lattice/crates/cargo-anneal/src/scaffold.rs) classify every `Trusted.Rustc.V2026_06_01.MirAst` construct identically:

| # | `MirAst` Construct | Minimum `MirFragment` | Rust Escalation Reason (`escalation_reasons`) | Accepted by `checkPureMir`? |
|---|---|---|---|---|
| 1 | CFG back-edge (`succ ≤ bbIdx` in `terminatorTargets`; exact spec `hasCfgBackedge_eq_true_iff`) | `.pureBoundedLoop` (`1`) | `"CFG back-edge"` | Yes |
| 2 | `ProjectionElem.deref` | `.treeBorrowsLocal` (`2`) | `"ProjectionElem.deref"` | No |
| 3 | `ProjectionElem.unwrapUnsafeBinder` | `.treeBorrowsLocal` (`2`) | `"ProjectionElem.unwrapUnsafeBinder"` | No |
| 4 | `Rvalue.ref` (`BorrowKind.shared` / `BorrowKind.mut b`; **not** `RigidTy.ref` / `Mutability.mut`) | `.treeBorrowsLocal` (`2`) | `"Rvalue.ref"` | No |
| 5 | `Rvalue.rawPtr` (**not** `RigidTy.rawPtr` / `AggregateKind.rawPtr`) | `.treeBorrowsLocal` (`2`) | `"Rvalue.rawPtr"` | No |
| 6 | `Rvalue.copyForDeref` | `.treeBorrowsLocal` (`2`) | `"Rvalue.copyForDeref"` | No |
| 7 | `BinOp.offset` | `.treeBorrowsLocal` (`2`) | `"BinOp.offset"` | No |
| 8 | `CastKind.pointerCoercion` | `.treeBorrowsLocal` (`2`) | `"CastKind.pointerCoercion"` | No |
| 9 | `CastKind.ptrToPtr` | `.treeBorrowsLocal` (`2`) | `"CastKind.ptrToPtr"` | No |
| 10 | `StatementKind.retag` | `.treeBorrowsLocal` (`2`) | `"StatementKind.retag"` | No |
| 11 | `NonDivergingIntrinsic.copyNonOverlapping` | `.intrinsicCopy` (`3`) | `"NonDivergingIntrinsic.copyNonOverlapping"` | No |
| 12 | `ConstValue.indirect` | `.intrinsicCopy` (`3`) | `"ConstValue.indirect"` | No |
| 13 | `ConstValue.slice (.ptr ..) _` (e.g. every `&'static str` literal) | `.intrinsicCopy` (`3`) | `"ConstValue.slice (ConstScalar.ptr)"` | No |
| 14 | `TerminatorKind.call` | `.fullMir` (`4`) | `"TerminatorKind.call"` | No |
| 15 | `TerminatorKind.tailCall` | `.fullMir` (`4`) | `"TerminatorKind.tailCall"` | No |
| 16 | `TerminatorKind.inlineAsm` | `.fullMir` (`4`) | `"TerminatorKind.inlineAsm"` | No |
| 17 | `CastKind.fnPtrToPtr` | `.fullMir` (`4`) | `"CastKind.fnPtrToPtr"` | No |
| 18 | `Rvalue.threadLocalRef` | `.fullMir` (`4`) | `"Rvalue.threadLocalRef"` | No |
| 19 | `Rvalue.shallowInitBox` | `.fullMir` (`4`) | `"Rvalue.shallowInitBox"` | No |
| 20 | `StatementKind.backwardIncompatibleDropHint` | `.fullMir` (`4`) | `"StatementKind.backwardIncompatibleDropHint"` | No |
| 21 | *(Rust-only, fail-closed)* non-inline / unscannable syntax inside `basicBlocks` (helper `def` refs, `let`/`fun`, `{ x with .. }`, positional `X.mk`, `⟨..⟩`) | `.fullMir` (`4`) $\ge$ Lean | ``"unscannable non-inline MIR syntax `<tok>` in basicBlocks (fail-closed)"`` | n/a (Lean sees through definitions) |

All other `MirAst` constructs (`.zeroSized`, `.scalar` — including `.scalar (.ptr ..)`, `.slice (.int _)`, `.unevaluated`, `.field`, `.index`, `.constantIndex`, `.subslice`, `.downcast`, `.opaqueCast`, the 25 non-`offset` `BinOp`s, `UnOp`, `NullOp`, the 8 remaining `CastKind`s, `Rvalue.{use,repeat,len,nullaryOp,unaryOp,discriminant,aggregate,wrapUnsafeBinder}`, `StatementKind.{assign,setDiscriminant,storageLive,storageDead,nop,coverage,constEvalCounter,placeMention,deinit}`, `NonDivergingIntrinsic.assume`, and `TerminatorKind.{goto,switchInt,return_,assert,drop,unreachable,unwindResume,unwindTerminate}`) belong to `.pureLoopFree` (`0`) whenever their sub-operands/places do.

**Parity is now enforced mechanically**: the unit test `mir_fragment_rust_classifier_matches_lean_witness_theorems` `include_str!`s `MirFragmentPrototype.lean`, extracts the verbatim text of every Section 8 witness (`def <w> : CapturedMir := { protoBase with .. basicBlocks := [..] }`), runs `classify_mir_fragment` on it, and asserts the result equals the value proven by the kernel-checked theorem `inferMinFragment <w> = .<frag> := rfl` (12 witnesses, all 5 levels) and `hasCfgBackedge <w> = <b> := rfl` (5 witnesses). Editing either side without the other fails `cargo test`.

---

## 4. Kernel-Checked Theorem Inventory (`theory/Anneal/MirFragmentPrototype.lean`, 203 theorems)

1. **Bounded Lattice Laws**:
   - `toRank_injective`, `fromStr?_asStr`, `fromStr?_leanCtor`, `ofRank?_toRank`, `toRank_lt_five`
   - `le_refl`, `le_trans`, `le_antisymm`, `le_total`, `lt_iff_le_not_le`, `bot_le`, `le_top`
   - `le_join_left`, `le_join_right`, `join_le`, `join_le_iff`, `join_comm`, `join_assoc`, `join_idem`
   - `meet_le_left`, `meet_le_right`, `le_meet`, `le_meet_iff`, `meet_comm`, `meet_assoc`, `meet_idem`
2. **CFG Back-Edge Rule, Exact Spec & General DAG Acyclicity**:
   - `cfgEdge_lt_of_hasCfgBackedge_false`, `cfgPath_lt_of_hasCfgBackedge_false`, `no_cfg_cycle_of_hasCfgBackedge_false` (soundness of the index-order rule)
   - `hasCfgBackedge_eq_true_iff : hasCfgBackedge body = true ↔ ∃ u v, CfgEdge body u v ∧ v ≤ u` and `hasCfgBackedge_eq_false_iff : hasCfgBackedge body = false ↔ ∀ u v, CfgEdge body u v → u < v` (exact biconditional specs of the rule `scaffold.rs` mirrors)
   - Rank certificates: `cfgEdge_rank_lt_of_hasRankViolation_false`, `cfgPath_rank_lt_of_hasRankViolation_false`, `no_cfg_cycle_of_hasRankViolation_false` (for **any** `rank : Nat → Nat`), `hasRankViolation_id_eq_hasCfgBackedge` (index order = identity rank), `exists_rank_certificate_of_hasCfgBackedge_false`
   - `isCfgDag` ($O(n^2|E|)$ longest-path relaxation) with `no_cfg_cycle_of_isCfgDag`
   - `nonTopoDagWitness_backedge_vs_dag`, `nonTopoDagWitness_acyclic`, `witnessRustcSharedReturn_pure_acyclic_but_pureBoundedLoop`, `witnessRustcSharedReturn_acyclic`, `witnessPureBoundedLoop_cycle` (genuine `bb1 → bb1` cycle, `isCfgDag = false`)
3. **Monotonicity, Totality & Galois Lower-Adjoint Minimality**:
   - `checkConstFragment_mono` … `checkBodyFragment_mono` (11 theorems)
   - `checkBodyFragment_fullMir`, `checkBodyFragment_inferMinFragment`, `inferMinFragment_minimal`, `checkBodyFragment_iff_inferMinFragment_le`, `checkBodyFragment_false_of_lt_inferMinFragment`, `inferMinFragment_eq_filter_headD`
4. **Structural Exclusion & Universal Lower-Bound Theorems**:
   - `pureLoopFree_has_no_backedges`, `pureLoopFree_no_cfg_cycle`
   - `no_deref_in_pureBoundedLoop`, `no_retag_in_pureBoundedLoop` (+ body form), `no_copyNonOverlapping_in_treeBorrowsLocal` (+ body form), `no_call_in_intrinsicCopy` (+ body form), `no_inlineAsm_in_intrinsicCopy` (+ body form)
   - Downward-closed forms across **all 20 parity-table rows** for every level `f < threshold`: `no_deref_below_treeBorrowsLocal`, `no_retag_below_treeBorrowsLocal`, `no_ref_or_rawPtr_below_treeBorrowsLocal`, `no_copyForDeref_below_treeBorrowsLocal`, `no_offset_below_treeBorrowsLocal`, `no_ptrCast_below_treeBorrowsLocal`, `no_unwrapUnsafeBinder_below_treeBorrowsLocal`, `no_copyNonOverlapping_below_intrinsicCopy`, `no_globalAllocConst_below_intrinsicCopy`, `no_call_below_fullMir`, `no_inlineAsm_below_fullMir`, `no_fullMirOnlyConstructs_below_fullMir`, plus body-level `no_{retag,copyNonOverlapping,call,inlineAsm}_body_below_*`
   - Universal membership lower bounds (`minBlockFragment_le_inferMinFragment_of_mem`, `minStmtFragment_le_inferMinFragment_of_mem`, `minTerminatorFragment_le_inferMinFragment_of_mem`) and universal downward-closed body exclusions (`checkBodyFragment_false_of_lt_minStmtFragment`, `checkBodyFragment_false_of_lt_minTerminatorFragment`)
5. **Exact `Anneal.PureMirExec` Bridge Theorems**:
   - `checkBodyFragment_pureBoundedLoop_eq_checkPureMir`, `checkPureMir_of_inferMinFragment_le_pureBoundedLoop`, `inferMinFragment_le_pureBoundedLoop_iff_checkPureMir`, `verifyMirNoPanic_of_inferMinFragment_le_pureBoundedLoop`, `verifyMirSafe_of_inferMinFragment_le_pureBoundedLoop`
   - `checkBodyFragment_pureLoopFree_eq : checkBodyFragment .pureLoopFree body = (checkPureMir body && !hasCfgBackedge body)`, `inferMinFragment_eq_pureLoopFree_iff`, and `inferMinFragment_eq_pureBoundedLoop_iff`
6. **Polymorphic Instantiation Invariance**: `checkBodyFragment_instantiate`, `inferMinFragment_instantiate`, `inferMinFragmentSinglePass_instantiate`, `hasRankViolation_instantiate`, `cfgEdgeList_instantiate`, `dagRanks_instantiate`, `dagRank_instantiate`, `isCfgDag_instantiate` (+ per-construct lemmas).
7. **Single-Pass Bottom-Up Inference**: `checkBodyFragment_eq_decide_singlePass`, `inferMinFragmentSinglePass_eq_inferMinFragment` (the `MirFragment.join` fold used by `scaffold.rs` is extensionally identical to the top-down cascade).
8. **Rank 1 is a CFG property**: `join_ne_pureBoundedLoop`, `joinList_ne_pureBoundedLoop`, `min*Fragment_ne_pureBoundedLoop` (9 lemmas), `minBlockFragment_ne_pureBoundedLoop`, `checkBlockFragment_pureLoopFree_eq_pureBoundedLoop`.
9. **Witnesses** (`rfl` + `#guard`): 12 `inferMinFragment_<w>` and 5 `hasCfgBackedge_<w>` theorems over `witnessPureLoopFree`, `witnessPureBoundedLoop`, `witnessTreeBorrowsLocal`, `witnessIntrinsicCopy`, `witnessFullMir`, `nonTopoDagWitness`, `witnessRustcSharedReturn`, `witnessShorthandMutTypes`, `witnessQualifiedEmitterRawPtr`, `witnessIndirectConst`, `witnessFullMirNoCall`, `witnessOutOfOrderFieldsAndParenSpan`.

---

## 5. Subtle Engineering Findings

1. **`CastKind` wildcard in `Anneal.PureMirExec.isPureRvalue`**: `isPureRvalue` rejects only `.pointerCoercion _`, `.fnPtrToPtr`, `.ptrToPtr`, so `.pointerExposeProvenance` / `.pointerWithExposedProvenance` are pure. Because `.pureBoundedLoop` must equal `checkPureMir` **and** satisfy `checkBodyFragment_mono`, those two casts sit at `.pureLoopFree`; `.pointerCoercion` / `.ptrToPtr` sit at `.treeBorrowsLocal`, `.fnPtrToPtr` at `.fullMir`. *Recommendation*: Episode 1 may move provenance-exposing casts to `.fullMir` only by changing `PureMirExec.isPureRvalue` first.
2. **Index-order back-edges vs. real cycles — `rustc` MIR is *not* RPO-numbered** *(B1 correction)*. A0 claimed captured MIR is in reverse postorder so index back-edges coincide with loops. That is false: `ReorderBasicBlocks` is disabled by default, and the capture reads `tcx.optimized_mir`. In the real corpus (Section 6.1) **6 of 64** bodies (`core::cmp::PartialOrd::{le,lt}`, `core::ops::RangeBounds::contains`, two captures each) have index back-edges yet are certified acyclic by `isCfgDag` (e.g. `PartialOrd::le`: the shared return block `bb2` is numbered before the arms `bb4`/`bb5` that jump to it); only `wireframe_demo::checksum_frame_safe` contains a genuine loop. The index rule stays **sound** (`no_cfg_cycle_of_hasCfgBackedge_false`, a special case of rank certificates) but is **incomplete**: `witnessRustcSharedReturn` (that real CFG, call removed) is pure and acyclic yet classified `.pureBoundedLoop`. All 6 affected real bodies contain calls, so no real body changed fragment, but pure `match` lowering can hit this. *Recommendation*: if Episode 1 wants precision, switch `.pureLoopFree` to `isCfgDag` in **both** Lean and `scaffold.rs` (port the relaxation verbatim) — never in only one.
3. **`Mutability.mut` vs. `BorrowKind.mut` token ambiguity** *(B1, fixed)*: A0's `has_ast_ctor(norm_blocks, "BorrowKind", "mut")` matched every shorthand `.mut` token, including `Mutability.mut` inside `&mut T` / `*mut T` type annotations (casts, field projections, constants) and the pure `AggregateKind.rawPtr _ .mut`. On a 600-body differential corpus, **49 of 300** shorthand bodies were mis-escalated to `tree_borrows_local` with a phantom `Rvalue.ref` (and `has_mut_borrow` was polluted for scaffold hints). B1 resolves `.mut` by its successor (`RigidTy` head ⇒ type; otherwise `BorrowKind.mut`) and pins it with `witnessShorthandMutTypes`.
4. **Fail-open scanning of non-inline syntax & named-argument / spoofed-namespace bypasses** *(B1 + A1, fixed)*: the text scanner only sees what is literally inside `basicBlocks := [...]`. B1 added `bound_to_top_level_decl` and `MIR_BLOCK_CTOR_VOCAB`, and **A1 closed four residual bypasses in B1's validator**:
   - **Closed field allowlist (`MIR_BLOCK_FIELD_VOCAB`)**: B1 allowed *any* `is_lean_ident(tok)` before `:=`, which let named constructor arguments (`.goto (target := 0)`, `.slice (data := .ptr ...) (meta_ := 1)`, `.ref (borrowKind := .mut false) ...`) pass `first_unscannable_block_token` and then defeat positional token detectors (`extract_terminator_targets` missed `0 ≤ 0`; `detect_const_slice_ptr` missed `.ptr`; `detect_mut_borrow` missed `.mut`). A1 restricts `tok :=` to the exact 18 `MirAst` structure field names (`MIR_BLOCK_FIELD_VOCAB`) not preceded by `let`/`have`.
   - **Canonical namespace qualifier check (`is_valid_mir_type_qualifier`)**: B1 checked only the last segment of `qual` in `qual.ctor`, allowing spoofed user helpers like `MyHelper.List.nil` or `Evil.Mutability.not` to pass `is_mir_vocab_ctor`. A1 validates the full qualifier prefix (`Trusted.Rustc.V2026_06_01.MirAst.<TypeName>`, etc.).
   - **Structural block & terminator validation (`detect_blocks_and_back_edges`)**: A1 verifies matching `statements :=` / `terminator :=` / `isCleanup :=` counts per block, strips parenthesized `span := ("...")` after paren normalization (`witnessOutOfOrderFieldsAndParenSpan`), and requires `extract_terminator_targets` to parse every required successor block index or fail closed to `FullMir`.
   - **Top-level declaration bounding**: A1 trims leading whitespace in `bound_to_top_level_decl` (catching `/- doc -/ def ...` after comment stripping) and bounds any `: CapturedMir` declaration even when not named `body`.
5. **Qualified-name robustness** *(B1, fixed)*: terminator heads, unwind actions, `Option.some`, `ConstValue.slice`/`ConstScalar.ptr`, and `StatementKind.intrinsic`/`NonDivergingIntrinsic.assume` are matched through `ast_ctor`, so fully-qualified `Trusted.Rustc.V2026_06_01.MirAst.TerminatorKind.goto` and `@TerminatorKind.goto` no longer hide CFG edges, and a fully-qualified `assume` is no longer mistaken for `copyNonOverlapping`.
6. **`hasCfgCycle` was exponential and unverified** *(B1, replaced)*: A0's `canReachInSteps` expanded an undeduplicated frontier (`List.flatMap`), exponential on chains of diamonds, and had no correctness theorem. B1 replaces it with `isCfgDag` (polynomial, sound for **any** rank via `no_cfg_cycle_of_hasRankViolation_false`).
7. **Full `cargo test -p cargo-anneal` exits `101` on `BASE_SHA` too** *(B1 receipt)*: `tests/end_to_end_demo_journeys.rs` fails in `examples/wireframe-demo` (`checksum_frame_safe.lean:255:10` invalid `⟨...⟩`, `clamp_payload_window.lean:30:0` and `frame_total_len.lean:66:9` `whnf` heartbeat timeouts). B1 swapped in the `BASE_SHA` `scaffold.rs`, re-ran the test, observed the **identical four errors**, and restored the file. The failure is independent of this prototype (consistent with A0's `disableLocalBorrows` / `dsimp only` diagnosis); `cargo test` stops at this first failing integration binary, so later integration binaries are not exercised by the receipt command.
8. **`&'static str` constants land in `intrinsic_copy`**: every `ConstValue.slice (ConstScalar.ptr ..)` (string/slice literal) reads a global allocation, so trivial marker bodies (`__ANNEAL_MODEL_*`, `__ANNEAL_EXT_SPEC_TARGET_*`: `_0 = const "..."; return`) classify as `intrinsic_copy` (4 of 64 real bodies). Episode 1 should decide whether read-only global slices deserve a cheaper treatment.
9. **Smaller parity fixes** *(B1)*: `MirFragment::from_str` no longer trims whitespace (exact parity with Lean `fromStr?`, `#guard MirFragment.fromStr? " pure_loop_free" == none`); `MirFragment::default()` and Lean `Inhabited` are now the fail-closed `FullMir` / `.fullMir` (an unanalyzed `MirLiftingProfile::default()` previously claimed `pure_loop_free`); `is_pure_call_free_candidate()` now provably agrees with `fragment_classification().is_pure_mir()` on every test fixture.
10. **Audit-tool scope**: `anneal-lsp audit-preview` checks the *last* theorem only, and its statement-isolation rule targets `Proof/` files. Theory theorems such as the brief-mandated `checkBodyFragment_pureBoundedLoop_eq_checkPureMir` legitimately mention `Anneal.PureMirExec.checkPureMir`; B1 therefore also ran `#print axioms` over **all** 168 theorems (summary in Section 1).

---

## 6. Empirical Fragment Classification

### 6.1 Real `rustc`-captured MIR (`trusted/rustc-capture` emitter output, 64 bodies)

Corpus: every `Mir/**/*.lean` module produced by the `cargo-anneal` integration tests on this capsule (`wireframe-demo`, multi-crate transitive-callee / external-spec fixtures with `core` callees) plus `examples/tutor-ch1`. Lean ground truth = `#eval inferMinFragment` / `hasCfgBackedge` / `isCfgDag` / `checkPureMir`; Rust = `classify_mir_fragment` (opt-in harness `mir_fragment_parity_corpus_dump`).

| Crate group | Bodies | `pure_loop_free` | `pure_bounded_loop` | `tree_borrows_local` | `intrinsic_copy` | `full_mir` | Lean ↔ Rust mismatches |
|---|---|---|---|---|---|---|---|
| `WireframeDemo` | 21 | 10 | 0 | 10 | 1 | 0 | 0 |
| `Core` callees | 20 | 3 | 0 | 11 | 0 | 6 | 0 |
| `CrateA` | 12 | 1 | 0 | 0 | 3 | 8 | 0 |
| `CrateB` | 9 | 0 | 0 | 0 | 0 | 9 | 0 |
| `FrameTutor` (`examples/tutor-ch1`) | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| **Total** | **64** | **16** | **0** | **21** | **4** | **23** | **0** |

Notable rows: `wireframe_demo::{clamp_payload_window, frame_total_len, decode_wire_header}` are `pure_loop_free` (`checkPureMir = true`, 4 / 2 / 10 blocks); `checksum_frame_safe` (12 blocks) is `tree_borrows_local` with the corpus's only genuine loop (`isCfgDag = false`); `checksum_frame_fast` (20 blocks) is `tree_borrows_local` and loop-free; `PartialOrd::{le,lt}` / `RangeBounds::contains` are `full_mir` with acyclic index back-edges (Finding 5.2).

### 6.2 Hand-written fixtures (`examples/mir/MirVerification.lean`)

Lean `inferMinFragment` re-verified in B1 for 12 of A0's rows (helpers + bodies extracted verbatim): `addU32UncheckedMirBody`, `eq42BoolSpecMirBody`, `branchObsMirBody`, `calleeAddOneMirBody`, `returnStubMirBody` → `pure_loop_free`; `countdownMirBody`, `infiniteLoopMirBody` → `pure_bounded_loop` (genuine loops, `isCfgDag = false`); `reborrowWriteMirBody`, `aliasingViolationMirBody`, `unalignSetMirBody` → `tree_borrows_local`; `ffiDoubleCallMirBody`, `callerAddTwoMirBody` → `full_mir`. *(B1 correction)*: A0's table attributed these values to `classify_mir_fragment` as well, but these bodies are built with `mkMirBody` / `mkTerm` / `mkStmt` helpers and contain no `basicBlocks :=` literal, so the Rust scanner returns the fail-closed `full_mir` for them — by design, `classify_mir_fragment` targets emitter output (Section 6.1).

### 6.3 Differential fuzzing (Lean ground truth vs. Rust, 1,400 random bodies)

Generator: random `CapturedMir` ASTs over **every** `MirAst` constructor (all 26 `BinOp`s, 11 `CastKind`s, 15 `Rvalue`s, 12 `StatementKind`s, 11 `TerminatorKind`s, 4 `UnwindAction`s, out-of-range targets, `u128::MAX` switch values), rendered both in emitter syntax (`List.cons`, fully qualified) and dot-shorthand syntax, with adversarial comments / string literals containing constructor names and `CapturedMir` field keywords.

| Run | Bodies | Syntax variants | Fragment mismatches (A0 → B1) | Fail-open (Rust < Lean) |
|---|---|---|---|---|
| seed 7 | 600 | 300 emitter + 300 shorthand | **49 → 0** | 0 |
| seed 11 | 800 | 571 inline + 96 fully-qualified (`Trusted.Rustc.V2026_06_01.MirAst.*`) + 133 helper-`def` terminators | **0** on all 667 inline bodies; 106 helper bodies over-approximated to `full_mir` (fail-closed by design) | **0** |

Lean level distribution of seed 11: 104 `pure_loop_free`, 267 `pure_bounded_loop`, 209 `tree_borrows_local`, 96 `intrinsic_copy`, 124 `full_mir`. Back-edge flags and block counts agree on every inline body.

---

## 7. Integration Plan for `ws-mir-fragment-lattice-unstable` (GO / `P1`)

1. **Episode 1 (`ep1-mir-fragment-lattice-lean` on `unstable`)**:
   - Promote `theory/Anneal/MirFragmentPrototype.lean` to `theory/Anneal/MirFragment.lean`, export it from `theory/Anneal.lean`, and update the `include_str!` path in `mir_fragment_rust_classifier_matches_lean_witness_theorems`.
   - Use `checkBodyFragment_pureLoopFree_eq` / `inferMinFragment_eq_pureLoopFree_iff` as the `#mir_lift` precondition and emit a fragment diagnostic whenever `inferMinFragment` exceeds `.pureLoopFree`.
   - Decide explicitly between the sound-but-conservative index rule and `isCfgDag` for `.pureLoopFree` (Finding 5.2), and change Lean and Rust together.
2. **Episode 2 (`ep2-cargo-anneal-fragment-certificates` on `unstable`)**:
   - Wire `classify_mir_fragment`, `render_mir_fragment_diagnostic`, and `compute_prototype_fragment_spec_digest` into `.anneal/generated/Obligations/<Item>.lean` (`def fragment : MirFragment := ...` + `theorem fragment_sound : checkBodyFragment fragment Mir.<Item>.body = true := by rfl`) and `.anneal/spec-lock.json` (`mir_fragment` + `spec_digest`), mirroring Zircon 2.1 cl/1016618663. The `rfl` certificate makes Lean the arbiter, so a Rust misclassification can only cost a failed build, never a wrong certificate.
   - Keep the fail-closed vocabulary validator and run the differential harness (`ANNEAL_MIR_FRAGMENT_CORPUS_DIR=<dir> cargo test -p cargo-anneal --lib mir_fragment_parity_corpus_dump -- --ignored`) against freshly captured MIR in CI.
   - Surface `render_mir_fragment_diagnostic` in `cargo anneal agent-context` whenever an item crosses `pure_bounded_loop`.
