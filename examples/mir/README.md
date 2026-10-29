# Worked MIR Verification Slices (`examples/mir/`)

[`MirVerification.lean`](MirVerification.lean) contains self-contained,
kernel-checked vertical slices of Rust `Runtime(PostCleanup)` MIR verification in
Lean 4 over `ITree MirEffect MirOutcome`, connecting raw `CapturedMir`
(`Trusted.Rustc.V2026_06_01.MirAst`) and coalgebraic `mirStatefulTree` /
`mirHandledTree` (`Trusted.Rustc.V2026_06_01.MirSemantics`) through open-effect
Dijkstra predicate transformers (`Anneal.EffectWP`, `Anneal.ITreeWP`, and
`Anneal.Rustc.V2026_06_01.Lower`) to all five trusted claim gates in
`Trusted.VerificationResult`.

Keeping these worked `CapturedMir` and `LayoutTable` fixtures in
`examples/mir/MirVerification.lean` separates example test data from the
reusable abstractions in `theory/Anneal/`.

## Worked Vertical Slices in `MirVerification.lean`

| Slice | Theorems | Verified Construct / Property | Layer Coverage |
| --- | --- | --- | --- |
| 1. Arithmetic & Overflow UB | `example_add_u32_safe_verified`, `example_add_u32_total_verified`, `example_overflow_add_u32_refuted` | Checked `u32` addition (`x + 1` under `x < 100`) proved for both partial (`VerificationResult`) and total (`TotalVerificationResult`) correctness, plus negative refutation `¬ overflowAddU32Claim.holds` at `u32::MAX` | `MirSemantics` -> `wpMirBounded` / `wpMirTotalBounded` -> `VerificationResult` & `TotalVerificationResult` |
| 2. Companion Boolean Contract | `example_companion_bool_spec_holds` | Rust boolean contract companion (`x == 42`) discharging `MirBoolPredicateHolds` | `mirBoolPredicateHolds_of_bounded` |
| 3. Observation Trace (`TraceClaim`) | `example_branch_obs_trace_verified` | Conditional `switchInt` branch verified against an explicit `List MirObs` observation trace contract | `mirTraceWP` -> `wpMirTraceBounded` -> `TraceVerificationResult` |
| 4. Tree Borrows Reborrowing vs. Aliasing UB | `example_reborrow_write_stateful_verified`, `example_aliasing_violation_refuted` | Mutable reference reborrowing (`&mut _1` -> `&mut *_2` -> write -> read) verified via `StatefulVerificationResult`, paired with refutation `¬ aliasingViolationClaim.holds` when writing through parent `_2` freezes child `_3` and a subsequent child read faults with `.ub` | `MirSemantics` (Tree Borrows) -> `verifyStatefulMirBounded` |
| 5. Loops: Bounded `DWP` vs. Coinductive `DWLP` & `Diverges` | `example_countdown_loop_total_verified`, `example_infinite_loop_partial_but_not_total` | Bounded countdown loop verified for total correctness (`TotalVerificationResult`), contrasted with `loop {}` satisfying `VerificationResult` via `DWLP.coinduct` while failing `TotalClaim` via `Diverges.coinduct` (`MayDiverge.of_diverges`) | `DWLP.coinduct`, `Diverges.coinduct`, `TotalVerificationResult` |
| 6. Impure-by-Default FFI, Modular Contracts & Horizontal Linking | `example_impure_ffi_double_call_refuted`, `example_pure_const_ffi_modular_verified`, `example_horizontal_caller_callee_linking` | Refutes `ext(0) == ext(0)` under unconstrained `MirCallE` (`¬ impureFfiDoubleCallClaim.holds`), verifies the caller under `ModularVerificationResult` against an explicit `CalleeContractSpec`, and horizontally links a verified MIR callee via `linkVerifiedMirCallee` (`WeakRef`) | `MirCallE`, `ModularVerificationResult`, `ITree.interp`, `linkVerifiedMirCallee` |
| 7. Unified `PartialHeap` Separation-Logic Framing | `example_unalign_set_stateful_verified`, `example_unalign_set_framed_preserved`, `example_partial_heap_exclusivity` | Verifies `Unalign<u16>::set` writing 2 bytes into `_1` via `copyNonOverlapping`, frames an arbitrary disjoint `PartialHeap` predicate `R` across the call via `statefulVerificationResult_frame_disjoint`, and proves `PointsToSep` exclusivity via `PartialHeap` disjointness | `Anneal.SepLogic` (`PartialHeap`, `SepProp`, `statefulVerificationResult_frame_disjoint`) |
| 8. Layout Certificate Checkers & Unsafe Pointer/Slice Obligations | `example_layout_certificate_checkers`, `example_unsafe_pointer_and_slice_obligations` | 1-line `rfl` verification of `Unaligned`, `FromZeros`, `FromBytes`, and `IntoBytes` for `#[repr(C)] PacketHeader([u8; 2], u16)` and `Unalign<u32>`, plus constructive raw-pointer alignment/in-bounds and `split_at_unchecked` disjointness obligations | `Anneal.BitValidity` + `Anneal.UnsafeObligations` |
