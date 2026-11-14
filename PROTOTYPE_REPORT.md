# PROTOTYPE_REPORT — `ws-proto-tcb-correspondence-div8-and-ieee-float` (`ep1-proto-div8-and-ieee-float`)

> [!IMPORTANT]
> **Prototype-only** (`track = "prototype"`, `merge_policy = "no_merge_prototype"`).
> Nothing under `trusted/**`, `lakefile.toml`, `minirust/**`, or `lean-miri/**` is modified.
> All semantics live in the overlay `theory/Anneal/TcbCorrespondenceDiv8AndFloatPrototype.lean`;
> the regression/audit suite is `scripts/test_tcb_correspondence_div8_proto.py`.

Status: **A3 critique & fix pass** (draft recommendation in §7, finalized in round A4). All
declarations of the overlay (including all 106 pinned headline theorems) are kernel-checked with axioms `⊆ {propext, Quot.sound}` — zero
`Classical.choice`, zero `sorry`, zero `native_decide` (see §5). The overlay is differentially
tested against the unpatched `Trusted` stepper on all 235 MiniRust witness bodies × 3 argument
vectors (705 runs), and its definite agreement on all 138 scalar-argument bodies (`114`
single-function + `24` multi-function callers) plus `33` composite-argument bodies (`171` bodies in
total) is proved in the Lean kernel (§2b).

## 1. What was built

### Part A — frame-qualified, Tree-Borrows-faithful operational overlay

`ProtoBorrowEntry` = `BorrowEntry` + `targetFrameDepth : Nat := 0` (depth of the frame owning
`targetLocal`; `0` = root, `currentFrameDepth s = s.memory.callStack.length` = active frame;
depth `d < currentFrameDepth` lives at `callStack[currentFrameDepth - 1 - d]`).
The interpreter `evalOperandProto` / `evalRvalueProto` / `evalStmtProto` /
`evalTerminatorProto` / `stepMirFnProto` / `runMirProto` executes the *real*
`Trusted.Rustc.V2026_06_01.MirAst` bodies (including the unmodified `MiniRustSpec`
witness bodies) and reuses the unmodified `Trusted` helpers (`treeBorrowNodeAccess`,
`projectionsOverlap`, `readProjectedValue`, `writeProjectedValue`, `evalScalarBinOp`,
`evalBinOpOffset`, `sharedBorrowPerm`, `mutableBorrowPerm`, `retagPerm`, `initLocals`, …).
Unmodeled constructs fail closed with `.unsupported`.

Besides the constructs needed by the eight items, the overlay executes (A1, mirroring
`Trusted.evalRvalue` / `Trusted.evalStmt`): `UnOp.{Not, Neg}` (`evalUnaryNot`),
`CopyForDeref`, `Repeat`, `WrapUnsafeBinder`, array / closure aggregates, `IntToInt` casts,
thin `PtrToPtr` casts, the layout-aware `Discriminant` (`evalPlaceDiscriminant`: single-variant
layouts, variant bounds, `core::cmp::Ordering`), `Deinit`, `PlaceMention`
(`placeMentionOperandsInit`), `Assume`, and `BackwardIncompatibleDropHint`. A safe reference
`&*p` through a pointer with a non-zero byte offset fails closed (the overlay has no
sub-local addresses, so it cannot check alignment: `RefWitness.misalignedRef`).

### Part B — pure `BitVec 32` / `BitVec 64` IEEE-754 casts

`F32Bits := BitVec 32`, `F64Bits := BitVec 64`, `FloatComponents`, `FloatKind`,
`unpackBits` / `packBits`, exact rational `decodeBits` (proved equal to a literal
transliteration of `Miri.Interpreter.FloatBits.decode`), `roundQuotientTiesToEven`,
`roundRatioBits` / `roundRatioTiesToEven` (transliteration of
`Miri.Interpreter.FloatBits.roundRatio`), and
`evalFloatToIntSaturating`, `evalIntToFloatRoundTiesToEven`,
`evalFloatToFloatRoundTiesToEven` (+ `f32ToF64` / `f64ToF32`), wired into
`evalRvalueProto` for `CastKind.{floatToInt, intToFloat, floatToFloat}`.

## 2. The eight tracked divergences (`TRACKED_CORRESPONDENCE_DIVERGENCES`)

| ID | Severity | Unpatched baseline (theorem) | Repaired agreement (theorem) | Canaries |
|----|----------|------------------------------|------------------------------|----------|
| `DIV-MR-CALL-TARGET-LOCAL` | P0_soundness | `div_mr_call_target_local_trusted_baseline` / `_trusted_137` (Trusted returns **137**) | `div_mr_call_target_local_repaired_agrees` (`.ok 42`, 3-way with `Mach` / `MachTB`) | `div_mr_call_target_local_write_back_canary` (caller `_1`: 5→42, callee `_1 = 100` untouched; Trusted returns 5137), `div_mr_call_target_local_reborrow_in_callee_canary` (`&mut *_2` + `Retag` inside callee), `reborrow_inherits_targetFrameDepth` (universal), `writePlaceProto_frame_local_isolation` (universal cross-frame local-slot isolation), `div_mr_call_ref_mut_protected_roundtrip_agrees` (`.ok 84` on `callerRefMutProtectedMir`, = `Mach`/`MachTB`) |
| `DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL` | P1_false_positive_ub | `div_mr_caller_borrow_across_scalar_call_trusted_ub` | `div_mr_caller_borrow_across_scalar_call_repaired_agrees` (`.ok 42`, 3-way) | `div_mr_caller_borrow_frame_isolation`, `writePlaceProto_direct_frame_isolation`, `writePlaceProto_deref_frame_isolation`, `readPlaceProto_and_stmt_borrow_frame_isolation` (universal across reads, writes, `StorageLive`/`StorageDead`, and `SetDiscriminant`), `updateBorrowPermAtProjProto_other_frame`, `entryAccessTransitionProto_other_frame` |
| `DIV-MR-TB-TWOPHASE-DIRECT-WRITE` | P1_soundness | already UB in `LM-3.3` `Trusted` (`twoPhaseDirectWriteTreeBorrowsGap_anneal_ub`) | `div_mr_tb_twophase_direct_write_repaired_agrees` (`.ub`, = `MachTB`, = `Trusted`) | pre-`LM-3.3` model `preserveReservedOnDirectWrite` returns 99; `direct_write_disables_reservedFrz_preserves_cell_and_reservedIM` (universal); `div_mr_tb_twophase_direct_write_reservedIM_and_cell_survive_canary` (`.ok 88`) |
| `DIV-MR-TB-FNENTRY-LOCAL-DEALLOC` | P1_soundness | `div_mr_tb_fnentry_local_dealloc_trusted_ret` (Trusted returns 5) | `div_mr_tb_fnentry_local_dealloc_repaired_agrees` (`.ub` at root `Return`, = `MachTB`) | `_ub_at_return` (fault is exactly the terminator), `_callee_return_canary` (callee-frame `Return` faults; Trusted returns 5), `disableFrameBorrowsProto_frame_isolation` (universal), `div_mr_tb_fnentry_dangling_callee_raw_ptr_return_ub` (dangling callee raw pointer deref faults; Trusted returns 5), `div_mr_return_destination_invalidation_and_protector_canary` (`Return` write to `caller.destination` invalidates caller borrows and checks `caller.savedProtectors`) |
| `DIV-MR-TB-UNSAFECELL-PROTECTED-IM` | P2_false_positive_ub | `Trusted.hasProtectedLocalBorrow` reports `true` (`div_mr_tb_unsafecell_storage_dead_canary`) | `div_mr_tb_unsafecell_protected_im_repaired_agrees` (`.ok 77`, = `Mach`/`MachTB`) | `div_mr_tb_unsafecell_coupling_legacy_breaks` (legacy rule ⇒ UB at `Return`), StorageDead canary (`.ok 5`), `hasProtectedLocalBorrowProto_cell_exempt_reservedIM_blocks` (universal `.cell` vs `.reservedIM`), `hasProtectedLocalBorrowProto_of_hasProtectedWriteConflictProto`, `hasProtectedLocalBorrowProto_disableLocalBorrowsProto` (downstream TCB compatibility) |
| `DIV-LM-RAW-OVERWRITE-CHAR-COPY` | P1_soundness | `div_lm_raw_overwrite_char_copy_trusted_steps` (Trusted copies/moves and returns surrogate `0xD800`) | `div_lm_raw_overwrite_char_copy_repaired_ub` (`.ub` on `0xD800`, `0xDFFF`, `0x110000`, copy and move) | `_ub_at_load`, `_valid_accepted` (`0x41`, `0xD7FF`, `0xE000`, `0x10FFFF` for both copy & move), `div_lm_raw_overwrite_char_projected_move_canary` (`move (*_3)`), `validateLoadedValueProto_char_eq_miri` (universal), `isValidCharCode_iff_isValidChar` |
| `DIV-LM-D6-OFFSET-DISABLED-TAG` | P2_false_positive_ub | `div_lm_d6_offset_disabled_trusted_ub`, `div_lm_d6_offset_trusted_evalPtrOffsetBinOp` | `div_lm_d6_offset_disabled_tag_repaired_agrees` (universal live-allocation lockstep) & `div_lm_d6_offset_dead_alloc_lockstep_miri` (universal dead-allocation lockstep at any `offsetBytes < 2^63`) | `div_lm_d6_offset_disabled_deref_canary`, `disabled_tag_deref_and_reborrow_ub` (universal across deref read/write/reborrow at any offset), `disableLocalBorrowsProto_and_disableFrameBorrowsProto_revival_sound` (universal post-deallocation & `StorageLive` revival UB across deref read/write/reborrow/non-zero offset), `div_lm_d6_wit_lm3_1_four_witnesses_and_revive_canary` (all 4 `WitLM3_1` D6 disabled-tag bodies including `lm31OffsetDisabledDeadZeroBody` + `StorageDead`+`StorageLive` revival offset UB/ok), `evalBinOpOffset_lockstep_miri` |
| `DIV-LM-ENUM-SET-DISCR-UNINIT` | P2_precision | `div_lm_enum_set_discr_trusted_uninit_ub` (universal), `_trusted_faults` | `div_lm_enum_set_discr_uninit_repaired_agrees` (universal lockstep with `miriWriteDiscriminant` over `.uninit` / `.init (.aggregate _ _)` / `.dead`) | `_observed` (`Rvalue.discriminant` sees the variant), `_payload_canary` (payload read is UB), `_dead_and_init`, `div_lm_enum_set_discr_protected_conflict_ub` (universal), `div_lm_enum_set_discr_borrow_invalidation_and_protector_canary` |

### Coupled findings

* `DIV-MR-TB-TWOPHASE-DIRECT-WRITE` is **already resolved** in `Trusted.MirSemantics.Places`
  (`LM-3.3`: `updateBorrowPerm` with `writerTag = .none` disables an unprotected
  `.reservedFrz`). Track A closes the tracker item by retiring/updating
  `twoPhaseDirectWriteTreeBorrowsGap` in `minirust/lean/MiniRustSpec/Correspondence/RefWitness.lean`
  and its entry in `scripts/run_nightly_verification_suite.py` — while still adding
  `targetFrameDepth` scoping to `updateBorrowPerm`.
* `DIV-MR-TB-FNENTRY-LOCAL-DEALLOC` + `DIV-MR-TB-UNSAFECELL-PROTECTED-IM` are **coupled** through the
  deallocation rule: adding the `Return` protector check (#4) with the unpatched
  "every protected tag blocks" rule of `Trusted.hasProtectedLocalBorrow` breaks
  `unsafeCellProtectedInteriorMut` (proved: `div_mr_tb_unsafecell_coupling_legacy_breaks`).
  Both must land together with `preventsDeallocation` (`.cell` / `.disabled` exempt), which is
  proved equal to `MiniRustSpec.Interp.PermissionProt.prevents_deallocation`
  (`preventsDeallocation_eq_miniRust`).
* `Trusted.hasProtectedWriteConflict` already exempts a protected `.cell` from foreign
  writes (that is why `unsafeCellProtectedInteriorMut` already returns 77 in `Trusted`); the
  remaining false positive is in `hasProtectedLocalBorrow` (`StorageDead` / `StorageLive`).
* **Additional Track A soundness & correspondence gaps uncovered in B1 and B2**:
  1. `Trusted.evalStmt` on `.setDiscriminant ⟨loc, .nil⟩ variantIdx` (`Statements.lean:3359-3364`)
     omits *both* `hasProtectedWriteConflict` and `invalidateConflictingBorrows` even when
     `locals[loc] = .some (.init (.aggregate _ fields))`! Thus Track A must add the
     frame-scoped protector check and borrow invalidation to **both** the `.uninit` and
     `.init (.aggregate _ fields)` branches (proved in
     `div_lm_enum_set_discr_borrow_invalidation_and_protector_canary`).
  2. `Trusted.evalTerminator` on `.return_` (`Terminators.lean:3006-3039`) does not disable
     borrows targeting the returning frame's locals (`disableFrameBorrowsProto`), allowing a
     returned raw pointer to a callee local to alias a caller local after return (proved in
     `div_mr_tb_fnentry_dangling_callee_raw_ptr_return_ub`). Track A must run both
     `hasFrameDeallocProtectorConflict` and `disableFrameBorrows` before popping the frame /
     restoring caller protectors.
  3. **(Uncovered in B2)** `Trusted.evalTerminator` on `.return_` (`Terminators.lean:3015`)
     writes `retVal` to `caller.destination` via `writePlaceValue`, which returns only
     `List LocalSlot` and **omits both `hasProtectedWriteConflict` (against
     `caller.savedProtectors`) and `invalidateConflictingBorrows` on `caller.destination`**!
     In `evalReturnProto`, `writePlaceProto` runs after restoring `caller.savedProtectors`,
     enforcing both checks (proved in
     `div_mr_return_destination_invalidation_and_protector_canary`).
  4. **(Uncovered in B2)** In `DIV-LM-D6-OFFSET-DISABLED-TAG` vs `D2` storage revival
     (`L5_ControlAndCalls.lean:5342` `stmt_div_storage_revive_ptr_offset_is_ub` and
     `WitLM3_1.lean:10067` `lm31OffsetDisabledDeadZeroBody`): simply dropping the `.disabled`
     check in `ptrAllocByteBound?` (`Places.lean:15023`) is **unsound** when a local is
     deallocated by `StorageDead(loc)` and revived by `StorageLive(loc)` (it would make stale
     pointers minted before `StorageDead(loc)` see the revived allocation's byte bound and
     allow non-zero `BinOp.offset`, breaking `stmt_div_storage_revive_ptr_offset_is_ub`), AND
     still fails on `WitLM3_1.lm31OffsetDisabledDeadZeroBody` (`Offset(copy _3, 0_usize)` at
     `offsetBytes = 8` after `StorageDead(_1)`) because `evalBinOpOffset` (`Places.lean:15445`)
     gated zero-delta offsets at `offsetBytes > bound = 0` on `ptrVal.allocId == 0`!
     Adding `allocDead : Bool := false` to `BorrowEntry` (set on `StorageDead`/`StorageLive`/
     `Return`, preserved on foreign writes) and allowing zero-delta offsets at any
     `offsetBytes < 2^63` regardless of `allocId` resolves both (proved in
     `div_lm_d6_offset_dead_alloc_lockstep_miri` and
     `div_lm_d6_wit_lm3_1_four_witnesses_and_revive_canary`).

## 2b. Corpus differential: overlay vs. unpatched `Trusted` (235 MiniRust witness bodies)

`CorpusDifferentialTests` runs `runMirProto` and the unpatched `Trusted` stepper (`runA` /
`faultsA`) on every `def _ : CapturedMir` of `Witness`, `PointerWitness`, `RefWitness`,
`TbWitness`, and `ProvenanceWitness` (all corpus bodies as callees) under three scalar
argument vectors — small positive (`5`, `true`, `'A'`), all-zero bits, and all-one bits
(`-1` / `MAX`, `char::MAX`) — 705 runs in total, and pins every outcome class. Default
vector shown; the all-zero / all-one vectors give 139 + 10 and 133 + 16 identical outcomes
with exactly the same 7 divergent bodies (values pinned per vector in
`EXPECTED_CORPUS_DIVERGENCES`) and the same 30 fail-closed bodies:

| Outcome | Bodies |
|---------|--------|
| identical outcome (value / UB / both indefinite) | 138 + 11 |
| definite divergence, overlay = MiniRust ground truth | 7 |
| overlay fails closed, `Trusted` definite (`FAIL_CLOSED_CORPUS`) | 30 |
| skipped (non-scalar arguments) | 49 |

The 7 definite divergences (`EXPECTED_CORPUS_DIVERGENCES`):
`callerRefMutSilentWrongLocalMir` (42 vs 137) and `callerBorrowAcrossScalarCallMir` (42 vs
UB) — tracked items 1–2; **`callerRefMutProtectedMir` (84 vs UB; `Mach`/`MachTB` = 84 by
`callRefMutProtectedRoundTrip_mach_and_tb`, proved in
`div_mr_call_ref_mut_protected_roundtrip_agrees`)** — a further instance of the
`DIV-MR-CALL-TARGET-LOCAL` frame bug not listed in the tracker (note that its companion
`callerRefMutProtectedBadCallDstMir` is an out-of-fragment syntactic counterexample with
`progCrossFrameTranslatable = false` in `ProvenanceWitness.lean:1436`, where MiniRust's
`prepareForInplacePassingM` deinitializes `destination = _1` at `Call` entry while
`Terminators.lean` writes `destination` only at `Return`); `retagFnEntryLocalDeallocUb` (UB
vs 5) — tracked item 4; and two out-of-fragment `Trusted` divergences that the overlay
fixes: `argCountMismatchCaller` (UB vs 5; `argCountMismatch_minirust_ub`) and
`uninitProjCallDestCaller` (251 vs UB; `uninitProjCallDest_minirust_ret`). The 30
fail-closed bodies are exactly the unmodeled exposed-provenance / int-to-pointer casts (19),
`transmute` (8), array-element `PtrToPtr` re-derivation (1), and sub-local byte offsets (2).
No body yields a definite overlay result where `Trusted` is indefinite.

**Kernel-checked:** `corpusAgreesWith` explicitly rejects `.indefinite` in Lean (`(p != .indefinite)`),
`corpus_agreement_kernel` proves by `decide +kernel` that the overlay and the unpatched `Trusted`
stepper produce the same definite outcome (same pointer-abstracted value, or UB) on all 114
single-function corpus bodies (`corpusAgreementBodies`), `corpus_multifn_agreement_kernel` proves
the same on all **24 multi-function caller bodies** (`corpusMultiFnAgreementBodies`, covering
100% of the `114 + 24 = 138` definite-agreement scalar-argument bodies, verified by exact set
equality in `test_kernel_agreement_list_consistent`), and `corpus_composite_agreement_kernel`
proves the same on **33 composite-argument bodies** (`Tuple`, `Array`, `PaddedStruct`,
`UnsafeCell<u32>`, `core::cmp::Ordering`, bringing total kernel-checked corpus agreement to
**171 bodies**); `overlay_coverage_canaries` pins 15 representative values / UB verdicts;
`corpus_out_of_fragment_fixes` re-proves the `argCountMismatchCaller` /
`uninitProjCallDestCaller` fixes with their callees; the frame-bug divergences are headline
theorems (items 1–2, `div_mr_call_ref_mut_protected_roundtrip_agrees`).

## 3. Track A edit plan (draft)

| File | Edit |
|------|------|
| `trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/State.lean` (`BorrowEntry`) | add `targetFrameDepth : Nat := 0` and `allocDead : Bool := false` |
| `…/MirSemantics/Places.lean` (`updateBorrowPerm`, `invalidateConflictingBorrows`, `updateBorrowPermAtProj`, `invalidateConflictingBorrowsAtProj`, `hasProtectedWriteConflict`, tree read/write helpers) | scope every entry test to `(targetFrameDepth, targetLocal)` |
| `…/MirSemantics/Places.lean` (`evalRvalue .ref` / `evalRvalueRawPtr`, `evalRvalueRefDeref`) | stamp `targetFrameDepth := callStack.length`; reborrows inherit the parent's `(targetFrameDepth, targetLocal)` |
| `…/MirSemantics/Places.lean` (deref reads / writes, `evalPlaceWrite`, `evalOperand`) | route through frame-qualified local access (`readFrameLocalProto` / `writeFrameLocalProto`) |
| `…/MirSemantics/Places.lean:16331` (`validateLoadedValue`) | add `.char` case `sizeBytes == 4 && isValidCharCode bits` |
| `…/MirSemantics/Places.lean:15023,15445,15468` (`ptrAllocByteBound?`, `evalBinOpOffset`, `evalPtrOffsetBinOp`) | in `evalPtrOffsetBinOp`, drop `borrowDisabled`; in `ptrAllocByteBound?`, check `entry.allocDead` (instead of `entry.perm == .disabled`) and frame-qualified target local liveness; in `evalBinOpOffset`, drop `Nat.beq ptrVal.allocId 0` on the zero-delta (`newOffset == ptrVal.offsetBytes`) branch so zero-count offsets on dead locals at `offsetBytes > 0` (`WitLM3_1.lm31OffsetDisabledDeadZeroBody`) succeed while non-zero offsets after `StorageDead`+`StorageLive` revival (`L5_ControlAndCalls.stmt_div_storage_revive_ptr_offset_is_ub`) still fault with `.ub` |
| `…/MirSemantics/Statements.lean:1842` (`hasProtectedLocalBorrow`), `disableLocalBorrows` | frame scoping + `preventsDeallocation` exemption; `disableLocalBorrows` sets `allocDead := true` |
| `…/MirSemantics/Statements.lean` (`evalStmt .setDiscriminant`) | `.uninit` ⇒ `.init (.aggregate v [])` with protector check + invalidation; `.init (.aggregate _ fs)` keeps `fs` with protector check + invalidation |
| `…/MirSemantics/Statements.lean` (`evalFnEntryRetag`, `evalNonFnEntryRetag`) | children inherit `targetFrameDepth` |
| `…/MirSemantics/Terminators.lean` (`evalTerminator .return_`) | `hasFrameDeallocProtectorConflict` over the returning frame's locals, disable its borrows (`allocDead := true`), restore `caller.savedProtectors`, and write `retVal` to `caller.destination` with `hasProtectedWriteConflict` + `invalidateConflictingBorrows` — in both root and callee return |
| `…/MirSemantics/Places.lean` (`evalRvalue .cast`) | `CastKind.{floatToInt, intToFloat, floatToFloat}` via the Part B functions |
| `V2026_08_01` mirror of every edit above | same |
| Downstream (`DIV-LM-RAW-OVERWRITE-CHAR-COPY`) | `SimLM2_1.lean` (`WellTypedLM2_1ScalarOperand.validateLoadedValue_true`), `SimLM2_4.lean` (`validateLoadedValue_unionField_true`), `SymReflect.lean` (symbolic `.char` arguments), `MiniRustSpec/Correspondence/AnnealEval.lean` |
| Downstream (`L5_ControlAndCalls.lean` & `Statements.lean` storage lemmas) | `Statements.lean:1945` (`hasProtectedLocalBorrow_of_hasProtectedWriteConflict`) continues to hold via `hasProtectedLocalBorrowProto_of_hasProtectedWriteConflictProto`; `Statements.lean:3752` (`evalStmt_storageRevive_old_ptr_deref_ub`) and `L5_ControlAndCalls.lean:5342` (`stmt_div_storage_revive_ptr_offset_is_ub`) continue to hold via `disableLocalBorrowsProto_and_disableFrameBorrowsProto_revival_sound`; in `theory/Correspondence/V2026_{06,08}_01/L5_ControlAndCalls.lean:278,443` (`hasProtectedLocalBorrow_disableLocalBorrows`), add `(d₁, loc₁) ≠ (d₂, loc₂) ∨ hasProtectedLocalBorrow ... d₁ loc₁ = false` per `hasProtectedLocalBorrowProto_disableLocalBorrowsProto` |
| `minirust/lean/MiniRustSpec/Correspondence/ProvenanceWitness.lean` | the frame fix also flips `callRefMutProtected_anneal_ret` (`Trusted` UB → 84 = `Mach`/`MachTB` in `callRefMutProtectedRoundTrip_three_way`); update that theorem together with items 1–2 (`callerRefMutProtectedBadCallDst_notInFragmentWithIntrinsics` is purely syntactic and needs no change) |
| `…/MirSemantics/Terminators.lean` (`Call` / `Return`) | as in the overlay: check the callee's arity at `Call` (MiniRust "call ABI violation", flips `argCountMismatch_*`) and write `_0` back with the general place write (uninit-field shell; flips `uninitProjCallDest_*`) — optional, outside the eight items |
| Tracker | retire the 8 IDs in `scripts/run_nightly_verification_suite.py` once the witnesses flip |

## 4. Part B specification summary

* `decodeBits` ≡ Miri `decode` (`decodeBits_agrees_miriDecode`, all in-width patterns).
* `evalFloatToIntSaturating`: NaN ↦ 0, ±∞ ↦ max/min, finite ↦ clamp(trunc); canonical
  two's-complement `ScalarInt` (`evalFloatToIntSaturating_sound`, `_nan`, `_canaries`), plus
  universal `IntToFloat → FloatToInt` exact round-trip on all representable integers (`|v| < 2^(fb+1)`)
  and unconditional `i32`/`u32 → f64 → i32`/`u32` left-inverse (`evalFloatToIntSaturating_roundtrip_of_intToFloat`).
* `evalIntToFloatRoundTiesToEven` (`evalIntToFloatRoundTiesToEven_sound` bundle):
  - Integer-quotient and **float-level** ≤ ½ ULP + even-LSB ties (`roundQuotientTiesToEven_half_ulp`,
    `_tie_even`, `roundRatioTiesToEven_float_half_ulp`), plus universal unreachability of the
    `inconsistentRounding` (`preferredNaNBits`) branches (`roundRatioBits_valid_and_not_nan`);
  - Exact on every integer with `|v| < 2^(fb+1)` (`evalIntToFloatRoundTiesToEven_exact`), hence
    every `i32`/`u32` → `f64` (`evalIntToFloat_i32_u32_to_f64_exact`);
  - `u128::MAX → f32 = +∞` and the exact overflow threshold `2^128 − 2^103`
    (`evalIntToFloatRoundTiesToEven_canaries`).
* `b/585733184`: `b585733184_ties_to_even_separation` (`0.5↦0` vs `1`, `−0.5↦−0` vs `−1`,
  `2.5↦2` vs `3`, `3.5↦4`, `16777217→0x4B800000` vs `0x4B800001`, `16777219→0x4B800002`,
  `2^53+1→0x4340000000000000` vs `…01`).
* `evalFloatToFloatRoundTiesToEven` (`evalFloatToFloatRoundTiesToEven_sound` bundle): exact
  widening + round trip (`f32ToF64_exact_and_roundtrip`), universal quiet-NaN output
  (`convertFloatBits_nan_quiet`), signaling-NaN canary (`f64ToF32_signaling_nan_quietized`),
  subnormal/overflow/underflow/signed-zero canaries, and single-rounding vs double-rounding /
  subnormal-to-normal carry-out canaries (`f64ToF32_subnormal_and_double_rounding_canaries`).
* **Correct rounding, biconditional overflow & universal signed-zero preservation (A1 + B2)**:
  `roundRatioTiesToEven_correctly_rounded` pins the rounding quantum to the IEEE-754 ULP
  (`ratioExponent = ⌊log2 (n/d)⌋`; `2^fb ≤ scaled < 2^(fb+1)` in the normal range, subnormal
  quantum below it) on top of the ½-ULP / ties-to-even / exact-value statements of
  `roundRatioTiesToEven_float_half_ulp`; `roundRatioTiesToEven_overflow_iff` proves the
  **necessary and sufficient (`↔`)** condition for overflow to `±∞` (`f.maxExponent < exponent
  ∨ (exponent = f.maxExponent ∧ sig = 2^(fb+1))`); `roundRatioBits_sign_and_underflow_zero_preserved`
  proves universal sign preservation on `n = 0`, gradual underflow `sig = 0`, `.zero neg`,
  and `.inf neg` (plus negative-finite gradual underflow to `-0.0`,
  `0xB690_0000_0000_0000 ↦ 0x8000_0000`); both cast bundles state that every int→float cast
  and every finite float→float conversion *is* `roundRatioTiesToEven` of the exact source value.
* `CastKind` wiring: `castKind_end_to_end` (`runMirProto` on real `Rvalue.cast` bodies, every
  conjunct proved by `rfl`);
  unpatched `Trusted.evalRvalue` returns `.unsupported` (`castKind_trusted_unsupported`).

## 5. Axiom hygiene (zero `Classical.choice`)

* `#guard_msgs in #print axioms` pins all 106 headline theorems (§7 of the Lean file); the
  audit suite replays `#print axioms` for **every** `theorem` / `def` of the file.
* Lean `v4.34.1` core lemmas that silently pull `Classical.choice` and were replaced by
  constructive versions: `Nat.pow_lt_pow_right`, `Nat.pow_lt_pow_iff_right`,
  `Nat.mul_lt_mul_left/right`, `Nat.div_lt_of_lt_mul`, `Nat.log2_two_pow`,
  `Nat.add_eq_left` (simp), and `BEq.rfl` at `Nat` (simp; via `Nat.instLawfulEqOrd`).
  `omega` itself is classical whenever it must refute `¬(A ∧ B)` (conjunction / iff goals or
  such hypotheses: `Lean.Omega.Decidable.or_not_not_of_not_and` + `Classical.propDecidable`),
  so every `omega` call is fed atomic goals.
* **MiniRust ground truth.** `MiniRustSpec.Correspondence.translateProgWithIntrinsics` — and
  therefore `ProvenanceWitness.callerRefMutSilentWrongLocalMInit` / `TBInit`,
  `callerBorrowAcrossScalarCallMInit` / `TBInit`, and every upstream `*_divergence` theorem
  about them — depends on `Classical.choice` through exactly one leaf: core `String.toList`
  in `translateIntrinsicOrNone` (`match defPath.toList with ...`). The overlay builds the
  `Mach` / `MachTB` states with a verbatim replica whose only change is a `String`-equality
  intrinsic matcher (`translateProgWithIntrinsicsSF`); the suite replays the kernel-checked
  bridges `callerRefMutSilentWrongLocalMInitSF = ProvenanceWitness.callerRefMutSilentWrongLocalMInit
  := rfl` (and `Prog` / `TBInit` / `callerBorrowAcrossScalarCall*`) in its temporary harness.
  **Track A recommendation:** replace that `String.toList` match upstream so the MiniRust
  witnesses themselves become classical-free.

## 6. Known limitations of the prototype

* Fail-closed (`.unsupported`): globals / untracked provenance, exposed provenance and
  int-to-pointer casts, `transmute`, wide-pointer and array-element `PtrToPtr` casts, deref
  or `&*p` at a non-zero pointer offset, index/subslice borrow projections, unions
  (`Aggregate` with an active field), `Len`, unwinding, external calls, `f16` / `f128`
  (30 of the 235 corpus bodies; `FAIL_CLOSED_CORPUS`).
* **Tree Borrows gap shared with `Trusted` (not fixed, not introduced):** direct (non-deref)
  local accesses apply no Tree Borrows transition. `tb_direct_read_freeze_gap_shared_with_trusted`
  pins a concrete missed UB: `_2 = &mut _1; *_2 = 6; _3 = copy _1; *_2 = 7` — the direct read
  `copy _1` is a foreign read that freezes the active `_2`, so `MachTB` raises `"Tree Borrows:
  local write of Frozen reference"` while `Trusted` and the overlay both return `7`. It is not
  one of the eight tracked items and is not in `TRACKED_CORRESPONDENCE_DIVERGENCES`; Track A
  should file it as a new soundness item (`DIV-MR-TB-DIRECT-LOCAL-ACCESS`) rather than claim
  Tree Borrows completeness.
* Return values (`_0`) are not re-validated at `Return` (same as `Trusted`); a typed load of
  the caller's destination validates them later.
* No `rangeOffset` / `rangeLen` byte-ranged entries.
* *(Resolved in B1)*: Float-level ≤ ½ ULP + even-tie guarantees and unreachability of the
  `inconsistentRounding` (`preferredNaNBits`) branches of `roundRatioBits` are now proved
  universally in `roundRatioBits_valid_and_not_nan` and `roundRatioTiesToEven_float_half_ulp`.

## 7. Recommendation (A3 draft — finalized in A4)

**CONDITIONAL GO** for the Track A TCB update `ws-tcb-correspondence-div8-and-ieee-float`.

Evidence: all eight tracked divergences flip to agreement with their MiniRust / lean-miri
ground truth (§2); the overlay does not regress `Trusted` on the 235-body MiniRust witness
corpus under three argument vectors — every definite divergence is a fix with ground truth,
171 agreements are kernel theorems, and the 30 fail-closed bodies are exactly the unmodeled
construct families (§2b); Part B is pure, kernel-reducible, and proved correctly rounded with
exact overflow, signed-zero, quiet-NaN, exactness, and round-trip guarantees, and is
differentially tested against `fractions` / `struct` and a lean-miri `Float.lean` port (§4);
every declaration is classical-free (§5).

Conditions:
1. **Land Part A as one unit.** Items 1–2 need `targetFrameDepth` threaded through *every*
   borrow-table operation and frame-qualified deref access; item 4 (`Return` dealloc check)
   breaks `unsafeCellProtectedInteriorMut` without item 5 (`preventsDeallocation` exemption)
   (`div_mr_tb_unsafecell_coupling_legacy_breaks`); item 7 needs `allocDead` together with
   the frame-qualified liveness bound.
2. **Update the dependent proofs and witnesses listed in §3** (char-validation sites
   `SimLM2_1` / `SimLM2_4` / `SymReflect` / `AnnealEval`; `hasProtectedLocalBorrow` /
   `disableLocalBorrows` lemma hypotheses in `Statements.lean` and `L5_ControlAndCalls.lean`;
   the `ProvenanceWitness` / `RefWitness` statements that flip, including
   `callRefMutProtected_anneal_ret`), mirror every edit into `V2026_08_01`, and retire the eight
   IDs in `scripts/run_nightly_verification_suite.py`.
3. **Do not claim Tree Borrows completeness**: file the direct-local-access gap (§6) as a new
   tracker item.
4. **Part B scope**: wire `CastKind.{floatToInt, intToFloat, floatToFloat}` for `f32` / `f64`
   only (`f16` / `f128` stay unsupported); NaN results follow the deterministic
   `rustc_apfloat` / Miri rule (quiet bit set, payload shifted), one admissible choice under
   Rust's non-deterministic NaN semantics.
5. **Upstream hygiene**: replace the `String.toList` match in `translateIntrinsicOrNone` so the
   MiniRust witnesses themselves become `Classical.choice`-free (§5).

Track A roadmap (in order): (1) `BorrowEntry.targetFrameDepth` + `allocDead` and frame-qualified
local access helpers; (2) frame-scoped borrow-table operations, `Return` dealloc check +
frame-borrow disabling, `preventsDeallocation`; (3) `validateLoadedValue` `.char` case,
`evalPtrOffsetBinOp` decoupling, `SetDiscriminant` on `.uninit`; (4) Part B float casts in
`evalRvalue`; (5) dependent proof / witness / tracker updates and the `V2026_08_01` mirror;
(6) re-run this suite's corpus differential against the patched `Trusted` (expected: the 7
divergences of §2b become agreements).
