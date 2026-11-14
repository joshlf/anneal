# PROTOTYPE_REPORT — `ws-proto-tcb-correspondence-div8-and-ieee-float` (`ep1-proto-div8-and-ieee-float`)

> [!IMPORTANT]
> **Prototype-only** (`track = "prototype"`, `merge_policy = "no_merge_prototype"`).
> Nothing under `trusted/**`, `lakefile.toml`, `minirust/**`, or `lean-miri/**` is modified.
> All semantics live in the overlay `theory/Anneal/TcbCorrespondenceDiv8AndFloatPrototype.lean`;
> the regression/audit suite is `scripts/test_tcb_correspondence_div8_proto.py`.

Status: **B1 adversarial critique & hardening pass** (to be finalized in round A4 with the
GO / CONDITIONAL GO / NO-GO recommendation). All declarations of the overlay (including all
84 pinned headline theorems) are kernel-checked with axioms `⊆ {propext, Quot.sound}` —
zero `Classical.choice`, zero `sorry`, zero `native_decide` (see §5).

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
| `DIV-MR-CALL-TARGET-LOCAL` | P0_soundness | `div_mr_call_target_local_trusted_baseline` / `_trusted_137` (Trusted returns **137**) | `div_mr_call_target_local_repaired_agrees` (`.ok 42`, 3-way with `Mach` / `MachTB`) | `div_mr_call_target_local_write_back_canary` (caller `_1`: 5→42, callee `_1 = 100` untouched; Trusted returns 5137), `div_mr_call_target_local_reborrow_in_callee_canary` (`&mut *_2` + `Retag` inside callee), `reborrow_inherits_targetFrameDepth` (universal) |
| `DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL` | P1_false_positive_ub | `div_mr_caller_borrow_across_scalar_call_trusted_ub` | `div_mr_caller_borrow_across_scalar_call_repaired_agrees` (`.ok 42`, 3-way) | `div_mr_caller_borrow_frame_isolation` (universal), `updateBorrowPermAtProjProto_other_frame`, `entryAccessTransitionProto_other_frame` |
| `DIV-MR-TB-TWOPHASE-DIRECT-WRITE` | P1_soundness | already UB in `LM-3.3` `Trusted` (`twoPhaseDirectWriteTreeBorrowsGap_anneal_ub`) | `div_mr_tb_twophase_direct_write_repaired_agrees` (`.ub`, = `MachTB`, = `Trusted`) | pre-`LM-3.3` model `preserveReservedOnDirectWrite` returns 99; `direct_write_disables_reservedFrz_preserves_cell_and_reservedIM` (universal); `div_mr_tb_twophase_direct_write_reservedIM_and_cell_survive_canary` (`.ok 88`) |
| `DIV-MR-TB-FNENTRY-LOCAL-DEALLOC` | P1_soundness | `div_mr_tb_fnentry_local_dealloc_trusted_ret` (Trusted returns 5) | `div_mr_tb_fnentry_local_dealloc_repaired_agrees` (`.ub` at root `Return`, = `MachTB`) | `_ub_at_return` (fault is exactly the terminator), `_callee_return_canary` (callee-frame `Return` faults; Trusted returns 5), `disableFrameBorrowsProto_frame_isolation` (universal), `div_mr_tb_fnentry_dangling_callee_raw_ptr_return_ub` (dangling callee raw pointer deref faults; Trusted returns 5) |
| `DIV-MR-TB-UNSAFECELL-PROTECTED-IM` | P2_false_positive_ub | `Trusted.hasProtectedLocalBorrow` reports `true` (`div_mr_tb_unsafecell_storage_dead_canary`) | `div_mr_tb_unsafecell_protected_im_repaired_agrees` (`.ok 77`, = `Mach`/`MachTB`) | `div_mr_tb_unsafecell_coupling_legacy_breaks` (legacy rule ⇒ UB at `Return`), StorageDead canary (`.ok 5`), `hasProtectedLocalBorrowProto_cell_exempt_reservedIM_blocks` (universal `.cell` vs `.reservedIM`) |
| `DIV-LM-RAW-OVERWRITE-CHAR-COPY` | P1_soundness | `div_lm_raw_overwrite_char_copy_trusted_steps` (Trusted copies/moves and returns surrogate `0xD800`) | `div_lm_raw_overwrite_char_copy_repaired_ub` (`.ub` on `0xD800`, `0xDFFF`, `0x110000`, copy and move) | `_ub_at_load`, `_valid_accepted` (`0x41`, `0xD7FF`, `0xE000`, `0x10FFFF` for both copy & move), `div_lm_raw_overwrite_char_projected_move_canary` (`move (*_3)`), `validateLoadedValueProto_char_eq_miri` (universal), `isValidCharCode_iff_isValidChar` |
| `DIV-LM-D6-OFFSET-DISABLED-TAG` | P2_false_positive_ub | `div_lm_d6_offset_disabled_trusted_ub`, `div_lm_d6_offset_trusted_evalPtrOffsetBinOp` | `div_lm_d6_offset_disabled_tag_repaired_agrees` (universal lockstep with `miriPtrOffsetInbounds`, every entry permission) | `div_lm_d6_offset_disabled_deref_canary` (read/write through the offset pointer is still UB), `disabled_tag_deref_and_reborrow_ub` (universal across deref read/write/reborrow at any offset), `evalBinOpOffset_lockstep_miri` |
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
* **Additional Track A soundness gaps uncovered in B1**:
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

## 3. Track A edit plan (draft)

| File | Edit |
|------|------|
| `trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/State.lean` (`BorrowEntry`) | add `targetFrameDepth : Nat := 0` |
| `…/MirSemantics/Places.lean` (`updateBorrowPerm`, `invalidateConflictingBorrows`, `updateBorrowPermAtProj`, `invalidateConflictingBorrowsAtProj`, `hasProtectedWriteConflict`, tree read/write helpers) | scope every entry test to `(targetFrameDepth, targetLocal)` |
| `…/MirSemantics/Places.lean` (`evalRvalue .ref` / `evalRvalueRawPtr`, `evalRvalueRefDeref`) | stamp `targetFrameDepth := callStack.length`; reborrows inherit the parent's `(targetFrameDepth, targetLocal)` |
| `…/MirSemantics/Places.lean` (deref reads / writes, `evalPlaceWrite`, `evalOperand`) | route through frame-qualified local access (`readFrameLocalProto` / `writeFrameLocalProto`) |
| `…/MirSemantics/Places.lean:16331` (`validateLoadedValue`) | add `.char` case `sizeBytes == 4 && isValidCharCode bits` |
| `…/MirSemantics/Places.lean:15468` (`evalPtrOffsetBinOp`) and `ptrAllocByteBound?` | drop the `.disabled` check / short-circuit; bound = live allocation size |
| `…/MirSemantics/Statements.lean:1842` (`hasProtectedLocalBorrow`), `disableLocalBorrows` | frame scoping + `preventsDeallocation` exemption |
| `…/MirSemantics/Statements.lean` (`evalStmt .setDiscriminant`) | `.uninit` ⇒ `.init (.aggregate v [])` with protector check + invalidation; `.init (.aggregate _ fs)` keeps `fs` with protector check + invalidation |
| `…/MirSemantics/Statements.lean` (`evalFnEntryRetag`, `evalNonFnEntryRetag`) | children inherit `targetFrameDepth` |
| `…/MirSemantics/Terminators.lean` (`evalTerminator .return_`) | `hasFrameDeallocProtectorConflict` over the returning frame's locals, disable its borrows, *then* restore the caller's protectors — in both root and callee return |
| `…/MirSemantics/Places.lean` (`evalRvalue .cast`) | `CastKind.{floatToInt, intToFloat, floatToFloat}` via the Part B functions |
| `V2026_08_01` mirror of every edit above | same |
| Downstream (`DIV-LM-RAW-OVERWRITE-CHAR-COPY`) | `SimLM2_1.lean` (`WellTypedLM2_1ScalarOperand.validateLoadedValue_true`), `SimLM2_4.lean` (`validateLoadedValue_unionField_true`), `SymReflect.lean` (symbolic `.char` arguments), `MiniRustSpec/Correspondence/AnnealEval.lean` |
| Tracker | retire the 8 IDs in `scripts/run_nightly_verification_suite.py` once the witnesses flip |

## 4. Part B specification summary

* `decodeBits` ≡ Miri `decode` (`decodeBits_agrees_miriDecode`, all in-width patterns).
* `evalFloatToIntSaturating`: NaN ↦ 0, ±∞ ↦ max/min, finite ↦ clamp(trunc); canonical
  two's-complement `ScalarInt` (`evalFloatToIntSaturating_sound`, `_nan`, `_canaries`).
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
* `CastKind` wiring: `castKind_end_to_end` (`runMirProto` on real `Rvalue.cast` bodies);
  unpatched `Trusted.evalRvalue` returns `.unsupported` (`castKind_trusted_unsupported`).

## 5. Axiom hygiene (zero `Classical.choice`)

* `#guard_msgs in #print axioms` pins all 84 headline theorems (§7 of the Lean file); the
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

* Fail-closed (`.unsupported`): globals / untracked provenance, deref of a non-zero
  pointer offset, index/subslice borrow projections, unwinding, external calls,
  `f16` / `f128`.
* Direct (non-deref) local reads do not apply Tree Borrows foreign-read transitions —
  identical to `Trusted` (pre-existing; out of scope of the eight items).
* No `rangeOffset` / `rangeLen` byte-ranged entries.
* *(Resolved in B1)*: Float-level ≤ ½ ULP + even-tie guarantees and unreachability of the
  `inconsistentRounding` (`preferredNaNBits`) branches of `roundRatioBits` are now proved
  universally in `roundRatioBits_valid_and_not_nan` and `roundRatioTiesToEven_float_half_ulp`.

## 7. Recommendation

*Pending (finalized in A4).*
