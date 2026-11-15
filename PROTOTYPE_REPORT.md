# PROTOTYPE_REPORT — `ws-proto-lean-miri-deinit-pin-and-correspondence-codec` (`ep1-prototype-codec-deinit-and-pin`)

> [!IMPORTANT]
> **Prototype only** (`track = "prototype"`, `merge_policy = "no_merge_prototype"`). Base
> `8e1523cbd65964ee06759174283536df4b083526`. Only four files are added:
> `theory/Anneal/LeanMiriDeinitAndCodecPrototype.lean`, `scripts/verify_lean_miri_pin_proto.py`,
> `scripts/test_verify_lean_miri_pin_proto.py`, `PROTOTYPE_REPORT.md`. Nothing under `trusted/**`,
> `lean-miri/**`, `minirust/**`, `lakefile.toml`, or `theory/Anneal.lean` is modified, and no
> `vendor/lean-miri/` is created.

Status: **round A0** (initial build of the N = 4 adversarial loop). Recommendation (§6):
**CONDITIONAL GO**.

## 1. Architecture

### 1.1 Lean module (`theory/Anneal/LeanMiriDeinitAndCodecPrototype.lean`)

`import Trusted`, plus `Lean.Util.CollectAxioms` / `Lean.Elab.Command` for the environment audit.
All definitions use the real `Trusted.Rustc.V2026_06_01` types (`RigidTy`, `Ty`, `ProjectionElem`,
`Place`, `ConstOperand`, `Operand`, `AggregateKind`, `Rvalue`, `NonDivergingIntrinsic`,
`StatementKind`, `Statement`, `TerminatorKind`, `Terminator`, `BasicBlockData`, `LocalDecl`,
`CapturedMir`, `TypeLayout`, `LayoutTable`, `AbstractByte`, `TreeBorrowPerm`, `BorrowEntry`,
`treeBorrowNodeAccess`, `isBorrowDescendantOrSelf`, `byteRangesOverlapBool`,
`encodeLittleEndianBytes` / `decodeLittleEndianBytes`, `RigidTy.computeLayout`,
`rigidTyIsFreeze`). There is no toy AST.

| Part | Content |
|---|---|
| 0 | Structural `RigidTy.beq` and its soundness and completeness proofs. `RigidTy` is nested, so Lean's `DecidableEq` deriving handler does not apply. This gives an axiom-free `DecidableEq RigidTy` / `Ty`. |
| 1 | A generic canonical interning library: `indexOf?`, `insertIfAbsent`, `insertAll`, `lookupId`, `typesAreCanonical`, plus prefix, membership and injectivity lemmas. |
| 2 | `TypeTable = {kinds : List RigidTy, types : List Ty}`. `internTy` interns the post-order (children first, i.e. bottom-up) of every kind into `kinds`, then the `Ty` itself into `types`. `initTypeTable` pre-seeds `()`, `bool` and `usize` at `KindId` 0/1/2. |
| 3 | `RefProg` syntax mirrors every constructor of the 16 MIR syntax types, with `Ty ↦ TyId`. Also defines `encode*` / `decode*` for each, the `*Tys` occurrence lists, and round trips. |
| 4 | Demand-time `LayoutQuery` (`localLayout`, `scalarTypeClass`, `castTypeInfo`, `pointeeTypes`, `retagTypeShape`, `builtinLayout`), answered from `(TypeTable, LayoutTable)` only. |
| 5 | Shared byte-level machine `PState`. Frames hold `imm`/`mem` slots, the heap holds real `AbstractByte`s, the borrow table holds real `BorrowEntry`s, and `pendingMoveDeinit` is LeanMiri's latch. `M_anneal` performs eager, value-level move deinit (`annealReadOperand`, `annealAssignUse`). `M_ref` uses the `d9b41b58b` two-phase protocol (`refEvalOperand` → `refReadImmediate` / `refCopyRuntimePlaceNoValidate`, `takePendingMoveDeinit`). Statements and terminators cover assign (`use`/`binaryOp`/`aggregate`/`ref`/`rawPtr`), `Deinit`, `StorageLive`/`StorageDead`, `goto`, `return`, `switchInt`, `assert` with `UnwindAction.cleanup`, `call` (arguments first, then callee resolution), and `unwindResume`. Everything else fails closed with `.unsupported`. |
| 6 | Fetch/resolve for both machines. `M_anneal` resolves deep `Ty`s against `CapturedMir.layouts`; `M_ref` resolves `TyId`s via `evalLayoutQuery`. Also defines the step budget (`RefState.stepsExecuted`/`maxSteps`), runs, and observations. |
| 6b | The codec-driven resolution correspondence and the whole-program equivalence. |
| 7 | 28 executable canary theorems covering `D1`–`D9`. |
| 8 | Falsification witnesses. |
| 9 | Tree Borrows theorems. |
| 10 | The wiring claim. |
| 11 | 66 `#guard_msgs (whitespace := lax) in #print axioms` guards. |
| 12 | A `run_cmd` audit of **every** declaration in the module. Its axioms must be ⊆ {propext, Quot.sound}; otherwise elaboration fails. This was checked with a planted `Classical.choice` probe. |

### 1.2 Inventory (A0)

| Metric | Value |
|---|---|
| Lean LOC | 4,410 |
| `theorem`s | 159 |
| `def`/`abbrev`s | 242 |
| `#guard_msgs` axiom guards | 66, all `[propext]` or `[propext, Quot.sound]` |
| `sorry` / `admit` / `axiom` / `native_decide` / `partial` / `unsafe` | 0 |
| `Classical.choice` anywhere in the module | 0 (enforced by the Part 12 audit) |
| Receipt 1 (`anneal-lean-run … lake env lean`) | exit 0, no output (0 errors, 0 warnings), 32 s wall |
| Receipt 3 (`unittest`) | 55 tests, OK (1 opt-in skip: real `d9b41b58b` diff via `ANNEAL_PROTO_DEINIT_PATCH_DIFF`), 58 s wall |
| Verifier LOC / test LOC / tests | 1,761 / 1,170 / 55 (plus 1 opt-in test that applies the real `d9b41b58b` diff) |

### 1.3 Headline theorems

* **Codec.** These hold with zero preconditions; each is stated against its own collected table
  and is extension-stable via `roundtrip_body_of_extends`: `decodeType_encodeType`,
  `decodePlace_encodePlace`, `decodeOperand_encodeOperand`, `decodeRvalue_encodeRvalue`,
  `decodeStmt_encodeStmt`, `decodeTerminator_encodeTerminator`, `decodeBody_encodeBody`,
  `decodeProg_encodeProg` (∀ p, `decodeProg (encodeProg p) = some p`), and `encodeProg_injective`.
* **`encodeProg_types_canonical`.** Both tables are duplicate-free. For interned types, `TyId`
  equality ↔ `Ty` equality. Every interned type's post-order kinds are interned. The built-ins sit
  at `KindId` 0/1/2.
* **`encodeStmt_no_dormant_noops`.** `(encodeStmt tt s).kind = .nop ↔ s.kind = .nop`, and the
  constructor tag is preserved. `encodeTermKind_tag` and `encodeRvalue_tag` do the same for
  terminators and rvalues.
* **Layout queries:**
  * `layoutQuery_scalar_iff`: a scalar answer is exactly the classification of the `localLayout`
    answer (single source).
  * `layoutQuery_zst_unit`: `()` is 0 bytes for every encoded program and layout table.
  * Out-of-range `TyId`s and `LayoutIdx`s fail closed with `.missingHook`
    (`layoutQuery_oob_fails_closed`, `layoutQuery_dangling_layout_fails_closed`).
  * `layoutQuery_mono_prefix`: appending types, kinds or layout entries preserves every `.ok`
    answer (table extension / call-cone narrowing).
  * `layoutQuery_agrees_with_eager`: the demand-time hook refines the eager `O(|types|)` table.
  * `layoutQuery_pointee_total`: `pointeeTypes` is total on interned pointers.
* **Latch transparency.** `twoPhaseStrategy_true_eq_eager : twoPhaseStrategy true = eagerStrategy`.
  With `deinitMoves = true`, the `pendingMoveDeinit` protocol is extensionally equal to eager
  deinit.
* **`deinitMovedPlace_false_id`.** With `deinitMoves = false`, `move` and `copy` agree at
  `evalOperand`, `readImmediate` and `copyRuntimePlaceNoValidate`.
* **Forward simulation:**
  * `anneal_corresponds_to_miri_proto`: ∀ p st, `refStepCore true (encodeProg p) st = annealStep p st`.
  * `refFetch_encodeProg` and `refInit_encodeProg` support it.
  * `refObs_encodeProg`: ∀ p args n, `refObs true (encodeProg p) args n = annealObs p args n`.
    This is whole-program equivalence, including the step budget.
* **Fault and behavior transfer:**
  * `reachesResult_fault_iff_refReachesOutcome_proto` gives bidirectional fault equivalence:
    `.ub` ↔ `.ub`, `.unsupported` ↔ `.blocked`.
  * `behavior_transfer_proto` transfers terminal behavior.
  * `simulationInv_bijective` shows the invariant is functional, injective at fixed counters,
    total, and preserved forward and backward by every step.
* **Falsification:**
  * `correspondence_fails_when_deinitMoves_false` covers use-after-move (`D1`: M_anneal UB vs
    upstream 7) and a `MaybeUninit<u8>` byte copy (UB vs 42).
  * `no_correspondence_when_deinitMoves_false` follows from it.
  * `eager_indirect_deinit_falsified`: a valid `move (*_2)` returns 5 in both machines but gives
    spurious `invalidUninitBytes` under eager deinit inside `evalOperand`.
  * `eagerInEvalOperandStrategy_ne_eager` follows from it.
  * `batched_call_args_lose_move_deinit` covers `kani#5172`.
* **Tree Borrows:**
  * `deinitMovedPlace_preserves_tb_tags` is universal. A successful `move p` leaves the borrow
    table exactly as `copy p` (a pure read) does, and every `.frozen` entry stays `.frozen`. It
    rests on `tbAccessAux_read_preserves_frozen`.
  * The contrast is `tbAccessAux_write_disables_foreign_frozen`, which is universal.
  * `assign_or_deinit_stmt_kills_sibling_frozen` is state-level: `[.frozen]` stays `[.frozen]`
    after `_4 = move (*_2)`, but becomes `[.disabled]` after `*_2 = 9` or `Deinit(*_2)`.
* **`miriMoveDeinitWiring_proto`.** Covers flag threading, latch reset on non-moves, the latch set
  by indirect moves, the unprojected immediate move (local becomes `.uninit`, latch cleared), and
  the `takePendingMoveDeinit` read-and-clear.

## 2. `D1`–`D9` canary matrix

Each row runs a real `CapturedMir`, with layouts from Trusted's `RigidTy.computeLayout`, in both
`M_anneal` and `M_ref(deinitMoves = true)` on `encodeProg p`. Results are decided by the kernel
(`decide`). "UB" means `Obs.ub .invalidUninitBytes` unless stated otherwise.

| ID | Scenario | Theorem(s) | M_anneal / M_ref | PR #257 / `DIV-LM-*` |
|---|---|---|---|---|
| D1 | `_2 = move _1; _0 = copy _1` (u8) | `canary_D1_direct_move_ub` | UB / UB (upstream `deinitMoves=false`: returns 7) | PR #257 `D6` |
| D1 | ZST `()` move then read | `canary_D1_zst_unit_move_ok` | `()` / `()` | PR #257 `D9` |
| D2 | `_2 = move _1.0`; read `_1.1` vs re-read `_1.0` | `canary_D2_partial_field_move_{sibling_ok,reread_ub}` | 2 / 2; UB / UB | `D2` |
| D3 | move, `_1 = 99`, read | `canary_D3_move_then_reinit_ok` | 99 / 99 | `D3` |
| D4 | `copy` keeps source; `copy _1 + move _1`; `move _1 + copy _1`; `move _1 + move _1` | `canary_D4_*` (4) | 5, 10, UB, UB in both | PR #257 `D7a`/`D7b`/`D7c` |
| D5 | `_3 = &_1; _2 = &raw mut _1; _4 = move (*_2)` | `canary_D5_indirect_move_{delivers_value,reread_ub}`, `canary_D5_move_preserves_sibling_frozen` | 5; UB; `*_3` passes TB, then UB on uninit bytes | `D5`; `DIV-LM-D6-OFFSET-DISABLED-TAG` naming |
| D5 | contrast `*_2 = 9` / `Deinit(*_2)` then `*_3` | `canary_D5_{assign,deinit}_disables_sibling_frozen` | `Obs.ub .treeBorrows` in both | — |
| D6 | `_1 = move _1`; `*_2 = move *_2`; `_1 = (move _1.1, move _1.0)` | `canary_D6_*` (3) | 5, 5, 2 in both | PR #257 `D8` |
| D7 | `call callee(move _1, copy _2)`, callee reads `*_2` | `canary_D7_call_arg_move_deinit_before_callee` / `_copy_ok` | UB / UB; 5 / 5 | `kani#5172` |
| D7 | `call unresolved(move _uninit)` vs `call unresolved(const 1)` | `canary_D7_uninit_arg_ub_before_unsupported` / `canary_D7_unresolved_callee_unsupported` | UB (before `.unsupported`); `.unsupported` | `kani#5172`, sibling `DIV-MR-CALL-TARGET-LOCAL` ordering |
| D8 | `assert(move _1)` fails → `cleanup bb2` reads `_1` / `_2` | `canary_D8_assert_cleanup_{moved_cond_ub,unmoved_ok}` | UB / UB; panicked / panicked | `D8` |
| D8 | unwinding `call panicky(move _1)` → `cleanup bb2` | `canary_D8_unwinding_call_{moved_arg_ub,unmoved_ok}` | UB / UB; panicked / panicked | `D8` |
| D9 | `move _1[1]`; read `_1[0]`, `_1[3]`, `_1[1]` | `canary_D9_elem_move_{neighbors_ok,reread_ub}` | 10, 13, UB in both | `D9` |
| D9 | `move _1[1..3]`; read `_1[0]`, `_1[3]`, `_1[1]`, `_1[2]` | `canary_D9_subslice_move_window` | 10, 13, UB, UB in both | `D9` |

Because of `refObs_encodeProg`, every M_ref column also follows from the M_anneal column. Both
columns are nonetheless computed independently by the kernel, as a non-vacuity check.

## 3. Soundness findings

1. **The `d9b41b58b` deinit write is a Tree Borrows *write* in real LeanMiri.** This conflicts
   with `deinitMovedPlace_preserves_tb_tags`.
   * The patch's `PlaceMachine.readImmediate` deinit uses
     `writeImmediateToMplaceNoValidate … (accessHooks config)`.
   * `accessHooks.beforeMemoryWrite := memoryAccess config true …`
     (`lean-miri/vendor/Miri/Interpreter/PlaceMachine.lean:81-86`) runs
     `tree.performBorrowAccessRange … .Write` and a race-detector `.Write`.
   * So upstream+patch would *disable* a sibling `&` after `move (*p)`. That is the
     `canary_D5_assign_disables_sibling_frozen` behavior, and it is a spurious-UB divergence from
     `M_anneal`.
   * The prototype models the intended ghost deinit (`deinitMPlaceRaw`, no TB access). It proves
     the move ≡ copy TB effect universally and the write contrast for `assign`/`Deinit`.
   * **Track A must route the deinit through hooks with no-op `beforeMemoryWrite` / race
     hooks.**
2. **`eager_indirect_deinit_falsified`.** Deinitializing an `.indirect mplace` inside
   `evalOperand` is wrong: `evalOperand` returns a *reference*, so the later `readImmediate` reads
   `.uninit`. The patch's deferral through `pendingMoveDeinit` is necessary, not cosmetic.
3. **`kani#5172` call-argument ordering.** The latch is a single Boolean.
   * If call arguments are evaluated to `OpTy`s in batch before consumption, a later argument's
     `evalOperand` clears or overwrites an earlier `move` argument's latch, and the use-after-move
     is missed (`batched_call_args_lose_move_deinit`).
   * `M_ref` therefore consumes each argument immediately after its `evalOperand`, and evaluates
     all arguments before resolving the callee (`canary_D7_uninit_arg_ub_before_unsupported`).
   * Track A must either check that LeanMiri's `TerminatorMachine` passes arguments one at a time,
     or replace the latch with a per-`OpTy` token.
4. **Memory-path (padded) copies.** `copyRuntimePlaceNoValidate`'s memory branch deinitializes the
   source *after* `memoryCopy`, which would clobber an overlapping destination (for example a
   self-move of a memory-repr aggregate). Both machines therefore reject overlapping memory-path
   copies with `overlappingCopy` UB, matching rustc's `mem_copy(.., nonoverlapping = true)`. The
   immediate branch, which deinitializes before the destination write, handles the `D6`
   self-moves.
5. **Trusted `V2026_06_01.evalOperand` only deinitializes unprojected root locals.**
   * `MirSemantics/Places.lean` `evalOperand`, `.move` arm: `.nil` sets the slot `.uninit`.
     `.deref :: _` and `proj :: _` return `.ok v locals` with the parent unchanged.
   * The real TCB therefore does **not** satisfy `D2`, `D5` and `D9` as stated. The prototype's
     `M_anneal` uses byte-granular deinit of the moved window.
   * Track A must extend `Places.lean` (field, deref and element windows) or scope the claims to
     root-local moves.
6. **Split shared libraries (`cl/1021969520`).**
   * On this host `libleanshared.so` is 233 MB, while `libleanshared_1.so` and
     `libleanshared_2.so` are 6,264-byte companions loaded at startup.
   * Checksumming only `libleanshared.so` leaves a substitution path through the companions.
   * The verifier pins `bin/lean`, `bin/lake` and every `lib/lean/libleanshared*.so`, plus
     `libInit_shared.so` and `libLake_shared.so` (`ldd`).
   * It fails closed on added, deleted or modified companions (`libleanshared_evil.so`,
     `libleanshared_1.so` tamper, deleted `libleanshared_2.so`), on any symlink in the toolchain,
     and on world-writable modes.
7. **Modeling limits, stated rather than hidden:**
   * Projections into immediates fail closed, so the patch's "projected immediate →
     `forceAllocation`" branch of `evalOperand` is unreachable in the prototype.
   * Protectors are not modeled (`isProtected = false`).
   * Pointer loads during nested `deref` walks are raw (no TB).
   * `retag`, `setDiscriminant`, intrinsics, casts and drops are `.unsupported` in both machines.

## 4. Pin verifier (`scripts/verify_lean_miri_pin_proto.py`)

* **Interface.** Stdlib-only and fail-closed, with `sys.dont_write_bytecode`. CLI flags:
  `--repo-root`, `--allow-deinit-patch`, `--dump-toolchain-pin`, `--toolchain-pin-json`, `--json`.
* **Vendor tree.** It checks schema keys and 40/64-hex digests. It requires the exact bijection of
  608 `.lean` files and 9 aux files, and rejects symlinks (file and directory), hard links,
  world-writable files and planted `.olean*`/`.ilean`/`.ir`/`.c`/`.ltar`/`.hash` artifacts.
* **Manifest.** It recomputes `manifest_sha256` as `sha256("".join(f"{sha}  {path}\n"))` over the
  listed order, which reproduces `081747a3…`.
* **Git objects.** It recomputes the git blob SHA-1 and the recursive `Miri` tree hash for
  `upstream_git_objects`, and compiles in a locked upstream identity.
* **Patch allowlist.** `PATCH_ALLOWLIST` is closed to the six files. Each patched entry needs
  distinct `upstream_sha256` ≠ `patched_sha256`, a `patch_reason`, and an `upstream_git_blob` (used
  to recompute the `Miri` tree). The optional `execution_machine_closure` is verified when
  `.olean`s are supplied.
* **Toolchain.** It runs `lean-toolchain` ↔ `build_lean_toolchain` drift detection, and invokes
  `bin/lean --version` / `bin/lake --version` with `stdin=DEVNULL` and a timeout.
* **Tests.** There are 55 unit tests: a live end-to-end run and every tamper vector of the brief.
  The Lean hygiene tests check for forbidden tokens, that every `#print axioms` is guarded with an
  allowed axiom list, and that receipt 1 compiles.

## 5. Receipts (A0)

See the A0 board post for the exact outputs of the four receipt commands. All four exit 0, and
`git diff --name-only 8e1523cb..HEAD` lists only the four prototype files.

## 6. Recommendation and Track A integration plan

**CONDITIONAL GO** for `ws-lean-miri-deinit-pin-and-correspondence-codec`. The conditions are
findings 1, 3, 4 and 5.

File-by-file plan. Patch in place at the repository root `lean-miri/`. This removes
`joshlf-mir-vendor`'s 113,855-line duplicate `vendor/lean-miri/`.

1. `lean-miri/vendor/Miri/Interpreter/{MachineHooks,LocalAccess,OperandMachine,Place,PlaceMachine,ExecutionMachine}.lean`:
   apply `d9b41b58b`. In addition, (a) give the deinit write TB/race-silent hooks (finding 1), and
   (b) either consume call arguments one at a time or make the latch per-operand (finding 3).
2. `lean-miri/UPSTREAM_PIN.json`: add `patched_files`, with six entries carrying
   `upstream_sha256`, `patched_sha256`, `upstream_git_blob` and `patch_reason`, and optionally
   `execution_machine_closure`.
3. `scripts/verify_lean_miri_pin.py` and `ci/`: promote the prototype verifier and wire it into
   `trusted/audit/check_trusted.py`, including the toolchain pin JSON and all `libleanshared*.so`.
4. `trusted/lean/Trusted/Correspondence.lean` (new, TCB): `TypeTable`, `RefProg`, `encodeProg` /
   `decodeProg`, `LayoutQuery`, and the claim statements (`CorrespondenceClaim`,
   `FaultEquivalenceClaim`, `MiriMoveDeinitWiringClaim`) over `V2026_06_01`.
5. `theory/Anneal/Mir/Correspondence/{Codec,LayoutQuery,MoveDeinit,Canaries}.lean`: port Parts
   0–12 of this prototype as proofs of the TCB claims.
6. `trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Places.lean`: byte-granular deinit for
   projected and deref moves (finding 5), with `trusted/root-manifest.sha256` refreshed.
