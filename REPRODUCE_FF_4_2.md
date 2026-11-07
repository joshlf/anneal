# Reproduction & Compression Report: FF-4.2 (`adv/ff-4-2`)

## 1. Overview

Work unit `FF-4.2` migrates Anneal's MIR proof corpus (`examples/wireframe-demo`, `examples/tutor`, and `examples/mir/MirVerification.lean`) to the fuel-free functional lifting and execution infrastructure (`Anneal.MirLiftCore`, `Anneal.PureMirExec`, `Anneal.MirFuelFree`, and fuel-free `Anneal.Rustc.V2026_06_01.SymbolicEval` combinators) while keeping `trusted/` (`trusted/lean/**` and `trusted/audit/**`) byte-for-byte identical to the baseline `0d3242d3`.

Key outcomes:
- **Zero `sorry` / `admit` / `sorryAx` / `axiom` / `#[trusted]` / `native_decide`** across all theory and proof modules.
- **Zero `BlockCtx` definitions (`0`)** and **zero manual `fuel` constants (`0`)** in `examples/wireframe-demo/anneal/proofs/Proof/WireframeDemo/*.lean`, `examples/tutor/anneal/proofs/Proof/FrameTutor/*.lean`, and `examples/mir/MirVerification.lean`.
- **52.7% LOC reduction** on `examples/wireframe-demo/anneal/proofs/Proof/WireframeDemo/*.lean` relative to `0d3242d3` (`4,264` LOC $\rightarrow$ `2,018` LOC), and **74.8% LOC reduction** relative to the pre-lifting manual proof corpus (`a6bebfc2`, `8,009` LOC $\rightarrow$ `2,018` LOC).

---

## 2. Per-File LOC & Boilerplate Comparison

### 2.1 `examples/wireframe-demo/anneal/proofs/Proof/WireframeDemo/*.lean`

| Proof Module | Pre-Lifting (`a6bebfc2`) LOC | Base (`0d3242d3`) LOC | Fuel-Free (`adv/ff-4-2`) LOC | Reduction vs `0d3242d3` | Reduction vs `a6bebfc2` | `BlockCtx` (Before $\rightarrow$ After) | Manual `fuel` (Before $\rightarrow$ After) |
| :--- | ---: | ---: | ---: | ---: | ---: | :---: | :---: |
| `advance_cursor.lean` | 542 | 239 | **171** | -28.5% | -68.5% | $1 \rightarrow 0$ | $1 \rightarrow 0$ |
| `checksum_frame_fast.lean` | 3,108 | 1,636 | **433** | -73.5% | -86.1% | $1 \rightarrow 0$ | $2 \rightarrow 0$ |
| `checksum_frame_safe.lean` | 2,598 | 1,252 | **196** | -84.3% | -92.5% | $1 \rightarrow 0$ | $1 \rightarrow 0$ |
| `clamp_payload_window.lean` | 384 | 227 | **330** | +45.4% | -14.1% | $2 \rightarrow 0$ | $3 \rightarrow 0$ |
| `decode_wire_header.lean` | 781 | 538 | **425** | -21.0% | -45.6% | $1 \rightarrow 0$ | $1 \rightarrow 0$ |
| `frame_total_len.lean` | 308 | 169 | **287** | +69.8% | -6.8% | $2 \rightarrow 0$ | $3 \rightarrow 0$ |
| `parse_compression_flag.lean` | 288 | 203 | **176** | -13.3% | -38.9% | $2 \rightarrow 0$ | $3 \rightarrow 0$ |
| **Total (`WireframeDemo`)** | **8,009** | **4,264** | **2,018** | **-52.7%** | **-74.8%** | **$10 \rightarrow 0$** | **$14 \rightarrow 0$** |

*(Note: In `0d3242d3`, `clamp_payload_window`, `frame_total_len`, and `parse_compression_flag` had already been partially compressed via custom `#mir_lift_spec` syntax commands that modified `trusted/audit/TrustedBoundary.lean`; `adv/ff-4-2` restores `trusted/audit/TrustedBoundary.lean` to `0d3242d3` and discharges all 7 obligations purely within standard Lean 4 declaration/tactic syntax admitted by the unmodified `TrustedBoundary` parser.)*

### 2.2 `examples/tutor/anneal/proofs/Proof/FrameTutor/*.lean`

| Proof Module | Base (`0d3242d3`) LOC | Fuel-Free (`adv/ff-4-2`) LOC | Fuel-Free Combinator Used | Manual `fuel` (Before $\rightarrow$ After) |
| :--- | ---: | ---: | :--- | :---: |
| `__anneal_unsafe_impl_WireHeader_for_FrameLen.lean` | 71 | **70** | `verifyByWPFuelFree` | $1 \rightarrow 0$ |
| `advance_offset.lean` | 89 | **87** | `verifyByWPSafeFuelFree` + `mirBoolPredicateHolds_of_wp_fuelFree` | $2 \rightarrow 0$ |
| `pin_magic.lean` | 30 | **28** | `dischargeRustEqU32FuelFree` | $2 \rightarrow 0$ |
| `read_version_ref.lean` | 34 | **33** | `dischargeStatefulEqFuelFree` | $1 \rightarrow 0$ |
| `total_frame_len.lean` | 31 | **29** | `dischargeRustEq2U8FuelFree` | $2 \rightarrow 0$ |
| `write_version_mut.lean` | 54 | **53** | `dischargeStatefulEqFuelFree` | $1 \rightarrow 0$ |
| **Total (`FrameTutor`)** | **309** | **300** | — | **$9 \rightarrow 0$** |

### 2.3 `examples/mir/MirVerification.lean`

All 10 bounded verification entrypoints in `examples/mir/MirVerification.lean` (`addU32SafeClaim_verified`, `addU32TotalClaim_verified`, `example_companion_bool_spec_holds`, `example_branch_obs_trace_verified`, `reborrowWriteStatefulClaim_verified`, `countdownTotalClaim_verified`, `pureConstFfiModularClaim_verified`, `callerAddTwoModular_verified`, `unalign_set_mir_verified`, and `polySwapPairU32Claim_verified`) now use the fuel-free combinators (`verifyMirFuelFree`, `verifyTotalMirFuelFree`, `mirBoolPredicateHolds_of_fuelFree`, `verifyTraceMirFuelFree`, `verifyStatefulMirFuelFree`, `verifyModularMirFuelFree`).

---

## 3. Elaboration Wall-Clock Timings & Heartbeat Budgets

Measured on single-file `anneal-lean-run --mode file --concurrency 1 -- lake env lean` invocations and full `cargo-anneal verify`:

| Target | `maxHeartbeats` Budget | Single-File Elaboration Wall-Clock | Kernel Replay (`TrustedBoundary`) |
| :--- | ---: | ---: | :--- |
| `Proof/WireframeDemo/parse_compression_flag.lean` | `800,000` (default) | ~3.2 s | PASS (`trustLevel := 0`) |
| `Proof/WireframeDemo/frame_total_len.lean` | `800,000` (default) | ~4.1 s | PASS (`trustLevel := 0`) |
| `Proof/WireframeDemo/clamp_payload_window.lean` | `800,000` (default) | ~4.8 s | PASS (`trustLevel := 0`) |
| `Proof/WireframeDemo/advance_cursor.lean` | `800,000` (default) | ~3.9 s | PASS (`trustLevel := 0`) |
| `Proof/WireframeDemo/decode_wire_header.lean` | `4,000,000` | ~9.4 s | PASS (`trustLevel := 0`) |
| `Proof/WireframeDemo/checksum_frame_safe.lean` | `8,000,000` | ~11.2 s | PASS (`trustLevel := 0`) |
| `Proof/WireframeDemo/checksum_frame_fast.lean` | `8,000,000` | ~16.8 s | PASS (`trustLevel := 0`) |
| `Proof/FrameTutor/*.lean` (all 6 files) | `200,000` (default) | < 2.0 s each | PASS (`trustLevel := 0`) |

---

## 4. Step-by-Step Reproduction Commands

Run the following commands from `/home/groupagent-anneal-fuzz-bot/Projects/markdittmer/anneal-wt-ff-4-2`:

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"

# 1. Verify zero changes to trusted/ against base commit 0d3242d3:
git diff 0d3242d3 -- trusted/

# 2. Verify LOC counts and zero BlockCtx / manual fuel occurrences in Proof/WireframeDemo:
wc -l examples/wireframe-demo/anneal/proofs/Proof/WireframeDemo/*.lean
grep -c "BlockCtx" examples/wireframe-demo/anneal/proofs/Proof/WireframeDemo/*.lean || true

# 3. Build Anneal theory and MirVerification examples:
(cd examples && anneal-lean-run --mode build --concurrency 1 -- lake build Anneal MirVerification)

# 4. Run end-to-end cargo-anneal verification (including TrustedBoundary kernel replay) on wireframe-demo:
anneal-lean-run --mode build --concurrency 1 -- cargo-anneal verify --manifest-path examples/wireframe-demo/Cargo.toml

# 5. Run end-to-end cargo-anneal verification (including TrustedBoundary kernel replay) on tutor:
anneal-lean-run --mode build --concurrency 1 -- cargo-anneal verify --manifest-path examples/tutor/Cargo.toml

# 6. Run repository hygiene and trusted-boundary fast audit checks:
./ci/check_todo.sh
python3 trusted/audit/check_trusted.py --fast
```
