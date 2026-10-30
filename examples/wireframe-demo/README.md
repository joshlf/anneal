# `wireframe_demo`: End-to-End Codec Showcase Across Four User Journeys

`wireframe_demo` is a `#![no_std]` binary packet and frame codec crate demonstrating
how humans and agents apply Anneal across four end-to-end verification workflows.
See [`../../docs/demo-user-journeys.md`](../../docs/demo-user-journeys.md) for the
architectural walkthrough and post-demo follow-up roadmap.

## User journeys covered in this crate

| Journey | Items in [`src/lib.rs`](src/lib.rs) | What Anneal proves or catches |
| --- | --- | --- |
| **1. Bootstrap safe Rust verification** | `WIRE_VERSION_V1`, `wire_protocol_version`, `is_valid_payload_len`, `FrameCursor`, `frame_total_len`, `advance_cursor` | Zero-authored-file `defaultProof` discharge on constant functions; `#[model]` and `#[invariant]` extraction; universal symbolic `#[spec]` verification across all `17,425` bounded `(header_len, payload_len)` inputs; stateful `&mut FrameCursor` verification via `Anneal.FunctionalTranslation` (`MutLens` + `PointsTo` + `TransPlan`) preserving `offset <= limit`. |
| **2. Find & repair an `unsafe` UB bug** | `WireHeader`, `decode_wire_header` | Catches unguarded `core::mem::transmute::<[u8; 4], WireHeader>(raw)` when `raw[1] = 2` violates `bool` bit-validity (`ITree.fail .ub`), produces a kernel-checked `¬ claim.holds` counterexample witness (`refuteClaimByBoundedUB`), and verifies the repaired parser unconditionally across all `2^32` 4-byte headers. |
| **3A. Keep an authoring agent in check** | `clamp_payload_window` | `cargo anneal lock-specs --allow-impl-edit clamp_payload_window` freezes `#[spec]` companions, `Specs/**`, `Assumptions/**`, and sibling functions; `cargo anneal agent-verify` blocks spec tampering, buggy code, `sorry`, and rogue `axiom` declarations before accepting the verified implementation. |
| **3B. Keep a human author in check during agent review** | `parse_compression_flag` | `refineSafeSpec` (`MirContractHoldsWithSafety`) enforces `MirNoUB` across all `256` `u8` inputs even outside `requires`, catching a human-authored `unsafe { core::mem::transmute::<u8, bool>(flags_byte) }` shortcut at `flags_byte = 2`, while `NonVacuousPre` blocks contradictory preconditions. |
| **4. Iterative verified `safe -> unsafe` optimization** | `checksum_frame_safe`, `checksum_frame_fast` | Freezes `Mir.WireframeDemo.checksum_frame_safe.body` as the specification (`StatefulEquivItemSpec` / `StatefulEquivVerificationResult`: `RefinesStatefulMir` + `TotalClaim.holds`), rejects an endianness-buggy `transmute` iteration in seconds via `--item checksum_frame_fast`, certifies behavioral equivalence across all `2^64` 8-byte frames, and benchmarks the compiled throughput speedup. |

## Running the crate verification and live walkthrough

From the repository root:

```bash
# Verify every item in wireframe_demo plus the CrateVerify whole-crate rollup:
cargo run -p cargo-anneal -- verify --manifest-path examples/wireframe-demo/Cargo.toml

# Run the automated four-journey live demonstration and release microbenchmark:
python3 -B examples/wireframe-demo/run_live_demo.py
```
