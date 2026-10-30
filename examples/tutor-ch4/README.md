# `frame_tutor` as Chapter 4 uses it

This directory is the crate that [Chapter 4 of the Anneal Tutor](../../docs/tutor/04-manual-proof-workflow.md)
runs its commands against. Compared with [`examples/tutor-ch3/`](../tutor-ch3/),
`src/lib.rs` is the four-item file from [`examples/tutor-ch2/`](../tutor-ch2/)
again, the assumption module is gone, and `anneal/proofs/` holds kernel-checked
proofs for `pin_magic` and `total_frame_len` plus the `refineSafeSpec`
specification and `verifyByWPSafe` proof for `advance_offset`. Every item
verifies `UNCONDITIONAL`. [`examples/tutor/`](../tutor/) adds the `unsafe`
items of Chapter 5.

From the repository root:

```sh
cargo run -p cargo-anneal -- verify --manifest-path examples/tutor-ch4/Cargo.toml
```

The differences between consecutive tutor crates are declared and checked in
[`docs/tutor/workflow/tutor.toml`](../../docs/tutor/workflow/tutor.toml).
