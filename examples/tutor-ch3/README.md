# `frame_tutor` as Chapter 3 uses it

This directory is the crate that [Chapter 3 of the Anneal Tutor](../../docs/tutor/03-assumptions-and-incremental-adoption.md)
runs its commands against. Compared with [`examples/tutor-ch2/`](../tutor-ch2/),
`src/lib.rs` is narrowed to `magic_version` and `pin_magic`, and `pin_magic`'s
proof is deferred to the scoped axiom in
`anneal/proofs/Assumptions/FrameTutor/pin_magic.lean`, which
`anneal/proofs/Proof/FrameTutor/pin_magic.lean` routes through. Default
verification rejects the assumption; `--allow-assumptions` reports `pin_magic`
as `CONDITIONAL`. [`examples/tutor-ch4/`](../tutor-ch4/) replaces the assumption
with a kernel-checked proof.

From the repository root:

```sh
cargo run -p cargo-anneal -- verify --allow-assumptions --manifest-path examples/tutor-ch3/Cargo.toml
```

The differences between consecutive tutor crates are declared and checked in
[`docs/tutor/workflow/tutor.toml`](../../docs/tutor/workflow/tutor.toml).
