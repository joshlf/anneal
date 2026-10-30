# `frame_tutor` as Chapter 1 uses it

This directory is the crate that [Chapter 1 of the Anneal Tutor](../../docs/tutor/01-basic-usage-and-outputs.md)
runs its commands against: a single zero-argument function, `magic_version`,
and no dependencies. `cargo anneal verify` discharges it without any file under
`anneal/proofs/`.

Section 6 of the chapter asks you to add an unannotated `advance_offset` to
`src/lib.rs` and watch verification reject it; the chapter shows the resulting
file and error. [`examples/tutor-ch2/`](../tutor-ch2/) continues from there.

From the repository root:

```sh
cargo run -p cargo-anneal -- verify --manifest-path examples/tutor-ch1/Cargo.toml
```

The differences between consecutive tutor crates are declared and checked in
[`docs/tutor/workflow/tutor.toml`](../../docs/tutor/workflow/tutor.toml).
