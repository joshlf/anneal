# `frame_tutor` as Chapter 2 uses it

This directory is the crate that [Chapter 2 of the Anneal Tutor](../../docs/tutor/02-rust-specifications.md)
runs its commands against. Compared with [`examples/tutor-ch1/`](../tutor-ch1/),
`Cargo.toml` depends on `anneal-spec`, and `src/lib.rs` adds `pin_magic`,
`total_frame_len`, and `advance_offset` with `#[anneal_spec::spec]` contracts,
the `#[anneal_spec::model]` helper `is_valid_version`, and the
`#[anneal_spec::invariant]` newtype `FrameLen`. Nothing exists under
`anneal/proofs/` yet, so `cargo anneal verify` does not succeed on this crate;
the chapter explains why, and [`examples/tutor-ch3/`](../tutor-ch3/) and
[`examples/tutor-ch4/`](../tutor-ch4/) supply the proofs.

From the repository root:

```sh
cargo run -p cargo-anneal -- extract --manifest-path examples/tutor-ch2/Cargo.toml
cargo run -p cargo-anneal -- scaffold --manifest-path examples/tutor-ch2/Cargo.toml
```

The differences between consecutive tutor crates are declared and checked in
[`docs/tutor/workflow/tutor.toml`](../../docs/tutor/workflow/tutor.toml).
