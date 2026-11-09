# BRIEF-3.1 Reproduction Guide: Whole-Graph Crate & Sysroot (`core`/`alloc`) MIR Capture

This document provides exact, copy-pasteable commands to reproduce and verify `BRIEF-3.1` in `<path/to/anneal>`.

## 1. Environment Setup

```bash
cd <path/to/anneal>
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
```

## 2. Sysroot (`core::slice`, `RangeBounds::contains`, & `core::option`) `.rmeta` MIR Extraction & Lean 4 Kernel Typechecking

Run the `anneal-rustc-capture` integration test that compiles a crate calling `<[T]>::len`, `<[T]>::as_ptr`, `core::slice::from_raw_parts_mut`, `<[T]>::split_at_mut`, `<Range<usize> as RangeBounds<usize>>::contains` (transitively resolving `<Range<T> as RangeBounds<T>>::start_bound` and `end_bound`), `Option::<usize>::is_some` via a `const` `fn` pointer (`GlobalAlloc::Function`), and `Option::unwrap_or_else(usize::default)`, extracts the real polymorphic upstream MIR bodies from `core`'s `.rmeta` into `Mir/Core/*.lean`, and verifies that every emitted `Mir/Core/*.lean` and `Mir/DemoSysroot/*.lean` module typechecks in the Lean 4 kernel (`lean`):

```bash
cargo test -p anneal-rustc-capture driver_captures_sysroot_core_slice_and_range_bounds_mir -- --nocapture
```

## 3. Multi-Crate Dependency Graph Capture & Primary-Crate Obligation Scoping

Run the `cargo-anneal` multi-crate workspace integration test where `crate_a` depends on `crate_b` and calls `crate_b::helper_add` alongside `core::slice` and `core::ops::RangeBounds` methods, verifying that:
- `build_cargo_check_command` wraps the full dependency graph via `RUSTC_WRAPPER` (clearing `RUSTC_WORKSPACE_WRAPPER` to avoid double-wrapping workspace members),
- `Mir/CrateB/helper_add.lean`, `Mir/Core/*.lean`, and `Mir/CrateA/*.lean` are emitted and placed in `.anneal/generated/Mir/`,
- Only primary-crate items (`crate_a`) generate `Obligations/CrateA/*.lean` and `Verify/CrateA/*.lean` proof obligations (while `crate_b` and `core` items are recorded with `"item_kind": "callee"`), and
- All generated `.anneal/generated/Mir/**/*.lean` modules compile cleanly in the Lean 4 kernel (`lean`).

```bash
cargo test -p cargo-anneal multi_crate_workspace_captures_dependency_and_sysroot_mir_while_scoping_obligations -- --nocapture
```

## 4. Full Verification Receipts

Run the full `anneal-rustc-capture` and `cargo-anneal` test suites and the `trusted/audit/check_trusted.py --fast` audit check:

```bash
cargo test -p anneal-rustc-capture -p cargo-anneal
python3 trusted/audit/check_trusted.py --fast
```
