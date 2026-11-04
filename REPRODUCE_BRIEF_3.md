# BRIEF-3 Reproduction Guide: Default Multi-Crate / `core` Lowering & Explicit `#[external_spec]` Dependency Abstraction

This document provides exact, copy-pasteable commands to reproduce and verify Workstream 3 (`BRIEF-3`, integrating `BRIEF-3.1` and `BRIEF-3.2`) in `/usr/local/google/Projects/anneal-workspace/anneal-wt-brief-3` on branch `sup/brief-3` (`adv/brief-3`).

## 1. Environment Setup

```bash
export PATH="$HOME/.local/bin:$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
export ELAN_TOOLCHAIN=leanprover/lean4:v4.34.1
cd /usr/local/google/Projects/anneal-workspace/anneal-wt-brief-3
git status --porcelain
git log --oneline -15
```

## 2. Lean 4 Trusted Verification Surface, `MirSemantics`, & Theory Libraries

Build `Trusted` (`trusted/lean/Trusted/VerificationResult.lean` and `trusted/lean/Trusted/Rustc/{V2026_06_01,V2026_08_01}/MirSemantics/Places.lean`) and `Anneal`:

```bash
cd /usr/local/google/Projects/anneal-workspace/anneal-wt-brief-3/examples
anneal-lean-run --mode build --concurrency 2 -- lake build Trusted Anneal
cd /usr/local/google/Projects/anneal-workspace/anneal-wt-brief-3
```

## 3. `BRIEF-3.1`: Whole-Graph Crate & Sysroot (`core`/`alloc`) MIR Capture

Verify sysroot `.rmeta` MIR extraction (`<[T]>::len`, `<[T]>::as_ptr`, `core::slice::from_raw_parts_mut`, `<[T]>::split_at_mut`, `RangeBounds::contains`, `Option::is_some`, `Option::unwrap_or_else`) and multi-crate dependency capture with primary-crate obligation scoping:

```bash
cargo test -p anneal-rustc-capture driver_captures_sysroot_core_slice_and_range_bounds_mir -- --nocapture
anneal-lean-run --mode build --concurrency 2 -- cargo test -p cargo-anneal multi_crate_workspace_captures_dependency_and_sysroot_mir_while_scoping_obligations -- --nocapture
```

## 4. `BRIEF-3.2`: Transitive `s.memory.callees` Population by Default, Explicit `#[external_spec]` Override, & Default Well-Typed Contracts

Verify clause-less and clause-bearing `#[external_spec(for = <target>)]` macro expansion, canonical `def_path` resolution across local/inherent/`core`/trait-impl targets, cycle-safe transitive `defaultCallees` population, `defaultSpecCallees` companion predicate evaluation, `generate-external-spec` CLI snippet generation, and end-to-end multi-crate + Lean 4 kernel `ModularVerificationResult` proof checking:

```bash
cargo test -p anneal-spec-macros -- --nocapture
cargo test -p anneal-rustc-capture driver_resolves_external_spec_targets_across_local_inherent_and_core_paths -- --nocapture
anneal-lean-run --mode build --concurrency 2 -- cargo test -p cargo-anneal --lib
anneal-lean-run --mode build --concurrency 2 -- cargo test -p cargo-anneal multi_crate_transitive_callees_and_external_spec_override_end_to_end -- --nocapture
```

## 5. Trusted Boundary & Repository Hygiene Gates

```bash
python3 trusted/audit/check_trusted.py --fast
./ci/check_todo.sh
```
