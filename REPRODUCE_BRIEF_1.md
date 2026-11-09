# Step-by-Step Reproduction Instructions — `BRIEF-1`: `Trusted.MirSemantics` Completeness for Emit'able MIR & `CallConv.rustIntrinsic`

- **Item ID**: `BRIEF-1` (Workstream 1 Supervisor Integration of `BRIEF-1.1`, `BRIEF-1.2`, `BRIEF-1.3`, and `BRIEF-1.4`)
- **Worktree**: `<path/to/anneal>`
- **Branches**: `sup/brief-1` and `adv/brief-1`
- **Child Leaf Milestones**:
  - `BRIEF-1.1` (`f515de96` — Function-Item Reification `ReifyFnPointer`, `fnPtrToPtr` Casts, and Indirect `FnPtr` Calls): see [`REPRODUCE_BRIEF_1_1.md`](REPRODUCE_BRIEF_1_1.md).
  - `BRIEF-1.2` (`163ff606` — Diverging Calls `target = .none` and Unwind Cleanup Terminators `unwindResume`, `unwindTerminate`): see [`REPRODUCE_BRIEF_1_2.md`](REPRODUCE_BRIEF_1_2.md).
  - `BRIEF-1.3` (`91c7f640` — `CallConv.rustIntrinsic` Compiler Intrinsics Executed Inside `core`): see [`REPRODUCE_BRIEF_1_3.md`](REPRODUCE_BRIEF_1_3.md).
  - `BRIEF-1.4` (`385d6d89` — Slice Unsizing `Unsize` `[T; N]` $\rightarrow$ `[T]`, `Rvalue.len` on Slices, Non-Scalar `ConstValue` / Global Reads, Signed `BinOp.offset`, and Structural Completeness): see [`REPRODUCE_BRIEF_1_4.md`](REPRODUCE_BRIEF_1_4.md).

## 1. Verify Worktree & Commit History

```bash
export PATH="$HOME/.local/bin:$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal>
git status --porcelain
git log --oneline -20
```

Expected output:
- `git status --porcelain` is empty.
- `git log --oneline -20` shows the complete linear history integrating `BRIEF-1.1` (`f515de96`), `BRIEF-1.2` (`163ff606`), `BRIEF-1.3` (`91c7f640`), and `BRIEF-1.4` (`385d6d89`).

## 2. Build All `Trusted`, `Anneal`, `MiniRust`, `Correspondence`, and `MirVerification` Targets

```bash
export PATH="$HOME/.local/bin:$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal>/examples
anneal-lean-run --mode build --concurrency 3 -- lake build Trusted Anneal MiniRust Correspondence MirVerification
anneal-lean-run --mode build --concurrency 3 -- lake build
```

Expected output:
- `Build completed successfully` with exit code `0` and zero warnings across both `V2026_06_01` and `V2026_08_01` dialects.

## 3. Run Trusted Computing Base Audit & Zero-Sorry Gate

```bash
export PATH="$HOME/.local/bin:$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal>
python3 trusted/audit/check_trusted.py --fast
./ci/check_todo.sh
```

Expected output:
- `PASS: kernel dependency closure, statement-origin separation, and Cargo DAG boundary (40 Trusted modules; 8068 Trusted kernel declarations; 16073 total replayed declarations; 11 claim theorem statements origin-checked)`
- Exit code `0`.

## 4. Run Compiler Capture & Miri Differential Test Suites

```bash
export PATH="$HOME/.local/bin:$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal>
cargo test -p anneal-rustc-capture
cargo test -p cargo-anneal --test end_to_end_miri_diff
```

Expected output:
- All `anneal-rustc-capture` and `end_to_end_miri_diff` tests pass with exit code `0`.
