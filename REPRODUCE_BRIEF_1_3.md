# Step-by-Step Reproduction Instructions for `BRIEF-1.3`

- **Item ID**: `BRIEF-1.3` (`CallConv.rustIntrinsic` Compiler Intrinsics Executed Inside `core`)
- **Worktree**: `<path/to/anneal>`
- **Branch**: `adv/brief-1-3`
- **Base Commit (`sup/brief-1`)**: `163ff6068da17eacfa4bb581f841e527e03ae455`

## 1. Verify Worktree & Commit History

```bash
cd <path/to/anneal>
git status --porcelain
git log --oneline -10
```

Expected output:
- `git status --porcelain` is empty.
- `git log --oneline -10` shows the complete 4-round adversarial commit chain on `adv/brief-1-3` stacked on `163ff606` (`sup/brief-1`):
  - `[adv A4]` (`HEAD`): `BRIEF-1.3: Recognize std::hint::unreachable_unchecked in isUnreachableCallTarget and finalize reproduction receipts`
  - `[adv B4] c0fe712d`: `BRIEF-1.3: Name intrinsics by defining path and ratchet the miri-diff suite`
  - `[adv A3] 5f702e77`: `BRIEF-1.3: Harden unknown-pointee pointer validation, const_eval_select ARG ops, and rhs signedness`
  - `[adv B3] 2bb6d3e3`: `BRIEF-1.3: Prove mixed-width shift parity, fail closed on unknown pointees, fix quotes`
  - `[adv A2] 435a641e`: `BRIEF-1.3: Prove BinOp intrinsic parity and harden DST layout/metadata and const_eval_select typeArgs`
  - `[adv B2] 8c83299e`: `BRIEF-1.3: Fix align_of_val, custom-DST, signedness, and ub_checks gaps`
  - `[adv A1] 8cd87e66`: `BRIEF-1.3: Harden const_eval_select ZST/panic dispatch, compound unsized pointees, and dyn Trait pointer validation`
  - `[adv B1] 4654a26d`: `BRIEF-1.3: Fix intrinsic layout, isize::MAX, and exact_div bugs`
  - `[adv A0] 10a3cd48`: `BRIEF-1.3: CallConv.rustIntrinsic core compiler intrinsics and L5 correspondence theorems`

## 2. Build `Trusted`, `Anneal`, and `Correspondence` (`L5_ControlAndCalls`) Modules

```bash
export PATH="$HOME/.local/bin:$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal>/examples
anneal-lean-run --mode build --concurrency 3 -- lake build Trusted Anneal Correspondence.V2026_06_01.L5_ControlAndCalls Correspondence.V2026_08_01.L5_ControlAndCalls
```

Expected output:
- `Build completed successfully.` and exit code `0`, with no warnings.
- This kernel-checks `Trusted.Rustc.{V2026_06_01,V2026_08_01}.MirSemantics.{Scalars,Terminators}`
  and both `L5_ControlAndCalls` modules, whose intrinsic theorems are listed in
  step 3.

## 3. Check the Intrinsic Theorems and Their Axioms

```bash
export PATH="$HOME/.local/bin:$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal>/examples
python3 - > /tmp/brief_1_3_axioms.lean <<'PY'
names = """mir_evalTerminator_exact_div_intrinsic_corresponds
mir_evalTerminator_ub_checks_intrinsic_corresponds
mir_evalTerminator_const_eval_select_intrinsic_corresponds
mir_evalTerminator_arith_offset_intrinsic_corresponds
mir_evalTerminator_bit_intrinsics_corresponds
mir_evalTerminator_wrapping_saturating_unchecked_intrinsics_corresponds
mir_evalTerminator_comparison_and_layout_intrinsics_corresponds
mir_evalTerminator_align_of_val_rejects_oversized_slices
mir_evalTerminator_intrinsic_signedness_fails_closed
mir_intrinsic_scalars_agree_with_evalScalarBinOp
mir_evalTerminator_dst_prefix_meta_decl_and_select_typeArgs_corresponds
mir_intrinsic_shifts_agree_with_evalScalarBinOp
mir_intrinsic_shifts_agree_with_evalScalarBinOp_instances
mir_evalTerminator_pointee_resolution_fails_closed
mir_evalTerminator_missing_pointee_ub_and_rhs_signedness_corresponds""".split()
print("import Correspondence.V2026_06_01.L5_ControlAndCalls")
print("import Correspondence.V2026_08_01.L5_ControlAndCalls")
for d in ["V2026_06_01", "V2026_08_01"]:
    for n in names:
        print(f"#print axioms Correspondence.{d}.L5_ControlAndCalls.{n}")
PY
anneal-lean-run --mode file --concurrency 3 -- lake env lean /tmp/brief_1_3_axioms.lean
rm -f /tmp/brief_1_3_axioms.lean
```

Expected output:
- 30 lines of the form `'Correspondence.<dialect>.L5_ControlAndCalls.<name>'
  depends on axioms: [...]`, each listing only `propext` and possibly
  `Quot.sound` (no `sorryAx`), and exit code `0`. An unknown name is an error.
- The theorems are numbered `L5.18`–`L5.31` in `V2026_06_01`; `V2026_08_01`
  numbers its `exact_div` theorem `L5.11` and the rest identically.

## 4. Run Trusted Boundary & Governance Audit

```bash
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal>
python3 trusted/audit/check_trusted.py --fast
./ci/check_todo.sh
```

Expected output:
- `PASS: kernel dependency closure, statement-origin separation, and Cargo DAG boundary`
- Exit code `0`.

## 5. Run `anneal-rustc-capture` Test Suite

```bash
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal>
cargo test -p anneal-rustc-capture
```

Expected output:
- All `anneal-rustc-capture` unit and integration tests pass with exit code `0`.

## 6. Run the Miri Differential Suite

```bash
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal>
cargo test -p cargo-anneal --test end_to_end_miri_diff
```

Expected output:
- `test result: ok. 2 passed`. The corpus's `exact_div` tests are verified
  rather than ratcheted as known bugs: `exact_div(84u32, 7u32)` returns `12`
  and `exact_div(19u32, 2u32)` faults with `.ub`, matching Miri.
