# Step-by-Step Reproduction Instructions for `BRIEF-1.3`

- **Item ID**: `BRIEF-1.3` (`CallConv.rustIntrinsic` Compiler Intrinsics Executed Inside `core`)
- **Worktree**: `/home/groupagent-anneal-bot/Projects/markdittmer/anneal-wt-brief-1-3`
- **Branch**: `adv/brief-1-3`
- **Base Commit (`sup/brief-1`)**: `163ff6068da17eacfa4bb581f841e527e03ae455`

## 1. Verify Worktree & Commit History

```bash
cd /home/groupagent-anneal-bot/Projects/markdittmer/anneal-wt-brief-1-3
git status --porcelain
git log --oneline -10
```

## 2. Build `Trusted`, `Anneal`, and `Correspondence` (`L5_ControlAndCalls`) Modules

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /home/groupagent-anneal-bot/Projects/markdittmer/anneal-wt-brief-1-3/examples
lake build Trusted Anneal Correspondence.V2026_06_01.L5_ControlAndCalls Correspondence.V2026_08_01.L5_ControlAndCalls
```

Expected output:
- `Build completed successfully.`
- Kernel-checks `Trusted.Rustc.V2026_06_01.MirSemantics.{Scalars,Terminators}`, `Trusted.Rustc.V2026_08_01.MirSemantics.{Scalars,Terminators}`, `Correspondence.V2026_06_01.L5_ControlAndCalls`, and `Correspondence.V2026_08_01.L5_ControlAndCalls` (including `mir_evalTerminator_exact_div_intrinsic_corresponds`, `mir_evalTerminator_ub_checks_intrinsic_corresponds`, `mir_evalTerminator_const_eval_select_intrinsic_corresponds`, `mir_evalTerminator_arith_offset_intrinsic_corresponds`, `mir_evalTerminator_bit_intrinsics_corresponds`, `mir_evalTerminator_wrapping_saturating_unchecked_intrinsics_corresponds`, and `mir_evalTerminator_comparison_and_layout_intrinsics_corresponds`).
- Exit code `0`.

## 3. Run Trusted Boundary & Governance Audit

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /home/groupagent-anneal-bot/Projects/markdittmer/anneal-wt-brief-1-3
python3 trusted/audit/check_trusted.py --fast
```

Expected output:
- `PASS: kernel dependency closure, statement-origin separation, and Cargo DAG boundary`
- `40 Trusted modules; 7578 Trusted kernel declarations; 15579 total replayed declarations; 11 claim theorem statements origin-checked; axioms=['propext', 'Classical.choice', 'Quot.sound']`
- Exit code `0`.
