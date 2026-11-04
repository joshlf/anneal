# Step-by-Step Reproduction Instructions for `BRIEF-1.2`

- **Item ID**: `BRIEF-1.2` (Diverging Calls (`target = .none`) and Unwind Cleanup Terminators (`unwindResume`, `unwindTerminate`))
- **Worktree**: `/home/groupagent-anneal-bot/Projects/markdittmer/anneal-wt-brief-1-2`
- **Branch**: `adv/brief-1-2`
- **Base Commit (`adv/brief-1-1`)**: `f515de96b6f6e123139680516e77ff985d3d53a8`
- **Adversarial Round Checkpoints (`N = 4`, 9 commits)**:
  1. `A0`: `9b028a60` — `[adv A0] BRIEF-1.2: Diverging calls and unwind terminators`
  2. `B1`: `1e66cfa8` — `[adv B1] Fix diverging call shadowing precedence for unreachable`
  3. `A1`: `04f64a17` — `[adv A1] Guard unlinked diverging inline targets on direct calls and strengthen correspondence theorems`
  4. `B2`: `96665b37` — `[adv B2] Add indirect diverging call coverage to universal indirect call theorems`
  5. `A2`: `9bb01935` — `[adv A2] Expand core panic/panic_impl entrypoints and certify non-diverging callee unwind propagation`
  6. `B3`: `f3f8bd17` — `[adv B3] Complete panic entrypoints in mir_evalTerminator_diverging_call_panic_entrypoints`
  7. `A3`: `d4c2f5a2` — `[adv A3] Add 4-way unlinked diverging call partition and multi-step callee cleanup/unwindResume chain theorems`
  8. `B4`: `924d3971` — `[adv B4] Add 4th missing branch for external unlinked calls to partition theorem`
  9. `A4`: Final convergence & reproduction guide commit (`HEAD` of `adv/brief-1-2`)

## 1. Verify Worktree & Commit History

```bash
cd /home/groupagent-anneal-bot/Projects/markdittmer/anneal-wt-brief-1-2
git status --porcelain
git log --oneline -10
```

Expected: `git status --porcelain` is empty and `git log --oneline -10` shows all 9 `[adv A0]`..`[adv A4]` checkpoints on top of `f515de96`.

## 2. Build `Trusted`, `Anneal`, and `Correspondence` (`L5_ControlAndCalls`) Modules

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /home/groupagent-anneal-bot/Projects/markdittmer/anneal-wt-brief-1-2/examples
lake build Trusted Anneal Correspondence.V2026_06_01.L5_ControlAndCalls Correspondence.V2026_08_01.L5_ControlAndCalls
```

Expected output:
- `Build completed successfully (69 jobs).`
- Kernel-checks `Trusted.Rustc.V2026_06_01.MirSemantics.{State,Terminators}`, `Trusted.Rustc.V2026_08_01.MirSemantics.{State,Terminators}`, `Correspondence.V2026_06_01.L5_ControlAndCalls`, and `Correspondence.V2026_08_01.L5_ControlAndCalls` (including `mir_applyUnwindAction_characterization`, `mir_evalTerminator_return_root_and_caller`, `mir_evalTerminator_call_transparent_and_unreachable_unchecked`, `mir_evalTerminator_indirect_call_and_tailCall_corresponds`, `mir_evalTerminator_indirect_call_nonZeroOffset_or_borrow_is_ub`, `mir_evalTerminator_diverging_call_args_and_unreachable`, `mir_evalTerminator_diverging_call_linked_callee_corresponds`, `mir_evalTerminator_diverging_call_panic_entrypoints`, `mir_evalTerminator_diverging_call_external_corresponds`, `mir_evalTerminator_unwindResume_and_unwindTerminate_corresponds`, `mir_evalTerminator_callee_unwind_and_external_resume_corresponds`, and `mir_evalTerminator_diverging_call_partition_and_cleanup_chain`).
- Exit code `0`.

## 3. Run Trusted Boundary & Governance Audit

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /home/groupagent-anneal-bot/Projects/markdittmer/anneal-wt-brief-1-2
python3 trusted/audit/check_trusted.py --fast
```

Expected output:
- `PASS: kernel dependency closure, statement-origin separation, and Cargo DAG boundary`
- `40 Trusted modules; 7186 Trusted kernel declarations; 15187 total replayed declarations; 11 claim theorem statements origin-checked; axioms=['propext', 'Classical.choice', 'Quot.sound']`
- Exit code `0`.
