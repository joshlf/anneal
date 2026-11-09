# Step-by-Step Reproduction Instructions for `BRIEF-1.1`

- **Item ID**: `BRIEF-1.1` (Function-Item Reification (`ReifyFnPointer`), `fnPtrToPtr` Casts, and Indirect `FnPtr` Calls)
- **Worktree**: `<path/to/anneal>`
- **Branch**: `adv/brief-1-1`
- **Base Commit (`sup/brief-1`)**: `d2851b0d778b90c2cb134350b3d7466361bcb3d1`
- **Adversarial Round Checkpoints (`N = 4`, 9 commits)**:
  1. `A0`: `7497891b` — `[adv A0] BRIEF-1.1: ReifyFnPointer, fnPtrToPtr, and indirect FnPtr calls`
  2. `B1`: `303ceb58` — `[adv B1] Fix synchronization of exact_div and add ReifyFnPointer callee signature validation`
  3. `A1`: `db1143f1` — `[adv A1] Fix checkCalleeSig docstrings/types, reject intrinsic fnPtrs, and support UnsafeFnPointer`
  4. `B2`: `0f69d718` — `[adv B2] Verify A1 changes`
  5. `A2`: `efcd40da` — `[adv A2] Enforce ReifyFnPointer(Safety) tag parity, reject intrinsic fnPtrToPtr, and tighten calleeLocalDeclsCompatible`
  6. `B3`: `c8ffb11e` — `[adv B3] Verify A2 changes`
  7. `A3`: `31ed7a27` — `[adv A3] Enforce ClosureFnPointer vs ReifyFnPointer target kind and guard indirect exact_div`
  8. `B4`: `28cc5de3` — `[adv B4] Verify A3 changes`
  9. `A4`: Final convergence & reproduction guide commit (`HEAD` of `adv/brief-1-1`)

## 1. Verify Worktree & Commit History

```bash
cd <path/to/anneal>
git status --porcelain
git log --oneline -10
```

Expected: `git status --porcelain` is empty and `git log --oneline -10` shows all 9 `[adv A0]`..`[adv A4]` checkpoints on top of `d2851b0d`.

## 2. Build `Trusted`, `Anneal`, and `Correspondence` (`L5_ControlAndCalls`) Modules

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd <path/to/anneal>/examples
lake build Trusted Anneal Correspondence.V2026_06_01.L5_ControlAndCalls Correspondence.V2026_08_01.L5_ControlAndCalls
```

Expected output:
- `Build completed successfully (69 jobs).`
- Kernel-checks `Trusted.Rustc.V2026_06_01.MirSemantics.{State,Places,Terminators}`, `Trusted.Rustc.V2026_08_01.MirSemantics.{State,Places,Terminators}`, `Correspondence.V2026_06_01.L5_ControlAndCalls`, and `Correspondence.V2026_08_01.L5_ControlAndCalls` (including `mir_evalRvalue_reifyFnPointer_and_fnPtrToPtr_chain`, `mir_evalRvalue_reifyFnPointer_callee_sig_and_unsafeFnPointer_corresponds`, `mir_fnPtr_data_deref_is_ub`, `mir_evalTerminator_indirect_call_and_tailCall_corresponds`, and `mir_evalTerminator_indirect_call_nonZeroOffset_or_borrow_is_ub`).
- Exit code `0`.

## 3. Run Trusted Boundary & Governance Audit

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd <path/to/anneal>
python3 trusted/audit/check_trusted.py --fast
```

Expected output:
- `PASS: kernel dependency closure, statement-origin separation, and Cargo DAG boundary`
- Exit code `0`.
