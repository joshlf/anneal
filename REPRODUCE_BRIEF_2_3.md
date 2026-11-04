# Step-by-Step Reproduction Instructions for `BRIEF-2.3`

- **Item ID**: `BRIEF-2.3` (Direct Polymorphic & Trait-Impl Emission in `anneal-rustc-capture`)
- **Worktree**: `/home/groupagent-anneal-bot/Projects/markdittmer/anneal-wt-brief-2-3`
- **Branch**: `adv/brief-2-3` (merged into `sup/brief-2` at `/home/groupagent-anneal-bot/Projects/markdittmer/anneal-wt-brief-2`)
- **Base Commit (`sup/brief-2` / `BRIEF-2.1`)**: `f4e8bf6b2a3d88c25fd5adf75968a827c1c64f8a`
- **Adversarial Round Checkpoints (`N = 4`, 9 commits)**:
  1. `A0`: `2607babb` — `[adv A0] Direct Polymorphic & Trait-Impl Emission`
  2. `B1`: `11641c15` — `[adv B1] Harden polymorphic layout slots, parent/method generics, and Lean kernel instantiation tests`
  3. `A1`: `43c32eb6` — `[adv A1] Audit B1: Confirm flawless compound layout propagation and generic parameter densification`
  4. `B2`: `a1436b6f` — `[adv B2] Harden inherent impl self_ty specialization detection and verify mixed-field generic struct layouts`
  5. `A2`: `bda5b007` — `[adv A2] Audit B2: Confirm diagonal and partial generic impl path disambiguation`
  6. `B3`: `ea1f6f71` — `[adv B3] Fix submodule generic type-invariant subject resolution and verify generic companion specs`
  7. `A3`: `6d8be20c` — `[adv A3] Audit B3: Confirm generic submodule invariant subject resolution`
  8. `B4`: `3913c186` — `[adv B4] Reject non-array trait_impls in UnitCaptureManifest and add polymorphic lean_emit & manifest round-trip tests`
  9. `A4`: Final convergence & reproduction guide commit (`HEAD` of `adv/brief-2-3` and `sup/brief-2`)

## 1. Verify Worktree & Commit History

```bash
cd /home/groupagent-anneal-bot/Projects/markdittmer/anneal-wt-brief-2-3
git status --porcelain
git log --oneline -10
```

Expected: `git status --porcelain` is empty and `git log --oneline -10` shows all 9 `[adv A0]`..`[adv A4]` checkpoints on top of `f4e8bf6b`.

## 2. Run `anneal-rustc-capture` Unit, Integration & Lean 4 Kernel Instantiation Suite

```bash
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd /home/groupagent-anneal-bot/Projects/markdittmer/anneal-wt-brief-2-3
cargo test -p anneal-rustc-capture
```

Expected output:
- `5 passed; 0 failed` in `src/lib.rs` (including `lean_emit::tests::emit_polymorphic_module_with_trait_impl_and_alias` and `manifest::tests::unit_capture_manifest_round_trip`).
- `9 passed; 0 failed` in `src/main.rs` (including `rustc_2026_06_01::tests::driver_captures_generic_functions_and_trait_impls`, which compiles `demo_generics.rs` via `anneal-rustc-capture`, verifies `RigidTy.param`, `RigidTy.alias`, dense 0-based generic parameter indexing across parent/method generics, collision-free `canonical_def_path` across specialized/diagonal inherent and trait `impl`s, `TraitImplEntry` emission in Lean and `UnitCaptureManifest.json`, and runs `lean` kernel verification on `VerifyPolymorphicCapture.lean` proving `rfl` instantiation theorems over `CapturedMir.instantiate`).
- Exit code `0`.

## 3. Run Trusted Boundary & Governance Audit

```bash
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd /home/groupagent-anneal-bot/Projects/markdittmer/anneal-wt-brief-2-3
python3 trusted/audit/check_trusted.py --fast
```

Expected output:
- `PASS: kernel dependency closure, statement-origin separation, and Cargo DAG boundary`
- Exit code `0`.
