# Reproduction Instructions for `BRIEF-4.1`: Well-Typed Signature & Generic Parameter Lowering

## 1. Environment & Worktree Setup

```bash
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal>
git status --short --branch
git log -n 9 --oneline
```

Expected branch and adversarial pass history (`A0` through `A4`):
- Branch: `adv/brief-4-1`
- Checkpoints:
  - `[adv A0] 694cda87` — Implement signature-typed predicates and polymorphic obligation lowering for BRIEF-4.1
  - `[adv B1] 5110be69` — Harden signature-typed predicates and polymorphic obligations for BRIEF-4.1
  - `[adv A1] 1a5a60b3` — Fix ADT fieldLayouts & ScalarPair signature checks and add polymorphic scaffold tests
  - `[adv B2] 6589c79c` — Fix sub-borrow/slice signature checks, polymorphic Verify certificates, and closed gap lint
  - `[adv A2] e317aed2` — Fix MaybeUninit union/Range/enum-variant signature checks, poly claim detection, and add MirVerification signature suite
  - `[adv B3] 16296269` — Guard monomorphic certificates, drop layout-adjacency guesses, and fix pointer/niche/dyn/enum signature checks
  - `[adv A3] 55f6e6db` — Gate single-variant positional adtArgs and enforce borrow range lower/length bounds
  - `[adv B4] 6ad44aef` — Type only Range/UnsafeCell fields positionally, map ScalarPair fields by offset, and validate sub-place borrows
  - `[adv A4]` (`HEAD`) — Validate subslice/projected-array wide slice borrows and add `REPRODUCE_BRIEF_4_1.md`

## 2. Kernel-Checked Lean Build (`Trusted`, `Anneal`, `MirVerification`)

```bash
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal>/examples && \
  lake build Trusted Anneal MirVerification
```

Expected output:
```text
Build completed successfully (62 jobs).
```

## 3. Rust Obligation Generator & Scaffold Unit Tests (`cargo-anneal`)

```bash
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal> && \
  cargo test -p cargo-anneal --lib
```

Expected output:
```text
running 39 tests
...
test obligations::tests::renders_signature_and_polymorphic_obligations ... ok
test scaffold::tests::detects_polymorphic_proofs_across_all_claim_surfaces ... ok
...
test result: ok. 39 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out
```

## 4. Trusted Kernel Boundary, Origin-Separation & `check_todo.sh` Gate

```bash
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd <path/to/anneal> && \
  python3 trusted/audit/check_trusted.py --fast && \
  ./ci/check_todo.sh
```

Expected output:
```text
PASS: kernel dependency closure, statement-origin separation, and Cargo DAG boundary
40 Trusted modules; 7767 Trusted kernel declarations; 16014 total replayed declarations; 11 claim theorem statements origin-checked; axioms=['propext', 'Classical.choice', 'Quot.sound']
```

## 5. Summary of Verified Deliverables

1. **Trusted Signature-Typed Predicates (`trusted/lean/Trusted/VerificationResult.lean`)**:
   - `argsMatchSignature`, `retMatchesSignature`, `valueMatchesTyAndLayout`, `valueMatchesRigidTyAndLayout`, `valueMatchesLayoutOnly`, `resolveChildLayout`, `sigPtrLiveForRef`, `sigScalarNicheHolds`, `sigFieldMatchesBackendRepr`, `sigStructFieldsAreTypeArgs`, `sigEnumPayloadsAreTypeArgs`, and `signatureIsMonomorphic`.
2. **Polymorphic & Signature-Typed Obligation Generation (`crates/cargo-anneal/src/obligations.rs` & `crates/cargo-anneal/src/scaffold.rs`)**:
   - Emits `sigPre` (`argsMatchSignature`) and `sigPost` (`retMatchesSignature`) across generated obligation modules; emits `polyClaim`, `polyStatefulClaim`, `polyTotalClaim`, `polyModularClaim`, `polyUbExceptionClaim` (`TypeSubst → ...`) via `Mir.mirBody.instantiate subst` when `type_param_count > 0`, and guards monomorphic certificates in `Verify.lean` with `signatureIsMonomorphic Mir.mirBody = true`.
3. **Kernel-Checked Proof Suites (`theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean` & `examples/mir/MirVerification.lean`)**:
   - `sig_scalars_validated`, `sig_thin_ref_validated`, `sig_wide_slice_validated`, `sig_composites_and_adts_validated`, `sig_polymorphic_instantiate_validated`, `sig_subborrow_and_slice_offset_validated`, `example_signature_predicates_and_polymorphic_obligations`, `example_capture_shaped_signature_predicates`, `example_dyn_and_extern_reference_signatures`, `example_generic_enum_payload_signatures`, `example_layoutless_fields_and_subplace_borrows`, and `example_signature_monomorphic_guard`.
