---
name: trust-review
description: >-
  Audit code changes, commits, and pull requests in joshlf/anneal to preserve
  Anneal's trust model and correctness promise. Use as a distinct review pass
  whenever reviewing changes or preparing modifications to verify both that code
  outside trusted/, ci/, and .github/ does not bypass trust auditing and that
  changes inside trusted/, ci/, .github/, and pinned root manifests preserve TCB
  soundness and enforcement completeness.
---

# Trust-boundary code review

Use this skill whenever reviewing code, commits, branches, or pull requests in
`joshlf/anneal`, or when auditing changes before committing.

Anneal's correctness promise in [`PRINCIPLES.md`](../../PRINCIPLES.md) depends
on a strict boundary documented in
[`docs/trust-model.md`](../../docs/trust-model.md): first-party trusted code
lives in [`trusted/`](../../trusted) (together with root manifests and the
vendored `vendor/lean-miri/` reference model pinned by hashes in `trusted/`),
and all code in `theory/` and `correspondence/` is untrusted and verified in
repository CI by [`trusted/audit/`](../../trusted/audit) (`anneal-audit`) to be
pure, effect-free, and within the locked foundation axiom allowlist.

Combine this skill with:

- [`comment-guidelines`](../comment-guidelines/SKILL.md) when reviewing or
  writing explanatory and citation comments in `trusted/`; and
- [`reader-oriented-explanation`](../reader-oriented-explanation/SKILL.md) and
  [`williams-style`](../williams-style/SKILL.md) when drafting review findings
  or documentation.

Reviewing changes under this skill does not authorize modifying repository
files, updating cryptographic lock manifests, weakening audit checks, or
approving, merging, or publishing a pull request.

## Run a distinct adversarial review pass

Do not fold trust-boundary review into a general code-review pass that checks
functionality, style, naming, or prose at the same time. In a combined pass,
high-frequency surface comments crowd out subtle cross-cutting boundary risks,
and reviewers default to a cooperative stance ("does this change do what the
author intended?") rather than an adversarial stance ("how could this change—or
an omission in it—subvert or bypass the trust model?").

Execute trust-boundary review as a dedicated pass:

1. **Inspect the complete change inventory:** Check all added, modified,
   renamed, and deleted paths, file modes, symlinks, and hidden dotfiles across
   the diff, not just isolated code hunks. Look both at what changed and at what
   companion updates (such as manifest hashes, pinned citations, or negative
   audit tests) are missing.
2. **Evaluate two distinct goals based on the affected paths:**
   - **Pass 1 (Enforcement-bypass audit outside `trusted/`, `ci/`, and
     `.github/`):** Run on every change that touches or adds files outside
     `trusted/`, `ci/`, and `.github/` to ensure untrusted code cannot
     intentionally or accidentally bypass `anneal-audit` or CI gates.
   - **Pass 2 (TCB and harness audit inside `trusted/`, `ci/`, `.github/`, and
     pinned root manifests):** Run whenever a change touches `trusted/`, `ci/`,
     `.github/`, or any root file pinned by
     [`trusted/root-manifest.sha256`](../../trusted/root-manifest.sha256)
     (`Cargo.toml`, `Cargo.lock`, `flake.nix`, `flake.lock`). If a diff touches
     none of these paths, skip Pass 2.
3. **In single-pass PR review environments:** When operating as a single-turn
   automated pull request reviewer that cannot spawn a separate pass, evaluate
   Pass 1 and (when triggered) Pass 2 first. Whenever a change raises a boundary
   question or touches `trusted/`, `ci/`, `.github/`, or pinned root manifests,
   report a `### Trust-Boundary Assessment` before general comments when the
   host permits prose. Otherwise use permitted summary or status fields, or
   another already authorized reporting channel. If none exists, omit the
   narrative, not the assessment, and return only schema-supported findings.
   Follow the [reporting
   fallback](../change-review/SKILL.md#report-within-the-hosts-constraints)
   for findings-only output and incomplete reviews; never fabricate a finding
   to carry the assessment.

## Complete the trust assessment

Use [`change-review`](../change-review/SKILL.md) for candidate identity,
coverage, finding verification, and the author's review-fix loop. This skill
retains ownership of the trust requirements below. Account for every changed
path under each applicable trust goal, including absent companion updates;
record why a goal is inapplicable rather than silently skipping it.

Continue after finding a bypass or unsoundness issue. Before concluding, sweep
for other affected boundaries and report every distinct supported violation.
Keep blocked checks and unresolved trust questions distinct from confirmed
findings and use the reporting fallback above. An incomplete trust pass is not
trust acceptance, and a local trust assessment does not grant hosted approval
or permission to merge.

## Pass 1: Audit changes outside `trusted/`, `ci/`, and `.github/` for bypasses

Code outside `trusted/`, `ci/`, and `.github/` (such as `theory/`,
`correspondence/`, tests, workspace configurations, or new directories) is
untrusted. Although `anneal-audit` and CI scripts are designed to enforce purity
mechanically, parts of the target architecture in
[`docs/trust-model.md`](../../docs/trust-model.md) are still evolving and any
static checker can have blind spots. Check every change outside the TCB for
intentional or accidental enforcement bypasses:

1. **Unchecked effectful code or build hooks outside `trusted/`:**
   - Reject any new Rust crate, `build.rs` script, procedural macro, Makefile,
     `lakefile.lean`, or shell/Python script outside `trusted/` that could
     execute arbitrary code during `cargo test`, `nix build`, `lake`, or
     developer workflows without being blocked by `anneal-audit`.
   - Reject ambient toolchain or compiler configuration files at the repository
     root or in subdirectories (such as `.cargo/config.toml`, `rust-toolchain`,
     `rust-toolchain.toml`, `.envrc`, or editor/plugin hooks) that could alter
     `rustc` flags, `RUSTC_WRAPPER`, linker behavior, or dependency sources.
2. **Filesystem, module-discovery, and artifact evasion:**
   - Check that no `.lean` files are placed in directories or naming layouts
     outside the trees verified by `anneal-audit` (`trusted/lean/`, `theory/`,
     `trusted/correspondence/`, `correspondence/`, and the SHA-256-pinned
     `vendor/lean-miri/` reference model), and that no symlinks, hardlinks, git
     submodules, or pre-compiled `.olean`, `.ilean`, or `.ir` artifacts are
     introduced into the source tree.
   - For any change touching `vendor/lean-miri/` (which bypasses Phase 1
     syntactic preflight and belongs to the correspondence TCB), verify the
     upstream commit and tree pin (`LOCKED_MIRI_COMMIT`,
     `vendor_tree.manifest_sha256`), the closed `LOCKED_PATCHED_MIRI_FILES`
     allowlist, the `LOCKED_UPSTREAM_PIN_SHA256` digest lock in
     [`trusted/audit/src/miri_pin.rs`](../../trusted/audit/src/miri_pin.rs),
     and human audit of any compile-time code (`run_cmd`, `initialize`, custom
     tactic `elab`s) in vendored or patched modules.
   - Watch for path-normalization tricks, case-collision filenames, or Unicode
     homoglyphs and bidirectional/invisible control characters in module or
     identifier names.
3. **Lean syntax, elaborator, or attribute blind spots in `theory/` and
   `correspondence/`:**
   - Verify that `.lean` files in `theory/` and `correspondence/` use only pure
     declarations and tactics (and that `trusted/lean/` and
     `trusted/correspondence/` remain tactic-free). Flag any construct that
     attempts to run metaprograms, read files or environment variables, or
     alter elaboration or compiler behavior—even if
     [`TrustedBoundary.lean`](../../trusted/audit/TrustedBoundary.lean)'s
     syntactic preflight (`allowedTrustedSyntaxKinds`,
     `allowedTheoryTacticKinds`, and `inspectNodeKind`) failed to reject that
     specific syntax shape.
   - Confirm that code outside `trusted/lean/` and `trusted/correspondence/`
     never declares constants in the `Trusted` root namespace, never includes
     `-- anneal-trust-tier:` directives, and never introduces `axiom`, `sorry`,
     `unsafe`, `partial`, `noncomputable section`, `opaque`, `native_decide`,
     `decide!`, `bv_decide`, `rfl'`, `grind`, tactic `configItem` flags
     (`+native`, `+kernel`), `by_elab`, `#eval`, `set_option`, `initialize`,
     `@[implemented_by]`, `@[extern]`, or `@[csimp]`. (`noncomputable`
     declaration modifiers are admitted mechanically across all roles and both
     passes by `allowedCommandSyntaxKinds`, while `noncomputable section` is
     forbidden mechanically and repository policy keeps `theory/` free of
     `noncomputable` definitions; unlike `theory/`, `correspondence/` modules
     may use `noncomputable def`.)
4. **Vacuous or misleading specifications at the `trusted/`–`theory/` seam:**
   - Check that lowering passes (`Abstracts`), weakest-precondition rules, and
     specification helpers in `theory/` do not discharge obligations via
     contradictory preconditions, tautological postconditions, or weakened
     intermediate predicates that make an unverified or trivial claim appear to
     test or prove a stronger property.

## Pass 2: Audit `trusted/`, `ci/`, `.github/`, and pinned root manifests

When a change touches `trusted/`, `ci/`, `.github/`, or any root file pinned by
[`trusted/root-manifest.sha256`](../../trusted/root-manifest.sha256), audit the
affected components against these requirements:

### 1. Semantic definitions and module tiers (`trusted/lean/`)

- **Rust semantic fidelity and fail-closed behavior:** Definitions in
  `trusted/lean/` must faithfully reflect Rust operational semantics and must
  never "fail open" by treating undefined behavior or unsupported constructs as
  no-ops or trivially valid states.
- **Mandatory pinned citations:** Every declaration or rule in `trusted/lean/`
  that claims to model Rust semantics must explain the correspondence in its
  comments and both quote and cite the applicable Rust Reference section
  (`rust-lang/reference`) or compiler source (`rust-lang/rust`) at a pinned
  commit hash.
- **Statement-Origin Separation:** Verify that the obligation definitions
  `Trusted.MirSemantics.CrateTheorem` and `UnitTheorem`, like every other
  `trusted/lean/` constant, reference only `Init.*` and `Trusted.*` constants,
  never `theory/` or `correspondence/` constants (`Anneal.*`).
- **Module trust-tier discipline (`-- anneal-trust-tier:`):** Every `Trusted.*`
  module must carry an accurate `-- anneal-trust-tier: vetted` or
  `-- anneal-trust-tier: candidate:<feature>` directive. Ensure that new or
  unreviewed semantics use `candidate:<feature>` rather than `vetted`, and that
  `vetted` modules never import or reference `candidate:<feature>` modules.

### 2. Compiler fact extraction and proof emission (`trusted/rustc-capture/`)

- **1:1 capture without semantic normalization:** `rustc-capture` must translate
  `Runtime(PostCleanup)` MIR and compiler facts directly into `Trusted` AST
  structures. Control-flow restructuring, expression simplification, and
  semantic desugaring must live in `theory/` where their soundness is proven in
  Lean, not in unverified Rust capture code.
- **Fail-closed translation and late-error guards:** Unsupported MIR statements,
  terminators, types, intrinsics, or attributes must produce hard errors rather
  than fallback defaults or skipped obligations, and capture must abort whenever
  `tcx.dcx().has_errors()` indicates compiler diagnostics. Capture must also
  refuse items whose captured body is not what calls execute, such as
  `#[rustc_intrinsic]` definitions (rustc lowers their calls without running
  the fallback body).
- **Emitted Lean integrity:** Generated Lean files (`Captured.lean`, and the
  runner-generated `Expected.lean` in `cargo-anneal verify`) must remain pure
  and deterministic, and must never allow crate names, identifiers, or
  annotation strings to inject raw Lean commands or alter the canonical
  `Expected.claim` statement. Nominal identities that specifications can name
  (such as `EnumTy.id`) must not depend on unrelated items in the crate.
- **Mandatory pinned `rustc` citations:** Code extracting `rustc` internal types
  (`TyCtxt`, `Body`, layouts, regions, ABI facts) must explain the
  correspondence and both quote and cite `rust-lang/rust` at a pinned commit
  hash.

### 3. Auditor, target inspector, and locks (`trusted/audit/`, lock files)

- **No silent weakening of `anneal-audit` or target acceptance:** Scrutinize
  any modification to:
  - the repository auditor in [`trusted/audit/src/`](../../trusted/audit/src):
    `cargo_boundary.rs` (Cargo containment, `.cargo`/`rust-toolchain*`
    rejection, and `bundled_resources.rs` parity), `miri_pin.rs`
    (`vendor/lean-miri/` pin and sysroot manifest), and `repo_audit.rs` (Pass
    1 and Pass 2 orchestration); `lib.rs` only re-exports them;
  - the enforcement substrate that `anneal-audit` shares with
    `cargo-anneal verify` in
    [`trusted/cargo-anneal/src/`](../../trusted/cargo-anneal/src):
    `toolchain.rs` (lock record types and the `LOCKED_*` toolchain
    constants), `stage.rs` (environment allowlist, Lean and lock admission,
    compile flags, inspector invocation, and result acceptance), `bundle.rs`
    (embedded bundle inventory and rendering), `target.rs` (target roles,
    module names, and `library-lock.json` digest admission), and `verify.rs`
    (capture invocation, reserved module names, and the `result.json`
    receipt); and
  - [`TrustedBoundary.lean`](../../trusted/audit/TrustedBoundary.lean),
    including its `"headers"` and `"target-audit"` modes.

  Flag any change that:
  - expands `allowedCommandKinds`, `allowedDeclarationKinds`,
    `allowedAttributeNames`, `allowedTrustedSyntaxKinds`,
    `allowedTheoryTacticKinds`, or the foundation axiom allowlist without a
    sound justification;
  - relaxes structural node checks in `inspectNodeKind` or `inspectSyntax`;
  - relaxes Cargo workspace containment (`check_cargo_boundary`), source-tree
    regular-file checks (`scan_lean_tree`), or environment variable stripping;
  - weakens synchronous compilation flags (`-DElab.async=false`,
    `-Ddebug.skipKernelTC=false`), `.olean` loading (`trustLevel := 0`,
    `plugins := #[]`, and `loadExts := false` without
    `enableInitializersExecution` in `"audit"`, `"correspondence-audit"`, and
    every `"target-audit"` import), `checkDeclarationEdges`, or fresh kernel
    replay (`base.toKernelEnv.replay`). Note that `"correspondence-preflight"`
    intentionally imports with `loadExts := true`, `level := .private`, and
    `enableInitializersExecution`, which executes pinned vendored `[init]`
    initializers (able to register user-defined environment extensions),
    evaluates pinned vendored tactic `elab`s, and deserializes compiled Pass 1
    `theory/` extension data inside the inspector process; flag any weakening
    of Pass 1's closed `theory/` attribute allowlist or vendored compile-time
    code review controls;
  - relaxes `"target-audit"` acceptance: the canonical claim built from
    role-authenticated kernel names, the kind, universe, `Prop`, and
    canonical-input role gates, the fixed three-axiom policy, `TargetRole`
    import and declaration-edge checks, `@[implemented_by]`, `@[extern]`, and
    `@[csimp]` metadata rejection, or replay of every reached library and
    source declaration onto `foundation-lock.json`; or
  - relaxes target staging admission: reserved module names (`Trusted`,
    `Trusted.*`, `Anneal`, `Anneal.*`, `Captured`, and `Expected`),
    module-name overlap with foundation or `library-lock.json` modules, or
    `library-lock.json` catalog and digest checks.
- **Negative regression tests:** Any change to admission rules, syntax filters,
  tier checks, or target acceptance must include negative tests verifying that
  prohibited inputs fail closed (policy exit code `1` for `anneal-audit` and
  `TrustedBoundary.lean`, or non-zero exit code `2` for standalone
  kernel-replay rejections):
  [`boundary_audit.rs`](../../trusted/audit/tests/boundary_audit.rs) and the
  `trusted/audit/src/` unit tests for repository audits,
  [`target_audit.rs`](../../trusted/audit/tests/target_audit.rs) for
  `"target-audit"`, `trusted/cargo-anneal/src/` unit tests or
  [`mvp_e2e.rs`](../../trusted/cargo-anneal/tests/mvp_e2e.rs) for target
  staging and receipts, and
  [`typed_capture.rs`](../../trusted/rustc-capture/tests/typed_capture.rs) for
  capture refusals.
- **Cryptographic lock synchronization:** When `Cargo.toml`, `Cargo.lock`,
  `flake.nix`, `flake.lock`, the Lean binary, sysroot `.olean` files, or
  `vendor/lean-miri/` change, verify that
  [`trusted/root-manifest.sha256`](../../trusted/root-manifest.sha256),
  [`foundation-lock.json`](../../trusted/lean/foundation-lock.json)
  (`trusted/lean/foundation-lock.json`),
  [`library-lock.json`](../../trusted/audit/library-lock.json)
  (`trusted/audit/library-lock.json`, whose `toolchain` and module digests
  must match the pinned Lean sysroot),
  [`UPSTREAM_PIN.json`](../../vendor/lean-miri/UPSTREAM_PIN.json), and the
  corresponding `LOCKED_*` constants in
  [`trusted/cargo-anneal/src/toolchain.rs`][toolchain-rs]
  and [`trusted/audit/src/miri_pin.rs`](../../trusted/audit/src/miri_pin.rs)
  (`LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256`, `LOCKED_UPSTREAM_PIN_SHA256`,
  `LOCKED_MIRI_COMMIT`, `LOCKED_PATCHED_MIRI_FILES`) are updated in lockstep
  and that the underlying dependency, toolchain, or vendored change is audited.
  Whenever a file in `BUNDLE_SOURCES` or `PROVENANCE_SOURCES`
  (`trusted/cargo-anneal/src/bundle.rs`) changes, including
  `TrustedBoundary.lean`, either lock file, `UPSTREAM_PIN.json`, and the
  correspondence sources, verify that
  [`bundled_resources.rs`](../../trusted/cargo-anneal/src/bundled_resources.rs)
  was regenerated with
  `cargo run --locked -p cargo-anneal --example regenerate_bundle -- --root .`.

### 4. CLI orchestrator and dependencies (`trusted/cargo-anneal/`, `Cargo.*`)

- **Orchestration integrity:** Verify that `cargo-anneal` does not allow ambient
  environment variables, target-crate configuration files, working-directory
  files (such as a relative capture-tool path), or CLI flags to skip Lean
  kernel checking, substitute an unverified toolchain archive or capture
  adapter, or suppress verification errors, and that `result.json` receipts
  never claim more authentication than the runner performed.
- **Dependency discipline:** Check any added or updated crate in `Cargo.toml`
  and `Cargo.lock` against [`AGENTS.md`](../../AGENTS.md): prefer standard,
  well-audited crates over hand-rolled plumbing, keep transitive dependency
  trees conservative, and ensure all dependencies come from pinned `crates.io`
  checksums.

### 5. CI workflows and scripts (`ci/`, `.github/workflows/`)

- **Mandatory CI gates:** Verify that
  [`.github/workflows/ci.yml`](../../.github/workflows/ci.yml) verifies
  `trusted/root-manifest.sha256` (`sha256sum --check --strict`), checks for
  forbidden `.cargo` and `rust-toolchain*` paths, runs
  `cargo run --locked -p anneal-audit`, and requires every job in the
  fail-closed `all-jobs-succeed` gate (enforced by
  [`ci/check_job_dependencies.sh`](../../ci/check_job_dependencies.sh)).
- **Privilege, action pinning, and cache isolation:** Ensure workflows keep
  `permissions: contents: read`, pin third-party GitHub Actions to full
  40-character commit SHAs, strip `ACTIONS_CACHE_URL`, `ACTIONS_RESULTS_URL`,
  and `ACTIONS_RUNTIME_TOKEN` in jobs running scripts outside `trusted/`, and
  never allow cached artifacts to bypass `anneal-audit` or shadow source
  changes.

## Report findings with clear evidence and scope

Treat any confirmed or plausible violation of Pass 1 (enforcement bypass) or
Pass 2 (TCB unsoundness or audit weakening) as a blocking review finding.

When reporting a finding:

1. **Cite the exact location and invariant:** Identify the file, line range or
   declaration, and the specific guarantee in
   [`PRINCIPLES.md`](../../PRINCIPLES.md),
   [`docs/trust-model.md`](../../docs/trust-model.md), or `anneal-audit` that is
   undermined or bypassed.
2. **Explain the concrete failure or bypass mechanism:** State how an untrusted
   input, `theory/` module, build step, or edge case could exploit or trigger
   the flaw.
3. **Distinguish confirmed defects from open verification questions:** When a
   finding depends on an unverified assumption (for example, whether a Lean
   parser production can be reached or how an external tool handles a path),
   state the hypothesis and what check or test would resolve it rather than
   asserting an unverified failure as fact.

[toolchain-rs]: ../../trusted/cargo-anneal/src/toolchain.rs
