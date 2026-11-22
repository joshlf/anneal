<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal Lean 4 Workbench (`workbench`)

Self-contained Lean 4 (`v4.34.1`) utility library, reflective solver pack,
exploration harness, and host diagnostic toolkit for Anneal development and
prototyping.

See [`AGENTS.md`](AGENTS.md) for branch governance and [`CATALOG.json`](CATALOG.json)
for the machine-readable inventory of modules, declarations, badges, and CLI
scripts.

## Directory layout

- `lean/` — Standalone zero-dependency Lake workspace (`Workbench`):
  - `Workbench/Pass1/` (`pass1_portable` — `prelude` + 51 locked `Init.*`
    modules, zero `._unsafe_rec`, allowed Pass-1 tactics only):
    - `InitLemmas.lean`: Consolidated `Bool`/`ite`/`dite`, generic `BEq`
      bridges, `Nat` power/div/mod, constructive `IntBalance`, and `@Nat.rec`
      total list/slice lemmas.
    - `Firewall.lean`: 1-field `Prop` structure `Firewall tag P` and
      zero-`Prop`-argument `IndexedCut` barriers preventing `whnf` and
      `rw`/`simp` AST blowups.
    - `SpineForce.lean`: $O(1)$ `@Nat.casesOn` numeral history stripper
      (`withStrictNat`), CPS spine-forcing (`forceNat`, `forceList`,
      `forceOption`), shallow $2^d$ stepper (`runPow2`), and bounded quantifier
      reflector (`checkRange_sound`).
    - `PTree.lean`: Canonical Appel-Leroy positive binary radix trie with
      zero-axiom extensionality (`ptree_eq_of_get`) and deterministic
      separation-logic framing (`PTree.diffWith` / `ptree_diffWith_sound`).
    - `LinearArith.lean`: Sparse `Nat` & `Int` Farkas + Chvatal-Gomory GCD
      floor-cut certifier (`checkNatCutGoal_sound`, `checkIntCutGoal_sound`) —
      drop-in Pass-1 replacement for `omega`.
    - `BitTrieLrat.lean`: Radix-2 trie RUP/LRAT propositional UNSAT checker
      (`checkRupProof_sound`) — drop-in Pass-1 replacement for boolean
      `bv_decide`.
    - `ClassicalEm.lean`: Diaconescu's `prop_em : p ∨ ¬ p`, `by_contra`, and
      `chooseExists` over `prelude` + `Init.Core` without `Init.Classical`
      (replacing banned `by_cases` via `cases prop_em P`).
  - `Workbench/Lab/` (`lab_meta` — rapid falsification & profiling):
    - `Counterexample.lean`: SplitMix64 + boundary-seed counterexample search
      (`findCounterexample1/2/3`) and 3-axis spec vacuity/output-sensitivity
      probing (`probeSpecHealth`).
    - `KernelBench.lean`: `Lean.Expr` unique-node DAG vs. unfolded tree profiler
      (`measureExpr`, `profileDecl`).
- `scripts/` — Standalone Python 3.10+ CLI diagnostics (`--help`, `--json`):
  - `proof_health_scan.py`: `<50ms` static Pass-1 `TrustedBoundary` scanner
    (catches banned tactics, missing `prelude`, disallowed imports, `>=33`-item
    list literals, and cross-module `.eq_1` diamond hazards).
  - `preflight_syntax_check.py`: Exact non-elaborating Lean 4 `Parser` CST
    allowlist validator mirroring `TrustedBoundary.lean` (`--role theory` or
    `--role trusted`).
  - `audit_lean_hygiene.py`: Compiled `Lean.Environment` inspector pinpointing
    `._unsafe_rec` parent definitions, `isPartial`/`isUnsafe` leaks,
    out-of-namespace `realizeConst` `.eq_1` emissions, `sorryAx`, and
    non-standard axioms (`_native.*` / `Lean.ofReduceBool`).
  - `replay_audit_lean.py`: Compiles any standalone `.lean` file (no Lake
    project required) with `-DElab.async=false -Ddebug.skipKernelTC=false` and
    runs fresh `trustLevel := 0`, `loadExts := false` `Kernel.Environment.replay`
    plus optional namespace reachability checks.
  - `olean_profiler.py`: Ranks `.olean` sizes and per-declaration `Expr`
    DAG/tree node hotspots.
  - `farkas_cert_gen.py`: Synthesizes verified `Workbench.Pass1.LinearArith`
    `CutStep` certificates directly from linear `Nat` or `Int` inequalities.
  - `split_lean_module.py`: Analyzes declaration dependency DAGs and cross-chunk
    `unfold`/`simp` `.eq_1` hazards to plan safe splits of multi-thousand-line
    Lean files.
- `tools/workbench.py` — Regenerates `CATALOG.json` (`catalog`) and runs all
  self-validation checks (`check`).
- `tests/test_workbench.py` — Unit tests for host scripts and validators.

## Quickstart

```bash
# Validate everything (static Pass-1 scan, unit tests, Lake build, env audit)
python3 tools/workbench.py catalog
python3 tools/workbench.py check

# Synthesize a Pass-1 replacement for `omega` (including parity/stride cuts)
python3 scripts/farkas_cert_gen.py --domain nat \
  --hyp "2*i + 1 <= 2*n" --goal "i < n"

# Statically scan an Anneal theory/ or correspondence/ file in <50ms
python3 scripts/proof_health_scan.py --pass1 path/to/Module.lean

# Audit compiled Lean modules for `._unsafe_rec` and non-standard axioms
python3 scripts/audit_lean_hygiene.py --lake-dir lean --module Workbench.Pass1
```
