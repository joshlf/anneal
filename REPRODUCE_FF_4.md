<!--
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-->

# Reproduction & Closeout Guide: Workstream FF-4 (`sup/ff-4`)

Workstream `FF-4` completes the migration, upstream semantic integration, CLI
tooling/guidance, and self-contained reference-corpus reporting for Anneal's
fuel-free MIR program lifters (`#mir_lift`, `#mir_lift_spec`, `forRangeUp` +
`runCfgToBlock`) and two-tier alias-erasure discipline (`Anneal.PureMirExec` +
`Anneal.SepLogicLenses`).

For unit-level details, see `REPRODUCE_FF_4_1.md`, `REPRODUCE_FF_4_2.md`,
`REPRODUCE_FF_4_2B.md`, and `REPRODUCE_FF_4_3.md`.

> [!WARNING]
> **`[diversity-reduced]` & Reserve-Fallback 3rd-Party Audit Notice**
>
> - **`FF-4.1` (`P0`, $N=4$)**: `ff41-a = model-family-y-primary`
>   (`Model Y`), `ff41-b = model-family-x-primary` (`Model X`) -> switched to
>   `supervisor-model-primary` (`Model Z`) on Pass `B4` (`[diversity-reduced]`).
> - **`FF-4.2` (`P1`, $N=4$)**: `ff42-a = model-family-x-primary` (`Model X`),
>   `ff42-b = model-family-y-primary` (`Model Y`) -> switched to
>   `supervisor-model-primary` (`Model Z`) on Pass `B4` (`429` at `0.0%` `Model Y`
>   quota). Cross-family `Claude <-> Gemini` diversity held across all 9 passes,
>   with `diversity_reduced=true` recorded for reserve-pool fallback.
> - **`FF-4.2b` (`P1`, $N=2$)**: `ff42b-a = model-family-x-primary` (`Model X`),
>   `ff42b-b = supervisor-model-primary` (`Model Z` substituting for `0.0%`
>   `Model Y`). Cross-family `Claude <-> Gemini` diversity held across all 5
>   passes (`DIVERSITY_REDUCED=true` recorded for reserve-pool usage).
> - **`FF-4.3` (`P2`, $N=4$)**: Because `Model X` (`4.5%`) and `Model Y`
>   (`0.0%`) were below Tier `P2`'s `40%` reserve floor at spawn, both `ff43-a`
>   and `ff43-b` ran on `supervisor-model-primary` (`Family Z`, single-family
>   `DIVERSITY_REDUCED=true`).
>
> Both `Model X` (`model-family-x-primary`) and `Model Y` (`model-family-y-primary`)
> have since refreshed (`>99%`). Run an independent cross-family (`Model X`) or
> human audit on the `[diversity-reduced]` units before merging `sup/ff-4` to
> `main` or publishing `adv/ff-4-3-reference` to `google/zerocopy`.

---

## 1. Workstream Deliverables & Branch Topology

1. **`FF-4.1` (`adv/ff-4-1` -> `a6bebfc2`, 9/9 checkpoints)**:
   - Authored the `Lift First, Evaluate Last` decision tree and Patterns A-E in
     `skills/anneal-prove/SKILL.md` and
     `skills/anneal-prove/references/proof-scaling-and-bottlenecks.md`, and
     stabilized the 7-function `examples/wireframe-demo` baseline (`8,009` LOC).
2. **`FF-4.2` (`adv/ff-4-2` @ `60d08cac`, 9/9 checkpoints)**:
   - Migrated all 7 `Proof/WireframeDemo/*.lean` proofs, `FrameTutor/*.lean`,
     and 6 pure `examples/mir/MirVerification.lean` proofs off hand-written
     `BlockCtx` records and manual fuel/step/tactic-round numerals (`iterate k`)
     onto `#mir_lift`, `#mir_lift_spec`, `forRangeUp` + `runCfgToBlock`, and
     `verifyStatefulMir_of_sepLenses` + `LiftLensBlock`, with zero `trusted/`
     diffs against `0d3242d3`.
3. **`FF-4.2b` (`adv/ff-4-2b` @ `cfad3ee4` -> `sup/ff-4` @ `9ec41a30`, 5/5)**:
   - Semantically merged `sup/brief-4` (`087b015b`: `BRIEF-0..4`, `b2341426`
     pointer-offset semantics, `cargo-anneal`, `anneal-difftest`) with
     `FF-1..FF-4.2` with zero upstream file reversions, cutting standalone
     `theory/Anneal/PureMirExec.lean` elaboration from `85 s` to `35.1 s` via an
     inline-`match` `kabstract` root-cause fix (`-187` dead lines, `-111` kernel
     declarations).
4. **`FF-4.3` (`adv/ff-4-3` @ `549ffba8` -> `sup/ff-4` @ `05763dcf`, 9/9;
   local `zerocopy-reference` `adv/ff-4-3-reference` @ `8ceec4bd6`, 9/9)**:
   - Added `MirLiftingProfile`, `--init-proofs` starter lifting hints, and the
     `cargo anneal agent-context` strategy guide in
     `crates/cargo-anneal/src/{scaffold.rs,agent.rs,lib.rs}` (`99/99` tests
     passing across all 11 `cargo-anneal` test suites), aligned fresh-capture
     `layoutIdx` indices on `WireframeDemo/{decode_wire_header,`
     `checksum_frame_fast}.lean` (`1,421` LOC preserved), and synced
     `examples/tutor-ch4` + `docs/tutor/{01,02,04,05}-*.md`.
   - Authored the self-contained cold-reader report package
     `reports/anneal-fuel-free-mir-lifting-and-alias-erasure/` on local branch
     `adv/ff-4-3-reference` (`origin/reference` untouched at `64e9b5c4d`),
     including a 938-line `Init`-only Lean `v4.34.1` probe proving 18
     constructive theorems, `wireframe_benchmark_metrics.json`,
     `verify_probes.py`, and regenerated `CATALOG.json` (`166` reports).

---

## 2. `WireframeDemo` Compression & Elaboration Summary

| Proof (`Proof/WireframeDemo/`) | `a6bebfc2` LOC | `sup/ff-4` LOC | Delta LOC | `[adv B2]` HB (k) | `sup/ff-4` HB (k) | Delta HB |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `advance_cursor.lean` | 227 | 231 | +1.8% | 5,771 | 5,504 | -4.6% |
| `checksum_frame_fast.lean` | 1,592 | 174 | -89.1% | 655,752 | 72,097 | -89.0% |
| `checksum_frame_safe.lean` | 1,242 | 275 | -77.9% | 180,914 | 64,596 | -64.3% |
| `clamp_payload_window.lean` | 1,595 | 187 | -88.3% | 187,030 | 186,993 | -0.0% |
| `decode_wire_header.lean` | 979 | 272 | -72.2% | 44,866 | 22,947 | -48.9% |
| `frame_total_len.lean` | 1,268 | 169 | -86.7% | 249,768 | 250,106 | +0.1% |
| `parse_compression_flag.lean` | 1,106 | 113 | -89.8% | 64,833 | 62,985 | -2.9% |
| **Total** | **8,009** | **1,421** | **-82.3%** | **1,388,934** | **665,228** | **-52.1%** |

Against `0d3242d3` (`4,264` LOC, where 3 files were incomplete stubs), proof LOC
falls by `-66.7%`. Across all 7 files: `BlockCtx = 0` (was `111`),
`defaultCfgSteps / runCfgSteps = 0`, manual fuel/step numerals = `0`, and
`iterate [0-9]+ = 0`. Shared reusable theory grew by `+2,972` net LOC (`45%` of
the `6,588` proof lines removed).

---

## 3. End-to-End Verification Commands

Run from `<path/to/anneal>`:

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"

# 1. Hygiene, TCB diff vs sup/brief-4 (087b015b), and TrustedBoundary audit
cd <path/to/anneal>
./ci/check_todo.sh
git diff 087b015b..HEAD -- trusted/lean/
python3 trusted/audit/check_trusted.py --fast

# 2. Zero BlockCtx, manual fuel/step numerals, or soundness escapes in proofs
D=examples/wireframe-demo/anneal/proofs/Proof/WireframeDemo
wc -l $D/*.lean
! grep -nE 'BlockCtx|defaultCfgSteps|runCfgSteps' $D/*.lean
! grep -nE 'LiftBlock .* [0-9]+ :=|^\s*[0-9]+ := by|\(n := [0-9]+\)' $D/*.lean
! grep -nE '\brfl [0-9]+\b|iterate [0-9]+' $D/*.lean

# 3. Lean theory + MirVerification + Miri sysroot + full cargo-anneal suite
(cd examples && \
  anneal-lean-run --mode build --concurrency 1 -- \
  lake build Anneal MiniRust MirVerification)
anneal-lean-run --mode build --concurrency 1 -- cargo miri setup
anneal-lean-run --mode build --concurrency 1 -- cargo test -p cargo-anneal

# 4. End-to-end crate verification with TrustedBoundary kernel replay
anneal-lean-run --mode build --concurrency 1 -- \
  cargo-anneal verify --manifest-path examples/wireframe-demo/Cargo.toml
anneal-lean-run --mode build --concurrency 1 -- \
  cargo-anneal verify --manifest-path examples/tutor/Cargo.toml
rm -rf examples/wireframe-demo/.anneal examples/wireframe-demo/Cargo.lock \
  examples/tutor/.anneal examples/tutor/Cargo.lock
test -z "$(git status --porcelain)"

# 5. Local zerocopy-reference report, 18-theorem Lean probe, and no-push check
cd <path/to/zerocopy-reference>
test "$(git rev-parse origin/reference)" = \
  "64e9b5c4d271fe3f3aadfea71f36bc784ff3391b"
python3 \
reports/anneal-fuel-free-mir-lifting-and-alias-erasure/support/verify_probes.py
python3 tools/reference.py catalog
python3 tools/reference.py check
python3 -m unittest discover -s tests
test -z "$(git status --porcelain)"
```

---

## 4. Publishing `adv/ff-4-3-reference` to `google/zerocopy` (`markdittmer`)

Nothing has been pushed to `origin/reference`. After completing 3rd-party review
of `adv/ff-4-3-reference` (`8ceec4bd6`), publish as a single linear fast-forward
commit onto `origin/reference` (full details in `REPRODUCE_FF_4_3.md` §4):

```bash
# On Capsule: stage report tarball to remote-storage at HEAD (never /mnt/fuse/rw/...)
cd <path/to/zerocopy-reference>
tar -czf /tmp/ff43-reference-report.tar.gz \
  reports/anneal-fuel-free-mir-lifting-and-alias-erasure
/usr/bin/remote-sync --force_client_creation_at_head cp -f \
  /tmp/ff43-reference-report.tar.gz \
  /remote/anneal-agent
rm -f /tmp/ff43-reference-report.tar.gz

# On workstations google/zerocopy reference worktree:
git fetch origin reference && git checkout -B reference-publish origin/reference
/usr/bin/remote-sync --force_client_creation_at_head cp -f \
  /remote/anneal-agent \
  /tmp/ff43-reference-report.tar.gz
tar -xzf /tmp/ff43-reference-report.tar.gz
rm -f /tmp/ff43-reference-report.tar.gz
python3 \
reports/anneal-fuel-free-mir-lifting-and-alias-erasure/support/verify_probes.py
python3 tools/reference.py catalog && python3 tools/reference.py check
git add CATALOG.json reports/anneal-fuel-free-mir-lifting-and-alias-erasure
git commit -m "[reference] Add fuel-free MIR lifting and alias-erasure report" \
  -m "Agent-authored-by: AI agent acting on Mark Dittmer's behalf"
git push origin HEAD:refs/heads/reference
```
