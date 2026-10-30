# The Tutor workflow: executable source for `docs/tutor/`

Every command, exit status, report, error message, and file listing quoted in
the six tutor chapters is produced by running [`tutor.toml`](tutor.toml) against
the current `cargo-anneal` and transcluding the results, and every chapter crate
under `examples/` is verified to be the previous chapter's crate plus the edits
the chapter describes. The chapters cannot drift from the tool or from the
crates without `cargo test` failing, and a maintainer refreshes them with one
command after an intentional change.

```sh
# Fast: validate tutor.toml, every directive, block coverage, and the deltas
# between the chapter crates (no execution).
python3 docs/tutor/workflow/tutor_workflow.py lint

# Full: build the CLI, run all steps, and fail if any chapter block is stale.
# This is what `cargo test -p cargo-anneal --test end_to_end_tutor` runs, and
# what the `Tutor chapters match the workflow` job in .github/workflows/ci.yml
# runs on every pull request.
python3 docs/tutor/workflow/tutor_workflow.py check

# Refresh the chapters after a CLI or tutorial change, then review `git diff`.
python3 docs/tutor/workflow/tutor_workflow.py render

# Iterate on directives or prose without re-running Lake (reuses the last run).
python3 docs/tutor/workflow/tutor_workflow.py render --reuse-artifacts
```

The driver needs only the Python standard library (3.11 or newer), the compiled
`cargo-anneal` and `anneal-rustc-capture` binaries, and the Lean toolchain that
`cargo anneal verify` already requires. A full `check` takes a few minutes the
first time; the `Trusted` and `Anneal` libraries land in Lake's artifact cache
(which `cargo anneal` enables for the builds it spawns), so later runs, other
crates, and parallel tests reuse them instead of recompiling.

## The chapter crates

`cargo anneal` always operates on a whole crate: it extracts every item,
scaffolds an obligation for every subject item, and audits every `Verify.*`
module. A chapter therefore gets a whole crate that contains exactly what it
discusses, and the chapter's commands name that crate:

| Chapter | Crate | Contents | Derived from the previous crate by |
| --- | --- | --- | --- |
| 1 | `examples/tutor-ch1/` | `magic_version`, no dependencies | — (`src/lib.rs` invites the Section 6 edit) |
| 2 | `examples/tutor-ch2/` | annotated safe functions, `#[model]`, `#[invariant]`; no proofs | new `Cargo.toml` and `src/lib.rs` |
| 3 | `examples/tutor-ch3/` | `magic_version` + `pin_magic`; `Assumptions/` + routed proof | narrowed `src/lib.rs`; two new Lean files |
| 4 | `examples/tutor-ch4/` | four safe items, `Specs/advance_offset`, three proofs | Chapter 2's `src/lib.rs`; assumption removed; four files from `examples/tutor/` |
| 5–6 | `examples/tutor/` | the complete companion crate | final `src/lib.rs`; five Lean files |

Files that are identical across crates (Chapter 4's proofs and the final
crate's, Chapter 2's and Chapter 4's `src/lib.rs`) are checked, not trusted:
each crate step in `tutor.toml` names the source of every file it writes, and
the driver fails with the offending path when a committed crate is not
`derive_from` plus those edits. `diff -r examples/tutor-ch3 examples/tutor-ch4`
shows exactly what Chapter 4 changes.

## How the pieces fit

```text
tutor.toml ──┐
examples/tutor-ch1..4, examples/tutor ──┼─ run ──▶ target/tutor-workflow/<step>/{stdout.txt,stderr.txt,meta.json,files/}
fixtures/ (probe files) ────────────────┘                         │
                                                                  ▼
docs/tutor/0N-*.md  ── directives ──▶ render ──▶ docs/tutor/0N-*.md (managed blocks replaced)
```

1. **`tutor.toml`** lists the steps in tutorial order. A step without `run`
   introduces a chapter crate and declares the file operations that turn the
   previous crate into it (checked against the committed trees). Every other
   step runs one `cargo anneal` subcommand in its crate and states what must be
   true of the outcome (`expect`, `stdout_contains`, `stderr_contains`). Probe
   steps (`probe = true`) apply edits the chapter invites the reader to make, or
   tampering the chapter warns about, and are rolled back afterwards; the
   probe files they write live under [`fixtures/`](fixtures/).
2. **`run`** executes the steps in a temporary directory that mirrors a checkout
   (`crates/`, `trusted/`, and `theory/` are symlinked) and copies each
   committed chapter crate into it when its crate step runs, so the chapters'
   relative paths such as `--manifest-path examples/tutor-ch3/Cargo.toml` and
   `../../crates/anneal-spec` resolve exactly as they do for a reader. Steps
   with `cwd = "root"` execute what `cargo run -p cargo-anneal -- ...` executes;
   steps with `cwd = "crate"` execute what `cargo anneal ...` executes inside
   the crate, so both documented flavours are exercised across a run. Temporary
   paths are stripped from the recorded output so it reads as it would in a
   checkout.
3. **Directives** in the chapters name a step and a kind of record. The renderer
   replaces only the interior of the fenced block that immediately follows a
   directive; prose, the directive, and the fence lines are preserved byte for
   byte. A `check` fails with a unified diff when a block differs from the
   current run; `lint` fails when a block quotes a command, report, or error
   without a directive.

## Directives

A directive is an HTML comment on its own line, immediately above an opening
fence. GitHub does not render the comment. Arguments use `key=value` (quote
values that contain spaces) or bare flags.

| Directive | Renders |
| --- | --- |
| `<!-- tutor: command step=<id>[,<id>...] -->` | Both documented flavours of the step's `cargo anneal` invocation, naming the step's crate. |
| `<!-- tutor: report step=<id> -->` | The `Anneal ... Summary:` block the step printed. |
| `<!-- tutor: errors step=<id> -->` | The `error:` diagnostics of a failing step, from Lake's output and then from `cargo-anneal`'s stderr. |
| `<!-- tutor: stdout step=<id> -->`, `<!-- tutor: stderr step=<id> -->` | The step's whole stream (path-normalized). |
| `<!-- tutor: file step=<id> path=<crate-relative> [strip_module_doc] [item=<name> \| items=<a>,<b>] [docs] -->` | A file as it exists in the step's crate after the step (for a probe, before the rollback). `strip_module_doc` drops Lean `/-! ... -/` headers; `item`/`items` cut named Rust items (with their attributes) out of a source file; `docs` keeps their `///` comments. |
| `<!-- tutor: rm step=<id> -->` | `rm` commands, relative to the crate, for the files the step removes. |
| `<!-- tutor: static -->` | Exempts a block that looks like a command or report from the coverage check. |

Blocks that quote library sources (`trusted/lean/`, `theory/Anneal/`) or show
illustrative code that no step runs are left as ordinary fenced blocks; keeping
those in step with the Lean sources is a separate, semantic task.

## Diagnosing a rendered block

Find the directive above the block, open the step with that `id` in
`tutor.toml` to see which crate it runs in, which files it wrote, and which
command it ran, and inspect `target/tutor-workflow/<id>/` for the raw
`stdout.txt`, `stderr.txt`, `meta.json` (the exact `argv` and exit status), and
the `files/` snapshot the `file` directive read from. `--keep-root` preserves
the temporary checkout mirror after a successful run.

## Changing the tutorial

- To change what a chapter demonstrates, edit the step (or add one) in
  `tutor.toml`, place a directive above the block that should show the result,
  and run `render`.
- To change a chapter's crate, edit the committed crate under `examples/` and
  the file operations of its crate step so they still describe the delta from
  the previous crate; `check` reports any file that disagrees. Files meant to be
  identical across crates should be written `from` the crate where they are
  canonical (usually the latest one) so a later edit is caught everywhere.
- Prose next to a managed block is yours to edit, but if a rendered output
  contradicts it, fix the prose or the step rather than the block: the next
  `render` overwrites the block.
