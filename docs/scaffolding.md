<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Building and testing the scaffold

This guide covers the current compiler and packaging scaffold. The capture
driver starts the pinned compiler and reports a successful analysis callback
on stderr after compilation succeeds. It does not extract verification
obligations or verify Rust code. A successful driver smoke test is evidence of
compiler startup, not a verification result.

The runtime workflow below has been validated on `x86_64-linux`. Nix also
evaluates the flake for `aarch64-linux`, `x86_64-darwin`, and `aarch64-darwin`;
that evaluation does not establish that the installed tools run on those hosts.

## Build and install the current archive

Use Bash on Linux with Nix flakes, Python 3, a host C linker, and an existing
Rust toolchain (Cargo and rustc) that can build the CLI's Rust 2024 crate and
locked dependencies. The first `cargo install` uses that toolchain before
the archive's pinned compiler is installed. Run the following commands from the
checkout root in one shell; later commands reuse these variables. The temporary
directory owns this run's CLI installation, cache, and staged test artifacts.

```bash
set -euo pipefail
repo_root="$(pwd -P)"
scaffold_root="$(mktemp -d /tmp/anneal-scaffold.XXXXXX)"

nix build .#omnibus-archive --max-jobs 1 --cores 4 \
  --out-link "$scaffold_root/archive"
archive="$(readlink -f "$scaffold_root/archive")"

cargo install --locked --debug --jobs 2 --path trusted/cargo-anneal \
  --root "$scaffold_root/cli"
env XDG_CACHE_HOME="$scaffold_root/cache" \
  "$scaffold_root/cli/bin/cargo-anneal" setup --local-archive "$archive"
```

`--max-jobs 1` limits concurrent Nix builds; `--cores 4` bounds the cores
advertised to each build. The archive contains the pinned Rust and Lean
toolchains, `bin/anneal-rustc-capture`, and the Lean foundation metadata under
`share/anneal/`. Build the Rust auditor and stage the Lean inspector separately
as shown below; they are not additional entries in this archive.

Use `--local-archive` to test the archive built from this checkout. The default
remote archive metadata still contains placeholder release URLs and hashes.
The fresh cache makes an earlier installation unable to satisfy this setup
command. `XDG_CACHE_HOME` applies only to that child process and does not change
the shell's ordinary cache location.

Find the installation created by this command, rather than guessing its
versioned directory name or searching another cache:

```bash
install_root="$(python3 - "$scaffold_root/cache" <<'PY'
import sys
from pathlib import Path

parent = Path(sys.argv[1]) / "anneal/toolchain"
roots = [path for path in parent.iterdir() if path.is_dir()]
if len(roots) != 1 or roots[0].is_symlink():
    raise SystemExit("setup must produce exactly one fresh installation")
root = roots[0].resolve()
for relative in (
    "rust/bin/rustc",
    "rust/bin/rustdoc",
    "lean/bin/lean",
    "bin/anneal-rustc-capture",
):
    if not (root / relative).is_file():
        raise SystemExit(f"installed tool is missing: {root / relative}")
print(root)
PY
)"
```

The installed driver accepts Rust compiler arguments. By default, it uses the
adjacent `rust/` directory as its sysroot. For an unbundled development binary,
pass the installed Rust directory with the compiler's standard
`--sysroot "$install_root/rust"` option. Use `--` before a compiler `--help` or
`--version` request to distinguish it from the driver's own help or version.
Information-only compiler requests do not establish that analysis ran.

## Test the workspace with the pinned Rust toolchain

The driver uses compiler-private libraries, so build and test it with the same
Rust distribution that the archive contains. Pin both Rust compiler tools, the
runtime library directory, and the sysroot used by compiler-session tests:

```bash
export RUSTC="$install_root/rust/bin/rustc"
export RUSTDOC="$install_root/rust/bin/rustdoc"
export LD_LIBRARY_PATH="$install_root/rust/lib"
export RUSTFLAGS="-Lnative=$install_root/rust/lib -Clink-arg=-Wl,-rpath,$install_root/rust/lib"
export ANNEAL_TEST_RUST_SYSROOT="$install_root/rust"

env XDG_CACHE_HOME="$scaffold_root/cache" \
  cargo test --locked --workspace --jobs 2 -- --test-threads=2
```

The workspace's boundary-audit tests find Lean through the cache, so give that
test process the fresh cache used by setup. The installed smoke suite is
ignored by this command and runs separately below.

Build the auditor into an explicit installation root and copy the inspector
source from the same checkout into owned staging:

```bash
cargo install --locked --debug --jobs 2 --path trusted/audit \
  --root "$scaffold_root/auditor"
mkdir -p "$scaffold_root/inspector"
cp trusted/audit/TrustedBoundary.lean \
  "$scaffold_root/inspector/TrustedBoundary.lean"

"$scaffold_root/auditor/bin/anneal-audit" \
  --lean "$install_root/lean/bin/lean" --anneal-root "$repo_root"
```

## Run installed smoke cases

The opt-in suite runs installed tools from temporary directories outside the
checkout. Supply absolute paths to the current CLI, auditor, and inspector
artifacts, plus a source-revision label. The label is caller-supplied metadata;
the harness does not attest that artifacts came from that revision. If the
checkout has uncommitted changes, use a label that records them and retain the
diff with the build artifacts.

Choose exactly one installation input: `ANNEAL_TEST_ARCHIVE` installs the
supplied archive into fresh test-owned storage, while
`ANNEAL_TEST_INSTALL_ROOT` uses an existing explicit installation. Existing-root
mode alone does not demonstrate that the current archive installs. This example
tests the archive built above and removes inherited installation and case
selection settings:

```bash
source_revision="$(git rev-parse HEAD)"
if [ -n "$(git status --porcelain)" ]; then
  source_revision="$source_revision+worktree"
fi

env -u ANNEAL_TEST_INSTALL_ROOT -u ANNEAL_TEST_CASE \
  ANNEAL_TEST_SOURCE_REVISION="$source_revision" \
  ANNEAL_TEST_CARGO_ANNEAL="$scaffold_root/cli/bin/cargo-anneal" \
  ANNEAL_TEST_AUDITOR="$scaffold_root/auditor/bin/anneal-audit" \
  ANNEAL_TEST_INSPECTOR="$scaffold_root/inspector/TrustedBoundary.lean" \
  ANNEAL_TEST_ARCHIVE="$archive" \
  ANNEAL_TEST_DIAGNOSTICS="$scaffold_root/diagnostics" \
  cargo test --locked -p cargo-anneal --test installed_smoke -- \
    --ignored --exact installed_smoke --nocapture
```

To use the installation created by setup instead, remove `ANNEAL_TEST_ARCHIVE`
from the command, unset any inherited archive setting, and pass
`ANNEAL_TEST_INSTALL_ROOT="$install_root"`.

Use these optional controls to narrow a failure or bound resource use:

| Variable | Behavior |
| --- | --- |
| `ANNEAL_TEST_CASE` | Selects one exact case name; unset selects every case. |
| `ANNEAL_TEST_JOBS` | Runs at most this many cases concurrently; default `2`, range `1..=32`. |
| `ANNEAL_TEST_TIMEOUT_SECS` | Deadline for each child process; default `120`, range `1..=3600`. |
| `ANNEAL_TEST_DIAGNOSTICS` | Exports failure evidence under this directory for collection. |

The available case names are:

| Case | What it checks |
| --- | --- |
| `audit-accepted` | A small accepted Lean fixture reaches kernel replay. |
| `audit-missing-lean` | An explicit missing Lean executable produces a toolchain error. |
| `audit-rejected` | A fixture containing `sorry` is rejected before target execution. |
| `bundled-cargo-check` | Installed Cargo and rustc check an offline fixture with a fresh Cargo home and produce crate metadata. |
| `cargo-arguments` | An unknown CLI command produces an argument error. |
| `cargo-help` | Direct and Cargo-style help requests succeed. |
| `cargo-setup-invalid-archive` | On Linux, the installed CLI rejects a broken local archive in a fresh cache. |
| `cargo-version` | Direct and Cargo-style version requests succeed. |
| `driver-callback` | The installed driver compiles a small crate and reports its analysis callback. |
| `lean-file` | The installed Lean compiler checks a small source file. |
| `rustdoc-html` | Installed rustdoc creates the crate index and function HTML for a small source file. |

For example, add `ANNEAL_TEST_CASE=driver-callback ANNEAL_TEST_JOBS=1` to the
environment above to rerun just the compiler case. An unknown case name fails
and lists the available cases.

The [release workflow](../.github/workflows/release.yml) runs a
[shared toolchain probe](../ci/probe_toolchain.sh) before uploading each
platform archive and after installing the remote toolchain into a fresh cache.
The probe checks tool versions and small compiler, documentation, Cargo, and
Lean fixtures. A successful probe establishes only those fixture operations.

The timeout kills and reaps the direct child process. It does not terminate
descendants or bound arbitrary Rust case code. CI must retain an outer job
deadline for those limits and cancellation.

## Inspect and replay a failure

On failure, the harness prints the retained temporary run directory. It keeps
test-owned inputs, any fresh installation, and metadata describing the supplied
revision, selected cases, and installation paths. Each command directory under
`cases/<case>/commands/<number>/` contains `invocation.json`, `outcome.json`,
raw `stdout` and `stderr`, and `reproduce.py`. Launch failures and timeouts
have distinct outcome records.

From a retained command directory, run:

```bash
python3 reproduce.py
```

The script repeats the recorded executable, arguments, environment, and working
directory. It relocates references to the original temporary run directory
when the evidence directory moves. It does not restore external artifacts.
Keep the original archive and every executable recorded in `invocation.json`,
including the installed-smoke test executable used by archive-install commands.
Keep the inspector source as well, and restore external artifacts at their
recorded paths before replaying. The replay applies the recorded process
deadline and supplies a null stdin, matching the original invocation. Its
deadline still covers only the direct child.

The diagnostics export omits the potentially large `installation/` subtree.
If the archive-install subprocess failed, `installation.json` may not exist.
Restore the external archive and recorded test executable. Make a fresh replay
copy of retained or exported evidence, omitting `installation/`, then run
`reproduce.py` from the copied command directory. If an earlier replay left a
partial installation in that copy, move it aside there before retrying. Preserve
the original retained run and any partial installation for inspection.

For an archive-backed run whose installation succeeded, `installation.json`
records the archive and installed root. Restore the omitted subtree from that
archive before replaying later cases; the script relocates the recorded
run-relative root. Existing-root mode instead needs the supplied external
installation available at its recorded path. If export fails, the harness still
reports the original failure and retained directory.

## Check packaging

Check the CLI crate's package without publishing a release:

```bash
cargo publish --locked --dry-run -p cargo-anneal
./ci/check_todo.sh
```

Cargo expects a clean checkout for the package check. To inspect uncommitted
changes, add `--allow-dirty` to the dry-run command and retain the diff with the
result. The dry run checks packaging; it does not publish the crate or turn the
placeholder remote archive metadata into a usable release. CI also compiles the
prepared package's test targets so they cannot borrow files from the checkout;
see the packaging step in [the workflow](../.github/workflows/ci.yml).
