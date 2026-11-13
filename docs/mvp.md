<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Experimental scalar verifier

The experimental verifier connects typed compiler capture, an operational Lean
model, authored specifications and proofs, and exact theorem acceptance. Its
first production example verifies Starnix's endianness conversion in the
original multi-file `ebpf_core` compilation.

The commands below target x86_64 Linux. Capture pins Rust nightly
`2026-05-31`, commit `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, and
`Runtime(PostCleanup)` MIR. Proof checking pins Lean 4.34.1 and authenticates
its foundation and checked library artifacts against the repository locks.

Archive variants select the host executables used to run Anneal. Verification
admits only `x86_64-unknown-linux-gnu`; the Cargo shortcut uses that same fixed
profile. Each default archive includes its host Rust standard library, so an
archive for another host may lack libraries for the verification target. A
compatible custom compiler/sysroot can provide those libraries without
changing the verified target. Cross-host verification remains unqualified
here; the compiler reports missing target libraries rather than retargeting
the program or rejecting the host itself.

## Install from the workspace

From the repository root, build the pinned omnibus archive with Nix and install
the CLI from this checkout:

```sh
mkdir -p target
nix build .#omnibus-archive --option max-jobs 2 --option cores 4 \
  --out-link target/anneal-omnibus
cargo install --locked --jobs 4 --path trusted/cargo-anneal \
  --root "$PWD/target/local-install"
export PATH="$PWD/target/local-install/bin:$PATH"
export XDG_CACHE_HOME="$(mktemp -d)"
cargo anneal setup --local-archive "$(readlink -f target/anneal-omnibus)"
```

The fresh cache prevents an earlier installation with the same package
metadata from satisfying setup instead of the archive just built. Keep this
`XDG_CACHE_HOME` for the commands below.

`setup` prints the installed bundle directory. Set `anneal_bundle` to that
printed path; the directory contains
`bin/anneal-rustc-capture`, `rust/`, and `lean/`. Verification resolves the
installed capture driver and sysroot automatically. Without `--capture`, it
uses an already installed bundle before looking for a driver beside the CLI;
that keeps the default capture adapter and Rust sysroot paired. This also
applies to workspace-built CLIs. Use the explicit development command below
to select a different adapter and sysroot. Discovery does not install or
download a missing bundle. The auditor locates and authenticates the pinned
Lean distribution. The CLI embeds its model, theory and inspector sources,
so the installed binary can run after the checkout is moved.

Use the local archive explicitly. This prototype provides a workspace install;
its Cargo registry publication and hosted archive URLs are not release channels.

For compiler-adapter development with existing `rustup` and `elan`
installations, the equivalent explicit tool setup is:

```sh
rustup toolchain install nightly-2026-05-31 --profile minimal \
  --component rustc-dev --component llvm-tools
elan toolchain install leanprover/lean4:v4.34.1
anneal_sysroot="$(rustup run nightly-2026-05-31 rustc --print sysroot)"
anneal_lean_prefix="$(elan run leanprover/lean4:v4.34.1 lean --print-prefix)"
export RUSTC="$anneal_sysroot/bin/rustc"
export RUSTFLAGS="-Lnative=$anneal_sysroot/lib -Clink-arg=-Wl,-rpath,$anneal_sysroot/lib"
export LD_LIBRARY_PATH="$anneal_sysroot/lib"
cargo build --locked --jobs 4 -p anneal-rustc-capture -p cargo-anneal
```

Pass these tools explicitly when verifying with that development build:

```sh
target/debug/cargo-anneal verify --request /path/to/request.json \
  --capture "$PWD/target/debug/anneal-rustc-capture" \
  --sysroot "$anneal_sysroot" --lean "$anneal_lean_prefix/bin/lean"
```

The native-library search path, rpath and runtime library path must reference
the compiler distribution used to build the capture driver. `LD_LIBRARY_PATH`
also lets the driver's dependencies find libraries from that distribution.
Building it with an unrelated Rust compiler cannot use the pinned
`rustc_private` metadata.

## Describe the compilation and proof

The build-neutral command accepts an explicit JSON request. Cargo, GN and Bazel
integrations can produce this same input format. Paths to the source roots are
relative to the request's directory; paths inside each root must be clean,
relative regular-file paths. Declare every source or included file that the
compiler reads. Undeclared reads and changed input bytes cause refusal.

For example, arrange a directory as follows:

```text
example/
  request.json
  rust/lib.rs
  proof/Spec.lean
  proof/Proof.lean
```

Use the existing [scalar source and proof fixture](../trusted/cargo-anneal/tests/fixtures/scalar/)
for a complete first example. Copy `lib.rs` into `rust/` and the two Lean files
into `proof/`, then write this `request.json`:

```json
{
  "schema_version": 1,
  "compilation": {
    "source_root": "rust",
    "crate_root": "lib.rs",
    "crate_name": "scalar",
    "edition": "2024",
    "target": "x86_64-unknown-linux-gnu",
    "cfg": [],
    "source_files": ["lib.rs"]
  },
  "scope": {"kind": "crate"},
  "proof": {
    "source_root": "proof",
    "specification": "Spec.specs",
    "theorem": "Proof.verify",
    "sources": [
      {"module": "Spec", "path": "Spec.lean", "role": "specification"},
      {"module": "Proof", "path": "Proof.lean", "role": "proof"}
    ]
  }
}
```

```sh
cargo anneal verify --request /path/to/example/request.json \
  --artifacts /path/to/new-verification-evidence
```

Every request compiles a library with optimization level 0, debug assertions
disabled and overflow checks disabled. The initial target is
`x86_64-unknown-linux-gnu`, with 64-bit pointers and little-endian layout.
`cfg` contains the resolved compiler cfg arguments for this compilation. The
format does not expose arbitrary compiler flags or external dependency inputs.
A request proves this configured source subject; correspondence to a different
Cargo profile or deployed binary requires separate evidence.

Declared regular files and their ancestor directories define the compilation's
source namespace. Source reads and existence checks resolve within that
namespace, including ordinary `.` and `..` paths through declared ancestors.
Ambient alternatives and undeclared aliases remain outside the compilation.
This defines the staged source subject; it does not establish that additional
files were absent from the original checkout.

To verify selected functions, replace the scope with compiler paths:

```json
"scope": {
  "kind": "selected_unit",
  "roots": ["api::apply_endianness"]
}
```

Selected-unit success covers the named callable bodies and the supported
dependencies needed to justify their verification: their admitted closure. The
current fragment refuses MIR calls and provides no waiver mechanism for
unverified Rust helpers. The receipt's `selected` list identifies the proved
bodies; its `census` also lists unselected crate items without claiming to
verify them.

Whole-crate verification accounts for every function, method, trait
implementation and other relevant item in the configured crate, including
uncalled entry points. All applicable obligations must be supported and proved;
an unsupported or missing obligation causes refusal. This includes relevant
owners without callable bodies, rather than just successfully translated
functions. Both modes require safety of every execution prefix. A safe infinite
loop is permitted; divergence does not exempt a faulty prefix from safety.

For a dependency-free, feature-free Cargo library whose compiler inputs are
`.rs` files, a shortcut constructs the request from package metadata and files:

```sh
cargo anneal verify --manifest-path /path/to/package/Cargo.toml \
  --proof-dir /path/to/package/proof --select module::function
```

Omit `--select` to require the whole crate. The shortcut uses the same fixed
Anneal profile. It refuses Cargo features, dependencies, build scripts,
procedural macros and package-local compiler overrides. An explicit request can
supply supported resolved cfg and source inputs; external dependencies and
unsupported MIR remain unavailable. The shortcut marks `Spec` and `Spec.*`
modules as specifications and other proof-directory modules as proofs. Use an
explicit request when specification helpers need other module names.

The shortcut declares regular `.rs` files below the package root, excluding
hidden names and `target` directories. It does not discover Rust dependencies
from source syntax. Use an explicit JSON request for non-`.rs` modules, included
code or data, or other inputs outside that scan, and list every required file
in `compilation.source_files`. Every observed compiler read must match a
declared file. Unused declared files remain in the receipt’s source inventory.
The shortcut does not infer a smaller set by parsing `mod`, `include!` or other
macros, and does not include every package file as a potential compiler input.

## Author specifications and proofs

Each Lean source starts with `prelude` and declares its imports explicitly.
For example, a specification imports `Trusted.Mvp`; a proof imports `Expected`
and may use checked theory such as `Anneal.Mvp.Execution`. Module identifiers
and source files are listed separately in the request. Optional
`specification_module` and `theorem_module` fields identify the defining modules
when they differ from the declarations' namespace prefixes.

Module and declaration names use ASCII identifier segments separated by dots.
`Trusted.*`, `Captured` and `Expected` modules are reserved for the verifier.

The verifier separates the authorities of the inputs:

| Role | Owner and permitted dependencies |
| :--- | :--- |
| Model | Installed primitive semantics and canonical roots; depends on the model and admitted foundation or checked libraries. |
| Capture | Driver-generated closed program data; depends on the model. |
| Specification | Authored `Specs` and every helper determining its meaning; depends on model and specification sources, plus admitted libraries. |
| Expected | Verifier-generated claim over the captured program and requested specification. |
| Proof | Authored theorem and proof helpers; may use the other roles and admitted checked libraries. |

A function's caller requirements must survive unrelated source edits. Compiler
inventory positions can change when items are inserted or reordered, so caller
safety predicates use each captured body's `identity` string. The capture
adapter emits crate-relative
`rust-path-v1::` identities using the pinned compiler's full semantic paths,
with path trimming and visible reexports disabled. It refuses duplicate keys.
For example, an ordinary `locked` function has key `rust-path-v1::locked`.
Reordering or inserting ordinary named functions preserves their keys.

This identity scheme belongs to Anneal and this pinned compiler. It is not a
promise that Rust diagnostic formatting remains stable across toolchains.
Renaming or moving an item, changing its owner type, or changing the identity
scheme requires reviewing the corresponding specification keys. The capture
receipt retains the diagnostic paths separately for source navigation.

Selected functions under anonymous owners can have order-derived components,
such as `outer::{closure#0}::inner`. Their reviewed keys expose the same
selector already present in the selected scope. They do not identify an item
persistently across anonymous-owner reordering. Whole-crate capture currently
refuses those enclosing closures. Persistent identities for these cases need
reviewed stable anchors or an explicit binding protocol before a broader
cross-edit identity guarantee can be made.

Specifications supply reviewed caller safety requirements for unsafe functions
and an additional property of the captured program. Functional properties
cannot remove baseline safety obligations for safe functions. A specification
helper must have the specification role; importing an unreviewed proof helper
into a specification is rejected. Adjacent compiled Lean files are ignored.

The submitted declaration must be a closed theorem proving the canonical
`Trusted.Mvp.CrateTheorem` or `Trusted.Mvp.UnitTheorem` application for the
actual captured subject and requested specification. Acceptance checks
declaration origins, the actual theorem type, the logical dependency closure
and kernel replay from the authenticated foundation. `sorry` and additional
logical axioms are rejected. Installed math libraries supply checked
declarations, not new trusted axioms. Arbitrary external Lean packages need an
admitted import path.

## Supported fragment and results

The operational fragment supports booleans, integers up to 64 bits, unit and
never locals, and local fieldless enums with isize discriminants. It preserves
storage markers, moves, copies and retag flags. Operations include ordinary
bitwise, shift, wrapping arithmetic and comparison operations, discriminant
reads, scalar assignment, branches, returns and loops.

The model represents logical scalar values and local storage slots. Physical
allocations, padding, pointer provenance and general memory operations are
outside this fragment. A MIR move marks its source uninitialized; reading that
source before reinitialization faults in the model. This conservative rule can
refuse valid Rust cases where a value of a Copy type may remain usable.

Selected code using references, pointers, projections, calls, payload-bearing
aggregates, drop, unwinding, assembly or unsupported constants is refused.
Generic functions require instantiation obligations beyond this fragment.
Broader memory, concurrency and full Starnix verification remain further work.

Verification returns a JSON receipt with one of these statuses:

| Status | Meaning | Exit code |
| :--- | :--- | :--- |
| `crate_verified` | The requested whole crate passed. | 0 |
| `selected_unit_verified` | The requested selected scope passed. | 0 |
| `unsupported` | A required input or obligation is outside the implemented fragment. | 1 |
| `proof_failed` | The frontend reported a source rejection, or acceptance policy rejected the proof. | 1 |
| `compiler_failed` | The configured Rust compilation failed. | 2 |
| `tool_failed` | A tool, protocol or artifact operation failed. | 2 |

A proof failure alone is not a counterexample. Target compilation classifies
well-formed frontend error diagnostics as source rejection. Native failures,
stderr, malformed output and resource or kernel diagnostics are tool failures;
classifying all kernel diagnostics this way is conservative and can include
kernel type errors. This is a reporting rule, not a complete taxonomy of Lean
bugs. Both failures reject the run. Successful capture alone is not verification.

The receipt identifies scope, source bytes, request, capture,
model and specification identities, fixed assumptions and timing. Its
`assumptions` field lists compiler-capture, model, foundation and environment
assumptions; `deferred` identifies assurance limits. The `audit` field contains
kernel-inspection evidence, including admitted axioms and declaration origins.
These fields are not a complete per-item TCB audit log; complete review-surface
reporting remains deferred. `--artifacts` retains staged inputs, compiler logs
and available audit evidence in a new directory; it refuses to overwrite an
existing destination.

If copying retained evidence fails, the command reports `tool_failed` and
removes the destination it created. If removal also fails, the error identifies
where incomplete evidence may remain. The destination can be visible while the
copy runs; its presence alone does not establish a completed export. An existing
destination is never changed.

## Run the production fixture and repository tests

Set `anneal_bundle` to the installation directory printed by `setup`, then run:

```sh
python3 ci/test_mvp_starnix.py \
  --cli "$PWD/target/local-install/bin/cargo-anneal" \
  --capture "$anneal_bundle/bin/anneal-rustc-capture" \
  --sysroot "$anneal_bundle/rust" \
  --lean "$anneal_bundle/lean/bin/lean" \
  --artifacts-dir "$PWD/target/starnix-evidence"
```

The helper fetches the original ten-file Fuchsia source set at the revision and
hashes in [source.json](../trusted/cargo-anneal/tests/fixtures/starnix/source.json).
Pass `--source-dir /path/to/ebpf/core/src` to use an existing copy with those
exact hashes. The authored specification covers every 64-bit input and each
width of 8, 16, 32 and 64 bits with `to_be = true`: a safe normal return exists,
its result reverses the bytes within that width and clears higher bits, and
two completed conversions recover the original input masked to that width.
With `to_be = false`, a safe normal return exists and equals the masked input.
Baseline safety also covers all valid function inputs independently of these
additional properties.

The helper regenerates baseline witnesses and requires their bytes to match
those just verified. It then changes the implementation to return zero and to
preserve the masked input. Both mutations must fail with the original witnesses
and with fresh witnesses for their changed captures. Before crediting each
fresh rejection, it separately verifies those exact witnesses against a safe
completion specification. The fixed endpoint claims remain unchanged, so a
syntax or transition failure cannot satisfy this negative test. Logs, receipts
and `summary.json` remain in the new evidence directory.

For the workspace tests, first install the omnibus archive as above, then build
the workspace capture driver with its pinned compiler. Explicit tool paths make
the installed CLI part of the test. Compiler integration tests require
`ANNEAL_TEST_RUST_SYSROOT`, while verification tests use `ANNEAL_MVP_SYSROOT`;
point both at the installed Rust distribution:

```sh
export RUSTC="$anneal_bundle/rust/bin/rustc"
export RUSTDOC="$anneal_bundle/rust/bin/rustdoc"
export ANNEAL_TEST_RUST_SYSROOT="$anneal_bundle/rust"
export RUSTFLAGS="-Lnative=$anneal_bundle/rust/lib -Clink-arg=-Wl,-rpath,$anneal_bundle/rust/lib"
export LD_LIBRARY_PATH="$anneal_bundle/rust/lib"
cargo build --locked --jobs 4 -p anneal-rustc-capture
export ANNEAL_MVP_CLI="$PWD/target/local-install/bin/cargo-anneal"
export ANNEAL_MVP_CAPTURE="$PWD/target/debug/anneal-rustc-capture"
export ANNEAL_MVP_SYSROOT="$anneal_bundle/rust"
export ANNEAL_MVP_LEAN="$anneal_bundle/lean/bin/lean"
cargo run --locked --jobs 4 -p anneal-audit -- --lean "$ANNEAL_MVP_LEAN"
cargo test --workspace --locked --jobs 4 -- --test-threads=1
./ci/check_todo.sh
```

Missing verification tools fail the tests. CI uses the same explicit tool
selection, tests a local workspace install, runs the production mutation helper
and retains its evidence while preserving the repository boundary audit.

An installed debug build on the development x86_64 Linux machine checked the
ten-file production request in 45.3 seconds, including 0.5 seconds for capture.
A repeated run with fresh private staging took 44.8 seconds; GNU `time -v`
reported a maximum resident set size of 1,313,432 KiB. These runs reused the
filesystem cache and did not reuse compiled target proofs. They establish a
measured prototype workload, not a performance
budget or a cold-cache benchmark. Each receipt records its own phase timings.

## Experimental assurance limits

The compiler, capture adapter, source model, Lean foundation and acceptance
runtime remain experimental trusted components: verification assumes their
correctness. Verification separately assumes an intact compiler and verification
environment. External target elaborators can execute host code; this prototype
does not isolate hostile elaborator effects. Its exact-root and
logical-assumption checks do not provide that isolation.

Full review-surface presentation, source-to-deployed-binary correspondence and
the complete Starnix migration remain deferred. These limitations do not weaken
the baseline safety proposition required for the supported source scope. The
governing [principles](../PRINCIPLES.md) and [threat model](../THREAT_MODEL.md)
define the broader project promise.
