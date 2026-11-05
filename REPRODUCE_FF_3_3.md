<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Reproduction guide for FF-3.3: polymorphic and indirect calls in `#mir_lift`

FF-3.3 extends the opaque-body lifting rules (`theory/Anneal/MirLiftCore.lean`)
and the `#mir_lift` elaborator (`theory/Anneal/MirLift.lean`) to function-pointer
reification, indirect calls through `Memory.fnPtrs`, and calls to generic
callees instantiated by `lookupCallee`. This guide rebuilds every artifact and
checks that the new theorems are kernel-checked and free of `sorryAx`.

## 1. Setup

Run every command from the worktree root:

```bash
cd /usr/local/google/Projects/anneal-workspace/anneal-wt-ff-3-3
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
```

Never run `lake clean` or bare `lake`/`lean`; wrap Lean commands in
`anneal-lean-run`, which bounds threads, memory, and wall-clock time.

## 2. Repository checks and the trusted-boundary audit

```bash
./ci/check_todo.sh
python3 trusted/audit/check_trusted.py --fast
```

`check_trusted.py` compiles every `Trusted` module and every downstream target
in its `DOWNSTREAM_TARGETS` table (including `Anneal.MirLiftCore` and
`Anneal.MirLiftBench`) with warnings as errors, replays them in the kernel, and
rejects any axiom outside the pinned foundation lock, so a `sorry` anywhere in
those modules fails the audit.

## 3. Build the audited `Anneal` library

```bash
cd examples
anneal-lean-run --mode build --concurrency 2 -- lake build Anneal
```

This builds the frame-lifting rules (`LiftFrame`, `LiftStmtMem`,
`LiftTerminator`, and the `lift_frame` tactic) and the benchmark in
`Anneal.MirLiftBench`:

- `liftIndirectCaller_wpConverges`: the caller reifies the generic
  `lift_poly_id::<u32>` into `_1 : fn(u32) -> u32`, calls it indirectly with
  `7`, and returns `7_u32` from `initMachineStateWithCallees`.
- `liftDirectCaller_wpConverges`: the same generic callee called directly.
- `liftIndirectCaller_verified`: the trusted `VerificationResult` for the claim
  with `lift_poly_id` linked in `Claim.callees`.
- Two `fail_if_success` checks: without the linked callee, or with a wrong
  expected value, `lift_frame` fails.

## 4. Build the `#mir_lift` elaborator and its benchmarks

`Anneal.MirLift` imports `Lean` for its command elaborator, so it sits outside
the audited umbrella (the audit admits only `Init` and `Std` imports in
downstream modules). Build it as a module target of the `Anneal` library:

```bash
cd examples
anneal-lean-run --mode build --concurrency 2 -- lake build Anneal.MirLift
```

The build runs `#mir_lift (callees := [liftPolyIdMir]) liftIndirectCallerMir`,
which defines `liftIndirectCallerMir_model := Value.scalar { bits := 7,
sizeBytes := 4 }` and proves `liftIndirectCallerMir_lift_sound`. Two
`#guard_msgs` checks pin the axioms of the generated theorems to
`[propext, Classical.choice, Quot.sound]`, so the build fails if `sorryAx` or a
custom axiom appears. The call-free `#mir_lift` tests from FF-3.2 run in the
same module.

## 5. Inspect the generated declarations (optional)

```bash
cd examples
cat > /tmp/ff33_probe.lean <<'EOF'
import Anneal.MirLift
open Trusted.Rustc.V2026_06_01.MirSemantics
#print liftIndirectCallerMir_model
#check @liftIndirectCallerMir_lift_sound
#print axioms liftIndirectCallerMir_lift_sound
#print axioms liftIndirectCaller_verified
EOF
anneal-lean-run --mode file --concurrency 2 -- lake env lean /tmp/ff33_probe.lean
```

Expected output: the model is `Value.scalar { bits := 7, sizeBytes := 4 }`, the
theorem states `MirWpConverges liftIndirectCallerMir
(initMachineStateWithCallees liftIndirectCallerMir [] [liftPolyIdMir])
(mirNormalPost fun retVal mem => retVal = liftIndirectCallerMir_model)`, and
both theorems depend only on `[propext, Classical.choice, Quot.sound]`.
