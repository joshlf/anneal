<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Reproduction guide for FF-3.3: polymorphic and indirect calls in `#mir_lift`

FF-3.3 extends the opaque-body lifting rules (`theory/Anneal/MirLiftCore.lean`)
and the `#mir_lift` elaborator (`theory/Anneal/MirLift.lean`) to
function-pointer reification, indirect calls through `Memory.fnPtrs`, and calls
to generic callees instantiated by `lookupCallee`. This guide rebuilds every
artifact and checks that the new theorems are kernel-checked and free of
`sorryAx`.

## 1. Setup

Run every command from the worktree root:

```bash
cd <path/to/anneal>
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

This builds the frame-lifting rules (`LiftFrame`, `LiftStmtMem` /
`LiftStmt.*`, and `LiftTerminator`) and the benchmarks in
`Anneal.MirLiftBench`:

- `liftIndirectCaller_wpConverges`: the caller reifies the generic
  `lift_poly_id::<u32>` into `_1 : fn(u32) -> u32`, calls it indirectly with
  `7`, and returns `7_u32` from `initMachineStateWithCallees`.
- `liftDirectCaller_wpConverges`: calls and tail-calls the same generic callee
  directly through its function-item constant (`LiftTerminator.callDirect` and
  `LiftTerminator.tailCallDirect`).
- `liftPolyWrapperTransmute_uninstantiated_fails`: proves that `evalPureStmt`
  on the uninstantiated generic `liftPolyWrapperTransmuteMir` returns `none`
  because `Wrapper<T>` has a 0-byte placeholder layout prior to
  `LayoutTable.instantiateForBody`.
- `liftPolyLayoutCaller_wpConverges`: comprehensive 23-step lifted derivation
  exercising projected function-pointer reification
  (`LiftStmtMem.reifyFnPointerPlace`), `CastKind.fnPtrToPtr`
  (`LiftStmtMem.fnPtrToPtr`), byte-level `CastKind.transmute` provenance
  round-tripping of `*const ()` back to `fn(u32) -> u32`, indirect calls
  through projected operands (`LiftTerminator.callIndirect`), safe-to-unsafe
  function-pointer coercion (`LiftStmtMem.unsafeFnPointer`), indirect tail
  calls (`LiftTerminator.tailCallIndirect`), projected drops
  (`LiftTerminator.dropProjected`), local function-item calls
  (`LiftTerminator.callFnItem`), and polymorphic compound layout recomputation
  (`LayoutTable.instantiateForBody`) on `Wrapper<T>` during
  `CastKind.transmute`.
- `liftClosureAndTraitCaller_wpConverges`: exercises non-capturing closure
  coercion (`PointerCoercion("ClosureFnPointer")` on
  `RigidTy.closure "ff33::closure_id" []`), local function-item tail calls
  (`LiftTerminator.tailCallFnItem`), generic trait-method function pointer
  reification and indirect dispatch (`TraitImplEntry` mapping
  `"ff33::ApplyTrait::apply"` to `"ff33::lift_poly_id"` in `checkCalleeSig`
  and `lookupCallee`), inline `core::intrinsics::exact_div::<u32>` calls
  (`LiftTerminator.callExactDiv`), and `LiftTerminator.drop`,
  `LiftTerminator.assert`, `LiftTerminator.switchInt`, and
  `LiftTerminator.goto`.
- `liftPolyApplyCaller_wpConverges`: higher-order polymorphic indirect calls.
  The caller passes reified `lift_poly_id::<u32>` and `lift_poly_id::<u8>` to
  the generic `lift_poly_apply::<u32>` and `lift_poly_apply::<u8>`, which call
  their `f : fn(T) -> T` parameter, writes the results into projected tuple
  fields `_2.0` and `_2.1`, and returns `3 + (4_u8 as u32)`. It covers
  function pointers crossing frames as arguments, signature checks against the
  instantiated parameter type, one generic callee instantiated at two layouts,
  returns two frames deep, and `LiftTerminator.returnToCaller` writing into
  projected `caller.destination` places.
- `liftIndirectCaller_verified`, `liftPolyLayoutCaller_verified`,
  `liftClosureAndTraitCaller_verified`, and `liftPolyApplyCaller_verified`: the
  trusted `VerificationResult` certificates for those claims.
- `liftBadDivergingReturn_not_converges`, `liftDivergingPanic_not_converges`,
  `liftBadNullFnPtrTransmute_not_converges`, `liftBadExactDiv_not_converges`,
  `liftBadPolyApplySig_not_converges`, and `liftBadCleanupReturnMir`: negative
  UB and well-formedness benchmarks covering diverging calls that return or
  unwind into cleanup blocks, transmuting `0_usize` to a function pointer,
  non-exact `exact_div`, passing a `fn(u8) -> u8` where
  `lift_poly_apply::<u32>` expects `fn(u32) -> u32`, and attempting to lift a
  cleanup block (`blk.isCleanup = true`).

## 4. Build the `#mir_lift` elaborator and its benchmarks

`Anneal.MirLift` imports `Lean` for its command elaborator, so it sits outside
the audited umbrella (the audit admits only `Init` and `Std` imports in
downstream modules). Build it as a module target of the `Anneal` library:

```bash
cd examples
anneal-lean-run --mode build --concurrency 2 -- lake build Anneal.MirLift
```

The build runs:
- `#mir_lift (callees := [liftPolyIdMir]) liftIndirectCallerMir`
- `#mir_lift (callees := [liftPolyIdMir]) liftDirectCallerMir`
- `#mir_lift (callees := liftPolyLayoutCallees) liftPolyLayoutCallerMir`
- `#mir_lift (callees := liftClosureAndTraitCallees) liftClosureAndTraitCallerMir`
- `#mir_lift (callees := liftPolyApplyCallees) liftPolyApplyCallerMir`
- `#mir_lift (callees := []) branchFrameBody`, a call-free body lifted in
  linked-callee mode so that its return value is synthesized

Each linked-callee `#mir_lift` defines `<item>_model` (the synthesized return
value) and proves `<item>_lift_sound` (`MirWpConverges` from
`initMachineStateWithCallees`) and `<item>_verified` (the trusted
`VerificationResult` of the closed claim with the callees linked). Seven
`#guard_msgs` checks pin the axioms of generated theorems to
`[propext, Classical.choice, Quot.sound]`, so the build fails if `sorryAx` or a
custom axiom appears. The call-free `#mir_lift` tests from FF-3.2 run in the
same module.

The module also checks rejections. `lift_frame` fails without the linked
callee, with a wrong expected value, on the signature-mismatch bodies in
`Anneal.MirLiftBench` (`liftBadReifySigMir`, `liftBadCallSigMir`, and
`liftBadPolyApplySigMir`), on the two diverging-call bodies
`liftBadDivergingReturnMir` and `liftDivergingPanicCallerMir`, and on
`liftBadNullFnPtrTransmuteMir`, `liftBadExactDivMir`, and
`liftBadCleanupReturnMir`. A `#guard_msgs` check confirms that `#mir_lift`
refuses a body that takes arguments (`liftPolyIdMir`), because both modes run
the body on the empty argument list. `multiCalleeBody` calls a `u32` constant,
which is also undefined behavior: `multiCalleeBody_not_converges` proves that
it does not converge, `multiCalleeBody_residual_false` refutes the universally
quantified residual hypothesis that a residual abstraction of its call block
would assume, and a `#guard_msgs` check confirms that
`#mir_lift (residual := true)` refuses bodies that need the memory-carrying
mode. A final `run_meta` check fails the build unless `LiftBlock`,
`LiftResidualBlock`, `LiftStmtsTerminator`, and `LiftFrame` are still
irreducible after every `#mir_lift` in the module.

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

## 6. Scope and known limitations

- `#mir_lift` lifts only closed bodies (`argCount = 0`) and rejects others
  with an error.
- In linked-callee mode every call must resolve to a body in `callees`, or to
  the inline `core::intrinsics::exact_div`. External calls cannot be lifted,
  because their answers may panic or abort, which no normal-return
  postcondition allows.
- Diverging calls (`target = none`), failed assertions, `UnwindResume`, and
  cleanup blocks have no lifting rules. In MIR that rustc emits, none of them
  can reach a normal root return (see the `LiftTerminator` docstring and
  `liftDivergingPanic_not_converges`).
- The call-free mode inherited from FF-3.2 does not record the return value:
  its `<item>_model` is `()` and its postcondition constrains only the final
  memory. The linked-callee mode also applies to call-free bodies given
  `(callees := [])` and synthesizes the returned value (see
  `branchFrameBody`).
