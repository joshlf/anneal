/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import LeanMiriSpec.UnwindSetDiscrAndFnPtrLM

/-!
# Episode 2 Dual-Authority Correspondence (`LeanMiriSpec` Authority):
# non-capturing closure function pointers (`ClosureFnPointer`) and their calls

Operational correspondence between the callee-directed closure semantics of
`Trusted.Rustc.V2026_06_01.MirSemantics` (reached only through the real
`stepMirFn`) and the **unmodified vendored** `Miri.Interpreter.Step.step`,
`Miri.Interpreter.Cast.cast`, and `Miri.Interpreter.Call.evalCallTerminator` /
`evalTailCallTerminator`, on verbatim `rustc-capture` bodies (§1).

## How the two machines reach a closure body

`Trusted` reaches a non-capturing closure body through a function pointer by
*callee-directed* dispatch: the linked body is classified by its own
environment parameter `_1`, and the indirect call enters it directly with a
synthesized zero-sized environment prepended (`N + 1` entry arguments for `N`
call arguments). No shim frame exists in `Trusted`.

Miri follows `rustc`: `ClosureFnPointer` resolves the closure for
`ClosureKind::FnOnce` (`Instance::resolve_closure`). The hooks of this module
(§2–§7) implement exactly that resolution and nothing more:

* a closure whose body takes the environment **by value** (`FnOnce`) resolves
  to the body item itself. The vendored `initStackFrame` then takes its
  `nonCapturing && localId == 1` branch: the caller passes `N` arguments, the
  callee has `N + 1` parameters, and `_1` is left storage-live and
  uninitialized. Every `Trusted` step is matched by exactly one `Step.step`
  (**1-to-1 lockstep**, `CfLockstepSim`);
* a closure whose body takes the environment **by reference** (`Fn`, `FnMut`)
  resolves to `InstanceKind::ClosureOnceShim`. The shim MIR (`cfShimBody`,
  `spread_arg = _2`) is `_3 = &mut _1; _0 = FnMut::call_mut(move _3, move _2);
  drop(_1); return`. The vendored `initStackFrame` takes the same
  `nonCapturing && localId == 1` branch for the *shim* frame, spreads the
  caller's `N` arguments into the tuple `_2`, and the shim calls the closure
  body with a real `&mut` to its zero-sized `_1`. `Trusted` takes one step
  where Miri takes one step plus the steps inside the shim frame
  (**stuttering simulation**, `CfStutterSim`; the stutter index counts the
  shim steps).

The call hooks (`cfCallHooks`) are frame-directed: the active body is
recovered from `Frame.functionInstance`, `nonCapturingClosure` is the vendored
`ExecutionCallLeaves.nonCapturingClosure` over the real closure upvar count,
and frames are pushed and popped by the vendored `Stack` operations.

## What is proved

1. **Universal laws (§10, §K, §14)**:
   * `cfStutterCheck_sound` / `cfCertificate_sound`: the executable
     certificate checker is sound for `CfStutterSim` under *any* hooks, any
     program, any body, and any pair of states;
   * `cfStutterSim_zero_lockstep`: a stuttering simulation with stutter index
     `0` is a 1-to-1 lockstep simulation;
   * `cfStutterSim_trusted_run`, `cfStutterSim_miri_run`: a stuttering
     simulation determines the bounded `stepMirFn` run and a successful
     `Step.step` run to a root `Return` with the same observation;
   * `cfStepHooks_eq_K`: the step hooks equal their mechanically derived
     kernel-evaluable form (every `for _ in [a:b]` loop of the vendored
     interpreter rewritten to the equal `List.range'` loop), so each
     kernel-checked statement is about the unmodified vendored code;
   * resolution and pointer-identity laws: `cfResolveClosure_fnOnce_is_item`,
     `cfResolveClosure_fn_is_shim`, `cfResolveClosure_generic_unsupported`,
     `cfInstanceOfAllocNat_item`, `cfInstanceOfAllocNat_shim`,
     `cfFnAllocNat_injective`.
2. **Kernel-checked witnesses (§15)** on the verbatim bodies: the `FnOnce`
   certificate and 1-to-1 lockstep simulation (`cf_fn_once_certificate`,
   `cf_fn_once_lockstep`); the reproducer on `stepMirFn`
   (`cf_trusted_finding_parity`: `159` and `9147 : u32`); the closure matrix on
   `stepMirFn` (`cf_trusted_matrix`); and the fail-closed negatives and
   boundaries on both machines (`cf_neg_capturing_fail_closed`,
   `cf_neg_forged_call_ub`, `cf_neg_transmuted_sig_fail_closed`,
   `cf_neg_extern_c_ub`, `cf_neg_safety_boundary`,
   `cf_normal_spelling_boundary`, `cf_generic_closure_r1_unsupported`,
   `cf_direct_closure_call_trusted_external`, `cf_unwind_boundary`,
   `cf_miri_finding_main_boundary`).
3. **Build-time certificates (§16), not kernel-checked**: the `Fn` / `FnMut`
   stuttering certificates across `ClosureOnceShim`, including the reproducer
   driver `__anneal_vt_driver_61873(35, 24) = 159`.

## What is NOT proved

* The `Fn` / `FnMut` stuttering certificates of §16 are checked by compiled
  evaluation (`#guard`) of the certificate checker, **not by the kernel**, and
  are not theorems: kernel reduction of the vendored memory model on the
  shim's `_3 = &mut _1` does not finish within the build's resource limits.
  Only the `FnOnce` path, which needs no memory, is kernel-checked.
* The reproducer's root body (`9147 : u32`) is kernel-checked on `stepMirFn`
  only. Under the hooks of this module `Step.step` stops with `.unsupported`
  at the body's struct aggregate (`cf_miri_finding_main_boundary`): struct
  aggregates and reference-to-struct projections are outside the hook overlay
  this module builds on. The driver, which contains every closure coercion
  and call of the reproducer, is covered by §16.
* Panic unwinding through an indirect closure call is a boundary only
  (`cf_unwind_boundary`).
* There is no simulation theorem quantified over all programs; the universal
  content is the soundness of the certificate checker and the resolution laws.

## Divergences that are characterized, not hidden

* **`Safety`.** Miri has no dynamic function-pointer `Safety` check; a
  `ClosureFnPointer(Unsafe)` coercion to a safe pointer type is `.ub` in
  `Trusted` and runs to completion in Miri (`cf_neg_safety_boundary`).
* **`"ClosureFnPointer(Normal)"`.** `Trusted` fails closed (`.unsupported`) on
  this spelling, which `rustc-capture` never emits; `translatePointerCoercion`
  maps it to `ClosureFnPointer(Safe)` (`cf_normal_spelling_boundary`).
* **Capturing closures.** `rustc` rejects the coercion (E0308). `Trusted`
  reports `.ub`; the vendored `Cast.cast` rejects the program
  (`invalidProgram "capturing closure in pointer cast"`).
* **Direct closure calls.** A direct `Fn::call(&_env, (x,))` is a visible
  external call in `Trusted` and is executed by Miri; no simulation is claimed.
* **Moves.** The vendored `evalFnCallArgument` does not de-initialize a moved
  caller local, `Trusted` does; `cfSlotRel` therefore relates a `Trusted`
  `.uninit` slot to any live Miri local.
* **Environment and data pointers.** The synchronization relation `cfRel`
  compares the active body, the location, the call depth up to shim frames,
  and the top-frame locals; scalars agree exactly and function pointers denote
  the same linked body. The closure environment local `_1`, data pointers,
  and memory-backed aggregates are **not** compared, and no aliasing model
  (Stacked or Tree Borrows, protectors) is installed.
* **Root unwinding.** Unwinding out of the root frame is UB in Miri
  ("unwinding past the topmost stack frame") and `.panic` in `Trusted`.

## Why the earlier `lean-miri` correspondence did not catch the reproducer

The difftest reproducer
`pass_shared_temp_const_raw_ptr_read_and_freeze_retag__b22_c27` coerces two
non-capturing closures to function pointers and calls them; Miri reports
`9147 : u32`, while the `Trusted` semantics and `rustc-capture` of that time
could not run it. The earlier `C8` correspondence of
`LeanMiriSpec.UnwindSetDiscrAndFnPtrLM` did not expose this, for four
structural reasons:

1. **Hand-constructed closure literals.** Its `ClosureFnPointer` witnesses
   were built on hand-written zero-sized closure operands whose closure type
   carried an empty upvar list (`.closure _ []` written by hand). At that time
   `rustc-capture` emitted the full generic-argument list in that position, so
   the premise "the closure type has no upvars" held for the hand-built
   fixtures and failed for every captured one: the real cast was `.ub`.
2. **Environment-less callee.** The end-to-end witness
   (`w_c8_end_to_end_closure_coercion_and_indirect_call`) linked a hand-built
   callee whose parameters were the `N` user arguments only. A real closure
   body has `arg_count = N + 1` with the environment `_1`, so the witness never
   exercised the closure MIR ABI: neither the synthesized environment of
   `Trusted` nor the `nonCapturing && localId == 1` branch of the vendored
   `initStackFrame`.
3. **Stubbed resolution.** The hooks stubbed `resolveClosureFnOnce` to a fixed
   item and `nonCapturingClosure` to `false`. The cast therefore never
   consulted the closure kind, `ClosureOnceShim` did not exist, and the one
   place where Miri and `Trusted` take a different number of steps was
   outside the proof. Coercion-only witnesses ran with no linked callees.
4. **Fixtures not produced by `rustc-capture`.** Because every premise was
   satisfied by a hand-built fixture, the capture-side defects stayed
   invisible to the correspondence: closure bodies were not captured or
   linked, the closure type's upvar list was wrong, and closure bodies'
   `fnAbi` and environment parameter were never read by any proof.

Episode 1 repaired the capture pipeline and the `Trusted` semantics. This
module closes the correspondence gap structurally: every fixture of §1 is a
verbatim `rustc-capture` body; every positive witness links the captured
closure bodies and calls through the coerced pointer; resolution is the real
`FnOnce` / `ClosureOnceShim` split decided by the linked body; the
`nonCapturingClosure` hook is the vendored one; and the `FnOnce` and
`Fn`/`FnMut` paths are distinguished by the stutter index of a checked
simulation instead of by a shared hand-built callee.

Strict import isolation: this module NEVER imports `MiniRustSpec.*`, and it
does not modify the vendored interpreter (verified by the trailing
`#assert_closure_fn_ptr_lm_audit`).
-/

set_option Elab.async false

namespace LeanMiriSpec.ClosureFnPtrLM

/-! ## §1. Verbatim `rustc-capture` Fixtures (shared with `MiniRustSpec.ClosureFnPtrMR`) -/

section Fixtures
open Trusted.Rustc.V2026_06_01.Layout Trusted.Rustc.V2026_06_01.MirAst Trusted.Rustc.V2026_06_01.MirSemantics
/-- Verbatim `rustc-capture` layout table of `Mir.MiriDiffCorpus.pass_shared_temp_const_raw_ptr_read_and_freeze_retag__b22_c27`. -/
def cfFx_finding_main_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 0 List.nil)) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))))) }
/-- Verbatim `rustc-capture` output (`defPath := "miri_diff_corpus::pass_shared_temp_const_raw_ptr_read_and_freeze_retag__b22_c27"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.MiriDiffCorpus.pass_shared_temp_const_raw_ptr_read_and_freeze_retag__b22_c27.body`). -/
-- bb0: StorageLive(_1); _1 = PairU32 { a: const 7_u32, b: const 35_u32 }; StorageLive(_2); StorageLive(_3); _3 = &_1; _2 = &(*_3); StorageDead(_3); StorageLive(_4); _4 = &raw const ((*_2).1: u32); StorageLive(_5); StorageLive(_6); _6 = &(*_2); _5 = &(*_6); StorageDead(_6); StorageLive(_7); _7 = copy (*_4); StorageLive(_8); _8 = copy (*_4); StorageLive(_9); StorageLive(_10); StorageLive(_11); _11 = copy _7; StorageLive(_12); _12 = copy ((*_5).0: u32); _10 = BitXor(move _11, move _12); StorageDead(_12); StorageDead(_11); StorageLive(_13); StorageLive(_14); _14 = copy _8; _15 = Lt(const 8_u32, const 32_u32); assert(move _15, "attempt to shift left by `{}`, which would overflow", const 8_u32) -> [success: bb1, unwind continue]
-- bb1: _13 = Shl(move _14, const 8_u32); StorageDead(_14); _9 = BitXor(move _10, move _13); StorageDead(_13); StorageDead(_10); StorageLive(_16); StorageLive(_17); StorageLive(_18); _18 = copy _7; _17 = BitAnd(move _18, const 65535_u32); StorageDead(_18); _16 = __anneal_vt_driver_61873(move _17, const 24_u32) -> [return: bb2, unwind continue]
-- bb2: StorageDead(_17); StorageLive(_19); _19 = copy _9; StorageLive(_20); _20 = copy _16; _0 = BitXor(move _19, move _20); StorageDead(_20); StorageDead(_19); StorageDead(_16); StorageDead(_9); StorageDead(_8); StorageDead(_7); StorageDead(_5); StorageDead(_4); StorageDead(_2); StorageDead(_1); return
def cfFx_finding_main : CapturedMir :=
  {
    defPath := "miri_diff_corpus::pass_shared_temp_const_raw_ptr_read_and_freeze_retag__b22_c27",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 0,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "miri_diff_corpus::PairU32" List.nil), layoutIdx := 1 }, debugName := (Option.some "pair") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::PairU32" List.nil)), layoutIdx := 2 }, debugName := (Option.some "tmp") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::PairU32" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.uint UintTy.u32)), layoutIdx := 3 }, debugName := (Option.some "raw") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::PairU32" List.nil)), layoutIdx := 2 }, debugName := (Option.some "shared") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::PairU32" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "first") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "again") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__tail___miri_vt_61873") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__miri_vt_61873") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))))))))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 15), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 1), span := "src/lib.rs:288:9: 288:13" } (List.cons { kind := (StatementKind.assign { local_ := 1, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::PairU32" 0 Option.none) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 7, sizeBytes := 4 })) }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 35, sizeBytes := 4 })) }) List.nil)))), span := "src/lib.rs:288:25: 288:54" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:289:9: 289:12" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:289:25: 289:30" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 1, projection := List.nil })), span := "src/lib.rs:289:25: 289:30" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 3, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:289:25: 289:30" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:289:30: 289:31" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:290:9: 290:12" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 2, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 1 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) })), span := "src/lib.rs:290:27: 290:46" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:291:9: 291:15" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:291:28: 291:33" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 2, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:291:28: 291:33" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 6, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:291:28: 291:33" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:291:33: 291:34" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:292:9: 292:14" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := (List.cons ProjectionElem.deref List.nil) }))), span := "src/lib.rs:292:31: 292:35" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:293:9: 293:14" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := (List.cons ProjectionElem.deref List.nil) }))), span := "src/lib.rs:293:31: 293:35" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:294:9: 294:31" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:294:39: 294:55" } (List.cons { kind := (StatementKind.storageLive 11), span := "src/lib.rs:294:39: 294:44" } (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 7, projection := List.nil }))), span := "src/lib.rs:294:39: 294:44" } (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:294:47: 294:55" } (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 5, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:294:47: 294:55" } (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 11, projection := List.nil }) (Operand.move { local_ := 12, projection := List.nil }))), span := "src/lib.rs:294:39: 294:55" } (List.cons { kind := (StatementKind.storageDead 12), span := "src/lib.rs:294:54: 294:55" } (List.cons { kind := (StatementKind.storageDead 11), span := "src/lib.rs:294:54: 294:55" } (List.cons { kind := (StatementKind.storageLive 13), span := "src/lib.rs:294:58: 294:73" } (List.cons { kind := (StatementKind.storageLive 14), span := "src/lib.rs:294:59: 294:64" } (List.cons { kind := (StatementKind.assign { local_ := 14, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 8, projection := List.nil }))), span := "src/lib.rs:294:59: 294:64" } (List.cons { kind := (StatementKind.assign { local_ := 15, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 8, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:294:58: 294:73" } List.nil)))))))))))))))))))))))))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 15, projection := List.nil }) true 1 UnwindAction.continue_), span := "src/lib.rs:294:58: 294:73" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 13, projection := List.nil } (Rvalue.binaryOp BinOp.shl (Operand.move { local_ := 14, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 8, sizeBytes := 4 })) }))), span := "src/lib.rs:294:58: 294:73" } (List.cons { kind := (StatementKind.storageDead 14), span := "src/lib.rs:294:72: 294:73" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 10, projection := List.nil }) (Operand.move { local_ := 13, projection := List.nil }))), span := "src/lib.rs:294:39: 294:73" } (List.cons { kind := (StatementKind.storageDead 13), span := "src/lib.rs:294:72: 294:73" } (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:294:72: 294:73" } (List.cons { kind := (StatementKind.storageLive 16), span := "src/lib.rs:295:9: 295:24" } (List.cons { kind := (StatementKind.storageLive 17), span := "src/lib.rs:296:9: 296:35" } (List.cons { kind := (StatementKind.storageLive 18), span := "src/lib.rs:296:9: 296:23" } (List.cons { kind := (StatementKind.assign { local_ := 18, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 7, projection := List.nil }))), span := "src/lib.rs:296:10: 296:15" } (List.cons { kind := (StatementKind.assign { local_ := 17, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 18, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 65535, sizeBytes := 4 })) }))), span := "src/lib.rs:296:9: 296:35" } (List.cons { kind := (StatementKind.storageDead 18), span := "src/lib.rs:296:34: 296:35" } List.nil))))))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__anneal_vt_driver_61873" List.nil), layoutIdx := 5 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 17, projection := List.nil }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 24, sizeBytes := 4 })) }) List.nil)) { local_ := 16, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:295:32: 298:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 17), span := "src/lib.rs:298:5: 298:6" } (List.cons { kind := (StatementKind.storageLive 19), span := "src/lib.rs:299:5: 299:27" } (List.cons { kind := (StatementKind.assign { local_ := 19, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 9, projection := List.nil }))), span := "src/lib.rs:299:5: 299:27" } (List.cons { kind := (StatementKind.storageLive 20), span := "src/lib.rs:299:30: 299:54" } (List.cons { kind := (StatementKind.assign { local_ := 20, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 16, projection := List.nil }))), span := "src/lib.rs:299:31: 299:46" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 19, projection := List.nil }) (Operand.move { local_ := 20, projection := List.nil }))), span := "src/lib.rs:299:5: 299:54" } (List.cons { kind := (StatementKind.storageDead 20), span := "src/lib.rs:299:53: 299:54" } (List.cons { kind := (StatementKind.storageDead 19), span := "src/lib.rs:299:53: 299:54" } (List.cons { kind := (StatementKind.storageDead 16), span := "src/lib.rs:300:1: 300:2" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:300:1: 300:2" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:300:1: 300:2" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:300:1: 300:2" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:300:1: 300:2" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:300:1: 300:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:300:1: 300:2" } (List.cons { kind := (StatementKind.storageDead 1), span := "src/lib.rs:300:1: 300:2" } List.nil)))))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:300:2: 300:2" }, isCleanup := false } List.nil))),
    fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_finding_main_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.MiriDiffCorpus.__anneal_vt_driver_61873`. -/
def cfFx_finding_driver_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))) }
/-- Verbatim `rustc-capture` output (`defPath := "miri_diff_corpus::__anneal_vt_driver_61873"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.MiriDiffCorpus.__anneal_vt_driver_61873.body`). -/
-- bb0: StorageLive(_3); StorageLive(_4); _4 = {closure@src/lib.rs:273:36: 273:49}; _3 = move _4 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_4); StorageLive(_5); StorageLive(_6); _6 = copy _3; _5 = move _6 as unsafe fn(u32) -> u32 (PointerCoercion(UnsafeFnPointer, Implicit)); StorageDead(_6); StorageLive(_7); StorageLive(_8); _8 = {closure@src/lib.rs:275:51: 275:64}; _7 = move _8 as unsafe fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Unsafe), Implicit)); StorageDead(_8); StorageLive(_9); StorageLive(_10); _10 = copy _3; _9 = move _10 as *const () (FnPtrToPtr); StorageDead(_10); StorageLive(_11); StorageLive(_12); _12 = copy _5; _11 = move _12 as *const () (FnPtrToPtr); StorageDead(_12); StorageLive(_13); StorageLive(_14); _14 = copy _3; StorageLive(_15); _15 = copy _1; _13 = move _14(move _15) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_15); StorageDead(_14); StorageLive(_16); StorageLive(_17); _17 = copy _5; StorageLive(_18); StorageLive(_19); _19 = copy _13; StorageLive(_20); _20 = copy _2; _18 = BitXor(move _19, move _20); StorageDead(_20); StorageDead(_19); _16 = move _17(move _18) -> [return: bb2, unwind continue]
-- bb2: StorageDead(_18); StorageDead(_17); StorageLive(_21); StorageLive(_22); _22 = copy _7; StorageLive(_23); StorageLive(_24); _24 = copy _16; _23 = BitXor(move _24, const 24_u32); StorageDead(_24); _21 = move _22(move _23) -> [return: bb3, unwind continue]
-- bb3: StorageDead(_23); StorageDead(_22); StorageLive(_25); StorageLive(_26); StorageLive(_27); _27 = copy _9; StorageLive(_28); _28 = copy _11; _26 = Eq(move _27, move _28); switchInt(move _26) -> [0: bb5, otherwise: bb4]
-- bb4: StorageDead(_28); StorageDead(_27); _25 = const 1_u32; goto -> bb6
-- bb5: StorageDead(_28); StorageDead(_27); _25 = const 0_u32; goto -> bb6
-- bb6: StorageDead(_26); StorageLive(_29); StorageLive(_30); StorageLive(_31); _31 = copy _13; StorageLive(_32); StorageLive(_33); _33 = copy _16; _34 = Lt(const 1_u32, const 32_u32); assert(move _34, "attempt to shift left by `{}`, which would overflow", const 1_u32) -> [success: bb7, unwind continue]
-- bb7: _32 = Shl(move _33, const 1_u32); StorageDead(_33); _30 = BitXor(move _31, move _32); StorageDead(_32); StorageDead(_31); StorageLive(_35); StorageLive(_36); _36 = copy _21; _37 = Lt(const 2_u32, const 32_u32); assert(move _37, "attempt to shift left by `{}`, which would overflow", const 2_u32) -> [success: bb8, unwind continue]
-- bb8: _35 = Shl(move _36, const 2_u32); StorageDead(_36); _29 = BitXor(move _30, move _35); StorageDead(_35); StorageDead(_30); StorageLive(_38); _38 = copy _25; _0 = BitXor(move _29, move _38); StorageDead(_38); StorageDead(_29); StorageDead(_25); StorageDead(_21); StorageDead(_16); StorageDead(_13); StorageDead(_11); StorageDead(_9); StorageDead(_7); StorageDead(_5); StorageDead(_3); return
def cfFx_finding_driver : CapturedMir :=
  {
    defPath := "miri_diff_corpus::__anneal_vt_driver_61873",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_seed") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_bias") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "__vt_cfp") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "miri_diff_corpus::__anneal_vt_driver_61873::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "__vt_cufp") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "__vt_cufp_direct") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "miri_diff_corpus::__anneal_vt_driver_61873::{closure#1}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 3 }, debugName := (Option.some "__vt_raw_c") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 3 }, debugName := (Option.some "__vt_raw_d") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_first") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_second") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_third") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_same") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))))))))))))))))))))))))))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 34), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 37), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:273:9: 273:17" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:273:36: 273:77" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "miri_diff_corpus::__anneal_vt_driver_61873::{closure#0}") List.nil)), span := "src/lib.rs:273:36: 273:77" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 4, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:273:36: 273:77" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:273:48: 273:49" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:274:9: 274:18" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:274:44: 274:52" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:274:44: 274:52" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "UnsafeFnPointer") (Operand.move { local_ := 6, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:274:44: 274:52" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:274:51: 274:52" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:275:9: 275:25" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:275:51: 275:79" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "miri_diff_corpus::__anneal_vt_driver_61873::{closure#1}") List.nil)), span := "src/lib.rs:275:51: 275:79" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Unsafe)") (Operand.move { local_ := 8, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:275:51: 275:79" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:275:63: 275:64" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:276:9: 276:19" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:276:33: 276:41" } (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:276:33: 276:41" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.cast CastKind.fnPtrToPtr (Operand.move { local_ := 10, projection := List.nil }) { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 3 })), span := "src/lib.rs:276:33: 276:54" } (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:276:53: 276:54" } (List.cons { kind := (StatementKind.storageLive 11), span := "src/lib.rs:277:9: 277:19" } (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:277:33: 277:42" } (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 5, projection := List.nil }))), span := "src/lib.rs:277:33: 277:42" } (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.cast CastKind.fnPtrToPtr (Operand.move { local_ := 12, projection := List.nil }) { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 3 })), span := "src/lib.rs:277:33: 277:55" } (List.cons { kind := (StatementKind.storageDead 12), span := "src/lib.rs:277:54: 277:55" } (List.cons { kind := (StatementKind.storageLive 13), span := "src/lib.rs:278:9: 278:19" } (List.cons { kind := (StatementKind.storageLive 14), span := "src/lib.rs:278:27: 278:35" } (List.cons { kind := (StatementKind.assign { local_ := 14, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:278:27: 278:35" } (List.cons { kind := (StatementKind.storageLive 15), span := "src/lib.rs:278:36: 278:45" } (List.cons { kind := (StatementKind.assign { local_ := 15, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:278:36: 278:45" } List.nil)))))))))))))))))))))))))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 14, projection := List.nil }) (List.cons (Operand.move { local_ := 15, projection := List.nil }) List.nil) { local_ := 13, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:278:27: 278:46" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 15), span := "src/lib.rs:278:45: 278:46" } (List.cons { kind := (StatementKind.storageDead 14), span := "src/lib.rs:278:45: 278:46" } (List.cons { kind := (StatementKind.storageLive 16), span := "src/lib.rs:279:9: 279:20" } (List.cons { kind := (StatementKind.storageLive 17), span := "src/lib.rs:279:37: 279:46" } (List.cons { kind := (StatementKind.assign { local_ := 17, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 5, projection := List.nil }))), span := "src/lib.rs:279:37: 279:46" } (List.cons { kind := (StatementKind.storageLive 18), span := "src/lib.rs:279:47: 279:69" } (List.cons { kind := (StatementKind.storageLive 19), span := "src/lib.rs:279:47: 279:57" } (List.cons { kind := (StatementKind.assign { local_ := 19, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 13, projection := List.nil }))), span := "src/lib.rs:279:47: 279:57" } (List.cons { kind := (StatementKind.storageLive 20), span := "src/lib.rs:279:60: 279:69" } (List.cons { kind := (StatementKind.assign { local_ := 20, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:279:60: 279:69" } (List.cons { kind := (StatementKind.assign { local_ := 18, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 19, projection := List.nil }) (Operand.move { local_ := 20, projection := List.nil }))), span := "src/lib.rs:279:47: 279:69" } (List.cons { kind := (StatementKind.storageDead 20), span := "src/lib.rs:279:68: 279:69" } (List.cons { kind := (StatementKind.storageDead 19), span := "src/lib.rs:279:68: 279:69" } List.nil))))))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 17, projection := List.nil }) (List.cons (Operand.move { local_ := 18, projection := List.nil }) List.nil) { local_ := 16, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:279:37: 279:70" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 18), span := "src/lib.rs:279:69: 279:70" } (List.cons { kind := (StatementKind.storageDead 17), span := "src/lib.rs:279:69: 279:70" } (List.cons { kind := (StatementKind.storageLive 21), span := "src/lib.rs:280:9: 280:19" } (List.cons { kind := (StatementKind.storageLive 22), span := "src/lib.rs:280:36: 280:52" } (List.cons { kind := (StatementKind.assign { local_ := 22, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 7, projection := List.nil }))), span := "src/lib.rs:280:36: 280:52" } (List.cons { kind := (StatementKind.storageLive 23), span := "src/lib.rs:280:53: 280:72" } (List.cons { kind := (StatementKind.storageLive 24), span := "src/lib.rs:280:53: 280:64" } (List.cons { kind := (StatementKind.assign { local_ := 24, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 16, projection := List.nil }))), span := "src/lib.rs:280:53: 280:64" } (List.cons { kind := (StatementKind.assign { local_ := 23, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 24, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 24, sizeBytes := 4 })) }))), span := "src/lib.rs:280:53: 280:72" } (List.cons { kind := (StatementKind.storageDead 24), span := "src/lib.rs:280:71: 280:72" } List.nil)))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 22, projection := List.nil }) (List.cons (Operand.move { local_ := 23, projection := List.nil }) List.nil) { local_ := 21, projection := List.nil } (Option.some 3) UnwindAction.continue_), span := "src/lib.rs:280:36: 280:73" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 23), span := "src/lib.rs:280:72: 280:73" } (List.cons { kind := (StatementKind.storageDead 22), span := "src/lib.rs:280:72: 280:73" } (List.cons { kind := (StatementKind.storageLive 25), span := "src/lib.rs:281:9: 281:18" } (List.cons { kind := (StatementKind.storageLive 26), span := "src/lib.rs:281:29: 281:53" } (List.cons { kind := (StatementKind.storageLive 27), span := "src/lib.rs:281:29: 281:39" } (List.cons { kind := (StatementKind.assign { local_ := 27, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 9, projection := List.nil }))), span := "src/lib.rs:281:29: 281:39" } (List.cons { kind := (StatementKind.storageLive 28), span := "src/lib.rs:281:43: 281:53" } (List.cons { kind := (StatementKind.assign { local_ := 28, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 11, projection := List.nil }))), span := "src/lib.rs:281:43: 281:53" } (List.cons { kind := (StatementKind.assign { local_ := 26, projection := List.nil } (Rvalue.binaryOp BinOp.eq (Operand.move { local_ := 27, projection := List.nil }) (Operand.move { local_ := 28, projection := List.nil }))), span := "src/lib.rs:281:29: 281:53" } List.nil))))))))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 26, projection := List.nil }) { branches := (List.cons (0, 5) List.nil), otherwise := 4 }), span := "src/lib.rs:281:29: 281:53" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 28), span := "src/lib.rs:281:52: 281:53" } (List.cons { kind := (StatementKind.storageDead 27), span := "src/lib.rs:281:52: 281:53" } (List.cons { kind := (StatementKind.assign { local_ := 25, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:281:56: 281:60" } List.nil))), terminator := { kind := (TerminatorKind.goto 6), span := "src/lib.rs:281:26: 281:76" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 28), span := "src/lib.rs:281:52: 281:53" } (List.cons { kind := (StatementKind.storageDead 27), span := "src/lib.rs:281:52: 281:53" } (List.cons { kind := (StatementKind.assign { local_ := 25, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:281:70: 281:74" } List.nil))), terminator := { kind := (TerminatorKind.goto 6), span := "src/lib.rs:281:26: 281:76" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 26), span := "src/lib.rs:281:75: 281:76" } (List.cons { kind := (StatementKind.storageLive 29), span := "src/lib.rs:282:5: 282:62" } (List.cons { kind := (StatementKind.storageLive 30), span := "src/lib.rs:282:5: 282:39" } (List.cons { kind := (StatementKind.storageLive 31), span := "src/lib.rs:282:5: 282:15" } (List.cons { kind := (StatementKind.assign { local_ := 31, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 13, projection := List.nil }))), span := "src/lib.rs:282:5: 282:15" } (List.cons { kind := (StatementKind.storageLive 32), span := "src/lib.rs:282:18: 282:39" } (List.cons { kind := (StatementKind.storageLive 33), span := "src/lib.rs:282:19: 282:30" } (List.cons { kind := (StatementKind.assign { local_ := 33, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 16, projection := List.nil }))), span := "src/lib.rs:282:19: 282:30" } (List.cons { kind := (StatementKind.assign { local_ := 34, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:282:18: 282:39" } List.nil))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 34, projection := List.nil }) true 7 UnwindAction.continue_), span := "src/lib.rs:282:18: 282:39" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 32, projection := List.nil } (Rvalue.binaryOp BinOp.shl (Operand.move { local_ := 33, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:282:18: 282:39" } (List.cons { kind := (StatementKind.storageDead 33), span := "src/lib.rs:282:38: 282:39" } (List.cons { kind := (StatementKind.assign { local_ := 30, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 31, projection := List.nil }) (Operand.move { local_ := 32, projection := List.nil }))), span := "src/lib.rs:282:5: 282:39" } (List.cons { kind := (StatementKind.storageDead 32), span := "src/lib.rs:282:38: 282:39" } (List.cons { kind := (StatementKind.storageDead 31), span := "src/lib.rs:282:38: 282:39" } (List.cons { kind := (StatementKind.storageLive 35), span := "src/lib.rs:282:42: 282:62" } (List.cons { kind := (StatementKind.storageLive 36), span := "src/lib.rs:282:43: 282:53" } (List.cons { kind := (StatementKind.assign { local_ := 36, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 21, projection := List.nil }))), span := "src/lib.rs:282:43: 282:53" } (List.cons { kind := (StatementKind.assign { local_ := 37, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:282:42: 282:62" } List.nil))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 37, projection := List.nil }) true 8 UnwindAction.continue_), span := "src/lib.rs:282:42: 282:62" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 35, projection := List.nil } (Rvalue.binaryOp BinOp.shl (Operand.move { local_ := 36, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }))), span := "src/lib.rs:282:42: 282:62" } (List.cons { kind := (StatementKind.storageDead 36), span := "src/lib.rs:282:61: 282:62" } (List.cons { kind := (StatementKind.assign { local_ := 29, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 30, projection := List.nil }) (Operand.move { local_ := 35, projection := List.nil }))), span := "src/lib.rs:282:5: 282:62" } (List.cons { kind := (StatementKind.storageDead 35), span := "src/lib.rs:282:61: 282:62" } (List.cons { kind := (StatementKind.storageDead 30), span := "src/lib.rs:282:61: 282:62" } (List.cons { kind := (StatementKind.storageLive 38), span := "src/lib.rs:282:65: 282:74" } (List.cons { kind := (StatementKind.assign { local_ := 38, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 25, projection := List.nil }))), span := "src/lib.rs:282:65: 282:74" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 29, projection := List.nil }) (Operand.move { local_ := 38, projection := List.nil }))), span := "src/lib.rs:282:5: 282:74" } (List.cons { kind := (StatementKind.storageDead 38), span := "src/lib.rs:282:73: 282:74" } (List.cons { kind := (StatementKind.storageDead 29), span := "src/lib.rs:282:73: 282:74" } (List.cons { kind := (StatementKind.storageDead 25), span := "src/lib.rs:283:1: 283:2" } (List.cons { kind := (StatementKind.storageDead 21), span := "src/lib.rs:283:1: 283:2" } (List.cons { kind := (StatementKind.storageDead 16), span := "src/lib.rs:283:1: 283:2" } (List.cons { kind := (StatementKind.storageDead 13), span := "src/lib.rs:283:1: 283:2" } (List.cons { kind := (StatementKind.storageDead 11), span := "src/lib.rs:283:1: 283:2" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:283:1: 283:2" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:283:1: 283:2" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:283:1: 283:2" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:283:1: 283:2" } List.nil))))))))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:283:2: 283:2" }, isCleanup := false } List.nil))))))))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_finding_driver_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.MiriDiffCorpus.__anneal_vt_driver_61873_closure_0`. -/
def cfFx_finding_closure_0_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "miri_diff_corpus::__anneal_vt_driver_61873::{closure#0}"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.MiriDiffCorpus.__anneal_vt_driver_61873_closure_0.body`). -/
-- bb0: StorageLive(_3); _3 = copy _2; _0 = Add(move _3, const 17_u32); StorageDead(_3); return
def cfFx_finding_closure_0 : CapturedMir :=
  {
    defPath := "miri_diff_corpus::__anneal_vt_driver_61873::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "miri_diff_corpus::__anneal_vt_driver_61873::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_z") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:273:63: 273:69" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:273:63: 273:69" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 17, sizeBytes := 4 })) }))), span := "src/lib.rs:273:50: 273:77" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:273:76: 273:77" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:273:77: 273:77" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_finding_closure_0_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.MiriDiffCorpus.__anneal_vt_driver_61873_closure_1`. -/
def cfFx_finding_closure_1_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "miri_diff_corpus::__anneal_vt_driver_61873::{closure#1}"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.MiriDiffCorpus.__anneal_vt_driver_61873_closure_1.body`). -/
-- bb0: StorageLive(_3); _3 = copy _2; _0 = BitXor(move _3, const 17_u32); StorageDead(_3); return
def cfFx_finding_closure_1 : CapturedMir :=
  {
    defPath := "miri_diff_corpus::__anneal_vt_driver_61873::{closure#1}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "miri_diff_corpus::__anneal_vt_driver_61873::{closure#1}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_z") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:275:65: 275:71" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:275:65: 275:71" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 17, sizeBytes := 4 })) }))), span := "src/lib.rs:275:65: 275:79" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:275:78: 275:79" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:275:79: 275:79" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_finding_closure_1_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.Guard_as_core_ops_Drop_drop`. -/
def cfFx_Guard_as_core_ops_Drop_drop_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::<Guard as core::ops::Drop>::drop"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.Guard_as_core_ops_Drop_drop.body`). -/
-- bb0: _0 = const (); return
def cfFx_Guard_as_core_ops_Drop_drop : CapturedMir :=
  {
    defPath := "closure_matrix::<Guard as core::ops::Drop>::drop",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "core::ops::Drop::drop", args := (List.cons (RigidTy.adt "closure_matrix::Guard" List.nil) List.nil) }, implPath := "closure_matrix::<Guard as core::ops::Drop>::drop" } List.nil),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.adt "closure_matrix::Guard" List.nil)), layoutIdx := 3 }, debugName := (Option.some "self") } List.nil)),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 0 }, val := ConstValue.zeroSized }))), span := "src/lib.rs:80:24: 80:26" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:80:26: 80:26" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.ignore }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_Guard_as_core_ops_Drop_drop_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.call_generic`. -/
def cfFx_call_generic_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::call_generic"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.call_generic.body`). -/
-- bb0: StorageLive(_2); _2 = copy _1; _0 = generic_closure::<u32>(move _2) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_2); return
def cfFx_call_generic : CapturedMir :=
  {
    defPath := "closure_matrix::call_generic",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:109:28: 109:29" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:109:28: 109:29" } List.nil)), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "closure_matrix::generic_closure" (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 2, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:109:5: 109:30" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:109:29: 109:30" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:110:2: 110:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_call_generic_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.capturing_direct`. -/
def cfFx_capturing_direct_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 3 List.nil) } List.nil)))))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::capturing_direct"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.capturing_direct.body`). -/
-- bb0: StorageLive(_3); _3 = (); StorageLive(_4); _4 = {closure@src/lib.rs:114:17: 114:30} { y: copy _2 }; StorageLive(_5); _5 = {closure@src/lib.rs:115:15: 115:28} { unit: copy _3 }; StorageLive(_6); StorageLive(_7); _7 = &_4; StorageLive(_8); StorageLive(_9); _9 = copy _1; _8 = (move _9,); _6 = <{closure@src/lib.rs:114:17: 114:30} as core::ops::Fn<(u32,)>>::call(move _7, move _8) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_9); StorageDead(_8); StorageDead(_7); StorageLive(_10); StorageLive(_11); _11 = &_5; StorageLive(_12); StorageLive(_13); _13 = copy _1; _12 = (move _13,); _10 = <{closure@src/lib.rs:115:15: 115:28} as core::ops::Fn<(u32,)>>::call(move _11, move _12) -> [return: bb2, unwind continue]
-- bb2: StorageDead(_13); StorageDead(_12); StorageDead(_11); _0 = BitXor(move _6, move _10); StorageDead(_10); StorageDead(_6); StorageDead(_5); StorageDead(_4); StorageDead(_3); return
def cfFx_capturing_direct : CapturedMir :=
  {
    defPath := "closure_matrix::capturing_direct",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "y") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 1 }, debugName := (Option.some "unit") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.closure "closure_matrix::capturing_direct::{closure#0}" (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 2 }, debugName := (Option.some "add_y") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.closure "closure_matrix::capturing_direct::{closure#1}" (List.cons (RigidTy.tuple List.nil) List.nil)), layoutIdx := 3 }, debugName := (Option.some "zst") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::capturing_direct::{closure#0}" (List.cons (RigidTy.uint UintTy.u32) List.nil))), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::capturing_direct::{closure#1}" (List.cons (RigidTy.tuple List.nil) List.nil))), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:113:9: 113:13" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate AggregateKind.tuple List.nil)), span := "src/lib.rs:113:16: 113:18" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:114:9: 114:14" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::capturing_direct::{closure#0}") (List.cons (Operand.copy { local_ := 2, projection := List.nil }) List.nil))), span := "src/lib.rs:114:17: 114:49" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:115:9: 115:12" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::capturing_direct::{closure#1}") (List.cons (Operand.copy { local_ := 3, projection := List.nil }) List.nil))), span := "src/lib.rs:115:15: 118:6" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:119:5: 119:13" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:119:5: 119:10" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 4, projection := List.nil })), span := "src/lib.rs:119:5: 119:10" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:119:5: 119:13" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:119:11: 119:12" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:119:11: 119:12" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.aggregate AggregateKind.tuple (List.cons (Operand.move { local_ := 9, projection := List.nil }) List.nil))), span := "src/lib.rs:119:5: 119:13" } List.nil))))))))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::ops::Fn::call" (List.cons (RigidTy.closure "closure_matrix::capturing_direct::{closure#0}" (List.cons (RigidTy.uint UintTy.u32) List.nil)) (List.cons (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)) List.nil))), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) (List.cons (Operand.move { local_ := 8, projection := List.nil }) List.nil)) { local_ := 6, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:119:5: 119:13" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:119:12: 119:13" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:119:12: 119:13" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:119:12: 119:13" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:119:16: 119:22" } (List.cons { kind := (StatementKind.storageLive 11), span := "src/lib.rs:119:16: 119:19" } (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 5, projection := List.nil })), span := "src/lib.rs:119:16: 119:19" } (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:119:16: 119:22" } (List.cons { kind := (StatementKind.storageLive 13), span := "src/lib.rs:119:20: 119:21" } (List.cons { kind := (StatementKind.assign { local_ := 13, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:119:20: 119:21" } (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.aggregate AggregateKind.tuple (List.cons (Operand.move { local_ := 13, projection := List.nil }) List.nil))), span := "src/lib.rs:119:16: 119:22" } List.nil)))))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::ops::Fn::call" (List.cons (RigidTy.closure "closure_matrix::capturing_direct::{closure#1}" (List.cons (RigidTy.tuple List.nil) List.nil)) (List.cons (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)) List.nil))), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 11, projection := List.nil }) (List.cons (Operand.move { local_ := 12, projection := List.nil }) List.nil)) { local_ := 10, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:119:16: 119:22" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 13), span := "src/lib.rs:119:21: 119:22" } (List.cons { kind := (StatementKind.storageDead 12), span := "src/lib.rs:119:21: 119:22" } (List.cons { kind := (StatementKind.storageDead 11), span := "src/lib.rs:119:21: 119:22" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 6, projection := List.nil }) (Operand.move { local_ := 10, projection := List.nil }))), span := "src/lib.rs:119:5: 119:22" } (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:119:21: 119:22" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:119:21: 119:22" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:120:1: 120:2" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:120:1: 120:2" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:120:1: 120:2" } List.nil))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:120:2: 120:2" }, isCleanup := false } List.nil))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_capturing_direct_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.capturing_direct_closure_0`. -/
def cfFx_capturing_direct_closure_0_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::capturing_direct::{closure#0}"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.capturing_direct_closure_0.body`). -/
-- bb0: StorageLive(_3); _3 = copy _2; StorageLive(_4); _4 = copy ((*_1).0: u32); _0 = Add(move _3, move _4); StorageDead(_4); StorageDead(_3); return
def cfFx_capturing_direct_closure_0 : CapturedMir :=
  {
    defPath := "closure_matrix::capturing_direct::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::capturing_direct::{closure#0}" (List.cons (RigidTy.uint UintTy.u32) List.nil))), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:114:44: 114:45" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:114:44: 114:45" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:114:47: 114:48" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:114:47: 114:48" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.move { local_ := 4, projection := List.nil }))), span := "src/lib.rs:114:31: 114:49" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:114:48: 114:49" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:114:48: 114:49" } List.nil))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:114:49: 114:49" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_capturing_direct_closure_0_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.capturing_direct_closure_1`. -/
def cfFx_capturing_direct_closure_1_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } List.nil)))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::capturing_direct::{closure#1}"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.capturing_direct_closure_1.body`). -/
-- bb0: StorageLive(_3); _3 = copy ((*_1).0: ()); _0 = copy _2; StorageDead(_3); return
def cfFx_capturing_direct_closure_1 : CapturedMir :=
  {
    defPath := "closure_matrix::capturing_direct::{closure#1}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::capturing_direct::{closure#1}" (List.cons (RigidTy.tuple List.nil) List.nil))), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 1 }, debugName := (Option.some "_keep") } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:116:13: 116:18" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.tuple List.nil), layoutIdx := 1 }) List.nil)) }))), span := "src/lib.rs:116:21: 116:25" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:117:9: 117:10" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:118:5: 118:6" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:118:6: 118:6" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_capturing_direct_closure_1_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.ces_through_closure_fn_ptr`. -/
def cfFx_ces_through_closure_fn_ptr_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } List.nil)))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::ces_through_closure_fn_ptr"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.ces_through_closure_fn_ptr.body`). -/
-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:99:30: 99:38}; _2 = move _3 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = copy _1; _4 = (move _5,); StorageDead(_5); StorageLive(_6); _6 = copy _2; _0 = move _6(move (_4.0: u32)) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_6); StorageDead(_4); StorageDead(_2); return
def cfFx_ces_through_closure_fn_ptr : CapturedMir :=
  {
    defPath := "closure_matrix::ces_through_closure_fn_ptr",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "rt") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::ces_through_closure_fn_ptr::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } List.nil))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:99:9: 99:11" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:99:30: 99:61" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::ces_through_closure_fn_ptr::{closure#0}") List.nil)), span := "src/lib.rs:99:30: 99:61" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:99:30: 99:61" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:99:37: 99:38" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:100:23: 100:27" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:100:24: 100:25" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:100:24: 100:25" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate AggregateKind.tuple (List.cons (Operand.move { local_ := 5, projection := List.nil }) List.nil))), span := "src/lib.rs:100:23: 100:27" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:100:26: 100:27" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:100:37: 100:39" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:100:37: 100:39" } List.nil)))))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 6, projection := List.nil }) (List.cons (Operand.move { local_ := 4, projection := (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil) }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:100:5: 100:40" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:100:39: 100:40" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:100:39: 100:40" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:101:1: 101:2" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:101:2: 101:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_ces_through_closure_fn_ptr_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.ces_through_closure_fn_ptr_closure_0`. -/
def cfFx_ces_through_closure_fn_ptr_closure_0_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::ces_through_closure_fn_ptr::{closure#0}"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.ces_through_closure_fn_ptr_closure_0.body`). -/
-- bb0: StorageLive(_3); _3 = copy _2; _0 = Add(move _3, const 17_u32); StorageDead(_3); return
def cfFx_ces_through_closure_fn_ptr_closure_0 : CapturedMir :=
  {
    defPath := "closure_matrix::ces_through_closure_fn_ptr::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::ces_through_closure_fn_ptr::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:99:52: 99:53" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:99:52: 99:53" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 17, sizeBytes := 4 })) }))), span := "src/lib.rs:99:39: 99:61" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:99:60: 99:61" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:99:61: 99:61" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_ces_through_closure_fn_ptr_closure_0_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.ct_add`. -/
def cfFx_ct_add_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::ct_add"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.ct_add.body`). -/
-- bb0: _0 = copy _1; return
def cfFx_ct_add : CapturedMir :=
  {
    defPath := "closure_matrix::ct_add",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } List.nil)),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:95:5: 95:6" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:96:2: 96:2" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_ct_add_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.direct_closure_call`. -/
def cfFx_direct_closure_call_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } List.nil)))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::direct_closure_call"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.direct_closure_call.body`). -/
-- bb0: StorageLive(_2); _2 = {closure@src/lib.rs:90:13: 90:21}; StorageLive(_3); _3 = &_2; StorageLive(_4); StorageLive(_5); _5 = copy _1; _4 = (move _5,); _0 = <{closure@src/lib.rs:90:13: 90:21} as core::ops::Fn<(u32,)>>::call(move _3, move _4) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_5); StorageDead(_4); StorageDead(_3); StorageDead(_2); return
def cfFx_direct_closure_call : CapturedMir :=
  {
    defPath := "closure_matrix::direct_closure_call",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.closure "closure_matrix::direct_closure_call::{closure#0}" List.nil), layoutIdx := 1 }, debugName := (Option.some "c") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::direct_closure_call::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:90:9: 90:10" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::direct_closure_call::{closure#0}") List.nil)), span := "src/lib.rs:90:13: 90:43" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:91:5: 91:6" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 2, projection := List.nil })), span := "src/lib.rs:91:5: 91:6" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:91:5: 91:9" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:91:7: 91:8" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:91:7: 91:8" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate AggregateKind.tuple (List.cons (Operand.move { local_ := 5, projection := List.nil }) List.nil))), span := "src/lib.rs:91:5: 91:9" } List.nil)))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::ops::Fn::call" (List.cons (RigidTy.closure "closure_matrix::direct_closure_call::{closure#0}" List.nil) (List.cons (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)) List.nil))), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 3, projection := List.nil }) (List.cons (Operand.move { local_ := 4, projection := List.nil }) List.nil)) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:91:5: 91:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:91:8: 91:9" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:91:8: 91:9" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:91:8: 91:9" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:92:1: 92:2" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:92:2: 92:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_direct_closure_call_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.direct_closure_call_closure_0`. -/
def cfFx_direct_closure_call_closure_0_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::direct_closure_call::{closure#0}"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.direct_closure_call_closure_0.body`). -/
-- bb0: StorageLive(_3); _3 = copy _2; _0 = Add(move _3, const 9_u32); StorageDead(_3); return
def cfFx_direct_closure_call_closure_0 : CapturedMir :=
  {
    defPath := "closure_matrix::direct_closure_call::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::direct_closure_call::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:90:35: 90:36" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:90:35: 90:36" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 9, sizeBytes := 4 })) }))), span := "src/lib.rs:90:22: 90:43" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:90:42: 90:43" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:90:43: 90:43" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_direct_closure_call_closure_0_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.fn_mut_kind`. -/
def cfFx_fn_mut_kind_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::fn_mut_kind"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.fn_mut_kind.body`). -/
-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:28:20: 28:28}; _2 = id_mut::<{closure@src/lib.rs:28:20: 28:28}>(move _3) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = copy _2; _4 = move _5 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_5); StorageLive(_6); _6 = copy _4; StorageLive(_7); _7 = copy _1; _0 = move _6(move _7) -> [return: bb2, unwind continue]
-- bb2: StorageDead(_7); StorageDead(_6); StorageDead(_4); StorageDead(_2); return
def cfFx_fn_mut_kind : CapturedMir :=
  {
    defPath := "closure_matrix::fn_mut_kind",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.closure "closure_matrix::fn_mut_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := (Option.some "c") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::fn_mut_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::fn_mut_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:28:9: 28:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:28:20: 28:50" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::fn_mut_kind::{closure#0}") List.nil)), span := "src/lib.rs:28:20: 28:50" } List.nil))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "closure_matrix::id_mut" (List.cons (RigidTy.closure "closure_matrix::fn_mut_kind::{closure#0}" List.nil) List.nil)), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 3, projection := List.nil }) List.nil) { local_ := 2, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:28:13: 28:51" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:28:50: 28:51" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:29:9: 29:10" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:29:29: 29:30" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:29:29: 29:30" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 5, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 })), span := "src/lib.rs:29:29: 29:30" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:29:29: 29:30" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:30:5: 30:6" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := List.nil }))), span := "src/lib.rs:30:5: 30:6" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:30:7: 30:8" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:30:7: 30:8" } List.nil)))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 6, projection := List.nil }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:30:5: 30:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:30:8: 30:9" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:30:8: 30:9" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:31:1: 31:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:31:1: 31:2" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:31:2: 31:2" }, isCleanup := false } List.nil))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_fn_mut_kind_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.fn_mut_kind_closure_0`. -/
def cfFx_fn_mut_kind_closure_0_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::fn_mut_kind::{closure#0}"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.fn_mut_kind_closure_0.body`). -/
-- bb0: StorageLive(_3); _3 = copy _2; _0 = Add(move _3, const 2_u32); StorageDead(_3); return
def cfFx_fn_mut_kind_closure_0 : CapturedMir :=
  {
    defPath := "closure_matrix::fn_mut_kind::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.closure "closure_matrix::fn_mut_kind::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:28:42: 28:43" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:28:42: 28:43" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }))), span := "src/lib.rs:28:29: 28:50" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:28:49: 28:50" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:28:50: 28:50" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_fn_mut_kind_closure_0_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.fn_once_kind`. -/
def cfFx_fn_once_kind_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::fn_once_kind"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.fn_once_kind.body`). -/
-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:34:21: 34:29}; _2 = id_once::<{closure@src/lib.rs:34:21: 34:29}>(move _3) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = copy _2; _4 = move _5 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_5); StorageLive(_6); _6 = copy _4; StorageLive(_7); _7 = copy _1; _0 = move _6(move _7) -> [return: bb2, unwind continue]
-- bb2: StorageDead(_7); StorageDead(_6); StorageDead(_4); StorageDead(_2); return
def cfFx_fn_once_kind : CapturedMir :=
  {
    defPath := "closure_matrix::fn_once_kind",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.closure "closure_matrix::fn_once_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := (Option.some "c") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::fn_once_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::fn_once_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:34:9: 34:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:34:21: 34:51" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::fn_once_kind::{closure#0}") List.nil)), span := "src/lib.rs:34:21: 34:51" } List.nil))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "closure_matrix::id_once" (List.cons (RigidTy.closure "closure_matrix::fn_once_kind::{closure#0}" List.nil) List.nil)), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 3, projection := List.nil }) List.nil) { local_ := 2, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:34:13: 34:52" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:34:51: 34:52" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:35:9: 35:10" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:35:29: 35:30" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:35:29: 35:30" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 5, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 })), span := "src/lib.rs:35:29: 35:30" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:35:29: 35:30" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:36:5: 36:6" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := List.nil }))), span := "src/lib.rs:36:5: 36:6" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:36:7: 36:8" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:36:7: 36:8" } List.nil)))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 6, projection := List.nil }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:36:5: 36:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:36:8: 36:9" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:36:8: 36:9" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:37:1: 37:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:37:1: 37:2" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:37:2: 37:2" }, isCleanup := false } List.nil))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_fn_once_kind_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.fn_once_kind_closure_0`. -/
def cfFx_fn_once_kind_closure_0_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::fn_once_kind::{closure#0}"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.fn_once_kind_closure_0.body`). -/
-- bb0: StorageLive(_3); _3 = copy _2; _0 = Add(move _3, const 3_u32); StorageDead(_3); return
def cfFx_fn_once_kind_closure_0 : CapturedMir :=
  {
    defPath := "closure_matrix::fn_once_kind::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::fn_once_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:34:43: 34:44" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:34:43: 34:44" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 3, sizeBytes := 4 })) }))), span := "src/lib.rs:34:30: 34:51" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:34:50: 34:51" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:34:51: 34:51" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.ignore } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_fn_once_kind_closure_0_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.fn_shared`. -/
def cfFx_fn_shared_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::fn_shared"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.fn_shared.body`). -/
-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:23:29: 23:37}; _2 = move _3 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); _4 = copy _2; StorageLive(_5); _5 = copy _1; _0 = move _4(move _5) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_5); StorageDead(_4); StorageDead(_2); return
def cfFx_fn_shared : CapturedMir :=
  {
    defPath := "closure_matrix::fn_shared",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::fn_shared::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:23:9: 23:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:23:29: 23:60" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::fn_shared::{closure#0}") List.nil)), span := "src/lib.rs:23:29: 23:60" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:23:29: 23:60" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:23:36: 23:37" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:24:5: 24:6" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:24:5: 24:6" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:24:7: 24:8" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:24:7: 24:8" } List.nil))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 4, projection := List.nil }) (List.cons (Operand.move { local_ := 5, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:24:5: 24:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:24:8: 24:9" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:24:8: 24:9" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:25:1: 25:2" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:25:2: 25:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_fn_shared_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.fn_shared_closure_0`. -/
def cfFx_fn_shared_closure_0_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::fn_shared::{closure#0}"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.fn_shared_closure_0.body`). -/
-- bb0: StorageLive(_3); _3 = copy _2; _0 = Add(move _3, const 17_u32); StorageDead(_3); return
def cfFx_fn_shared_closure_0 : CapturedMir :=
  {
    defPath := "closure_matrix::fn_shared::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::fn_shared::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:23:51: 23:52" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:23:51: 23:52" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 17, sizeBytes := 4 })) }))), span := "src/lib.rs:23:38: 23:60" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:23:59: 23:60" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:23:60: 23:60" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_fn_shared_closure_0_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.generic_closure`. -/
def cfFx_generic_closure_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::generic_closure"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.generic_closure.body`). -/
-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:104:25: 104:31}; _2 = move _3 as fn(T) -> T (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); _4 = copy _2; StorageLive(_5); _5 = copy _1; _0 = move _4(move _5) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_5); StorageDead(_4); StorageDead(_2); return
def cfFx_generic_closure : CapturedMir :=
  {
    defPath := "closure_matrix::generic_closure",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    typeParamCount := 1,
    genericParams := (List.cons { idx := 0, name := "T" } List.nil),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.param 0 "T"), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.param 0 "T"), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.param 0 "T") List.nil) (RigidTy.param 0 "T") Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::generic_closure::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.param 0 "T") List.nil) (RigidTy.param 0 "T") Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.param 0 "T"), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:104:9: 104:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:104:25: 104:33" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::generic_closure::{closure#0}") List.nil)), span := "src/lib.rs:104:25: 104:33" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.param 0 "T") List.nil) (RigidTy.param 0 "T") Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:104:25: 104:33" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:104:30: 104:31" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:105:5: 105:6" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:105:5: 105:6" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:105:7: 105:8" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:105:7: 105:8" } List.nil))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 4, projection := List.nil }) (List.cons (Operand.move { local_ := 5, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:105:5: 105:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:105:8: 105:9" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:105:8: 105:9" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:106:1: 106:2" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:106:2: 106:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.ignore } List.nil), ret := { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.ignore }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_generic_closure_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.generic_closure_closure_0`. -/
def cfFx_generic_closure_closure_0_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::generic_closure::{closure#0}"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.generic_closure_closure_0.body`). -/
-- bb0: _0 = copy _2; return
def cfFx_generic_closure_closure_0 : CapturedMir :=
  {
    defPath := "closure_matrix::generic_closure::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    typeParamCount := 1,
    genericParams := (List.cons { idx := 0, name := "T" } List.nil),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.param 0 "T"), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::generic_closure::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.param 0 "T"), layoutIdx := 0 }, debugName := (Option.some "y") } List.nil))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:104:32: 104:33" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:104:33: 104:33" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.ignore } List.nil)), ret := { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.ignore }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_generic_closure_closure_0_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.helper_triple`. -/
def cfFx_helper_triple_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::helper_triple"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.helper_triple.body`). -/
-- bb0: StorageLive(_2); _2 = copy _1; _0 = Mul(move _2, const 3_u32); StorageDead(_2); return
def cfFx_helper_triple : CapturedMir :=
  {
    defPath := "closure_matrix::helper_triple",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:19:18: 19:19" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:19:18: 19:19" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.mul (Operand.move { local_ := 2, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 3, sizeBytes := 4 })) }))), span := "src/lib.rs:19:5: 19:26" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:19:25: 19:26" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:20:2: 20:2" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_helper_triple_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.id_mut`. -/
def cfFx_id_mut_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::id_mut"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.id_mut.body`). -/
-- bb0: _0 = move _1; return
def cfFx_id_mut : CapturedMir :=
  {
    defPath := "closure_matrix::id_mut",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    typeParamCount := 1,
    genericParams := (List.cons { idx := 0, name := "F" } List.nil),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.param 0 "F"), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.param 0 "F"), layoutIdx := 0 }, debugName := (Option.some "f") } List.nil)),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.move { local_ := 1, projection := List.nil }))), span := "src/lib.rs:9:5: 9:6" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:10:2: 10:2" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.ignore } List.nil), ret := { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.ignore }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_id_mut_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.id_once`. -/
def cfFx_id_once_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::id_once"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.id_once.body`). -/
-- bb0: _0 = move _1; return
def cfFx_id_once : CapturedMir :=
  {
    defPath := "closure_matrix::id_once",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    typeParamCount := 1,
    genericParams := (List.cons { idx := 0, name := "F" } List.nil),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.param 0 "F"), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.param 0 "F"), layoutIdx := 0 }, debugName := (Option.some "f") } List.nil)),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.move { local_ := 1, projection := List.nil }))), span := "src/lib.rs:14:5: 14:6" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:15:2: 15:2" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.ignore } List.nil), ret := { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.ignore }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_id_once_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.mixed_fn_item_and_closure`. -/
def cfFx_mixed_fn_item_and_closure_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::mixed_fn_item_and_closure"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.mixed_fn_item_and_closure.body`). -/
-- bb0: StorageLive(_2); _2 = helper_triple as fn(u32) -> u32 (PointerCoercion(ReifyFnPointer(Safe), Implicit)); StorageLive(_3); StorageLive(_4); _4 = {closure@src/lib.rs:63:29: 63:37}; _3 = move _4 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_4); StorageLive(_5); StorageLive(_6); _6 = copy _2; StorageLive(_7); _7 = copy _1; _5 = move _6(move _7) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_7); StorageDead(_6); StorageLive(_8); StorageLive(_9); _9 = copy _3; StorageLive(_10); _10 = copy _1; _8 = move _9(move _10) -> [return: bb2, unwind continue]
-- bb2: StorageDead(_10); StorageDead(_9); _0 = BitXor(move _5, move _8); StorageDead(_8); StorageDead(_5); StorageDead(_3); StorageDead(_2); return
def cfFx_mixed_fn_item_and_closure : CapturedMir :=
  {
    defPath := "closure_matrix::mixed_fn_item_and_closure",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "b") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::mixed_fn_item_and_closure::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:62:9: 62:10" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ReifyFnPointer(Safe)") (Operand.constant { ty := { kind := (RigidTy.fnDef "closure_matrix::helper_triple" List.nil), layoutIdx := 2 }, val := ConstValue.zeroSized }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:62:29: 62:42" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:63:9: 63:10" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:63:29: 63:59" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::mixed_fn_item_and_closure::{closure#0}") List.nil)), span := "src/lib.rs:63:29: 63:59" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 4, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:63:29: 63:59" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:63:36: 63:37" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:64:5: 64:9" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:64:5: 64:6" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:64:5: 64:6" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:64:7: 64:8" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:64:7: 64:8" } List.nil)))))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 6, projection := List.nil }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) List.nil) { local_ := 5, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:64:5: 64:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:64:8: 64:9" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:64:8: 64:9" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:64:12: 64:16" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:64:12: 64:13" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:64:12: 64:13" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:64:14: 64:15" } (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:64:14: 64:15" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 9, projection := List.nil }) (List.cons (Operand.move { local_ := 10, projection := List.nil }) List.nil) { local_ := 8, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:64:12: 64:16" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:64:15: 64:16" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:64:15: 64:16" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 5, projection := List.nil }) (Operand.move { local_ := 8, projection := List.nil }))), span := "src/lib.rs:64:5: 64:16" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:64:15: 64:16" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:64:15: 64:16" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:65:1: 65:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:65:1: 65:2" } List.nil))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:65:2: 65:2" }, isCleanup := false } List.nil))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_mixed_fn_item_and_closure_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.mixed_fn_item_and_closure_closure_0`. -/
def cfFx_mixed_fn_item_and_closure_closure_0_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::mixed_fn_item_and_closure::{closure#0}"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.mixed_fn_item_and_closure_closure_0.body`). -/
-- bb0: StorageLive(_3); _3 = copy _2; _0 = Mul(move _3, const 5_u32); StorageDead(_3); return
def cfFx_mixed_fn_item_and_closure_closure_0 : CapturedMir :=
  {
    defPath := "closure_matrix::mixed_fn_item_and_closure::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::mixed_fn_item_and_closure::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "v") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:63:51: 63:52" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:63:51: 63:52" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.mul (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 5, sizeBytes := 4 })) }))), span := "src/lib.rs:63:38: 63:59" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:63:58: 63:59" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:63:59: 63:59" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_mixed_fn_item_and_closure_closure_0_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.tail_through_closure`. -/
def cfFx_tail_through_closure_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := VariantsShape.empty, isUninhabited := true } List.nil)))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::tail_through_closure"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.tail_through_closure.body`). -/
-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:68:29: 68:37}; _2 = move _3 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = copy _2; StorageLive(_6); _6 = copy _1; tailcall move _5(move _6)
def cfFx_tail_through_closure : CapturedMir :=
  {
    defPath := "closure_matrix::tail_through_closure",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::tail_through_closure::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.never, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:68:9: 68:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:68:29: 68:46" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::tail_through_closure::{closure#0}") List.nil)), span := "src/lib.rs:68:29: 68:46" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:68:29: 68:46" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:68:36: 68:37" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:69:5: 69:16" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:69:12: 69:13" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:69:12: 69:13" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:69:14: 69:15" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:69:14: 69:15" } List.nil)))))))))), terminator := { kind := (TerminatorKind.tailCall (Operand.move { local_ := 5, projection := List.nil }) (List.cons (Operand.move { local_ := 6, projection := List.nil }) List.nil)), span := "src/lib.rs:69:5: 69:16" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_tail_through_closure_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.tail_through_closure_closure_0`. -/
def cfFx_tail_through_closure_closure_0_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::tail_through_closure::{closure#0}"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.tail_through_closure_closure_0.body`). -/
-- bb0: StorageLive(_3); _3 = copy _2; _0 = BitXor(move _3, const 5_u32); StorageDead(_3); return
def cfFx_tail_through_closure_closure_0 : CapturedMir :=
  {
    defPath := "closure_matrix::tail_through_closure::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::tail_through_closure::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:68:38: 68:39" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:68:38: 68:39" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 5, sizeBytes := 4 })) }))), span := "src/lib.rs:68:38: 68:46" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:68:45: 68:46" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:68:46: 68:46" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_tail_through_closure_closure_0_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.two_arg`. -/
def cfFx_two_arg_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::two_arg"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.two_arg.body`). -/
-- bb0: StorageLive(_3); StorageLive(_4); _4 = {closure@src/lib.rs:45:34: 45:50}; _3 = move _4 as fn(u32, u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_4); StorageLive(_5); _5 = copy _3; StorageLive(_6); _6 = copy _1; StorageLive(_7); _7 = copy _2; _0 = move _5(move _6, move _7) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_7); StorageDead(_6); StorageDead(_5); StorageDead(_3); return
def cfFx_two_arg : CapturedMir :=
  {
    defPath := "closure_matrix::two_arg",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "y") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) (List.cons (RigidTy.uint UintTy.u32) List.nil)) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::two_arg::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) (List.cons (RigidTy.uint UintTy.u32) List.nil)) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:45:9: 45:10" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:45:34: 45:56" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::two_arg::{closure#0}") List.nil)), span := "src/lib.rs:45:34: 45:56" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 4, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) (List.cons (RigidTy.uint UintTy.u32) List.nil)) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:45:34: 45:56" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:45:49: 45:50" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:46:5: 46:6" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:46:5: 46:6" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:46:7: 46:8" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:46:7: 46:8" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:46:10: 46:11" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:46:10: 46:11" } List.nil))))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 5, projection := List.nil }) (List.cons (Operand.move { local_ := 6, projection := List.nil }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) List.nil)) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:46:5: 46:12" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:46:11: 46:12" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:46:11: 46:12" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:46:11: 46:12" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:47:1: 47:2" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:47:2: 47:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_two_arg_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.two_arg_closure_0`. -/
def cfFx_two_arg_closure_0_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::two_arg::{closure#0}"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.two_arg_closure_0.body`). -/
-- bb0: StorageLive(_4); _4 = copy _2; StorageLive(_5); _5 = copy _3; _0 = BitXor(move _4, move _5); StorageDead(_5); StorageDead(_4); return
def cfFx_two_arg_closure_0 : CapturedMir :=
  {
    defPath := "closure_matrix::two_arg::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 3,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::two_arg::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "b") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:45:51: 45:52" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:45:51: 45:52" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:45:55: 45:56" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:45:55: 45:56" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 4, projection := List.nil }) (Operand.move { local_ := 5, projection := List.nil }))), span := "src/lib.rs:45:51: 45:56" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:45:55: 45:56" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:45:55: 45:56" } List.nil))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:45:56: 45:56" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil))), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_two_arg_closure_0_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.unsafe_closure`. -/
def cfFx_unsafe_closure_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::unsafe_closure"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.unsafe_closure.body`). -/
-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:50:36: 50:44}; _2 = move _3 as unsafe fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Unsafe), Implicit)); StorageDead(_3); StorageLive(_4); _4 = copy _2; StorageLive(_5); _5 = copy _1; _0 = move _4(move _5) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_5); StorageDead(_4); StorageDead(_2); return
def cfFx_unsafe_closure : CapturedMir :=
  {
    defPath := "closure_matrix::unsafe_closure",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::unsafe_closure::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:50:9: 50:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:50:36: 50:54" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::unsafe_closure::{closure#0}") List.nil)), span := "src/lib.rs:50:36: 50:54" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Unsafe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:50:36: 50:54" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:50:43: 50:44" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:51:14: 51:15" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:51:14: 51:15" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:51:16: 51:17" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:51:16: 51:17" } List.nil))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 4, projection := List.nil }) (List.cons (Operand.move { local_ := 5, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:51:14: 51:18" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:51:17: 51:18" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:51:17: 51:18" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:52:1: 52:2" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:52:2: 52:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_unsafe_closure_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.unsafe_closure_closure_0`. -/
def cfFx_unsafe_closure_closure_0_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::unsafe_closure::{closure#0}"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.unsafe_closure_closure_0.body`). -/
-- bb0: StorageLive(_3); _3 = copy _2; _0 = BitXor(move _3, const 17_u32); StorageDead(_3); return
def cfFx_unsafe_closure_closure_0 : CapturedMir :=
  {
    defPath := "closure_matrix::unsafe_closure::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::unsafe_closure::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:50:45: 50:46" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:50:45: 50:46" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 17, sizeBytes := 4 })) }))), span := "src/lib.rs:50:45: 50:54" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:50:53: 50:54" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:50:54: 50:54" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_unsafe_closure_closure_0_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.unwind_through_closure`. -/
def cfFx_unwind_through_closure_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::unwind_through_closure"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.unwind_through_closure.body`). -/
-- bb0: StorageLive(_2); StorageLive(_3); _3 = copy _1; _2 = Guard(move _3); StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = {closure@src/lib.rs:85:29: 85:37}; _4 = move _5 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_5); StorageLive(_6); _6 = copy _4; StorageLive(_7); _7 = copy _1; _0 = move _6(move _7) -> [return: bb1, unwind: bb3]
-- bb1: StorageDead(_7); StorageDead(_6); StorageDead(_4); drop(_2) -> [return: bb2, unwind: bb4]
-- bb2: StorageDead(_2); return
-- bb3: drop(_2) -> [return: bb4, unwind terminate(cleanup)]
-- bb4: resume
def cfFx_unwind_through_closure : CapturedMir :=
  {
    defPath := "closure_matrix::unwind_through_closure",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "closure_matrix::Guard" List.nil), layoutIdx := 1 }, debugName := (Option.some "_g") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::unwind_through_closure::{closure#0}" List.nil), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:84:9: 84:11" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:84:20: 84:21" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:84:20: 84:21" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "closure_matrix::Guard" 0 Option.none) (List.cons (Operand.move { local_ := 3, projection := List.nil }) List.nil))), span := "src/lib.rs:84:14: 84:22" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:84:21: 84:22" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:85:9: 85:10" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:85:29: 85:80" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::unwind_through_closure::{closure#0}") List.nil)), span := "src/lib.rs:85:29: 85:80" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 5, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 })), span := "src/lib.rs:85:29: 85:80" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:85:36: 85:37" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:86:5: 86:6" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := List.nil }))), span := "src/lib.rs:86:5: 86:6" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:86:7: 86:8" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:86:7: 86:8" } List.nil)))))))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 6, projection := List.nil }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) (UnwindAction.cleanup 3)), span := "src/lib.rs:86:5: 86:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:86:8: 86:9" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:86:8: 86:9" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:87:1: 87:2" } List.nil))), terminator := { kind := (TerminatorKind.drop { local_ := 2, projection := List.nil } 2 (UnwindAction.cleanup 4)), span := "src/lib.rs:87:1: 87:2" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:87:1: 87:2" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:87:2: 87:2" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.drop { local_ := 2, projection := List.nil } 4 UnwindAction.terminate), span := "src/lib.rs:87:1: 87:2" }, isCleanup := true } (List.cons { statements := List.nil, terminator := { kind := TerminatorKind.unwindResume, span := "src/lib.rs:83:1: 87:2" }, isCleanup := true } List.nil))))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_unwind_through_closure_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.unwind_through_closure_closure_0`. -/
def cfFx_unwind_through_closure_closure_0_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := VariantsShape.empty, isUninhabited := true } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 5 List.nil) } (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 6 (List.cons 6 List.nil)) } (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))))))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::unwind_through_closure::{closure#0}"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.unwind_through_closure_closure_0.body`). -/
-- bb0: StorageLive(_3); StorageLive(_4); _4 = copy _2; _3 = Eq(move _4, const 0_u32); switchInt(move _3) -> [0: bb3, otherwise: bb1]
-- bb1: StorageDead(_4); StorageLive(_6); StorageLive(_7); _7 = core::fmt::Arguments::<'_>::from_str(const "zero") -> [return: bb2, unwind continue]
-- bb2: _6 = core::panicking::panic_fmt(move _7) -> unwind continue
-- bb3: StorageDead(_4); _0 = copy _2; StorageDead(_3); return
def cfFx_unwind_through_closure_closure_0 : CapturedMir :=
  {
    defPath := "closure_matrix::unwind_through_closure::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::unwind_through_closure::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.never, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := RigidTy.never, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "core::fmt::Arguments" List.nil), layoutIdx := 7 }, debugName := Option.none } List.nil)))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:85:41: 85:50" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:85:41: 85:42" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:85:41: 85:42" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.eq (Operand.move { local_ := 4, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:85:41: 85:50" } List.nil)))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 3, projection := List.nil }) { branches := (List.cons (0, 3) List.nil), otherwise := 1 }), span := "src/lib.rs:85:41: 85:50" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:85:49: 85:50" } (List.cons { kind := (StatementKind.storageLive 6), span := "/rustc/library/core/src/panic.rs:62:9: 62:73" } (List.cons { kind := (StatementKind.storageLive 7), span := "/rustc/library/core/src/panic.rs:62:38: 62:72" } List.nil))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::fmt::Arguments::<'a>::from_str" List.nil), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.constant { ty := { kind := (RigidTy.ref Mutability.not RigidTy.str), layoutIdx := 8 }, val := (ConstValue.slice (ConstScalar.ptr { allocId := 1, offsetBytes := 0 } 8) 4) }) List.nil) { local_ := 7, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "/rustc/library/core/src/panic.rs:62:38: 62:72" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::panicking::panic_fmt" List.nil), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) List.nil) { local_ := 6, projection := List.nil } Option.none UnwindAction.continue_), span := "/rustc/library/core/src/panic.rs:62:9: 62:73" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:85:49: 85:50" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:85:77: 85:78" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:85:79: 85:80" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:85:80: 85:80" }, isCleanup := false } List.nil)))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_unwind_through_closure_closure_0_layouts,
    allocations := (List.cons { allocId := 1, bytes := (List.cons (Option.some (UInt8.ofNat 122)) (List.cons (Option.some (UInt8.ofNat 101)) (List.cons (Option.some (UInt8.ofNat 114)) (List.cons (Option.some (UInt8.ofNat 111)) List.nil)))), relocations := List.nil, align := { bytes := 1 }, mutability := Mutability.not } List.nil)
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.widen_and_identity`. -/
def cfFx_widen_and_identity_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } List.nil))))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::widen_and_identity"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.widen_and_identity.body`). -/
-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:55:29: 55:37}; _2 = move _3 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = copy _2; _4 = move _5 as unsafe fn(u32) -> u32 (PointerCoercion(UnsafeFnPointer, Implicit)); StorageDead(_5); StorageLive(_6); StorageLive(_7); StorageLive(_8); StorageLive(_9); _9 = copy _2; _8 = move _9 as *const () (FnPtrToPtr); StorageDead(_9); StorageLive(_10); StorageLive(_11); _11 = copy _4; _10 = move _11 as *const () (FnPtrToPtr); StorageDead(_11); _7 = Eq(move _8, move _10); switchInt(move _7) -> [0: bb2, otherwise: bb1]
-- bb1: StorageDead(_10); StorageDead(_8); _6 = const 1_u32; goto -> bb3
-- bb2: StorageDead(_10); StorageDead(_8); _6 = const 0_u32; goto -> bb3
-- bb3: StorageDead(_7); StorageLive(_12); StorageLive(_13); _13 = copy _4; StorageLive(_14); _14 = copy _1; _12 = move _13(move _14) -> [return: bb4, unwind continue]
-- bb4: StorageDead(_14); StorageDead(_13); StorageLive(_15); StorageLive(_16); _16 = copy _6; _17 = Lt(const 8_u32, const 32_u32); assert(move _17, "attempt to shift left by `{}`, which would overflow", const 8_u32) -> [success: bb5, unwind continue]
-- bb5: _15 = Shl(move _16, const 8_u32); StorageDead(_16); _0 = BitXor(move _12, move _15); StorageDead(_15); StorageDead(_12); StorageDead(_6); StorageDead(_4); StorageDead(_2); return
def cfFx_widen_and_identity : CapturedMir :=
  {
    defPath := "closure_matrix::widen_and_identity",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::widen_and_identity::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "g") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "same") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } List.nil)))))))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 17), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:55:9: 55:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:55:29: 55:59" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::widen_and_identity::{closure#0}") List.nil)), span := "src/lib.rs:55:29: 55:59" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:55:29: 55:59" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:55:36: 55:37" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:56:9: 56:10" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:56:36: 56:37" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:56:36: 56:37" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "UnsafeFnPointer") (Operand.move { local_ := 5, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:56:36: 56:37" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:56:36: 56:37" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:57:9: 57:13" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:57:24: 57:60" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:57:24: 57:40" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:57:25: 57:26" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:57:25: 57:26" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.cast CastKind.fnPtrToPtr (Operand.move { local_ := 9, projection := List.nil }) { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 4 })), span := "src/lib.rs:57:24: 57:40" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:57:39: 57:40" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:57:44: 57:60" } (List.cons { kind := (StatementKind.storageLive 11), span := "src/lib.rs:57:45: 57:46" } (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := List.nil }))), span := "src/lib.rs:57:45: 57:46" } (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.cast CastKind.fnPtrToPtr (Operand.move { local_ := 11, projection := List.nil }) { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 4 })), span := "src/lib.rs:57:44: 57:60" } (List.cons { kind := (StatementKind.storageDead 11), span := "src/lib.rs:57:59: 57:60" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.binaryOp BinOp.eq (Operand.move { local_ := 8, projection := List.nil }) (Operand.move { local_ := 10, projection := List.nil }))), span := "src/lib.rs:57:24: 57:60" } List.nil)))))))))))))))))))))))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 7, projection := List.nil }) { branches := (List.cons (0, 2) List.nil), otherwise := 1 }), span := "src/lib.rs:57:24: 57:60" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:57:59: 57:60" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:57:59: 57:60" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:57:63: 57:67" } List.nil))), terminator := { kind := (TerminatorKind.goto 3), span := "src/lib.rs:57:21: 57:83" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:57:59: 57:60" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:57:59: 57:60" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:57:77: 57:81" } List.nil))), terminator := { kind := (TerminatorKind.goto 3), span := "src/lib.rs:57:21: 57:83" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:57:82: 57:83" } (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:58:5: 58:22" } (List.cons { kind := (StatementKind.storageLive 13), span := "src/lib.rs:58:15: 58:16" } (List.cons { kind := (StatementKind.assign { local_ := 13, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := List.nil }))), span := "src/lib.rs:58:15: 58:16" } (List.cons { kind := (StatementKind.storageLive 14), span := "src/lib.rs:58:17: 58:18" } (List.cons { kind := (StatementKind.assign { local_ := 14, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:58:17: 58:18" } List.nil)))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 13, projection := List.nil }) (List.cons (Operand.move { local_ := 14, projection := List.nil }) List.nil) { local_ := 12, projection := List.nil } (Option.some 4) UnwindAction.continue_), span := "src/lib.rs:58:15: 58:19" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 14), span := "src/lib.rs:58:18: 58:19" } (List.cons { kind := (StatementKind.storageDead 13), span := "src/lib.rs:58:18: 58:19" } (List.cons { kind := (StatementKind.storageLive 15), span := "src/lib.rs:58:25: 58:39" } (List.cons { kind := (StatementKind.storageLive 16), span := "src/lib.rs:58:26: 58:30" } (List.cons { kind := (StatementKind.assign { local_ := 16, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 6, projection := List.nil }))), span := "src/lib.rs:58:26: 58:30" } (List.cons { kind := (StatementKind.assign { local_ := 17, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 8, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:58:25: 58:39" } List.nil)))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 17, projection := List.nil }) true 5 UnwindAction.continue_), span := "src/lib.rs:58:25: 58:39" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 15, projection := List.nil } (Rvalue.binaryOp BinOp.shl (Operand.move { local_ := 16, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 8, sizeBytes := 4 })) }))), span := "src/lib.rs:58:25: 58:39" } (List.cons { kind := (StatementKind.storageDead 16), span := "src/lib.rs:58:38: 58:39" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 12, projection := List.nil }) (Operand.move { local_ := 15, projection := List.nil }))), span := "src/lib.rs:58:5: 58:39" } (List.cons { kind := (StatementKind.storageDead 15), span := "src/lib.rs:58:38: 58:39" } (List.cons { kind := (StatementKind.storageDead 12), span := "src/lib.rs:58:38: 58:39" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:59:1: 59:2" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:59:1: 59:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:59:1: 59:2" } List.nil)))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:59:2: 59:2" }, isCleanup := false } List.nil)))))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_widen_and_identity_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.widen_and_identity_closure_0`. -/
def cfFx_widen_and_identity_closure_0_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::widen_and_identity::{closure#0}"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.widen_and_identity_closure_0.body`). -/
-- bb0: StorageLive(_3); _3 = copy _2; _0 = Add(move _3, const 1_u32); StorageDead(_3); return
def cfFx_widen_and_identity_closure_0 : CapturedMir :=
  {
    defPath := "closure_matrix::widen_and_identity::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::widen_and_identity::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:55:51: 55:52" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:55:51: 55:52" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:55:38: 55:59" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:55:58: 55:59" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:55:59: 55:59" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_widen_and_identity_closure_0_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.zero_arg`. -/
def cfFx_zero_arg_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::zero_arg"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.zero_arg.body`). -/
-- bb0: StorageLive(_1); StorageLive(_2); _2 = {closure@src/lib.rs:40:26: 40:28}; _1 = move _2 as fn() -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_2); StorageLive(_3); _3 = copy _1; _0 = move _3() -> [return: bb1, unwind continue]
-- bb1: StorageDead(_3); StorageDead(_1); return
def cfFx_zero_arg : CapturedMir :=
  {
    defPath := "closure_matrix::zero_arg",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 0,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr List.nil (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::zero_arg::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr List.nil (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 1), span := "src/lib.rs:40:9: 40:10" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:40:26: 40:33" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::zero_arg::{closure#0}") List.nil)), span := "src/lib.rs:40:26: 40:33" } (List.cons { kind := (StatementKind.assign { local_ := 1, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 2, projection := List.nil }) { kind := (RigidTy.fnPtr List.nil (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:40:26: 40:33" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:40:27: 40:28" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:41:5: 41:6" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:41:5: 41:6" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 3, projection := List.nil }) List.nil { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:41:5: 41:8" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:41:7: 41:8" } (List.cons { kind := (StatementKind.storageDead 1), span := "src/lib.rs:42:1: 42:2" } List.nil)), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:42:2: 42:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_zero_arg_layouts,
    allocations := List.nil
  }

/-- Verbatim `rustc-capture` layout table of `Mir.ClosureMatrix.zero_arg_closure_0`. -/
def cfFx_zero_arg_closure_0_layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }
/-- Verbatim `rustc-capture` output (`defPath := "closure_matrix::zero_arg::{closure#0}"`), copied from
`tests/mir/ClosureFnPtrTests.lean` (`Mir.ClosureMatrix.zero_arg_closure_0.body`). -/
-- bb0: _0 = const 7_u32; return
def cfFx_zero_arg_closure_0 : CapturedMir :=
  {
    defPath := "closure_matrix::zero_arg::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::zero_arg::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } List.nil)),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 7, sizeBytes := 4 })) }))), span := "src/lib.rs:40:29: 40:33" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:40:33: 40:33" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := cfFx_zero_arg_closure_0_layouts,
    allocations := List.nil
  }

end Fixtures

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence
open LeanMiriSpec.UnwindSetDiscrAndFnPtrLM

/-! ## §2. Program table, closure kinds, and the `ClosureOnceShim` -/

abbrev CfHooks := Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine Unit (Miri.Interpreter.RuntimePlace AnnealProv)
abbrev CfM := EStateM Miri.Interpreter.StepError AnnealStepState

structure CfItem where
  typeArgs : List RigidTy := []
  body : CapturedMir

abbrev CfProg := List CfItem

def cfItem? (prog : CfProg) (n : Nat) : Option CfItem := prog[n]?

def cfFindItemAux (path : DefPath) (targs : List RigidTy) : CfProg → Nat → Option Nat
  | [], _ => none
  | it :: rest, i =>
    if stringEq it.body.defPath path && rigidTyListEq it.typeArgs targs then some i
    else cfFindItemAux path targs rest (i + 1)

def cfFindItem? (prog : CfProg) (path : DefPath) (targs : List RigidTy) : Option Nat :=
  cfFindItemAux path targs prog 0

inductive CfClosureKind where
  | fn | fnMut | fnOnce
  deriving DecidableEq, Repr

def cfClosureKindOfEnvTy? (ownPath : DefPath) : RigidTy → Option (CfClosureKind × Nat)
  | .ref .not (.closure p upvars) => if stringEq p ownPath then some (.fn, length upvars) else none
  | .ref .mut (.closure p upvars) => if stringEq p ownPath then some (.fnMut, length upvars) else none
  | .closure p upvars => if stringEq p ownPath then some (.fnOnce, length upvars) else none
  | _ => none

def cfClosureKind? (c : CapturedMir) : Option (CfClosureKind × Nat) :=
  match c.argCount, c.localDecls with
  | _ + 1, _ :: env :: _ => cfClosureKindOfEnvTy? c.defPath env.ty.kind
  | _, _ => none

def cfZstLayout : TypeLayout :=
  { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }

def cfPtrLayout : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 8 },
    backendRepr := .scalar (.initialized (.pointer 0) { start := 1, end_ := 18446744073709551615 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def cfAlignUp (n a : Nat) : Nat := ((n + a - 1) / a) * a

/-- Layout of the argument tuple `(T1, .., TN)` of the shim for `N ≤ 2` scalar parameters. -/
def cfTupleLayout? (layouts : LayoutTable) (params : List LocalDecl) : Option TypeLayout :=
  match params with
  | [] => some cfZstLayout
  | [p] =>
    match layouts.lookup p.ty.layoutIdx with
    | some l =>
      match l.backendRepr with
      | .scalar _ => some { l with fields := .arbitrary [{ bytes := 0 }] [0], fieldLayouts := [p.ty.layoutIdx] }
      | _ => none
    | none => none
  | [p, q] =>
    match layouts.lookup p.ty.layoutIdx, layouts.lookup q.ty.layoutIdx with
    | some l1, some l2 =>
      match l1.backendRepr, l2.backendRepr with
      | .scalar s1, .scalar s2 =>
        let off2 := cfAlignUp l1.size.bytes l2.align.bytes
        let al := Nat.max l1.align.bytes l2.align.bytes
        some { size := { bytes := cfAlignUp (off2 + l2.size.bytes) al }, align := { bytes := al },
               backendRepr := .scalarPair s1 s2,
               fields := .arbitrary [{ bytes := 0 }, { bytes := off2 }] [0, 1],
               variants := .single 0, isUninhabited := false,
               fieldLayouts := [p.ty.layoutIdx, q.ty.layoutIdx] }
      | _, _ => none
    | _, _ => none
  | _ => none

def cfCallMutPath : DefPath := "core::ops::FnMut::call_mut"
def cfCallPath : DefPath := "core::ops::Fn::call"
def cfCallOncePath : DefPath := "core::ops::FnOnce::call_once"

def cfShimStmt (k : StatementKind) : MirAst.Statement := { kind := k, span := "<closure-once-shim>" }
def cfShimTerm (k : TerminatorKind) : MirAst.Terminator := { kind := k, span := "<closure-once-shim>" }

/-- The `ClosureOnceShim` MIR for the non-`FnOnce` closure body `c`. -/
def cfShimBody (c : CapturedMir) : Option CapturedMir :=
  match c.localDecls with
  | ret :: _env :: rest =>
    let params := rest.take (c.argCount - 1)
    match cfTupleLayout? c.layouts params, c.fnAbi.args with
    | some tupleLayout, _ :: userAbis =>
      let k0 := length c.layouts.entries
      let closTy : Ty := { kind := .closure c.defPath [], layoutIdx := k0 }
      let tupTy : Ty := { kind := .tuple (params.map fun p => p.ty.kind), layoutIdx := k0 + 1 }
      let refTy : Ty := { kind := .ref .mut (.closure c.defPath []), layoutIdx := k0 + 2 }
      let mk (ty : Ty) : LocalDecl := { mutability := .mut, ty := ty, debugName := none }
      some
        { defPath := c.defPath ++ "::{closure_once_shim}"
          phase := c.phase
          role := c.role
          argCount := 2
          localDecls := [ret, mk closTy, mk tupTy, mk refTy]
          basicBlocks :=
            [ { statements := [cfShimStmt (.storageLive 3), cfShimStmt (.assign ⟨3, []⟩ (.ref (.mut false) ⟨1, []⟩))]
                terminator := cfShimTerm (.call
                  (.constant { ty := { kind := .fnDef cfCallMutPath [closTy.kind, tupTy.kind], layoutIdx := 0 }, val := .zeroSized })
                  [.move ⟨3, []⟩, .move ⟨2, []⟩] ⟨0, []⟩ (some 1) (.cleanup 3))
                isCleanup := false },
              { statements := [], terminator := cfShimTerm (.drop ⟨1, []⟩ 2 .continue_), isCleanup := false },
              { statements := [], terminator := cfShimTerm .return_, isCleanup := false },
              { statements := [], terminator := cfShimTerm (.drop ⟨1, []⟩ 4 .terminate), isCleanup := true },
              { statements := [], terminator := cfShimTerm .unwindResume, isCleanup := true } ]
          fnAbi := { args := { layout := cfZstLayout, mode := .ignore } :: userAbis, ret := c.fnAbi.ret,
                     conv := .rust, canUnwind := true }
          layouts := { c.layouts with entries := c.layouts.entries ++ [cfZstLayout, tupleLayout, cfPtrLayout] }
          allocations := [] }
    | _, _ => none
  | _ => none

/-! ## §3. Function instances and function allocations -/

def cfCallOnceDefId : Miri.MIR.DefId := 4000000
def cfCallMutDefId : Miri.MIR.DefId := 4000001
def cfCallDefId : Miri.MIR.DefId := 4000002
def cfClosureArgBase : Miri.MIR.TyId := 5000000

def cfItemInstance (n : Nat) : Miri.Interpreter.CallInstance := ⟨.Item n, #[]⟩
def cfShimInstance (n : Nat) : Miri.Interpreter.CallInstance := ⟨.Shim (.ClosureOnce cfCallOnceDefId n false), #[]⟩

def cfFnAllocNat (inst : Miri.Interpreter.CallInstance) : Option Nat :=
  match inst.kind with
  | .Item n => some (65536 + 2 * n)
  | .Shim (.ClosureOnce _ n _) => some (65536 + 2 * n + 1)
  | _ => none

def cfInstanceOfAllocNat (a : Nat) : Option Miri.Interpreter.CallInstance :=
  if a < 65536 then none
  else if (a - 65536) % 2 == 0 then some (cfItemInstance ((a - 65536) / 2))
  else some (cfShimInstance ((a - 65536) / 2))

def cfBodyOfInstance (prog : CfProg) (inst : Miri.Interpreter.CallInstance) : Option CapturedMir :=
  match inst.kind with
  | .Item n => (cfItem? prog n).map (·.body)
  | .Shim (.ClosureOnce _ n _) => (cfItem? prog n).bind fun it => cfShimBody it.body
  | _ => none

def cfMirBodyOfInstance (prog : CfProg) (inst : Miri.Interpreter.CallInstance) : Option Miri.MIR.Body :=
  match inst.kind with
  | .Item n => (cfItem? prog n).map fun it => translateBody it.body
  | .Shim (.ClosureOnce _ n _) =>
    (cfItem? prog n).bind fun it => (cfShimBody it.body).map fun s => { translateBody s with spreadArgument := some 2 }
  | _ => none

def cfIsShimInstance (inst : Miri.Interpreter.CallInstance) : Bool :=
  match inst.kind with
  | .Shim (.ClosureOnce ..) => true
  | _ => false

def cfActive (prog : CfProg) : CfM CapturedMir := fun st =>
  match st.stack.currentFrame? with
  | none => .error (.stack .emptyStack) st
  | some f =>
    match cfBodyOfInstance prog f.functionInstance with
    | some b => .ok b st
    | none => .error (.invalidProgram "frame instance has no captured body") st

/-- The captured body and terminator at the current location of the top frame. -/
def cfActiveTerminator (prog : CfProg) : CfM (CapturedMir × TerminatorKind) := fun st =>
  match st.stack.currentFrame? with
  | none => .error (.stack .emptyStack) st
  | some f =>
    match cfBodyOfInstance prog f.functionInstance, f.location with
    | some b, .mir loc =>
      match get? b.basicBlocks loc.block with
      | some bb => .ok (b, bb.terminator.kind) st
      | none => .error (.invalidBlock loc.block) st
    | some _, .unwinding _ => .error .expectedMirLocation st
    | none, _ => .error (.invalidProgram "frame instance has no captured body") st

def cfActiveCall (prog : CfProg) : CfM (CapturedMir × Operand) := do
  let (b, term) ← cfActiveTerminator prog
  match term with
  | .call func _ _ _ _ => pure (b, func)
  | .tailCall func _ => pure (b, func)
  | _ => throw (.invalidProgram "call hook outside a call terminator")

/-! ## §4. Function ABIs -/

structure CfArgAbi where
  rigid : RigidTy
  abi : Miri.ABI.ArgAbi Miri.MIR.TyId

structure CfFnAbi where
  args : Array CfArgAbi
  ret : CfArgAbi
  conv : Miri.ABI.CanonAbi
  canUnwind : Bool

def cfPassModeOfTrusted : AbiPassMode → Miri.ABI.PassMode
  | .ignore => .Ignore
  | .direct => .Direct Miri.ABI.ArgAttributes.new
  | .pair => .Pair Miri.ABI.ArgAttributes.new Miri.ABI.ArgAttributes.new
  | .indirect => .Indirect Miri.ABI.ArgAttributes.new none .Pointer

def cfPassModeOfLayout (l : Miri.ABI.LayoutData) : Option Miri.ABI.PassMode :=
  if l.isSized && l.size.bytes == 0 then some .Ignore
  else match l.backendRepr with
    | .Scalar _ => some (.Direct Miri.ABI.ArgAttributes.new)
    | .ScalarPair .. => some (.Pair Miri.ABI.ArgAttributes.new Miri.ABI.ArgAttributes.new)
    | _ => none

def cfCanonAbi : CallConv → Miri.ABI.CanonAbi
  | .rust => .Rust
  | .c => .C
  | .rustIntrinsic => .Rust
  | .other _ => .Custom

def cfArgAbiOfDecl (layouts : LayoutTable) (d : LocalDecl) (mode : AbiPassMode) : CfArgAbi :=
  ⟨d.ty.kind, ⟨translateTy d.ty layouts, cfPassModeOfTrusted mode⟩⟩

def cfZipArgAbis (layouts : LayoutTable) : List LocalDecl → List ArgAbi → Option (List CfArgAbi)
  | [], [] => some []
  | d :: ds, a :: as => (cfZipArgAbis layouts ds as).map (cfArgAbiOfDecl layouts d a.mode :: ·)
  | _, _ => none

/-- `fn_abi_of_instance` of an item body: the captured `FnAbi` with the declared local types. -/
def cfFnAbiOfBody (c : CapturedMir) : Option CfFnAbi :=
  match c.localDecls with
  | ret :: rest =>
    match cfZipArgAbis c.layouts (rest.take c.argCount) c.fnAbi.args with
    | some args =>
      some { args := args.toArray, ret := cfArgAbiOfDecl c.layouts ret c.fnAbi.ret.mode,
             conv := cfCanonAbi c.fnAbi.conv, canUnwind := c.fnAbi.canUnwind }
    | none => none
  | [] => none

/-- `fn_abi_of_instance` of the `ClosureOnceShim` of closure body `c`. -/
def cfFnAbiOfShim (c : CapturedMir) : Option CfFnAbi :=
  match cfShimBody c, cfFnAbiOfBody c with
  | some s, some abi =>
    match s.localDecls with
    | _ :: self :: _ =>
      some { abi with args := #[cfArgAbiOfDecl s.layouts self .ignore] ++ abi.args.extract 1 abi.args.size }
    | _ => none
  | _, _ => none

def cfFnAbiOfInstance (prog : CfProg) (inst : Miri.Interpreter.CallInstance) : Option CfFnAbi :=
  match inst.kind with
  | .Item n => (cfItem? prog n).bind fun it => cfFnAbiOfBody it.body
  | .Shim (.ClosureOnce _ n _) => (cfItem? prog n).bind fun it => cfFnAbiOfShim it.body
  | _ => none

/-- A `Ty` (with layout index into `b.layouts`) for the type `k` named in a signature. -/
def cfTyOfRigid (b : CapturedMir) (k : RigidTy) : Option Ty :=
  match encodeScalarRigidTy k with
  | some _ => some { kind := k, layoutIdx := 0 }
  | none => (b.localDecls.find? fun d => rigidTyEq d.ty.kind k).map (·.ty)

def cfArgAbiOfRigid (b : CapturedMir) (k : RigidTy) : Option CfArgAbi :=
  match cfTyOfRigid b k with
  | some ty =>
    let lay := translateTy ty b.layouts
    (cfPassModeOfLayout lay.layout).map fun mode => ⟨k, ⟨lay, mode⟩⟩
  | none => none

def cfArgAbisOfRigids (b : CapturedMir) : List RigidTy → Option (List CfArgAbi)
  | [] => some []
  | k :: ks =>
    match cfArgAbiOfRigid b k, cfArgAbisOfRigids b ks with
    | some a, some as => some (a :: as)
    | _, _ => none

/-- `fn_abi_of_fn_ptr` of the function-pointer type `fn(ins) -> out` with ABI `abi`. -/
def cfFnAbiOfFnPtrTy (b : CapturedMir) (ins : List RigidTy) (out : RigidTy) (abi : CallConv) : Option CfFnAbi :=
  match cfArgAbisOfRigids b ins, cfArgAbiOfRigid b out with
  | some args, some ret =>
    some { args := args.toArray, ret := ret, conv := cfCanonAbi abi,
           canUnwind := match abi with | .rust => true | _ => false }
  | _, _ => none

/-- `check_argument_compat`: layout compatibility, then the `eq_abi` assertion. -/
def cfCheckArgumentCompat (caller callee : CfArgAbi) : CfM Bool :=
  if annealRigidTyLayoutCompat caller.rigid callee.rigid then
    if caller.abi.eqAbi callee.abi then pure true
    else throw (.invalidProgram "check_argument_compat: concrete ArgAbi.eq_abi assertion failed")
  else pure false

/-! ## §5. Closure-aware `CastHooks` -/

def cfFunctionPointer (inst : Miri.Interpreter.CallInstance) :
    CfM (Miri.Memory.Pointer (Option AnnealProv)) := fun st =>
  match cfFnAllocNat inst with
  | none => .error (.unsupported "function pointer to this instance kind") st
  | some a =>
    if h : UInt64.ofNat a ≠ 0 then
      let id : Miri.Memory.AllocId := ⟨UInt64.ofNat a, h⟩
      match st.machine.lookupBaseAddr id with
      | some base => .ok ⟨Miri.ABI.Size.ofBytes base, some (.concrete id Miri.Memory.BorTag.one)⟩ st
      | none =>
        let base := annealStackBaseAddr id
        let addresses' := { st.machine.addresses with baseAddr := #[⟨id, base⟩] ++ st.machine.addresses.baseAddr }
        .ok ⟨Miri.ABI.Size.ofBytes base, some (.concrete id Miri.Memory.BorTag.one)⟩
          { st with machine := { st.machine with addresses := addresses' } }
    else .error (.resourceExhaustion "function allocation ID wrap") st

/-- Resolve a function pointer value to the instance of its function allocation (`get_ptr_fn`). -/
def cfGetPtrFn (prog : CfProg) (ptr : Miri.Memory.Pointer (Option AnnealProv)) :
    CfM Miri.Interpreter.CallInstance := fun st =>
  match ptr.intoPointerOrAddr with
  | .error _ => .error (.undefinedBehavior "DanglingIntPointer") st
  | .ok _ =>
    match annealResolvePtr st.machine ptr 0 with
    | .error _ => .error (.undefinedBehavior "DanglingIntPointer") st
    | .ok resolved =>
      if resolved.offset != Miri.ABI.Size.ZERO then .error (.undefinedBehavior "InvalidFunctionPointer") st
      else
        match cfInstanceOfAllocNat resolved.allocId.value.toNat with
        | some inst =>
          match cfBodyOfInstance prog inst with
          | some _ => .ok inst st
          | none => .error (.undefinedBehavior "InvalidFunctionPointer") st
        | none => .error (.undefinedBehavior "InvalidFunctionPointer") st

/-- `Instance::resolve_closure(def_id, args, ClosureKind::FnOnce)`. -/
def cfResolveClosure (prog : CfProg) (n : Nat) (requested : CfClosureKind) :
    Except Miri.Interpreter.StepError Miri.Interpreter.CallInstance :=
  match cfItem? prog n with
  | none => .error (.invalidProgram "resolve_closure of an unknown definition")
  | some it =>
    if it.body.typeParamCount != 0 && it.typeArgs.isEmpty then
      .error (.unsupported "closure body with unresolved parent generic arguments")
    else
      match cfClosureKind? it.body, requested with
      | some (.fnOnce, _), .fnOnce => .ok (cfItemInstance n)
      | some (.fn, _), .fnOnce | some (.fnMut, _), .fnOnce => .ok (cfShimInstance n)
      | some (.fn, _), .fn | some (.fn, _), .fnMut | some (.fnMut, _), .fnMut => .ok (cfItemInstance n)
      | some _, _ => .error (.invalidProgram "closure does not implement the requested Fn trait")
      | none, _ => .error (.invalidProgram "resolve_closure of a non-closure body")

/-- The source operand type of the pointer-coercion cast at the current location. -/
def cfActiveCoercionSource? (body : CapturedMir) (st : AnnealStepState) : Option (String × Ty) :=
  match st.stack.currentFrame? with
  | some frame =>
    match frame.location with
    | .mir loc =>
      match get? body.basicBlocks loc.block with
      | some bb =>
        match get? bb.statements loc.statementIndex with
        | some { kind := .assign _ (.cast (.pointerCoercion ck) op _), .. } =>
          (operandTy body.localDecls body.layouts op).map fun ty => (ck, ty)
        | _ => none
      | none => none
    | .unwinding _ => none
  | none => none

def cfCastTypeInfo (prog : CfProg) (body : CapturedMir) (tyId : Miri.MIR.TyId) :
    CfM Miri.Interpreter.CastTypeInfo := do
  let st ← get
  let fallback : CfM Miri.Interpreter.CastTypeInfo :=
    match castTypeInfoOverlay body st tyId with
    | .ok info => pure info
    | .error err => throw err
  match cfActiveCoercionSource? body st with
  | some (_, srcTy) =>
    if encodeTyId srcTy == tyId then
      match srcTy.kind with
      | .closure path upvars =>
        match cfFindItem? prog path [] with
        | some n => pure (.closure n #[] (length upvars))
        | none => throw (.unsupported "ClosureFnPointer of a closure whose body is not linked")
      | .fnDef path targs =>
        match cfFindItem? prog path targs with
        | some n => pure (.fnDefinition n #[])
        | none => throw (.unsupported "ReifyFnPointer of a function whose body is not linked")
      | _ => fallback
    else fallback
  | none => fallback

def cfCheckFnPointer (prog : CfProg) (ptr : Miri.Memory.Pointer (Option AnnealProv)) : CfM Unit := do
  let _ ← cfGetPtrFn prog ptr
  pure ()

def cfCastHooks (prog : CfProg) (body : CapturedMir) :
    Miri.Interpreter.CastHooks AnnealProv AnnealStepState Unit (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealCastHooksUnwindFnPtrClosure body [] with
    typeInfo := fun _ tyId => cfCastTypeInfo prog body tyId
    checkFunctionPointer := fun _ ptr => cfCheckFnPointer prog ptr
    resolveFunction := fun _ defId _ => pure (some (cfItemInstance defId))
    resolveClosureFnOnce := fun _ defId _ =>
      match cfResolveClosure prog defId .fnOnce with
      | .ok inst => pure inst
      | .error err => throw err
    functionPointer := fun _ inst => cfFunctionPointer inst }

def cfIsFnPtrCastKind : Miri.MIR.CastKind → Bool
  | .PointerCoercion (.ClosureFnPointer _) _ | .PointerCoercion (.ReifyFnPointer _) _
  | .PointerCoercion .UnsafeFnPointer _ | .FnPtrToPtr => true
  | _ => false

def cfRvalueHooks (prog : CfProg) (body : CapturedMir) :
    Miri.Interpreter.RvalueHooks AnnealProv AnnealStepState Unit (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealRvalueHooksUnwindFnPtrClosure body []
  { base with
    cast := fun c src kind ty dest =>
      if cfIsFnPtrCastKind kind then Miri.Interpreter.Cast.cast (cfCastHooks prog body) c 16 src kind ty dest
      else base.cast c src kind ty dest }

def cfIsFnPtrCastRvalue : Miri.MIR.Rvalue → Bool
  | .Cast kind _ _ => cfIsFnPtrCastKind kind
  | _ => false

/-! ## §6. Closure-aware `CallHooks` for the vendored call pipeline -/

def cfLiftStep {A : Type} (r : AnnealStepState → Miri.Interpreter.StepResult AnnealStepState A) : CfM A := fun st =>
  match r st with
  | (st', .ok a) => .ok a st'
  | (st', .error e) => .error e st'

/-- `Operand::offset` on a local read at byte offset `off` with field layout `layout`. -/
def cfLocalOperandAtOffset (operand : Miri.Interpreter.Operand AnnealProv) (off : Miri.ABI.Size)
    (layout : Miri.Interpreter.LocalLayout) : CfM (Miri.Interpreter.OpTy AnnealProv) :=
  match operand with
  | .indirect mp =>
    match mp.ptr.offset.add off with
    | .ok o => pure ⟨.indirect { mp with ptr := { mp.ptr with offset := o } }, layout⟩
    | .error _ => throw (.invalidProgram "projected local offset overflow")
  | .immediate .uninit => pure ⟨.immediate .uninit, layout⟩
  | .immediate (.scalar s) =>
    if off.bytes == 0 then pure ⟨.immediate (.scalar s), layout⟩
    else throw (.invalidProgram "projected read past a scalar local")
  | .immediate (.scalarPair a b) =>
    if off.bytes == 0 then pure ⟨.immediate (.scalar a), layout⟩ else pure ⟨.immediate (.scalar b), layout⟩

/-- `place_to_op` for saved destinations and in-place arguments in the top frame. -/
def cfStackPlaceToOp (prog : CfProg) (place : Miri.Interpreter.RuntimeStackPlace AnnealProv) :
    CfM (Miri.Interpreter.OpTy AnnealProv) := do
  let b ← cfActive prog
  match place with
  | .frameLocal _ localId none _ _ =>
    annealEvalOperandOverlay b.localDecls b.layouts (.Copy ⟨localId, #[]⟩) none
  | .memory mp => pure ⟨.indirect mp.mplace, mp.layout⟩
  | .frameLocal _ localId (some off) layout _ =>
    let st ← get
    match st.stack.currentFrame? with
    | none => throw (.stack .emptyStack)
    | some frame =>
      match frame.getLocalOperand localId with
      | .ok operand => cfLocalOperandAtOffset operand off layout
      | .error (.localExpectedLive _) => throw (.undefinedBehavior "read of dead local")
      | .error e => throw (.stack e)

/-- Resolution of the callee operand of the call terminator at the current location. -/
inductive CfCallee where
  | fnPtr (ins : List RigidTy) (out : RigidTy) (abi : CallConv)
  | item (n : Nat)
  | closureMethod (methodDefId : Miri.MIR.DefId) (n : Nat)

def cfClassifyCallee (prog : CfProg) : CfM (CapturedMir × Ty × CfCallee) := do
  let (b, func) ← cfActiveCall prog
  match operandTy b.localDecls b.layouts func with
  | none => throw (.invalidProgram "call operand without a type")
  | some ty =>
    match ty.kind with
    | .fnPtr ins out _ abi => pure (b, ty, .fnPtr ins out abi)
    | .fnDef path targs =>
      let method? : Option Miri.MIR.DefId :=
        if stringEq path cfCallMutPath then some cfCallMutDefId
        else if stringEq path cfCallPath then some cfCallDefId
        else if stringEq path cfCallOncePath then some cfCallOnceDefId
        else none
      match method?, targs with
      | some m, .closure cpath _ :: _ =>
        match cfFindItem? prog cpath [] with
        | some n => pure (b, ty, .closureMethod m n)
        | none => throw (.unsupported "unresolved external call")
      | _, _ =>
        match cfFindItem? prog path targs with
        | some n => pure (b, ty, .item n)
        | none => throw (.unsupported "unresolved external call")
    | _ => throw (.invalidProgram "invalid callee type")

def cfRunFrameStorage (prog : CfProg)
    (op : List LocalDecl → LayoutTable → Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit →
      AnnealMemory → Miri.Interpreter.LocalStorageResult AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMemory) :
    CfM Unit := do
  let b ← cfActive prog
  cfLiftStep (annealRunFrameStorage (op b.localDecls b.layouts))

def cfLiftStack {A : Type} (prog : CfProg)
    (op : Miri.Interpreter.StackLifecycleHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMemory →
      Miri.Interpreter.Stack AnnealProv Miri.Interpreter.LocalLayout Unit → AnnealMemory →
      Miri.Interpreter.StackRunResult AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMemory A)
    (decls : Option (List LocalDecl × LayoutTable)) : CfM A := do
  let (ld, ly) ← match decls with
    | some p => pure p
    | none => do let b ← cfActive prog; pure (b.localDecls, b.layouts)
  fun st =>
    let r := op (annealStackLifecycleHooksLM4_1 ld ly) st.stack st.machine.memory
    let st' : AnnealStepState := { stack := r.stack, machine := { st.machine with memory := r.state } }
    match r.outcome with
    | .ok a => .ok a st'
    | .error e => .error (.stack e) st'

def cfTupleFields (prog : CfProg) (ty : Miri.MIR.TyId) : CfM (Array Miri.MIR.TyId) := do
  let b ← cfActive prog
  match b.localDecls.find? fun d => encodeTyId d.ty == ty && (match d.ty.kind with | .tuple _ => true | _ => false) with
  | some d =>
    match d.ty.kind with
    | .tuple fields =>
      let rec go : List RigidTy → Option (List Miri.MIR.TyId)
        | [] => some []
        | k :: ks =>
          match cfTyOfRigid b k, go ks with
          | some t, some ts => some (encodeTyId t :: ts)
          | _, _ => none
      match go fields with
      | some ts => pure ts.toArray
      | none => throw (.unsupported "tuple field type without a layout")
    | _ => throw (.invalidProgram "tupleFields of a non-tuple type")
  | none => throw (.invalidProgram "tupleFields of a non-tuple type")

/-- `project_field` on a function argument (the untupled `rust-call` argument). -/
def cfProjectFnArg (prog : CfProg) (arg : Miri.Interpreter.FnArg AnnealProv) (idx : Nat) :
    CfM (Miri.Interpreter.FnArg AnnealProv) := do
  let b ← cfActive prog
  let fields ← cfTupleFields prog arg.layout.ty
  let some fieldTy := fields[idx]? | throw (.invalidProgram "missing tuple field")
  match arg with
  | .InPlace place =>
    match annealProjectFieldPlace b.layouts (some fieldTy) ⟨.memory place.mplace, place.layout⟩ idx with
    | .ok ⟨.memory mp, lay⟩ => pure (.InPlace ⟨mp, lay⟩)
    | .ok _ => throw (.invalidProgram "in-place argument projected to a local")
    | .error err => throw err
  | .Copy op =>
    let projected ← annealEvalProjection b.layouts op [.Field idx fieldTy]
    pure (.Copy projected)

def cfBodyIndex (inst : Miri.Interpreter.CallInstance) : Nat :=
  match cfFnAllocNat inst with
  | some a => a - 65536
  | none => 0

/-- The compiler capabilities consulted by the vendored non-capturing-closure test. -/
def cfCompiler (prog : CfProg) :
    Miri.Interpreter.ExecutionCallLeaves.Compiler AnnealStepState Unit Miri.ABI.ExternAbi where
  functionSignature := fun _ _ => annealUnsupportedLeaf "compiler.functionSignature"
  functionKind := fun _ => annealUnsupportedLeaf "compiler.functionKind"
  resolve := fun _ _ _ => annealUnsupportedLeaf "compiler.resolve"
  fnAbiOfFnPtr := fun _ _ _ => annealUnsupportedLeaf "compiler.fnAbiOfFnPtr"
  fnAbiOfInstance := fun _ _ _ => annealUnsupportedLeaf "compiler.fnAbiOfInstance"
  isRustCall := fun e => e == .RustCall
  rustAbi := .Rust
  checkArgumentCompat := fun _ _ _ => annealUnsupportedLeaf "compiler.checkArgumentCompat"
  targetFeatures :=
    { required := fun _ => pure #[], available := fun _ => pure true, isLikeWasm := pure false }
  tupleFields := fun ty => cfTupleFields prog ty
  isClosureLike := fun inst =>
    match inst.kind with
    | .Item n => pure ((cfItem? prog n).bind (fun it => cfClosureKind? it.body)).isSome
    | _ => pure false
  closureUpvarCount := fun ty => do
    let b ← cfActive prog
    match b.localDecls with
    | _ :: self :: _ =>
      if encodeTyId self.ty == ty then
        match self.ty.kind with
        | .closure _ upvars => pure (some (length upvars))
        | _ => pure none
      else pure none
    | _ => pure none
  llvmLinkName := fun _ => annealUnsupportedLeaf "compiler.llvmLinkName"

def cfVendoredFnAbi (abi : CfFnAbi) : Miri.ABI.FnAbi Miri.MIR.TyId :=
  { args := abi.args.map (·.abi), ret := abi.ret.abi, cVariadic := false,
    fixedCount := UInt32.ofNat abi.args.size, conv := abi.conv, canUnwind := abi.canUnwind }

def cfCallHooks (prog : CfProg) :
    Miri.Interpreter.CallHooks AnnealProv AnnealStepState Unit Unit Unit Miri.ABI.ExternAbi CfFnAbi CfArgAbi where
  debugAssertions := false
  getFrame := fun st =>
    match st.stack.currentFrame? with
    | some frame => .ok frame st
    | none => .error (.stack .emptyStack) st
  setFrame := fun frame st =>
    let idx := st.stack.frames.size - 1
    if h : idx < st.stack.frames.size then
      .ok () { st with stack := { frames := st.stack.frames.set idx frame h } }
    else .error (.stack .emptyStack) st
  frameIndex := fun st => .ok (st.stack.frames.size - 1) st
  evalOperand := fun _ op => do
    let b ← cfActive prog
    annealEvalOperandOverlay b.localDecls b.layouts op none
  evalOperandAt := fun _ _ op => do
    let b ← cfActive prog
    annealEvalOperandOverlay b.localDecls b.layouts op none
  evalPlace := fun _ place _ => do
    let b ← cfActive prog
    let runtimePlace ← annealEvalPlaceOverlay b.localDecls b.layouts place
    pure runtimePlace.stackView
  placeToOp := fun _ place => cfStackPlaceToOp prog place
  forceAllocation := fun _ place => do
    let b ← cfActive prog
    let mp ← annealForceAllocation b.localDecls b.layouts place.toRuntimePlace
    pure ⟨mp, place.layout⟩
  functionSignature := fun _ layout => do
    let (_, ty, callee) ← cfClassifyCallee prog
    if encodeTyId ty != layout.ty then throw (.invalidProgram "callee operand type mismatch")
    match callee with
    | .fnPtr ins _ abi =>
      pure (length ins, match abi with | .rust => .Rust | .c => .C false | .rustIntrinsic => .Rust | .other _ => .Custom)
    | .item n =>
      match cfItem? prog n with
      | some it => pure (it.body.argCount, .Rust)
      | none => throw (.invalidProgram "unknown item")
    | .closureMethod _ _ => pure (2, .RustCall)
  functionKind := fun tyId => do
    let (_, ty, callee) ← cfClassifyCallee prog
    if encodeTyId ty != tyId then throw (.invalidProgram "callee operand type mismatch")
    match callee with
    | .fnPtr .. => pure .FnPtr
    | .item n => pure (.FnDef n #[])
    | .closureMethod m n => pure (.FnDef m #[.Type (cfClosureArgBase + n)])
  readPointer := fun _ op => do
    let imm ← annealReadImmediateOverlay op
    match imm.imm.toScalar with
    | .error err => throw (Miri.Interpreter.ScalarOps.immediateError err)
    | .ok sc =>
      match sc.toPointer annealTargetDataLayout with
      | .error err => throw (Miri.Interpreter.ScalarOps.scalarError err)
      | .ok ptr => pure ptr
  getPtrFn := fun _ ptr => do
    let inst ← cfGetPtrFn prog ptr
    pure (.Instance inst)
  resolve := fun _ defId args =>
    if defId == cfCallMutDefId || defId == cfCallDefId || defId == cfCallOnceDefId then
      match (args[0]? : Option Miri.MIR.GenericArg) with
      | some (Miri.MIR.GenericArg.Type t) =>
        let requested : CfClosureKind :=
          if defId == cfCallDefId then .fn else if defId == cfCallMutDefId then .fnMut else .fnOnce
        match cfResolveClosure prog (t - cfClosureArgBase) requested with
        | .ok inst => pure inst
        | .error err => throw err
      | _ => throw (.invalidProgram "closure trait method without a self type")
    else
      match cfItem? prog defId with
      | some _ => pure (cfItemInstance defId)
      | none => throw (.invalidProgram "call.resolve of an unknown item")
  fnAbiOfFnPtr := fun _ layout _ => do
    let (b, ty, callee) ← cfClassifyCallee prog
    if encodeTyId ty != layout.ty then throw (.invalidProgram "callee operand type mismatch")
    match callee with
    | .fnPtr ins out abi =>
      match cfFnAbiOfFnPtrTy b ins out abi with
      | some fnAbi => pure fnAbi
      | none => throw (.unsupported "fn_abi_of_fn_ptr of an unsupported signature")
    | _ => throw (.invalidProgram "fn_abi_of_fn_ptr of a non-pointer callee")
  fnAbiOfInstance := fun _ inst _ =>
    match cfFnAbiOfInstance prog inst with
    | some fnAbi => pure fnAbi
    | none => throw (.unsupported "fn_abi_of_instance of an unsupported instance")
  requiresCallerLocation := fun _ => pure false
  callerLocation := annealUnsupportedLeaf "call.callerLocation"
  abiCanUnwind := fun abi => abi.canUnwind
  abiVariadic := fun _ => false
  abiFixedCount := fun abi => abi.args.size
  abiArgs := fun abi => abi.args
  abiReturn := fun abi => abi.ret
  sameConvention := fun a b => a.conv == b.conv
  isRustCall := fun e => e == .RustCall
  rustAbi := .Rust
  argLayout := fun a => a.abi.layout
  argIsIgnore := fun a => a.abi.isIgnore
  isOneZst := fun l => l.layout.is1zst
  checkArgumentCompat := fun _ a b => cfCheckArgumentCompat a b
  checkTargetFeatures := fun _ _ => pure ()
  tupleFields := fun ty => cfTupleFields prog ty
  projectFnArg := fun _ arg idx => cfProjectFnArg prog arg idx
  localLayout := fun _ localId => do
    let b ← cfActive prog
    match lookupLocalDeclLayout b.localDecls b.layouts localId with
    | some l => pure l
    | none => throw (.stack (.missingLocalType localId))
  localSpan := fun _ _ => pure defaultSpanRef
  storageLiveDyn := fun _ localId metadata =>
    cfRunFrameStorage prog fun ld ly frame mem =>
      frame.storageLiveDyn mem (annealLocalStorageHooks ld ly) localId metadata
  copyAllowTransmute := fun _ src dest => annealCopyAllowTransmuteOverlay src dest.toRuntimePlace
  protectArgument := fun _ _ => pure ()
  withRetagMode := fun _ _ action => action
  nonCapturingClosure := fun _ inst abi =>
    Miri.Interpreter.ExecutionCallLeaves.nonCapturingClosure (cfCompiler prog) inst (cfVendoredFnAbi abi)
  allocateStack := fun _ _ => annealUnsupportedLeaf "call.allocateStack"
  copyToMemory := fun _ _ _ => annealUnsupportedLeaf "call.copyToMemory"
  vaListPtr := fun _ _ => annealUnsupportedLeaf "call.vaListPtr"
  writeZeroBytes := fun _ _ _ => annealUnsupportedLeaf "call.writeZeroBytes"
  vaListKeyField := fun _ _ => annealUnsupportedLeaf "call.vaListKeyField"
  writePointerToMemory := fun _ _ _ => annealUnsupportedLeaf "call.writePointerToMemory"
  pushRaw := fun _ inst loaded dest cont =>
    cfLiftStack prog (fun hooks stack mem =>
      stack.pushStackFrameRaw mem hooks loaded inst cont dest defaultSpanRef) (some ([], emptyLayoutTable))
  pushDone := fun _ => cfLiftStack prog (fun hooks stack mem => stack.pushStackFrameDone mem hooks) none
  popRaw := fun _ => cfLiftStack prog (fun hooks stack mem => stack.popStackFrameRaw mem hooks) none
  cleanup := fun _ unwinding frame =>
    match cfBodyOfInstance prog frame.functionInstance with
    | some b =>
      cfLiftStack prog (fun hooks stack mem => stack.cleanupStackFrame mem hooks unwinding frame)
        (some (b.localDecls, b.layouts))
    | none => throw (.invalidProgram "frame instance has no captured body")
  afterFrameInit := fun _ => pure ()
  callExtra := fun _ _ _ _ _ _ _ => annealUnsupportedLeaf "call.callExtra"
  callIntrinsic := fun _ _ _ _ _ _ => annealUnsupportedLeaf "call.callIntrinsic"
  callLlvmIntrinsic := fun _ _ _ _ _ => annealUnsupportedLeaf "call.callLlvmIntrinsic"
  findMirOrEvalFn := fun _ inst _ _ _ _ _ =>
    match cfMirBodyOfInstance prog inst with
    | some body => pure (some (⟨.ofCanonicalIndex (cfBodyIndex inst), body⟩, inst))
    | none => throw (.unsupported "no MIR body for the callee instance")
  resolveVirtual := fun _ _ _ _ _ _ => annealUnsupportedLeaf "call.resolveVirtual"
  isDynamic := fun _ => annealUnsupportedLeaf "call.isDynamic"
  unpackDynForDrop := fun _ _ => annealUnsupportedLeaf "call.unpackDynForDrop"
  resolveDropGlue := fun _ _ => annealUnsupportedLeaf "call.resolveDropGlue"
  mplaceToMutRef := fun _ _ => annealUnsupportedLeaf "call.mplaceToMutRef"
  fakeUnitReturn := fun _ => annealUnsupportedLeaf "call.fakeUnitReturn"

def cfCallBudget : Nat := 2

/-! ## §7. Step hooks -/

def cfBaseHooks (body : CapturedMir) : CfHooks := annealStepHooksUnwindFnPtrClosure body [] {} []

def cfControlHooks (body : CapturedMir) :=
  annealControlHooksLM4_1 body.localDecls body.layouts {}

def cfDrop (prog : CfProg) (body : CapturedMir) (place : Miri.MIR.Place) (target : Miri.MIR.BasicBlockId)
    (unwind : Miri.MIR.UnwindAction) (st : AnnealStepState) : Miri.Interpreter.StepResult AnnealStepState Unit :=
  match st.stack.currentFrame? with
  | none => (st, .error (.stack .emptyStack))
  | some frame =>
    if cfIsShimInstance frame.functionInstance then
      -- A non-capturing closure has no drop glue: `Drop` is `go_to_block(target)`.
      match Miri.Interpreter.runRvalue (annealEvalPlaceOverlay body.localDecls body.layouts place) st with
      | (st', .ok _) => Miri.Interpreter.ControlFlow.goToBlock target st'
      | (st', .error e) => (st', .error e)
    else
      let _ := prog
      annealEvalDropLM4_1 place target unwind st

abbrev CfCallImpl := Unit → Nat → Miri.MIR.Terminator → CfM Unit

def cfTerminatorHooks (callImpl tailImpl : CfCallImpl) (prog : CfProg) (body : CapturedMir) :=
  { annealTerminatorHooksLM4_1 body [] {} [] with
    toControlHooks := cfControlHooks body
    call := fun c term st => Miri.Interpreter.Call.run (callImpl c cfCallBudget term) st
    tailCall := fun c term st => Miri.Interpreter.Call.run (tailImpl c cfCallBudget term) st
    drop := fun _ place target unwind st => cfDrop prog body place target unwind st }

/-- A whole-local copy or move between zero-sized locals (e.g. a non-capturing closure value). -/
def cfLocalIsZst (b : CapturedMir) (p : Miri.MIR.Place) : Bool :=
  p.projection.isEmpty &&
    (match lookupLocalDeclLayout b.localDecls b.layouts p.localId with
     | some l => l.layout.isZst
     | none => false)

def cfZstUseOperand? (b : CapturedMir) (place : Miri.MIR.Place) : Miri.MIR.Rvalue → Option Miri.MIR.Operand
  | .Use op _ =>
    (match op with
     | .Copy p | .Move p => if cfLocalIsZst b place && cfLocalIsZst b p then some op else none
     | _ => none)
  | _ => none

/-- `copy_op` of a zero-sized value: the source must be live, and the destination becomes the
(bit-free) zero-sized value. -/
def cfAssignZstUse (b : CapturedMir) (place : Miri.MIR.Place) (op : Miri.MIR.Operand) : CfM Unit := do
  let dest ← annealEvalPlaceOverlay b.localDecls b.layouts place
  let _ ← annealEvalOperandOverlay b.localDecls b.layouts op (some dest.layout)
  annealWriteImmediateLM2_2 .uninit dest

/-- A whole-local tuple aggregate of one or two operands, e.g. the argument tuple `(x,)` of a
direct `Fn::call`. -/
def cfScalarTupleOperands? (place : Miri.MIR.Place) : Miri.MIR.Rvalue → Option (List Miri.MIR.Operand)
  | .Aggregate .Tuple ops =>
    if place.projection.isEmpty && (ops.size == 1 || ops.size == 2) then some ops.toList else none
  | _ => none

/-- Write a tuple of one or two scalars as a `Scalar` / `ScalarPair` immediate. -/
def cfAssignScalarTuple (b : CapturedMir) (place : Miri.MIR.Place) (ops : List Miri.MIR.Operand) : CfM Unit := do
  let dest ← annealEvalPlaceOverlay b.localDecls b.layouts place
  match ops with
  | [op] =>
    let v ← annealEvalOperandOverlay b.localDecls b.layouts op none
    match v.op with
    | .immediate (.scalar s) => annealWriteImmediateLM2_2 (.scalar s) dest
    | _ => throw (.unsupported "tuple aggregate of a non-scalar operand")
  | [op0, op1] =>
    let v0 ← annealEvalOperandOverlay b.localDecls b.layouts op0 none
    let v1 ← annealEvalOperandOverlay b.localDecls b.layouts op1 none
    match v0.op, v1.op with
    | .immediate (.scalar s0), .immediate (.scalar s1) => annealWriteImmediateLM2_2 (.scalarPair s0 s1) dest
    | _, _ => throw (.unsupported "tuple aggregate of a non-scalar operand")
  | _ => throw (.unsupported "tuple aggregate arity")

def cfWithBody {A : Type} (prog : CfProg) (st : AnnealStepState)
    (k : CapturedMir → Miri.Interpreter.StepResult AnnealStepState A) : Miri.Interpreter.StepResult AnnealStepState A :=
  match st.stack.currentFrame? with
  | none => (st, .error (.stack .emptyStack))
  | some f =>
    match cfBodyOfInstance prog f.functionInstance with
    | some b => k b
    | none => (st, .error (.invalidProgram "frame instance has no captured body"))

def cfStepHooksWith (callImpl tailImpl : CfCallImpl) (prog : CfProg) : CfHooks where
  assign := fun c place rvalue st => cfWithBody prog st fun b =>
    if cfIsFnPtrCastRvalue rvalue then
      Miri.Interpreter.runRvalue (Miri.Interpreter.evalRvalueIntoPlace (cfRvalueHooks prog b) c rvalue place) st
    else
      match cfZstUseOperand? b place rvalue with
      | some op => Miri.Interpreter.runRvalue (cfAssignZstUse b place op) st
      | none =>
        match cfScalarTupleOperands? place rvalue with
        | some ops => Miri.Interpreter.runRvalue (cfAssignScalarTuple b place ops) st
        | none => (cfBaseHooks b).assign c place rvalue st
  evalPlace := fun c place skip st => cfWithBody prog st fun b => (cfBaseHooks b).evalPlace c place skip st
  writeDiscriminant := fun c v p st => cfWithBody prog st fun b => (cfBaseHooks b).writeDiscriminant c v p st
  storageLive := fun c l st => cfWithBody prog st fun b => (cfBaseHooks b).storageLive c l st
  storageDead := fun c l st => cfWithBody prog st fun b => (cfBaseHooks b).storageDead c l st
  intrinsic := fun c i st => cfWithBody prog st fun b => (cfBaseHooks b).intrinsic c i st
  incrementConstEvalCounter := fun _ st => (st, .ok ())
  returnFromCurrentFrame := fun c unwinding st => cfWithBody prog st fun b =>
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame (cfControlHooks b) c unwinding st
  beforeTerminator := fun _ st => (st, .ok ())
  terminator := fun c term st => cfWithBody prog st fun b =>
    Miri.Interpreter.ControlFlow.evalTerminator (cfTerminatorHooks callImpl tailImpl prog b) c term st

/-- Step hooks running the unmodified vendored `Call.evalCallTerminator` / `Call.evalTailCallTerminator`. -/
def cfStepHooks (prog : CfProg) : CfHooks :=
  cfStepHooksWith (Miri.Interpreter.Call.evalCallTerminator (cfCallHooks prog))
    (Miri.Interpreter.Call.evalTailCallTerminator (cfCallHooks prog)) prog

/-! ## §8. Machine runner and observations -/

def cfU32Imm (n : Nat) : Miri.Interpreter.Immediate AnnealProv :=
  match Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 n) (Miri.ABI.Size.ofBytes 4) with
  | .ok s => .scalar s
  | .error _ => .uninit

def cfInitLocalsAux (layouts : LayoutTable) : Nat → List LocalDecl → List (Miri.Interpreter.Immediate AnnealProv) →
    List (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
  | _, [], _ => []
  | 0, d :: ds, args => ⟨.live (.immediate .uninit), some (translateTy d.ty layouts)⟩ :: cfInitLocalsAux layouts 1 ds args
  | i + 1, d :: ds, a :: as => ⟨.live (.immediate a), some (translateTy d.ty layouts)⟩ :: cfInitLocalsAux layouts (i + 2) ds as
  | i + 1, _ :: ds, [] => ⟨.dead, none⟩ :: cfInitLocalsAux layouts (i + 2) ds []

/-- Initial machine state: the root frame runs item `0` of `prog` on `args`. -/
def cfMiriInit (prog : CfProg) (args : List (Miri.Interpreter.Immediate AnnealProv)) : Option AnnealStepState :=
  match cfItem? prog 0 with
  | none => none
  | some it =>
    let body := it.body
    match body.localDecls with
    | [] => none
    | ret :: _ =>
      some
        { stack := { frames := #[{
            body := translateBody body, bodyIdentity := .ofCanonicalIndex 0,
            functionInstance := cfItemInstance 0, extra := (),
            returnContinuation := .stop false,
            returnPlace := .frameLocal 0 0 none (translateTy ret.ty body.layouts) (.ofAllocationToken 0),
            localsIdentity := .ofAllocationToken 0,
            locals := (cfInitLocalsAux body.layouts 0 body.localDecls args).toArray, vaList := #[],
            trackCallerArg := none, location := .mir ⟨0, 0⟩ }] },
          machine := AnnealMachine.empty }

inductive CfObs : Type where
  | scalar (bits size : Nat)
  | other
  | panic
  | abort
  | ub
  | unsupported
  | ext (defPath : String)
  | invalid
  | stuck
  deriving DecidableEq, Repr

/-- The root frame is about to execute `Return`: observe `_0`. -/
def cfMiriRootReturn? (st : AnnealStepState) : Option CfObs :=
  if st.stack.frames.size != 1 then none
  else
    match st.stack.currentFrame? with
    | none => none
    | some f =>
      match f.location with
      | .unwinding _ => none
      | .mir loc =>
        match f.body.basicBlocks[loc.block]? with
        | none => none
        | some bb =>
          if loc.statementIndex != bb.statements.size then none
          else
            match bb.terminator.kind with
            | .Return =>
              match f.locals[0]? with
              | some ls =>
                match ls.value with
                | .live (.immediate (.scalar s)) =>
                  match s.toBits s.size with
                  | .ok bits => some (.scalar bits.toNat s.size.bytes.toNat)
                  | .error _ => some .other
                | _ => some .other
              | none => none
            | _ => none

def cfMiriObsOfError : Miri.Interpreter.StepError → CfObs
  | .undefinedBehavior _ => .ub
  | .unsupported _ => .unsupported
  | .invalidProgram _ => .invalid
  | .termination (.abort _) => .abort
  | _ => .stuck

/-- Run the vendored `Miri.Interpreter.Step.step` under the hooks `h`. -/
def cfMiriRun (h : CfHooks) : Nat → AnnealStepState → CfObs
  | 0, _ => .stuck
  | n + 1, st =>
    match cfMiriRootReturn? st with
    | some obs =>
      match Miri.Interpreter.Step.step h () st with
      | (_, .ok true) => obs
      | (_, .ok false) => .stuck
      | (_, .error e) => cfMiriObsOfError e
    | none =>
      match Miri.Interpreter.Step.step h () st with
      | (st', .ok true) => cfMiriRun h n st'
      | (_, .ok false) => .stuck
      | (_, .error e) => cfMiriObsOfError e

def cfMiriRunFrom (h : CfHooks) (prog : CfProg) (fuel : Nat)
    (args : List (Miri.Interpreter.Immediate AnnealProv)) : CfObs :=
  match cfMiriInit prog args with
  | some st => cfMiriRun h fuel st
  | none => .stuck

/-! ## §9. Trusted runner (real `stepMirFn`) -/

inductive CfRunState : Type where
  | running (s : MachineState)
  | done (o : CfObs)

/-- One `stepMirFn` step of the bounded Trusted runner. -/
def cfRunStep (body : CapturedMir) : CfRunState → CfRunState
  | .done o => .done o
  | .running s =>
    match stepMirFn body s with
    | .tau (.running s') => .running s'
    | .vis (.inr (.inl (.emit _))) k =>
      match k PUnit.unit with
      | .running s' => .running s'
      | _ => .done .stuck
    | .ret (.normal r) =>
      match r.1 with
      | .scalar sc => .done (.scalar sc.bits sc.sizeBytes)
      | _ => .done .other
    | .ret .panic => .done .panic
    | .ret .abort => .done .abort
    | .vis (.inl (.fail .ub)) _ => .done .ub
    | .vis (.inl (.fail .unsupported)) _ => .done .unsupported
    | .vis (.inr (.inr (.call req))) _ => .done (.ext req.defPath)
    | _ => .done .stuck

/-- Execute `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` for up to `fuel` steps. -/
def cfRun (body : CapturedMir) (fuel : Nat) (s : MachineState) : CfObs :=
  match Nat.repeat (cfRunStep body) fuel (.running s) with
  | .done o => o
  | .running _ => .stuck

/-- Initial Trusted state of `body` on `args` with linked `callees`. -/
def cfInit (body : CapturedMir) (args : List MirSemantics.Value) (callees : List CapturedMir) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := initLocalsAux 0 body.localDecls args },
    memory := { emptyMemory with nextAllocId := length body.allocations, globals := body.allocations,
                                 callees := callees, traitImpls := body.traitImpls } }

/-! ## §10. Stuttering simulation across `ClosureOnceShim` frames -/

/-- Scalar agreement: equal width and equal bits. -/
def cfScalarRel (sc : MirAst.ScalarInt) (s : Miri.Memory.Scalar AnnealProv) : Bool :=
  s.size.bytes.toNat == sc.sizeBytes &&
    (match s.toBits s.size with
     | .ok bits => bits.toNat == sc.bits
     | .error _ => false)

/-- Function-pointer agreement: both pointers denote the same linked function or closure body. -/
def cfFnPtrRel (prog : CfProg) (fnPtrs : List FnPtrEntry) (mach : AnnealMachine) (p : ProvenancePtr)
    (s : Miri.Memory.Scalar AnnealProv) : Bool :=
  match lookupFnPtr fnPtrs p.allocId, s.toPointer annealTargetDataLayout with
  | some entry, .ok ptr =>
    match annealResolvePtr mach ptr 0 with
    | .ok resolved =>
      resolved.offset == Miri.ABI.Size.ZERO && p.offsetBytes == 0 &&
        (match cfInstanceOfAllocNat resolved.allocId.value.toNat with
         | some inst =>
           (match inst.kind with
            | .Item n | .Shim (.ClosureOnce _ n _) =>
              (match cfItem? prog n with
               | some it => stringEq it.body.defPath entry.defPath
               | none => false)
            | _ => false)
         | none => false)
    | .error _ => false
  | _, _ => false

/-- Value agreement at a synchronization point: scalars agree exactly, function pointers denote
the same function, zero-sized values are unconstrained, and data pointers and memory-backed
aggregates are not compared. -/
def cfValRel (prog : CfProg) (fnPtrs : List FnPtrEntry) (mach : AnnealMachine) :
    MirSemantics.Value → Miri.Interpreter.Operand AnnealProv → Bool
  | .scalar sc, .immediate (.scalar s) => cfScalarRel sc s
  | .scalar _, _ => false
  | .ptr p _, .immediate (.scalar s) =>
    if (lookupFnPtr fnPtrs p.allocId).isSome then cfFnPtrRel prog fnPtrs mach p s else s.isPointer
  | .ptr _ _, _ => false
  | .aggregate _ [.scalar sc], .immediate (.scalar s) => cfScalarRel sc s
  | .aggregate _ [.scalar a, .scalar b], .immediate (.scalarPair s0 s1) => cfScalarRel a s0 && cfScalarRel b s1
  | _, _ => true

def cfSlotRel (prog : CfProg) (fnPtrs : List FnPtrEntry) (mach : AnnealMachine) (exempt : Bool) :
    LocalSlot → Miri.Interpreter.LocalValue AnnealProv → Bool
  | .dead, .dead => true
  | .uninit, .live _ => true
  | .init v, .live op => exempt || cfValRel prog fnPtrs mach v op
  | _, _ => false

def cfLocalsRel (prog : CfProg) (fnPtrs : List FnPtrEntry) (mach : AnnealMachine) (envExempt : Bool) :
    Nat → List LocalSlot → List (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) → Bool
  | _, [], [] => true
  | i, a :: as, b :: bs =>
    cfSlotRel prog fnPtrs mach (envExempt && i == 1) a b.value && cfLocalsRel prog fnPtrs mach envExempt (i + 1) as bs
  | _, _, _ => false

def cfNonShimDepth (m : AnnealStepState) : Nat :=
  (m.stack.frames.toList.filter fun f => !cfIsShimInstance f.functionInstance).length

/-- Synchronization relation: same active body, same location, same depth up to shim frames,
and agreeing locals (the environment local `_1` of a closure body is exempt). -/
def cfRel (prog : CfProg) (body : CapturedMir) (s : MachineState) (m : AnnealStepState) : Bool :=
  match m.stack.currentFrame? with
  | none => false
  | some f =>
    match cfBodyOfInstance prog f.functionInstance, f.location with
    | some b, .mir loc =>
      !cfIsShimInstance f.functionInstance &&
      stringEq b.defPath (activeMirBody body s).defPath &&
      loc.block == s.frame.blockIdx && loc.statementIndex == s.frame.stmtIdx &&
      cfNonShimDepth m == length s.memory.callStack + 1 &&
      cfLocalsRel prog s.memory.fnPtrs m.machine (cfClosureKind? b).isSome 0 s.frame.locals f.locals.toList
    | _, _ => false

/-- A `ClosureOnceShim` frame, or a frame being unwound, is on top. -/
def cfStutterTop (m : AnnealStepState) : Bool :=
  match m.stack.currentFrame? with
  | some f =>
    cfIsShimInstance f.functionInstance ||
      (match f.location with
       | .unwinding _ => true
       | .mir _ => false)
  | none => false

/-- One `Step.step`, then every further `Step.step` taken while `cfStutterTop` holds. -/
def cfMiriStutter (h : CfHooks) : Nat → AnnealStepState → Option (AnnealStepState × Nat)
  | 0, _ => none
  | b + 1, m =>
    match Miri.Interpreter.Step.step h () m with
    | (m', .ok true) =>
      if cfStutterTop m' then (cfMiriStutter h b m').map fun r => (r.1, r.2 + 1) else some (m', 0)
    | _ => none

inductive CfMiriStutter (h : CfHooks) : AnnealStepState → AnnealStepState → Nat → Prop where
  | last {m m' : AnnealStepState} :
      Miri.Interpreter.Step.step h () m = (m', .ok true) → cfStutterTop m' = false → CfMiriStutter h m m' 0
  | more {m m1 m' : AnnealStepState} {k : Nat} :
      Miri.Interpreter.Step.step h () m = (m1, .ok true) → cfStutterTop m1 = true →
      CfMiriStutter h m1 m' k → CfMiriStutter h m m' (k + 1)

theorem cfMiriStutter_sound (h : CfHooks) :
    ∀ (b : Nat) (m m' : AnnealStepState) (k : Nat),
      cfMiriStutter h b m = some (m', k) → CfMiriStutter h m m' k := by
  intro b
  induction b with
  | zero => intro m m' k hc; simp [cfMiriStutter] at hc
  | succ b ih =>
    intro m m' k hc
    unfold cfMiriStutter at hc
    generalize hstep : Miri.Interpreter.Step.step h () m = r at hc
    obtain ⟨m1, res⟩ := r
    cases res with
    | error e => simp at hc
    | ok v =>
      cases v with
      | false => simp at hc
      | true =>
        dsimp only at hc
        cases htop : cfStutterTop m1 with
        | false =>
          rw [htop] at hc
          simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          exact .last hstep htop
        | true =>
          rw [htop] at hc
          simp only [↓reduceIte, Option.map_eq_some_iff] at hc
          obtain ⟨⟨m2, k2⟩, hrec, heq⟩ := hc
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          exact .more hstep htop (ih m1 m2 k2 hrec)

def cfStutterBudget : Nat := 8

/-- Stuttering simulation: each Trusted step is matched by one `Step.step` plus the steps taken
inside `ClosureOnceShim` (or unwinding) frames; both machines end with the same observation `o`.
The index counts the stutter steps. -/
inductive CfStutterSim (h : CfHooks) (prog : CfProg) (body : CapturedMir) :
    MachineState → AnnealStepState → CfObs → Nat → Prop where
  | done {s : MachineState} {m : AnnealStepState} {o : CfObs} :
      cfRunStep body (.running s) = .done o → cfMiriRootReturn? m = some o →
      (Miri.Interpreter.Step.step h () m).2 = .ok true → CfStutterSim h prog body s m o 0
  | step {s s' : MachineState} {m m' : AnnealStepState} {o : CfObs} {k j : Nat} :
      cfRunStep body (.running s) = .running s' → CfMiriStutter h m m' k →
      cfRel prog body s' m' = true → CfStutterSim h prog body s' m' o j →
      CfStutterSim h prog body s m o (j + k)

/-- Executable stuttering-simulation certificate checker. -/
def cfStutterCheck (h : CfHooks) (prog : CfProg) (body : CapturedMir) :
    Nat → MachineState → AnnealStepState → Option (CfObs × Nat)
  | 0, _, _ => none
  | n + 1, s, m =>
    match cfRunStep body (.running s) with
    | .running s' =>
      match cfMiriStutter h cfStutterBudget m with
      | some (m', k) =>
        if cfRel prog body s' m' then (cfStutterCheck h prog body n s' m').map fun r => (r.1, r.2 + k)
        else none
      | none => none
    | .done o =>
      match cfMiriRootReturn? m with
      | some o' =>
        if o' = o then
          (match (Miri.Interpreter.Step.step h () m).2 with
           | .ok true => some (o, 0)
           | _ => none)
        else none
      | none => none

/-- **Universal soundness of the certificate checker.** -/
theorem cfStutterCheck_sound (h : CfHooks) (prog : CfProg) (body : CapturedMir) :
    ∀ (n : Nat) (s : MachineState) (m : AnnealStepState) (o : CfObs) (k : Nat),
      cfStutterCheck h prog body n s m = some (o, k) → CfStutterSim h prog body s m o k := by
  intro n
  induction n with
  | zero => intro s m o k hc; simp [cfStutterCheck] at hc
  | succ n ih =>
    intro s m o k hc
    unfold cfStutterCheck at hc
    cases hT : cfRunStep body (.running s) with
    | running s' =>
      rw [hT] at hc
      dsimp only at hc
      cases hM : cfMiriStutter h cfStutterBudget m with
      | none => rw [hM] at hc; simp at hc
      | some r =>
        obtain ⟨m', k1⟩ := r
        rw [hM] at hc
        dsimp only at hc
        cases hR : cfRel prog body s' m' with
        | false => rw [hR] at hc; simp at hc
        | true =>
          rw [hR] at hc
          simp only [↓reduceIte, Option.map_eq_some_iff] at hc
          obtain ⟨⟨o2, j⟩, hrec, heq⟩ := hc
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          exact .step hT (cfMiriStutter_sound h _ _ _ _ hM) hR (ih s' m' o2 j hrec)
    | done o1 =>
      rw [hT] at hc
      dsimp only at hc
      cases hO : cfMiriRootReturn? m with
      | none => rw [hO] at hc; simp at hc
      | some o' =>
        rw [hO] at hc
        dsimp only at hc
        by_cases heq : o' = o1
        · subst heq
          simp only [↓reduceIte] at hc
          generalize hS : (Miri.Interpreter.Step.step h () m).2 = res at hc
          cases res with
          | error e => simp at hc
          | ok v =>
            cases v with
            | false => simp at hc
            | true =>
              simp only [Option.some.injEq, Prod.mk.injEq] at hc
              obtain ⟨rfl, rfl⟩ := hc
              exact .done hT hO hS
        · simp [heq] at hc

/-- 1-to-1 lockstep simulation: every Trusted step is matched by exactly one `Step.step`. -/
inductive CfLockstepSim (h : CfHooks) (prog : CfProg) (body : CapturedMir) :
    MachineState → AnnealStepState → CfObs → Prop where
  | done {s : MachineState} {m : AnnealStepState} {o : CfObs} :
      cfRunStep body (.running s) = .done o → cfMiriRootReturn? m = some o →
      (Miri.Interpreter.Step.step h () m).2 = .ok true → CfLockstepSim h prog body s m o
  | step {s s' : MachineState} {m m' : AnnealStepState} {o : CfObs} :
      cfRunStep body (.running s) = .running s' →
      Miri.Interpreter.Step.step h () m = (m', .ok true) →
      cfRel prog body s' m' = true → CfLockstepSim h prog body s' m' o →
      CfLockstepSim h prog body s m o

/-- A stuttering simulation without stutter steps is a 1-to-1 lockstep simulation. -/
theorem cfStutterSim_zero_lockstep {h : CfHooks} {prog : CfProg} {body : CapturedMir}
    {s : MachineState} {m : AnnealStepState} {o : CfObs} {k : Nat}
    (hs : CfStutterSim h prog body s m o k) (hk : k = 0) : CfLockstepSim h prog body s m o := by
  induction hs with
  | done h1 h2 h3 => exact .done h1 h2 h3
  | @step s s' m m' o k j h1 h2 h3 _ ih =>
    have hj : j = 0 := by omega
    have hk' : k = 0 := by omega
    subst hk'
    cases h2 with
    | last e _ => exact .step h1 e h3 (ih hj)

theorem cfNatRepeat_succ_comm {α : Type} (f : α → α) : ∀ (n : Nat) (a : α),
    Nat.repeat f (n + 1) a = Nat.repeat f n (f a) := by
  intro n
  induction n with
  | zero => intro a; rfl
  | succ n ih => intro a; show f (Nat.repeat f (n + 1) a) = f (Nat.repeat f n (f a)); rw [ih]

/-- A stuttering simulation determines the bounded Trusted run. -/
theorem cfStutterSim_trusted_run {h : CfHooks} {prog : CfProg} {body : CapturedMir}
    {s : MachineState} {m : AnnealStepState} {o : CfObs} {k : Nat}
    (hs : CfStutterSim h prog body s m o k) : ∃ fuel, cfRun body fuel s = o := by
  induction hs with
  | done h1 _ _ =>
    refine ⟨1, ?_⟩
    show (match cfRunStep body (.running _) with | .done o => o | .running _ => CfObs.stuck) = _
    rw [h1]
  | step h1 _ _ _ ih =>
    obtain ⟨fuel, hf⟩ := ih
    refine ⟨fuel + 1, ?_⟩
    unfold cfRun at hf ⊢
    rw [cfNatRepeat_succ_comm, h1]
    exact hf

/-- `n` consecutive successful steps of the vendored `Step.step`. -/
inductive CfMiriSteps (h : CfHooks) : Nat → AnnealStepState → AnnealStepState → Prop where
  | refl (m : AnnealStepState) : CfMiriSteps h 0 m m
  | cons {n : Nat} {m m1 m' : AnnealStepState} :
      Miri.Interpreter.Step.step h () m = (m1, .ok true) → CfMiriSteps h n m1 m' → CfMiriSteps h (n + 1) m m'

theorem cfMiriStutter_steps {h : CfHooks} {m m' : AnnealStepState} {k : Nat}
    (hs : CfMiriStutter h m m' k) : CfMiriSteps h (k + 1) m m' := by
  induction hs with
  | last e _ => exact .cons e (.refl _)
  | more e _ _ ih => exact .cons e ih

theorem cfMiriSteps_trans {h : CfHooks} {a b : Nat} {m1 m2 m3 : AnnealStepState}
    (h1 : CfMiriSteps h a m1 m2) (h2 : CfMiriSteps h b m2 m3) : ∃ n, CfMiriSteps h n m1 m3 := by
  induction h1 with
  | refl _ => exact ⟨b, h2⟩
  | cons e _ ih =>
    obtain ⟨n, hn⟩ := ih h2
    exact ⟨n + 1, .cons e hn⟩

/-- A stuttering simulation determines the vendored run: `Step.step` reaches a root `Return`
observing `o`, and that final `Return` step succeeds. -/
theorem cfStutterSim_miri_run {h : CfHooks} {prog : CfProg} {body : CapturedMir}
    {s : MachineState} {m : AnnealStepState} {o : CfObs} {k : Nat}
    (hs : CfStutterSim h prog body s m o k) :
    ∃ n mf, CfMiriSteps h n m mf ∧ cfMiriRootReturn? mf = some o ∧
      (Miri.Interpreter.Step.step h () mf).2 = .ok true := by
  induction hs with
  | done _ h2 h3 => exact ⟨0, _, .refl _, h2, h3⟩
  | step _ h2 _ _ ih =>
    obtain ⟨n, mf, hn, ho, hok⟩ := ih
    obtain ⟨n', hn'⟩ := cfMiriSteps_trans (cfMiriStutter_steps h2) hn
    exact ⟨n', mf, hn', ho, hok⟩

/-- Certificate for a whole program: initial states related, then `cfStutterCheck`. -/
def cfCertificate (h : CfHooks) (prog : CfProg) (body : CapturedMir) (callees : List CapturedMir)
    (targs : List MirSemantics.Value) (margs : List (Miri.Interpreter.Immediate AnnealProv)) (fuel : Nat) :
    Option (CfObs × Nat) :=
  match cfMiriInit prog margs with
  | some m =>
    if cfRel prog body (cfInit body targs callees) m then
      cfStutterCheck h prog body fuel (cfInit body targs callees) m
    else none
  | none => none

theorem cfCertificate_sound {h : CfHooks} {prog : CfProg} {body : CapturedMir} {callees : List CapturedMir}
    {targs : List MirSemantics.Value} {margs : List (Miri.Interpreter.Immediate AnnealProv)} {fuel : Nat}
    {o : CfObs} {k : Nat} (hc : cfCertificate h prog body callees targs margs fuel = some (o, k)) :
    ∃ m, cfMiriInit prog margs = some m ∧ cfRel prog body (cfInit body targs callees) m = true ∧
      CfStutterSim h prog body (cfInit body targs callees) m o k := by
  unfold cfCertificate at hc
  cases hM : cfMiriInit prog margs with
  | none => rw [hM] at hc; simp at hc
  | some m =>
    rw [hM] at hc
    dsimp only at hc
    cases hR : cfRel prog body (cfInit body targs callees) m with
    | false => rw [hR] at hc; simp at hc
    | true =>
      rw [hR] at hc
      simp only [↓reduceIte] at hc
      exact ⟨m, rfl, hR, cfStutterCheck_sound h prog body _ _ _ _ _ hc⟩

/-! ## §K. Mechanically derived, kernel-evaluable forms of the vendored interpreter -/

section KernelForms
open Lean Meta Elab Command

/-- Whether `c` is the `Std.Legacy.Range` instance behind `for _ in [a:b]` loops. -/
def cfIsRangeLoopConst (c : Name) : Bool :=
  let s := c.toString
  (s.splitOn "Std.Legacy.Range").length > 1 && ((s.splitOn "forIn").length > 1 || (s.splitOn "ForIn").length > 1)

/-- `#cf_derive_kernel_forms root => rootK rootEq` derives, for `root` and every definition it
transitively uses whose body contains a `Std.Legacy.Range` loop, a copy in which every such loop
is rewritten to the equal `List.range'` loop (`Std.Legacy.Range.forIn_eq_forIn_range'`), together
with a kernel-checked theorem `original = copy`. `rootK` and `rootEq : @root = @rootK` name the
copy and theorem of `root`. -/
elab "#cf_derive_kernel_forms " root:ident " => " rootK:ident rootEq:ident : command => liftTermElabM do
  let env ← getEnv
  let rootName ← realizeGlobalConstNoOverloadWithInfo root
  let ns ← getCurrNamespace
  -- Post-order traversal of the definitions reachable from `root`.
  let mut visited : Std.HashSet Name := {}
  let mut order : Array Name := #[]
  let mut stack : Array (Name × Bool) := #[(rootName, false)]
  let mut deps : Std.HashMap Name (Array Name) := {}
  while !stack.isEmpty do
    let (n, done) := stack.back!
    stack := stack.pop
    if done then
      order := order.push n
    else if !visited.contains n then
      visited := visited.insert n
      match env.find? n with
      | some (.defnInfo d) =>
        let used := d.value.getUsedConstants
        deps := deps.insert n used
        stack := stack.push (n, true)
        for u in used do
          if !visited.contains u then stack := stack.push (u, false)
      | _ => pure ()
  -- Definitions whose bodies (transitively) contain a `Std.Legacy.Range` loop.
  let mut tainted : Std.HashSet Name := {}
  for n in order do
    let used := deps.getD n #[]
    if (n.toString.splitOn "Std.Legacy.Range").length > 1 then
      pure ()
    else if used.any cfIsRangeLoopConst || used.any tainted.contains then
      tainted := tainted.insert n
  let mut eqThm : Std.HashMap Name Name := {}
  let mut idx : Nat := 0
  let mut derived : Nat := 0
  for n in order do
    if tainted.contains n then
      let some (.defnInfo d) := (← getEnv).find? n | throwError "not a definition: {n}"
      let mut thms : SimpTheorems := {}
      thms ← thms.addConst ``Std.Legacy.Range.forIn_eq_forIn_range'
      for u in deps.getD n #[] do
        if let some t := eqThm[u]? then
          thms ← thms.addConst t
      let ctx ← Simp.mkContext
        (config := { zeta := false, zetaDelta := false, maxSteps := 100000000, decide := false })
        (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
      let (r, _) ← simp d.value ctx
      match r.proof? with
      | none => pure ()
      | some proof =>
        let isRoot := n == rootName
        let last := match n with | .str _ s => s | _ => "c"
        let kName : Name := if isRoot then ns ++ rootK.getId else ns ++ `KernelForm ++ Name.mkSimple s!"k{idx}_{last}"
        let tName : Name := if isRoot then ns ++ rootEq.getId else ns ++ `KernelForm ++ Name.mkSimple s!"k{idx}_{last}_eq"
        idx := idx + 1
        addDecl (.defnDecl { name := kName, levelParams := d.levelParams, type := d.type,
                             value := r.expr, hints := d.hints, safety := .safe })
        let lvls := d.levelParams.map mkLevelParam
        let eqType ← mkEq (mkConst n lvls) (mkConst kName lvls)
        addDecl (.thmDecl { name := tName, levelParams := d.levelParams, type := eqType, value := proof })
        eqThm := eqThm.insert n tName
        derived := derived + 1
  unless eqThm.contains rootName do
    throwError "{rootName} does not use any `Std.Legacy.Range` loop"
  logInfo m!"derived {derived} kernel forms from {order.size} reachable definitions"

end KernelForms

set_option maxHeartbeats 0 in
#cf_derive_kernel_forms cfStepHooks => cfStepHooksK cfStepHooks_eq_K

/-! ## §12. Programs -/

/-- The monomorphic instance `generic::<targs>` computed by Trusted `lookupCallee`. -/
def cfMono (generic : CapturedMir) (callerLayouts : LayoutTable) (targs : List RigidTy) : CfItem :=
  ⟨targs, (lookupCallee [generic] callerLayouts generic.defPath targs).getD generic⟩

def cfU32 (n : Nat) : MirSemantics.Value := .scalar ⟨n, 4⟩

/-- Root harness `fn(x: u32) -> u32 { callee(x) }` (a tail call cannot be the root frame). -/
def cfCallHarness (callee : CapturedMir) : CapturedMir :=
  { defPath := "harness::call_" ++ callee.defPath, phase := callee.phase, role := callee.role, argCount := 1,
    localDecls := [{ mutability := .mut, ty := { kind := .uint .u32, layoutIdx := 0 }, debugName := none },
                   { mutability := .mut, ty := { kind := .uint .u32, layoutIdx := 0 }, debugName := none }],
    basicBlocks :=
      [ { statements := [],
          terminator := cfShimTerm (.call (.constant { ty := { kind := .fnDef callee.defPath [], layoutIdx := 0 }, val := .zeroSized })
            [.move ⟨1, []⟩] ⟨0, []⟩ (some 1) .continue_),
          isCleanup := false },
        { statements := [], terminator := cfShimTerm .return_, isCleanup := false } ],
    fnAbi := callee.fnAbi, layouts := callee.layouts, allocations := [] }

def cfProgDriver : CfProg := [⟨[], cfFx_finding_driver⟩, ⟨[], cfFx_finding_closure_0⟩, ⟨[], cfFx_finding_closure_1⟩]
def cfProgFinding : CfProg :=
  [⟨[], cfFx_finding_main⟩, ⟨[], cfFx_finding_driver⟩, ⟨[], cfFx_finding_closure_0⟩, ⟨[], cfFx_finding_closure_1⟩]
def cfProgFnShared : CfProg := [⟨[], cfFx_fn_shared⟩, ⟨[], cfFx_fn_shared_closure_0⟩]
def cfProgFnMut : CfProg :=
  [⟨[], cfFx_fn_mut_kind⟩,
   cfMono cfFx_id_mut cfFx_fn_mut_kind.layouts [.closure "closure_matrix::fn_mut_kind::{closure#0}" []],
   ⟨[], cfFx_fn_mut_kind_closure_0⟩]
def cfProgFnOnce : CfProg :=
  [⟨[], cfFx_fn_once_kind⟩,
   cfMono cfFx_id_once cfFx_fn_once_kind.layouts [.closure "closure_matrix::fn_once_kind::{closure#0}" []],
   ⟨[], cfFx_fn_once_kind_closure_0⟩]
def cfProgZeroArg : CfProg := [⟨[], cfFx_zero_arg⟩, ⟨[], cfFx_zero_arg_closure_0⟩]
def cfProgTwoArg : CfProg := [⟨[], cfFx_two_arg⟩, ⟨[], cfFx_two_arg_closure_0⟩]
def cfProgUnsafe : CfProg := [⟨[], cfFx_unsafe_closure⟩, ⟨[], cfFx_unsafe_closure_closure_0⟩]
def cfProgWiden : CfProg := [⟨[], cfFx_widen_and_identity⟩, ⟨[], cfFx_widen_and_identity_closure_0⟩]
def cfProgMixed : CfProg :=
  [⟨[], cfFx_mixed_fn_item_and_closure⟩, ⟨[], cfFx_helper_triple⟩, ⟨[], cfFx_mixed_fn_item_and_closure_closure_0⟩]
def cfProgCes : CfProg := [⟨[], cfFx_ces_through_closure_fn_ptr⟩, ⟨[], cfFx_ces_through_closure_fn_ptr_closure_0⟩]
def cfTailRoot : CapturedMir := cfCallHarness cfFx_tail_through_closure
def cfProgTail : CfProg := [⟨[], cfTailRoot⟩, ⟨[], cfFx_tail_through_closure⟩, ⟨[], cfFx_tail_through_closure_closure_0⟩]
def cfProgGeneric : CfProg :=
  [⟨[], cfFx_call_generic⟩, cfMono cfFx_generic_closure cfFx_call_generic.layouts [.uint .u32],
   ⟨[], cfFx_generic_closure_closure_0⟩]
def cfProgDirect : CfProg := [⟨[], cfFx_direct_closure_call⟩, ⟨[], cfFx_direct_closure_call_closure_0⟩]
def cfProgUnwind : CfProg :=
  [⟨[], cfFx_unwind_through_closure⟩, ⟨[], cfFx_unwind_through_closure_closure_0⟩,
   ⟨[], cfFx_Guard_as_core_ops_Drop_drop⟩]

/-! ## §13. Hand-built negative programs -/

def cfHandStmt (k : StatementKind) : MirAst.Statement := { kind := k, span := "<hand>" }
def cfHandTerm (k : TerminatorKind) : MirAst.Terminator := { kind := k, span := "<hand>" }
def cfHandDecl (ty : Ty) : LocalDecl := { mutability := .mut, ty := ty, debugName := none }
def cfU32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
def cfNegClosurePath : String := "closure_matrix::fn_once_kind::{closure#0}"
def cfNegFnPtrTy (inputs : List RigidTy) (safety : Safety) (conv : CallConv) : Ty :=
  { kind := .fnPtr inputs (.uint .u32) safety conv, layoutIdx := 1 }

/-- Hand-built variant of the captured `closure_matrix::fn_shared`, linked against the captured
`FnOnce` closure body `closure_matrix::fn_once_kind::{closure#0}`:
`_3 = {closure}; _2 = move _3 as castTy (PointerCoercion(coercion)); _4 = copy _2; _5 = copy _1;
_0 = move _4(callArgs)`, where the closure type of `_3` lists `upvarTys` and `_4 : callTy` may
differ from `_2 : castTy` (the effect of a `transmute` between function-pointer types). -/
def cfNegCaller (upvarTys : List RigidTy) (coercion : String) (castTy callTy : Ty)
    (callArgs : List Operand) : CapturedMir :=
  { defPath := "hand::negative_caller", phase := .runtimeOptimized, role := .subject, argCount := 1,
    localDecls := [cfHandDecl cfU32Ty, cfHandDecl cfU32Ty, cfHandDecl castTy,
                   cfHandDecl { kind := .closure cfNegClosurePath upvarTys, layoutIdx := 2 },
                   cfHandDecl callTy, cfHandDecl cfU32Ty],
    basicBlocks :=
      [ { statements :=
            [ cfHandStmt (.storageLive 2), cfHandStmt (.storageLive 3),
              cfHandStmt (.assign ⟨3, []⟩ (.aggregate (.closure cfNegClosurePath) [])),
              cfHandStmt (.assign ⟨2, []⟩ (.cast (.pointerCoercion coercion) (.move ⟨3, []⟩) castTy)),
              cfHandStmt (.storageDead 3), cfHandStmt (.storageLive 4),
              cfHandStmt (.assign ⟨4, []⟩ (.use (.copy ⟨2, []⟩))),
              cfHandStmt (.storageLive 5), cfHandStmt (.assign ⟨5, []⟩ (.use (.copy ⟨1, []⟩))) ],
          terminator := cfHandTerm (.call (.move ⟨4, []⟩) callArgs ⟨0, []⟩ (some 1) .continue_),
          isCleanup := false },
        { statements := [cfHandStmt (.storageDead 5), cfHandStmt (.storageDead 4), cfHandStmt (.storageDead 2)],
          terminator := cfHandTerm .return_, isCleanup := false } ],
    fnAbi := cfFx_fn_shared.fnAbi, layouts := cfFx_fn_shared.layouts, allocations := [] }

def cfSafeFn1 : Ty := cfNegFnPtrTy [.uint .u32] .safe .rust
/-- Closure type with one `u32` upvar coerced by `ClosureFnPointer(Safe)` (rejected by rustc, E0308). -/
def cfNegCapU32 : CapturedMir :=
  cfNegCaller [.uint .u32] "ClosureFnPointer(Safe)" cfSafeFn1 cfSafeFn1 [.move ⟨5, []⟩]
/-- Closure type with one zero-sized `()` upvar coerced by `ClosureFnPointer(Safe)`. -/
def cfNegCapUnit : CapturedMir :=
  cfNegCaller [.tuple []] "ClosureFnPointer(Safe)" cfSafeFn1 cfSafeFn1 [.move ⟨5, []⟩]
/-- Forged `(N+1)`-argument indirect call through a `fn(u32, u32) -> u32` pointer type. -/
def cfNegForged : CapturedMir :=
  cfNegCaller [] "ClosureFnPointer(Safe)" cfSafeFn1 (cfNegFnPtrTy [.uint .u32, .uint .u32] .safe .rust)
    [.move ⟨5, []⟩, .copy ⟨1, []⟩]
/-- Indirect call through a pointer retyped to `fn(u64) -> u32`. -/
def cfNegTransSig : CapturedMir :=
  cfNegCaller [] "ClosureFnPointer(Safe)" cfSafeFn1 (cfNegFnPtrTy [.uint .u64] .safe .rust) [.move ⟨5, []⟩]
/-- Indirect call through a pointer retyped to `extern "C" fn(u32) -> u32`. -/
def cfNegExternC : CapturedMir :=
  cfNegCaller [] "ClosureFnPointer(Safe)" cfSafeFn1 (cfNegFnPtrTy [.uint .u32] .safe .c) [.move ⟨5, []⟩]
/-- `ClosureFnPointer(Unsafe)` coercion whose target type is a safe `fn(u32) -> u32`. -/
def cfNegSafetyCast : CapturedMir :=
  cfNegCaller [] "ClosureFnPointer(Unsafe)" cfSafeFn1 cfSafeFn1 [.move ⟨5, []⟩]
/-- Indirect call through a safe pointer retyped to `unsafe fn(u32) -> u32`. -/
def cfNegSafetyCall : CapturedMir :=
  cfNegCaller [] "ClosureFnPointer(Safe)" cfSafeFn1 (cfNegFnPtrTy [.uint .u32] .unsafe_ .rust) [.move ⟨5, []⟩]
/-- The spelling `ClosureFnPointer(Normal)`, which `rustc-capture` never emits. -/
def cfNegNormal : CapturedMir :=
  cfNegCaller [] "ClosureFnPointer(Normal)" cfSafeFn1 cfSafeFn1 [.move ⟨5, []⟩]

def cfNegProg (body : CapturedMir) : CfProg := [⟨[], body⟩, ⟨[], cfFx_fn_once_kind_closure_0⟩]
def cfNegTrusted (body : CapturedMir) : CfObs := cfRun body 100 (cfInit body [cfU32 5] [cfFx_fn_once_kind_closure_0])
def cfNegMiri (body : CapturedMir) : CfObs := cfMiriRunFrom (cfStepHooks (cfNegProg body)) (cfNegProg body) 100 [cfU32Imm 5]

/-! ## §14. Universal resolution and pointer-identity laws -/

/-- The function allocation `65536 + 2n` denotes item `n`. -/
theorem cfInstanceOfAllocNat_item (n : Nat) :
    cfInstanceOfAllocNat (65536 + 2 * n) = some (cfItemInstance n) := by
  have h2 : (65536 + 2 * n - 65536) % 2 = 0 := by omega
  have h3 : (65536 + 2 * n - 65536) / 2 = n := by omega
  unfold cfInstanceOfAllocNat
  split
  · omega
  · rw [h2, h3]; rfl

/-- The function allocation `65536 + 2n + 1` denotes the `ClosureOnceShim` of item `n`. -/
theorem cfInstanceOfAllocNat_shim (n : Nat) :
    cfInstanceOfAllocNat (65536 + 2 * n + 1) = some (cfShimInstance n) := by
  have h2 : (65536 + 2 * n + 1 - 65536) % 2 = 1 := by omega
  have h3 : (65536 + 2 * n + 1 - 65536) / 2 = n := by omega
  unfold cfInstanceOfAllocNat
  split
  · omega
  · rw [h2, h3]; rfl

/-- Pointer identity: an item and a `ClosureOnceShim` never share a function allocation, and
distinct items have distinct function allocations. -/
theorem cfFnAllocNat_injective (n m : Nat) :
    cfFnAllocNat (cfItemInstance n) ≠ cfFnAllocNat (cfShimInstance m) ∧
    (cfFnAllocNat (cfItemInstance n) = cfFnAllocNat (cfItemInstance m) → n = m) ∧
    (cfFnAllocNat (cfShimInstance n) = cfFnAllocNat (cfShimInstance m) → n = m) := by
  simp only [cfFnAllocNat, cfItemInstance, cfShimInstance, Option.some.injEq, ne_eq]
  omega

/-- `resolve_closure(.., FnOnce)` of a by-value (`FnOnce`) closure body is the body item itself:
no shim, hence the 1-to-1 lockstep path. -/
theorem cfResolveClosure_fnOnce_is_item {prog : CfProg} {n k : Nat} {it : CfItem}
    (hit : cfItem? prog n = some it)
    (hgen : (it.body.typeParamCount != 0 && it.typeArgs.isEmpty) = false)
    (hk : cfClosureKind? it.body = some (.fnOnce, k)) :
    cfResolveClosure prog n .fnOnce = .ok (cfItemInstance n) := by
  simp [cfResolveClosure, hit, hgen, hk]

/-- `resolve_closure(.., FnOnce)` of a by-reference (`Fn` or `FnMut`) closure body is its
`ClosureOnceShim`: the stuttering path. -/
theorem cfResolveClosure_fn_is_shim {prog : CfProg} {n k : Nat} {it : CfItem} {kind : CfClosureKind}
    (hit : cfItem? prog n = some it)
    (hgen : (it.body.typeParamCount != 0 && it.typeArgs.isEmpty) = false)
    (hk : cfClosureKind? it.body = some (kind, k)) (hkind : kind = .fn ∨ kind = .fnMut) :
    cfResolveClosure prog n .fnOnce = .ok (cfShimInstance n) := by
  rcases hkind with rfl | rfl <;> simp [cfResolveClosure, hit, hgen, hk]

/-- A closure body with unresolved parent generic arguments (`R1`) is never resolved: the hooks
fail closed with `.unsupported`, never with UB. -/
theorem cfResolveClosure_generic_unsupported {prog : CfProg} {n : Nat} {it : CfItem}
    (requested : CfClosureKind) (hit : cfItem? prog n = some it)
    (hgen : (it.body.typeParamCount != 0 && it.typeArgs.isEmpty) = true) :
    cfResolveClosure prog n requested =
      .error (.unsupported "closure body with unresolved parent generic arguments") := by
  simp [cfResolveClosure, hit, hgen]

/-! ## §15. Kernel-checked witnesses

Every theorem of this section is closed by `decide +kernel` on closed terms. Where the vendored
interpreter runs, the goal is first transported along `cfStepHooks_eq_K`, so each statement is
about `cfStepHooks`, i.e. the unmodified `Step.step`, `Cast.cast`, and `Call.evalCallTerminator`. -/

/-- **`FnOnce` certificate (C6).** `closure_matrix::fn_once_kind(5) = 8` on both machines with
stutter index `0`: the indirect call enters the by-value closure body directly through the
vendored `nonCapturing && localId == 1` branch. -/
theorem cf_fn_once_certificate :
    cfCertificate (cfStepHooks cfProgFnOnce) cfProgFnOnce cfFx_fn_once_kind
      [cfFx_id_once, cfFx_fn_once_kind_closure_0] [cfU32 5] [cfU32Imm 5] 200 =
      some (.scalar 8 4, 0) := by
  rw [cfStepHooks_eq_K]; decide +kernel

/-- **`FnOnce` 1-to-1 lockstep simulation (C6)** between `stepMirFn` and `Step.step`. -/
theorem cf_fn_once_lockstep :
    ∃ m, cfMiriInit cfProgFnOnce [cfU32Imm 5] = some m ∧
      CfLockstepSim (cfStepHooks cfProgFnOnce) cfProgFnOnce cfFx_fn_once_kind
        (cfInit cfFx_fn_once_kind [cfU32 5] [cfFx_id_once, cfFx_fn_once_kind_closure_0]) m
        (.scalar 8 4) := by
  obtain ⟨m, hm, _, hs⟩ := cfCertificate_sound cf_fn_once_certificate
  exact ⟨m, hm, cfStutterSim_zero_lockstep hs rfl⟩

/-- **Reproducer parity on `stepMirFn`.** `__anneal_vt_driver_61873(35, 24) = 159` and
`pass_shared_temp_const_raw_ptr_read_and_freeze_retag__b22_c27() = 9147 : u32`, the value Miri
reports. -/
theorem cf_trusted_finding_parity :
    cfRun cfFx_finding_driver 600
      (cfInit cfFx_finding_driver [cfU32 35, cfU32 24] [cfFx_finding_closure_0, cfFx_finding_closure_1]) =
      .scalar 159 4 ∧
    cfRun cfFx_finding_main 600
      (cfInit cfFx_finding_main [] [cfFx_finding_driver, cfFx_finding_closure_0, cfFx_finding_closure_1]) =
      .scalar 9147 4 :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- **Boundary of the reproducer's `main` body under `Step.step`.** The hooks of this module stop
with `.unsupported` at the struct aggregate `PairU32 { .. }` of the root body, before any closure
is reached. The closure coercions and calls of the reproducer all live in the driver. -/
theorem cf_miri_finding_main_boundary :
    cfMiriRunFrom (cfStepHooks cfProgFinding) cfProgFinding 600 [] = .unsupported := by
  rw [cfStepHooks_eq_K]; decide +kernel

/-- The `stepMirFn` results of the closure matrix: `Fn`, `FnMut`, `FnOnce`, zero-argument,
two-argument, `ClosureFnPointer(Unsafe)`, `UnsafeFnPointer` + `FnPtrToPtr` (`262 = 6 ^ (1 << 8)`
records `raw_c == raw_d`), mixed `fn` item + closure, lowered `const_eval_select`, and
`TailCall`. -/
theorem cf_trusted_matrix :
    cfRun cfFx_fn_shared 600 (cfInit cfFx_fn_shared [cfU32 5] [cfFx_fn_shared_closure_0]) = .scalar 22 4 ∧
    cfRun cfFx_fn_mut_kind 600
      (cfInit cfFx_fn_mut_kind [cfU32 5] [cfFx_id_mut, cfFx_fn_mut_kind_closure_0]) = .scalar 7 4 ∧
    cfRun cfFx_fn_once_kind 600
      (cfInit cfFx_fn_once_kind [cfU32 5] [cfFx_id_once, cfFx_fn_once_kind_closure_0]) = .scalar 8 4 ∧
    cfRun cfFx_zero_arg 600 (cfInit cfFx_zero_arg [] [cfFx_zero_arg_closure_0]) = .scalar 7 4 ∧
    cfRun cfFx_two_arg 600 (cfInit cfFx_two_arg [cfU32 6, cfU32 3] [cfFx_two_arg_closure_0]) = .scalar 5 4 ∧
    cfRun cfFx_unsafe_closure 600
      (cfInit cfFx_unsafe_closure [cfU32 5] [cfFx_unsafe_closure_closure_0]) = .scalar 20 4 ∧
    cfRun cfFx_widen_and_identity 600
      (cfInit cfFx_widen_and_identity [cfU32 5] [cfFx_widen_and_identity_closure_0]) = .scalar 262 4 ∧
    cfRun cfFx_mixed_fn_item_and_closure 600
      (cfInit cfFx_mixed_fn_item_and_closure [cfU32 4]
        [cfFx_helper_triple, cfFx_mixed_fn_item_and_closure_closure_0]) = .scalar 24 4 ∧
    cfRun cfFx_ces_through_closure_fn_ptr 600
      (cfInit cfFx_ces_through_closure_fn_ptr [cfU32 4] [cfFx_ces_through_closure_fn_ptr_closure_0]) =
      .scalar 21 4 ∧
    cfRun cfTailRoot 600
      (cfInit cfTailRoot [cfU32 9] [cfFx_tail_through_closure, cfFx_tail_through_closure_closure_0]) =
      .scalar 12 4 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Generic closure under `R1` (C5).** Both machines fail closed with `.unsupported`, never UB. -/
theorem cf_generic_closure_r1_unsupported :
    cfRun cfFx_call_generic 300
      (cfInit cfFx_call_generic [cfU32 77] [cfFx_generic_closure, cfFx_generic_closure_closure_0]) =
      .unsupported ∧
    cfMiriRunFrom (cfStepHooks cfProgGeneric) cfProgGeneric 300 [cfU32Imm 77] = .unsupported := by
  refine ⟨by decide +kernel, ?_⟩
  rw [cfStepHooks_eq_K]; decide +kernel

/-- **Direct closure call with explicit `&_env` (C11).** `Trusted` does not route a direct
`Fn::call(&_env, (x,))` through the function-pointer path: it surfaces as the visible external
call `core::ops::Fn::call`. -/
theorem cf_direct_closure_call_trusted_external :
    cfRun cfFx_direct_closure_call 300
      (cfInit cfFx_direct_closure_call [cfU32 5] [cfFx_direct_closure_call_closure_0]) =
      .ext "core::ops::Fn::call" := by
  decide +kernel

/-- **Boundary of panic unwinding through an indirect closure call.** `Trusted` reaches the
panic machinery of the closure body through the pointer (the external call
`core::fmt::Arguments::from_str`); the hooks of this module stop with `.unsupported` at the
`Guard(..)` struct aggregate of the caller. No unwinding simulation is claimed. -/
theorem cf_unwind_boundary :
    cfRun cfFx_unwind_through_closure 300
      (cfInit cfFx_unwind_through_closure [cfU32 0]
        [cfFx_unwind_through_closure_closure_0, cfFx_Guard_as_core_ops_Drop_drop]) =
      .ext "core::fmt::Arguments::<'a>::from_str" ∧
    cfMiriRunFrom (cfStepHooks cfProgUnwind) cfProgUnwind 300 [cfU32Imm 0] = .unsupported := by
  refine ⟨by decide +kernel, ?_⟩
  rw [cfStepHooks_eq_K]; decide +kernel

/-- **Capturing closures fail closed (C10).** A closure type with a `u32` upvar or a zero-sized
`()` upvar is `.ub` in `Trusted`; the vendored `Cast.cast` rejects the program
(`invalidProgram "capturing closure in pointer cast"`). -/
theorem cf_neg_capturing_fail_closed :
    cfNegTrusted cfNegCapU32 = .ub ∧ cfNegMiri cfNegCapU32 = .invalid ∧
    cfNegTrusted cfNegCapUnit = .ub ∧ cfNegMiri cfNegCapUnit = .invalid := by
  refine ⟨by decide +kernel, ?_, by decide +kernel, ?_⟩ <;>
    (unfold cfNegMiri; rw [cfStepHooks_eq_K]; decide +kernel)

/-- **Forged `(N+1)`-argument indirect call (C10)** is UB on both machines; the vendored
`initStackFrame` reports the argument-count mismatch on the closure `self` parameter. -/
theorem cf_neg_forged_call_ub :
    cfNegTrusted cfNegForged = .ub ∧ cfNegMiri cfNegForged = .ub := by
  refine ⟨by decide +kernel, ?_⟩
  unfold cfNegMiri; rw [cfStepHooks_eq_K]; decide +kernel

/-- **Retyped signature `fn(u64) -> u32`**: `.ub` in `Trusted`; the hooks reject the program
(the caller's layout table has no layout for the forged argument type). -/
theorem cf_neg_transmuted_sig_fail_closed :
    cfNegTrusted cfNegTransSig = .ub ∧ cfNegMiri cfNegTransSig = .invalid := by
  refine ⟨by decide +kernel, ?_⟩
  unfold cfNegMiri; rw [cfStepHooks_eq_K]; decide +kernel

/-- **`extern "C"` call of a Rust-ABI closure** is UB on both machines (the vendored
`evalCalleeAndArgs` calling-convention check). -/
theorem cf_neg_extern_c_ub :
    cfNegTrusted cfNegExternC = .ub ∧ cfNegMiri cfNegExternC = .ub := by
  refine ⟨by decide +kernel, ?_⟩
  unfold cfNegMiri; rw [cfStepHooks_eq_K]; decide +kernel

/-- **`Safety` boundary.** A `ClosureFnPointer(Unsafe)` coercion to a safe pointer type is `.ub`
in `Trusted`, while Miri (which has no dynamic `Safety` check) runs it; retyping a safe pointer
to `unsafe fn` is accepted by both. -/
theorem cf_neg_safety_boundary :
    cfNegTrusted cfNegSafetyCast = .ub ∧ cfNegMiri cfNegSafetyCast = .scalar 8 4 ∧
    cfNegTrusted cfNegSafetyCall = .scalar 8 4 ∧ cfNegMiri cfNegSafetyCall = .scalar 8 4 := by
  refine ⟨by decide +kernel, ?_, by decide +kernel, ?_⟩ <;>
    (unfold cfNegMiri; rw [cfStepHooks_eq_K]; decide +kernel)

/-- **`"ClosureFnPointer(Normal)"` spelling boundary.** `Trusted` fails closed with
`.unsupported`; `translatePointerCoercion` maps the spelling to the same vendored coercion as
`"ClosureFnPointer(Safe)"`, so Miri runs it. `rustc-capture` never emits this spelling. -/
theorem cf_normal_spelling_boundary :
    cfNegTrusted cfNegNormal = .unsupported ∧ cfNegMiri cfNegNormal = .scalar 8 4 ∧
    translatePointerCoercion "ClosureFnPointer(Normal)" =
      translatePointerCoercion "ClosureFnPointer(Safe)" := by
  refine ⟨by decide +kernel, ?_, rfl⟩
  unfold cfNegMiri; rw [cfStepHooks_eq_K]; decide +kernel

/-! ## §16. `Fn` / `FnMut` stuttering certificates checked by compiled evaluation

**These are NOT theorems and NOT kernel-checked.** Each `#guard` below runs the certificate
checker `cfCertificate` under `cfStepHooks` (the unmodified vendored `Step.step`) with Lean's
compiled evaluator and fails the build if the result differs. By `cfCertificate_sound`, an
accepted certificate `some (o, k)` is a `CfStutterSim` with stutter index `k`; the index `5`
is the five `Step.step`s inside one `ClosureOnceShim` frame (`StorageLive(_3)`,
`_3 = &mut _1`, the `call_mut` terminator, `drop(_1)`, `return`), and `15` is three such calls.
Kernel reduction of the vendored memory model on the shim's `_3 = &mut _1` (which forces the
zero-sized closure local into memory) does not finish within the build's resource limits, so
these certificates are not stated as theorems. -/

-- Reproducer driver: `__anneal_vt_driver_61873(35, 24) = 159` across three `Fn` closure calls.
#guard cfCertificate (cfStepHooks cfProgDriver) cfProgDriver cfFx_finding_driver
  [cfFx_finding_closure_0, cfFx_finding_closure_1] [cfU32 35, cfU32 24] [cfU32Imm 35, cfU32Imm 24] 600 =
  some (.scalar 159 4, 15)
-- `Fn`.
#guard cfCertificate (cfStepHooks cfProgFnShared) cfProgFnShared cfFx_fn_shared
  [cfFx_fn_shared_closure_0] [cfU32 5] [cfU32Imm 5] 600 = some (.scalar 22 4, 5)
-- `FnMut`.
#guard cfCertificate (cfStepHooks cfProgFnMut) cfProgFnMut cfFx_fn_mut_kind
  [cfFx_id_mut, cfFx_fn_mut_kind_closure_0] [cfU32 5] [cfU32Imm 5] 600 = some (.scalar 7 4, 5)
-- `FnOnce` (also kernel-checked: `cf_fn_once_certificate`).
#guard cfCertificate (cfStepHooks cfProgFnOnce) cfProgFnOnce cfFx_fn_once_kind
  [cfFx_id_once, cfFx_fn_once_kind_closure_0] [cfU32 5] [cfU32Imm 5] 600 = some (.scalar 8 4, 0)
-- Zero-argument and two-argument closures.
#guard cfCertificate (cfStepHooks cfProgZeroArg) cfProgZeroArg cfFx_zero_arg
  [cfFx_zero_arg_closure_0] [] [] 600 = some (.scalar 7 4, 5)
#guard cfCertificate (cfStepHooks cfProgTwoArg) cfProgTwoArg cfFx_two_arg
  [cfFx_two_arg_closure_0] [cfU32 6, cfU32 3] [cfU32Imm 6, cfU32Imm 3] 600 = some (.scalar 5 4, 5)
-- `ClosureFnPointer(Unsafe)`.
#guard cfCertificate (cfStepHooks cfProgUnsafe) cfProgUnsafe cfFx_unsafe_closure
  [cfFx_unsafe_closure_closure_0] [cfU32 5] [cfU32Imm 5] 600 = some (.scalar 20 4, 5)
-- `ClosureFnPointer(Safe)` + `UnsafeFnPointer` + `FnPtrToPtr` (`raw_c == raw_d`).
#guard cfCertificate (cfStepHooks cfProgWiden) cfProgWiden cfFx_widen_and_identity
  [cfFx_widen_and_identity_closure_0] [cfU32 5] [cfU32Imm 5] 600 = some (.scalar 262 4, 5)
-- Mixed `fn` item and closure coercions.
#guard cfCertificate (cfStepHooks cfProgMixed) cfProgMixed cfFx_mixed_fn_item_and_closure
  [cfFx_helper_triple, cfFx_mixed_fn_item_and_closure_closure_0] [cfU32 4] [cfU32Imm 4] 600 =
  some (.scalar 24 4, 5)
-- `const_eval_select` as lowered by `rustc` in runtime MIR (a plain indirect call).
#guard cfCertificate (cfStepHooks cfProgCes) cfProgCes cfFx_ces_through_closure_fn_ptr
  [cfFx_ces_through_closure_fn_ptr_closure_0] [cfU32 4] [cfU32Imm 4] 600 = some (.scalar 21 4, 5)
-- `TerminatorKind::TailCall` through a closure function pointer (below a root harness frame).
#guard cfCertificate (cfStepHooks cfProgTail) cfProgTail cfTailRoot
  [cfFx_tail_through_closure, cfFx_tail_through_closure_closure_0] [cfU32 9] [cfU32Imm 9] 600 =
  some (.scalar 12 4, 5)
-- Direct closure call with explicit `&_env` (C11): Miri executes it and returns `14`.
#guard cfMiriRunFrom (cfStepHooks cfProgDirect) cfProgDirect 300 [cfU32Imm 5] = .scalar 14 4

/-! ## §17. Exhaustive Axiom and Import-Isolation Audit -/

section AxiomAudit
open Lean Elab Command

/-- Exhaustively verify that this module imports no `MiniRustSpec.*` module; that every
declaration of this module depends only on the standard axioms (`propext`, `Quot.sound`,
`Classical.choice`) with zero `sorryAx` and zero `Lean.ofReduceBool`; that no non-internal
theorem is trivial; and that the headline theorems exist. -/
elab "#assert_closure_fn_ptr_lm_audit" : command => do
  let env ← getEnv
  for modName in env.header.moduleNames do
    if (`MiniRustSpec).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported"
  let rec isTrivialProp : Expr → Bool
    | .forallE _ _ body _ => isTrivialProp body
    | .letE _ _ _ body _ => isTrivialProp body
    | e =>
      if e.isConstOf ``True then true
      else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
      else if e.isAppOfArity ``Iff 2 then e.appFn!.appArg! == e.appArg!
      else false
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  for (c, ci) in env.constants.map₂.toList do
    if let .thmInfo v := ci then
      let u := (Lean.privateToUserName? c).getD c
      if !u.isInternal && isTrivialProp v.type then
        throwError "{c} is a trivial theorem"
      theorems := theorems + 1
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    checked := checked + 1
  if checked == 0 then
    throwError "LeanMiriSpec.ClosureFnPtrLM: 0 declarations found"
  let headline : List Lean.Name := [
    ``cfStepHooks_eq_K, ``cfMiriStutter_sound, ``cfStutterCheck_sound, ``cfCertificate_sound,
    ``cfStutterSim_zero_lockstep, ``cfStutterSim_trusted_run, ``cfStutterSim_miri_run,
    ``cfInstanceOfAllocNat_item, ``cfInstanceOfAllocNat_shim, ``cfFnAllocNat_injective,
    ``cfResolveClosure_fnOnce_is_item, ``cfResolveClosure_fn_is_shim,
    ``cfResolveClosure_generic_unsupported, ``cf_fn_once_certificate, ``cf_fn_once_lockstep,
    ``cf_trusted_finding_parity, ``cf_miri_finding_main_boundary, ``cf_trusted_matrix,
    ``cf_generic_closure_r1_unsupported, ``cf_direct_closure_call_trusted_external,
    ``cf_unwind_boundary, ``cf_neg_capturing_fail_closed, ``cf_neg_forged_call_ub,
    ``cf_neg_transmuted_sig_fail_closed, ``cf_neg_extern_c_ub, ``cf_neg_safety_boundary,
    ``cf_normal_spelling_boundary ]
  for c in headline do
    let some (.thmInfo _) := env.find? c | throwError "{c} is not a theorem of this module"
  logInfo m!"LeanMiriSpec.ClosureFnPtrLM: verified {checked} declarations ({theorems} theorems, {headline.length} headline; sorry_free=true, standard_axioms_only=true, minirustspec_import_free=true)"

#assert_closure_fn_ptr_lm_audit

end AxiomAudit

end LeanMiriSpec.ClosureFnPtrLM
